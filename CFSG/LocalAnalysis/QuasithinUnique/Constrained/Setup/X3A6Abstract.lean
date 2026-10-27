module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AltPerm
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOrig

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.LocalCores CFSG.SectionRank

section Sylow

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem isSylowTwoOf_map_of_odd_ker (θ : X →* Y) (hker : Odd (Nat.card θ.ker)) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map θ) θ.range := by
  classical
  obtain ⟨-, hT2, hTc⟩ := isSylowTwoOf_iff.mp hT
  have hTker : ∀ x ∈ T, θ x = 1 → x = 1 := by
    intro x hxT hx1
    obtain ⟨k, hk⟩ := hT2 ⟨x, hxT⟩
    have h1 : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : x ^ Nat.card θ.ker = 1 := by
      have h3 : ((⟨x, hx1⟩ : θ.ker) ^ Nat.card θ.ker : θ.ker) = 1 := pow_card_eq_one'
      exact congrArg Subtype.val h3
    have hcop : Nat.Coprime (2 ^ k) (Nat.card θ.ker) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hker)
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop, pow_one] at this
  have hinj : Function.Injective (θ.comp T.subtype) := by
    intro a b hab
    apply Subtype.ext
    have : θ ((a : X) * (b : X)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr hab
    have h0 := hTker _ (T.mul_mem a.2 (T.inv_mem b.2)) this
    exact mul_inv_eq_one.mp h0
  have hcardT : Nat.card (T.map θ) = Nat.card T := by
    have : T.map θ = (θ.comp T.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrange : Nat.card X = Nat.card θ.ker * Nat.card θ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, mul_comm]
  have htwo : twoPart (⊤ : Subgroup X) = twoPart θ.range := by
    have h0 : (Nat.card θ.ker).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
      intro h2
      exact (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr h2))
    unfold twoPart
    rw [Subgroup.card_top, hrange, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, h0, zero_add]
  rw [isSylowTwoOf_iff]
  exact ⟨Subgroup.map_le_range θ T, hT2.map θ, by rw [hcardT, hTc, htwo]⟩

omit [Finite X] [Finite Y] in
theorem isUniqueMaxOver_map_of_ker_le (θ : X →* Y) {T M : Subgroup X} (hker : θ.ker ≤ M)
    (h : IsUniqueMaxOver T M ⊤) : IsUniqueMaxOver (T.map θ) (M.map θ) θ.range := by
  obtain ⟨hTM, hMX, hY⟩ := h
  refine ⟨Subgroup.map_mono hTM, ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_le_range θ M) fun heq => hMX.ne ?_
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : θ x ∈ M.map θ := by rw [heq]; exact ⟨x, rfl⟩
    obtain ⟨m, hm, hmx⟩ := hx
    have : m⁻¹ * x ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
    have := M.mul_mem hm (hker this)
    simpa using this
  · intro Y' hTY hYr
    have hY1 : Y'.comap θ < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hYr.ne ?_
      refine le_antisymm hYr.le ?_
      rintro _ ⟨x, rfl⟩
      have : x ∈ Y'.comap θ := htop ▸ Subgroup.mem_top x
      exact this
    have hTc : T ≤ Y'.comap θ := Subgroup.map_le_iff_le_comap.mp hTY
    have := Subgroup.map_mono (f := θ) (hY _ hTc hY1)
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hYr.le] at this
    exact this

end Sylow

section Perm6

theorem eq_top_or_eq_alt {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    {D : Subgroup (Equiv.Perm α)} (h : alternatingGroup α ≤ D) :
    D = ⊤ ∨ D = alternatingGroup α := by
  have hdvd : D.index ∣ (alternatingGroup α).index := Subgroup.index_dvd_of_le h
  rw [alternatingGroup.index_eq_two] at hdvd
  have h2 : D.index = 1 ∨ D.index = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd
  rcases h2 with h1 | h2
  · exact Or.inl (Subgroup.index_eq_one.mp h1)
  · right
    refine le_antisymm ?_ h
    have h3 := Subgroup.relIndex_mul_index h
    rw [alternatingGroup.index_eq_two, h2] at h3
    have : (alternatingGroup α).relIndex D = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp this

end Perm6


section Components

variable {X : Type} [Group X] [Finite X]

noncomputable def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem pow_three_multiplicative (x : Multiplicative (Fin 2 → ZMod 3)) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply, nsmul_eq_mul]
  exact mul_eq_zero_of_left (by simpa using ZMod.natCast_self 3) _

theorem eq_of_isComponent_of_alt6 (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    (hsqtk : IsSQTKCat X) {L₀ L₁ : Subgroup X} (h₀ : CFSG.IsComponent L₀)
    (h₁ : CFSG.IsComponent L₁)
    (e₀ : Nonempty (↥L₀ ⧸ Subgroup.center ↥L₀ ≃* alternatingGroup (Fin 6)))
    (e₁ : Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃* alternatingGroup (Fin 6))) : L₀ = L₁ := by
  classical
  by_contra hne
  obtain ⟨e₀⟩ := e₀
  obtain ⟨e₁⟩ := e₁
  have hKtop : CFSG.layer ↥(CFSG.layer X) = ⊤ := Layer.layer_subgroupOf_eq_top rfl
  have hQtop : CFSG.layer (↥(CFSG.layer X) ⧸ Subgroup.center ↥(CFSG.layer X)) = ⊤ :=
    layer_eq_top_of_surjective hKtop (QuotientGroup.mk' _) QuotientGroup.mk_surjective
  have hsqt := sqtk_semisimple_section_rank_of_catalog hcent hcat hsqtk (CFSG.layer X)
    (Subgroup.center ↥(CFSG.layer X)) hQtop
  have hrank := (isStronglyQuasithin_iff.mp hsqt) 3 Nat.prime_three (by norm_num)
  let c₀ : ComponentIndex X := ⟨L₀, h₀⟩
  let c₁ : ComponentIndex X := ⟨L₁, h₁⟩
  have hc : c₀ ≠ c₁ := fun h => hne (congrArg Subtype.val h)
  let ε := layerCentralQuotientEquiv X
  let f₀ : alternatingGroup (Fin 6) →* ∀ K : ComponentIndex X, K.1 ⧸ Subgroup.center K.1 :=
    (MonoidHom.mulSingle (fun K : ComponentIndex X => K.1 ⧸ Subgroup.center K.1) c₀).comp
      e₀.symm.toMonoidHom
  let f₁ : alternatingGroup (Fin 6) →* ∀ K : ComponentIndex X, K.1 ⧸ Subgroup.center K.1 :=
    (MonoidHom.mulSingle (fun K : ComponentIndex X => K.1 ⧸ Subgroup.center K.1) c₁).comp
      e₁.symm.toMonoidHom
  have hcomm : ∀ a b : Multiplicative (Fin 2 → ZMod 3),
      Commute ((f₀.comp sixHom) a) ((f₁.comp sixHom) b) := fun a b =>
    Pi.mulSingle_commute hc _ _
  let ψ : Multiplicative (Fin 2 → ZMod 3) × Multiplicative (Fin 2 → ZMod 3) →*
      ∀ K : ComponentIndex X, K.1 ⧸ Subgroup.center K.1 :=
    (f₀.comp sixHom).noncommCoprod (f₁.comp sixHom) hcomm
  have hev₀ : ∀ p : Multiplicative (Fin 2 → ZMod 3) × Multiplicative (Fin 2 → ZMod 3),
      ψ p c₀ = e₀.symm (sixHom p.1) := by
    intro p
    simp [ψ, f₀, f₁, MonoidHom.noncommCoprod_apply]
    exact Pi.mulSingle_eq_of_ne hc _
  have hev₁ : ∀ p : Multiplicative (Fin 2 → ZMod 3) × Multiplicative (Fin 2 → ZMod 3),
      ψ p c₁ = e₁.symm (sixHom p.2) := by
    intro p
    simp [ψ, f₀, f₁, MonoidHom.noncommCoprod_apply]
    exact Pi.mulSingle_eq_of_ne hc.symm _
  have hψ : Function.Injective ψ := by
    intro p q hpq
    have h0 := congrFun hpq c₀
    have h1 := congrFun hpq c₁
    rw [hev₀, hev₀] at h0
    rw [hev₁, hev₁] at h1
    exact Prod.ext (sixHom_injective (e₀.symm.injective h0))
      (sixHom_injective (e₁.symm.injective h1))
  have hcardM : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 3 ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.card_zmod]
  have hA : Nat.card (Multiplicative (Fin 2 → ZMod 3) × Multiplicative (Fin 2 → ZMod 3)) =
      3 ^ 4 := by
    rw [Nat.card_prod, hcardM]
    norm_num
  have hle := le_pRank_of_injective (p := 3) (by norm_num)
    (fun a b : Multiplicative (Fin 2 → ZMod 3) × Multiplicative (Fin 2 → ZMod 3) => mul_comm a b)
    (fun a => Prod.ext (pow_three_multiplicative a.1) (pow_three_multiplicative a.2)) hA
    (ε.toMonoidHom.comp ψ)
    (ε.injective.comp hψ) (H := ⊤) le_top
  omega

theorem false_of_A6_layer (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    (hsqtk : IsSQTKCat X) {T M : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M) (hMX : M < ⊤)
    (hmax : ∀ Y : Subgroup X, T ≤ Y → Y < ⊤ → Y ≤ M)
    (hgf : CFSG.generalizedFitting X = CFSG.layer X)
    (hC : (Subgroup.center ↥(CFSG.layer X)).map (CFSG.layer X).subtype ≤ M)
    (hCodd : Odd (Nat.card (Subgroup.center ↥(CFSG.layer X))))
    (htrans : ∀ L L' : Subgroup X, CFSG.IsComponent L → CFSG.IsComponent L' →
      ∃ t ∈ T, L.map (MulAut.conj t).toMonoidHom = L')
    {L₀ : Subgroup X} (hL₀ : CFSG.IsComponent L₀)
    (e₀ : Nonempty (↥L₀ ⧸ Subgroup.center ↥L₀ ≃* alternatingGroup (Fin 6)))
    (hθ : L₀.Normal → Subgroup.centralizer (L₀ : Set X) = (Subgroup.center ↥L₀).map L₀.subtype →
      Odd (Nat.card (Subgroup.center ↥L₀)) →
      ∃ θ : X →* Equiv.Perm (Fin 6), θ.ker = (Subgroup.center ↥L₀).map L₀.subtype ∧
        L₀.map θ = alternatingGroup (Fin 6)) : False := by
  classical
  obtain ⟨e₀⟩ := e₀
  have hall : ∀ L' : Subgroup X, CFSG.IsComponent L' →
      Nonempty (↥L' ⧸ Subgroup.center ↥L' ≃* alternatingGroup (Fin 6)) := by
    intro L' hL'
    obtain ⟨t, -, rfl⟩ := htrans L₀ L' hL₀ hL'
    exact ⟨(centerQuotientCongr (L₀.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)).symm.trans e₀⟩
  have huniq : ∀ L' : Subgroup X, CFSG.IsComponent L' → L' = L₀ := fun L' hL' =>
    (eq_of_isComponent_of_alt6 hcent hcat hsqtk hL₀ hL' ⟨e₀⟩ (hall L' hL')).symm
  have hlayer : CFSG.layer X = L₀ := by
    have : {K : Subgroup X | CFSG.IsComponent K} = {L₀} := by
      ext K
      exact ⟨fun hK => huniq K hK, fun hK => by rw [Set.mem_singleton_iff.mp hK]; exact hL₀⟩
    rw [CFSG.layer, this, sSup_singleton]
  have hnormal : L₀.Normal := by
    have := layer_characteristic (G := X)
    rw [hlayer] at this
    infer_instance
  have hcl : Subgroup.centralizer (L₀ : Set X) ≤ L₀ := by
    have := centralizer_generalizedFitting_le X
    rw [hgf, hlayer] at this
    exact this
  have hcent_eq : Subgroup.centralizer (L₀ : Set X) = (Subgroup.center ↥L₀).map L₀.subtype := by
    apply le_antisymm
    · intro c hc
      have hcL : c ∈ L₀ := hcl hc
      refine ⟨⟨c, hcL⟩, ?_, rfl⟩
      exact Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) g g.2)
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨h, hh⟩)
  subst hlayer
  obtain ⟨θ, hker, himg⟩ := hθ hnormal hcent_eq hCodd
  have hkerodd : Odd (Nat.card θ.ker) := by
    rw [hker, Subgroup.card_map_of_injective (CFSG.layer X).subtype_injective]
    exact hCodd
  have hker_le : θ.ker ≤ M := hker ▸ hC
  have halt_le : alternatingGroup (Fin 6) ≤ θ.range := himg ▸ Subgroup.map_le_range θ _
  have hD := eq_top_or_eq_alt halt_le
  have hS := isSylowTwoOf_map_of_odd_ker θ hkerodd hT
  have hU := isUniqueMaxOver_map_of_ker_le θ hker_le ⟨hTM, hMX, hmax⟩
  obtain ⟨X', Y', h1, h2, h3, h4, h5⟩ := twoGenPerm_six hD hS
  exact not_isUniqueMaxOver_of_two_gen ⟨X', Y', h1, h2, h3, h4, h5⟩ ⟨_, hU⟩

end Components

end CFSG.QuasithinUnique.Setup.X3
