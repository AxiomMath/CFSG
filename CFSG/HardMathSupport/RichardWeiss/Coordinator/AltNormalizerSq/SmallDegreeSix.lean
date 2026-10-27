module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeAux
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AltSixSevenAut

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open scoped commutatorElement

@[expose] def centerQuotientAut (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by ext ⟨x⟩; rfl
  map_mul' φ ψ := by ext ⟨x⟩; rfl

theorem mem_centralizer_of_centerQuotientAut_eq_one {X : Type} [Group X] {L : Subgroup X}
    (hL : commutator ↥L = ⊤) {u : X} (hu : u ∈ Subgroup.normalizer (L : Set X))
    (h : centerQuotientAut ↥L (L.normalizerMonoidHom ⟨u, hu⟩) = 1) :
    u ∈ Subgroup.centralizer (L : Set X) := by
  set c := L.normalizerMonoidHom ⟨u, hu⟩ with hc
  have h1 : ∀ l : ↥L, l⁻¹ * c l ∈ Subgroup.center ↥L := fun l =>
    QuotientGroup.eq.1 (DFunLike.congr_fun h (l : ↥L ⧸ Subgroup.center ↥L)).symm
  have h2 : ∀ l₁ l₂ : ↥L, c ⁅l₁, l₂⁆ = ⁅l₁, l₂⁆ := by
    intro l₁ l₂
    obtain ⟨z₁, hz₁, e₁⟩ : ∃ z ∈ Subgroup.center ↥L, c l₁ = l₁ * z :=
      ⟨_, h1 l₁, (mul_inv_cancel_left _ _).symm⟩
    obtain ⟨z₂, hz₂, e₂⟩ : ∃ z ∈ Subgroup.center ↥L, c l₂ = l₂ * z :=
      ⟨_, h1 l₂, (mul_inv_cancel_left _ _).symm⟩
    rw [map_commutatorElement, e₁, e₂]
    exact CFSG.AGLEmbedding.AltSixSevenAut.commutatorElement_mul_central hz₁ hz₂
  have h3 : ∀ l : ↥L, c l = l := by
    have hle : commutator ↥L ≤ MonoidHom.eqLocus (c : ↥L →* ↥L) (MonoidHom.id ↥L) :=
      Subgroup.commutator_le.2 fun a _ b _ => h2 a b
    exact fun l => hle (hL ▸ Subgroup.mem_top l)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h4 : u * l * u⁻¹ = l := congrArg Subtype.val (h3 ⟨l, hl⟩)
  calc l * u = (u * l * u⁻¹) * u := by rw [h4]
    _ = u * l := by group

@[expose] def pCoreQuotientAut (J : Type*) [Group J] : MulAut J →* MulAut (J ⧸ CFSG.pCore 2 J) where
  toFun φ := QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  map_one' := by ext ⟨x⟩; rfl
  map_mul' φ ψ := by ext ⟨x⟩; rfl

theorem pCoreQuotientAut_mk {J : Type*} [Group J] (φ : MulAut J) (x : J) :
    pCoreQuotientAut J φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

theorem card_mulAut_perm_three : Nat.card (MulAut (Equiv.Perm (Fin 3))) = 6 := by
  rw [← Nat.card_congr CFSG.Quasithin.SBd.conjEquivPerm3.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

theorem index_centralizer_le_three_of_alt6
    {Γ : Type} [Group Γ] [Finite Γ] {Lb J : Subgroup Γ} (hLb : commutator ↥Lb = ⊤)
    (eL : ↥Lb ⧸ Subgroup.center ↥Lb ≃* alternatingGroup (Fin 6))
    (hJL : J ≤ Lb) (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin 3))
    {U : Type*} [Group U] [Finite U] (hU : IsPGroup 3 U) (ι : U →* Γ)
    (hNL : ∀ u, ι u ∈ Subgroup.normalizer (Lb : Set Γ))
    (hNJ : ∀ u, ι u ∈ Subgroup.normalizer (J : Set Γ)) :
    ((Subgroup.centralizer (Lb : Set Γ)).comap ι).index ≤ 3 := by
  classical
  set Cc := (Subgroup.centralizer (Lb : Set Γ)).comap ι with hCc
  set ψ : U →* MulAut (↥Lb ⧸ Subgroup.center ↥Lb) :=
    (centerQuotientAut ↥Lb).comp (Lb.normalizerMonoidHom.comp (ι.codRestrict _ hNL)) with hψ
  have hψker : ψ.ker ≤ Cc := fun u hu =>
    mem_centralizer_of_centerQuotientAut_eq_one hLb (hNL u) hu
  set θ : U →* MulAut ↥J := J.normalizerMonoidHom.comp (ι.codRestrict _ hNJ) with hθ
  set χ : U →* MulAut (↥J ⧸ CFSG.pCore 2 ↥J) := (pCoreQuotientAut ↥J).comp θ with hχ
  have hχcard : Nat.card (MulAut (↥J ⧸ CFSG.pCore 2 ↥J)) = 6 := by
    rw [card_mulAut_eq_of_equiv eJ, card_mulAut_perm_three]
  have : Finite (MulAut (↥J ⧸ CFSG.pCore 2 ↥J)) :=
    Nat.finite_of_card_ne_zero (by rw [hχcard]; norm_num)
  have hχidx : χ.ker.index ≤ 3 :=
    index_ker_le_of_not_sq_dvd Nat.prime_three hU χ (by rw [hχcard]; norm_num)
  by_cases hle : χ.ker ≤ ψ.ker
  · have h1 : Cc.index ∣ χ.ker.index := Subgroup.index_dvd_of_le (hle.trans hψker)
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1).trans hχidx
  exfalso
  obtain ⟨u, huχ, huψ⟩ := IsConcreteLE.not_le_iff_exists.1 hle
  obtain ⟨k, hk⟩ := hU u
  have hα1 : ψ u ≠ 1 := huψ
  set α' := MulAut.congr eL (ψ u) with hα'
  have hα'1 : α' ≠ 1 := fun h => hα1 ((MulAut.congr eL).injective (h.trans (map_one _).symm))
  have hα'k : α' ^ 3 ^ k = 1 := by
    rw [hα', ← map_pow, ← map_pow, hk, map_one, map_one]
  obtain ⟨g, hg⟩ := alt6_exists_conj_of_pow α' hα'k
  have hg1 : g ≠ 1 := by rintro rfl; exact hα'1 (hg.trans (map_one _))
  have hgk : g ^ 3 ^ k = 1 := by
    apply CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
    rw [map_pow, ← hg, hα'k, map_one]
  have hgo : orderOf g = 3 := alt6_orderOf_eq_three g hg1 hgk
  set τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hτ
  obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk_surjective (eJ.symm τ)
  let X := {h : ↥J // (QuotientGroup.mk h : ↥J ⧸ CFSG.pCore 2 ↥J) = QuotientGroup.mk h₀}
  have hact : ∀ (k' : χ.ker) (x : X),
      (QuotientGroup.mk (θ (k' : U) x.1) : ↥J ⧸ CFSG.pCore 2 ↥J) = QuotientGroup.mk h₀ := by
    intro k' x
    have h1 : χ k' = 1 := k'.2
    have h2 := congrArg (fun φ => φ (QuotientGroup.mk x.1 : ↥J ⧸ CFSG.pCore 2 ↥J)) h1
    simp only [hχ, MonoidHom.comp_apply, pCoreQuotientAut_mk, MulAut.one_apply] at h2
    exact h2.trans x.2
  let _ : MulAction χ.ker X :=
    { smul := fun k' x => ⟨θ (k' : U) x.1, hact k' x⟩
      one_smul := fun x => Subtype.ext (by
        show θ 1 x.1 = x.1
        rw [map_one]; rfl)
      mul_smul := fun a b x => Subtype.ext (by
        show θ ((a : U) * (b : U)) x.1 = θ (a : U) (θ (b : U) x.1)
        rw [map_mul]; rfl) }
  have hXcard : ¬ 3 ∣ Nat.card X := by
    have hXN : Nat.card X = Nat.card (CFSG.pCore 2 ↥J) := Nat.card_congr
      { toFun := fun x => ⟨h₀⁻¹ * x.1, QuotientGroup.eq.1 x.2.symm⟩
        invFun := fun n => ⟨h₀ * n, by
          rw [QuotientGroup.eq]; simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (G := CFSG.pCore 2 ↥J)).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
    rw [hXN, ha]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hKp : IsPGroup 3 χ.ker := hU.to_subgroup _
  obtain ⟨x₁, hx₁⟩ := hKp.nonempty_fixed_point_of_prime_not_dvd_card X hXcard
  have hfix : θ u x₁.1 = x₁.1 := congrArg Subtype.val (hx₁ ⟨u, huχ⟩)
  set h' : ↥J := x₁.1 with hh'
  have hθu : ((θ u h' : ↥J) : Γ) = ι u * h' * (ι u)⁻¹ := by
    simp [hθ]
  have hconj : ι u * (h' : Γ) * (ι u)⁻¹ = h' := by
    rw [← hθu, hfix]
  set ĥ : ↥Lb ⧸ Subgroup.center ↥Lb := QuotientGroup.mk ⟨h', hJL h'.2⟩ with hĥ
  have hαĥ : ψ u ĥ = ĥ := by
    show (QuotientGroup.mk ((Lb.normalizerMonoidHom ⟨ι u, hNL u⟩) ⟨h', hJL h'.2⟩) :
      ↥Lb ⧸ Subgroup.center ↥Lb) = _
    congr 1
    apply Subtype.ext
    simpa using hconj
  have hcomm : g * eL ĥ = eL ĥ * g := by
    have h1 : α' (eL ĥ) = eL ĥ := by
      rw [hα']
      simp [MulAut.congr_apply, hαĥ]
    rw [hg] at h1
    simpa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using h1
  have hcent : eL ĥ ∈ Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 6))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hcomm
  have hpow : (eL ĥ) ^ 3 = 1 :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.pow_three_of_mem_centralizer hgo _ hcent
  have hĥ3 : ĥ ^ 3 = 1 := by
    apply eL.injective
    rw [map_pow, hpow, map_one]
  have hcen : (⟨(h' ^ 3 : ↥J), hJL (h' ^ 3).2⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← hĥ3, hĥ, ← QuotientGroup.mk_pow]
    rfl
  have hmk' : eJ (QuotientGroup.mk h') = τ := by
    rw [x₁.2, hh₀]; simp
  have hcomm2 : ∀ y : ↥J, y * h' ^ 3 = h' ^ 3 * y := by
    intro y
    have h := congrArg (fun z : ↥Lb => (z : Γ)) (Subgroup.mem_center_iff.1 hcen ⟨y, hJL y.2⟩)
    exact Subtype.ext h
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (eJ.symm (Equiv.swap 1 2))
  have h3 := congrArg (fun z => eJ (QuotientGroup.mk z)) (hcomm2 y)
  simp only [QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_pow, map_pow, hmk', hy,
    MulEquiv.apply_symm_apply] at h3
  revert h3
  decide

end CFSG.HardMathSupport.RichardWeiss.Coordinator
