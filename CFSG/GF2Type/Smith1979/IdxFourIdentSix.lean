module

public import CFSG.GF2Type.Smith1979.IdxFourIdentWeightsDefs
public import CFSG.GF2Type.Smith1979.IdxFourIdentOrbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.Case25.U43Weights

private theorem eq_zero_of_theta0_eq {x : V12} (h : theta0 x = x) : x = 0 := by
  have hz : ∀ a c : ZMod 2, c = a → a + c = c → a = 0 ∧ c = 0 := by decide
  have key : ∀ i, x (lo i) = 0 ∧ x (hi i) = 0 := fun i => by
    have h1 := congrFun h (lo i)
    have h2 := congrFun h (hi i)
    rw [theta0_lo] at h1
    rw [theta0_hi] at h2
    exact hz _ _ h1 h2
  exact ext_lo_hi (fun i => (key i).1) (fun i => (key i).2)

private theorem ne_one_of_eq_theta0e {A : Type} [Group A] {ρ : A →* G12} {θ : A}
    (hθ : ρ θ = theta0e) : θ ≠ 1 := by
  rintro rfl
  rw [map_one] at hθ
  have h : theta0 (Pi.single 0 1 : V12) = Pi.single 0 1 := (DFunLike.congr_fun hθ _).symm
  have := congrFun (eq_zero_of_theta0_eq h) 0
  simp at this

private theorem fixedSpace_top_eq_bot {A : Type} [CommGroup A] {ρ : A →* G12} {θ : A}
    (hθ : ρ θ = theta0e) : LemmaW.fixedSpace (rep ρ) ⊤ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hfix := (LemmaW.mem_fixedSpace (rep ρ)).mp hv θ (Subgroup.mem_top θ)
  rw [rep_apply, hθ, theta0e_apply] at hfix
  exact eq_zero_of_theta0_eq hfix

private theorem weightSpace_eq_bot_of_mem {A : Type} [CommGroup A] [Finite A]
    (hA3 : ∀ a : A, a ^ 3 = 1) {ρ : A →* G12} {θ : A} (hθ : ρ θ = theta0e) {H : Subgroup A}
    (h : θ ∈ H) : LemmaW.weightSpace (rep ρ) H = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hfix := ((LemmaW.mem_weightSpace_iff (rep ρ) hA3 H v).mp hv).1 θ h
  rw [rep_apply, hθ, theta0e_apply] at hfix
  exact eq_zero_of_theta0_eq hfix

private theorem card_le_six {α : Type*} {S : Finset α} {d : α → ℕ} (hsum : ∑ x ∈ S, d x = 12)
    (h2 : ∀ x ∈ S, 2 ≤ d x) : S.card ≤ 6 := by
  have hl : ∑ _x ∈ S, 2 ≤ ∑ x ∈ S, d x := Finset.sum_le_sum h2
  rw [Finset.sum_const, smul_eq_mul, hsum] at hl
  omega

private theorem eq_two_of_card_six {α : Type*} [DecidableEq α] {S : Finset α} {d : α → ℕ}
    (hsum : ∑ x ∈ S, d x = 12) (h2 : ∀ x ∈ S, 2 ≤ d x) (h6 : S.card = 6) :
    ∀ x ∈ S, d x = 2 := by
  intro x hx
  have e1 := Finset.add_sum_erase S d hx
  have hc := Finset.card_erase_of_mem hx
  have hl : ∑ _y ∈ S.erase x, 2 ≤ ∑ y ∈ S.erase x, d y :=
    Finset.sum_le_sum fun y hy => h2 y (Finset.mem_of_mem_erase hy)
  rw [Finset.sum_const, smul_eq_mul] at hl
  have := h2 x hx
  omega

private theorem exists_four_of_card_five {α : Type*} [DecidableEq α] {S : Finset α}
    {d : α → ℕ} (hsum : ∑ x ∈ S, d x = 12) (h2 : ∀ x ∈ S, 2 ≤ d x)
    (hev : ∀ x ∈ S, Even (d x)) (h5 : S.card = 5) :
    ∃ x₀ ∈ S, 4 ≤ d x₀ ∧ ∀ x ∈ S, x ≠ x₀ → d x ≤ 2 := by
  have hex : ∃ x₀ ∈ S, 4 ≤ d x₀ := by
    by_contra hcon
    push Not at hcon
    have h22 : ∀ x ∈ S, d x = 2 := fun x hx => by
      obtain ⟨m, hm⟩ := hev x hx
      have := h2 x hx
      have := hcon x hx
      omega
    rw [Finset.sum_congr rfl h22, Finset.sum_const, h5, smul_eq_mul] at hsum
    omega
  obtain ⟨x₀, hx₀, h4⟩ := hex
  refine ⟨x₀, hx₀, h4, fun x hx hne => ?_⟩
  have hx' : x ∈ S.erase x₀ := Finset.mem_erase.mpr ⟨hne, hx⟩
  have e1 := Finset.add_sum_erase S d hx₀
  have e2 := Finset.add_sum_erase (S.erase x₀) d hx'
  have hc1 := Finset.card_erase_of_mem hx₀
  have hc2 := Finset.card_erase_of_mem hx'
  have hl : ∑ _y ∈ (S.erase x₀).erase x, 2 ≤ ∑ y ∈ (S.erase x₀).erase x, d y :=
    Finset.sum_le_sum fun y hy => h2 y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
  rw [Finset.sum_const, smul_eq_mul] at hl
  omega

private theorem index_map_inf {A : Type} [CommGroup A] [Finite A] (hA3 : ∀ a : A, a ^ 3 = 1)
    {θ : A} (hθ1 : θ ≠ 1) {G : Type} [Group G] (ψ : A →* G) (hψs : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.zpowers θ) {H₁ H₂ : Subgroup A} (h₁ : H₁.index = 3)
    (h₂ : H₂.index = 3) (hne : H₁ ≠ H₂) (hθ : θ ∉ H₁) : ((H₁ ⊓ H₂).map ψ).index = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Nat.card (Subgroup.zpowers θ) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA3 θ) hθ1
  have hXidx : (H₁ ⊓ H₂).index = 9 := by
    rw [Subgroup.index_inf, h₂, ← Subgroup.relIndex_sup_left H₂ H₁,
      LemmaW.sup_eq_top_of_index_eq_three h₁ h₂ hne, Subgroup.relIndex_top_right, h₁]
  have hXZ : H₁ ⊓ H₂ ⊓ Subgroup.zpowers θ = ⊥ := by
    have hd := Subgroup.card_dvd_of_le (inf_le_right : H₁ ⊓ H₂ ⊓ Subgroup.zpowers θ ≤ _)
    rw [hZ] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_right : H₁ ⊓ H₂ ⊓ Subgroup.zpowers θ ≤ _) (by rw [hZ, h3])
      have hmem : θ ∈ H₁ ⊓ H₂ ⊓ Subgroup.zpowers θ := by
        rw [heq]
        exact Subgroup.mem_zpowers θ
      exact hθ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hmem).1).1
  have hrel : (H₁ ⊓ H₂).relIndex (H₁ ⊓ H₂ ⊔ Subgroup.zpowers θ) = 3 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right (H₁ ⊓ H₂), hXZ,
      Subgroup.relIndex_bot_left, hZ]
  have hmul := Subgroup.relIndex_mul_index (le_sup_left : H₁ ⊓ H₂ ≤ H₁ ⊓ H₂ ⊔ Subgroup.zpowers θ)
  rw [hrel, hXidx] at hmul
  rw [Subgroup.index_map, ψ.range_eq_top_of_surjective hψs, Subgroup.index_top, mul_one, hker]
  omega

private theorem false_of_card_five {A : Type} [CommGroup A] [Finite A]
    (hA3 : ∀ a : A, a ^ 3 = 1) {θ : A} (hθ1 : θ ≠ 1) (ψ : A →* A4)
    (hψs : Function.Surjective ψ) (hker : ψ.ker = Subgroup.zpowers θ) (β : Gen → (A ≃* A))
    (hψβ : ∀ k a, ψ (β k a) = sg k (ψ a)) (S : Finset (Subgroup A))
    (hS3 : ∀ H ∈ S, H.index = 3) (hSθ : ∀ H ∈ S, θ ∉ H)
    (hSmap : ∀ k, ∀ H ∈ S, H.map (β k).toMonoidHom ∈ S) (d : Subgroup A → ℕ)
    (hdmap : ∀ k H, d (H.map (β k).toMonoidHom) = d H) (hsum : ∑ H ∈ S, d H = 12)
    (h2 : ∀ H ∈ S, 2 ≤ d H) (hev : ∀ H ∈ S, Even (d H)) (h5 : S.card = 5) : False := by
  classical
  obtain ⟨H₀, hH₀, h4, hlt⟩ := exists_four_of_card_five hsum h2 hev h5
  have hfix : ∀ k, H₀.map (β k).toMonoidHom = H₀ := by
    intro k
    by_contra hne
    have := hlt _ (hSmap k H₀ hH₀) hne
    rw [hdmap] at this
    omega
  have hperm : ∀ k, ∀ H ∈ S.erase H₀, H.map (β k).toMonoidHom ∈ S.erase H₀ := by
    intro k H hH
    obtain ⟨hne, hHS⟩ := Finset.mem_erase.mp hH
    refine Finset.mem_erase.mpr ⟨fun heq => ?_, hSmap k H hHS⟩
    have h1 := hlt H hHS hne
    have h3 := hdmap k H
    rw [heq] at h3
    omega
  have hfin : ((fun H => (H₀ ⊓ H).map ψ) '' ↑(S.erase H₀)).Finite :=
    (S.erase H₀).finite_toSet.image _
  have hle4 : ((fun H => (H₀ ⊓ H).map ψ) '' ↑(S.erase H₀)).ncard ≤ 4 := by
    refine (Set.ncard_image_le (S.erase H₀).finite_toSet).trans ?_
    have := Finset.card_erase_of_mem hH₀
    rw [Set.ncard_coe_finset]
    omega
  have hinv : ∀ K ∈ (fun H => (H₀ ⊓ H).map ψ) '' ↑(S.erase H₀), ∀ k : Gen,
      K.map (sg k).toMonoidHom ∈ (fun H => (H₀ ⊓ H).map ψ) '' ↑(S.erase H₀) := by
    rintro _ ⟨H, hH, rfl⟩ k
    refine ⟨H.map (β k).toMonoidHom, hperm k H hH, ?_⟩
    have hcomp : (sg k).toMonoidHom.comp ψ = ψ.comp (β k).toMonoidHom :=
      MonoidHom.ext fun a => (hψβ k a).symm
    show (H₀ ⊓ H.map (β k).toMonoidHom).map ψ = ((H₀ ⊓ H).map ψ).map (sg k).toMonoidHom
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_inf_eq H₀ H (β k).toMonoidHom (β k).injective, hfix k]
  obtain ⟨H, hH⟩ : (S.erase H₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hH₀, h5]
    norm_num
  obtain ⟨hne, hHS⟩ := Finset.mem_erase.mp hH
  have hidx := index_map_inf hA3 hθ1 ψ hψs hker (hS3 H₀ hH₀) (hS3 H hHS) (Ne.symm hne)
    (hSθ H₀ hH₀)
  have hmem : (H₀ ⊓ H).map ψ ∈ (fun H => (H₀ ⊓ H).map ψ) '' ↑(S.erase H₀) := ⟨H, hH, rfl⟩
  have := ten_le_ncard_of_invariant hfin hinv hmem hidx
  omega

theorem six_weights
    {A : Type} [CommGroup A] [Finite A] (hA3 : ∀ a : A, a ^ 3 = 1) (hcard : Nat.card A = 243)
    {ρ : A →* G12} (hρ : Function.Injective ρ) (hρg : ∀ a, ρ a ∈ gammaU) {θ : A}
    (hθ : ρ θ = theta0e)
    (ψ : A →* A4) (hψs : Function.Surjective ψ) (hψk : ∀ a, ψ a = 1 ↔ a ∈ Subgroup.zpowers θ)
    (β : Gen → (A ≃* A)) (b : Gen → G12) (hb : ∀ k a, b k * ρ a * (b k)⁻¹ = ρ (β k a))
    (hψβ : ∀ k a, ψ (β k a) = sg k (ψ a)) :
    ∃ H : Fin 6 → Subgroup A, (∀ i, (H i).index = 3) ∧ (∀ i, θ ∉ H i) ∧
      Function.Injective H ∧
      (∀ i, Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) (H i)) = 2) ∧
      (⨆ i, LemmaW.weightSpace (rep ρ) (H i) = ⊤) ∧
      (∀ H' : Subgroup A, H'.index = 3 → LemmaW.weightSpace (rep ρ) H' ≠ ⊥ → ∃ i, H' = H i) ∧
      (∀ k i, ∃ j, (H i).map (β k).toMonoidHom = H j) := by
  clear hρg
  classical
  haveI : Fintype (Subgroup A) := Fintype.ofFinite _
  obtain ⟨S, hS⟩ : ∃ S : Finset (Subgroup A), S = (Finset.univ.filter
      fun H : Subgroup A => H.index = 3).filter fun H => LemmaW.weightSpace (rep ρ) H ≠ ⊥ :=
    ⟨_, rfl⟩
  have hmemS : ∀ H, H ∈ S ↔ H.index = 3 ∧ LemmaW.weightSpace (rep ρ) H ≠ ⊥ := fun H => by
    rw [hS, Finset.mem_filter, Finset.mem_filter, and_iff_right (Finset.mem_univ H)]
  have hSθ : ∀ H ∈ S, θ ∉ H := fun H hH hθH =>
    ((hmemS H).mp hH).2 (weightSpace_eq_bot_of_mem hA3 hθ hθH)
  have hsum : ∑ H ∈ S, Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) H) = 12 := by
    have key := LemmaW.finrank_eq_fixedSpace_add_sum (rep ρ) hA3
    rw [Module.finrank_fin_fun, fixedSpace_top_eq_bot hθ, finrank_bot, zero_add,
      ← Finset.sum_subtype (p := fun H : Subgroup A => H.index = 3)
        (Finset.univ.filter fun H : Subgroup A => H.index = 3) (fun _ => by simp)
        (fun H => Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) H))] at key
    have hfilter : ∑ H ∈ S, Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) H) =
        ∑ H ∈ Finset.univ.filter (fun H : Subgroup A => H.index = 3),
          Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) H) := by
      rw [hS]
      exact Finset.sum_filter_of_ne fun _ _ hne hbot => hne (by rw [hbot, finrank_bot])
    rw [hfilter]
    exact key.symm
  have h2 : ∀ H ∈ S, 2 ≤ Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) H) :=
    fun H hH => LemmaW.two_le_finrank_weightSpace (rep ρ) hA3 ((hmemS H).mp hH).2
  have hev : ∀ H ∈ S, Even (Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) H)) :=
    fun H _ => LemmaW.even_finrank_weightSpace (rep ρ) hA3 H
  have hfaith : Function.Injective (rep ρ) := fun _ _ h =>
    hρ (LinearEquiv.ext fun v => LinearMap.congr_fun h v)
  have hge5 : 5 ≤ S.card := by
    have hbot : (⨅ H : S, (H : Subgroup A)) = ⊥ := by
      refine eq_bot_iff.mpr (le_trans ?_
        (LemmaW.iInf_hyperplane_weightSpace_ne_bot (rep ρ) hA3 hfaith).le)
      exact le_iInf fun H => iInf_le_of_le ⟨H.1.1, (hmemS _).mpr ⟨H.1.2, H.2⟩⟩ le_rfl
    have h243 : 243 ≤ 3 ^ S.card := by
      calc 243 = (⨅ H : S, (H : Subgroup A)).index := by rw [hbot, Subgroup.index_bot, hcard]
        _ ≤ ∏ H : S, (H : Subgroup A).index := Subgroup.index_iInf_le _
        _ ≤ 3 ^ Fintype.card S :=
          Finset.prod_le_pow_card _ _ 3 fun H _ => ((hmemS _).mp H.2).1.le
        _ = 3 ^ S.card := by rw [Fintype.card_coe]
    by_contra hlt
    have h81 : 3 ^ S.card ≤ 81 :=
      (Nat.pow_le_pow_right (by norm_num) (by omega : S.card ≤ 4)).trans (by norm_num)
    omega
  have hbk : ∀ k a v, rep ρ (β k a) (b k v) = b k (rep ρ a v) := by
    intro k a v
    rw [rep_apply, rep_apply, ← hb k a, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact congrArg (b k) (congrArg (ρ a) ((b k).symm_apply_apply v))
  have hdmap : ∀ k H,
      Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) (H.map (β k).toMonoidHom)) =
        Module.finrank (ZMod 2) (LemmaW.weightSpace (rep ρ) H) := fun k H =>
    LemmaW.finrank_weightSpace_map (rep ρ) hA3 (hbk k) H
  have hSmap : ∀ k, ∀ H ∈ S, H.map (β k).toMonoidHom ∈ S := by
    intro k H hH
    obtain ⟨hidx, hne⟩ := (hmemS H).mp hH
    refine (hmemS _).mpr ⟨(Subgroup.index_map_equiv H (β k)).trans hidx, fun hbot => hne ?_⟩
    have h0 := hdmap k H
    rw [hbot, finrank_bot] at h0
    exact Submodule.finrank_eq_zero.mp h0.symm
  have hker : ψ.ker = Subgroup.zpowers θ := by
    ext a
    rw [MonoidHom.mem_ker]
    exact hψk a
  have hcard6 : S.card = 6 := by
    have hle := card_le_six hsum h2
    rcases (show S.card = 5 ∨ S.card = 6 by omega) with h5 | h6
    · exact (false_of_card_five hA3 (ne_one_of_eq_theta0e hθ) ψ hψs hker β hψβ S
        (fun H hH => ((hmemS H).mp hH).1) hSθ hSmap _ hdmap hsum h2 hev h5).elim
    · exact h6
  have hd2 := eq_two_of_card_six hsum h2 hcard6
  let e : Fin 6 ≃ S := (Finset.equivFinOfCardEq hcard6).symm
  refine ⟨fun i => (e i : Subgroup A), fun i => ((hmemS _).mp (e i).2).1, fun i => hSθ _ (e i).2,
    fun _ _ hij => e.injective (Subtype.ext hij), fun i => hd2 _ (e i).2, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← LemmaW.iSup_weightFamily (rep ρ) hA3]
    refine iSup_le fun o => ?_
    rcases o with _ | H
    · rw [LemmaW.weightFamily_none (rep ρ) hA3, fixedSpace_top_eq_bot hθ]
      exact bot_le
    · rw [LemmaW.weightFamily_some]
      by_cases hbot : LemmaW.weightSpace (rep ρ) H.1 = ⊥
      · rw [hbot]
        exact bot_le
      · have hmem : H.1 ∈ S := (hmemS _).mpr ⟨H.2, hbot⟩
        refine le_trans (le_of_eq ?_) (le_iSup _ (e.symm ⟨H.1, hmem⟩))
        simp
  · intro H' hidx hne
    exact ⟨e.symm ⟨H', (hmemS _).mpr ⟨hidx, hne⟩⟩, by simp⟩
  · intro k i
    exact ⟨e.symm ⟨_, hSmap k _ (e i).2⟩, by simp⟩

end CFSG.GF2Type.Smith1979.IdxFour
