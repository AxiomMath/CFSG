module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyCover3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Inner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Outer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOffenderAssembly

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank CFSG.Quasithin

section Small

theorem exists_natCast_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = p) (k : K) : ∃ n : ℕ, (n : K) = k := by
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hbij : Function.Bijective f :=
    f.injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])
  obtain ⟨m, rfl⟩ := hbij.2 k
  refine ⟨m.val, ?_⟩
  rw [← map_natCast f m.val, ZMod.natCast_zmod_val]

theorem center_cube {K : Type} [Field K] {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) : x ^ 3 = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have h3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← hrx, ← map_pow, hr3, map_one]
  have := congrFun (congrFun h3 i) j
  rwa [← Matrix.SpecialLinearGroup.coe_pow] at this

theorem odd_card_of_pow_three {G : Type*} [Group G] [Finite G] (h : ∀ g : G, g ^ 3 = 1) :
    Odd (Nat.card G) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card G := by
    rw [Nat.not_odd_iff_even] at hne
    exact even_iff_two_dvd.1 hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h2
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at h3
  omega

theorem card_le_four_SL3 {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    (T : Subgroup (SpecialLinearGroup (Fin 3) K)) (hT : ∀ x ∈ T, x * x = 1) :
    Nat.card T ≤ 4 := by
  have h := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2
    (T.map Matrix.SpecialLinearGroup.toGL)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, hT x hx, map_one])
    (by rintro _ ⟨x, hx, rfl⟩; exact x.2)
  rwa [Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective] at h

end Small

section Model

theorem exists_coverData3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {W : Type} [CommGroup W]
    {Lb : Subgroup (MulAut W)} [Finite (MulAut W)] (hperf : Group.IsPerfect ↥Lb)
    (hodd : Odd (Nat.card (Subgroup.center ↥Lb))) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p)
    (e : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* StatedProj (StatedSL 3 K)) :
    Nonempty (CoverData3 K Lb) := by
  obtain ⟨φ', hφ's, hφ'c, hker⟩ := exists_cover_hom (ε := 1) (H := StatedSL 3 K) hp hp2
    (Or.inl ⟨rfl, hK, rfl⟩) hperf hodd e
  refine ⟨{ φ := φ'.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom
            surj := hφ's.comp (specialLinearGroupEquivStatedSL 3 K).surjective
            ker_central := ?_
            ψ := e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
              (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
            hψ := ?_ }⟩
  · intro g hg
    have h1 : specialLinearGroupEquivStatedSL 3 K g ∈ φ'.ker := hg
    have h2 := hker h1
    rw [← map_center_eq_statedScalars] at h2
    obtain ⟨g', hg', hg'g⟩ := h2
    have : g' = g := (specialLinearGroupEquivStatedSL 3 K).injective hg'g
    rwa [← this]
  · intro g
    have h1 := hφ'c (specialLinearGroupEquivStatedSL 3 K g)
    show (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
      ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
        (e (QuotientGroup.mk (φ' (specialLinearGroupEquivStatedSL 3 K g))))) = proj 3 K g
    have h2 : e (QuotientGroup.mk (φ' (specialLinearGroupEquivStatedSL 3 K g))) =
        QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
          (specialLinearGroupEquivStatedSL 3 K g) := h1.symm
    rw [h2]
    have h3 : (projectiveSpecialLinearGroupEquivStatedProj 3 K)
        (QuotientGroup.mk g) = QuotientGroup.mk' _ (specialLinearGroupEquivStatedSL 3 K g) :=
      QuotientGroup.congr_mk' _ _ _ _ g
    rw [(MulEquiv.symm_apply_eq _).2 h3.symm]
    rfl

end Model

section Final

theorem primeLinearThreeExclusion : PrimeLinearThreeExclusionProp := by
  classical
  intro p hp hp2 W _ _ hW Lb hperf hirr hmod B hBN hB1 hB2
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hKp : Nat.card K = p := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p := by rw [← Nat.card_eq_fintype_card]; exact hKp
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by rw [pow_one]; exact hKcard)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hoddK : Odd (Fintype.card K) := by rw [hKcard]; exact hpodd
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hKprime : ∀ k : K, ∃ n : ℕ, (n : K) = k := exists_natCast_of_card_prime hKp
  have hσ : ∀ σ : K ≃+* K, σ = 1 := fun σ => RingEquiv.ext fun k => by
    obtain ⟨n, rfl⟩ := hKprime k
    simp
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  obtain ⟨D⟩ := exists_coverData3 hp hp2 hperf hodd hKp e
  have hkerodd : Odd (Nat.card D.φ.ker) :=
    odd_card_of_pow_three fun g => Subtype.ext (by simpa using center_cube (D.ker_central g.1 g.2))
  let ρ₀ : SpecialLinearGroup (Fin 3) K →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    binaryLin.comp (Lb.subtype.comp D.φ)
  have hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro g hg
    have h1 : (D.φ g : MulAut W) = 1 := binaryLin_injective (by rw [map_one]; exact hg)
    exact D.ker_central g (MonoidHom.mem_ker.2 (Subtype.ext h1))
  have hB2' : ∀ a ∈ B, a * a = 1 := fun a ha => by
    have := hB2.2 a ha
    rwa [pow_two] at this
  have hbN : ∀ a ∈ B, a ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := fun a ha => hBN ha
  have hin : ∀ t ∈ B, t ∈ Lb → t ≠ 1 →
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin t))) := by
    intro t htB htL ht1
    obtain ⟨g, hg2, hgt⟩ := exists_involution_lift D.φ hkerodd (t := (⟨t, htL⟩ : ↥Lb))
      (Subtype.ext (hB2' t htB)) (MonoidHom.mem_range.2 (D.surj _))
    have hg1 : g ≠ 1 := fun h => ht1 (by
      have := hgt
      rw [h, map_one] at this
      exact congrArg Subtype.val this.symm)
    have h4 := inner_rank_ge_four ρ₀ h2 hKprime hoddK hρ hg2 hg1
    have e1 : ρ₀ g = binaryLin t := by simp [ρ₀, hgt]
    rwa [e1] at h4
  have hcard : ∀ T : Subgroup (MulAut W), T ≤ B → T ≤ Lb → Nat.card T ≤ 4 := by
    intro T hTB hTL
    have hcT : Nat.card (T.subgroupOf Lb) ≤ 4 := by
      refine card_le_of_lifts D.φ (fun g hg h => ?_) hkerodd 4
        (fun T' hT' => card_le_four_SL3 h2 T' hT') (T.subgroupOf Lb)
        (fun x _ => MonoidHom.mem_range.2 (D.surj x)) (fun x hx => ?_) (fun x hx y hy => ?_)
      · exact (Subgroup.mem_center_iff.1 (D.ker_central g hg) h).symm
      · exact Subtype.ext (hB2' _ (hTB hx))
      · exact Subtype.ext (hB2.1 _ (hTB hx) _ (hTB hy))
    have : Nat.card (T.subgroupOf Lb) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    omega
  have hout : ∀ a ∈ B, a ∉ Lb →
      2 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin a))) := by
    intro a haB haL
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a haB) (hB2' a haB) with h | ⟨A, hA, hβ⟩
    · exact absurd h haL
    · exact D.outer_rank h2 hKprime hoddK hperfSL (hbN a haB) (hB2' a haB) A hA hβ
  have hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ Lb → a' ∉ Lb → a * a' ∈ Lb := by
    intro a haB a' ha'B haL ha'L
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a haB) (hB2' a haB) with h | ⟨A, -, hβ⟩
    · exact absurd h haL
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a' ha'B) (hB2' a' ha'B) with
      h' | ⟨A', -, hβ'⟩
    · exact absurd h' ha'L
    have hsq : a * a' * (a * a') = 1 := by
      calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hB2.1 a' ha'B a haB]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [hB2' a haB, hB2' a' ha'B, one_mul]
    exact D.mul_mem_of_dual hperfSL hW hirr.2 hodd (hbN a haB) (hbN a' ha'B) hβ hβ' hsq
  by_contra hne
  push Not at hne
  let F : Submodule (ZMod 2) (Additive W) :=
    { carrier := {x | ∀ a ∈ B, binaryLin a x = x}
      add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
      zero_mem' := fun a _ => map_zero _
      smul_mem' := fun c x hx a ha => by rw [map_smul, hx a ha] }
  have hfix : Nat.card F = Nat.card (fixV B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => congrArg Additive.toMul (x.2 a ha)⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun a ha => congrArg Additive.ofMul (w.2 a ha)⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
  have hpgrp : IsPGroup 2 B := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hB2.2 a a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : Module.finrank (ZMod 2) (Additive W) - Module.finrank (ZMod 2) F ≤
      Nat.log 2 (Nat.card B) := by
    refine finrank_sub_le_log_of_card_le F hk ?_
    rw [hcardE, hfix]
    exact hne
  exact no_offender_of_ranks binaryLin Lb B hB1 F (fun a ha x hx => hx a ha) hin hcard hout hidx
    hoff

end Final

end CFSG.QuasithinUnique.Setup.Family
