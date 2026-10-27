module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescentPhi
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ChainsInput

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
open CFSG.LieType.Ree (ReeTag)

local instance f4DescNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem f4Desc_supp02 :
    ∀ q : Fin 48, 24 ≤ (q : ℕ) → orbitCertRoot .F4 q 1 = 0 → orbitCertRoot .F4 q 3 = 0 →
      orbitCertRoot .F4 q ≠ Pi.single 0 1 → ∀ l : Fin Tag.F4.rank, l ∉ [2] →
        orbitCertRoot .F4 q l = 0 := by
  decide +kernel

theorem f4Desc_single_eq :
    (Pi.single 0 1 : Fin Tag.F4.rank → ℤ) = orbitCertRoot .F4 33 ∧
      (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = orbitCertRoot .F4 27 ∧
      (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) = orbitCertRoot .F4 25 := by
  decide +kernel

theorem f4DescCandidates_eq : f4DescCandidates = f4FrameCandidates := rfl

variable {K : Type} [Field K]

section Small



theorem f4Desc_eq_pinnedX_of_mem_single {i : Fin Tag.F4.rank} {z : ModGL .F4 K}
    (hz : z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ [i]})) :
    ∃ a : K, z = pinnedX .F4 K (Pi.single i 1) a := by
  obtain ⟨a, u, hu, rfl⟩ := classDescent_exists_pinnedX_mul (J := {j | j ∈ [i]}) (i := i)
    (by simp) hz
  have hS : parabolicPosRoots .F4 {j | j ∈ [i]} \ {Pi.single i 1} = ∅ := by
    ext δ
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]
    intro hδ
    have hnn := (IsRoot.height_pos_iff hδ.2.1).1 hδ.2.2
    have he : δ = (δ i) • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) := funext fun l => by
      by_cases hl : l = i
      · subst hl
        simp
      · rw [hδ.1.2 l (by simpa using hl)]
        simp [hl]
    have hr := hδ.1.1
    rw [he] at hr
    rcases (isRoot_smul_single_iff i (δ i)).1 hr with h1 | h1
    · rw [he, h1, one_smul]
    · have := hnn i
      omega
  rw [hS] at hu
  have hu1 : u = 1 := by
    have hbot : rootSpan .F4 K (∅ : Set (Fin Tag.F4.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rw [hbot] at hu
    exact Subgroup.mem_bot.1 hu
  exact ⟨a, by rw [hu1, mul_one]⟩

theorem f4Desc_eq_mul_of_mem_02 {z : ModGL .F4 K}
    (hz : z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ [0, 2]})) :
    ∃ a b : K, z = pinnedX .F4 K (Pi.single 0 1) a * pinnedX .F4 K (Pi.single 2 1) b := by
  obtain ⟨a, u, hu, rfl⟩ := classDescent_exists_pinnedX_mul (J := {j | j ∈ [0, 2]}) (i := 0)
    (by simp) hz
  have hsub : parabolicPosRoots .F4 {j | j ∈ [0, 2]} \ {Pi.single 0 1} ⊆
      parabolicPosRoots .F4 {j | j ∈ [2]} := by
    rintro δ ⟨hδ, hδ0⟩
    obtain ⟨q, hq, hq', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 _).1 hδ.2
    have h1 : orbitCertRoot .F4 q 1 = 0 := hδ.1.2 1 (by decide)
    have h3 : orbitCertRoot .F4 q 3 = 0 := hδ.1.2 3 (by decide)
    exact ⟨⟨hδ.1.1, fun l hl => f4Desc_supp02 ⟨q, by omega⟩ hq h1 h3
      (fun h => hδ0 (Set.mem_singleton_iff.2 h)) l hl⟩, hδ.2⟩
  obtain ⟨b, hb⟩ := f4Desc_eq_pinnedX_of_mem_single (classDescent_rootSpan_mono hsub hu)
  exact ⟨a, b, by rw [hb]⟩

end Small

variable [Finite K] [CharP K 2]

theorem f4DescGood_L3 {F : List ℕ} (hF : F = [47, 32, 30] ∨ F = [44, 35, 30]) {z : ModGL .F4 K}
    (hz : z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ [1]})) :
    F4DescGood K (f4DescProd K F * z) := by
  obtain ⟨a, rfl⟩ := f4Desc_eq_pinnedX_of_mem_single hz
  rw [f4Desc_single_eq.2.1]
  by_cases ha : a = 0
  · rw [ha, pinnedX_zero, mul_one]
    rcases hF with rfl | rfl <;> exact f4DescGood_of_mem (by decide)
  · have key : F4DescGood K (f4DescProd K F * f4x K 27 a * 1) := by
      refine f4DescGood_of_torus (by norm_num) ?_ ha (S := ∅) (by simp) (one_mem _) ?_
      · rcases hF with rfl | rfl <;> decide +kernel
      · rw [mul_one]
        rcases hF with rfl | rfl <;> exact f4DescGood_of_mem (by decide)
    rw [mul_one] at key
    exact key

theorem f4DescGood_L2' {z : ModGL .F4 K}
    (hz : z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ [0, 2]})) :
    F4DescGood K (f4DescProd K [44, 40] * z) := by
  obtain ⟨a, b, rfl⟩ := f4Desc_eq_mul_of_mem_02 hz
  rw [f4Desc_single_eq.1, f4Desc_single_eq.2.2]
  have hb : ∀ F : List ℕ, (F = [44, 40] ∨ F = [44, 40, 33]) →
      F4DescGood K (f4DescProd K F * pinnedX .F4 K (orbitCertRoot .F4 25) b) := by
    intro F hF
    by_cases hb0 : b = 0
    · rw [hb0, pinnedX_zero, mul_one]
      rcases hF with rfl | rfl <;> exact f4DescGood_of_mem (by decide)
    · have key : F4DescGood K (f4DescProd K F * f4x K 25 b * 1) := by
        refine f4DescGood_of_torus (by norm_num) ?_ hb0 (S := ∅) (by simp) (one_mem _) ?_
        · rcases hF with rfl | rfl <;> decide +kernel
        · rw [mul_one]
          rcases hF with rfl | rfl <;> exact f4DescGood_of_mem (by decide)
      rw [mul_one] at key
      exact key
  by_cases ha0 : a = 0
  · rw [ha0, pinnedX_zero, one_mul]
    exact hb _ (Or.inl rfl)
  · rw [← mul_assoc]
    exact f4DescGood_of_torus (S := {orbitCertRoot .F4 25}) (by norm_num) (by decide +kernel) ha0
      (fun δ hδ => by
        rw [Set.mem_singleton_iff.1 hδ]
        exact ⟨(f4_isRoot_pos (by norm_num)).1, by decide +kernel⟩)
      (classKill_pinnedX_mem (Set.mem_singleton _) b) (hb _ (Or.inr rfl))

theorem f4DescGood_L2 {ℓ : ModGL .F4 K}
    (hℓ : ℓ ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ [1, 2]})) (h2 : ℓ ^ 2 = 1) :
    F4DescGood K (f4DescProd K [47, 32] * ℓ) := by
  by_cases h1 : ℓ = 1
  · rw [h1, mul_one]
    exact f4DescGood_of_mem (by decide)
  refine f4DescGood_of_level [1, 2] [47, 32] (by decide +kernel)
    (fun i hi c hc u hu h2' => ?_) hℓ h2 h1
  by_cases hlong : i ∈ classKillLongSimple .F4
  · exact f4DescGood_of_long [1, 2] [47, 32] 30 [1] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (fun z hz _ => f4DescGood_L3 (Or.inl rfl) hz) hi hlong hc hu h2'
  · exact f4DescGood_of_short [1, 2] [1, 2] (by decide) [47, 32] [44, 35]
      f4Desc_phi_f4DescProd_47_32
      (fun i₂ hi₂ hlong₂ c₂ hc₂ u₂ hu₂ h2₂ => f4DescGood_of_long [1, 2] [44, 35] 30 [1]
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (fun z hz _ => f4DescGood_L3 (Or.inr rfl) hz) hi₂ hlong₂ hc₂ hu₂ h2₂)
      hi hlong hc hu h2'

theorem f4DescGood_L1' : ∀ i₂ ∈ ([0, 1, 2] : List (Fin Tag.F4.rank)),
    i₂ ∈ classKillLongSimple .F4 → ∀ c₂ : K, c₂ ≠ 0 →
      ∀ u₂ ∈ rootSpan .F4 K
          (parabolicPosRoots .F4 {j | j ∈ ([0, 1, 2] : List (Fin Tag.F4.rank))} \
            {Pi.single i₂ 1}),
        (pinnedX .F4 K (Pi.single i₂ 1) c₂ * u₂) ^ 2 = 1 →
          F4DescGood K (f4DescProd K [44] * (pinnedX .F4 K (Pi.single i₂ 1) c₂ * u₂)) :=
  fun _ hi₂ hlong₂ _ hc₂ _ hu₂ h2₂ => f4DescGood_of_long [0, 1, 2] [44] 40 [0, 2]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ hz _ => f4DescGood_L2' hz) hi₂ hlong₂ hc₂ hu₂ h2₂

theorem f4DescGood_L1 {ℓ : ModGL .F4 K}
    (hℓ : ℓ ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ [1, 2, 3]})) (h2 : ℓ ^ 2 = 1) :
    F4DescGood K (f4DescProd K [47] * ℓ) := by
  by_cases h1 : ℓ = 1
  · rw [h1, mul_one]
    exact f4DescGood_of_mem (by decide)
  refine f4DescGood_of_level [1, 2, 3] [47] (by decide +kernel)
    (fun i hi c hc u hu h2' => ?_) hℓ h2 h1
  by_cases hlong : i ∈ classKillLongSimple .F4
  · exact f4DescGood_of_long [1, 2, 3] [47] 32 [1, 2] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (fun z hz hz2 => f4DescGood_L2 hz hz2) hi hlong hc hu h2'
  · exact f4DescGood_of_short [1, 2, 3] [0, 1, 2] (by decide) [47] [44]
      f4Desc_phi_f4DescProd_47 f4DescGood_L1' hi hlong hc hu h2'

theorem f4DescGood_of_mem_posUnipotent {ℓ : ModGL .F4 K} (hℓ : ℓ ∈ posUnipotent .F4 K)
    (h2 : ℓ ^ 2 = 1) (h1 : ℓ ≠ 1) : F4DescGood K ℓ := by
  have hℓ' : ℓ ∈ rootSpan .F4 K
      (parabolicPosRoots .F4 {j | j ∈ List.finRange Tag.F4.rank}) := by
    rw [cascade_parabolicPosRoots_finRange]
    exact hℓ
  have hcont : ∀ z ∈ rootSpan .F4 K (parabolicPosRoots .F4 {j | j ∈ [1, 2, 3]}), z ^ 2 = 1 →
      F4DescGood K (f4DescProd K ([] ++ [47]) * z) := fun _ hz hz2 => f4DescGood_L1 hz hz2
  have key : F4DescGood K (f4DescProd K [] * ℓ) := by
    refine f4DescGood_of_level (List.finRange Tag.F4.rank) [] (by decide)
      (fun i hi c hc u hu h2' => ?_) hℓ' h2 h1
    by_cases hlong : i ∈ classKillLongSimple .F4
    · exact f4DescGood_of_long _ [] 47 [1, 2, 3] (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hcont hi hlong hc hu h2'
    · exact f4DescGood_of_short (List.finRange Tag.F4.rank) (List.finRange Tag.F4.rank)
        (by decide) [] [] f4Desc_phi_f4DescProd_nil
        (fun _ hi₂ hlong₂ _ hc₂ _ hu₂ h2₂ => f4DescGood_of_long _ [] 47 [1, 2, 3]
          (by decide +kernel) (by decide +kernel) (by decide +kernel) hcont hi₂ hlong₂ hc₂ hu₂
          h2₂)
        hi hlong hc hu h2'
  simpa [f4DescProd] using key

theorem f4DescGood_of_sq_eq_one {t : adjointGroup .F4 K} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    F4DescGood K (t : ModGL .F4 K) := by
  obtain ⟨g, hg⟩ := cascade_exists_conj_mem_posUnipotent ht
  have h2 : ((g * t * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, conj_pow, ht, mul_one, mul_inv_cancel, Subgroup.coe_one]
  have h1 : ((g * t * g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ≠ 1 := by
    intro h
    apply ht1
    have h' : g * t * g⁻¹ = 1 := Subtype.ext h
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  have key := f4DescGood_of_mem_posUnipotent hg h2 h1
  refine F4DescGood.of_conj (g := (g : ModGL .F4 K)) g.2 t.2 ?_
  simpa using key

theorem exists_mulAut_eq_f4DescProd {t : adjointGroup .F4 K} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ ψ : MulAut (adjointGroup .F4 K), ∃ L ∈ f4DescCandidates,
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = (L.map fun p => f4x K p 1).prod := by
  obtain ⟨hx, ψ, L, hL, he⟩ := f4DescGood_of_sq_eq_one ht ht1
  exact ⟨ψ, L, hL, he⟩

theorem exists_mulAut_eq_f4_candidate {t : adjointGroup .F4 K} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ ψ : MulAut (adjointGroup .F4 K),
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 47 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 47 1 * f4x K 32 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 47 1 * f4x K 32 1 * f4x K 30 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) =
        f4x K 47 1 * f4x K 32 1 * f4x K 30 1 * f4x K 27 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 44 1 * f4x K 35 1 * f4x K 30 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) =
        f4x K 44 1 * f4x K 35 1 * f4x K 30 1 * f4x K 27 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 44 1 * f4x K 40 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 44 1 * f4x K 40 1 * f4x K 33 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 44 1 * f4x K 40 1 * f4x K 25 1 ∨
      ((ψ t : adjointGroup .F4 K) : ModGL .F4 K) =
        f4x K 44 1 * f4x K 40 1 * f4x K 33 1 * f4x K 25 1 := by
  obtain ⟨ψ, L, hL, he⟩ := exists_mulAut_eq_f4DescProd ht ht1
  refine ⟨ψ, ?_⟩
  simp only [f4DescCandidates, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at he <;>
    simp only [he, mul_assoc] <;> simp

omit [CharP K 2] in
theorem f4Desc_sq_eq_one_of_orderOf_conj {x : adjointGroup .F4 K}
    (hx : orderOf (MulAut.conj x) = 2) : x ^ 2 = 1 ∧ x ≠ 1 := by
  refine ⟨?_, fun h => by rw [h, map_one, orderOf_one] at hx; exact absurd hx (by decide)⟩
  have h := pow_orderOf_eq_one (MulAut.conj x)
  rw [hx, ← map_pow] at h
  have hc : x ^ 2 ∈ Subgroup.center (adjointGroup .F4 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut (adjointGroup .F4 K) => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x ^ 2 = x ^ 2 * g * (x ^ 2)⁻¹ * x ^ 2 := by rw [this]
      _ = x ^ 2 * g := by group
  rw [center_adjointGroup_eq_bot] at hc
  exact Subgroup.mem_bot.1 hc

theorem f4ClassDescent_hfr : ∀ x : adjointGroup .F4 K, orderOf (MulAut.conj x) = 2 →
    ∃ ψ : MulAut (adjointGroup .F4 K), ∃ y : adjointGroup .F4 K, ψ y = x ∧
      ∃ L ∈ f4FrameCandidates, ∃ e : (Fin Tag.F4.rank → ℤ) → K,
        (∀ p ∈ L, e (orbitCertRoot .F4 p) ≠ 0) ∧
          (y : ModGL .F4 K) = (L.map fun p => f4x K p (e (orbitCertRoot .F4 p))).prod := by
  intro x hx
  obtain ⟨hx2, hx1⟩ := f4Desc_sq_eq_one_of_orderOf_conj hx
  obtain ⟨hy, ψ, L, hL, he⟩ := f4DescGood_of_sq_eq_one hx2 hx1
  have hψ : ψ x = ⟨f4DescProd K L, f4DescProd_mem_adjointGroup L⟩ := Subtype.ext he
  refine ⟨ψ⁻¹, ⟨f4DescProd K L, f4DescProd_mem_adjointGroup L⟩, ?_, L,
    f4DescCandidates_eq ▸ hL, fun _ => 1, fun _ _ => one_ne_zero, rfl⟩
  rw [← hψ]
  exact ψ.symm_apply_apply x

theorem innerInvolutionInput_F4 : InnerInvolutionInput (adjointGroup .F4 K) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact innerInvolutionInput_F4_of_frameCandidates (f := n) n.pos
    (by rw [Nat.card_eq_fintype_card, hn]) f4ClassDescent_hfr

omit [Finite K] [CharP K 2] in
theorem innerInvolutionInput_F4' {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    InnerInvolutionInput (adjointGroup .F4 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact innerInvolutionInput_F4

end CFSG.SeitzReduction
