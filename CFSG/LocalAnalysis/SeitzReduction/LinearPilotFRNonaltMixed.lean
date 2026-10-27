module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore perfectCore_le)

section Transport

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

open Nonalt in
theorem comap_map_le_coreRadical {G : Type*} [Group G] {φ₁ φ₂ : projectiveSL n K →* G}
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ} (hr : n = 2 * r + 2)
    (hr1 : 1 ≤ r) (hφ₂ : Function.Injective φ₂) {Λ T : Subgroup (projectiveSL n K)}
    (hΛX : Λ.map φ₁ = (perfectCore (autFixSubgroup (dualAut n K))).map φ₂)
    (hT : IsPGroup 2 T) (hTΛ : T ≤ Λ) (hN : Λ ≤ normalizer (T : Set (projectiveSL n K))) :
    (T.map φ₁).comap φ₂ ≤ coreRadical K ⟨0, by omega⟩ := by
  obtain ⟨-, -, -, hmax, -⟩ := coreRadical_spec hK hq hr hr1 (⟨0, by omega⟩ : Fin n)
  exact hmax _ (isPGroup_comap_map hφ₂ hT) (comap_map_le hφ₂ hΛX hTΛ)
    (le_normalizer_comap_map hΛX hN)

open Nonalt in
theorem card_le_of_map_eq {G : Type*} [Group G] {φ₁ φ₂ : projectiveSL n K →* G}
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ} (hr : n = 2 * r + 2)
    (hr1 : 1 ≤ r) (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    {Λ T : Subgroup (projectiveSL n K)}
    (hΛX : Λ.map φ₁ = (perfectCore (autFixSubgroup (dualAut n K))).map φ₂)
    (hT : IsPGroup 2 T) (hTΛ : T ≤ Λ) (hN : Λ ≤ normalizer (T : Set (projectiveSL n K))) :
    Nat.card T ≤ Nat.card K ^ (n - 1) := by
  have hle := comap_map_le_coreRadical hK hq hr hr1 hφ₂ hΛX hT hTΛ hN
  have hcard : Nat.card ((T.map φ₁).comap φ₂) = Nat.card T := by
    rw [← card_map_of_injective hφ₂, map_comap_map_eq hΛX hTΛ, card_map_of_injective hφ₁]
  rw [← hcard]
  exact (Subgroup.card_le_of_le hle).trans (card_coreRadical_le ⟨r + 1, by omega⟩ _)

open Nonalt in
theorem commutator_eq_bot_of_map_eq {G : Type*} [Group G] {φ₁ φ₂ : projectiveSL n K →* G}
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {r : ℕ} (hr : n = 2 * r + 2)
    (hr1 : 1 ≤ r) (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    {Λ T : Subgroup (projectiveSL n K)}
    (hΛX : Λ.map φ₁ = (perfectCore (autFixSubgroup (dualAut n K))).map φ₂)
    (hT : IsPGroup 2 T) (hTΛ : T ≤ Λ) (hN : Λ ≤ normalizer (T : Set (projectiveSL n K))) :
    ⁅T, T⁆ = ⊥ := by
  have hle := comap_map_le_coreRadical hK hq hr hr1 hφ₂ hΛX hT hTΛ hN
  set T' := (T.map φ₁).comap φ₂ with hT'
  have hT'T' : ⁅T', T'⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact coreRadical_comm ⟨r + 1, by omega⟩ (hle hy) (hle hx)
  have h := map_commutator_comap_map hΛX hTΛ
  rw [← hT', hT'T', Subgroup.map_bot] at h
  exact (map_eq_bot_iff_of_injective _ hφ₁).1 h.symm

end Transport

section TwoLe

variable {n k : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldRigidIn_inner_nonalt_of_two_le_free {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) {r : ℕ} (hr : n = 2 * r + 2) (hr1 : 1 ≤ r)
    (P : InvPlacement n k) (hP : P.elt K ≠ 1) (hJ : 2 ≤ P.free.card) :
    FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (autFixSubgroup (dualAut n K))) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hΛX γ β₁ β₂ hβX h₁ h₂
  exfalso
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)
  obtain ⟨hQp, hΛeq, -, hMN, -⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ)
  have hQΛ : P.radicalP K ≤ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
    rw [hΛeq]
    exact le_sup_left
  have hΛN : perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
      normalizer (P.radicalP K : Set (projectiveSL n K)) := by
    rw [hΛeq]
    exact sup_le le_normalizer hMN
  obtain ⟨j, hj⟩ : P.free.Nonempty := Finset.card_pos.1 (by omega)
  exact P.commutator_radicalP_ne_bot hk ⟨j, hj⟩
    (commutator_eq_bot_of_map_eq hK hq hr hr1 hφ₁ hφ₂ hΛX hQp hQΛ hΛN)

end TwoLe

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type} [Field K]

@[expose] def offDiagMat (g : (Finset.univ : Finset (Fin k)).offDiag → K) :
    Matrix (Fin n) (Fin n) K :=
  ∑ p, single (P.u p.1.1) (P.w p.1.2) (g p)

theorem offDiagMat_mul (g g' : (Finset.univ : Finset (Fin k)).offDiag → K) :
    P.offDiagMat g * P.offDiagMat g' = 0 := by
  rw [offDiagMat, offDiagMat, Finset.sum_mul]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun p' _ => ?_
  exact single_mul_single_of_ne _ _ _ _ (P.u_ne_w p'.1.1 p.1.2).symm _

theorem offDiagMat_add (g g' : (Finset.univ : Finset (Fin k)).offDiag → K) :
    P.offDiagMat (g + g') = P.offDiagMat g + P.offDiagMat g' := by
  rw [offDiagMat, offDiagMat, offDiagMat, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Pi.add_apply]
  ext a b
  rw [Matrix.add_apply]
  simp only [single, of_apply]
  split_ifs <;> simp

theorem offDiagMat_apply (g : (Finset.univ : Finset (Fin k)).offDiag → K)
    (p : (Finset.univ : Finset (Fin k)).offDiag) :
    P.offDiagMat g (P.u p.1.1) (P.w p.1.2) = g p := by
  rw [offDiagMat, Matrix.sum_apply, Finset.sum_eq_single p]
  · exact single_apply_same _ _ _
  · intro p' _ hp'
    apply single_apply_of_ne
    rintro ⟨h1, h2⟩
    apply hp'
    apply Subtype.ext
    exact Prod.ext (P.u_injective h1) (P.w_injective h2)
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem offDiagMat_single (p : (Finset.univ : Finset (Fin k)).offDiag) (c : K) :
    P.offDiagMat (Pi.single p c) = single (P.u p.1.1) (P.w p.1.2) c := by
  rw [offDiagMat, Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro p' _ hp'
    rw [Pi.single_eq_of_ne hp', single_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

variable [CharP K 2]

omit [CharP K 2] in
theorem one_add_offDiagMat_mul (g g' : (Finset.univ : Finset (Fin k)).offDiag → K) :
    (1 + P.offDiagMat g) * (1 + P.offDiagMat g') = 1 + P.offDiagMat (g + g') := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, P.offDiagMat_mul,
    add_zero, P.offDiagMat_add]
  abel

theorem det_one_add_offDiagMat (g : (Finset.univ : Finset (Fin k)).offDiag → K) :
    (1 + P.offDiagMat g).det = 1 := by
  have h := congrArg Matrix.det (P.one_add_offDiagMat_mul g g)
  have hgg : g + g = 0 := funext fun p => CharTwo.add_self_eq_zero (g p)
  rw [hgg, det_mul] at h
  have h0 : P.offDiagMat (0 : (Finset.univ : Finset (Fin k)).offDiag → K) = 0 := by
    rw [offDiagMat]
    simp
  rw [h0, add_zero, det_one] at h
  have h1 : ((1 + P.offDiagMat g).det - 1) ^ 2 = 0 := by
    have e : ((1 + P.offDiagMat g).det - 1) ^ 2 =
        (1 + P.offDiagMat g).det * (1 + P.offDiagMat g).det - 1 -
          2 * ((1 + P.offDiagMat g).det - 1) := by ring
    rw [e, h, CharTwo.two_eq_zero]
    ring
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)

@[expose] def offDiagSL (g : (Finset.univ : Finset (Fin k)).offDiag → K) :
    SpecialLinearGroup (Fin n) K :=
  ⟨1 + P.offDiagMat g, P.det_one_add_offDiagMat g⟩

theorem offDiagSL_add (g g' : (Finset.univ : Finset (Fin k)).offDiag → K) :
    P.offDiagSL (g + g') = P.offDiagSL g * P.offDiagSL g' :=
  Subtype.ext (P.one_add_offDiagMat_mul g g').symm

theorem offDiagSL_single (p : (Finset.univ : Finset (Fin k)).offDiag) (c : K) :
    P.offDiagSL (Pi.single p c) =
      SpecialLinearGroup.transvection (P.u_ne_w p.1.1 p.1.2) c := by
  apply Subtype.ext
  change 1 + P.offDiagMat (Pi.single p c) = _
  rw [P.offDiagMat_single, SpecialLinearGroup.transvection_coe]

theorem proj_offDiagSL_injective :
    Function.Injective fun g : (Finset.univ : Finset (Fin k)).offDiag → K =>
      proj n K (P.offDiagSL g) := by
  intro g g' h
  have hsq : ∀ g : (Finset.univ : Finset (Fin k)).offDiag → K, P.offDiagSL g * P.offDiagSL g = 1 :=
    fun g => by
      rw [← P.offDiagSL_add]
      have hgg : g + g = 0 := funext fun p => CharTwo.add_self_eq_zero (g p)
      rw [hgg]
      apply Subtype.ext
      change 1 + P.offDiagMat 0 = 1
      rw [offDiagMat]
      simp
  obtain ⟨l, -, hl⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  rw [inv_eq_of_mul_eq_one_right (hsq g), ← P.offDiagSL_add] at hl
  funext p
  have he := congrFun (congrFun hl (P.u p.1.1)) (P.w p.1.2)
  change (1 + P.offDiagMat (g + g')) (P.u p.1.1) (P.w p.1.2) = _ at he
  rw [Matrix.add_apply, P.offDiagMat_apply, scalar_apply, diagonal_apply_ne _ (P.u_ne_w _ _),
    one_apply_ne (P.u_ne_w _ _), zero_add, Pi.add_apply] at he
  calc g p = g p + (g p + g' p) := by rw [he, add_zero]
    _ = g' p := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

variable [Finite K]

theorem proj_offDiagSL_mem (hq : 4 ≤ Nat.card K)
    (g : (Finset.univ : Finset (Fin k)).offDiag → K) :
    proj n K (P.offDiagSL g) ∈ P.coreRadicalP K := by
  have key : ∀ s : Finset (Finset.univ : Finset (Fin k)).offDiag,
      proj n K (P.offDiagSL (∑ p ∈ s, Pi.single p (g p))) ∈ P.coreRadicalP K := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      have h1 : P.offDiagSL (0 : (Finset.univ : Finset (Fin k)).offDiag → K) = 1 := by
        apply Subtype.ext
        change 1 + P.offDiagMat 0 = 1
        rw [offDiagMat]
        simp
      rw [h1, map_one]
      exact one_mem _
    | insert q s hq' ih =>
      rw [Finset.sum_insert hq', P.offDiagSL_add, map_mul, P.offDiagSL_single]
      have hab : q.1.1 ≠ q.1.2 := (Finset.mem_offDiag.1 q.2).2.2
      exact mul_mem (P.proj_transvection_u_w_mem_coreRadicalP hq hab _) ih
  have hg : ∑ p, Pi.single p (g p) = g := Finset.univ_sum_single g
  rw [← hg]
  exact key Finset.univ

theorem card_coreRadicalP_ge (hq : 4 ≤ Nat.card K) :
    Nat.card K ^ (k * k - k) ≤ Nat.card (P.coreRadicalP K) := by
  have hinj : Function.Injective fun g : (Finset.univ : Finset (Fin k)).offDiag → K =>
      (⟨proj n K (P.offDiagSL g), P.proj_offDiagSL_mem hq g⟩ : P.coreRadicalP K) :=
    fun g g' h => P.proj_offDiagSL_injective (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fun, Nat.card_eq_finsetCard, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_fin] at hcard

end InvPlacement

section FreeEmpty

variable {n k : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldRigidIn_inner_nonalt_of_free_eq_empty {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) {r : ℕ} (hr : n = 2 * r + 2) (hr2 : 2 ≤ r)
    (P : InvPlacement n k) (hJ : P.free = ∅) :
    FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (autFixSubgroup (dualAut n K))) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hΛX γ β₁ β₂ hβX h₁ h₂
  exfalso
  have hcard := P.card_free
  rw [hJ, Finset.card_empty] at hcard
  have h2k : 2 * k ≤ n := by
    have := Fintype.card_le_of_injective P.supp P.supp_injective
    simpa [two_mul] using this
  have hk : k = r + 1 := by omega
  obtain ⟨hQp, hQΛ, hΛN, -⟩ := P.coreRadicalP_spec hq (by omega) hJ
  have h1 := card_le_of_map_eq hK hq hr (by omega) hφ₁ hφ₂ hΛX hQp hQΛ hΛN
  have h2 := P.card_coreRadicalP_ge hq
  have hlt : n - 1 < k * k - k := by
    have e : k * k - k = (r + 1) * r := by
      rw [hk, ← Nat.mul_sub_one, Nat.add_sub_cancel]
    have e2 : (r + 1) * r = r * r + r := by ring
    have : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr2
    omega
  have h3 : Nat.card K ^ (n - 1) < Nat.card K ^ (k * k - k) :=
    Nat.pow_lt_pow_right (by omega) hlt
  omega

end FreeEmpty

end CFSG.SeitzReduction.LinearPilot
