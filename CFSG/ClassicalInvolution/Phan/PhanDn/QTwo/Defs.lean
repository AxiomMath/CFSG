module

public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.ClassicalInvolution.Phan.AutSU3
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenComb

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg Matrix

section Reverse

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def revSU3 : Su K p f 3 ≃* Su K p f 3 :=
  (fieldAutSU p f (unitaryInvolution K p f) 3).trans (MulAut.conj (swapElt K p f))

theorem rotSU_mul_fieldAutSU_mul_inv (A : Su K p f 2) :
    rotSU (unitaryInvolution K p f) * fieldAutSU p f (unitaryInvolution K p f) 2 A *
      (rotSU (unitaryInvolution K p f))⁻¹ = A := by
  set σ : K →+* K := (unitaryInvolution K p f : K →+* K)
  set M : Matrix (Fin 2) (Fin 2) K := ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have h := conj_w_eq_map σ M A.2.1 (by simpa [conjTr, σ] using A.2.2)
  have h' : rotMatInv * M * rotMat = M.map σ := h
  refine Subtype.ext (Units.ext ?_)
  change rotMat * M.map (unitaryInvolution K p f) * rotMatInv = M
  rw [show M.map (unitaryInvolution K p f) = M.map σ from rfl, ← h']
  calc rotMat * (rotMatInv * M * rotMat) * rotMatInv
      = (rotMat * rotMatInv) * M * (rotMat * rotMatInv) := by noncomm_ring
    _ = M := by rw [rotMat_mul_rotMatInv, Matrix.one_mul, Matrix.mul_one]

theorem revSU3_comp_embSUid_two :
    (revSU3 K p f).toMonoidHom.comp (embSUid (unitaryInvolution K p f) 2) =
      embSUid (unitaryInvolution K p f) 0 := by
  ext A
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, revSU3, MulEquiv.trans_apply,
    MulAut.conj_apply, swapElt]
  rw [fieldAutSU_embSUid, swapSU_mul_embSUid_two_mul_inv, rotSU_mul_fieldAutSU_mul_inv]

theorem revSU3_comp_embSUid_zero :
    (revSU3 K p f).toMonoidHom.comp (embSUid (unitaryInvolution K p f) 0) =
      embSUid (unitaryInvolution K p f) 2 := by
  ext A
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, revSU3, MulEquiv.trans_apply,
    MulAut.conj_apply, swapElt]
  rw [fieldAutSU_embSUid, swapSU_mul_embSUid_zero_mul_inv, rotSU_mul_fieldAutSU_mul_inv]

theorem revSU3_revSU3 (hK : Nat.card K = (p ^ f) ^ 2) (X : Su K p f 3) :
    revSU3 K p f (revSU3 K p f X) = X := by
  have hswap : fieldAutSU p f (unitaryInvolution K p f) 3 (swapElt K p f) = swapElt K p f := by
    refine Subtype.ext (Units.ext ?_)
    rw [coe_coe_fieldAutSU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapElt, swapSU, swapMat]
  have hcomp : fieldAutSU p f (unitaryInvolution K p f) 3
      (fieldAutSU p f (unitaryInvolution K p f) 3 X) = X := by
    refine Subtype.ext (Units.ext ?_)
    rw [coe_coe_fieldAutSU, coe_coe_fieldAutSU]
    ext i j
    simp only [Matrix.map_apply, unitaryInvolution_involutive hK]
  have hsq : swapElt K p f * swapElt K p f = 1 := by
    have h := mul_inv_cancel (swapElt K p f)
    rwa [swapElt_inv] at h
  simp only [revSU3, MulEquiv.trans_apply, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv, hswap, hcomp]
  rw [show swapElt K p f * (swapElt K p f * X * (swapElt K p f)⁻¹) *
      (swapElt K p f)⁻¹ =
      (swapElt K p f * swapElt K p f) * X * (swapElt K p f * swapElt K p f)⁻¹ from by group]
  rw [hsq]
  simp

end Reverse

structure QTwoWeakPhanSystemSL (K : Type) [Field K] [Finite K] [CharP K 2] {G : Type}
    [Group G] {n : ℕ} (M : CoxeterMatrix (Fin n)) (H : Subgroup G)
    (U : Fin n → Subgroup G) (W : Fin n → Fin n → Subgroup G) : Prop where
  card_four : Nat.card K = 4
  hlab : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3
  iso : ∀ i, Nonempty (Su K 2 1 2 ≃* U i)
  symm : ∀ i j, W i j = W j i
  join : ∀ i j, M i j = 2 → W i j = U i ⊔ U j
  comm : ∀ i j, M i j = 2 → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x
  pair : ∀ i j, M i j = 3 → UnitaryBlockStandardPair K 2 1 (W i j) (U i) (U j)
  gen : (⨆ (i) (j) (_ : i ≠ j), W i j) = H
  adjA3 : ∀ i j k, M i j = 3 → M j k = 3 → M i k = 2 →
    ∃ θ : Su K 2 1 4 →* G, θ.range = W i j ⊔ W j k
  farNodeEdge : ∀ i j k, M j k = 3 → M i j = 2 → M i k = 2 →
    ∀ x ∈ U i, ∀ y ∈ W j k, x * y = y * x
  farEdgeEdge : ∀ i k j l, M i k = 3 → M j l = 3 → M i j = 2 → M i l = 2 → M k j = 2 →
    M k l = 2 → ∀ x ∈ W i k, ∀ y ∈ W j l, x * y = y * x

abbrev QTwoWeakPhanSystemD (K : Type) [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
    (m : ℕ) (H : Subgroup G) (U : Fin m → Subgroup G) (W : Fin m → Fin m → Subgroup G) :=
  QTwoWeakPhanSystemSL K (CFSG.StandardType.ggCoxeterMatrixD m) H U W

theorem QTwoWeakPhanSystemSL.le_of_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] {n : ℕ} {M : CoxeterMatrix (Fin n)} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (h : QTwoWeakPhanSystemSL K M H U W) {i j : Fin n} (hij : M i j = 3) :
    U i ≤ W i j ∧ U j ≤ W i j := by
  obtain ⟨θ, c, hrange, -, h | h⟩ := h.pair i j hij
  · constructor
    · rw [← h.1, ← hrange]
      exact Subgroup.map_le_range _ _
    · rw [← h.2, ← hrange]
      exact Subgroup.map_le_range _ _
  · constructor
    · rw [← h.2, ← hrange]
      exact Subgroup.map_le_range _ _
    · rw [← h.1, ← hrange]
      exact Subgroup.map_le_range _ _

theorem QTwoWeakPhanSystemSL.iSup_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] {n : ℕ} {M : CoxeterMatrix (Fin n)} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (h : QTwoWeakPhanSystemSL K M H U W)
    (hnbr : ∀ i, ∃ j, M i j = 3) :
    (⨆ (i) (j) (_ : M i j = 3), W i j) = H := by
  rw [← h.gen]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    refine le_iSup_of_le i (le_iSup_of_le j (le_iSup (fun _ : i ≠ j => W i j) ?_))
    rintro rfl
    have h1 : M i i = 1 := M.diagonal i
    omega
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    rcases h.hlab i j hij with h2 | h3
    · rw [h.join i j h2]
      refine sup_le ?_ ?_
      · obtain ⟨k, hk⟩ := hnbr i
        have hik : i ≠ k := by
          rintro rfl
          have h1 : M i i = 1 := M.diagonal i
          omega
        refine le_trans (h.le_of_three hk).1 ?_
        exact le_iSup_of_le i (le_iSup_of_le k (le_iSup (fun _ : M i k = 3 => W i k) hk))
      · obtain ⟨l, hl⟩ := hnbr j
        have hjl : j ≠ l := by
          rintro rfl
          have h1 : M j j = 1 := M.diagonal j
          omega
        refine le_trans (h.le_of_three hl).1 ?_
        exact le_iSup_of_le j (le_iSup_of_le l (le_iSup (fun _ : M j l = 3 => W j l) hl))
    · exact le_iSup_of_le i (le_iSup_of_le j (le_iSup (fun _ : M i j = 3 => W i j) h3))

theorem QTwoWeakPhanSystemSL.ne_bot {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] {n : ℕ} {M : CoxeterMatrix (Fin n)} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (h : QTwoWeakPhanSystemSL K M H U W) (hn : 2 ≤ n) : H ≠ ⊥ := by
  intro hbot
  have hn0 : 0 < n := by omega
  let i : Fin n := ⟨0, hn0⟩
  obtain ⟨j, hji⟩ : ∃ j : Fin n, j ≠ i := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set (Fin n)) ⊆ {i} := fun x _ => hcon x
    have hcard : Nat.card (Fin n) ≤ 1 := by
      rw [← Set.ncard_univ (Fin n)]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by simp)
    rw [Nat.card_fin] at hcard
    omega
  have hij : i ≠ j := hji.symm
  have hmem : U i ≤ W i j := by
    rcases h.hlab i j hij with h2 | h3
    · rw [h.join i j h2]
      exact le_sup_left
    · exact (h.le_of_three h3).1
  have hle : W i j ≤ H := by
    rw [← h.gen]
    exact le_iSup_of_le i (le_iSup_of_le j (le_iSup (fun _ : i ≠ j => W i j) hij))
  have hU : U i ≠ ⊥ := by
    intro hUi
    obtain ⟨e⟩ := h.iso i
    have hrot : rotSU (unitaryInvolution K 2 1) ≠ 1 := by
      intro hr
      have h' : (0 : K) = 1 := by
        simpa [rotSU, rotMat] using congrArg
          (fun g : Su K 2 1 2 => (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0)) hr
      exact zero_ne_one h'
    have hsingle : Subsingleton (U i) := by rw [hUi]; infer_instance
    have heq : e (rotSU (unitaryInvolution K 2 1)) = 1 :=
      @Subsingleton.elim (U i) hsingle _ _
    exact hrot (e.injective (heq.trans (map_one e).symm))
  exact hU (le_bot_iff.mp (hmem.trans (hle.trans (le_of_eq hbot))))

@[expose] noncomputable def blk012 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Su K 2 1 3 →* Su K 2 1 4 :=
  blockEmb K 2 1 4 3 0 (by norm_num)

@[expose] noncomputable def blk123 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Su K 2 1 3 →* Su K 2 1 4 :=
  blockEmb K 2 1 4 3 1 (by norm_num)

structure QTwoPhanFamily (K : Type) [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (M : CoxeterMatrix (Fin n)) (Y : Type) [Group Y] where
  ι : Fin n → (Su K 2 1 2 →* Y)
  θ : Fin n → Fin n → (Su K 2 1 3 →* Y)
  left : ∀ i j, M i j = 3 → (θ i j).comp (embSUid (unitaryInvolution K 2 1) 2) = ι i
  right : ∀ i j, M i j = 3 → (θ i j).comp (embSUid (unitaryInvolution K 2 1) 0) = ι j
  rev : ∀ i j, M i j = 3 → θ j i = (θ i j).comp (revSU3 K 2 1).toMonoidHom
  comm : ∀ i j, M i j = 2 → ∀ a b, ι i a * ι j b = ι j b * ι i a
  a3 : ∀ i j k, M i j = 3 → M j k = 3 → M i k = 2 →
    ∃ κ : Su K 2 1 4 →* Y, κ.comp (blk012 K) = θ i j ∧ κ.comp (blk123 K) = θ j k
  farNodeEdge : ∀ i j k, M j k = 3 → M i j = 2 → M i k = 2 →
    ∀ a b, ι i a * θ j k b = θ j k b * ι i a
  farEdgeEdge : ∀ i k j l, M i k = 3 → M j l = 3 → M i j = 2 → M i l = 2 → M k j = 2 →
    M k l = 2 → ∀ a b, θ i k a * θ j l b = θ j l b * θ i k a

@[expose] def QTwoPhanFamily.IsUniversal {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X : Type} [Group X]
    (S : QTwoPhanFamily K M X) : Prop :=
  ∀ (Y : Type) [Group Y] (F : QTwoPhanFamily K M Y), ∃ ψ : X →* Y,
    (∀ i, ψ.comp (S.ι i) = F.ι i) ∧
      ∀ i j, M i j = 3 → ψ.comp (S.θ i j) = F.θ i j

@[expose] def QTwoPhanFamily.Generates {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X : Type} [Group X]
    (S : QTwoPhanFamily K M X) : Prop :=
  (⨆ (i) (j) (_ : M i j = 3), (S.θ i j).range) = ⊤

@[expose] noncomputable def QTwoPhanFamily.map {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X Y : Type} [Group X] [Group Y]
    (S : QTwoPhanFamily K M X) (φ : X →* Y) : QTwoPhanFamily K M Y where
  ι i := φ.comp (S.ι i)
  θ i j := φ.comp (S.θ i j)
  left i j h := by rw [MonoidHom.comp_assoc, S.left i j h]
  right i j h := by rw [MonoidHom.comp_assoc, S.right i j h]
  rev i j h := by rw [MonoidHom.comp_assoc, S.rev i j h]
  comm i j h a b := by
    simpa only [MonoidHom.comp_apply, map_mul] using congrArg φ (S.comm i j h a b)
  a3 i j k hij hjk hik := by
    obtain ⟨κ, h1, h2⟩ := S.a3 i j k hij hjk hik
    exact ⟨φ.comp κ, by rw [MonoidHom.comp_assoc, h1],
      by rw [MonoidHom.comp_assoc, h2]⟩
  farNodeEdge i j k hjk hij hik a b := by
    simpa only [MonoidHom.comp_apply, map_mul] using
      congrArg φ (S.farNodeEdge i j k hjk hij hik a b)
  farEdgeEdge i k j l hik hjl hij hil hkj hkl a b := by
    simpa only [MonoidHom.comp_apply, map_mul] using
      congrArg φ (S.farEdgeEdge i k j l hik hjl hij hil hkj hkl a b)

theorem QTwoPhanFamily.range_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X Y : Type} [Group X] [Group Y]
    {S : QTwoPhanFamily K M X} {F : QTwoPhanFamily K M Y}
    (hS : S.Generates) {ψ : X →* Y}
    (hψ : ∀ i j, M i j = 3 → ψ.comp (S.θ i j) = F.θ i j) :
    ψ.range = ⨆ (i) (j) (_ : M i j = 3), (F.θ i j).range := by
  have htop : ψ.range = Subgroup.map ψ
      (⨆ (i) (j) (_ : M i j = 3), (S.θ i j).range) := by
    rw [hS, Subgroup.map_top]
  rw [htop, Subgroup.map_iSup]
  apply iSup_congr
  intro i
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro j
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro h3
  rw [← MonoidHom.range_comp, hψ i j h3]

@[expose] noncomputable def QTwoPhanFamily.levi {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X : Type} [Group X]
    (S : QTwoPhanFamily K M X) (C : Set (Fin n)) : Subgroup X :=
  (⨆ i ∈ C, (S.ι i).range) ⊔
    ⨆ (i ∈ C) (j ∈ C) (_ : M i j = 3), (S.θ i j).range

theorem QTwoPhanFamily.levi_mono {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X : Type} [Group X]
    (S : QTwoPhanFamily K M X) {C C' : Set (Fin n)} (h : C ⊆ C') :
    S.levi C ≤ S.levi C' := by
  refine sup_le ?_ ?_
  · refine iSup_le fun i => iSup_le fun hi => ?_
    exact (le_iSup_of_le i (le_iSup (fun _ : i ∈ C' => (S.ι i).range) (h hi))).trans
      le_sup_left
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
      iSup_le fun hij => ?_
    refine (le_iSup_of_le i (le_iSup_of_le (h hi) (le_iSup_of_le j (le_iSup_of_le (h hj)
      (le_iSup (fun _ : M i j = 3 => (S.θ i j).range) hij))))).trans le_sup_right

theorem QTwoPhanFamily.levi_eq_iSup_small {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X : Type} [Group X]
    (S : QTwoPhanFamily K M X) (C : Set (Fin n)) :
    S.levi C = ⨆ (E : Set (Fin n)) (_ : E ⊆ C) (_ : E.ncard ≤ 2), S.levi E := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · refine iSup_le fun i => iSup_le fun hi => ?_
      have hsub : ({i} : Set (Fin n)) ⊆ C := by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hi
      have h2 : ({i} : Set (Fin n)).ncard ≤ 2 := by simp
      have hle : (S.ι i).range ≤ S.levi ({i} : Set (Fin n)) := by
        refine le_trans ?_ le_sup_left
        exact le_iSup_of_le i (le_iSup (fun _ : i ∈ ({i} : Set (Fin n)) =>
          (S.ι i).range) (by simp))
      exact hle.trans (le_iSup_of_le ({i} : Set (Fin n)) (le_iSup_of_le hsub
        (le_iSup (fun _ : ({i} : Set (Fin n)).ncard ≤ 2 => S.levi {i}) h2)))
    · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
        iSup_le fun hij => ?_
      have hsub : ({i, j} : Set (Fin n)) ⊆ C := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hi
        · exact hj
      have h2 : ({i, j} : Set (Fin n)).ncard ≤ 2 := by
        have hle := Set.ncard_insert_le i ({j} : Set (Fin n))
        simp only [Set.ncard_singleton] at hle
        omega
      have hle : (S.θ i j).range ≤ S.levi ({i, j} : Set (Fin n)) := by
        refine le_trans ?_ le_sup_right
        exact le_iSup_of_le i (le_iSup_of_le (by simp) (le_iSup_of_le j
          (le_iSup_of_le (by simp) (le_iSup (fun _ : M i j = 3 => (S.θ i j).range) hij))))
      exact hle.trans (le_iSup_of_le ({i, j} : Set (Fin n)) (le_iSup_of_le hsub
        (le_iSup (fun _ : ({i, j} : Set (Fin n)).ncard ≤ 2 => S.levi {i, j}) h2)))
  · refine iSup_le fun E => iSup_le fun hE => iSup_le fun h2 => ?_
    exact S.levi_mono hE

@[expose] def IsA2A2 {n : ℕ} (M : CoxeterMatrix (Fin n)) (C : Set (Fin n)) : Prop :=
  ∃ i k j l, C = {i, k, j, l} ∧ M i k = 3 ∧ M j l = 3 ∧ M i j = 2 ∧ M i l = 2 ∧
    M k j = 2 ∧ M k l = 2

@[expose] def qTwoShape {n : ℕ} (M : CoxeterMatrix (Fin n)) : Set (Set (Fin n)) :=
  {C | C ≠ Set.univ ∧ (C.ncard ≤ 3 ∨ IsA2A2 M C)}

theorem qTwoShape_mono {n : ℕ} {M : CoxeterMatrix (Fin n)} {C C' : Set (Fin n)}
    (hC : C ∈ qTwoShape M) (h : C' ⊆ C) : C' ∈ qTwoShape M := by
  refine ⟨?_, ?_⟩
  · intro hC'
    exact hC.1 (Set.eq_univ_of_subset h hC')
  · rcases hC.2 with h3 | hA
    · exact Or.inl ((Set.ncard_le_ncard h (Set.toFinite _)).trans h3)
    · by_cases h3 : C'.ncard ≤ 3
      · exact Or.inl h3
      · right
        obtain ⟨i, k, j, l, rfl, hik, hjl, hij, hil, hkj, hkl⟩ := hA
        have h4 : ({i, k, j, l} : Set (Fin n)).ncard ≤ 4 := by
          have h1 := Set.ncard_insert_le i ({k, j, l} : Set (Fin n))
          have h2 := Set.ncard_insert_le k ({j, l} : Set (Fin n))
          have h3' := Set.ncard_insert_le j ({l} : Set (Fin n))
          simp only [Set.ncard_singleton] at h3'
          omega
        have heq : C' = {i, k, j, l} :=
          Set.eq_of_subset_of_ncard_le h (by omega)
        rw [heq]
        exact ⟨i, k, j, l, rfl, hik, hjl, hij, hil, hkj, hkl⟩

theorem mem_qTwoShape_of_ncard_le_three {n : ℕ} (hn : 4 ≤ n) {M : CoxeterMatrix (Fin n)}
    {C : Set (Fin n)} (hC : C.ncard ≤ 3) : C ∈ qTwoShape M := by
  refine ⟨?_, Or.inl hC⟩
  intro h
  have hcard : C.ncard = n := by
    rw [h, Set.ncard_univ (Fin n), Nat.card_fin]
  omega

theorem ggCoxeterMatrixD_two_or_three {m : ℕ} (i j : Fin m) (h : i ≠ j) :
    CFSG.StandardType.ggCoxeterMatrixD m i j = 2 ∨
      CFSG.StandardType.ggCoxeterMatrixD m i j = 3 := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_neg h]
  split_ifs <;> simp

theorem ggCoxeterMatrixD_not_triangle {m : ℕ} (hm : 4 ≤ m) (i j k : Fin m) :
    CFSG.StandardType.ggCoxeterMatrixD m i j = 3 →
    CFSG.StandardType.ggCoxeterMatrixD m j k = 3 →
    CFSG.StandardType.ggCoxeterMatrixD m i k ≠ 3 := by
  intro hij hjk hik
  rw [CFSG.StandardType.OrthTorus.ggCoxeterMatrixD_eq_three_iff (by omega)] at hij hjk hik
  rcases hij with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    rcases hjk with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ <;>
    rcases hik with ⟨e, f⟩ | ⟨e, f⟩ | ⟨e, f⟩ | ⟨e, f⟩ <;> omega

theorem ggCoxeterMatrixD_exists_three {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    ∃ j : Fin m, CFSG.StandardType.ggCoxeterMatrixD m i j = 3 := by
  have hm3 : 3 ≤ m := by omega
  by_cases hi : (i : ℕ) + 4 ≤ m
  · refine ⟨⟨(i : ℕ) + 1, by omega⟩, ?_⟩
    rw [CFSG.StandardType.OrthTorus.ggCoxeterMatrixD_eq_three_iff hm3]
    exact Or.inl ⟨rfl, by rw [Fin.val_mk]; omega⟩
  · have hi3 : (i : ℕ) = m - 3 ∨ (i : ℕ) = m - 2 ∨ (i : ℕ) = m - 1 := by omega
    rcases hi3 with h | h | h
    · refine ⟨⟨m - 1, by omega⟩, ?_⟩
      rw [CFSG.StandardType.OrthTorus.ggCoxeterMatrixD_eq_three_iff hm3]
      refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
      · omega
      · change m - 1 + 1 = m
        omega
    · refine ⟨⟨m - 3, by omega⟩, ?_⟩
      rw [CFSG.StandardType.OrthTorus.ggCoxeterMatrixD_eq_three_iff hm3]
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [h]
        change m - 2 = m - 3 + 1
        omega
      · rw [h]
        omega
    · refine ⟨⟨m - 3, by omega⟩, ?_⟩
      rw [CFSG.StandardType.OrthTorus.ggCoxeterMatrixD_eq_three_iff hm3]
      refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
      · change m - 3 + 3 = m
        omega
      · omega

structure QTwoPhanFamily.Faithful {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X : Type} [Group X]
    (S : QTwoPhanFamily K M X) : Prop where
  ι_inj : ∀ i, Function.Injective (S.ι i)
  θ_inj : ∀ i j, M i j = 3 → Function.Injective (S.θ i j)
  split : ∀ C₁ C₂ : Set (Fin n), C₁ ∪ C₂ ∈ qTwoShape M → Disjoint C₁ C₂ →
    (∀ i ∈ C₁, ∀ j ∈ C₂, M i j = 2) → S.levi C₁ ⊓ S.levi C₂ = ⊥

theorem blk123_comp_embSUid_two (K : Type) [Field K] [Finite K] [CharP K 2] :
    (blk123 K).comp (embSUid (unitaryInvolution K 2 1) 2) =
      (blk012 K).comp (embSUid (unitaryInvolution K 2 1) 0) := by
  have h1 : blk123 K = blockEmb3 K 2 1 3 ⟨1, by decide⟩ (by decide) := rfl
  have h0 : blk012 K = blockEmb3 K 2 1 3 ⟨0, by decide⟩ (by decide) := rfl
  rw [h1, h0, blockEmb3_comp_embSUid_two, blockEmb3_comp_embSUid_zero]

@[expose] def QTwoA3Mark : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    ∀ {G : Type} [Group G] (U₁ U₂ U₃ W₁₂ W₂₃ : Subgroup G),
      UnitaryBlockStandardPair K 2 1 W₁₂ U₁ U₂ → UnitaryBlockStandardPair K 2 1 W₂₃ U₂ U₃ →
      (∀ x ∈ U₁, ∀ y ∈ U₃, x * y = y * x) → (∃ θ : Su K 2 1 4 →* G, θ.range = W₁₂ ⊔ W₂₃) →
      ∃ κ : Su K 2 1 4 →* G, Function.Injective κ ∧
        (κ.comp (blk012 K)).range = W₁₂ ∧ (κ.comp (blk123 K)).range = W₂₃ ∧
        (B12 K 2 1).map (κ.comp (blk012 K)) = U₁ ∧
        (B23 K 2 1).map (κ.comp (blk012 K)) = U₂ ∧
        (B23 K 2 1).map (κ.comp (blk123 K)) = U₃

end CFSG.ClassicalInvolution.PhanDn.QTwo
