module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp4

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open CFSG.RankThree.Classical
open CFSG.LieType.Steinberg.Sp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups commutatorElement Matrix

section Planes

variable {r : ℕ} {K : Type} [Field K]

theorem eq_zero_of_mem_spPlane {k : Fin r} {v : Fin r ⊕ Fin r → K} (hv : v ∈ spPlane k)
    {a : Fin r ⊕ Fin r} (ha : a ∉ coords k) : v a = 0 := by
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hv
  rw [← hαβ]
  have h1 : a ≠ Sum.inl k := fun h => ha (h ▸ inl_mem_coords k)
  have h2 : a ≠ Sum.inr k := fun h => ha (h ▸ inr_mem_coords k)
  simp [h1, h2]

theorem single_mem_spPlane {k : Fin r} {a : Fin r ⊕ Fin r} (ha : a ∈ coords k) :
    (Pi.single a 1 : Fin r ⊕ Fin r → K) ∈ spPlane k := by
  rcases mem_coords.mp ha with rfl | rfl
  · exact single_inl_mem_spPlane k
  · exact single_inr_mem_spPlane k

theorem single_notMem_spPlane {k : Fin r} {a : Fin r ⊕ Fin r} (ha : a ∉ coords k) :
    (Pi.single a 1 : Fin r ⊕ Fin r → K) ∉ spPlane k := by
  intro h
  have hz := eq_zero_of_mem_spPlane h ha
  simp at hz

theorem spForm_single_one_eq_zero_of_mem_spPlane {k : Fin r} {a : Fin r ⊕ Fin r}
    (ha : a ∉ coords k) {v : Fin r ⊕ Fin r → K} (hv : v ∈ spPlane k) :
    spForm r K (Pi.single a 1) v = 0 := by
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hv
  have hpa : par a ∉ coords k := fun h => ha (by simpa using parClosed_coords k _ h)
  have h1 : Sum.inl k ≠ par a := fun h => hpa (h ▸ inl_mem_coords k)
  have h2 : Sum.inr k ≠ par a := fun h => hpa (h ▸ inr_mem_coords k)
  rw [← hαβ, map_add, map_smul, map_smul, spForm_single_one, spForm_single_one, gram_apply,
    gram_apply, if_neg h1, if_neg h2]
  simp

theorem mat_apply_eq_zero_of_mapsTo {n : ℕ} {K : Type} [Field K] {g : StatedSp n K} {k : Fin n}
    (h : ∀ v ∈ spPlane k, spEnd g v ∈ spPlane k) {a b : Fin n ⊕ Fin n} (hb : b ∈ coords k)
    (ha : a ∉ coords k) : mat n K g a b = 0 := by
  have hmem : spEnd g (Pi.single b 1) ∈ spPlane k := h _ (single_mem_spPlane hb)
  have hzero : spEnd g (Pi.single b 1) a = 0 := eq_zero_of_mem_spPlane hmem ha
  rw [spEnd_apply, Matrix.mulVec_single_one, Matrix.col_apply] at hzero
  exact hzero

end Planes

theorem spTransvection_mem_range_longBlock {n : ℕ} {K : Type} [Field K] {k : Fin n}
    {v : Fin n ⊕ Fin n → K} (hv : v ∈ spPlane k) (t : K) :
    spTransvection v t ∈ (longBlock K n k).range := by
  rw [range_longBlock, mem_suppGroup_iff (parClosed_coords k)]
  intro c hc a
  have hfix : spEnd (spTransvection v t) (Pi.single c 1) = Pi.single c 1 := by
    rw [spEnd_spTransvection, spForm_single_one_eq_zero_of_mem_spPlane hc hv, mul_zero, zero_smul,
      add_zero]
  have hfix' : mat n K (spTransvection v t) *ᵥ Pi.single c 1 = Pi.single c 1 := hfix
  rw [← mulVec_single_one_apply (mat n K (spTransvection v t)) c a, hfix', Pi.single_apply,
    Matrix.one_apply]

section Block

variable {K : Type} [Field K]

private theorem mulVec_eq_of_eq_on_coords {k : Fin 2}
    {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hMN : ∀ a b, a ∈ coords k → b ∈ coords k → M a b = N a b)
    (hM : ∀ a b, a ∉ coords k → b ∈ coords k → M a b = 0)
    (hN : ∀ a b, a ∉ coords k → b ∈ coords k → N a b = 0)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ spPlane k) : M *ᵥ v = N *ᵥ v := by
  funext a
  have hv0 : ∀ b, b ∉ coords k → v b = 0 := fun b hb => eq_zero_of_mem_spPlane hv hb
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
  by_cases ha : a ∈ coords k
  · refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ coords k
    · rw [hMN a b ha hb]
    · rw [hv0 b hb, mul_zero, mul_zero]
  · have hM0 : ∑ b, M a b * v b = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : b ∈ coords k
      · rw [hM a b ha hb, zero_mul]
      · rw [hv0 b hb, mul_zero]
    have hN0 : ∑ b, N a b * v b = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : b ∈ coords k
      · rw [hN a b ha hb, zero_mul]
      · rw [hv0 b hb, mul_zero]
    rw [hM0, hN0]

private theorem spPlane_sup_spPlane :
    spPlane (r := 2) (K := K) 0 ⊔ spPlane (r := 2) (K := K) 1 = ⊤ := by
  have key : (⨆ i, spPlane (r := 2) (K := K) i) =
      spPlane (r := 2) (K := K) 0 ⊔ spPlane (r := 2) (K := K) 1 := by
    have h : (⨆ i, spPlane (r := 2) (K := K) i) =
        ⨆ i ∈ (Finset.univ : Finset (Fin 2)), spPlane (r := 2) (K := K) i := by simp
    rw [h, ← Finset.sup_eq_iSup, show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
    simp
  rw [← key, iSup_spPlane]

end Block

section MapsTo

variable {K : Type} [Field K]

theorem mem_longBlock_sup_longBlock_of_mapsTo {g : StatedSp 2 K}
    (h0 : ∀ v ∈ spPlane (0 : Fin 2), spEnd g v ∈ spPlane (0 : Fin 2))
    (h1 : ∀ v ∈ spPlane (1 : Fin 2), spEnd g v ∈ spPlane (1 : Fin 2)) :
    g ∈ (longBlock K 2 0).range ⊔ (longBlock K 2 1).range := by
  set A : Matrix (Fin 2) (Fin 2) K := stdBlock 0 (mat 2 K g) with hA
  set B : Matrix (Fin 2) (Fin 2) K := stdBlock 1 (mat 2 K g) with hB
  have hdetA : A.det = 1 := by
    rw [hA]
    exact det_stdBlock_eq_one g 0 fun c hc =>
      mat_apply_eq_zero_of_mapsTo h0 (inl_mem_coords 0) hc
  have hdetB : B.det = 1 := by
    rw [hB]
    exact det_stdBlock_eq_one g 1 fun c hc =>
      mat_apply_eq_zero_of_mapsTo h1 (inl_mem_coords 1) hc
  set x : StatedSp 2 K := longBlock K 2 0 (mkSL A hdetA) with hx
  set y : StatedSp 2 K := longBlock K 2 1 (mkSL B hdetB) with hy
  have hxmat : mat 2 K x = blockMat (Sum.inl 0) (Sum.inr 0) A := by
    rw [hx, mat_longBlock, coe_mkSL]
  have hymat : mat 2 K y = blockMat (Sum.inl 1) (Sum.inr 1) B := by
    rw [hy, mat_longBlock, coe_mkSL]
  have hAg : ∀ a b, a ∈ coords (0 : Fin 2) → b ∈ coords (0 : Fin 2) →
      mat 2 K g a b = mat 2 K x a b := by
    intro a b ha hb
    rw [hxmat]
    rcases mem_coords.mp ha with rfl | rfl <;> rcases mem_coords.mp hb with rfl | rfl <;>
      simp [blockMat, stdBlock, hA]
  have hAz : ∀ a b, a ∉ coords (0 : Fin 2) → b ∈ coords (0 : Fin 2) →
      mat 2 K x a b = 0 := by
    intro a b ha hb
    rw [hxmat, blockMat_apply_of_not_mem (0 : Fin 2) A (fun h => ha h.1),
      Matrix.one_apply_ne fun h => ha (by rw [h]; exact hb)]
  have hBg : ∀ a b, a ∈ coords (1 : Fin 2) → b ∈ coords (1 : Fin 2) →
      mat 2 K g a b = mat 2 K y a b := by
    intro a b ha hb
    rw [hymat]
    rcases mem_coords.mp ha with rfl | rfl <;> rcases mem_coords.mp hb with rfl | rfl <;>
      simp [blockMat, stdBlock, hB]
  have hBz : ∀ a b, a ∉ coords (1 : Fin 2) → b ∈ coords (1 : Fin 2) →
      mat 2 K y a b = 0 := by
    intro a b ha hb
    rw [hymat, blockMat_apply_of_not_mem (1 : Fin 2) B (fun h => ha h.1),
      Matrix.one_apply_ne fun h => ha (by rw [h]; exact hb)]
  have hxg : ∀ v ∈ spPlane (0 : Fin 2), mat 2 K g *ᵥ v = mat 2 K x *ᵥ v := fun v hv =>
    mulVec_eq_of_eq_on_coords hAg (fun a b ha hb => mat_apply_eq_zero_of_mapsTo h0 hb ha) hAz hv
  have hyg : ∀ v ∈ spPlane (1 : Fin 2), mat 2 K g *ᵥ v = mat 2 K y *ᵥ v := fun v hv =>
    mulVec_eq_of_eq_on_coords hBg (fun a b ha hb => mat_apply_eq_zero_of_mapsTo h1 hb ha) hBz hv
  have hxfix : ∀ w ∈ spPlane (1 : Fin 2), mat 2 K x *ᵥ w = w := by
    intro w hw
    rw [hxmat]
    exact mulVec_eq_self_of_isSupp (isSupp_blockMat (0 : Fin 2) A)
      fun t ht => eq_zero_of_mem_spPlane hw (coords_subset_compl (by decide) ht)
  have hyfix : ∀ w ∈ spPlane (0 : Fin 2), mat 2 K y *ᵥ w = w := by
    intro w hw
    rw [hymat]
    exact mulVec_eq_self_of_isSupp (isSupp_blockMat (1 : Fin 2) B)
      fun t ht => eq_zero_of_mem_spPlane hw (coords_subset_compl (by decide) ht)
  have hgprod : ∀ v ∈ spPlane (0 : Fin 2) ⊔ spPlane (1 : Fin 2),
      mat 2 K g *ᵥ v = (mat 2 K x * mat 2 K y) *ᵥ v := by
    intro v hv
    obtain ⟨v0, hv0, v1, hv1, hv01⟩ := Submodule.mem_sup.mp hv
    have hx1 : mat 2 K x *ᵥ (mat 2 K y *ᵥ v1) = mat 2 K y *ᵥ v1 :=
      hxfix (mat 2 K y *ᵥ v1) (by rw [← hyg v1 hv1]; exact h1 v1 hv1)
    calc mat 2 K g *ᵥ v
        = mat 2 K g *ᵥ v0 + mat 2 K g *ᵥ v1 := by rw [← hv01, Matrix.mulVec_add]
      _ = mat 2 K x *ᵥ v0 + mat 2 K y *ᵥ v1 := by rw [hxg v0 hv0, hyg v1 hv1]
      _ = (mat 2 K x * mat 2 K y) *ᵥ v0 + (mat 2 K x * mat 2 K y) *ᵥ v1 := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hyfix v0 hv0, hx1]
      _ = (mat 2 K x * mat 2 K y) *ᵥ (v0 + v1) := by rw [Matrix.mulVec_add]
      _ = (mat 2 K x * mat 2 K y) *ᵥ v := by rw [hv01]
  have hprod : mat 2 K g = mat 2 K (x * y) := by
    rw [map_mul]
    ext a b
    have hb : (Pi.single b 1 : Fin 2 ⊕ Fin 2 → K) ∈ spPlane (0 : Fin 2) ⊔ spPlane (1 : Fin 2) := by
      rw [spPlane_sup_spPlane]
      exact Submodule.mem_top
    have h := congrFun (hgprod _ hb) a
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h
  have hgxy : g = x * y := mat_injective hprod
  rw [hgxy]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨mkSL A hdetA, hx.symm⟩)
    (Subgroup.mem_sup_right ⟨mkSL B hdetB, hy.symm⟩)

end MapsTo

section PlaneAction

variable {K : Type} [Field K]

private def PresPlanes (g : StatedSp 2 K) : Prop :=
  (∀ v ∈ spPlane (0 : Fin 2), spEnd g v ∈ spPlane (0 : Fin 2)) ∧
    ∀ v ∈ spPlane (1 : Fin 2), spEnd g v ∈ spPlane (1 : Fin 2)

private def SwapPlanes (g : StatedSp 2 K) : Prop :=
  (∀ v ∈ spPlane (0 : Fin 2), spEnd g v ∈ spPlane (1 : Fin 2)) ∧
    ∀ v ∈ spPlane (1 : Fin 2), spEnd g v ∈ spPlane (0 : Fin 2)

private theorem spPlane_zero_ne_top : spPlane (r := 2) (K := K) 0 ≠ ⊤ := fun h =>
  single_notMem_spPlane (k := (0 : Fin 2)) (a := Sum.inl (1 : Fin 2)) (by decide)
    (by rw [h]; exact Submodule.mem_top)

private theorem spPlane_one_ne_top : spPlane (r := 2) (K := K) 1 ≠ ⊤ := fun h =>
  single_notMem_spPlane (k := (1 : Fin 2)) (a := Sum.inl (0 : Fin 2)) (by decide)
    (by rw [h]; exact Submodule.mem_top)

private theorem presPlanes_mul {a b : StatedSp 2 K} (ha : PresPlanes a) (hb : PresPlanes b) :
    PresPlanes (a * b) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.1 _ (hb.1 v hv)
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.2 _ (hb.2 v hv)

private theorem presPlanes_swapPlanes_mul {a b : StatedSp 2 K} (ha : PresPlanes a)
    (hb : SwapPlanes b) : SwapPlanes (a * b) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.2 _ (hb.1 v hv)
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.1 _ (hb.2 v hv)

private theorem swapPlanes_presPlanes_mul {a b : StatedSp 2 K} (ha : SwapPlanes a)
    (hb : PresPlanes b) : SwapPlanes (a * b) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.1 _ (hb.1 v hv)
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.2 _ (hb.2 v hv)

private theorem swapPlanes_swapPlanes_mul {a b : StatedSp 2 K} (ha : SwapPlanes a)
    (hb : SwapPlanes b) : PresPlanes (a * b) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.2 _ (hb.1 v hv)
  · rw [spEnd_mul, Module.End.mul_apply]
    exact ha.1 _ (hb.2 v hv)

private theorem not_swapPlanes_inv_of_presPlanes {g : StatedSp 2 K} (h : PresPlanes g) :
    ¬ SwapPlanes g⁻¹ := by
  rintro ⟨h0, -⟩
  have hv : spEnd g⁻¹ (Pi.single (Sum.inl (0 : Fin 2)) 1) ∈ spPlane (1 : Fin 2) :=
    h0 _ (single_mem_spPlane (inl_mem_coords 0))
  have hmem := h.2 _ hv
  rw [spEnd_spEnd_inv_apply] at hmem
  exact single_notMem_spPlane (k := (1 : Fin 2)) (a := Sum.inl (0 : Fin 2)) (by decide) hmem

private theorem not_presPlanes_inv_of_swapPlanes {g : StatedSp 2 K} (h : SwapPlanes g) :
    ¬ PresPlanes g⁻¹ := by
  rintro ⟨h0, -⟩
  have hv : spEnd g⁻¹ (Pi.single (Sum.inl (0 : Fin 2)) 1) ∈ spPlane (0 : Fin 2) :=
    h0 _ (single_mem_spPlane (inl_mem_coords 0))
  have hmem := h.1 _ hv
  rw [spEnd_spEnd_inv_apply] at hmem
  exact single_notMem_spPlane (k := (1 : Fin 2)) (a := Sum.inl (0 : Fin 2)) (by decide) hmem

private theorem presPlanes_or_swapPlanes {g : StatedSp 2 K}
    (h : ∀ (k : Fin 2) (v : Fin 2 ⊕ Fin 2 → K), v ∈ spPlane k →
      spEnd g v ∈ spPlane (0 : Fin 2) ∨ spEnd g v ∈ spPlane (1 : Fin 2)) :
    PresPlanes g ∨ SwapPlanes g := by
  have h0 := CFSG.LieType.BorelTits.le_or_le_of_forall_mem_or_mem
    (P := Submodule.map (spEnd g) (spPlane (0 : Fin 2)))
    (A := spPlane (0 : Fin 2)) (B := spPlane (1 : Fin 2)) fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
      exact h 0 v hv
  have h1 := CFSG.LieType.BorelTits.le_or_le_of_forall_mem_or_mem
    (P := Submodule.map (spEnd g) (spPlane (1 : Fin 2)))
    (A := spPlane (0 : Fin 2)) (B := spPlane (1 : Fin 2)) fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
      exact h 1 v hv
  have htop : ∀ P : Submodule K (Fin 2 ⊕ Fin 2 → K),
      Submodule.map (spEnd g) (spPlane (0 : Fin 2)) ≤ P →
      Submodule.map (spEnd g) (spPlane (1 : Fin 2)) ≤ P →
      (⊤ : Submodule K (Fin 2 ⊕ Fin 2 → K)) ≤ P := by
    intro P hP0 hP1 w _
    have hw : spEnd g⁻¹ w ∈ spPlane (0 : Fin 2) ⊔ spPlane (1 : Fin 2) := by
      rw [spPlane_sup_spPlane]
      exact Submodule.mem_top
    obtain ⟨y0, hy0, y1, hy1, hy01⟩ := Submodule.mem_sup.mp hw
    have hgw : spEnd g (spEnd g⁻¹ w) = w := spEnd_spEnd_inv_apply g w
    rw [← hgw, ← hy01, map_add]
    exact Submodule.add_mem _ (hP0 (Submodule.mem_map_of_mem hy0))
      (hP1 (Submodule.mem_map_of_mem hy1))
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact absurd (top_le_iff.mp (htop _ h0 h1)) spPlane_zero_ne_top
  · exact Or.inl ⟨fun v hv => h0 (Submodule.mem_map_of_mem hv),
      fun v hv => h1 (Submodule.mem_map_of_mem hv)⟩
  · exact Or.inr ⟨fun v hv => h0 (Submodule.mem_map_of_mem hv),
      fun v hv => h1 (Submodule.mem_map_of_mem hv)⟩
  · exact absurd (top_le_iff.mp (htop _ h0 h1)) spPlane_one_ne_top

end PlaneAction

section Main

theorem longBlock_sup_longBlock_sup_eq_top_of_perfect {K : Type} [Field K]
    {S : Subgroup (StatedSp 2 K)} (hS : ⁅S, S⁆ = S)
    (hSle : ¬ S ≤ (longBlock K 2 0).range ⊔ (longBlock K 2 1).range) :
    (longBlock K 2 0).range ⊔ (longBlock K 2 1).range ⊔ S = ⊤ := by
  set H0 : Subgroup (StatedSp 2 K) := (longBlock K 2 0).range ⊔ (longBlock K 2 1).range
  set H : Subgroup (StatedSp 2 K) := H0 ⊔ S with hH
  have hcenter : ∀ (k : Fin 2) (v : Fin 2 ⊕ Fin 2 → K), v ∈ spPlane k → IsSpCenter H v := by
    intro k v hv t
    have hk : (longBlock K 2 k).range ≤ H0 := by
      fin_cases k
      · exact le_sup_left
      · exact le_sup_right
    exact Subgroup.mem_sup_left (hk (spTransvection_mem_range_longBlock hv t))
  by_cases hpos : ∃ s ∈ S, ∃ (k : Fin 2) (v : Fin 2 ⊕ Fin 2 → K), v ∈ spPlane k ∧
      spEnd s v ∉ spPlane (0 : Fin 2) ∧ spEnd s v ∉ spPlane (1 : Fin 2)
  · obtain ⟨s, hs, k, v, hv, hv0, hv1⟩ := hpos
    have hw : spEnd s v ∈ spPlane (0 : Fin 2) ⊔ spPlane (1 : Fin 2) := by
      rw [spPlane_sup_spPlane]
      exact Submodule.mem_top
    obtain ⟨w0, hw0, w1, hw1, hw01⟩ := Submodule.mem_sup.mp hw
    have hw0ne : w0 ≠ 0 := fun h => hv1 (by rw [← hw01, h, zero_add]; exact hw1)
    have hw1ne : w1 ≠ 0 := fun h => hv0 (by rw [← hw01, h, add_zero]; exact hw0)
    have hwcenter : IsSpCenter H (spEnd s v) :=
      (hcenter k v hv).map (Subgroup.mem_sup_right hs)
    have hpair01 : ∀ y ∈ spPlane (0 : Fin 2), ∀ y' ∈ spPlane (1 : Fin 2), y ≠ 0 → y' ≠ 0 →
        IsSpCenter H (y + y') := by
      intro y hy y' hy' hy0 hy'0
      obtain ⟨g0, hg0, hg0y, hg0fix⟩ := exists_mem_fixing_eq (H := H)
        (U := spPlane (0 : Fin 2)) (nondegenerate_spPlane 0)
        (fun c hc => hcenter 0 c hc) hw0 hy hw0ne hy0
      obtain ⟨g1, hg1, hg1y, hg1fix⟩ := exists_mem_fixing_eq (H := H)
        (U := spPlane (1 : Fin 2)) (nondegenerate_spPlane 1)
        (fun c hc => hcenter 1 c hc) hw1 hy' hw1ne hy'0
      have hfixw1 : spEnd g0 w1 = w1 := hg0fix w1 fun c hc =>
        spForm_eq_zero_of_mem_spPlane (i := 1) (j := 0) (by decide) hw1 hc
      have hfixy : spEnd g1 y = y := hg1fix y fun c hc =>
        spForm_eq_zero_of_mem_spPlane (i := 0) (j := 1) (by decide) hy hc
      have hcomp : spEnd (g1 * g0) (spEnd s v) = y + y' := by
        rw [spEnd_mul, Module.End.mul_apply, ← hw01, map_add, hg0y, hfixw1, map_add, hfixy,
          hg1y]
      have hcent := hwcenter.map (H.mul_mem hg1 hg0)
      rwa [hcomp] at hcent
    have hpair : ∀ i j : Fin 2, i ≠ j → ∀ y ∈ spPlane i, ∀ y' ∈ spPlane j, y ≠ 0 → y' ≠ 0 →
        IsSpCenter H (y + y') := by
      intro i j hij y hy y' hy' hy0 hy'0
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hpair01 y hy y' hy' hy0 hy'0
      · rw [add_comm]
        exact hpair01 y' hy' y hy hy'0 hy0
      · exact absurd rfl hij
    have hall : ∀ w, IsSpCenter H w :=
      isSpCenter_of_pairs (H := H) (Vs := spPlane) (iSup_spPlane (r := 2) (K := K))
        (fun i j hij u hu v hv => spForm_eq_zero_of_mem_spPlane hij hu hv)
        (fun i => nondegenerate_spPlane i) (fun i c hc => hcenter i c hc) hpair
    show H = ⊤
    exact eq_top_of_isSpCenter hall
  · have hno : ∀ s ∈ S, ∀ (k : Fin 2) (v : Fin 2 ⊕ Fin 2 → K), v ∈ spPlane k →
        spEnd s v ∈ spPlane (0 : Fin 2) ∨ spEnd s v ∈ spPlane (1 : Fin 2) := by
      intro s hs k v hv
      by_contra hc
      push Not at hc
      exact hpos ⟨s, hs, k, v, hv, hc⟩
    have hmemH0 : S ≤ H0 := by
      rw [← hS]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      have hta := presPlanes_or_swapPlanes (hno a ha)
      have htb := presPlanes_or_swapPlanes (hno b hb)
      have hia : PresPlanes a⁻¹ ∨ SwapPlanes a⁻¹ :=
        presPlanes_or_swapPlanes (hno a⁻¹ (S.inv_mem ha))
      have hib : PresPlanes b⁻¹ ∨ SwapPlanes b⁻¹ :=
        presPlanes_or_swapPlanes (hno b⁻¹ (S.inv_mem hb))
      have hpa : PresPlanes a → PresPlanes a⁻¹ := fun hp =>
        hia.resolve_right (not_swapPlanes_inv_of_presPlanes hp)
      have hpb : PresPlanes b → PresPlanes b⁻¹ := fun hp =>
        hib.resolve_right (not_swapPlanes_inv_of_presPlanes hp)
      have hsa : SwapPlanes a → SwapPlanes a⁻¹ := fun hp =>
        hia.resolve_left (not_presPlanes_inv_of_swapPlanes hp)
      have hsb : SwapPlanes b → SwapPlanes b⁻¹ := fun hp =>
        hib.resolve_left (not_presPlanes_inv_of_swapPlanes hp)
      have key : PresPlanes ⁅a, b⁆ := by
        rw [commutatorElement_def]
        rcases hta with hta | hta <;> rcases htb with htb | htb
        · exact presPlanes_mul (presPlanes_mul (presPlanes_mul hta htb) (hpa hta)) (hpb htb)
        · exact swapPlanes_swapPlanes_mul
            (swapPlanes_presPlanes_mul (presPlanes_swapPlanes_mul hta htb) (hpa hta)) (hsb htb)
        · exact presPlanes_mul
            (swapPlanes_swapPlanes_mul (swapPlanes_presPlanes_mul hta htb) (hsa hta)) (hpb htb)
        · exact swapPlanes_swapPlanes_mul
            (presPlanes_swapPlanes_mul (swapPlanes_swapPlanes_mul hta htb) (hsa hta)) (hsb htb)
      obtain ⟨key0, key1⟩ := key
      exact mem_longBlock_sup_longBlock_of_mapsTo key0 key1
    exact absurd hmemH0 hSle

end Main

end CFSG.ClassicalGroups.Symplectic.Sp4

end
