module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.SeitzReduction

namespace UnitaryLagrangian

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

structure IsLagrangianFrame (h : UnitaryFieldData p f K) (G s : Matrix (Fin n) (Fin n) K) {l : ℕ}
    (e d : Fin l → Fin n → K) : Prop where
  ee : ∀ i j, gramForm h G (e i) (e j) = 0
  dd : ∀ i j, gramForm h G (d i) (d j) = 0
  ed : ∀ i j, gramForm h G (e i) (d j) = if i = j then 1 else 0
  de : ∀ i j, gramForm h G (d i) (e j) = if i = j then 1 else 0
  expand : ∀ v, v = ∑ k, gramForm h G (d k) v • e k + ∑ k, gramForm h G (e k) v • d k
  mulVec : ∀ v, s *ᵥ v = v + ∑ k, gramForm h G (e k) v • e k

theorem exists_isLagrangianFrame (h : UnitaryFieldData 2 f K) {G : Matrix (Fin n) (Fin n) K}
    (hG : (G.map h.bar)ᵀ = G) (hdet : G.det ≠ 0) {s : Matrix (Fin n) (Fin n) K}
    (hs : ∀ x y, gramForm h G (s *ᵥ x) (s *ᵥ y) = gramForm h G x y) (hss : s * s = 1)
    (hWL : LinearMap.range (s - 1).mulVecLin = LinearMap.ker (s - 1).mulVecLin) :
    ∃ l, n = l + l ∧ ∃ e d : Fin l → Fin n → K, IsLagrangianFrame h G s e d := by
  classical
  have : CharP K 2 := h.charP
  set B := gramForm h G with hB
  have hBs : B.IsSymm := gramForm_isSymm h hG
  have hBsep : B.SeparatingLeft := gramForm_separatingLeft h hdet
  set N := s - 1 with hN
  have hNv : ∀ v, N *ᵥ v = s *ᵥ v - v := fun v => by rw [hN, sub_mulVec, one_mulVec]
  have hNN : ∀ v, N *ᵥ (N *ᵥ v) = 0 := by
    intro v
    have h1 : N *ᵥ v ∈ LinearMap.ker N.mulVecLin := by
      rw [← hWL]
      exact ⟨v, rfl⟩
    exact h1
  have hadj : ∀ x y, B (N *ᵥ x) y = B x (N *ᵥ y) := by
    intro x y
    have hss' : s *ᵥ (s *ᵥ y) = y := by rw [mulVec_mulVec, hss, one_mulVec]
    rw [hNv, hNv, map_sub, LinearMap.sub_apply, map_sub]
    congr 1
    calc B (s *ᵥ x) y = B (s *ᵥ x) (s *ᵥ (s *ᵥ y)) := by rw [hss']
      _ = B x (s *ᵥ y) := hs x (s *ᵥ y)
  have hWW : ∀ x y, B (N *ᵥ x) (N *ᵥ y) = 0 := fun x y => by rw [hadj, hNN, map_zero]
  set W := LinearMap.ker N.mulVecLin with hW
  obtain ⟨U, hWU⟩ := Submodule.exists_isCompl W
  set bU : U →ₛₗ[h.bar] U →ₗ[K] K := (B.compl₂ N.mulVecLin).domRestrict₁₂ U U with hbU
  have hbU_apply : ∀ x y : U, bU x y = B x (N *ᵥ y) := fun x y => rfl
  have hbsymm : bU.IsSymm := ⟨fun x y => by
    rw [hbU_apply, hbU_apply, hBs.eq, ← hadj]⟩
  have hbsep : bU.SeparatingLeft := by
    intro x hx
    have hall : ∀ v, B x (N *ᵥ v) = 0 := by
      intro v
      have hv : v ∈ W ⊔ U := by rw [hWU.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
      have hw0 : N *ᵥ w = 0 := hw
      rw [mulVec_add, hw0, zero_add]
      exact hx ⟨u, hu⟩
    have hNx : N *ᵥ (x : Fin n → K) = 0 := hBsep _ fun v => by rw [hadj]; exact hall v
    have hxW : (x : Fin n → K) ∈ W := hNx
    have hx0 : (x : Fin n → K) ∈ W ⊓ U := ⟨hxW, x.2⟩
    rw [hWU.inf_eq_bot, Submodule.mem_bot] at hx0
    exact Subtype.ext hx0
  obtain ⟨g, hg⟩ := h.exists_orthonormal_basis hbsymm hbsep
  have hnl : n = Module.finrank K U + Module.finrank K U := by
    have h1 : Module.finrank K W + Module.finrank K U = n := by
      have := Submodule.finrank_add_eq_of_isCompl hWU
      rwa [Module.finrank_fin_fun] at this
    have h2 : Module.finrank K W + Module.finrank K W = n := by
      have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
      rw [hWL, Module.finrank_fin_fun] at this
      exact this
    omega
  refine ⟨Module.finrank K U, hnl, ?_⟩
  set gv : Fin (Module.finrank K U) → Fin n → K := fun i => (g i : Fin n → K) with hgv
  have hbg : ∀ i j, B (gv i) (N *ᵥ gv j) = if i = j then 1 else 0 := fun i j => hg i j
  set e : Fin (Module.finrank K U) → Fin n → K := fun i => N *ᵥ gv i with he
  have heg : ∀ i j, B (e i) (gv j) = if i = j then 1 else 0 := fun i j => by
    rw [he, hadj]; exact hbg i j
  have hge : ∀ i j, B (gv i) (e j) = if i = j then 1 else 0 := fun i j => hbg i j
  have hee : ∀ i j, B (e i) (e j) = 0 := fun i j => hWW _ _
  set m : Fin (Module.finrank K U) → Fin (Module.finrank K U) → K :=
    fun i j => B (gv i) (gv j) with hm
  have hmbar : ∀ i j, h.bar (m i j) = m j i := fun i j => hBs.eq _ _
  have hd₀ : ∀ i, ∃ a : K, a + h.bar a = m i i := fun i => by
    obtain ⟨a, ha⟩ := h.traceLin_surjective ⟨m i i, by rw [UnitaryFieldData.mem_fixedField, hmbar]⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  choose d₀ hd₀ using hd₀
  set c : Fin (Module.finrank K U) → Fin (Module.finrank K U) → K :=
    fun j i => if i < j then m i j else if i = j then d₀ i else 0 with hc
  have hcc : ∀ i j, c j i + h.bar (c i j) = m i j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have h1 : c j i = m i j := by simp [hc, hij]
      have h2 : c i j = 0 := by simp [hc, not_lt.mpr hij.le, hij.ne']
      rw [h1, h2, map_zero, add_zero]
    · have h1 : c i i = d₀ i := by simp [hc]
      rw [h1]
      exact hd₀ i
    · have h1 : c j i = 0 := by simp [hc, not_lt.mpr hij.le, hij.ne']
      have h2 : c i j = m j i := by simp [hc, hij]
      rw [h1, h2, hmbar, zero_add]
  set d : Fin (Module.finrank K U) → Fin n → K := fun i => gv i + ∑ k, c i k • e k with hd
  have hd_left : ∀ i w, B (d i) w = B (gv i) w + ∑ k, h.bar (c i k) * B (e k) w := by
    intro i w
    rw [hd, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  have hd_right : ∀ i w, B w (d i) = B w (gv i) + ∑ k, c i k * B w (e k) := by
    intro i w
    rw [hd, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
  have hed : ∀ i j, B (e i) (d j) = if i = j then 1 else 0 := by
    intro i j
    rw [hd_right, heg]
    simp [hee]
  have hde : ∀ i j, B (d i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hBs.eq, hed j i]
    split_ifs with h1 h2 h2
    · exact map_one _
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact map_zero _
  have hdd : ∀ i j, B (d i) (d j) = 0 := by
    intro i j
    have h1 : B (gv i) (d j) = m i j + c j i := by
      rw [hd_right]
      simp [hge, hm]
    have h2 : ∑ k, h.bar (c i k) * B (e k) (d j) = h.bar (c i j) := by
      simp [hed]
    rw [hd_left, h1, h2, add_assoc, hcc, CharTwo.add_self_eq_zero]
  have hli : LinearIndependent K (Sum.elim e d) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha x
    rw [Fintype.sum_sum_type] at ha
    simp only [Sum.elim_inl, Sum.elim_inr] at ha
    rcases x with x | x
    · have h1 := congrArg (B (d x)) ha
      rw [map_zero, map_add, map_sum, map_sum] at h1
      simp only [map_smul, smul_eq_mul, hde, hdd, mul_ite, mul_one, mul_zero, Finset.sum_const_zero,
        add_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h1
      exact h1
    · have h1 := congrArg (B (e x)) ha
      rw [map_zero, map_add, map_sum, map_sum] at h1
      simp only [map_smul, smul_eq_mul, hee, hed, mul_ite, mul_one, mul_zero,
        Finset.sum_const_zero, zero_add, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h1
      exact h1
  have hspan : Submodule.span K (Set.range (Sum.elim e d)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_sum, Fintype.card_fin, Module.finrank_fin_fun, ← hnl])
  have hexp : ∀ v, v = ∑ k, B (d k) v • e k + ∑ k, B (e k) v • d k := by
    intro v
    set y := v - (∑ k, B (d k) v • e k + ∑ k, B (e k) v • d k) with hy
    have hyz : ∀ z ∈ Set.range (Sum.elim e d), B z y = 0 := by
      rintro _ ⟨x | x, rfl⟩
      · simp only [Sum.elim_inl, hy, map_sub, map_add, map_sum, map_smul, smul_eq_mul, hee, hed,
          mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true, sub_self]
      · simp only [Sum.elim_inr, hy, map_sub, map_add, map_sum, map_smul, smul_eq_mul, hde, hdd,
          mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true, sub_self]
    have hker : Submodule.span K (Set.range (Sum.elim e d)) ≤ LinearMap.ker (B.flip y) :=
      Submodule.span_le.mpr fun z hz => by
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
        exact hyz z hz
    rw [hspan] at hker
    have hy0 : y = 0 := hBsep y fun z => by
      have h1 : B z y = 0 := by
        have := hker (Submodule.mem_top (x := z))
        rwa [LinearMap.mem_ker, LinearMap.flip_apply] at this
      rw [← hBs.eq, h1, map_zero]
    exact sub_eq_zero.mp hy0
  refine ⟨e, d, ⟨hee, hdd, hed, hde, hexp, fun v => ?_⟩⟩
  have hNe : ∀ k, N *ᵥ e k = 0 := fun k => hNN _
  have hNd : ∀ k, N *ᵥ d k = e k := by
    intro k
    rw [hd, mulVec_add, mulVec_sum]
    simp only [mulVec_smul, hNe, smul_zero, Finset.sum_const_zero, add_zero]
    rfl
  have h1 : s *ᵥ v = v + N *ᵥ v := by rw [hNv, add_sub_cancel]
  rw [h1]
  congr 1
  conv_lhs => rw [hexp v]
  rw [mulVec_add, mulVec_sum, mulVec_sum]
  simp only [mulVec_smul, hNe, hNd, smul_zero, Finset.sum_const_zero, zero_add]
  rfl

end UnitaryLagrangian

end CFSG.SeitzReduction
