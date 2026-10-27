module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.ClassicalInvolution.Phan.Frames.BlockStab
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def fixSU (S : Set (Fin 4 → K)) : Subgroup (Su K 2 1 4) :=
  ⨅ v ∈ S, MulAction.stabilizer (Su K 2 1 4) v

theorem fixSU_smul (g : Su K 2 1 4) (S : Set (Fin 4 → K)) :
    fixSU (g • S) = (fixSU S).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [fixSU, Subgroup.mem_iInf, Subgroup.mem_map, MulAut.conj_apply,
    MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · intro v hv
      have h1 := hx (g • v) (Set.smul_mem_smul_set hv)
      calc (g⁻¹ * x * g) • v = g⁻¹ • (x • (g • v)) := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • v) := by rw [h1]
        _ = v := by rw [inv_smul_smul]
    · group
  · rintro ⟨y, hy, rfl⟩
    intro v hv
    rcases hv with ⟨u, hu, rfl⟩
    calc (g * y * g⁻¹) • (g • u) = g • (y • (g⁻¹ • (g • u))) := by rw [mul_smul, mul_smul]
      _ = g • (y • u) := by rw [inv_smul_smul]
      _ = g • u := by rw [hy u hu]

theorem fixSU_std :
    fixSU {Pi.single 3 (1 : K)} = (blk012 K).range ∧
    fixSU {Pi.single 0 (1 : K)} = (blk123 K).range ∧
    fixSU {Pi.single 2 (1 : K), Pi.single 3 (1 : K)} = (B12 K 2 1).map (blk012 K) ∧
    fixSU {Pi.single 0 (1 : K), Pi.single 3 (1 : K)} = (B23 K 2 1).map (blk012 K) ∧
    fixSU {Pi.single 0 (1 : K), Pi.single 1 (1 : K)} = (B23 K 2 1).map (blk123 K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    have h1 : x ∈ fixSU {Pi.single 3 (1 : K)} ↔ x • (Pi.single 3 (1 : K) : Fin 4 → K) = (Pi.single 3 (1 : K) : Fin 4 → K) := by
      simp [fixSU, MulAction.mem_stabilizer_iff]
    rw [h1, show blk012 K = blockEmb K 2 1 4 3 0 (by norm_num) from rfl,
      mem_range_blockEmb_iff]
    constructor
    · intro hx l hl
      have hl3 : l.val = 3 := by omega
      have hl_eq : l = ⟨3, by norm_num⟩ := Fin.ext hl3
      simpa [hl_eq] using hx
    · intro hx
      have h3 := hx 3 (by norm_num)
      simpa using h3
  · ext x
    have h1 : x ∈ fixSU {Pi.single 0 (1 : K)} ↔ x • (Pi.single 0 (1 : K) : Fin 4 → K) = (Pi.single 0 (1 : K) : Fin 4 → K) := by
      simp [fixSU, MulAction.mem_stabilizer_iff]
    rw [h1, show blk123 K = blockEmb K 2 1 4 3 1 (by norm_num) from rfl,
      mem_range_blockEmb_iff]
    constructor
    · intro hx l hl
      have hl0 : l.val = 0 := by omega
      have hl_eq : l = ⟨0, by norm_num⟩ := Fin.ext hl0
      simpa [hl_eq] using hx
    · intro hx
      have h0 := hx 0 (by norm_num)
      simpa using h0
  · have hcomp : (blk012 K).comp (embSUid (unitaryInvolution K 2 1) 2) =
        blockEmb K 2 1 4 2 0 (by norm_num) := by
      rw [show blk012 K = blockEmb K 2 1 4 3 0 (by norm_num) from rfl]
      rw [embSUid_two_eq_blockEmb, blockEmb_comp]
    rw [show B12 K 2 1 = (embSUid (unitaryInvolution K 2 1) 2).range from rfl]
    rw [← MonoidHom.range_comp]
    rw [hcomp]
    ext x
    have h1 : x ∈ fixSU {Pi.single 2 (1 : K), Pi.single 3 (1 : K)} ↔
        (x • (Pi.single 2 (1 : K) : Fin 4 → K) = (Pi.single 2 (1 : K) : Fin 4 → K) ∧
         x • (Pi.single 3 (1 : K) : Fin 4 → K) = (Pi.single 3 (1 : K) : Fin 4 → K)) := by
      simp [fixSU, MulAction.mem_stabilizer_iff]
    rw [h1, mem_range_blockEmb_iff]
    constructor
    · rintro ⟨h2, h3⟩ l hl
      have hl2 : l.val = 2 ∨ l.val = 3 := by omega
      rcases hl2 with h2' | h3'
      · have hl_eq : l = ⟨2, by norm_num⟩ := Fin.ext h2'
        simpa [hl_eq] using h2
      · have hl_eq : l = ⟨3, by norm_num⟩ := Fin.ext h3'
        simpa [hl_eq] using h3
    · intro hx
      constructor
      · simpa using hx 2 (by norm_num)
      · simpa using hx 3 (by norm_num)
  · have hcomp : (blk012 K).comp (embSUid (unitaryInvolution K 2 1) 0) =
        blockEmb K 2 1 4 2 1 (by norm_num) := by
      rw [show blk012 K = blockEmb K 2 1 4 3 0 (by norm_num) from rfl]
      rw [embSUid_zero_eq_blockEmb, blockEmb_comp]
    rw [show B23 K 2 1 = (embSUid (unitaryInvolution K 2 1) 0).range from rfl]
    rw [← MonoidHom.range_comp]
    rw [hcomp]
    ext x
    have h1 : x ∈ fixSU {Pi.single 0 (1 : K), Pi.single 3 (1 : K)} ↔
        (x • (Pi.single 0 (1 : K) : Fin 4 → K) = (Pi.single 0 (1 : K) : Fin 4 → K) ∧
         x • (Pi.single 3 (1 : K) : Fin 4 → K) = (Pi.single 3 (1 : K) : Fin 4 → K)) := by
      simp [fixSU, MulAction.mem_stabilizer_iff]
    rw [h1, mem_range_blockEmb_iff]
    constructor
    · rintro ⟨h0, h3⟩ l hl
      have hl2 : l.val = 0 ∨ l.val = 3 := by omega
      rcases hl2 with h0' | h3'
      · have hl_eq : l = ⟨0, by norm_num⟩ := Fin.ext h0'
        simpa [hl_eq] using h0
      · have hl_eq : l = ⟨3, by norm_num⟩ := Fin.ext h3'
        simpa [hl_eq] using h3
    · intro hx
      constructor
      · simpa using hx 0 (by norm_num)
      · simpa using hx 3 (by norm_num)
  · have hcomp : (blk123 K).comp (embSUid (unitaryInvolution K 2 1) 0) =
        blockEmb K 2 1 4 2 2 (by norm_num) := by
      rw [show blk123 K = blockEmb K 2 1 4 3 1 (by norm_num) from rfl]
      rw [embSUid_zero_eq_blockEmb, blockEmb_comp]
    rw [show B23 K 2 1 = (embSUid (unitaryInvolution K 2 1) 0).range from rfl]
    rw [← MonoidHom.range_comp]
    rw [hcomp]
    ext x
    have h1 : x ∈ fixSU {Pi.single 0 (1 : K), Pi.single 1 (1 : K)} ↔
        (x • (Pi.single 0 (1 : K) : Fin 4 → K) = (Pi.single 0 (1 : K) : Fin 4 → K) ∧
         x • (Pi.single 1 (1 : K) : Fin 4 → K) = (Pi.single 1 (1 : K) : Fin 4 → K)) := by
      simp [fixSU, MulAction.mem_stabilizer_iff]
    rw [h1, mem_range_blockEmb_iff]
    constructor
    · rintro ⟨h0, h1'⟩ l hl
      have hl2 : l.val = 0 ∨ l.val = 1 := by omega
      rcases hl2 with h0' | h1''
      · have hl_eq : l = ⟨0, by norm_num⟩ := Fin.ext h0'
        simpa [hl_eq] using h0
      · have hl_eq : l = ⟨1, by norm_num⟩ := Fin.ext h1''
        simpa [hl_eq] using h1'
    · intro hx
      constructor
      · simpa using hx 0 (by norm_num)
      · simpa using hx 1 (by norm_num)

theorem eq_one_of_hom_Su_three {A : Type*} [Group A] (hK : Nat.card K = 4)
    (χ : Su K 2 1 3 →* A) (h3 : ∀ a : A, a ^ 3 = 1) : χ = 1 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hgen := (CFSG.LocalAnalysis.RankThreeTheoremC.kFactSUThreeTwoShape_holds K hK).1
  let e : Su K 2 1 3 ≃* ↥(CFSG.Open.StatedSU 3 2 K) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF 3)
  have hgen_su : Subgroup.closure {x : Su K 2 1 3 | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ := by
    have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
    rw [MonoidHom.map_closure, Subgroup.map_top] at hmap
    have hset : ⇑e.symm.toMonoidHom '' {x : ↥(CFSG.Open.StatedSU 3 2 K) | ∃ k, x ^ 2^k = 1} =
        {x : Su K 2 1 3 | ∃ k, x ^ 2^k = 1} := by
      ext x
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, ⟨k, hk⟩, rfl⟩
        exact ⟨k, by rw [← map_pow, hk, map_one]⟩
      · intro ⟨k, hk⟩
        refine ⟨e x, ⟨k, ?_⟩, by simp⟩
        rw [← map_pow, hk, map_one]
    rw [hset] at hmap
    rw [MonoidHom.range_eq_top.mpr (by simpa using e.symm.surjective)] at hmap
    exact hmap
  apply MonoidHom.ext
  intro x
  have hx : x ∈ Subgroup.closure {x : Su K 2 1 3 | ∃ k : ℕ, x ^ (2 ^ k) = 1} := by
    rw [hgen_su]; exact Subgroup.mem_top x
  refine Subgroup.closure_induction (p := fun y _ => χ y = 1) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨k, hk⟩ := hy
    have h2k : (χ y) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have h3y : (χ y) ^ 3 = 1 := h3 (χ y)
    have hdvd2 : orderOf (χ y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
    have hdvd3 : orderOf (χ y) ∣ 3 := orderOf_dvd_of_pow_eq_one h3y
    have hcop : Nat.Coprime (2 ^ k) 3 := by
      have hodd : Odd 3 := by norm_num
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
    have hone : orderOf (χ y) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd3
    exact orderOf_eq_one_iff.mp hone
  · exact map_one χ
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb, one_mul]
  · intro a _ ha
    rw [map_inv, ha, inv_one]

end CFSG.ClassicalInvolution.PhanDn.QTwo

end
