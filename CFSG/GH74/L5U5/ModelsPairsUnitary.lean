module

public import CFSG.GH74.L5U5.ModelsPairs
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_apply_blockIdx blockIdx)
open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups

section Transport

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem unitaryBlockStandardPair_map' {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair F p f W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    Phan.UnitaryBlockStandardPair F p f (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem weakPhanA_map_equiv {X Y : Type} [Group X] [Group Y] {n : ℕ}
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X}
    (h : Phan.WeakPhanA F p f n U W) (e : X ≃* Y) :
    Phan.WeakPhanA F p f n (fun i => (U i).map e.toMonoidHom)
      (fun i j => (W i j).map e.toMonoidHom) where
  iso i := by
    obtain ⟨φ⟩ := h.iso i
    exact ⟨φ.trans ((U i).equivMapOfInjective e.toMonoidHom e.injective)⟩
  join i j hij := by rw [h.join i j hij, Subgroup.map_sup]
  comm i j hij := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h.comm i j hij x hx y hy]
  pair i j hj := unitaryBlockStandardPair_map' (h.pair i j hj) e.toMonoidHom e.injective
  gen := by
    rw [← Subgroup.map_iSup, h.gen]
    exact Subgroup.map_top_of_surjective _ e.surjective

end Transport

section Blocks

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

@[expose] noncomputable def suEquiv (n : ℕ) : Phan.Su F p f n ≃* ↥(StatedSU n (p ^ f) F) :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU hF n)

theorem coe_suEquiv (n : ℕ) (x : Phan.Su F p f n) :
    ((suEquiv hF n x : ↥(StatedSU n (p ^ f) F)) : GL (Fin n) F) = (x : GL (Fin n) F) := rfl

theorem mem_uni_H2_iff {a : GL (Fin 2) F} :
    a ∈ (ModelData.uni hF).H2 ↔ a ∈ SUid (unitaryInvolution F p f) 2 := by
  change a ∈ StatedSU 2 (p ^ f) F ↔ _
  rw [← SUid_eq_statedSU hF 2]

theorem coe_suEquiv_blockEmb2_zero (A : Phan.Su F p f 2) :
    ((suEquiv hF 4 (Phan.blockEmb2 F p f 3 0 A) : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      blkL F (A : GL (Fin 2) F) := by
  apply Units.ext
  change blockMat 4 0 (((A : Phan.Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
  rw [blockMat_four_zero]
  rfl

theorem coe_suEquiv_blockEmb2_two (A : Phan.Su F p f 2) :
    ((suEquiv hF 4 (Phan.blockEmb2 F p f 3 2 A) : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      blkR F (A : GL (Fin 2) F) := by
  apply Units.ext
  change blockMat 4 2 (((A : Phan.Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
  rw [blockMat_four_two]
  rfl

theorem uni_J2_eq :
    (ModelData.uni hF).J2 =
      (Phan.blockEmb2 F p f 3 0).range.map (suEquiv hF 4).toMonoidHom := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, hga⟩ := ModelData.mem_J2.1 hg
    have ha' := (mem_uni_H2_iff hF).1 ha
    refine Subgroup.mem_map.2 ⟨Phan.blockEmb2 F p f 3 0 ⟨a, ha'⟩, ⟨⟨a, ha'⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((suEquiv hF 4 (Phan.blockEmb2 F p f 3 0 ⟨a, ha'⟩) : ↥(StatedSU 4 (p ^ f) F)) :
      GL (Fin 4) F) = _
    rw [coe_suEquiv_blockEmb2_zero, hga]
  · intro hg
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hg
    refine ModelData.mem_J2.2 ⟨(A : GL (Fin 2) F), (mem_uni_H2_iff hF).2 A.2, ?_⟩
    exact coe_suEquiv_blockEmb2_zero hF A

theorem uni_J4_eq :
    (ModelData.uni hF).J4 =
      (Phan.blockEmb2 F p f 3 2).range.map (suEquiv hF 4).toMonoidHom := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, hga⟩ := ModelData.mem_J4.1 hg
    have ha' := (mem_uni_H2_iff hF).1 ha
    refine Subgroup.mem_map.2 ⟨Phan.blockEmb2 F p f 3 2 ⟨a, ha'⟩, ⟨⟨a, ha'⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((suEquiv hF 4 (Phan.blockEmb2 F p f 3 2 ⟨a, ha'⟩) : ↥(StatedSU 4 (p ^ f) F)) :
      GL (Fin 4) F) = _
    rw [coe_suEquiv_blockEmb2_two, hga]
  · intro hg
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hg
    refine ModelData.mem_J4.2 ⟨(A : GL (Fin 2) F), (mem_uni_H2_iff hF).2 A.2, ?_⟩
    exact coe_suEquiv_blockEmb2_two hF A

end Blocks

section SystemUni

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices CFSG.GH74.Filter.ClassicalOdd

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

@[expose] noncomputable def negSu : Phan.Su F p f 2 :=
  ⟨(-1 : GL (Fin 2) F), (mem_uni_H2_iff hF).1 (ModelData.neg_one_mem_H2 _)⟩

@[expose] noncomputable def quatSu (_hF : Nat.card F = (p ^ f) ^ 2) : Phan.Su F p f 2 :=
  ⟨SpecialLinearGroup.toGL (slQuatI F),
    mem_SUid.2 ⟨(slQuatI F).2, isUni_quatI (σ := (unitaryInvolution F p f : F →+* F))⟩⟩

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem coe_coe_negSu_aux : (((-1 : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  simp

theorem coe_negSu : (((negSu hF : Phan.Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    -1 := coe_coe_negSu_aux

theorem negSu_mul_self : negSu hF * negSu hF = 1 :=
  Subtype.ext (by
    change (-1 : GL (Fin 2) F) * (-1 : GL (Fin 2) F) = 1
    rw [neg_mul_neg, one_mul])

theorem negSu_ne_one (h2 : (2 : F) ≠ 0) : negSu hF ≠ 1 := fun h =>
  ModelData.neg_one_ne_one_gl2 h2 (congrArg Subtype.val h)

theorem orderOf_negSu (h2 : (2 : F) ≠ 0) : orderOf (negSu hF) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact negSu_mul_self hF) (negSu_ne_one hF h2)

theorem blockEmb2_negSu_comm (i j : Fin 3) :
    Phan.blockEmb2 F p f 3 i (negSu hF) * Phan.blockEmb2 F p f 3 j (negSu hF) =
      Phan.blockEmb2 F p f 3 j (negSu hF) * Phan.blockEmb2 F p f 3 i (negSu hF) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [Phan.coe_coe_blockEmb2, Phan.coe_coe_blockEmb2, coe_negSu]
  exact blockMat_neg_one_comm 4 i j

theorem blockEmb2_zero_negSu_not_comm (h2 : (2 : F) ≠ 0) :
    Phan.blockEmb2 F p f 3 0 (negSu hF) * Phan.blockEmb2 F p f 3 1 (quatSu hF) ≠
      Phan.blockEmb2 F p f 3 1 (quatSu hF) * Phan.blockEmb2 F p f 3 0 (negSu hF) := by
  intro h
  have h' := congrArg (fun g : Phan.Su F p f 4 =>
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul] at h'
  rw [Phan.coe_coe_blockEmb2, Phan.coe_coe_blockEmb2, coe_negSu] at h'
  refine blockMat_zero_neg_one_not_comm h2
    (((quatSu hF : Phan.Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ?_ h'
  change quatI F 0 1 = 1
  simp [quatI]

theorem equiv_blockEmb2_zero_negSu :
    suEquiv hF 4 (Phan.blockEmb2 F p f 3 0 (negSu hF)) = (ModelData.uni hF).yK := by
  apply Subtype.ext
  rw [coe_suEquiv_blockEmb2_zero]
  rfl

include hF in
theorem exists_system_uni {K : Type} [Group K] (hq : p ^ f % 4 = 1)
    (e : K ≃* StatedSU 4 (p ^ f) F) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (x y z₃ : K) (J₂ J₃ J₄ : Subgroup K)
      (U : Fin 3 → Subgroup K) (W : Fin 3 → Fin 3 → Subgroup K),
      Nat.card F' = p ^ f ∧ IsFrame F' x y J₂ J₄ ∧ Phan.WeakPhanA F p f 3 U W ∧
      U 0 = J₂ ∧ U 1 = J₃ ∧ U 2 = J₄ ∧
      z₃ ∈ J₃ ∧ orderOf z₃ = 2 ∧ y * z₃ = z₃ * y ∧ x * y * z₃ = z₃ * (x * y) ∧
      ¬ (∀ b ∈ J₃, y * b = b * y) := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have h2 := two_ne_zero_of_odd_card (F := F) hodd
  obtain ⟨e2⟩ := nonempty_sl2_equiv_uni_H2 hF
  have hfr := isFrame_of_model (ModelData.uni hF) h2 e e2
  let Φ : Phan.Su F p f 4 ≃* K := (suEquiv hF 4).trans e.symm
  have hsys := weakPhanA_map_equiv (Phan.weakPhanA_standard hF (by omega : p ^ f ≠ 2) 3) Φ
  have hy : e.symm (ModelData.uni hF).yK = Φ (Phan.blockEmb2 F p f 3 0 (negSu hF)) := by
    change e.symm _ = e.symm (suEquiv hF 4 (Phan.blockEmb2 F p f 3 0 (negSu hF)))
    rw [equiv_blockEmb2_zero_negSu]
  have hcomm₃ : e.symm (ModelData.uni hF).yK * Φ (Phan.blockEmb2 F p f 3 1 (negSu hF)) =
      Φ (Phan.blockEmb2 F p f 3 1 (negSu hF)) * e.symm (ModelData.uni hF).yK := by
    rw [hy, ← map_mul, ← map_mul, blockEmb2_negSu_comm hF 0 1]
  refine ⟨↥(fixedSubfield F p f), inferInstance, inferInstance, e.symm (ModelData.uni hF).xK,
    e.symm (ModelData.uni hF).yK, Φ (Phan.blockEmb2 F p f 3 1 (negSu hF)),
    (ModelData.uni hF).J2.map e.symm.toMonoidHom,
    (Phan.blockEmb2 F p f 3 1).range.map Φ.toMonoidHom,
    (ModelData.uni hF).J4.map e.symm.toMonoidHom,
    fun i => (Phan.blockEmb2 F p f 3 i).range.map Φ.toMonoidHom,
    fun i j => ((Phan.blockEmb2 F p f 3 i).range ⊔
      (Phan.blockEmb2 F p f 3 j).range).map Φ.toMonoidHom,
    card_fixedSubfield hF, hfr, hsys, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (Phan.blockEmb2 F p f 3 0).range.map Φ.toMonoidHom = _
    rw [uni_J2_eq, Subgroup.map_map]
    rfl
  · change (Phan.blockEmb2 F p f 3 2).range.map Φ.toMonoidHom = _
    rw [uni_J4_eq, Subgroup.map_map]
    rfl
  · exact Subgroup.mem_map.2 ⟨Phan.blockEmb2 F p f 3 1 (negSu hF), ⟨negSu hF, rfl⟩, rfl⟩
  · rw [MulEquiv.orderOf_eq, orderOf_injective _ (Phan.blockEmb2_injective 3 1)]
    exact orderOf_negSu hF h2
  · exact hcomm₃
  · exact comm_of_center hfr.x_mem_center hcomm₃
  · intro hall
    have hb : Φ (Phan.blockEmb2 F p f 3 1 (quatSu hF)) ∈
        (Phan.blockEmb2 F p f 3 1).range.map Φ.toMonoidHom :=
      Subgroup.mem_map.2 ⟨Phan.blockEmb2 F p f 3 1 (quatSu hF), ⟨quatSu hF, rfl⟩, rfl⟩
    have := hall _ hb
    rw [hy, ← map_mul, ← map_mul] at this
    exact blockEmb2_zero_negSu_not_comm hF h2 (Φ.injective this)

end SystemUni

section StandardPairThree

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_standard_pair_uni {K₃ : Type} [Group K₃] (hF : Nat.card F = (p ^ f) ^ 2)
    (hq : p ^ f ≠ 2) (e : K₃ ≃* StatedSU 3 (p ^ f) F) :
    ∃ J_a J_b : Subgroup K₃, J_a ⊔ J_b = ⊤ ∧
      Phan.UnitaryBlockStandardPair F p f (J_a ⊔ J_b) J_a J_b ∧
      Nonempty (Phan.Su F p f 2 ≃* J_a) ∧ Nonempty (Phan.Su F p f 2 ≃* J_b) := by
  let Φ : Phan.Su F p f 3 ≃* K₃ := (suEquiv hF 3).trans e.symm
  have hsys := weakPhanA_map_equiv (Phan.weakPhanA_standard hF hq 2) Φ
  refine ⟨(Phan.blockEmb2 F p f 2 0).range.map Φ.toMonoidHom,
    (Phan.blockEmb2 F p f 2 1).range.map Φ.toMonoidHom, ?_, ?_, hsys.iso 0, hsys.iso 1⟩
  · rw [← Subgroup.map_sup]
    have hgen : (Phan.blockEmb2 F p f 2 0).range ⊔ (Phan.blockEmb2 F p f 2 1).range = ⊤ := by
      have := Phan.B12_sup_B23 hF hq
      rw [Phan.B12, Phan.B23, Phan.embSUid_two_eq_blockEmb, Phan.embSUid_zero_eq_blockEmb] at this
      exact this
    rw [hgen]
    exact Subgroup.map_top_of_surjective _ Φ.surjective
  · have h01 := hsys.pair 0 1 rfl
    have hj := hsys.join 0 1 (by decide)
    rw [hj] at h01
    exact h01

end StandardPairThree

end CFSG.GH74.L5U5
