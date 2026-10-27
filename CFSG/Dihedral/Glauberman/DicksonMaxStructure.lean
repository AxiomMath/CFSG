module

public import CFSG.CharacterTheory.PSL2Table.Partition
public import CFSG.CharacterTheory.PSL2Table.Classes
public import CFSG.Dihedral.Glauberman.DicksonMaxExist
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.IntegralDomain
public import CFSG.CharacterTheory.PSL2Table.Halves
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import Certificates.Certificate43

public section

namespace CFSG.Glauberman.Dickson.MaxStructure

open CFSG.PSL2Table BenderSuzuki.MatrixGroups
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {F : Type} [Field F]

theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem isCoatom_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    IsCoatom (H.map (MulAut.conj g).toMonoidHom) ↔ IsCoatom H := by
  have h : H.map (MulAut.conj g).toMonoidHom = (MulAut.conj g).mapSubgroup H := rfl
  rw [h, OrderIso.isCoatom_iff]

theorem normalizer_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx h
    have h1 := hx (g * h * g⁻¹)
    simp only [mem_map_conj_iff] at h1
    have e1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    have e2 : g⁻¹ * (x * (g * h * g⁻¹) * x⁻¹) * g =
        g⁻¹ * x * g * h * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  · intro hx h
    simp only [mem_map_conj_iff]
    have h1 := hx (g⁻¹ * h * g)
    have e2 : g⁻¹ * x * g * (g⁻¹ * h * g) * (g⁻¹ * x * g)⁻¹ =
        g⁻¹ * (x * h * x⁻¹) * g := by group
    rw [e2] at h1
    exact h1

theorem card_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem stabilizer_lineZero :
    MulAction.stabilizer PSL(2, F) (lineZero F) = borel F := by
  ext x
  obtain ⟨A, rfl⟩ := mk_surjective x
  rw [MulAction.mem_stabilizer_iff, mk_mem_borel_iff, mem_borelSL_iff, lineZero, mk_smul_proj,
    show Projectivization.mk F ![1, 0] e0_ne_zero = lineZero F from rfl, mk_eq_lineZero_iff]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem isCoatom_stabilizer [Finite F] (x : ℙ F (Fin 2 → F)) :
    IsCoatom (MulAction.stabilizer PSL(2, F) x) := by
  have : Nontrivial (ℙ F (Fin 2 → F)) := by
    refine ⟨⟨lineZero F, lineOne F, lineZero_ne_lineOne⟩⟩
  rw [MulAction.isCoatom_stabilizer_iff_preprimitive]
  infer_instance

theorem exists_stabilizer_eq_iff [Finite F] (H : Subgroup PSL(2, F)) :
    (∃ x : ℙ F (Fin 2 → F), H = MulAction.stabilizer PSL(2, F) x) ↔
      ∃ g : PSL(2, F), H = (borel F).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, F) (lineZero F) x
    refine ⟨g, ?_⟩
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_lineZero]
  · rintro ⟨g, rfl⟩
    refine ⟨g • lineZero F, ?_⟩
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_lineZero]

theorem nonsplitTorus_isCyclic [Finite F] {ν : F} (hν : ¬ IsSquare ν) :
    IsCyclic (nonsplitTorus ν) := by
  classical
  have : Fact (¬ IsSquare ν) := ⟨hν⟩
  let ψ : nonsplitSL ν →* QuadraticAlgebra F ν 0 :=
    { toFun := fun A => ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 1 0⟩
      map_one' := by
        ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      map_mul' := by
        rintro ⟨A, hA1, hA2⟩ ⟨B, hB1, hB2⟩
        ext
        · simp only [Subgroup.coe_mul, mul_apply_SL, QuadraticAlgebra.re_mul]
          rw [hA2]
        · simp only [Subgroup.coe_mul, mul_apply_SL, QuadraticAlgebra.im_mul]
          rw [hA1]
          ring }
  have hψ : Function.Injective ψ := by
    rintro ⟨A, hA1, hA2⟩ ⟨B, hB1, hB2⟩ h
    have h0 := congrArg QuadraticAlgebra.re h
    have h1 := congrArg QuadraticAlgebra.im h
    change (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (B : Matrix (Fin 2) (Fin 2) F) 0 0 at h0
    change (A : Matrix (Fin 2) (Fin 2) F) 1 0 = (B : Matrix (Fin 2) (Fin 2) F) 1 0 at h1
    apply Subtype.ext
    exact SL_ext h0 (by rw [hA2, hB2, h1]) h1 (by rw [hA1, hB1, h0])
  have : IsCyclic (nonsplitSL ν) := isCyclic_of_injective_ringHom ψ hψ
  exact isCyclic_of_surjective
    ((mk : SL(2, F) →* PSL(2, F)).comp (nonsplitSL ν).subtype |>.rangeRestrict)
    (MonoidHom.rangeRestrict_surjective _) |> fun h => by
      have e : ((mk : SL(2, F) →* PSL(2, F)).comp (nonsplitSL ν).subtype).range =
          nonsplitTorus ν := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
        rfl
      rw [← e]
      exact h

theorem normalizer_le_of_TI {G : Type*} [Group G] {A Nb : Subgroup G}
    (hTI : ∀ x ∈ A, x ≠ 1 → ∀ g : G, g * x * g⁻¹ ∈ A → g ∈ Nb) (c : G) {R : Subgroup G}
    (hR : R ≤ A.map (MulAut.conj c).toMonoidHom) (hR1 : R ≠ ⊥) :
    Subgroup.normalizer (R : Set G) ≤ Nb.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨y, hyR, hy1⟩ : ∃ y ∈ R, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hR1 (eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (hcon y hy))
  intro m hm
  rw [mem_map_conj_iff]
  have hy : c⁻¹ * (y : G) * c ∈ A := (mem_map_conj_iff A c y).mp (hR hyR)
  have hmy : m * y * m⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hm y).mp hyR
  have hmyA : c⁻¹ * (m * y * m⁻¹) * c ∈ A := (mem_map_conj_iff A c _).mp (hR hmy)
  apply hTI _ hy (fun h => hy1 (by
    have : (y : G) = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [this, h]
    simp))
  have e : c⁻¹ * m * c * (c⁻¹ * (y : G) * c) * (c⁻¹ * m * c)⁻¹ =
      c⁻¹ * (m * y * m⁻¹) * c := by group
  rw [e]
  exact hmyA

variable [Fintype F]

theorem normalizer_splitTorus_eq (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    Subgroup.normalizer (splitTorus F : Set PSL(2, F)) =
      splitTorus F ⊔ Subgroup.zpowers (splitWeyl F) := by
  have hle : splitTorus F ⊔ Subgroup.zpowers (splitWeyl F) ≤
      Subgroup.normalizer (splitTorus F : Set PSL(2, F)) := by
    apply sup_le Subgroup.le_normalizer
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [splitWeyl_conj hx]
      exact (splitTorus F).inv_mem hx
    · intro hx
      have hw : splitWeyl F * (splitWeyl F * x * (splitWeyl F)⁻¹) * (splitWeyl F)⁻¹ = x := by
        have hww : (splitWeyl F)⁻¹ = splitWeyl F :=
          (eq_inv_of_mul_eq_one_left splitWeyl_mul_self).symm
        rw [hww]
        calc splitWeyl F * (splitWeyl F * x * splitWeyl F) * splitWeyl F =
            (splitWeyl F * splitWeyl F) * x * (splitWeyl F * splitWeyl F) := by group
          _ = x := by rw [splitWeyl_mul_self]; group
      rw [← hw, splitWeyl_conj hx]
      exact (splitTorus F).inv_mem hx
  obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral (splitTorus F) splitTorus_isCyclic
    (splitWeyl F) splitWeyl_not_mem splitWeyl_mul_self (fun c hc => splitWeyl_conj hc)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_normalizer_splitTorus hF hq, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem normalizer_nonsplitTorus_eq (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) : ∃ w : PSL(2, F), w ∉ nonsplitTorus ν ∧ w * w = 1 ∧
      (∀ x ∈ nonsplitTorus ν, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.normalizer (nonsplitTorus ν : Set PSL(2, F)) =
        nonsplitTorus ν ⊔ Subgroup.zpowers w := by
  obtain ⟨w, hwS, hww, hinv, -⟩ := exists_nonsplitWeyl hF hν
  refine ⟨w, hwS, hww, hinv, ?_⟩
  have hwinv : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hww).symm
  have hle : nonsplitTorus ν ⊔ Subgroup.zpowers w ≤
      Subgroup.normalizer (nonsplitTorus ν : Set PSL(2, F)) := by
    apply sup_le Subgroup.le_normalizer
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinv x hx]
      exact (nonsplitTorus ν).inv_mem hx
    · intro hx
      have hw : w * (w * x * w⁻¹) * w⁻¹ = x := by
        rw [hwinv]
        calc w * (w * x * w) * w = (w * w) * x * (w * w) := by group
          _ = x := by rw [hww]; group
      rw [← hw, hinv _ hx]
      exact (nonsplitTorus ν).inv_mem hx
  obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral (nonsplitTorus ν)
    (nonsplitTorus_isCyclic hν) w hwS hww hinv
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_normalizer_nonsplitTorus hF hq hν, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem card_splitTorus_eq (hF : ringChar F ≠ 2) :
    Nat.card (splitTorus F) = (Fintype.card F - 1) / 2 := by
  have := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  omega

theorem card_nonsplitTorus_eq (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    Nat.card (nonsplitTorus ν) = (Fintype.card F + 1) / 2 := by
  have := card_nonsplitTorus hF hν
  omega

theorem normalizer_splitTorus_mulEquiv (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    Nonempty (Subgroup.normalizer (splitTorus F : Set PSL(2, F)) ≃*
      DihedralGroup ((Fintype.card F - 1) / 2)) := by
  obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral (splitTorus F) splitTorus_isCyclic
    (splitWeyl F) splitWeyl_not_mem splitWeyl_mul_self (fun c hc => splitWeyl_conj hc)
  rw [card_splitTorus_eq hF] at e
  exact ⟨(MulEquiv.subgroupCongr (normalizer_splitTorus_eq hF hq)).trans e⟩

theorem normalizer_nonsplitTorus_mulEquiv (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) :
    Nonempty (Subgroup.normalizer (nonsplitTorus ν : Set PSL(2, F)) ≃*
      DihedralGroup ((Fintype.card F + 1) / 2)) := by
  obtain ⟨w, hwS, hww, hinv, heq⟩ := normalizer_nonsplitTorus_eq hF hq hν
  obtain ⟨e⟩ := nonempty_sup_zpowers_mulEquiv_dihedral (nonsplitTorus ν)
    (nonsplitTorus_isCyclic hν) w hwS hww hinv
  rw [card_nonsplitTorus_eq hF hν] at e
  exact ⟨(MulEquiv.subgroupCongr heq).trans e⟩

theorem normalizer_le_of_le_conj_splitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    (c : PSL(2, F)) {R : Subgroup PSL(2, F)}
    (hR : R ≤ (splitTorus F).map (MulAut.conj c).toMonoidHom) (hR1 : R ≠ ⊥) :
    Subgroup.normalizer (R : Set PSL(2, F)) ≤
      (Subgroup.normalizer (splitTorus F : Set PSL(2, F))).map (MulAut.conj c).toMonoidHom :=
  normalizer_le_of_TI (fun x hx hx1 g h => (splitTorus_TI hF hq x hx hx1 g).mp h) c hR hR1

theorem normalizer_le_of_le_conj_nonsplitTorus (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) (c : PSL(2, F)) {R : Subgroup PSL(2, F)}
    (hR : R ≤ (nonsplitTorus ν).map (MulAut.conj c).toMonoidHom) (hR1 : R ≠ ⊥) :
    Subgroup.normalizer (R : Set PSL(2, F)) ≤
      (Subgroup.normalizer (nonsplitTorus ν : Set PSL(2, F))).map
        (MulAut.conj c).toMonoidHom :=
  normalizer_le_of_TI (fun x hx hx1 g h => (nonsplitTorus_TI hF hq hν x hx hx1 g).mp h) c hR hR1

omit [Fintype F] in
theorem normalizer_le_of_le_conj_unipotent (hF : ringChar F ≠ 2) (c : PSL(2, F))
    {R : Subgroup PSL(2, F)} (hR : R ≤ (unipotent F).map (MulAut.conj c).toMonoidHom)
    (hR1 : R ≠ ⊥) :
    Subgroup.normalizer (R : Set PSL(2, F)) ≤ (borel F).map (MulAut.conj c).toMonoidHom :=
  normalizer_le_of_TI (fun x hx hx1 g h => (unipotent_TI hF x hx hx1 g).mp h) c hR hR1

end CFSG.Glauberman.Dickson.MaxStructure
