module

public import CFSG.LargeExtraspecial.Setting
public import CFSG.Monster.GMS.Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Monster.GMS

theorem map_center_of_mulEquiv {P R : Type*} [Group P] [Group R] (e : P ≃* R) :
    (center P).map e.toMonoidHom = center R := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {P R : Type*} [Group P] [Group R]
    (e : P ≃* R) (h : IsExtraspecialPGroup p P) : IsExtraspecialPGroup p R := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator P).map e.toMonoidHom = commutator R := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini P).map e.toMonoidHom = frattini R :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, map_center_of_mulEquiv]
  · rw [← hf, hfrat, map_center_of_mulEquiv]
  · rw [← map_center_of_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]

namespace Setting

variable {G G' : Type*} [Group G] [Group G']

@[expose] noncomputable def map (S : Setting G) (e : G ≃* G') : Setting G' where
  z := e S.z
  orderOf_z := by rw [MulEquiv.orderOf_eq, S.orderOf_z]
  Q := S.Q.map (centralizerMulEquiv e S.z).toMonoidHom
  normal := S.normal.map _ (centralizerMulEquiv e S.z).surjective
  extraspecial := isExtraspecialPGroup_of_mulEquiv
    ((centralizerMulEquiv e S.z).subgroupMap S.Q) S.extraspecial
  centralizer_le := by
    set f := centralizerMulEquiv e S.z
    intro y hy
    obtain ⟨x, rfl⟩ := f.surjective y
    refine ⟨x, S.centralizer_le ?_, rfl⟩
    rw [mem_centralizer_iff] at hy ⊢
    intro q hq
    apply f.injective
    rw [map_mul, map_mul]
    exact hy (f q) ⟨q, hq, rfl⟩
  le_of_normal := by
    set f := centralizerMulEquiv e S.z
    intro P hP h2
    have hle := S.le_of_normal (P.comap f.toMonoidHom) (hP.comap _)
      (h2.comap_of_injective _ f.injective)
    intro y hy
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨x, hle (by simpa using hy), rfl⟩

@[simp] theorem map_z (S : Setting G) (e : G ≃* G') : (S.map e).z = e S.z := rfl

theorem map_QG (S : Setting G) (e : G ≃* G') : (S.map e).QG = S.QG.map e.toMonoidHom := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem QG_le_of_z_eq [Finite G] (S T : Setting G) (h : S.z = T.z) : S.QG ≤ T.QG := by
  obtain ⟨zS, oS, QS, nS, eS, cS, lS⟩ := S
  obtain ⟨zT, oT, QT, nT, eT, cT, lT⟩ := T
  simp only at h
  subst h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Subgroup.map_mono (lT QS nS eS.1)

theorem QG_eq_of_z_eq [Finite G] (S T : Setting G) (h : S.z = T.z) : S.QG = T.QG :=
  le_antisymm (S.QG_le_of_z_eq T h) (T.QG_le_of_z_eq S h.symm)

@[expose] noncomputable def conjBy (S : Setting G) (g : G) : Setting G := S.map (MulAut.conj g)

@[simp] theorem conjBy_z (S : Setting G) (g : G) : (S.conjBy g).z = g * S.z * g⁻¹ := rfl

@[expose] noncomputable def Qa (S : Setting G) (g : G) : Subgroup G := (S.conjBy g).QG

theorem Qa_eq_map (S : Setting G) (g : G) :
    S.Qa g = S.QG.map (MulAut.conj g).toMonoidHom := map_QG S _

theorem Qa_eq_of_conj_eq [Finite G] (S : Setting G) {g h : G}
    (hgh : g * S.z * g⁻¹ = h * S.z * h⁻¹) : S.Qa g = S.Qa h :=
  QG_eq_of_z_eq _ _ hgh

theorem Qa_one [Finite G] (S : Setting G) : S.Qa 1 = S.QG := by
  rw [Qa_eq_map]
  ext x
  simp

end Setting

end CFSG.LargeExtraspecial
