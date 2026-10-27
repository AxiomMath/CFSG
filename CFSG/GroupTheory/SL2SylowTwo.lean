module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Timmesfeld.RankOne.SL2
import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem exists_SL2_hom_map_sylowTwo_eq_upperUnipotent {L P : Subgroup G} {n : ℕ}
    (hL2 : IsL2Quot n (oTwoQuot ↥L)) (hP : IsSylowTwoOf P L) :
    ∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (pCoreOf 2 L).subgroupOf L ∧
      (P.subgroupOf L).map φ = CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n) := by
  classical
  let K := GaloisField 2 n
  obtain ⟨e2⟩ := hL2
  let eSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) K := CFSG.Quasithin.pslTwoGf2EquivSl n
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    eSL.toMonoidHom.comp (e2.toMonoidHom.comp q)
  have hφs : Function.Surjective φ :=
    eSL.surjective.comp (e2.surjective.comp (QuotientGroup.mk'_surjective _))
  have hφker : φ.ker = (pCoreOf 2 L).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : e2 (q x) = 1 := eSL.injective (by simpa [φ] using hx)
      have h2 : q x = 1 := e2.injective (by simpa using h1)
      have h3 : x ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff x).mp h2
      exact Subgroup.mem_map.mpr ⟨x, h3, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hxy : x = y := Subtype.ext hyx.symm
      have h3 : x ∈ CFSG.pCore 2 ↥L := hxy ▸ hy
      have h2 : q x = 1 := (QuotientGroup.eq_one_iff x).mpr h3
      simpa [φ, h2]
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hKcard⟩ := FiniteField.card K 2
  have hKcard' : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hKcard]
  have hSyl : IsSylowTwoOf ((P.subgroupOf L).map φ) ⊤ :=
    CFSG.Quasithin.Vol2.Ch10.SecA.isSylowTwoOf_map_of_surjective hP φ hφs
  have hUcard : Nat.card ↥((P.subgroupOf L).map φ) = Nat.card K := by
    rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_eq_of_isSylowTwoOf_top hSyl
      (Nat.Even.sub_odd (Nat.one_le_pow (m : ℕ) 4 (by norm_num))
        (Even.pow_of_ne_zero (n := (m : ℕ)) (by norm_num : Even 4) m.pos.ne')
        (by norm_num : Odd 1))
      (CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_two_pow hKcard'), hKcard']
  obtain ⟨g, hg⟩ := CFSG.SL2MinimalFaithful.exists_conj_unipotent_mem
    (F := K) (p := 2) (f := (m : ℕ)) Nat.prime_two hKcard' hUcard
  have huni : ∀ t : K, CFSG.SL2MinimalFaithful.unipotent t = CFSG.Timmesfeld.RankOne.upperElt K t :=
    fun t => Subtype.ext rfl
  have hle : (CFSG.Timmesfeld.upperUnipotent K).map (MulAut.conj g).toMonoidHom ≤
      (P.subgroupOf L).map φ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff K).1 hz
    change (MulAut.conj g) (CFSG.Timmesfeld.RankOne.upperElt K t) ∈ (P.subgroupOf L).map φ
    rw [MulAut.conj_apply]
    simpa [huni] using hg t
  have hUeq : (CFSG.Timmesfeld.upperUnipotent K).map (MulAut.conj g).toMonoidHom =
      (P.subgroupOf L).map φ :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective, CFSG.Timmesfeld.RankOne.card_upperUnipotent, hUcard])
  let φ' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp φ
  have hφ's : Function.Surjective φ' := (MulAut.conj g⁻¹).surjective.comp hφs
  have hφ'ker : φ'.ker = (pCoreOf 2 L).subgroupOf L := by
    ext x
    show (MulAut.conj g⁻¹) (φ x) = 1 ↔ x ∈ (pCoreOf 2 L).subgroupOf L
    rw [MulEquiv.map_eq_one_iff, ← hφker]
    rfl
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = MonoidHom.id (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine MonoidHom.ext fun x => ?_
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hU'eq : (P.subgroupOf L).map φ' = CFSG.Timmesfeld.upperUnipotent K := by
    have h1 : (P.subgroupOf L).map φ' = ((P.subgroupOf L).map φ).map
        (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [h1, ← hUeq, Subgroup.map_map, hcomp, Subgroup.map_id]
  exact ⟨φ', hφ's, hφ'ker, hU'eq⟩

end CFSG.GroupTheory
