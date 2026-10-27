module

public import Mathlib.GroupTheory.PGroup
public import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG

theorem exists_fixed_subgroup_of_odd_ncard
    {Q X : Type*} [Group Q] [Group X] (hQ : IsPGroup 2 Q)
    (α : Q →* MulAut X) (Ω : Set (Subgroup X))
    (hfin : Ω.Finite) (hodd : Odd Ω.ncard)
    (hinv : ∀ q : Q, ∀ P ∈ Ω, P.map (α q).toMonoidHom ∈ Ω) :
    ∃ P ∈ Ω, ∀ q : Q, P.map (α q).toMonoidHom = P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI act : MulAction Q ↥Ω :=
    { smul := fun q P => ⟨P.1.map (α q).toMonoidHom, hinv q P.1 P.2⟩
      one_smul := fun P => Subtype.ext (by
        change P.1.map (α 1).toMonoidHom = P.1
        rw [map_one]
        exact Subgroup.map_id P.1)
      mul_smul := fun q r P => Subtype.ext (by
        change P.1.map (α (q * r)).toMonoidHom =
          (P.1.map (α r).toMonoidHom).map (α q).toMonoidHom
        rw [map_mul, Subgroup.map_map]
        rfl) }
  have hcard : Nat.card ↥Ω = Ω.ncard := Nat.card_coe_set_eq Ω
  have hnot : ¬ 2 ∣ Nat.card ↥Ω := by
    rw [hcard]
    exact hodd.not_two_dvd_nat
  obtain ⟨⟨P, hP⟩, hfix⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card (↥Ω) hnot
  exact ⟨P, hP, fun q => congrArg Subtype.val (hfix q)⟩

theorem exists_le_normalizer_of_odd_ncard
    {G X : Type*} [Group G] [Group X]
    {L : Subgroup G} [L.Normal] (e : ↥L ≃* X)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (Ω : Set (Subgroup X)) (hfin : Ω.Finite) (hodd : Odd Ω.ncard)
    (hinv : ∀ q ∈ Q, ∀ P ∈ Ω,
      P.map (MulAut.congr e (MulAut.conjNormal (q : G))).toMonoidHom ∈ Ω) :
    ∃ P ∈ Ω, Q ≤ Subgroup.normalizer
      ((P.map (L.subtype.comp e.symm.toMonoidHom) : Subgroup G) : Set G) := by
  classical
  let α : ↥Q →* MulAut X :=
    { toFun := fun q => MulAut.congr e (MulAut.conjNormal (q : G))
      map_one' := by
        ext x
        simp
      map_mul' := fun q r => by simp [map_mul] }
  have hinv' : ∀ q : ↥Q, ∀ P ∈ Ω, P.map (α q).toMonoidHom ∈ Ω := by
    intro q P hP
    exact hinv (q : G) q.2 P hP
  obtain ⟨P, hP, hfix⟩ :=
    exists_fixed_subgroup_of_odd_ncard hQ α Ω hfin hodd hinv'
  let P₀ : Subgroup ↥L := P.map e.symm.toMonoidHom
  have hcomp_e : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  have hP₀map : P₀.map e.toMonoidHom = P := by
    rw [Subgroup.map_map, hcomp_e, Subgroup.map_id]
  have hP₀fix (q : G) (hq : q ∈ Q) :
      P₀.map (MulAut.conjNormal q).toMonoidHom = P₀ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) (by simpa using e.injective)
    have hfixed : P.map (MulAut.congr e (MulAut.conjNormal q)).toMonoidHom = P := by
      exact hfix ⟨q, hq⟩
    calc
      (P₀.map (MulAut.conjNormal q).toMonoidHom).map e.toMonoidHom =
          (P₀.map e.toMonoidHom).map
            (MulAut.congr e (MulAut.conjNormal q)).toMonoidHom :=
        (CFSG.map_mulAut_congr e (MulAut.conjNormal q) P₀).symm
      _ = P := by rw [hP₀map, hfixed]
      _ = P₀.map e.toMonoidHom := hP₀map.symm
  refine ⟨P, hP, fun q hq => ?_⟩
  have himg : P.map (L.subtype.comp e.symm.toMonoidHom) = P₀.map L.subtype := by
    rw [Subgroup.map_map]
  have hcomp : (MulAut.conj q).toMonoidHom.comp L.subtype =
      L.subtype.comp (MulAut.conjNormal q).toMonoidHom := by
    ext l
    simp [MulAut.conj_apply, MulAut.conjNormal_apply]
  have hconj : (P₀.map L.subtype).map (MulAut.conj q).toMonoidHom =
      (P₀.map (MulAut.conjNormal q).toMonoidHom).map L.subtype := by
    calc
      (P₀.map L.subtype).map (MulAut.conj q).toMonoidHom =
          P₀.map ((MulAut.conj q).toMonoidHom.comp L.subtype) :=
        Subgroup.map_map P₀ (MulAut.conj q).toMonoidHom L.subtype
      _ = P₀.map (L.subtype.comp (MulAut.conjNormal q).toMonoidHom) := by rw [hcomp]
      _ = (P₀.map (MulAut.conjNormal q).toMonoidHom).map L.subtype :=
        (Subgroup.map_map P₀ L.subtype (MulAut.conjNormal q).toMonoidHom).symm
  rw [himg, Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj q).toMonoidHom (Subgroup.map L.subtype P₀) =
    Subgroup.map L.subtype P₀
  rw [hconj, hP₀fix q hq]

end CFSG
