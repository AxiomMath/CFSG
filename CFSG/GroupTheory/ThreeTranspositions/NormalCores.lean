module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open Subgroup

theorem pPrimeCore_eq_bot_of_normal {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hQ : CFSG.pPrimeCore p Q = ⊥) (N : Subgroup Q) [N.Normal] :
    CFSG.pPrimeCore p ↥N = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let K : Subgroup ↥N := CFSG.pPrimeCore p ↥N
  have hKchar : K.Characteristic := CFSG.pPrimeCore_characteristic
  haveI : K.Characteristic := hKchar
  have hCnormal : (K.map N.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hcard : Nat.card (K.map N.subtype) = Nat.card K :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hcop : Nat.Coprime p (Nat.card (K.map N.subtype)) := by
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have hle : K.map N.subtype ≤ CFSG.pPrimeCore p Q := le_sSup ⟨hCnormal, hcop⟩
  rw [hQ] at hle
  have hbot : K.map N.subtype = ⊥ := le_bot_iff.mp hle
  exact (Subgroup.map_eq_bot_iff_of_injective K N.subtype_injective).mp hbot

theorem pCore_eq_bot_of_isStronglyPEmbedded {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {Y : Subgroup Q} (hY : CFSG.RankThree.PartOne.IsStronglyPEmbedded p Y) :
    CFSG.pCore p Q = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let R : Subgroup Q := CFSG.pCore p Q
  have hRnormal : R.Normal := CFSG.pCore_normal
  haveI : R.Normal := hRnormal
  have hRp : IsPGroup p R := CFSG.pCore_isPGroup
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  have hRleP : R ≤ (P : Subgroup Q) := hRp.le_sylow_of_normal P
  have hPsyl : CFSG.RankThree.PartOne.IsSylowOf p (P : Subgroup Q) ⊤ :=
    ⟨le_top, P.isPGroup', by simpa [Subgroup.relIndex_top_right] using P.not_dvd_index⟩
  obtain ⟨g, hg⟩ := hY.exists_conj_ge hPsyl
  have hnot : ¬ p ∣ Nat.card R :=
    (hY.conj g).not_dvd_card_of_normal_le (hRleP.trans hg)
  rcases hRp.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact absurd h hnot

theorem eq_bot_of_normal_of_isMulCommutative {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (h1 : CFSG.pPrimeCore p Q = ⊥) (h2 : CFSG.pCore p Q = ⊥)
    (A : Subgroup Q) [A.Normal] [IsMulCommutative A] : A = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p A) := inferInstance
  haveI : Finite (Sylow p A) := Sylow.finite_of_finiteIndex P
  have hPchar : (P : Subgroup A).Characteristic :=
    Sylow.characteristic_of_normal P (inferInstance : (P : Subgroup A).Normal)
  haveI : (P : Subgroup A).Characteristic := hPchar
  have hmapNormal : ((P : Subgroup A).map A.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hmapP : IsPGroup p ((P : Subgroup A).map A.subtype) := P.isPGroup'.map A.subtype
  have hle : (P : Subgroup A).map A.subtype ≤ CFSG.pCore p Q :=
    le_sSup ⟨hmapNormal, hmapP⟩
  rw [h2] at hle
  have hPbot : (P : Subgroup A) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective).mp (le_bot_iff.mp hle)
  have hnotdvd : ¬ p ∣ Nat.card A := by
    have h := P.not_dvd_index
    rw [hPbot, Subgroup.index_bot] at h
    exact h
  have hcop : Nat.Coprime p (Nat.card A) := hp.coprime_iff_not_dvd.mpr hnotdvd
  have hAle : A ≤ CFSG.pPrimeCore p Q := le_sSup ⟨inferInstance, hcop⟩
  rw [h1] at hAle
  exact le_bot_iff.mp hAle

theorem center_eq_bot_of_normal {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (h1 : CFSG.pPrimeCore p Q = ⊥) (h2 : CFSG.pCore p Q = ⊥)
    (N : Subgroup Q) [N.Normal] : Subgroup.center ↥N = ⊥ := by
  classical
  have hZbot : (Subgroup.center ↥N).map N.subtype = ⊥ :=
    eq_bot_of_normal_of_isMulCommutative hp h1 h2 ((Subgroup.center ↥N).map N.subtype)
  exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hZbot

end CFSG.GroupTheory.ThreeTranspositions
