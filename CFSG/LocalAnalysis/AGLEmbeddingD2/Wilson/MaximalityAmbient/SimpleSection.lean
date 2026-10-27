module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

open Subgroup

theorem card_le_of_simple_section {H : Type*} [Group H] [Finite H] (T : Subgroup H) [T.Normal]
    (hT : Group.IsSolvable T) (L : Subgroup H) (K : Subgroup ↥L) (hKT : K.map L.subtype ≤ T)
    {M : Type*} [Group M] [IsSimpleGroup M] (hM : ¬ Group.IsSolvable M) (P : Subgroup H)
    (hP : P ≤ L ⊔ T) (φ : ↥P →* M) (hφ : Function.Surjective φ) :
    Nat.card M ≤ Nat.card (↥L ⧸ K) := by
  classical
  have : Group.IsSolvable T := hT
  let π : H →* H ⧸ T := QuotientGroup.mk' T
  let Φ : ↥P →* H ⧸ T := π.comp P.subtype
  let Ψ : ↥L →* H ⧸ T := π.comp L.subtype
  have hkerT : ∀ p : ↥P, p ∈ Φ.ker → (p : H) ∈ T := by
    intro p hp
    have : π (p : H) = 1 := hp
    exact (QuotientGroup.eq_one_iff _).1 this
  have hs1 : Group.IsSolvable Φ.ker := by
    let g : Φ.ker →* T :=
      (P.subtype.comp Φ.ker.subtype).codRestrict T fun p => hkerT p.1 p.2
    refine Group.isSolvable_of_isSolvable_injective (f := g) ?_
    intro p q h
    have h' : ((g p : T) : H) = ((g q : T) : H) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  set R : Subgroup M := Φ.ker.map φ with hR
  have : R.Normal := Subgroup.Normal.map inferInstance φ hφ
  have hRs : Group.IsSolvable R :=
    Group.isSolvable_of_surjective (f := φ.subgroupMap Φ.ker) (φ.subgroupMap_surjective _)
  have hRbot : R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h | h
    · exact h
    · exfalso
      apply hM
      rw [h] at hRs
      exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup M) ≃* M).toMonoidHom)
        (Subgroup.topEquiv : (⊤ : Subgroup M) ≃* M).surjective
  have hkerle : Φ.ker ≤ φ.ker := by
    intro p hp
    have : φ p ∈ R := ⟨p, hp, rfl⟩
    rw [hRbot] at this
    exact this
  have h1 : φ.ker.index = Nat.card M := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top]
  have h2 : φ.ker.index ∣ Φ.ker.index := Subgroup.index_dvd_of_le hkerle
  have h3 : Φ.ker.index = Nat.card Φ.range := Subgroup.index_ker Φ
  have hΦΨ : Φ.range ≤ Ψ.range := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_right.1 (hP p.2)
    refine ⟨⟨l, hl⟩, ?_⟩
    change π l = π (p : H)
    have ht1 : π t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [← hlt, map_mul, ht1, mul_one]
  have h4 : Nat.card Φ.range ≤ Nat.card Ψ.range := Subgroup.card_le_of_le hΦΨ
  have hKker : K ≤ Ψ.ker := by
    intro k hk
    have : (k : H) ∈ T := hKT ⟨k, hk, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 this
  have h5 : Ψ.ker.index = Nat.card Ψ.range := Subgroup.index_ker Ψ
  have h6 : Ψ.ker.index ∣ K.index := Subgroup.index_dvd_of_le hKker
  have h7 : K.index = Nat.card (↥L ⧸ K) := Subgroup.index_eq_card K
  have hK0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hΦ0 : Φ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc Nat.card M = φ.ker.index := h1.symm
    _ ≤ Φ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hΦ0) h2
    _ = Nat.card Φ.range := h3
    _ ≤ Nat.card Ψ.range := h4
    _ = Ψ.ker.index := h5.symm
    _ ≤ K.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hK0) h6
    _ = Nat.card (↥L ⧸ K) := h7

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
