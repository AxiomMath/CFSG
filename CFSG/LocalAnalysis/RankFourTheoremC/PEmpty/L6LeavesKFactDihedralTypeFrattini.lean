module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType

open Subgroup

theorem card_frattini_quotient_le {H : Type} [Group H] [Finite H] (hH : IsPGroup 2 H)
    (M : Subgroup H) (hM : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (T : Set H)
    (hT : ∀ x ∈ M, x ^ 2 = 1 → x ∈ T) :
    Nat.card (H ⧸ frattini H) ≤ M.index * Nat.card T := by
  classical
  letI : CommGroup M := { (inferInstance : Group M) with
    mul_comm := fun a b => Subtype.ext (hM a a.2 b b.2) }
  let sq : M →* M := powMonoidHom 2
  let K' : Subgroup M := sq.range
  let K : Subgroup H := K'.map M.subtype
  have hKΦ : K ≤ frattini H := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
    have h1 : (QuotientGroup.mk' (frattini H) : H →* H ⧸ frattini H) ((x : H) ^ 2) = 1 := by
      rw [map_pow]
      exact (CFSG.GroupTheory.frattini_elementary_quotient hH).2.2.1 _
    have h2 : ((x : H) ^ 2) ∈ frattini H := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (M.subtype (sq x) : H) = (x : H) ^ 2 := by
      simp [sq, powMonoidHom_apply]
    rw [h3]
    exact h2
  have hKidx : K.index = K'.index * M.index := by
    have hinj : Function.Injective M.subtype := Subtype.val_injective
    have h := Subgroup.index_map_of_injective (H := K') hinj
    rw [Subgroup.range_subtype] at h
    exact h
  have hkerK : K'.index = Nat.card sq.ker := by
    have hA : Nat.card sq.ker * Nat.card K' = Nat.card M := by
      have h := Subgroup.card_mul_index sq.ker
      rw [Subgroup.index_ker sq] at h
      exact h
    have hB := Subgroup.card_mul_index K'
    have hpos : 0 < Nat.card K' := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hB, ← hA, mul_comm]
  have hker : Nat.card sq.ker ≤ Nat.card T := by
    let f : sq.ker → T := fun x =>
      ⟨(x.1 : H), hT _ x.1.2 (by
        have hx : sq x.1 = 1 := MonoidHom.mem_ker.mp x.2
        have hx2 := congrArg Subtype.val hx
        simpa [sq, powMonoidHom_apply] using hx2)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    exact Nat.card_le_card_of_injective f hf
  have hIdx : (frattini H).index ∣ K.index := Subgroup.index_dvd_of_le hKΦ
  have hKpos : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (frattini H).index ≤ K.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hKpos) hIdx
  calc Nat.card (H ⧸ frattini H) = (frattini H).index := rfl
    _ ≤ K.index := hle
    _ = K'.index * M.index := hKidx
    _ = Nat.card sq.ker * M.index := by rw [hkerK]
    _ ≤ Nat.card T * M.index := Nat.mul_le_mul_right _ hker
    _ = M.index * Nat.card T := mul_comm _ _

theorem card_mulAut_dvd_six {V : Type} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hpow : ∀ a : V, a ^ 2 = 1) {n : ℕ} (hcard : Nat.card V = 2 ^ n) (hn : n ≤ 2) :
    Nat.card (MulAut V) ∣ 6 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

theorem card_mulAut_eq_168 {V : Type} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hpow : ∀ a : V, a ^ 2 = 1) (hcard : Nat.card V = 2 ^ 3) :
    Nat.card (MulAut V) = 168 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  norm_num [Fin.prod_univ_succ]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType
