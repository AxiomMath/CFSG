module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped MatrixGroups
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2 (mulEquivPSL)

theorem center_eq_bot_of_sl2 {L : Type} [Group L] {n : ℕ} (e : L ≃* SL(2, GaloisField 2 n)) :
    Subgroup.center L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hc : e x ∈ Subgroup.center SL(2, GaloisField 2 n) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx y)]
  rw [SL2Char2.center_eq_bot, Subgroup.mem_bot] at hc
  exact e.injective (hc.trans (map_one e).symm)

theorem card_le_three_of_sl2 {L : Type} [Group L] {n : ℕ} (e : L ≃* SL(2, GaloisField 2 n))
    (A : Subgroup L) (hA : CFSG.Open.IsElemAbelian 3 A) : Nat.card A ≤ 3 := by
  have hB : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
    Nat.card_congr (A.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm
  rw [← hB]
  refine SL2Char2.sl2_card_le_three _ ?_ ?_
  · obtain ⟨hc, -⟩ := hA
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    apply Subtype.ext
    show e a * e b = e b * e a
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    simp [hA.2 x hx]

theorem card_inf_innerAut_le_of_sl2 {L : Type} [Group L] [Finite L] {n : ℕ}
    (e : L ≃* SL(2, GaloisField 2 n)) (H : Subgroup (MulAut L))
    (hH : CFSG.Open.IsElemAbelian 3 H) : Nat.card ↥(H ⊓ innerAut113 L) ≤ 3 := by
  have hinj := conj_injective_of_center_eq_bot (center_eq_bot_of_sl2 e)
  let c : L →* MulAut L := MulAut.conj
  let A : Subgroup L := (H ⊓ innerAut113 L).comap c
  have hmem : ∀ x, x ∈ A ↔ c x ∈ H := fun x => by
    change c x ∈ H ⊓ innerAut113 L ↔ _
    exact ⟨fun h => h.1, fun h => ⟨h, ⟨x, rfl⟩⟩⟩
  have hA : CFSG.Open.IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      apply Subtype.ext
      apply hinj
      have := congrArg Subtype.val
        (hH.1.is_comm.comm (⟨c a, (hmem a).1 ha⟩ : H) ⟨c b, (hmem b).1 hb⟩)
      simpa using this
    · apply hinj
      rw [map_pow, map_one]
      exact hH.2 _ ((hmem x).1 hx)
  have hcard : Nat.card ↥(H ⊓ innerAut113 L) = Nat.card A := by
    have hmap : A.map c = H ⊓ innerAut113 L := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr inf_le_right
    rw [← hmap]
    exact (Nat.card_congr (A.equivMapOfInjective c hinj).toEquiv).symm
  rw [hcard]
  exact card_le_three_of_sl2 e A hA

theorem card_le_nine_of_sl2 {L : Type} [Group L] [Finite L] {n : ℕ}
    (e : L ≃* SL(2, GaloisField 2 n)) (E : Subgroup (MulAut L))
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have hcyc : IsCyclic (MulAut L ⧸ innerAut113 L) := by
    have := isCyclic_ringEquiv_galoisField n
    exact isCyclic_of_surjective _ (outer_surjective e)
  let f : E →* MulAut L ⧸ innerAut113 L := (QuotientGroup.mk' (innerAut113 L)).comp E.subtype
  have hker : Nat.card f.ker = Nat.card ↥(E ⊓ innerAut113 L) := by
    have : f.ker = (E ⊓ innerAut113 L).subgroupOf E := by
      ext x
      simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card f.range ≤ 3 := by
    refine card_le_three_of_cyclic fun x => ?_
    obtain ⟨y, hy⟩ := x.2
    apply Subtype.ext
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow]
    rw [← hy]
    change f (y ^ 3) = 1
    have : y ^ 3 = 1 := Subtype.ext (hE.2 y y.2)
    rw [this, map_one]
  rw [← Subgroup.card_ker_mul_card_range f, hker]
  calc Nat.card ↥(E ⊓ innerAut113 L) * Nat.card f.range ≤ 3 * 3 :=
        Nat.mul_le_mul (card_inf_innerAut_le_of_sl2 e E hE) hrange
    _ = 9 := by norm_num

theorem A1_of_match {d1 : TauCeti.LieTypeIndex}
    (h : match d1 with | .A 1 q => q.p = 2 | _ => False) :
    ∃ q : TauCeti.PrimePower, d1 = .A 1 q ∧ q.p = 2 := by
  cases d1 with
  | A n q =>
    rcases n with _ | _ | n
    · exact False.elim h
    · exact ⟨q, rfl, h⟩
    · exact False.elim h
  | _ => exact False.elim h

theorem l2Two_holds : ∀ (S : Type) [Group S] [Finite S], catalogIs S l2Two →
    ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E < 3 ^ 3 := by
  intro S _ _ hS E hE
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  cases i with
  | lie d =>
    obtain ⟨q, hq, hq2⟩ := A1_of_match (d1 := d.1) hi
    obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2)
      (n := q.exponent) ⟨q, hq, hq2, rfl⟩
    have e3 : S ≃* SL(2, GaloisField 2 q.exponent) :=
      e.trans (e2.trans (mulEquivPSL (GaloisField 2 q.exponent)).symm)
    have hB : Nat.card E ≤ 9 := card_le_nine_of_sl2 e3 E hE
    exact lt_of_le_of_lt hB (by norm_num)
  | cyclic p h => exact False.elim hi
  | alternating n h => exact False.elim hi
  | sporadic s => exact False.elim hi

end CFSG.LocalAnalysis.GLTheoremA.List93

end
