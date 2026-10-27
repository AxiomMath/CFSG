module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem pRank_chevAut_ge {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X L B : Subgroup G}
    (hL : GLAPComponent p X L) (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (L : Set G)) {r : ℕ}
    (hk : p ^ r * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B) :
    r ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) := by
  let φ : ↥B →* MulAut (PSimple p L) := (chevAut p L).comp (Subgroup.inclusion hBN)
  have hker : ∀ b : ↥B, φ b = 1 ↔ (b : G) ∈ centModSubgroup p L := by
    intro b
    have h1 : φ b = chevAut p L ⟨(b : G), hBN b.2⟩ := rfl
    rw [h1, chevAut_eq_one_iff hp hL (hBN b.2), centMod_iff]
  have hmap : (φ.ker).map B.subtype = B ⊓ centModSubgroup p L := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, (hker b).1 hb⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩, (hker ⟨g, hgB⟩).2 hgC, rfl⟩
  have hkerCard : Nat.card ↥(φ.ker) = Nat.card ↥(B ⊓ centModSubgroup p L) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (f := B.subtype) Subtype.val_injective).symm
  have hBcard : Nat.card ↥B = Nat.card ↥(φ.range) * Nat.card ↥(B ⊓ centModSubgroup p L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hkerCard]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hcpos : 0 < Nat.card ↥(B ⊓ centModSubgroup p L) := Nat.card_pos
  have hpow : p ^ r ≤ Nat.card ↥(φ.range) := by
    rw [hBcard] at hk
    exact Nat.le_of_mul_le_mul_right hk hcpos
  have hE : IsElemAbelian p (φ.range) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      show (x : MulAut (PSimple p L)) * y = (y : MulAut (PSimple p L)) * x
      have hc : a * b = b * a := hB.1.is_comm.comm a b
      rw [← ha, ← hb, ← map_mul, ← map_mul, hc]
    · rintro x hx
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
      have hpow : a ^ p = 1 := by
        have hB' := hB.2 a a.2
        exact Subtype.ext (by simpa using hB')
      rw [← ha, ← map_pow, hpow, map_one]
  obtain ⟨k, hk'⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  have hrk : r ≤ k := by
    rw [hk'] at hpow
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hpow
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup (MulAut (PSimple p L)), E ≤ ⊤ ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card (MulAut (PSimple p L)), ?_⟩
    rintro m ⟨E, -, -, hEm⟩
    have hle : Nat.card E ≤ Nat.card (MulAut (PSimple p L)) := Subgroup.card_le_card_group E
    have hlt : m < p ^ m := Nat.lt_pow_self hp.one_lt
    omega
  unfold CFSG.Open.pRank
  exact le_trans hrk (le_csSup hbdd ⟨φ.range, le_top, hE, hk'⟩)

end CFSG.LocalAnalysis.GLTheoremA

end
