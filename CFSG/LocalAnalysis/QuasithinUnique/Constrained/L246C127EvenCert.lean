module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCertDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

namespace L246C127

section Check

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R] (enc : G → R)

variable {enc}

theorem CTCert.charTwo [Finite G] (h : IsEnc enc) (c : CTCert G) (hc : c.check enc = true) :
    CharTwo (Subgroup.closure {g | g ∈ c.hGens}) := by
  simp only [CTCert.check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hclH, hclN⟩, hNH⟩, hnorm⟩, hcent⟩, hsize⟩ := hc
  set H : Subgroup G := Subgroup.closure {g | g ∈ c.hGens} with hH
  set N : Subgroup G := Subgroup.closure {g | g ∈ c.nGens} with hN
  have memH : ∀ x : G, x ∈ H ↔ enc x ∈ elts enc c.depth c.hGens := fun x =>
    mem_closure_iff_H h c.hGens c.depth hclH x
  have memN : ∀ x : G, x ∈ N ↔ enc x ∈ elts enc c.depth c.nGens := fun x =>
    mem_closure_iff_H h c.nGens c.depth hclN x
  have hNle : N ≤ H := by
    rw [hN, Subgroup.closure_le]
    intro g hg
    exact (memH g).2 (Std.HashSet.contains_iff_mem.mp (hNH g hg))
  have hN2 : IsPGroup 2 N := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := c.expo) ?_
    rw [card_closure_of_closedH h c.nGens c.depth hclN]
    exact hsize
  have hgen : ∀ x ∈ H, ∀ n ∈ c.nGens, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    obtain ⟨n', hn'mem, hn'eq⟩ := hnorm (enc x) (Std.HashSet.mem_toList.mpr ((memH x).1 hx)) n hn
    obtain ⟨y, hy, rfl⟩ := bfsSet_sound h c.nGens c.depth n' (Std.HashSet.mem_toList.mp hn'mem)
    have hxy : x * n = y * x := h.inj (by rw [h.map_mul, h.map_mul]; exact hn'eq)
    have : x * n * x⁻¹ = y := by rw [hxy]; group
    rw [this]
    exact hy
  have hconj : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    induction hn using Subgroup.closure_induction with
    | mem g hg => exact hgen x hx g hg
    | one => simp
    | mul a b _ _ ha hb =>
      have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [e]
      exact N.mul_mem ha hb
    | inv a _ ha =>
      have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact N.inv_mem ha
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    B6.mem_normalizer_of_forall_mem (hconj x hx)
      (fun n hn => by simpa using hconj x⁻¹ (H.inv_mem hx) n hn)
  have hNQ : N ≤ pCoreOf 2 H := C1.le_pCoreOf_of_normalized hNle hHN hN2
  have hCN : ∀ x ∈ H, (∀ n ∈ N, n * x = x * n) → x ∈ N := by
    intro x hx hc'
    have hall : ∀ n ∈ c.nGens, enc x * enc n = enc n * enc x := by
      intro n hn
      have := hc' n (Subgroup.subset_closure hn)
      rw [← h.map_mul, ← h.map_mul, this]
    exact (memN x).2 (Std.HashSet.contains_iff_mem.mp
      ((hcent (enc x) (Std.HashSet.mem_toList.mpr ((memH x).1 hx))).resolve_left
        (fun hnot => by
          have hT : (c.nGens.all fun n => enc x * enc n == enc n * enc x) = true :=
            List.all_eq_true.2 fun n hn => beq_iff_eq.2 (hall n hn)
          rw [hT] at hnot
          exact Bool.noConfusion hnot)))
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxH, hxC⟩ := hx
  exact hNQ (hCN x hxH fun n hn => (Subgroup.mem_centralizer_iff.1 hxC n (hNQ hn)))

end Check

end L246C127

end CFSG.QuasithinUnique
