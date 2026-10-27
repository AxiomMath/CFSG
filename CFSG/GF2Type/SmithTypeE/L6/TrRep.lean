module

public import CFSG.GF2Type.SmithTypeE.L6.TrCand
public import CFSG.GF2Type.SmithTypeE.L6.TrIndep
public import CFSG.GF2Type.SmithTypeE.L6.TrFp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup Module QuadraticMap CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
  CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero bit)

attribute [local irreducible] tvIdxTab tvTab tvImg tvList planePtsArr flagArr wtArr maskArr annArr

variable
  {A : V ≃ₗ[ZMod 2] V} {π : Equiv.Perm (Fin 1953)}

theorem image_of_tab {ct : Array ℕ} (hc : IsTab ct π) {i i' : ℕ} (hi : i < 1395) (hi' : i' < 1395)
    (h : ∀ x < 1953, inPlane i x = true → inPlane i' ct[x]! = true) :
    ⇑π '' wPlane i = wPlane i' :=
  image_wPlane_eq_of_subset hi hi' fun p hp => by
    have e := h p.val p.2 (mem_wPlane.1 hp)
    rw [hc p] at e
    exact mem_wPlane.2 e

theorem decode_wt_mem (h : InvHyp A π) {ct : Array ℕ} (hc : IsTab ct π) {i i' : ℕ} (hi : i < 1395)
    (hi' : i' < 1395) (hp : ∀ x < 1953, inPlane i x = true → inPlane i' ct[x]! = true) :
    decode (wt i' ^^^ wt i) ∈ commSpace A := by
  have e : decode (wt i' ^^^ wt i) = A (wtV i) - wtV i := by
    rw [decode_xor, sub_eq_add_V, h.wtV_eq hi hi' (image_of_tab hc hi hi' hp)]
    rfl
  rw [e]
  exact sub_mem_commSpace A _

theorem invConcl_of_rep (h : InvHyp A π) {ct : Array ℕ} (hc : IsTab ct π) {P : List (ℕ × ℕ)}
    (hlen : P.length = 6)
    (hP : ∀ p ∈ P, p.1 < 1395 ∧ p.2 < 1395 ∧
      ∀ x < 1953, inPlane p.1 x = true → inPlane p.2 ct[x]! = true)
    (hind : ∀ m, 0 < m → m < 64 → trXorSel (P.map fun p => wt p.2 ^^^ wt p.1) m ≠ 0)
    (hbr : (∃ i i', i < 1395 ∧ i' < 1395 ∧
        (∀ x < 1953, inPlane i x = true → inPlane i' ct[x]! = true) ∧ fB (wt i') (wt i) = true) ∨
      (∃ i < 1395, ∀ x < 1953, inPlane i x = true → ct[x]! = x) ∨
      (finrank (ZMod 2) (commSpace A) ≤ 8 ∧ NoTwoSub π)) :
    InvConcl A π := by
  have hmem : ∀ v ∈ P.map (fun p => wt p.2 ^^^ wt p.1), decode v ∈ commSpace A := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
    exact decode_wt_mem h hc (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2
  have hlt : ∀ v ∈ P.map (fun p => wt p.2 ^^^ wt p.1), v < 2 ^ 20 := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hv
    exact Nat.xor_lt_two_pow (CFSG.SmithL6.K.wt_lt20K _) (CFSG.SmithL6.K.wt_lt20K _)
  have hsel : SelIndep (P.map fun p => wt p.2 ^^^ wt p.1) := fun m hm0 hm =>
    hind m hm0 (by rw [List.length_map, hlen] at hm; exact hm)
  have h6 := le_finrank_of_selIndep hmem hlt hsel
  rw [List.length_map, hlen] at h6
  refine ⟨h6, fun q hpol hwt hsing => ?_⟩
  rcases hbr with ⟨i, i', hi, hi', hp, hfB⟩ | ⟨j, hj, hfix⟩ | hfp
  ·
    exfalso
    have hq := hsing _ (decode_wt_mem h hc hi hi' hp)
    have h1 := hwt _ hi'
    have h2 := hwt _ hi
    rw [wtV] at h1 h2
    rw [decode_xor, QuadraticMap.map_add (⇑q), hpol, fModel_decode, hfB, h1, h2] at hq
    exact absurd hq (by decide)
  ·
    left
    refine ⟨j, hj, mem_UA_of_fix h.norm hj fun p hp => Fin.ext ?_⟩
    rw [← hc p]
    exact hfix p.val p.2 (mem_wPlane.1 hp)
  ·
    exact Or.inr hfp

end CFSG.GF2Type.SmithTypeE.L6
