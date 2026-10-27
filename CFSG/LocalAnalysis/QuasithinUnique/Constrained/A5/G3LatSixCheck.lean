module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheckDefs

public section

namespace CFSG.QuasithinUnique.A5.G3

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

section NoSix

theorem noSix_of_check {n : ℕ} (gens : List (Perm (Fin n))) {depth : ℕ}
    (hc : closedH (gens.map RN.enc) (elts RN.enc depth gens) = true)
    (hs : noSixCheck (elts RN.enc depth gens) = true) :
    ∀ g ∈ Subgroup.closure {g | g ∈ gens}, orderOf g ≠ 6 := by
  intro g hg h6
  have hmem : RN.enc g ∈ elts RN.enc depth gens :=
    (mem_closure_iff_H (rawIsEnc n) gens depth hc g).mp hg
  have hall := List.all_eq_true.mp hs (RN.enc g) (Std.HashSet.mem_toList.mpr hmem)
  have h := rawIsEnc n
  have e6 : g * g * g * g * g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [h6] at this
    simpa [pow_succ] using this
  have e2 : g * g ≠ 1 := by
    have := pow_ne_one_of_lt_orderOf (x := g) (n := 2) (by norm_num) (by rw [h6]; norm_num)
    simpa [pow_succ] using this
  have e3 : g * g * g ≠ 1 := by
    have := pow_ne_one_of_lt_orderOf (x := g) (n := 3) (by norm_num) (by rw [h6]; norm_num)
    simpa [pow_succ] using this
  have f6 : RN.enc g * RN.enc g * RN.enc g * RN.enc g * RN.enc g * RN.enc g = 1 := by
    have := congrArg RN.enc e6
    simpa only [h.map_mul, h.map_one] using this
  have f2 : RN.enc g * RN.enc g ≠ 1 := by
    intro hh
    apply e2
    apply h.inj
    rw [h.map_mul, h.map_one]
    exact hh
  have f3 : RN.enc g * RN.enc g * RN.enc g ≠ 1 := by
    intro hh
    apply e3
    apply h.inj
    rw [h.map_mul, h.map_mul, h.map_one]
    exact hh
  simp [f6, f2, f3] at hall

end NoSix

theorem AData.sound {n : ℕ} (d : AData n) {depth : ℕ} (h : d.check depth = true) :
    Nat.card (Subgroup.closure {g | g ∈ d.gens}) = 960 ∧
      ⁅Subgroup.closure {g | g ∈ d.gens}, Subgroup.closure {g | g ∈ d.gens}⁆ =
        Subgroup.closure {g | g ∈ d.gens} ∧
      ∀ g ∈ Subgroup.closure {g | g ∈ d.gens}, orderOf g ≠ 6 := by
  simp only [AData.check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hcl, hsize⟩, hperf⟩, hsix⟩ := h
  refine ⟨?_, perfect_of_perfOK (rawIsEnc n) hperf, noSix_of_check d.gens hcl hsix⟩
  rw [card_closure_of_closedH (rawIsEnc n) d.gens depth hcl]
  exact hsize

theorem hA_of_latSixCheck {n : ℕ} (c : LatCert (Perm (Fin n))) (hcl : c.closedOK RN.enc = true)
    (ds : List (AData n)) (h : latSixCheck c ds = true) :
    ∀ (j : ℕ) (hj : j < (c.tGens :: c.lat).length), c.sizes.getD j 0 = 1920 →
      ∃ A : Subgroup (Perm (Fin n)), A ≤ Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} ∧
        Nat.card A = 960 ∧ ⁅A, A⁆ = A ∧ ∀ g ∈ A, orderOf g ≠ 6 := by
  simp only [latSixCheck, Bool.and_eq_true] at h
  obtain ⟨hds, hj⟩ := h
  intro j hjlen hs
  have ha := List.all_eq_true.mp hj j (List.mem_range.mpr hjlen)
  simp only [hs, bne_self_eq_false, Bool.false_or] at ha
  obtain ⟨d, hd, hdgens⟩ := List.any_eq_true.mp ha
  obtain ⟨hcard, hperf, hsix⟩ := d.sound (List.all_eq_true.mp hds d hd)
  have hmem : (c.tGens :: c.lat)[j] ∈ c.tGens :: c.lat := List.getElem_mem hjlen
  refine ⟨Subgroup.closure {g | g ∈ d.gens}, ?_, hcard, hperf, hsix⟩
  rw [Subgroup.closure_le]
  intro g hg
  have := List.all_eq_true.mp hdgens g hg
  rw [List.getD_eq_getElem _ _ hjlen] at this
  exact (mem_closure_iff_H (rawIsEnc n) _ c.depth (c.members_closed hcl _ hmem) g).mpr
    (Std.HashSet.contains_iff_mem.mp this)

end CFSG.QuasithinUnique.A5.G3
