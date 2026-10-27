module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Defs

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open CFSG.EvenSporadicStandard.Induction

section TLinksRepeat

variable {H : Type} [Group H] [Finite H] {a : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}

theorem TLinks.cqOrd_eq_of_endpoints_eq (h : TLinks H a L T s) {c d j : ℕ} (hcj : c ≤ j)
    (hjd : j ≤ d) (hda : d ≤ a) (heq : cqOrd (L c) = cqOrd (L d)) :
    cqOrd (L j) = cqOrd (L c) := by
  have h1 := h.cqOrd_mono hcj (hjd.trans hda)
  have h2 := h.cqOrd_mono hjd hda
  omega

theorem TLinks.swap_of_cqOrd_eq (h : TLinks H a L T s) {c d i : ℕ} (hci : c < i) (hid : i ≤ d)
    (hda : d ≤ a) (heq : cqOrd (L c) = cqOrd (L d)) (hne : L (i - 1) ≠ L i) :
    Sol78Link5a (L i) (L (i - 1)) (s i) := by
  have h1 := h.cqOrd_eq_of_endpoints_eq (j := i - 1) (by omega) (by omega) hda heq
  have h2 := h.cqOrd_eq_of_endpoints_eq hci.le hid hda heq
  exact h.link5a_of_cqOrd_eq (by omega) (hid.trans hda) (h1.trans h2.symm) hne

theorem TLinks.fiveALink_of_cqOrd_eq (h : TLinks H a L T s) {c d i : ℕ} (hci : c < i)
    (hid : i ≤ d) (hda : d ≤ a) (heq : cqOrd (L c) = cqOrd (L d)) (hne : L (i - 1) ≠ L i)
    (hT : T i ≠ ⊥) : FiveALink (L i) (L (i - 1)) :=
  h.fiveALink (by omega) (hid.trans hda) hT (h.swap_of_cqOrd_eq hci hid hda heq hne)

end TLinksRepeat

section Collision

variable {G : Type} [Group G] [Finite G] {n r : ℕ} {L T U TU : ℕ → Subgroup G} {s sU : ℕ → G}

theorem InCG.exists_fiveALink_of_collision (hG : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (h : InCG G n L T s) (hU : InCG G r U TU sU)
    (hcq : cqOrd (U 0) = cqOrd (L (n - 2))) (hne : U 0 ≠ L (n - 2))
    (hcol : ∃ a ≤ n - 2, ∃ j < r, L a = U j) : ∃ J : Subgroup G, FiveALink (L (n - 2)) J := by
  obtain ⟨a, ha, j, hjr, haj⟩ := hcol
  have hLa : cqOrd (L a) = cqOrd (U j) := by rw [haj]
  have hUj : cqOrd (U 0) ≤ cqOrd (U j) := hU.links.cqOrd_mono (Nat.zero_le j) hjr.le
  by_cases hae : a = n - 2
  · subst hae
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne haj.symm
    have hj1 : 0 < j := Nat.pos_of_ne_zero hj0
    have hneq : U (j - 1) ≠ U j := fun hh =>
      absurd (hU.inj (j - 1) (by omega) j (by omega) hh) (by omega)
    refine ⟨U (j - 1), ?_⟩
    rw [haj]
    exact hU.links.fiveALink_of_cqOrd_eq hj1 le_rfl hjr.le (hcq.trans hLa) hneq
      (hU.T_ne_bot hG hna hjr)
  · have hlt : a < n - 2 := lt_of_le_of_ne ha hae
    have hle : cqOrd (L a) ≤ cqOrd (L (n - 2)) := h.links.cqOrd_mono ha (by omega)
    have heq : cqOrd (L a) = cqOrd (L (n - 2)) := by omega
    have hneq : L (n - 2 - 1) ≠ L (n - 2) := fun hh =>
      absurd (h.inj (n - 2 - 1) (by omega) (n - 2) (by omega) hh) (by omega)
    exact ⟨L (n - 2 - 1), h.links.fiveALink_of_cqOrd_eq hlt le_rfl (by omega) heq hneq
      (h.T_ne_bot hG hna (by omega))⟩

end Collision

end CFSG.EvenSporadicStandard.M12Std.Rbc
