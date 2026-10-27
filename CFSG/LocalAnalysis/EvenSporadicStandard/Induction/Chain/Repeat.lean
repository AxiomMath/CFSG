module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ChainLemmas

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

@[expose] def FiveALink (K J : Subgroup H) : Prop :=
  ∃ (T₀ : Subgroup H) (s₀ : H), T₀ ≠ ⊥ ∧ IsPGroup 2 T₀ ∧ IsCompIn K (centralizer (T₀ : Set H)) ∧
    IsPGroup 2 (zpowers s₀) ∧ s₀ ∈ normalizer (T₀ : Set H) ∧ s₀ ^ 2 ∈ T₀ ∧
    IsCompIn J (centralizer ((T₀ ⊔ zpowers s₀ : Subgroup H) : Set H)) ∧
    J ≤ K ⊔ K.map (MulAut.conj s₀).toMonoidHom ∧
    K ⊔ K.map (MulAut.conj s₀).toMonoidHom = conjClosure J (layerIn (centralizer (T₀ : Set H))) ∧
    K ≠ K.map (MulAut.conj s₀).toMonoidHom ∧ Nonempty ((↥K ⧸ center ↥K) ≃* (↥J ⧸ center ↥J))

variable {a n r : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}

theorem Sol78Links.fiveALink (h : Sol78Links H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hT : T i ≠ ⊥) (h5a : Sol78Link5a (L i) (L (i - 1)) (s i)) : FiveALink (L i) (L (i - 1)) := by
  obtain ⟨hTp, hLc⟩ := h.comp i hia
  obtain ⟨hsp, hsN, hs2, hLp⟩ := h.elem i hi hia
  obtain ⟨hincl, heq⟩ := h.incl i hi hia
  exact ⟨T i, s i, hT, hTp, hLc, hsp, hsN, hs2, hLp, hincl, heq, h5a.1, h5a.2⟩

variable [Finite H] {N : Subgroup H}

theorem fiveALink_of_cqOrd_L (hN : FStarSimple N) (h : Sol78Chain23 H N n L T s) {a : ℕ}
    (ha : a < n - 2) (heq : cqOrd (L a) = cqOrd (L (n - 2))) :
    ∃ J : Subgroup H, FiveALink (L (n - 2)) J := by
  have hLmono : ∀ {c d : ℕ}, c ≤ d → d ≤ n → cqOrd (L c) ≤ cqOrd (L d) := fun hcd hd =>
    h.toLinks.cqOrd_mono hcd hd
  have h1 : cqOrd (L a) ≤ cqOrd (L (n - 3)) := hLmono (by omega) (by omega)
  have h2 : cqOrd (L (n - 3)) ≤ cqOrd (L (n - 2)) := hLmono (by omega) (by omega)
  have heq' : cqOrd (L (n - 2 - 1)) = cqOrd (L (n - 2)) := by
    have : n - 2 - 1 = n - 3 := by omega
    rw [this]
    omega
  have hneq : L (n - 2 - 1) ≠ L (n - 2) := fun hh =>
    absurd (h.inj (n - 2 - 1) (by omega) (n - 2) (by omega) hh) (by omega)
  have h5a := h.toLinks.link5a_of_cqOrd_eq (i := n - 2) (by omega) (by omega) heq' hneq
  have hT : T (n - 2) ≠ ⊥ := h.T_ne_bot hN (by omega)
  exact ⟨L (n - 2 - 1), h.toLinks.fiveALink (by omega) (by omega) hT h5a⟩

theorem exists_fiveALink {U TU : ℕ → Subgroup H} {sU : ℕ → H} (hN : FStarSimple N)
    (h : Sol78Chain23 H N n L T s) (hU : Sol78Chain23 H N r U TU sU)
    (hcq : cqOrd (U 0) = cqOrd (L (n - 2))) (hne : U 0 ≠ L (n - 2))
    (hcol : ∃ a ≤ n - 2, ∃ j < r, L a = U j) : ∃ J : Subgroup H, FiveALink (L (n - 2)) J := by
  obtain ⟨a, ha, j, hjr, haj⟩ := hcol
  have hLmono : ∀ {c d : ℕ}, c ≤ d → d ≤ n → cqOrd (L c) ≤ cqOrd (L d) := fun hcd hd =>
    h.toLinks.cqOrd_mono hcd hd
  have hUmono : ∀ {c d : ℕ}, c ≤ d → d ≤ r → cqOrd (U c) ≤ cqOrd (U d) := fun hcd hd =>
    hU.toLinks.cqOrd_mono hcd hd
  have hUj : cqOrd (U 0) ≤ cqOrd (U j) := hUmono (Nat.zero_le _) (by omega)
  have hLa : cqOrd (L a) = cqOrd (U j) := by rw [haj]
  by_cases hae : a = n - 2
  ·
    subst hae
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne haj.symm
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj0
    have hm1 : cqOrd (U (j - 1)) ≤ cqOrd (U j) := hU.toLinks.cqOrd_le_succ hj1 (by omega)
    have hm0 : cqOrd (U 0) ≤ cqOrd (U (j - 1)) := hUmono (Nat.zero_le _) (by omega)
    have heq : cqOrd (U (j - 1)) = cqOrd (U j) := by omega
    have hneq : U (j - 1) ≠ U j := fun hh =>
      absurd (hU.inj (j - 1) (by omega) j (by omega) hh) (by omega)
    have h5a := hU.toLinks.link5a_of_cqOrd_eq hj1 (by omega) heq hneq
    have hT : TU j ≠ ⊥ := hU.T_ne_bot hN hjr
    exact ⟨U (j - 1), by rw [haj]; exact hU.toLinks.fiveALink hj1 (by omega) hT h5a⟩
  ·
    have hle : cqOrd (L a) ≤ cqOrd (L (n - 2)) := hLmono (by omega) (by omega)
    exact fiveALink_of_cqOrd_L hN h (a := a) (by omega) (by omega)

end CFSG.EvenSporadicStandard.Induction
