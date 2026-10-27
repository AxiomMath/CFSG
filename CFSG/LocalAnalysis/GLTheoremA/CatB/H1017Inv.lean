module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open

@[expose] def L3Inputs {X : Type*} [Group X] (t : X) : Prop :=
  (∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ 3) ∧
    (∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F →
      Nat.card F = 3 ^ 3 → ∀ u : X, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set X) →
        u * t = t * u → u = t)

theorem L3Inputs.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {t : X}
    (h : L3Inputs (e t)) : L3Inputs t := by
  have hmap : ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) →
      F.map e.toMonoidHom ≤ Subgroup.centralizer ({(e t)} : Set Y) := by
    intro F hF
    have h1 : (Subgroup.centralizer ({t} : Set X)).map e.toMonoidHom ≤
        Subgroup.centralizer (e.toMonoidHom '' ({t} : Set X)) :=
      Subgroup.map_centralizer_le_centralizer_image ({t} : Set X) e.toMonoidHom
    have h2 : e.toMonoidHom '' ({t} : Set X) = {e t} := by
      ext y
      simp
    rw [h2] at h1
    exact (Subgroup.map_mono hF).trans h1
  constructor
  · intro F hF hFab
    have hcard := h.1 (F.map e.toMonoidHom) (hmap F hF) (hFab.map e.toMonoidHom)
    rwa [Subgroup.card_map_of_injective e.injective] at hcard
  · intro F hF hFab hF27 u hu2 huC hut
    have hFab' : IsElemAbelian 3 (F.map e.toMonoidHom) := hFab.map e.toMonoidHom
    have hF27' : Nat.card (F.map e.toMonoidHom) = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective e.injective, hF27]
    have hu2' : orderOf (e u) = 2 := by
      rw [MulEquiv.orderOf_eq, hu2]
    have huC' : e u ∈ Subgroup.centralizer ((F.map e.toMonoidHom : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨f, hf, rfl⟩
      change e.toMonoidHom f * e.toMonoidHom u = e.toMonoidHom u * e.toMonoidHom f
      calc e.toMonoidHom f * e.toMonoidHom u = e.toMonoidHom (f * u) :=
            (map_mul e.toMonoidHom f u).symm
        _ = e.toMonoidHom (u * f) := by
            rw [(Subgroup.mem_centralizer_iff.1 huC) f hf]
        _ = e.toMonoidHom u * e.toMonoidHom f := map_mul e.toMonoidHom u f
    have hut' : e u * e t = e t * e u := by
      calc e u * e t = e.toMonoidHom (u * t) := (map_mul e.toMonoidHom u t).symm
        _ = e.toMonoidHom (t * u) := by rw [hut]
        _ = e t * e u := map_mul e.toMonoidHom t u
    exact e.injective (h.2 (F.map e.toMonoidHom) (hmap F hF) hFab' hF27' (e u) hu2' huC' hut')

theorem L3Inputs.of_isConj {X : Type*} [Group X] {s t : X} (hst : IsConj s t)
    (h : L3Inputs t) : L3Inputs s := by
  obtain ⟨c, hc⟩ := hst
  have hconj : MulAut.conj (c : X) s = t := by
    rw [MulAut.conj_apply, hc.eq]
    group
  rw [← hconj] at h
  exact L3Inputs.of_mulEquiv (MulAut.conj (c : X)) h

theorem l3Inputs_of_not_dvd {X : Type*} [Group X] [Finite X] {t : X}
    (h : ¬ 3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({t} : Set X))) : L3Inputs t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · intro F hF hFab
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hFab.isPGroup
    have hdvd : Nat.card F ∣ Nat.card (Subgroup.centralizer ({t} : Set X)) :=
      Subgroup.card_dvd_of_le hF
    have hn3 : n ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have h27 : 3 ^ 3 ∣ Nat.card F := by
        rw [hn]
        exact Nat.pow_dvd_pow 3 hlt
      exact h (h27.trans hdvd)
    rw [hn]
    calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn3
      _ ≤ 3 ^ 3 := by norm_num
  · intro F hF _ hF27
    exact absurd (hF27 ▸ Subgroup.card_dvd_of_le hF) h

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
