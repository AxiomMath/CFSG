module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaR

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

@[expose] def e1EStar (v : Fin 64) : Prop := e1E v ∧ v ≠ 0 ∧ v ≠ 40

instance : DecidablePred e1EStar := fun v => by unfold e1EStar; infer_instance

@[expose] def e1Perp (v : Fin 64) : Fin 64 :=
  if c3Mul 32 v = c3Mul v 32 then 32 else if c3Mul 2 v = c3Mul v 2 then 2 else 34

theorem e1Perp_spec : ∀ v : Fin 64, e1R v → ¬ e1E v →
    e1Sing (e1Perp v) ∧ e1E (e1Perp v) ∧ c3Mul (e1Perp v) v = c3Mul v (e1Perp v) := by
  decide

theorem e1Perp_unique : ∀ v : Fin 64, e1R v → ¬ e1E v → ∀ t : Fin 64, e1EStar t →
    c3Mul t v = c3Mul v t → t = e1Perp v ∨ t = c3Mul (e1Perp v) 40 := by
  decide +kernel

@[expose] def e1PtW (w : Fin 64) : Fin 3 :=
  if w = 32 ∨ w = 8 then 0 else if w = 2 ∨ w = 42 then 1 else 2

theorem e1PtW_eq_iff : ∀ w w' : Fin 64, e1EStar w → e1EStar w' →
    (e1PtW w = e1PtW w' ↔ w' = w ∨ w' = c3Mul w 40) := by
  decide +kernel

variable {G : Type} [Group G]

theorem mem_normalizer_of_forall_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (hg : ∀ s ∈ H, g * s * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hginv : g⁻¹ = g ^ (orderOf g - 1) := (eq_inv_of_mul_eq_one_left (by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one])).symm
  refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨hg s, fun hs => ?_⟩
  have h := pow_conj_mem_of_conj_mem hg (orderOf g - 1) _ hs
  rwa [← hginv, inv_inv, show g⁻¹ * (g * s * g⁻¹) * g = s by group] at h

variable {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem mem_e1NBar_of_odd {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) :
    g ∈ e1NBar Z u m y x := by
  refine ⟨mem_e1M0_of_pow_eq_one hb.partC.center hb.mem_iff ?_ hk hgk,
    mem_normalizer_of_forall_conj_mem hgR⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← caseC3Word_forty (m := m) (y := y)]
  calc g * caseC3Word Z u m y x 40 = g * caseC3Word Z u m y x 40 * g⁻¹ * g := by group
    _ = caseC3Word Z u m y x 40 * g := by rw [hb.conj_forty_of_normalizes hgR]

variable (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z), s ∉ T.map (QuotientGroup.mk' Z) →
  s * s = 1 → CaseC3.Genuine Z s)
include htype

theorem conj_mem_e1EBar_of_typeD {g : G ⧸ Z}
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) {t : G ⧸ Z}
    (ht : t ∈ e1EBar Z u m y x) (ht1 : t ≠ 1) (htz : t ≠ caseC3Word Z u m y x 40) :
    g * t * g⁻¹ ∈ e1EBar Z u m y x ∧ g * t * g⁻¹ ≠ 1 ∧
      g * t * g⁻¹ ≠ caseC3Word Z u m y x 40 := by
  have hz := hb.conj_forty_of_normalizes hgR
  have hinj : ∀ a b : G ⧸ Z, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b h =>
    mul_left_cancel (mul_right_cancel h)
  refine ⟨hb.mem_e1EBar_of_typeD htype (hgR t (hb.e1EBar_le_e1RBar ht)) ?_ ?_,
    fun h => ht1 (hinj _ _ (by rw [h]; group)), fun h => htz (hinj _ _ (by rw [h, hz]))⟩
  · rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group,
      hb.mul_self_of_mem_e1EBar ht]
    group
  · intro hgen
    have h' := CaseC3.genuine_conj Z hgen g
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h'
    exact (hb.not_genuine_of_mem_e1EBar ht ht1 htz).1 h'

theorem commute_of_odd_of_conj_typeD {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) {s : G ⧸ Z}
    (hs : s ∈ e1RBar Z u m y x) (hs1 : s ≠ 1) (hsz : s ≠ caseC3Word Z u m y x 40)
    (hgs : g * s * g⁻¹ = s ∨ g * s * g⁻¹ = s * caseC3Word Z u m y x 40) :
    ∀ t ∈ e1RBar Z u m y x, g * t = t * g := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  by_cases hvE : e1E v
  · exact hb.commute_of_odd hk hgk hgR hs
      (hb.mul_self_of_mem_e1EBar (hb.caseC3Word_mem_e1EBar_iff.mpr hvE)) hs1 hsz hgs
  obtain ⟨hpS, hpE, hpc⟩ := e1Perp_spec v hv hvE
  obtain ⟨hpR, hpp, hp1, hpz⟩ := hb.sing_iff.mpr hpS
  obtain ⟨hgE, hg1, hgz⟩ := hb.conj_mem_e1EBar_of_typeD htype hgR
    (hb.caseC3Word_mem_e1EBar_iff.mpr hpE) hp1 hpz
  obtain ⟨t, htE, ht⟩ := hb.mem_e1EBar_iff.mp hgE
  have hcv : (g * caseC3Word Z u m y x (e1Perp v) * g⁻¹) * (g * caseC3Word Z u m y x v * g⁻¹) =
      (g * caseC3Word Z u m y x v * g⁻¹) * (g * caseC3Word Z u m y x (e1Perp v) * g⁻¹) := by
    rw [show (g * caseC3Word Z u m y x (e1Perp v) * g⁻¹) * (g * caseC3Word Z u m y x v * g⁻¹) =
        g * (caseC3Word Z u m y x (e1Perp v) * caseC3Word Z u m y x v) * g⁻¹ by group,
      show (g * caseC3Word Z u m y x v * g⁻¹) * (g * caseC3Word Z u m y x (e1Perp v) * g⁻¹) =
        g * (caseC3Word Z u m y x v * caseC3Word Z u m y x (e1Perp v)) * g⁻¹ by group,
      hb.caseC3Word_mul, hb.caseC3Word_mul, hpc]
  rw [← ht] at hcv
  have htv : caseC3Word Z u m y x t * caseC3Word Z u m y x v =
      caseC3Word Z u m y x v * caseC3Word Z u m y x t := by
    rcases hgs with h | h <;> rw [h] at hcv
    · exact hcv
    · have hzt : caseC3Word Z u m y x 40 * caseC3Word Z u m y x t =
          caseC3Word Z u m y x t * caseC3Word Z u m y x 40 :=
        (hb.forall_commute_e1RBar_iff hb.forty_mem_e1RBar).mpr (Or.inr rfl) _
          (hb.caseC3Word_mem_e1RBar_iff.mpr (e1R_of_e1E t htE))
      refine mul_right_cancel (b := caseC3Word Z u m y x 40) ?_
      rw [mul_assoc, hcv, mul_assoc, hzt, ← mul_assoc]
  rw [hb.caseC3Word_mul, hb.caseC3Word_mul, hb.caseC3Word_inj] at htv
  have ht0 : t ≠ 0 := fun h => hg1 (by rw [← ht, h, caseC3Word_zero])
  have ht40 : t ≠ 40 := fun h => hgz (by rw [← ht, h])
  refine hb.commute_of_odd hk hgk hgR hpR hpp hp1 hpz ?_
  rcases e1Perp_unique v hv hvE t ⟨htE, ht0, ht40⟩ htv with h | h
  · exact Or.inl (by rw [← ht, h])
  · exact Or.inr (by rw [← ht, h, hb.caseC3Word_mul])

theorem conj_ne_of_odd_typeD {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x)
    (hgc : ¬ ∀ s ∈ e1RBar Z u m y x, g * s = s * g) {s : G ⧸ Z} (hs : s ∈ e1RBar Z u m y x)
    (hs1 : s ≠ 1) (hsz : s ≠ caseC3Word Z u m y x 40) :
    g * s * g⁻¹ ≠ s ∧ g * s * g⁻¹ ≠ s * caseC3Word Z u m y x 40 :=
  ⟨fun h => hgc (hb.commute_of_odd_of_conj_typeD htype hk hgk hgR hs hs1 hsz (Or.inl h)),
    fun h => hgc (hb.commute_of_odd_of_conj_typeD htype hk hgk hgR hs hs1 hsz (Or.inr h))⟩

theorem mem_e1KBar_of_conj_typeD (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {n : G ⧸ Z}
    (hn : n ∈ e1NBar Z u m y x) {s : G ⧸ Z} (hs : s ∈ e1RBar Z u m y x) (hs1 : s ≠ 1)
    (hsz : s ≠ caseC3Word Z u m y x 40)
    (hns : n * s * n⁻¹ = s ∨ n * s * n⁻¹ = s * caseC3Word Z u m y x 40) :
    n ∈ e1KBar Z u m y x := by
  obtain ⟨r, hr, c, hc, ⟨k, hk, hck⟩, rfl⟩ := hb.exists_mul_of_mem_e1NBar S' hS' hn
  have hri := (e1RBar Z u m y x).inv_mem hr
  have hcs : c * s * c⁻¹ = s ∨ c * s * c⁻¹ = s * caseC3Word Z u m y x 40 := by
    have h := conj_mul_conj_mod hb.forty_mul_self
      (hb.conj_forty_of_mem_e1NBar (hb.e1RBar_le_e1NBar hri)) hns (hb.conj_of_mem_e1RBar hri hs)
    rwa [inv_mul_cancel_left] at h
  have hcomm := hb.commute_of_odd_of_conj_typeD htype hk hck (conj_mem_of_mem_e1NBar hc) hs hs1
    hsz hcs
  exact Subgroup.mul_mem_sup hr
    ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun t ht => (hcomm t ht).symm⟩

theorem conj_ne_of_not_mem_e1KBar_typeD (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S)
    {n : G ⧸ Z} (hn : n ∈ e1NBar Z u m y x) (hnK : n ∉ e1KBar Z u m y x) {s : G ⧸ Z}
    (hs : s ∈ e1RBar Z u m y x) (hs1 : s ≠ 1) (hsz : s ≠ caseC3Word Z u m y x 40) :
    n * s * n⁻¹ ≠ s ∧ n * s * n⁻¹ ≠ s * caseC3Word Z u m y x 40 :=
  ⟨fun h => hnK (hb.mem_e1KBar_of_conj_typeD htype S' hS' hn hs hs1 hsz (Or.inl h)),
    fun h => hnK (hb.mem_e1KBar_of_conj_typeD htype S' hS' hn hs hs1 hsz (Or.inr h))⟩

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
