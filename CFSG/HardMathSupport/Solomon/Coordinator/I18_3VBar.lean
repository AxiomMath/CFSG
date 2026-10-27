module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Tools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification Subgroup

theorem i183v_barX_gLBConj {G : Type*} [Group G] {p : ℕ} {X : Subgroup G} {g : G} (hg : g ∈ X)
    (T : Subgroup G) :
    barX p X (GLBConj g T) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩) (barX p X T) := by
  refine le_antisymm (barX_le_gLBConj p hg T) ?_
  have h := barX_le_gLBConj p (X.inv_mem hg) (GLBConj g T)
  rw [gLBConj_inv_gLBConj] at h
  have h2 := gLBConj_mono (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩) h
  rw [gLBConj_gLBConj] at h2
  have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g⁻¹, X.inv_mem hg⟩) *
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g, hg⟩) = 1 := by
    rw [← map_mul]
    have : (⟨g⁻¹, X.inv_mem hg⟩ : ↥X) * ⟨g, hg⟩ = 1 := Subtype.ext (by simp)
    rw [this, map_one]
  rw [e, gLBConj_one] at h2
  exact h2

theorem i183v_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem i183v_eq_or_le_center {G : Type*} [Group G] {A B : Subgroup G} (h : IsSubnormal A B)
    (hB : CFSG.Open.IsQuasisimple B) : A = B ∨ A ≤ (Subgroup.center B).map B.subtype := by
  induction h with
  | refl A => exact Or.inl rfl
  | step hAM hn _ ih =>
    rename_i A M
    rcases ih hB with hMB | hM
    · subst hMB
      rcases CFSG.LocalCores.quasisimple_normal_subgroups (i183v_isQuasisimple hB) hn with h | h
      · exact Or.inl (le_antisymm hAM (Subgroup.subgroupOf_eq_top.mp h))
      · refine Or.inr fun x hx => ⟨⟨x, hAM hx⟩, h ?_, rfl⟩
        exact hx
    · exact Or.inr (hAM.trans hM)

theorem i183v_center_quotient_trivial {A : Type*} [Group A] [Finite A]
    (hA : CFSG.Open.IsQuasisimple A) (hcore : GLAPPrimeCore 3 A = ⊥) (N : Subgroup A) [N.Normal]
    (hN : N ≤ Subgroup.center A) {q : A ⧸ N} (hq : q ∈ Subgroup.center (A ⧸ N))
    (hord : Nat.Coprime 3 (orderOf q)) : q = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have : Group.IsPerfect A := ⟨hA.1⟩
  have ha : a ∈ Subgroup.center A := by
    have h0 : (QuotientGroup.mk' (Subgroup.center A)) a ∈ Subgroup.center (A ⧸ Subgroup.center A) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
      have hb := Subgroup.mem_center_iff.mp hq (QuotientGroup.mk b)
      have hb' : QuotientGroup.mk (b * a) = (QuotientGroup.mk (a * b) : A ⧸ N) := by
        simpa using hb
      have h1 : (b * a)⁻¹ * (a * b) ∈ N := QuotientGroup.eq.1 hb'
      have h2 := hN h1
      have h3 : (QuotientGroup.mk (b * a) : A ⧸ Subgroup.center A) = QuotientGroup.mk (a * b) :=
        QuotientGroup.eq.2 h2
      simpa using h3
    rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
    exact h0
  have hm : orderOf a ≠ 0 := (orderOf_pos a).ne'
  obtain ⟨e, t, ht, hmt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm 3 (by norm_num)
  have hc1 : (a ^ 3 ^ e) = 1 := by
    set c := a ^ 3 ^ e with hc
    have hcc : c ∈ Subgroup.center A := Subgroup.pow_mem _ ha _
    have hord_c : orderOf c = t := by
      rw [hc, orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hmt]
      have : Nat.gcd (3 ^ e * t) (3 ^ e) = 3 ^ e := Nat.gcd_eq_right (dvd_mul_right _ _)
      rw [this]
      exact Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)
    have hnorm : (Subgroup.zpowers c).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hcc)
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers c)) := by
      rw [Nat.card_zpowers, hord_c]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ht
    have hle : Subgroup.zpowers c ≤ GLAPPrimeCore 3 A := le_sSup ⟨hnorm, hcop⟩
    rw [hcore, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    exact hle
  have hmpow : orderOf a = 3 ^ e := by
    have h1 : orderOf (a ^ 3 ^ e) = 1 := by rw [hc1]; exact orderOf_one
    rw [orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hmt] at h1
    have : Nat.gcd (3 ^ e * t) (3 ^ e) = 3 ^ e := Nat.gcd_eq_right (dvd_mul_right _ _)
    rw [this, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)] at h1
    rw [hmt, h1, mul_one]
  have hdvd : orderOf (QuotientGroup.mk a : A ⧸ N) ∣ 3 ^ e := by
    rw [← hmpow]
    exact orderOf_map_dvd (QuotientGroup.mk' N) a
  have h1 : orderOf (QuotientGroup.mk a : A ⧸ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hord.symm) hdvd
  exact orderOf_eq_one_iff.1 h1

end CFSG.HardMathSupport.Solomon.Coordinator
