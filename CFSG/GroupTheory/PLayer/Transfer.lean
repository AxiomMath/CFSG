module

public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

variable {G G' : Type} [Group G] [Group G'] [Finite G]

theorem glaPLayer_ne_bot_iff_map_ne_bot_of_coprime_ker {p : ℕ} (hp : p.Prime)
    (ψ : G →* G') {X : Subgroup G} (hker : Nat.Coprime p (Nat.card ↥(X ⊓ ψ.ker))) :
    GLAPLayer p X ≠ ⊥ ↔ GLAPLayer p (X.map ψ) ≠ ⊥ := by
  constructor
  · intro hX hbot
    have hex : ∃ J : Subgroup G, GLAPComponent p X J ∧ J ≠ ⊥ := by
      by_contra h
      push Not at h
      exact hX (by rw [GLAPLayer, sSup_eq_bot]; exact fun J hJ => h J hJ)
    obtain ⟨J, hJ, hJne⟩ := hex
    have hJmap : J.map ψ ≠ ⊥ := by
      intro hmap
      have hJle : J ≤ ψ.ker := (Subgroup.map_eq_bot_iff (f := ψ) J).1 hmap
      have hcopJ : Nat.Coprime p (Nat.card J) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (le_inf hJ.1 hJle)) hker
      have hself : GLAPPrimeCoreOf p J = J := CFSG.gLAPPrimeCoreOf_eq_self_of_coprime hcopJ
      have hcore : GLAPPrimeCore p ↥J = ⊤ := by
        apply Subgroup.map_injective J.subtype_injective
        change GLAPPrimeCoreOf p J = (⊤ : Subgroup ↥J).map J.subtype
        rw [hself, Subgroup.map_top, Subgroup.range_subtype]
      haveI : Subsingleton (PQuot p J) := by
        change Subsingleton (↥J ⧸ GLAPPrimeCore p ↥J)
        rw [hcore]
        exact QuotientGroup.subsingleton_quotient_top
      have hq := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
      exact (not_subsingleton_iff_nontrivial.mpr
        (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hq)) inferInstance
    have hJ' : GLAPComponent p (X.map ψ) (J.map ψ) :=
      CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp ψ hker hJ
    exact hJmap (le_bot_iff.1 (hbot ▸ le_sSup hJ'))
  · intro hX' hbot
    have hex : ∃ J' : Subgroup G', GLAPComponent p (X.map ψ) J' ∧ J' ≠ ⊥ := by
      by_contra h
      push Not at h
      exact hX' (by rw [GLAPLayer, sSup_eq_bot]; exact fun J hJ => h J hJ)
    obtain ⟨J', hJ', hJ'ne⟩ := hex
    obtain ⟨J, hJ, hJmap⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.exists_glaPComponent_map_eq hp ψ hker hJ'
    have hJne : J ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.map_bot] at hJmap
      exact hJ'ne hJmap.symm
    exact hJne (le_bot_iff.1 (hbot ▸ le_sSup hJ))

theorem zpowers_inf_eq_bot_of_not_mem {p : ℕ} (hp : p.Prime) {b : G}
    (hbp : b ^ p = 1) (hb1 : b ≠ 1) {H : Subgroup G} (hbH : b ∉ H) :
    Subgroup.zpowers b ⊓ H = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxp : x ^ p = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx.1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hx.1
  have hxeq : Subgroup.zpowers x = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hxle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hbord])
  have hb_mem : b ∈ Subgroup.zpowers x := by
    rw [hxeq]
    exact Subgroup.mem_zpowers b
  exact hbH ((Subgroup.zpowers_le.2 hx.2) hb_mem)

theorem card_sup_sup_mul_card_inf_eq {A C Z : Subgroup G}
    (hCA : C ≤ Subgroup.normalizer (A : Set G))
    (hZ : Z ≤ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G))
    (hdisj : (A ⊔ C : Subgroup G) ⊓ Z = ⊥) :
    Nat.card ↥(A ⊔ C ⊔ Z) * Nat.card ↥(A ⊓ C) =
      Nat.card A * Nat.card C * Nat.card Z := by
  have hAC := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
    (A := A) (B := C) hCA
  have hH := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
    (A := (A ⊔ C : Subgroup G)) (B := Z) hZ
  rw [hdisj, Subgroup.card_bot, mul_one] at hH
  rw [hH]
  calc Nat.card ↥(A ⊔ C) * Nat.card Z * Nat.card ↥(A ⊓ C)
      = Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) * Nat.card Z := by ring
    _ = Nat.card A * Nat.card C * Nat.card Z := by rw [hAC]

end CFSG

end
