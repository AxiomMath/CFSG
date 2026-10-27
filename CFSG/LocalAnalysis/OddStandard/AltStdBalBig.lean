module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalCaseO
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Configuration

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def AltStdBalancedBigResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → 4 ≤ Nat.card S →
          (∀ y : G, orderOf y = 2 → CFSG.oddCore (centralizer ({y} : Set G)) = ⊥) →
          (∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 ∧
            ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) →
          (∃ g : G, g ∉ normalizer (L : Set G) ∧
            Even (Nat.card ((centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
              normalizer (L : Set G) : Subgroup G))) →
          (∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
            P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
              normalizer (L : Set G) → IsPGroup 2 P → Nat.card P ≤ 2) → False

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem altStdBalancedBig_of_residue (hRes : AltStdBalancedBigResidue) : AltStdBalancedBig := by
  intro G _ _ L hS n hn hθ S hcyc h4 hbal
  have h : Setting G L n := ⟨hS, hn, hθ, ⟨S, hcyc⟩, hbal⟩
  obtain ⟨z, d⟩ := Cyc.of_sylow h S hcyc
  have hQcard : Nat.card (sylowSub S) = Nat.card S := card_sylowSub S
  have h4Q : 4 ≤ Nat.card (sylowSub S) := hQcard ▸ h4
  by_cases hE : centralizer ({z} : Set G) ≤ L ⊔ sylowSub S
  · have := card_eq_two_of_centralizer_le_sup h d hE
    omega
  have hO : ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) := fun hle =>
    hE fun c hc => mem_sup_of_mem_sup_centralizer h d hc (hle hc)
  by_cases hb : ∃ g : G, g ∉ normalizer (L : Set G) ∧ ∃ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) ∧
        IsPGroup 2 P ∧ 4 ≤ Nat.card P
  ·
    obtain ⟨g, hg, P, hP, hPp, hP4⟩ := hb
    obtain ⟨g', hg', R, T, hRK, hR, hRcard, hTK, hTN, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized h.isStandard S hcyc hg (hP.trans inf_le_left)
        (hP.trans inf_le_right) hPp hP4
    obtain ⟨zR, dR⟩ := Cyc.of_card d hRK hR (by rw [hRcard, hQcard])
    have hRc4 : 4 ≤ Nat.card R := by rw [hRcard]; exact h4
    have hgi : g'⁻¹ ∉ normalizer (L : Set G) := fun hmem => hg' (by simpa using inv_mem hmem)
    have hTK' : T ≤ CFSG.conjugate (centralizer (L : Set G)) g'⁻¹ := by
      simpa [CFSG.conjugate] using hTK
    exact fullPair_false h dR hgi hTK' hT (by rw [hTcard, hRcard]) hRT hRc4
  ·
    have hbc : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
        P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
          normalizer (L : Set G) → IsPGroup 2 P → Nat.card P ≤ 2 := by
      intro g hg P hP hPp
      by_contra hlt
      push Not at hlt
      obtain ⟨j, hj⟩ := hPp.exists_card_eq
      have h4P : 4 ≤ Nat.card P := by
        rcases j with _ | _ | j
        · rw [hj] at hlt
          norm_num at hlt
        · rw [hj] at hlt
          norm_num at hlt
        · rw [hj]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hb ⟨g, hg, P, hP, hPp, h4P⟩
    obtain ⟨g, -, hcomm, haK, -⟩ := exists_partner h d
    have haC : g⁻¹ * z * g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hcomm
    have haN : g⁻¹ * z * g ∈ normalizer (L : Set G) := centralizer_le_normalizer h d haC
    have hgN : g⁻¹ ∉ normalizer (L : Set G) := by
      intro hgN
      apply haK
      rw [← h.normalizer_eq] at hgN
      have := (mem_normalizer_iff.1 hgN z).1 (d.le d.mem)
      simpa using this
    have ha2 : orderOf (g⁻¹ * z * g) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
      rw [MulAut.conj_apply] at this
      simpa using this.trans d.order
    have haK' : g⁻¹ * z * g ∈ (centralizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ⊓
        normalizer (L : Set G) :=
      Subgroup.mem_inf.2 ⟨⟨z, d.le d.mem, by simp⟩, haN⟩
    have heven : Even (Nat.card ((centralizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ⊓
        normalizer (L : Set G) : Subgroup G)) := by
      have := Subgroup.orderOf_dvd_natCard _ haK'
      rw [ha2] at this
      exact even_iff_two_dvd.2 this
    exact hRes G L hS n hn hθ S hcyc h4 hbal ⟨z, d.le d.mem, d.order, hO⟩ ⟨g⁻¹, hgN, heven⟩ hbc

end Assembly

end CFSG.OddStandard.AltStdBal
