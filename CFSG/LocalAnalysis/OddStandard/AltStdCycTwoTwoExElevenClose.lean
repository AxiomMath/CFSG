module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoExClose

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two.Exact

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec AltStdSec.Wreath

@[expose] def ExactWreathUnique (G : Type) [Group G] [Finite G] (n : ℕ) : Prop :=
  ∀ (L' : Subgroup G) (w : G), StandardSetting G L' → ExactShape w L' n →
    ∀ H₁ H₂ : Subgroup G, WreathPair L' w n H₁ → WreathPair L' w n H₂ →
      H₂ = H₁ ∨ H₂ = H₁.map (MulAut.conj w).toMonoidHom

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

theorem centralizer_le_subStab_of_unique_cent (hU : ExactWreathUnique G n)
    (T : Shape G L Q n z u) (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q)
    (hn : 4 ≤ n) {H : Subgroup G} (hH : WreathPair L z n H) :
    centralizer ({z} : Set G) ≤ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
  intro x hx
  have hz2 := T.cyc.mul_self
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 hx
  have hxL : cjSub x L = L := cjSub_eq_of_mem_normalizer (cent_le_normalizer T.std T.cyc hx)
  have hzx : x * z * x⁻¹ = z := by rw [hxz]; group
  have hH₂ : WreathPair L z n (cjSub x H) := by
    have := hH.conjugate x⁻¹
    simp only [inv_inv] at this
    have e1 : CFSG.conjugate L x⁻¹ = cjSub x L := by simp [CFSG.conjugate, cjSub]
    have e2 : CFSG.conjugate H x⁻¹ = cjSub x H := by simp [CFSG.conjugate, cjSub]
    rw [e1, e2, hzx, hxL] at this
    exact this
  have hne : H ≠ cjSub z H := hH.ne_cjSub hn
  have hu := hU L z T.std (exactShape_of_cent T.toBase hC) H _ hH hH₂
  rw [mem_subStab_pair_iff hne]
  have hxz' : cjSub x (cjSub z H) = cjSub z (cjSub x H) := by
    rw [← cjSub_mul, ← cjSub_mul, hxz]
  rcases hu with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rw [hxz', h1]
  · right
    have h1' : cjSub x H = cjSub z H := h1
    refine ⟨h1', ?_⟩
    rw [hxz', h1', ← cjSub_mul, hz2, cjSub_one]

theorem mem_subStab_of_swap_of_unique_cent (hU : ExactWreathUnique G n)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 5 ≤ n)
    {H : Subgroup G} (hH : WreathPair L z n H) {g : G}
    (hg1 : cjSub (g⁻¹ * z * g) H = cjSub z H) (hg2 : cjSub (g⁻¹ * z * g) (cjSub z H) = H) :
    g ∈ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
  have hz2 := T.cyc.mul_self
  set w := g⁻¹ * z * g with hw
  have hw2 : w * w = 1 := by
    calc w * w = g⁻¹ * (z * z) * g := by rw [hw]; group
      _ = 1 := by rw [hz2]; group
  have hS' : StandardSetting G (CFSG.conjugate L g) :=
    ⟨T.std.simple, T.std.nonab, T.std.kProper,
      Solomon75.standardComponentIsStandard_conjugate g T.std.standard⟩
  have hex' : ExactShape w (CFSG.conjugate L g) n := by
    have h1 := exactShape_map (exactShape_of_cent T.toBase hC) (MulAut.conj g⁻¹)
    rw [MulAut.conj_apply, inv_inv] at h1
    exact h1
  obtain ⟨eH⟩ := hH.iso
  have hcardL : Nat.card (CFSG.conjugate L g) ≤ Nat.card H := by
    rw [card_conjugate_eq, Nat.card_congr θ.toEquiv, Nat.card_congr eH.toEquiv]
  have hcomm : ⁅centralizer ({w} : Set G), centralizer ({w} : Set G)⁆ ≤ CFSG.conjugate L g :=
    commutator_centralizer_conj_le (commutator_centralizer_le_of_cent T.toBase θ hC) g
  have hHw : WreathPair (CFSG.conjugate L g) w n H :=
    wreathPair_of_swap hH hn hw2 hg1 hcomm hcardL
  have hHg : WreathPair (CFSG.conjugate L g) w n (CFSG.conjugate H g) := hH.conjugate g
  have hu := hU (CFSG.conjugate L g) w hS' hex' H _ hHw hHg
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have key : cjSub g⁻¹ H = H ∨ cjSub g⁻¹ H = cjSub z H := by
    rcases hu with h1 | h1
    · exact Or.inl h1
    · right
      have : cjSub g⁻¹ H = cjSub w H := h1
      rw [this, hg1]
  have hgz : g⁻¹ * z = w * g⁻¹ := by rw [hw]; group
  have hconj : cjSub g⁻¹ (cjSub z H) = cjSub w (cjSub g⁻¹ H) := by
    rw [← cjSub_mul, ← cjSub_mul, hgz]
  have hmem : g⁻¹ ∈ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
    rw [mem_subStab_pair_iff hne]
    rcases key with k1 | k1
    · left
      refine ⟨k1, ?_⟩
      rw [hconj, k1, hg1]
    · right
      refine ⟨k1, ?_⟩
      rw [hconj, k1, hg2]
  simpa using Subgroup.inv_mem _ hmem

theorem wreathOvergroup_of_unique_cent (hU : ExactWreathUnique G n) (T : Shape G L Q n z u)
    (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 11 ≤ n) :
    ∀ H : Subgroup G, WreathPair L z n H →
      ∃ (M : Subgroup G) (hCM : centralizer ({z} : Set G) ≤ M)
        (χ : M →* Multiplicative (ZMod 2)),
        (∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m) ∧
          χ ⟨z, hCM (mem_centralizer_singleton_iff.2 rfl)⟩ ≠ 1 := by
  intro H hH
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have hCM := centralizer_le_subStab_of_unique_cent hU T hC (by omega) hH
  refine ⟨subStab ({H, cjSub z H} : Set (Subgroup G)), hCM, pairChar H (cjSub z H) hne, ?_, ?_⟩
  · intro g hg
    rcases (mem_subStab_pair_iff hne).1 hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
    · exact (false_of_conj_fixes_of_cent T θ hC hn hH g hg1 hg2).elim
    · exact ⟨g, mem_subStab_of_swap_of_unique_cent hU T θ hC (by omega) hH hg1 hg2, rfl⟩
  · intro h1
    have h2 := (pairChar_eq_one_iff hne).1 h1
    exact hH.cjSub_ne (by omega) h2

theorem false_of_dichotomy_of_unique_cent (hU : ExactWreathUnique G n) (T : Shape G L Q n z u)
    (θ : L ≃* alternatingGroup (Fin n))
    (hC : centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q) (hn : 11 ≤ n)
    (hdich : CaseII θ T.hn (L ⊔ zpowers u) z ∨ CaseII θ T.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z n H) : False := by
  rcases hdich with h1 | h1 | ⟨H, hH⟩
  · exact false_of_caseII_or_of_cent T θ hC (Or.inl h1)
  · exact false_of_caseII_or_of_cent T θ hC (Or.inr h1)
  · obtain ⟨M, hCM, χ, hfus, hχ⟩ := wreathOvergroup_of_unique_cent hU T θ hC hn H hH
    have := T.std.simple
    exact false_of_fixedPoint_thompson T.std.nonab T.cyc.order hCM hfus
      (A := Multiplicative (ZMod 2))
      ((Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)) χ hχ

end CFSG.OddStandard.AltStdCycTwo.Two.Exact
