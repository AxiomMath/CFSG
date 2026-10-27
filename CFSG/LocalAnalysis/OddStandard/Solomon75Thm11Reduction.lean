module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Reduction

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

private theorem exists_not_comm_alt {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩, ?_⟩,
    ⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨3, by omega⟩, ?_⟩, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · intro h
    have h2 := congrArg (fun p : alternatingGroup (Fin n) =>
      (p : Equiv.Perm (Fin n)) ⟨2, by omega⟩) h
    simp [Equiv.swap_apply_def] at h2

theorem isAhatIntr_of_solomon2An_hypotheses {G : Type} [Group G] {z : G} {L : Subgroup G}
    {n : ℕ} (hn : 8 ≤ n) (hLC : L ≤ centralizer ({z} : Set G))
    (hLpc : IsPComponent 2 (L.subgroupOf (centralizer ({z} : Set G)))) (hzL : z ∈ L)
    (hperf : Group.IsPerfect (L ⧸ pPrimeCore 2 L))
    (hcard : Nat.card (center (L ⧸ pPrimeCore 2 L)) = 2)
    (hquot : Nonempty ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃*
      alternatingGroup (Fin n))) : IsAhatIntr G z L := by
  obtain ⟨e⟩ := hquot
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  refine ⟨hLC, hzL, hLpc, n, hn, ⟨hperf, e.isSimpleGroup, ?_⟩, hcard, ⟨e⟩⟩
  obtain ⟨a, b, hab⟩ := exists_not_comm_alt (by omega : 4 ≤ n)
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem nonempty_equiv_of_isKType_of_simple {Q G : Type} [Group Q] [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (e : Q ≃* G) (hQ : IsKType Q) :
    Nonempty (G ≃* Blueprint.NativeSporadic.McL) ∨ Nonempty (G ≃* Blueprint.NativeSporadic.Ly) := by
  have : IsSimpleGroup Q := e.isSimpleGroup
  have hcen : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have h1 : e.symm a ∈ center Q := h ▸ Subgroup.mem_top _
      have := Subgroup.mem_center_iff.mp h1 (e.symm b)
      have h2 := congrArg e this
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h2.symm
  have e2 : G ≃* Q ⧸ center Q :=
    e.symm.trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcen.symm))
  rcases hQ.2 with ⟨m, -, -, hc, -⟩ | h | h
  · rw [hcen, Subgroup.card_bot] at hc
    omega
  · exact Or.inl (h.map fun f => e2.trans f)
  · exact Or.inr (h.map fun f => e2.trans f)

theorem isKComp_top_of_ne_bot {G : Type} [Group G] [IsSimpleGroup G] {J : Subgroup G}
    (hJ : IsKComp J) (hne : J ≠ ⊥) : J = ⊤ := by
  obtain ⟨K, -, hsub, -, -⟩ := hJ.1
  exact (hsub.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left hne

theorem solomon2AnInput_of_thm11 (h : SolomonThm11) :
    ComponentClassification.GSThmB.Solomon2AnInput := by
  intro G _ _ _ z hz L n hn hLC hLpc hzL hperf hcard hquot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnonab : ∃ a b : G, a * b ≠ b * a := nonabelian_of_quotient_alt (by omega) hquot
  have hA := isAhatIntr_of_solomon2An_hypotheses hn hLC hLpc hzL hperf hcard hquot
  have hzK : z ∈ KProd G := h G z hz L (Or.inl hA) hzL
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  obtain ⟨J, hJ, hJne⟩ : ∃ J : Subgroup G, IsKComp J ∧ J ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hle : KProd G ≤ ⊥ := sSup_le fun J hJ => (hcon J hJ).le
    exact hz1 (by simpa using hle hzK)
  have hJtop : J = ⊤ := isKComp_top_of_ne_bot hJ hJne
  subst hJtop
  have : IsSimpleGroup ↥(⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
  have hbot : pPrimeCore 2 ↥(⊤ : Subgroup G) = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 ↥(⊤ : Subgroup G)).Normal).eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      have h2 : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(⊤ : Subgroup G))) :=
        pPrimeCore_coprime_card
      rw [h1, Subgroup.card_top] at h2
      have h3 : 2 ∣ Nat.card ↥(⊤ : Subgroup G) := by
        rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
        exact hz ▸ orderOf_dvd_natCard z
      exact absurd (Nat.Coprime.eq_one_of_dvd h2 h3) (by norm_num)
  let e : (↥(⊤ : Subgroup G) ⧸ pPrimeCore 2 ↥(⊤ : Subgroup G)) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  exact nonempty_equiv_of_isKType_of_simple hnonab e hJ.2

end CFSG.OddStandard.Solomon75
