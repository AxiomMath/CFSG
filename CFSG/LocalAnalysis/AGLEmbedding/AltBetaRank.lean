module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding

open CFSG.Open Equiv Equiv.Perm Finset MulAction

theorem mul_le_pow_self {p : ℕ} (hp : 2 ≤ p) (k : ℕ) : p * k ≤ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h1 : p ≤ p ^ k := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
      rw [pow_succ, mul_add, mul_one]
      nlinarith

theorem pow_mul_pow_div_le {p k N : ℕ} (hp : 2 ≤ p) (hk : p ^ k ≤ N) :
    p ^ k * p ^ ((N - p ^ k) / p) ≤ p ^ (N / p) := by
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  have h1 := mul_le_pow_self hp k
  have h2 : (N - p ^ k + k * p) / p = (N - p ^ k) / p + k := Nat.add_mul_div_right _ _ (by omega)
  have h3 : (N - p ^ k + k * p) / p ≤ N / p := Nat.div_le_div_right (by rw [mul_comm k p]; omega)
  omega

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem apply_apply_eq_of_commute {E : Subgroup (Perm α)} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {g h : Perm α} (hg : g ∈ E) (hh : h ∈ E) {a : α} (hga : g a = a) : g (h a) = h a := by
  rw [← Perm.mul_apply, hc g hg h hh, Perm.mul_apply, hga]

omit [Fintype α] [DecidableEq α] in
theorem eq_bot_of_forall_apply_eq {E : Subgroup (Perm α)} (hfix : ∀ g ∈ E, ∀ a, g a = a) :
    E = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext a
  exact hfix g hg a

theorem card_le_pow_of_forall_apply_eq {p : ℕ} [hp : Fact p.Prime] (m : ℕ) :
    ∀ (s : Finset α), #s ≤ m → ∀ E : Subgroup (Perm α), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      IsPGroup p E → (∀ g ∈ E, ∀ a ∉ s, g a = a) → Nat.card E ≤ p ^ (#s / p) := by
  induction m with
  | zero =>
    intro s hs E _ _ hfix
    have hs0 : s = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [eq_bot_of_forall_apply_eq fun g hg a => hfix g hg a (by simp [hs0])]
    simpa using Nat.one_le_pow _ _ hp.out.pos
  | succ m ih =>
    intro s hs E hc hpE hfix
    rcases s.eq_empty_or_nonempty with hs0 | ⟨a, ha⟩
    · rw [eq_bot_of_forall_apply_eq fun g hg a => hfix g hg a (by simp [hs0])]
      simpa using Nat.one_le_pow _ _ hp.out.pos
    have hOs : ∀ b ∈ orbit E a, b ∈ s := by
      intro b hb'
      obtain ⟨h, rfl⟩ := mem_orbit_iff.mp hb'
      by_contra hb
      have h1 := hfix h h.2 _ hb
      rw [Subgroup.smul_def, Perm.smul_def] at h1 hb
      exact hb (by rw [(h : Perm α).injective h1]; exact ha)
    set O : Finset α := (Set.toFinite (orbit E a)).toFinset with hO
    have hOsub : O ⊆ s := fun b hb => hOs b ((Set.Finite.mem_toFinset _).1 hb)
    have haO : a ∈ O := (Set.Finite.mem_toFinset _).2 (mem_orbit_self a)
    have hOcard : Nat.card (orbit E a) = #O := Nat.card_eq_card_finite_toFinset _
    obtain ⟨k, hk⟩ := hpE.card_orbit a
    set E' : Subgroup (Perm α) := (stabilizer E a).map E.subtype with hE'
    have hE'E : E' ≤ E := Subgroup.map_subtype_le _
    have hcardE' : Nat.card E' = Nat.card (stabilizer E a) :=
      Subgroup.card_map_of_injective E.subtype_injective
    have hcardE : Nat.card E = Nat.card (orbit E a) * Nat.card (stabilizer E a) := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (orbitProdStabilizerEquivGroup E a)).symm
    have hfix' : ∀ g ∈ E', ∀ b ∉ s \ O, g b = b := by
      rintro _ ⟨g, hg, rfl⟩ b hb
      rw [Finset.mem_sdiff, not_and, not_not] at hb
      by_cases hbs : b ∈ s
      · obtain ⟨h, rfl⟩ := (Set.Finite.mem_toFinset _).1 (hb hbs)
        have hga : (g : Perm α) a = a := by
          have := mem_stabilizer_iff.1 hg
          rwa [Subgroup.smul_def, Perm.smul_def] at this
        simp only [Subgroup.coe_subtype, Subgroup.smul_def, Perm.smul_def]
        exact apply_apply_eq_of_commute hc g.2 h.2 hga
      · exact hfix g g.2 b hbs
    have hlt : #(s \ O) < #s := Finset.card_lt_card (Finset.sdiff_ssubset hOsub ⟨a, haO⟩)
    have ih' := ih (s \ O) (by omega) E' (fun x hx y hy => hc x (hE'E hx) y (hE'E hy))
      (hpE.to_le hE'E) hfix'
    rw [Finset.card_sdiff_of_subset hOsub] at ih'
    rw [hcardE, ← hcardE', hOcard]
    rw [hOcard] at hk
    rw [hk] at ih' ⊢
    calc p ^ k * Nat.card E' ≤ p ^ k * p ^ ((#s - p ^ k) / p) := Nat.mul_le_mul_left _ ih'
      _ ≤ p ^ (#s / p) := pow_mul_pow_div_le hp.out.two_le (hk ▸ Finset.card_le_card hOsub)

theorem card_le_pow_div_of_commute {p : ℕ} [Fact p.Prime] (E : Subgroup (Perm α))
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hpE : IsPGroup p E) :
    Nat.card E ≤ p ^ (Fintype.card α / p) := by
  simpa using card_le_pow_of_forall_apply_eq (Fintype.card α) univ (by simp) E hc hpE
    (fun _ _ a ha => absurd (mem_univ a) ha)

theorem pRank_top_perm_le {p : ℕ} (hp : p.Prime) :
    pRank p (⊤ : Subgroup (Perm α)) ≤ Fintype.card α / p := by
  have : Fact p.Prime := ⟨hp⟩
  refine SectionRank.pRank_le hp.one_lt fun E _ hE => card_le_pow_div_of_commute E ?_ ?_
  · intro x hx y hy
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  · exact fun g => ⟨1, Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, hE.2 _ g.2, OneMemClass.coe_one])⟩

theorem pRank_top_mulAut_le {K : Type*} [Group K] [Finite K] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime) :
    pRank p (⊤ : Subgroup (MulAut K)) ≤ n / p := by
  rw [SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt ((MulAut.congr e).trans
    (MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
      hn6)).symm)]
  simpa using pRank_top_perm_le (α := Fin n) hp

end CFSG.AGLEmbedding
