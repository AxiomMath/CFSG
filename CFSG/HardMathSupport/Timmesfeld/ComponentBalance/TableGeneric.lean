module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

section Bridge

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem open_pRank_top_eq_pRank (p : ℕ) (H : Type*) [Group H] [Finite H] :
    CFSG.Open.pRank p (⊤ : Subgroup H) = CFSG.pRank p H :=
  (pRank_eq_open_pRank_top p H).symm

theorem open_pRank_eq_pRank_top (H : Subgroup G) :
    CFSG.Open.pRank p H = CFSG.Open.pRank p (⊤ : Subgroup ↥H) :=
  pRank_eq_pRank_top_subgroup H

variable {G' : Type*} [Group G'] [Finite G']

theorem pRank_map_eq_of_injective (hp : 1 < p) (f : G →* G') (hf : Function.Injective f)
    (H : Subgroup G) : CFSG.Open.pRank p (H.map f) = CFSG.Open.pRank p H := by
  rw [pRank_eq_pRank_top_subgroup (H.map f), pRank_eq_pRank_top_subgroup H]
  exact (pRank_top_eq_of_mulEquiv hp (Subgroup.equivMapOfInjective H f hf)).symm

theorem pRank_map_mulEquiv (hp : 1 < p) (e : G ≃* G') (H : Subgroup G) :
    CFSG.Open.pRank p (H.map e.toMonoidHom) = CFSG.Open.pRank p H :=
  pRank_map_eq_of_injective hp e.toMonoidHom e.injective H

end Bridge

section KerRange

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {G' : Type*} [Group G']

omit [Finite G] in
theorem exists_card_split_map (hp : p.Prime) {E : Subgroup G} {k : ℕ} (hk : Nat.card E = p ^ k)
    (f : G →* G') :
    ∃ i j : ℕ, i + j = k ∧ Nat.card (E.map f) = p ^ i ∧
      ∃ F : Subgroup G, F ≤ E ∧ F ≤ f.ker ∧ Nat.card F = p ^ j := by
  let g : E →* G' := f.comp E.subtype
  have hrange : g.range = E.map f := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, g, MonoidHom.comp_apply,
      Subgroup.subtype_apply, Subtype.exists, exists_prop]
  have hcard : Nat.card E = Nat.card (E ⧸ g.ker) * Nat.card g.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  have hquot : Nat.card (E ⧸ g.ker) = Nat.card (E.map f) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have h1 : Nat.card (E.map f) ∣ p ^ k := by
    rw [← hk, hcard, hquot]
    exact dvd_mul_right _ _
  have h2 : Nat.card g.ker ∣ p ^ k := by
    rw [← hk, hcard]
    exact dvd_mul_left _ _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h2
  refine ⟨i, j, ?_, hi, g.ker.map E.subtype, ?_, ?_, ?_⟩
  · have : p ^ (i + j) = p ^ k := by
      rw [pow_add, ← hi, ← hj, ← hquot, ← hcard, hk]
    exact Nat.pow_right_injective hp.two_le this
  · exact fun x hx => by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact hy
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hj]

variable [Finite G']

theorem pRank_top_le_pRank_ker_add_pRank_range (hp : p.Prime) (f : G →* G') :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤
      CFSG.Open.pRank p f.ker + CFSG.Open.pRank p f.range := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup G)
  obtain ⟨i, j, hij, hi, F, hFE, hFk, hj⟩ := exists_card_split_map hp hcard f
  have hi' : i ≤ CFSG.Open.pRank p f.range :=
    le_pRank hp1 (fun y hy => by
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨x, rfl⟩) (isElemAbelian_map hE f) hi
  have hj' : j ≤ CFSG.Open.pRank p f.ker :=
    le_pRank hp1 hFk (isElemAbelian_of_le hE hFE) hj
  omega

theorem pRank_top_le_add_of_normal (hp : p.Prime) (N : Subgroup G) [N.Normal] :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤
      CFSG.Open.pRank p (⊤ : Subgroup N) + CFSG.Open.pRank p (⊤ : Subgroup (G ⧸ N)) := by
  have h := pRank_top_le_pRank_ker_add_pRank_range hp (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', pRank_eq_pRank_top_subgroup N] at h
  exact h.trans (Nat.add_le_add_left (pRank_mono hp.one_lt le_top) _)

end KerRange

section Perfect

open CFSG.ComponentClassification.PerfectAutomorphisms

variable {L : Type*} [Group L] [Finite L] {p : ℕ}

omit [Finite L] in
theorem centerQuotientHom_injective_of_commutator (hL : commutator L = ⊤) :
    Function.Injective (centerQuotientHom L) := by
  have : Group.IsPerfect L := Group.isPerfect_def.mpr hL
  exact centerQuotientHom_injective L

theorem pRank_mulAut_le_of_perfect (hp : 1 < p) (hL : commutator L = ⊤) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (L ⧸ Subgroup.center L))) :=
  pRank_top_le_of_injective hp (centerQuotientHom L) (centerQuotientHom_injective_of_commutator hL)

theorem pRank_mulAut_le_of_quasisimple (hp : 1 < p) (hq : CFSG.Open.IsQuasisimple L) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (L ⧸ Subgroup.center L))) :=
  pRank_mulAut_le_of_perfect hp hq.1

theorem pRank_quotient_center_eq_of_not_dvd (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) =
      CFSG.Open.pRank p (⊤ : Subgroup L) :=
  haveI : Fact p.Prime := ⟨hp⟩
  pRank_quotient_eq (Subgroup.center L) hZ

omit [Finite L] in
theorem exists_noncomm_quotient_center_of_quasisimple (hq : CFSG.Open.IsQuasisimple L) :
    ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcomm : commutator L ≤ Subgroup.center L := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    have h1 : QuotientGroup.mk' (Subgroup.center L) ⁅g₁, g₂⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcon _ _
    exact (QuotientGroup.eq_one_iff _).1 h1
  have htop : Subgroup.center L = ⊤ := top_le_iff.1 (hq.1 ▸ hcomm)
  have := hq.2.toNontrivial
  have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ hsub

end Perfect

section Out

variable (X : Type*) [Group X]

@[expose] def innerAut : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range

instance innerAut_normal : (innerAut X).Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ g
    refine ⟨g x, ?_⟩
    ext y
    simp [MulAut.conj_apply]

variable {X}

noncomputable def innerAutEquiv (hZ : Subgroup.center X = ⊥) : X ≃* innerAut X :=
  MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)

variable [Finite X] {p : ℕ}

omit [Finite X] in
theorem center_eq_bot_of_simple_nonabelian [IsSimpleGroup X] (h : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center X = ⊥ := by
  rcases (Subgroup.center X).normal_of_characteristic.eq_bot_or_eq_top with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center X := by rw [h0]; trivial
    exact hab (by simpa [eq_comm] using (Subgroup.mem_center_iff.1 ha b))

theorem center_quotient_eq_bot_of_quasisimple {L : Type*} [Group L] (hq : CFSG.Open.IsQuasisimple L) :
    Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
  have := hq.2
  exact center_eq_bot_of_simple_nonabelian (exists_noncomm_quotient_center_of_quasisimple hq)

end Out

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
