module

public import CFSG.ClassicalInvolution.Q3.Q3ABoot
public import CFSG.Walter.TwoRank

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn)

section ElemAbelian

theorem isElemAbelian_mono {G : Type*} [Group G] {p : ℕ} {E V : Subgroup G}
    (hE : IsElemAbelian p E) (hle : V ≤ E) : IsElemAbelian p V :=
  CFSG.Open.IsElemAbelian.mono hE hle

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (ψ : G →* H) {p : ℕ}
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map ψ) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_closure_pair {G : Type} [Group G] {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) :
    IsElemAbelian 2 (Subgroup.closure ({u, v} : Set G)) := by
  have h2 : ∀ s ∈ ({u, v} : Set G), s * s = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> assumption
  have hc : ∀ s ∈ ({u, v} : Set G), ∀ t ∈ ({u, v} : Set G), s * t = t * s := by
    intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      first | rfl | assumption | exact (by assumption : _ = _).symm
  exact Balance.Theorem5.isElemAbelian_closure_of_commuting_involutions h2 hc

theorem exists_fourGroup_of_two_le_twoRank {M : Type} [Group M] [Finite M]
    (h : 2 ≤ CFSG.Assembly.twoRank M) :
    ∃ E : Subgroup M, IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  classical
  have hbdd : BddAbove
      {k | ∃ E : Subgroup M, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨Nat.card M, fun k ⟨E, _, _, hk⟩ => (Nat.lt_two_pow_self).le.trans
      (hk ▸ Subgroup.card_le_card_group E)⟩
  have hne : Set.Nonempty
      {k | ∃ E : Subgroup M, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨0, ⊥, le_top, ⟨⟨⟨fun x y => Subsingleton.elim _ _⟩⟩, fun x hx => by
      rw [Subgroup.mem_bot.mp hx, one_pow]⟩, by simp⟩
  obtain ⟨E, -, hE, hcard⟩ := Nat.sSup_mem hne hbdd
  have hr : 2 ≤ CFSG.Assembly.twoRank M := h
  have hdvd : 2 ^ 2 ∣ Nat.card E := by
    rw [hcard]
    exact pow_dvd_pow 2 hr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 hdvd
  refine ⟨V.map E.subtype, ?_, ?_⟩
  · exact isElemAbelian_mono (E := E) hE (Subgroup.map_subtype_le V)
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective E), hV]
    norm_num

end ElemAbelian

section ModOdd

variable {G : Type} [Group G] [Finite G] (X : Subgroup G)

theorem mk_ne_one_of_involution {x : G} (hx : x ∈ X) (hsq : x * x = 1) (h1 : x ≠ 1) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨x, hx⟩ ≠ 1 := by
  intro h
  have hmem : (⟨x, hx⟩ : ↥X) ∈ classicalInvolutionOddCore ↥X := (QuotientGroup.eq_one_iff _).mp h
  exact h1 (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn X) ⟨_, hmem, rfl⟩ hsq)

theorem exists_conj_of_mk_eq {u v : G} (hu : u ∈ X) (hv : v ∈ X) (hu2 : u * u = 1)
    (hv2 : v * v = 1)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨u, hu⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨v, hv⟩) :
    ∃ o ∈ oddCoreIn X, v = o * u * o⁻¹ := by
  have h1 : (⟨v, hv⟩ : ↥X)⁻¹ * ⟨u, hu⟩ ∈ classicalInvolutionOddCore ↥X :=
    QuotientGroup.eq.mp h.symm
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hmem : v * u ∈ oddCoreIn X := by
    refine ⟨_, h1, ?_⟩
    simp [hvi]
  exact exists_conj_of_mul_mem hu2 hv2 (odd_card_oddCoreIn X) hmem

omit [Finite G] in
theorem mk_eq_of_mul_mem {u v : G} (hu : u ∈ X) (hv : v ∈ X) (hu2 : u * u = 1)
    (h : u * v ∈ oddCoreIn X) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨u, hu⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨v, hv⟩ := by
  obtain ⟨w, hw, hwe⟩ := h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hw' : (⟨u, hu⟩ : ↥X)⁻¹ * ⟨v, hv⟩ = w := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hui]
    exact hwe.symm
  rw [hw']
  exact hw

end ModOdd


section PairForm

theorem bd_pair_of_forall_fourGroup {Y : Type} [Group Y] [Finite Y] {z : Y} (hz1 : z ≠ 1)
    (hF : ∀ F : Subgroup Y, IsElemAbelian 2 F → Nat.card F = 4 → z ∈ F) {p q : Y}
    (hp2 : p * p = 1) (hq2 : q * q = 1) (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hpq : p ≠ q)
    (hc : p * q = q * p) : z = p ∨ z = q ∨ z = p * q := by
  have hFe := isElemAbelian_closure_pair hp2 hq2 hc
  have hF4 : Nat.card (Subgroup.closure ({p, q} : Set Y)) = 4 :=
    Balance.Bootstrap.card_closure_pair_eq_four hp2 hq2 hp1 hq1 hpq hc
  rcases mem_closure_pair_cases hp2 hq2 hc (hF _ hFe hF4) with h | h | h | h
  · exact absurd h hz1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem exists_conj_of_mk_eq_group {Y : Type} [Group Y] [Finite Y] {u v : Y} (hu2 : u * u = 1)
    (hv2 : v * v = 1)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore Y) u =
      QuotientGroup.mk' (classicalInvolutionOddCore Y) v) :
    ∃ o ∈ classicalInvolutionOddCore Y, v = o * u * o⁻¹ := by
  have h1 : v⁻¹ * u ∈ classicalInvolutionOddCore Y := QuotientGroup.eq.mp h.symm
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  rw [hvi] at h1
  exact exists_conj_of_mul_mem hu2 hv2 (CFSG.ComponentClassification.OddCore.odd_card Y) h1

end PairForm

section Centerless

theorem false_of_central_component {M X : Type} [Group M] [Group X] [Finite M] (ψ : M →* X)
    (hker : ψ.ker ≤ Subgroup.center M) (hcen : Subgroup.center M = ⊥)
    (hsimple : IsSimpleGroup M) (hnab : ∃ a b : M, a * b ≠ b * a)
    (heven : Even (Nat.card M)) {z : X} (hz1 : z ≠ 1) (hzc : ∀ x : X, x * z = z * x)
    (hF : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → z ∈ F) : False := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hcen ▸ hker
  obtain ⟨E, hE, hEcard⟩ := exists_fourGroup_of_two_le_twoRank
    (CFSG.Walter.two_le_twoRank M hnab heven)
  have hFcard : Nat.card (E.map ψ) = 4 := by
    rw [Subgroup.card_map_of_injective hinj, hEcard]
  obtain ⟨e, he, hez⟩ := hF (E.map ψ) (isElemAbelian_map ψ hE) hFcard
  have hec : e ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply hinj
    rw [map_mul, map_mul, hez]
    exact hzc (ψ m)
  rw [hcen, Subgroup.mem_bot] at hec
  rw [hec, map_one] at hez
  exact hz1 hez.symm

theorem isSimpleGroup_of_center_eq_bot {M : Type} [Group M] (hq : CFSG.Open.IsQuasisimple M)
    (hcen : Subgroup.center M = ⊥) : IsSimpleGroup M := by
  have e : M ⧸ Subgroup.center M ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have h2 : IsSimpleGroup (M ⧸ Subgroup.center M) := hq.2
  exact MulEquiv.isSimpleGroup e.symm

theorem exists_noncomm_of_isQuasisimple {M : Type} [Group M] (hq : CFSG.Open.IsQuasisimple M) :
    ∃ a b : M, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hsimple : IsSimpleGroup (M ⧸ Subgroup.center M) := hq.2
  have hperf : commutator M = ⊤ := hq.1
  have hcomm : commutator M = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨a, -, b, -, rfl⟩
    simp [commutatorElement_def, hcon a b]
  have htriv : Subsingleton M := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ commutator M := hperf ▸ Subgroup.mem_top a
    have hb : b ∈ commutator M := hperf ▸ Subgroup.mem_top b
    rw [hcomm, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have h1 : Subsingleton (M ⧸ Subgroup.center M) := inferInstance
  obtain ⟨x, y, hxy⟩ := (IsSimpleGroup.toNontrivial (G := M ⧸ Subgroup.center M)).exists_pair_ne
  exact hxy (Subsingleton.elim x y)

end Centerless

end CFSG.ClassicalInvolution.Q3.Q3Y
