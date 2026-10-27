module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def pmbFix (G : Type*) [Group G] [MulAction G X] {Y : Type*} (u : X → Y) :
    Subgroup G where
  carrier := {g | ∀ x, u (g • x) = u x}
  mul_mem' {a b} ha hb x := by
    simp only [Set.mem_setOf_eq] at ha hb
    rw [mul_smul, ha, hb]
  one_mem' x := by rw [one_smul]
  inv_mem' {a} ha x := by
    simp only [Set.mem_setOf_eq] at ha
    rw [← ha (a⁻¹ • x), smul_inv_smul]

theorem mem_pmbFix {Y : Type*} {u : X → Y} {g : G} : g ∈ pmbFix G u ↔ ∀ x, u (g • x) = u x :=
  Iff.rfl

@[expose] def pmbAff (X : Type*) [MulAction G X] (r : ℕ) (K : Subgroup G) : Set (X → ZMod r) :=
  {u | (∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c) ∧ K ≤ pmbFix G u}

theorem pmbAff_sub_smul {r : ℕ} {K : Subgroup G} {u v : X → ZMod r} (hu : u ∈ pmbAff X r K)
    (hv : v ∈ pmbAff X r K) (a : ZMod r) : u - a • v ∈ pmbAff X r K := by
  refine ⟨fun g => ?_, fun k hk => ?_⟩
  · obtain ⟨c, hc⟩ := hu.1 g
    obtain ⟨d, hd⟩ := hv.1 g
    refine ⟨c - a * d, fun x => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hc x, ← hd x]
    ring
  · rw [mem_pmbFix]
    intro x
    simp only [Pi.sub_apply, Pi.smul_apply, mem_pmbFix.mp (hu.2 hk) x, mem_pmbFix.mp (hv.2 hk) x]

theorem pmb_card_aff_le [Finite X] {r : ℕ} [Fact r.Prime] (K : Subgroup G) (b : G) :
    Nat.card (pmbAff X r K) ≤ r * Nat.card (pmbAff X r (K ⊔ Subgroup.zpowers b)) := by
  have key : ∀ w ∈ pmbAff X r K, (∀ x, w (b • x) = w x) →
      w ∈ pmbAff X r (K ⊔ Subgroup.zpowers b) :=
    fun w hw hb => ⟨hw.1, sup_le hw.2 (Subgroup.zpowers_le.mpr (mem_pmbFix.mpr hb))⟩
  by_cases h : ∀ w ∈ pmbAff X r K, ∀ x, w (b • x) = w x
  · calc Nat.card (pmbAff X r K) ≤ Nat.card (pmbAff X r (K ⊔ Subgroup.zpowers b)) :=
          Nat.card_mono (Set.toFinite _) fun w hw => key w hw (h w hw)
      _ ≤ r * _ := Nat.le_mul_of_pos_left _ (Fact.out : r.Prime).pos
  push Not at h
  obtain ⟨v, hv, x₀, hx₀⟩ := h
  let ψ : (X → ZMod r) → ZMod r := fun u => u x₀ - u (b • x₀)
  have hconst : ∀ u ∈ pmbAff X r K, ∀ x, u (b⁻¹ • x) - u x = ψ u := by
    intro u hu x
    obtain ⟨c, hc⟩ := hu.1 b
    rw [hc x, ← hc (b • x₀), inv_smul_smul]
  have hψv : ψ v ≠ 0 := sub_ne_zero.mpr (Ne.symm hx₀)
  have hmem : ∀ u ∈ pmbAff X r K, u - (ψ u / ψ v) • v ∈ pmbAff X r (K ⊔ Subgroup.zpowers b) := by
    intro u hu
    have hw := pmbAff_sub_smul hu hv (ψ u / ψ v)
    refine key _ hw fun x => ?_
    have h1 := hconst _ hw (b • x)
    have h2 : ψ (u - (ψ u / ψ v) • v) = 0 := by
      have : ψ (u - (ψ u / ψ v) • v) = ψ u - ψ u / ψ v * ψ v := by
        simp only [ψ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this, div_mul_cancel₀ _ hψv, sub_self]
    rw [h2, inv_smul_smul, sub_eq_zero] at h1
    exact h1.symm
  let Φ : pmbAff X r K → ZMod r × pmbAff X r (K ⊔ Subgroup.zpowers b) :=
    fun u => (ψ u, ⟨_, hmem u u.2⟩)
  have hΦ : Function.Injective Φ := by
    intro u₁ u₂ h
    simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, sub_left_inj] at h2
    exact Subtype.ext h2
  calc Nat.card (pmbAff X r K) ≤ Nat.card (ZMod r × pmbAff X r (K ⊔ Subgroup.zpowers b)) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = r * _ := by rw [Nat.card_prod, Nat.card_zmod]

theorem pmb_card_aff_top_le [Finite X] {r : ℕ} [NeZero r] :
    Nat.card (pmbAff X r (⊤ : Subgroup G)) ≤ r ^ Nat.card (orbitRel.Quotient G X) := by
  let F : pmbAff X r (⊤ : Subgroup G) → orbitRel.Quotient G X → ZMod r :=
    fun u ω => (u : X → ZMod r) ω.out
  have hF : Function.Injective F := by
    intro u v huv
    apply Subtype.ext
    funext x
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp
      (orbitRel_apply.mp (Quotient.mk_out' (s₁ := orbitRel G X) x))
    have h := congrFun huv (Quotient.mk'' x)
    simp only [F] at h
    rw [← hg, mem_pmbFix.mp (u.2.2 (Subgroup.mem_top g)),
      mem_pmbFix.mp (v.2.2 (Subgroup.mem_top g))] at h
    exact h
  calc Nat.card (pmbAff X r (⊤ : Subgroup G))
      ≤ Nat.card (orbitRel.Quotient G X → ZMod r) := Nat.card_le_card_of_injective F hF
    _ = r ^ Nat.card (orbitRel.Quotient G X) := by rw [Nat.card_fun, Nat.card_zmod]

theorem pmb_mul_card_le_of_lt [Finite G] {r : ℕ} [Fact r.Prime] (hG : IsPGroup r G)
    {K L : Subgroup G} (h : K < L) : r * Nat.card K ≤ Nat.card L := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hG.to_subgroup K)
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp (hG.to_subgroup L)
  have hr : 1 < r := (Fact.out : r.Prime).one_lt
  have hlt : Nat.card K < Nat.card L := Subgroup.card_lt_of_lt h
  rw [ha, hc] at hlt ⊢
  have hac : a < c := (Nat.pow_lt_pow_iff_right hr).mp hlt
  calc r * r ^ a = r ^ (a + 1) := by ring
    _ ≤ r ^ c := Nat.pow_le_pow_right hr.le hac

theorem pmb_card_aff_mul_card_le [Finite G] [Finite X] {r : ℕ} [Fact r.Prime]
    (hG : IsPGroup r G) (K : Subgroup G) :
    Nat.card (pmbAff X r K) * Nat.card K ≤
      r ^ Nat.card (orbitRel.Quotient G X) * Nat.card G := by
  suffices ∀ n, ∀ K : Subgroup G, Nat.card G - Nat.card K = n →
      Nat.card (pmbAff X r K) * Nat.card K ≤
        r ^ Nat.card (orbitRel.Quotient G X) * Nat.card G from this _ K rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hK
    by_cases htop : K = ⊤
    · subst htop
      rw [Subgroup.card_top]
      exact Nat.mul_le_mul_right _ pmb_card_aff_top_le
    obtain ⟨b, hb⟩ : ∃ b, b ∉ K := by
      by_contra! hall
      exact htop (eq_top_iff.mpr fun g _ => hall g)
    set K' := K ⊔ Subgroup.zpowers b
    have hlt : K < K' := by
      refine lt_of_le_of_ne le_sup_left fun he => hb ?_
      rw [he]
      exact (le_sup_right : Subgroup.zpowers b ≤ K') (Subgroup.mem_zpowers b)
    have hcard := Subgroup.card_lt_of_lt hlt
    have hle := Subgroup.card_le_card_group K'
    have h1 := ih _ (by omega) K' rfl
    have h2 := pmb_mul_card_le_of_lt hG hlt
    calc Nat.card (pmbAff X r K) * Nat.card K
        ≤ (r * Nat.card (pmbAff X r K')) * Nat.card K :=
          Nat.mul_le_mul_right _ (pmb_card_aff_le K b)
      _ = Nat.card (pmbAff X r K') * (r * Nat.card K) := by ring
      _ ≤ Nat.card (pmbAff X r K') * Nat.card K' := Nat.mul_le_mul_left _ h2
      _ ≤ _ := h1

theorem pmb_card_affine_le [Finite G] [Finite X] {r : ℕ} [Fact r.Prime] (hG : IsPGroup r G)
    (x₀ : X) :
    Nat.card {u : X → ZMod r // ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} ≤
      r ^ Nat.card (orbitRel.Quotient G X) * Nat.card (orbit G x₀) := by
  have hsub : ∀ u : X → ZMod r, (∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c) →
      u ∈ pmbAff X r (stabilizer G x₀) := by
    intro u hu
    refine ⟨hu, fun k hk => mem_pmbFix.mpr fun x => ?_⟩
    obtain ⟨c, hc⟩ := hu k⁻¹
    have h0 := hc x₀
    have h1 := hc x
    rw [inv_inv] at h0 h1
    rw [mem_stabilizer_iff.mp hk, sub_self] at h0
    rw [← h0, sub_eq_zero] at h1
    exact h1
  have h2 : Nat.card {u : X → ZMod r // ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} ≤
      Nat.card (pmbAff X r (stabilizer G x₀)) :=
    Nat.card_le_card_of_injective (fun u => ⟨u.1, hsub u.1 u.2⟩) fun u v h =>
      Subtype.ext (congrArg Subtype.val h :)
  have h3 : Nat.card (orbit G x₀) * Nat.card (stabilizer G x₀) = Nat.card G := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (orbitProdStabilizerEquivGroup G x₀)
  have h4 := (Nat.mul_le_mul_right (Nat.card (stabilizer G x₀)) h2).trans
    (pmb_card_aff_mul_card_le hG (stabilizer G x₀))
  rw [← h3, ← mul_assoc] at h4
  exact Nat.le_of_mul_le_mul_right h4 Nat.card_pos

theorem pmb_card_le_prod_card_orbit [Finite X] [FaithfulSMul G X]
    [Fintype (orbitRel.Quotient G X)] (hc : ∀ g h : G, g * h = h * g) :
    Nat.card G ≤ ∏ ω : orbitRel.Quotient G X, Nat.card (orbit G ω.out) := by
  rw [← Nat.card_pi]
  refine Nat.card_le_card_of_injective (fun g ω => ⟨g • ω.out, mem_orbit _ g⟩) fun g g' h => ?_
  refine eq_of_smul_eq_smul (α := X) fun x => ?_
  obtain ⟨k, hk⟩ := mem_orbit_iff.mp
    (orbitRel_apply.mp (Quotient.mk_out' (s₁ := orbitRel G X) x))
  have h1 := congrArg Subtype.val (congrFun h (Quotient.mk'' x))
  simp only at h1
  rw [← hk, smul_smul, smul_smul, hc g k, hc g' k, mul_smul, mul_smul] at h1
  exact smul_left_cancel k h1

theorem pmb_sum_card_orbit [Finite X] [Fintype (orbitRel.Quotient G X)] :
    ∑ ω : orbitRel.Quotient G X, Nat.card (orbit G ω.out) = Nat.card X :=
  ((Nat.card_congr (selfEquivSigmaOrbits G X)).trans Nat.card_sigma).symm

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
