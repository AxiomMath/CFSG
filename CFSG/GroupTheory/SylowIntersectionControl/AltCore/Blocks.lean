module

public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction
open CFSG.Quasithin (omegaOneCenterOf)

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem omegaOneCenterOf_eq_closure (K : Subgroup (Perm α)) :
    omegaOneCenterOf K = closure {x | x ∈ K ∧ (∀ k ∈ K, x * k = k * x) ∧ x ^ 2 = 1} := by
  unfold omegaOneCenterOf CFSG.Quasithin.omegaOneOf CFSG.Quasithin.centerOf
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, mem_inf, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨hx, hc⟩, h2⟩
    exact ⟨hx, fun k hk => (hc k hk).symm, h2⟩
  · rintro ⟨hx, hc, h2⟩
    exact ⟨⟨hx, fun k hk => (hc k hk).symm⟩, h2⟩

omit [Fintype α] [DecidableEq α] in
theorem omegaOneCenter_le (K : Subgroup (Perm α)) : omegaOneCenterOf K ≤ K := by
  rw [omegaOneCenterOf_eq_closure]
  exact (closure_le K).mpr fun _ hx => hx.1

omit [Fintype α] [DecidableEq α] in
theorem omegaOneCenter_commute (K : Subgroup (Perm α)) {x y : Perm α}
    (hx : x ∈ omegaOneCenterOf K) (hy : y ∈ K) : x * y = y * x := by
  rw [omegaOneCenterOf_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact hz.2.1 y hy
  | one => rw [one_mul, mul_one]
  | mul a b _ _ iha ihb => rw [mul_assoc, ihb, ← mul_assoc, iha, mul_assoc]
  | inv a _ ih => exact Commute.inv_left (show Commute a y from ih)

omit [Fintype α] [DecidableEq α] in
theorem omegaOneCenter_sq (K : Subgroup (Perm α)) {x : Perm α} (hx : x ∈ omegaOneCenterOf K) :
    x ^ 2 = 1 := by
  rw [omegaOneCenterOf_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact hz.2.2
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := omegaOneCenter_commute K
      (by rw [omegaOneCenterOf_eq_closure]; exact ha) (omegaOneCenter_le K
        (by rw [omegaOneCenterOf_eq_closure]; exact hb))
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a _ ih => rw [inv_pow, ih, inv_one]

omit [Fintype α] [DecidableEq α] in
private theorem conj_mem_omegaOneCenterOf {K : Subgroup (Perm α)} {n : Perm α}
    (hn : n ∈ normalizer (K : Set (Perm α))) {x : Perm α} (hx : x ∈ omegaOneCenterOf K) :
    n * x * n⁻¹ ∈ omegaOneCenterOf K := by
  rw [omegaOneCenterOf_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    refine subset_closure ⟨(mem_normalizer_iff.mp hn z).mp hz.1, fun k hk => ?_, ?_⟩
    · have hk' : n⁻¹ * k * n ∈ K := by
        simpa using (mem_normalizer_iff.mp (inv_mem hn) k).mp hk
      have h := hz.2.1 _ hk'
      calc n * z * n⁻¹ * k = n * (z * (n⁻¹ * k * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * k * n) * z) * n⁻¹ := by rw [h]
        _ = k * (n * z * n⁻¹) := by group
    · rw [conj_pow, hz.2.2, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b _ _ iha ihb =>
    rw [show n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) by group]
    exact mul_mem iha ihb
  | inv a _ ih =>
    rw [show n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ by group]
    exact inv_mem ih

omit [Fintype α] [DecidableEq α] in
theorem normalizer_le_normalizer_omegaOneCenterOf (K : Subgroup (Perm α)) :
    normalizer (K : Set (Perm α)) ≤ normalizer (omegaOneCenterOf K : Set (Perm α)) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_omegaOneCenterOf hn, fun hh => ?_⟩
  simpa [mul_assoc] using conj_mem_omegaOneCenterOf (inv_mem hn) hh

omit [DecidableEq α] in
theorem omegaOneCenter_ne_bot {K : Subgroup (Perm α)} (hK : IsPGroup 2 K) (hK1 : K ≠ ⊥) :
    omegaOneCenterOf K ≠ ⊥ := by
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  have : Nontrivial (Subgroup.center K) := hK.center_nontrivial
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : IsPGroup 2 (Subgroup.center K) := hK.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center K) := by
    obtain ⟨n, hn0, hn⟩ := hc.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨c, hc2⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hc1 : c ≠ 1 := fun h => by simp [h] at hc2
  have hcsq : c ^ 2 = 1 := by simpa [hc2] using pow_orderOf_eq_one c
  have hy2 : ((c : K) : Perm α) ^ 2 = 1 := by
    simpa using congrArg (fun z : Subgroup.center K => ((z : K) : Perm α)) hcsq
  have hycen : ∀ k ∈ K, ((c : K) : Perm α) * k = k * ((c : K) : Perm α) := fun k hk =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨k, hk⟩)).symm
  intro hbot
  have hmem : ((c : K) : Perm α) ∈ omegaOneCenterOf K := by
    rw [omegaOneCenterOf_eq_closure]
    exact subset_closure ⟨(c : K).2, hycen, hy2⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hc1 (Subtype.ext (Subtype.ext hmem))

omit [Fintype α] [DecidableEq α] in
private theorem mem_orbit_iff' {E : Subgroup (Perm α)} {x y : α} :
    y ∈ orbit E x ↔ ∃ e ∈ E, e x = y := by
  constructor
  · rintro ⟨⟨e, he⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

omit [Fintype α] [DecidableEq α] in
private theorem apply_mem_orbit {E : Subgroup (Perm α)} {e : Perm α} (he : e ∈ E) {x y : α}
    (hy : y ∈ orbit E x) : e y ∈ orbit E x := by
  obtain ⟨f, hf, rfl⟩ := mem_orbit_iff'.mp hy
  exact mem_orbit_iff'.mpr ⟨e * f, E.mul_mem he hf, rfl⟩

@[expose] def blockKer (E : Subgroup (Perm α)) : Subgroup (Perm α) where
  carrier := {g | ∀ x, g x ∈ orbit E x}
  mul_mem' := by
    intro a b ha hb x
    have h1 : a (b x) ∈ orbit E (b x) := ha (b x)
    rwa [orbit_eq_iff.mpr (hb x)] at h1
  one_mem' := fun x => mem_orbit_self x
  inv_mem' := by
    intro a ha x
    have h1 : x ∈ orbit E (a⁻¹ x) := by simpa using ha (a⁻¹ x)
    rw [orbit_eq_iff.mpr h1]
    exact mem_orbit_self _

@[expose] def blockBase (E : Subgroup (Perm α)) : Subgroup (Perm α) where
  carrier := {g | ∀ x, ∃ e ∈ E, ∀ y ∈ orbit E x, g y = e y}
  mul_mem' := by
    intro a b ha hb x
    obtain ⟨e, he, hae⟩ := ha x
    obtain ⟨f, hf, hbf⟩ := hb x
    refine ⟨e * f, E.mul_mem he hf, fun y hy => ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, hbf y hy, hae _ (apply_mem_orbit hf hy)]
  one_mem' := fun x => ⟨1, E.one_mem, fun y _ => rfl⟩
  inv_mem' := by
    intro a ha x
    obtain ⟨e, he, hae⟩ := ha x
    refine ⟨e⁻¹, E.inv_mem he, fun y hy => ?_⟩
    have h1 := hae _ (apply_mem_orbit (E.inv_mem he) hy)
    have h2 : e (e⁻¹ y) = y := by simp
    rw [h2] at h1
    exact Perm.inv_eq_iff_eq.mpr h1.symm

omit [Fintype α] [DecidableEq α] in
theorem blockBase_le_blockKer (E : Subgroup (Perm α)) : blockBase E ≤ blockKer E := by
  intro g hg x
  obtain ⟨e, he, hge⟩ := hg x
  rw [hge x (mem_orbit_self x)]
  exact apply_mem_orbit he (mem_orbit_self x)

omit [Fintype α] [DecidableEq α] in
theorem blockBase_sq {E : Subgroup (Perm α)} (hE : ∀ e ∈ E, e ^ 2 = 1) {g : Perm α}
    (hg : g ∈ blockBase E) : g ^ 2 = 1 := by
  ext y
  obtain ⟨e, he, hge⟩ := hg y
  have h1 : g y = e y := hge y (mem_orbit_self y)
  have h2 : g (e y) = e (e y) := hge _ (apply_mem_orbit he (mem_orbit_self y))
  have h3 : e (e y) = y := by simpa [pow_two] using congrArg (fun f : Perm α => f y) (hE e he)
  rw [pow_two, Perm.mul_apply, h1, h2, h3]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem isPGroup_blockBase {E : Subgroup (Perm α)} (hE : ∀ e ∈ E, e ^ 2 = 1) :
    IsPGroup 2 (blockBase E) := fun g =>
  ⟨1, Subtype.ext (by simpa using blockBase_sq hE g.2)⟩

omit [Fintype α] [DecidableEq α] in
private theorem apply_mem_orbit_of_mem_normalizer {E : Subgroup (Perm α)} {n : Perm α}
    (hn : n ∈ normalizer (E : Set (Perm α))) {x y : α} (hy : y ∈ orbit E x) :
    n y ∈ orbit E (n x) := by
  obtain ⟨e, he, rfl⟩ := mem_orbit_iff'.mp hy
  refine mem_orbit_iff'.mpr ⟨n * e * n⁻¹, (mem_normalizer_iff.mp hn e).mp he, ?_⟩
  simp [Perm.mul_apply]

omit [Fintype α] [DecidableEq α] in
private theorem conj_mem_blockKer {E : Subgroup (Perm α)} {n : Perm α}
    (hn : n ∈ normalizer (E : Set (Perm α))) {g : Perm α} (hg : g ∈ blockKer E) :
    n * g * n⁻¹ ∈ blockKer E := fun x => by
  simpa using apply_mem_orbit_of_mem_normalizer hn (hg (n⁻¹ x))

omit [Fintype α] [DecidableEq α] in
theorem normalizer_le_normalizer_blockKer (E : Subgroup (Perm α)) :
    normalizer (E : Set (Perm α)) ≤ normalizer (blockKer E : Set (Perm α)) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_blockKer hn, fun h => ?_⟩
  simpa [mul_assoc] using conj_mem_blockKer (inv_mem hn) h

omit [Fintype α] [DecidableEq α] in
private theorem conj_mem_blockBase {E : Subgroup (Perm α)} {n : Perm α}
    (hn : n ∈ normalizer (E : Set (Perm α))) {g : Perm α} (hg : g ∈ blockBase E) :
    n * g * n⁻¹ ∈ blockBase E := by
  intro x
  obtain ⟨e, he, hge⟩ := hg (n⁻¹ x)
  refine ⟨n * e * n⁻¹, (mem_normalizer_iff.mp hn e).mp he, fun y hy => ?_⟩
  have hy' : n⁻¹ y ∈ orbit E (n⁻¹ x) := apply_mem_orbit_of_mem_normalizer (inv_mem hn) hy
  simp only [Perm.mul_apply, hge _ hy']

omit [Fintype α] [DecidableEq α] in
theorem normalizer_le_normalizer_blockBase (E : Subgroup (Perm α)) :
    normalizer (E : Set (Perm α)) ≤ normalizer (blockBase E : Set (Perm α)) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_blockBase hn, fun h => ?_⟩
  simpa [mul_assoc] using conj_mem_blockBase (inv_mem hn) h

omit [Fintype α] [DecidableEq α] in
theorem mem_blockBase_of_mem_blockKer {E K : Subgroup (Perm α)}
    (hEc : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e) (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    {k : Perm α} (hk : k ∈ K) (hkb : k ∈ blockKer E) : k ∈ blockBase E := by
  intro x
  obtain ⟨e₀, he₀, h₀⟩ := mem_orbit_iff'.mp (hkb x)
  refine ⟨e₀, he₀, fun y hy => ?_⟩
  obtain ⟨e, he, rfl⟩ := mem_orbit_iff'.mp hy
  have h1 : k (e x) = e (k x) := by
    simpa using (congrArg (fun f : Perm α => f x) (hEc e he k hk)).symm
  rw [h1, ← h₀]
  simpa using congrArg (fun f : Perm α => f x) (hEab e he e₀ he₀)

omit [Fintype α] [DecidableEq α] in
theorem apply_eq_of_mem_orbit {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    {e : Perm α} (he : e ∈ E) {x : α} (hx : e x = x) {y : α} (hy : y ∈ orbit E x) : e y = y := by
  obtain ⟨f, hf, rfl⟩ := mem_orbit_iff'.mp hy
  have h := congrArg (fun g : Perm α => g x) (hEab e he f hf)
  simpa [hx] using h

omit [Fintype α] [DecidableEq α] in
theorem card_orbit_eq_of_normalizer {E : Subgroup (Perm α)} {g : Perm α}
    (hg : g ∈ normalizer (E : Set (Perm α))) (x : α) :
    Nat.card (orbit E (g x)) = Nat.card (orbit E x) := by
  have himg : (g : α → α) '' orbit E x = orbit E (g x) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact apply_mem_orbit_of_mem_normalizer hg hy
    · intro hz
      refine ⟨g⁻¹ z, ?_, by simp⟩
      simpa using apply_mem_orbit_of_mem_normalizer (inv_mem hg) hz
  rw [← himg]
  exact Nat.card_image_of_injective g.injective _

private theorem sign_eq_one_of_sq_eq_one {g : Perm α} (hg : g ^ 2 = 1) (h4 : 4 ∣ g.support.card) :
    sign g = 1 := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one hg, Equiv.Perm.card_fixedPoints,
    Nat.sub_sub_self g.sum_cycleType_le, g.sum_cycleType]
  obtain ⟨m, hm⟩ := h4
  rw [hm, show 4 * m / 2 = 2 * m by omega, pow_mul]
  simp

omit [DecidableEq α] in
private theorem four_dvd_ncard_of_stable {E : Subgroup (Perm α)} (n : ℕ) :
    ∀ S : Set α, S.ncard = n → (∀ e ∈ E, ∀ x ∈ S, e x ∈ S) →
      (∀ x ∈ S, 4 ∣ Nat.card (orbit E x)) → 4 ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hSn hS h4
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp at hSn
      simp [← hSn]
    · have hOS : orbit E x ⊆ S := fun y hy => by
        obtain ⟨e, he, rfl⟩ := mem_orbit_iff'.mp hy
        exact hS e he x hx
      have hO4 : 4 ∣ (orbit E x).ncard := by
        rw [← Nat.card_coe_set_eq]
        exact h4 x hx
      have hstab : ∀ e ∈ E, ∀ y ∈ S \ orbit E x, e y ∈ S \ orbit E x := by
        rintro e he y ⟨hyS, hyO⟩
        refine ⟨hS e he y hyS, fun h => hyO ?_⟩
        simpa using apply_mem_orbit (E.inv_mem he) h
      have hcard := Set.ncard_sdiff_add_ncard_of_subset hOS S.toFinite
      have hpos : 0 < (orbit E x).ncard :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, mem_orbit_self x⟩
      have := ih (S \ orbit E x).ncard (by omega) (S \ orbit E x) rfl hstab
        fun y hy => h4 y hy.1
      omega

private theorem support_stable {E : Subgroup (Perm α)}
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) {g : Perm α} (hg : g ∈ blockBase E) :
    ∀ e ∈ E, ∀ x ∈ (g.support : Set α), e x ∈ (g.support : Set α) := by
  intro e he x hx
  rw [Finset.mem_coe, Equiv.Perm.mem_support] at hx ⊢
  obtain ⟨f, hf, hgf⟩ := hg x
  have hy : e x ∈ orbit E x := mem_orbit_iff'.mpr ⟨e, he, rfl⟩
  intro hfix
  have h1 : f (e x) = e x := by rw [← hgf _ hy]; exact hfix
  have hxo : x ∈ orbit E (e x) := mem_orbit_iff'.mpr ⟨e⁻¹, E.inv_mem he, by simp⟩
  have h2 : f x = x := apply_eq_of_mem_orbit hEab hf h1 hxo
  exact hx (by rw [hgf x (mem_orbit_self x)]; exact h2)

private theorem card_orbit_ne_one_of_mem_support {E : Subgroup (Perm α)} {g : Perm α}
    (hg : g ∈ blockBase E) {x : α} (hx : x ∈ g.support) : Nat.card (orbit E x) ≠ 1 := by
  rw [Equiv.Perm.mem_support] at hx
  obtain ⟨f, hf, hgf⟩ := hg x
  intro h1
  have hfx : f x ∈ orbit E x := mem_orbit_iff'.mpr ⟨f, hf, rfl⟩
  obtain ⟨y, hy⟩ := Nat.card_eq_one_iff_exists.mp h1
  have e1 := hy ⟨f x, hfx⟩
  have e2 := hy ⟨x, mem_orbit_self x⟩
  exact hx (by rw [hgf x (mem_orbit_self x)]; exact congrArg Subtype.val (e1.trans e2.symm))

theorem blockBase_le_alternatingGroup {E : Subgroup (Perm α)} (hE : ∀ e ∈ E, e ^ 2 = 1)
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (h4 : ∀ x : α, Nat.card (orbit E x) = 1 ∨ 4 ∣ Nat.card (orbit E x)) :
    blockBase E ≤ alternatingGroup α := by
  intro g hg
  rw [Equiv.Perm.mem_alternatingGroup]
  refine sign_eq_one_of_sq_eq_one (blockBase_sq hE hg) ?_
  have := four_dvd_ncard_of_stable _ (g.support : Set α) rfl (support_stable hEab hg)
    fun x hx => (h4 x).resolve_left (card_orbit_ne_one_of_mem_support hg hx)
  rwa [Set.ncard_coe_finset] at this

end CFSG.GroupTheory.AltCore
