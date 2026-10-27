module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import CFSG.Certificates.Kernel.Co1DceCover
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.Certificates.DceTw

variable {G : Type*} [Group G] {K : Type*} [Group K]

structure Orb (M : Subgroup K) (NORD : ℕ) (Pt : Type*) (act : Pt → K → Pt) (θ : Pt) (ω : ℕ → Pt)
    (g : ℕ → M) (NO I0 : ℕ) (σ : ℕ → M) (nT : ℕ) : Prop where
  finM : Finite M
  cardM : Nat.card M ≤ NORD
  act_one : ∀ p, act p 1 = p
  act_mul : ∀ p a b, act (act p a) b = act p (a * b)
  orbit : ∀ j < NO, act θ (g j) = ω j
  ω_inj : ∀ j < NO, ∀ j' < NO, ω j = ω j' → j = j'
  I0_lt : I0 < NO
  ωI0 : ω I0 = θ
  stab : ∀ e < nT, act θ (σ e) = θ
  σ_inj : ∀ e < nT, ∀ e' < nT, σ e = σ e' → e = e'
  nord : nT * NO = NORD

structure Hyp (N : Subgroup G) (u : G) (M : Subgroup K) (φ : M →* G) (NORD : ℕ) (Pt : Type*)
    (act : Pt → K → Pt) (θ : Pt) (ω : ℕ → Pt) (g : ℕ → M) (NO I0 : ℕ) (σ : ℕ → M) (nT : ℕ)
    (w : ℕ → G) (A : Finset ℕ) (mD : ℕ → ℕ) : Prop where
  φN : ∀ m, φ m ∈ N
  Nφ : ∀ n ∈ N, ∃ m, φ m = n
  orb : Orb M NORD Pt act θ ω g NO I0 σ nT
  psi : ∀ e < nT, ∃ e' < nT, u⁻¹ * φ (σ e) * u = φ (σ e')
  usq : ∃ m, u * u = φ m
  zero_mem : 0 ∈ A
  w_zero : w 0 = 1
  cover : ∀ D ∈ A, ∀ j < NO,
    (∃ D' ∈ A, ∃ π : M, w D * ((φ (g j))⁻¹ * u * φ (g j)) * (w D' * φ π)⁻¹ ∈ N) ∨
    (∃ D' ∈ A, ∃ j' < NO, ∃ π : M, act (ω j) π = ω j' ∧
      w D' * ((φ (g j'))⁻¹ * u * φ (g j')) * (w D * φ π)⁻¹ ∈ N)
  mD_dvd : ∀ D ∈ A, D ≠ 0 → mD D ∣ NORD
  stabD : ∀ D ∈ A, D ≠ 0 → mD D = 1 ∨ ∃ E : ℕ → M, (∀ k < mD D, ∀ k' < mD D, E k = E k' → k = k') ∧
    ∀ k < mD D, w D * φ (E k) * (w D)⁻¹ ∈ N

variable {N : Subgroup G} {u : G} {M : Subgroup K} {φ : M →* G} {NORD : ℕ} {Pt : Type*}
  {act : Pt → K → Pt} {θ : Pt} {ω : ℕ → Pt} {g : ℕ → M} {NO I0 : ℕ} {σ : ℕ → M} {nT : ℕ}
  {w : ℕ → G} {A : Finset ℕ} {mD : ℕ → ℕ}

theorem fin_N (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) :
    Finite N ∧ Nat.card N ≤ Nat.card M := by
  have _ := h.orb.finM
  let f : M → N := fun m => ⟨φ m, h.φN m⟩
  have hf : Function.Surjective f := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := h.Nφ n hn
    exact ⟨m, rfl⟩
  exact ⟨Finite.of_surjective f hf, Nat.card_le_card_of_surjective f hf⟩

theorem decompO (o : Orb M NORD Pt act θ ω g NO I0 σ nT) :
    Nat.card M = NORD ∧ ∀ m : M, ∃ e < nT, ∃ j < NO, m = σ e * g j := by
  classical
  have _ := o.finM
  let _ : Fintype M := Fintype.ofFinite M
  let F : ℕ × ℕ → M := fun p => σ p.1 * g p.2
  let S : Finset (ℕ × ℕ) := Finset.range nT ×ˢ Finset.range NO
  have hinj : Set.InjOn F S := by
    rintro ⟨e, j⟩ hej ⟨e', j'⟩ hej' he
    simp only [S, Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hej hej'
    have h1 : act θ ((F (e, j) : M) : K) = ω j := by
      simp only [F, Subgroup.coe_mul]
      rw [← o.act_mul, o.stab e hej.1, o.orbit j hej.2]
    have h2 : act θ ((F (e', j') : M) : K) = ω j' := by
      simp only [F, Subgroup.coe_mul]
      rw [← o.act_mul, o.stab e' hej'.1, o.orbit j' hej'.2]
    rw [he, h2] at h1
    have hj := o.ω_inj j' hej'.2 j hej.2 h1
    subst hj
    simp only [F, mul_left_inj] at he
    rw [o.σ_inj e hej.1 e' hej'.1 he]
  have hcard : S.card ≤ Nat.card M := by
    have := Finset.card_le_card_of_injOn F (fun _ _ => Finset.mem_univ _) hinj
    simpa [Nat.card_eq_fintype_card] using this
  have hS : S.card = NORD := by
    simp [S, Finset.card_product, ← o.nord]
  have hM : Nat.card M = NORD := le_antisymm o.cardM (hS ▸ hcard)
  refine ⟨hM, fun m => ?_⟩
  have himage : (S.image F).card = Nat.card M := by
    rw [Finset.card_image_of_injOn hinj, hS, hM]
  have hall : S.image F = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [himage, Nat.card_eq_fintype_card]
  have hm : m ∈ S.image F := by rw [hall]; exact Finset.mem_univ _
  obtain ⟨⟨e, j⟩, hej, rfl⟩ := Finset.mem_image.1 hm
  simp only [S, Finset.mem_product, Finset.mem_range] at hej
  exact ⟨e, hej.1, j, hej.2, rfl⟩

theorem decomp (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) :
    Nat.card M = NORD ∧ ∀ m : M, ∃ e < nT, ∃ j < NO, m = σ e * g j := decompO h.orb

theorem stab_eq (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) (s : M)
    (hs : act θ (s : K) = θ) : ∃ e < nT, s = σ e := by
  classical
  obtain ⟨-, hdec⟩ := decomp h
  have hgI0 : act θ (g I0 : K) = θ := by rw [h.orb.orbit I0 h.orb.I0_lt, h.orb.ωI0]
  have key : ∀ t : M, act θ (t : K) = θ → ∃ e < nT, t = σ e * g I0 := by
    intro t ht
    obtain ⟨e, he, j, hj, rfl⟩ := hdec t
    have : ω j = θ := by
      rw [← h.orb.orbit j hj]
      calc act θ (g j : K) = act (act θ (σ e : K)) (g j) := by rw [h.orb.stab e he]
        _ = act θ ((σ e : K) * g j) := h.orb.act_mul _ _ _
        _ = θ := by simpa using ht
    rw [← h.orb.ωI0] at this
    rw [h.orb.ω_inj j hj I0 h.orb.I0_lt this]
    exact ⟨e, he, rfl⟩
  obtain ⟨e1, he1, rfl⟩ := key s hs
  let f : ℕ → ℕ := fun e => if hx : ∃ e' < nT, σ e = σ e' * g I0 then Classical.choose hx else 0
  have hf : ∀ e < nT, f e < nT ∧ σ e = σ (f e) * g I0 := by
    intro e he
    have hx := key (σ e) (h.orb.stab e he)
    simp only [f, dite_eq_left hx]
    exact Classical.choose_spec hx
  have hinj : Set.InjOn f (Finset.range nT : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have e1 := (hf a ha).2
    have e2 := (hf b hb).2
    rw [hab, ← e2] at e1
    exact h.orb.σ_inj a ha b hb e1
  have hmaps : Set.MapsTo f (Finset.range nT : Set ℕ) (Finset.range nT : Set ℕ) := by
    intro a ha
    simp only [Finset.coe_range, Set.mem_Iio] at ha ⊢
    exact (hf a ha).1
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range nT) (t := Finset.range nT)
    (fun a _ => f a) (fun a ha => Finset.mem_coe.1 (hmaps (Finset.mem_coe.2 ha)))
    (fun a b ha hb hab => hinj (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab) (le_refl _)
  obtain ⟨e, he, hfe⟩ := hsurj e1 (Finset.mem_range.2 he1)
  have he' := Finset.mem_range.1 he
  refine ⟨e, he', ?_⟩
  rw [(hf e he').2, ← hfe]

theorem conj_stab (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) (s : M)
    (hs : act θ (s : K) = θ) : u⁻¹ * φ s * u ∈ N ∧ u * φ s * u⁻¹ ∈ N := by
  classical
  obtain ⟨e, he, rfl⟩ := stab_eq h s hs
  refine ⟨?_, ?_⟩
  · obtain ⟨e', -, he'⟩ := h.psi e he
    rw [he']
    exact h.φN _
  · let S : Finset G := (Finset.range nT).image fun e => φ (σ e)
    let c : G → G := fun y => u⁻¹ * y * u
    have hmaps : ∀ y ∈ S, c y ∈ S := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨e', he', h'⟩ := h.psi e (Finset.mem_range.1 he)
      exact Finset.mem_image.2 ⟨e', Finset.mem_range.2 he', h'.symm⟩
    have hinj : ∀ y z, y ∈ S → z ∈ S → c y = c z → y = z := by
      intro y z _ _ hyz
      simpa [c] using hyz
    obtain ⟨y, hy, hcy⟩ := Finset.surj_on_of_inj_on_of_card_le (s := S) (t := S) (fun y _ => c y)
      hmaps hinj (le_refl _) (φ (σ e)) (Finset.mem_image.2 ⟨e, Finset.mem_range.2 he, rfl⟩)
    have : u * φ (σ e) * u⁻¹ = y := by
      rw [hcy]
      simp only [c]
      group
    rw [this]
    obtain ⟨e'', -, rfl⟩ := Finset.mem_image.1 hy
    exact h.φN _

def Cov (N : Subgroup G) (w : ℕ → G) (A : Finset ℕ) : Set G :=
  {y | ∃ D ∈ A, ∃ a ∈ N, ∃ b ∈ N, y = a * w D * b}

theorem cov_mul_N {y n : G} (hy : y ∈ Cov N w A) (hn : n ∈ N) : y * n ∈ Cov N w A := by
  obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hy
  exact ⟨D, hD, a, ha, b * n, N.mul_mem hb hn, by group⟩

theorem cov_mul_u (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) {y : G}
    (hy : y ∈ Cov N w A) : y * u ∈ Cov N w A := by
  obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hy
  obtain ⟨m, rfl⟩ := h.Nφ b hb
  obtain ⟨-, hdec⟩ := decomp h
  obtain ⟨e, he, j, hj, hm⟩ := hdec m⁻¹
  have hs : act θ (((σ e)⁻¹ : M) : K) = θ := by
    have := h.orb.stab e he
    calc act θ (((σ e)⁻¹ : M) : K) = act (act θ (σ e : K)) (((σ e)⁻¹ : M) : K) := by rw [this]
      _ = θ := by rw [h.orb.act_mul]; simp [h.orb.act_one]
  have hm' : m = (g j)⁻¹ * (σ e)⁻¹ := by
    rw [← inv_inv m, hm, mul_inv_rev]
  have hn1 := (conj_stab h _ hs).1
  have key : a * w D * φ m * u =
      a * (w D * ((φ (g j))⁻¹ * u * φ (g j))) * ((φ (g j))⁻¹ * (u⁻¹ * φ ((σ e)⁻¹) * u)) := by
    rw [hm', map_mul, map_inv]
    group
  rw [key]
  rcases h.cover D hD j hj with ⟨D', hD', π, hrel⟩ | ⟨D', hD', j', hj', π, hact, hrel⟩
  ·
    refine ⟨D', hD', a * (w D * ((φ (g j))⁻¹ * u * φ (g j)) * (w D' * φ π)⁻¹),
      N.mul_mem ha hrel, φ π * ((φ (g j))⁻¹ * (u⁻¹ * φ ((σ e)⁻¹) * u)), ?_, by group⟩
    exact N.mul_mem (h.φN π) (N.mul_mem (N.inv_mem (h.φN _)) hn1)
  ·
    have hs' : act θ (((g j) * π * (g j')⁻¹ : M) : K) = θ := by
      have h1 := h.orb.orbit j hj
      have h2 := h.orb.orbit j' hj'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h.orb.act_mul, ← h.orb.act_mul, h1, hact, ← h2, h.orb.act_mul]
      simp [h.orb.act_one]
    have hn2 := (conj_stab h _ (show act θ ((((g j) * π * (g j')⁻¹)⁻¹ : M) : K) = θ by
      have := hs'
      calc act θ ((((g j) * π * (g j')⁻¹)⁻¹ : M) : K) =
          act (act θ (((g j) * π * (g j')⁻¹ : M) : K)) ((((g j) * π * (g j')⁻¹)⁻¹ : M) : K) := by
            rw [this]
        _ = θ := by rw [h.orb.act_mul]; simp [h.orb.act_one])).2
    obtain ⟨mW, hW⟩ := h.usq
    have hrel' : w D * ((φ (g j))⁻¹ * u * φ (g j)) = (w D' * ((φ (g j'))⁻¹ * u * φ (g j')) *
        (w D * φ π)⁻¹)⁻¹ * w D' * ((φ (g j'))⁻¹ * (u * φ (((g j) * π * (g j')⁻¹)⁻¹) * u⁻¹) *
          φ mW * φ (g j)) := by
      rw [← hW, map_inv, map_mul, map_mul, map_inv]
      group
    rw [hrel']
    refine ⟨D', hD', a * (w D' * ((φ (g j'))⁻¹ * u * φ (g j')) * (w D * φ π)⁻¹)⁻¹,
      N.mul_mem ha (N.inv_mem hrel),
      (φ (g j'))⁻¹ * (u * φ (((g j) * π * (g j')⁻¹)⁻¹) * u⁻¹) * φ mW * φ (g j) *
        ((φ (g j))⁻¹ * (u⁻¹ * φ ((σ e)⁻¹) * u)), ?_, by group⟩
    exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem (h.φN _)) hn2) (h.φN _)) (h.φN _))
      (N.mul_mem (N.inv_mem (h.φN _)) hn1)

theorem cov_finite (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) : (Cov N w A).Finite := by
  have _ := (fin_N h).1
  have hNf : (N : Set G).Finite := Set.toFinite _
  have : Cov N w A ⊆ (fun q : ℕ × G × G => q.2.1 * w q.1 * q.2.2) ''
      ((A : Set ℕ) ×ˢ ((N : Set G) ×ˢ (N : Set G))) := by
    rintro _ ⟨D, hD, a, ha, b, hb, rfl⟩
    exact ⟨(D, a, b), ⟨hD, ha, hb⟩, rfl⟩
  exact Set.Finite.subset (Set.Finite.image _ (A.finite_toSet.prod (hNf.prod hNf))) this

theorem cov_mul_uinv (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) {y : G}
    (hy : y ∈ Cov N w A) : y * u⁻¹ ∈ Cov N w A := by
  classical
  let T := (cov_finite h).toFinset
  obtain ⟨z, hz, hzy⟩ := Finset.surj_on_of_inj_on_of_card_le (s := T) (t := T) (fun z _ => z * u)
    (fun z hz => (cov_finite h).mem_toFinset.2 (cov_mul_u h ((cov_finite h).mem_toFinset.1 hz)))
    (fun a b _ _ hab => mul_right_cancel hab) (le_refl _) y ((cov_finite h).mem_toFinset.2 hy)
  rw [hzy, mul_inv_cancel_right]
  exact (cov_finite h).mem_toFinset.1 hz

theorem dceTw_bound (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) (X : Set G)
    (hX : ∀ x ∈ X, x ∈ N ∨ x = u ∨ x = u⁻¹) :
    Finite (Subgroup.closure X) ∧
      Nat.card (Subgroup.closure X) ≤ NORD * (1 + ∑ D ∈ A.erase 0, NORD / mD D) := by
  classical
  obtain ⟨hNfin, hNcard⟩ := fin_N h
  obtain ⟨hMcard, -⟩ := decomp h
  have _ := h.orb.finM
  have hsub : ∀ x ∈ Subgroup.closure X, x ∈ Cov N w A := by
    intro x hx
    induction hx using Subgroup.closure_induction_right with
    | one => exact ⟨0, h.zero_mem, 1, N.one_mem, 1, N.one_mem, by rw [h.w_zero]; group⟩
    | mul_right x _ y hy ih =>
      rcases hX y hy with hy | rfl | rfl
      · exact cov_mul_N ih hy
      · exact cov_mul_u h ih
      · exact cov_mul_uinv h ih
    | mul_inv_cancel x _ y hy ih =>
      rcases hX y hy with hy | rfl | rfl
      · exact cov_mul_N ih (N.inv_mem hy)
      · exact cov_mul_uinv h ih
      · rw [inv_inv]
        exact cov_mul_u h ih
  let bnd : ℕ → ℕ := fun D => if D = 0 then 1 else NORD / mD D
  have hrep : ∀ D ∈ A, ∃ R : Finset G, R.card ≤ bnd D ∧
      ∀ a ∈ N, ∀ b ∈ N, ∃ a' ∈ N, ∃ r ∈ R, a * w D * b = a' * w D * r := by
    intro D hD
    by_cases hD0 : D = 0
    · subst hD0
      obtain ⟨R, hR, -, hcov⟩ := CFSG.Certificates.Co1D.dcoset_reps N (w 0) ⊤
        (fun k _ => by rw [h.w_zero, one_mul, inv_one, mul_one]; exact k.2)
      refine ⟨R, ?_, hcov⟩
      simp only [bnd, ite_true]
      rwa [Subgroup.index_top] at hR
    · let H : Subgroup N :=
        { carrier := {n | w D * (n : G) * (w D)⁻¹ ∈ N}
          one_mem' := by simp [N.one_mem]
          mul_mem' := fun {a b} ha hb => by
            have e : w D * ((a * b : N) : G) * (w D)⁻¹ =
                (w D * (a : G) * (w D)⁻¹) * (w D * (b : G) * (w D)⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
            simp only [Set.mem_ofPred_eq] at ha hb ⊢
            rw [e]
            exact N.mul_mem ha hb
          inv_mem' := fun {a} ha => by
            have e : w D * ((a⁻¹ : N) : G) * (w D)⁻¹ = (w D * (a : G) * (w D)⁻¹)⁻¹ := by
              simp only [Subgroup.coe_inv]
              group
            simp only [Set.mem_ofPred_eq] at ha ⊢
            rw [e]
            exact N.inv_mem ha }
      obtain ⟨R, hR, -, hcov⟩ := CFSG.Certificates.Co1D.dcoset_reps N (w D) H (fun k hk => hk)
      refine ⟨R, hR.trans ?_, hcov⟩
      simp only [bnd, hD0, ite_false]
      let φ' : M →* N := φ.codRestrict N h.φN
      have hφ' : Function.Surjective φ' := by
        rintro ⟨n, hn⟩
        obtain ⟨m, rfl⟩ := h.Nφ n hn
        exact ⟨m, rfl⟩
      rw [← Subgroup.index_comap_of_surjective (H := H) hφ']
      have hmul := Subgroup.card_mul_index (H.comap φ')
      rw [hMcard] at hmul
      have hpos : 0 < Nat.card (H.comap φ') := Nat.card_pos
      have hcomap : mD D ≤ Nat.card (H.comap φ') := by
        rcases h.stabD D hD hD0 with h1 | ⟨E, hEinj, hE⟩
        · rw [h1]
          exact hpos
        · have hmem : ∀ k < mD D, E k ∈ H.comap φ' := fun k hk => hE k hk
          let E' : Fin (mD D) → H.comap φ' := fun k => ⟨E k, hmem k k.2⟩
          have hinj : Function.Injective E' := by
            intro k k' hkk
            exact Fin.ext (hEinj k k.2 k' k'.2 (congrArg Subtype.val hkk))
          have := Nat.card_le_card_of_injective E' hinj
          simpa using this
      rw [← hmul]
      calc (H.comap φ').index = Nat.card (H.comap φ') * (H.comap φ').index / Nat.card (H.comap φ') := by
            rw [Nat.mul_div_cancel_left _ hpos]
        _ ≤ Nat.card (H.comap φ') * (H.comap φ').index / mD D := by
            apply Nat.div_le_div_left hcomap
            rcases h.stabD D hD hD0 with h1 | -
            · rw [h1]; exact Nat.one_pos
            · rcases Nat.eq_zero_or_pos (mD D) with h0 | h0
              · exfalso
                have := h.mD_dvd D hD hD0
                rw [h0, Nat.zero_dvd] at this
                rw [this] at hMcard
                exact absurd hMcard (Nat.card_pos (α := M)).ne'
              · exact h0
        _ = _ := rfl
  choose! R hRcard hRcov using hrep
  obtain ⟨hfin, hcard⟩ := CFSG.Certificates.Co1D.card_cover N A w R (Subgroup.closure X) (by
    intro x hx
    obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hsub x hx
    obtain ⟨a', ha', r, hr, e⟩ := hRcov D hD a ha b hb
    exact ⟨D, hD, a', ha', r, hr, e⟩)
  refine ⟨hfin, hcard.trans ?_⟩
  calc ∑ D ∈ A, Nat.card N * (R D).card ≤ ∑ D ∈ A, NORD * bnd D :=
        Finset.sum_le_sum fun D hD => Nat.mul_le_mul (hNcard.trans h.orb.cardM) (hRcard D hD)
    _ = NORD * ∑ D ∈ A, bnd D := by rw [Finset.mul_sum]
    _ = NORD * (1 + ∑ D ∈ A.erase 0, NORD / mD D) := by
        rw [← Finset.add_sum_erase A bnd h.zero_mem]
        congr 2
        apply Finset.sum_congr rfl
        intro D hD
        simp only [bnd, Finset.ne_of_mem_erase hD, ite_false]

theorem lift_hom {K : Type} [Group K] (R : Set (FreeGroup ℕ)) (S : Set ℕ) (NORD : ℕ)
    (hN : ∀ (H : Type) [Group H] (y : ℕ → H), (∀ r ∈ R, FreeGroup.lift y r = 1) →
      Finite (Subgroup.closure (y '' S)) ∧ Nat.card (Subgroup.closure (y '' S)) ≤ NORD)
    (L : ℕ → K) (hL : ∀ r ∈ R, FreeGroup.lift L r = 1)
    (hM : NORD ≤ Nat.card (Subgroup.closure (L '' S)))
    (x : ℕ → G) (hx : ∀ r ∈ R, FreeGroup.lift x r = 1) :
    ∃ φ : Subgroup.closure (L '' S) →* G,
      (∀ c (hc : c ∈ S), φ ⟨L c, Subgroup.subset_closure ⟨c, hc, rfl⟩⟩ = x c) ∧
      (∀ m, φ m ∈ Subgroup.closure (x '' S)) ∧ ∀ n ∈ Subgroup.closure (x '' S), ∃ m, φ m = n := by
  classical
  have hrel : ∀ r ∈ R, FreeGroup.lift (PresentedGroup.of (rels := R)) r = 1 := by
    intro r hr
    have e : FreeGroup.lift (PresentedGroup.of (rels := R)) = PresentedGroup.mk R :=
      FreeGroup.ext_hom _ _ (fun a => by rw [FreeGroup.lift_apply_of]; rfl)
    rw [e]
    exact PresentedGroup.one_of_mem hr
  set P₀ := Subgroup.closure ((PresentedGroup.of (rels := R)) '' S)
  obtain ⟨hP₀f, hP₀c⟩ := hN (PresentedGroup R) PresentedGroup.of hrel
  let ψ := PresentedGroup.toGroup hL
  let χ := PresentedGroup.toGroup hx
  have hψ : P₀.map ψ = Subgroup.closure (L '' S) := by
    rw [MonoidHom.map_closure, ← Set.image_comp]
    congr 1
    apply Set.image_congr
    intro c _
    exact PresentedGroup.toGroup.of hL
  have hχ : P₀.map χ = Subgroup.closure (x '' S) := by
    rw [MonoidHom.map_closure, ← Set.image_comp]
    congr 1
    apply Set.image_congr
    intro c _
    exact PresentedGroup.toGroup.of hx
  let ψ₀ : P₀ →* Subgroup.closure (L '' S) :=
    { toFun := fun p => ⟨ψ p, by rw [← hψ]; exact Subgroup.mem_map_of_mem ψ p.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hψ₀s : Function.Surjective ψ₀ := by
    rintro ⟨k, hk⟩
    rw [← hψ] at hk
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨p, hp⟩, rfl⟩
  have hψ₀b : Function.Bijective ψ₀ := hψ₀s.bijective_of_nat_card_le (hP₀c.trans hM)
  let e := MulEquiv.ofBijective ψ₀ hψ₀b
  let χ₀ : P₀ →* G := χ.comp P₀.subtype
  refine ⟨χ₀.comp e.symm.toMonoidHom, fun c hc => ?_, fun m => ?_, fun n hn => ?_⟩
  · have hpc : PresentedGroup.of c ∈ P₀ := Subgroup.subset_closure ⟨c, hc, rfl⟩
    have he : e ⟨PresentedGroup.of c, hpc⟩ = ⟨L c, Subgroup.subset_closure ⟨c, hc, rfl⟩⟩ := by
      apply Subtype.ext
      exact PresentedGroup.toGroup.of hL
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he, MulEquiv.symm_apply_apply]
    exact PresentedGroup.toGroup.of hx
  · rw [← hχ]
    exact Subgroup.mem_map.2 ⟨_, (e.symm m).2, rfl⟩
  · rw [← hχ] at hn
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hn
    refine ⟨e ⟨p, hp⟩, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl

end CFSG.Certificates.DceTw

end
