module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCyc

open Equiv Equiv.Perm Subgroup CFSG
open scoped Nat commutatorElement

theorem perfect_le_of_two {G : Type*} [Group G] {I K : Subgroup G} (hI : ⁅I, I⁆ = I)
    (hK : ∀ g ∈ I, ∀ h ∈ I, g ∉ K → h ∉ K → g * h ∈ K) : I ≤ K := by
  have hinv : ∀ g, g ∉ K → g⁻¹ ∉ K := fun g hg hm => hg (by simpa using K.inv_mem hm)
  rw [← hI, Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  by_cases hgK : g ∈ K <;> by_cases hhK : h ∈ K
  · exact K.mul_mem (K.mul_mem (K.mul_mem hgK hhK) (K.inv_mem hgK)) (K.inv_mem hhK)
  · have h1 : g * h * g⁻¹ ∉ K := fun hm => hhK (by
      have := K.mul_mem (K.mul_mem (K.inv_mem hgK) hm) hgK
      simpa [mul_assoc] using this)
    exact hK _ (I.mul_mem (I.mul_mem hg hh) (I.inv_mem hg)) _ (I.inv_mem hh) h1 (hinv h hhK)
  · have h1 : g * h ∉ K := fun hm => hgK (by simpa using K.mul_mem hm (K.inv_mem hhK))
    exact K.mul_mem (hK _ (I.mul_mem hg hh) _ (I.inv_mem hg) h1 (hinv g hgK)) (K.inv_mem hhK)
  · have h1 := hK g hg h hh hgK hhK
    have h2 := hK _ (I.inv_mem hg) _ (I.inv_mem hh) (hinv g hgK) (hinv h hhK)
    rw [mul_assoc (g * h)]
    exact K.mul_mem h1 h2

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def setwiseStab (A : Finset α) : Subgroup (Perm α) where
  carrier := {g | ∀ x, g x ∈ A ↔ x ∈ A}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {g h} hg hh x => by rw [Perm.mul_apply, hg, hh]
  inv_mem' := fun {g} hg x => by
    rw [← hg (g⁻¹ x), ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

omit [Fintype α] in
theorem mem_stabSet_of_maps {g : Perm α} {A : Finset α} (h : ∀ x ∈ A, g x ∈ A) :
    g ∈ setwiseStab A := by
  have himg : A.image g = A := Finset.eq_of_subset_of_card_le
    (fun y hy => by obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact h x hx)
    (by rw [Finset.card_image_of_injective _ g.injective])
  intro x
  refine ⟨fun hx => ?_, h x⟩
  rw [← himg] at hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
  rwa [← g.injective hyx]

@[expose] def pointwiseFix (B : Finset α) : Subgroup (Perm α) where
  carrier := {g | ∀ x ∈ B, g x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {g h} hg hh x hx => by rw [Perm.mul_apply, hh x hx, hg x hx]
  inv_mem' := fun {g} hg x hx => by rw [Perm.inv_eq_iff_eq, hg x hx]

theorem card_dvd_of_fix (B : Finset α) {I : Subgroup (Perm α)} (hI : I ≤ pointwiseFix B) :
    Nat.card ↥I ∣ (Bᶜ.card)! := by
  have hpres : ∀ g ∈ I, ∀ x, g x ∈ Bᶜ ↔ x ∈ Bᶜ := by
    intro g hg x
    simp only [Finset.mem_compl]
    constructor
    · intro h hx
      exact h (by rw [hI hg x hx]; exact hx)
    · intro h hgx
      exact h (g.injective (hI hg _ hgx) ▸ hgx)
  let ψ : ↥I →* Perm {x // x ∈ Bᶜ} :=
    { toFun := fun g => (g : Perm α).subtypePerm (hpres g g.2)
      map_one' := by ext; rfl
      map_mul' := fun g h => by ext; rfl }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ B
    · rw [hI g.2 x hx, hI h.2 x hx]
    · have := congrArg (fun π : Perm {x // x ∈ Bᶜ} => (π ⟨x, Finset.mem_compl.mpr hx⟩ : α)) hgh
      simpa [ψ] using this
  have := Subgroup.card_dvd_of_injective ψ hψ
  rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := {x // x ∈ Bᶜ}), Fintype.card_coe] at this

theorem eq_one_of_fix {g : Perm α} {B : Finset α} (hB : Bᶜ.card ≤ 1)
    (hg : ∀ x ∈ B, g x = x) : g = 1 := by
  ext x
  rw [Perm.one_apply]
  by_contra hx
  have h1 : x ∈ Bᶜ := Finset.mem_compl.mpr fun h => hx (hg x h)
  have h2 : g x ∈ Bᶜ := Finset.mem_compl.mpr fun h => hx (g.injective (hg _ h))
  exact hx (Finset.card_le_one.mp hB _ h2 _ h1)

theorem isCycle_of_orderOf {σ : Perm α} {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p)
    (h : σ.support.card < 2 * p) : σ.IsCycle ∧ σ.support.card = p := by
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := σ) (by rw [hσ]; exact hp)
  rw [hσ] at hm
  have hs : σ.support.card = (m + 1) * p := by
    rw [← sum_cycleType, hm, Multiset.sum_replicate, smul_eq_mul]
  have hm0 : m = 0 := by
    by_contra hm0
    have : 2 * p ≤ (m + 1) * p := Nat.mul_le_mul_right p (by omega)
    omega
  subst hm0
  exact ⟨card_cycleType_eq_one.mp (by rw [hm, Multiset.card_replicate]),
    by rw [hs, zero_add, one_mul]⟩

theorem comm_of_not_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (hX : IsPGroup p ↥X) (h : ¬ p ^ 3 ∣ Nat.card G) :
    ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
  have hk2 : k ≤ 2 := by
    by_contra hk2
    exact h ((Nat.pow_dvd_pow p (by omega)).trans (hk ▸ Subgroup.card_subgroup_dvd_card X))
  intro x hx y hy
  suffices hc : (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ from congrArg Subtype.val hc
  interval_cases k
  · have : Subsingleton ↥X := (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
    exact Subsingleton.elim _ _
  · have : IsCyclic ↥X := isCyclic_of_prime_card (by rw [hk, pow_one])
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥X)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    rw [← hi, ← hj]
    exact ((Commute.refl g).zpow_zpow i j).eq
  · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk).is_comm.comm _ _

theorem conj_eq_or_inv {G : Type*} [Group G] {σ u : G} (hσ : orderOf σ = 5) (hu : u * u = 1)
    (h : u * σ * u⁻¹ ∈ zpowers σ) : u * σ * u⁻¹ = σ ∨ u * σ * u⁻¹ = σ⁻¹ := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  have huinv : u⁻¹ = u := (inv_eq_of_mul_eq_one_right hu)
  have hk2 : σ ^ (k * k) = σ ^ (1 : ℤ) := by
    have e1 : u * σ ^ k * u⁻¹ = (u * σ * u⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [zpow_one, zpow_mul, hk, ← e1, hk, huinv]
    calc u * (u * σ * u) * u = (u * u) * σ * (u * u) := by group
      _ = σ := by rw [hu, one_mul, mul_one]
  rw [zpow_eq_zpow_iff_modEq, hσ] at hk2
  have hres : k % 5 = 1 ∨ k % 5 = 4 := by
    have h1 := Int.mul_emod k k 5
    have h0 : 0 ≤ k % 5 := Int.emod_nonneg k (by norm_num)
    have h5 : k % 5 < 5 := Int.emod_lt_of_pos k (by norm_num)
    unfold Int.ModEq at hk2
    push_cast at hk2
    generalize k % 5 = r at h1 h0 h5 ⊢
    interval_cases r <;> omega
  have hmod : σ ^ k = σ ^ (k % 5) := by
    rw [← zpow_mod_orderOf, hσ]
    norm_num
  rcases hres with h1 | h1
  · left
    rw [← hk, hmod, h1, zpow_one]
  · right
    rw [← hk, hmod, h1]
    have : σ ^ (5 : ℤ) = 1 := by
      rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hσ, pow_orderOf_eq_one]
    calc σ ^ (4 : ℤ) = σ ^ (5 : ℤ) * σ⁻¹ := by group
      _ = σ⁻¹ := by rw [this, one_mul]

theorem exists_two_of_four {G : Type} [Group G] {U : Subgroup G} (hU : IVK.IsFourSubgroup U) :
    ∃ u ∈ U, ∃ v ∈ U, u ≠ 1 ∧ v ≠ 1 ∧ v ≠ u := by
  have h4 := hU.2
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    push Not at h
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr h
    rw [this, card_bot] at h4
    omega
  obtain ⟨v, hvU, hv1, hvu⟩ : ∃ v ∈ U, v ≠ 1 ∧ v ≠ u := by
    by_contra h
    push Not at h
    have hsub : (U : Set G) ⊆ {1, u} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hu1.symm, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at this
    omega
  exact ⟨u, huU, v, hvU, hu1, hv1, hvu⟩

theorem exists_commute_of_four {G : Type} [Group G] {U : Subgroup G}
    (hU : IVK.IsFourSubgroup U) {σ : G} (hσ : orderOf σ = 5)
    (h : ∀ u ∈ U, u * σ * u⁻¹ ∈ zpowers σ) : ∃ u ∈ U, u ≠ 1 ∧ Commute u σ := by
  have := hU.1
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
  have hcomm_of : ∀ u, u * σ * u⁻¹ = σ → Commute u σ := fun u hu =>
    show u * σ = σ * u by
      calc u * σ = (u * σ * u⁻¹) * u := by group
        _ = σ * u := by rw [hu]
  obtain ⟨u, huU, v, hvU, hu1, hv1, hvu⟩ := exists_two_of_four hU
  rcases conj_eq_or_inv hσ (hsq u huU) (h u huU) with hu | hu
  · exact ⟨u, huU, hu1, hcomm_of u hu⟩
  rcases conj_eq_or_inv hσ (hsq v hvU) (h v hvU) with hv | hv
  · exact ⟨v, hvU, hv1, hcomm_of v hv⟩
  refine ⟨u * v, U.mul_mem huU hvU, fun h1 => hvu ?_, hcomm_of _ ?_⟩
  · have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u huU)
    rw [← huinv]
    exact eq_inv_of_mul_eq_one_right h1
  · calc u * v * σ * (u * v)⁻¹ = u * (v * σ * v⁻¹) * u⁻¹ := by group
      _ = (u * σ * u⁻¹)⁻¹ := by rw [hv]; group
      _ = σ := by rw [hu, inv_inv]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCyc
