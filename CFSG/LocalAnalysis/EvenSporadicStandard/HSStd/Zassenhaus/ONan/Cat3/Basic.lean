module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.C0Facts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Open

@[expose] def CentHyp (L : Type*) [Group L] : Prop :=
  ∀ x : L, orderOf x = 3 → ThreeA5OrS5 ↥(centralizer ({x} : Set L))

namespace CentHyp

variable {L : Type*} [Group L]

theorem of_mulEquiv {M : Type*} [Group M] (e : L ≃* M) (h : CentHyp M) : CentHyp L := by
  intro x hx
  have hx' : orderOf (e x) = 3 := by rw [e.orderOf_eq, hx]
  have hC := h (e x) hx'
  let F : ↥(centralizer ({x} : Set L)) ≃* ↥(centralizer ({e x} : Set M)) :=
    { toFun := fun c => ⟨e c, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa only [map_mul] using
          congrArg e (Subgroup.mem_centralizer_singleton_iff.mp c.2)⟩
      invFun := fun d => ⟨e.symm d, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa only [map_mul, MulEquiv.symm_apply_apply] using
          congrArg e.symm (Subgroup.mem_centralizer_singleton_iff.mp d.2)⟩
      left_inv := fun c => by ext; simp
      right_inv := fun d => by ext; simp
      map_mul' := fun a b => by ext; simp }
  obtain hC | hC := hC
  · obtain ⟨e'⟩ := hC
    exact Or.inl ⟨F.trans e'⟩
  · obtain ⟨e'⟩ := hC
    exact Or.inr ⟨F.trans e'⟩

theorem card_centralizer (h : CentHyp L) {x : L} (hx : orderOf x = 3) :
    Nat.card ↥(centralizer ({x} : Set L)) = 180 ∨
      Nat.card ↥(centralizer ({x} : Set L)) = 360 :=
  (h x hx).card

theorem orderOf_mem (h : CentHyp L) {x y : L} (hx : orderOf x = 3) (hxy : y * x = x * y) :
    orderOf y ∈ ({1, 2, 3, 4, 5, 6, 12, 15} : Finset ℕ) :=
  orderOf_mem_of_commute (h x hx) hxy

theorem card_le (h : CentHyp L) {x : L} (hx : orderOf x = 3) {B : Subgroup L}
    (hBx : ∀ b ∈ B, b * x = x * b) (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 18 :=
  card_le_of_comm (h x hx) hBx hB

theorem exists_five (h : CentHyp L) {x : L} (hx : orderOf x = 3) :
    ∃ y : L, orderOf y = 5 ∧ y * x = x * y :=
  exists_orderOf_eq_five_commute (h x hx)

theorem not_comm (h : CentHyp L) {x : L} (hx : orderOf x = 3) :
    ∃ a b : L, a * x = x * a ∧ b * x = x * b ∧ a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hC : ∀ a ∈ centralizer ({x} : Set L), ∀ b ∈ centralizer ({x} : Set L),
      a * b = b * a :=
    fun a ha b hb => hcon a b (Subgroup.mem_centralizer_singleton_iff.mp ha)
      (Subgroup.mem_centralizer_singleton_iff.mp hb)
  have hCx : ∀ b ∈ centralizer ({x} : Set L), b * x = x * b :=
    fun b hb => Subgroup.mem_centralizer_singleton_iff.mp hb
  have hle := card_le h hx hCx hC
  rcases card_centralizer h hx with hc | hc <;> omega

end CentHyp

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

theorem mk_eq_one_iff (g : H) :
    (QuotientGroup.mk g : StatedProj H) = 1 ↔ (g : GL ι K) ∈ StatedScalars ι K := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem orderOf_mk_eq (g : H) (n : ℕ)
    (hg : ∀ m : ℕ, (g : GL ι K) ^ m ∈ StatedScalars ι K ↔ n ∣ m) :
    orderOf (QuotientGroup.mk g : StatedProj H) = n := by
  have hkey : ∀ m : ℕ, (QuotientGroup.mk g : StatedProj H) ^ m = 1 ↔ n ∣ m := by
    intro m
    rw [← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff (g ^ m)).trans (by rw [Subgroup.coe_pow]; exact hg m)
  have hdvd : ∀ m : ℕ,
      orderOf (QuotientGroup.mk g : StatedProj H) ∣ m ↔ n ∣ m :=
    fun m => (orderOf_dvd_iff_pow_eq_one).trans (hkey m)
  exact Nat.dvd_antisymm ((hdvd n).mpr dvd_rfl)
    ((hdvd (orderOf (QuotientGroup.mk g : StatedProj H))).mp dvd_rfl)

theorem orderOf_mk_eq_prime {p : ℕ} [Fact p.Prime] (g : H)
    (hp : (g : GL ι K) ^ p ∈ StatedScalars ι K) (h1 : (g : GL ι K) ∉ StatedScalars ι K) :
    orderOf (QuotientGroup.mk g : StatedProj H) = p := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff (g ^ p)).mpr (by rw [Subgroup.coe_pow]; exact hp)
  · intro h
    exact h1 ((mk_eq_one_iff g).mp h)

theorem CentHyp.card_le_of_proj (h : CentHyp (StatedProj H)) {x : H}
    (hx : orderOf (QuotientGroup.mk x : StatedProj H) = 3) {A : Subgroup H}
    (hAx : ∀ a ∈ A, a * x = x * a) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAZ : ∀ a ∈ A, (a : GL ι K) ∈ StatedScalars ι K → a = 1) : Nat.card A ≤ 18 := by
  let π : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)
  have hInjOn : Set.InjOn π (A : Set H) := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ A := A.mul_mem (A.inv_mem ha) hb
    have hker : π (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hscal : ((a⁻¹ * b : H) : GL ι K) ∈ StatedScalars ι K :=
      (mk_eq_one_iff (a⁻¹ * b)).mp hker
    exact inv_mul_eq_one.mp (hAZ (a⁻¹ * b) hmem hscal)
  have hcard : Nat.card (A.map π) = Nat.card A :=
    Nat.card_image_of_injOn hInjOn
  rw [← hcard]
  apply CentHyp.card_le h hx
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := hb
    change (QuotientGroup.mk (a * x) : StatedProj H) = QuotientGroup.mk (x * a)
    rw [hAx a ha]
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    change (QuotientGroup.mk (a' * b') : StatedProj H) = QuotientGroup.mk (b' * a')
    rw [hA a' ha' b' hb']

end Proj

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
