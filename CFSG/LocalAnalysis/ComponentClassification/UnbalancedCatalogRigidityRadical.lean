module

public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Subgroup CFSG

variable {C : Type*} [Group C]

@[expose] def setStabilizer (U : Subgroup C) : Subgroup (MulAut C) where
  carrier := {α | ∀ x, α x ∈ U ↔ x ∈ U}
  mul_mem' {α β} hα hβ x := by
    change α (β x) ∈ U ↔ x ∈ U
    rw [hα, hβ]
  one_mem' x := Iff.rfl
  inv_mem' {α} hα x := by
    rw [← hα, MulAut.apply_inv_self]

theorem mem_setStabilizer {U : Subgroup C} {α : MulAut C} :
    α ∈ setStabilizer U ↔ ∀ x, α x ∈ U ↔ x ∈ U :=
  Iff.rfl

theorem mul_conj_mul_inv (α : MulAut C) (c : C) :
    α * MulAut.conj c * α⁻¹ = MulAut.conj (α c) := by
  ext x
  simp [MulAut.conj_apply]

theorem conj_injective (hZ : center C = ⊥) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [← hZ, mem_center_iff]
  intro x
  have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hc) x
  rw [MulAut.conj_apply, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

variable [Finite C]

theorem full_inner_p_centralizer_core_from_equivariant_radical (hZ : center C = ⊥)
    (p : ℕ) [Fact p.Prime] {A A₀ : Subgroup (MulAut C)} (hA₀ : (A₀.subgroupOf A).Normal)
    (hιA₀ : (MulAut.conj : C →* MulAut C).range ≤ A₀)
    {e : ℕ} (hindex : A₀.relIndex A = p ^ e) {t : C} (ht : orderOf t = p)
    {U : Subgroup C} (hU : IsPGroup p U)
    (hpoint : ∀ α ∈ A₀, (∀ u ∈ U, α u = u) → α ∈ U.map (MulAut.conj : C →* MulAut C))
    (hset : ∀ α ∈ A₀, α * MulAut.conj t = MulAut.conj t * α → ∀ u ∈ U, α u ∈ U)
    (H : Subgroup (MulAut C)) (hιH : (MulAut.conj : C →* MulAut C).range ≤ H) (hHA : H ≤ A) :
    pPrimeCore p ↥(H ⊓ centralizer {MulAut.conj t}) = ⊥ := by
  classical
  have hιinj : Function.Injective (MulAut.conj : C →* MulAut C) := conj_injective hZ
  set CH := H ⊓ centralizer ({MulAut.conj t} : Set (MulAut C)) with hCH
  set R := pPrimeCore p ↥CH with hR
  have hRcop : Nat.Coprime p (Nat.card R) := pPrimeCore_coprime_card
  have hRA₀ : ∀ x ∈ R, (x : MulAut C) ∈ A₀ := by
    intro x hx
    have hxA : (x : MulAut C) ∈ A := hHA (mem_inf.mp x.2).1
    have h1 : orderOf (QuotientGroup.mk' (A₀.subgroupOf A) ⟨x, hxA⟩) ∣ p ^ e := by
      rw [← hindex]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk' (A₀.subgroupOf A) ⟨x, hxA⟩) ∣ Nat.card R := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard R hx
    have h3 := Nat.Coprime.eq_one_of_dvd ((hRcop.pow_left e).coprime_dvd_left h1) h2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf] at h3
    exact h3
  have hstab : ∀ α ∈ A₀, α * MulAut.conj t = MulAut.conj t * α → α ∈ setStabilizer U := by
    intro α hα hcomm x
    have hcomm' : α⁻¹ * MulAut.conj t = MulAut.conj t * α⁻¹ :=
      (show Commute α (MulAut.conj t) from hcomm).inv_left
    constructor
    · intro hx
      simpa using hset α⁻¹ (A₀.inv_mem hα) hcomm' _ hx
    · exact hset α hα hcomm x
  set H₀ := H ⊓ A₀ with hH₀
  have hιH₀ : ∀ c : C, MulAut.conj c ∈ H₀ := fun c =>
    mem_inf.mpr ⟨hιH ⟨c, rfl⟩, hιA₀ ⟨c, rfl⟩⟩
  set it : H₀ := ⟨MulAut.conj t, hιH₀ t⟩ with hit
  set P : Subgroup H₀ := (setStabilizer U).subgroupOf H₀ with hP
  set W : Subgroup H₀ := (U.map (MulAut.conj : C →* MulAut C)).subgroupOf H₀ with hW
  set Q : Subgroup H₀ := zpowers it with hQ
  set L : Subgroup H₀ := centralizer (Q : Set H₀) with hL
  have hWP : W ≤ P := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ := mem_map.mp (mem_subgroupOf.mp hw)
    rw [mem_subgroupOf, ← hwu]
    intro x
    rw [MulAut.conj_apply]
    exact (U.mul_mem_cancel_right (U.inv_mem hu)).trans (U.mul_mem_cancel_left hu)
  have hWn : (W.subgroupOf P).Normal := by
    refine ⟨fun w hw g => ?_⟩
    obtain ⟨u, hu, hwu⟩ := mem_map.mp (mem_subgroupOf.mp (mem_subgroupOf.mp hw))
    refine mem_subgroupOf.mpr (mem_subgroupOf.mpr (mem_map.mpr ⟨(g : MulAut C) u,
      ((mem_subgroupOf.mp g.2) u).mpr hu, ?_⟩))
    simp only [coe_mul, coe_inv, ← hwu]
    exact (mul_conj_mul_inv _ _).symm
  have hWp : IsPGroup p W :=
    (hU.map _).comap_of_injective H₀.subtype H₀.subtype_injective
  have hCW : centralizer (W : Set H₀) ⊓ P ≤ W := by
    intro g hg
    obtain ⟨hgc, -⟩ := mem_inf.mp hg
    refine mem_subgroupOf.mpr (hpoint _ (mem_inf.mp g.2).2 fun u hu => ?_)
    have hwW : (⟨MulAut.conj u, hιH₀ u⟩ : H₀) ∈ W := mem_subgroupOf.mpr ⟨u, hu, rfl⟩
    have hcomm : MulAut.conj u * (g : MulAut C) = (g : MulAut C) * MulAut.conj u :=
      congrArg Subtype.val (mem_centralizer_iff.mp hgc _ hwW)
    apply hιinj
    rw [← mul_conj_mul_inv, ← hcomm, mul_inv_cancel_right]
  have hQP : Q ≤ P := by
    rw [hQ, zpowers_le]
    exact mem_subgroupOf.mpr (hstab _ (hιA₀ ⟨t, rfl⟩) rfl)
  have hQp : IsPGroup p Q := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, hit, Subgroup.orderOf_mk, orderOf_injective _ hιinj, ht]
  have hLP : L ≤ P := by
    intro g hg
    have hcomm : (g : MulAut C) * MulAut.conj t = MulAut.conj t * g :=
      (congrArg Subtype.val (mem_centralizer_iff.mp hg it (mem_zpowers it))).symm
    exact mem_subgroupOf.mpr (hstab _ (mem_inf.mp g.2).2 hcomm)
  obtain ⟨-, -, hkill, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.parabolic_containing_subgroup_local_characteristic_transfer
      hWP hWn hWp hCW hQP hQp (Or.inr rfl) hLP
  set R₁ : Subgroup (MulAut C) := R.map CH.subtype with hR₁def
  have hR₁ : ∀ r ∈ R₁, r ∈ H₀ ∧ r ∈ CH := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_inf.mpr ⟨(mem_inf.mp x.2).1, hRA₀ x hx⟩, x.2⟩
  have hR₁H₀ : R₁ ≤ H₀ := fun r hr => (hR₁ r hr).1
  have hXL : R₁.subgroupOf H₀ ≤ L := by
    intro g hg
    have hgC : (g : MulAut C) ∈ centralizer ({MulAut.conj t} : Set (MulAut C)) :=
      (mem_inf.mp (hR₁ _ (mem_subgroupOf.mp hg)).2).2
    have hcomm : it * g = g * it :=
      Subtype.ext (mem_centralizer_iff.mp hgC _ rfl)
    rw [hL, mem_centralizer_iff]
    intro q hq
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hq
    exact ((Commute.zpow_left hcomm k))
  set R₂ : Subgroup L := (R₁.subgroupOf H₀).subgroupOf L with hR₂
  have hR₂n : R₂.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨x, hx, hxy⟩ := mem_map.mp (mem_subgroupOf.mp (mem_subgroupOf.mp hy))
    have hgC : ((g : H₀) : MulAut C) ∈ CH := by
      refine mem_inf.mpr ⟨(mem_inf.mp (g : H₀).2).1, ?_⟩
      rw [mem_centralizer_iff]
      rintro _ rfl
      exact congrArg Subtype.val (mem_centralizer_iff.mp g.2 it (mem_zpowers it))
    have hconj := (pPrimeCore_normal (p := p) (G := ↥CH)).conj_mem x hx ⟨_, hgC⟩
    refine mem_subgroupOf.mpr (mem_subgroupOf.mpr (mem_map.mpr ⟨_, hconj, ?_⟩))
    simp only [coe_mul, coe_inv, CH.subtype_apply] at hxy ⊢
    rw [hxy]
  have hR₂card : Nat.card R₂ = Nat.card R := by
    rw [hR₂, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₁H₀).toEquiv, hR₁def,
      Subgroup.card_map_of_injective CH.subtype_injective]
  have hR₂p : ¬ p ∣ Nat.card R₂ := by
    rw [hR₂card]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hRcop
  have hR₂bot := hkill R₂ hR₂n hR₂p
  rw [eq_bot_iff]
  intro x hx
  have hxR₁ : (x : MulAut C) ∈ R₁ := mem_map_of_mem _ hx
  have hy : (⟨⟨x, hR₁H₀ hxR₁⟩, hXL (mem_subgroupOf.mpr hxR₁)⟩ : L) ∈ R₂ :=
    mem_subgroupOf.mpr (mem_subgroupOf.mpr hxR₁)
  rw [hR₂bot, mem_bot] at hy
  have h1 := congrArg (fun y : L => ((y : H₀) : MulAut C)) hy
  simp only [OneMemClass.coe_one] at h1
  exact mem_bot.mpr (Subtype.ext h1)

end CFSG.ComponentClassification.UnbalancedCatalog
