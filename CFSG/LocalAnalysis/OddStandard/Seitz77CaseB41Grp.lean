module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Abs
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Solv

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup
open CFSG.RankThreeCoreUniqueness
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem exists_noncomm_of_simple_card_sixty {S : Type*} [Group S] [IsSimpleGroup S]
    (h : Nat.card S = 60) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup S := { ‹Group S› with mul_comm := fun a b => hcon a b }
  have := IsSimpleGroup.prime_card (α := S)
  rw [h] at this
  norm_num at this

theorem isPerfect_of_simple_card_sixty {S : Type*} [Group S] [IsSimpleGroup S]
    (h : Nat.card S = 60) : Group.IsPerfect S := by
  refine Group.isPerfect_def.mpr ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h0 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_simple_card_sixty h
    apply hab
    have hm : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h0, Subgroup.mem_bot] at hm
    exact commutatorElement_eq_one_iff_mul_comm.mp hm
  · exact h1

section Fac

variable {HH Q : Type} [Group HH] [Group Q] (π : HH →* Q)
  (S₁ S₂ : Subgroup Q)

@[expose] def fHhat : Subgroup HH := perfectResidualOf ((S₁ ⊔ S₂).comap π)

@[expose] def fLam₁ : Subgroup HH := fHhat π S₁ S₂ ⊓ S₁.comap π

@[expose] def fLam₂ : Subgroup HH := fHhat π S₁ S₂ ⊓ S₂.comap π

variable {π S₁ S₂}

theorem fHhat_perfect [Finite HH] : ⁅fHhat π S₁ S₂, fHhat π S₁ S₂⁆ = fHhat π S₁ S₂ := prOf_perfect _

theorem sup_perfect (hT : TwoComp Q S₁ S₂) (h₁ : Nat.card S₁ = 60) (h₂ : Nat.card S₂ = 60) :
    ⁅S₁ ⊔ S₂, S₁ ⊔ S₂⁆ = S₁ ⊔ S₂ := by
  have hS₁ := hT.simple₁
  have hS₂ := hT.simple₂
  have p₁ : ⁅S₁, S₁⁆ = S₁ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_simple_card_sixty h₁)
  have p₂ : ⁅S₂, S₂⁆ = S₂ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_simple_card_sixty h₂)
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (sup_le ?_ ?_)
  · have e : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := commutatorElement_def a b
    rw [e]
    exact (S₁ ⊔ S₂).mul_mem ((S₁ ⊔ S₂).mul_mem ((S₁ ⊔ S₂).mul_mem ha hb)
      ((S₁ ⊔ S₂).inv_mem ha)) ((S₁ ⊔ S₂).inv_mem hb)
  · calc S₁ = ⁅S₁, S₁⁆ := p₁.symm
      _ ≤ ⁅S₁ ⊔ S₂, S₁ ⊔ S₂⁆ := commutator_mono le_sup_left le_sup_left
  · calc S₂ = ⁅S₂, S₂⁆ := p₂.symm
      _ ≤ ⁅S₁ ⊔ S₂, S₁ ⊔ S₂⁆ := commutator_mono le_sup_right le_sup_right

theorem map_fHhat [Finite HH] (hπ : Function.Surjective π) (hT : TwoComp Q S₁ S₂)
    (h₁ : Nat.card S₁ = 60) (h₂ : Nat.card S₂ = 60) : (fHhat π S₁ S₂).map π = S₁ ⊔ S₂ := by
  set Y : Subgroup HH := (S₁ ⊔ S₂).comap π with hY
  let f : ↥Y →* ↥(S₁ ⊔ S₂) := (π.comp Y.subtype).codRestrict (S₁ ⊔ S₂) (fun y => y.2)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := hπ (z : Q)
    exact ⟨⟨x, by rw [hY, mem_comap, hx]; exact z.2⟩, Subtype.ext hx⟩
  have : Group.IsPerfect ↥(S₁ ⊔ S₂) := Subgroup.isPerfect_iff.mpr (sup_perfect hT h₁ h₂)
  have h := finite_perfectResidual_surjects_to_perfect_image f hf
  have e : (fHhat π S₁ S₂).map π = ((Helpers.perfectResidual ↥Y).map f).map (S₁ ⊔ S₂).subtype := by
    rw [fHhat, perfectResidualOf, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [e, h, Subgroup.map_top, Subgroup.range_subtype]

structure FacData (π : HH →* Q) (S₁ S₂ : Subgroup Q) : Prop where
  surj : Function.Surjective π
  twoComp : TwoComp Q S₁ S₂
  card₁ : Nat.card S₁ = 60
  card₂ : Nat.card S₂ = 60
  ker : fHhat π S₁ S₂ ⊓ π.ker = ⊥

namespace FacData

variable [Finite HH] (D : FacData π S₁ S₂)

include D

theorem map_Hhat : (fHhat π S₁ S₂).map π = S₁ ⊔ S₂ :=
  map_fHhat D.surj D.twoComp D.card₁ D.card₂

omit [Finite HH] in
theorem inj {x y : HH} (hx : x ∈ fHhat π S₁ S₂) (hy : y ∈ fHhat π S₁ S₂) (h : π x = π y) :
    x = y := by
  have hm : x⁻¹ * y ∈ fHhat π S₁ S₂ ⊓ π.ker :=
    Subgroup.mem_inf.mpr ⟨(fHhat π S₁ S₂).mul_mem ((fHhat π S₁ S₂).inv_mem hx) hy, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]⟩
  rw [D.ker, Subgroup.mem_bot] at hm
  exact (inv_mul_eq_one.mp hm)

theorem pi_mem_sup {x : HH} (hx : x ∈ fHhat π S₁ S₂) : π x ∈ S₁ ⊔ S₂ := by
  have := Subgroup.mem_map_of_mem π hx
  rwa [D.map_Hhat] at this

theorem map_Lam₁ : (fLam₁ π S₁ S₂).map π = S₁ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_inf.mp hx).2
  · intro s hs
    have : s ∈ (fHhat π S₁ S₂).map π := by rw [D.map_Hhat]; exact mem_sup_left hs
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, Subgroup.mem_inf.mpr ⟨hx, hs⟩, rfl⟩

theorem map_Lam₂ : (fLam₂ π S₁ S₂).map π = S₂ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_inf.mp hx).2
  · intro s hs
    have : s ∈ (fHhat π S₁ S₂).map π := by rw [D.map_Hhat]; exact mem_sup_right hs
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, Subgroup.mem_inf.mpr ⟨hx, hs⟩, rfl⟩

noncomputable def lam₁Equiv : ↥(fLam₁ π S₁ S₂) ≃* ↥S₁ :=
  (MonoidHom.ofInjective (f := π.comp (fLam₁ π S₁ S₂).subtype) (fun x y h =>
    Subtype.ext (D.inj (x.2.1) (y.2.1) h))).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact D.map_Lam₁))

noncomputable def lam₂Equiv : ↥(fLam₂ π S₁ S₂) ≃* ↥S₂ :=
  (MonoidHom.ofInjective (f := π.comp (fLam₂ π S₁ S₂).subtype) (fun x y h =>
    Subtype.ext (D.inj (x.2.1) (y.2.1) h))).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact D.map_Lam₂))

theorem Lam₁_simple : IsSimpleGroup ↥(fLam₁ π S₁ S₂) := by
  have := D.twoComp.simple₁
  exact D.lam₁Equiv.isSimpleGroup

theorem Lam₂_simple : IsSimpleGroup ↥(fLam₂ π S₁ S₂) := by
  have := D.twoComp.simple₂
  exact D.lam₂Equiv.isSimpleGroup

theorem Lam₁_card : Nat.card ↥(fLam₁ π S₁ S₂) = 60 :=
  (Nat.card_congr D.lam₁Equiv.toEquiv).trans D.card₁

theorem Lam₂_card : Nat.card ↥(fLam₂ π S₁ S₂) = 60 :=
  (Nat.card_congr D.lam₂Equiv.toEquiv).trans D.card₂

omit [Finite HH] in
theorem Lam_comm {x y : HH} (hx : x ∈ fLam₁ π S₁ S₂) (hy : y ∈ fLam₂ π S₁ S₂) :
    x * y = y * x := by
  refine D.inj (mul_mem hx.1 hy.1) (mul_mem hy.1 hx.1) ?_
  rw [map_mul, map_mul]
  exact D.twoComp.comm _ hx.2 _ hy.2

omit [Finite HH] in
theorem Lam_inf : fLam₁ π S₁ S₂ ⊓ fLam₂ π S₁ S₂ = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
  have h : π x ∈ S₁ ⊓ S₂ :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx₁).2, (Subgroup.mem_inf.mp hx₂).2⟩
  rw [disjoint_iff.mp D.twoComp.disj, Subgroup.mem_bot] at h
  have h2 : x ∈ fHhat π S₁ S₂ ⊓ π.ker :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx₁).1, h⟩
  rw [D.ker] at h2
  exact h2

theorem Lam_sup : fLam₁ π S₁ S₂ ⊔ fLam₂ π S₁ S₂ = fHhat π S₁ S₂ := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
  have hπx : π x ∈ S₁ ⊔ S₂ := D.pi_mem_sup hx
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_forall_comm D.twoComp.comm hπx
  have ha' : a ∈ (fLam₁ π S₁ S₂).map π := by rw [D.map_Lam₁]; exact ha
  have hb' : b ∈ (fLam₂ π S₁ S₂).map π := by rw [D.map_Lam₂]; exact hb
  obtain ⟨x₁, hx₁, rfl⟩ := ha'
  obtain ⟨x₂, hx₂, rfl⟩ := hb'
  have hx₁H : x₁ ∈ fHhat π S₁ S₂ := (Subgroup.mem_inf.mp hx₁).1
  have hx₂H : x₂ ∈ fHhat π S₁ S₂ := (Subgroup.mem_inf.mp hx₂).1
  have : x = x₁ * x₂ :=
    D.inj hx ((fHhat π S₁ S₂).mul_mem hx₁H hx₂H) (by rw [map_mul]; exact hab)
  rw [this]
  exact Subgroup.mul_mem_sup hx₁ hx₂

theorem Lam₁_norm {x : HH} (hx : x ∈ fHhat π S₁ S₂) {y : HH} (hy : y ∈ fLam₁ π S₁ S₂) :
    x * y * x⁻¹ ∈ fLam₁ π S₁ S₂ := by
  obtain ⟨hyH, hyS⟩ := Subgroup.mem_inf.mp hy
  have hπx : π x ∈ layer Q := by rw [← D.twoComp.sup_eq]; exact D.pi_mem_sup hx
  refine Subgroup.mem_inf.mpr ⟨(fHhat π S₁ S₂).mul_mem
    ((fHhat π S₁ S₂).mul_mem hx hyH) ((fHhat π S₁ S₂).inv_mem hx), ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv]
  exact D.twoComp.norm₁ _ hπx _ hyS

theorem Lam₂_norm {x : HH} (hx : x ∈ fHhat π S₁ S₂) {y : HH} (hy : y ∈ fLam₂ π S₁ S₂) :
    x * y * x⁻¹ ∈ fLam₂ π S₁ S₂ := by
  obtain ⟨hyH, hyS⟩ := Subgroup.mem_inf.mp hy
  have hπx : π x ∈ layer Q := by rw [← D.twoComp.sup_eq]; exact D.pi_mem_sup hx
  refine Subgroup.mem_inf.mpr ⟨(fHhat π S₁ S₂).mul_mem
    ((fHhat π S₁ S₂).mul_mem hx hyH) ((fHhat π S₁ S₂).inv_mem hx), ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv]
  exact D.twoComp.norm₂ _ hπx _ hyS

omit [Finite HH] in
theorem le_Hhat_of_perfect [Finite Q] {P : Subgroup HH} (hP : ⁅P, P⁆ = P) : P ≤ fHhat π S₁ S₂ := by
  have hder : ∀ n : ℕ, P ≤ derivedSeries HH n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc P = ⁅P, P⁆ := hP.symm
        _ ≤ ⁅derivedSeries HH n, derivedSeries HH n⁆ := commutator_mono ih ih
  have h2 := derivedSeries_two_le_layer_of_twoComp D.twoComp D.card₁ D.card₂
  have hPl : P ≤ (S₁ ⊔ S₂).comap π := by
    intro x hx
    have h3 : π x ∈ derivedSeries Q 2 := map_derivedSeries_le_derivedSeries π 2
      ⟨x, hder 2 hx, rfl⟩
    rw [mem_comap, D.twoComp.sup_eq]
    exact h2 h3
  exact le_prOf hP hPl

end FacData

end Fac

end CFSG.OddStandard.Seitz77
