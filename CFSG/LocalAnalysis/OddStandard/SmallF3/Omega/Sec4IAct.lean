module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ITheta
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutAlpha

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def sec4IConj (L : Subgroup G) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    MulAut ↥L where
  toFun l := ⟨s * l * s⁻¹, (hs l).mp l.2⟩
  invFun l := ⟨s⁻¹ * l * s, by simpa using ((Subgroup.inv_mem _ hs) (l : G)).mp l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    change s * ((a : G) * (b : G)) * s⁻¹ = (s * (a : G) * s⁻¹) * (s * (b : G) * s⁻¹)
    group)

theorem coe_sec4IConj (L : Subgroup G) {s : G} (hs : s ∈ normalizer (L : Set G)) (l : ↥L) :
    ((sec4IConj L hs l : ↥L) : G) = s * l * s⁻¹ := rfl

@[expose] def Sec4IActs (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (s : G)
    (y : ProjOrth Sec4IQ) : Prop :=
  s ∈ normalizer (L : Set G) ∧
    ∀ l l' : ↥L, (l' : G) = s * l * s⁻¹ →
      ((e (QuotientGroup.mk l') : Sec4IOmega) : ProjOrth Sec4IQ) =
        y * ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ) * y⁻¹

theorem exists_sec4IActs (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G}
    (hs : s ∈ normalizer (L : Set G)) : ∃ y : ProjOrth Sec4IQ, Sec4IActs e s y := by
  let σ := sec4IConj L hs
  have hσ : (Subgroup.center ↥L).map σ.toMonoidHom = Subgroup.center ↥L :=
    Subgroup.map_center_eq σ
  let α₁ := QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) σ hσ
  let α : MulAut Sec4IOmega := e.symm.trans (α₁.trans e)
  obtain ⟨y, hy⟩ := sec4I_conjNormal_bijective_std.2 α
  refine ⟨y, hs, fun l l' hl' => ?_⟩
  have hl'σ : l' = σ l := Subtype.ext hl'
  have h1 : e (QuotientGroup.mk l') = α (e (QuotientGroup.mk l)) := by
    rw [hl'σ]
    have h3 : α₁ (QuotientGroup.mk l) = QuotientGroup.mk (σ l) := rfl
    show _ = e (α₁ (e.symm (e (QuotientGroup.mk l))))
    rw [e.symm_apply_apply, h3]
  have h2 := congrArg
    (fun φ : MulAut Sec4IOmega => ((φ (e (QuotientGroup.mk l)) : Sec4IOmega) : ProjOrth Sec4IQ)) hy
  simp only [MulAut.conjNormal_apply] at h2
  rw [h1]
  exact h2.symm

theorem Sec4IActs.unique {e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega} {s : G}
    {y y' : ProjOrth Sec4IQ} (h : Sec4IActs e s y) (h' : Sec4IActs e s y') : y = y' := by
  have hc : ∀ w ∈ Sec4IOmega, (y⁻¹ * y') * w = w * (y⁻¹ * y') := by
    intro w hw
    obtain ⟨q, hq⟩ := e.surjective ⟨w, hw⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    let l' : ↥L := ⟨s * l * s⁻¹, (h.1 l).mp l.2⟩
    have hw' : ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ) = w :=
      congrArg Subtype.val hq
    have key : y * w * y⁻¹ = y' * w * y'⁻¹ := by
      rw [← hw']
      exact (h.2 l l' rfl).symm.trans (h'.2 l l' rfl)
    calc y⁻¹ * y' * w = y⁻¹ * (y' * w * y'⁻¹) * y' := by group
      _ = y⁻¹ * (y * w * y⁻¹) * y' := by rw [key]
      _ = w * (y⁻¹ * y') := by group
  exact inv_mul_eq_one.mp (sec4I_eq_one_of_commute sec4IQ_nondegenerate sec4IQ_finrank
    sec4IQ_quadSign hc)

theorem Sec4IActs.one (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) :
    Sec4IActs e (1 : G) 1 := by
  refine ⟨Subgroup.one_mem _, fun l l' hl' => ?_⟩
  have : l' = l := Subtype.ext (by simpa using hl')
  rw [this]
  group

theorem Sec4IActs.mul {e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega} {s s' : G}
    {y y' : ProjOrth Sec4IQ} (h : Sec4IActs e s y) (h' : Sec4IActs e s' y') :
    Sec4IActs e (s * s') (y * y') := by
  refine ⟨Subgroup.mul_mem _ h.1 h'.1, fun l l'' hl'' => ?_⟩
  let l' : ↥L := ⟨s' * l * s'⁻¹, (h'.1 l).mp l.2⟩
  have hl2 : (l'' : G) = s * l' * s⁻¹ := by
    rw [hl'']
    change _ = s * (s' * (l : G) * s'⁻¹) * s⁻¹
    group
  have e1 := h.2 l' l'' hl2
  have e2 := h'.2 l l' rfl
  rw [e1, e2]
  group

theorem Sec4IActs.inv {e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega} {s : G}
    {y : ProjOrth Sec4IQ} (h : Sec4IActs e s y) : Sec4IActs e s⁻¹ y⁻¹ := by
  refine ⟨Subgroup.inv_mem _ h.1, fun l l' hl' => ?_⟩
  have hl : (l : G) = s * l' * s⁻¹ := by
    rw [hl']
    group
  have e1 := h.2 l' l hl
  have e2 : ((e (QuotientGroup.mk l') : Sec4IOmega) : ProjOrth Sec4IQ) =
      y⁻¹ * ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ) * y := by
    rw [e1]
    group
  rw [e2]
  group

theorem Sec4IActs.sq {e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega} {s : G}
    {y : ProjOrth Sec4IQ} (h : Sec4IActs e s y) (hss : s * s = 1) : y * y = 1 := by
  have h2 := h.mul h
  rw [hss] at h2
  exact h2.unique (Sec4IActs.one e)

theorem Sec4IActs.of_mem (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {w : G} (hw : w ∈ L) :
    Sec4IActs e w ((e (QuotientGroup.mk (⟨w, hw⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ) := by
  refine ⟨Subgroup.le_normalizer hw, fun l l' hl' => ?_⟩
  have : l' = ⟨w, hw⟩ * l * ⟨w, hw⟩⁻¹ := Subtype.ext hl'
  rw [this]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv,
    Subgroup.coe_mul, Subgroup.coe_inv]

theorem Sec4IActs.eq_one_iff [Finite G] {e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega} {s : G}
    {y : ProjOrth Sec4IQ} (hL : IsOmega7Group L) (h : Sec4IActs e s y) :
    y = 1 ↔ s ∈ centralizer (L : Set G) := by
  constructor
  · rintro rfl
    have hs : s ∈ normalizer (L : Set G) := h.1
    have hρ := sec4ICover_odd hL e
    have hfix : ∀ l : ↥L, sec4ICover e (sec4IConj L hs l) = sec4ICover e l := by
      intro l
      apply Subtype.ext
      have h2 := h.2 l (sec4IConj L hs l) rfl
      rw [one_mul, inv_one, mul_one] at h2
      exact h2
    obtain ⟨y₀, hy₀⟩ := exists_inner_of_conj hρ hL.1.1.commutator_eq_top
      (σ := sec4IConj L hs) (α := 1) (p := 1)
      (fun l => by simpa using hfix l) (by ext; simp)
    have hcen : ((sec4ICover e y₀ : Sec4IOmega) : ProjOrth Sec4IQ) = 1 := by
      refine eq_one_of_central_omegaProj_seven sec4IQ_nondegenerate sec4IQ_finrank
        sec4IQ_quadSign (sec4ICover e y₀).2 (fun w' hw' => ?_)
      obtain ⟨l, hl⟩ := hρ.surjective ⟨w', hw'⟩
      have h1 := hfix l
      rw [hy₀ l, map_mul, map_mul, map_inv] at h1
      have h2 := congrArg Subtype.val h1
      have hw'' : ((sec4ICover e l : Sec4IOmega) : ProjOrth Sec4IQ) = w' := congrArg Subtype.val hl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw''] at h2
      calc (sec4ICover e y₀ : ProjOrth Sec4IQ) * w' =
          ((sec4ICover e y₀ : ProjOrth Sec4IQ) * w' * (sec4ICover e y₀ : ProjOrth Sec4IQ)⁻¹) *
            (sec4ICover e y₀ : ProjOrth Sec4IQ) := by group
        _ = w' * (sec4ICover e y₀ : ProjOrth Sec4IQ) := by rw [h2]
    have hker : y₀ ∈ Subgroup.center ↥L :=
      hρ.ker_le_center (MonoidHom.mem_ker.mpr (Subtype.ext hcen))
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h3 := congrArg Subtype.val (hy₀ ⟨l, hl⟩)
    change s * l * s⁻¹ = (y₀ : G) * l * (y₀ : G)⁻¹ at h3
    have h4 := Subgroup.mem_center_iff.mp hker ⟨l, hl⟩
    have h5 : l * (y₀ : G) = (y₀ : G) * l := congrArg Subtype.val h4
    have h6 : s * l * s⁻¹ = l := by
      rw [h3, ← h5]
      group
    exact (mul_inv_eq_iff_eq_mul.mp h6).symm
  · intro hc
    have h1 : Sec4IActs e s 1 := by
      refine ⟨Subgroup.centralizer_le_normalizer (L : Set G) hc, fun l l' hl' => ?_⟩
      have : l' = l := by
        apply Subtype.ext
        rw [hl']
        have := Subgroup.mem_centralizer_iff.mp hc l l.2
        rw [← this, mul_inv_cancel_right]
      rw [this]
      group
    exact h.unique h1

end CFSG.OddStandard.SmallF3.Omega
