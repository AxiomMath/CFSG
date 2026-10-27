module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearModule
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements

public noncomputable section

namespace CFSG.EvenSmallLie.Child3.AltEight

open Subgroup

variable {G : Type} [Group G] {C : Subgroup G}

@[expose] def conjDiff (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (t : G)
    (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C) : C →* G where
  toFun c := (c : G)⁻¹ * (t * c * t⁻¹)
  map_one' := by simp
  map_mul' c d := by
    have hc := c.2
    have hd := d.2
    have h1 := hCab _ (inv_mem hd) _ (mul_mem (inv_mem hc) (htC _ hc))
    calc ((c * d : C) : G)⁻¹ * (t * ((c * d : C) : G) * t⁻¹)
        = (d : G)⁻¹ * ((c : G)⁻¹ * (t * c * t⁻¹)) * (t * d * t⁻¹) := by
          rw [Subgroup.coe_mul]
          group
      _ = (c : G)⁻¹ * (t * c * t⁻¹) * (d : G)⁻¹ * (t * d * t⁻¹) := by rw [h1]
      _ = _ := by group

theorem conjDiff_apply (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (t : G)
    (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (c : C) :
    conjDiff hCab t htC c = (c : G)⁻¹ * (t * c * t⁻¹) := rfl

theorem conjDiff_mem (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (t : G)
    (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (c : C) : conjDiff hCab t htC c ∈ C :=
  mul_mem (inv_mem c.2) (htC _ c.2)

theorem conjDiff_eq_one_iff (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (t : G)
    (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (c : C) :
    conjDiff hCab t htC c = 1 ↔ (c : G) * t = t * c := by
  rw [conjDiff_apply]
  constructor
  · intro h
    have h1 : t * (c : G) * t⁻¹ = c := by
      calc t * (c : G) * t⁻¹ = c * ((c : G)⁻¹ * (t * c * t⁻¹)) := by group
        _ = c := by rw [h, mul_one]
    calc (c : G) * t = t * c * t⁻¹ * t := by rw [h1]
      _ = t * c := by group
  · intro h
    rw [← mul_assoc, ← h]
    group

@[expose] def mulInvHom (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (f g : C →* G)
    (hf : ∀ c, f c ∈ C) (hg : ∀ c, g c ∈ C) : C →* G where
  toFun c := f c * (g c)⁻¹
  map_one' := by simp
  map_mul' c d := by
    have h1 := hCab _ (mul_mem (hf d) (inv_mem (hg d))) _ (inv_mem (hg c))
    calc f (c * d) * (g (c * d))⁻¹ = f c * ((f d * (g d)⁻¹) * (g c)⁻¹) := by
          rw [map_mul, map_mul]
          group
      _ = f c * ((g c)⁻¹ * (f d * (g d)⁻¹)) := by rw [h1]
      _ = f c * (g c)⁻¹ * (f d * (g d)⁻¹) := by group

theorem mulInvHom_apply (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (f g : C →* G)
    (hf : ∀ c, f c ∈ C) (hg : ∀ c, g c ∈ C) (c : C) :
    mulInvHom hCab f g hf hg c = f c * (g c)⁻¹ := rfl

theorem card_eq_card_map_mul_card_inf {H : Type*} [Group H] {K : Type*} [Group K] (f : H →* K)
    (W : Subgroup H) : Nat.card W = Nat.card (W.map f) * Nat.card ↥(f.ker ⊓ W) := by
  rw [← relIndex_ker W f, relIndex_mul_card]

theorem conj_commutator_eq {z t c : G} (hzt : z * t = t * z) :
    t * (c⁻¹ * z⁻¹ * c * z) * t⁻¹ =
      (t * c * t⁻¹)⁻¹ * z⁻¹ * (t * c * t⁻¹) * z := by
  have h1 : t * z⁻¹ * t⁻¹ = z⁻¹ := by
    calc t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ := by group
      _ = z⁻¹ := by rw [← hzt, mul_inv_cancel_right]
  have h2 : t * z * t⁻¹ = z := by rw [← hzt, mul_inv_cancel_right]
  calc t * (c⁻¹ * z⁻¹ * c * z) * t⁻¹
      = (t * c * t⁻¹)⁻¹ * (t * z⁻¹ * t⁻¹) * (t * c * t⁻¹) * (t * z * t⁻¹) := by group
    _ = _ := by rw [h1, h2]

section Count

variable [Finite G] {A : Subgroup G} {I : Set G} {z t i₀ : G}

theorem card_inf_centralizer_le_two_pow_five
    (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c)
    (hzC : ∀ c ∈ C, z⁻¹ * c * z ∈ C) (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (hzt : z * t = t * z)
    (hAC : A ≤ C) (hfix : ∀ c ∈ C, c * z = z * c ↔ c ∈ A)
    (hNI : ∀ c ∈ C, c⁻¹ * z⁻¹ * c * z ∈ I) (hIA : I ⊆ A)
    (hA : Nat.card A = 2 ^ 6) (hAt : Nat.card ↥(A ⊓ centralizer {t}) ≤ 2 ^ 4)
    (hIt : Nat.card {i : G // i ∈ I ∧ i * t = t * i} ≤ 2 ^ 2)
    (hi₀C : ∃ c ∈ C, c⁻¹ * z⁻¹ * c * z = i₀) (hi₀t : i₀ * t = t * i₀)
    (hi₀ : ∀ a ∈ A, a⁻¹ * (t * a * t⁻¹) ≠ i₀)
    (hzt6 : 2 ^ 6 ≤ Nat.card ↥(C ⊓ centralizer {z * t})) :
    Nat.card ↥(C ⊓ centralizer {t}) ≤ 2 ^ 5 := by
  classical
  have hzC' : ∀ c ∈ C, z⁻¹ * c * z⁻¹⁻¹ ∈ C := fun c hc => by rw [inv_inv]; exact hzC c hc
  set Tm := conjDiff hCab t htC with hTm
  set Nm := conjDiff hCab z⁻¹ hzC' with hNm
  have hTmC : ∀ c, Tm c ∈ C := conjDiff_mem hCab t htC
  have hNmC : ∀ c, Nm c ∈ C := conjDiff_mem hCab z⁻¹ hzC'
  have hNmv : ∀ c : C, Nm c = (c : G)⁻¹ * z⁻¹ * c * z := fun c => by
    rw [hNm, conjDiff_apply, inv_inv]
    group
  have hcz : ∀ x : G, x * z⁻¹ = z⁻¹ * x ↔ x * z = z * x := fun x => by
    constructor
    · intro h
      calc x * z = z * (z⁻¹ * x) * z := by group
        _ = z * (x * z⁻¹) * z := by rw [h]
        _ = z * x := by group
    · intro h
      calc x * z⁻¹ = z⁻¹ * (z * x) * z⁻¹ := by group
        _ = z⁻¹ * (x * z) * z⁻¹ := by rw [h]
        _ = z⁻¹ * x := by group
  have hNker : ∀ c : C, Nm c = 1 ↔ (c : G) ∈ A := fun c => by
    rw [hNm, conjDiff_eq_one_iff, hcz]
    exact hfix _ c.2
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := by
    intro a ha
    have haC := hAC ha
    rw [← hfix _ (htC _ haC)]
    have h1 : a * z = z * a := (hfix _ haC).2 ha
    have h2 : t⁻¹ * z = z * t⁻¹ := by
      calc t⁻¹ * z = t⁻¹ * (z * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * z) * t⁻¹ := by rw [hzt]
        _ = z * t⁻¹ := by group
    calc t * a * t⁻¹ * z = t * a * (t⁻¹ * z) := by group
      _ = t * (a * z) * t⁻¹ := by rw [h2]; group
      _ = t * (z * a) * t⁻¹ := by rw [h1]
      _ = (t * z) * a * t⁻¹ := by group
      _ = z * (t * a * t⁻¹) := by rw [← hzt]; group
  have hNT : ∀ c : C, t * Nm c * t⁻¹ = Nm c * Nm ⟨Tm c, hTmC c⟩ := by
    intro c
    have hd : (⟨t * c * t⁻¹, htC _ c.2⟩ : C) = c * ⟨Tm c, hTmC c⟩ := Subtype.ext (by
      change t * (c : G) * t⁻¹ = c * Tm c
      rw [hTm, conjDiff_apply]
      group)
    rw [← map_mul, ← hd, hNmv, hNmv, conj_commutator_eq hzt]
  have hTA : ∀ c : C, Tm c ∈ A ↔ Nm c * t = t * Nm c := by
    intro c
    rw [← hNker ⟨Tm c, hTmC c⟩]
    constructor
    · intro h
      have h1 := hNT c
      rw [h, mul_one] at h1
      calc Nm c * t = t * Nm c * t⁻¹ * t := by rw [h1]
        _ = t * Nm c := by group
    · intro h
      have h1 := hNT c
      have h2 : t * Nm c * t⁻¹ = Nm c := by rw [← h]; group
      rw [h2] at h1
      exact (mul_eq_left.1 h1.symm)
  set A' := A.subgroupOf C with hA'
  set W := A.comap Tm with hW
  have hA'card : Nat.card A' = 2 ^ 6 := by
    rw [hA', Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, hA]
  have hA'W : A' ≤ W := by
    intro a ha
    rw [hA', mem_subgroupOf] at ha
    change Tm a ∈ A
    rw [hTm, conjDiff_apply]
    exact mul_mem (inv_mem ha) (htA _ ha)
  have hNmker : Nm.ker = A' := by
    ext c
    rw [MonoidHom.mem_ker, hNker, hA', mem_subgroupOf]
  have hWcard : Nat.card W ≤ 2 ^ 8 := by
    have h1 := card_eq_card_map_mul_card_inf Nm W
    have h2 : Nat.card ↥(Nm.ker ⊓ W) ≤ 2 ^ 6 := by
      rw [← hA'card, ← hNmker]
      exact Subgroup.card_le_of_le inf_le_left
    have h3 : Nat.card (W.map Nm) ≤ 2 ^ 2 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : W.map Nm => (⟨(x : G), ?_⟩ : {i : G // i ∈ I ∧ i * t = t * i})) ?_) hIt
      · obtain ⟨c, hc, hcx⟩ := x.2
        rw [← hcx]
        exact ⟨by rw [hNmv]; exact hNI _ c.2, (hTA c).1 hc⟩
      · intro x y h
        exact Subtype.ext (congrArg (fun i : {i : G // i ∈ I ∧ i * t = t * i} => (i : G)) h)
    rw [h1]
    calc Nat.card (W.map Nm) * Nat.card ↥(Nm.ker ⊓ W) ≤ 2 ^ 2 * 2 ^ 6 :=
          Nat.mul_le_mul h3 h2
      _ = 2 ^ 8 := by norm_num
  set Δ := mulInvHom hCab Tm Nm hTmC hNmC with hΔ
  have hΔker : ∀ c : C, Δ c = 1 ↔ (c : G) * (z * t) = (z * t) * c := by
    intro c
    rw [hΔ, mulInvHom_apply, mul_inv_eq_one, hTm, conjDiff_apply, hNmv]
    constructor
    · intro h
      have h1 : t * (c : G) * t⁻¹ = z⁻¹ * c * z := by
        calc t * (c : G) * t⁻¹ = c * ((c : G)⁻¹ * (t * c * t⁻¹)) := by group
          _ = c * ((c : G)⁻¹ * z⁻¹ * c * z) := by rw [h]
          _ = z⁻¹ * c * z := by group
      calc (c : G) * (z * t) = z * (z⁻¹ * c * z) * t := by group
        _ = z * (t * c * t⁻¹) * t := by rw [h1]
        _ = z * t * c := by group
    · intro h
      calc (c : G)⁻¹ * (t * c * t⁻¹) = (c : G)⁻¹ * z⁻¹ * (z * t * c) * t⁻¹ := by group
        _ = (c : G)⁻¹ * z⁻¹ * (c * (z * t)) * t⁻¹ := by rw [h]
        _ = (c : G)⁻¹ * z⁻¹ * c * z := by group
  have hΔW : Δ.ker ≤ W := by
    intro c hc
    have h1 : Tm c = Nm c := by
      have := (MonoidHom.mem_ker.1 hc)
      rwa [hΔ, mulInvHom_apply, mul_inv_eq_one] at this
    change Tm c ∈ A
    rw [h1, hNmv]
    exact hIA (hNI _ c.2)
  have hΔcard : 2 ^ 6 ≤ Nat.card Δ.ker := by
    have heq : Δ.ker.map C.subtype = C ⊓ centralizer {z * t} := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact mem_inf.2 ⟨c.2, mem_centralizer_singleton_iff.2 ((hΔker c).1 hc)⟩
      · intro hx
        obtain ⟨hxC, hxz⟩ := mem_inf.1 hx
        exact ⟨⟨x, hxC⟩, (hΔker _).2 (mem_centralizer_singleton_iff.1 hxz), rfl⟩
    rw [← Subgroup.card_map_of_injective C.subtype_injective, heq]
    exact hzt6
  have hWΔ : Nat.card (W.map Δ) ≤ 2 ^ 2 := by
    have h1 := card_eq_card_map_mul_card_inf Δ W
    rw [inf_eq_left.2 hΔW] at h1
    have h2 : Nat.card (W.map Δ) * 2 ^ 6 ≤ 2 ^ 2 * 2 ^ 6 := by
      calc Nat.card (W.map Δ) * 2 ^ 6 ≤ Nat.card (W.map Δ) * Nat.card Δ.ker :=
            Nat.mul_le_mul_left _ hΔcard
        _ = Nat.card W := h1.symm
        _ ≤ 2 ^ 8 := hWcard
        _ = 2 ^ 2 * 2 ^ 6 := by norm_num
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  set TA := A'.map Tm with hTAdef
  have hTAcard : 2 ^ 2 ≤ Nat.card TA := by
    have h1 := card_eq_card_map_mul_card_inf Tm A'
    have h2 : Nat.card ↥(Tm.ker ⊓ A') ≤ 2 ^ 4 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun c : ↥(Tm.ker ⊓ A') => (⟨((c : C) : G), ?_⟩ : ↥(A ⊓ centralizer {t}))) ?_) hAt
      · obtain ⟨hc1, hc2⟩ := mem_inf.1 c.2
        have hc2' : ((c : C) : G) ∈ A := mem_subgroupOf.1 hc2
        refine mem_inf.2 ⟨hc2', mem_centralizer_singleton_iff.2 ?_⟩
        exact (conjDiff_eq_one_iff hCab t htC _).1 (MonoidHom.mem_ker.1 hc1)
      · intro x y h
        exact Subtype.ext (Subtype.ext
          (congrArg (fun i : ↥(A ⊓ centralizer {t}) => (i : G)) h))
    rw [hA'card] at h1
    by_contra hlt
    push Not at hlt
    have h3 : Nat.card TA * Nat.card ↥(Tm.ker ⊓ A') < 2 ^ 2 * 2 ^ 4 := by
      calc Nat.card TA * Nat.card ↥(Tm.ker ⊓ A') ≤ Nat.card TA * 2 ^ 4 :=
            Nat.mul_le_mul_left _ h2
        _ < 2 ^ 2 * 2 ^ 4 := Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
    rw [← h1] at h3
    norm_num at h3
  have hTAΔ : TA ≤ W.map Δ := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, hA'W ha, ?_⟩
    rw [hΔ, mulInvHom_apply, (MonoidHom.mem_ker.1 (hNmker ▸ ha : a ∈ Nm.ker)), inv_one,
      mul_one]
  have hΔTA : W.map Δ = TA :=
    (Subgroup.eq_of_le_of_card_ge hTAΔ (hWΔ.trans hTAcard)).symm
  obtain ⟨c₀, hc₀C, hc₀⟩ := hi₀C
  have hNc₀ : Nm ⟨c₀, hc₀C⟩ = i₀ := by rw [hNmv]; exact hc₀
  have hc₀W : (⟨c₀, hc₀C⟩ : C) ∈ W := by
    change Tm ⟨c₀, hc₀C⟩ ∈ A
    rw [hTA, hNc₀]
    exact hi₀t
  have hTc₀ : Tm ⟨c₀, hc₀C⟩ ∉ TA := by
    intro h
    have hΔc₀ : Δ ⟨c₀, hc₀C⟩ ∈ TA := hΔTA ▸ mem_map_of_mem Δ hc₀W
    have h1 : i₀ = (Δ ⟨c₀, hc₀C⟩)⁻¹ * Tm ⟨c₀, hc₀C⟩ := by
      rw [hΔ, mulInvHom_apply, hNc₀]
      group
    have h2 : i₀ ∈ TA := by
      rw [h1]
      exact mul_mem (inv_mem hΔc₀) h
    obtain ⟨a, ha, hai⟩ := h2
    exact hi₀ _ (mem_subgroupOf.1 ha) (by rw [← hai, hTm, conjDiff_apply])
  have hTW : 2 ^ 3 ≤ Nat.card (W.map Tm) := by
    have hle : TA ≤ W.map Tm := map_mono hA'W
    have hlt : TA < W.map Tm := lt_of_le_of_ne hle fun h =>
      hTc₀ (h ▸ mem_map_of_mem Tm hc₀W)
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [hm] at h1 ⊢
    have hm2 : 2 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m
      · simp at h1
      · simp at h1
    calc 2 ^ 3 = 2 ^ 2 * 2 := by norm_num
      _ ≤ Nat.card TA * m := Nat.mul_le_mul hTAcard hm2
  have hTker : Tm.ker ≤ W := by
    intro c hc
    change Tm c ∈ A
    rw [MonoidHom.mem_ker.1 hc]
    exact one_mem _
  have hTcard : Nat.card Tm.ker ≤ 2 ^ 5 := by
    have h1 := card_eq_card_map_mul_card_inf Tm W
    rw [inf_eq_left.2 hTker] at h1
    have h2 : 2 ^ 3 * Nat.card Tm.ker ≤ 2 ^ 3 * 2 ^ 5 := by
      calc 2 ^ 3 * Nat.card Tm.ker ≤ Nat.card (W.map Tm) * Nat.card Tm.ker :=
            Nat.mul_le_mul_right _ hTW
        _ = Nat.card W := h1.symm
        _ ≤ 2 ^ 8 := hWcard
        _ = 2 ^ 3 * 2 ^ 5 := by norm_num
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have heq : Tm.ker.map C.subtype = C ⊓ centralizer {t} := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact mem_inf.2 ⟨c.2, mem_centralizer_singleton_iff.2
        ((conjDiff_eq_one_iff hCab t htC c).1 hc)⟩
    · intro hx
      obtain ⟨hxC, hxt⟩ := mem_inf.1 hx
      exact ⟨⟨x, hxC⟩, (conjDiff_eq_one_iff hCab t htC _).2
        (mem_centralizer_singleton_iff.1 hxt), rfl⟩
  rw [← heq, Subgroup.card_map_of_injective C.subtype_injective]
  exact hTcard

end Count

section Levi

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open Module
open LinearMap (BilinForm)

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def symE13 : ↥(binarySymMatrices 3) := ⟨!![0, 0, 1; 0, 0, 0; 1, 0, 0], by decide⟩

@[expose] def symE22 : ↥(binarySymMatrices 3) := ⟨!![0, 0, 0; 0, 1, 0; 0, 0, 0], by decide⟩

theorem symThreeCongr_trans_symE13 : symThreeCongr glTransThreeOne symE13 = symE13 := by
  decide +kernel

theorem sub_ne_symE13 : ∀ B : ↥(binarySymMatrices 3),
    -B + symThreeCongr glTransThreeOne B ≠ symE13 := by
  decide +kernel

theorem symE22_facts : symThreeCongr glTransThreeOne symE22 = symE22 ∧
    symThreeCongr glTransTwoOne symE22 ≠ symE22 := by
  decide +kernel

theorem symE13_ne : symThreeCongr glTransThreeTwo symE13 ≠ symE13 := by
  decide +kernel

theorem eq_of_alt_fix {B B' : ↥(binarySymMatrices 3)} (hB : ∀ i, (B : M₃) i i = 0)
    (hB' : ∀ i, (B' : M₃) i i = 0) (hBt : symThreeCongr glTransThreeOne B = B)
    (hB't : symThreeCongr glTransThreeOne B' = B') (h01 : (B : M₃) 0 1 = (B' : M₃) 0 1)
    (h02 : (B : M₃) 0 2 = (B' : M₃) 0 2) : B = B' := by
  obtain ⟨h12, -⟩ := SteinbergBM.fix_glTransThreeOne B hBt
  obtain ⟨h12', -⟩ := SteinbergBM.fix_glTransThreeOne B' hB't
  exact SteinbergBM.eq_of_upper_eq ((hB 0).trans (hB' 0).symm) h01 h02
    ((hB 1).trans (hB' 1).symm) (h12.trans h12'.symm) ((hB 2).trans (hB' 2).symm)

variable {L : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) {z : G}

theorem tauHom_mem_sp6A₂ (B : Multiplicative ↥(binarySymMatrices 3)) :
    tauHom φ he B ∈ sp6A₂ φ e :=
  (mem_pullSub_iff φ he).2 ⟨B, rfl⟩

theorem leviHom_comm_tauHom_iff (g : GL (Fin 3) (ZMod 2)) (B : ↥(binarySymMatrices 3)) :
    tauHom φ he (Multiplicative.ofAdd B) * leviHom φ he g =
        leviHom φ he g * tauHom φ he (Multiplicative.ofAdd B) ↔ symThreeCongr g B = B := by
  constructor
  · intro h
    have h1 : leviHom φ he g * tauHom φ he (Multiplicative.ofAdd B) * (leviHom φ he g)⁻¹ =
        tauHom φ he (Multiplicative.ofAdd B) := by
      rw [← h]
      group
    rw [RadicalLabels.leviHom_conj_tauHom'] at h1
    exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1)
  · intro h
    have h1 := RadicalLabels.leviHom_conj_tauHom' φ he g B
    rw [h] at h1
    calc tauHom φ he (Multiplicative.ofAdd B) * leviHom φ he g
        = leviHom φ he g * tauHom φ he (Multiplicative.ofAdd B) * (leviHom φ he g)⁻¹ *
            leviHom φ he g := by rw [h1]
      _ = _ := by group

theorem card_inf_centralizer_leviTrans_le [Finite G] {C : Subgroup G}
    (hzL : z ∈ centralizer (L : Set G))
    (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) (hzC : ∀ c ∈ C, z⁻¹ * c * z ∈ C)
    (htC : ∀ c ∈ C,
      leviHom φ he glTransThreeOne * c * (leviHom φ he glTransThreeOne)⁻¹ ∈ C)
    (hA₂C : sp6A₂ φ e ≤ C) (hfixz : ∀ c ∈ C, c * z = z * c ↔ c ∈ sp6A₂ φ e)
    (hA₂card : Nat.card (sp6A₂ φ e) = 2 ^ 6)
    (hcomm : {x | ∃ c ∈ C, c⁻¹ * z⁻¹ * c * z = x} = tauSet φ e (fun B => ∀ i, B i i = 0))
    (h6 : 2 ^ 6 ≤ Nat.card ↥(C ⊓ centralizer {z * leviHom φ he glTransThreeOne})) :
    Nat.card ↥(C ⊓ centralizer {leviHom φ he glTransThreeOne}) ≤ 2 ^ 5 := by
  classical
  set t := leviHom φ he glTransThreeOne with ht
  set I := tauSet φ e (fun B => ∀ i, B i i = 0) with hIdef
  have hzt : z * t = t * z := (RadicalLabels.leviHom_mul_z φ he hzL _).symm
  have hNI : ∀ c ∈ C, c⁻¹ * z⁻¹ * c * z ∈ I := fun c hc => by
    rw [← hcomm]
    exact ⟨c, hc, rfl⟩
  have hIA : I ⊆ sp6A₂ φ e := by
    intro x hx
    obtain ⟨B, -, rfl⟩ := (mem_tauSet_iff φ he).1 hx
    exact tauHom_mem_sp6A₂ φ he B
  have hAt : Nat.card ↥(sp6A₂ φ e ⊓ centralizer {t}) ≤ 2 ^ 4 := by
    have h := SteinbergBM.card_tauHom_fixed_le φ he (S := {glTransThreeOne}) (n := 4) (by
      have e' : {B : ↥(binarySymMatrices 3) //
          ∀ g ∈ ({glTransThreeOne} : Set (GL (Fin 3) (ZMod 2))), symThreeCongr g B = B} ≃
          {B : ↥(binarySymMatrices 3) // symThreeCongr glTransThreeOne B = B} :=
        Equiv.subtypeEquivRight fun B => by simp
      rw [Nat.card_congr e']
      exact SteinbergBM.card_fix_glTransThreeOne_le)
    rwa [Set.image_singleton] at h
  have hIt : Nat.card {i : G // i ∈ I ∧ i * t = t * i} ≤ 2 ^ 2 := by
    have key : ∀ i : {i : G // i ∈ I ∧ i * t = t * i}, ∃ B : ↥(binarySymMatrices 3),
        (∀ j, (B : M₃) j j = 0) ∧ symThreeCongr glTransThreeOne B = B ∧
          tauHom φ he (Multiplicative.ofAdd B) = i := by
      rintro ⟨i, hi, hit⟩
      obtain ⟨B, hB, rfl⟩ := (mem_tauSet_iff φ he).1 hi
      exact ⟨Multiplicative.toAdd B, hB, (leviHom_comm_tauHom_iff φ he _ _).1 hit, rfl⟩
    choose f hf0 hft hfi using key
    have hinj : Function.Injective (fun i => ((f i : M₃) 0 1, (f i : M₃) 0 2)) := by
      intro i j h
      simp only [Prod.mk.injEq] at h
      have h1 := eq_of_alt_fix (hf0 i) (hf0 j) (hft i) (hft j) h.1 h.2
      apply Subtype.ext
      rw [← hfi i, ← hfi j, h1]
    have := Nat.card_le_card_of_injective _ hinj
    simpa [Nat.card_prod, Nat.card_zmod] using this
  set i₀ := tauHom φ he (Multiplicative.ofAdd symE13) with hi₀def
  have hi₀I : i₀ ∈ I := (mem_tauSet_iff φ he).2 ⟨_, by decide, rfl⟩
  have hi₀C : ∃ c ∈ C, c⁻¹ * z⁻¹ * c * z = i₀ := by
    have h : i₀ ∈ {x | ∃ c ∈ C, c⁻¹ * z⁻¹ * c * z = x} := by
      rw [hcomm]
      exact hi₀I
    exact h
  have hi₀t : i₀ * t = t * i₀ :=
    (leviHom_comm_tauHom_iff φ he _ _).2 symThreeCongr_trans_symE13
  have hi₀ : ∀ a ∈ sp6A₂ φ e, a⁻¹ * (t * a * t⁻¹) ≠ i₀ := by
    intro a ha h
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    have hc := RadicalLabels.leviHom_conj_tauHom' φ he glTransThreeOne (Multiplicative.toAdd B)
    rw [ofAdd_toAdd] at hc
    rw [ht, hc, ← map_inv, ← map_mul] at h
    have h1 := congrArg Multiplicative.toAdd (tauHom_injective φ he h)
    apply sub_ne_symE13 (Multiplicative.toAdd B)
    simpa using h1
  exact card_inf_centralizer_le_two_pow_five hCab hzC htC hzt hA₂C hfixz hNI hIA hA₂card hAt hIt
    hi₀C hi₀t hi₀ h6

theorem exists_tauHom_comm_not_comm {s : GL (Fin 3) (ZMod 2)}
    (hs : s = glTransTwoOne ∨ s = glTransThreeTwo) :
    ∃ B : ↥(binarySymMatrices 3),
      tauHom φ he (Multiplicative.ofAdd B) * leviHom φ he glTransThreeOne =
        leviHom φ he glTransThreeOne * tauHom φ he (Multiplicative.ofAdd B) ∧
      tauHom φ he (Multiplicative.ofAdd B) * leviHom φ he s ≠
        leviHom φ he s * tauHom φ he (Multiplicative.ofAdd B) := by
  rcases hs with rfl | rfl
  · exact ⟨symE22, (leviHom_comm_tauHom_iff φ he _ _).2 symE22_facts.1,
      fun h => symE22_facts.2 ((leviHom_comm_tauHom_iff φ he _ _).1 h)⟩
  · exact ⟨symE13, (leviHom_comm_tauHom_iff φ he _ _).2 symThreeCongr_trans_symE13,
      fun h => symE13_ne ((leviHom_comm_tauHom_iff φ he _ _).1 h)⟩

theorem card_inf_centralizer_leviPair_le [Finite G] {C : Subgroup G} (hA₂C : sp6A₂ φ e ≤ C)
    (h5 : Nat.card ↥(C ⊓ centralizer {leviHom φ he glTransThreeOne}) ≤ 2 ^ 5)
    {s : GL (Fin 3) (ZMod 2)} (hs : s = glTransTwoOne ∨ s = glTransThreeTwo) :
    Nat.card ↥(C ⊓ centralizer (leviHom φ he '' {s, glTransThreeOne})) ≤ 2 ^ 4 := by
  set H := C ⊓ centralizer (leviHom φ he '' {s, glTransThreeOne}) with hH
  set K := C ⊓ centralizer {leviHom φ he glTransThreeOne} with hK
  have hle : H ≤ K := inf_le_inf_left _ (centralizer_le (by
    rw [Set.singleton_subset_iff]
    exact ⟨glTransThreeOne, Or.inr rfl, rfl⟩))
  obtain ⟨B, hBt, hBs⟩ := exists_tauHom_comm_not_comm φ he hs
  have hBK : tauHom φ he (Multiplicative.ofAdd B) ∈ K :=
    mem_inf.2 ⟨hA₂C (tauHom_mem_sp6A₂ φ he _), mem_centralizer_singleton_iff.2 hBt⟩
  have hBH : tauHom φ he (Multiplicative.ofAdd B) ∉ H := fun h =>
    hBs ((mem_centralizer_iff.1 (mem_inf.1 h).2 (leviHom φ he s) ⟨s, Or.inl rfl, rfl⟩).symm)
  have hlt : H < K := lt_of_le_of_ne hle fun h => hBH (h ▸ hBK)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [hm] at h1 h5
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    interval_cases m
    · simp at h1
    · simp at h1
  have h2 : Nat.card H * 2 ≤ 2 ^ 4 * 2 := by
    calc Nat.card H * 2 ≤ Nat.card H * m := Nat.mul_le_mul_left _ hm2
      _ ≤ 2 ^ 5 := h5
      _ = 2 ^ 4 * 2 := by norm_num
  exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

end Levi

end CFSG.EvenSmallLie.Child3.AltEight
