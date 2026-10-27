module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64MiddleElementary

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise commutatorElement

theorem mul_sq_eq_of_comm {X : Type*} [Group X] {x y : X}
    (hk : (x⁻¹ * y⁻¹ * x * y) * x = x * (x⁻¹ * y⁻¹ * x * y)) :
    (y * x) ^ 2 = y ^ 2 * x ^ 2 * (x⁻¹ * y⁻¹ * x * y) := by
  rw [sq, sq, sq]
  calc y * x * (y * x) = y * y * x * (x⁻¹ * y⁻¹ * x * y * x) := by group
    _ = y * y * x * (x * (x⁻¹ * y⁻¹ * x * y)) := by rw [hk]
    _ = y * y * (x * x) * (x⁻¹ * y⁻¹ * x * y) := by group

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "ℬ₁" => ptSub φ z hb e

include he in
theorem qV_add (v w : 𝔼 × ZMod 2) :
    OddQuadraticFive.qV (ptQuad e) (v + w) = OddQuadraticFive.qV (ptQuad e) v +
      OddQuadraticFive.qV (ptQuad e) w + b (v.1 : V) (w.1 : V) := by
  have h1 : ptQuad e (v.1 + w.1) = ptQuad e v.1 + ptQuad e w.1 +
      QuadraticMap.polar (ptQuad e) v.1 w.1 := by
    rw [QuadraticMap.polar]
    abel
  have h2 : QuadraticMap.polar (ptQuad e) v.1 w.1 = b (v.1 : V) (w.1 : V) := by
    rw [← QuadraticMap.polarBilin_apply_apply, polarBilin_ptQuad he]
    rfl
  simp only [OddQuadraticFive.qV, Prod.fst_add, Prod.snd_add]
  rw [h1, h2]
  ring

include he hnd hinf in
theorem degree64_central_alternatives [Finite G] [FiniteDimensional (ZMod 2) V]
    {D₁ C₁ : Subgroup G} {τ₁ : G → 𝔼 × ZMod 2} {β ε : ZMod 2}
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁)
    (hτz : ∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c = ptHom he hb φ hzC hz (Multiplicative.ofAdd (τ₁ c, 0)))
    (hτmul : ∀ c ∈ C₁, ∀ c' ∈ C₁, τ₁ (c * c') = τ₁ c + τ₁ c')
    (hτsurj : ∀ v : 𝔼 × ZMod 2, ∃ c ∈ C₁, τ₁ c = v) (hτker : ∀ c ∈ C₁, τ₁ c = 0 ↔ c ∈ 𝒜₁)
    (hsq : ∀ c ∈ C₁, c ^ 2 = ptHom he hb φ hzC hz (Multiplicative.ofAdd
      ((β * OddQuadraticFive.qV (ptQuad e) (τ₁ c)) • OddQuadraticFive.rV, 0)))
    (hCC : ⁅C₁, C₁⁆ ≤ zpowers (ptB₁ he hb φ hzC hz))
    (hsq₀ : closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ zpowers (ptB₁ he hb φ hzC hz))
    (hEc : ∀ x ∈ C₁, z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz) →
      ∀ y ∈ C₁, x * y = y * x)
    (hEcard : Nat.card ↥((C₁ : Set G) ∩ {d | d ∈ D₁ ∧
      z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)}) = 64)
    {e₀ : G} (he₀C : e₀ ∈ C₁) (he₀τ : τ₁ e₀ = ((0 : 𝔼), (1 : ZMod 2)))
    (he₀sq : e₀ ^ 2 = ptB₁ he hb φ hzC hz ^ ε.val) :
    (∀ c ∈ C₁, c ^ 2 = ptHom he hb φ hzC hz (Multiplicative.ofAdd
      ((ε * OddQuadraticFive.qV (ptQuad e) (τ₁ c)) • OddQuadraticFive.rV, 0))) ∧
    (∀ c ∈ C₁, ∀ d ∈ C₁, c⁻¹ * d⁻¹ * c * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd
      ((ε * b ((τ₁ c).1 : V) ((τ₁ d).1 : V)) • OddQuadraticFive.rV, 0))) ∧
    (ε = 0 → (∀ c ∈ C₁, c ^ 2 = 1) ∧ ∀ c ∈ C₁, ∀ d ∈ C₁, c * d = d * c) ∧
    (ε = 1 → ⁅C₁, C₁⁆ = zpowers (ptB₁ he hb φ hzC hz) ∧
      closure {x | ∃ y ∈ C₁, y ^ 2 = x} = zpowers (ptB₁ he hb φ hzC hz) ∧
      (∀ x : G, x ∈ (center C₁).map C₁.subtype ↔
        x ∈ C₁ ∧ z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧
      Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 4 × (Fin 4 → ZMod 2)))) := by
  classical
  have hb₁ord := orderOf_ptB₁ he hb φ hzC hz
  have hb₁ne : ptB₁ he hb φ hzC hz ≠ 1 := fun h => by
    rw [h, orderOf_one] at hb₁ord
    exact absurd hb₁ord (by norm_num)
  have hAC : 𝒜₁ ≤ C₁ := fun a ha => by
    have h : a ∈ C₁ ⊓ ℬ₁ := by
      rw [hC₁B]
      exact ha
    exact (mem_inf.1 h).1
  have hrV : (OddQuadraticFive.rV : 𝔼 × ZMod 2) = ((0 : 𝔼), (1 : ZMod 2)) := rfl
  have hpt : ∀ t : ZMod 2, ptHom he hb φ hzC hz (Multiplicative.ofAdd (t • OddQuadraticFive.rV,
      (0 : ZMod 2))) = ptB₁ he hb φ hzC hz ^ t.val := by
    intro t
    rcases zmod_two_eq_zero_or_eq_one t with rfl | rfl
    · rw [zero_smul, Prod.mk_zero_zero, ofAdd_zero, map_one, ZMod.val_zero, pow_zero]
    · rw [one_smul, ZMod.val_one, pow_one]
      rfl
  have hβ : β = ε := by
    have h := hsq e₀ he₀C
    rw [he₀sq, he₀τ] at h
    have hq : OddQuadraticFive.qV (ptQuad e) (((0 : 𝔼), (1 : ZMod 2))) = 1 := by
      simp [OddQuadraticFive.qV]
    rw [hq, mul_one, hpt] at h
    rcases zmod_two_eq_zero_or_eq_one β with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_eq_one ε with rfl | rfl
    · rfl
    · rw [ZMod.val_one, pow_one, ZMod.val_zero, pow_zero] at h
      exact absurd h hb₁ne
    · rw [ZMod.val_one, pow_one, ZMod.val_zero, pow_zero] at h
      exact absurd h.symm hb₁ne
    · rfl
  subst hβ
  set s : 𝔼 × ZMod 2 → G := fun v => ptHom he hb φ hzC hz (Multiplicative.ofAdd
    ((β * OddQuadraticFive.qV (ptQuad e) v) • OddQuadraticFive.rV, 0)) with hs
  have hsI : ∀ v, s v ∈ zpowers (ptB₁ he hb φ hzC hz) := fun v => by
    rw [hs]
    simp only
    rw [hpt]
    exact pow_mem (mem_zpowers _) _
  have hs_mul : ∀ v w : 𝔼 × ZMod 2, s (v + w) = s v * s w * ptHom he hb φ hzC hz
      (Multiplicative.ofAdd ((β * b (v.1 : V) (w.1 : V)) • OddQuadraticFive.rV, 0)) := by
    intro v w
    have hvec : (((β * OddQuadraticFive.qV (ptQuad e) (v + w)) • OddQuadraticFive.rV,
        (0 : ZMod 2)) : (𝔼 × ZMod 2) × ZMod 2) =
        ((β * OddQuadraticFive.qV (ptQuad e) v) • OddQuadraticFive.rV, (0 : ZMod 2)) +
          ((β * OddQuadraticFive.qV (ptQuad e) w) • OddQuadraticFive.rV, (0 : ZMod 2)) +
          ((β * b (v.1 : V) (w.1 : V)) • OddQuadraticFive.rV, (0 : ZMod 2)) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        rw [qV_add he, mul_add, mul_add, add_smul, add_smul]
      · simp only [Prod.snd_add, add_zero]
    simp only [hs]
    rw [← map_mul, ← map_mul, ← ofAdd_add, ← ofAdd_add, ← hvec]
  have hIcen : ∀ i ∈ zpowers (ptB₁ he hb φ hzC hz), ∀ c ∈ C₁, i * c = c * i := by
    intro i hi c hc
    have hiA : i ∈ 𝒜₁ := by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hi
      refine zpow_mem ?_ n
      rw [ptB₁, ptHom_pt]
      exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
    refine hEc i (hAC hiA) ?_ c hc
    have h1 : i⁻¹ * z * i = z := by
      have h2 := hτz i (hAC hiA)
      rw [(hτker i (hAC hiA)).2 hiA, Prod.mk_zero_zero, ofAdd_zero, map_one] at h2
      calc i⁻¹ * z * i = z * (z⁻¹ * i⁻¹ * z * i) := by group
        _ = z := by rw [h2, mul_one]
    rw [h1, inv_mul_cancel]
    exact one_mem _
  have hcomm : ∀ c ∈ C₁, ∀ d ∈ C₁, c⁻¹ * d⁻¹ * c * d = ptHom he hb φ hzC hz
      (Multiplicative.ofAdd ((β * b ((τ₁ c).1 : V) ((τ₁ d).1 : V)) • OddQuadraticFive.rV, 0)) := by
    intro c hc d hd
    have hk : c⁻¹ * d⁻¹ * c * d ∈ zpowers (ptB₁ he hb φ hzC hz) := by
      have h : c⁻¹ * d⁻¹ * c * d = ⁅c⁻¹, d⁻¹⁆ := by
        rw [commutatorElement_def, inv_inv, inv_inv]
      rw [h]
      exact hCC (commutator_mem_commutator (inv_mem hc) (inv_mem hd))
    have h1 := mul_sq_eq_of_comm (hIcen _ hk c hc)
    rw [hsq (d * c) (mul_mem hd hc), hsq d hd, hsq c hc, hτmul d hd c hc] at h1
    change s (τ₁ d + τ₁ c) = s (τ₁ d) * s (τ₁ c) * (c⁻¹ * d⁻¹ * c * d) at h1
    rw [hs_mul] at h1
    have h2 := mul_left_cancel h1
    rw [← h2]
    have hsym : b ((τ₁ d).1 : V) ((τ₁ c).1 : V) = b ((τ₁ c).1 : V) ((τ₁ d).1 : V) := by
      rw [← hb.neg_eq ((τ₁ c).1 : V) ((τ₁ d).1 : V)]
      exact OddQuadraticFive.zmod2_neg _
    rw [hsym]
  have hE : Module.finrank (ZMod 2) 𝔼 = 4 := finrank_pairOrth_eq he hb hnd
  have hnd' : (b.restrict 𝔼).Nondegenerate :=
    hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd
  refine ⟨hsq, hcomm, fun h0 => ?_, fun h1 => ?_⟩
  ·
    subst h0
    have hsq1 : ∀ c ∈ C₁, c ^ 2 = 1 := fun c hc => by
      rw [hsq c hc, zero_mul, zero_smul, Prod.mk_zero_zero, ofAdd_zero, map_one]
    exact ⟨hsq1, fun c hc d hd => comm_of_sq_eq_one hsq1 hc hd⟩
  ·
    subst h1
    have hb₁C : ptB₁ he hb φ hzC hz ∈ C₁ := by
      apply hAC
      rw [ptB₁, ptHom_pt]
      exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
    have hE₂ne : ptE₂ he ≠ 0 := fun h => by
      have h1 := congrArg Subtype.val h
      exact e.ne_zero _ h1
    obtain ⟨w, hw⟩ : ∃ w : 𝔼, b (ptE₂ he : V) (w : V) = 1 := by
      by_contra hne
      push Not at hne
      apply hE₂ne
      refine hnd'.1 _ fun w => ?_
      rcases zmod_two_eq_zero_or_eq_one ((b.restrict 𝔼) (ptE₂ he) w) with h | h
      · exact h
      · exact absurd h (hne w)
    refine ⟨le_antisymm hCC ?_, le_antisymm hsq₀ ?_, fun x => ?_, ?_⟩
    · obtain ⟨c, hc, hcv⟩ := hτsurj (ptE₂ he, 0)
      obtain ⟨d, hd, hdv⟩ := hτsurj (w, 0)
      have h := hcomm c hc d hd
      rw [hcv, hdv] at h
      change c⁻¹ * d⁻¹ * c * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd
        ((1 * b (ptE₂ he : V) (w : V)) • OddQuadraticFive.rV, 0)) at h
      rw [hw, mul_one, one_smul] at h
      rw [zpowers_le]
      have h2 : ptB₁ he hb φ hzC hz = ⁅c⁻¹, d⁻¹⁆ := by
        rw [commutatorElement_def, inv_inv, inv_inv, h]
        rfl
      rw [h2]
      exact commutator_mem_commutator (inv_mem hc) (inv_mem hd)
    · rw [zpowers_le]
      have h : ptB₁ he hb φ hzC hz = e₀ ^ 2 := by
        rw [he₀sq, ZMod.val_one, pow_one]
      rw [h]
      exact subset_closure ⟨e₀, he₀C, rfl⟩
    · rw [mem_map_center_subtype_iff]
      constructor
      · rintro ⟨hxC, hxZ⟩
        refine ⟨hxC, ?_⟩
        have hb0 : ∀ v : 𝔼, b ((τ₁ x).1 : V) (v : V) = 0 := by
          intro v
          obtain ⟨d, hd, hdv⟩ := hτsurj (v, 0)
          have h := hcomm x hxC d hd
          have h1 : x⁻¹ * d⁻¹ * x * d = 1 := by
            have h2 := hxZ d hd
            calc x⁻¹ * d⁻¹ * x * d = x⁻¹ * d⁻¹ * (d * x) := by rw [h2]; group
              _ = 1 := by group
          rw [h1, hdv, one_mul] at h
          rcases zmod_two_eq_zero_or_eq_one (b ((τ₁ x).1 : V) (v : V)) with h3 | h3
          · exact h3
          · exfalso
            rw [h3, one_smul] at h
            exact hb₁ne h.symm
        have hx0 : (τ₁ x).1 = 0 := hnd'.1 _ hb0
        have h := hτz x hxC
        have h1 : z⁻¹ * (x⁻¹ * z * x) = ptHom he hb φ hzC hz (Multiplicative.ofAdd
            (((0 : 𝔼), (τ₁ x).2), 0)) := by
          rw [← hx0, ← h]
          group
        rw [h1]
        rcases zmod_two_eq_zero_or_eq_one (τ₁ x).2 with h2 | h2
        · rw [h2, Prod.mk_zero_zero, Prod.mk_zero_zero, ofAdd_zero, map_one]
          exact one_mem _
        · rw [h2]
          exact mem_zpowers _
      · rintro ⟨hxC, hxI⟩
        exact ⟨hxC, fun c hc => (hEc x hxC hxI c hc).symm⟩
    ·
      set Z := (center C₁).map C₁.subtype with hZ
      have hmemZ : ∀ x : G, x ∈ Z ↔ x ∈ C₁ ∧ z⁻¹ * (x⁻¹ * z * x) ∈
          zpowers (ptB₁ he hb φ hzC hz) := fun x => by
        rw [hZ, mem_map_center_subtype_iff]
        constructor
        · rintro ⟨hxC, hxZ⟩
          refine ⟨hxC, ?_⟩
          have hb0 : ∀ v : 𝔼, b ((τ₁ x).1 : V) (v : V) = 0 := by
            intro v
            obtain ⟨d, hd, hdv⟩ := hτsurj (v, 0)
            have h := hcomm x hxC d hd
            have h1 : x⁻¹ * d⁻¹ * x * d = 1 := by
              have h2 := hxZ d hd
              calc x⁻¹ * d⁻¹ * x * d = x⁻¹ * d⁻¹ * (d * x) := by rw [h2]; group
                _ = 1 := by group
            rw [h1, hdv, one_mul] at h
            rcases zmod_two_eq_zero_or_eq_one (b ((τ₁ x).1 : V) (v : V)) with h3 | h3
            · exact h3
            · exfalso
              rw [h3, one_smul] at h
              exact hb₁ne h.symm
          have hx0 : (τ₁ x).1 = 0 := hnd'.1 _ hb0
          have h := hτz x hxC
          have h1 : z⁻¹ * (x⁻¹ * z * x) = ptHom he hb φ hzC hz (Multiplicative.ofAdd
              (((0 : 𝔼), (τ₁ x).2), 0)) := by
            rw [← hx0, ← h]
            group
          rw [h1]
          rcases zmod_two_eq_zero_or_eq_one (τ₁ x).2 with h2 | h2
          · rw [h2, Prod.mk_zero_zero, Prod.mk_zero_zero, ofAdd_zero, map_one]
            exact one_mem _
          · rw [h2]
            exact mem_zpowers _
        · rintro ⟨hxC, hxI⟩
          exact ⟨hxC, fun c hc => (hEc x hxC hxI c hc).symm⟩
      have hZcard : Nat.card Z = 64 := by
        have hset : (Z : Set G) = (C₁ : Set G) ∩ {d | d ∈ D₁ ∧
            z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} := by
          ext x
          rw [SetLike.mem_coe, hmemZ]
          exact ⟨fun h => ⟨h.1, hC₁D h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
        rw [← hEcard, ← hset, SetLike.coe_sort_coe]
      have he₀4 : e₀ ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, he₀sq, ZMod.val_one, pow_one, ← hb₁ord,
          pow_orderOf_eq_one]
      set bas := Module.finBasisOfFinrankEq (ZMod 2) 𝔼 hE with hbas
      set a : (Fin 4 → ZMod 2) → G := fun v =>
        ptHom he hb φ hzC hz (Multiplicative.ofAdd ((bas.equivFun.symm v, 0), 0)) with ha
      have haA : ∀ v, a v ∈ 𝒜₁ := fun v => by
        rw [ha]
        simp only
        rw [ptHom_pt]
        exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
      have ha_mul : ∀ v v', a (v + v') = a v * a v' := fun v v' => by
        simp only [ha]
        rw [← map_mul, ← ofAdd_add, map_add, Prod.mk_add_mk, Prod.mk_add_mk]
        simp only [add_zero]
      have haZ : ∀ v, a v ∈ Z := fun v => by
        rw [hmemZ]
        refine ⟨hAC (haA v), ?_⟩
        have h := hτz (a v) (hAC (haA v))
        rw [(hτker _ (hAC (haA v))).2 (haA v), Prod.mk_zero_zero, ofAdd_zero, map_one] at h
        have h1 : z⁻¹ * ((a v)⁻¹ * z * a v) = 1 := by
          rw [← h]
          group
        rw [h1]
        exact one_mem _
      have he₀Z : e₀ ∈ Z := by
        rw [hmemZ]
        refine ⟨he₀C, ?_⟩
        have h := hτz e₀ he₀C
        rw [he₀τ] at h
        have h1 : z⁻¹ * (e₀⁻¹ * z * e₀) = ptB₁ he hb φ hzC hz := by
          rw [ptB₁, ← h]
          group
        rw [h1]
        exact mem_zpowers _
      have hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
        (hEc x ((hmemZ x).1 hx).1 ((hmemZ x).1 hx).2 y ((hmemZ y).1 hy).1)
      let Φ₀ : Multiplicative (ZMod 4 × (Fin 4 → ZMod 2)) →* G :=
        { toFun := fun x => e₀ ^ (Multiplicative.toAdd x).1.val * a (Multiplicative.toAdd x).2
          map_one' := by
            change e₀ ^ (0 : ZMod 4).val * a 0 = 1
            rw [ZMod.val_zero, pow_zero, one_mul, ha]
            simp only [map_zero, Prod.mk_zero_zero, ofAdd_zero, map_one]
          map_mul' := fun x y => by
            change e₀ ^ ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1).val *
              a ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2) =
              e₀ ^ (Multiplicative.toAdd x).1.val * a (Multiplicative.toAdd x).2 *
                (e₀ ^ (Multiplicative.toAdd y).1.val * a (Multiplicative.toAdd y).2)
            rw [ZMod.val_add, ← pow_eq_pow_mod _ he₀4, pow_add, ha_mul]
            have hc : a (Multiplicative.toAdd x).2 * e₀ ^ (Multiplicative.toAdd y).1.val =
                e₀ ^ (Multiplicative.toAdd y).1.val * a (Multiplicative.toAdd x).2 :=
              hZc _ (haZ _) _ (pow_mem he₀Z _)
            calc e₀ ^ (Multiplicative.toAdd x).1.val * e₀ ^ (Multiplicative.toAdd y).1.val *
                (a (Multiplicative.toAdd x).2 * a (Multiplicative.toAdd y).2) =
                e₀ ^ (Multiplicative.toAdd x).1.val * (e₀ ^ (Multiplicative.toAdd y).1.val *
                  a (Multiplicative.toAdd x).2) * a (Multiplicative.toAdd y).2 := by group
              _ = e₀ ^ (Multiplicative.toAdd x).1.val * (a (Multiplicative.toAdd x).2 *
                  e₀ ^ (Multiplicative.toAdd y).1.val) * a (Multiplicative.toAdd y).2 := by
                rw [hc]
              _ = _ := by group }
      have hΦZ : ∀ x, Φ₀ x ∈ Z := fun x => mul_mem (pow_mem he₀Z _) (haZ _)
      have he₀A : e₀ ∉ 𝒜₁ := fun h => by
        have h1 := (hτker e₀ he₀C).2 h
        rw [he₀τ] at h1
        have h2 : (1 : ZMod 2) = 0 := congrArg Prod.snd h1
        exact absurd h2 (by decide)
      have hΦinj : Function.Injective Φ₀ := by
        rw [injective_iff_map_eq_one]
        intro x hx
        obtain ⟨⟨k, v⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = x := ⟨Multiplicative.toAdd x, rfl⟩
        change e₀ ^ k.val * a v = 1 at hx
        have hav : (a v)⁻¹ ∈ 𝒜₁ := inv_mem (haA v)
        have hk : e₀ ^ k.val = (a v)⁻¹ := eq_inv_of_mul_eq_one_left hx
        fin_cases k
        · change e₀ ^ 0 * a v = 1 at hx
          rw [pow_zero, one_mul, ha] at hx
          simp only at hx
          rw [← map_one (ptHom he hb φ hzC hz), ← ofAdd_zero] at hx
          have h1 := congrArg (fun p => p.1.1) (Multiplicative.ofAdd.injective
            (ptHom_injective he hb φ hzC hz hinf hx))
          have h2 : v = 0 := bas.equivFun.symm.injective (by simpa using h1)
          rw [h2]
          rfl
        · exfalso
          change e₀ ^ 1 = (a v)⁻¹ at hk
          rw [pow_one] at hk
          exact he₀A (hk ▸ hav)
        · exfalso
          change e₀ ^ 2 * a v = 1 at hx
          rw [he₀sq, ZMod.val_one, pow_one, ha] at hx
          simp only at hx
          rw [ptB₁, ← map_mul, ← ofAdd_add, ← map_one (ptHom he hb φ hzC hz), ← ofAdd_zero] at hx
          have h1 := congrArg (fun p => p.1.2) (Multiplicative.ofAdd.injective
            (ptHom_injective he hb φ hzC hz hinf hx))
          exact absurd h1 (by simp)
        · exfalso
          change e₀ ^ 3 = (a v)⁻¹ at hk
          have h3 : e₀ = (e₀ ^ 3)⁻¹ := by
            rw [inv_eq_of_mul_eq_one_left]
            rw [← pow_succ', he₀4]
          rw [hk, inv_inv] at h3
          exact he₀A (h3 ▸ haA v)
      let Φ : Multiplicative (ZMod 4 × (Fin 4 → ZMod 2)) →* Z := Φ₀.codRestrict Z hΦZ
      have hΦbij : Function.Bijective Φ := by
        refine Function.Injective.bijective_of_nat_card_le (fun x y h => hΦinj ?_) ?_
        · exact congrArg Subtype.val h
        · rw [hZcard, Nat.card_eq_fintype_card]
          rfl
      exact ⟨((center C₁).equivMapOfInjective C₁.subtype C₁.subtype_injective).trans
        (MulEquiv.ofBijective Φ hΦbij).symm⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
