module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightExtraspecial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒟₁" => ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
local notation "τ₁" => ptTr hzC hsup hinf hz hb hnd hV φ he halt
local notation "θD" => ptθD hzC hsup hinf hz hb hnd hV φ he halt
local notation "𝐛₁" => ptB₁ hzC hz hb φ he

theorem exists_C :
    ∃ C : Subgroup 𝒟₁, OddQuadraticFive.subA θD ≤ C ∧ OddQuadraticFive.zz θD ∉ C ∧
      (∀ d, d ∈ C ∨ d * OddQuadraticFive.zz θD ∈ C) ∧
      (∀ c ∈ C, ∀ c' ∈ C, OddQuadraticFive.om θD c c' = 0) ∧
      (∀ w : 𝔼, ∃ c ∈ C, Multiplicative.toAdd (τ₁ c) = w) := by
  classical
  set Lb := ptLabels hzC hsup hinf hz hb hnd hV φ he halt with hLb
  have hb' := restrict_isAlt (e := e) hb
  have hfaith := ptLabels_faith hzC hsup hinf hz hb hnd hV φ he halt
  set eb := Module.finBasisOfFinrankEq (ZMod 2) 𝔼 (finrank_pairOrth_eq he hb hnd) with heb
  obtain ⟨y, -, hyτ, -, hyω⟩ := exists_split_lifts hzC hsup hinf hz hb hnd hV φ he halt eb
  have hcomm := commutator_eq_subA hzC hsup hinf hz hb hnd hV φ he halt
  have hof : ∀ x : 𝒟₁, Abelianization.of x = 1 ↔ x ∈ OddQuadraticFive.subA θD := fun x => by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of, hcomm]
  set Y : Multiplicative 𝔼 → 𝒟₁ := fun w =>
    y 0 ^ (eb.repr (Multiplicative.toAdd w) 0).val *
      y 1 ^ (eb.repr (Multiplicative.toAdd w) 1).val *
        y 2 ^ (eb.repr (Multiplicative.toAdd w) 2).val *
          y 3 ^ (eb.repr (Multiplicative.toAdd w) 3).val with hYdef
  have hY1 : Y 1 = 1 := by simp [hYdef]
  have hYτ : ∀ w, τ₁ (Y w) = w := by
    intro w
    apply Multiplicative.toAdd.injective
    simp only [hYdef, map_mul, map_pow, toAdd_mul, toAdd_pow, hyτ,
      OddQuadraticFive.val_nsmul_eq_smul]
    conv_rhs => rw [← eb.sum_repr (Multiplicative.toAdd w), Fin.sum_univ_four]
  have hsq : ∀ g : 𝒟₁, Abelianization.of g ^ 2 = 1 := fun g => by
    rw [← map_pow, hof]
    exact Lb.sq_mem_subA hb' hfaith g
  set Ybar : Multiplicative 𝔼 →* Abelianization 𝒟₁ :=
    { toFun := fun w => Abelianization.of (Y w)
      map_one' := by rw [hY1, map_one]
      map_mul' := by
        intro w₁ w₂
        simp only [hYdef, map_mul, map_pow, toAdd_mul, map_add, Finsupp.add_apply,
          OddQuadraticFive.pow_val_add_of_sq (hsq _)]
        ac_rfl } with hYbar
  set C : Subgroup 𝒟₁ := MonoidHom.eqLocus Abelianization.of (Ybar.comp τ₁) with hC
  have hmemC : ∀ d, d ∈ C ↔ (Y (τ₁ d))⁻¹ * d ∈ OddQuadraticFive.subA θD := fun d => by
    rw [← hof, map_mul, map_inv, inv_mul_eq_one, eq_comm]
    exact Iff.rfl
  have hYB : ∀ d, (Y (τ₁ d))⁻¹ * d ∈ (ptSub φ z hb e).subgroupOf 𝒟₁ := fun d => by
    rw [mem_B_iff, map_mul, map_inv, hYτ, inv_mul_cancel]
  have hYC : ∀ w, Y w ∈ C := fun w => by
    rw [hmemC, hYτ, inv_mul_cancel]
    exact one_mem _
  have hAC : ∀ x ∈ OddQuadraticFive.subA θD, x ∈ C := fun x hx => by
    rw [hmemC, (mem_B_iff hzC hsup hinf hz hb hnd hV φ he halt x).1
      (OddQuadraticFive.subA_le θD hx), hY1, inv_one, one_mul]
    exact hx
  have hTω : ∀ g ∈ Set.range y, ∀ h ∈ Set.range y, OddQuadraticFive.om θD g h = 0 := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hyω i j
  have hy' : ∀ i, y i ∈ Subgroup.closure (Set.range y) := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  have hYT : ∀ w, Y w ∈ Subgroup.closure (Set.range y) := fun w =>
    mul_mem (mul_mem (mul_mem (pow_mem (hy' 0) _) (pow_mem (hy' 1) _)) (pow_mem (hy' 2) _))
      (pow_mem (hy' 3) _)
  have hωY : ∀ w w', OddQuadraticFive.om θD (Y w) (Y w') = 0 := fun w w' =>
    Lb.om_eq_zero_of_mem_closure hb' hfaith hTω (hYT w) (hYT w')
  have hdec : ∀ c ∈ C, ∃ g ∈ OddQuadraticFive.subA θD, c = Y (τ₁ c) * g := fun c hc =>
    ⟨_, (hmemC c).1 hc, by group⟩
  refine ⟨C, hAC, fun hz' => ?_, fun d => ?_, fun c hc c' hc' => ?_,
    fun w => ⟨Y (Multiplicative.ofAdd w), hYC _, by rw [hYτ, toAdd_ofAdd]⟩⟩
  · rw [hmemC, ptTr_zz, hY1, inv_one, one_mul] at hz'
    exact OddQuadraticFive.zz_not_mem_subA θD hz'
  · rcases OddQuadraticFive.mem_subA_or_mul_zz θD (hYB d) with h | h
    · exact Or.inl ((hmemC d).2 h)
    · refine Or.inr ((hmemC _).2 ?_)
      rw [map_mul, ptTr_zz, mul_one, ← mul_assoc]
      exact h
  · obtain ⟨g, hg, hceq⟩ := hdec c hc
    obtain ⟨g', hg', hceq'⟩ := hdec c' hc'
    rw [hceq, hceq', Lb.om_mul_of_mem_subA hb' hfaith _ _ hg, Lb.om_mul_right hb' hfaith, hωY,
      Lb.om_of_mem_subA_right hb' hfaith hg', add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem trMap_ut (a u : 𝔼) (t : ZMod 2) :
    ((u, t), 0) + trMap a (((u, t), 0) : (𝔼 × ZMod 2) × ZMod 2) = ((0, b u a), 0) := by
  rw [trMap_apply]
  simp only [Prod.mk_add_mk, zero_smul, add_zero, zero_mul]
  rw [add_self_eq_zero_zmod_two, ← add_assoc, add_self_eq_zero_zmod_two, zero_add]

theorem comm_pt₁_pt₁' (d : 𝒟₁) (u : 𝔼) (t : ZMod 2) :
    (pt₁ hzC hz hb φ he ((u, t), 0))⁻¹ * (d : G)⁻¹ * pt₁ hzC hz hb φ he ((u, t), 0) * d =
      pt₁ hzC hz hb φ he ((0, b u (Multiplicative.toAdd (τ₁ d) : 𝔼)), 0) := by
  rw [mul_assoc _ (d : G)⁻¹, mul_assoc, inv_mul_pt₁_mul hzC hsup hinf hz hb hnd hV φ he halt,
    pt₁_inv, ← pt₁_add, trMap_ut]

theorem coe_comm_mem_ptI {d d' : 𝒟₁} (h : OddQuadraticFive.om θD d d' = 0) :
    ((d⁻¹ * d'⁻¹ * d * d' : 𝒟₁) : G) ∈ zpowers 𝐛₁ := by
  obtain ⟨v, hv⟩ := (ptLabels hzC hsup hinf hz hb hnd hV φ he halt).comm_mem_subA
    (restrict_isAlt hb) (ptLabels_faith hzC hsup hinf hz hb hnd hV φ he halt) d d'
  have hom : OddQuadraticFive.om θD d d' = v.1 := by
    rw [OddQuadraticFive.om, ← hv, OddQuadraticFive.cB_bv]
  rw [← hv, coe_bv_ptθD, mem_ptI_iff_pt₁ hzC hinf hz hb φ he]
  exact ⟨hom ▸ h, rfl⟩

include hsup hinf hnd hV halt in
theorem mul_comm_of_mem_ptI {i : G} (hi : i ∈ zpowers 𝐛₁) {g : G} (hg : g ∈ 𝒩₁) :
    g * i = i * g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hi
  have h := conj_ptB₁ hzC hsup hinf hz hb hnd hV φ he halt ⟨g, hg⟩
  rw [mul_inv_eq_iff_eq_mul] at h
  exact (Commute.zpow_right h k)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptB₁_mem_ptA : 𝐛₁ ∈ 𝒜₁ :=
  pt₁_mem_ptA hzC hz hb φ he _

theorem exists_extraspecial :
    ∃ C₁ : Subgroup G, C₁ ≤ 𝒟₁ ∧ Nat.card C₁ = 512 ∧
      ((zpowers z : Set G) * (C₁ : Set G)) = 𝒟₁ ∧ C₁ ⊓ ptSub φ z hb e = 𝒜₁ ∧
      (∀ g ∈ 𝒩₁, ∀ c ∈ C₁, g * c * g⁻¹ ∈ C₁) ∧
      ⁅C₁, C₁⁆ = zpowers 𝐛₁ ∧ closure {x | ∃ c ∈ C₁, c ^ 2 = x} = zpowers 𝐛₁ ∧
      (center C₁).map C₁.subtype = zpowers 𝐛₁ ∧
      (∀ F : Subgroup G, zpowers 𝐛₁ ≤ F → F ≤ 𝒟₁ → Nat.card F = 512 →
        (∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ * y⁻¹ ∈ zpowers 𝐛₁) → F = C₁) ∧
      (∀ x ∈ 𝒟₁, x ∉ C₁ → ∀ f ∈ C₁, x⁻¹ * f⁻¹ * x * f ∈ zpowers 𝐛₁ → f ∈ 𝒜₁) := by
  classical
  obtain ⟨C, hAC, hzC', hind, hω, hlab⟩ := exists_C hzC hsup hinf hz hb hnd hV φ he halt
  set Lb := ptLabels hzC hsup hinf hz hb hnd hV φ he halt with hLb
  have hb' := restrict_isAlt (e := e) hb
  have hfaith := ptLabels_faith hzC hsup hinf hz hb hnd hV φ he halt
  set C₁ := C.map (𝒟₁).subtype with hC₁
  have hDN := ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt
  have hzz : ((OddQuadraticFive.zz θD : 𝒟₁) : G) = z := by
    rw [OddQuadraticFive.zz, coe_bv_ptθD, pt₁, ptHom_z]
  have hmemC₁ : ∀ {x : G}, x ∈ C₁ ↔ ∃ h : x ∈ 𝒟₁, (⟨x, h⟩ : 𝒟₁) ∈ C := fun {x} =>
    ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨y.2, hy⟩, fun ⟨h, hx⟩ => ⟨⟨x, h⟩, hx, rfl⟩⟩
  have hidx : C.index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨OddQuadraticFive.zz θD, fun d => ?_⟩
    rcases hind d with h | h
    · exact Or.inr ⟨h, fun h' => hzC' (by simpa using mul_mem (inv_mem h) h')⟩
    · exact Or.inl ⟨h, fun hd => hzC' (by simpa using mul_mem (inv_mem hd) h)⟩
  have hCn : C.Normal := normal_of_index_eq_two hidx
  have hcardC : Nat.card C = 512 := by
    have h := C.card_mul_index
    rw [hidx, card_ptD₁] at h
    omega
  have hAB : ∀ x : 𝒟₁, x ∈ C → x ∈ (ptSub φ z hb e).subgroupOf 𝒟₁ →
      x ∈ OddQuadraticFive.subA θD := by
    intro x hxC hxB
    rcases OddQuadraticFive.mem_subA_or_mul_zz θD hxB with h | h
    · exact h
    · exfalso
      apply hzC'
      have := mul_mem (inv_mem hxC) (hAC h)
      rwa [inv_mul_cancel_left] at this
  have hA₁C₁ : 𝒜₁ ≤ C₁ := by
    rw [← map_subA hzC hsup hinf hz hb hnd hV φ he halt]
    exact map_mono hAC
  have hb₁C₁ : 𝐛₁ ∈ C₁ := hA₁C₁ (ptB₁_mem_ptA hzC hz hb φ he)
  have hcommC : ∀ x ∈ C₁, ∀ y ∈ C₁, x * y * x⁻¹ * y⁻¹ ∈ zpowers 𝐛₁ := by
    intro x hx y hy
    obtain ⟨hxD, hxC⟩ := hmemC₁.1 hx
    obtain ⟨hyD, hyC⟩ := hmemC₁.1 hy
    have h := coe_comm_mem_ptI hzC hsup hinf hz hb hnd hV φ he halt
      (hω _ (inv_mem hxC) _ (inv_mem hyC))
    simpa only [inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv] using h
  have hcomm₁ : ⁅C₁, C₁⁆ = zpowers 𝐛₁ := by
    apply le_antisymm
    · rw [commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      exact hcommC x hx y hy
    · rw [zpowers_le]
      obtain ⟨c, hc, hca⟩ := hlab (ptF₂ he)
      have h := comm_pt₁_pt₁ hzC hsup hinf hz hb hnd hV φ he halt c (ptE₂ he)
      rw [hca, show b (ptE₂ he) (ptF₂ he) = 1 from restrict_ptE₂_ptF₂ he] at h
      rw [ptB₁_eq, ← h]
      have hu : pt₁ hzC hz hb φ he ((ptE₂ he, 0), 0) ∈ C₁ :=
        hA₁C₁ (pt₁_mem_ptA hzC hz hb φ he _)
      have hcC₁ : (c : G) ∈ C₁ := ⟨c, hc, rfl⟩
      have h2 := commutator_mem_commutator (inv_mem hu) (inv_mem hcC₁)
      rwa [commutatorElement_def, inv_inv, inv_inv] at h2
  have hcenter : (center C₁).map C₁.subtype = zpowers 𝐛₁ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxD, hxC⟩ := hmemC₁.1 x.2
      have hxcomm : ∀ c ∈ C₁, (x : G) * c = c * x := fun c hc =>
        (congrArg Subtype.val (mem_center_iff.1 hx ⟨c, hc⟩)).symm
      set d : 𝒟₁ := ⟨x, hxD⟩ with hd
      have ha : Multiplicative.toAdd (τ₁ d) = 0 := by
        refine (restrict_nondegenerate hb hnd he).1 _ fun u => ?_
        have hu : pt₁ hzC hz hb φ he ((u, 0), 0) ∈ C₁ := hA₁C₁ (pt₁_mem_ptA hzC hz hb φ he _)
        have h1 := comm_pt₁_pt₁ hzC hsup hinf hz hb hnd hV φ he halt d u
        have h2 : (pt₁ hzC hz hb φ he ((u, 0), 0))⁻¹ * (d : G)⁻¹ *
            pt₁ hzC hz hb φ he ((u, 0), 0) * d = 1 := by
          change (pt₁ hzC hz hb φ he ((u, 0), 0))⁻¹ * (x : G)⁻¹ *
            pt₁ hzC hz hb φ he ((u, 0), 0) * x = 1
          calc (pt₁ hzC hz hb φ he ((u, 0), 0))⁻¹ * (x : G)⁻¹ *
                pt₁ hzC hz hb φ he ((u, 0), 0) * x =
              (pt₁ hzC hz hb φ he ((u, 0), 0))⁻¹ * ((x : G)⁻¹ *
                (pt₁ hzC hz hb φ he ((u, 0), 0) * x)) := by group
            _ = 1 := by rw [← hxcomm _ hu]; group
        rw [h2, ← pt₁_zero hzC hz hb φ he] at h1
        have h4 := congrArg (fun v : (𝔼 × ZMod 2) × ZMod 2 => v.1.2)
          (pt₁_injective hzC hinf hz hb φ he h1)
        change (0 : ZMod 2) = b u (Multiplicative.toAdd (τ₁ d) : 𝔼) at h4
        change b (Multiplicative.toAdd (τ₁ d) : 𝔼) u = 0
        rw [BinarySymplecticTransvection.symm_apply hb]
        exact h4.symm
      have hdB : d ∈ (ptSub φ z hb e).subgroupOf 𝒟₁ := by
        rw [mem_B_iff]
        exact Multiplicative.toAdd.injective ha
      have hdA := hAB d hxC hdB
      obtain ⟨⟨w, t⟩, hwt⟩ := hdA
      have hx' : (x : G) = pt₁ hzC hz hb φ he ((w, t), 0) := by
        rw [← coe_bv_ptθD hzC hsup hinf hz hb hnd hV φ he halt, hwt]
      have hw : w = 0 := by
        refine (restrict_nondegenerate hb hnd he).1 _ fun a => ?_
        obtain ⟨c, hc, hca⟩ := hlab a
        have hcC₁ : (c : G) ∈ C₁ := ⟨c, hc, rfl⟩
        have h1 := comm_pt₁_pt₁' hzC hsup hinf hz hb hnd hV φ he halt c w t
        have h2 : (pt₁ hzC hz hb φ he ((w, t), 0))⁻¹ * (c : G)⁻¹ *
            pt₁ hzC hz hb φ he ((w, t), 0) * c = 1 := by
          rw [← hx']
          calc (x : G)⁻¹ * (c : G)⁻¹ * x * c = (x : G)⁻¹ * (c : G)⁻¹ * (x * c) := by group
            _ = 1 := by rw [hxcomm _ hcC₁]; group
        rw [h2, ← pt₁_zero hzC hz hb φ he, hca] at h1
        have h4 := congrArg (fun v : (𝔼 × ZMod 2) × ZMod 2 => v.1.2)
          (pt₁_injective hzC hinf hz hb φ he h1)
        exact h4.symm
      rw [Subgroup.coe_subtype, hx', hw, mem_ptI_iff_pt₁ hzC hinf hz hb φ he]
      exact ⟨rfl, rfl⟩
    · rw [zpowers_le]
      refine ⟨⟨𝐛₁, hb₁C₁⟩, mem_center_iff.2 fun c => Subtype.ext ?_, rfl⟩
      exact mul_comm_of_mem_ptI hzC hsup hinf hz hb hnd hV φ he halt (mem_zpowers _)
        (hDN (map_subtype_le _ c.2))
  have hsq : closure {x | ∃ c ∈ C₁, c ^ 2 = x} = zpowers 𝐛₁ := by
    apply le_antisymm
    · refine (closure_le _).2 ?_
      rintro _ ⟨c, hc, rfl⟩
      rw [← hcenter]
      refine ⟨⟨c ^ 2, pow_mem hc 2⟩, mem_center_iff.2 fun c' => Subtype.ext ?_, rfl⟩
      have hi := hcommC c hc c' c'.2
      have hiN : c * c' * c⁻¹ * (c' : G)⁻¹ ∈ zpowers 𝐛₁ := hi
      have hcen : ∀ g ∈ 𝒩₁, g * (c * c' * c⁻¹ * (c' : G)⁻¹) =
          (c * c' * c⁻¹ * (c' : G)⁻¹) * g := fun g hg =>
        mul_comm_of_mem_ptI hzC hsup hinf hz hb hnd hV φ he halt hiN hg
      have hi2 : (c * c' * c⁻¹ * (c' : G)⁻¹) ^ 2 = 1 := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hiN
        rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          ptB₁_eq, sq,
          ← pt₁_add, add_self_eq_zero_zmod_two, pt₁_zero, _root_.one_zpow]
      have hcN : c ∈ 𝒩₁ := hDN (map_subtype_le _ hc)
      have hc'N : (c' : G) ∈ 𝒩₁ := hDN (map_subtype_le _ c'.2)
      change (c' : G) * c ^ 2 = c ^ 2 * c'
      set i := c * c' * c⁻¹ * (c' : G)⁻¹ with hi_def
      have hcc' : c * c' = i * c' * c := by rw [hi_def]; group
      have hic : c * i = i * c := hcen c hcN
      have hii : i * i = 1 := by rw [← sq, hi2]
      symm
      calc c ^ 2 * c' = c * (c * c') := by rw [sq, mul_assoc]
        _ = c * (i * c' * c) := by rw [hcc']
        _ = (c * i) * c' * c := by group
        _ = (i * c) * c' * c := by rw [hic]
        _ = i * (c * c') * c := by group
        _ = i * (i * c' * c) * c := by rw [hcc']
        _ = (i * i) * c' * (c * c) := by group
        _ = c' * c ^ 2 := by rw [hii, one_mul, sq]
    · rw [← hcomm₁]
      exact OddQuadraticFive.commutator_le_closure_sq _
  have hcardC₁ : Nat.card C₁ = 512 := by
    rw [hC₁, card_map_of_injective (𝒟₁).subtype_injective, hcardC]
  have hinter : C₁ ⊓ ptSub φ z hb e = 𝒜₁ := by
    apply le_antisymm
    · rintro x ⟨hx, hxB⟩
      obtain ⟨hxD, hxC⟩ := hmemC₁.1 hx
      have h := hAB _ hxC (mem_subgroupOf.2 hxB)
      rw [← map_subA hzC hsup hinf hz hb hnd hV φ he halt]
      exact ⟨_, h, rfl⟩
    · exact le_inf hA₁C₁ (fun x hx => mem_sup_left hx)
  have hzD : z ∈ 𝒟₁ := ptSub_le_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
    (mem_sup_right (mem_zpowers z))
  have hprod : ((zpowers z : Set G) * (C₁ : Set G)) = 𝒟₁ := by
    ext d
    constructor
    · rintro ⟨t, ht, c, hc, rfl⟩
      exact mul_mem (zpowers_le.2 hzD ht) (map_subtype_le _ hc)
    · intro hd
      rcases hind ⟨d, hd⟩ with h | h
      · exact ⟨1, one_mem _, d, ⟨⟨d, hd⟩, h, rfl⟩, one_mul d⟩
      · have h' : OddQuadraticFive.zz θD * ⟨d, hd⟩ ∈ C := by
          have := hCn.conj_mem _ h (OddQuadraticFive.zz θD)
          simpa [mul_assoc] using this
        refine ⟨z⁻¹, inv_mem (mem_zpowers z), z * d, ⟨_, h', ?_⟩, by group⟩
        rw [Subgroup.coe_subtype, Subgroup.coe_mul, hzz]
  have hkey : ∀ x ∈ 𝒟₁, x ∉ C₁ → ∀ f ∈ C₁, x⁻¹ * f⁻¹ * x * f ∈ zpowers 𝐛₁ → f ∈ 𝒜₁ := by
    intro x hxD hxC f hfC h
    have hxz : (⟨x, hxD⟩ : 𝒟₁) * OddQuadraticFive.zz θD ∈ C :=
      (hind _).resolve_left fun h => hxC ⟨_, h, rfl⟩
    obtain ⟨hfD, hfC'⟩ := hmemC₁.1 hfC
    have hom : OddQuadraticFive.om θD ⟨x, hxD⟩ ⟨f, hfD⟩ = 0 := by
      obtain ⟨v, hv⟩ := Lb.comm_mem_subA hb' hfaith ⟨x, hxD⟩ ⟨f, hfD⟩
      have hv' : x⁻¹ * f⁻¹ * x * f = pt₁ hzC hz hb φ he (v, 0) := by
        have h1 := congrArg Subtype.val hv
        rw [coe_bv_ptθD] at h1
        exact h1.symm
      rw [hv', mem_ptI_iff_pt₁ hzC hinf hz hb φ he] at h
      rw [OddQuadraticFive.om, ← hv, OddQuadraticFive.cB_bv]
      exact h.1
    have hom' : OddQuadraticFive.om θD ⟨x, hxD⟩ ⟨f, hfD⟩ = (Lb.lab ⟨f, hfD⟩).1 := by
      have hx' : (⟨x, hxD⟩ : 𝒟₁) =
          (⟨x, hxD⟩ * OddQuadraticFive.zz θD) * OddQuadraticFive.zz θD := by
        rw [mul_assoc, OddQuadraticFive.zz, OddQuadraticFive.bv_mul_self, mul_one]
      rw [hx', Lb.om_mul_zz hb' hfaith, hω _ hxz _ hfC', zero_add]
    have hf0 : Multiplicative.toAdd (τ₁ ⟨f, hfD⟩) = 0 := hom'.symm.trans hom
    have hfB : (⟨f, hfD⟩ : 𝒟₁) ∈ (ptSub φ z hb e).subgroupOf 𝒟₁ := by
      rw [mem_B_iff]
      exact Multiplicative.toAdd.injective hf0
    rw [← map_subA hzC hsup hinf hz hb hnd hV φ he halt]
    exact ⟨_, hAB _ hfC' hfB, rfl⟩
  have huniq : ∀ F : Subgroup G, zpowers 𝐛₁ ≤ F → F ≤ 𝒟₁ → Nat.card F = 512 →
      (∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ * y⁻¹ ∈ zpowers 𝐛₁) → F = C₁ := by
    intro F _ hFD hcardF hFcomm
    by_contra hne
    have hFC : ¬ F ≤ C₁ := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge h (by rw [hcardF, hcardC₁]))
    obtain ⟨x, hxF, hxC⟩ := Set.not_subset.1 hFC
    have hinter' : F ⊓ C₁ ≤ 𝒜₁ := by
      rintro f ⟨hfF, hfC⟩
      refine hkey x (hFD hxF) hxC f hfC ?_
      have h := hFcomm _ (inv_mem hxF) _ (inv_mem hfF)
      rwa [inv_inv, inv_inv] at h
    have hcardI : Nat.card (C₁ ⊓ F : Subgroup G) ≤ 32 := by
      rw [inf_comm]
      calc Nat.card (F ⊓ C₁ : Subgroup G) ≤ Nat.card 𝒜₁ := Subgroup.card_le_of_le hinter'
        _ = 32 := (ptA_facts he hb hnd φ).2.2.1
    have hidxC₁ : C₁.relIndex 𝒟₁ = 2 := by
      have h : Nat.card C₁ * C₁.relIndex 𝒟₁ = Nat.card 𝒟₁ :=
        card_mul_relIndex_of_le (map_subtype_le C)
      rw [hcardC₁, card_ptD₁] at h
      omega
    have hidx' : (C₁ ⊓ F).relIndex F ≤ 2 := by
      have h1 := relIndex_inf_le (H := C₁) (K := F) (L := F)
      rw [relIndex_self, mul_one] at h1
      refine h1.trans ?_
      rw [← hidxC₁]
      exact relIndex_le_of_le_right hFD (by rw [hidxC₁]; norm_num)
    have h := card_mul_relIndex_of_le (inf_le_right : C₁ ⊓ F ≤ F)
    rw [hcardF] at h
    have : Nat.card (C₁ ⊓ F : Subgroup G) * (C₁ ⊓ F).relIndex F ≤ 32 * 2 :=
      Nat.mul_le_mul hcardI hidx'
    omega
  have hnorm : ∀ g ∈ 𝒩₁, ∀ c ∈ C₁, g * c * g⁻¹ ∈ C₁ := by
    intro g hg c hc
    have hF := huniq (C₁.map (MulAut.conj g).toMonoidHom) ?_ ?_ ?_ ?_
    · rw [← hF]
      exact ⟨c, hc, rfl⟩
    · rw [zpowers_le]
      refine ⟨𝐛₁, hb₁C₁, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact conj_ptB₁ hzC hsup hinf hz hb hnd hV φ he halt ⟨g, hg⟩
    · rintro _ ⟨c', hc', rfl⟩
      exact conj_mem_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt hg (map_subtype_le _ hc')
    · rw [card_map_of_injective (MulAut.conj g).injective, hcardC₁]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h := hcommC x hx y hy
      have e : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
          g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ := by group
      rw [e, mul_comm_of_mem_ptI hzC hsup hinf hz hb hnd hV φ he halt h hg, mul_inv_cancel_right]
      exact h
  exact ⟨C₁, map_subtype_le C, hcardC₁, hprod, hinter, hnorm, hcomm₁, hsq, hcenter, huniq, hkey⟩

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
