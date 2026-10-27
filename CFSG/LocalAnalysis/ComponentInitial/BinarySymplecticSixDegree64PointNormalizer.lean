module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64Point

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type*} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))

include he hnd in
theorem ptA_facts :
    𝒜₁ ≤ L ∧ IsElementaryAbelian 2 𝒜₁ ∧ Nat.card 𝒜₁ = 32 ∧
      centralizer (𝒜₁ : Set G) ⊓ L = 𝒜₁ ∧
      normalizer (𝒜₁ : Set G) ⊓ L = pullSub φ (vecStabilizer b (e (Sum.inl 0))) ∧
      pullSub φ (vecStabilizer b (e (Sum.inl 0))) =
        𝒜₁ ⊔ pullSub φ (pairStabilizer b (e (Sum.inl 0)) (e (Sum.inr 0))) := by
  have huf := bilin_f_u he
  refine ⟨pullSub_le φ _, isElementaryAbelian_pullSub φ (isElementaryAbelian_pointRadical hb),
    by rw [card_pullSub, card_pointRadical_eq hb he hnd], ?_, ?_, ?_⟩
  · rw [centralizer_pullSub_inf, centralizer_pointRadical hb hnd huf]
  · rw [normalizer_pullSub_inf, normalizer_pointRadical hb hnd huf]
  · rw [← pointRadical_sup_pairStabilizer hb huf, pullSub_eq_map, pullSub_eq_map, pullSub_eq_map,
      Subgroup.map_sup]

include he hnd hzC hinf hz in
theorem ptSub_facts :
    𝒜₁ ⊓ zpowers z = ⊥ ∧ IsElementaryAbelian 2 (ptSub φ z hb e) ∧
      Nat.card (ptSub φ z hb e) = 64 ∧ ptSub φ z hb e ⊓ L = 𝒜₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAL, hAe, hAc, -⟩ := ptA_facts he hb hnd φ
  have hzA : zpowers z ≤ centralizer (𝒜₁ : Set G) := fun t ht =>
    mem_centralizer_iff.2 fun a ha =>
      mem_centralizer_iff.1 (zpowers_le_centralizer hzC ht) a (hAL ha)
  have hAz : 𝒜₁ ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf hAL le_rfl
  have : IsElementaryAbelian 2 𝒜₁ := hAe
  have : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (sq_eq_one_of_orderOf hz)
  refine ⟨hAz, IsElementaryAbelian.sup_of_le_centralizer hzA, ?_, sup_inf_eq hzC hinf hAL⟩
  rw [card_sup_eq_mul hzA hAz, hAc, Nat.card_zpowers, hz]

include he hnd hzC hsup hinf hz in
theorem centralizer_ptSub :
    centralizer ((ptSub φ z hb e : Subgroup G) : Set G) = ptSub φ z hb e := by
  obtain ⟨-, hBe, -, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  obtain ⟨-, -, -, hAC, -⟩ := ptA_facts he hb hnd φ
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_centralizer_iff.2 fun r hr =>
    mul_comm_of_isElementaryAbelian hBe hr hx)
  have hxz : x ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hx z (mem_sup_right (mem_zpowers z))).symm
  have hxA : x ∈ centralizer (𝒜₁ : Set G) := mem_centralizer_iff.2 fun a ha =>
    mem_centralizer_iff.1 hx a (mem_sup_left ha)
  exact centralizer_inf_le hzC hsup hAC (Subgroup.mem_inf.2 ⟨hxA, hxz⟩)

variable [Finite G] [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 6)

include hzC hsup hinf hz hnd hV in
theorem not_conj_of_mem_ptA {a : G} (ha : a ∈ 𝒜₁) : ¬ ∃ g : G, g * z * g⁻¹ = a := by
  obtain ⟨haL, haP⟩ := mem_pullSub.1 ha
  exact not_conj_of_rank_le_two φ hzC hsup hinf hz hb hnd hV haL
    (finrank_range_sub_one_le hb haP)

include he hzC hsup hinf hz hnd hV in
theorem conj_mem_ptSub {g : G} (hg : g * z * g⁻¹ ∈ ptSub φ z hb e) :
    g * z * g⁻¹ ∈ z • (𝒜₁ : Set G) := by
  obtain ⟨a, ha, s, hs, has⟩ := (mem_sup_of_le_centralizer
    (FusionOrbits.zpowers_le_centralizer_pullSub φ hzC _)).1 hg
  rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hz hs with rfl | rfl
  · rw [mul_one] at has
    exact absurd ⟨g, has.symm⟩ (not_conj_of_mem_ptA hb hnd φ hzC hsup hinf hz hV ha)
  · rw [← has, mul_comm_z hzC ((ptA_facts he hb hnd φ).1 ha)]
    exact Set.smul_mem_smul_set ha

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem conj_ptHom_of_pairStabilizer (k : pairStabilizer b (e (Sum.inl 0)) (e (Sum.inr 0)))
    (v : 𝔼 × ZMod 2) (ε : ZMod 2) :
    ((φ.symm (k : bilinIsometryGroup b) : L) : G) *
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) *
        ((φ.symm (k : bilinIsometryGroup b) : L) : G)⁻¹ =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd (OddQuadraticFive.hV (polarBilin_ptQuad he)
        (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)) k) v, ε)) := by
  have hzε : ((φ.symm (k : bilinIsometryGroup b) : L) : G) * zPow z ε *
      ((φ.symm (k : bilinIsometryGroup b) : L) : G)⁻¹ = zPow z ε := by
    rw [mul_inv_eq_iff_eq_mul, mul_comm_zPow hzC (φ.symm _).2 ε]
  have h1 := congrArg (fun g : bilinIsometryGroup b => ((φ.symm g : L) : G)) (conj_ptHomV he hb k v)
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  rw [ptHom_apply, ptHom_apply, ← h1]
  calc ((φ.symm (k : bilinIsometryGroup b) : L) : G) *
        (((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) * zPow z ε) *
        ((φ.symm (k : bilinIsometryGroup b) : L) : G)⁻¹ =
      (((φ.symm (k : bilinIsometryGroup b) : L) : G) *
        ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) *
        ((φ.symm (k : bilinIsometryGroup b) : L) : G)⁻¹) *
      (((φ.symm (k : bilinIsometryGroup b) : L) : G) * zPow z ε *
        ((φ.symm (k : bilinIsometryGroup b) : L) : G)⁻¹) := by group
    _ = _ := by rw [hzε]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hsup hinf hnd in
theorem exists_hV_of_mem_stab {m : G} (hmN : m ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G))
    (hmz : m * z = z * m) :
    ∃ s : bilinIsometryGroup (b.restrict 𝔼), ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      m * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * m⁻¹ =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, ε)) := by
  obtain ⟨hBe, -, hBL⟩ := (ptSub_facts he hb hnd φ hzC hinf hz).2
  obtain ⟨hAL, -, -, -, hAN, -⟩ := ptA_facts he hb hnd φ
  have hmH : m ∈ L ⊔ zpowers z := hsup ▸ mem_centralizer_singleton_iff.2 hmz
  obtain ⟨l, hl, t, ht, rfl⟩ := (mem_sup_of_le_centralizer (zpowers_le_centralizer hzC)).1 hmH
  have htB : t ∈ ptSub φ z hb e := mem_sup_right ht
  have hlN : l ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
    have h := mul_mem hmN (inv_mem (le_normalizer htB))
    rwa [mul_inv_cancel_right] at h
  have hlA : l ∈ normalizer (𝒜₁ : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    rw [← hBL, mem_inf, mem_inf]
    constructor
    · rintro ⟨hx, hxL⟩
      exact ⟨(mem_normalizer_iff.1 hlN x).1 hx, mul_mem (mul_mem hl hxL) (inv_mem hl)⟩
    · rintro ⟨hx, hxL⟩
      refine ⟨(mem_normalizer_iff.1 hlN x).2 hx, ?_⟩
      have h := mul_mem (mul_mem (inv_mem hl) hxL) hl
      simpa [mul_assoc] using h
  have hlV : l ∈ pullSub φ (vecStabilizer b (e (Sum.inl 0))) := hAN ▸ mem_inf.2 ⟨hlA, hl⟩
  obtain ⟨_, hφl⟩ := mem_pullSub.1 hlV
  obtain ⟨a, ha, hk⟩ := exists_mem_pointRadical_mul_mem_pairStabilizer hb (bilin_f_u he) hφl
  set k : pairStabilizer b (e (Sum.inl 0)) (e (Sum.inr 0)) := ⟨_, hk⟩ with hkdef
  refine ⟨pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)) k, fun v ε => ?_⟩
  have hlak : l = ((φ.symm a : L) : G) * ((φ.symm (k : bilinIsometryGroup b) : L) : G) := by
    have h1 : (k : bilinIsometryGroup b) = a * φ ⟨l, hl⟩ := rfl
    rw [h1, map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul, ← mul_assoc,
      ← Subgroup.coe_mul, ← map_mul, pointRadical_mul_self hb ha, map_one, Subgroup.coe_one,
      one_mul]
  have haA : ((φ.symm a : L) : G) ∈ 𝒜₁ := by
    refine mem_pullSub.2 ⟨(φ.symm a).2, ?_⟩
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact ha
  have haB : ((φ.symm a : L) : G) ∈ ptSub φ z hb e := mem_sup_left haA
  have hxB : ptHom he hb φ hzC hz (Multiplicative.ofAdd
      (OddQuadraticFive.hV (polarBilin_ptQuad he) (pairRestrict b _ _ k) v, ε)) ∈
        ptSub φ z hb e := by
    rw [← range_ptHom he hb φ hzC hz]
    exact ⟨_, rfl⟩
  have hc1 := mul_comm_of_isElementaryAbelian hBe haB hxB
  have hvB : ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) ∈ ptSub φ z hb e := by
    rw [← range_ptHom he hb φ hzC hz]
    exact ⟨Multiplicative.ofAdd (v, ε), rfl⟩
  have hc2 := mul_comm_of_isElementaryAbelian hBe htB hvB
  rw [← conj_ptHom_of_pairStabilizer he hb φ hzC hz k v ε] at hc1 ⊢
  rw [hlak]
  calc ((φ.symm a : L) : G) * ((φ.symm (k : bilinIsometryGroup b) : L) : G) * t *
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) *
        (((φ.symm a : L) : G) * ((φ.symm (k : bilinIsometryGroup b) : L) : G) * t)⁻¹ =
      ((φ.symm a : L) : G) * (((φ.symm (k : bilinIsometryGroup b) : L) : G) *
        (t * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε))) * t⁻¹ *
        ((φ.symm (k : bilinIsometryGroup b) : L) : G)⁻¹) * ((φ.symm a : L) : G)⁻¹ := by group
    _ = ((φ.symm a : L) : G) * (((φ.symm (k : bilinIsometryGroup b) : L) : G) *
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) *
        ((φ.symm (k : bilinIsometryGroup b) : L) : G)⁻¹) * ((φ.symm a : L) : G)⁻¹ := by
      rw [hc2]; group
    _ = _ := by rw [hc1]; group

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hz in
theorem z_mul_self : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rwa [hz, sq] at h

@[expose] def zetaHom : ZetaGroup →* G where
  toFun ζ := if ζ = 1 then 1 else z
  map_one' := by simp
  map_mul' ζ ζ' := by
    rcases eq_one_or_eq_zeta ζ with rfl | rfl <;> rcases eq_one_or_eq_zeta ζ' with rfl | rfl
    · simp
    · simp
    · simp
    · have h1 : zeta * zeta = 1 := rfl
      simp [h1, z_mul_self hz]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem zetaHom_mem (ζ : ZetaGroup) : zetaHom hz ζ ∈ zpowers z := by
  rcases eq_one_or_eq_zeta ζ with rfl | rfl
  · rw [map_one]
    exact one_mem _
  · change (if zeta = 1 then 1 else z) ∈ zpowers z
    simp only [zeta_ne_one, ite_false]
    exact mem_zpowers z

@[expose] def hModel : bilinIsometryGroup b × ZetaGroup →* G :=
  MonoidHom.noncommCoprod (L.subtype.comp φ.symm.toMonoidHom) (zetaHom hz) fun g ζ =>
    ((mem_centralizer_iff.1 (zpowers_le_centralizer hzC (zetaHom_mem hz ζ)))
      _ (φ.symm g).2)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem hModel_apply (x : bilinIsometryGroup b × ZetaGroup) :
    hModel φ hzC hz x = ((φ.symm x.1 : L) : G) * zetaHom hz x.2 :=
  rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hinf in
theorem hModel_injective : Function.Injective (hModel φ hzC hz) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, ζ⟩ h
  rw [hModel_apply] at h
  have h1 : zetaHom hz ζ ∈ L ⊓ zpowers z := by
    refine mem_inf.2 ⟨?_, zetaHom_mem hz ζ⟩
    have h2 : zetaHom hz ζ = ((φ.symm g : L) : G)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h2]
    exact L.inv_mem (φ.symm g).2
  rw [hinf, mem_bot] at h1
  rw [h1, mul_one] at h
  have hg : g = 1 := by
    have h3 : φ.symm g = 1 := Subtype.ext h
    rwa [MulEquiv.map_eq_one_iff] at h3
  have hζ : ζ = 1 := by
    by_contra hne
    have h4 : zetaHom hz ζ = z := by
      change (if ζ = 1 then 1 else z) = z
      simp only [hne, ite_false]
    rw [h1] at h4
    rw [← h4, orderOf_one] at hz
    exact absurd hz (by norm_num)
  rw [hg, hζ]
  rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem map_hModel_prod_top (P : Subgroup (bilinIsometryGroup b)) :
    (P.prod (⊤ : Subgroup ZetaGroup)).map (hModel φ hzC hz) = pullSub φ P ⊔ zpowers z := by
  ext x
  constructor
  · rintro ⟨⟨g, ζ⟩, hgζ, rfl⟩
    rw [hModel_apply]
    refine mul_mem (mem_sup_left (mem_pullSub.2 ⟨(φ.symm g).2, ?_⟩))
      (mem_sup_right (zetaHom_mem hz ζ))
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_prod.1 hgζ).1
  · intro hx
    obtain ⟨a, ha, t, ht, rfl⟩ := (mem_sup_of_le_centralizer
      (FusionOrbits.zpowers_le_centralizer_pullSub φ hzC _)).1 hx
    obtain ⟨haL, haP⟩ := mem_pullSub.1 ha
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hz ht with rfl | rfl
    · refine ⟨(φ ⟨a, haL⟩, 1), Subgroup.mem_prod.2 ⟨haP, mem_top _⟩, ?_⟩
      rw [hModel_apply, MulEquiv.symm_apply_apply, map_one]
    · refine ⟨(φ ⟨a, haL⟩, zeta), Subgroup.mem_prod.2 ⟨haP, mem_top _⟩, ?_⟩
      rw [hModel_apply, MulEquiv.symm_apply_apply]
      change (a : G) * (if zeta = 1 then 1 else t) = a * t
      simp only [zeta_ne_one, ite_false]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem map_hModel_pointRadicalProd :
    (pointRadicalProd hb e).map (hModel φ hzC hz) = ptSub φ z hb e :=
  map_hModel_prod_top φ hzC hz _

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem map_hModel_lagrangianRadicalProd :
    (lagrangianRadicalProd b e).map (hModel φ hzC hz) = radSub φ z e :=
  map_hModel_prod_top φ hzC hz _

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem map_hModel_radicalProduct :
    (radicalProduct hb e).map (hModel φ hzC hz) = ptSub φ z hb e ⊔ radSub φ z e := by
  rw [radicalProduct, Subgroup.map_sup, map_hModel_pointRadicalProd,
    map_hModel_lagrangianRadicalProd]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include he hnd hzC hinf hz in
theorem eq_ptSub_of_sup_eq {Y : Subgroup G} (hYX : Y ≤ ptSub φ z hb e ⊔ radSub φ z e)
    (hYe : IsElementaryAbelian 2 Y) (hYc : Nat.card Y = 64)
    (hYR : Y ⊔ radSub φ z e = ptSub φ z hb e ⊔ radSub φ z e) : Y = ptSub φ z hb e := by
  set Ψ := hModel φ hzC hz with hΨ
  have hinj : Function.Injective Ψ := hModel_injective φ hzC hinf hz
  have hX : (radicalProduct hb e).map Ψ = ptSub φ z hb e ⊔ radSub φ z e :=
    map_hModel_radicalProduct hb φ hzC hz
  have hYrange : Y ≤ Ψ.range := hYX.trans (hX ▸ map_le_range _ _)
  set Y' := Y.comap Ψ with hY'
  have hYY' : Y'.map Ψ = Y := map_comap_eq_self hYrange
  have hY'X : Y' ≤ radicalProduct hb e := by
    intro x hx
    have h1 : Ψ x ∈ (radicalProduct hb e).map Ψ := hX ▸ hYX hx
    obtain ⟨y, hy, hyx⟩ := h1
    rw [← hinj hyx]
    exact hy
  have hY'e : IsElementaryAbelian 2 Y' := isElementaryAbelian_of_forall
    (fun x hx y hy => hinj (by
      rw [map_mul, map_mul]; exact mul_comm_of_isElementaryAbelian hYe hx hy))
    (fun x hx => hinj (by rw [map_mul, map_one]; exact mul_self_of_isElementaryAbelian hYe hx))
  have hY'c : Nat.card Y' = 64 := by
    rw [← hYc, ← hYY', card_map_of_injective hinj]
  have hY'R : Y' ⊔ lagrangianRadicalProd b e = radicalProduct hb e := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, hYY', map_hModel_lagrangianRadicalProd, hYR, hX]
  have h1 := eq_of_isElementaryAbelian_of_sup_eq hb he hnd hY'X hY'e hY'c hY'R
  rw [← hYY', h1, map_hModel_pointRadicalProd]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include he hnd hzC hinf hz in
theorem mem_normalizer_ptSub {d : G} (hdR : d ∈ normalizer ((radSub φ z e : Subgroup G) : Set G))
    (hdX : d ∈ normalizer ((ptSub φ z hb e ⊔ radSub φ z e : Subgroup G) : Set G)) :
    d ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
  obtain ⟨-, hBe, hBc, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := (ptSub φ z hb e).map (MulAut.conj d⁻¹).toMonoidHom with hYdef
  have hXmap := map_conj_eq_of_mem_normalizer (inv_mem hdX)
  have hRmap := map_conj_eq_of_mem_normalizer (inv_mem hdR)
  have : IsElementaryAbelian 2 (ptSub φ z hb e) := hBe
  have hYX : Y ≤ ptSub φ z hb e ⊔ radSub φ z e := by
    rw [← hXmap]
    exact map_mono le_sup_left
  have hYe : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hYc : Nat.card Y = 64 := by
    rw [hYdef, card_map_of_injective (MulAut.conj d⁻¹).injective, hBc]
  have hYR : Y ⊔ radSub φ z e = ptSub φ z hb e ⊔ radSub φ z e := by
    conv_lhs => rw [← hRmap]
    rw [hYdef, ← Subgroup.map_sup, hXmap]
  have hY := eq_ptSub_of_sup_eq he hb hnd φ hzC hinf hz hYX hYe hYc hYR
  have hinv : d⁻¹ ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : d⁻¹ * x * d⁻¹⁻¹ ∈ Y := ⟨x, hx, rfl⟩
      rwa [hY] at h1
    · intro hx
      rw [← hY] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have h2 : y = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
        have h4 := congrArg (fun w => d * w * d⁻¹) hyx
        simpa [mul_assoc] using h4
      rwa [← h2]
  have h3 := inv_mem hinv
  rwa [inv_inv] at h3

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
