module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64PointNormalizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

theorem mem_normalizer_of_map_le {G : Type*} [Group G] [Finite G] {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom ≤ X) : g ∈ normalizer (X : Set G) := by
  have heq : X.map (MulAut.conj g).toMonoidHom = X :=
    eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [heq] at h1
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h2 : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have h4 := congrArg (fun w => g⁻¹ * w * g) hyx
      simpa [mul_assoc] using h4
    rwa [← h2]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type*} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))

include he hnd hzC hinf hz in
theorem mem_normalizer_ptSub_of_comm [Finite G] {d : G}
    (hdR : d ∈ normalizer ((radSub φ z e : Subgroup G) : Set G))
    (hcomm : ∀ a ∈ 𝒜₁, d⁻¹ * a * d * a⁻¹ ∈ radSub φ z e) :
    d ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
  have hzR : z ∈ radSub φ z e := mem_sup_right (mem_zpowers z)
  have hR : ∀ r ∈ radSub φ z e, d⁻¹ * r * d ∈ radSub φ z e := fun r hr => by
    have h := (mem_normalizer_iff.1 (inv_mem hdR) r).1 hr
    rwa [inv_inv] at h
  have hX : d⁻¹ ∈ normalizer ((ptSub φ z hb e ⊔ radSub φ z e : Subgroup G) : Set G) := by
    refine mem_normalizer_of_map_le ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le (sup_le (fun a ha => ?_) ?_) (fun r hr => ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have h1 : d⁻¹ * a * d = (d⁻¹ * a * d * a⁻¹) * a := by group
      rw [h1]
      exact mul_mem (mem_sup_right (hcomm a ha)) (mem_sup_left (mem_sup_left ha))
    · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mem_sup_right (hR z hzR)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mem_sup_right (hR r hr)
  have hX' := inv_mem hX
  rw [inv_inv] at hX'
  exact mem_normalizer_ptSub he hb hnd φ hzC hinf hz hdR hX'

include he in
theorem mem_pairOrth_inl_one : e (Sum.inl 1) ∈ 𝔼 := by
  rw [mem_pairOrth, bilin_inl he, bilin_inr he]
  simp

abbrev ptE₂ : 𝔼 := ⟨e (Sum.inl 1), mem_pairOrth_inl_one he⟩

theorem ptQuad_ptE₂ : ptQuad e (ptE₂ he) = 0 := by
  rw [ptQuad_apply]
  simp

include he in
theorem pointElt_mem_pointwiseStabilizer {w : V} (hwE : w ∈ 𝔼) (hwW : w ∈ lagrangianOf e)
    (c : ZMod 2) :
    pointElt hb (mem_pairOrth_left hwE) c ∈ pointwiseStabilizer b (lagrangianOf e) := by
  intro x hx
  have hiso := isTotallyIsotropic_lagrangianOf he
  have hu : e (Sum.inl 0) ∈ lagrangianOf e := Submodule.subset_span ⟨0, rfl⟩
  change pointMap b (e (Sum.inl 0)) w c x = x
  rw [pointMap_apply, hiso x hx w hwW, hiso _ hu x hx, zero_smul, zero_smul, add_zero, add_zero]

theorem ptB_mem_radA :
    ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (0, 1))) : L) : G) ∈
      pullSub φ (pointwiseStabilizer b (lagrangianOf e)) := by
  refine mem_pullSub.2 ⟨(φ.symm _).2, ?_⟩
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, ptHomV_apply, ptElt_eq]
  exact pointElt_mem_pointwiseStabilizer he hb (zero_mem _) (zero_mem _) _

theorem ptE_mem_radA :
    ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (ptE₂ he, 0))) : L) : G) ∈
      pullSub φ (pointwiseStabilizer b (lagrangianOf e)) := by
  refine mem_pullSub.2 ⟨(φ.symm _).2, ?_⟩
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, ptHomV_apply, ptElt_eq]
  exact pointElt_mem_pointwiseStabilizer he hb (mem_pairOrth_inl_one he)
    (Submodule.subset_span ⟨1, rfl⟩) _

include he hnd hzC hsup hinf hz in
theorem card_conjClass_dvd_GL_six [Finite G] :
    Nat.card (conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z) ∣
      ∏ i : Fin 6, (2 ^ 6 - 2 ^ (i : ℕ)) := by
  obtain ⟨-, hBe, hBc, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  set B := ptSub φ z hb e with hB
  set N := normalizer ((B : Subgroup G) : Set G) with hN
  have hBC := centralizer_ptSub he hb hnd φ hzC hsup hinf hz
  have : IsMulCommutative B := hBe.toIsMulCommutative
  have hAut : Nat.card (MulAut B) = ∏ i : Fin 6, (2 ^ 6 - 2 ^ (i : ℕ)) :=
    card_mulAut_of_sq_eq_one (fun x => Subtype.ext (by
      rw [SubgroupClass.coe_pow, pow_two]
      exact mul_self_of_isElementaryAbelian hBe x.2)) (by rw [hBc]; norm_num)
  have hker := ker_conjNormalizer hBC
  have h1 : B.relIndex N ∣ Nat.card (MulAut B) := by
    have := Subgroup.index_ker (conjNormalizer B)
    rw [hker] at this
    change (B.subgroupOf N).index ∣ _
    rw [this]
    exact Subgroup.card_subgroup_dvd_card _
  have hBz : B ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mul_comm_of_isElementaryAbelian hBe hx
      (mem_sup_right (mem_zpowers z)))
  have h2 : (centralizer ({z} : Set G)).relIndex N ∣ B.relIndex N :=
    relIndex_dvd_of_le_left N hBz
  rw [card_conjClass, ← hAut]
  exact h2.trans h1

include he hzC hz in
theorem ptSub_le_normalizer_radSub :
    ptSub φ z hb e ≤ normalizer ((radSub φ z e : Subgroup G) : Set G) := by
  rw [← map_hModel_pointRadicalProd hb φ hzC hz, ← map_hModel_lagrangianRadicalProd φ hzC hz]
  exact (map_mono (pointRadicalProd_le_normalizer hb he)).trans (le_normalizer_map _)

include hzC hz in
theorem ptLevi_mem_normalizer [Finite G] (s : bilinIsometryGroup (b.restrict 𝔼)) :
    ptLevi he hb φ s ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_le ?_
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← range_ptHom he hb φ hzC hz] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨⟨v, ε⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = y := ⟨Multiplicative.toAdd y, rfl⟩
  rw [ptLevi_conj_ptHom]
  exact ⟨_, rfl⟩

include he hb hnd in
theorem card_pairOrth_eq : Nat.card 𝔼 = 16 := by
  have h := card_pointSpan he hb hnd
  rwa [pointSpan_eq_pairOrth he] at h

include he hb hnd in
theorem finrank_pairOrth_eq [FiniteDimensional (ZMod 2) V] : finrank (ZMod 2) 𝔼 = 4 := by
  have h := finrank_pairOrth hb hnd (bilin_f_u he)
  rw [finrank_eq_six e] at h
  omega

abbrev symE₁₁ : ↥(binarySymMatrices 3) :=
  ⟨jMat 1 0 0, mem_binarySymMatrices.2 (jMat_transpose 1 0 0)⟩

abbrev symE₁₂ : ↥(binarySymMatrices 3) :=
  ⟨jMat 0 1 0, mem_binarySymMatrices.2 (jMat_transpose 0 1 0)⟩

theorem tauHom_symE₁₁ :
    tauHom φ he (Multiplicative.ofAdd symE₁₁) =
      ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (0, 1))) : L) : G) := by
  refine (eq_tauHom_of_toMatrix φ he (φ.symm _).2 _ ?_).symm
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, ptHomV_apply, ptElt_eq]
  have hw : ((0 : 𝔼 × ZMod 2).1 : V) ∈ pointSpan e := by
    rw [pointSpan_eq_pairOrth he]
    exact (0 : 𝔼 × ZMod 2).1.2
  change LinearMap.toMatrix e e (pointMap b (e (Sum.inl 0)) ((0 : 𝔼 × ZMod 2).1 : V) _) = _
  rw [toMatrix_pointMap he hw]
  have hQ0 : ptQuad e (0 : 𝔼) = 0 := QuadraticMap.map_zero _
  simp [hQ0, t0Mat_zero]

theorem tauHom_symE₁₂ :
    tauHom φ he (Multiplicative.ofAdd symE₁₂) =
      ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (ptE₂ he, 0))) : L) : G) := by
  refine (eq_tauHom_of_toMatrix φ he (φ.symm _).2 _ ?_).symm
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, ptHomV_apply, ptElt_eq]
  have hw : (((ptE₂ he, (0 : ZMod 2)) : 𝔼 × ZMod 2).1 : V) ∈ pointSpan e := by
    rw [pointSpan_eq_pairOrth he]
    exact (ptE₂ he).2
  change LinearMap.toMatrix e e (pointMap b (e (Sum.inl 0))
    (((ptE₂ he, (0 : ZMod 2)) : 𝔼 × ZMod 2).1 : V) _) = _
  rw [toMatrix_pointMap he hw]
  simp [ptQuad_ptE₂ he, t0Mat_zero]

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}

include he hnd hzC hinf hz in
theorem mem_normalizer_ptSub_of_mem [Finite G] {D₂ : Subgroup G} {ν₂ : G → 𝕍}
    (hDN : D₂ ≤ normalizer ((radSub φ z e : Subgroup G) : Set G))
    (hDn : ∀ n ∈ normalizer ((radSub φ z e : Subgroup G) : Set G), ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hνz : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hνeq : ∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ d = ν₂ d' ↔ d⁻¹ * d' ∈ radSub φ z e)
    {d : G} (hd : d ∈ D₂) (hdA : tauHom φ he (Multiplicative.ofAdd (ν₂ d)) ∈ 𝒜₁) :
    d ∈ normalizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
  obtain ⟨-, hBe, -, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  refine mem_normalizer_ptSub_of_comm he hb hnd φ hzC hinf hz (hDN hd) fun a ha => ?_
  have haN : a ∈ normalizer ((radSub φ z e : Subgroup G) : Set G) :=
    ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left ha)
  have hd' : a * d * a⁻¹ ∈ D₂ := hDn a haN d hd
  have haL : a ∈ L := (ptA_facts he hb hnd φ).1 ha
  have hza : a * z = z * a := mul_comm_z hzC haL
  have hcomm : a * tauHom φ he (Multiplicative.ofAdd (ν₂ d)) =
      tauHom φ he (Multiplicative.ofAdd (ν₂ d)) * a :=
    mul_comm_of_isElementaryAbelian hBe (mem_sup_left ha) (mem_sup_left hdA)
  have hR1 : ∀ B : 𝕍, radHom φ he hzC hz (Multiplicative.ofAdd (B, 1)) =
      z * tauHom φ he (Multiplicative.ofAdd B) := fun B => by
    rw [radHom_apply, zPow_one, mul_comm_z hzC (tauHom_mem φ he _)]
  have h2 : (a * d * a⁻¹)⁻¹ * z * (a * d * a⁻¹) =
      radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)) := by
    have hza' : a⁻¹ * z * a = z := by rw [mul_assoc, ← hza, inv_mul_cancel_left]
    calc (a * d * a⁻¹)⁻¹ * z * (a * d * a⁻¹) = a * (d⁻¹ * (a⁻¹ * z * a) * d) * a⁻¹ := by group
      _ = a * (z * tauHom φ he (Multiplicative.ofAdd (ν₂ d))) * a⁻¹ := by
        rw [hza', hνz d hd, hR1]
      _ = (a * z) * tauHom φ he (Multiplicative.ofAdd (ν₂ d)) * a⁻¹ := by group
      _ = z * (a * tauHom φ he (Multiplicative.ofAdd (ν₂ d))) * a⁻¹ := by rw [hza]; group
      _ = z * tauHom φ he (Multiplicative.ofAdd (ν₂ d)) := by rw [hcomm]; group
      _ = _ := (hR1 _).symm
  have h3 := radHom_injective φ he hzC hz hinf ((hνz _ hd').symm.trans h2)
  have hν : ν₂ (a * d * a⁻¹) = ν₂ d := congrArg Prod.fst (Multiplicative.ofAdd.injective h3)
  have h4 := (hνeq d hd _ hd').1 hν.symm
  simpa only [mul_assoc] using h4

include hzC hz in
theorem mem_smul_ptA_iff {x : G} :
    x ∈ z • (𝒜₁ : Set G) ↔
      ∃ v : 𝔼 × ZMod 2, ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) = x := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_ptA_iff he hb φ).1 ha
    refine ⟨v, ?_⟩
    rw [ptHom_apply, zPow_one, smul_eq_mul, mul_comm_z hzC (φ.symm _).2]
  · rintro ⟨v, rfl⟩
    refine ⟨_, (mem_ptA_iff he hb φ).2 ⟨v, rfl⟩, ?_⟩
    rw [ptHom_apply, zPow_one, smul_eq_mul, mul_comm_z hzC (φ.symm _).2]

include he hnd hzC hsup hinf hz in
theorem conjClass_subset_smul_ptA [Finite G] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) :
    conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z ⊆ z • (𝒜₁ : Set G) := by
  rintro x ⟨g, hg, rfl⟩
  exact conj_mem_ptSub he hb hnd φ hzC hsup hinf hz hV
    ((mem_normalizer_iff.1 hg z).1 (mem_sup_right (mem_zpowers z)))

theorem zmod_two_eq_or_eq_add_one : ∀ x y : ZMod 2, x = y ∨ x = y + 1 := by
  decide

include he hnd hzC hsup hinf hz in
theorem ptHom_mem_conjClass [Finite G] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6)
    (h1 : ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), (1 : ZMod 2)), 1)) ∈
      conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z)
    (h2 : ptHom he hb φ hzC hz (Multiplicative.ofAdd ((ptE₂ he, (0 : ZMod 2)), 1)) ∈
      conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z)
    (v : 𝔼 × ZMod 2) :
    ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) ∈
      conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z := by
  classical
  set N := normalizer ((ptSub φ z hb e : Subgroup G) : Set G) with hN
  set f : 𝔼 × ZMod 2 → G := fun v => ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) with hf
  set S : Set (𝔼 × ZMod 2) := {v | f v ∈ conjClass N z} with hS
  have hfinj : Function.Injective f := fun v v' h => by
    have := ptHom_injective he hb φ hzC hz hinf h
    exact congrArg Prod.fst (Multiplicative.ofAdd.injective this)
  have hinv : ∀ (s : bilinIsometryGroup (b.restrict 𝔼)), ∀ v ∈ S,
      OddQuadraticFive.hV (polarBilin_ptQuad he) s v ∈ S := by
    intro s v hv
    have h := conj_mem_conjClass (ptLevi_mem_normalizer he hb φ hzC hz s) hv
    rw [ptLevi_conj_ptHom] at h
    exact h
  have htr : ∀ w w' : 𝔼, w ≠ 0 → w' ≠ 0 → ∃ s : bilinIsometryGroup (b.restrict 𝔼),
      OddQuadraticFive.sE s w = w' := by
    intro w w' hw hw'
    obtain ⟨k, hk, hkw⟩ := exists_pairStabilizer_apply_eq hb hnd (bilin_f_u he) w.2 w'.2
      (fun h => hw (Subtype.ext h)) (fun h => hw' (Subtype.ext h))
    exact ⟨pairRestrict b _ _ ⟨k, hk⟩, Subtype.ext hkw⟩
  have hQ0 : ptQuad e (0 : 𝔼) = 0 := QuadraticMap.map_zero _
  have hE₂ : ptE₂ he ≠ 0 := fun h => e.ne_zero (Sum.inl 1) (congrArg Subtype.val h)
  have hgraph : ∀ w : 𝔼, (w, ptQuad e w) ∈ S := by
    intro w
    by_cases hw : w = 0
    · subst hw
      rw [hQ0]
      change ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), (0 : ZMod 2)), 1)) ∈
        conjClass N z
      rw [Prod.mk_zero_zero, ptHom_z]
      exact self_mem_conjClass N z
    · obtain ⟨s, hs⟩ := htr (ptE₂ he) w hE₂ hw
      have h := hinv s _ h2
      rw [OddQuadraticFive.hV_apply, hs, ptQuad_ptE₂ he, add_zero, zero_add] at h
      exact h
  by_cases hall : ∃ w : 𝔼, w ≠ 0 ∧ (w, ptQuad e w + 1) ∈ S
  · obtain ⟨w₀, hw₀, hw₀S⟩ := hall
    obtain ⟨w, t⟩ := v
    rcases zmod_two_eq_or_eq_add_one t (ptQuad e w) with rfl | rfl
    · exact hgraph w
    · by_cases hw : w = 0
      · subst hw
        rw [hQ0, zero_add]
        exact h1
      · obtain ⟨s, hs⟩ := htr w₀ w hw₀ hw
        have h := hinv s _ hw₀S
        rw [OddQuadraticFive.hV_apply, hs] at h
        have ht : ptQuad e w₀ + 1 + ptQuad e w₀ + ptQuad e w = ptQuad e w + 1 := by
          rw [add_right_comm (ptQuad e w₀), add_self_eq_zero_zmod_two, zero_add, add_comm]
        rw [ht] at h
        exact h
  · exfalso
    push Not at hall
    have : Finite 𝔼 := Module.finite_of_finite (ZMod 2)
    have hr : ((0 : 𝔼), (1 : ZMod 2)) ∉ Set.range fun w : 𝔼 => (w, ptQuad e w) := by
      rintro ⟨w, hw⟩
      have h1' := congrArg Prod.fst hw
      have h2' := congrArg Prod.snd hw
      simp only at h1' h2'
      rw [h1', hQ0] at h2'
      exact zero_ne_one h2'
    have hginj : Function.Injective fun w : 𝔼 => (w, ptQuad e w) := fun w w' h =>
      congrArg Prod.fst h
    have hSeq : S = insert ((0 : 𝔼), (1 : ZMod 2)) (Set.range fun w : 𝔼 => (w, ptQuad e w)) := by
      ext ⟨w, t⟩
      constructor
      · intro hv
        rcases zmod_two_eq_or_eq_add_one t (ptQuad e w) with rfl | rfl
        · exact Or.inr ⟨w, rfl⟩
        · by_cases hw : w = 0
          · subst hw
            left
            rw [hQ0, zero_add]
          · exact absurd hv (hall w hw)
      · rintro (h | ⟨w', h⟩)
        · rw [h]
          exact h1
        · rw [← h]
          exact hgraph w'
    have hO : conjClass N z = f '' S := by
      ext x
      constructor
      · intro hx
        obtain ⟨u, hu⟩ := (mem_smul_ptA_iff he hb φ hzC hz).1
          (conjClass_subset_smul_ptA he hb hnd φ hzC hsup hinf hz hV hx)
        refine ⟨u, ?_, hu⟩
        change f u ∈ conjClass N z
        rw [hf]
        simp only
        rw [hu]
        exact hx
      · rintro ⟨u, hu, rfl⟩
        exact hu
    have hcard : Nat.card (conjClass N z) = 17 := by
      rw [hO, Nat.card_image_of_injective hfinj, hSeq, Nat.card_coe_set_eq,
        Set.ncard_insert_of_notMem hr, Set.ncard_range_of_injective hginj,
        card_pairOrth_eq he hb hnd]
    have hdvd := card_conjClass_dvd_GL_six he hb hnd φ hzC hsup hinf hz
    rw [hcard, Fin.prod_univ_six] at hdvd
    norm_num at hdvd

include he hnd hzC hsup hinf hz in
theorem conjClass_ptSub_eq [Finite G] [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6)
    (h1 : ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), (1 : ZMod 2)), 1)) ∈
      conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z)
    (h2 : ptHom he hb φ hzC hz (Multiplicative.ofAdd ((ptE₂ he, (0 : ZMod 2)), 1)) ∈
      conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z) :
    conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z = z • (𝒜₁ : Set G) := by
  refine Set.Subset.antisymm (conjClass_subset_smul_ptA he hb hnd φ hzC hsup hinf hz hV)
    fun x hx => ?_
  obtain ⟨v, rfl⟩ := (mem_smul_ptA_iff he hb φ hzC hz).1 hx
  exact ptHom_mem_conjClass he hb hnd φ hzC hsup hinf hz hV h1 h2 v

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
