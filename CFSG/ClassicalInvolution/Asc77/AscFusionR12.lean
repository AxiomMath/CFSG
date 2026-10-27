module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR10
public import CFSG.ClassicalInvolution.Asc77.AscFusionR6

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem not_forall_comm_of_sq_eq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) {a : G} (haK : a ∈ K) (ha2 : a * a = z) :
    ¬ ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K := by
  intro h
  obtain ⟨φ, hφs, hφk⟩ := exists_chart_of_classical hK
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hcen : φ ⟨a, haK⟩ ∈ Subgroup.center SL(2, GaloisField p f) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := hφs g
    have hmemK : ⁅a, (x : G)⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem haK x.2) (K.inv_mem haK)) (K.inv_mem x.2)
    have h1 : φ (⟨⁅a, (x : G)⁆, hmemK⟩ : ↥K) = 1 := by
      apply (hφk _).mpr
      exact (mem_oddCoreOf_iff.mp (h x x.2)).choose_spec
    have e : (⟨⁅a, (x : G)⁆, hmemK⟩ : ↥K) = ⟨a, haK⟩ * x * ⟨a, haK⟩⁻¹ * x⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [e] at h1
    simp only [map_mul, map_inv] at h1
    have h2 : φ x * φ ⟨a, haK⟩ = φ ⟨a, haK⟩ * φ x := by
      have h3 := mul_inv_eq_one.mp h1
      have h4 : φ ⟨a, haK⟩ * φ x * (φ ⟨a, haK⟩)⁻¹ = φ x := h3
      calc φ x * φ ⟨a, haK⟩ = (φ ⟨a, haK⟩ * φ x * (φ ⟨a, haK⟩)⁻¹) * φ ⟨a, haK⟩ := by rw [h4]
        _ = φ ⟨a, haK⟩ * φ x := by group
    exact h2
  have hsq : φ ⟨a, haK⟩ * φ ⟨a, haK⟩ = 1 := by
    obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrs, ← map_mul, ← pow_two, hr]
    simp
  have hz1 : (⟨z, hKz.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
    apply (hφk _).mp
    have : (⟨z, hKz.mem⟩ : ↥K) = ⟨a, haK⟩ * ⟨a, haK⟩ := Subtype.ext ha2.symm
    rw [this, map_mul]
    exact hsq
  have hz1' : z ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨hKz.mem, hz1⟩
  exact hKz.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hz1'
    (isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one))

omit [Finite G] in
theorem inner_of_mul_trivial {K : Subgroup G} {x y t : G} (hy : y ∈ K)
    (hxt : ∀ u ∈ K, ⁅x, u⁆ ∈ oddCoreOf K) (htxy : t = y * x) :
    ∀ u ∈ K, t * u * t⁻¹ * (y * u * y⁻¹)⁻¹ ∈ oddCoreOf K := by
  intro u hu
  have h1 : y * ⁅x, u⁆ * y⁻¹ ∈ oddCoreOf K :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hy) (hxt u hu)
  have e : t * u * t⁻¹ * (y * u * y⁻¹)⁻¹ = y * ⁅x, u⁆ * y⁻¹ := by
    rw [htxy, commutatorElement_def]
    group
  rw [e]
  exact h1

theorem exists_sq_eq_z_comm_of_trivial (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z t : G}
    {R : Subgroup G} (hK : IsClassicalMember p f K z) (hR2 : IsPGroup 2 R)
    (hRK : IsSylow2In (R ⊓ K) K) (htR : t ∈ R) (hT0 : ∀ x ∈ K, ⁅t, x⁆ ∈ oddCoreOf K) :
    ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hQuat : IsQuatSub (R ⊓ K) := isQuatSub_of_isSylow2In hp2 hK hRK
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := id hQuat
  have : NeZero (2 ^ k₁) := ⟨by positivity⟩
  set a₁ : ↥(R ⊓ K) := eQ.symm (QuaternionGroup.xa 0) with ha₁
  have ha₁ord : orderOf a₁ = 4 := by
    rw [ha₁, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  set a : G := (a₁ : G) with ha
  have haR : a ∈ R ⊓ K := a₁.2
  have haord : orderOf a = 4 := by rw [ha, Subgroup.orderOf_coe]; exact ha₁ord
  have ha4 : (a * a) * (a * a) = 1 := by
    have : a ^ 4 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
    simpa [pow_succ, mul_assoc] using this
  have ha2 : a * a = z := by
    rcases hKz.unique (a * a) (K.mul_mem haR.2 haR.2) ha4 with h | h
    · exfalso
      have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [haord] at this
      omega
    · exact h
  refine ⟨a, haR, ha2, ?_⟩
  have h1 : t * a * t⁻¹ * a⁻¹ ∈ oddCoreOf K := by
    have := hT0 a haR.2
    rwa [commutatorElement_def] at this
  have h2 : t * a * t⁻¹ * a⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem htR haR.1) (R.inv_mem htR)) (R.inv_mem haR.1)
  have h3 : t * a * t⁻¹ * a⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
      (hR2.to_le (Subgroup.zpowers_le.mpr h2))
  calc t * a = (t * a * t⁻¹ * a⁻¹) * a * t := by group
    _ = a * t := by rw [h3]; group

theorem exists_dual_twin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    {t : G} (ht : IsUniqueInvolution J t) (hne : t ≠ z) {a : G} (haK : a ∈ K) (ha2 : a * a = z)
    (hta : t * a = a * t) (haJ : a ∉ Subgroup.normalizer (J : Set G))
    (hzJ : z ∈ Subgroup.normalizer (J : Set G)) (hnt : ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) :
    ∃ K₃ ∈ CoreAssembly.conjClass K, IsUniqueInvolution K₃ z ∧ K₃ ≠ K ∧ a * t ∈ K₃ := by
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := ht.sq
  have haord : orderOf a = 4 := by
    have ha4 : (a * a) * (a * a) = 1 := by rw [ha2]; exact hz2
    have h4 : a ^ 2 ^ (1 + 1) = 1 := by simpa [pow_succ, mul_assoc] using ha4
    have hn2 : ¬ a ^ 2 ^ 1 = 1 := by
      intro h
      apply hKz.ne_one
      rw [← ha2]
      simpa [pow_two] using h
    have := orderOf_eq_prime_pow hn2 h4
    simpa using this
  have hnt' : ¬ ∀ j ∈ J, ⁅a * a, j⁆ ∈ oddCoreOf J := by rwa [ha2]
  obtain ⟨κ, hκJ, hκ2, hκn, hκc⟩ :=
    exists_kappa hp2 hq hz hJ ht haord hta.symm haJ (by rw [ha2]; exact hzJ) hnt'
  obtain ⟨δ, hδ2, hzδ, hδa⟩ := dual_delta_facts hz2 ht2 ha2 hta hκ2 hκn hκc
  have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  have hzδ' : δ⁻¹ * z * δ⁻¹⁻¹ = z := by
    rw [inv_inv, hδi]
    calc δ * z * δ = (z * δ) * δ := by rw [← hzδ]
      _ = z := by rw [mul_assoc, hδ2, mul_one]
  set K₃ : Subgroup G := conjSub δ⁻¹ K with hK₃
  have hK₃mem : K₃ ∈ CoreAssembly.conjClass K := conjSub_mem_conjClass hKc δ⁻¹
  have hK₃z : IsUniqueInvolution K₃ z := by
    have := hKz.conj δ⁻¹
    rwa [hzδ'] at this
  have hb₃ : a * t ∈ K₃ := by
    have := conj_mem_conjSub (n := δ⁻¹) haK
    rw [inv_inv] at this
    rwa [hδa] at this
  refine ⟨K₃, hK₃mem, hK₃z, ?_, hb₃⟩
  intro h
  have htK' : t ∈ K := by
    have h1 : a * t ∈ K := h ▸ hb₃
    have := K.mul_mem (K.inv_mem haK) h1
    simpa using this
  rcases hKz.unique t htK' ht2 with h1 | h1
  · exact ht.ne_one h1
  · exact hne h1

theorem oddQuot_facts (hq : 5 ≤ p ^ f) {J : Subgroup G} {t : G} (hJt : IsClassicalMember p f J t) :
    CFSG.IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) ∧
      pPrimeCore 2 (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := by
  have e := QuotientGroup.quotientMulEquivOfEq (CatalogueBAlternating.primeCore_two_eq_oddCore ↥J)
  refine ⟨?_, ?_⟩
  · refine CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv e ?_)
    exact isQuasisimple_oddQuot hq hJt
  · have h1 := pPrimeCore_map_iso 2 e
    rw [CatalogueBAlternating.primeCore_two_eq_oddCore (↥J ⧸ componentClassificationOddCore ↥J),
      OddCore.quotient_corefree ↥J] at h1
    exact (Subgroup.map_injective e.injective) (by rw [h1, Subgroup.map_bot])

theorem exists_trivial_action_lift (hq : 5 ≤ p ^ f) {J : Subgroup G} {t : G}
    (hJt : IsClassicalMember p f J t) {z : G} (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (hz2 : z * z = 1) (hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) :
    ∃ J₀ : Subgroup G, J₀ ≤ J ∧ (∀ x ∈ J₀, z * x * z⁻¹ = x) ∧ ⁅J₀, J₀⁆ = J₀ ∧
      CFSG.IsQuasisimple (J₀ ⧸ pPrimeCore 2 J₀) ∧
      (J₀.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set G))).IsSubnormal ∧
      ∀ x ∈ J, z * x * z⁻¹ = x → IsPGroup 2 (Subgroup.zpowers x) → x ∈ J₀ := by
  classical
  obtain ⟨hJq, hJcore⟩ := oddQuot_facts hq hJt
  let σ : MulAut ↥J := J.normalizerMonoidHom ⟨z, hzJ⟩
  have hσapp : ∀ x : ↥J, ((σ x : ↥J) : G) = z * (x : G) * z⁻¹ := fun x => rfl
  have hσσ : ∀ x : ↥J, σ (σ x) = x := fun x => by
    apply Subtype.ext
    rw [hσapp, hσapp]
    calc z * (z * (x : G) * z⁻¹) * z⁻¹ = (z * z) * (x : G) * (z * z)⁻¹ := by group
      _ = x := by rw [hz2]; group
  have hJperf : Group.IsPerfect ↥J := hJt.perfect
  have hbarperf : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
      (QuotientGroup.mk'_surjective _)
  have hTperf : ⁅(⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)), ⊤⁆ = ⊤ := hbarperf.commutator_eq_top
  have hTfix : ∀ y ∈ (⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)), oddQuotAut σ y = y := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [oddQuotAut_mk, QuotientGroup.eq]
    have hmem : ⁅z, (x : G)⁻¹⁆ ∈ oddCoreOf J := hζ _ (J.inv_mem x.2)
    obtain ⟨hmemJ, hmemO⟩ := mem_oddCoreOf_iff.mp hmem
    have e : (σ x)⁻¹ * x = ⟨⁅z, (x : G)⁻¹⁆, hmemJ⟩ := by
      apply Subtype.ext
      simp [hσapp, commutatorElement_def, mul_assoc]
    rw [e, CatalogueBAlternating.primeCore_two_eq_oddCore]
    exact hmemO
  have hTnorm : ∀ y : ↥J ⧸ pPrimeCore 2 ↥J, oddQuotAut σ y = y →
      ∀ t ∈ (⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)), y * t * y⁻¹ ∈ (⊤ : Subgroup _) :=
    fun _ _ _ _ => Subgroup.mem_top _
  obtain ⟨L, hLfix, hLperf, hLmap, hLsub, hL2⟩ :=
    exists_perfect_lift_fixed σ hσσ hTperf hTfix hTnorm
  have hT : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)) :=
    isQuasisimple_of_mulEquiv Subgroup.topEquiv hJq
  have hTcore : pPrimeCore 2 ↥(⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)) = ⊥ := by
    have h1 := pPrimeCore_map_iso 2
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)) ≃* _)
    rw [hJcore] at h1
    exact (Subgroup.map_injective Subgroup.topEquiv.injective) (by rw [h1, Subgroup.map_bot])
  have hLq : CFSG.IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    isQuasisimple_oddQuot_of_lift hLmap hT hTcore
  set J₀ : Subgroup G := L.map J.subtype with hJ₀
  have hJ₀J : J₀ ≤ J := Subgroup.map_subtype_le _
  refine ⟨J₀, hJ₀J, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : σ x = x := hLfix hx
    have h2 := congrArg Subtype.val h1
    rw [hσapp] at h2
    exact h2
  · rw [hJ₀, ← Subgroup.map_commutator, hLperf]
  · let e : ↥L ≃* ↥J₀ := L.equivMapOfInjective J.subtype J.subtype_injective
    exact isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (pPrimeCore 2 ↥L) (pPrimeCore 2 ↥J₀) e (pPrimeCore_map_iso 2 e)).symm hLq
  · set F : Subgroup G := J ⊓ Subgroup.centralizer ({z} : Set G) with hF
    have hFJ : ∀ x : ↥(fixSub σ), ((x : ↥J) : G) ∈ F := by
      intro x
      refine ⟨x.1.2, ?_⟩
      have h1 : σ (x : ↥J) = x := x.2
      have h2 := congrArg Subtype.val h1
      rw [hσapp] at h2
      show ((x : ↥J) : G) ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((x : ↥J) : G) * z = (z * ((x : ↥J) : G) * z⁻¹) * z := by rw [h2]
        _ = z * ((x : ↥J) : G) := by group
    let ι : ↥(fixSub σ) →* ↥F := (J.subtype.comp (fixSub σ).subtype).codRestrict F hFJ
    have hrange : ι.range = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hxJ : (x : G) ∈ J := x.2.1
      have hxz : (x : G) * z = z * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      refine ⟨⟨⟨x, hxJ⟩, ?_⟩, rfl⟩
      show σ ⟨x, hxJ⟩ = ⟨x, hxJ⟩
      apply Subtype.ext
      rw [hσapp]
      calc z * (x : G) * z⁻¹ = (x : G) * z * z⁻¹ := by rw [hxz]
        _ = x := by group
    have hsn := isSubnormal_map_of_isSubnormal_range ι hLsub
      (by rw [hrange]; exact Subgroup.IsSubnormal.top)
    have hid : (L.subgroupOf (fixSub σ)).map ι = J₀.subgroupOf F := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : ↥J), hy, rfl⟩
      · intro hx
        obtain ⟨ℓ, hℓ, hℓx⟩ := hx
        exact ⟨⟨ℓ, hLfix hℓ⟩, hℓ, Subtype.ext hℓx⟩
    rwa [hid] at hsn
  · intro x hxJ hxz hx2
    have hxfix : (⟨x, hxJ⟩ : ↥J) ∈ fixSub σ := by
      show σ ⟨x, hxJ⟩ = ⟨x, hxJ⟩
      apply Subtype.ext
      rw [hσapp]
      exact hxz
    have hx2' : IsPGroup 2 (Subgroup.zpowers (⟨x, hxJ⟩ : ↥J)) := by
      obtain ⟨n, hn⟩ := hx2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, show orderOf (⟨x, hxJ⟩ : ↥J) = orderOf x from
        (Subgroup.orderOf_coe (⟨x, hxJ⟩ : ↥J)).symm, ← hn, Nat.card_zpowers]
    have := hL2 ⟨x, hxJ⟩ hxfix hx2' (Subgroup.mem_top _)
    exact ⟨⟨x, hxJ⟩, this, rfl⟩

theorem mem_normalizer_of_trivial_action (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    {z : G} (hz : IsClassicalMember p f K z) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {t : G} (ht : IsUniqueInvolution J t)
    (htz : t * z = z * t) (hzJ : z ∈ Subgroup.normalizer (J : Set G))
    (hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) {v : G} (hvJ : v ∈ J)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v) :
    v ∈ Subgroup.normalizer (K : Set G) := by
  classical
  have hJt : IsClassicalMember p f J t := isClassicalMember_of_mem_conjClass hp2 hq hz hJ ht
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hz2 : z * z = 1 := hKz.sq
  obtain ⟨J₀, hJ₀J, hJ₀fix, hJ₀perf, hJ₀qs, hJ₀sub, hJ₀2⟩ :=
    exists_trivial_action_lift hq hJt hzJ hz2 hζ
  have hvJ₀ : v ∈ J₀ := by
    refine hJ₀2 v hvJ ?_ hv2
    calc z * v * z⁻¹ = (v * z) * z⁻¹ := by rw [hvz]
      _ = v := by group
  set Y : Subgroup G := Subgroup.centralizer ({z} : Set G) with hY
  have hKY : K ≤ Y := isSubnormal_le hz.subnormal
  have hJt' : J ≤ Subgroup.centralizer ({t} : Set G) := isSubnormal_le hJt.subnormal
  have htY : t ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr htz
  set R₂ : Subgroup G := Y ⊓ Subgroup.centralizer ({t} : Set G) with hR₂
  have hR₂Y : R₂ ≤ Y := inf_le_left
  have hR₂t : R₂ ≤ Subgroup.centralizer ({t} : Set G) := inf_le_right
  have hJ₀R₂ : J₀ ≤ R₂ := by
    intro x hx
    refine ⟨?_, hJt' (hJ₀J hx)⟩
    show x ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hJ₀fix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hJ₀Y : J₀ ≤ Y := hJ₀R₂.trans hR₂Y
  set a₀ : ↥Y := ⟨t, htY⟩ with ha₀
  have hA2 : IsPGroup 2 (Subgroup.zpowers a₀) :=
    isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext ht.sq) (fun h => ht.ne_one
      (congrArg Subtype.val h))
  have hcentA : Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y) =
      R₂.subgroupOf Y := by
    ext x
    constructor
    · intro hx
      have h1 : a₀ * x = x * a₀ := Subgroup.mem_centralizer_iff.mp hx a₀ (Subgroup.mem_zpowers a₀)
      refine ⟨x.2, ?_⟩
      show (x : G) ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val h1).symm
    · intro hx
      have hxt : (x : G) * t = t * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hcm : Commute a₀ x := Subtype.ext hxt.symm
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left hcm k).eq
  set LY : Subgroup ↥Y := J₀.subgroupOf Y with hLYdef
  have hLA : LY ≤ Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y) := by
    rw [hcentA]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hJ₀R₂ (Subgroup.mem_subgroupOf.mp hx))
  have hJsn : (J.subgroupOf (Subgroup.centralizer ({t} : Set G))).IsSubnormal :=
    subnormal_subgroupOf_member hJt
  have hJsnR₂ : (J.subgroupOf R₂).IsSubnormal := by
    have h1 := hJsn.comap (Subgroup.inclusion hR₂t)
    have h2 : (J.subgroupOf (Subgroup.centralizer ({t} : Set G))).comap
        (Subgroup.inclusion hR₂t) = J.subgroupOf R₂ := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1
  set F : Subgroup G := J ⊓ Y with hF
  have hFR₂ : ∀ x : ↥F, ((x : ↥F) : G) ∈ R₂ := by
    intro x
    exact ⟨x.2.2, hJt' x.2.1⟩
  let ι : ↥F →* ↥R₂ := (F.subtype).codRestrict R₂ hFR₂
  have hrange : ι.range = J.subgroupOf R₂ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2.1
    · intro hx
      exact ⟨⟨x, ⟨hx, x.2.1⟩⟩, rfl⟩
  have hJ₀F : (J₀.subgroupOf F).IsSubnormal := by
    have h1 := hJ₀sub
    simpa [hF, hY] using h1
  have hsnR₂ : (J₀.subgroupOf R₂).IsSubnormal := by
    have hsn := isSubnormal_map_of_isSubnormal_range ι hJ₀F (by rw [hrange]; exact hJsnR₂)
    have hid : (J₀.subgroupOf F).map ι = J₀.subgroupOf R₂ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxJ₀ : (x : G) ∈ J₀ := hx
        exact ⟨⟨x, ⟨hJ₀J hxJ₀, x.2.1⟩⟩, hxJ₀, rfl⟩
    rwa [hid] at hsn
  have hLsubY : IsSubnormal LY
      (Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y)) := by
    rw [hcentA]
    have h1 : IsSubnormal (J₀.subgroupOf R₂) ⊤ := Components.chain_of_mathlib_subnormal hsnR₂
    have h2 := Components.chain_map (Subgroup.inclusion hR₂Y) h1
    have e1 : (J₀.subgroupOf R₂).map (Subgroup.inclusion hR₂Y) = LY := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxJ₀ : (x : G) ∈ J₀ := hx
        exact ⟨⟨x, hJ₀R₂ hxJ₀⟩, hxJ₀, rfl⟩
    have e2 : (⊤ : Subgroup ↥R₂).map (Subgroup.inclusion hR₂Y) = R₂.subgroupOf Y := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rwa [e1, e2] at h2
  have e : ↥LY ≃* ↥J₀ := Subgroup.subgroupOfEquivOfLe hJ₀Y
  have hJ₀perf' : Group.IsPerfect ↥J₀ := Subgroup.isPerfect_iff.mpr hJ₀perf
  have hLYperf : commutator ↥LY = ⊤ := by
    have : Group.IsPerfect ↥LY :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hLq0 : CFSG.Open.IsQuasisimple (↥J₀ ⧸ componentClassificationOddCore ↥J₀) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.quotientMulEquivOfEq
        (CatalogueBAlternating.primeCore_two_eq_oddCore ↥J₀).symm)
      (CatalogueBAlternating.quasisimple_iff_native.mp hJ₀qs)
  have hLYq : CFSG.Open.IsQuasisimple (↥LY ⧸ componentClassificationOddCore LY) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore LY) (componentClassificationOddCore J₀)
        e (OddCore.equiv_invariant e)) hLq0
  have hLYlayer : LY ≤ TwoLayer.subgroup ↥Y :=
    Balance.le_twoLayer_of_l2PrimeBalance l2PrimeBalance hA2 hLA hLsubY hLYperf hLYq
  have hKcomp : TwoComponents.IsTwoComponent (K.subgroupOf Y) :=
    isTwoComponent_subgroupOf_of_perfect hz.subnormal hz.perfect.commutator_eq_top
      (isQuasisimple_oddQuot hq hz)
  have hnorm : TwoLayer.subgroup ↥Y ≤
      Subgroup.normalizer ((K.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    refine sSup_le fun K' hK' => ?_
    by_cases hKI : K' = K.subgroupOf Y
    · rw [hKI]
      exact Subgroup.le_normalizer
    · exact (TwoComponentInteraction.mutual_normalization_core_commutation _ _ hKcomp hK'
        (Ne.symm hKI)).1
  have hvY : v ∈ Y := hJ₀Y hvJ₀
  have h1 := hnorm (hLYlayer (show (⟨v, hvY⟩ : ↥Y) ∈ LY from hvJ₀))
  have h2 : (⟨v, hvY⟩ : ↥Y) ∈ (Subgroup.normalizer (K : Set G)).subgroupOf Y := by
    rw [Subgroup.subgroupOf_normalizer_eq hKY]
    exact h1
  exact Subgroup.mem_subgroupOf.mp h2

theorem exists_inner_order_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    {t : G} (ht : IsUniqueInvolution J t) (hne : t ≠ z) {v : G} (hvJ : v ∈ J)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hv4 : orderOf v = 4) (hvz : v * z = z * v)
    (hvK : v ^ 2 ∈ Subgroup.normalizer (K : Set G)) (hv : v ∉ Subgroup.normalizer (K : Set G))
    {R : Subgroup G} (hRcomm : ∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub v⁻¹ K, q * q' = q' * q)
    (hRinv : ∀ q ∈ R ⊓ K, v⁻¹ * q * v ∈ R ⊓ conjSub v⁻¹ K) {a₀ : G} (ha₀ : a₀ ∈ R ⊓ K)
    (ha₀2 : a₀ * a₀ = z) (hta₀ : t * a₀ = a₀ * t) :
    ∃ k ∈ K, k * k = z ∧ ∀ y ∈ K, t * y * t⁻¹ * (k * y * k⁻¹)⁻¹ ∈ oddCoreOf K := by
  classical
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := ht.sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hvv : v * v = t := by
    have hv22 : (v * v) * (v * v) = 1 := by
      have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
      simpa [pow_succ, mul_assoc] using this
    rcases ht.unique (v * v) (J.mul_mem hvJ hvJ) hv22 with h | h
    · exfalso
      have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hv4] at this
      omega
    · exact h
  have hvK' : v * v ∈ Subgroup.normalizer (K : Set G) := by simpa [pow_two] using hvK
  have htz : t * z = z * t := by
    rw [← hvv]
    calc v * v * z = v * (v * z) := by group
      _ = v * (z * v) := by rw [hvz]
      _ = (v * z) * v := by group
      _ = (z * v) * v := by rw [hvz]
      _ = z * (v * v) := by group
  have hvz' : v⁻¹ * z = z * v⁻¹ := by
    calc v⁻¹ * z = v⁻¹ * z * v * v⁻¹ := by group
      _ = z * v⁻¹ := by
        have : v⁻¹ * z * v = z := by
          calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
            _ = v⁻¹ * (v * z) := by rw [hvz]
            _ = z := by group
        rw [this]
  have hvK'' : conjSub v⁻¹ K ≠ K := fun h =>
    hv (by
      have := (Subgroup.normalizer (K : Set G)).inv_mem
        (AscHypOmega.mem_normalizer_of_conjSub_eq h)
      simpa using this)
  obtain ⟨hK'mem, hK'z, hK'N, hKN', hcomm'⟩ :=
    twin_facts_conj hp2 hq hz hKc hKz hvz' hvK''.symm
  set K' : Subgroup G := conjSub v⁻¹ K with hK'
  have hKK' : K ≠ K' := hvK''.symm
  obtain ⟨ha₀R, ha₀K⟩ := ha₀
  have ha₀4' : (a₀ * a₀) * (a₀ * a₀) = 1 := by rw [ha₀2]; exact hz2
  have ha₀pg : IsPGroup 2 (Subgroup.zpowers a₀) := isPGroup_zpowers_of_sq_sq ha₀4'
  have ha₀ord : orderOf a₀ = 4 := by
    have h4 : a₀ ^ 2 ^ (1 + 1) = 1 := by simpa [pow_succ, mul_assoc] using ha₀4'
    have hn2 : ¬ a₀ ^ 2 ^ 1 = 1 := by
      intro h
      apply hKz.ne_one
      rw [← ha₀2]
      simpa [pow_two] using h
    have := orderOf_eq_prime_pow hn2 h4
    simpa using this
  have hzv : v⁻¹ * z * v = z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * z) := by rw [hvz]
      _ = z := by group
  set a₀' : G := v⁻¹ * a₀ * v with ha₀'
  obtain ⟨ha₀'R, ha₀'K'⟩ := hRinv a₀ ⟨ha₀R, ha₀K⟩
  have ha₀cm : a₀ * a₀' = a₀' * a₀ := hRcomm a₀ ⟨ha₀R, ha₀K⟩ a₀' ⟨ha₀'R, ha₀'K'⟩
  have ha₀'2 : a₀' * a₀' = z := by
    calc a₀' * a₀' = v⁻¹ * (a₀ * a₀) * v := by rw [ha₀']; group
      _ = z := by rw [ha₀2, hzv]
  have hcommK : ∀ x ∈ K', ∀ u ∈ K, ⁅x, u⁆ ∈ oddCoreOf K := fun x hx u hu => by
    rw [← commutatorElement_inv]
    exact (oddCoreOf K).inv_mem (hcomm' (Subgroup.commutator_mem_commutator hu hx)).1
  by_cases hJa : a₀ ∈ Subgroup.normalizer (J : Set G)
  ·
    have hc : a₀ * a₀'⁻¹ = a₀'⁻¹ * a₀ := (Commute.inv_right (show Commute a₀ a₀' from ha₀cm)).eq
    have hσJ : a₀'⁻¹ * a₀ ∈ J := by
      have h1 : a₀⁻¹ * v * a₀ ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (J : Set G)).inv_mem hJa) v).mp hvJ
        simpa using this
      have : a₀'⁻¹ * a₀ = v⁻¹ * (a₀⁻¹ * v * a₀) := by rw [ha₀']; group
      rw [this]
      exact J.mul_mem (J.inv_mem hvJ) h1
    have hσ2 : (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = 1 := by
      calc (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = a₀'⁻¹ * (a₀ * a₀'⁻¹) * a₀ := by group
        _ = a₀'⁻¹ * (a₀'⁻¹ * a₀) * a₀ := by rw [hc]
        _ = (a₀' * a₀')⁻¹ * (a₀ * a₀) := by group
        _ = 1 := by rw [ha₀'2, ha₀2]; exact inv_mul_cancel z
    have hσt : a₀'⁻¹ * a₀ = t := by
      rcases ht.unique _ hσJ hσ2 with h | h
      · exfalso
        have hee : a₀' = a₀ := inv_mul_eq_one.mp h
        have hK'eq := eq_of_mem_of_mem hp2 hq hz hKc hK'mem ha₀K (hee ▸ ha₀'K') ha₀pg
          (by omega)
        exact hKK' hK'eq
      · exact h
    refine ⟨a₀, ha₀K, ha₀2, ?_⟩
    refine inner_of_mul_trivial ha₀K (x := a₀'⁻¹) (fun u hu => hcommK _ (K'.inv_mem ha₀'K') u hu) ?_
    rw [← hσt, hc]
  · have hzJ : z ∈ Subgroup.normalizer (J : Set G) := by
      have := centralizer_le_normalizer_of_mem hp2 hq hz hJ hvJ hv2 (by omega : 4 ≤ orderOf v)
      exact this (Subgroup.mem_centralizer_singleton_iff.mpr hvz.symm)
    by_cases hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J
    · exact absurd (mem_normalizer_of_trivial_action hp2 hq hz hJ ht htz hzJ hζ hvJ hv2 hvz) hv
    ·
      obtain ⟨K₃, hK₃mem, hK₃z, hK₃K, hb₃⟩ :=
        exists_dual_twin hp2 hq hz hJ ht hne ha₀K ha₀2 hta₀ hJa hzJ hζ
      obtain ⟨-, -, hcomm₃⟩ := twin_facts_general hq hp2 hz hK₃mem hKc hK₃z hKz hK₃K
      refine ⟨a₀⁻¹, K.inv_mem ha₀K, ?_, ?_⟩
      · calc a₀⁻¹ * a₀⁻¹ = (a₀ * a₀)⁻¹ := by group
          _ = z := by rw [ha₀2, hzi]
      · refine inner_of_mul_trivial (K.inv_mem ha₀K) (x := a₀ * t) (fun u hu => ?_) ?_
        · exact (hcomm₃ (Subgroup.commutator_mem_commutator hb₃ hu)).2
        · group

end CFSG.ClassicalInvolution.Asc77.AscFusion
