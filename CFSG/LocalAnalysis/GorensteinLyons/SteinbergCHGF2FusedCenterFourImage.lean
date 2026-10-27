module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourSymplecticFusion
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCCyclicFourNormalizer
public import CFSG.LinearAlgebra.SteinbergBQSmallInvolution

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement

namespace SteinbergCH

theorem natCard_generalLinearGroup_of_finrank_eq_two {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] (h : Module.finrank (ZMod 2) W = 2) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) W) = 6 := by
  classical
  let bW := Module.finBasisOfFinrankEq (ZMod 2) W h
  let e : LinearMap.GeneralLinearGroup (ZMod 2) W ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv bW).toMulEquiv
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  norm_num

theorem two_le_of_core_embedding
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M : Subgroup G}
    (hSyl : ∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ι : M ⧸ CFSG.pCore 2 M →* LinearMap.GeneralLinearGroup (ZMod 2) W)
    (hι : Function.Injective ι) {v : ℕ} (hv : 1 ≤ v)
    (hcard : Nat.card (CFSG.pCore 2 M) = 2 ^ (2 * v + 2))
    (hdim : Module.finrank (ZMod 2) W = 2 * v) : 2 ≤ v := by
  by_contra hlt
  obtain rfl : v = 1 := by omega
  have hGL := natCard_generalLinearGroup_of_finrank_eq_two (W := W) (by simpa using hdim)
  have hMQ : Nat.card (M ⧸ CFSG.pCore 2 M) ∣ 6 := hGL ▸ Subgroup.card_dvd_of_injective ι hι
  have hM : Nat.card M ∣ 96 := by
    rw [← (CFSG.pCore 2 M).card_mul_index, hcard, index_eq_card]
    exact Nat.mul_dvd_mul_left _ hMQ
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 M) := inferInstance
  obtain ⟨-, hS2, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp (hSyl _ ⟨T₀, rfl⟩)
  rw [relIndex_top_right] at hSidx
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
  have hSdvd : 2 ^ n ∣ 96 := hn ▸ (card_dvd_of_le (map_subtype_le _)).trans hM
  obtain ⟨-, -, hlocal, ⟨p, hp, hp2, B', r, hB', hB'r, hr, T, hT1, hT2, hBT⟩, -⟩ :=
    large_local_rank_core_and_component_reduction hchar he
  obtain ⟨⟨d, hd, hdr⟩, h6, -⟩ := hlocal p hp hp2 B' r hB' hB'r hr T hT1 hT2 hBT
  have hQ₀2 : IsPGroup 2 (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G))) :=
    CFSG.pCore_isPGroup.map _
  have h64 : 2 ^ 6 ≤ Nat.card (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G))) := by
    have h1 := Subgroup.card_quotient_dvd_card
      (frattini (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G))))
    rw [hd] at h1
    exact (Nat.pow_le_pow_right (by norm_num) (h6.trans hdr)).trans
      (Nat.le_of_dvd Nat.card_pos h1)
  obtain ⟨P', hP'⟩ := hQ₀2.exists_le_sylow
  have hle := (h64.trans (card_le_of_le hP')).trans_eq
    ((Sylow.card_eq_multiplicity P').trans (Sylow.card_eq_multiplicity (hS2.toSylow hSidx)).symm)
  rw [IsPGroup.toSylow_coe, hn] at hle
  have h6n : 6 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have := (pow_dvd_pow 2 h6n).trans hSdvd
  norm_num at this

variable {G : Type*} [Group G]

theorem normalizer_conjugate_eq (H : Subgroup G) (g : G) :
    normalizer (CFSG.conjugate H g : Set G) = CFSG.conjugate (normalizer (H : Set G)) g := by
  ext x
  rw [mem_conjugate_iff_conj_mem, mem_normalizer_iff_conjugate_eq,
    mem_normalizer_iff_conjugate_eq, conjugate_conjugate]
  have h1 : CFSG.conjugate H (g * x) = CFSG.conjugate (CFSG.conjugate H (g * x * g⁻¹)) g := by
    rw [conjugate_conjugate]
    congr 1
    group
  rw [h1]
  exact ⟨fun h => conjugate_injective g h, fun h => by rw [h]⟩

theorem conjugate_centralizer_singleton_eq (t g : G) :
    CFSG.conjugate (centralizer ({t} : Set G)) g = centralizer ({g⁻¹ * t * g} : Set G) := by
  ext x
  rw [mem_conjugate_iff_conj_mem, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor <;> intro h
  · calc x * (g⁻¹ * t * g) = g⁻¹ * ((g * x * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * t * g * x := by group
  · calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [h]
      _ = t * (g * x * g⁻¹) := by group

theorem conjugate_zpowers_eq (t g : G) :
    CFSG.conjugate (zpowers t) g = zpowers (g⁻¹ * t * g) := by
  rw [CFSG.conjugate, MonoidHom.map_zpowers]
  simp

theorem fused_conjugate_center [Finite G] {M Q Z : Subgroup G} {z : G}
    (huniq : ∀ y ∈ Z, orderOf y = 2 → y = z) (hMC : M = centralizer ({z} : Set G))
    (hMNZ : M = normalizer (Z : Set G))
    (hconj : ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      Z ⊔ CFSG.conjugate Z g ≤ M ∧ ⁅Z, CFSG.conjugate Z g⁆ = ⊥ ∧
      IsCyclic (CFSG.conjugate Z g) ∧ Nat.card (CFSG.conjugate Z g) = Nat.card Z)
    (hZ4 : Nat.card Z = 4) {a g : G} (haQ : a ∈ Q) (haz : a ≠ z) (hg : g⁻¹ * z * g = a) :
    (∀ g' : G, g'⁻¹ * z * g' = a → CFSG.conjugate Z g' = CFSG.conjugate Z g) ∧
    CFSG.conjugate Z g ≤ M ∧ IsCyclic (CFSG.conjugate Z g) ∧ ⁅Z, CFSG.conjugate Z g⁆ = ⊥ ∧
    normalizer (CFSG.conjugate Z g : Set G) = centralizer ({a} : Set G) ∧
    ∀ t : G, zpowers t = CFSG.conjugate Z g → orderOf t = 4 ∧ t ^ 2 = a := by
  obtain ⟨hle, hcomm, hcyc, hcard⟩ := hconj g (hg ▸ haQ) (hg ▸ haz)
  refine ⟨fun g' hg' => ?_, le_sup_right.trans hle, hcyc, hcomm, ?_, fun t ht => ?_⟩
  · have hc : g' * g⁻¹ ∈ normalizer (Z : Set G) := by
      rw [← hMNZ, hMC, mem_centralizer_singleton_iff]
      have h : g⁻¹ * z * g = g'⁻¹ * z * g' := hg.trans hg'.symm
      calc g' * g⁻¹ * z = g' * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = g' * (g'⁻¹ * z * g') * g⁻¹ := by rw [h]
        _ = z * (g' * g⁻¹) := by group
    rw [show g' = g' * g⁻¹ * g by group, ← conjugate_conjugate,
      mem_normalizer_iff_conjugate_eq.mp hc]
  · rw [normalizer_conjugate_eq, ← hMNZ, hMC, conjugate_centralizer_singleton_eq, hg]
  · have h4 : orderOf t = 4 := by rw [← Nat.card_zpowers, ht, hcard, hZ4]
    refine ⟨h4, ?_⟩
    have h2 : orderOf (t ^ 2) = 2 := by
      rw [orderOf_pow' t (by norm_num), h4]
      rfl
    have hmem : g * t ^ 2 * g⁻¹ ∈ Z := by
      rw [← mem_conjugate_iff_conj_mem, ← ht]
      exact pow_mem (mem_zpowers t) 2
    have hord : orderOf (g * t ^ 2 * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h2]
    have hz' := huniq _ hmem hord
    calc t ^ 2 = g⁻¹ * (g * t ^ 2 * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [hz']
      _ = a := hg

theorem cyclic_four_conjugate_product [Finite G] {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) {z : G} (hΦ : (frattini Q).map Q.subtype = zpowers z)
    (hQ' : ⁅Q, Q⁆ = zpowers z) (hz : orderOf z = 2) {t : G}
    (htN : t ∈ normalizer (Q : Set G)) (ht : orderOf t = 4) (haQ : t ^ 2 ∈ Q)
    (haZ : ∃ q ∈ Q, t ^ 2 * q ≠ q * t ^ 2) (htZ : ∀ c : Q, c ∈ center Q → t * c = c * t)
    (hNX : normalizer (zpowers t : Set G) = centralizer {t ^ 2}) :
    t ∉ Q ∧
    Nonempty ((⨆ q ∈ Q, CFSG.conjugate (zpowers t) q : Subgroup G) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    Q ≤ normalizer ((⨆ q ∈ Q, CFSG.conjugate (zpowers t) q : Subgroup G) : Set G) ∧
    IsMulCommutative ((⨆ q ∈ Q, CFSG.conjugate (zpowers t) q) ⊓ Q : Subgroup G) ∧
    Nat.card ((⨆ q ∈ Q, CFSG.conjugate (zpowers t) q) ⊓ Q : Subgroup G) = 8 := by
  obtain ⟨htQ, -, -, hiso, hnorm, hcard, hcomm, -⟩ :=
    cyclic_four_normalizer_forces_small_quadratic_action hQ2 hΦ hQ' hz htN ht haQ haZ htZ hNX
  have hA : (⨆ q ∈ Q, CFSG.conjugate (zpowers t) q : Subgroup G) =
      closure {x | ∃ q ∈ Q, x = q⁻¹ * t * q} := by
    apply le_antisymm
    · refine iSup₂_le fun q hq => ?_
      rw [conjugate_zpowers_eq, zpowers_le]
      exact subset_closure ⟨q, hq, rfl⟩
    · rw [closure_le]
      rintro x ⟨q, hq, rfl⟩
      refine (le_iSup₂ (f := fun q (_ : q ∈ Q) => CFSG.conjugate (zpowers t) q) q hq) ?_
      rw [conjugate_zpowers_eq]
      exact mem_zpowers _
  rw [hA]
  exact ⟨htQ, hiso, hnorm, hcomm, hcard⟩

theorem small_involution_shape {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {b : LinearMap.BilinForm (ZMod 2) V} (halt : b.IsAlt)
    (hnd : b.Nondegenerate) {T : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hT : T ∈ bilinIsometryGroup b) (hT2 : T ^ 2 = 1) {m : ℕ}
    (hm : Module.finrank (ZMod 2) (LinearMap.range ((T : Module.End (ZMod 2) V) - 1)) = m)
    (hm12 : m = 1 ∨ m = 2) {a : V} (ha : a ≠ 0)
    (hfun : ∀ x, b x (((T : Module.End (ZMod 2) V) - 1) x) = b x a) :
    (m = 1 → ∀ x, (T : Module.End (ZMod 2) V) x = x + b x a • a) ∧
    (m = 2 → ∃ u v₀ : V, LinearIndependent (ZMod 2) ![u, v₀] ∧ b u v₀ = 0 ∧ u + v₀ = a ∧
      ∃ τu τv : Module.End (ZMod 2) V, (∀ x, τu x = x + b x u • u) ∧
        (∀ x, τv x = x + b x v₀ • v₀) ∧ (T : Module.End (ZMod 2) V) = τu * τv ∧
        τu * τv = τv * τu) := by
  have hrk : Module.finrank (ZMod 2)
      (LinearMap.range ((T : V →ₗ[ZMod 2] V) - LinearMap.id)) ≤ 2 := by
    rw [← Module.End.one_eq_id, hm]
    omega
  have hfun' : ∀ x, b x ((T : V →ₗ[ZMod 2] V) x - x) = b x a := fun x => by
    rw [← hfun x, LinearMap.sub_apply, Module.End.one_apply]
  obtain ⟨hxor, -, -⟩ := CFSG.LinearAlgebra.binary_symplectic_small_nonalternating_involution b
    hnd halt T hT hT2 hrk ha hfun'
  rw [← Module.End.one_eq_id, hm] at hxor
  refine ⟨fun h1 x => ?_, fun h2 => ?_⟩
  · obtain ⟨-, hT1⟩ := hxor.elim (fun h => h.1) fun h => absurd (h.1.1.symm.trans h1) (by omega)
    rw [hT1, CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
  · obtain ⟨-, u, v₀, hli, huv, hauv, hTuv, hcomm, -⟩ :=
      hxor.elim (fun h => absurd (h.1.1.symm.trans h2) (by omega)) fun h => h.1
    refine ⟨u, v₀, hli, huv, hauv.symm,
      (CFSG.ClassicalGroups.Alternating.symplecticTransvection b halt u 1 : Module.End (ZMod 2) V),
      (CFSG.ClassicalGroups.Alternating.symplecticTransvection b halt v₀ 1 :
        Module.End (ZMod 2) V), fun x => ?_, fun x => ?_, ?_, ?_⟩
    · rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
    · rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
    · rw [hTuv, Units.val_mul]
    · rw [← Units.val_mul, ← Units.val_mul, hcomm]

theorem map_frattini_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective e.surjective
  · intro x hx
    have h := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom)
      e.symm.surjective hx
    exact ⟨e.symm x, h, by simp⟩

theorem cyclic_four_core_action [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hz : orderOf z = 2) (hzM : z ∈ M)
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    {t : G} (htM : t ∈ M)
    {T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, (y : M) = ⟨t, htM⟩ * x * (⟨t, htM⟩ : M)⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (ht : orderOf t = 4) (haQ : t ^ 2 ∈ Q) (haZ : t ^ 2 ∉ (center Q).map Q.subtype)
    (htZ : ∀ c ∈ (center Q).map Q.subtype, t * c = c * t)
    (hNX : normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G))
    {a₀ : CFSG.pCore 2 M} (ha₀ : ((a₀ : M) : G) = t ^ 2) :
    (∀ x, T x = x ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) * t = t * ((q : M) : G) ∧
      x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
    ∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = m ∧
      (centralizer ({t} : Set G)).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
      ∀ x, b x ((T - 1) x) =
        b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) := by
  have hinj := M.subtype_injective
  have hPQ : (CFSG.pCore 2 M).map M.subtype = Q := by rw [hQ]; rfl
  obtain ⟨e, heval⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
      ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
    subst hQ
    exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype hinj, fun _ => rfl⟩
  have hQmap : ∀ {x : M}, (x : G) ∈ Q ↔ x ∈ CFSG.pCore 2 M := fun {x} => by
    rw [← hPQ]
    exact mem_map_iff_mem hinj
  have hz₀ : orderOf (⟨z, hzM⟩ : M) = 2 := by rw [← Subgroup.orderOf_coe]; exact hz
  have ht₀ : orderOf (⟨t, htM⟩ : M) = 4 := by rw [← Subgroup.orderOf_coe]; exact ht
  have haQ₀ : (⟨t, htM⟩ : M) ^ 2 ∈ CFSG.pCore 2 M :=
    hQmap.mp (by rw [Subgroup.coe_pow]; exact haQ)
  have hΦ₀ : (frattini (CFSG.pCore 2 M)).map (CFSG.pCore 2 M).subtype =
      zpowers (⟨z, hzM⟩ : M) := by
    apply map_injective hinj
    rw [map_map, MonoidHom.map_zpowers]
    have he : M.subtype.comp (CFSG.pCore 2 M).subtype = Q.subtype.comp e.toMonoidHom := by
      ext x
      exact (heval x).symm
    rw [he, ← map_map, map_frattini_mulEquiv]
    exact hΦ
  have hQ'₀ : ⁅CFSG.pCore 2 M, CFSG.pCore 2 M⁆ = zpowers (⟨z, hzM⟩ : M) := by
    apply map_injective hinj
    rw [map_commutator, MonoidHom.map_zpowers, hPQ]
    exact hQ'
  have htN₀ : (⟨t, htM⟩ : M) ∈ normalizer (CFSG.pCore 2 M : Set M) := by
    rw [normalizer_eq_top]
    exact mem_top _
  have haZ₀ : ∃ q ∈ CFSG.pCore 2 M,
      (⟨t, htM⟩ : M) ^ 2 * q ≠ q * (⟨t, htM⟩ : M) ^ 2 := by
    by_contra hall
    push Not at hall
    apply haZ
    refine ⟨⟨t ^ 2, haQ⟩, mem_center_iff.mpr fun c => ?_, rfl⟩
    obtain ⟨c, hc⟩ := c
    rw [← hPQ] at hc
    obtain ⟨c', hc', rfl⟩ := mem_map.mp hc
    have h := congrArg Subtype.val (hall c' hc')
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow] at h
    exact Subtype.ext h.symm
  have htZ₀ : ∀ c : CFSG.pCore 2 M, c ∈ center (CFSG.pCore 2 M) →
      (⟨t, htM⟩ : M) * c = c * (⟨t, htM⟩ : M) := by
    intro c hc
    have hcZ : ((c : M) : G) ∈ (center Q).map Q.subtype := by
      refine ⟨e c, ?_, heval c⟩
      rw [← map_center_eq e]
      exact mem_map_of_mem _ hc
    exact Subtype.ext (htZ _ hcZ)
  have hNX₀ : normalizer (zpowers (⟨t, htM⟩ : M) : Set M) =
      centralizer ({(⟨t, htM⟩ : M) ^ 2} : Set M) := by
    ext x
    have h1 : x ∈ normalizer (zpowers (⟨t, htM⟩ : M) : Set M) ↔
        (x : G) ∈ normalizer (zpowers t : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers,
        MonoidHom.map_zpowers]
      constructor
      · intro h
        have h' := congrArg (map M.subtype) h
        rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h'
        simpa [MulAut.conj_apply] using h'
      · intro h
        apply map_injective hinj
        rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        simpa [MulAut.conj_apply] using h
    rw [h1, hNX, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor <;> intro h
    · exact Subtype.ext (by simpa using h)
    · simpa using congrArg Subtype.val h
  obtain ⟨-, ⟨inst', b', -, huniq', -, -, T', hT', -, -, hfix', ⟨m, hm, hrel, hm12, -⟩,
      hfun', -⟩, -⟩ :=
    cyclic_four_normalizer_forces_small_quadratic_action (G := M) (Q := CFSG.pCore 2 M)
      CFSG.pCore_isPGroup hΦ₀ hQ'₀ hz₀ htN₀ ht₀ haQ₀ haZ₀ htZ₀ hNX₀
  have hbb : b = b' := huniq' b fun x y => Subtype.ext ((hrule x y).trans
    (Subgroup.coe_pow M ⟨z, hzM⟩ _).symm)
  have hTT : T = T' := by
    apply LinearMap.ext
    intro w
    obtain ⟨w', rfl⟩ := Additive.ofMul.surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w'
    have hy : (⟨t, htM⟩ : M) * (x : M) * (⟨t, htM⟩ : M)⁻¹ ∈ CFSG.pCore 2 M :=
      (CFSG.pCore_normal).conj_mem _ x.2 _
    rw [hT x ⟨_, hy⟩ rfl, hT' x ⟨_, hy⟩ rfl]
  have ha : (⟨(⟨t, htM⟩ : M) ^ 2, haQ₀⟩ : CFSG.pCore 2 M) = a₀ :=
    Subtype.ext (Subtype.ext (by rw [ha₀]; rfl))
  refine ⟨fun x => ?_, m, hTT ▸ hm, ?_, hm12, fun x => ?_⟩
  · rw [hTT, hfix' x]
    constructor <;> rintro ⟨q, hq, rfl⟩ <;> refine ⟨q, ?_, rfl⟩
    · exact congrArg Subtype.val hq
    · exact Subtype.ext hq
  · rw [← hrel]
    have hc : (centralizer ({t} : Set G)).comap M.subtype =
        centralizer ({(⟨t, htM⟩ : M)} : Set M) := by
      ext x
      rw [mem_comap, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [← hc, relIndex_comap, hPQ]
  · rw [hbb, hTT, hfun' x, ha]

theorem exists_zpowers_eq_of_isCyclic {H : Subgroup G} (hH : IsCyclic H) :
    ∃ t ∈ H, zpowers t = H := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hH
  refine ⟨g, g.2, ?_⟩
  have h1 := MonoidHom.map_zpowers H.subtype g
  rw [hg, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact h1.symm

theorem mem_fusedSet_iff {Q : Subgroup G} {z a : G} :
    a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} ↔
      (∃ g : G, g⁻¹ * z * g = a) ∧ a ∈ Q ∧ a ≠ z := by
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe,
    Set.mem_singleton_iff]
  exact and_assoc

theorem fused_action_package [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hz : orderOf z = 2) (hzM : z ∈ M)
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (halt : b.IsAlt) (hnd : b.Nondegenerate) {t : G} (htM : t ∈ M)
    {T : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hTsp : T ∈ bilinIsometryGroup b) (hT2 : T ^ 2 = 1)
    (hT : ∀ x y : CFSG.pCore 2 M, (y : M) = ⟨t, htM⟩ * x * (⟨t, htM⟩ : M)⁻¹ →
      (T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
        (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (ht : orderOf t = 4) (haQ : t ^ 2 ∈ Q) (haZ : t ^ 2 ∉ (center Q).map Q.subtype)
    (htZ : ∀ c ∈ (center Q).map Q.subtype, t * c = c * t)
    (hNX : normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G))
    {a₀ : CFSG.pCore 2 M} (ha₀ : ((a₀ : M) : G) = t ^ 2) :
    (∀ x, (T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) x = x ↔
      ∃ q : CFSG.pCore 2 M, ((q : M) : G) * t = t * ((q : M) : G) ∧
        x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
    ∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range
        ((T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1)) =
        m ∧
      (centralizer ({t} : Set G)).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
      (∀ x, b x (((T : Module.End (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1) x) =
        b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) ∧
      (m = 1 → ∀ x,
        (T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) x =
          x + b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) •
            Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
      (m = 2 → ∃ u v₀ : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)),
        LinearIndependent (ZMod 2) ![u, v₀] ∧ b u v₀ = 0 ∧
        u + v₀ = Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∧
        ∃ τu τv : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
          (∀ x, τu x = x + b x u • u) ∧ (∀ x, τv x = x + b x v₀ • v₀) ∧
          (T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) =
            τu * τv ∧ τu * τv = τv * τu) := by
  obtain ⟨hfix, m, hm, hrel, hm12, hfun⟩ :=
    cyclic_four_core_action hQ hz hzM hΦ hQ' hrule htM hT ht haQ haZ htZ hNX ha₀
  have ha0 : Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ≠ 0 := by
    intro h0
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff] at h0
    obtain ⟨e, heval⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
        ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
      subst hQ
      exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective, fun _ => rfl⟩
    apply haZ
    refine ⟨e a₀, ?_, (heval a₀).trans ha₀⟩
    rw [← map_center_eq e]
    exact mem_map_of_mem _ h0
  obtain ⟨h1, h2⟩ := small_involution_shape halt hnd hTsp hT2 hm hm12 ha0 hfun
  exact ⟨hfix, m, hm, hrel, hm12, hfun, h1, h2⟩


theorem fused_generators [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzord : orderOf z = 2)
    (hMNQ : M = normalizer (Q : Set G)) (hΦ : (frattini Q).map Q.subtype = zpowers z)
    (hQ' : ⁅Q, Q⁆ = zpowers z) {a : G} (haQ : a ∈ Q) (haZ' : ∃ q ∈ Q, a * q ≠ q * a)
    {X : Subgroup G} (hXM : X ≤ M) (hXcomm : ⁅(center Q).map Q.subtype, X⁆ = ⊥)
    (hXN : normalizer (X : Set G) = centralizer ({a} : Set G))
    (hgen : ∀ t : G, zpowers t = X → orderOf t = 4 ∧ t ^ 2 = a) :
    ∀ t : G, zpowers t = X → t ∈ M ∧ orderOf t = 4 ∧ t ^ 2 = a ∧
      (∀ c ∈ (center Q).map Q.subtype, t * c = c * t) ∧
      normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G) ∧ t ∉ Q := by
  intro t ht
  have hQ2 : IsPGroup 2 Q := hQ ▸ CFSG.pCore_isPGroup.map _
  have htM : t ∈ M := hXM (ht ▸ mem_zpowers t)
  obtain ⟨h4, hsq⟩ := hgen t ht
  have htZ : ∀ c ∈ (center Q).map Q.subtype, t * c = c * t := by
    intro c hc
    have hc' := (commutator_eq_bot_iff_le_centralizer.mp hXcomm) hc
    exact mem_centralizer_iff.mp hc' t (ht ▸ mem_zpowers t)
  have hNX : normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G) := by
    rw [ht, hXN, hsq]
  refine ⟨htM, h4, hsq, htZ, hNX, ?_⟩
  exact (cyclic_four_conjugate_product hQ2 hΦ hQ' hzord (hMNQ ▸ htM) h4 (hsq ▸ haQ)
    (hsq ▸ haZ') (fun c hc => htZ c ⟨c, hc, rfl⟩) hNX).1

theorem zpowers_inf_eq_of_sq {Q : Subgroup G} {t a : G} (htQ : t ∉ Q) (hsq : t ^ 2 = a)
    (haQ : a ∈ Q) : zpowers t ⊓ Q = zpowers a := by
  have h2 : t ^ (2 : ℤ) = a := by rw [← hsq]; exact (zpow_two t).trans (pow_two t).symm
  apply le_antisymm
  · rintro x ⟨hxX, hxQ⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxX
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, h2]
      exact zpow_mem (mem_zpowers a) n
    · exfalso
      apply htQ
      have h1 : t ^ (2 * n) ∈ Q := by
        rw [zpow_mul, h2]
        exact zpow_mem haQ n
      have h3 := Q.mul_mem (Q.inv_mem h1) hxQ
      rwa [zpow_add, zpow_one, ← mul_assoc, inv_mul_cancel, one_mul] at h3
  · rw [zpowers_le]
    exact ⟨hsq ▸ pow_mem (mem_zpowers t) 2, haQ⟩

theorem fused_local_action [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzord : orderOf z = 2) (hzM : z ∈ M)
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (halt : b.IsAlt) (hnd : b.Nondegenerate) (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b)
    (hιf : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {a : G} (haQ : a ∈ Q) (haZ : a ∉ (center Q).map Q.subtype) {Xa : Subgroup G}
    {σa : M ⧸ CFSG.pCore 2 M} (hσ2 : σa ^ 2 = 1)
    (hgens : ∀ t : G, zpowers t = Xa → t ∈ M ∧ orderOf t = 4 ∧ t ^ 2 = a ∧
      (∀ c ∈ (center Q).map Q.subtype, t * c = c * t) ∧
      normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G) ∧ t ∉ Q)
    (hσ : ∀ t : G, zpowers t = Xa → ∀ htM : t ∈ M,
      ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = σa) :
    ∀ T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      T = ((ι σa : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) →
      ∀ t : G, zpowers t = Xa → ∀ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a →
      (∀ x, T x = x ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) * t = t * ((q : M) : G) ∧
        x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
      ∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = m ∧
        (centralizer ({t} : Set G)).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
        (∀ x, b x ((T - 1) x) =
          b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) ∧
        (m = 1 → ∀ x, T x = x +
          b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) •
            Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
        (m = 2 → ∃ u v₀ : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)),
          LinearIndependent (ZMod 2) ![u, v₀] ∧ b u v₀ = 0 ∧
          u + v₀ = Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∧
          ∃ τu τv : Module.End (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
            (∀ x, τu x = x + b x u • u) ∧ (∀ x, τv x = x + b x v₀ • v₀) ∧
            T = τu * τv ∧ τu * τv = τv * τu) := by
  intro T hT t ht a₀ ha₀
  subst hT
  obtain ⟨htM, h4, hsq, htZ, hNX, -⟩ := hgens t ht
  have hT2 : ((ι σa : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hσ2, map_one, Subgroup.coe_one]
  have hT' : ∀ x y : CFSG.pCore 2 M, (y : M) = ⟨t, htM⟩ * x * (⟨t, htM⟩ : M)⁻¹ →
      (((ι σa : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
        (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) := by
    intro x y hy
    rw [← hσ t ht htM]
    exact hιf _ x y hy
  exact fused_action_package hQ hzord hzM hΦ hQ' hrule halt hnd htM (ι σa).2 hT2 hT' h4
    (hsq ▸ haQ) (hsq ▸ haZ) htZ hNX (ha₀.trans hsq.symm)

theorem fused_local [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzord : orderOf z = 2)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hMC : M = centralizer ({z} : Set G)) (hMNQ : M = normalizer (Q : Set G))
    (hMNZ : M = normalizer ((center Q).map Q.subtype : Set G))
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hZ4 : Nat.card ((center Q).map Q.subtype) = 4)
    (hconj : ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      (center Q).map Q.subtype ⊔ CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
      ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ∧
      IsCyclic (CFSG.conjugate ((center Q).map Q.subtype) g) ∧
      Nat.card (CFSG.conjugate ((center Q).map Q.subtype) g) =
        Nat.card ((center Q).map Q.subtype))
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (halt : b.IsAlt) (hnd : b.Nondegenerate) (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b)
    (hιf : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {a g : G} (haQ : a ∈ Q) (haz : a ≠ z) (hg : g⁻¹ * z * g = a) {Xa : Subgroup G}
    (hXa : CFSG.conjugate ((center Q).map Q.subtype) g = Xa) {t₁ : G} (htX : zpowers t₁ = Xa)
    (ht₁M : t₁ ∈ M) {σa : M ⧸ CFSG.pCore 2 M}
    (hσa : ((⟨t₁, ht₁M⟩ : M) : M ⧸ CFSG.pCore 2 M) = σa) :
    (∀ g : G, g⁻¹ * z * g = a → CFSG.conjugate ((center Q).map Q.subtype) g = Xa) ∧
    Xa ≤ M ∧ IsCyclic Xa ∧ ⁅(center Q).map Q.subtype, Xa⁆ = ⊥ ∧
    normalizer (Xa : Set G) = centralizer ({a} : Set G) ∧ Xa ⊓ Q = zpowers a ∧
    (∀ t : G, zpowers t = Xa → orderOf t = 4 ∧ t ^ 2 = a ∧ t ∉ Q ∧
      ∀ htM : t ∈ M, ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = σa) ∧
    orderOf σa = 2 ∧
    (∀ T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      T = ((ι σa : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) →
      ∀ t : G, zpowers t = Xa → ∀ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a →
      (∀ x, T x = x ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) * t = t * ((q : M) : G) ∧
        x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
      ∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = m ∧
        (centralizer ({t} : Set G)).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
        (∀ x, b x ((T - 1) x) =
          b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) ∧
        (m = 1 → ∀ x, T x = x +
          b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) •
            Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
        (m = 2 → ∃ u v₀ : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)),
          LinearIndependent (ZMod 2) ![u, v₀] ∧ b u v₀ = 0 ∧
          u + v₀ = Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∧
          ∃ τu τv : Module.End (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
            (∀ x, τu x = x + b x u • u) ∧ (∀ x, τv x = x + b x v₀ • v₀) ∧
            T = τu * τv ∧ τu * τv = τv * τu)) ∧
    Nonempty ((⨆ q ∈ Q, CFSG.conjugate Xa q : Subgroup G) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
    Q ≤ normalizer ((⨆ q ∈ Q, CFSG.conjugate Xa q : Subgroup G) : Set G) ∧
    IsMulCommutative ((⨆ q ∈ Q, CFSG.conjugate Xa q) ⊓ Q : Subgroup G) ∧
    Nat.card ((⨆ q ∈ Q, CFSG.conjugate Xa q) ⊓ Q : Subgroup G) = 8 := by
  subst hXa hσa
  obtain ⟨hXg, hXM, hXcyc, hXcomm, hXN, hgen⟩ :=
    fused_conjugate_center huniq hMC hMNZ hconj hZ4 haQ haz hg
  have hQ2 : IsPGroup 2 Q := hQ ▸ CFSG.pCore_isPGroup.map _
  have hzM : z ∈ M := hMC ▸ mem_centralizer_singleton_iff.mpr rfl
  have hQmap : ∀ {x : M}, (x : G) ∈ Q ↔ x ∈ CFSG.pCore 2 M := fun {x} => by
    rw [hQ]
    exact mem_map_iff_mem M.subtype_injective
  have ha2 : orderOf a = 2 := by
    rw [← hg, show g⁻¹ * z * g = MulAut.conj g⁻¹ z by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hzord]
  have haZ : a ∉ (center Q).map Q.subtype := fun h => haz (huniq a h ha2)
  have haZ' : ∃ q ∈ Q, a * q ≠ q * a := by
    by_contra hall
    push Not at hall
    exact haZ ⟨⟨a, haQ⟩, mem_center_iff.mpr fun c => Subtype.ext (hall c c.2).symm, rfl⟩
  have hgens := fused_generators hQ hzord hMNQ hΦ hQ' haQ haZ' hXM hXcomm hXN hgen
  obtain ⟨-, h4, hsq, htZ, hNX, htQ⟩ := hgens t₁ htX
  have hσ : ∀ t : G, zpowers t = CFSG.conjugate ((center Q).map Q.subtype) g →
      ∀ htM : t ∈ M, ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) =
        ((⟨t₁, ht₁M⟩ : M) : M ⧸ CFSG.pCore 2 M) := by
    intro t ht htM
    have htt : t ∈ zpowers t₁ := htX ▸ ht ▸ mem_zpowers t
    rcases eq_or_eq_of_mem_zpowers_of_orderOf_eq_four h4 htt (hgens t ht).2.1 with rfl | rfl
    · rfl
    · rw [QuotientGroup.eq]
      apply hQmap.mp
      rw [Subgroup.coe_mul, Subgroup.coe_inv, show ((⟨t₁ ^ 3, htM⟩ : M) : G)⁻¹ * t₁ =
        (t₁ ^ 2)⁻¹ by simp only; group, hsq]
      exact Q.inv_mem haQ
  have hσ2 : ((⟨t₁, ht₁M⟩ : M) : M ⧸ CFSG.pCore 2 M) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply hQmap.mp
    rw [Subgroup.coe_pow]
    exact hsq ▸ haQ
  have hσ1 : ((⟨t₁, ht₁M⟩ : M) : M ⧸ CFSG.pCore 2 M) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => htQ (hQmap.mpr h)
  obtain ⟨-, hiso, hnorm, hcomm, hcard⟩ := cyclic_four_conjugate_product hQ2 hΦ hQ' hzord
    (hMNQ ▸ ht₁M) h4 (hsq ▸ haQ) (hsq ▸ haZ') (fun c hc => htZ c ⟨c, hc, rfl⟩) hNX
  rw [htX] at hiso hnorm hcomm hcard
  refine ⟨hXg, hXM, hXcyc, hXcomm, hXN, htX ▸ zpowers_inf_eq_of_sq htQ hsq haQ, fun t ht => ?_,
    orderOf_eq_prime hσ2 hσ1, fused_local_action hQ hzord hzM hΦ hQ' hrule halt hnd ι hιf haQ
      haZ hσ2 hgens hσ, hiso, hnorm, hcomm, hcard⟩
  obtain ⟨-, h4', hsq', -, -, htQ'⟩ := hgens t ht
  exact ⟨h4', hsq', htQ', hσ t ht⟩

theorem fused_equivariance {M Q Z : Subgroup G} {z : G} (hMC : M = centralizer ({z} : Set G))
    (hMNQ : M = normalizer (Q : Set G)) {F : Set G}
    (hF : F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z})
    {X : G → Subgroup G} {σ : G → M ⧸ CFSG.pCore 2 M}
    (hX : ∀ a ∈ F, ∀ g : G, g⁻¹ * z * g = a → CFSG.conjugate Z g = X a)
    (hσ : ∀ a ∈ F, ∀ t : G, zpowers t = X a → ∀ htM : t ∈ M,
      ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = σ a)
    (hgen : ∀ a ∈ F, ∃ t ∈ M, zpowers t = X a) :
    ∀ a ∈ F, ∀ (h : G) (hh : h ∈ M), h⁻¹ * a * h ∈ F ∧
      σ (h⁻¹ * a * h) = ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M)⁻¹ * σ a *
        ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M) := by
  intro a ha h hh
  have ha' := ha
  rw [hF, mem_fusedSet_iff] at ha'
  obtain ⟨⟨g, hg⟩, haQ, haz⟩ := ha'
  have hha : h⁻¹ * a * h ∈ F := by
    rw [hF, mem_fusedSet_iff]
    refine ⟨⟨g * h, by rw [← hg]; group⟩, ?_, fun hz => haz ?_⟩
    · have hh' : h⁻¹ ∈ normalizer (Q : Set G) := hMNQ ▸ M.inv_mem hh
      simpa using (mem_normalizer_iff.mp hh' a).mp haQ
    · have hc : h * z = z * h := mem_centralizer_singleton_iff.mp (hMC ▸ hh)
      calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
        _ = h * z * h⁻¹ := by rw [hz]
        _ = z := by rw [hc]; group
  refine ⟨hha, ?_⟩
  obtain ⟨t, htM, ht⟩ := hgen a ha
  have hXh : X (h⁻¹ * a * h) = CFSG.conjugate (X a) h := by
    rw [← hX _ hha (g * h) (by rw [← hg]; group), ← hX a ha g hg, conjugate_conjugate]
  have ht' : zpowers (h⁻¹ * t * h) = X (h⁻¹ * a * h) := by
    rw [hXh, ← ht, conjugate_zpowers_eq]
  rw [← hσ _ hha _ ht' (M.mul_mem (M.mul_mem (M.inv_mem hh) htM) hh), ← hσ a ha t ht htM,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem fused_fibers [Finite G] {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    {z : G} (hzord : orderOf z = 2)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hfuse : ∀ t ∈ Q, t ∉ (center Q).map Q.subtype → orderOf t = 2 →
      ∃ q ∈ Q, q * t * q⁻¹ = t * z)
    {F : Set G} (hF : F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z})
    {σ : G → M ⧸ CFSG.pCore 2 M}
    (hequiv : ∀ a ∈ F, ∀ (h : G) (hh : h ∈ M), h⁻¹ * a * h ∈ F ∧
      σ (h⁻¹ * a * h) = ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M)⁻¹ * σ a *
        ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M))
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hnd : b.Nondegenerate) (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b)
    (hid : ∀ a ∈ F, ∀ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a → ∀ x,
      b x (((((ι (σ a) : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
          Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1) x) =
        b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
    ∀ a ∈ F, a * z ∈ F ∧ ∀ b₀ ∈ F, σ a = σ b₀ ↔ b₀ = a ∨ b₀ = a * z := by
  have hQM : Q ≤ M := hQ ▸ map_subtype_le _
  have hQmap : ∀ {x : M}, (x : G) ∈ Q ↔ x ∈ CFSG.pCore 2 M := fun {x} => by
    rw [hQ]
    exact mem_map_iff_mem M.subtype_injective
  have hlift : ∀ {a : G}, a ∈ Q → ∃ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a := by
    intro a ha
    rw [hQ] at ha
    obtain ⟨a₁, ha₁, rfl⟩ := mem_map.mp ha
    exact ⟨⟨a₁, ha₁⟩, rfl⟩
  have hord : ∀ {a : G}, a ∈ F → a ∈ Q ∧ a ≠ z ∧ orderOf a = 2 := by
    intro a ha
    rw [hF, mem_fusedSet_iff] at ha
    obtain ⟨⟨g, hg⟩, haQ, haz⟩ := ha
    refine ⟨haQ, haz, ?_⟩
    rw [← hg, show g⁻¹ * z * g = MulAut.conj g⁻¹ z by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hzord]
  have hpair : ∀ a ∈ F, a * z ∈ F ∧ σ (a * z) = σ a := by
    intro a ha
    obtain ⟨haQ, haz, hao⟩ := hord ha
    obtain ⟨q, hqQ, hq⟩ := hfuse a haQ (fun h => haz (huniq a h hao)) hao
    have hqM : q⁻¹ ∈ M := M.inv_mem (hQM hqQ)
    obtain ⟨h1, h2⟩ := hequiv a ha q⁻¹ hqM
    rw [inv_inv, hq] at h1 h2
    refine ⟨h1, ?_⟩
    have h3 : ((⟨q⁻¹, hqM⟩ : M) : M ⧸ CFSG.pCore 2 M) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hQmap.mp (Q.inv_mem hqQ)
    rw [h2, h3, inv_one, one_mul, mul_one]
  intro a ha
  obtain ⟨hazF, hσaz⟩ := hpair a ha
  refine ⟨hazF, fun b₀ hb₀ => ⟨fun hab => ?_, ?_⟩⟩
  · obtain ⟨haQ, -, hao⟩ := hord ha
    obtain ⟨hbQ, -, hbo⟩ := hord hb₀
    obtain ⟨a₀, ha₀⟩ := hlift haQ
    obtain ⟨b₁, hb₁⟩ := hlift hbQ
    have hab' : Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) =
        Additive.ofMul (b₁ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) := by
      refine sub_eq_zero.mp (hnd.2 _ fun x => ?_)
      rw [map_sub, ← hid a ha a₀ ha₀ x, ← hid b₀ hb₀ b₁ hb₁ x, hab, sub_self]
    obtain ⟨e, heval⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
        ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
      subst hQ
      exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective, fun _ => rfl⟩
    have hc : a⁻¹ * b₀ ∈ (center Q).map Q.subtype := by
      refine ⟨e (a₀⁻¹ * b₁), ?_, ?_⟩
      · rw [← map_center_eq e]
        exact mem_map_of_mem _ (QuotientGroup.eq.mp (Additive.ofMul.injective hab'))
      · rw [Q.coe_subtype, heval]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha₀, hb₁]
    have hcomm : a * (a⁻¹ * b₀) = (a⁻¹ * b₀) * a := by
      obtain ⟨c', hc', hc'eq⟩ := hc
      have h := congrArg Subtype.val (mem_center_iff.mp hc' ⟨a, haQ⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
      rw [← hc'eq]
      exact h
    have ha2 : a * a = 1 := by rw [← pow_two, ← hao]; exact pow_orderOf_eq_one a
    have hb2 : b₀ * b₀ = 1 := by rw [← pow_two, ← hbo]; exact pow_orderOf_eq_one b₀
    have hba : b₀ * a⁻¹ = a⁻¹ * b₀ := by
      calc b₀ * a⁻¹ = a * (a⁻¹ * b₀) * a⁻¹ := by group
        _ = (a⁻¹ * b₀) * a * a⁻¹ := by rw [hcomm]
        _ = a⁻¹ * b₀ := by group
    have hc2 : (a⁻¹ * b₀) ^ 2 = 1 := by
      calc (a⁻¹ * b₀) ^ 2 = a⁻¹ * (b₀ * a⁻¹) * b₀ := by rw [pow_two]; group
        _ = a⁻¹ * (a⁻¹ * b₀) * b₀ := by rw [hba]
        _ = (a * a)⁻¹ * (b₀ * b₀) := by group
        _ = 1 := by rw [ha2, hb2, inv_one, one_mul]
    by_cases hc1 : a⁻¹ * b₀ = 1
    · left
      calc b₀ = a * (a⁻¹ * b₀) := by group
        _ = a := by rw [hc1, mul_one]
    · right
      calc b₀ = a * (a⁻¹ * b₀) := by group
        _ = a * z := by rw [huniq _ hc (orderOf_eq_prime hc2 hc1)]
  · rintro (rfl | rfl)
    · rfl
    · exact hσaz.symm

theorem fused_choice [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzord : orderOf z = 2)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hMC : M = centralizer ({z} : Set G)) (hMNQ : M = normalizer (Q : Set G))
    (hMNZ : M = normalizer ((center Q).map Q.subtype : Set G))
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hZ4 : Nat.card ((center Q).map Q.subtype) = 4)
    (hconj : ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      (center Q).map Q.subtype ⊔ CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
      ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ∧
      IsCyclic (CFSG.conjugate ((center Q).map Q.subtype) g) ∧
      Nat.card (CFSG.conjugate ((center Q).map Q.subtype) g) =
        Nat.card ((center Q).map Q.subtype))
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (halt : b.IsAlt) (hnd : b.Nondegenerate) (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b)
    (hιf : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {F : Set G} (hF : F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z}) :
    ∀ a : G, ∃ (Xa : Subgroup G) (σa : M ⧸ CFSG.pCore 2 M), a ∈ F →
      (∀ g : G, g⁻¹ * z * g = a → CFSG.conjugate ((center Q).map Q.subtype) g = Xa) ∧
      Xa ≤ M ∧ IsCyclic Xa ∧ ⁅(center Q).map Q.subtype, Xa⁆ = ⊥ ∧
      normalizer (Xa : Set G) = centralizer ({a} : Set G) ∧ Xa ⊓ Q = zpowers a ∧
      (∀ t : G, zpowers t = Xa → orderOf t = 4 ∧ t ^ 2 = a ∧ t ∉ Q ∧
        ∀ htM : t ∈ M, ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = σa) ∧
      orderOf σa = 2 ∧
      (∀ T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        T = ((ι σa : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) →
        ∀ t : G, zpowers t = Xa → ∀ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a →
        (∀ x, T x = x ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) * t = t * ((q : M) : G) ∧
          x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
        ∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = m ∧
          (centralizer ({t} : Set G)).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
          (∀ x, b x ((T - 1) x) =
            b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) ∧
          (m = 1 → ∀ x, T x = x +
            b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) •
              Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
          (m = 2 → ∃ u v₀ : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)),
            LinearIndependent (ZMod 2) ![u, v₀] ∧ b u v₀ = 0 ∧
            u + v₀ = Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∧
            ∃ τu τv : Module.End (ZMod 2)
                (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
              (∀ x, τu x = x + b x u • u) ∧ (∀ x, τv x = x + b x v₀ • v₀) ∧
              T = τu * τv ∧ τu * τv = τv * τu)) ∧
      Nonempty ((⨆ q ∈ Q, CFSG.conjugate Xa q : Subgroup G) ≃*
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
      Q ≤ normalizer ((⨆ q ∈ Q, CFSG.conjugate Xa q : Subgroup G) : Set G) ∧
      IsMulCommutative ((⨆ q ∈ Q, CFSG.conjugate Xa q) ⊓ Q : Subgroup G) ∧
      Nat.card ((⨆ q ∈ Q, CFSG.conjugate Xa q) ⊓ Q : Subgroup G) = 8 := by
  intro a
  by_cases ha : a ∈ F
  · rw [hF, mem_fusedSet_iff] at ha
    obtain ⟨⟨g, hg⟩, haQ, haz⟩ := ha
    obtain ⟨-, hXM, hXcyc, -⟩ := fused_conjugate_center huniq hMC hMNZ hconj hZ4 haQ haz hg
    obtain ⟨t, htX, ht⟩ := exists_zpowers_eq_of_isCyclic hXcyc
    exact ⟨_, _, fun _ => fused_local hQ hzord huniq hMC hMNQ hMNZ hΦ hQ' hZ4 hconj hrule halt hnd
      ι hιf haQ haz hg rfl ht (hXM htX) rfl⟩
  · exact ⟨⊥, 1, fun h => absurd h ha⟩

theorem fused_image_package [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzord : orderOf z = 2)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hMC : M = centralizer ({z} : Set G)) (hMNQ : M = normalizer (Q : Set G))
    (hMNZ : M = normalizer ((center Q).map Q.subtype : Set G))
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hZ4 : Nat.card ((center Q).map Q.subtype) = 4)
    (hconj : ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      (center Q).map Q.subtype ⊔ CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
      ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ∧
      IsCyclic (CFSG.conjugate ((center Q).map Q.subtype) g) ∧
      Nat.card (CFSG.conjugate ((center Q).map Q.subtype) g) =
        Nat.card ((center Q).map Q.subtype))
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (halt : b.IsAlt) (hnd : b.Nondegenerate) (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b)
    (hιf : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hfuse : ∀ t ∈ Q, t ∉ (center Q).map Q.subtype → orderOf t = 2 →
      ∃ q ∈ Q, q * t * q⁻¹ = t * z) :
    ∀ F : Set G, F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} →
    ∃ (X : G → Subgroup G) (σ : G → M ⧸ CFSG.pCore 2 M), ∀ a ∈ F,
      (∀ g : G, g⁻¹ * z * g = a → CFSG.conjugate ((center Q).map Q.subtype) g = X a) ∧
      X a ≤ M ∧ IsCyclic (X a) ∧ ⁅(center Q).map Q.subtype, X a⁆ = ⊥ ∧
      normalizer (X a : Set G) = centralizer ({a} : Set G) ∧ X a ⊓ Q = zpowers a ∧
      (∀ t : G, zpowers t = X a → orderOf t = 4 ∧ t ^ 2 = a ∧ t ∉ Q ∧
        ∀ htM : t ∈ M, ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = σ a) ∧
      orderOf (σ a) = 2 ∧
      (∀ T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        T = ((ι (σ a) : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) →
        ∀ t : G, zpowers t = X a → ∀ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a →
        (∀ x, T x = x ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) * t = t * ((q : M) : G) ∧
          x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
        ∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = m ∧
          (centralizer ({t} : Set G)).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
          (∀ x, b x ((T - 1) x) =
            b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) ∧
          (m = 1 → ∀ x, T x = x +
            b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) •
              Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
          (m = 2 → ∃ u v₀ : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)),
            LinearIndependent (ZMod 2) ![u, v₀] ∧ b u v₀ = 0 ∧
            u + v₀ = Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∧
            ∃ τu τv : Module.End (ZMod 2)
                (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
              (∀ x, τu x = x + b x u • u) ∧ (∀ x, τv x = x + b x v₀ • v₀) ∧
              T = τu * τv ∧ τu * τv = τv * τu)) ∧
      Nonempty ((⨆ q ∈ Q, CFSG.conjugate (X a) q : Subgroup G) ≃*
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
      Q ≤ normalizer ((⨆ q ∈ Q, CFSG.conjugate (X a) q : Subgroup G) : Set G) ∧
      IsMulCommutative ((⨆ q ∈ Q, CFSG.conjugate (X a) q) ⊓ Q : Subgroup G) ∧
      Nat.card ((⨆ q ∈ Q, CFSG.conjugate (X a) q) ⊓ Q : Subgroup G) = 8 ∧
      (∀ (h : G) (hh : h ∈ M), h⁻¹ * a * h ∈ F ∧
        σ (h⁻¹ * a * h) = ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M)⁻¹ * σ a *
          ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M)) ∧
      a * z ∈ F ∧ ∀ b₀ ∈ F, σ a = σ b₀ ↔ b₀ = a ∨ b₀ = a * z := by
  intro F hF
  choose X σ hXσ using fused_choice hQ hzord huniq hMC hMNQ hMNZ hΦ hQ' hZ4 hconj hrule halt
    hnd ι hιf hF
  have hX : ∀ a ∈ F, ∀ g : G, g⁻¹ * z * g = a →
      CFSG.conjugate ((center Q).map Q.subtype) g = X a := fun a ha => (hXσ a ha).1
  have hσ : ∀ a ∈ F, ∀ t : G, zpowers t = X a → ∀ htM : t ∈ M,
      ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = σ a := fun a ha t ht =>
    ((hXσ a ha).2.2.2.2.2.2.1 t ht).2.2.2
  have hgen : ∀ a ∈ F, ∃ t ∈ M, zpowers t = X a := by
    intro a ha
    obtain ⟨t, htX, ht⟩ := exists_zpowers_eq_of_isCyclic (hXσ a ha).2.2.1
    exact ⟨t, (hXσ a ha).2.1 htX, ht⟩
  have hequiv := fused_equivariance hMC hMNQ hF hX hσ hgen
  have hid : ∀ a ∈ F, ∀ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a → ∀ x,
      b x (((((ι (σ a) : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
          Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1) x) =
        b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) := by
    intro a ha a₀ ha₀ x
    obtain ⟨t, -, ht⟩ := hgen a ha
    obtain ⟨-, m, -, -, -, hb, -⟩ := (hXσ a ha).2.2.2.2.2.2.2.2.1 _ rfl t ht a₀ ha₀
    exact hb x
  have hfib := fused_fibers hQ hzord huniq hfuse hF hequiv hnd ι hid
  refine ⟨X, σ, fun a ha => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hXσ a ha
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hequiv a ha, hfib a ha⟩

theorem width_package
    [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 3 ≤ CFSG.twoLocalOddRank G) {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hSyl : ∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b) (hι : Function.Injective ι)
    (hdim : ∃! v : ℕ, 1 ≤ v ∧ Module.finrank (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v)
    {w : ℕ} (hQcard : Nat.card Q = 2 ^ (2 * w + 2))
    (hVcard : Nat.card (Q ⧸ center Q) = 2 ^ (2 * w)) :
    ∃! v : ℕ, 2 ≤ v ∧ Nat.card Q = 2 ^ (2 * v + 2) ∧ Module.finrank (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v := by
  obtain ⟨v, ⟨hv1, hv⟩, -⟩ := hdim
  obtain ⟨e, -⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
      ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
    subst hQ
    exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective, fun _ => rfl⟩
  have hVQ : Nat.card (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 ^ (2 * w) := by
    rw [← hVcard, Nat.card_congr Additive.toMul,
      Nat.card_congr (QuotientGroup.congr _ _ e (map_center_eq e)).toEquiv]
  rw [natCard_eq_two_pow_finrank, hv] at hVQ
  have hvw : v = w := by
    have := Nat.pow_right_injective (le_refl 2) hVQ
    omega
  subst hvw
  have hPcard : Nat.card (CFSG.pCore 2 M) = 2 ^ (2 * v + 2) := by
    rw [Nat.card_congr e.toEquiv, hQcard]
  have hv2 := two_le_of_core_embedding hchar he hSyl ((bilinIsometryGroup b).subtype.comp ι)
    ((bilinIsometryGroup b).subtype_injective.comp hι) hv1 hPcard hv
  refine ⟨v, ⟨hv2, hQcard, hv⟩, fun v' hv' => ?_⟩
  have := hv'.2.2
  omega

theorem iota_conj_formula {M : Subgroup G}
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    {ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hρ : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b}
    (hιρ : ∀ h : M, ((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
      LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) = ρ h) :
    ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) := fun h x y hy => by
  rw [hιρ h]
  exact hρ h x y hy

theorem fused_base_package
    [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) :
    IsCharacteristicP 2 M ∧ Odd (Nat.card B) ∧ IsCyclic (center Q) ∧ Nat.card (center Q) = 4 ∧
    CFSG.IsElementaryAbelian 2 (Q ⧸ center Q) ∧
    (∃ w : ℕ, Nat.card Q = 2 ^ (2 * w + 2) ∧ Nat.card (Q ⧸ center Q) = 2 ^ (2 * w)) ∧
    ∃ z ∈ (center Q).map Q.subtype, orderOf z = 2 ∧
      (∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z) ∧
      M = centralizer ({z} : Set G) ∧ M = normalizer (Q : Set G) ∧
      M = normalizer ((center Q).map Q.subtype : Set G) ∧
      (∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤) ∧
      ⁅Q, Q⁆ = zpowers z ∧ (frattini Q).map Q.subtype = zpowers z ∧
      Nat.card ((center Q).map Q.subtype) = 4 ∧
      (∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
        (center Q).map Q.subtype ⊔ CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
        ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ∧
        IsCyclic (CFSG.conjugate ((center Q).map Q.subtype) g) ∧
        Nat.card (CFSG.conjugate ((center Q).map Q.subtype) g) =
          Nat.card ((center Q).map Q.subtype)) ∧
      ∀ t ∈ Q, t ∉ (center Q).map Q.subtype → orderOf t = 2 → ∃ q ∈ Q, q * t * q⁻¹ = t * z := by
  classical
  have hcharM : IsCharacteristicP 2 M := hchar M hM.1
  obtain ⟨⟨z, hzZ, hzord, huniq, hMC, hMNQ, hMNZ, hSyl⟩, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ rfl
  obtain ⟨⟨D, hD⟩, hBK⟩ := gf2_critical_center_and_exponent_four_reduction hchar he hM hsym hB hBM
    hQ hzZ hzord rfl
  obtain ⟨-, -, hZ₀cyc, -, -, -, -, -, -, -, -, -, -, -, hcase⟩ := hBK D hD _ rfl _ rfl
  have hnotB : ¬ (8 ≤ Nat.card ((center D).map D.subtype) ∧ ∃ x : Q, 8 ≤ orderOf x) := by
    rintro ⟨-, x, hx⟩
    have h1 : x ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hexp x x.2)
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
    omega
  obtain ⟨-, hDtop, hZ₀, hZ₀card, w, -, -, hQ', hΦ, hQcard, hVel, hVcard, -, -, -⟩ :=
    (hcase hnex).elim (fun h => h.1) fun h => absurd h.1 hnotB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hgcl, -⟩ := hBK D hD (center Q) hZ₀.symm _ rfl
  rw [hZ₀] at hZ₀cyc hZ₀card
  have hQ'G : ⁅Q, Q⁆ = zpowers z := by rw [← map_subtype_commutator]; exact hQ'
  have hSylM : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M := by
    obtain ⟨T₀⟩ : Nonempty (Sylow 2 M) := inferInstance
    obtain ⟨-, hT2, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp (hSyl _ ⟨T₀, rfl⟩).1
    rw [relIndex_top_right] at hidx
    exact ⟨hT2.toSylow hidx, by rw [IsPGroup.toSylow_coe]; exact map_subtype_le _⟩
  obtain ⟨-, hnc, -⟩ :=
    core_fusion_package hchar hzord hMC hcharM hQ hΦ hQ'G hZ₀cyc hSylM hzZ huniq
  refine ⟨hcharM, ?_, hZ₀cyc, hZ₀card, hVel, ⟨w, hQcard, hVcard⟩, z, hzZ, hzord, huniq, hMC, hMNQ,
    hMNZ, fun S hS => (hSyl S hS).1, hQ'G, hΦ, ?_, fun g hgQ hgz => ?_,
    fun t htQ htZ ht2 => (hnc t htQ htZ ht2).2.2.1⟩
  · rw [hB.2.1]
    exact Odd.pow (by decide)
  · rw [card_map_of_injective Q.subtype_injective]
    exact hZ₀card
  · have hD' : g⁻¹ * z * g ∈ D.map Q.subtype := by
      rw [hDtop, ← MonoidHom.range_eq_map, range_subtype]
      exact hgQ
    obtain ⟨h1, h2, -, h4, h5, -⟩ := (hgcl g).2.2.2.2 hD' hgz
    exact ⟨h1, h2, h4, h5⟩

end SteinbergCH

open SteinbergCH

theorem gf2_fused_center_four_involution_image
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) :
    Nat.card (center Q) = 4 ∧
    ∃ z ∈ (center Q).map Q.subtype, orderOf z = 2 ∧
      (∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z) ∧
      ⁅Q, Q⁆ = zpowers z ∧ (frattini Q).map Q.subtype = zpowers z ∧
      ∃ (_ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∃! v : ℕ, 2 ≤ v ∧ Nat.card Q = 2 ^ (2 * v + 2) ∧ Module.finrank (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v) ∧
        ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
          (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
            z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
              (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
          (∀ b' : LinearMap.BilinForm (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
            (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
              z ^ (b' (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
                (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) →
            b' = b) ∧
          b.IsAlt ∧ b.Nondegenerate ∧
          ∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
            (∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
              (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
                  LinearMap.GeneralLinearGroup (ZMod 2)
                    (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
                Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
                  (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
                Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
            ∀ F : Set G, F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} →
            ∃ (X : G → Subgroup G) (σ : G → M ⧸ CFSG.pCore 2 M), ∀ a ∈ F,
              (∀ g : G, g⁻¹ * z * g = a → CFSG.conjugate ((center Q).map Q.subtype) g = X a) ∧
              X a ≤ M ∧ IsCyclic (X a) ∧ ⁅(center Q).map Q.subtype, X a⁆ = ⊥ ∧
              normalizer (X a : Set G) = centralizer ({a} : Set G) ∧ X a ⊓ Q = zpowers a ∧
              (∀ t : G, zpowers t = X a → orderOf t = 4 ∧ t ^ 2 = a ∧ t ∉ Q ∧
                ∀ htM : t ∈ M, ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = σ a) ∧
              orderOf (σ a) = 2 ∧
              (∀ T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
                T = ((ι (σ a) : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
                  (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) →
                ∀ t : G, zpowers t = X a → ∀ a₀ : CFSG.pCore 2 M, ((a₀ : M) : G) = a →
                (∀ x, T x = x ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) * t = t * ((q : M) : G) ∧
                  x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
                ∃ m : ℕ, Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = m ∧
                  (centralizer ({t} : Set G)).relIndex Q = 2 ^ m ∧ (m = 1 ∨ m = 2) ∧
                  (∀ x, b x ((T - 1) x) =
                    b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) ∧
                  (m = 1 → ∀ x, T x = x +
                    b x (Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) •
                      Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
                  (m = 2 → ∃ u v₀ : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)),
                    LinearIndependent (ZMod 2) ![u, v₀] ∧ b u v₀ = 0 ∧
                    u + v₀ = Additive.ofMul (a₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∧
                    ∃ τu τv : Module.End (ZMod 2)
                        (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
                      (∀ x, τu x = x + b x u • u) ∧ (∀ x, τv x = x + b x v₀ • v₀) ∧
                      T = τu * τv ∧ τu * τv = τv * τu)) ∧
              Nonempty ((⨆ q ∈ Q, CFSG.conjugate (X a) q : Subgroup G) ≃*
                Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
              Q ≤ normalizer ((⨆ q ∈ Q, CFSG.conjugate (X a) q : Subgroup G) : Set G) ∧
              IsMulCommutative ((⨆ q ∈ Q, CFSG.conjugate (X a) q) ⊓ Q : Subgroup G) ∧
              Nat.card ((⨆ q ∈ Q, CFSG.conjugate (X a) q) ⊓ Q : Subgroup G) = 8 ∧
              (∀ (h : G) (hh : h ∈ M), h⁻¹ * a * h ∈ F ∧
                σ (h⁻¹ * a * h) = ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M)⁻¹ * σ a *
                  ((⟨h, hh⟩ : M) : M ⧸ CFSG.pCore 2 M)) ∧
              a * z ∈ F ∧ ∀ b₀ ∈ F, σ a = σ b₀ ↔ b₀ = a ∨ b₀ = a * z := by
  obtain ⟨hcharM, hBodd, hZcyc, hZcard, hVel, ⟨w, hQcard, hVcard⟩, z, hzZ, hzord, huniq, hMC,
    hMNQ, hMNZ, hSyl, hQ'G, hΦ, hZ4, hconj, hfuse⟩ :=
    fused_base_package hchar he hM hsym hB hBM hQ hnex hexp
  obtain ⟨hVel₀, hdim, b, hrule, huniqb, halt, hnd, ρ, hρ, -, -, ⟨ι, hιinj, hιρ⟩, -⟩ :=
    core_symplectic_transport hBM hcharM hBodd hQ hZcyc hVel hzZ hzord hQ'G
  exact ⟨hZcard, z, hzZ, hzord, huniq, hQ'G, hΦ, hVel₀,
    width_package hchar he hQ hSyl ι hιinj hdim hQcard hVcard, b, hrule, huniqb, halt, hnd, ι,
    hιinj, iota_conj_formula hρ hιρ,
    fused_image_package hQ hzord huniq hMC hMNQ hMNZ hΦ hQ'G hZ4 hconj hrule halt hnd ι
      (iota_conj_formula hρ hιρ) hfuse⟩

end CFSG.LocalAnalysis.GorensteinLyons
