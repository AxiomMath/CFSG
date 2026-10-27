module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourS0FusionTransfer
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXMutualFourRoots
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCosetFusion
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBNGF2MovedFactorCentralizers

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

namespace SteinbergCG

variable {G : Type*} [Group G]

theorem mem_conjugate_iff_cg {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem conjugate_inf_cg (H K : Subgroup G) (h : G) :
    CFSG.conjugate (H ⊓ K) h = CFSG.conjugate H h ⊓ CFSG.conjugate K h := by
  ext y
  simp only [mem_inf, mem_conjugate_iff_cg]

theorem conjugate_zpowers_cg (c h : G) :
    CFSG.conjugate (zpowers c) h = zpowers (h⁻¹ * c * h) := by
  unfold CFSG.conjugate
  rw [MonoidHom.map_zpowers]
  simp

theorem centralizer_conj_cg (x h : G) :
    centralizer ({h⁻¹ * x * h} : Set G) = CFSG.conjugate (centralizer ({x} : Set G)) h := by
  ext y
  rw [mem_conjugate_iff_cg, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    calc h * y * h⁻¹ * x = h * (y * (h⁻¹ * x * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * x * h) * y) * h⁻¹ := by rw [hy]
      _ = x * (h * y * h⁻¹) := by group
  · intro hy
    calc y * (h⁻¹ * x * h) = h⁻¹ * ((h * y * h⁻¹) * x) * h := by group
      _ = h⁻¹ * (x * (h * y * h⁻¹)) * h := by rw [hy]
      _ = h⁻¹ * x * h * y := by group

theorem twoCore_centralizer_conj (x h : G) :
    CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({h⁻¹ * x * h} : Set G)) =
      CFSG.conjugate (CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({x} : Set G))) h := by
  ext y
  rw [mem_conjugate_iff_cg]
  constructor
  · intro hy
    have h1 := conj_mem_twoCore_conj (h := h⁻¹) hy
    rwa [inv_inv, show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at h1
  · intro hy
    have h1 := conj_mem_twoCore_conj (h := h) hy
    rwa [show h⁻¹ * (h * y * h⁻¹) * h = y by group] at h1

theorem center_conjugate (H : Subgroup G) (h : G) :
    (center (CFSG.conjugate H h)).map (CFSG.conjugate H h).subtype =
      CFSG.conjugate ((center H).map H.subtype) h := by
  rw [SteinbergBN.map_center_subtype_eq, SteinbergBN.map_center_subtype_eq,
    conjugate_inf_cg]
  congr 1
  ext y
  rw [mem_centralizer_iff, mem_conjugate_iff_cg, mem_centralizer_iff]
  constructor
  · intro hy k hk
    have hk' : h⁻¹ * k * h ∈ CFSG.conjugate H h := by
      rw [mem_conjugate_iff_cg, show h * (h⁻¹ * k * h) * h⁻¹ = k by group]
      exact hk
    have h1 := hy _ hk'
    calc k * (h * y * h⁻¹) = h * ((h⁻¹ * k * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * k * h)) * h⁻¹ := by rw [h1]
      _ = h * y * h⁻¹ * k := by group
  · intro hy k hk
    rw [SetLike.mem_coe, mem_conjugate_iff_cg] at hk
    have h1 := hy _ hk
    calc k * y = h⁻¹ * ((h * k * h⁻¹) * (h * y * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * y * h⁻¹) * (h * k * h⁻¹)) * h := by rw [h1]
      _ = y * k := by group

theorem isElementaryAbelian_conjugate_cg {p : ℕ} {H : Subgroup G}
    (hH : CFSG.IsElementaryAbelian p H) (h : G) :
    CFSG.IsElementaryAbelian p (CFSG.conjugate H h) := by
  let e : CFSG.conjugate H h ≃* H :=
    (H.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).symm
  exact { is_comm := ⟨fun x y => e.injective (by
            rw [map_mul, map_mul]
            exact hH.1.1.1 (e x) (e y))⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => e.injective (by
            rw [map_pow, map_one]
            exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hH.2 (e x)) }

theorem exists_isSylowOf_mem_of_orderOf [Finite G] {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hx : orderOf x = 2) : ∃ S : Subgroup G, IsSylowOf 2 S M ∧ x ∈ S := by
  have := Fact.mk Nat.prime_two
  have hx' : orderOf (⟨x, hxM⟩ : M) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hx
  have hP : IsPGroup 2 (zpowers (⟨x, hxM⟩ : M)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx', pow_one])
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  exact ⟨_, ⟨T, rfl⟩, ⟨⟨x, hxM⟩, hT (mem_zpowers _), rfl⟩⟩

theorem twoCore_le_of_isSylowOf [Finite G] {M S : Subgroup G} (hS : IsSylowOf 2 S M) :
    CFSG.inSubgroup (CFSG.pCore 2) M ≤ S := by
  have := Fact.mk Nat.prime_two
  obtain ⟨T, rfl⟩ := hS
  exact map_mono (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup T)

theorem core_fusion_contradiction
    {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {Z : Subgroup G}
    (hZ : Z = (center Q).map Q.subtype) {z : G} (hzZ : z ∈ Z) (hz : orderOf z = 2)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z}) : False := by
  classical
  have := Fact.mk Nat.prime_two
  have hQ2 : IsPGroup 2 Q := hQ ▸ CFSG.pCore_isPGroup.map M.subtype
  have hZQ : Z ≤ Q := by
    rw [hZ]
    exact map_subtype_le _
  have hzQ : z ∈ Q := hZQ hzZ
  have hQCZ : Q ≤ centralizer (Z : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro w hw
    rw [hZ] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact (congrArg Subtype.val (mem_center_iff.mp hw' ⟨x, hx⟩)).symm
  have hconj_order : ∀ g x : G, orderOf (g⁻¹ * x * g) = orderOf x := fun g x => by
    have h1 := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
    simpa [MulAut.conj_apply] using h1
  have hzinv : z⁻¹ = z :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_two, ← hz, pow_orderOf_eq_one])
  have hSymp := gf2_center_four_symplectic_embedding_and_fusion hchar (by omega) hM hsym hB hBM
    hQ hnex hexp
  obtain ⟨hZcyc, hZ4, z₁, -, -, hz₁u, hRest₁⟩ := hSymp
  have hz1 : z₁ = z := (hz₁u z (hZ ▸ hzZ) hz).symm
  rw [hz1] at hRest₁
  obtain ⟨hQ'z, -, -, hMC, -, -, -, -⟩ := hRest₁
  have hQz : Q = CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({z} : Set G)) := by
    rw [hQ, hMC]
  have hCyc := gf2_center_four_all_cyclic_root_images_and_weak_closure_obstruction hchar
    (by omega) hM hsym hB hBM hQ hnex hexp Z hZ
  obtain ⟨z₂, -, -, hz₂u, hRest₂⟩ := hCyc
  have hz2 : z₂ = z := (hz₂u z hzZ hz).symm
  rw [hz2] at hRest₂
  obtain ⟨hVel, bform, -, -, -, ι, -, -, hFcl⟩ := hRest₂
  have hFcl' := hFcl _ rfl
  obtain ⟨-, -, -, -, -, -, -, hFinv, hFsyl⟩ := hFcl'
  have hF0 : ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} = ∅ := by
    rw [hwc, Set.sdiff_self]
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hSyl := hFsyl hF0 hsimple hnab S hS
  obtain ⟨-, -, -, -, a, haS, ⟨h, hzh⟩, haS0⟩ := hSyl
  have hQS : Q ≤ S := hQ ▸ twoCore_le_of_isSylowOf hS
  have hzS0 : z ∈ S ⊓ centralizer (Z : Set G) := ⟨hQS hzQ, hQCZ hzQ⟩
  have haz : a ≠ z := fun h1 => haS0 (h1 ▸ hzS0)
  have haQ : a ∉ Q := fun h1 => haS0 ⟨hQS h1, hQCZ h1⟩
  have haM : a ∈ M := hS.le haS
  have haC : a * z = z * a := mem_centralizer_singleton_iff.mp (hMC ▸ haM)
  have ha2 : orderOf a = 2 := by
    rw [← hzh, hconj_order, hz]
  have hainv2 : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_two, ← ha2, pow_orderOf_eq_one])
  have hT := gf2_center_four_S0_fusion_transfer_maximal_rank_images hsimple hnab hchar he hM hsym
    hB hBM hQ hnex hexp hZ hzZ hz hwc hS rfl
  obtain ⟨hVel', b', -, -, -, -, -, v, -, hv4, -, -, -, -, -, haT⟩ := hT
  have hA := haT a ⟨⟨⟨h, hzh⟩, haS⟩, haz⟩
  obtain ⟨-, -, hainv, -, -, -, hPcl⟩ := hA
  have hPa := hPcl _ rfl
  obtain ⟨hPel, hPcard, -, -, -, -, -, hDcl⟩ := hPa
  have hDa := hDcl _ rfl
  obtain ⟨hDmem, -, -, -, -, hDZP, -, -, haQD, hXor, -, -⟩ := hDa
  have ha'G : ∃ g : G, g⁻¹ * z * g = h * z * h⁻¹ := ⟨h⁻¹, by group⟩
  have ha'M : h * z * h⁻¹ ∈ M := by
    rw [hMC, mem_centralizer_singleton_iff]
    calc h * z * h⁻¹ * z = h * (z * (h⁻¹ * z * h)) * h⁻¹ := by group
      _ = h * (z * a) * h⁻¹ := by rw [hzh]
      _ = h * (a * z) * h⁻¹ := by rw [haC]
      _ = h * ((h⁻¹ * z * h) * z) * h⁻¹ := by rw [hzh]
      _ = z * (h * z * h⁻¹) := by group
  have ha'z : h * z * h⁻¹ ≠ z := by
    intro h1
    apply haz
    rw [← hzh]
    calc h⁻¹ * z * h = h⁻¹ * (h * z * h⁻¹) * h := by rw [h1]
      _ = z := by group
  have ha'inv := (hFinv hF0 (h * z * h⁻¹) ⟨⟨ha'G, ha'M⟩, ha'z⟩).2
  have ha'o : orderOf (h * z * h⁻¹) = 2 := by
    have h1 := hconj_order h⁻¹ z
    rwa [inv_inv, hz] at h1
  obtain ⟨S', hS', ha'S'⟩ := exists_isSylowOf_mem_of_orderOf ha'M ha'o
  have hT' := gf2_center_four_S0_fusion_transfer_maximal_rank_images hsimple hnab hchar he hM
    hsym hB hBM hQ hnex hexp hZ hzZ hz hwc hS' rfl
  obtain ⟨hVel'', b'', -, -, -, -, -, v', -, -, -, -, -, -, -, ha'T⟩ := hT'
  have hA' := ha'T (h * z * h⁻¹) ⟨⟨ha'G, ha'S'⟩, ha'z⟩
  obtain ⟨-, -, -, -, -, -, hP'cl⟩ := hA'
  have hP'a := hP'cl _ rfl
  obtain ⟨hP'el, -⟩ := hP'a
  obtain ⟨c0, hc0⟩ := hZcyc.exists_generator
  have hZc : Z = zpowers ((c0 : Q) : G) := by
    rw [hZ]
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hc0 ⟨y, hy⟩)
      refine mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h1 := congrArg (fun t : center Q => ((t : Q) : G)) hk
      simpa using h1
    · rw [zpowers_le]
      exact ⟨c0, c0.2, rfl⟩
  have hcZ : ((c0 : Q) : G) ∈ Z := by
    rw [hZc]
    exact mem_zpowers _
  have hc4 : orderOf ((c0 : Q) : G) = 4 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hc0,
      hZ4]
  have hc2 : ((c0 : Q) : G) ^ 2 = z := by
    refine (hz₁u _ ?_ ?_).trans hz1
    · rw [← hZ, hZc]
      exact pow_mem (mem_zpowers _) 2
    · rw [orderOf_pow' _ two_ne_zero, hc4]
      rfl
  have hQa : CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)) =
      CFSG.conjugate Q h := by
    rw [← hzh, twoCore_centralizer_conj, ← hQz]
  have hZa : (center (CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)))).map
      (CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G))).subtype =
      zpowers (h⁻¹ * ((c0 : Q) : G) * h) := by
    rw [hQa, center_conjugate, ← hZ, hZc, conjugate_zpowers_cg]
  have hR : CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)) ⊓
      centralizer ({z} : Set G) =
      CFSG.conjugate (Q ⊓ centralizer ({h * z * h⁻¹} : Set G)) h := by
    rw [hQa, conjugate_inf_cg, ← centralizer_conj_cg,
      show h⁻¹ * (h * z * h⁻¹) * h = z by group]
  have hRe : CFSG.IsElementaryAbelian 2 ↥(CFSG.inSubgroup (CFSG.pCore 2)
      (centralizer ({a} : Set G)) ⊓ centralizer ({z} : Set G)) := by
    rw [hR]
    exact isElementaryAbelian_conjugate_cg hP'el h
  have hs2 : (h⁻¹ * ((c0 : Q) : G) * h) ^ 2 = a := by
    rw [← hzh, ← hc2, pow_two, pow_two]
    group
  have hca : a⁻¹ * ((c0 : Q) : G) * a = ((c0 : Q) : G)⁻¹ := by
    have h1 := hainv _ hcZ
    rw [hainv2] at h1 ⊢
    exact h1
  have ha'inv' : (h * z * h⁻¹)⁻¹ * ((c0 : Q) : G) * (h * z * h⁻¹) = ((c0 : Q) : G)⁻¹ := by
    have h1 := ha'inv _ hcZ
    have ha'2 : (h * z * h⁻¹)⁻¹ = h * z * h⁻¹ := by
      rw [show (h * z * h⁻¹)⁻¹ = h * z⁻¹ * h⁻¹ by group, hzinv]
    rw [ha'2] at h1 ⊢
    exact h1
  have hsz : z⁻¹ * (h⁻¹ * ((c0 : Q) : G) * h) * z = (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ := by
    calc z⁻¹ * (h⁻¹ * ((c0 : Q) : G) * h) * z =
          h⁻¹ * ((h * z * h⁻¹)⁻¹ * ((c0 : Q) : G) * (h * z * h⁻¹)) * h := by group
      _ = h⁻¹ * ((c0 : Q) : G)⁻¹ * h := by rw [ha'inv']
      _ = (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ := by group
  have hcZQ : (center Q).map Q.subtype = zpowers ((c0 : Q) : G) := by
    rw [← hZ, hZc]
  have hMR := mutual_cyclic_four_roots_elementary_common_centralizer hz ha2 haz.symm haC.symm
    (U := closure ({z, a} : Set G))
    (N := normalizer ((closure ({z, a} : Set G) : Subgroup G) : Set G))
    (C := centralizer ((closure ({z, a} : Set G) : Subgroup G) : Set G)) (Qz := Q)
    (Qa := CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)))
    (P := Q ⊓ centralizer ({a} : Set G))
    (R := CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)) ⊓
      centralizer ({z} : Set G))
    (K := Q ⊓ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)))
    rfl rfl rfl hQz rfl rfl rfl rfl hcZQ hZa hc2 hs2 hca hsz hPel hRe
  obtain ⟨-, -, -, -, -, ⟨-, hPR, -, -, -, -⟩, -, hNPR, -, -, -, ⟨hsa, hszs, hszas⟩, hza1⟩ := hMR
  have hsU : h⁻¹ * ((c0 : Q) : G) * h ∈
      normalizer ((closure ({z, a} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun x hx => ?_
    have hle : closure ({z, a} : Set G) ≤ (closure ({z, a} : Set G)).comap
        (MulAut.conj (h⁻¹ * ((c0 : Q) : G) * h)).toMonoidHom := by
      rw [closure_le]
      intro y hy
      rcases hy with hy | hy
      · rw [hy]
        change (MulAut.conj (h⁻¹ * ((c0 : Q) : G) * h)) z ∈ closure ({z, a} : Set G)
        rw [MulAut.conj_apply]
        have h1 : h⁻¹ * ((c0 : Q) : G) * h * z * (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ = z * a := by
          calc h⁻¹ * ((c0 : Q) : G) * h * z * (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ =
                h⁻¹ * ((c0 : Q) : G) * h * ((h⁻¹ * ((c0 : Q) : G) * h)⁻¹ * (z * a) *
                  (h⁻¹ * ((c0 : Q) : G) * h)) * (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ := by
                rw [hszas]
            _ = z * a := by group
        rw [h1]
        exact mul_mem (subset_closure (Set.mem_insert z _))
          (subset_closure (Set.mem_insert_of_mem z rfl))
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        change (MulAut.conj (h⁻¹ * ((c0 : Q) : G) * h)) a ∈ closure ({z, a} : Set G)
        rw [MulAut.conj_apply]
        have h1 : h⁻¹ * ((c0 : Q) : G) * h * a * (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ = a := by
          calc h⁻¹ * ((c0 : Q) : G) * h * a * (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ =
                h⁻¹ * ((c0 : Q) : G) * h * ((h⁻¹ * ((c0 : Q) : G) * h)⁻¹ * a *
                  (h⁻¹ * ((c0 : Q) : G) * h)) * (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ := by
                rw [hsa]
            _ = a := by group
        rw [h1]
        exact subset_closure (Set.mem_insert_of_mem z rfl)
    exact hle hx
  have hsE : h⁻¹ * ((c0 : Q) : G) * h ∈
      normalizer ((Q ⊓ centralizer ({a} : Set G) ⊔ zpowers a : Subgroup G) : Set G) := by
    rw [← hPR]
    exact hNPR hsU
  have hQ'c : ⁅Q, Q⁆ ≤ zpowers (((c0 : Q) : G) ^ 2) := by
    rw [hc2, hQ'z]
  have haNQ : a ∈ normalizer (Q : Set G) := by
    rw [hQ]
    exact SteinbergBN.le_normalizer_core M haM
  have hDdef : ⁅Q, zpowers a⁆ = closure {x | ∃ q ∈ Q, x = q⁻¹ * a⁻¹ * q * a} := by
    have hset : {x | ∃ q ∈ Q, x = q⁻¹ * a⁻¹ * q * a} = ((⁅Q, zpowers a⁆ : Subgroup G) : Set G) := by
      ext x
      exact (hDmem x).symm
    rw [hset, closure_eq]
  have hDZP' : ⁅Q, zpowers a⁆ ≤ (center Q).map Q.subtype ⊔ (Q ⊓ centralizer ({a} : Set G)) := by
    rw [← hZ]
    exact hDZP
  have haQD' : (fun q => q⁻¹ * a * q) '' (Q : Set G) =
      a • ((⁅Q, zpowers a⁆ : Subgroup G) : Set G) := by
    ext w
    have h1 := Set.ext_iff.mp haQD w
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    simpa using h1
  have hF4 : 4 ≤ Nat.card (⁅Q, zpowers a⁆ ⊓ (Q ⊓ centralizer ({a} : Set G)) : Subgroup G) := by
    rcases hXor with ⟨⟨hDP, -⟩, -⟩ | ⟨⟨-, hcardDP⟩, -⟩
    · rw [hDP, inf_idem, hPcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hcardDP]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzG : ∀ x ∈ Q, IsConj (((c0 : Q) : G) ^ 2) x ↔ x = ((c0 : Q) : G) ^ 2 := by
    intro x hx
    rw [hc2]
    constructor
    · intro hxc
      obtain ⟨g, hg⟩ := isConj_iff.mp hxc
      have hxS : x ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) :=
        ⟨⟨g⁻¹, by rw [inv_inv]; exact hg⟩, hx⟩
      rw [hwc] at hxS
      exact hxS
    · rintro rfl
      exact IsConj.refl _
  have hCF := class_two_involution_coset_fusion_product hQ2 (hZQ hcZ) hcZQ hc4 hQ'c haNQ haQ ha2
    hca (P := Q ⊓ centralizer ({a} : Set G)) (D := ⁅Q, zpowers a⁆)
    (F := ⁅Q, zpowers a⁆ ⊓ (Q ⊓ centralizer ({a} : Set G)))
    (E := Q ⊓ centralizer ({a} : Set G) ⊔ zpowers a) rfl hDdef rfl rfl hPel hDZP' haQD' hF4 hzG
  obtain ⟨-, -, -, -, hNE⟩ := hCF
  have hsz' := hNE hsE
  rw [hc2, mem_centralizer_singleton_iff] at hsz'
  apply hza1
  rw [← hszs]
  calc (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ * z * (h⁻¹ * ((c0 : Q) : G) * h) =
        (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ * (z * (h⁻¹ * ((c0 : Q) : G) * h)) := by group
    _ = (h⁻¹ * ((c0 : Q) : G) * h)⁻¹ * ((h⁻¹ * ((c0 : Q) : G) * h) * z) := by rw [hsz']
    _ = z := by group

end SteinbergCG

open SteinbergCG

theorem gf2_center_four_nonempty_core_fusion
    {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {Z : Subgroup G}
    (hZ : Z = (center Q).map Q.subtype) {z : G} (hzZ : z ∈ Z) (hz : orderOf z = 2) :
    (({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z}).Nonempty ∧
    ¬ (∀ g : G, CFSG.conjugate Z g ≤ M → CFSG.conjugate Z g = Z) ∧
    ∀ S : Subgroup G, IsSylowOf 2 S M →
      {w | ∃ g : G, g⁻¹ * z * g = w} ∩ ((S ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) ≠
        {z} := by
  classical
  have hZQ : Z ≤ Q := by
    rw [hZ]
    exact map_subtype_le _
  have hQCZ : Q ≤ centralizer (Z : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro w hw
    rw [hZ] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact (congrArg Subtype.val (mem_center_iff.mp hw' ⟨x, hx⟩)).symm
  have hzQ : z ∈ Q := hZQ hzZ
  have hF0 : ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} ≠ ∅ := by
    intro hF0
    have hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z} := by
      ext w
      constructor
      · intro hw
        by_contra hwz
        have h1 : w ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} := ⟨hw, hwz⟩
        rw [hF0] at h1
        exact h1
      · rintro rfl
        exact ⟨⟨1, by group⟩, hzQ⟩
    exact core_fusion_contradiction hsimple hnab hchar he hM hsym hB hBM hQ hnex hexp hZ hzZ hz
      hwc
  have hCyc := gf2_center_four_all_cyclic_root_images_and_weak_closure_obstruction hchar
    (by omega) hM hsym hB hBM hQ hnex hexp Z hZ
  obtain ⟨z₂, -, -, hz₂u, hRest₂⟩ := hCyc
  have hz2 : z₂ = z := (hz₂u z hzZ hz).symm
  rw [hz2] at hRest₂
  obtain ⟨hVel, bform, -, -, -, ι, -, -, hFcl⟩ := hRest₂
  have hFcl' := hFcl _ rfl
  obtain ⟨-, -, -, -, -, hFwc, -, -, -⟩ := hFcl'
  have hne := Set.nonempty_iff_ne_empty.mpr hF0
  refine ⟨hne, fun hwcl => hF0 (hFwc.mpr hwcl), fun S hS hS0 => ?_⟩
  obtain ⟨x, ⟨hxG, hxQ⟩, hxz⟩ := hne
  have hQS : Q ≤ S := hQ ▸ twoCore_le_of_isSylowOf hS
  have hxS0 : x ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩
      ((S ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := ⟨hxG, hQS hxQ, hQCZ hxQ⟩
  rw [hS0] at hxS0
  exact hxz hxS0

end CFSG.LocalAnalysis.GorensteinLyons
