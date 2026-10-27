module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelFusion
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverData

public section

namespace CFSG.ComponentClassification.M12Cover

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise
open CyclicKernel

theorem ctss_m12_original_large_cyclic_kernel_false {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ x : G, orderOf x = 2 → CFSG.Assembly.oddCore (centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) {t : G} (ht : orderOf t = 2)
    (hZ : (center L).map L.subtype = zpowers t)
    (hQ : NativeSporadic.IsSporadic (L ⧸ center L) .M12) (hS4 : 4 ≤ Nat.card S) : False := by
  classical
  obtain ⟨hCL, hCH, -, -, -, -, -, -, -, -, hLSfix, ⟨g, hg, hpH, hpLS⟩, hext⟩ :=
    ctss_m12_original_large_cyclic_kernel_fusion_reduction hnonab hL hcore S hS ht hZ hQ rfl rfl
      hS4
  set T := (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    with hTdef
  obtain ⟨p, hpdef⟩ : ∃ p : G, p = g⁻¹ * t * g := ⟨_, rfl⟩
  rw [← hpdef] at hpH hpLS
  obtain ⟨hidx2, -, hTp, hinv, -, -, -⟩ := hext g p hpdef hg hpH hpLS
  have htL : t ∈ L := by
    have h : t ∈ (center L).map L.subtype := by rw [hZ]; exact mem_zpowers t
    obtain ⟨z, -, rfl⟩ := h
    exact z.2
  set t' : L := ⟨t, htL⟩ with ht'def
  have hZ' : center L = zpowers t' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hZ, MonoidHom.map_zpowers]
    rfl
  have ht' : orderOf t' = 2 := by rw [ht'def, Subgroup.orderOf_mk, ht]
  have htZ : t' ∈ center L := hZ' ▸ mem_zpowers t'
  have hLq : CFSG.Assembly.IsQuasisimple L := hL.1
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    congrArg Subtype.val (mem_center_iff.mp htZ ⟨l, hl⟩)
  have hHN : centralizer {t} ≤ normalizer (L : Set G) :=
    (LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL htC ht).1
  obtain ⟨φ₀⟩ := hQ
  let φ : L ⧸ center L ≃* NativeSporadic.M12 := φ₀
  let π : L →* NativeSporadic.M12 := φ.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = zpowers t' := hkerZ.trans hZ'
  have htT : t ∈ T := by rw [← hCL]; exact htC
  have hTc : IsCyclic T := isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have hT2 : IsPGroup 2 T := S.isPGroup'.map _
  have hT4 : 4 ≤ Nat.card T := by
    rw [hTdef, card_map_of_injective (subtype_injective _)]
    exact hS4
  have hpt : p * t = t * p := mem_centralizer_singleton_iff.mp hpH
  have hp2 : orderOf p = 2 := by
    rw [hpdef, show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, ht]
  have hqH : g * t * g⁻¹ ∈ centralizer {t} := by
    rw [mem_centralizer_singleton_iff]
    calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (t * p) * g⁻¹ := by rw [hpdef]
      _ = g * (p * t) * g⁻¹ := by rw [← hpt]
      _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [hpdef]
      _ = t * (g * t * g⁻¹) := by group
  have hg' : g⁻¹ ∉ centralizer {t} := fun h => hg (by simpa using inv_mem h)
  have hqLS : g * t * g⁻¹ ∉ L ⊔ T := by
    intro h
    have h' := hLSfix g⁻¹ (by rwa [inv_inv])
    rw [inv_inv] at h'
    apply hg
    rw [mem_centralizer_singleton_iff]
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h']
  obtain ⟨-, -, -, hinvq, -⟩ := hext g⁻¹ (g * t * g⁻¹) (by rw [inv_inv]) hg' hqH hqLS
  obtain ⟨a, haT, ha4⟩ := exists_orderOf_eq_four_of_isCyclic hTc hT2 (by omega)
  have ha2 : a ^ 2 = t :=
    eq_of_orderOf_eq_two_of_isCyclic hTc (pow_mem haT 2) htT (orderOf_sq_of_orderOf_eq_four ha4)
      ht
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hroot : ∀ q : G, q * a * q⁻¹ = a⁻¹ → a⁻¹ * q * a = t * q := by
    intro q hq
    have h1 : q * a = a⁻¹ * q := by rw [← hq]; group
    calc a⁻¹ * q * a = a⁻¹ * (q * a) := by group
      _ = a⁻¹ * (a⁻¹ * q) := by rw [h1]
      _ = (a * a)⁻¹ * q := by group
      _ = t * q := by rw [← sq, ha2, htinv]
  have hpa : a⁻¹ * p * a = t * p := hroot p (hinv a haT ha4)
  have hqa : a⁻¹ * (g * t * g⁻¹) * a = t * (g * t * g⁻¹) := hroot _ (hinvq a haT ha4)
  have hb2 : (g⁻¹ * a * g) ^ 2 = p := by
    rw [hpdef, show g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ by rw [inv_inv], conj_pow, ha2, inv_inv]
  have htb : (g⁻¹ * a * g)⁻¹ * t * (g⁻¹ * a * g) = t * p := by
    calc (g⁻¹ * a * g)⁻¹ * t * (g⁻¹ * a * g) = g⁻¹ * (a⁻¹ * (g * t * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (t * (g * t * g⁻¹)) * g := by rw [hqa]
      _ = p * t := by rw [hpdef]; group
      _ = t * p := hpt
  have hHp : L ⊔ T ⊔ zpowers p = centralizer {t} := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) (zpowers_le.mpr hpH)
      · intro l hl
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_center_iff.mp htZ ⟨l, hl⟩))
      · rw [← hCH]
        exact inf_le_right
    · intro h hh
      by_cases hhLS : h ∈ L ⊔ T
      · exact mem_sup_left hhLS
      · have hmul : (⟨h, hh⟩ : centralizer ({t} : Set G)) * ⟨p, hpH⟩ ∈
            (L ⊔ T).subgroupOf (centralizer {t}) := by
          rw [mul_mem_iff_of_index_two hidx2, mem_subgroupOf, mem_subgroupOf]
          exact iff_of_false hhLS hpLS
        rw [mem_subgroupOf] at hmul
        have h' : h = h * p * p⁻¹ := by group
        rw [h']
        exact mul_mem (mem_sup_left hmul) (inv_mem (mem_sup_right (mem_zpowers p)))
  obtain ⟨hAL, -, hAcard, -, hAout, -, hderC, hAchar, -⟩ :=
    ctss_m12_outer_involution_full_cyclic_kernel_common_centralizer_ambient hLq ht' hZ' hHN π hπ
      hker (by rw [← hCH, inf_comm]) hTc hT2 hT4 hpH hp2 hpLS hHp hTp rfl
  have hAC : ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ ≤
      centralizer (closure ({t, p} : Set G) : Set G) := by
    rw [← hderC]
    exact commutator_le_self _
  have hpN : p ∈ normalizer (L : Set G) := hHN hpH
  have hpC : ∀ l ∈ L, l * p ∉ centralizer (L : Set G) := fun l hl h => hpLS (by
    have h' : p = l⁻¹ * (l * p) := by group
    rw [h']
    exact mul_mem (mem_sup_left (inv_mem hl)) (mem_sup_right (by rw [← hCL]; exact h)))
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  obtain ⟨θ, hθ, -⟩ := exists_normalizer_action hHN π hπ hkerZ
  obtain ⟨-, -, -, hfusL, -⟩ := external_data_of_mem_normalizer hLq ht' hZ' π hπ hker hpN hp2 hpC
    (θ ⟨p, hpH⟩) (fun l l' h => hθ ⟨p, hpH⟩ l l' h)
  have hpp : p * p = 1 := by rw [← sq, ← hp2, pow_orderOf_eq_one]
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
  have hfus : ∀ z ∈ ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆, orderOf z = 2 →
      IsConj (p * z) p := by
    intro z hz hz2
    have hzC : z ∈ L ⊓ centralizer {p} := commutator_le_self _ hz
    obtain ⟨hzL, hzp⟩ := mem_inf.mp hzC
    have hzp' : z * p = p * z := mem_centralizer_singleton_iff.mp hzp
    have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
    have hpzL : p * z * p ∈ L := by
      have h := (mem_normalizer_iff.mp hpN z).mp hzL
      rwa [hpinv] at h
    have hpz2 : orderOf (p * z) = 2 := by
      refine orderOf_eq_prime ?_ fun h => hpLS (mem_sup_left ?_)
      · rw [sq]
        calc p * z * (p * z) = p * (z * p) * z := by group
          _ = (p * p) * (z * z) := by rw [hzp']; group
          _ = 1 := by rw [hpp, hzz, one_mul]
      · rw [eq_inv_of_mul_eq_one_left h]
        exact inv_mem hzL
    obtain ⟨l, hl⟩ := hfusL (p * z) hpzL hpz2
    exact (isConj_iff.mpr ⟨(l : G), hl⟩).symm
  obtain ⟨⟨z, hzA, hz2, hzt⟩, -⟩ :=
    CentralCover.two_inverting_four_roots_characteristic_factor_force_fusion ht hp2
      (show Commute t p from hpt.symm) ha2 hb2 hpa htb hAC hAchar
      (by rw [hAcard]; exact ⟨30, rfl⟩) (fun h3 => absurd (dvd_trans h3 hAout) (by norm_num))
      hfus (isConj_iff.mpr ⟨g, by rw [hpdef]; group⟩)
  obtain ⟨c, hc⟩ := isConj_iff.mp hzt
  have hzL : z ∈ L := hAL hzA
  have htz : c⁻¹ * t * c = t * z := by
    calc c⁻¹ * t * c = c⁻¹ * (c * (t * z) * c⁻¹) * c := by rw [hc]
      _ = t * z := by group
  have h1 := hLSfix c (by rw [htz]; exact mem_sup_left (mul_mem htL hzL))
  rw [htz, mul_eq_left] at h1
  rw [h1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem ctss_m12_central_double_cover_local_kernel_frontier :
    StandardRecognition.LocalKernel .M12 := by
  intro G _ _ _ hnonab _ L hL hcore S hS t ht hZ hQ
  classical
  have htL : t ∈ L := by
    have h : t ∈ (center L).map L.subtype := by rw [hZ]; exact mem_zpowers t
    obtain ⟨z, -, rfl⟩ := h
    exact z.2
  have htC : t ∈ centralizer (L : Set G) := by
    have h : t ∈ (center L).map L.subtype := by rw [hZ]; exact mem_zpowers t
    obtain ⟨z, hz, hzt⟩ := h
    rw [mem_centralizer_iff]
    intro l hl
    rw [← hzt]
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
  have ht₁ : orderOf (⟨t, htC⟩ : centralizer (L : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk, ht]
  have ht₁S : (⟨t, htC⟩ : centralizer (L : Set G)) ∈ S :=
    StandardRecognition.mem_sylow_of_mem_center_of_orderOf_eq_two
      (mem_center_iff.mpr fun x => Subtype.ext (mem_centralizer_iff.mp x.2 t htL).symm) ht₁ S
  obtain ⟨-, -, -, -, -, -, hCH, -, -⟩ :=
    StandardRecognition.standard_cyclic_local_centralizer_kernel hL S hS ht₁S ht₁ (hcore t ht)
  have hCH' : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) =
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := hCH
  by_cases hS4 : 4 ≤ Nat.card S
  · exact (ctss_m12_original_large_cyclic_kernel_false hnonab hL hcore S hS ht hZ hQ hS4).elim
  · rw [hCH']
    have htT : t ∈ (S : Subgroup (centralizer (L : Set G))).map
        (centralizer (L : Set G)).subtype := ⟨_, ht₁S, rfl⟩
    have hcard : Nat.card ((S : Subgroup (centralizer (L : Set G))).map
        (centralizer (L : Set G)).subtype) = Nat.card S :=
      card_map_of_injective (subtype_injective _)
    have h2 : 2 ∣ Nat.card ((S : Subgroup (centralizer (L : Set G))).map
        (centralizer (L : Set G)).subtype) := by
      have h := orderOf_dvd_natCard _ htT
      rwa [ht] at h
    have hpos : 0 < Nat.card S := Nat.card_pos
    refine (eq_of_le_of_card_ge (zpowers_le.mpr htT) ?_).symm
    rw [Nat.card_zpowers, ht]
    omega

end CFSG.ComponentClassification.M12Cover
