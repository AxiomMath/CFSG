module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelFusion
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelAction
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelExternal

public section

namespace CFSG.ComponentClassification.J2Cover

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise
open CyclicKernel
open CFSG.ComponentClassification.M12Cover.CyclicKernel (exists_normalizer_action
  exists_orderOf_eq_four_of_isCyclic eq_of_orderOf_eq_two_of_isCyclic orderOf_sq_of_orderOf_eq_four
  mul_comm_of_isCyclic conj_eq_of_mem_normalizer_of_center_eq_zpowers mem_centralizer_of_conj_mem
  eq_of_isConj_of_commute exists_mul_of_mem_sup_of_commute
  exists_conj_mem_centralizer_ne_of_isSimpleGroup orderOf_conj_eq eq_one_or_eq_of_isConj_of_commute
  conj_eq_inv_of_isConj mem_or_mul_mem_of_mem_sup_zpowers)

theorem ctss_j2_original_large_cyclic_kernel_fusion_reduction {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ x : G, orderOf x = 2 → CFSG.Assembly.oddCore (centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) {t : G} (ht : orderOf t = 2)
    (hZ : (center L).map L.subtype = zpowers t)
    (hQ : NativeSporadic.IsSporadic (L ⧸ center L) .J2) {H : Subgroup G}
    (hH : H = centralizer {t}) {T : Subgroup G}
    (hT : T = (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hS4 : 4 ≤ Nat.card S) :
    centralizer (L : Set G) = T ∧ centralizer (L : Set G) ⊓ H = T ∧ (L.subgroupOf H).Normal ∧
    L ⊓ T = zpowers t ∧ normalizer (L : Set G) = H ∧ normalizer (T : Set G) = H ∧
    (∀ φ : L ⧸ center L ≃* P,
      (∃ θ : H →* MulAut P, ∀ (h : H) (l l' : L),
        (l' : G) = h * l * (h : G)⁻¹ → θ h (φ (l : L ⧸ center L)) = φ (l' : L ⧸ center L)) ∧
      ∀ θ : H →* MulAut P, (∀ (h : H) (l l' : L),
        (l' : G) = h * l * (h : G)⁻¹ → θ h (φ (l : L ⧸ center L)) = φ (l' : L ⧸ center L)) →
        θ.ker = T.subgroupOf H ∧ (inner P).comap θ = (L ⊔ T).subgroupOf H) ∧
    (L ⊔ T).relIndex H ≤ 2 ∧ (∀ h ∈ H, ∀ s ∈ T, h ^ 2 * s = s * h ^ 2) ∧
    (∀ g : G, g ∉ H → Nat.card (MulAut.conj g⁻¹ • T ⊓ H : Subgroup G) ≤ 2 ∧
      ¬ MulAut.conj g⁻¹ • T ≤ H) ∧
    (∀ g : G, g⁻¹ * t * g ∈ L ⊔ T → g⁻¹ * t * g = t) ∧
    (∃ g : G, g ∉ H ∧ g⁻¹ * t * g ∈ H ∧ g⁻¹ * t * g ∉ L ⊔ T) ∧
    ∀ g p : G, p = g⁻¹ * t * g → g ∉ H → p ∈ H → p ∉ L ⊔ T →
      (L ⊔ T).relIndex H = 2 ∧ MulAut.conj g⁻¹ • T ⊓ H = zpowers p ∧
      T ⊓ centralizer {p} = zpowers t ∧ (∀ a ∈ T, orderOf a = 4 → p * a * p⁻¹ = a⁻¹) ∧
      (L ⊔ zpowers p) ⊓ centralizer (L : Set G) = zpowers t ∧
      (∃ A : Subgroup G, A ≤ L ∧ zpowers t ⊔ A = L ⊓ centralizer {p} ∧ zpowers t ⊓ A = ⊥ ∧
        (∀ a ∈ A, a * t = t * a) ∧ _root_.commutator A = ⊤ ∧ Even (Nat.card A) ∧
        ¬ 3 ∣ Nat.card (Outer A)) ∧
      ∃ v ∈ L, v ^ 2 = t ∧ v * p * v⁻¹ = t * p := by
  classical
  subst hH hT
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
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    congrArg Subtype.val (mem_center_iff.mp htZ ⟨l, hl⟩)
  have hLH : L ≤ centralizer {t} := fun l hl => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_center_iff.mp htZ ⟨l, hl⟩))
  have hCLH : centralizer (L : Set G) ≤ centralizer {t} := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx t htL).symm
  have hHN : centralizer {t} ≤ normalizer (L : Set G) :=
    (LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL htC ht).1
  have ht₁ : orderOf (⟨t, htC⟩ : centralizer (L : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk, ht]
  have ht₁S : (⟨t, htC⟩ : centralizer (L : Set G)) ∈ S :=
    StandardRecognition.mem_sylow_of_mem_center_of_orderOf_eq_two
      (mem_center_iff.mpr fun x => Subtype.ext (mem_centralizer_iff.mp x.2 t htL).symm) ht₁ S
  obtain ⟨-, -, -, hLn, -, -, hCH, -, hLT⟩ :=
    StandardRecognition.standard_cyclic_local_centralizer_kernel hL S hS ht₁S ht₁ (hcore t ht)
  set T := (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    with hTdef
  have hCL : centralizer (L : Set G) = T := by rw [← hCH, inf_of_le_left hCLH]
  have hLTt : L ⊓ T = zpowers t := hLT.trans hZ
  have htT : t ∈ T := ⟨_, ht₁S, rfl⟩
  have hTc : IsCyclic T := isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have hT2 : IsPGroup 2 T := S.isPGroup'.map _
  have hT4 : 4 ≤ Nat.card T := by
    rw [hTdef, card_map_of_injective (subtype_injective _)]
    exact hS4
  obtain ⟨φ₀⟩ := hQ
  let φ : L ⧸ center L ≃* P := (φ₀ : L ⧸ center L ≃* NativeSporadic.J2).trans nativeEquivP
  let π : L →* P := φ.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = zpowers t' := hkerZ.trans hZ'
  obtain ⟨θ, hθ, hθ1⟩ := exists_normalizer_action hHN π hπ hkerZ
  obtain ⟨hTn, hsq⟩ := sq_mul_comm_of_kernel index_inner_P hLq π hπ hkerZ hLH hHN hCH hTc
  have hobs : ∀ g : G, (∀ s ∈ T, g⁻¹ * s * g ∈ centralizer {t}) → g ∈ centralizer {t} :=
    fun g hg => j2_cyclic_kernel_obstruction hLq π hπ hkerZ hLH hHN hCH hTc hT2 hT4 htT ht g hg
  obtain ⟨a, haT, ha4⟩ := exists_orderOf_eq_four_of_isCyclic hTc hT2 (by omega)
  have ha2 : a ^ 2 = t :=
    eq_of_orderOf_eq_two_of_isCyclic hTc (pow_mem haT 2) htT (orderOf_sq_of_orderOf_eq_four ha4)
      ht
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy => mul_comm_of_isCyclic hTc hx hy
  have hLTc : ∀ l ∈ L, ∀ s ∈ T, l * s = s * l := fun l hl s hs =>
    mem_centralizer_iff.mp (show s ∈ centralizer (L : Set G) by rw [hCL]; exact hs) l hl
  have hNL : normalizer (L : Set G) = centralizer {t} := by
    refine le_antisymm (fun x hx => ?_) hHN
    rw [mem_centralizer_singleton_iff]
    have h : x * t * x⁻¹ = t := conj_eq_of_mem_normalizer_of_center_eq_zpowers hZ' ht' hx
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h]
  have hNC : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G) := hL.2.2.2.1
  have hNT : normalizer (T : Set G) = centralizer {t} := by rw [← hCL, hNC, hNL]
  have hθall : ∀ φ' : L ⧸ center L ≃* P,
      (∃ θ' : centralizer {t} →* MulAut P, ∀ (h : centralizer {t}) (l l' : L),
        (l' : G) = h * l * (h : G)⁻¹ → θ' h (φ' (l : L ⧸ center L)) = φ' (l' : L ⧸ center L)) ∧
      ∀ θ' : centralizer {t} →* MulAut P, (∀ (h : centralizer {t}) (l l' : L),
        (l' : G) = h * l * (h : G)⁻¹ → θ' h (φ' (l : L ⧸ center L)) = φ' (l' : L ⧸ center L)) →
        θ'.ker = T.subgroupOf (centralizer {t}) ∧
          (inner P).comap θ' = (L ⊔ T).subgroupOf (centralizer {t}) := by
    intro φ'
    let π' : L →* P := φ'.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hπ' : Function.Surjective π' := φ'.surjective.comp (QuotientGroup.mk'_surjective _)
    have hkerZ' : π'.ker = center L := by
      ext l
      simp only [π', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨θ', hθ', hθ1'⟩ := exists_normalizer_action hHN π' hπ' hkerZ'
    refine ⟨⟨θ', fun h l l' hl' => hθ' h l l' hl'⟩, fun θ'' hθ'' => ?_⟩
    have heq : θ'' = θ' := by
      refine MonoidHom.ext fun h => MulEquiv.ext fun q => ?_
      obtain ⟨l, rfl⟩ := hπ' q
      have hl' : (h : G) * l * (h : G)⁻¹ ∈ L := (mem_normalizer_iff.mp (hHN h.2) l).mp l.2
      exact (hθ'' h l ⟨_, hl'⟩ rfl).trans (hθ' h l ⟨_, hl'⟩ rfl).symm
    subst heq
    refine ⟨?_, ?_⟩
    · ext h
      rw [MonoidHom.mem_ker, hθ1', mem_subgroupOf, hCL]
    · ext h
      rw [mem_comap, action_mem_inner_iff hLH hπ' hθ' hθ1', mem_subgroupOf, hCH]
  have hcomap : (inner P).comap θ = (L ⊔ T).subgroupOf (centralizer {t}) := by
    ext h
    rw [mem_comap, action_mem_inner_iff hLH hπ hθ hθ1, mem_subgroupOf, hCH]
  have hidx : (L ⊔ T).relIndex (centralizer {t}) ≤ 2 := by
    have h1 : (L ⊔ T).relIndex (centralizer {t}) ∣ 2 := by
      rw [relIndex, ← hcomap, index_comap, ← index_inner_P]
      exact relIndex_dvd_index_of_le (inner_le_range_action hLH hπ hθ)
    exact Nat.le_of_dvd (by norm_num) h1
  have hconjmem : ∀ g x : G, x ∈ MulAut.conj g⁻¹ • T ↔ g * x * g⁻¹ ∈ T := by
    intro g x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
      MulAut.conj_apply]
  have hnotle : ∀ g : G, g ∉ centralizer {t} → ¬ MulAut.conj g⁻¹ • T ≤ centralizer {t} := by
    intro g hg hle
    refine hg (hobs g fun s hs => hle ?_)
    rw [hconjmem, show g * (g⁻¹ * s * g) * g⁻¹ = s by group]
    exact hs
  have hcard : ∀ g : G, g ∉ centralizer {t} →
      Nat.card (MulAut.conj g⁻¹ • T ⊓ centralizer {t} : Subgroup G) ≤ 2 := by
    intro g hg
    by_contra hlt
    push Not at hlt
    have hKT : MulAut.conj g⁻¹ • T ⊓ centralizer {t} ≤ MulAut.conj g⁻¹ • T := inf_le_left
    have hTgc : IsCyclic (MulAut.conj g⁻¹ • T : Subgroup G) :=
      (MulEquiv.isCyclic (equivSMul (MulAut.conj g⁻¹) T)).mp hTc
    have hKc : IsCyclic (MulAut.conj g⁻¹ • T ⊓ centralizer {t} : Subgroup G) := isCyclic_of_le hKT
    have hK2 : IsPGroup 2 (MulAut.conj g⁻¹ • T ⊓ centralizer {t} : Subgroup G) :=
      (hT2.of_equiv (equivSMul (MulAut.conj g⁻¹) T)).to_le hKT
    obtain ⟨w, hwK, hw4⟩ := exists_orderOf_eq_four_of_isCyclic hKc hK2 hlt
    obtain ⟨hwTg, hwH⟩ := mem_inf.mp hwK
    have hwT : g * w * g⁻¹ ∈ T := (hconjmem g w).mp hwTg
    have ha'2 : (g * w * g⁻¹) ^ 2 = t := by
      refine eq_of_orderOf_eq_two_of_isCyclic hTc (pow_mem hwT 2) htT ?_ ht
      rw [conj_pow, orderOf_conj_eq]
      exact orderOf_sq_of_orderOf_eq_four hw4
    have hg' := mem_centralizer_of_conj_mem hsq hobs ha'2 (g := g⁻¹) (by
      rw [inv_inv, show g⁻¹ * (g * w * g⁻¹) * g = w by group]
      exact hwH)
    exact hg (by simpa using inv_mem hg')
  have hLSfix : ∀ g : G, g⁻¹ * t * g ∈ L ⊔ T → g⁻¹ * t * g = t := by
    intro g hg
    refine eq_of_isConj_of_commute hsq hobs ha2 (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩) ?_
    obtain ⟨l, hl, s, hs, hls⟩ := exists_mul_of_mem_sup_of_commute hLTc hg
    rw [hls]
    calc l * s * a = l * (a * s) := by rw [mul_assoc, hTab s hs a haT]
      _ = a * (l * s) := by rw [← mul_assoc, hLTc l hl a haT, mul_assoc]
  have hex : ∃ g : G, g ∉ centralizer {t} ∧ g⁻¹ * t * g ∈ centralizer {t} ∧
      g⁻¹ * t * g ∉ L ⊔ T := by
    obtain ⟨g, hgH, hgt⟩ := exists_conj_mem_centralizer_ne_of_isSimpleGroup hnonab ht
    refine ⟨g, fun hg => hgt ?_, hgH, fun h => hgt (hLSfix g h)⟩
    rw [mem_centralizer_singleton_iff] at hg
    rw [mul_assoc, ← hg, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨hCL, hCH, hLn, hLTt, hNL, hNT, hθall, hidx, hsq, fun g hg => ⟨hcard g hg, hnotle g hg⟩,
    hLSfix, hex, fun g p hp hg hpH hpLS => ?_⟩
  have hconj : IsConj t p := isConj_iff.mpr ⟨g⁻¹, by rw [hp, inv_inv]⟩
  have hpt : p ≠ t := fun h => hpLS (h ▸ mem_sup_left htL)
  have hp2 : orderOf p = 2 := by rw [hp, ← inv_inv g, inv_inv g⁻¹, orderOf_conj_eq, ht]
  have hpp : p * p = 1 := by rw [← sq, ← hp2, pow_orderOf_eq_one]
  have htp : t * p = p * t := (mem_centralizer_singleton_iff.mp hpH).symm
  have hpN : p ∈ normalizer (L : Set G) := hHN hpH
  have hpC : ∀ l ∈ L, l * p ∉ centralizer (L : Set G) := fun l hl h => hpLS (by
    have h' : p = l⁻¹ * (l * p) := by group
    rw [h']
    exact mul_mem (mem_sup_left (inv_mem hl)) (mem_sup_right (by rw [← hCL]; exact h)))
  obtain ⟨hAL, hsupA, hinfA, hAperf, hAcard, -, hAout, -, v, hvL, hv2, -, hvp, -⟩ :=
    j2_outer_involution_fixed_factor hLq ht' hZ' π hπ hker hpN hp2 hpC (θ ⟨p, hpH⟩)
      (fun l l' h => hθ ⟨p, hpH⟩ l l' h) rfl
  refine ⟨?_, ?_, ?_, fun a' ha'T ha'4 => ?_, ?_, ⟨_, hAL, hsupA, hinfA, fun x hx => ?_,
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hAperf), by rw [hAcard]; exact ⟨84, rfl⟩,
    fun h3 => absurd (dvd_trans h3 hAout) (by norm_num)⟩, ⟨v, hvL, hv2, hvp⟩⟩
  ·
    have h1 : (L ⊔ T).relIndex (centralizer {t}) ≠ 1 := fun h =>
      hpLS (relIndex_eq_one.mp h hpH)
    have h0 : (L ⊔ T).relIndex (centralizer {t}) ≠ 0 := index_ne_zero_of_finite
    omega
  ·
    have hpTg : p ∈ MulAut.conj g⁻¹ • T := by
      rw [hconjmem, hp, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact htT
    refine (eq_of_le_of_card_ge (zpowers_le.mpr (mem_inf.mpr ⟨hpTg, hpH⟩)) ?_).symm
    rw [Nat.card_zpowers, hp2]
    exact hcard g hg
  ·
    apply le_antisymm
    · intro s hs
      obtain ⟨hsT, hsp⟩ := mem_inf.mp hs
      rcases eq_one_or_eq_of_isConj_of_commute hTc hT2 htT ht hsq hobs haT ha2 hconj hpt hsT
        (mem_centralizer_singleton_iff.mp hsp).symm with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact mem_zpowers t
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨htT, mem_centralizer_singleton_iff.mpr htp⟩
  ·
    have ha'2 : a' ^ 2 = t := eq_of_orderOf_eq_two_of_isCyclic hTc (pow_mem ha'T 2) htT
      (orderOf_sq_of_orderOf_eq_four ha'4) ht
    exact conj_eq_inv_of_isConj hTc ht hsq hobs ha'T ha'2 (hTn p hpH a' ha'T) hconj hpt
  ·
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      have hxT : x ∈ T := by rw [← hCL]; exact hx2
      rcases mem_or_mul_mem_of_mem_sup_zpowers hpN hpp hx1 with h | h
      · rw [← hLTt]
        exact mem_inf.mpr ⟨h, hxT⟩
      · exfalso
        apply hpLS
        have h' : p = x⁻¹ * (x * p) := by group
        rw [h']
        exact mul_mem (mem_sup_right (inv_mem hxT)) (mem_sup_left h)
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨mem_sup_left htL, htC⟩
  · exact congrArg Subtype.val (mem_center_iff.mp htZ ⟨x, hAL hx⟩)

end CFSG.ComponentClassification.J2Cover
