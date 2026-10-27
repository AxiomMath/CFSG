module

public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarFusion
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarSylow

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup
open CFSG.ClassicalInvolution (orderOf_conj_eq)

variable {G : Type*} [Group G]

theorem map_oddCore_le_of_mulEquiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] (e : G₁ ≃* G₂) :
    (CFSG.oddCore G₁).map e.toMonoidHom ≤ CFSG.oddCore G₂ := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← map_le_iff_le_comap]
  exact le_sSup ⟨hN.1.map _ e.surjective, by rw [card_map_of_injective e.injective]; exact hN.2⟩

theorem glauberman_zStar_central_sylow_involution_univ [Finite G] (S : Sylow 2 G)
    (z : (S : Subgroup G)) (hzZ : z ∈ center (S : Subgroup G)) (hz : orderOf z = 2)
    (hwc : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) → g⁻¹ * (z : G) * g = z) :
    (∀ g : G, ∃ c ∈ centralizer ({(z : G)} : Set G), ∃ k ∈ CFSG.oddCore G, g = c * k) ∧
      (QuotientGroup.mk (z : G) : G ⧸ CFSG.oddCore G) ∈ center (G ⧸ CFSG.oddCore G) := by
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have hrange : (S : Subgroup G) ≤ e.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  let S' : Sylow 2 (Shrink.{0} G) := S.comapOfInjective e.toMonoidHom e.injective hrange
  have hmemS' : ∀ x : Shrink.{0} G, x ∈ (S' : Subgroup (Shrink.{0} G)) ↔ e x ∈ (S : Subgroup G) :=
    fun _ => Iff.rfl
  let z' : (S' : Subgroup (Shrink.{0} G)) := ⟨e.symm z, (hmemS' _).mpr (by simp)⟩
  have hz'e : e (z' : Shrink.{0} G) = z := e.apply_symm_apply _
  have hzZ' : z' ∈ center (S' : Subgroup (Shrink.{0} G)) := by
    rw [mem_center_iff]
    intro w
    apply Subtype.ext
    apply e.injective
    have := congrArg Subtype.val (mem_center_iff.mp hzZ ⟨e w, (hmemS' w).mp w.2⟩)
    simpa only [Subgroup.coe_mul, map_mul, hz'e] using this
  have hz' : orderOf z' = 2 := by
    rw [← orderOf_coe, ← MulEquiv.orderOf_eq e, hz'e, orderOf_coe, hz]
  have hwc' : ∀ g : Shrink.{0} G, g⁻¹ * (z' : Shrink.{0} G) * g ∈ (S' : Subgroup (Shrink.{0} G)) →
      g⁻¹ * (z' : Shrink.{0} G) * g = z' := by
    intro g hg
    rw [hmemS', map_mul, map_mul, map_inv, hz'e] at hg
    apply e.injective
    rw [map_mul, map_mul, map_inv, hz'e]
    exact hwc (e g) hg
  obtain ⟨hfac, hcen⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution S' z' hzZ' hz' hwc'
  have hcore := map_oddCore_le_of_mulEquiv e
  refine ⟨fun g => ?_, ?_⟩
  · obtain ⟨c, hc, k, hk, hgck⟩ := hfac (e.symm g)
    refine ⟨e c, ?_, e k, hcore (mem_map_of_mem _ hk), ?_⟩
    · rw [mem_centralizer_singleton_iff] at hc ⊢
      have := congrArg e hc
      rwa [map_mul, map_mul, hz'e] at this
    · rw [← map_mul, ← hgck, MulEquiv.apply_symm_apply]
  · rw [mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have h := mem_center_iff.mp hcen (QuotientGroup.mk (e.symm g))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h ⊢
    have := hcore (mem_map_of_mem e.toMonoidHom h)
    rwa [MulEquiv.coe_toMonoidHom, map_mul, map_inv, map_mul, map_mul, hz'e,
      MulEquiv.apply_symm_apply] at this

theorem closure_pair_sup_eq_centralizer [Finite G] {t p : G} {K A : Subgroup G}
    (htt : t * t = 1) (hpp : p * p = 1) (hKH : K ≤ centralizer ({t} : Set G))
    (hindex : K.relIndex (centralizer ({t} : Set G)) ≤ 2) (hpH : p ∈ centralizer ({t} : Set G))
    (hpK : p ∉ K) (hA : zpowers t ⊔ A = K ⊓ centralizer ({p} : Set G)) :
    Subgroup.closure ({t, p} : Set G) ⊔ A =
      centralizer ((Subgroup.closure ({t, p} : Set G) : Subgroup G) : Set G) := by
  have htp : t * p = p * t := (mem_centralizer_singleton_iff.mp hpH).symm
  have htV : t ∈ Subgroup.closure ({t, p} : Set G) := subset_closure (by simp)
  have hpV : p ∈ Subgroup.closure ({t, p} : Set G) := subset_closure (by simp)
  have hmemC : ∀ {x : G}, x ∈ centralizer ((Subgroup.closure ({t, p} : Set G) :
      Subgroup G) : Set G) ↔ t * x = x * t ∧ p * x = x * p := by
    intro x
    simp only [centralizer_closure, mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hidx : (K.subgroupOf (centralizer ({t} : Set G))).index = 2 := by
    have hne1 : (K.subgroupOf (centralizer ({t} : Set G))).index ≠ 1 := by
      rw [Ne, index_eq_one]
      intro htop
      have : (⟨p, hpH⟩ : centralizer ({t} : Set G)) ∈ K.subgroupOf (centralizer ({t} : Set G)) :=
        htop ▸ mem_top _
      exact hpK (mem_subgroupOf.mp this)
    have hne0 : (K.subgroupOf (centralizer ({t} : Set G))).index ≠ 0 := index_ne_zero_of_finite
    have hle : (K.subgroupOf (centralizer ({t} : Set G))).index ≤ 2 := hindex
    omega
  apply le_antisymm
  · refine sup_le (fun x hx => hmemC.mpr ?_) (fun a ha => hmemC.mpr ?_)
    · exact ⟨(commute_and_mul_self_of_mem_closure_pair htt hpp htp htV hx).1,
        (commute_and_mul_self_of_mem_closure_pair htt hpp htp hpV hx).1⟩
    · have haKC : a ∈ K ⊓ centralizer ({p} : Set G) := hA ▸ mem_sup_right ha
      exact ⟨(mem_centralizer_singleton_iff.mp (hKH haKC.1)).symm,
        (mem_centralizer_singleton_iff.mp haKC.2).symm⟩
  · intro x hx
    obtain ⟨hxt, hxp⟩ := hmemC.mp hx
    have hxH : x ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hxt.symm
    have hxp' : x ∈ centralizer ({p} : Set G) := mem_centralizer_singleton_iff.mpr hxp.symm
    have hle : K ⊓ centralizer ({p} : Set G) ≤ Subgroup.closure ({t, p} : Set G) ⊔ A :=
      hA ▸ sup_le_sup_right (zpowers_le.mpr htV) A
    by_cases hxK : x ∈ K
    · exact hle ⟨hxK, hxp'⟩
    · have hxpK : x * p⁻¹ ∈ K := by
        have := (mul_mem_iff_of_index_two hidx (a := ⟨x, hxH⟩)
          (b := (⟨p, hpH⟩ : centralizer ({t} : Set G))⁻¹)).mpr
          (iff_of_false (by rwa [mem_subgroupOf]) (by rwa [inv_mem_iff, mem_subgroupOf]))
        rwa [mem_subgroupOf] at this
      have hxpC : x * p⁻¹ ∈ centralizer ({p} : Set G) :=
        mul_mem hxp' (inv_mem (mem_centralizer_singleton_iff.mpr rfl))
      have := mul_mem (hle ⟨hxpK, hxpC⟩) (mem_sup_left hpV)
      rwa [inv_mul_cancel_right] at this

theorem rigid_index_two_centralizer_perfect_data_give_zStar [Finite G] {t : G}
    (ht : orderOf t = 2) {K : Subgroup G} (hKH : K ≤ centralizer ({t} : Set G)) (htK : t ∈ K)
    (hindex : K.relIndex (centralizer ({t} : Set G)) ≤ 2)
    (T : Sylow 2 (centralizer ({t} : Set G)))
    (hfix : ∀ φ : MulAut (T : Subgroup (centralizer ({t} : Set G))),
      ∀ x : (T : Subgroup (centralizer ({t} : Set G))),
        ((x : centralizer ({t} : Set G)) : G) = t → φ x = x)
    (hcent : ∀ u ∈ K, orderOf u = 2 → ∃ k ∈ K,
      ∃ z ∈ center (T : Subgroup (centralizer ({t} : Set G))),
        ((z : centralizer ({t} : Set G)) : G) = k⁻¹ * u * k)
    (hext : ∀ x y : G, x ∈ centralizer ({t} : Set G) → x ∉ K → orderOf x = 2 →
      y ∈ centralizer ({t} : Set G) → y ∉ K → orderOf y = 2 →
      ∃ h ∈ centralizer ({t} : Set G), h⁻¹ * x * h = y)
    (hA : ∀ p ∈ centralizer ({t} : Set G), p ∉ K → orderOf p = 2 → ∃ A : Subgroup G,
      zpowers t ⊔ A = K ⊓ centralizer ({p} : Set G) ∧ _root_.commutator A = ⊤ ∧
        Even (Nat.card A)) :
    (∃ S : Sylow 2 G,
        (T : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype = S) ∧
      (∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g = t) ∧
      (∀ g : G, ∃ c ∈ centralizer ({t} : Set G), ∃ k ∈ CFSG.oddCore G, g = c * k) ∧
      (QuotientGroup.mk t : G ⧸ CFSG.oddCore G) ∈ center (G ⧸ CFSG.oddCore G) := by
  obtain ⟨⟨S, hS⟩, hfusK⟩ :=
    rigid_sylow_central_involution_excludes_internal_fusion ht hKH T hfix hcent
  have htt : t * t = 1 := (sq t).symm.trans (orderOf_eq_prime_iff.mp ht).1
  have hfusH : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g = t := by
    intro g hgH
    by_cases hgK : g⁻¹ * t * g ∈ K
    · exact hfusK g hgK
    exfalso
    have hu2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, ht]
    obtain ⟨A, hAsup, hAperf, hAeven⟩ := hA _ hgH hgK hu2
    have hAK : A ≤ K := le_sup_right.trans (hAsup.le.trans inf_le_left)
    exact four_group_perfect_factor_forces_internal_fusion ht hKH htK hfusK hext hgH hgK ⟨g, rfl⟩
      hAK hAperf hAeven (closure_pair_sup_eq_centralizer htt
        ((sq _).symm.trans (orderOf_eq_prime_iff.mp hu2).1) hKH hindex hgH hgK hAsup)
  have htH : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have htZ : (⟨t, htH⟩ : centralizer ({t} : Set G)) ∈ center (centralizer ({t} : Set G)) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have htT : (⟨t, htH⟩ : centralizer ({t} : Set G)) ∈
      (T : Subgroup (centralizer ({t} : Set G))) :=
    mem_sylow_of_mem_center_of_orderOf_eq_two htZ (by rw [orderOf_mk, ht]) T
  have htS : t ∈ (S : Subgroup G) := by
    rw [← hS]
    exact mem_map_of_mem _ htT
  have hSH : (S : Subgroup G) ≤ centralizer ({t} : Set G) := hS ▸ map_subtype_le _
  have hzZ : (⟨t, htS⟩ : (S : Subgroup G)) ∈ center (S : Subgroup G) :=
    mem_center_iff.mpr fun w => Subtype.ext (mem_centralizer_singleton_iff.mp (hSH w.2))
  have hz : orderOf (⟨t, htS⟩ : (S : Subgroup G)) = 2 := by rw [orderOf_mk, ht]
  obtain ⟨hfac, hcen⟩ := glauberman_zStar_central_sylow_involution_univ S ⟨t, htS⟩ hzZ hz
    fun g hg => hfusH g (hSH hg)
  exact ⟨⟨S, hS⟩, hfusH, hfac, hcen⟩

theorem rigid_index_two_centralizer_data_give_zStar [Finite G] {t : G} (ht : orderOf t = 2)
    {K : Subgroup G} (hKH : K ≤ centralizer ({t} : Set G))
    (_hKn : (K.subgroupOf (centralizer ({t} : Set G))).Normal) (htK : t ∈ K)
    (hindex : K.relIndex (centralizer ({t} : Set G)) ≤ 2)
    (T : Sylow 2 (centralizer ({t} : Set G)))
    (hfix : ∀ φ : MulAut (T : Subgroup (centralizer ({t} : Set G))),
      ∀ x : (T : Subgroup (centralizer ({t} : Set G))),
        ((x : centralizer ({t} : Set G)) : G) = t → φ x = x)
    (hcent : ∀ u ∈ K, orderOf u = 2 → ∃ k ∈ K,
      ∃ z ∈ center (T : Subgroup (centralizer ({t} : Set G))),
        ((z : centralizer ({t} : Set G)) : G) = k⁻¹ * u * k)
    (hext : ∀ x y : G, x ∈ centralizer ({t} : Set G) → x ∉ K → orderOf x = 2 →
      y ∈ centralizer ({t} : Set G) → y ∉ K → orderOf y = 2 →
      ∃ h ∈ centralizer ({t} : Set G), h⁻¹ * x * h = y)
    (hA : ∀ p ∈ centralizer ({t} : Set G), p ∉ K → orderOf p = 2 → ∃ A : Subgroup G, A ≤ K ∧
      zpowers t ⊔ A = K ⊓ centralizer ({p} : Set G) ∧ zpowers t ⊓ A = ⊥ ∧
      (∀ a ∈ A, ∀ v ∈ zpowers t, a * v = v * a) ∧ _root_.commutator A = ⊤ ∧
      Even (Nat.card A) ∧ ¬ 3 ∣ Nat.card (OuterAutomorphisms.Outer A)) :
    (∃ S : Sylow 2 G,
        (T : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype = S) ∧
      (∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g = t) ∧
      (∀ g : G, ∃ c ∈ centralizer ({t} : Set G), ∃ k ∈ CFSG.oddCore G, g = c * k) ∧
      (QuotientGroup.mk t : G ⧸ CFSG.oddCore G) ∈ center (G ⧸ CFSG.oddCore G) :=
  rigid_index_two_centralizer_perfect_data_give_zStar ht hKH htK hindex T hfix hcent hext
    fun p hpH hpK hp2 => by
      obtain ⟨A, -, hsup, -, -, hperf, heven, -⟩ := hA p hpH hpK hp2
      exact ⟨A, hsup, hperf, heven⟩

end CFSG.ComponentClassification.StandardRecognition
