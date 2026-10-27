module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentULabels

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem w_mem_partCLeft : x * m * x⁻¹ ∈ partCLeft T L :=
  d.caseC3BCD.swap_right m d.caseC3BCD.m_mem

theorem w_mem : x * m * x⁻¹ ∈ quasiNormalizer u :=
  mem_quasiNormalizer_of_mem_partCSylow (partCLeft_le d.w_mem_partCLeft)

theorem w_mul_self : x * m * x⁻¹ * (x * m * x⁻¹) = centralElt J := by
  rw [show x * m * x⁻¹ * (x * m * x⁻¹) = x * (m * m) * x⁻¹ by group, d.m_mul_self,
    d.caseC3BCD.partC.conj_centralElt]

theorem w_ne : x * m * x⁻¹ ≠ x * u * x⁻¹ ∧ x * m * x⁻¹ ≠ x * u * x⁻¹ * centralElt J := by
  obtain ⟨-, -, hmu, hmue⟩ := d.m_ne
  refine ⟨fun h => hmu (by simpa using h), fun h => hmue ?_⟩
  have h1 : x * m * x⁻¹ = x * (u * centralElt J) * x⁻¹ := by
    rw [h, show x * (u * centralElt J) * x⁻¹ = x * u * (centralElt J * x⁻¹) by group,
      ← (d.setting.commute_centralElt x⁻¹).eq]
    group
  simpa using h1

theorem mem_left_cases {q : J} (hq : q ∈ partCLeft T L) :
    q = 1 ∨ q = centralElt J ∨ q = x * u * x⁻¹ ∨ q = x * u * x⁻¹ * centralElt J ∨
      q = x * m * x⁻¹ ∨ q = x * m * x⁻¹ * centralElt J ∨ q = x * u * x⁻¹ * (x * m * x⁻¹) ∨
      q = x * u * x⁻¹ * (x * m * x⁻¹) * centralElt J := by
  have hc := d.caseC3BCD.partC
  obtain ⟨φ⟩ := hc.quaternion
  exact quaternion_enum φ hc.mem_left hc.order d.v_mem_partCLeft d.w_mem_partCLeft hq d.v_mul_self
    d.w_mul_self d.w_ne.1 d.w_ne.2

@[expose] noncomputable def lv : QuasiQuotient u := quasiMk u ⟨x * u * x⁻¹, d.v_mem⟩

@[expose] noncomputable def lw : QuasiQuotient u := quasiMk u ⟨x * m * x⁻¹, d.w_mem⟩

theorem lv_lw_facts : d.lv ∈ L ∧ d.lw ∈ L ∧
    d.lv ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) ∧
    d.lw ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) ∧
    d.lv * d.lv = quasiCentral u ∧ d.lw * d.lw = quasiCentral u ∧
    d.lv * d.lw = d.lw * d.lv * quasiCentral u := by
  have hc := d.caseC3BCD.partC
  obtain ⟨φ⟩ := hc.quaternion
  have he := d.quasiMk_centralElt
  refine ⟨quasiMk_mem_of_mem_partCLeft d.v_mem_partCLeft _,
    quasiMk_mem_of_mem_partCLeft d.w_mem_partCLeft _,
    Subgroup.mem_map_of_mem _ (mem_sylow_of_mem_partCSylow (partCLeft_le d.v_mem_partCLeft)),
    Subgroup.mem_map_of_mem _ (mem_sylow_of_mem_partCSylow (partCLeft_le d.w_mem_partCLeft)),
    ?_, ?_, ?_⟩
  · rw [lv, ← map_mul, ← he]
    exact congrArg (quasiMk u) (Subtype.ext d.v_mul_self)
  · rw [lw, ← map_mul, ← he]
    exact congrArg (quasiMk u) (Subtype.ext d.w_mul_self)
  · have h := quaternion_anticomm φ hc.mem_left hc.order d.v_mem_partCLeft d.w_mem_partCLeft
      d.v_mul_self d.w_mul_self d.w_ne.1 d.w_ne.2
    rw [lv, lw, ← map_mul, ← he, ← map_mul, ← map_mul]
    exact congrArg (quasiMk u) (Subtype.ext h)

@[expose] noncomputable def fourV : List (Perm (Fin 5)) :=
  [1, d.rho5 d.lv, d.rho5 d.lw, d.rho5 d.lv * d.rho5 d.lw]

theorem fourGroup_facts :
    (Perm.sign (d.rho5 d.lv) = 1 ∧ d.rho5 d.lv * d.rho5 d.lv = 1 ∧ d.rho5 d.lv ≠ 1) ∧
    (Perm.sign (d.rho5 d.lw) = 1 ∧ d.rho5 d.lw * d.rho5 d.lw = 1 ∧ d.rho5 d.lw ≠ 1 ∧
      d.rho5 d.lv ≠ d.rho5 d.lw ∧ d.rho5 d.lv * d.rho5 d.lw = d.rho5 d.lw * d.rho5 d.lv) := by
  obtain ⟨hvL, hwL, hvT, hwT, hvv, hww, hvw⟩ := d.lv_lw_facts
  obtain ⟨a1, a2, a3⟩ := d.rho5_of_mem_of_mul_self hvL hvv
  obtain ⟨b1, b2, b3⟩ := d.rho5_of_mem_of_mul_self hwL hww
  refine ⟨⟨a3, a1, a2⟩, b3, b1, b2, fun h => ?_, ?_⟩
  ·
    have hK := d.mem_centralizer_of_rho5_eq_one (g := d.lv⁻¹ * d.lw)
      (by rw [map_mul, map_inv, h, inv_mul_cancel])
    have hT := Subgroup.mul_mem _ (Subgroup.inv_mem _ hvT) hwT
    set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
    have hv₀ := mem_sylow_of_mem_partCSylow (T := T) (partCLeft_le d.v_mem_partCLeft)
    have hw₀ := mem_sylow_of_mem_partCSylow (T := T) (partCLeft_le d.w_mem_partCLeft)
    rcases d.eq_of_mem_of_mem_centralizer (L.mul_mem (L.inv_mem hvL) hwL) hK with h1 | h1
    · have h2 := quasiMk_injOn_twoGroup u T.isPGroup' hw₀ hv₀
        (show d.lw = d.lv from (inv_mul_eq_one.mp h1).symm)
      exact d.w_ne.1 (congrArg Subtype.val h2)
    · have h2 := quasiMk_injOn_twoGroup u T.isPGroup' hw₀
        (Subgroup.mul_mem _ hv₀ d.centralElt_mem_sylow)
        (show d.lw = d.lv * quasiMk u e₀ by rw [d.quasiMk_centralElt, ← h1, mul_inv_cancel_left])
      exact d.w_ne.2 (congrArg Subtype.val h2)
  · rw [← map_mul, ← map_mul, hvw, map_mul,
      d.rho5_of_mem_centralizer d.quasiCentral_mem_centralizer, mul_one]

theorem mem_sylow_of_rho5_eq {l l' : QuasiQuotient u}
    (hl'T : l' ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u)) (h : d.rho5 l = d.rho5 l') :
    l ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := by
  have hK := d.mem_centralizer_of_rho5_eq_one (g := l'⁻¹ * l)
    (by rw [map_mul, map_inv, h, inv_mul_cancel])
  rw [show l = l' * (l'⁻¹ * l) by group]
  exact Subgroup.mul_mem _ hl'T (d.centralizer_le_sylow hK)

theorem mem_sylow_inf_iff {t : QuasiQuotient u} :
    (t ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) ∧
      t ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u))) ↔
    (t ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) ∧ d.rho5 t ∈ d.fourV) := by
  have hKn := d.oneComponent.centralizer_normal
  obtain ⟨-, -, hvT, hwT, -, -, -⟩ := d.lv_lw_facts
  have he5 := d.rho5_of_mem_centralizer d.quasiCentral_mem_centralizer
  constructor
  · rintro ⟨htT, htLK⟩
    refine ⟨htLK, ?_⟩
    have hT' := Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective
      (pPrimeCore 2 (quasiNormalizer u))) T
    obtain ⟨l, ⟨hlT, hlL⟩, k, ⟨-, hkK⟩, rfl⟩ :=
      d.oneComponent.exists_mul_eq_of_mem_sup d.star.1 _ (hT'.symm ▸ htT) htLK
    rw [hT'] at hlT
    rw [map_mul, d.rho5_of_mem_centralizer hkK, mul_one]
    obtain ⟨q, hqT, rfl⟩ := Subgroup.mem_map.mp hlT
    have hqQ : (q : J) ∈ partCLeft T L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr ⟨hqT, Subgroup.mem_comap.mpr hlL⟩)
    set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
    set v₀ : quasiNormalizer u := ⟨x * u * x⁻¹, d.v_mem⟩
    set w₀ : quasiNormalizer u := ⟨x * m * x⁻¹, d.w_mem⟩
    have he := d.quasiMk_centralElt
    simp only [fourV, List.mem_cons, List.not_mem_nil, or_false]
    rcases d.mem_left_cases hqQ with h | h | h | h | h | h | h | h
    · left; rw [show q = 1 from Subtype.ext h, map_one, map_one]
    · left; rw [show q = e₀ from Subtype.ext h, he, he5]
    · right; left; rw [show q = v₀ from Subtype.ext h]; rfl
    · right; left; rw [show q = v₀ * e₀ from Subtype.ext h, map_mul, map_mul, he, he5, mul_one]
      rfl
    · right; right; left; rw [show q = w₀ from Subtype.ext h]; rfl
    · right; right; left; rw [show q = w₀ * e₀ from Subtype.ext h, map_mul, map_mul, he, he5,
        mul_one]
      rfl
    · right; right; right; rw [show q = v₀ * w₀ from Subtype.ext h, map_mul, map_mul]; rfl
    · right; right; right
      rw [show q = v₀ * w₀ * e₀ from Subtype.ext h, map_mul, map_mul, map_mul, map_mul, he, he5,
        mul_one]
      rfl
  · rintro ⟨htLK, htV⟩
    refine ⟨?_, htLK⟩
    obtain ⟨l, hl, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp htLK
    refine Subgroup.mul_mem _ ?_ (d.centralizer_le_sylow hk)
    rw [map_mul, d.rho5_of_mem_centralizer hk, mul_one] at htV
    simp only [fourV, List.mem_cons, List.not_mem_nil, or_false] at htV
    rcases htV with h | h | h | h
    · exact d.mem_sylow_of_rho5_eq (Subgroup.one_mem _) (by rw [h, map_one])
    · exact d.mem_sylow_of_rho5_eq hvT h
    · exact d.mem_sylow_of_rho5_eq hwT h
    · exact d.mem_sylow_of_rho5_eq (Subgroup.mul_mem _ hvT hwT) (by rw [h, map_mul])

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
