module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadA
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwSmall
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwTrans

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

section Helpers

variable {G : Type} [Group G] [Finite G]

private theorem card_le_of_isSylowTwoIn' {D H Y : Subgroup G} (hD : IsSylowTwoIn D H)
    (hYH : Y ≤ H) (hY : IsPGroup 2 Y) : Nat.card Y ≤ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDH, P, hP⟩ := hD
  have hY' : IsPGroup 2 (Y.subgroupOf H) := hY.of_equiv (subgroupOfEquivOfLe hYH).symm
  obtain ⟨Q, hQ⟩ := hY'.exists_le_sylow
  have h1 : Nat.card Y = Nat.card (Y.subgroupOf H) :=
    (Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv).symm
  have h2 : Nat.card D = Nat.card (P : Subgroup ↥H) := by
    rw [hP]; exact (Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv).symm
  rw [h1, h2, Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity Q]
  exact Subgroup.card_le_of_le hQ

private theorem inf_oddIn_eq_bot_of_syl' {M T : Subgroup G} (hT : IsSylowTwoIn T M) :
    T ⊓ oddIn M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_of_le_two_group_of_le_odd (P := T) (O := oddIn M)
    (GrS4.isPGroup_of_isSylowTwoIn hT) ?_ inf_le_left inf_le_right
  rw [oddIn, card_map_of_injective (subtype_injective _)]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem eq_of_rho_eq' {B : Type*} [Group B] {M T : Subgroup G} (hT : IsSylowTwoIn T M)
    {ρ : ↥M →* B} (hker : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ oddIn M) {m₁ m₂ : ↥M}
    (h₁ : (m₁ : G) ∈ T) (h₂ : (m₂ : G) ∈ T) (h : ρ m₁ = ρ m₂) : m₁ = m₂ := by
  have h1 : ρ (m₁⁻¹ * m₂) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((m₁⁻¹ * m₂ : ↥M) : G) ∈ oddIn M := (hker _).mp h1
  have h3 : ((m₁⁻¹ * m₂ : ↥M) : G) ∈ T := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem h₁) h₂
  have h4 : ((m₁⁻¹ * m₂ : ↥M) : G) ∈ T ⊓ oddIn M := mem_inf.mpr ⟨h3, h2⟩
  rw [inf_oddIn_eq_bot_of_syl' hT, mem_bot] at h4
  exact inv_mul_eq_one.mp (Subtype.ext h4)

private theorem mem_imgT_iff' {M T : Subgroup G} {ρ : ↥M →* WrE} {z : WrE} :
    z ∈ imgT T M ρ ↔ ∃ m : ↥M, (m : G) ∈ T ∧ ρ m = z := by
  unfold imgT
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨m, hm, e⟩ => ⟨m, mem_subgroupOf.mp hm, e⟩,
    fun ⟨m, hm, e⟩ => ⟨m, mem_subgroupOf.mpr hm, e⟩⟩

private theorem comm_conj_of_comm {a d z g : G} (hg : g⁻¹ * a * g = d) (hz : z * d = d * z) :
    g * z * g⁻¹ * a = a * (g * z * g⁻¹) := by
  have ha : a = g * d * g⁻¹ := by rw [← hg]; group
  rw [ha]
  calc g * z * g⁻¹ * (g * d * g⁻¹) = g * (z * d) * g⁻¹ := by group
    _ = g * (d * z) * g⁻¹ := by rw [hz]
    _ = g * d * g⁻¹ * (g * z * g⁻¹) := by group

end Helpers

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}
  {ρ : ↥(normalizer (W : Set G)) →* WrE}

theorem card_lt_of_le_centralizer (hMax : MaximalTwoComponentInput)
    (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPa : P ≤ centralizer ({a} : Set G)) : Nat.card P < Nat.card T := by
  obtain ⟨haM, haA⟩ := isA_a h hρ
  obtain ⟨-, -, -, -, hSsyl, haS, -⟩ := h.hset
  have haT : a ∈ T := h.hST haS
  have hPN : P ≤ normalizer (J : Set G) :=
    hPa.trans (GrS5S.centralizer_le_normalizer_of_sec4 hMax h.hset)
  have h1 : Nat.card P ≤ Nat.card S' := card_le_of_isSylowTwoIn' hSsyl hPN hP
  have hSle : S' ≤ T ⊓ centralizer ({a} : Set G) :=
    le_inf h.hST fun s hs => mem_centralizer_singleton_iff.mpr (h.hcent s hs)
  have h2 : Nat.card S' ≤ Nat.card ↥(T ⊓ centralizer ({a} : Set G)) :=
    Subgroup.card_le_of_le hSle
  have hlt : T ⊓ centralizer ({a} : Set G) < T := by
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    obtain ⟨z, hzX, hz⟩ := hC.a_noncentral (ρ ⟨a, haM⟩)
      (mem_imgT_iff'.mpr ⟨⟨a, haM⟩, haT, rfl⟩) haA
    obtain ⟨y, hyT, rfl⟩ := mem_imgT_iff'.mp hzX
    have hyC : (y : G) ∈ centralizer ({a} : Set G) := by
      have : (y : G) ∈ T ⊓ centralizer ({a} : Set G) := by rw [heq]; exact hyT
      exact (mem_inf.mp this).2
    have hya : y * ⟨a, haM⟩ = ⟨a, haM⟩ * y :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hyC)
    exact hz (by rw [← map_mul, ← map_mul, hya])
  exact lt_of_le_of_lt (h1.trans h2) (Subgroup.card_lt_of_lt hlt)

theorem exists_d0 (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) :
    ∃ d : ↥(normalizer (W : Set G)), (d : G) ∈ T ∧ d * d = 1 ∧ IsD (ρ d) ∧
      ∀ y ∈ T, y * (d : G) = (d : G) * y := by
  obtain ⟨dd, hddX, hdc, hdD⟩ := hC.d_central
  obtain ⟨d, hdT, rfl⟩ := mem_imgT_iff'.mp hddX
  refine ⟨d, hdT, ?_, hdD, fun y hyT => ?_⟩
  ·
    have h1 : ρ (d * d) = ρ 1 := by rw [map_mul, map_one]; exact hdD.2.1
    exact eq_of_rho_eq' h.hTsyl hρ.ker_iff (mul_mem hdT hdT) (one_mem T) h1
  ·
    have hyM : y ∈ normalizer (W : Set G) := h.hTsyl.1 hyT
    have h1 : ρ (⟨y, hyM⟩ * d) = ρ (d * ⟨y, hyM⟩) := by
      rw [map_mul, map_mul]
      exact hdc (ρ ⟨y, hyM⟩) (mem_imgT_iff'.mpr ⟨⟨y, hyM⟩, hyT, rfl⟩)
    exact congrArg Subtype.val
      (eq_of_rho_eq' h.hTsyl hρ.ker_iff (mul_mem hyT hdT) (mul_mem hdT hyT) h1)

theorem a_not_conj_d (hMax : MaximalTwoComponentInput)
    (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) {m : ↥(normalizer (W : Set G))}
    (hm2 : m * m = 1) (hmD : IsD (ρ m)) (g : G) : g⁻¹ * a * g ≠ (m : G) := by
  intro hg
  obtain ⟨d, hdT, hd2, hdD, hdZ⟩ := exists_d0 h hρ hC
  obtain ⟨k, hk⟩ := invol_conj_of_type h hρ hm2 hd2 (Or.inr (Or.inl ⟨hmD, hdD⟩))
  have hk' : (k : G)⁻¹ * (m : G) * (k : G) = (d : G) := congrArg Subtype.val hk
  have hgd : (g * (k : G))⁻¹ * a * (g * (k : G)) = (d : G) := by
    rw [← hk', ← hg]; group
  have hP2 : IsPGroup 2 (T.map (MulAut.conj (g * (k : G))).toMonoidHom) :=
    (GrS4.isPGroup_of_isSylowTwoIn h.hTsyl).map _
  have hPa : T.map (MulAut.conj (g * (k : G))).toMonoidHom ≤ centralizer ({a} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact comm_conj_of_comm hgd (hdZ z hz)
  have hlt := card_lt_of_le_centralizer hMax h hρ hC hP2 hPa
  rw [Subgroup.card_map_of_injective (MulAut.conj (g * (k : G))).injective] at hlt
  exact lt_irrefl _ hlt

end CFSG.ComponentClassification.GrSLit.L34Tw
