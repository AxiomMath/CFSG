module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiNotSylowBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28Elem

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

theorem two_pow_factorization_card_centralizer
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 = 2 * Nat.card T₁ := by
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 (centralizer ({t} : Set G))))
  rw [← Sylow.card_eq_multiplicity P₀, hCt P₀]

theorem two_pow_factorization_card_centralizer_conj
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) (g : G) :
    2 ^ (Nat.card (centralizer ({g⁻¹ * t * g} : Set G))).factorization 2 = 2 * Nat.card T₁ := by
  rw [card_centralizer_inv_mul_mul]
  exact two_pow_factorization_card_centralizer hCt

namespace SzRCoords2

theorem t_not_mem_sup (h : SzRCoords2 T₁ R₂ t a u v φ γ c) : t ∉ T₁ ⊔ R₂ := by
  intro ht
  have h1 := (h.thd_eq_zero_iff t (mem_szR_right T₁ R₂ t)).mpr ht
  rw [h.of_t] at h1
  simp at h1

theorem orderOf_t (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) : orderOf t = 2 :=
  orderOf_eq_prime hS.t_sq fun h1 => h.t_not_mem_sup (h1 ▸ one_mem _)

theorem inf_zpowers_eq_bot (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    T₁ ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxT, hxt⟩ := mem_inf.mp hx
  rcases mem_zpowers_involution_eq_one_or_eq hS.t_sq hxt with rfl | rfl
  · exact one_mem _
  · exact absurd (mem_sup_left hxT) h.t_not_mem_sup

theorem card_sup_zpowers (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    Nat.card (T₁ ⊔ zpowers t : Subgroup G) = Nat.card T₁ * 2 :=
  card_sup_zpowers_of_disjoint (mem_centralizer_iff.mpr hS.t_comm) (h.orderOf_t hS)
    (h.inf_zpowers_eq_bot hS)

theorem isSylowOf_sup_zpowers (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    IsSylowOf 2 (T₁ ⊔ zpowers t) (centralizer ({t} : Set G)) :=
  isSylowOf_of_card (sup_zpowers_le_centralizer_singleton (mem_centralizer_iff.mpr hS.t_comm))
    (by rw [h.card_sup_zpowers hS, two_pow_factorization_card_centralizer hCt, mul_comm])

theorem card_szR_eq (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    Nat.card (szR T₁ R₂ t) = 2 * Fintype.card K ^ 2 * Fintype.card K := by
  rw [h.card_szR, card_szCoordSpace, hc.card_szA₁ ha hK, Nat.card_eq_fintype_card]

theorem isPGroup_szR (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) : IsPGroup 2 (szR T₁ R₂ t) :=
  IsPGroup.of_card (n := 6 * a + 4) (by rw [h.card_szR_eq hc ha hK, hK]; ring)

theorem conj_t_not_mem_szA₁ (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) (g : G) :
    g⁻¹ * t * g ∉ szA₁ T₁ := by
  intro hb
  have hle : szR T₁ R₂ t ≤ centralizer ({g⁻¹ * t * g} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (h.central x hx _ hb)
  have h1 := card_le_of_isPGroup_of_le (h.isPGroup_szR hc ha hK) hle
  rw [two_pow_factorization_card_centralizer_conj hCt g, h.card_szR_eq hc ha hK, hc.card_eq,
    Nat.card_eq_fintype_card] at h1
  have hq : 2 ≤ Fintype.card K := by
    rw [hK]
    exact Nat.le_self_pow (by omega) 2
  nlinarith

theorem szR_le_normalizer_szA₁ (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    szR T₁ R₂ t ≤ normalizer (szA₁ T₁ : Set G) := by
  intro r hr
  refine mem_normalizer_iff.mpr fun b => ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [h.central r hr b hb, mul_inv_cancel_right]
    exact hb
  · have e := h.central r hr _ hb
    have e' : r * b * r⁻¹ = b := by
      calc r * b * r⁻¹ = r⁻¹ * (r * (r * b * r⁻¹)) := by group
        _ = r⁻¹ * (r * b * r⁻¹ * r) := by rw [e]
        _ = b := by group
    rwa [e'] at hb

theorem exists_conj_szR_inf_centralizer (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) {g : G}
    (hx : g⁻¹ * t * g ∈ szR T₁ R₂ t) :
    ∃ k : G, k⁻¹ * t * k = g⁻¹ * t * g ∧ ∀ y : G,
      y ∈ szR T₁ R₂ t ⊓ centralizer ({g⁻¹ * t * g} : Set G) ↔ k * y * k⁻¹ ∈ T₁ ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := h.isSylowOf_sup_zpowers hS hCt
  refine exists_conj_eq_of_card_le hsyl.le hsyl.card_eq inf_le_right
    ((h.isPGroup_szR hc ha hK).to_le inf_le_left) ?_
  have h1 := h.card_szR_le_mul hx
  rw [h.card_szR_eq hc ha hK] at h1
  rw [h.card_sup_zpowers hS, hc.card_eq, Nat.card_eq_fintype_card]
  have hq : 0 < Fintype.card K := Fintype.card_pos
  nlinarith

theorem mem_normalizer_szA₁_of_conj (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) {x k : G}
    (hx : x ∈ szR T₁ R₂ t)
    (hk : ∀ y : G, y ∈ szR T₁ R₂ t ⊓ centralizer ({x} : Set G) ↔ k * y * k⁻¹ ∈ T₁ ⊔ zpowers t) :
    k ∈ normalizer (szA₁ T₁ : Set G) := by
  have ht : t ∈ centralizer (T₁ : Set G) := mem_centralizer_iff.mpr hS.t_comm
  have htA : t ∈ centralizer (szA₁ T₁ : Set G) := centralizer_le (szA₁_le T₁) ht
  have key : ∀ b ∈ szA₁ T₁, k * b * k⁻¹ ∈ szA₁ T₁ := by
    intro b hb
    have hbR : b ∈ szR T₁ R₂ t := le_szR_left T₁ R₂ t (szA₁_le T₁ hb)
    have hbC : b ∈ szR T₁ R₂ t ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨hbR, mem_centralizer_singleton_iff.mpr (h.central x hx b hb).symm⟩
    have hbT : k * b * k⁻¹ ∈ T₁ ⊔ zpowers t := (hk b).mp hbC
    have hbZ : k * b * k⁻¹ ∈ (T₁ ⊔ zpowers t) ⊓ centralizer ((T₁ ⊔ zpowers t : Subgroup G) :
        Set G) := by
      refine mem_inf.mpr ⟨hbT, mem_centralizer_iff.mpr fun p hp => ?_⟩
      have hp' : k⁻¹ * p * k ∈ szR T₁ R₂ t ⊓ centralizer ({x} : Set G) := by
        rw [hk]
        simpa [mul_assoc] using hp
      have e := h.central _ (mem_inf.mp hp').1 b hb
      calc p * (k * b * k⁻¹) = k * ((k⁻¹ * p * k) * b) * k⁻¹ := by group
        _ = k * (b * (k⁻¹ * p * k)) * k⁻¹ := by rw [e]
        _ = k * b * k⁻¹ * p := by group
    rw [SzRootCoords.inf_centralizer_sup_eq ht] at hbZ
    obtain ⟨b', hb', z, hz, hbz⟩ := exists_mul_eq_of_mem_sup_zpowers htA hbZ
    rcases mem_zpowers_involution_eq_one_or_eq hS.t_sq hz with hz1 | hz1
    · rw [← hbz, hz1, mul_one]
      exact hb'
    · rw [hz1] at hbz
      exfalso
      obtain ⟨r, -, hr⟩ := hS.rho_surj b' hb'
      apply h.conj_t_not_mem_szA₁ hc ha hK hCt (r⁻¹ * k)
      have e : (r⁻¹ * k)⁻¹ * t * (r⁻¹ * k) = k⁻¹ * (r * t * r⁻¹ * t⁻¹ * t) * k := by group
      rw [e, hr, hbz, show k⁻¹ * (k * b * k⁻¹) * k = b by group]
      exact hb
  have hk' : k⁻¹ ∈ normalizer (szA₁ T₁ : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun b hb => by simpa using key b hb
  simpa using inv_mem hk'

theorem conj_t_not_mem_sup_of_isSylowOf (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hR : IsSylowOf 2 (szR T₁ R₂ t) ⊤) (g : G) : g⁻¹ * t * g ∉ T₁ ⊔ R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxH
  have hx : g⁻¹ * t * g ∈ szR T₁ R₂ t := sup_le_szR T₁ R₂ t hxH
  obtain ⟨k, hkt, hk⟩ := h.exists_conj_szR_inf_centralizer hS hc ha hK hCt hx
  have hkN := h.mem_normalizer_szA₁_of_conj hS hc ha hK hCt hx hk
  obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_inv_mul_mem_of_isSylowOf hR
    h.szR_le_normalizer_szA₁ h.comm_mem (mem_szR_right T₁ R₂ t) hkN (hkt ▸ hx)
  apply (h.conj_t_not_mem_sup ha hK hn).1
  rw [hkt] at hnt
  have e : n⁻¹ * t * n = g⁻¹ * t * g * ((g⁻¹ * t * g)⁻¹ * (n⁻¹ * t * n)) := by group
  rw [e]
  exact mul_mem hxH (mem_sup_left (szA₁_le T₁ hnt))

end SzRCoords2

theorem isSylowOf_top_of_sylow_eq {R : Subgroup G} {S : Sylow 2 G} (hS : (S : Subgroup G) = R) :
    IsSylowOf 2 R ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_iff.mpr ⟨le_top, hS ▸ S.isPGroup', ?_⟩
  rw [relIndex_top_right, ← hS]
  exact S.not_dvd_index

theorem exists_sylow_eq_of_isSylowOf_top {R : Subgroup G} (hR : IsSylowOf 2 R ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hR2, hRidx⟩ := isSylowOf_iff.mp hR
  rw [relIndex_top_right] at hRidx
  exact ⟨hR2.toSylow hRidx, IsPGroup.toSylow_coe hR2 hRidx⟩

namespace SzR2

theorem not_isSylow (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) (hS : SzR2 T₁ R₂ t d)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = szR T₁ R₂ t := by
  rintro ⟨S, hSR⟩
  obtain ⟨φ, γ, c, h⟩ := hS.exists_coords hc ha hK hμ
  have hR := isSylowOf_top_of_sylow_eq hSR
  have htW := h.t_not_mem_sup
  have htt : t * t = 1 := by rw [← sq, hS.t_sq]
  have htN : t ∈ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
    mem_normalizer_sup (centralizer_le_normalizer _ (mem_centralizer_iff.mpr hS.t_comm))
      hS.t_mem_normalizer_R₂
  have hidx : (T₁ ⊔ R₂).relIndex (szR T₁ R₂ t) = 2 :=
    Endings.relIndex_sup_zpowers_eq_two htW htN htt
  apply hG
  refine CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson (T := szR T₁ R₂ t)
    (U := T₁ ⊔ R₂) (hSR ▸ S.isPGroup') (hSR ▸ S.not_dvd_index) (sup_le_szR T₁ R₂ t) hidx
    (mem_szR_right T₁ R₂ t) htW (fun y _ hyU => ?_)
    (h.conj_t_not_mem_sup_of_isSylowOf hS hc ha hK hCt hR)
  exact Endings.orderOf_le_of_ne_one htt fun hy1 => hyU (hy1 ▸ one_mem _)

theorem not_isSylowOf_normalizer (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    ¬ IsSylowOf 2 (szR T₁ R₂ t) (normalizer (szR T₁ R₂ t : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hRN
  obtain ⟨φ, γ, c, h⟩ := hS.exists_coords hc ha hK hμ
  apply hS.not_isSylow hG hc ha hK hμ hCt
  refine exists_sylow_eq_of_isSylowOf_top (by_contra fun hnot => ?_)
  obtain ⟨P, hRP, z, hzP, hzN, hzR⟩ :=
    GMS28.exists_mem_normalizer_of_not_isSylowOf (h.isPGroup_szR hc ha hK) hnot
  have hle : szR T₁ R₂ t ⊔ zpowers z ≤ normalizer (szR T₁ R₂ t : Set G) :=
    sup_le (le_normalizer) (zpowers_le.mpr hzN)
  have heq := hRN.eq_of_le le_sup_left hle (P.isPGroup'.to_le (sup_le hRP (zpowers_le.mpr hzP)))
  exact hzR (heq ▸ mem_sup_right (mem_zpowers z))

theorem exists_mem_normalizer_not_mem (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    ∃ z ∈ normalizer (szR T₁ R₂ t : Set G), z ∉ szR T₁ R₂ t ∧
      IsPGroup 2 (szR T₁ R₂ t ⊔ zpowers z : Subgroup G) := by
  obtain ⟨φ, γ, c, h⟩ := hS.exists_coords hc ha hK hμ
  have hnot : ¬ IsSylowOf 2 (szR T₁ R₂ t) ⊤ := fun hR =>
    hS.not_isSylow hG hc ha hK hμ hCt (exists_sylow_eq_of_isSylowOf_top hR)
  obtain ⟨P, hRP, z, hzP, hzN, hzR⟩ :=
    GMS28.exists_mem_normalizer_of_not_isSylowOf (h.isPGroup_szR hc ha hK) hnot
  exact ⟨z, hzN, hzR, P.isPGroup'.to_le (sup_le hRP (zpowers_le.mpr hzP))⟩

end SzR2

end CFSG.SeitzReduction.RankOne
