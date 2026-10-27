module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiYTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiYBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

theorem map_conj_szA₁_sup_zpowers {y : G} (hy : y ∈ normalizer (szA₁ T₁ : Set G)) (x : G) :
    (szA₁ T₁ ⊔ zpowers x).map (MulAut.conj y⁻¹).toMonoidHom =
      szA₁ T₁ ⊔ zpowers (y⁻¹ * x * y) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 1
  · ext b
    rw [mem_map_conj_inv_iff]
    exact (mem_normalizer_iff.mp hy b).symm
  · simp

theorem szA_le_szR (T₁ R₂ : Subgroup G) (t : G) : szA₁ T₁ ⊔ zpowers t ≤ szR T₁ R₂ t :=
  sup_le ((szA₁_le T₁).trans (le_szR_left T₁ R₂ t)) (zpowers_le.mpr (mem_szR_right T₁ R₂ t))

theorem map_conj_szA_le_szR {y : G} (hy : y ∈ normalizer (szR T₁ R₂ t : Set G)) :
    (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj y⁻¹).toMonoidHom ≤ szR T₁ R₂ t := by
  intro w hw
  have hw' := szA_le_szR T₁ R₂ t (mem_map_conj_inv_iff.mp hw)
  have h1 := (mem_normalizer_iff''.mp hy _).mp hw'
  simpa [mul_assoc] using h1

theorem szA_mem_gmsRootConjugates (T₁ R₂ : Subgroup G) (t : G) :
    szA₁ T₁ ⊔ zpowers t ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) :=
  ⟨1, by ext x; rw [mem_map_conj_inv_iff, one_mul, inv_one, mul_one], szA_le_szR T₁ R₂ t⟩

theorem SzR2.t_mem_normalizer_sup (hS : SzR2 T₁ R₂ t d) :
    t ∈ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
  mem_normalizer_sup (centralizer_le_normalizer _ (mem_centralizer_iff.mpr hS.t_comm))
    hS.t_mem_normalizer_R₂

namespace SzRCoords2

theorem normalizer_szR_le_normalizer_szA₁ (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (szA₁ T₁ : Set G) := fun _ hn =>
  mem_normalizer_of_forall_inv_mul_mul_mem fun _ hb => h.conj_mem_szA₁ ha hK hn hb

theorem mem_szA₁_sup_zpowers_iff (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {x : G}
    (hx : x ∈ szR T₁ R₂ t) {y : G} :
    y ∈ szA₁ T₁ ⊔ zpowers x ↔ y ∈ szR T₁ R₂ t ∧ (φ y = 0 ∨ φ y = φ x) := by
  have hxC : x ∈ centralizer (szA₁ T₁ : Set G) :=
    mem_centralizer_iff.mpr fun b hb => (h.central x hx b hb).symm
  have hA₁R : ∀ b ∈ szA₁ T₁, b ∈ szR T₁ R₂ t := fun b hb => le_szR_left T₁ R₂ t (szA₁_le T₁ hb)
  constructor
  · intro hy
    obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers hxC hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hpow : ∀ j : ℤ, x ^ (2 * j) ∈ szA₁ T₁ := fun j => by
      rw [zpow_mul, zpow_two, ← _root_.sq]
      exact zpow_mem (h.sq_mem x hx) j
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hb' : b * x ^ (2 * j) ∈ szA₁ T₁ := mul_mem hb (hpow j)
      exact ⟨hA₁R _ hb', Or.inl ((h.ker _ (hA₁R _ hb')).mpr hb')⟩
    · have e : b * x ^ (2 * j + 1) = b * x ^ (2 * j) * x := by
        rw [zpow_add, zpow_one, mul_assoc]
      have hb' : b * x ^ (2 * j) ∈ szA₁ T₁ := mul_mem hb (hpow j)
      rw [e]
      refine ⟨mul_mem (hA₁R _ hb') hx, Or.inr ?_⟩
      rw [h.mul _ (hA₁R _ hb') _ hx, (h.ker _ (hA₁R _ hb')).mpr hb', zero_add]
  · rintro ⟨hyR, hy0 | hyx⟩
    · exact mem_sup_left ((h.ker y hyR).mp hy0)
    · have hb := h.inv_mul_mem_szA₁_of_map_eq hx hyR hyx.symm
      have e : y = x * (x⁻¹ * y) := by group
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left hb)

theorem szA₁_sup_zpowers_eq_of_map_eq (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {x x' : G}
    (hx : x ∈ szR T₁ R₂ t) (hx' : x' ∈ szR T₁ R₂ t) (he : φ x = φ x') :
    szA₁ T₁ ⊔ zpowers x = szA₁ T₁ ⊔ zpowers x' := by
  ext y
  rw [h.mem_szA₁_sup_zpowers_iff hx, h.mem_szA₁_sup_zpowers_iff hx', he]

theorem map_eq_of_szA₁_sup_zpowers_eq (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {x x' : G}
    (hx : x ∈ szR T₁ R₂ t) (h0 : φ x' ≠ 0) (he : szA₁ T₁ ⊔ zpowers x = szA₁ T₁ ⊔ zpowers x') :
    φ x' = φ x := by
  have h1 : x' ∈ szA₁ T₁ ⊔ zpowers x := he ▸ mem_sup_right (mem_zpowers x')
  exact ((h.mem_szA₁_sup_zpowers_iff hx).mp h1).2.resolve_left h0

theorem mem_szCand_of_sq_eq_one (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hγ : γ = 0) {x : G}
    (hx : x ∈ szR T₁ R₂ t) (hx2 : x ^ 2 = 1) (hxH : x ∉ T₁ ⊔ R₂) : φ x ∈ szCand a c := by
  have h3 : (φ x).2.2 = 1 := by
    rcases h.mem x hx with h0 | h1
    · exact absurd ((h.thd_eq_zero_iff x hx).mp h0) hxH
    · exact h1
  refine ⟨h3, ?_⟩
  have hsq := h.sq x hx
  rw [hx2, h.v_one, hγ] at hsq
  simp only [szSqMap, h3, zero_mul, add_zero] at hsq
  linear_combination -hsq

theorem map_conj_t_mem_szCand (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ht2 : t ^ 2 = 1) (hγ : γ = 0) {n : G}
    (hn : n ∈ normalizer (szR T₁ R₂ t : Set G)) : φ (n⁻¹ * t * n) ∈ szCand a c := by
  refine h.mem_szCand_of_sq_eq_one hγ ((mem_normalizer_iff''.mp hn t).mp (mem_szR_right T₁ R₂ t))
    ?_ (h.conj_t_not_mem_sup ha hK hn).1
  rw [show (n⁻¹ * t * n) ^ 2 = n⁻¹ * t ^ 2 * n by simp only [_root_.sq]; group, ht2]
  group

theorem two_mul_card_sup (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    2 * Nat.card (T₁ ⊔ R₂ : Subgroup G) = Nat.card (szR T₁ R₂ t) := by
  have hidx := Endings.relIndex_sup_zpowers_eq_two h.t_not_mem_sup hS.t_mem_normalizer_sup
    (by rw [← _root_.sq, hS.t_sq])
  have h1 := Subgroup.relIndex_mul_card (T₁ ⊔ R₂) (szR T₁ R₂ t)
  rw [inf_eq_left.mpr (sup_le_szR T₁ R₂ t)] at h1
  rw [← h1]
  exact congrArg (· * _) hidx.symm

theorem _root_.CFSG.SeitzReduction.RankOne.SzRootCoords.exists_mul_ne
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    ∃ y₁ ∈ T₁, ∃ y₂ ∈ T₁, y₁ * y₂ ≠ y₂ * y₁ := by
  obtain ⟨w, hw⟩ := SzStartField.exists_pow_theta_add_ne_zero ha hK
  obtain ⟨y₁, hy₁, hu₁, -⟩ := hc.surj 1 0
  obtain ⟨y₂, hy₂, hu₂, -⟩ := hc.surj w 0
  refine ⟨y₁, hy₁, y₂, hy₂, fun he => hw ?_⟩
  have h1 := (hc.comm hy₁ hy₂).2
  rw [he, mul_inv_cancel_right, mul_inv_cancel, hc.v_one, hu₁, hu₂, one_mul, one_pow,
    mul_one] at h1
  exact h1.symm

theorem conj_t_not_mem_sup_of_gamma_eq_zero (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hγ : γ = 0) (g : G) : g⁻¹ * t * g ∉ T₁ ⊔ R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxH
  have hx : g⁻¹ * t * g ∈ szR T₁ R₂ t := sup_le_szR T₁ R₂ t hxH
  obtain ⟨k, -, hk⟩ := h.exists_conj_szR_inf_centralizer hS hc ha hK hCt hx
  have hcomm := h.commute_of_gamma_eq_zero hγ
  have hup : Nat.card (szR T₁ R₂ t ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G) ≤
      2 * Nat.card T₁ := by
    have h1 := card_le_of_isPGroup_of_le ((h.isPGroup_szR hc ha hK).to_le inf_le_left)
      (inf_le_right : szR T₁ R₂ t ⊓ centralizer ({g⁻¹ * t * g} : Set G) ≤ _)
    rwa [two_pow_factorization_card_centralizer_conj hCt g] at h1
  have hq : 8 ≤ Fintype.card K := by
    rw [hK, show 2 * a + 1 = 3 + (2 * a - 2) by omega, pow_add]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hT₁ : Nat.card T₁ = Fintype.card K ^ 2 := by
    rw [hc.card_eq, Nat.card_eq_fintype_card, _root_.sq]
  have hA₁ : Nat.card (szA₁ T₁) = Fintype.card K := by
    rw [hc.card_szA₁ ha hK, Nat.card_eq_fintype_card]
  have h1 : ((T₁ ⊔ R₂ : Subgroup G) : Set G) = (T₁ : Set G) * (R₂ : Set G) :=
    coe_mul_of_left_le_normalizer_right T₁ R₂ hS.le_normalizer_R₂
  have hxH' : g⁻¹ * t * g ∈ ((T₁ ⊔ R₂ : Subgroup G) : Set G) := hxH
  rw [h1] at hxH'
  obtain ⟨y, hy, r, hr, hyr⟩ := hxH'
  simp only at hyr
  have hR₂C : ∀ r' ∈ R₂, r' ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
    intro r' hr'
    rw [mem_centralizer_singleton_iff, ← hyr]
    calc r' * (y * r) = y * (r' * r) := by rw [← mul_assoc, ← hcomm y hy r' hr', mul_assoc]
      _ = y * (r * r') := by rw [hS.R₂_comm r' hr' r hr]
      _ = y * r * r' := by rw [mul_assoc]
  by_cases hyA : y ∈ szA₁ T₁
  · have hxR₂ : g⁻¹ * t * g ∈ R₂ := hyr ▸ mul_mem (hS.le_R₂ hyA) hr
    have hle : T₁ ⊔ R₂ ≤ szR T₁ R₂ t ⊓ centralizer ({g⁻¹ * t * g} : Set G) :=
      le_inf (sup_le_szR T₁ R₂ t) (sup_le (fun y' hy' =>
        mem_centralizer_singleton_iff.mpr (hcomm y' hy' _ hxR₂)) hR₂C)
    have h2 := (Subgroup.card_le_of_le hle).trans hup
    have h3 := h.two_mul_card_sup hS
    rw [h.card_szR_eq hc ha hK] at h3
    rw [hT₁] at h2
    nlinarith
  · have hyR₂ : y ∉ R₂ := fun hyR => hyA (hS.inf_le (mem_inf.mpr ⟨hy, hyR⟩))
    have hidx := relIndex_sup_zpowers_eq_two_of_mul_self_mem hyR₂ (hS.le_normalizer_R₂ hy)
      (by rw [← _root_.sq]; exact hS.le_R₂ (hc.sq_mem_szA₁ ha hK hy))
    have hcard := Subgroup.relIndex_mul_card R₂ (R₂ ⊔ zpowers y)
    rw [inf_eq_left.mpr le_sup_left, hidx, h.card_R₂ hS, hA₁] at hcard
    have hyC : y ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
      rw [mem_centralizer_singleton_iff, ← hyr]
      calc y * (y * r) = y * (r * y) := by rw [hcomm y hy r hr]
        _ = y * r * y := by rw [mul_assoc]
    have hle : R₂ ⊔ zpowers y ≤ szR T₁ R₂ t ⊓ centralizer ({g⁻¹ * t * g} : Set G) :=
      le_inf (sup_le (le_szR_mid T₁ R₂ t) (zpowers_le.mpr (le_szR_left T₁ R₂ t hy)))
        (sup_le hR₂C (zpowers_le.mpr hyC))
    have heq : R₂ ⊔ zpowers y = szR T₁ R₂ t ⊓ centralizer ({g⁻¹ * t * g} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [← hcard]
        calc _ ≤ 2 * Nat.card T₁ := hup
          _ = _ := by rw [hT₁, _root_.sq])
    have hyC' : y ∈ centralizer (R₂ : Set G) :=
      mem_centralizer_iff.mpr fun r' hr' => (hcomm y hy r' hr').symm
    have hab : R₂ ⊔ zpowers y ≤ centralizer ((R₂ ⊔ zpowers y : Subgroup G) : Set G) := by
      have hR₂ : R₂ ≤ centralizer (R₂ : Set G) := fun r' hr' =>
        mem_centralizer_iff.mpr fun r'' hr'' => hS.R₂_comm r'' hr'' r' hr'
      have h4 : R₂ ⊔ zpowers y ≤ centralizer (R₂ : Set G) := sup_le hR₂ (zpowers_le.mpr hyC')
      have h5 : R₂ ⊔ zpowers y ≤ centralizer (zpowers y : Set G) :=
        sup_le (le_centralizer_iff.mp (zpowers_le.mpr hyC'))
          (zpowers_le.mpr (mem_centralizer_iff.mpr fun z hz =>
            (commute_of_mem_zpowers hz rfl).symm))
      exact sup_le (le_centralizer_iff.mp h4) (le_centralizer_iff.mp h5)
    obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hc.exists_mul_ne ha hK
    have hmem : ∀ p ∈ T₁, k⁻¹ * p * k ∈ R₂ ⊔ zpowers y := fun p hp => by
      rw [heq, hk]
      simpa [mul_assoc] using mem_sup_left (S := T₁) (T := zpowers t) hp
    have e := mem_centralizer_iff.mp (hab (hmem y₂ hy₂)) _ (hmem y₁ hy₁)
    apply hne
    calc y₁ * y₂ = k * ((k⁻¹ * y₁ * k) * (k⁻¹ * y₂ * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y₂ * k) * (k⁻¹ * y₁ * k)) * k⁻¹ := by rw [e]
      _ = y₂ * y₁ := by group

theorem map_conj_szA_eq_and_mem_szCand (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hγ : γ = 0) {g : G}
    (hg : (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj g⁻¹).toMonoidHom ≤ szR T₁ R₂ t) :
    (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj g⁻¹).toMonoidHom = szA₁ T₁ ⊔ zpowers (g⁻¹ * t * g) ∧
      φ (g⁻¹ * t * g) ∈ szCand a c := by
  have ht : t ∈ centralizer (T₁ : Set G) := mem_centralizer_iff.mpr hS.t_comm
  have htA₁ : t ∈ centralizer (szA₁ T₁ : Set G) := centralizer_le (szA₁_le T₁) ht
  have hxA : g⁻¹ * t * g ∈ (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj g⁻¹).toMonoidHom :=
    mem_map_conj_inv_iff.mpr (by simpa [mul_assoc] using mem_sup_right (mem_zpowers t))
  have hx := hg hxA
  obtain ⟨k, hkt, hk⟩ := h.exists_conj_szR_inf_centralizer hS hc ha hK hCt hx
  have hkN := h.mem_normalizer_szA₁_of_conj hS hc ha hK hCt hx hk
  have hZ := SzRootCoords.inf_centralizer_sup_eq ht
  have hAab : ∀ w ∈ szA₁ T₁ ⊔ zpowers t, w * t = t * w := fun w hw => by
    rw [← hZ] at hw
    exact (mem_centralizer_iff.mp (mem_inf.mp hw).2 t (mem_sup_right (mem_zpowers t))).symm
  have key : ∀ w ∈ szA₁ T₁ ⊔ zpowers t, k * (g⁻¹ * w * g) * k⁻¹ ∈ szA₁ T₁ ⊔ zpowers t := by
    intro w hw
    have hw' : g⁻¹ * w * g ∈ (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj g⁻¹).toMonoidHom :=
      mem_map_conj_inv_iff.mpr (by simpa [mul_assoc] using hw)
    have hwC : g⁻¹ * w * g ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g⁻¹ * w * g * (g⁻¹ * t * g) = g⁻¹ * (w * t) * g := by group
        _ = g⁻¹ * (t * w) * g := by rw [hAab w hw]
        _ = g⁻¹ * t * g * (g⁻¹ * w * g) := by group
    have hwT := (hk _).mp (mem_inf.mpr ⟨hg hw', hwC⟩)
    refine hc.mem_of_sq_eq_one ha hK ht hS.t_sq hwT ?_
    rw [show (k * (g⁻¹ * w * g) * k⁻¹) ^ 2 = k * g⁻¹ * w ^ 2 * g * k⁻¹ by
      simp only [_root_.sq]; group, hc.sq_eq_one_of_mem_szA₁_sup ha hK ht hS.t_sq hw]
    group
  have hm : g * k⁻¹ ∈ normalizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
      simpa [mul_assoc] using key w hw
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le (fun b hb => ?_) (zpowers_le.mpr hxA)), ?_⟩
  · have hw' := mem_map_conj_inv_iff.mp hw
    have hkw : k * w * k⁻¹ ∈ szA₁ T₁ ⊔ zpowers t := by
      have h2 := (mem_normalizer_iff''.mp hm _).mp hw'
      simpa [mul_assoc] using h2
    obtain ⟨b, hb, z, hz, hbz⟩ := exists_mul_eq_of_mem_sup_zpowers htA₁ hkw
    have hb' : k⁻¹ * b * k ∈ szA₁ T₁ := (mem_normalizer_iff''.mp hkN b).mp hb
    have hz' : k⁻¹ * z * k ∈ zpowers (g⁻¹ * t * g) := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
      refine mem_zpowers_iff.mpr ⟨j, ?_⟩
      rw [← hkt]
      simpa using conj_zpow (a := k⁻¹) (b := t) (i := j)
    have e : w = (k⁻¹ * b * k) * (k⁻¹ * z * k) := by
      calc w = k⁻¹ * (k * w * k⁻¹) * k := by group
        _ = k⁻¹ * (b * z) * k := by rw [hbz]
        _ = (k⁻¹ * b * k) * (k⁻¹ * z * k) := by group
    rw [e]
    exact mul_mem (mem_sup_left hb') (mem_sup_right hz')
  · refine mem_map_conj_inv_iff.mpr ?_
    have hkb : k * b * k⁻¹ ∈ szA₁ T₁ := (mem_normalizer_iff.mp hkN b).mp hb
    have h2 := (mem_normalizer_iff.mp hm _).mp
      ((le_sup_left : szA₁ T₁ ≤ szA₁ T₁ ⊔ zpowers t) hkb)
    simpa [mul_assoc] using h2
  · refine h.mem_szCand_of_sq_eq_one hγ hx ?_
      (h.conj_t_not_mem_sup_of_gamma_eq_zero hS hc ha hK hCt hγ g)
    rw [show (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g by simp only [_root_.sq]; group, hS.t_sq]
    group

theorem exists_mem_normalizer_map_conj_t_eq (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hγ : γ = 0) {z : K × K × K} (hz : z ∈ szCand a c) :
    ∃ y ∈ normalizer (szR T₁ R₂ t : Set G), φ (y⁻¹ * t * y) = z := by
  have htR := mem_szR_right T₁ R₂ t
  by_cases hz0 : z = (0, 0, 1)
  · exact ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.of_t, hz0]⟩
  obtain ⟨n, hn, hnt⟩ := h.exists_mem_normalizer_conj_t_not_mem hG hS hc ha hK hμ hCt
  have hnR : n⁻¹ * t * n ∈ szR T₁ R₂ t := (mem_normalizer_iff''.mp hn t).mp htR
  have hz₀ := h.map_conj_t_mem_szCand ha hK hS.t_sq hγ hn
  have hz₀0 : φ (n⁻¹ * t * n) ≠ (0, 0, 1) := fun he =>
    hnt (h.inv_mul_mem_szA₁_of_map_eq htR hnR (h.of_t.trans he.symm))
  obtain ⟨l, hl0, hl⟩ := exists_szTorusSmul_eq_of_mem_szCand hK hz₀ hz hz₀0 hz0
  obtain ⟨m, hm⟩ := hμ l hl0
  refine ⟨n * d ^ ((2 ^ (a + 1) + 1) * m),
    mul_mem hn (pow_mem (hS.d_mem_normalizer_szR hc) _), ?_⟩
  have e : (n * d ^ ((2 ^ (a + 1) + 1) * m))⁻¹ * t * (n * d ^ ((2 ^ (a + 1) + 1) * m)) =
      (d ^ ((2 ^ (a + 1) + 1) * m))⁻¹ * (n⁻¹ * t * n) * d ^ ((2 ^ (a + 1) + 1) * m) := by group
  rw [e, h.map_conj_d_pow hS hc ha hK _ hnR, pow_mul, hm, hl]

theorem exists_eq_szA₁_sup_zpowers (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    {S : Subgroup G} (hSΔ : S ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) :
    ∃ x ∈ szR T₁ R₂ t, φ x ∈ szCand a c ∧ S = szA₁ T₁ ⊔ zpowers x := by
  obtain ⟨g, rfl, hg⟩ := hSΔ
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  obtain ⟨hSeq, hmem⟩ := h.map_conj_szA_eq_and_mem_szCand hS hc ha hK hCt hγ hg
  refine ⟨g⁻¹ * t * g, hg ?_, hmem, hSeq⟩
  rw [hSeq]
  exact mem_sup_right (mem_zpowers _)

theorem ncard_gmsRootConjugates (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).ncard = Fintype.card K := by
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  have hNA := h.normalizer_szR_le_normalizer_szA₁ ha hK
  choose sec hsecR hsecφ using h.surj
  have hCV : ∀ z ∈ szCand a c, z ∈ szCoordSpace K := fun z hz => Or.inr (mem_szCand.mp hz).1
  rw [← ncard_szCand a c]
  refine (Set.ncard_congr (fun z hz => szA₁ T₁ ⊔ zpowers (sec z (hCV z hz))) ?_ ?_ ?_).symm
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := h.exists_mem_normalizer_map_conj_t_eq hG hS hc ha hK hμ hCt hγ hz
    have hyR : y⁻¹ * t * y ∈ szR T₁ R₂ t := (mem_normalizer_iff''.mp hy t).mp
      (mem_szR_right T₁ R₂ t)
    have heq : szA₁ T₁ ⊔ zpowers (sec z (hCV z hz)) =
        (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj y⁻¹).toMonoidHom := by
      rw [map_conj_szA₁_sup_zpowers (hNA hy) t]
      exact h.szA₁_sup_zpowers_eq_of_map_eq (hsecR _ _) hyR
        ((hsecφ z (hCV z hz)).trans hyz.symm)
    exact ⟨y, heq, heq ▸ map_conj_szA_le_szR hy⟩
  · intro z z' hz hz' he
    have h0 : φ (sec z' (hCV z' hz')) ≠ 0 := by
      rw [hsecφ z' (hCV z' hz')]
      intro h0
      have h1 := (mem_szCand.mp hz').1
      rw [h0] at h1
      exact zero_ne_one h1
    have h1 := h.map_eq_of_szA₁_sup_zpowers_eq (hsecR _ _) h0 he
    rw [hsecφ z' (hCV z' hz'), hsecφ z (hCV z hz)] at h1
    exact h1.symm
  · intro S hSΔ
    obtain ⟨x, hx, hxC, rfl⟩ := h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt hSΔ
    exact ⟨φ x, hxC, h.szA₁_sup_zpowers_eq_of_map_eq (hsecR _ _) hx (hsecφ _ _)⟩

theorem two_transitive_gmsRootConjugates (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁) :
    ∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t), Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range,
        σ Q₁ = Z₁ ∧ σ Q₂ = Z₂ := by
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  have hNA := h.normalizer_szR_le_normalizer_szA₁ ha hK
  have hdN := hS.d_mem_normalizer_szR hc
  have htR := mem_szR_right T₁ R₂ t
  set Δ := gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)
  set Y := normalizer (szR T₁ R₂ t : Set G)
  let x₀ : Δ := ⟨szA₁ T₁ ⊔ zpowers t, szA_mem_gmsRootConjugates T₁ R₂ t⟩
  have hsmul : ∀ (n : Y) (S : Δ),
      ((n • S : Δ) : Subgroup G) = (S : Subgroup G).map (MulAut.conj (n : G)).toMonoidHom :=
    fun _ _ => rfl
  have htrans : ∀ S : Δ, ∃ n : Y, n • x₀ = S := by
    intro S
    obtain ⟨x, hx, hxC, hSx⟩ := h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt S.2
    obtain ⟨y, hy, hyx⟩ := h.exists_mem_normalizer_map_conj_t_eq hG hS hc ha hK hμ hCt hγ hxC
    have hyR : y⁻¹ * t * y ∈ szR T₁ R₂ t := (mem_normalizer_iff''.mp hy t).mp htR
    refine ⟨⟨y⁻¹, inv_mem hy⟩, Subtype.ext ?_⟩
    rw [hsmul, map_conj_szA₁_sup_zpowers (hNA hy) t, hSx]
    exact h.szA₁_sup_zpowers_eq_of_map_eq hyR hx hyx
  have hne : ∀ S : Δ, S ≠ x₀ → ∃ x ∈ szR T₁ R₂ t, φ x ∈ szCand a c ∧ φ x ≠ (0, 0, 1) ∧
      (S : Subgroup G) = szA₁ T₁ ⊔ zpowers x := by
    intro S hS0
    obtain ⟨x, hx, hxC, hSx⟩ := h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt S.2
    refine ⟨x, hx, hxC, fun he => hS0 (Subtype.ext ?_), hSx⟩
    rw [hSx]
    exact h.szA₁_sup_zpowers_eq_of_map_eq hx htR (he.trans h.of_t.symm)
  have hstab : ∀ S S' : Δ, S ≠ x₀ → S' ≠ x₀ → ∃ n : Y, n • x₀ = x₀ ∧ n • S = S' := by
    intro S S' hS0 hS0'
    obtain ⟨x, hx, hxC, hx0, hSx⟩ := hne S hS0
    obtain ⟨x', hx', hxC', hx0', hSx'⟩ := hne S' hS0'
    obtain ⟨l, hl0, hl⟩ := exists_szTorusSmul_eq_of_mem_szCand hK hxC hxC' hx0 hx0'
    obtain ⟨m, hm⟩ := hμ l hl0
    set e := d ^ ((2 ^ (a + 1) + 1) * m) with he
    have heN : e ∈ Y := pow_mem hdN _
    refine ⟨⟨e⁻¹, inv_mem heN⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [hsmul]
      show (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj e⁻¹).toMonoidHom = szA₁ T₁ ⊔ zpowers t
      rw [map_conj_szA₁_sup_zpowers (hNA heN) t]
      have hde : e * t = t * e := (Commute.pow_left hS.d_comm _).eq
      rw [mul_assoc, ← hde, inv_mul_cancel_left]
    · rw [hsmul, hSx, map_conj_szA₁_sup_zpowers (hNA heN) x, hSx']
      have hexR : e⁻¹ * x * e ∈ szR T₁ R₂ t := (mem_normalizer_iff''.mp heN x).mp hx
      refine h.szA₁_sup_zpowers_eq_of_map_eq hexR hx' ?_
      rw [he, h.map_conj_d_pow hS hc ha hK _ hx, pow_mul, hm, hl]
  intro Q₁ Q₂ Z₁ Z₂ hQ hZ
  obtain ⟨n, hn1, hn2⟩ := exists_smul_eq_smul_eq_of_stabilizer x₀ htrans hstab hQ hZ
  exact ⟨gmsRootConjugateAction _ _ n, ⟨n, rfl⟩, hn1, hn2⟩

theorem map_conj_eq_of_mem_szR (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    {S : Subgroup G} (hSΔ : S ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) {r : G}
    (hr : r ∈ szR T₁ R₂ t) : S.map (MulAut.conj r).toMonoidHom = S := by
  obtain ⟨x, hx, -, rfl⟩ := h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt hSΔ
  have hr' : r⁻¹ ∈ normalizer (szA₁ T₁ : Set G) :=
    h.szR_le_normalizer_szA₁ (inv_mem hr)
  have h1 := map_conj_szA₁_sup_zpowers hr' x
  rw [inv_inv] at h1
  rw [h1]
  have hxr : r * x * r⁻¹ ∈ szR T₁ R₂ t := mul_mem (mul_mem hr hx) (inv_mem hr)
  refine h.szA₁_sup_zpowers_eq_of_map_eq hxr hx ?_
  rw [h.mul _ (mul_mem hr hx) _ (inv_mem hr), h.mul _ hr _ hx]
  have h2 := h.mul _ hr _ (inv_mem hr)
  rw [mul_inv_cancel, h.map_one] at h2
  rw [show φ r + φ x + φ r⁻¹ = φ x + (φ r + φ r⁻¹) by abel, ← h2, add_zero]

end SzRCoords2

end CFSG.SeitzReduction.RankOne
