module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KOrd

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem c13K_eq_pCore_sup {K : Subgroup G} {n : ℕ} (hK : Nat.card ↥K = 3 * 2 ^ n) {ρ l : G}
    (hρ : ρ ∈ K) (hl : l ∈ K) (hρ3 : orderOf ρ = 3) (hl2 : l ^ 2 = 1)
    (hlρ : l * ρ * l⁻¹ = ρ⁻¹) :
    K = CFSG.Open.pCoreOf 2 K ⊔ closure ({ρ, l} : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρK : ↥K := ⟨ρ, hρ⟩
  let lK : ↥K := ⟨l, hl⟩
  have hρK3 : orderOf ρK = 3 := by rw [Subgroup.orderOf_mk, hρ3]
  have hρKpow : ρK ^ 3 = 1 := by rw [← hρK3]; exact pow_orderOf_eq_one ρK
  have hlK2 : lK ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show l ^ 2 = 1
    exact hl2
  have hlKρK : lK * ρK * lK⁻¹ = ρK⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    show l * ρ * l⁻¹ = ρ⁻¹
    exact hlρ
  let P : Sylow 2 ↥K := (inferInstance : Nonempty (Sylow 2 ↥K)).some
  have hPindex : (P : Subgroup ↥K).index = 3 := by
    have hnot2 : ¬ 2 ∣ (P : Subgroup ↥K).index := Sylow.not_dvd_index P
    have hcop : ((P : Subgroup ↥K).index).Coprime (2 ^ n) :=
      Nat.prime_two.coprime_pow_of_not_dvd hnot2
    have hdvdK : (P : Subgroup ↥K).index ∣ Nat.card ↥K :=
      ⟨Nat.card ↥(P : Subgroup ↥K), by rw [mul_comm, Subgroup.card_mul_index]⟩
    have hdvd3 : (P : Subgroup ↥K).index ∣ 3 := by
      refine Nat.Coprime.dvd_of_dvd_mul_right hcop ?_
      rw [← hK]
      exact hdvdK
    have h3dvd_index : 3 ∣ (P : Subgroup ↥K).index := by
      have h3dvd_prod : 3 ∣ Nat.card ↥(P : Subgroup ↥K) * (P : Subgroup ↥K).index := by
        rw [Subgroup.card_mul_index, hK]
        exact dvd_mul_right 3 (2 ^ n)
      have h3_not_P : ¬ 3 ∣ Nat.card ↥(P : Subgroup ↥K) := by
        obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
        rw [hk]
        intro h3
        have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        obtain ⟨c, hc⟩ := h32
        omega
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3dvd_prod with h | h
      · exact absurd h h3_not_P
      · exact h
    exact Nat.dvd_antisymm hdvd3 h3dvd_index
  let α := ↥K ⧸ (P : Subgroup ↥K)
  let φ : ↥K →* Equiv.Perm α := MulAction.toPermHom ↥K α
  have hα_card : Nat.card α = 3 := by
    change Nat.card (↥K ⧸ (P : Subgroup ↥K)) = 3
    rw [← Subgroup.index_eq_card]
    exact hPindex
  have hker_eq : φ.ker = (P : Subgroup ↥K).normalCore :=
    (Subgroup.normalCore_eq_ker (P : Subgroup ↥K)).symm
  have hker_le_P : φ.ker ≤ (P : Subgroup ↥K) := by
    rw [hker_eq]
    exact Subgroup.normalCore_le _
  have hker_le_pcore : φ.ker ≤ CFSG.pCore 2 ↥K := by
    change φ.ker ≤ sSup {J : Subgroup ↥K | J.Normal ∧ IsPGroup 2 J}
    exact le_sSup ⟨φ.normal_ker, P.isPGroup'.to_le hker_le_P⟩
  have hker_mem_pcoreOf : ∀ x : ↥K, x ∈ φ.ker → (x : G) ∈ CFSG.Open.pCoreOf 2 K := by
    intro x hx
    exact Subgroup.mem_map_of_mem K.subtype (hker_le_pcore hx)
  let a : Equiv.Perm α := φ ρK
  let b : Equiv.Perm α := φ lK
  have ha3 : a ^ 3 = 1 := by
    change (φ ρK) ^ 3 = 1
    rw [← map_pow, hρKpow, map_one]
  have ha_ne_one : a ≠ 1 := by
    intro ha
    have hmem : ρK ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact ha
    have hPmem : ρK ∈ (P : Subgroup ↥K) := hker_le_P hmem
    have hord3 : 3 ∣ Nat.card ↥(P : Subgroup ↥K) := by
      rw [← hρK3]
      exact Subgroup.orderOf_dvd_natCard _ hPmem
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk] at hord3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hord3
    obtain ⟨c, hc⟩ := h32
    omega
  have ha_order : orderOf a = 3 := by
    have hdvd : orderOf a ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr ha3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha_ne_one
    · exact h
  have hb2 : b ^ 2 = 1 := by
    change (φ lK) ^ 2 = 1
    rw [← map_pow, hlK2, map_one]
  have hb_conj : b * a * b⁻¹ = a⁻¹ := by
    change φ lK * φ ρK * (φ lK)⁻¹ = (φ ρK)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hlKρK, map_inv]
  have hb_not_mem : b ∉ Subgroup.zpowers a := by
    intro hb
    have hcomm : b ∈ Subgroup.centralizer ({a} : Set (Equiv.Perm α)) := by
      have hle : Subgroup.zpowers a ≤ Subgroup.centralizer ({a} : Set (Equiv.Perm α)) :=
        Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      exact hle hb
    have hba : b * a = a * b := Subgroup.mem_centralizer_singleton_iff.mp hcomm
    have hbconj_a : b * a * b⁻¹ = a := by rw [hba, mul_inv_cancel_right]
    have ha_inv : a = a⁻¹ := by
      calc a = b * a * b⁻¹ := hbconj_a.symm
        _ = a⁻¹ := hb_conj
    have ha2 : a ^ 2 = 1 := by
      have h2 : a * a = 1 := by
        rw [congrArg (fun x => a * x) ha_inv, mul_inv_cancel]
      rwa [pow_two]
    have hdvd2 : orderOf a ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr ha2
    have h32 : 3 ∣ 2 := ha_order ▸ hdvd2
    obtain ⟨c, hc⟩ := h32
    omega
  let H0 : Subgroup (Equiv.Perm α) := Subgroup.closure ({a, b} : Set (Equiv.Perm α))
  have hzple : Subgroup.zpowers a ≤ H0 :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hb_mem_H0 : b ∈ H0 := Subgroup.subset_closure (by simp)
  have hzple_ne : Subgroup.zpowers a ≠ H0 := by
    intro heq
    refine hb_not_mem ?_
    rw [heq]
    exact hb_mem_H0
  have hcard_zp : Nat.card ↥(Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, ha_order]
  have hcard_lt : Nat.card ↥(Subgroup.zpowers a) < Nat.card ↥H0 :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hzple hzple_ne)
  have hcard_perm : Nat.card (Equiv.Perm α) = 6 := by
    rw [Nat.card_perm, hα_card]
    norm_num
  have hcard_dvd : Nat.card ↥H0 ∣ 6 := by
    rw [← hcard_perm]
    exact Subgroup.card_subgroup_dvd_card H0
  have hcard_eq : Nat.card ↥H0 = 6 := by
    have hle : Nat.card ↥H0 ≤ 6 := Nat.le_of_dvd (by norm_num) hcard_dvd
    have hgt : 3 < Nat.card ↥H0 := by rw [← hcard_zp]; exact hcard_lt
    set m := Nat.card ↥H0 with hm
    interval_cases m
    · norm_num at hcard_dvd
    · norm_num at hcard_dvd
    · rfl
  have hH0_top : H0 = ⊤ :=
    Subgroup.eq_top_of_card_eq H0 (by rw [hcard_eq, hcard_perm])
  have hmap_closure : Subgroup.map φ (Subgroup.closure ({ρK, lK} : Set ↥K)) = H0 := by
    unfold H0
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨ρK, Or.inl rfl, rfl⟩
      · exact ⟨lK, Or.inr rfl, rfl⟩
  have hfinal : ∀ g ∈ K, g ∈ CFSG.Open.pCoreOf 2 K ⊔ closure ({ρ, l} : Set G) := by
    intro g hg
    let gK : ↥K := ⟨g, hg⟩
    have hmem_closure : φ gK ∈ H0 := by
      rw [hH0_top]
      exact Subgroup.mem_top _
    have hmem_map : φ gK ∈ Subgroup.map φ (Subgroup.closure ({ρK, lK} : Set ↥K)) := by
      rwa [hmap_closure]
    rw [Subgroup.mem_map] at hmem_map
    obtain ⟨s, hs, hφs⟩ := hmem_map
    have hker : gK * s⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      simp [hφs]
    have hsG : (s : G) ∈ Subgroup.closure ({ρ, l} : Set G) := by
      have hle : Subgroup.closure ({ρK, lK} : Set ↥K) ≤
          (Subgroup.closure ({ρ, l} : Set G)).comap K.subtype := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact Subgroup.mem_comap.mpr (Subgroup.subset_closure (Or.inl rfl))
        · exact Subgroup.mem_comap.mpr (Subgroup.subset_closure (Or.inr rfl))
      exact hle hs
    have hprod : ((gK * s⁻¹ : ↥K) : G) * (s : G) = g := by
      have h1 : (gK * s⁻¹) * s = gK := by group
      change K.subtype (gK * s⁻¹) * K.subtype s = K.subtype gK
      rw [← map_mul, h1]
    rw [← hprod]
    exact Subgroup.mul_mem_sup (hker_mem_pcoreOf _ hker) hsG
  refine le_antisymm hfinal ?_
  refine sup_le (Subgroup.map_subtype_le _) ?_
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact hρ
  · exact hl

theorem c13K_K_eq
    (hc : Ctx13M t L S x₁ x₂ lam rho tau om)
    (hne : ∃ k ∈ ctxK t tau x₁ x₂ rho, k ∉ ctxM t tau x₁ x₂) :
    ctxK t tau x₁ x₂ rho =
      CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) ⊔ closure ({rho, lam} : Set G) := by
  obtain ⟨_, _, _, hrho, hlam⟩ := c13K_mem_M hc
  refine c13K_eq_pCore_sup (K := ctxK t tau x₁ x₂ rho) (n := 12)
    (c13K_card_K hc hne) (hc.M_le_K hrho) (hc.M_le_K hlam) hc.ord_rho ?_ hc.lam_rho
  rw [← hc.wreath.ord_lam]
  exact pow_orderOf_eq_one lam

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
