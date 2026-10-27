module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiU1
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEndingBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

section Coords

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}
  {U U₁ : Subgroup G}

namespace SzRCoords2

theorem eight_le_card (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    8 ≤ Fintype.card K := by
  rw [hK]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem sq_mul_two_lt_pow_four (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    Fintype.card K ^ 2 * 2 < Fintype.card K ^ 4 := by
  have hq := eight_le_card ha hK
  have h3 : 8 * 8 ≤ Fintype.card K ^ 2 := by
    rw [_root_.sq]
    exact Nat.mul_le_mul hq hq
  have h4 : 0 < Fintype.card K ^ 2 := by positivity
  calc Fintype.card K ^ 2 * 2 < Fintype.card K ^ 2 * Fintype.card K ^ 2 :=
        Nat.mul_lt_mul_of_pos_left (by omega) h4
    _ = Fintype.card K ^ 4 := by ring

theorem conj_t_not_mem_U₁ (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hγ : γ = 0)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) (g : G) :
    g⁻¹ * t * g ∉ U₁ := by
  intro hxU₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hcardU₁⟩ := h.u1_structure hS hc ha hK hκ hγ hU hc0
  have hconj := h.conj_R₂_eq_of_sq_eq_one hS hc ha hK hκ hγ hU hc0
  have hTt : T₁ ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_zpowers_le_centralizer_singleton (mem_centralizer_iff.mpr hS.t_comm)
  have hTc : Nat.card (T₁ ⊔ zpowers t : Subgroup G) =
      2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 := by
    rw [h.card_sup_zpowers hS, two_pow_factorization_card_centralizer hCt, mul_comm]
  have hTtcard : Nat.card (T₁ ⊔ zpowers t : Subgroup G) = Fintype.card K ^ 2 * 2 := by
    rw [h.card_sup_zpowers hS, hc.card_eq, Nat.card_eq_fintype_card, _root_.sq]
  have hU₁p : IsPGroup 2 U₁ :=
    IsPGroup.of_card (n := 4 * (2 * a + 1)) (by rw [hcardU₁, hK]; ring)
  have hcommx : ∀ y ∈ U₁, ∀ r ∈ R₂, y * r = r * y := fun y hy r hr => by
    calc y * r = y * r * y⁻¹ * y := by group
      _ = r * y := by rw [hconj y hy r hr]
  have hR₂U₁ : R₂ ≤ U₁ := le_sup_right.trans (sup_le_U₁ hU)
  by_cases hxR : g⁻¹ * t * g ∈ R₂
  ·
    have hP : U₁ ≤ centralizer ({g⁻¹ * t * g} : Set G) := fun y hy =>
      mem_centralizer_singleton_iff.mpr (hcommx y hy _ hxR)
    have hle : Nat.card (T₁ ⊔ zpowers t : Subgroup G) ≤ Nat.card U₁ := by
      rw [hTtcard, hcardU₁]
      exact (sq_mul_two_lt_pow_four (K := K) ha hK).le
    obtain ⟨k, -, hk⟩ := exists_conj_eq_of_card_le hTt hTc hP hU₁p hle
    have hmap : U₁.map (MulAut.conj k).toMonoidHom = T₁ ⊔ zpowers t := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hk z).mp hz
      · intro hy
        refine ⟨k⁻¹ * y * k, (hk _).mpr (by simpa [mul_assoc] using hy), ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    have h1 : Nat.card (U₁.map (MulAut.conj k).toMonoidHom) = Nat.card U₁ :=
      card_map_of_injective (MulAut.conj k).injective
    rw [hmap, hTtcard, hcardU₁] at h1
    exact absurd h1 (sq_mul_two_lt_pow_four (K := K) ha hK).ne
  ·
    set x := g⁻¹ * t * g with hxdef
    have hxx : x * x = 1 := by
      rw [hxdef, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ← _root_.sq,
        hS.t_sq]
      group
    have hxN : x ∈ normalizer (R₂ : Set G) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr => (hcommx x hxU₁ r hr).symm)
    have hidx := relIndex_sup_zpowers_eq_two_of_mul_self_mem hxR hxN (by rw [hxx]; exact one_mem _)
    have hPcard : Nat.card (R₂ ⊔ zpowers x : Subgroup G) = Fintype.card K ^ 2 * 2 := by
      have h1 := Subgroup.relIndex_mul_card R₂ (R₂ ⊔ zpowers x)
      rw [inf_eq_left.mpr le_sup_left, hidx, h.card_R₂ hS, hc.card_szA₁ ha hK,
        Nat.card_eq_fintype_card] at h1
      rw [← h1]
      ring
    have hPU₁ : R₂ ⊔ zpowers x ≤ U₁ := sup_le hR₂U₁ (zpowers_le.mpr hxU₁)
    have hP : R₂ ⊔ zpowers x ≤ centralizer ({x} : Set G) :=
      sup_le (fun r hr => mem_centralizer_singleton_iff.mpr (hcommx x hxU₁ r hr).symm)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    have hPab : R₂ ⊔ zpowers x ≤ centralizer ((R₂ ⊔ zpowers x : Subgroup G) : Set G) := by
      refine sup_le (fun r hr => mem_centralizer_iff.mpr fun p hp => ?_)
        (zpowers_le.mpr (mem_centralizer_iff.mpr fun p hp => mem_centralizer_singleton_iff.mp
          (hP hp)))
      have hle : R₂ ⊔ zpowers x ≤ centralizer ({r} : Set G) :=
        sup_le (fun r' hr' => mem_centralizer_singleton_iff.mpr (hS.R₂_comm r' hr' r hr))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcommx x hxU₁ r hr)))
      exact mem_centralizer_singleton_iff.mp (hle hp)
    obtain ⟨k, -, hk⟩ := exists_conj_eq_of_card_le hTt hTc hP (hU₁p.to_le hPU₁)
      (by rw [hTtcard, hPcard])
    obtain ⟨y, hy, y', hy', hne⟩ := hc.exists_not_commute ha hK
    have hmem : ∀ z ∈ T₁, k⁻¹ * z * k ∈ R₂ ⊔ zpowers x := fun z hz =>
      (hk _).mpr (by simpa [mul_assoc] using mem_sup_left hz)
    have h1 := mem_centralizer_iff.mp (hPab (hmem y hy)) _ (hmem y' hy')
    apply hne
    calc y * y' = k * ((k⁻¹ * y * k) * (k⁻¹ * y' * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y' * k) * (k⁻¹ * y * k)) * k⁻¹ := by rw [h1]
      _ = y' * y := by group

theorem exists_conj_eq_of_mem_mul_t (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hγ : γ = 0)
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) {x : G}
    (hx : x ∈ U₁) (hxt : x * t * (x * t) = 1) : ∃ w ∈ U₁, w * t * w⁻¹ = x * t := by
  have hinv := h.exists_not_inverts_of_sq_eq_one hS hc0
  obtain ⟨hcomm, hsq, -, -⟩ := h.u1_structure hS hc ha hK hκ hγ hU hc0
  have htt : t * t = 1 := by rw [← _root_.sq]; exact hS.t_sq
  refine conj_of_free_series htt hS.t_mem_normalizer_R₂ (le_sup_right.trans (sup_le_U₁ hU))
    (fun r hr => by rw [← _root_.sq]; exact hc0 r hr) hcomm
    (fun y hy => by rw [← _root_.sq]; exact hsq y hy) (fun r hr htr => ?_) (fun y hy hty => ?_)
    hx hxt
  ·
    have hrt : r * t * r⁻¹ * t⁻¹ = 1 := by
      have e : r * t = t * r := by
        calc r * t = t * r * t⁻¹ * t := by rw [htr]
          _ = t * r := by group
      rw [e]
      group
    exact hS.rho_surj r (hS.rho_ker r hr hrt)
  ·
    have hyU := hU.U₁_le hy
    have h1 : y * t * y⁻¹ * t⁻¹ ∈ R₂ := by
      have e : y * t * y⁻¹ * t⁻¹ = (t * y * t⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hty
    have hyH : y ∈ T₁ ⊔ R₂ :=
      h.mem_sup_of_szLam_eq_zero hS hc ha hK hU hinv hy (by simp only [szLam]; rw [h.of_R₂ _ h1])
    obtain ⟨w, hw, hwl⟩ := h.szLam_surj hS hc ha hK hκ hU hinv (φ y).1
    refine ⟨w, hw, ?_⟩
    have h2 := (h.layerOne_heq hS hc ha hK _ (comm_t_mem hU (hU.U₁_le hw)) y hyH).mp hwl
    exact h2

theorem isSylowOf_top_U (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hγ : γ = 0)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) :
    IsSylowOf 2 U ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 U :=
    IsPGroup.of_card (n := 1 + 4 * (2 * a + 1)) (by rw [hU.card, hK]; ring)
  by_contra hnot
  obtain ⟨S, hUS, z, hzS, hzN, hzU⟩ := GMS28.exists_mem_normalizer_of_not_isSylowOf hUp hnot
  have htU : t ∈ U := hU.szR_le (mem_szR_right T₁ R₂ t)
  have htt : t * t = 1 := by rw [← _root_.sq]; exact hS.t_sq
  have hy : z * t * z⁻¹ ∈ U := (mem_normalizer_iff.mp hzN t).mp htU
  have hyU₁ : z * t * z⁻¹ ∉ U₁ := by
    have h1 := h.conj_t_not_mem_U₁ hS hc ha hK hκ hγ hCt hU hc0 z⁻¹
    rwa [inv_inv] at h1
  rw [← hU.sup_eq] at hy
  obtain ⟨x, hx, hxy | hxy⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt
    (zpowers_le.mpr (hU.le_normalizer_U₁ htU)) hy
  · exact hyU₁ (hxy ▸ hx)
  have hinv2 : x * t * (x * t) = 1 := by
    rw [hxy]
    calc z * t * z⁻¹ * (z * t * z⁻¹) = z * (t * t) * z⁻¹ := by group
      _ = 1 := by rw [htt]; group
  obtain ⟨w, hw, hwt⟩ := h.exists_conj_eq_of_mem_mul_t hS hc ha hK hκ hγ hU hc0 hx hinv2
  have he : w⁻¹ * z ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : z * t * z⁻¹ = w * t * w⁻¹ := by rw [hwt, hxy]
    calc w⁻¹ * z * t = w⁻¹ * (z * t * z⁻¹) * z := by group
      _ = w⁻¹ * (w * t * w⁻¹) * z := by rw [h1]
      _ = t * (w⁻¹ * z) := by group
  have heS : w⁻¹ * z ∈ (S : Subgroup G) := mul_mem (inv_mem (hUS (hU.U₁_le hw))) hzS
  have hTt : T₁ ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_zpowers_le_centralizer_singleton (mem_centralizer_iff.mpr hS.t_comm)
  have hTc : Nat.card (T₁ ⊔ zpowers t : Subgroup G) =
      2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 := by
    rw [h.card_sup_zpowers hS, two_pow_factorization_card_centralizer hCt, mul_comm]
  have hTtU : T₁ ⊔ zpowers t ≤ U :=
    sup_le ((le_szR_left T₁ R₂ t).trans hU.szR_le) (zpowers_le.mpr htU)
  have hQS : (T₁ ⊔ zpowers t) ⊔ zpowers (w⁻¹ * z) ≤ S :=
    sup_le (hTtU.trans hUS) (zpowers_le.mpr heS)
  have hQC : (T₁ ⊔ zpowers t) ⊔ zpowers (w⁻¹ * z) ≤ centralizer ({t} : Set G) :=
    sup_le hTt (zpowers_le.mpr he)
  have h1 := card_le_of_isPGroup_of_le (S.isPGroup'.to_le hQS) hQC
  rw [← hTc] at h1
  have hQeq := Subgroup.eq_of_le_of_card_ge (le_sup_left : T₁ ⊔ zpowers t ≤ _) h1
  have heT : w⁻¹ * z ∈ T₁ ⊔ zpowers t := hQeq ▸ mem_sup_right (mem_zpowers _)
  apply hzU
  have e : z = w * (w⁻¹ * z) := by group
  rw [e]
  exact mul_mem (hU.U₁_le hw) (hTtU heT)

theorem false_of_c0 (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hγ : γ = 0) (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hUp, hUidx⟩ := isSylowOf_iff.mp (h.isSylowOf_top_U hS hc ha hK hκ hγ hCt hU hc0)
  rw [relIndex_top_right] at hUidx
  have htU : t ∈ U := hU.szR_le (mem_szR_right T₁ R₂ t)
  have htt : t * t = 1 := by rw [← _root_.sq]; exact hS.t_sq
  have hidx : U₁.relIndex U = 2 := by
    rw [← hU.sup_eq]
    exact Endings.relIndex_sup_zpowers_eq_two hU.t_not_mem (hU.le_normalizer_U₁ htU) htt
  exact hG (CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hUp hUidx hU.U₁_le hidx htU
    hU.t_not_mem (fun y _ hyU => Endings.orderOf_le_of_ne_one htt fun hy1 => hyU (hy1 ▸ one_mem _))
    (h.conj_t_not_mem_U₁ hS hc ha hK hκ hγ hCt hU hc0))

end SzRCoords2

end Coords

section Start

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Fintype K] [CharP K 2]
  {R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {U U₁ : Subgroup G}

namespace SzStart

variable {L : Subgroup G} {f : ℕ} {T : Subgroup G}

theorem false_of_c0_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d) (hU : SzU (szT₁ L T) R₂ t d (2 ^ f) U U₁)
    (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) : False := by
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hKn : Nat.card K = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card, hKa]
  have hμ := pow_theta_succ_generator_of_generator ha hKn hκ
  obtain ⟨φ, γ, c, hφ⟩ := hR.exists_coords hc ha hKa hμ
  have hCt := h.card_sylow_centralizer_of_card_sylow hS2 hc hK
  have hγ := hφ.gamma_eq_zero h.not_exists_normal_index_two hR hc ha hKa hμ hCt
  rw [← hK] at hU
  exact hφ.false_of_c0 h.not_exists_normal_index_two hR hc ha hKa hκ hγ hCt hU hc0

end SzStart

end Start

end CFSG.SeitzReduction.RankOne
