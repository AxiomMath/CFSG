module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiU1Coords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiTwist
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiU1Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

section Coords

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}
  {U U₁ : Subgroup G}

namespace SzRCoords2

theorem comm_mem_R₂_of_not_inverts (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁)
    (hinv : ∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹) : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ R₂ := by
  have hU₁U := hU.U₁_le
  have hmemH : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ T₁ ⊔ R₂ := fun x hx y hy =>
    hU.comm_mem x (hU₁U hx) y (hU₁U hy)
  have hl : ∀ x ∈ U₁, ∀ x' ∈ U₁, szLam φ t (x * x') = szLam φ t x + szLam φ t x' :=
    fun x hx x' hx' => h.szLam_mul hS hc ha hK hU (hU₁U hx) (hU₁U hx')
  have hls := h.szLam_surj hS hc ha hK hκ hU hinv
  have hP1 : ∀ x ∈ U₁, ∀ x' ∈ U₁, ∀ y ∈ U₁, (φ (x * x' * y * (x * x')⁻¹ * y⁻¹)).1 =
      (φ (x * y * x⁻¹ * y⁻¹)).1 + (φ (x' * y * x'⁻¹ * y⁻¹)).1 := by
    intro x hx x' hx' y hy
    obtain ⟨hm1, he1⟩ := fst_conj_eq hS h hc ha hK hU (hU₁U hx) (hmemH x' hx' y hy)
    have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
        (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e, h.mul _ (sup_le_szR T₁ R₂ t hm1) _ (sup_le_szR T₁ R₂ t (hmemH x hx y hy)),
      Prod.fst_add, he1, add_comm]
  have hP2 : ∀ x ∈ U₁, ∀ y ∈ U₁, ∀ y' ∈ U₁, (φ (x * (y * y') * x⁻¹ * (y * y')⁻¹)).1 =
      (φ (x * y * x⁻¹ * y⁻¹)).1 + (φ (x * y' * x⁻¹ * y'⁻¹)).1 := by
    intro x hx y hy y' hy'
    obtain ⟨hm1, he1⟩ := fst_conj_eq hS h hc ha hK hU (hU₁U hy) (hmemH x hx y' hy')
    have e : x * (y * y') * x⁻¹ * (y * y')⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by group
    rw [e, h.mul _ (sup_le_szR T₁ R₂ t (hmemH x hx y hy)) _ (sup_le_szR T₁ R₂ t hm1),
      Prod.fst_add, he1]
  have hPl : ∀ x ∈ U₁, szLam φ t x = 0 → ∀ y ∈ U₁, (φ (x * y * x⁻¹ * y⁻¹)).1 = 0 := by
    intro x hx h0 y hy
    have hxH := h.mem_sup_of_szLam_eq_zero hS hc ha hK hU hinv hx h0
    rw [h.of_R₂ _ (comm_mem_R₂_of_mem_sup hS hU hxH (hU₁U hy))]
  have hPr : ∀ y ∈ U₁, szLam φ t y = 0 → ∀ x ∈ U₁, (φ (x * y * x⁻¹ * y⁻¹)).1 = 0 := by
    intro y hy h0 x hx
    have hyH := h.mem_sup_of_szLam_eq_zero hS hc ha hK hU hinv hy h0
    rw [h.of_R₂ _ (comm_mem_R₂_of_mem_sup' hS hU (hU₁U hx) hyH)]
  obtain ⟨B, hB1, hB2, hB⟩ := exists_biadditive_of_descends (X := U₁) (Y := U₁)
    (P := fun x y => (φ (x * y * x⁻¹ * y⁻¹)).1) hl hls hl hls hP1 hP2 hPl hPr
  have hB' : ∀ x ∈ U₁, ∀ y ∈ U₁,
      (φ (x * y * x⁻¹ * y⁻¹)).1 = B (szLam φ t x) (szLam φ t y) := hB
  have halt : ∀ w, B w w = 0 := by
    intro w
    obtain ⟨x, hx, rfl⟩ := hls w
    rw [← hB' x hx x hx, mul_inv_cancel_right, mul_inv_cancel, h.map_one]
    rfl
  have hBeq : ∀ w z, B (κ * w) (κ * z) = κ * B w z := by
    intro w z
    obtain ⟨x, hx, rfl⟩ := hls w
    obtain ⟨y, hy, rfl⟩ := hls z
    rw [← h.szLam_conj_d hS hc ha hK hU (hU₁U hx), ← h.szLam_conj_d hS hc ha hK hU (hU₁U hy),
      ← hB' _ (conj_d_mem_U₁ hU hx) _ (conj_d_mem_U₁ hU hy), ← hB' x hx y hy]
    have e : d⁻¹ * x * d * (d⁻¹ * y * d) * (d⁻¹ * x * d)⁻¹ * (d⁻¹ * y * d)⁻¹ =
        d⁻¹ * (x * y * x⁻¹ * y⁻¹) * d := by group
    rw [e, h.map_conj_d hS hc ha hK (sup_le_szR T₁ R₂ t (hmemH x hx y hy))]
    rfl
  intro x hx y hy
  refine (h.fst_eq_zero_iff hS hc ha hK (hmemH x hx y hy)).mp ?_
  rw [hB' x hx y hy]
  exact bilinear_eq_zero_of_alternating_equivariant' hK B hB1 hB2 hκ hBeq halt _ _

theorem sup_le_centralizer_R₂ (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hγ : γ = 0) : T₁ ⊔ R₂ ≤ centralizer (R₂ : Set G) := by
  have hcommT := h.commute_of_gamma_eq_zero hγ
  exact sup_le (fun y hy => mem_centralizer_iff.mpr fun r hr => (hcommT y hy r hr).symm)
    (fun y hy => mem_centralizer_iff.mpr fun r hr => hS.R₂_comm r hr y hy)

theorem sq_mem_R₂_of_sq_eq_one (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hγ : γ = 0)
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) :
    ∀ x ∈ U₁, x ^ 2 ∈ R₂ := by
  have hinv := h.exists_not_inverts_of_sq_eq_one hS hc0
  have hU₁U := hU.U₁_le
  have hcomm := h.comm_mem_R₂_of_not_inverts hS hc ha hK hκ hU hinv
  have hl : ∀ x ∈ U₁, ∀ x' ∈ U₁, szLam φ t (x * x') = szLam φ t x + szLam φ t x' :=
    fun x hx x' hx' => h.szLam_mul hS hc ha hK hU (hU₁U hx) (hU₁U hx')
  have hls := h.szLam_surj hS hc ha hK hκ hU hinv
  have hsqH : ∀ x ∈ U₁, x ^ 2 ∈ T₁ ⊔ R₂ := fun x hx => hU.sq_mem x (hU₁U hx)
  have hF : ∀ x ∈ U₁, ∀ x' ∈ U₁, (φ ((x * x') ^ 2)).1 = (φ (x ^ 2)).1 + (φ (x' ^ 2)).1 := by
    intro x hx x' hx'
    have hm := hcomm _ (inv_mem hx) _ hx'
    have e : (x * x') ^ 2 = x ^ 2 * (x⁻¹ * x' * x⁻¹⁻¹ * x'⁻¹) * x' ^ 2 := by
      simp only [_root_.sq]; group
    have hm1 := sup_le_szR T₁ R₂ t (hsqH x hx)
    have hm2 := le_szR_mid T₁ R₂ t hm
    have hm3 := sup_le_szR T₁ R₂ t (hsqH x' hx')
    rw [e, h.mul _ (mul_mem hm1 hm2) _ hm3, h.mul _ hm1 _ hm2, h.of_R₂ _ hm]
    simp
  have hF0 : ∀ x ∈ U₁, szLam φ t x = 0 → (φ (x ^ 2)).1 = 0 := by
    intro x hx h0
    have hxR := sup_le_szR T₁ R₂ t (h.mem_sup_of_szLam_eq_zero hS hc ha hK hU hinv hx h0)
    rw [(h.ker _ (pow_mem hxR 2)).mpr (h.sq_mem x hxR)]
    rfl
  obtain ⟨Sq, hSqadd, hSq⟩ := exists_additive_of_descends (X := U₁)
    (F := fun x => (φ (x ^ 2)).1) hl hls hF hF0
  have hSq' : ∀ x ∈ U₁, (φ (x ^ 2)).1 = Sq (szLam φ t x) := hSq
  have hSqeq : ∀ w, Sq (κ * w) = κ * Sq w := by
    intro w
    obtain ⟨x, hx, rfl⟩ := hls w
    rw [← h.szLam_conj_d hS hc ha hK hU (hU₁U hx), ← hSq' _ (conj_d_mem_U₁ hU hx), ← hSq' x hx]
    have e : (d⁻¹ * x * d) ^ 2 = d⁻¹ * x ^ 2 * d := by simp only [_root_.sq]; group
    rw [e, h.map_conj_d hS hc ha hK (sup_le_szR T₁ R₂ t (hsqH x hx))]
    rfl
  have hSq0 : Sq 0 = 0 := by
    have h1 := hSqadd 0 0
    rw [add_zero] at h1
    exact add_eq_left.mp h1.symm
  have hlin := SzCoords.linear_of_equivariant hSqeq hSq0 hκ
  by_cases hf : Sq 1 = 0
  · intro x hx
    refine (h.fst_eq_zero_iff hS hc ha hK (hsqH x hx)).mp ?_
    rw [hSq' x hx, hlin, hf, zero_mul]
  exfalso
  have hsq : ∀ y ∈ T₁, ∃ x ∈ U₁, ∃ r ∈ R₂, y = x ^ 2 * r := by
    intro y hy
    obtain ⟨x, hx, hxw⟩ := hls ((φ y).1 / Sq 1)
    have h1 : (φ y).1 = (φ (x ^ 2)).1 := by
      rw [hSq' x hx, hxw, hlin ((φ y).1 / Sq 1), mul_comm, div_mul_cancel₀ _ hf]
    have h2 := (h.layerOne_heq hS hc ha hK y (mem_sup_left hy) _ (hsqH x hx)).mp h1
    refine ⟨x, hx, (x ^ 2)⁻¹ * y, ?_, by group⟩
    have h3 := inv_mem h2
    rwa [mul_inv_rev, inv_inv] at h3
  have hsqc : ∀ x ∈ U₁, ∀ x' ∈ U₁, x ^ 2 * x' ^ 2 = x' ^ 2 * x ^ 2 := fun x hx x' hx' =>
    sq_mul_sq_comm (M := U₁) (N := R₂) (A := szA₁ T₁) hcomm hc0
      (fun m hm n hn => hU.conj_R₂ m (hU₁U hm) n hn)
      (fun m hm b hb => hU.conj_szA₁ m (hU₁U hm) b hb)
      (fun b hb => hc.sq_eq_one_of_mem_szA₁ ha hK hb) hx hx'
  have hcentral : ∀ r ∈ R₂, ∀ z ∈ T₁ ⊔ R₂, r * z = z * r := fun r hr z hz =>
    mem_centralizer_iff.mp (h.sup_le_centralizer_R₂ hS hγ hz) r hr
  obtain ⟨y, hy, y', hy', hne⟩ := hc.exists_not_commute ha hK
  apply hne
  obtain ⟨x, hx, r, hr, rfl⟩ := hsq y hy
  obtain ⟨x', hx', r', hr', rfl⟩ := hsq y' hy'
  have h1 : r * x' ^ 2 = x' ^ 2 * r := hcentral r hr _ (hsqH x' hx')
  have h2 : r' * x ^ 2 = x ^ 2 * r' := hcentral r' hr' _ (hsqH x hx)
  have h3 : r * r' = r' * r := hS.R₂_comm r hr r' hr'
  have h4 := hsqc x hx x' hx'
  generalize x ^ 2 = X at h1 h2 h4 ⊢
  generalize x' ^ 2 = X' at h1 h2 h4 ⊢
  calc X * r * (X' * r') = X * (r * X') * r' := by group
    _ = X * (X' * r) * r' := by rw [h1]
    _ = X * X' * (r * r') := by group
    _ = X' * X * (r' * r) := by rw [h4, h3]
    _ = X' * (X * r') * r := by group
    _ = X' * (r' * X) * r := by rw [h2]
    _ = X' * r' * (X * r) := by group

theorem conj_R₂_eq_of_sq_eq_one (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hγ : γ = 0)
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) :
    ∀ x ∈ U₁, ∀ r ∈ R₂, x * r * x⁻¹ = r := by
  have hinv := h.exists_not_inverts_of_sq_eq_one hS hc0
  have hU₁U := hU.U₁_le
  have hcommT := h.commute_of_gamma_eq_zero hγ
  have hl : ∀ x ∈ U₁, ∀ x' ∈ U₁, szLam φ t (x * x') = szLam φ t x + szLam φ t x' :=
    fun x hx x' hx' => h.szLam_mul hS hc ha hK hU (hU₁U hx) (hU₁U hx')
  have hls := h.szLam_surj hS hc ha hK hκ hU hinv
  have hρ : ∀ r ∈ R₂, ∀ r' ∈ R₂, (φ (r * r')).2.1 = (φ r).2.1 + (φ r').2.1 := by
    intro r hr r' hr'
    rw [h.mul _ (le_szR_mid T₁ R₂ t hr) _ (le_szR_mid T₁ R₂ t hr')]
    rfl
  have hχ : ∀ x ∈ U₁, ∀ r ∈ R₂, r⁻¹ * (x * r * x⁻¹) ∈ szA₁ T₁ := fun x hx r hr =>
    hU.conj_R₂ x (hU₁U hx) r hr
  have hP1 : ∀ x ∈ U₁, ∀ x' ∈ U₁, ∀ r ∈ R₂, v (r⁻¹ * (x * x' * r * (x * x')⁻¹)) =
      v (r⁻¹ * (x * r * x⁻¹)) + v (r⁻¹ * (x' * r * x'⁻¹)) := by
    intro x hx x' hx' r hr
    have e : r⁻¹ * (x * x' * r * (x * x')⁻¹) =
        (r⁻¹ * (x * r * x⁻¹)) * (x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹) := by group
    rw [e, hU.conj_szA₁ x (hU₁U hx) _ (hχ x' hx' r hr),
      h.v_mul _ (hχ x hx r hr) _ (hχ x' hx' r hr)]
  have hP2 : ∀ x ∈ U₁, ∀ r ∈ R₂, ∀ r' ∈ R₂, v ((r * r')⁻¹ * (x * (r * r') * x⁻¹)) =
      v (r⁻¹ * (x * r * x⁻¹)) + v (r'⁻¹ * (x * r' * x⁻¹)) := by
    intro x hx r hr r' hr'
    have hcm : r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * r' = r⁻¹ * (x * r * x⁻¹) := by
      have h1 := hS.R₂_comm _ (hS.le_R₂ (hχ x hx r hr)) r' hr'
      calc r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * r' = r'⁻¹ * ((r⁻¹ * (x * r * x⁻¹)) * r') :=
            mul_assoc _ _ _
        _ = r'⁻¹ * (r' * (r⁻¹ * (x * r * x⁻¹))) := by rw [h1]
        _ = r⁻¹ * (x * r * x⁻¹) := inv_mul_cancel_left _ _
    have e : (r * r')⁻¹ * (x * (r * r') * x⁻¹) =
        (r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * r') * (r'⁻¹ * (x * r' * x⁻¹)) := by group
    rw [e, hcm, h.v_mul _ (hχ x hx r hr) _ (hχ x hx r' hr')]
  have hPl : ∀ x ∈ U₁, szLam φ t x = 0 → ∀ r ∈ R₂, v (r⁻¹ * (x * r * x⁻¹)) = 0 := by
    intro x hx h0 r hr
    have hxH := h.mem_sup_of_szLam_eq_zero hS hc ha hK hU hinv hx h0
    have hrx : r * x = x * r := mem_centralizer_iff.mp (h.sup_le_centralizer_R₂ hS hγ hxH) r hr
    rw [← hrx, mul_inv_cancel_right, inv_mul_cancel, h.v_one]
  have hPr : ∀ r ∈ R₂, (φ r).2.1 = 0 → ∀ x ∈ U₁, v (r⁻¹ * (x * r * x⁻¹)) = 0 := by
    intro r hr h0 x hx
    rw [hU.conj_szA₁ x (hU₁U hx) r ((h.snd_eq_zero_iff hr).mp h0), inv_mul_cancel, h.v_one]
  obtain ⟨B, hB1, hB2, hB⟩ := exists_biadditive_of_descends (X := U₁) (Y := R₂)
    (r := fun r => (φ r).2.1) (P := fun x r => v (r⁻¹ * (x * r * x⁻¹))) hl hls hρ
    (h.layerTwo_surj hS) hP1 hP2 hPl hPr
  have hB' : ∀ x ∈ U₁, ∀ r ∈ R₂, v (r⁻¹ * (x * r * x⁻¹)) = B (szLam φ t x) (φ r).2.1 := hB
  have hBeq : ∀ w z, B (κ * w) (κ ^ (2 ^ (a + 1) + 1) * z) = κ ^ (2 ^ (a + 1) + 1) * B w z := by
    intro w z
    obtain ⟨x, hx, rfl⟩ := hls w
    obtain ⟨r, hr, rfl⟩ := h.layerTwo_surj hS z
    have hρd : (φ (d⁻¹ * r * d)).2.1 = κ ^ (2 ^ (a + 1) + 1) * (φ r).2.1 := by
      rw [h.map_conj_d hS hc ha hK (le_szR_mid T₁ R₂ t hr)]
      rfl
    rw [← h.szLam_conj_d hS hc ha hK hU (hU₁U hx), ← hρd,
      ← hB' _ (conj_d_mem_U₁ hU hx) _ (hS.conj_d_mem hr), ← hB' x hx r hr]
    have e : (d⁻¹ * r * d)⁻¹ * (d⁻¹ * x * d * (d⁻¹ * r * d) * (d⁻¹ * x * d)⁻¹) =
        d⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * d := by group
    rw [e, hc.v_conj_szA₁ ha hK (hχ x hx r hr)]
  obtain ⟨c', hc'⟩ := SzCoords.bilinear_of_equivariant' ha hK B hB1 hB2 hκ hBeq
  have hsqU := h.sq_mem_R₂_of_sq_eq_one hS hc ha hK hκ hγ hU hc0
  obtain ⟨x₀, hx₀, hx₀R⟩ := h.exists_mem_U₁_not_mem hc ha hK hU
  obtain ⟨t₂, ht₂, hDR₂, hDA⟩ := h.exists_mem_T₁_conj_not_mem hS hc ha hK hγ hU hinv
    (inv_mem (hU₁U hx₀)) (fun hR => hx₀R (by simpa using inv_mem hR))
  rw [inv_inv] at hDR₂ hDA
  generalize hD : t₂⁻¹ * (x₀ * t₂ * x₀⁻¹) = D at hDR₂ hDA
  have hDD : D⁻¹ = D := inv_eq_of_mul_eq_one_right (by rw [← _root_.sq]; exact hc0 D hDR₂)
  have hfix : x₀ * D * x₀⁻¹ = D := by
    have h2 : x₀ ^ 2 * t₂ = t₂ * x₀ ^ 2 := (hcommT t₂ ht₂ _ (hsqU x₀ hx₀)).symm
    have e1 : x₀ * t₂ * x₀⁻¹ = t₂ * D := by rw [← hD]; group
    have e2 : t₂ * D * (x₀ * D * x₀⁻¹) = t₂ := by
      calc t₂ * D * (x₀ * D * x₀⁻¹) = (x₀ * t₂ * x₀⁻¹) * (x₀ * D * x₀⁻¹) := by rw [e1]
        _ = x₀ * (t₂ * D) * x₀⁻¹ := by group
        _ = x₀ * (x₀ * t₂ * x₀⁻¹) * x₀⁻¹ := by rw [e1]
        _ = x₀ ^ 2 * t₂ * (x₀ ^ 2)⁻¹ := by simp only [_root_.sq]; group
        _ = t₂ := by rw [h2, mul_inv_cancel_right]
    have e3 : D * (x₀ * D * x₀⁻¹) = 1 := by
      calc D * (x₀ * D * x₀⁻¹) = t₂⁻¹ * (t₂ * D * (x₀ * D * x₀⁻¹)) := by group
        _ = 1 := by rw [e2, inv_mul_cancel]
    rw [eq_inv_of_mul_eq_one_right e3, hDD]
  have hP0 : v (D⁻¹ * (x₀ * D * x₀⁻¹)) = 0 := by rw [hfix, inv_mul_cancel, h.v_one]
  have hl0 : szLam φ t x₀ ≠ 0 := fun h0 =>
    hx₀R (sup_le_szR T₁ R₂ t (h.mem_sup_of_szLam_eq_zero hS hc ha hK hU hinv hx₀ h0))
  have hρ0 : (φ D).2.1 ≠ 0 := fun h0 => hDA ((h.snd_eq_zero_iff hDR₂).mp h0)
  have hc'0 : c' = 0 := by
    rw [hB' x₀ hx₀ D hDR₂, hc'] at hP0
    exact (mul_eq_zero.mp hP0).resolve_right (pow_ne_zero _ (mul_ne_zero hl0 hρ0))
  intro x hx r hr
  have h1 : v (r⁻¹ * (x * r * x⁻¹)) = 0 := by rw [hB' x hx r hr, hc', hc'0, zero_mul]
  exact (inv_mul_eq_one.mp (h.v_inj _ (hχ x hx r hr) h1)).symm

theorem inf_centralizer_U₁_eq_of_sq_eq_one (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hγ : γ = 0) (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) :
    U₁ ⊓ centralizer (U₁ : Set G) = R₂ := by
  have hinv := h.exists_not_inverts_of_sq_eq_one hS hc0
  have hHU₁ := sup_le_U₁ hU
  have hconj := h.conj_R₂_eq_of_sq_eq_one hS hc ha hK hκ hγ hU hc0
  apply le_antisymm
  · intro z hz
    obtain ⟨hzU₁, hzC⟩ := mem_inf.mp hz
    by_cases hzR : z ∈ szR T₁ R₂ t
    · have hzH : z ∈ T₁ ⊔ R₂ := by
        rw [← hU.inf_eq]
        exact mem_inf.mpr ⟨hzU₁, hzR⟩
      rw [← hS.inf_centralizer_sup_eq (h.commute_of_gamma_eq_zero hγ)]
      exact mem_inf.mpr ⟨hzH, centralizer_le (SetLike.coe_subset_coe.mpr hHU₁) hzC⟩
    · exfalso
      obtain ⟨t₂, ht₂, -, hDA⟩ := h.exists_mem_T₁_conj_not_mem hS hc ha hK hγ hU hinv
        (hU.U₁_le hzU₁) hzR
      apply hDA
      have hc2 : t₂ * z = z * t₂ := mem_centralizer_iff.mp hzC t₂ (hHU₁ (mem_sup_left ht₂))
      have h1 : z⁻¹ * t₂ * z = t₂ := by rw [mul_assoc, hc2, inv_mul_cancel_left]
      rw [h1, inv_mul_cancel]
      exact one_mem _
  · intro r hr
    refine mem_inf.mpr ⟨hHU₁ (mem_sup_right hr), mem_centralizer_iff.mpr fun x hx => ?_⟩
    have h1 := hconj x hx r hr
    calc x * r = x * r * x⁻¹ * x := by group
      _ = r * x := by rw [h1]

theorem u1_structure (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hγ : γ = 0)
    (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) (hc0 : ∀ r ∈ R₂, r ^ 2 = 1) :
    (∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ R₂) ∧ (∀ x ∈ U₁, x ^ 2 ∈ R₂) ∧
      U₁ ⊓ centralizer (U₁ : Set G) = R₂ ∧ Nat.card U₁ = Fintype.card K ^ 4 :=
  ⟨h.comm_mem_R₂_of_not_inverts hS hc ha hK hκ hU (h.exists_not_inverts_of_sq_eq_one hS hc0),
    h.sq_mem_R₂_of_sq_eq_one hS hc ha hK hκ hγ hU hc0,
    h.inf_centralizer_U₁_eq_of_sq_eq_one hS hc ha hK hκ hγ hU hc0, hU.card_U₁⟩

end SzRCoords2

end Coords

end CFSG.SeitzReduction.RankOne
