module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUKernel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUOne
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLemmaS

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open scoped Pointwise

structure SzU {G : Type*} [Group G] (T₁ R₂ : Subgroup G) (t d : G) (q : ℕ) (U U₁ : Subgroup G) :
    Prop where
  le_normalizer : U ≤ normalizer (szR T₁ R₂ t : Set G)
  normalizer_le : normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (U : Set G)
  isSylowOf : IsSylowOf 2 U (normalizer (szR T₁ R₂ t : Set G))
  card : Nat.card U = 2 * q ^ 4
  szR_le : szR T₁ R₂ t ≤ U
  ker : ∀ u ∈ U, (∀ S ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t),
    S.map (MulAut.conj u).toMonoidHom = S) → u ∈ szR T₁ R₂ t
  conj_t_not_mem_szA : ∀ u ∈ U, u ∉ szR T₁ R₂ t → u * t * u⁻¹ ∉ szA₁ T₁ ⊔ zpowers t
  conj_t_not_mem : (∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹) →
    ∀ u ∈ U, u ∉ szR T₁ R₂ t → u * t * u⁻¹ ∉ R₂ ⊔ zpowers t
  conj_szA₁ : ∀ u ∈ U, ∀ b ∈ szA₁ T₁, u * b * u⁻¹ = b
  conj_sup : ∀ u ∈ U, ∀ x ∈ T₁ ⊔ R₂, x⁻¹ * (u * x * u⁻¹) ∈ R₂
  conj_R₂ : ∀ u ∈ U, ∀ r ∈ R₂, r⁻¹ * (u * r * u⁻¹) ∈ szA₁ T₁
  comm_mem : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ T₁ ⊔ R₂
  sq_mem : ∀ x ∈ U, x ^ 2 ∈ T₁ ⊔ R₂
  inf_centralizer : U ⊓ centralizer ({t} : Set G) = T₁ ⊔ zpowers t
  U₁_le : U₁ ≤ U
  le_normalizer_U₁ : U ≤ normalizer (U₁ : Set G)
  sup_eq : U₁ ⊔ zpowers t = U
  t_not_mem : t ∉ U₁
  inf_eq : U₁ ⊓ szR T₁ R₂ t = T₁ ⊔ R₂
  card_U₁ : Nat.card U₁ = q ^ 4
  d_mem : d ∈ normalizer (U₁ : Set G)

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

namespace SzRCoords2

theorem inf_centralizer_R₂ (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hγ : γ = 0) : szR T₁ R₂ t ⊓ centralizer (R₂ : Set G) = T₁ ⊔ R₂ := by
  have hcomm := h.commute_of_gamma_eq_zero hγ
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le_szR T₁ R₂ t) (sup_le
    (fun y hy => mem_centralizer_iff.mpr fun r hr => (hcomm y hy r hr).symm)
    (fun r hr => mem_centralizer_iff.mpr fun r' hr' => hS.R₂_comm r' hr' r hr)))
  obtain ⟨hxR, hxC⟩ := mem_inf.mp hx
  rcases h.mem x hxR with h0 | h1
  · exact (h.thd_eq_zero_iff x hxR).mp h0
  · exfalso
    obtain ⟨r, hr, hr1⟩ := h.layerTwo_surj hS 1
    have hrR := le_szR_mid T₁ R₂ t hr
    have e := h.comm x hxR r hrR
    rw [(mem_centralizer_iff.mp hxC r hr).symm, mul_inv_cancel_right, mul_inv_cancel,
      h.v_one, h.of_R₂ r hr, hγ] at e
    have e' : (φ r).2.1 = v (r * t * r⁻¹ * t⁻¹) := h.snd_eq r hrR
    rw [← e', hr1] at e
    simp [szCommMap, h1, zero_pow (SzRadical.two_pow_ne_zero _)] at e

theorem comm_mem_centralizer_R₂ (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) {P : Subgroup G}
    (hP1 : ∀ g ∈ P, ∀ b ∈ szA₁ T₁, g * b * g⁻¹ = b)
    (hP2 : ∀ g ∈ P, ∀ r ∈ R₂, r⁻¹ * (g * r * g⁻¹) ∈ szA₁ T₁) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ centralizer (R₂ : Set G) ∧ x ^ 2 ∈ centralizer (R₂ : Set G) := by
  have hA₁comm : ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, b * b' = b' * b := fun b hb b' hb' =>
    hS.R₂_comm b (hS.le_R₂ hb) b' (hS.le_R₂ hb')
  have hmul : ∀ g ∈ P, ∀ g' ∈ P, ∀ r ∈ R₂,
      r⁻¹ * (g * g' * r * (g * g')⁻¹) = (r⁻¹ * (g * r * g⁻¹)) * (r⁻¹ * (g' * r * g'⁻¹)) := by
    intro g hg g' hg' r hr
    have h1 := hP1 g hg _ (hP2 g' hg' r hr)
    calc r⁻¹ * (g * g' * r * (g * g')⁻¹)
        = r⁻¹ * (g * r * g⁻¹) * (g * (r⁻¹ * (g' * r * g'⁻¹)) * g⁻¹) := by group
      _ = (r⁻¹ * (g * r * g⁻¹)) * (r⁻¹ * (g' * r * g'⁻¹)) := by rw [h1]
  have hinv : ∀ g ∈ P, ∀ r ∈ R₂,
      (r⁻¹ * (g * r * g⁻¹)) * (r⁻¹ * (g⁻¹ * r * g⁻¹⁻¹)) = 1 := by
    intro g hg r hr
    rw [← hmul g hg _ (inv_mem hg) r hr]
    group
  have key : ∀ g ∈ P, (∀ r ∈ R₂, r⁻¹ * (g * r * g⁻¹) = 1) → g ∈ centralizer (R₂ : Set G) := by
    intro g _ h1
    refine mem_centralizer_iff.mpr fun r hr => ?_
    have h2 := h1 r hr
    rw [inv_mul_eq_one] at h2
    calc r * g = g * r * g⁻¹ * g := by rw [← h2]
      _ = g * r := by group
  refine ⟨key _ (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) fun r hr => ?_,
    key _ (pow_mem hx 2) fun r hr => ?_⟩
  · rw [hmul _ (mul_mem (mul_mem hx hy) (inv_mem hx)) _ (inv_mem hy) r hr,
      hmul _ (mul_mem hx hy) _ (inv_mem hx) r hr, hmul _ hx _ hy r hr]
    set χx := r⁻¹ * (x * r * x⁻¹)
    set χy := r⁻¹ * (y * r * y⁻¹)
    set χx' := r⁻¹ * (x⁻¹ * r * x⁻¹⁻¹)
    set χy' := r⁻¹ * (y⁻¹ * r * y⁻¹⁻¹)
    have h1 := hinv x hx r hr
    have h2 := hinv y hy r hr
    have hyx : χy * χx' = χx' * χy := hA₁comm _ (hP2 y hy r hr) _ (hP2 _ (inv_mem hx) r hr)
    calc χx * χy * χx' * χy' = (χx * χx') * (χy * χy') := by
          rw [mul_assoc χx, hyx]; group
      _ = 1 := by rw [h1, h2, one_mul]
  · rw [_root_.sq, hmul _ hx _ hx r hr, ← _root_.sq]
    exact hc.sq_eq_one_of_mem_szA₁ ha hK (hP2 x hx r hr)

theorem fst_eq_zero_of_mem_sup_zpowers (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    {x : G} (hx : x ∈ R₂ ⊔ zpowers t) : (φ x).1 = 0 := by
  have hcoe : ((R₂ ⊔ zpowers t : Subgroup G) : Set G) = (R₂ : Set G) * (zpowers t : Set G) :=
    coe_mul_of_right_le_normalizer_left R₂ (zpowers t) (zpowers_le.mpr hS.t_mem_normalizer_R₂)
  have hx' : x ∈ ((R₂ ⊔ zpowers t : Subgroup G) : Set G) := hx
  rw [hcoe] at hx'
  obtain ⟨r, hr, s, hs, rfl⟩ := hx'
  rw [h.mul _ (le_szR_mid T₁ R₂ t hr) _ (mem_sup_right hs), h.of_R₂ r hr]
  rcases mem_zpowers_involution_eq_one_or_eq hS.t_sq hs with rfl | rfl
  · rw [h.map_one]
    simp
  · rw [h.of_t]
    simp

theorem inverts_of_c_eq_one (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc1 : c + 1 = 0) : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹ := by
  intro r hr
  have hrR := le_szR_mid T₁ R₂ t hr
  have hx : r * t ∈ szR T₁ R₂ t := mul_mem hrR (mem_szR_right T₁ R₂ t)
  have h1 := h.sq _ hx
  rw [h.map_mul_t hrR, h.of_R₂ r hr] at h1
  simp only [szSqMap, Prod.fst_add, Prod.snd_add, add_zero, zero_add] at h1
  rw [zero_pow (Nat.succ_ne_zero _), zero_mul, zero_pow (SzRadical.two_pow_ne_zero _), mul_zero,
    zero_add, zero_add, hc1, zero_mul] at h1
  have h2 := h.v_inj _ (h.sq_mem _ hx) h1
  have ht2 : t⁻¹ = t := hS.t_inv
  calc t * r * t⁻¹ = r⁻¹ * (r * t) ^ 2 * t⁻¹ * t⁻¹ := by simp only [_root_.sq]; group
    _ = r⁻¹ := by rw [h2, ht2, mul_one, mul_assoc, ← _root_.sq, hS.t_sq, mul_one]

theorem kappa_ne_one (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) :
    κ ≠ 1 ∧ κ ^ (2 ^ (a + 1) + 1) ≠ 1 := by
  obtain ⟨w, hw⟩ := SzStartField.exists_pow_theta_add_ne_zero ha hK
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (by rw [zero_pow (SzRadical.two_pow_ne_zero _), add_zero])
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hw (by rw [one_pow, CharTwo.add_self_eq_zero])
  have hμ1 : κ ^ (2 ^ (a + 1) + 1) ≠ 1 := by
    intro h1
    obtain ⟨m, hm⟩ := hμ w hw0
    rw [h1, one_pow] at hm
    exact hw1 hm.symm
  refine ⟨fun h1 => hμ1 (by rw [h1, one_pow]), hμ1⟩

theorem eq_szA_of_map_conj_d_eq (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    {S : Subgroup G} (hSΔ : S ∈ gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t))
    (hfix : S.map (MulAut.conj d).toMonoidHom = S) : S = szA₁ T₁ ⊔ zpowers t := by
  obtain ⟨x, hx, hxC, rfl⟩ := h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt hSΔ
  have hdY := hS.d_mem_normalizer_szR hc
  have h1 := h.map_eq_of_map_conj_eq ha hK hdY hx (map_ne_zero_of_thd_eq_one hxC.1) hfix
  have hdx : d * x * d⁻¹ ∈ szR T₁ R₂ t := by
    have := (mem_normalizer_iff''.mp (inv_mem hdY) x).mp hx
    rwa [inv_inv] at this
  have h2 := h.map_conj_d hS hc ha hK hdx
  rw [show d⁻¹ * (d * x * d⁻¹) * d = x by group, h1] at h2
  obtain ⟨hκ1, hμ1⟩ := kappa_ne_one ha hK hμ
  have hs : (φ x).1 = 0 := by
    have h3 := congrArg Prod.fst h2
    simp only [szTorusSmul] at h3
    have h4 : (κ - 1) * (φ x).1 = 0 := by linear_combination -h3
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hκ1)
  have hr : (φ x).2.1 = 0 := by
    have h3 := congrArg (fun z : K × K × K => z.2.1) h2
    simp only [szTorusSmul] at h3
    have h4 : (κ ^ (2 ^ (a + 1) + 1) - 1) * (φ x).2.1 = 0 := by linear_combination -h3
    exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hμ1)
  refine h.szA₁_sup_zpowers_eq_of_map_eq hx (mem_szR_right T₁ R₂ t) ?_
  rw [h.of_t]
  exact Prod.ext hs (Prod.ext hr hxC.1)

theorem mem_sup_zpowers_of_commute (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    {x : G} (hx : x ∈ szR T₁ R₂ t) (hxt : x * t = t * x) : x ∈ T₁ ⊔ zpowers t := by
  obtain ⟨y, hy, r, hr, s, hs, rfl⟩ := hS.exists_decomp' hx
  have hyR := le_szR_left T₁ R₂ t hy
  have hrR := le_szR_mid T₁ R₂ t hr
  have hsR : s ∈ szR T₁ R₂ t := mem_sup_right hs
  have h0 : (φ (y * r * s)).2.1 = 0 := by
    rw [h.snd_eq _ hx, hxt, show t * (y * r * s) * (y * r * s)⁻¹ * t⁻¹ = 1 by group, h.v_one]
  rw [h.mul _ (mul_mem hyR hrR) _ hsR, h.map_mul_T₁_R₂ hy hr] at h0
  have hs2 : (φ s).2.1 = 0 := by
    rcases mem_zpowers_involution_eq_one_or_eq hS.t_sq hs with rfl | rfl
    · rw [h.map_one]; rfl
    · rw [h.of_t]
  simp only [Prod.snd_add, Prod.fst_add, hs2, add_zero] at h0
  have hrA : r ∈ szA₁ T₁ := (h.snd_eq_zero_iff hr).mp h0
  exact mul_mem (mul_mem (mem_sup_left hy) (mem_sup_left (szA₁_le T₁ hrA))) (mem_sup_right hs)

theorem exists_szU_of_regular (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hCA : centralizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) ≤ T₁ ⊔ zpowers t)
    (hd : Odd (orderOf d))
    (hodd : Odd (Nat.card ((gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range ⊓
      MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)))
        (⟨szA₁ T₁ ⊔ zpowers t, szA_mem_gmsRootConjugates T₁ R₂ t⟩ :
          gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) :
      Subgroup (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t))))))
    {E : Subgroup (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)))}
    (hE : E ≤ (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range)
    (hEn : (E.subgroupOf
      (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range).Normal)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hEc : Nat.card E = Fintype.card K)
    (hreg : ∀ Q Z, ∃! e : E,
      (e : Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t))) Q = Z) :
    ∃ U U₁ : Subgroup G, SzU T₁ R₂ t d (Fintype.card K) U U₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  have hNA := h.normalizer_szR_le_normalizer_szA₁ ha hK
  have htR := mem_szR_right T₁ R₂ t
  set ψ := gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) with hψ
  set α₀ : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) :=
    ⟨szA₁ T₁ ⊔ zpowers t, szA_mem_gmsRootConjugates T₁ R₂ t⟩ with hα₀
  have hψapp : ∀ (n : normalizer (szR T₁ R₂ t : Set G))
      (S : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)),
      ((ψ n S : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) : Subgroup G) =
        (S : Subgroup G).map (MulAut.conj (n : G)).toMonoidHom :=
    fun _ _ => rfl
  have hker : ∀ n : normalizer (szR T₁ R₂ t : Set G), ψ n = 1 ↔ (n : G) ∈ szR T₁ R₂ t := by
    intro n
    constructor
    · intro h1
      refine h.mem_szR_of_forall_map_conj_eq hG hS hc ha hK hμ hCt hCA n.2 fun S hSΔ => ?_
      have h2 := congrArg (fun σ : Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t)
        (szA₁ T₁ ⊔ zpowers t)) => ((σ ⟨S, hSΔ⟩ : gmsRootConjugates (szR T₁ R₂ t)
          (szA₁ T₁ ⊔ zpowers t)) : Subgroup G)) h1
      rw [hψapp] at h2
      exact h2
    · intro hnR
      refine Equiv.ext fun S => Subtype.ext ?_
      rw [hψapp]
      exact h.map_conj_eq_of_mem_szR hG hS hc ha hK hμ hCt S.2 hnR
  set U : Subgroup G := (E.comap ψ).map (normalizer (szR T₁ R₂ t : Set G)).subtype with hUdef
  have hmemU : ∀ x : G, x ∈ U ↔ ∃ hx : x ∈ normalizer (szR T₁ R₂ t : Set G), ψ ⟨x, hx⟩ ∈ E := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxE⟩
      exact ⟨⟨x, hx⟩, hxE, rfl⟩
  have hUY : U ≤ normalizer (szR T₁ R₂ t : Set G) := map_subtype_le _
  have hψU : ∀ x (hx : x ∈ U), ψ ⟨x, hUY hx⟩ ∈ E := fun x hx => by
    obtain ⟨hx', hxE⟩ := (hmemU x).mp hx
    exact hxE
  have hRU : szR T₁ R₂ t ≤ U := fun r hr =>
    (hmemU r).mpr ⟨le_normalizer hr, by rw [(hker ⟨r, le_normalizer hr⟩).mpr hr]; exact one_mem E⟩
  have hconjU : ∀ n ∈ normalizer (szR T₁ R₂ t : Set G), ∀ x ∈ U, n * x * n⁻¹ ∈ U := by
    intro n hn x hx
    have hxE := hψU x hx
    have h1 := hEn.conj_mem ⟨ψ ⟨x, hUY hx⟩, hE hxE⟩ (mem_subgroupOf.mpr hxE)
      ⟨ψ ⟨n, hn⟩, ⟨n, hn⟩, rfl⟩
    rw [mem_subgroupOf] at h1
    refine (hmemU _).mpr ⟨mul_mem (mul_mem hn (hUY hx)) (inv_mem hn), ?_⟩
    have e : (⟨n * x * n⁻¹, mul_mem (mul_mem hn (hUY hx)) (inv_mem hn)⟩ :
        normalizer (szR T₁ R₂ t : Set G)) =
        ⟨n, hn⟩ * ⟨x, hUY hx⟩ * ⟨n, hn⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact h1
  have hYU : normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (U : Set G) := by
    intro n hn
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx => hconjU n hn x hx, fun hx => ?_⟩
    have h1 := hconjU n⁻¹ (inv_mem hn) _ hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at h1
  have hkerR : Nat.card ψ.ker = Nat.card (szR T₁ R₂ t) := by
    have e : ψ.ker = (szR T₁ R₂ t).subgroupOf (normalizer (szR T₁ R₂ t : Set G)) := by
      ext n
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      exact hker n
    rw [e, Nat.card_congr (subgroupOfEquivOfLe
      (le_normalizer : szR T₁ R₂ t ≤ normalizer (szR T₁ R₂ t : Set G))).toEquiv]
  have hcardR : Nat.card (szR T₁ R₂ t) = 2 * Fintype.card K ^ 2 * Fintype.card K :=
    h.card_szR_eq hc ha hK
  have hcardU : Nat.card U = 2 * Fintype.card K ^ 4 := by
    have h1 : Nat.card U = Nat.card (E.comap ψ) :=
      Subgroup.card_map_of_injective (normalizer (szR T₁ R₂ t : Set G)).subtype_injective
    have h2 := card_eq_card_map_mul_card_ker_of_ker_le ψ (S := E.comap ψ)
      (fun n hn => by rw [mem_comap, (MonoidHom.mem_ker).mp hn]; exact one_mem E)
    rw [map_comap_eq_self hE] at h2
    rw [h1, h2, hEc, hkerR, hcardR]
    ring
  have hUp : IsPGroup 2 U :=
    IsPGroup.of_card (n := 1 + 4 * (2 * a + 1)) (by rw [hcardU, hK]; ring)
  have hdY : d ∈ normalizer (szR T₁ R₂ t : Set G) := hS.d_mem_normalizer_szR hc
  have hdU : d ∈ normalizer (U : Set G) := hYU hdY
  obtain ⟨hU1, hU2, hU3⟩ := h.fixed_of_isPGroup hS hc ha hK hμ hγ hUp hUY hdU
  have hUA : ∀ x ∈ U, ∀ b ∈ szA₁ T₁, x * b * x⁻¹ = b := hU1
  have hUR₂ : ∀ x ∈ U, ∀ r ∈ R₂, r⁻¹ * (x * r * x⁻¹) ∈ szA₁ T₁ := by
    intro x hx r hr
    have hxr : x * r * x⁻¹ ∈ R₂ :=
      (mem_normalizer_iff.mp (h.normalizer_le_normalizer_R₂ hS ha hK hγ (hUY hx)) r).mp hr
    exact (h.layerTwo_heq r hr _ hxr).mp (hU3 x hx r hr).symm
  have hUsup : ∀ x ∈ U, ∀ y ∈ T₁ ⊔ R₂, y⁻¹ * (x * y * x⁻¹) ∈ R₂ := by
    intro x hx y hy
    have hxy : x * y * x⁻¹ ∈ T₁ ⊔ R₂ :=
      (mem_normalizer_iff.mp (h.normalizer_le_normalizer_sup ha hK hγ (hUY hx)) y).mp hy
    exact (h.layerOne_heq hS hc ha hK y hy _ hxy).mp (hU2 x hx y hy).symm
  have hfixA : ∀ x (hx : x ∈ U), ψ ⟨x, hUY hx⟩ α₀ = α₀ → x ∈ szR T₁ R₂ t := by
    intro x hx h1
    obtain ⟨e, -, he⟩ := hreg α₀ α₀
    have h2 : (⟨ψ ⟨x, hUY hx⟩, hψU x hx⟩ : E) = e := he _ h1
    have h3 : (1 : E) = e := he 1 rfl
    have h4 : ψ ⟨x, hUY hx⟩ = 1 := congrArg Subtype.val (h2.trans h3.symm)
    exact (hker _).mp h4
  have hA_of : ∀ x (hx : x ∈ U), x * t * x⁻¹ ∈ szA₁ T₁ ⊔ zpowers t → x ∈ szR T₁ R₂ t := by
    intro x hx hxA
    refine hfixA x hx (Subtype.ext ?_)
    rw [hψapp]
    have hx' : x⁻¹ ∈ normalizer (szA₁ T₁ : Set G) := hNA (inv_mem (hUY hx))
    have h1 := map_conj_szA₁_sup_zpowers hx' t
    simp only [inv_inv] at h1
    show (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj x).toMonoidHom = szA₁ T₁ ⊔ zpowers t
    rw [h1]
    obtain ⟨hxt, hxt3⟩ := h.thd_conj_t ha hK (hUY hx)
    have hφ : φ (x * t * x⁻¹) = φ t :=
      ((h.mem_szA₁_sup_zpowers_iff htR).mp hxA).2.resolve_left (map_ne_zero_of_thd_eq_one hxt3)
    exact h.szA₁_sup_zpowers_eq_of_map_eq hxt htR hφ
  have hnotA : ∀ x ∈ U, x ∉ szR T₁ R₂ t → x * t * x⁻¹ ∉ szA₁ T₁ ⊔ zpowers t :=
    fun x hx hxR hxA => hxR (hA_of x hx hxA)
  have hnot : (∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹) →
      ∀ x ∈ U, x ∉ szR T₁ R₂ t → x * t * x⁻¹ ∉ R₂ ⊔ zpowers t := by
    rintro ⟨r, hr, hrt⟩ x hx hxR hxt
    have hc1 : c + 1 ≠ 0 := fun hc1 => hrt (h.inverts_of_c_eq_one hS hc1 r hr)
    apply hnotA x hx hxR
    have hs := h.fst_eq_zero_of_mem_sup_zpowers hS hxt
    have hC := h.map_conj_t_mem_szCand ha hK hS.t_sq hγ (inv_mem (hUY hx))
    rw [inv_inv] at hC
    obtain ⟨h3, h4⟩ := hC
    rw [hs, zero_pow (Nat.succ_ne_zero _), zero_add] at h4
    have hr0 : (φ (x * t * x⁻¹)).2.1 = 0 := (mul_eq_zero.mp h4).resolve_left hc1
    have hφ : φ (x * t * x⁻¹) = φ t := by
      rw [h.of_t]
      exact Prod.ext hs (Prod.ext hr0 h3)
    obtain ⟨hxt', -⟩ := h.thd_conj_t ha hK (hUY hx)
    exact (h.mem_szA₁_sup_zpowers_iff htR).mpr ⟨hxt', Or.inr hφ⟩
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ T₁ ⊔ R₂ := by
    intro x hx y hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ U :=
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ szR T₁ R₂ t := by
      refine (hker ⟨_, hUY hmem⟩).mp ?_
      have e : (⟨x * y * x⁻¹ * y⁻¹, hUY hmem⟩ : normalizer (szR T₁ R₂ t : Set G)) =
          ⟨x, hUY hx⟩ * ⟨y, hUY hy⟩ * ⟨x, hUY hx⟩⁻¹ * ⟨y, hUY hy⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hEab _ (hψU x hx) _ (hψU y hy)]
      group
    rw [← h.inf_centralizer_R₂ hS hγ]
    exact mem_inf.mpr ⟨h1, (SzRCoords2.comm_mem_centralizer_R₂ hS hc ha hK hUA hUR₂ hx hy).1⟩
  have hsq : ∀ x ∈ U, x ^ 2 ∈ T₁ ⊔ R₂ := by
    intro x hx
    have h1 : x ^ 2 ∈ szR T₁ R₂ t := by
      refine (hker ⟨_, hUY (pow_mem hx 2)⟩).mp ?_
      have e : (⟨x ^ 2, hUY (pow_mem hx 2)⟩ : normalizer (szR T₁ R₂ t : Set G)) =
          ⟨x, hUY hx⟩ ^ 2 := rfl
      rw [e, map_pow]
      exact hE2 _ (hψU x hx)
    rw [← h.inf_centralizer_R₂ hS hγ]
    exact mem_inf.mpr ⟨h1, (SzRCoords2.comm_mem_centralizer_R₂ hS hc ha hK hUA hUR₂ hx hx).2⟩
  have hCU : U ⊓ centralizer ({t} : Set G) = T₁ ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxU, hxC⟩ := mem_inf.mp hx
      have hxC' : x * t = t * x := mem_centralizer_singleton_iff.mp hxC
      have hxt : x * t * x⁻¹ = t := by rw [hxC']; group
      have hxR : x ∈ szR T₁ R₂ t :=
        hA_of x hxU (by rw [hxt]; exact mem_sup_right (mem_zpowers t))
      exact h.mem_sup_zpowers_of_commute hS hxR hxC'
    · refine le_inf (sup_le ((le_szR_left T₁ R₂ t).trans hRU) (zpowers_le.mpr (hRU htR)))
        (sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hS.t_comm y hy))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)))
  have hY1 := h.normalizer_le_normalizer_sup ha hK hγ
  have hfixd : ∀ w ∈ U, w⁻¹ * (d⁻¹ * w * d) ∈ T₁ ⊔ R₂ →
      w ∈ T₁ ⊔ R₂ ∨ t⁻¹ * w ∈ T₁ ⊔ R₂ := by
    intro w hw hwd
    have hdw : d⁻¹ * w * d ∈ U := by
      have := hconjU d⁻¹ (inv_mem hdY) w hw
      rwa [inv_inv] at this
    have hwdU : w⁻¹ * (d⁻¹ * w * d) ∈ U := mul_mem (inv_mem hw) hdw
    have h1 : ψ ⟨d⁻¹ * w * d, hUY hdw⟩ = ψ ⟨w, hUY hw⟩ := by
      have h2 := (hker ⟨w⁻¹ * (d⁻¹ * w * d), hUY hwdU⟩).mpr (sup_le_szR T₁ R₂ t hwd)
      have e : (⟨w⁻¹ * (d⁻¹ * w * d), hUY hwdU⟩ : normalizer (szR T₁ R₂ t : Set G)) =
          ⟨w, hUY hw⟩⁻¹ * ⟨d⁻¹ * w * d, hUY hdw⟩ := rfl
      rw [e, map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
    have hdA : ψ ⟨d, hdY⟩ α₀ = α₀ := by
      apply Subtype.ext
      rw [hψapp]
      show (szA₁ T₁ ⊔ zpowers t).map (MulAut.conj d).toMonoidHom = szA₁ T₁ ⊔ zpowers t
      have hd' : d⁻¹ ∈ normalizer (szA₁ T₁ : Set G) := hNA (inv_mem hdY)
      have h3 := map_conj_szA₁_sup_zpowers hd' t
      simp only [inv_inv] at h3
      rw [h3, show d * t * d⁻¹ = t by rw [hS.d_comm]; group]
    have hcommdw : ψ ⟨d, hdY⟩ * ψ ⟨w, hUY hw⟩ = ψ ⟨w, hUY hw⟩ * ψ ⟨d, hdY⟩ := by
      have e : (⟨d⁻¹ * w * d, hUY hdw⟩ : normalizer (szR T₁ R₂ t : Set G)) =
          ⟨d, hdY⟩⁻¹ * ⟨w, hUY hw⟩ * ⟨d, hdY⟩ := rfl
      rw [e, map_mul, map_mul, map_inv] at h1
      calc ψ ⟨d, hdY⟩ * ψ ⟨w, hUY hw⟩ =
          ψ ⟨d, hdY⟩ * ((ψ ⟨d, hdY⟩)⁻¹ * ψ ⟨w, hUY hw⟩ * ψ ⟨d, hdY⟩) := by rw [h1]
        _ = ψ ⟨w, hUY hw⟩ * ψ ⟨d, hdY⟩ := by group
    have hP : ψ ⟨d, hdY⟩ (ψ ⟨w, hUY hw⟩ α₀) = ψ ⟨w, hUY hw⟩ α₀ := by
      calc ψ ⟨d, hdY⟩ (ψ ⟨w, hUY hw⟩ α₀) = (ψ ⟨d, hdY⟩ * ψ ⟨w, hUY hw⟩) α₀ := rfl
        _ = (ψ ⟨w, hUY hw⟩ * ψ ⟨d, hdY⟩) α₀ := by rw [hcommdw]
        _ = ψ ⟨w, hUY hw⟩ (ψ ⟨d, hdY⟩ α₀) := rfl
        _ = ψ ⟨w, hUY hw⟩ α₀ := by rw [hdA]
    have hPA : ψ ⟨w, hUY hw⟩ α₀ = α₀ := by
      apply Subtype.ext
      have h4 := congrArg Subtype.val hP
      rw [hψapp] at h4
      exact h.eq_szA_of_map_conj_d_eq hG hS hc ha hK hμ hCt (ψ ⟨w, hUY hw⟩ α₀).2 h4
    have hwR := hfixA w hw hPA
    rcases h.mem w hwR with h0 | h1'
    · exact Or.inl ((h.thd_eq_zero_iff w hwR).mp h0)
    · right
      have htw : t⁻¹ * w ∈ szR T₁ R₂ t := mul_mem (inv_mem htR) hwR
      refine (h.thd_eq_zero_iff _ htw).mp ?_
      rw [h.map_inv_mul htR hwR, h.of_t]
      simp [h1']
  obtain ⟨U₁, hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁⟩ := exists_complement_of_coprime
    ((sup_le_szR T₁ R₂ t).trans hRU) (hUY.trans hY1) hcomm hsq hdU (hY1 hdY) hd (hRU htR)
    h.t_not_mem_sup hS.d_comm hfixd
  have hinf : U₁ ⊓ szR T₁ R₂ t = T₁ ⊔ R₂ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hHU₁ (sup_le_szR T₁ R₂ t))
    obtain ⟨hxU₁, hxR⟩ := mem_inf.mp hx
    rcases h.mem x hxR with h0 | h1'
    · exact (h.thd_eq_zero_iff x hxR).mp h0
    · exfalso
      have htx : t⁻¹ * x ∈ T₁ ⊔ R₂ := by
        refine (h.thd_eq_zero_iff _ (mul_mem (inv_mem htR) hxR)).mp ?_
        rw [h.map_inv_mul htR hxR, h.of_t]
        simp [h1']
      apply htU₁
      have e : t = x * (t⁻¹ * x)⁻¹ := by group
      rw [e]
      exact mul_mem hxU₁ (inv_mem (hHU₁ htx))
  have hcardU₁ : Nat.card U₁ = Fintype.card K ^ 4 := by
    have hidx := relIndex_sup_zpowers_eq_two_of_mul_self_mem htU₁ (hUU₁ (hRU htR))
      (by rw [← _root_.sq, hS.t_sq]; exact one_mem _)
    have h1 := Subgroup.relIndex_mul_card U₁ (U₁ ⊔ zpowers t)
    rw [inf_eq_left.mpr le_sup_left, hidx, hsupU₁, hcardU] at h1
    linarith
  have hsyl : IsSylowOf 2 U (normalizer (szR T₁ R₂ t : Set G)) := by
    rw [isSylowOf_iff]
    refine ⟨hUY, hUp, ?_⟩
    have h1 : U.relIndex (normalizer (szR T₁ R₂ t : Set G)) = E.relIndex ψ.range := by
      rw [relIndex, subgroupOf, hUdef,
        comap_map_eq_self_of_injective (normalizer (szR T₁ R₂ t : Set G)).subtype_injective,
        index_comap]
    have htr : ∀ β γ : gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t),
        ∃ m ∈ ψ.range, m β = γ := by
      intro β γ
      obtain ⟨e, he, -⟩ := hreg β γ
      exact ⟨e, hE e.2, he⟩
    have h2 := card_eq_card_mul_card_inf_stabilizer htr α₀
    have h3 := Subgroup.relIndex_mul_card E ψ.range
    rw [inf_eq_left.mpr hE, h2, hEc] at h3
    have hΔ : Nat.card (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) =
        Fintype.card K := by
      rw [Nat.card_coe_set_eq]
      exact h.ncard_gmsRootConjugates hG hS hc ha hK hμ hCt
    rw [hΔ, mul_comm] at h3
    have h4 : E.relIndex ψ.range = Nat.card (ψ.range ⊓ MulAction.stabilizer
        (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t))) α₀ :
          Subgroup (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)))) :=
      Nat.eq_of_mul_eq_mul_left Fintype.card_pos h3
    rw [h1, h4, ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd
  refine ⟨U, U₁, ⟨hUY, hYU, hsyl, hcardU, hRU, fun x hx hfix => ?_, hnotA, hnot, hUA, hUsup,
    hUR₂, hcomm, hsq, hCU, hU₁U, hUU₁, hsupU₁, htU₁, hinf, hcardU₁, hdU₁⟩⟩
  exact h.mem_szR_of_forall_map_conj_eq hG hS hc ha hK hμ hCt hCA (hUY hx) hfix

end SzRCoords2

end CFSG.SeitzReduction.RankOne
