module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUEightBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

section SecAdd

variable {G : Type*} [Group G] {K : Type*} [AddCommGroup K] {S S' X : Subgroup G} {f : G → K}

theorem secPerm_add (hXS : X ≤ normalizer (S : Set G)) (hXS' : X ≤ normalizer (S' : Set G))
    (hsurj : ∀ w, ∃ x ∈ S, f x = w) (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S')
    (hadd : ∀ x ∈ S, ∀ x' ∈ S, f (x * x') = f x + f x') (n : X) (w w' : K) :
    secPerm hXS hXS' hsurj heq n (w + w') =
      secPerm hXS hXS' hsurj heq n w + secPerm hXS hXS' hsurj heq n w' := by
  obtain ⟨x, hx, rfl⟩ := hsurj w
  obtain ⟨x', hx', rfl⟩ := hsurj w'
  have hnx : (n : G) * x * (n : G)⁻¹ ∈ S := (mem_normalizer_iff.mp (hXS n.2) x).mp hx
  have hnx' : (n : G) * x' * (n : G)⁻¹ ∈ S := (mem_normalizer_iff.mp (hXS n.2) x').mp hx'
  rw [← hadd x hx x' hx', secPerm_apply hXS hXS' hsurj heq n (mul_mem hx hx'),
    secPerm_apply hXS hXS' hsurj heq n hx, secPerm_apply hXS hXS' hsurj heq n hx',
    ← hadd _ hnx _ hnx']
  congr 1
  group

@[expose] noncomputable def secAddAut (hXS : X ≤ normalizer (S : Set G))
    (hXS' : X ≤ normalizer (S' : Set G)) (hsurj : ∀ w, ∃ x ∈ S, f x = w)
    (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S')
    (hadd : ∀ x ∈ S, ∀ x' ∈ S, f (x * x') = f x + f x') (n : X) : AddAut K :=
  AddEquiv.mk' (secPerm hXS hXS' hsurj heq n) (secPerm_add hXS hXS' hsurj heq hadd n)

theorem secAddAut_apply (hXS : X ≤ normalizer (S : Set G)) (hXS' : X ≤ normalizer (S' : Set G))
    (hsurj : ∀ w, ∃ x ∈ S, f x = w) (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S')
    (hadd : ∀ x ∈ S, ∀ x' ∈ S, f (x * x') = f x + f x') (n : X) {x : G} (hx : x ∈ S) :
    secAddAut hXS hXS' hsurj heq hadd n (f x) = f ((n : G) * x * (n : G)⁻¹) :=
  secPerm_apply hXS hXS' hsurj heq n hx

end SecAdd

section Affine

variable {Y Δ : Type*} [Group Y] {K : Type*} [AddCommGroup K]

theorem exists_eq_affine_of_mem_map (ψ : Y →* Equiv.Perm Δ) (e : Δ ≃ K) (L : Y → AddAut K)
    (b : Y → K) (hL : ∀ n S, e (ψ n S) = L n (e S) + b n) {x : Equiv.Perm K}
    (hx : x ∈ ψ.range.map e.permCongrHom.toMonoidHom) : ∃ n, ∀ w, x w = L n w + b n := by
  obtain ⟨σ, ⟨n, rfl⟩, rfl⟩ := hx
  refine ⟨n, fun w => ?_⟩
  show e (ψ n (e.symm w)) = _
  rw [hL, Equiv.apply_symm_apply]

theorem false_of_affine_card_range_eq_168 {Y Δ : Type*} [Group Y] {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 8) (ψ : Y →* Equiv.Perm Δ) (e : Δ ≃ K) (L : Y → AddAut K) (b : Y → K)
    (hL : ∀ n S, e (ψ n S) = L n (e S) + b n) (hN : Nat.card ψ.range = 168)
    (hs : IsSimpleGroup ψ.range)
    (hsq : (∀ n, ∃ φ : AddAut K, ∀ a, L n (a ^ 5) = φ a ^ 5) ∨
      ∀ n, ∃ φ : AddAut K, ∀ a, L n a ^ 5 = φ (a ^ 5)) : False := by
  set N' := ψ.range.map e.permCongrHom.toMonoidHom with hN'
  have hiso : ψ.range ≃* N' := ψ.range.equivMapOfInjective _ e.permCongrHom.injective
  have hcard : Nat.card N' = 168 := by rw [← Nat.card_congr hiso.toEquiv, hN]
  have hs' : IsSimpleGroup N' := hiso.symm.isSimpleGroup
  have haff : ∀ x ∈ N', ∀ v w, x (v + w) + x 0 = x v + x w := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_eq_affine_of_mem_map ψ e L b hL hx
    exact affine_of_eq_add (L n).toAddMonoidHom (b n) hn
  rcases hsq with hsq | hsq
  · refine false_of_affine_card_eq_168_of_sq_equivariant hK N' haff hcard hs' fun x hx => ?_
    obtain ⟨n, hn⟩ := exists_eq_affine_of_mem_map ψ e L b hL hx
    obtain ⟨φ, hφ⟩ := hsq n
    exact ⟨φ, fun a => by rw [hn, hn, map_zero, zero_add, add_sub_cancel_right, hφ]⟩
  · refine false_of_affine_card_eq_168_of_sq_equivariant' hK N' haff hcard hs' fun x hx => ?_
    obtain ⟨n, hn⟩ := exists_eq_affine_of_mem_map ψ e L b hL hx
    obtain ⟨φ, hφ⟩ := hsq n
    exact ⟨φ, fun a => by rw [hn, hn, map_zero, zero_add, add_sub_cancel_right, hφ]⟩

end Affine

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

namespace SzRCoords2

theorem conj_mem_T₁_of_c_eq_one (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hγ : γ = 0) (hc1 : c + 1 = 0) {n : G} (hn : n ∈ normalizer (szR T₁ R₂ t : Set G)) {y : G}
    (hy : y ∈ T₁) : n * y * n⁻¹ ∈ T₁ := by
  have hs₀ : (φ (n * t * n⁻¹)).1 = 0 := by
    have hC := h.map_conj_t_mem_szCand ha hK hS.t_sq hγ (inv_mem hn)
    rw [inv_inv] at hC
    have h2 := hC.2
    rw [hc1, zero_mul, add_zero] at h2
    exact pow_eq_zero_iff (Nat.succ_ne_zero _) |>.mp h2
  have h1 := h.snd_conj_T₁ hS ha hK hγ hn hy
  rw [hs₀] at h1
  simp only [zero_pow (SzRadical.two_pow_ne_zero _), mul_zero, add_zero] at h1
  have hny : n * y * n⁻¹ ∈ T₁ ⊔ R₂ :=
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_sup ha hK hγ hn) y).mp (mem_sup_left hy)
  obtain ⟨y', hy', r', hr', hyr⟩ := exists_mul_of_mem_sup hS hny
  rw [← hyr, h.map_mul_T₁_R₂ hy' hr'] at h1
  have hrA : r' ∈ szA₁ T₁ := (h.snd_eq_zero_iff hr').mp h1
  rw [← hyr]
  exact mul_mem hy' (szA₁_le T₁ hrA)

theorem _root_.CFSG.SeitzReduction.RankOne.SzRootCoords.u_eq_iff (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) :
    ∀ x ∈ T₁, ∀ x' ∈ T₁, u x = u x' ↔ x⁻¹ * x' ∈ szA₁ T₁ := by
  intro x hx x' hx'
  refine ⟨hc.inv_mul_mem_szA₁_of_u_eq ha hK hx hx', fun hA => ?_⟩
  have h1 := hc.u_eq_zero_of_mem_szA₁ ha hK hA
  rw [(hc.mul _ (inv_mem hx) _ hx').1, (hc.inv hx).1] at h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h1 - u x' * h2

theorem false_of_card_range_eq_168 (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1)) (ha1 : a = 1)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hCA : centralizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) ≤ T₁ ⊔ zpowers t)
    (hN : Nat.card (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range = 168)
    (hs : IsSimpleGroup (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range)
    (hperf : ⁅(gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range,
      (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range⁆ =
      (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range) : False := by
  classical
  have hγ := h.gamma_eq_zero hG hS hc ha hK hμ hCt
  have hK8 : Nat.card K = 8 := by rw [Nat.card_eq_fintype_card, hK, ha1]; norm_num
  have hθ : 2 ^ (a + 1) + 1 = 5 := by rw [ha1]; norm_num
  have htR := mem_szR_right T₁ R₂ t
  have hYA : normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (szA₁ T₁ : Set G) :=
    h.normalizer_szR_le_normalizer_szA₁ ha hK
  have hY1 : normalizer (szR T₁ R₂ t : Set G) ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
    h.normalizer_le_normalizer_sup ha hK hγ
  have hY2 : normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (R₂ : Set G) :=
    h.normalizer_le_normalizer_R₂ hS ha hK hγ
  have hadd1 : ∀ x ∈ T₁ ⊔ R₂, ∀ x' ∈ T₁ ⊔ R₂, (φ (x * x')).1 = (φ x).1 + (φ x').1 :=
    fun x hx x' hx' => by
      rw [h.mul x (sup_le_szR T₁ R₂ t hx) x' (sup_le_szR T₁ R₂ t hx')]
      rfl
  have hadd2 : ∀ x ∈ R₂, ∀ x' ∈ R₂, (φ (x * x')).2.1 = (φ x).2.1 + (φ x').2.1 :=
    fun x hx x' hx' => by
      rw [h.mul x (le_szR_mid T₁ R₂ t hx) x' (le_szR_mid T₁ R₂ t hx')]
      rfl
  set β := secAddAut hYA (le_normalizer_bot _) h.v_surj h.layerA_heq h.v_mul with hβ
  set h₁ := secAddAut hY1 hY2 (h.layerOne_surj hc) (h.layerOne_heq hS hc ha hK) hadd1 with hh₁
  set k₂ := secAddAut hY2 hYA (h.layerTwo_surj hS) h.layerTwo_heq hadd2 with hk₂
  have hβa : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) {b : G}, b ∈ szA₁ T₁ →
      β n (v b) = v ((n : G) * b * (n : G)⁻¹) := fun n b hb => secAddAut_apply _ _ _ _ _ n hb
  have hh₁a : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) {x : G}, x ∈ T₁ ⊔ R₂ →
      h₁ n (φ x).1 = (φ ((n : G) * x * (n : G)⁻¹)).1 := fun n x hx => secAddAut_apply _ _ _ _ _ n hx
  have hk₂a : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) {x : G}, x ∈ R₂ →
      k₂ n (φ x).2.1 = (φ ((n : G) * x * (n : G)⁻¹)).2.1 :=
    fun n x hx => secAddAut_apply _ _ _ _ _ n hx
  have hkβ : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) (w : K), k₂ n w = β n w := by
    intro n w
    obtain ⟨r, hr, rfl⟩ := h.layerTwo_surj hS w
    rw [hk₂a n hr, h.snd_conj_R₂ hS ha hK hγ n.2 hr, h.snd_eq r (le_szR_mid T₁ R₂ t hr),
      hβa n (hS.rho_mem r hr)]
  have hdec : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) {x : G}, x ∈ szR T₁ R₂ t →
      (φ x).2.2 = 1 → x * t⁻¹ ∈ T₁ ⊔ R₂ ∧
        φ ((n : G) * x * (n : G)⁻¹) = φ ((n : G) * (x * t⁻¹) * (n : G)⁻¹) +
          φ ((n : G) * t * (n : G)⁻¹) ∧ φ (x * t⁻¹) = φ x - (0, 0, 1) := by
    intro n x hx hx3
    have hz : x * t⁻¹ ∈ szR T₁ R₂ t := mul_mem hx (inv_mem htR)
    have hφz : φ (x * t⁻¹) = φ x - (0, 0, 1) := by
      have h1 := h.map_mul_t hz
      rw [show x * t⁻¹ * t = x by group] at h1
      rw [h1]
      abel
    refine ⟨(h.thd_eq_zero_iff _ hz).mp (by rw [hφz]; simp [hx3]), ?_, hφz⟩
    have hnz : (n : G) * (x * t⁻¹) * (n : G)⁻¹ ∈ szR T₁ R₂ t := (mem_normalizer_iff.mp n.2 _).mp hz
    have hnt : (n : G) * t * (n : G)⁻¹ ∈ szR T₁ R₂ t := (mem_normalizer_iff.mp n.2 _).mp htR
    rw [← h.mul _ hnz _ hnt]
    congr 1
    group
  by_cases hc1 : c + 1 = 0
  ·
    have hYT : normalizer (szR T₁ R₂ t : Set G) ≤ normalizer (T₁ : Set G) := by
      intro n hn
      refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
      have := h.conj_mem_T₁_of_c_eq_one hS ha hK hγ hc1 (inv_mem hn) hx
      rwa [inv_inv] at this
    have hsurjT : ∀ w, ∃ x ∈ T₁, u x = w := fun w => by
      obtain ⟨x, hx, hu, -⟩ := hc.surj w 0
      exact ⟨x, hx, hu⟩
    set ψT := secAddAut hYT hYA hsurjT (hc.u_eq_iff ha hK)
      (fun x hx x' hx' => (hc.mul x hx x' hx').1)
      with hψT
    have hψTa : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) {x : G}, x ∈ T₁ →
        ψT n (u x) = u ((n : G) * x * (n : G)⁻¹) := fun n x hx => secAddAut_apply _ _ _ _ _ n hx
    have hCand : ∀ z ∈ szCand a c, z.1 = 0 := by
      intro z hz
      have h2 := hz.2
      rw [hc1, zero_mul, add_zero] at h2
      exact pow_eq_zero_iff (Nat.succ_ne_zero _) |>.mp h2
    obtain ⟨e, he⟩ := h.exists_equiv_coord hG hS hc ha hK hμ hCt (fun z => z.2.1)
      (fun z hz z' hz' hzz => Prod.ext (by rw [hCand z hz, hCand z' hz'])
        (Prod.ext hzz (by rw [hz.1, hz'.1])))
      (fun w => ⟨(0, w, 1), ⟨rfl, by simp [hc1]⟩, rfl⟩)
    refine false_of_affine_card_range_eq_168 hK8 _ e k₂
      (fun n => (φ ((n : G) * t * (n : G)⁻¹)).2.1) (fun n S => ?_) hN hs (Or.inl fun n => ?_)
    · obtain ⟨x, hx, hxC, hSx⟩ := h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt S.2
      rw [h.equiv_coord_action ha hK hγ (fun z => z.2.1) he n S hx hxC hSx, he S x hx hxC hSx]
      obtain ⟨hz, hφ, hφz⟩ := hdec n hx hxC.1
      have hz1 : (φ (x * t⁻¹)).1 = 0 := by rw [hφz]; simp [hCand _ hxC]
      have hzR₂ : x * t⁻¹ ∈ R₂ := (h.fst_eq_zero_iff hS hc ha hK hz).mp hz1
      show (φ ((n : G) * x * (n : G)⁻¹)).2.1 = k₂ n (φ x).2.1 + (φ ((n : G) * t * (n : G)⁻¹)).2.1
      rw [hφ, Prod.snd_add, Prod.fst_add, ← hk₂a n hzR₂, hφz]
      simp
    · refine ⟨ψT n, fun w => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hsurjT w
      have hny : (n : G) * y * (n : G)⁻¹ ∈ T₁ := by
        have := (mem_normalizer_iff.mp (hYT n.2) y).mp hy
        exact this
      rw [hkβ, ← hθ, ← (hc.sq hy).2, hβa n (hc.sq_mem_szA₁ ha hK hy), hψTa n hy,
        show (n : G) * y ^ 2 * (n : G)⁻¹ = ((n : G) * y * (n : G)⁻¹) ^ 2 by
          simp only [_root_.sq]; group, (hc.sq hny).2]
  · by_cases hc0 : c = 0
    ·
      have hCand : ∀ z ∈ szCand a c, z.2.1 = z.1 ^ 5 := by
        intro z hz
        have h2 := hz.2
        rw [hc0, zero_add, one_mul, hθ] at h2
        have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination h2 - z.1 ^ 5 * h3
      obtain ⟨e, he⟩ := h.exists_equiv_coord hG hS hc ha hK hμ hCt (fun z => z.1)
        (fun z hz z' hz' hzz => Prod.ext hzz
          (Prod.ext (by rw [hCand z hz, hCand z' hz', show z.1 = z'.1 from hzz])
            (by rw [hz.1, hz'.1])))
        (fun w => ⟨(w, w ^ 5, 1), ⟨rfl, by
          simp only
          rw [hc0, zero_add, one_mul, hθ, CharTwo.add_self_eq_zero]⟩, rfl⟩)
      refine false_of_affine_card_range_eq_168 hK8 _ e h₁
        (fun n => (φ ((n : G) * t * (n : G)⁻¹)).1) (fun n S => ?_) hN hs (Or.inr fun n => ?_)
      · obtain ⟨x, hx, hxC, hSx⟩ := h.exists_eq_szA₁_sup_zpowers hG hS hc ha hK hμ hCt S.2
        rw [h.equiv_coord_action ha hK hγ (fun z => z.1) he n S hx hxC hSx, he S x hx hxC hSx]
        obtain ⟨hz, hφ, hφz⟩ := hdec n hx hxC.1
        show (φ ((n : G) * x * (n : G)⁻¹)).1 = h₁ n (φ x).1 + (φ ((n : G) * t * (n : G)⁻¹)).1
        rw [hφ, Prod.fst_add, ← hh₁a n hz, hφz]
        simp
      · refine ⟨β n, fun w => ?_⟩
        obtain ⟨y, hy, hyu, -⟩ := hc.surj w 0
        have h1 := h.v_conj_sq_T₁ ha hK hγ n.2 hy
        rw [hc0, zero_mul, add_zero, ← hh₁a n (mem_sup_left hy), h.of_T₁ y hy, hyu, hθ] at h1
        rw [← h1, ← hβa n (hc.sq_mem_szA₁ ha hK hy), (hc.sq hy).2, hyu, hθ]
    ·
      have hc1' : c ≠ 1 := fun h1 => hc1 (by rw [h1, CharTwo.add_self_eq_zero])
      have hβc : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) (w : K), β n (c * w) = c * β n w := by
        intro n w
        obtain ⟨r, hr, rfl⟩ := h.layerTwo_surj hS w
        have hrR := le_szR_mid T₁ R₂ t hr
        have hr2 : v (r ^ 2) = c * (φ r).2.1 := by
          rw [h.sq r hrR, h.of_R₂ r hr, hγ]
          simp [szSqMap, zero_pow (Nat.succ_ne_zero _)]
        rw [← hr2, hβa n (h.sq_mem r hrR), h.v_conj_sq_R₂ hS ha hK hγ n.2 hr, ← hk₂a n hr, hkβ]
      have hlin : ∀ (n : normalizer (szR T₁ R₂ t : Set G)) (w : K), β n w = β n 1 * w :=
        fun n => eq_mul_of_map_mul_eq hK8 hc0 hc1' (β n).toAddMonoidHom (hβc n)
      set B := secPerm hYA (le_normalizer_bot _) h.v_surj h.layerA_heq with hB
      have hBβ : ∀ n w, B n w = β n w := fun _ _ => rfl
      have hBc : ∀ n m, B n * B m = B m * B n := by
        intro n m
        refine Equiv.ext fun w => ?_
        simp only [Equiv.Perm.mul_apply, hBβ]
        rw [hlin n (β m w), hlin m w, hlin m (β n w), hlin n w]
        ring
      have hcomm_le : ⁅(⊤ : Subgroup (normalizer (szR T₁ R₂ t : Set G))), ⊤⁆ ≤ B.ker := by
        rw [commutator_le]
        intro g₁ _ g₂ _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
        exact hBc g₁ g₂
      have hdY : d ∈ normalizer (szR T₁ R₂ t : Set G) := hS.d_mem_normalizer_szR hc
      have hψd : gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t) ⟨d, hdY⟩ ∈
          Subgroup.map (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t))
            ⁅(⊤ : Subgroup (normalizer (szR T₁ R₂ t : Set G))), ⊤⁆ := by
        rw [map_commutator, ← MonoidHom.range_eq_map, hperf]
        exact ⟨⟨d, hdY⟩, rfl⟩
      obtain ⟨z, hz, hzd⟩ := hψd
      have hker : ((z⁻¹ * ⟨d, hdY⟩ : normalizer (szR T₁ R₂ t : Set G)) : G) ∈ szR T₁ R₂ t := by
        refine h.mem_szR_of_forall_map_conj_eq hG hS hc ha hK hμ hCt hCA (z⁻¹ * ⟨d, hdY⟩).2
          fun S hSΔ => ?_
        have h1 : gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)
            (z⁻¹ * ⟨d, hdY⟩) = 1 := by
          rw [map_mul, map_inv, hzd, inv_mul_cancel]
        have h2 := congrArg (fun σ : Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t)
          (szA₁ T₁ ⊔ zpowers t)) => ((σ ⟨S, hSΔ⟩ : gmsRootConjugates (szR T₁ R₂ t)
            (szA₁ T₁ ⊔ zpowers t)) : Subgroup G)) h1
        exact h2
      have hBd : B ⟨d, hdY⟩ = 1 := by
        have h1 : B z = 1 := hcomm_le hz
        have h2 : B (z⁻¹ * ⟨d, hdY⟩) = 1 := by
          refine Equiv.ext fun w => ?_
          obtain ⟨b, hb, rfl⟩ := h.v_surj w
          rw [hBβ, hβa _ hb, h.central _ hker b hb, mul_inv_cancel_right]
          rfl
        calc B ⟨d, hdY⟩ = B z * B (z⁻¹ * ⟨d, hdY⟩) := by rw [← map_mul, mul_inv_cancel_left]
          _ = 1 := by rw [h1, h2, one_mul]
      obtain ⟨b, hb, hb1⟩ := h.v_surj 1
      have h1 := congrArg (fun σ : Equiv.Perm K => σ (v b)) hBd
      simp only [Equiv.Perm.coe_one, id] at h1
      rw [hBβ, hβa _ hb] at h1
      have hdb : d * b * d⁻¹ ∈ szA₁ T₁ := (mem_normalizer_iff.mp (hYA hdY) b).mp hb
      have h2 := (h.layerA_heq _ hdb _ hb).mp h1
      rw [mem_bot, inv_mul_eq_one] at h2
      have h3 := hc.v_conj_szA₁ ha hK hb
      rw [show d⁻¹ * b * d = b by
        calc d⁻¹ * b * d = d⁻¹ * (d * b * d⁻¹) * d := by rw [h2]
          _ = b := by group, hb1, mul_one] at h3
      exact (kappa_ne_one ha hK hμ).2 h3.symm

end SzRCoords2

end CFSG.SeitzReduction.RankOne
