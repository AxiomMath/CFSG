module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchHKS
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1CornerA

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}
  {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}

theorem mem_U_of_mem_normalizer_T₁_of_centralizes
    (h : SzC1Stage G L f a t T d V U U₁ k)
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) {n : G}
    (hnU : n ∈ normalizer (U : Set G)) (hnT : n ∈ normalizer (szT₁ L T : Set G))
    (hcen : ∀ b ∈ szA₁ (szT₁ L T), n * b * n⁻¹ = b) : n ∈ U := by
  obtain ⟨w, hw, hwc⟩ := h.mem_U₁_mul_centralizer hμ hlam hν hnU hnT
  set c := w⁻¹ * n with hcdef
  have hwU : w ∈ U := h.U₁_le hw
  have hcA : ∀ b ∈ szA₁ (szT₁ L T), b * c = c * b := by
    intro b hb
    have e1 := hcen b hb
    have e2 := h.conj_szA₁ w⁻¹ (inv_mem hwU) b hb
    rw [inv_inv] at e2
    calc b * c = b * w⁻¹ * n := by rw [hcdef, mul_assoc]
      _ = w⁻¹ * (w * b * w⁻¹) * n := by group
      _ = w⁻¹ * (w * (w⁻¹ * b * w) * w⁻¹) * n := by rw [e2]
      _ = w⁻¹ * (n * b * n⁻¹) * n := by rw [e1]; group
      _ = c * b := by rw [hcdef]; group
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hwc
  have hle : szA L T t ≤ centralizer ({c} : Set G) := by
    refine sup_le (fun b hb => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      exact hcA b hb
    · rw [mem_centralizer_singleton_iff]
      exact hct.symm
  have hcC : c ∈ centralizer (szA L T t : Set G) := mem_centralizer_iff.mpr fun x hx =>
    mem_centralizer_singleton_iff.mp (hle hx)
  have hfacts := h.start.facts
  have hcT : c ∈ T := by
    rw [hfacts.2.2.2.2.2.2.2.1] at hcC
    exact hcC
  have hTU : T ≤ U := by
    rw [hfacts.1]
    exact sup_le (h.T₁_le_U₁.trans h.U₁_le) (zpowers_le.mpr h.t_mem_U)
  have e : n = w * c := by rw [hcdef]; group
  rw [e]
  exact mul_mem hwU (hTU hcT)

theorem _root_.CFSG.SeitzReduction.RankOne.SzCorner.mul_mul_inv_eq {G : Type*} [Group G]
    {y₁ y₂ y₃ w₁ w₂ w₃ : G} (h12 : y₂ * w₁ = w₁ * y₂) (h13 : y₃ * w₁ = w₁ * y₃)
    (h23 : y₃ * w₂ = w₂ * y₃) (h33 : y₃ * w₃ = w₃ * y₃) :
    (y₁ * w₁) * (y₂ * w₂) * (y₃ * w₃)⁻¹ = (y₁ * y₂ * y₃⁻¹) * (w₁ * w₂ * w₃⁻¹) := by
  have c13 : w₁ * y₃⁻¹ = y₃⁻¹ * w₁ := by
    calc w₁ * y₃⁻¹ = y₃⁻¹ * (y₃ * w₁) * y₃⁻¹ := by group
      _ = y₃⁻¹ * (w₁ * y₃) * y₃⁻¹ := by rw [h13]
      _ = y₃⁻¹ * w₁ := by group
  have c23 : w₂ * y₃⁻¹ = y₃⁻¹ * w₂ := by
    calc w₂ * y₃⁻¹ = y₃⁻¹ * (y₃ * w₂) * y₃⁻¹ := by group
      _ = y₃⁻¹ * (w₂ * y₃) * y₃⁻¹ := by rw [h23]
      _ = y₃⁻¹ * w₂ := by group
  have c33 : w₃⁻¹ * y₃⁻¹ = y₃⁻¹ * w₃⁻¹ := by
    calc w₃⁻¹ * y₃⁻¹ = (y₃ * w₃)⁻¹ := by group
      _ = (w₃ * y₃)⁻¹ := by rw [h33]
      _ = y₃⁻¹ * w₃⁻¹ := by group
  calc (y₁ * w₁) * (y₂ * w₂) * (y₃ * w₃)⁻¹ = y₁ * (w₁ * y₂) * w₂ * (w₃⁻¹ * y₃⁻¹) := by group
    _ = y₁ * (y₂ * w₁) * w₂ * (y₃⁻¹ * w₃⁻¹) := by rw [← h12, c33]
    _ = y₁ * y₂ * w₁ * (w₂ * y₃⁻¹) * w₃⁻¹ := by group
    _ = y₁ * y₂ * (w₁ * y₃⁻¹) * w₂ * w₃⁻¹ := by rw [c23]; group
    _ = (y₁ * y₂ * y₃⁻¹) * (w₁ * w₂ * w₃⁻¹) := by rw [c13]; group

section Coords

variable (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem mem_U_of_centralizes
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U)
    (hsimple : IsSimpleGroup (h.famPerm hK hc hμ hlam).range)
    (hbig : 2 ^ f < Nat.card (h.famPerm hK hc hμ hlam).range) {n : G}
    (hn : n ∈ normalizer (U : Set G)) (hcen : ∀ b ∈ szA₁ (szT₁ L T), n * b * n⁻¹ = b) :
    n ∈ U := by
  set φ := h.famPerm hK hc hμ hlam with hφ
  set C : Subgroup (normalizer (U : Set G)) :=
    (centralizer (szA₁ (szT₁ L T) : Set G)).subgroupOf (normalizer (U : Set G)) with hCdef
  have hC : ∀ m : normalizer (U : Set G),
      m ∈ C ↔ ∀ b ∈ szA₁ (szT₁ L T), (m : G) * b * (m : G)⁻¹ = b := by
    intro m
    rw [hCdef, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro hm b hb
      rw [← hm b hb, mul_inv_cancel_right]
    · intro hm b hb
      calc b * m = ((m : G) * b * (m : G)⁻¹) * m := by rw [hm b hb]
        _ = m * b := by group
  have hCn : C.Normal := ⟨fun m hm g => by
    rw [hC] at hm ⊢
    intro b hb
    have hb' := h.conj_mem_szA₁_of_normalizer hμ (inv_mem g.2) hb
    rw [inv_inv] at hb'
    have e := hm _ hb'
    show (g : G) * m * (g : G)⁻¹ * b * ((g : G) * m * (g : G)⁻¹)⁻¹ = b
    calc (g : G) * m * (g : G)⁻¹ * b * ((g : G) * m * (g : G)⁻¹)⁻¹ =
        (g : G) * ((m : G) * ((g : G)⁻¹ * b * g) * (m : G)⁻¹) * (g : G)⁻¹ := by group
      _ = b := by rw [e]; group⟩
  have hfix : ∀ m ∈ C, φ m 0 = 0 → φ m = 1 := by
    intro m hm h0
    have hmT := (h.famPerm_zero_iff hK hc hμ hlam m).mp h0
    have hmU := h.mem_U_of_mem_normalizer_T₁_of_centralizes hμ hlam hν m.2 hmT ((hC m).mp hm)
    exact Equiv.ext fun c => h.famPerm_eq_of_mem_U hK hc hκ hμ hlam hν hU m hmU c
  set D := C.map φ.rangeRestrict with hD
  have hDn : D.Normal := hCn.map φ.rangeRestrict φ.rangeRestrict_surjective
  have := hsimple
  have := hDn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with hbot | htop
  · have hmem : φ.rangeRestrict ⟨n, hn⟩ ∈ D := ⟨⟨n, hn⟩, (hC _).mpr hcen, rfl⟩
    rw [hbot, mem_bot] at hmem
    have h1 : φ ⟨n, hn⟩ = 1 := congrArg Subtype.val hmem
    have h0 : φ ⟨n, hn⟩ 0 = 0 := by rw [h1]; rfl
    exact h.mem_U_of_mem_normalizer_T₁_of_centralizes hμ hlam hν hn
      ((h.famPerm_zero_iff hK hc hμ hlam ⟨n, hn⟩).mp h0) hcen
  · exfalso
    have hinj : Function.Injective (fun p : φ.range => (p : Equiv.Perm K) 0) := by
      intro p p' hpp'
      obtain ⟨m, hm, hmp⟩ : p ∈ D := by rw [htop]; exact mem_top p
      obtain ⟨m', hm', hmp'⟩ : p' ∈ D := by rw [htop]; exact mem_top p'
      have hp : (p : Equiv.Perm K) = φ m := by rw [← hmp]; rfl
      have hp' : (p' : Equiv.Perm K) = φ m' := by rw [← hmp']; rfl
      have h0 : φ (m⁻¹ * m') 0 = 0 := by
        have e : φ m' 0 = φ m 0 := by
          simp only at hpp'
          rw [← hp, ← hp']
          exact hpp'.symm
        rw [map_mul, map_inv, Equiv.Perm.mul_apply, e]
        exact (φ m).symm_apply_apply 0
      have h1 := hfix _ (mul_mem (inv_mem hm) hm') h0
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact Subtype.ext (by rw [hp, hp', h1])
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := K), hK] at hle
    omega

theorem U_le_of_conj_mem (hf : f = 3)
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) {X : Subgroup G}
    (hX : ∀ n ∈ normalizer (U : Set G), n * t * n⁻¹ ∈ X)
    (hXd : ∀ x ∈ X, d⁻¹ * x * d ∈ X) : U ≤ X := by
  have ha1 : a = 1 := by have := h.hfa; omega
  subst ha1
  have hK' := h.card_K hK hc
  have hcardK : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [Nat.card_eq_fintype_card, hK']
  have hμg := pow_theta_succ_generator_of_generator h.ha hcardK hκ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set V₁ := U₁ ⊓ centralizer (szT₁ L T : Set G) with hV₁
  set S : G → K := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) with hSdef
  have hSmul : ∀ x ∈ U₁, ∀ y ∈ U₁, S (x * y) = S x + S y := fun x hx y hy =>
    h.S_mul hK hc hx hy
  have hS1 : S 1 = 0 := by simp [hSdef, hc.v_one]
  have hSinv : ∀ x ∈ U₁, S x⁻¹ = S x := by
    intro x hx
    have e := hSmul x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, hS1] at e
    linear_combination -e - S x * h2
  have ht : t ∈ X := by simpa using hX 1 (one_mem _)
  have hVX : V ≤ X := by
    intro r hr
    obtain ⟨y, hy, hyr⟩ := h.exists_comm_t_eq hK hc hκ hr
    rw [← hyr]
    exact mul_mem (hX y (le_normalizer (h.U₁_le hy))) (inv_mem ht)
  obtain ⟨ν, hν'⟩ := h.exists_nu hK hc hκ hμ hlam
  have hν0 : ν ≠ 0 := by
    rintro rfl
    obtain ⟨w₀, hw₀, hw₀1⟩ := hν
    have e := hν' w₀ hw₀
    rw [zero_mul] at e
    exact hw₀1 (hc.eq_one_of_v_eq_zero h.ha hK' (h.sq_mul_t_mem_szA₁ hK hc hμ (mem_inf.mp hw₀).1) e)
  have step2 : ∀ c : K, ∃ y ∈ szT₁ L T, ∃ w ∈ V₁, u y = c ∧ y * w ∈ X ∧
      ν * S w = c ^ (2 ^ (1 + 1) + 1) := by
    intro c
    obtain ⟨n, hn⟩ := h.exists_famPerm_eq hK hc hκ hμ hlam hν hU c
    obtain ⟨y₀, hy₀, w, hw, hx, hmap⟩ := h.map_conj_T₁_eq hK hc hμ hlam n.2
    have hspec := h.famPerm_spec hK hc hμ hlam n 0
    rw [h.fam_zero hK hc hμ, hn, hmap] at hspec
    have h1 := h.cent_eq_of_u_eq hK hc hμ hy₀ hy₀ rfl hw (one_mem V₁)
    rw [mul_one] at h1
    have huy : u y₀ = c := by
      have := h.u_eq_of_cent_eq hK hc hμ hy₀ (SzC1.szSec_mem hc c) (h1.symm.trans hspec)
      rwa [SzC1.szSec_u hc] at this
    refine ⟨y₀, hy₀, w, hw, huy, ?_, ?_⟩
    · have hxX := hX n n.2
      rw [hx] at hxX
      have := mul_mem hxX ht
      rwa [mul_assoc (y₀ * w) t t, h.t_mul_self, mul_one] at this
    · have hsq1 : (y₀ * w * t) ^ 2 = 1 := by rw [← hx, conj_pow, h.t_sq]; group
      have hyw : y₀ * w = w * y₀ := mem_centralizer_iff.mp (mem_inf.mp hw).2 y₀ hy₀
      have hyt : y₀ * t = t * y₀ := h.t_comm hy₀
      have e : (y₀ * w * t) ^ 2 = y₀ ^ 2 * (w * t) ^ 2 := by
        rw [sq, sq, sq]
        calc y₀ * w * t * (y₀ * w * t) = y₀ * w * (t * y₀) * w * t := by group
          _ = y₀ * w * (y₀ * t) * w * t := by rw [← hyt]
          _ = y₀ * (w * y₀) * t * w * t := by group
          _ = y₀ * (y₀ * w) * t * w * t := by rw [← hyw]
          _ = y₀ * y₀ * (w * t * (w * t)) := by group
      have hwt : (w * t) ^ 2 = (y₀ ^ 2)⁻¹ := by
        rw [e] at hsq1
        exact eq_inv_of_mul_eq_one_right hsq1
      have := hν' w hw
      rw [hwt, hc.v_inv_szA₁ h.ha hK' (hc.sq_mem_szA₁ h.ha hK' hy₀), (hc.sq hy₀).2, huy] at this
      exact this.symm
  choose yc hyc wc hwc huc hXc hSc using step2
  have hwcU : ∀ c, wc c ∈ U₁ := fun c => (mem_inf.mp (hwc c)).1
  have hcomm : ∀ c c', yc c' * wc c = wc c * yc c' := fun c c' =>
    mem_centralizer_iff.mp (mem_inf.mp (hwc c)).2 (yc c') (hyc c')
  set z := (yc κ * wc κ) * (yc 1 * wc 1) * (yc (κ + 1) * wc (κ + 1))⁻¹ with hz
  have hzX : z ∈ X := mul_mem (mul_mem (hXc κ) (hXc 1)) (inv_mem (hXc (κ + 1)))
  have hz' := SzCorner.mul_mul_inv_eq (y₁ := yc κ) (hcomm κ 1) (hcomm κ (κ + 1))
    (hcomm 1 (κ + 1)) (hcomm (κ + 1) (κ + 1))
  rw [← hz] at hz'
  set y' := yc κ * yc 1 * (yc (κ + 1))⁻¹ with hy'
  have hy'T : y' ∈ szT₁ L T := mul_mem (mul_mem (hyc κ) (hyc 1)) (inv_mem (hyc (κ + 1)))
  have hy'A : y' ∈ szA₁ (szT₁ L T) := by
    refine (hc.mem_szA₁_iff h.ha hK' hy'T).mpr ?_
    rw [hy', (hc.mul _ (mul_mem (hyc κ) (hyc 1)) _ (inv_mem (hyc (κ + 1)))).1,
      (hc.mul _ (hyc κ) _ (hyc 1)).1, (hc.inv (hyc (κ + 1))).1, huc, huc, huc]
    linear_combination (κ + 1) * h2
  have hwV₁ : wc κ * wc 1 * (wc (κ + 1))⁻¹ ∈ V₁ :=
    mul_mem (mul_mem (hwc κ) (hwc 1)) (inv_mem (hwc (κ + 1)))
  have hzV₁ : z ∈ V₁ := by
    rw [hz']
    exact mul_mem (h.V_le_V₁ (h.le hy'A)) hwV₁
  have hSz : ν * S z = κ ^ 4 + κ := by
    have hy'S : S y' = 0 := h.S_eq_zero_of_mem_sup hK hc (mem_sup_left hy'T)
    rw [hz', hSmul _ (h.T₁_le_U₁ hy'T) _ (mem_inf.mp hwV₁).1, hy'S, zero_add,
      hSmul _ (mul_mem (hwcU κ) (hwcU 1)) _ (inv_mem (hwcU (κ + 1))), hSmul _ (hwcU κ) _ (hwcU 1),
      hSinv _ (hwcU (κ + 1))]
    have e1 := hSc κ
    have e2 := hSc 1
    have e3 := hSc (κ + 1)
    norm_num at e1 e2 e3
    linear_combination e1 + e2 + e3 + (κ ^ 5 + 1 + 2 * κ ^ 4 + 5 * κ ^ 3 + 5 * κ ^ 2 + 2 * κ) * h2
  have hK8 : Fintype.card K = 8 := by rw [hK']; norm_num
  have hne01 : ∃ w : K, w ≠ 0 ∧ w ≠ 1 := by
    classical
    by_contra hne
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
      by_cases hw0 : w = 0
      · simp [hw0]
      · have hw1 : w = 1 := by
          by_contra hw1
          exact hne ⟨w, hw0, hw1⟩
        simp [hw1]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hK8] at h1
    have h2' : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  have hκ4 : κ ^ 4 + κ ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw1⟩ := hne01
    obtain ⟨m, hm⟩ := hκ w hw0
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0, pow_zero] at hm
        exact hw1 hm.symm
      · rw [zero_pow (Nat.pos_iff_ne_zero.mp hm0)] at hm
        exact hw0 hm.symm
    have hκ3 : κ ^ 3 = 1 := by
      have e : κ * (κ ^ 3 - 1) = 0 := by linear_combination h0 - κ * h2
      rcases mul_eq_zero.mp e with e1 | e1
      · exact absurd e1 hκ0
      · linear_combination e1
    have hw3 : w ^ 3 = 1 := by rw [← hm, ← pow_mul, mul_comm, pow_mul, hκ3, one_pow]
    have hw7 : w ^ 7 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one w hw0
      rwa [hK8] at this
    apply hw1
    calc w = (w ^ 3) ^ 2 * w := by rw [hw3, one_pow, one_mul]
      _ = w ^ 7 := by ring
      _ = 1 := hw7
  have hSz0 : S z ≠ 0 := fun h0 => hκ4 (by rw [← hSz, h0, mul_zero])
  have hiter : ∀ m : ℕ, ∃ w ∈ X, w ∈ V₁ ∧ S w = (κ ^ (2 ^ (1 + 1) + 1)) ^ m * S z := by
    intro m
    induction m with
    | zero => exact ⟨z, hzX, hzV₁, by rw [pow_zero, one_mul]⟩
    | succ m ih =>
      obtain ⟨w, hwX, hwV, hwS⟩ := ih
      refine ⟨d⁻¹ * w * d, hXd w hwX, h.conj_d_mem_V₁ hwV, ?_⟩
      have e := h.S_conj_d hK hc (mem_inf.mp hwV).1
      show v ((d⁻¹ * w * d * t * (d⁻¹ * w * d)⁻¹ * t⁻¹) ^ 2 ^ k) = _
      rw [e]
      show κ ^ (2 ^ (1 + 1) + 1) * S w = _
      rw [hwS, pow_succ]
      ring
  have hallS : ∀ s : K, ∃ w ∈ X, w ∈ V₁ ∧ S w = s := by
    intro s
    by_cases hs : s = 0
    · exact ⟨1, one_mem _, one_mem _, by rw [hS1, hs]⟩
    · obtain ⟨m, hm⟩ := hμg (s / S z) (div_ne_zero hs hSz0)
      obtain ⟨w, hwX, hwV, hwS⟩ := hiter m
      exact ⟨w, hwX, hwV, by rw [hwS, hm, div_mul_cancel₀ s hSz0]⟩
  have hV₁X : V₁ ≤ X := by
    intro w hw
    obtain ⟨w', hw'X, hw'V, hw'S⟩ := hallS (S w)
    have hU₁w := (mem_inf.mp hw).1
    have hU₁w' := (mem_inf.mp hw'V).1
    have h0 : S (w'⁻¹ * w) = 0 := by
      rw [hSmul _ (inv_mem hU₁w') _ hU₁w, hSinv _ hU₁w', hw'S]
      linear_combination S w * h2
    have hmV : w'⁻¹ * w ∈ V := h.mem_V_of_mem_V₁_of_mem_sup (mul_mem (inv_mem hw'V) hw)
      (h.mem_sup_of_S_eq_zero hK hc (mul_mem (inv_mem hU₁w') hU₁w) h0)
    have e : w = w' * (w'⁻¹ * w) := by group
    rw [e]
    exact mul_mem hw'X (hVX hmV)
  have hT₁X : szT₁ L T ≤ X := by
    intro y hy
    have hycX : yc (u y) ∈ X := by
      have := mul_mem (hXc (u y)) (inv_mem (hV₁X (hwc (u y))))
      rwa [mul_inv_cancel_right] at this
    have hA := hc.inv_mul_mem_szA₁_of_u_eq h.ha hK' (hyc (u y)) hy (huc (u y))
    have e : y = yc (u y) * ((yc (u y))⁻¹ * y) := by group
    rw [e]
    exact mul_mem hycX (hVX (h.le hA))
  rw [← h.sup_eq, hlam]
  exact sup_le (sup_le hT₁X hV₁X) (zpowers_le.mpr ht)

theorem not_two_dvd_index_normalizer
    (hf : f = 3) (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U)
    (hA : ∀ n ∈ normalizer (U : Set G), n ^ 2 = 1 →
      (∀ b ∈ szA₁ (szT₁ L T), n * b * n⁻¹ = b) → n ∈ U) :
    ¬ 2 ∣ (normalizer (U : Set G)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (U : Set G) with hNdef
  set X := closure {x : G | x ∈ U ∧ ∃ g : G, x = g * t * g⁻¹} with hXdef
  have hgen : ∀ g : G, g * t * g⁻¹ ∈ U → g * t * g⁻¹ ∈ X := fun g hg =>
    subset_closure ⟨hg, g, rfl⟩
  have hXU : X ≤ U := (closure_le U).mpr fun x hx => hx.1
  have hconjX : ∀ g : G, (∀ y : G, y * t * y⁻¹ ∈ U → g * (y * t * y⁻¹) * g⁻¹ ∈ U) →
      ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    have hle : X ≤ X.comap (MulAut.conj g).toMonoidHom := (closure_le _).mpr fun y hy => by
      obtain ⟨hyU, y', rfl⟩ := hy
      show g * (y' * t * y'⁻¹) * g⁻¹ ∈ X
      rw [show g * (y' * t * y'⁻¹) * g⁻¹ = (g * y') * t * (g * y')⁻¹ by group]
      refine hgen _ ?_
      rw [show (g * y') * t * (g * y')⁻¹ = g * (y' * t * y'⁻¹) * g⁻¹ by group]
      exact hg y' hyU
    exact hle hx
  have hXN : ∀ n ∈ N, n * t * n⁻¹ ∈ X := fun n hn =>
    hgen n ((mem_normalizer_iff.mp hn t).mp h.t_mem_U)
  have hXd : ∀ x ∈ X, d⁻¹ * x * d ∈ X := by
    intro x hx
    have := hconjX d⁻¹ (fun y hy => (mem_normalizer_iff.mp (inv_mem h.d_mem_normalizer_U) _).mp hy)
      x hx
    rwa [inv_inv] at this
  have hUX : U ≤ X := h.U_le_of_conj_mem hK hc hf hκ hμ hlam hν hU hXN hXd
  have hU2 : IsPGroup 2 (U.subgroupOf N) := h.isPGroup_U.comap_subtype
  obtain ⟨P₀, hP₀⟩ := hU2.exists_le_sylow
  set P : Subgroup G := (P₀ : Subgroup N).map N.subtype with hPdef
  have hP2 : IsPGroup 2 P := P₀.isPGroup'.map _
  have hUP : U ≤ P := fun x hx => ⟨⟨x, le_normalizer hx⟩, hP₀ (mem_subgroupOf.mpr hx), rfl⟩
  have hPN : P ≤ N := map_subtype_le _
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hSP : (S : Subgroup G) = P := by
    by_contra hne
    obtain ⟨g, hgS, hgP, hgnP⟩ := SzC1.exists_mem_normalizer_of_lt S.isPGroup' hPS hne
    have hg' : ∀ y : G, y * t * y⁻¹ ∈ U → g * (y * t * y⁻¹) * g⁻¹ ∈ U := by
      intro y hy
      have hP : g * (y * t * y⁻¹) * g⁻¹ ∈ P := (mem_normalizer_iff.mp hgP _).mp (hUP hy)
      rw [show g * (y * t * y⁻¹) * g⁻¹ = (g * y) * t * (g * y)⁻¹ by group] at hP ⊢
      have hU₁ := h.conj_mul_t_mem_U₁ hμ hlam hA (g * y) (hPN hP)
      have e : (g * y) * t * (g * y)⁻¹ = ((g * y) * t * (g * y)⁻¹ * t) * t := by
        rw [mul_assoc _ t t, h.t_mul_self, mul_one]
      rw [e]
      exact mul_mem (h.U₁_le hU₁) h.t_mem_U
    have hgN : g ∈ N := by
      have hgU : ∀ x ∈ U, g * x * g⁻¹ ∈ U := fun x hx => hXU (hconjX g hg' x (hUX hx))
      have := mem_normalizer_of_forall_inv_mul_mul_mem (H := U) (d := g⁻¹) fun x hx => by
        simpa using hgU x hx
      simpa using inv_mem this
    set Q : Subgroup G := P ⊔ zpowers g with hQ
    have hQ2 : IsPGroup 2 Q := S.isPGroup'.to_le (sup_le hPS (zpowers_le.mpr hgS))
    have hQN : Q ≤ N := sup_le hPN (zpowers_le.mpr hgN)
    have hQ2' : IsPGroup 2 (Q.subgroupOf N) := hQ2.comap_subtype
    have hPQ : (P₀ : Subgroup N) ≤ Q.subgroupOf N := fun x hx =>
      mem_subgroupOf.mpr (mem_sup_left ⟨x, hx, rfl⟩)
    have heq := P₀.is_maximal' hQ2' hPQ
    have hgQ : (⟨g, hgN⟩ : N) ∈ Q.subgroupOf N := mem_subgroupOf.mpr (mem_sup_right (mem_zpowers g))
    rw [heq] at hgQ
    exact hgnP ⟨⟨g, hgN⟩, hgQ, rfl⟩
  intro h2
  apply S.not_dvd_index
  rw [hSP]
  exact dvd_trans h2 (index_dvd_of_le hPN)

end Coords

end SzC1Stage

end CFSG.SeitzReduction.RankOne
