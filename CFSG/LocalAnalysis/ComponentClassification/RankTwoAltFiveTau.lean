module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveConn

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem comm_mul_left {y₁ y₂ b : G} (hy₁ : y₁ ∈ P) (hy₂ : y₂ ∈ P) (hb : b ∈ P) :
    y₁ * y₂ * b * (y₁ * y₂)⁻¹ * b⁻¹ = (y₁ * b * y₁⁻¹ * b⁻¹) * (y₂ * b * y₂⁻¹ * b⁻¹) := by
  have hc₂ := h.P_comm_mem_V₀ hP hPC hIIa hy₂ hb
  have hz := P_comm_V₀ hP hc₂ hy₁
  calc y₁ * y₂ * b * (y₁ * y₂)⁻¹ * b⁻¹ =
      y₁ * (y₂ * b * y₂⁻¹ * b⁻¹) * b * y₁⁻¹ * b⁻¹ := by group
    _ = (y₂ * b * y₂⁻¹ * b⁻¹) * y₁ * b * y₁⁻¹ * b⁻¹ := by rw [hz]
    _ = (y₂ * b * y₂⁻¹ * b⁻¹) * (y₁ * b * y₁⁻¹ * b⁻¹) := by group
    _ = (y₁ * b * y₁⁻¹ * b⁻¹) * (y₂ * b * y₂⁻¹ * b⁻¹) :=
      h.comm (h.V₀_le hc₂) (h.V₀_le (h.P_comm_mem_V₀ hP hPC hIIa hy₁ hb))

theorem comm_mul_right {y b₁ b₂ : G} (hy : y ∈ P) (hb₁ : b₁ ∈ P) (hb₂ : b₂ ∈ P) :
    y * (b₁ * b₂) * y⁻¹ * (b₁ * b₂)⁻¹ = (y * b₁ * y⁻¹ * b₁⁻¹) * (y * b₂ * y⁻¹ * b₂⁻¹) := by
  have hc₂ := h.P_comm_mem_V₀ hP hPC hIIa hy hb₂
  have hz := P_comm_V₀ hP hc₂ hb₁
  calc y * (b₁ * b₂) * y⁻¹ * (b₁ * b₂)⁻¹ =
      y * b₁ * y⁻¹ * (y * b₂ * y⁻¹ * b₂⁻¹) * b₁⁻¹ := by group
    _ = y * b₁ * y⁻¹ * (b₁⁻¹ * (b₁ * (y * b₂ * y⁻¹ * b₂⁻¹))) * b₁⁻¹ := by group
    _ = y * b₁ * y⁻¹ * (b₁⁻¹ * ((y * b₂ * y⁻¹ * b₂⁻¹) * b₁)) * b₁⁻¹ := by rw [hz]
    _ = (y * b₁ * y⁻¹ * b₁⁻¹) * (y * b₂ * y⁻¹ * b₂⁻¹) := by group

theorem exists_conj_eq_mul_of_tau (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {x : G} (hxS : x ∈ (S : Subgroup G)) (hxP : x ∉ P) (hx2 : x * x = 1)
    (hxV₀ : ∀ w ∈ V₀, x * w = w * x) {c : G} (hc : c ∈ V₀) :
    ∃ u ∈ P, u * x * u⁻¹ = x * c := by
  obtain ⟨-, -, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  obtain ⟨hVx, hV'x⟩ := hswap x hxS hxP
  have hxinv : x⁻¹ = x := by
    calc x⁻¹ = x⁻¹ * (x * x) := by rw [hx2, mul_one]
      _ = x := by group
  have hxV : ∀ y ∈ R ⊔ T, x * y * x⁻¹ ∈ V' := fun y hy => by
    rw [← hV'x] at hy
    exact (mem_rightConjugate_iff _ _ _).mp hy
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  have hcmem : ∀ v ∈ R ⊔ T, v * (x * v * x⁻¹) * v⁻¹ * (x * v * x⁻¹)⁻¹ ∈ V₀ := fun v hv =>
    h.P_comm_mem_V₀ hP hPC hIIa (hVP hv) (hV'P (hxV v hv))
  let φ : ↥(R ⊔ T) →* ↥V₀ :=
    { toFun := fun v => ⟨(v : G) * (x * v * x⁻¹) * (v : G)⁻¹ * (x * v * x⁻¹)⁻¹, hcmem v v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun v₁ v₂ => by
        apply Subtype.ext
        simp only [coe_mul]
        have hv₁ := hVP v₁.2
        have hv₂ := hVP v₂.2
        have ha₁ := hV'P (hxV _ v₁.2)
        have ha₂ := hV'P (hxV _ v₂.2)
        have e0 : x * ((v₁ : G) * v₂) * x⁻¹ = (x * v₁ * x⁻¹) * (x * v₂ * x⁻¹) := by group
        rw [e0, h.comm_mul_left hP hPC hIIa hv₁ hv₂ (mul_mem ha₁ ha₂),
          h.comm_mul_right hP hPC hIIa hv₁ ha₁ ha₂, h.comm_mul_right hP hPC hIIa hv₂ ha₁ ha₂]
        have hk := h.P_comm_mem_V₀ hP hPC hIIa hv₂ ha₁
        have hsym : x * ((v₂ : G) * (x * v₁ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹) * x⁻¹ =
            ((v₁ : G) * (x * v₂ * x⁻¹) * (v₁ : G)⁻¹ * (x * v₂ * x⁻¹)⁻¹)⁻¹ := by
          rw [show x * ((v₂ : G) * (x * v₁ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹) * x⁻¹ =
            (x * v₂ * x⁻¹) * ((x * x) * v₁ * (x * x)⁻¹) * (x * v₂ * x⁻¹)⁻¹ *
              ((x * x) * v₁ * (x * x)⁻¹)⁻¹ by group, hx2]
          group
        have hfix : x * ((v₂ : G) * (x * v₁ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹) * x⁻¹ =
            (v₂ : G) * (x * v₁ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹ := by
          rw [hxV₀ _ hk]
          group
        have key : ((v₁ : G) * (x * v₂ * x⁻¹) * (v₁ : G)⁻¹ * (x * v₂ * x⁻¹)⁻¹) *
            ((v₂ : G) * (x * v₁ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹) = 1 := by
          rw [← hfix, hsym, mul_inv_cancel]
        calc ((v₁ : G) * (x * v₁ * x⁻¹) * (v₁ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹) *
              ((v₁ : G) * (x * v₂ * x⁻¹) * (v₁ : G)⁻¹ * (x * v₂ * x⁻¹)⁻¹) *
            (((v₂ : G) * (x * v₁ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹) *
              ((v₂ : G) * (x * v₂ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₂ * x⁻¹)⁻¹)) =
            ((v₁ : G) * (x * v₁ * x⁻¹) * (v₁ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹) *
              (((v₁ : G) * (x * v₂ * x⁻¹) * (v₁ : G)⁻¹ * (x * v₂ * x⁻¹)⁻¹) *
                ((v₂ : G) * (x * v₁ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₁ * x⁻¹)⁻¹)) *
              ((v₂ : G) * (x * v₂ * x⁻¹) * (v₂ : G)⁻¹ * (x * v₂ * x⁻¹)⁻¹) := by group
          _ = _ := by rw [key, mul_one] }
  have hker : Nat.card φ.ker = 4 := by
    have h1 : φ.ker = V₀.subgroupOf (R ⊔ T) := by
      ext v
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro hv
        have h2 : (v : G) * (x * v * x⁻¹) * (v : G)⁻¹ * (x * v * x⁻¹)⁻¹ = 1 :=
          congrArg Subtype.val hv
        by_contra hv0
        have haV : x * v * x⁻¹ ∉ R ⊔ T := by
          intro haV
          apply hv0
          have h3 : x * v * x⁻¹ ∈ V₀ := hinf ▸ mem_inf.mpr ⟨haV, hxV v v.2⟩
          have hc' := hxV₀ _ h3
          have e : (v : G) = x * v * x⁻¹ := by
            calc (v : G) = x⁻¹ * (x * v * x⁻¹ * x) := by group
              _ = x⁻¹ * (x * (x * v * x⁻¹)) := by rw [← hc']
              _ = x * v * x⁻¹ := by group
          rw [e]
          exact h3
        exact hv0 (h.P_fixed hP hPC (hV'P (hxV v v.2)) haV v.2 (by
          calc x * ↑v * x⁻¹ * ↑v * (x * ↑v * x⁻¹)⁻¹ =
              (↑v * (x * ↑v * x⁻¹) * (↑v)⁻¹ * (x * ↑v * x⁻¹)⁻¹)⁻¹ * ↑v := by group
            _ = ↑v := by rw [h2, inv_one, one_mul]))
      · intro hv
        apply Subtype.ext
        change (v : G) * (x * v * x⁻¹) * (v : G)⁻¹ * (x * v * x⁻¹)⁻¹ = 1
        rw [← P_comm_V₀ hP hv (hV'P (hxV v v.2))]
        group
    rw [h1, ← h.card_V₀]
    exact Nat.card_congr (subgroupOfEquivOfLe h.V₀_le).toEquiv
  have hsurj : Function.Surjective φ := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, h.loc.card] at h1
    have h2 : Nat.card φ.range = 4 := by omega
    have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h2, h.card_V₀])
    exact MonoidHom.range_eq_top.mp htop
  obtain ⟨v, hv⟩ := hsurj ⟨c, hc⟩
  have hcv : (v : G) * (x * v * x⁻¹) * (v : G)⁻¹ * (x * v * x⁻¹)⁻¹ = c := congrArg Subtype.val hv
  refine ⟨(v : G) * (x * v * x⁻¹), mul_mem (hVP v.2) (hV'P (hxV v v.2)), ?_⟩
  have hxv' : x⁻¹ * v * x = x * v * x⁻¹ := by rw [hxinv]
  have hcc : c * c = 1 := h.mul_self (h.V₀_le hc)
  calc (v : G) * (x * v * x⁻¹) * x * ((v : G) * (x * v * x⁻¹))⁻¹ =
      (v : G) * x * (x⁻¹ * (x * v * x⁻¹) * x) * (x * v * x⁻¹)⁻¹ * (v : G)⁻¹ := by group
    _ = (v : G) * x * v * (x * v * x⁻¹)⁻¹ * (v : G)⁻¹ := by
        rw [show x⁻¹ * (x * ↑v * x⁻¹) * x = (v : G) by group]
    _ = x * (x⁻¹ * v * x) * v * (x * v * x⁻¹)⁻¹ * (v : G)⁻¹ := by group
    _ = x * (x * v * x⁻¹) * v * (x * v * x⁻¹)⁻¹ * (v : G)⁻¹ := by rw [hxv']
    _ = x * ((v : G) * (x * v * x⁻¹) * (v : G)⁻¹ * (x * v * x⁻¹)⁻¹)⁻¹ := by group
    _ = x * c := by rw [hcv, inv_eq_of_mul_eq_one_right hcc]

theorem sq_mem_centralizer_of_tau (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    (hτ : ∀ s ∈ (S : Subgroup G), ∀ w ∈ V₀, s * w = w * s) {E : Subgroup G}
    (hES : E ≤ S) (hEP : E ⊓ P ≤ V₀) {s : G} (hs : s ∈ (S : Subgroup G))
    (hsN : s ∈ normalizer (E : Set G)) : s * s ∈ centralizer (E : Set G) := by
  obtain ⟨hSN, hS128, -, -, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hrelPS : P.relIndex S = 2 := by
    have h1 := Subgroup.relIndex_mul_card P S
    rw [inf_eq_left.mpr hPS, hS128, hP64] at h1
    omega
  rw [mem_centralizer_iff]
  intro e he
  have hse : s * e * s⁻¹ ∈ E := (mem_normalizer_iff.mp hsN e).mp he
  by_cases heP : e ∈ P
  · have he0 : e ∈ V₀ := hEP (mem_inf.mpr ⟨he, heP⟩)
    have h1 := hτ s hs e he0
    calc e * (s * s) = (e * s) * s := (mul_assoc _ _ _).symm
      _ = (s * e) * s := by rw [h1]
      _ = s * (e * s) := mul_assoc _ _ _
      _ = s * (s * e) := by rw [h1]
      _ = (s * s) * e := (mul_assoc _ _ _).symm
  ·
    have hseP : s * e * s⁻¹ ∉ P := by
      intro h1
      apply heP
      have := (mem_normalizer_iff.mp (hSN (inv_mem hs)) _).mp h1
      rwa [show s⁻¹ * (s * e * s⁻¹) * s⁻¹⁻¹ = e by group] at this
    have hc : e⁻¹ * (s * e * s⁻¹) ∈ P := CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hrelPS
      (hES he) (hES hse) heP hseP
    have hc0 : e⁻¹ * (s * e * s⁻¹) ∈ V₀ := hEP (mem_inf.mpr ⟨mul_mem (inv_mem he) hse, hc⟩)
    obtain ⟨c, hcdef⟩ : ∃ c : G, e⁻¹ * (s * e * s⁻¹) = c := ⟨_, rfl⟩
    rw [hcdef] at hc0
    have hcc : c * c = 1 := h.mul_self (h.V₀_le hc0)
    have h1 : s * e * s⁻¹ = e * c := by rw [← hcdef]; group
    have hsc := hτ s hs c hc0
    have h2 : (s * s) * e * (s * s)⁻¹ = e := by
      calc (s * s) * e * (s * s)⁻¹ = s * (s * e * s⁻¹) * s⁻¹ := by group
        _ = s * (e * c) * s⁻¹ := by rw [h1]
        _ = (s * e * s⁻¹) * (s * c * s⁻¹) := by group
        _ = e * c * c := by rw [h1, hsc]; group
        _ = e := by rw [mul_assoc, hcc, mul_one]
    have h3 : (s * s) * e = e * (s * s) := by
      calc (s * s) * e = (s * s) * e * (s * s)⁻¹ * (s * s) := by group
        _ = e * (s * s) := by rw [h2]
    exact h3.symm

theorem false_of_tauType (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    (hτ : ∀ s ∈ (S : Subgroup G), ∀ w ∈ V₀, s * w = w * s) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNA := h.normalizer_le_sup_of_eps_one hP hε
  have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
  obtain ⟨z, hz, hz1, -⟩ := exists_ne_one_ne h.card_V₀ hV₀2 (one_mem V₀)
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hcls : ∀ y : G, y ^ 2 = 1 → y ≠ 1 → IsConj z y ∨ IsConj r₀ y := fun y hy2 hy1 =>
    h.isConj_or_isConj hIIa hP hPC hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv hz hz1
      hr₀ hr₀1 hy2 hy1
  have hPz : ∀ t ∈ P, t * t = 1 → IsConj z t → t ∈ V₀ := fun t ht ht2 hzt =>
    h.mem_V₀_of_isConj hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv hz hz1
      ht ht2 hzt
  have hzS : ∀ y ∈ (S : Subgroup G), z * y = y * z := fun y hy => (hτ y hy z hz).symm
  have hz2 : z * z = 1 := hV₀2 z hz
  have hV₀S : V₀ ≤ (S : Subgroup G) := (h.V₀_le.trans hVP).trans hPS
  obtain ⟨c, hcS, hcP⟩ := h.exists_conj_not_mem hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e
    hV'16 hinf hsup hV'inv S hPS hz hz1
  obtain ⟨x, hx⟩ : ∃ x : G, c⁻¹ * z * c = x := ⟨_, rfl⟩
  rw [hx] at hcS hcP
  have hzx : IsConj z x := isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hx⟩
  have hx2 : x * x = 1 := by
    rw [← hx]
    calc c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
      _ = 1 := by rw [hz2]; group
  have hxV₀ : ∀ w ∈ V₀, x * w = w * x := hτ x hcS
  obtain ⟨k, hxk, hCk⟩ := exists_conj_sylow_of_isConj S hzS hzx
  obtain ⟨v, hvV₀, hv1, hvk⟩ := h.exists_conj_inf_of_tau hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS hτ hz hz1 hcS hCk
  obtain ⟨w, hw, hwk⟩ : ∃ w ∈ V₀, k⁻¹ * w * k ∉ V₀ := by
    by_contra hno
    push Not at hno
    have hle : V₀.map (MulAut.conj k⁻¹).toMonoidHom ≤ V₀ := by
      rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hno y hy
    have heq := eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj k⁻¹).injective])
    have hkN : k⁻¹ ∈ normalizer (V₀ : Set G) := mem_normalizer_of_map_conj_eq heq
    have : x ∈ V₀ := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hkN) z).mp hz
      rwa [inv_inv, hxk] at h1
    exact hcP (hVP (h.V₀_le this))
  have hw1 : w ≠ 1 := fun he => hwk (by rw [he]; simp)
  have hvw : v ≠ w := fun he => hwk (he ▸ hvk)
  have hxinv : x⁻¹ = x := by
    calc x⁻¹ = x⁻¹ * (x * x) := by rw [hx2, mul_one]
      _ = x := by group
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2)
    (fun he => hcP (he ▸ one_mem P))
  set E := V₀ ⊔ zpowers x with hEdef
  have hV₀Nx : V₀ ≤ normalizer ((zpowers x : Subgroup G) : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (show Commute x a from hxV₀ a ha) i)).eq)
  have hEcases : ∀ e ∈ E, e ∈ V₀ ∨ x * e ∈ V₀ := by
    intro e he
    have he' : e ∈ ((E : Subgroup G) : Set G) := he
    rw [hEdef, coe_mul_of_left_le_normalizer_right _ _ hV₀Nx] at he'
    obtain ⟨a, ha, y, hy, hay⟩ := he'
    have hay' : a * y = e := hay
    rcases eq_one_or_eq_of_mem_zpowers hxo hy with h1 | h1
    · left
      rw [← hay', h1, mul_one]
      exact ha
    · right
      rw [← hay', h1, ← mul_assoc, hxV₀ a ha, mul_assoc, hx2, mul_one]
      exact ha
  have hES : E ≤ (S : Subgroup G) := sup_le hV₀S (zpowers_le.mpr hcS)
  have hEC : E ≤ centralizer ({x} : Set G) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.mpr (hxV₀ a ha).symm)
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hΩE : ∀ e ∈ E, e ≠ 1 → IsConj z e := by
    intro e he he1
    rcases hEcases e he with h1 | h1
    · exact h.isConj_of_mem_V₀ hz hz1 h1 he1
    · have he2 : e = x * (x * e) := by
        rw [← mul_assoc, hx2, one_mul]
      by_cases ha1 : x * e = 1
      · rw [he2, ha1, mul_one]
        exact hzx
      · rw [he2]
        refine h.isConj_mul_of_commute hNA hz hz1 hr₀ hcls hzx (h.isConj_of_mem_V₀ hz hz1 h1 ha1)
          (hxV₀ _ h1) ?_
        intro hxe
        exact hcP (hVP (h.V₀_le (hxe ▸ h1)))
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    rcases hEcases e he with h1 | h1
    · exact hV₀2 e h1
    · have he2 : e = x * (x * e) := by
        rw [← mul_assoc, hx2, one_mul]
      have hc' := hxV₀ _ h1
      rw [he2]
      calc x * (x * e) * (x * (x * e)) = x * ((x * e) * x) * (x * e) := by group
        _ = x * (x * (x * e)) * (x * e) := by rw [← hc']
        _ = (x * x) * ((x * e) * (x * e)) := by group
        _ = 1 := by rw [hx2, hV₀2 _ h1, one_mul]
  obtain ⟨u₁, hu₁P, hu₁⟩ := h.exists_conj_eq_mul_of_tau hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS hcS hcP hx2 hxV₀ hvV₀
  have hu₁V₀ : ∀ a ∈ V₀, u₁ * a * u₁⁻¹ = a := fun a ha => by
    rw [P_comm_V₀ hP ha hu₁P]; group
  have hwS : w ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    mem_inf.mpr ⟨hV₀S hw, mem_centralizer_singleton_iff.mpr (hxV₀ w hw).symm⟩
  have hx'S : k⁻¹ * w * k ∈ (S : Subgroup G) := hCk w hwS
  have hx'2 : k⁻¹ * w * k * (k⁻¹ * w * k) = 1 := by
    calc k⁻¹ * w * k * (k⁻¹ * w * k) = k⁻¹ * (w * w) * k := by group
      _ = 1 := by rw [hV₀2 w hw]; group
  have hx'P : k⁻¹ * w * k ∉ P := fun hm => hwk (hPz _ hm hx'2
    ((h.isConj_of_mem_V₀ hz hz1 hw hw1).trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)))
  have hzk : k⁻¹ * x * k = z := by rw [← hxk]; group
  obtain ⟨u₀, hu₀P, hu₀⟩ := h.exists_conj_eq_mul_of_tau hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS hx'S hx'P hx'2 (hτ _ hx'S) hz
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : G, k * u₀ * k⁻¹ = n₂ := ⟨_, rfl⟩
  have hn₂w : n₂ * w * n₂⁻¹ = w * x := by
    rw [← hn₂]
    calc k * u₀ * k⁻¹ * w * (k * u₀ * k⁻¹)⁻¹ = k * (u₀ * (k⁻¹ * w * k) * u₀⁻¹) * k⁻¹ := by group
      _ = k * (k⁻¹ * w * k * z) * k⁻¹ := by rw [hu₀]
      _ = w * (k * z * k⁻¹) := by group
      _ = w * x := by rw [hxk]
  have hn₂fix : ∀ y, k⁻¹ * y * k ∈ V₀ → n₂ * y * n₂⁻¹ = y := by
    intro y hy
    rw [← hn₂]
    have e := P_comm_V₀ hP hy hu₀P
    calc k * u₀ * k⁻¹ * y * (k * u₀ * k⁻¹)⁻¹ = k * (u₀ * (k⁻¹ * y * k)) * u₀⁻¹ * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * u₀) * u₀⁻¹ * k⁻¹ := by rw [e]
      _ = y := by group
  have hn₂x : n₂ * x * n₂⁻¹ = x := hn₂fix x (by rw [hzk]; exact hz)
  have hn₂v : n₂ * v * n₂⁻¹ = v := hn₂fix v hvk
  obtain ⟨g', hg'⟩ : ∃ g' : G, u₁ * n₂ = g' := ⟨_, rfl⟩
  have hconj : ∀ y, g' * y * g'⁻¹ = u₁ * (n₂ * y * n₂⁻¹) * u₁⁻¹ := fun y => by rw [← hg']; group
  have hgv : g' * v * g'⁻¹ = v := by rw [hconj, hn₂v, hu₁V₀ v hvV₀]
  have hgx : g' * x * g'⁻¹ = x * v := by rw [hconj, hn₂x, hu₁]
  have hgw : g' * w * g'⁻¹ = w * (x * v) := by
    rw [hconj, hn₂w, show u₁ * (w * x) * u₁⁻¹ = (u₁ * w * u₁⁻¹) * (u₁ * x * u₁⁻¹) by group,
      hu₁V₀ w hw, hu₁]
  have hxv : x * v = v * x := hxV₀ v hvV₀
  have hvv : v * v = 1 := hV₀2 v hvV₀
  have hg2v : (g' * g') * v * (g' * g')⁻¹ = v := by
    rw [show (g' * g') * v * (g' * g')⁻¹ = g' * (g' * v * g'⁻¹) * g'⁻¹ by group, hgv, hgv]
  have hg2x : (g' * g') * x * (g' * g')⁻¹ = x := by
    rw [show (g' * g') * x * (g' * g')⁻¹ = g' * (g' * x * g'⁻¹) * g'⁻¹ by group, hgx,
      show g' * (x * v) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * v * g'⁻¹) by group, hgx, hgv,
      mul_assoc, hvv, mul_one]
  have hg2w : (g' * g') * w * (g' * g')⁻¹ = w * v := by
    rw [show (g' * g') * w * (g' * g')⁻¹ = g' * (g' * w * g'⁻¹) * g'⁻¹ by group, hgw,
      show g' * (w * (x * v)) * g'⁻¹ =
        (g' * w * g'⁻¹) * ((g' * x * g'⁻¹) * (g' * v * g'⁻¹)) by group, hgw, hgx, hgv]
    calc w * (x * v) * (x * v * v) = w * (x * (v * x) * (v * v)) := by group
      _ = w * (x * (x * v) * 1) := by rw [← hxv, hvv]
      _ = w * ((x * x) * v) := by group
      _ = w * v := by rw [hx2, one_mul]
  have hvE : v ∈ E := mem_sup_left hvV₀
  have hwE : w ∈ E := mem_sup_left hw
  have hxE : x ∈ E := mem_sup_right (mem_zpowers x)
  have hV₀4 : ∀ a ∈ V₀, a = 1 ∨ a = v ∨ a = w ∨ a = v * w := fun a ha =>
    mem_four h.card_V₀ hV₀2 hvV₀ hw hv1 hw1 hvw ha
  have hgN : g' ∈ normalizer (E : Set G) := by
    refine mem_normalizer_of_map_conj_le ?_
    rw [hEdef, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ (zpowers_le.mpr ?_)
    · rintro _ ⟨a, ha, rfl⟩
      change g' * a * g'⁻¹ ∈ E
      rcases hV₀4 a ha with rfl | rfl | rfl | rfl
      · rw [mul_one, mul_inv_cancel]; exact one_mem _
      · rw [hgv]; exact hvE
      · rw [hgw]; exact mul_mem hwE (mul_mem hxE hvE)
      · rw [show g' * (v * w) * g'⁻¹ = (g' * v * g'⁻¹) * (g' * w * g'⁻¹) by group, hgv, hgw]
        exact mul_mem hvE (mul_mem hwE (mul_mem hxE hvE))
    · change g' * x * g'⁻¹ ∈ E
      rw [hgx]
      exact mul_mem hxE hvE
  obtain ⟨g4, hg4⟩ : ∃ g4 : G, (g' * g') * (g' * g') = g4 := ⟨_, rfl⟩
  have hfix4 : ∀ y, (g' * g') * y * (g' * g')⁻¹ = y → g4 * y * g4⁻¹ = y := fun y hy => by
    rw [← hg4, show (g' * g') * (g' * g') * y * ((g' * g') * (g' * g'))⁻¹ =
      (g' * g') * ((g' * g') * y * (g' * g')⁻¹) * (g' * g')⁻¹ by group, hy, hy]
  have hC4 : ∀ y, g4 * y * g4⁻¹ = y → y ∈ centralizer ({g4} : Set G) := fun y hy => by
    rw [mem_centralizer_singleton_iff]
    calc y * g4 = g4 * y * g4⁻¹ * g4 := by rw [hy]
      _ = g4 * y := by group
  have hEg4 : E ≤ centralizer ({g4} : Set G) := by
    refine sup_le ?_ (zpowers_le.mpr (hC4 x (hfix4 x (by rw [hg2x]))))
    intro a ha
    have hv4 := hC4 v (hfix4 v hg2v)
    have hw4 : w ∈ centralizer ({g4} : Set G) := by
      refine hC4 w ?_
      rw [← hg4, show (g' * g') * (g' * g') * w * ((g' * g') * (g' * g'))⁻¹ =
        (g' * g') * ((g' * g') * w * (g' * g')⁻¹) * (g' * g')⁻¹ by group, hg2w,
        show (g' * g') * (w * v) * (g' * g')⁻¹ =
          ((g' * g') * w * (g' * g')⁻¹) * ((g' * g') * v * (g' * g')⁻¹) by group, hg2w, hg2v,
        mul_assoc, hvv, mul_one]
    rcases hV₀4 a ha with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hv4
    · exact hw4
    · exact mul_mem hv4 hw4
  have hg4C : g4 ∈ centralizer (E : Set G) := mem_centralizer_iff.mpr fun e he =>
    mem_centralizer_singleton_iff.mp (hEg4 he)
  obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g').ne'
  obtain ⟨i, hi⟩ := hm
  set g₂ := g' ^ m with hg₂def
  have hg₂N : g₂ ∈ normalizer (E : Set G) := pow_mem hgN m
  have hg₂sq : (g₂ * g₂) * w * (g₂ * g₂)⁻¹ = w * v := by
    have e0 : g' ^ 4 = g' * g' * (g' * g') := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    have e1 : g₂ * g₂ = g4 ^ i * (g' * g') := by
      rw [hg₂def, ← pow_add, hi, ← hg4, show 2 * i + 1 + (2 * i + 1) = 4 * i + 2 by ring,
        pow_add, pow_mul, e0, sq]
    have hwv : w * v ∈ E := mul_mem hwE hvE
    have e2 : g4 ^ i * (w * v) * (g4 ^ i)⁻¹ = w * v := by
      have hc := mem_centralizer_iff.mp (pow_mem hg4C i) _ hwv
      rw [← hc]; group
    rw [e1, show g4 ^ i * (g' * g') * w * (g4 ^ i * (g' * g'))⁻¹ =
      g4 ^ i * ((g' * g') * w * (g' * g')⁻¹) * (g4 ^ i)⁻¹ by group, hg2w, e2]
  have hg₂2 : g₂ ^ 2 ^ a = 1 := by
    rw [hg₂def, ← pow_mul, mul_comm, ← hgm, pow_orderOf_eq_one]
  have hEp : IsPGroup 2 E := S.isPGroup'.to_le hES
  have hZp : IsPGroup 2 (zpowers g₂) := by
    obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg₂2)
    exact IsPGroup.of_card (n := t) (by rw [Nat.card_zpowers, ht])
  have hZN : zpowers g₂ ≤ normalizer (E : Set G) := zpowers_le.mpr hg₂N
  have hHp : IsPGroup 2 (zpowers g₂ ⊔ E : Subgroup G) := by
    obtain ⟨n₁, hn₁⟩ := hZp.exists_card_eq
    obtain ⟨n₂', hn₂'⟩ := hEp.exists_card_eq
    have h1 := card_sup_mul_card_inf_of_le hZN
    rw [hn₁, hn₂', ← pow_add] at h1
    have h2 : Nat.card (zpowers g₂ ⊔ E : Subgroup G) ∣ 2 ^ (n₁ + n₂') := Dvd.intro _ h1
    obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact IsPGroup.of_card ht
  obtain ⟨S'', hS''⟩ := hHp.exists_le_sylow
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq G S S''
  have hmem'' : ∀ y ∈ (S'' : Subgroup G), j⁻¹ * y * j ∈ (S : Subgroup G) := by
    intro y hy
    rw [← hj, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hy
  have hES'' : E ≤ (S'' : Subgroup G) := le_sup_right.trans hS''
  have hg₂S'' : g₂ ∈ (S'' : Subgroup G) := hS'' (mem_sup_left (mem_zpowers g₂))
  set E' := E.map (MulAut.conj j⁻¹).toMonoidHom with hE'def
  have hmemE' : ∀ y, y ∈ E' ↔ j * y * j⁻¹ ∈ E := by
    intro y
    rw [hE'def, mem_map_conj_iff, inv_inv]
  have hE'S : E' ≤ (S : Subgroup G) := by
    intro y hy
    rw [hmemE'] at hy
    have := hmem'' _ (hES'' hy)
    rwa [show j⁻¹ * (j * y * j⁻¹) * j = y by group] at this
  have hE'P : E' ⊓ P ≤ V₀ := by
    intro y hy
    obtain ⟨hyE, hyP⟩ := mem_inf.mp hy
    rw [hmemE'] at hyE
    by_cases hy1 : y = 1
    · rw [hy1]; exact one_mem _
    have he1 : j * y * j⁻¹ ≠ 1 := fun he => hy1 (by
      calc y = j⁻¹ * (j * y * j⁻¹) * j := by group
        _ = 1 := by rw [he]; group)
    refine hPz y hyP ?_ ((hΩE _ hyE he1).trans (isConj_iff.mpr ⟨j⁻¹, by group⟩))
    have := hE2 _ hyE
    calc y * y = j⁻¹ * ((j * y * j⁻¹) * (j * y * j⁻¹)) * j := by group
      _ = 1 := by rw [this]; group
  have hsS : j⁻¹ * g₂ * j ∈ (S : Subgroup G) := hmem'' _ hg₂S''
  have hsN : j⁻¹ * g₂ * j ∈ normalizer (E' : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [hmemE', hmemE', show j * (j⁻¹ * g₂ * j * y * (j⁻¹ * g₂ * j)⁻¹) * j⁻¹ =
      g₂ * (j * y * j⁻¹) * g₂⁻¹ by group]
    exact mem_normalizer_iff.mp hg₂N _
  have hsq := h.sq_mem_centralizer_of_tau hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf
    hsup hV'inv S hPS hτ hE'S hE'P hsS hsN
  have hwE' : j⁻¹ * w * j ∈ E' := by
    rw [hmemE', show j * (j⁻¹ * w * j) * j⁻¹ = w by group]
    exact hwE
  have hc := mem_centralizer_iff.mp hsq _ hwE'
  have hc' : (g₂ * g₂) * w * (g₂ * g₂)⁻¹ = w := by
    have e1 : j⁻¹ * w * j * (j⁻¹ * g₂ * j * (j⁻¹ * g₂ * j)) =
        j⁻¹ * (w * (g₂ * g₂)) * j := by group
    have e2 : j⁻¹ * g₂ * j * (j⁻¹ * g₂ * j) * (j⁻¹ * w * j) =
        j⁻¹ * ((g₂ * g₂) * w) * j := by group
    rw [e1, e2] at hc
    have hc2 : w * (g₂ * g₂) = (g₂ * g₂) * w := by
      have := congrArg (fun t => j * t * j⁻¹) hc
      simpa [mul_assoc] using this
    calc (g₂ * g₂) * w * (g₂ * g₂)⁻¹ = w * (g₂ * g₂) * (g₂ * g₂)⁻¹ := by rw [hc2]
      _ = w := by group
  rw [hg₂sq] at hc'
  exact hv1 (by
    calc v = w⁻¹ * (w * v) := by group
      _ = 1 := by rw [hc', inv_mul_cancel])

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
