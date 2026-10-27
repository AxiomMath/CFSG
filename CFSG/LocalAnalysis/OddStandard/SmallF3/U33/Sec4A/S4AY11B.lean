module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem m11_comm_of_inverting {ρ a w : G} (hρ3 : ρ ^ 3 = 1) (haρ : a * ρ * a⁻¹ = ρ⁻¹)
    (haw : a * w = w * a) (haw' : a * (ρ * w * ρ⁻¹) = (ρ * w * ρ⁻¹) * a) : ρ * w = w * ρ := by
  have haρ1 : a * ρ = ρ⁻¹ * a := mul_inv_eq_iff_eq_mul.mp haρ
  have haρ2 : a * ρ⁻¹ = ρ * a := by
    have : a * ρ⁻¹ * a⁻¹ = ρ := by
      calc a * ρ⁻¹ * a⁻¹ = (a * ρ * a⁻¹)⁻¹ := by group
        _ = ρ := by rw [haρ, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp this
  have h1 : ρ⁻¹ * w * ρ * a = ρ * w * ρ⁻¹ * a := by
    calc ρ⁻¹ * w * ρ * a = ρ⁻¹ * w * (ρ * a) := by group
      _ = ρ⁻¹ * w * (a * ρ⁻¹) := by rw [haρ2]
      _ = ρ⁻¹ * (w * a) * ρ⁻¹ := by group
      _ = ρ⁻¹ * (a * w) * ρ⁻¹ := by rw [haw]
      _ = (ρ⁻¹ * a) * w * ρ⁻¹ := by group
      _ = (a * ρ) * w * ρ⁻¹ := by rw [haρ1]
      _ = a * (ρ * w * ρ⁻¹) := by group
      _ = ρ * w * ρ⁻¹ * a := haw'
  have h2 : ρ⁻¹ * w * ρ = ρ * w * ρ⁻¹ := mul_right_cancel h1
  have hρ2 : ρ * ρ * ρ = 1 := by
    have := hρ3
    rwa [pow_succ, pow_two] at this
  have a1 : ρ * ρ = ρ⁻¹ := eq_inv_of_mul_eq_one_left hρ2
  have a2 : ρ⁻¹ * ρ⁻¹ = ρ := by rw [← mul_inv_rev, a1, inv_inv]
  have h3 : w = ρ⁻¹ * w * ρ := by
    calc w = ρ * (ρ⁻¹ * w * ρ) * ρ⁻¹ := by group
      _ = ρ * (ρ * w * ρ⁻¹) * ρ⁻¹ := by rw [h2]
      _ = (ρ * ρ) * w * (ρ⁻¹ * ρ⁻¹) := by group
      _ = ρ⁻¹ * w * ρ := by rw [a1, a2]
  calc ρ * w = ρ * (ρ⁻¹ * w * ρ) := by rw [← h3]
    _ = w * ρ := by group

theorem m11_eq_bot_of_inverting_centralizes (X : Subgroup G) {ρ a : G}
    (hρX : ∀ x ∈ X, ρ * x * ρ⁻¹ ∈ X) (hρ3 : ρ ^ 3 = 1) (haρ : a * ρ * a⁻¹ = ρ⁻¹)
    (hfix : ∀ x ∈ X, ρ * x = x * ρ → x = 1) (hcent : ∀ x ∈ X, a * x = x * a) : X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact hfix x hx (m11_comm_of_inverting hρ3 haρ (hcent x hx) (hcent _ (hρX x hx)))

variable [Finite G]

theorem m11_card_cent_inv (Y : Subgroup G) (hY16 : Nat.card Y = 16)
    (hY2 : ∀ y ∈ Y, y * y = 1) (hYc : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y)
    {ρ a : G} (hρY : ∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y) (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    (hρ3 : ρ ^ 3 = 1) (ha2 : a * a = 1) (haρ : a * ρ * a⁻¹ = ρ⁻¹)
    (hfix : ∀ y ∈ Y, ρ * y = y * ρ → y = 1) :
    Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) = 4 := by
  have hCa : ∀ c ∈ Y ⊓ centralizer ({a} : Set G), c * a = a * c := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
  have hCY : ∀ c ∈ Y ⊓ centralizer ({a} : Set G), c ∈ Y := fun c hc => (Subgroup.mem_inf.mp hc).1
  let nm : ↥Y →* ↥Y := MonoidHom.mk'
    (fun v => ⟨(v : G) * (a * (v : G) * a⁻¹), Subgroup.mul_mem _ v.2 (haY _ v.2)⟩) (fun u v => by
      apply Subtype.ext
      have hc : (a * (u : G) * a⁻¹) * (v : G) = (v : G) * (a * (u : G) * a⁻¹) :=
        hYc _ (haY _ u.2) _ v.2
      show (u : G) * (v : G) * (a * ((u : G) * (v : G)) * a⁻¹) =
        (u : G) * (a * (u : G) * a⁻¹) * ((v : G) * (a * (v : G) * a⁻¹))
      calc (u : G) * (v : G) * (a * ((u : G) * (v : G)) * a⁻¹)
          = (u : G) * ((v : G) * (a * (u : G) * a⁻¹)) * (a * (v : G) * a⁻¹) := by group
        _ = (u : G) * ((a * (u : G) * a⁻¹) * (v : G)) * (a * (v : G) * a⁻¹) := by rw [hc]
        _ = (u : G) * (a * (u : G) * a⁻¹) * ((v : G) * (a * (v : G) * a⁻¹)) := by group)
  have hker : nm.ker = (Y ⊓ centralizer ({a} : Set G)).subgroupOf Y := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 : (v : G) * (a * (v : G) * a⁻¹) = 1 := congrArg Subtype.val h1
      refine ⟨v.2, ?_⟩
      have h3 : a * (v : G) * a⁻¹ = (v : G)⁻¹ := eq_inv_of_mul_eq_one_right h2
      have h4 : (v : G)⁻¹ = (v : G) := inv_eq_of_mul_eq_one_right (hY2 _ v.2)
      exact (mul_inv_eq_iff_eq_mul.mp (h3.trans h4)).symm
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      show (v : G) * (a * (v : G) * a⁻¹) = 1
      rw [n4_conj_eq_of_comm h1]
      exact hY2 _ v.2
  have hrange : nm.range ≤ (Y ⊓ centralizer ({a} : Set G)).subgroupOf Y := by
    rintro _ ⟨v, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(nm v).2, ?_⟩
    show (v : G) * (a * (v : G) * a⁻¹) * a = a * ((v : G) * (a * (v : G) * a⁻¹))
    have hc : (v : G) * (a * (v : G) * a⁻¹) = (a * (v : G) * a⁻¹) * (v : G) :=
      hYc _ v.2 _ (haY _ v.2)
    have key : a * ((v : G) * (a * (v : G) * a⁻¹)) * a⁻¹ = (v : G) * (a * (v : G) * a⁻¹) := by
      calc a * ((v : G) * (a * (v : G) * a⁻¹)) * a⁻¹
          = (a * (v : G) * a⁻¹) * ((a * a) * (v : G) * (a * a)⁻¹) := by group
        _ = (a * (v : G) * a⁻¹) * (v : G) := by rw [ha2]; group
        _ = (v : G) * (a * (v : G) * a⁻¹) := hc.symm
    exact (mul_inv_eq_iff_eq_mul.mp key).symm
  have hsub : Nat.card ↥((Y ⊓ centralizer ({a} : Set G)).subgroupOf Y) =
      Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left)).toEquiv
  have hcardker : Nat.card nm.ker = Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) := by
    rw [hker, hsub]
  have hcardrange : Nat.card nm.range ≤ Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) := by
    have := Subgroup.card_le_of_le hrange
    rwa [hsub] at this
  have hlow := card_ker_mul_card_range nm
  rw [hY16] at hlow
  have hupper : Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) *
      Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) ≤ 16 := by
    let Φ : ↥(Y ⊓ centralizer ({a} : Set G)) × ↥(Y ⊓ centralizer ({a} : Set G)) → ↥Y :=
      fun p => ⟨(p.1 : G) * (ρ * (p.2 : G) * ρ⁻¹),
        Subgroup.mul_mem _ (hCY _ p.1.2) (hρY _ (hCY _ p.2.2))⟩
    have hΦ : Function.Injective Φ := by
      rintro ⟨c₁, c₁'⟩ ⟨c₂, c₂'⟩ hEq
      have hEq' : (c₁ : G) * (ρ * (c₁' : G) * ρ⁻¹) = (c₂ : G) * (ρ * (c₂' : G) * ρ⁻¹) :=
        congrArg Subtype.val hEq
      have hu : (c₂ : G)⁻¹ * (c₁ : G) = ρ * ((c₂' : G) * (c₁' : G)⁻¹) * ρ⁻¹ := by
        calc (c₂ : G)⁻¹ * (c₁ : G)
            = ((c₂ : G)⁻¹ * ((c₁ : G) * (ρ * (c₁' : G) * ρ⁻¹))) * (ρ * (c₁' : G) * ρ⁻¹)⁻¹ := by
              group
          _ = ((c₂ : G)⁻¹ * ((c₂ : G) * (ρ * (c₂' : G) * ρ⁻¹))) * (ρ * (c₁' : G) * ρ⁻¹)⁻¹ := by
              rw [hEq']
          _ = ρ * ((c₂' : G) * (c₁' : G)⁻¹) * ρ⁻¹ := by group
      have huC : (c₂ : G)⁻¹ * (c₁ : G) ∈ Y ⊓ centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ c₂.2) c₁.2
      have hwC : (c₂' : G) * (c₁' : G)⁻¹ ∈ Y ⊓ centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ c₂'.2 (Subgroup.inv_mem _ c₁'.2)
      have hw : ρ * ((c₂' : G) * (c₁' : G)⁻¹) = ((c₂' : G) * (c₁' : G)⁻¹) * ρ := by
        refine m11_comm_of_inverting hρ3 haρ (hCa _ hwC).symm ?_
        rw [← hu]
        exact (hCa _ huC).symm
      have hw1 : (c₂' : G) * (c₁' : G)⁻¹ = 1 := hfix _ (hCY _ hwC) hw
      have hu1 : (c₂ : G)⁻¹ * (c₁ : G) = 1 := by rw [hu, hw1]; group
      have e1 : (c₁ : G) = (c₂ : G) := (inv_mul_eq_one.mp hu1).symm
      have e2 : (c₁' : G) = (c₂' : G) := (mul_inv_eq_one.mp hw1).symm
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
    have := Nat.card_le_card_of_injective Φ hΦ
    rwa [Nat.card_prod, hY16] at this
  rw [hcardker] at hlow
  have hc1 := Nat.mul_le_mul_left (Nat.card ↥(Y ⊓ centralizer ({a} : Set G))) hcardrange
  have hc2 : 16 ≤ Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) *
      Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) := by
    rw [← hlow]
    exact hc1
  have hle : Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) ≤ 4 := by nlinarith
  have hge : 4 ≤ Nat.card ↥(Y ⊓ centralizer ({a} : Set G)) := by nlinarith
  omega

end Abstract

section Y11B

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_fix_R (h : L41GPh8 t L S x₁ x₂ lam rho) {x : G} (hx : x ∈ l41R t x₁ x₂ rho)
    (hxρ : rho * x = x * rho) : x = 1 := by
  have : x ∈ l41R t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxρ.symm⟩
  rw [h.rfacts.cent_rho, Subgroup.mem_bot] at this
  exact this

theorem m11_rho_conj_R (h : L41GPh8 t L S x₁ x₂ lam rho) {x : G} (hx : x ∈ l41R t x₁ x₂ rho) :
    rho * x * rho⁻¹ ∈ l41R t x₁ x₂ rho :=
  (Subgroup.mem_normalizer_iff.mp (n4_mem_normalizer_R h).1 x).mp hx

theorem m11_rho_conj_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {x : G} (hx : x ∈ l41Y t x₁ x₂ rho) :
    rho * x * rho⁻¹ ∈ l41Y t x₁ x₂ rho :=
  m11_conj_Y h (n4_mem_normalizer_R h.toL41GPh8).1 hx

theorem m11_rho_conj_F2 (h : L41GPh8 t L S x₁ x₂ lam rho) {x : G} (hx : x ∈ fourGrp x₁ x₂) :
    rho * x * rho⁻¹ ∈ fourGrp x₁ x₂ :=
  h.normalizerFacts.normal_F2.2 rho (n4_rho_mem_N h.toL41GPh1) x hx

theorem m11_lamt_sq (h : L41GPh5 t L S x₁ x₂ lam rho) : lam * t * (lam * t) = 1 := by
  have hl2 : lam * lam = 1 := n4_lam_sq h.toCtx0
  have htl : t * lam = lam * t := m13_t_comm_L h (generators_mem_L h.toCtx0).2.2
  calc lam * t * (lam * t) = lam * (t * lam) * t := by group
    _ = lam * (lam * t) * t := by rw [htl]
    _ = (lam * lam) * (t * t) := by group
    _ = 1 := by rw [hl2, t_mul_self h.hyp, one_mul]

theorem m11_lamt_rho (h : L41GPh5 t L S x₁ x₂ lam rho) :
    lam * t * rho * (lam * t)⁻¹ = rho⁻¹ := by
  have htc : ∀ g ∈ L, t * g = g * t := fun g hg =>
    n4_zpowers_t_comm h (Subgroup.mem_zpowers t) hg
  calc lam * t * rho * (lam * t)⁻¹ = lam * (t * rho * t⁻¹) * lam⁻¹ := by group
    _ = lam * rho * lam⁻¹ := by rw [n4_conj_eq_of_comm (htc rho h.rho_mem).symm]
    _ = rho⁻¹ := h.lam_rho

theorem m11_card_cent_lam (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Nat.card ↥(l41Y t x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) = 4 := by
  obtain ⟨-, hlamN, -⟩ := n4_mem_normalizer_R h.toL41GPh8
  exact m11_card_cent_inv (l41Y t x₁ x₂ rho) (m11_card_Y h)
    (fun y hy => ((m11_mem_Y_iff h).mp hy).2) (fun y hy y' hy' => m11_comm_Y h hy hy')
    (fun y hy => m11_rho_conj_Y h hy) (fun y hy => m11_conj_Y h hlamN hy)
    (n4_rho_cube h.toCtx0) (n4_lam_sq h.toCtx0) h.lam_rho
    (fun y hy hyρ => m11_fix_R h.toL41GPh8 (m13_Y_le_R t x₁ x₂ rho hy) hyρ)

theorem m11_card_cent_lamt (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Nat.card ↥(l41Y t x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) = 4 := by
  obtain ⟨-, hlamN, htN⟩ := n4_mem_normalizer_R h.toL41GPh8
  exact m11_card_cent_inv (l41Y t x₁ x₂ rho) (m11_card_Y h)
    (fun y hy => ((m11_mem_Y_iff h).mp hy).2) (fun y hy y' hy' => m11_comm_Y h hy hy')
    (fun y hy => m11_rho_conj_Y h hy)
    (fun y hy => m11_conj_Y h (Subgroup.mul_mem _ hlamN htN) hy)
    (n4_rho_cube h.toCtx0) (m11_lamt_sq h.toL41GPh5) (m11_lamt_rho h.toL41GPh5)
    (fun y hy hyρ => m11_fix_R h.toL41GPh8 (m13_Y_le_R t x₁ x₂ rho hy) hyρ)

end Y11B

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
