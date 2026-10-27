module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtF1
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtOrders

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

namespace PtC1

theorem zmod2_mul_self (a : ZMod 2) : a * a = a := by
  fin_cases a <;> rfl

theorem card_eq_card_map_mul {H M : Type*} [Group H] [Group M] (f : H →* M) (K : Subgroup H) :
    Nat.card K = Nat.card (K.map f) * Nat.card (K ⊓ f.ker : Subgroup H) := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.domRestrict K).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.domRestrict K)).toEquiv,
    MonoidHom.domRestrict_range] at hcard
  rw [hcard, MonoidHom.ker_domRestrict, inf_comm, ← subgroupOf_map_subtype,
    Subgroup.card_map_of_injective K.subtype_injective]

theorem comm_mul_central {X : Type*} [Group X] {a j t : X} (hja : j * a = a * j)
    (hjt : j * t = t * j) : (a * j)⁻¹ * t⁻¹ * (a * j) * t = a⁻¹ * t⁻¹ * a * t := by
  have h2 : j⁻¹ * t⁻¹ * j = t⁻¹ := by
    calc j⁻¹ * t⁻¹ * j = j⁻¹ * t⁻¹ * (j * t) * t⁻¹ := by group
      _ = j⁻¹ * t⁻¹ * (t * j) * t⁻¹ := by rw [hjt]
      _ = t⁻¹ := by group
  rw [← hja]
  calc (j * a)⁻¹ * t⁻¹ * (j * a) * t = a⁻¹ * (j⁻¹ * t⁻¹ * j) * a * t := by group
    _ = a⁻¹ * t⁻¹ * a * t := by rw [h2]

theorem eq_t0Mat_of_fix {g : M₃} (e1 : g * jMat 1 0 0 * gᵀ = jMat 1 0 0)
    (e2 : g * jMat 0 1 0 * gᵀ = jMat 0 1 0) (e3 : g * jMat 0 0 1 * gᵀ = jMat 0 0 1) :
    g = t0Mat (g 0 1) (g 0 2) := by
  have a := fun i j => congrFun (congrFun e1 i) j
  have b := fun i j => congrFun (congrFun e2 i) j
  have c := fun i j => congrFun (congrFun e3 i) j
  have a00 := a 0 0
  have a11 := a 1 1
  have a22 := a 2 2
  have b01 := b 0 1
  have b02 := b 0 2
  have c01 := c 0 1
  have c02 := c 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, jMat, zmod2_mul_self] at a00 a11 a22 b01 b02 c01 c02
  simp only [a00, a11, a22, mul_zero, zero_add, one_mul] at b01 b02 c01 c02
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t0Mat, a00, a11, a22, b01, b02, c01, c02]

theorem eq_zero_of_inv : ∀ m11 m12 m22 y y' : ZMod 2, m11 * m22 + m12 = 1 →
    y * m11 + y' * m12 = 0 → y * m12 + y' * m22 = 0 → y = 0 ∧ y' = 0 := by
  decide

theorem inv_of_sum : ∀ m11 m12 m22 n11 n12 n22 : ZMod 2,
    ¬ (m11 = 0 ∧ m12 = 0 ∧ m22 = 0) → ¬ (n11 = 0 ∧ n12 = 0 ∧ n22 = 0) →
    ¬ (m11 = n11 ∧ m12 = n12 ∧ m22 = n22) → m11 * m22 + m12 = 0 → n11 * n22 + n12 = 0 →
    (m11 + n11) * (m22 + n22) + (m12 + n12) = 1 := by
  decide

theorem exists_ne_zero_of_ne : ∀ m11 m12 m22 : ZMod 2, ¬ (m11 = 0 ∧ m12 = 0 ∧ m22 = 0) →
    ∃ y y' : ZMod 2, ¬ (y * m11 + y' * m12 = 0 ∧ y * m12 + y' * m22 = 0) := by
  decide

end PtC1

section Setting

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e} {hb : b.IsAlt}
variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}
variable {D₁ C₁ F₁ : Subgroup G} {ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2}

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "𝐛₁" => ptB₁ he hb φ hzC hz
local notation "τ" M => tauHom φ he (Multiplicative.ofAdd M)

namespace PtC1

theorem mem_D₁A₂ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {c : G}
    (hc : c ∈ D₁ ⊔ 𝒜₂) : ∃ d ∈ D₁, ∃ M : ↥(binarySymMatrices 3), c = d * τ M := by
  have hle : 𝒜₂ ≤ normalizer (D₁ : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₁n a (h.A₂N₁ ha) d hd
  have hc' : c ∈ ((D₁ ⊔ 𝒜₂ : Subgroup G) : Set G) := hc
  rw [coe_mul_of_right_le_normalizer_left _ _ hle] at hc'
  obtain ⟨d, hd, a, ha, rfl⟩ := hc'
  obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
  exact ⟨d, hd, Multiplicative.toAdd B, by rw [ofAdd_toAdd]⟩

theorem tau_mem_A₂ (M : ↥(binarySymMatrices 3)) : (τ M) ∈ 𝒜₂ :=
  (mem_pullSub_iff φ he).2 ⟨_, rfl⟩

theorem tau_mem_D₁_iff (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (M : ↥(binarySymMatrices 3)) :
    (τ M) ∈ D₁ ↔ ((M : M₃) 1 1 = 0 ∧ (M : M₃) 1 2 = 0 ∧ (M : M₃) 2 2 = 0) := by
  constructor
  · intro hM
    have hJ : (τ M) ∈ 𝒜₁ ⊓ 𝒜₂ := by
      rw [← h.A₂_inf_D₁]
      exact mem_inf.2 ⟨tau_mem_A₂ M, hM⟩
    obtain ⟨c, y, y', hcy⟩ := (mem_ptA_inf_radA_iff he hb φ).1 hJ
    have h1 := Multiplicative.ofAdd.injective (tauHom_injective φ he hcy)
    rw [← h1]
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h11, h12, h22⟩
    have hsymm : ∀ i j : Fin 3, (M : M₃) j i = (M : M₃) i j := fun i j =>
      congrFun (congrFun (mem_binarySymMatrices.1 M.2) i) j
    have hM : M = jSym ((M : M₃) 0 0) ((M : M₃) 0 1) ((M : M₃) 0 2) := by
      apply Subtype.ext
      refine eq_jMat_iff.1 ⟨mem_binarySymMatrices.1 M.2, fun i j hi hj => ?_⟩
      fin_cases i <;> fin_cases j
      · exact absurd rfl hi
      · exact absurd rfl hi
      · exact absurd rfl hi
      · exact absurd rfl hj
      · exact h11
      · exact h12
      · exact absurd rfl hj
      · rw [hsymm]; exact h12
      · exact h22
    have hJ : (τ M) ∈ 𝒜₁ ⊓ 𝒜₂ := (mem_ptA_inf_radA_iff he hb φ).2 ⟨_, _, _, by rw [← hM]⟩
    exact h.A₁D₁ (mem_inf.1 hJ).1

theorem A₁_le_N₂₀ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : 𝒜₁ ≤ 𝒩₂₀ :=
  fun _ ha => mem_inf.2 ⟨ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left ha),
    ptSub_le_centralizer he hb h.hnd φ h.hsup (mem_sup_left ha)⟩

theorem sigma_t0 (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {x : G} (hx : x ∈ 𝒜₁)
    (hxN : x ∈ 𝒩₂₀) :
    σ ⟨x, hxN⟩ = t0Unit ((σ ⟨x, hxN⟩ : M₃) 0 1) ((σ ⟨x, hxN⟩ : M₃) 0 2) := by
  have hfix : ∀ c y y' : ZMod 2,
      (σ ⟨x, hxN⟩ : M₃) * jMat c y y' * (σ ⟨x, hxN⟩ : M₃)ᵀ = jMat c y y' := by
    intro c y y'
    have hJ : (τ (jSym c y y')) ∈ 𝒜₁ ⊓ 𝒜₂ := (mem_ptA_inf_radA_iff he hb φ).2 ⟨c, y, y', rfl⟩
    have hcomm : x * (τ (jSym c y y')) = (τ (jSym c y y')) * x :=
      mul_comm_of_isElementaryAbelian (ptA_facts he hb h.hnd φ).2.1 hx (mem_inf.1 hJ).1
    have h1 := conj_tauHom_of_sigma φ he σ h.hσ ⟨x, hxN⟩ (jSym c y y')
    have h2 : x * (τ (jSym c y y')) * x⁻¹ = τ (jSym c y y') := by
      rw [hcomm, mul_inv_cancel_right]
    change x * _ * x⁻¹ = _ at h1
    rw [h2] at h1
    have h3 := Multiplicative.ofAdd.injective (tauHom_injective φ he h1)
    exact (congrArg (fun B : ↥(binarySymMatrices 3) => (B : M₃)) h3).symm
  exact Units.ext (by
    rw [coe_t0Unit]
    exact eq_t0Mat_of_fix (hfix 1 0 0) (hfix 0 1 0) (hfix 0 0 1))

theorem mem_A₂_of_sigma_eq_one (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {x : G}
    (hx : x ∈ 𝒜₁) (hxN : x ∈ 𝒩₂₀) (h1 : σ ⟨x, hxN⟩ = 1) : x ∈ 𝒜₂ := by
  have hxL : x ∈ L := pullSub_le φ _ hx
  have hcomm : ∀ a ∈ 𝒜₂, a * x = x * a := by
    intro a ha
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    have h2 := conj_tauHom_of_sigma φ he σ h.hσ ⟨x, hxN⟩ (Multiplicative.toAdd B)
    rw [h1, symThreeCongr_one, ofAdd_toAdd] at h2
    change x * tauHom φ he B * x⁻¹ = tauHom φ he B at h2
    calc tauHom φ he B * x = x * tauHom φ he B * x⁻¹ * x := by rw [h2]
      _ = x * tauHom φ he B := by group
  have hle : radSub φ z e ≤ centralizer ({x} : Set G) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hcomm a ha))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (mul_comm_z hzC hxL).symm))
  have hxR : x ∈ radSub φ z e := by
    rw [← h.hRc, mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.1 (hle hr)
  exact mem_radA_of_mem_radSub φ hzC h.hinf hxR hxL

theorem comm_mem_I₁_iff (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {x : G}
    (hx : x ∈ 𝒜₁) {y y' : ZMod 2} (hσx : σ ⟨x⁻¹, A₁_le_N₂₀ h (inv_mem hx)⟩ = t0Unit y y')
    (M : ↥(binarySymMatrices 3)) :
    x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ zpowers 𝐛₁ ↔
      (y * (M : M₃) 1 1 + y' * (M : M₃) 1 2 = 0 ∧ y * (M : M₃) 1 2 + y' * (M : M₃) 2 2 = 0) := by
  have hJ : x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ 𝒜₁ ⊓ 𝒜₂ := by
    have h1 := comm_mem_ptA_inf_radA' he hb h.hnd φ hzC h.hinf hz (inv_mem hx)
      (inv_mem (tau_mem_A₂ (he := he) M))
    simpa only [inv_inv] using h1
  have hlab := labJ_comm_tauHom he φ σ h.hσ (A₁_le_N₂₀ h (inv_mem hx)) hσx M
  have hsymm : (M : M₃) 2 1 = (M : M₃) 1 2 :=
    congrFun (congrFun (mem_binarySymMatrices.1 M.2) 1) 2
  rw [hsymm] at hlab
  constructor
  · intro hI
    have h0 := labJ_of_mem_zpowers he hb φ hzC hz hI
    rw [hlab] at h0
    exact ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩
  · rintro ⟨h1, h2⟩
    refine mem_zpowers_of_labJ he hb φ hzC hz hJ ?_
    rw [hlab]
    funext i
    fin_cases i
    · simpa using h1
    · simpa using h2

theorem exists_sigma_eq [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (y y' : ZMod 2) :
    ∃ x, ∃ hx : x ∈ 𝒜₁, σ ⟨x⁻¹, A₁_le_N₂₀ h (inv_mem hx)⟩ = t0Unit y y' := by
  let ρ : ↥𝒜₁ →* GL (Fin 3) (ZMod 2) := σ.comp (Subgroup.inclusion (A₁_le_N₂₀ h))
  have hρ : ∀ x : ↥𝒜₁, ρ x = σ ⟨x, A₁_le_N₂₀ h x.2⟩ := fun x => rfl
  have hrange : ρ.range ≤ lagrangianT0 := by
    rintro _ ⟨x, rfl⟩
    rw [hρ, sigma_t0 h x.2]
    exact ⟨(_, _), rfl⟩
  have hker : ∀ x : ↥𝒜₁, x ∈ ρ.ker → (x : G) ∈ 𝒜₁ ⊓ 𝒜₂ := fun x hx =>
    mem_inf.2 ⟨x.2, mem_A₂_of_sigma_eq_one h x.2 _ hx⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv] at hcard
  have hkle : Nat.card ρ.ker ≤ 8 := by
    rw [← card_ptA_inf_radA he hb φ]
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥𝒜₁) : G), hker x x.2⟩) ?_
    intro a c hac
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hac
  have hA : Nat.card ↥𝒜₁ = 32 := (ptA_facts he hb h.hnd φ).2.2.1
  have hR : ρ.range = lagrangianT0 := by
    refine Subgroup.eq_of_le_of_card_ge hrange ?_
    rw [card_lagrangianT0]
    by_contra hlt
    push Not at hlt
    have h1 := Nat.mul_le_mul (Nat.le_of_lt_succ hlt) hkle
    rw [hA] at hcard
    linarith
  obtain ⟨x, hx⟩ : t0Unit y y' ∈ ρ.range := by
    rw [hR]
    exact ⟨(y, y'), rfl⟩
  refine ⟨(x : G)⁻¹, inv_mem x.2, ?_⟩
  have he' : (⟨(x : G)⁻¹⁻¹, A₁_le_N₂₀ h (inv_mem (inv_mem x.2))⟩ : 𝒩₂₀) =
      ⟨x, A₁_le_N₂₀ h x.2⟩ := Subtype.ext (inv_inv _)
  rw [he', ← hρ, hx]

local notation "𝔓" v => ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G)

theorem P_add (v v' : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2) :
    (𝔓 (v + v')) = (𝔓 v) * (𝔓 v') := by
  rw [ofAdd_add, map_mul, map_mul, Subgroup.coe_mul]

theorem P_mem_A₁ (v : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2) : (𝔓 v) ∈ 𝒜₁ :=
  (mem_ptA_iff he hb φ).2 ⟨v, rfl⟩

theorem P_injective {v v' : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2}
    (hv : (𝔓 v) = (𝔓 v')) : v = v' :=
  Multiplicative.ofAdd.injective (ptHomV_injective he hb (φ.symm.injective (Subtype.ext hv)))

theorem P_zero_mem (s : ZMod 2) :
    (𝔓 ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))), s)) ∈ zpowers 𝐛₁ := by
  rcases zmod_two_eq_zero_or_eq_one s with rfl | rfl
  · rw [Prod.mk_zero_zero, ofAdd_zero, map_one, map_one]
    exact one_mem _
  · rw [ptB₁, ptHom_pt]
    exact mem_zpowers _

theorem pairOrth_add_self (v : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem gamma_eq (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {u : G} (hu : u ∈ D₁) :
    z⁻¹ * (u⁻¹ * z * u) = (𝔓 (ν₁ u)) := by
  rw [h.hν₁z u hu, ptHom_apply, zPow_one,
    mul_comm_z hzC (φ.symm (ptHomV he hb (Multiplicative.ofAdd (ν₁ u)))).2, inv_mul_cancel_left]

theorem nu_fst_mul (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {u u' : G}
    (hu : u ∈ D₁) (hu' : u' ∈ D₁) : (ν₁ (u * u')).1 = (ν₁ u).1 + (ν₁ u').1 := by
  have h1 := h.hν₁z (u * u') (mul_mem hu hu')
  have h2 : (u * u')⁻¹ * z * (u * u') = u'⁻¹ * (u⁻¹ * z * u) * u' := by group
  rw [h2, h.hν₁z u hu, h.hact₁ u' hu' (ν₁ u) 1] at h1
  have h3 := ptHom_injective he hb φ hzC hz h.hinf h1
  have h4 := congrArg (fun x => (Multiplicative.toAdd x).1.1) h3
  simp only [toAdd_ofAdd, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, one_smul] at h4
  exact h4.symm

theorem nu_fst_one (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : (ν₁ 1).1 = 0 :=
  ((h.hF₁mem 1).1 (one_mem _)).2

theorem nu_fst_conj (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {u d : G}
    (hu : u ∈ D₁) (hd : d ∈ D₁) : (ν₁ (d⁻¹ * u * d)).1 = (ν₁ u).1 := by
  have h1 := nu_fst_mul h (mul_mem (inv_mem hd) hu) hd
  have h2 := nu_fst_mul h (inv_mem hd) hu
  have h3 := nu_fst_mul h (inv_mem hd) hd
  rw [inv_mul_cancel, nu_fst_one h] at h3
  rw [h1, h2]
  calc (ν₁ d⁻¹).1 + (ν₁ u).1 + (ν₁ d).1 = (ν₁ u).1 + ((ν₁ d⁻¹).1 + (ν₁ d).1) := by abel
    _ = (ν₁ u).1 := by rw [← h3, add_zero]

theorem comm_label_mem (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {C : Subgroup G}
    (hCcomm : ∀ x ∈ C, ∀ y ∈ C, x⁻¹ * y⁻¹ * x * y ∈ zpowers 𝐛₁) {k d : G}
    {M : ↥(binarySymMatrices 3)} (hkC : k ∈ C) (hkD : k ∈ D₁) (hd : d ∈ D₁)
    (hw : d * (τ M) ∈ C) (s : ZMod 2) :
    (𝔓 ((ν₁ k).1, s))⁻¹ * (τ M)⁻¹ * (𝔓 ((ν₁ k).1, s)) * (τ M) ∈ zpowers 𝐛₁ := by
  have hτA := tau_mem_A₂ (φ := φ) (he := he) M
  have hτN : (τ M) ∈ 𝒩₁ := h.A₂N₁ hτA
  have hτz : (τ M) ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (mul_comm_z hzC (pullSub_le φ _ hτA))
  have hkN : k ∈ 𝒩₁ := h.hD₁N hkD
  have hy : d⁻¹ * k * d ∈ D₁ := mul_mem (mul_mem (inv_mem hd) hkD) hd
  have hi := hCcomm k hkC _ hw
  have hc := PtF1.I₁_comm h hi (mul_mem (mul_mem (inv_mem hkN) (PtF1.zN₁ h)) hkN)
  have h1 : z⁻¹ * (((τ M)⁻¹ * (d⁻¹ * k * d) * (τ M))⁻¹ * z * ((τ M)⁻¹ * (d⁻¹ * k * d) * (τ M))) =
      z⁻¹ * (k⁻¹ * z * k) := by
    have he1 : (τ M)⁻¹ * (d⁻¹ * k * d) * (τ M) =
        k * (k⁻¹ * (d * (τ M))⁻¹ * k * (d * (τ M))) := by group
    rw [he1]
    generalize k⁻¹ * (d * (τ M))⁻¹ * k * (d * (τ M)) = i at hc ⊢
    have hc' : i⁻¹ * (k⁻¹ * z * k) * i = k⁻¹ * z * k := by
      rw [mul_assoc, ← hc, inv_mul_cancel_left]
    calc z⁻¹ * ((k * i)⁻¹ * z * (k * i)) = z⁻¹ * (i⁻¹ * (k⁻¹ * z * k) * i) := by group
      _ = z⁻¹ * (k⁻¹ * z * k) := by rw [hc']
  have h2 := h.hγeq (τ M) (mem_inf.2 ⟨hτN, hτz⟩) (d⁻¹ * k * d)
  rw [h1, gamma_eq h hkD, gamma_eq h hy] at h2
  have hfst := nu_fst_conj h hkD hd
  have hinv : ∀ v, (𝔓 v)⁻¹ = 𝔓 v := fun v =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact PtF1.sq_A₁ h (P_mem_A₁ v))
  have h3 : (𝔓 (ν₁ (d⁻¹ * k * d)))⁻¹ * (τ M)⁻¹ * (𝔓 (ν₁ (d⁻¹ * k * d))) * (τ M) ∈
      zpowers 𝐛₁ := by
    have h4 : (𝔓 (ν₁ (d⁻¹ * k * d)))⁻¹ * (τ M)⁻¹ * (𝔓 (ν₁ (d⁻¹ * k * d))) * (τ M) =
        (𝔓 (ν₁ (d⁻¹ * k * d)))⁻¹ * (𝔓 (ν₁ k)) := by
      rw [h2]
      group
    rw [h4, hinv, ← P_add]
    have h6 : ν₁ (d⁻¹ * k * d) + ν₁ k =
        ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))), (ν₁ (d⁻¹ * k * d)).2 + (ν₁ k).2) := by
      refine Prod.ext ?_ rfl
      rw [Prod.fst_add, hfst, pairOrth_add_self]
    rw [h6]
    exact P_zero_mem _
  have hv : ((ν₁ k).1, s) = ν₁ (d⁻¹ * k * d) +
      ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))), s + (ν₁ (d⁻¹ * k * d)).2) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, hfst, add_zero]
    · rw [Prod.snd_add, add_comm s, ← add_assoc, zmod_two_add_self_eq_zero, zero_add]
  have hj := P_zero_mem (he := he) (hb := hb) (φ := φ) (hzC := hzC) (hz := hz)
    (s + (ν₁ (d⁻¹ * k * d)).2)
  rw [hv, P_add, comm_mul_central
    (mul_comm_of_isElementaryAbelian (ptA_facts he hb h.hnd φ).2.1 (P_mem_A₁ _) (P_mem_A₁ _))
    (PtF1.I₁_comm h hj hτN)]
  exact h3

theorem card_le_of_le_F₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {K : Subgroup G} (hK : K ≤ F₁) : Nat.card K ≤ 4 * Nat.card (𝒜₁ ⊓ K : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card (H := 𝒜₁) (K := F₁)
  rw [inf_of_le_left (PtF1.A₁F₁ h), PtF1.card_A₁' h, h.hF₁card] at h1
  have h4 : Subgroup.relIndex 𝒜₁ F₁ = 4 := by omega
  have h2 := Subgroup.relIndex_le_of_le_right hK (by rw [h4]; norm_num)
  rw [h4] at h2
  rw [← Subgroup.relIndex_mul_card (H := 𝒜₁) (K := K)]
  exact Nat.mul_le_mul_right _ h2

theorem card_le_of_le_E₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {K : Subgroup G} (hK : K ≤ C₁ ⊓ F₁) : Nat.card K ≤ 2 * Nat.card (𝒜₁ ⊓ K : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card (H := 𝒜₁) (K := C₁ ⊓ F₁)
  rw [inf_of_le_left (le_inf (PtF1.A₁C₁' h) (PtF1.A₁F₁ h)), PtF1.card_A₁' h, h.hE₁card] at h1
  have h4 : Subgroup.relIndex 𝒜₁ (C₁ ⊓ F₁) = 2 := by omega
  have h2 := Subgroup.relIndex_le_of_le_right hK (by rw [h4]; norm_num)
  rw [h4] at h2
  rw [← Subgroup.relIndex_mul_card (H := 𝒜₁) (K := K)]
  exact Nat.mul_le_mul_right _ h2

theorem inf_F₁_le_C₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {X : Subgroup G} (hXD : X ≤ D₁) (hXsq : ∀ x ∈ X, x ^ 2 ∈ zpowers 𝐛₁) (hXF : ¬ X ≤ F₁) :
    X ⊓ F₁ ≤ C₁ := by
  obtain ⟨x₀, hx₀, hx₀F⟩ := IsConcreteLE.not_le_iff_exists.1 hXF
  have hx₀C : x₀ ∈ C₁ := by
    by_contra hC
    exact hx₀F (PtF1.mem_F₁_of_sq_mem h (hXD hx₀) hC (hXsq x₀ hx₀))
  intro f hf
  obtain ⟨hfX, hfF⟩ := mem_inf.1 hf
  by_contra hfC
  have hfx : f * x₀ ∉ C₁ := fun h' => hfC (by
    have h1 := mul_mem h' (inv_mem hx₀C)
    rwa [mul_inv_cancel_right] at h1)
  have h2 := PtF1.mem_F₁_of_sq_mem h (hXD (mul_mem hfX hx₀)) hfx (hXsq _ (mul_mem hfX hx₀))
  apply hx₀F
  have h3 := mul_mem (inv_mem hfF) h2
  rwa [inv_mul_cancel_left] at h3

theorem exists_labels [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {X : Subgroup G} (hXD : X ≤ D₁) :
    ∃ W : Subgroup (Multiplicative (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)))),
      Nat.card X = Nat.card W * Nat.card (X ⊓ F₁ : Subgroup G) ∧
      ∀ w ∈ W, ∃ x ∈ X, (ν₁ x).1 = Multiplicative.toAdd w := by
  let π : ↥D₁ →* Multiplicative (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) :=
    { toFun := fun u => Multiplicative.ofAdd (ν₁ u).1
      map_one' := by
        change Multiplicative.ofAdd (ν₁ 1).1 = 1
        rw [nu_fst_one h, ofAdd_zero]
      map_mul' := fun u u' => by
        change Multiplicative.ofAdd (ν₁ ((u : G) * u')).1 =
          Multiplicative.ofAdd (ν₁ u).1 * Multiplicative.ofAdd (ν₁ u').1
        rw [nu_fst_mul h u.2 u'.2, ofAdd_add] }
  have hker : ∀ u : ↥D₁, u ∈ π.ker ↔ (u : G) ∈ F₁ := fun u => by
    rw [MonoidHom.mem_ker, h.hF₁mem]
    change Multiplicative.ofAdd (ν₁ u).1 = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact ⟨fun h1 => ⟨u.2, h1⟩, fun h1 => h1.2⟩
  refine ⟨(X.subgroupOf D₁).map π, ?_, ?_⟩
  · have hf := card_eq_card_map_mul π (X.subgroupOf D₁)
    have h1 : X.subgroupOf D₁ ⊓ π.ker = (X ⊓ F₁).subgroupOf D₁ := by
      ext u
      rw [mem_inf, mem_subgroupOf, mem_subgroupOf, hker, mem_inf]
    rw [h1, Nat.card_congr (subgroupOfEquivOfLe hXD).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hXD)).toEquiv] at hf
    exact hf
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, mem_subgroupOf.1 hu, rfl⟩

theorem comm_tau_mem_of_comm (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {x d : G}
    (hx : x ∈ 𝒜₁) (hd : d ∈ D₁) (M : ↥(binarySymMatrices 3))
    (hxw : x⁻¹ * (d * (τ M))⁻¹ * x * (d * (τ M)) ∈ zpowers 𝐛₁) :
    x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ zpowers 𝐛₁ := by
  have hi : x⁻¹ * d⁻¹ * x * d ∈ zpowers 𝐛₁ := by
    rw [← h.hAD₁]
    have h1 := Subgroup.commutator_mem_commutator (inv_mem hx) (inv_mem hd)
    rwa [commutatorElement_def, inv_inv, inv_inv] at h1
  have hτN : (τ M) ∈ 𝒩₁ := h.A₂N₁ (tau_mem_A₂ M)
  have hc : (τ M)⁻¹ * (x⁻¹ * d⁻¹ * x * d) * (τ M) = x⁻¹ * d⁻¹ * x * d := by
    rw [mul_assoc, PtF1.I₁_comm h hi hτN, inv_mul_cancel_left]
  have heq : x⁻¹ * (d * (τ M))⁻¹ * x * (d * (τ M)) =
      (x⁻¹ * (τ M)⁻¹ * x * (τ M)) * ((τ M)⁻¹ * (x⁻¹ * d⁻¹ * x * d) * (τ M)) := by group
  rw [heq, hc] at hxw
  have h2 := mul_mem hxw (inv_mem hi)
  rwa [mul_inv_cancel_right] at h2

theorem two_mul_card_le [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {M : ↥(binarySymMatrices 3)} {F : ℕ}
    (hF : ∀ X : Subgroup G, X ≤ 𝒜₁ →
      (∀ x ∈ X, x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ zpowers 𝐛₁) → Nat.card X ≤ F)
    {W : Subgroup (Multiplicative (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))))}
    (hW : ∀ w ∈ W, (𝔓 (Multiplicative.toAdd w, 0))⁻¹ * (τ M)⁻¹ *
      (𝔓 (Multiplicative.toAdd w, 0)) * (τ M) ∈ zpowers 𝐛₁) :
    2 * Nat.card W ≤ F := by
  have hAe := (ptA_facts he hb h.hnd φ).2.1
  have hτN : (τ M) ∈ 𝒩₁ := h.A₂N₁ (tau_mem_A₂ M)
  let α : Multiplicative (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) →* G :=
    L.subtype.comp (φ.symm.toMonoidHom.comp ((ptHomV he hb).comp
      (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ (ZMod 2)))))
  have hα : ∀ w, α w = 𝔓 (Multiplicative.toAdd w, 0) := fun w => rfl
  have hαinj : Function.Injective α := fun w w' hww' => by
    rw [hα, hα] at hww'
    exact Multiplicative.toAdd.injective (congrArg Prod.fst (P_injective hww'))
  have hαA : ∀ w, α w ∈ 𝒜₁ := fun w => by
    rw [hα]
    exact P_mem_A₁ (he := he) _
  have hT : zpowers 𝐛₁ ≤ centralizer (W.map α : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    exact mul_comm_of_isElementaryAbelian hAe (hαA w) (PtF1.I₁A₁ (mem_zpowers _))
  have hinf : W.map α ⊓ zpowers 𝐛₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨w, -, rfl⟩, hxI⟩ := mem_inf.1 hx
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) hxI with h1 | h1
    · rw [h1]
      exact one_mem _
    · exfalso
      rw [hα, ptB₁, ptHom_pt] at h1
      exact zero_ne_one (congrArg Prod.snd (P_injective h1))
  have hcard : Nat.card (W.map α ⊔ zpowers 𝐛₁ : Subgroup G) = Nat.card W * 2 := by
    rw [card_sup_eq_mul hT hinf, Subgroup.card_map_of_injective hαinj, Nat.card_zpowers,
      orderOf_ptB₁ he hb φ hzC hz]
  have hXA : W.map α ⊔ zpowers 𝐛₁ ≤ 𝒜₁ := sup_le (by
    rintro _ ⟨w, -, rfl⟩
    exact hαA w) PtF1.I₁A₁
  have hXfix : ∀ x ∈ W.map α ⊔ zpowers 𝐛₁, x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ zpowers 𝐛₁ := by
    intro x hx
    obtain ⟨l, hl, j, hj, rfl⟩ := (mem_sup_of_le_centralizer hT).1 hx
    obtain ⟨w, hw, rfl⟩ := hl
    rw [comm_mul_central (mul_comm_of_isElementaryAbelian hAe (PtF1.I₁A₁ hj) (hαA w))
      (PtF1.I₁_comm h hj hτN), hα]
    exact hW w hw
  have h1 := hF _ hXA hXfix
  rw [hcard] at h1
  omega

theorem card_inf_le [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {C : Subgroup G} (hCsq : ∀ x ∈ C, x ^ 2 ∈ zpowers 𝐛₁)
    (hCcomm : ∀ x ∈ C, ∀ y ∈ C, x⁻¹ * y⁻¹ * x * y ∈ zpowers 𝐛₁) {d : G}
    {M : ↥(binarySymMatrices 3)} (hd : d ∈ D₁) (hw : d * (τ M) ∈ C) {F : ℕ}
    (hF : ∀ X : Subgroup G, X ≤ 𝒜₁ →
      (∀ x ∈ X, x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ zpowers 𝐛₁) → Nat.card X ≤ F) :
    Nat.card (C ⊓ D₁ : Subgroup G) ≤ 4 * F + F * F := by
  obtain ⟨W, hWcard, hWlab⟩ := exists_labels h (inf_le_right : C ⊓ D₁ ≤ D₁)
  have hW : 2 * Nat.card W ≤ F := two_mul_card_le h hF fun w hw' => by
    obtain ⟨k, hk, hkw⟩ := hWlab w hw'
    have h1 := comm_label_mem h hCcomm (mem_inf.1 hk).1 (mem_inf.1 hk).2 hd hw 0
    rwa [hkw] at h1
  have hK1 : Nat.card (𝒜₁ ⊓ (C ⊓ D₁ ⊓ F₁) : Subgroup G) ≤ F := by
    refine hF _ inf_le_left fun x hx => ?_
    obtain ⟨hxA, hxK⟩ := mem_inf.1 hx
    exact comm_tau_mem_of_comm h hxA hd M
      (hCcomm x (mem_inf.1 (mem_inf.1 hxK).1).1 _ hw)
  by_cases hKF : C ⊓ D₁ ≤ F₁
  · have h1 := card_le_of_le_F₁ h (inf_le_right : C ⊓ D₁ ⊓ F₁ ≤ F₁)
    rw [inf_of_le_left hKF] at h1 hK1
    nlinarith
  · have hle := inf_F₁_le_C₁ h inf_le_right (fun x hx => hCsq x (mem_inf.1 hx).1) hKF
    have h1 := card_le_of_le_E₁ h (le_inf hle inf_le_right)
    rw [hWcard]
    have h2 : Nat.card W * Nat.card (C ⊓ D₁ ⊓ F₁ : Subgroup G) ≤ Nat.card W * (2 * F) :=
      Nat.mul_le_mul_left _ (h1.trans (by omega))
    nlinarith

theorem two_mul_le_of_dvd {d n : ℕ} (hd : d ∣ n) (hn : 0 < n) (hne : d ≠ n) : 2 * d ≤ n := by
  obtain ⟨m, rfl⟩ := hd
  rcases m with _ | _ | m
  · simp at hn
  · simp at hne
  · nlinarith

theorem card_le_of_fix [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (M : ↥(binarySymMatrices 3)) (hM : ¬ ((M : M₃) 1 1 = 0 ∧ (M : M₃) 1 2 = 0 ∧ (M : M₃) 2 2 = 0))
    {X : Subgroup G} (hXA : X ≤ 𝒜₁)
    (hX : ∀ x ∈ X, x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ zpowers 𝐛₁) : Nat.card X ≤ 16 := by
  obtain ⟨y, y', hyy⟩ := exists_ne_zero_of_ne _ _ _ hM
  obtain ⟨x₀, hx₀, hσ₀⟩ := exists_sigma_eq h y y'
  have hx₀X : x₀ ∉ X := fun hx => hyy ((comm_mem_I₁_iff h hx₀ hσ₀ M).1 (hX x₀ hx))
  have hA : Nat.card ↥𝒜₁ = 32 := (ptA_facts he hb h.hnd φ).2.2.1
  have hdvd : Nat.card X ∣ 32 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le hXA
  have hne : Nat.card X ≠ 32 := fun h32 => hx₀X (by
    rw [Subgroup.eq_of_le_of_card_ge hXA (by rw [h32, hA])]
    exact hx₀)
  have := two_mul_le_of_dvd hdvd (by norm_num) hne
  omega

theorem le_J_of_fix [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (M : ↥(binarySymMatrices 3)) (hM : (M : M₃) 1 1 * (M : M₃) 2 2 + (M : M₃) 1 2 = 1)
    {X : Subgroup G} (hXA : X ≤ 𝒜₁)
    (hX : ∀ x ∈ X, x⁻¹ * (τ M)⁻¹ * x * (τ M) ∈ zpowers 𝐛₁) : X ≤ 𝒜₁ ⊓ 𝒜₂ := by
  intro x hx
  have hxA := hXA hx
  have hσ := sigma_t0 h (inv_mem hxA) (A₁_le_N₂₀ h (inv_mem hxA))
  have h1 := (comm_mem_I₁_iff h hxA hσ M).1 (hX x hx)
  obtain ⟨hy, hy'⟩ := eq_zero_of_inv _ _ _ _ _ hM h1.1 h1.2
  have hσ1 : σ ⟨x⁻¹, A₁_le_N₂₀ h (inv_mem hxA)⟩ = 1 := by
    rw [hσ, hy, hy']
    exact Units.ext t0Mat_zero
  have h2 := mem_A₂_of_sigma_eq_one h (inv_mem hxA) _ hσ1
  exact mem_inf.2 ⟨hxA, by simpa using inv_mem h2⟩

theorem card_le_two_mul [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {C : Subgroup G} (hC : C ≤ D₁ ⊔ 𝒜₂)
    (hinv : ∀ c ∈ C, ∀ d ∈ D₁, ∀ M : ↥(binarySymMatrices 3), c = d * (τ M) →
      (M : M₃) 1 1 * (M : M₃) 2 2 + (M : M₃) 1 2 ≠ 1) :
    Nat.card C ≤ 2 * Nat.card (C ⊓ D₁ : Subgroup G) := by
  have hsing : ∀ c ∈ C, ∀ d ∈ D₁, ∀ M : ↥(binarySymMatrices 3), c = d * (τ M) →
      (M : M₃) 1 1 * (M : M₃) 2 2 + (M : M₃) 1 2 = 0 := fun c hc d hd M hcM =>
    (zmod_two_eq_zero_or_eq_one _).resolve_right (hinv c hc d hd M hcM)
  have hτN : ∀ M : ↥(binarySymMatrices 3), (τ M) ∈ 𝒩₁ := fun M => h.A₂N₁ (tau_mem_A₂ M)
  have hentry : ∀ (M M' : ↥(binarySymMatrices 3)) (i j : Fin 3),
      ((M + M' : ↥(binarySymMatrices 3)) : M₃) i j = (M : M₃) i j + (M' : M₃) i j :=
    fun _ _ _ _ => rfl
  by_cases hCD : C ≤ D₁
  · rw [inf_of_le_left hCD]
    omega
  obtain ⟨w₁, hw₁C, hw₁D⟩ := IsConcreteLE.not_le_iff_exists.1 hCD
  obtain ⟨d₁, hd₁, M₁, rfl⟩ := mem_D₁A₂ h (hC hw₁C)
  have hM₁ : ¬ ((M₁ : M₃) 1 1 = 0 ∧ (M₁ : M₃) 1 2 = 0 ∧ (M₁ : M₃) 2 2 = 0) := fun h0 =>
    hw₁D (mul_mem hd₁ ((tau_mem_D₁_iff h M₁).2 h0))
  have hcoset : ∀ c ∈ C, c ∉ D₁ → (d₁ * (τ M₁))⁻¹ * c ∈ D₁ := by
    intro c hc hcD
    obtain ⟨d, hd, M, rfl⟩ := mem_D₁A₂ h (hC hc)
    have hM : ¬ ((M : M₃) 1 1 = 0 ∧ (M : M₃) 1 2 = 0 ∧ (M : M₃) 2 2 = 0) := fun h0 =>
      hcD (mul_mem hd ((tau_mem_D₁_iff h M).2 h0))
    have hd' : (τ M₁) * d * (τ M₁)⁻¹ ∈ D₁ := h.hD₁n _ (hτN M₁) d hd
    have hprod : d₁ * (τ M₁) * (d * (τ M)) = (d₁ * ((τ M₁) * d * (τ M₁)⁻¹)) * (τ (M₁ + M)) := by
      rw [ofAdd_add, map_mul]
      group
    have heq : (M₁ : M₃) 1 1 = (M : M₃) 1 1 ∧ (M₁ : M₃) 1 2 = (M : M₃) 1 2 ∧
        (M₁ : M₃) 2 2 = (M : M₃) 2 2 := by
      by_contra hne
      have h1 := inv_of_sum _ _ _ _ _ _ hM₁ hM hne (hsing _ hw₁C d₁ hd₁ M₁ rfl)
        (hsing _ hc d hd M rfl)
      refine hinv _ (mul_mem hw₁C hc) _ (mul_mem hd₁ hd') (M₁ + M) hprod ?_
      rw [hentry, hentry, hentry]
      exact h1
    have hd'' : (τ M₁)⁻¹ * (d₁⁻¹ * d) * (τ M₁) ∈ D₁ := by
      have h1 := h.hD₁n _ (inv_mem (hτN M₁)) _ (mul_mem (inv_mem hd₁) hd)
      rwa [inv_inv] at h1
    have h2 : (d₁ * (τ M₁))⁻¹ * (d * (τ M)) =
        ((τ M₁)⁻¹ * (d₁⁻¹ * d) * (τ M₁)) * ((τ M₁)⁻¹ * (τ M)) := by group
    rw [h2, tauHom_inv_mul]
    refine mul_mem hd'' ((tau_mem_D₁_iff h _).2 ?_)
    rw [hentry, hentry, hentry, heq.1, heq.2.1, heq.2.2, zmod_two_add_self_eq_zero,
      zmod_two_add_self_eq_zero, zmod_two_add_self_eq_zero]
    exact ⟨rfl, rfl, rfl⟩
  have hidx : D₁.relIndex C ≤ 2 := by
    rw [Subgroup.relIndex, Subgroup.index]
    let f : Bool → ↥C ⧸ D₁.subgroupOf C :=
      fun c => if c then QuotientGroup.mk ⟨d₁ * (τ M₁), hw₁C⟩ else QuotientGroup.mk 1
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H k =>
        by_cases hk : (k : G) ∈ D₁
        · refine ⟨false, ?_⟩
          change (QuotientGroup.mk 1 : _ ⧸ D₁.subgroupOf C) = QuotientGroup.mk k
          refine QuotientGroup.eq.2 ?_
          rw [mem_subgroupOf, inv_one, one_mul]
          exact hk
        · refine ⟨true, ?_⟩
          change (QuotientGroup.mk ⟨d₁ * (τ M₁), hw₁C⟩ : _ ⧸ D₁.subgroupOf C) =
            QuotientGroup.mk k
          refine QuotientGroup.eq.2 ?_
          rw [mem_subgroupOf]
          exact hcoset k k.2 hk
    calc Nat.card (↥C ⧸ D₁.subgroupOf C) ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
      _ = 2 := by simp
  have h1 := Subgroup.relIndex_mul_card (H := D₁) (K := C)
  rw [inf_comm] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hidx

end PtC1

theorem PtBase.eq_C₁_of_le_D₁_sup [Finite G]
    (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {C : Subgroup G}
    (hIC : zpowers 𝐛₁ ≤ C) (hC : C ≤ D₁ ⊔ 𝒜₂) (hCcard : Nat.card C = 1024)
    (hCsq : ∀ x ∈ C, x ^ 2 ∈ zpowers 𝐛₁)
    (hCcomm : ∀ x ∈ C, ∀ y ∈ C, x⁻¹ * y⁻¹ * x * y ∈ zpowers 𝐛₁) : C = C₁ := by
  by_cases hCD : C ≤ D₁
  · exact h.eq_C₁_of_le_D₁ hIC hCD hCcard hCsq hCcomm
  exfalso
  obtain ⟨w₁, hw₁C, hw₁D⟩ := IsConcreteLE.not_le_iff_exists.1 hCD
  obtain ⟨d₁, hd₁, M₁, rfl⟩ := PtC1.mem_D₁A₂ h (hC hw₁C)
  have hM₁ : ¬ ((M₁ : M₃) 1 1 = 0 ∧ (M₁ : M₃) 1 2 = 0 ∧ (M₁ : M₃) 2 2 = 0) := fun h0 =>
    hw₁D (mul_mem hd₁ ((PtC1.tau_mem_D₁_iff h M₁).2 h0))
  have hle : C ≤ normalizer (D₁ : Set G) := by
    refine hC.trans (sup_le le_normalizer fun a ha => ?_)
    exact mem_normalizer_of_conj_mem fun d hd => h.hD₁n a (h.A₂N₁ ha) d hd
  have hprod := natCard_sup_mul_inf hle
  have hsup : Nat.card (C ⊔ D₁ : Subgroup G) ≤ 2 ^ 14 := by
    rw [← h.card_D₁A₂]
    exact Subgroup.card_le_of_le (sup_le hC le_sup_left)
  rw [hCcard, h.hD₁card] at hprod
  have hK128 : 128 ≤ Nat.card (C ⊓ D₁ : Subgroup G) := by nlinarith
  by_cases hinv : ∃ c ∈ C, ∃ d ∈ D₁, ∃ M : ↥(binarySymMatrices 3), c = d * (τ M) ∧
      (M : M₃) 1 1 * (M : M₃) 2 2 + (M : M₃) 1 2 = 1
  · obtain ⟨c, hc, d, hd, M, rfl, hM⟩ := hinv
    have h1 := PtC1.card_inf_le h hCsq hCcomm hd hc (F := 8) fun X hXA hX => by
      have h2 := Subgroup.card_le_of_le (PtC1.le_J_of_fix h M hM hXA hX)
      rwa [card_ptA_inf_radA he hb φ] at h2
    omega
  · push Not at hinv
    have h512 := PtC1.card_le_two_mul h hC hinv
    rw [hCcard] at h512
    have h1 := PtC1.card_inf_le h hCsq hCcomm hd₁ hw₁C (F := 16) fun X hXA hX =>
      PtC1.card_le_of_fix h M₁ hM₁ hXA hX
    omega

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
