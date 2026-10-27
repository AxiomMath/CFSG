module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Setup

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_center_of_mem_normalizer_D4 {R : Subgroup G} {n z : G}
    (hn : n ∈ normalizer (R : Set G)) (hz : z ∈ R) (hzc : ∀ r ∈ R, z * r = r * z) :
    n * z * n⁻¹ ∈ R ∧ ∀ r ∈ R, n * z * n⁻¹ * r = r * (n * z * n⁻¹) := by
  refine ⟨(mem_normalizer_iff.1 hn z).1 hz, fun r hr => ?_⟩
  have hr' : n⁻¹ * r * n ∈ R := by
    have := (mem_normalizer_iff.1 (inv_mem hn) r).1 hr
    simpa using this
  have h1 := hzc _ hr'
  calc n * z * n⁻¹ * r = n * (z * (n⁻¹ * r * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * r * n) * z) * n⁻¹ := by rw [h1]
    _ = r * (n * z * n⁻¹) := by group

theorem mem_normalizer_of_conj_mem_D4 {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hinj : Function.Injective (fun x : H => (⟨g * x * g⁻¹, h x x.2⟩ : H)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.1 hinj
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  obtain ⟨k, hk⟩ := hsurj ⟨g * n * g⁻¹, hn⟩
  have hkn : (k : G) = n := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← hkn]
  exact k.2

theorem mem_map_conj_iff_D4 {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem ncard_conj_mul_card_inf_centralizer_D4 (H : Subgroup G) (x : G) :
    {y | ∃ h ∈ H, h * x * h⁻¹ = y}.ncard * Nat.card (H ⊓ centralizer {x} : Subgroup G) =
      Nat.card H := by
  let _ : MulAction H G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (y : G), h • y = (h : G) * y * (h : G)⁻¹ := fun h y =>
    ConjAct.toConjAct_smul (h : G) y
  have horb : MulAction.orbit H x = {y | ∃ h ∈ H, h * x * h⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h x).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul _ x⟩
  have hstab : MulAction.stabilizer H x = (centralizer {x}).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
  have h := (MulAction.stabilizer H x).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

variable [Finite G]

@[expose] noncomputable def rankJr (P : Subgroup G) : Subgroup G :=
  ⨆ (A : Subgroup G) (_ : A ≤ P ∧ IsMulCommutative A ∧
    CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 P), A

theorem odd_ncard_conj_D4 {H Q : Subgroup G} (hQ : IsSylowOf 2 Q H) {x : G}
    (hxQ : Q ≤ centralizer ({x} : Set G)) : Odd {y | ∃ h ∈ H, h * x * h⁻¹ = y}.ncard := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQH, -, hdvd⟩ := isSylowOf_iff.1 hQ
  have hQC : Q ≤ H ⊓ centralizer {x} := le_inf hQH hxQ
  have h1 := ncard_conj_mul_card_inf_centralizer_D4 H x
  have h2 := Subgroup.relIndex_mul_card (H ⊓ centralizer {x}) H
  rw [inf_eq_left.2 (inf_le_left : H ⊓ centralizer {x} ≤ H)] at h2
  have h3 := Subgroup.relIndex_mul_relIndex Q (H ⊓ centralizer {x}) H hQC inf_le_left
  have hpos : 0 < Nat.card (H ⊓ centralizer {x} : Subgroup G) := Nat.card_pos
  have h4 : {y | ∃ h ∈ H, h * x * h⁻¹ = y}.ncard = (H ⊓ centralizer {x}).relIndex H := by
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  rw [h4]
  refine Nat.not_even_iff_odd.1 fun he => hdvd ?_
  rw [← h3]
  exact Dvd.dvd.mul_left (even_iff_two_dvd.1 he) _

theorem exists_conj_le_of_isSylowOf_D4 {p : ℕ} [Fact p.Prime] {T H X : Subgroup G}
    (hT : IsSylowOf p T H) (hXH : X ≤ H) (hX : IsPGroup p X) :
    ∃ c ∈ H, ∀ x ∈ X, c⁻¹ * x * c ∈ T := by
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨Q, hQ⟩ := (hX.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXH hx⟩ : H) ∈ (Q : Subgroup H) := hQ hx
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  refine ⟨s, hs, ?_⟩
  have : (c : G) * s * (c : G)⁻¹ = x := by
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [Subgroup.subtype_apply, ← this]
  group

omit [Finite G] in
theorem mem_commutator_of_conj_eq {A : Type*} [Field A] {x : A → G}
    (hx : ∀ a b, x (a + b) = x a * x b) {K : Subgroup G} {h : G} (hh : h ∈ K) {μ : A}
    (hμ : μ ≠ 1) (hconj : ∀ a, h * x a * h⁻¹ = x (μ * a)) {a : A}
    (ha : x ((μ - 1)⁻¹ * a) ∈ K) : x a ∈ ⁅K, K⁆ := by
  have hc := commutator_mem_commutator hh ha
  rw [commutatorElement_def, hconj, ← map_neg_of_add hx, ← hx] at hc
  convert hc using 2
  have h1 : μ - 1 ≠ 0 := sub_ne_zero.2 hμ
  field_simp
  ring

theorem conj_mem_commutator_commutator {K : Subgroup G} {k x : G} (hk : k ∈ K)
    (hx : x ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆) : k * x * k⁻¹ ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆ := by
  have hk' : k ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun n hn =>
      conj_mem_commutator (le_normalizer hk) hn
  exact conj_mem_commutator hk' hx

end Generic

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem σ_σ_eq_of_tr {c : d.Γ} (hc : d.tr c = 0) : d.σ (d.σ c) = c + d.σ c := by
  have h := congrArg Subtype.val hc
  rw [coe_fixedTrace, ZeroMemClass.coe_zero] at h
  linear_combination h - (c + d.σ c) * (CharTwo.two_eq_zero (R := d.Γ))

theorem qComm_eq_of_tr {a b : d.Γ} (ha : d.tr a = 0) (hb : d.tr b = 0) :
    d.qComm a b = d.σ a * b + a * d.σ b := by
  rw [qComm, d.σ_σ_eq_of_tr ha, d.σ_σ_eq_of_tr hb]
  linear_combination (d.σ a * d.σ b) * (CharTwo.two_eq_zero (R := d.Γ))

theorem exists_qComm_eq_one : ∃ a b : d.Γ, d.tr a = 0 ∧ d.tr b = 0 ∧ d.qComm a b = 1 := by
  classical
  have hq := d.two_le_q
  have hcard : Nat.card {a : d.Γ // d.tr (a * 1) = 0} = q ^ 2 :=
    d.card_tr_mul_eq_zero one_ne_zero
  have h0 : d.tr 0 = 0 := Subtype.ext (by rw [coe_fixedTrace]; simp)
  obtain ⟨a, ha, ha0⟩ : ∃ a : d.Γ, d.tr a = 0 ∧ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton {a : d.Γ // d.tr (a * 1) = 0} := ⟨fun x y => Subtype.ext (by
      rw [hcon x.1 (by simpa using x.2), hcon y.1 (by simpa using y.2)])⟩
    have h1 := Finite.card_le_one_iff_subsingleton.2 this
    rw [hcard] at h1
    nlinarith
  obtain ⟨b, hb, hba⟩ : ∃ b : d.Γ, d.tr b = 0 ∧ ∀ l : d.Γ₀, b ≠ (l : d.Γ) * a := by
    by_contra hcon
    push Not at hcon
    choose l hl using hcon
    have hinj : Function.Injective (fun x : {a : d.Γ // d.tr (a * 1) = 0} =>
        l x.1 (by simpa using x.2)) := by
      intro x y hxy
      apply Subtype.ext
      rw [hl x.1 (by simpa using x.2), hl y.1 (by simpa using y.2)]
      simp only at hxy
      rw [hxy]
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hcard, d.card_Γ₀] at h1
    nlinarith
  set c := d.qComm a b with hc
  have hc' : c = d.σ a * b + a * d.σ b := d.qComm_eq_of_tr ha hb
  have hσc : d.σ c = c := by
    rw [hc', map_add, map_mul, map_mul, d.σ_σ_eq_of_tr ha, d.σ_σ_eq_of_tr hb]
    linear_combination (d.σ a * d.σ b) * (CharTwo.two_eq_zero (R := d.Γ))
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc'] at hc0
    have hσa : d.σ a ≠ 0 := fun h => ha0 (d.σ.injective (by rw [h, map_zero]))
    have e : d.σ (b / a) = b / a := by
      rw [map_div₀, div_eq_div_iff hσa ha0]
      linear_combination (-1 : d.Γ) * hc0 + (a * d.σ b) * (CharTwo.two_eq_zero (R := d.Γ))
    refine hba ⟨b / a, e⟩ ?_
    change b = b / a * a
    rw [div_mul_cancel₀ b ha0]
  set l : d.Γ₀ := ⟨c, hσc⟩ with hl
  have hl0 : l ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  refine ⟨a, ((l⁻¹ : d.Γ₀) : d.Γ) * b, ha, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [d.tr_smul, hb, ZeroMemClass.coe_zero, mul_zero]
  · have hσl : d.σ ((l⁻¹ : d.Γ₀) : d.Γ) = ((l⁻¹ : d.Γ₀) : d.Γ) := apply_coe_fixedSubfield _
    have e1 : d.qComm a (((l⁻¹ : d.Γ₀) : d.Γ) * b) = ((l⁻¹ : d.Γ₀) : d.Γ) * d.qComm a b := by
      rw [qComm, qComm, map_mul, map_mul, hσl, hσl]
      ring
    rw [e1, ← hc, Subfield.coe_inv]
    exact inv_mul_cancel₀ hc0

theorem x₄_commute (e e' : d.Γ) : Commute (d.x₄ e) (d.x₄ e') := by
  rw [Commute, SemiconjBy, ← d.x₄_add, ← d.x₄_add, add_comm]

theorem x₄_one_mem_commutator_S_inf :
    d.x₄ 1 ∈ ⁅d.S ⊓ centralizer ({d.x₄ 1} : Set X), d.S ⊓ centralizer ({d.x₄ 1} : Set X)⁆ := by
  set K := d.S ⊓ centralizer ({d.x₄ 1} : Set X) with hK
  obtain ⟨a, b, ha, hb, hab⟩ := d.exists_qComm_eq_one
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [qComm, map_zero, map_zero, zero_mul, zero_mul, add_zero] at hab
    exact zero_ne_one hab
  have hmem : ∀ g : X, g ∈ d.S → g * d.x₄ 1 = d.x₄ 1 * g → g ∈ K := fun g hg hc =>
    ⟨hg, mem_centralizer_singleton_iff.2 hc⟩
  have hx₁ : d.x₁ a ∈ K := hmem _ (d.U₁_le_S (d.x₁_mem_U₁ a)) (by
    rw [← commutatorElement_eq_one_iff_mul_comm, d.comm₁₄, mul_one]
    change d.x₅ (d.tr a) = 1
    rw [ha, d.x₅_zero])
  have hx₃ : d.x₃ b ∈ K := hmem _ (d.U₃_le_S (d.x₃_mem_U₃ b)) (by
    rw [← commutatorElement_eq_one_iff_mul_comm, d.comm₃₄, mul_one]
    change d.x₆ (d.tr b) = 1
    rw [hb, d.x₆_zero])
  have hx₄ : ∀ e, d.x₄ e ∈ K := fun e => hmem _ (d.U₄_le_S (d.x₄_mem_U₄ e)) (d.x₄_commute e 1)
  have hx₂ : d.x₂ 1 ∈ K := hmem _ (d.U₂_le_S (d.x₂_mem_U₂ 1)) (d.commute₂₄ 1 1)
  have hx₅ : ∀ c, d.x₅ c ∈ K := fun c => hmem _ (d.U₅_le_S (d.x₅_mem_U₅ c)) (d.commute₄₅ 1 c).symm
  have hU₅ : ∀ c, d.x₅ c ∈ ⁅K, K⁆ := by
    intro c
    obtain ⟨e, he⟩ := d.exists_tr_eq c
    have h := commutator_mem_commutator hx₁ (hx₄ (a⁻¹ * e))
    rw [d.comm₁₄, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at h
    change d.x₅ (d.tr e) ∈ _ at h
    rwa [he] at h
  have hU₆ : ∀ c, d.x₆ c ∈ ⁅K, K⁆ := by
    intro c
    have h := commutator_mem_commutator hx₂ (hx₅ c)
    rwa [d.comm₂₅, one_mul] at h
  have h := commutator_mem_commutator hx₁ hx₃
  rw [d.comm₁₃] at h
  change d.x₄ (d.qComm a b) * _ * _ ∈ _ at h
  rw [hab] at h
  have h' := mul_mem (mul_mem h (inv_mem (hU₆ (d.tr (a * d.σ b * d.σ (d.σ b))))))
    (inv_mem (hU₅ (d.tr (a * d.σ a * d.σ (d.σ b)))))
  rwa [mul_inv_cancel_right, mul_inv_cancel_right] at h'

theorem root_mem_commutator_centralizer_x₄_one (hq : 4 ≤ q) :
    (∀ a, d.tr a = 0 → d.x₁ a ∈ ⁅centralizer ({d.x₄ 1} : Set X),
      centralizer ({d.x₄ 1} : Set X)⁆) ∧
    (∀ a, d.tr a = 0 → d.x₃ a ∈ ⁅centralizer ({d.x₄ 1} : Set X),
      centralizer ({d.x₄ 1} : Set X)⁆) ∧
    (∀ a, d.x₂ a ∈ ⁅centralizer ({d.x₄ 1} : Set X), centralizer ({d.x₄ 1} : Set X)⁆) ∧
    ∀ a, d.x₅ a ∈ ⁅centralizer ({d.x₄ 1} : Set X), centralizer ({d.x₄ 1} : Set X)⁆ := by
  have := d.finite
  set K := centralizer ({d.x₄ 1} : Set X) with hK
  obtain ⟨β, hβ⟩ : ∃ β : (d.Γ₀)ˣ, β ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (d.Γ₀)ˣ := ⟨fun x y => by rw [hcon x, hcon y]⟩
    have h1 := Finite.card_le_one_iff_subsingleton.2 this
    rw [d.card_units_Γ₀] at h1
    omega
  have hβ' : (β : d.Γ₀) ≠ 1 := fun h => hβ (Units.ext h)
  have hβi : ((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) ≠ 1 := fun h => hβ (inv_eq_one.1 (Units.ext h))
  have hβ2 : ((β ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) ≠ 1 := fun h => hβ (d.units₀_eq_one_of_sq (Units.ext h))
  set hb := d.hA β with hhb
  have hσ : ∀ l : d.Γ₀, d.σ (l : d.Γ) = l := fun l => apply_coe_fixedSubfield l
  have hbK : hb ∈ K := by
    have h4 : hb ∈ d.J₄ := by rw [d.J₄_eq_range_hA]; exact ⟨β, rfl⟩
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h4.2 _ (d.x₄_mem_U₄ 1)).symm
  have hmem : ∀ g : X, g * d.x₄ 1 = d.x₄ 1 * g → g ∈ K := fun g hc =>
    mem_centralizer_singleton_iff.2 hc
  have hcoe : ∀ l l' : (d.Γ₀)ˣ, ((l * l' : (d.Γ₀)ˣ) : d.Γ₀) = (l : d.Γ₀) * (l' : d.Γ₀) :=
    fun _ _ => rfl
  have hc₁ : ∀ a, hb * d.x₁ a * hb⁻¹ = d.x₁ (((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) * a) := fun a => by
    rw [hhb, hA_apply, d.torus_x₁, coe_unitsIncl]
  have hc₃ : ∀ a, hb * d.x₃ a * hb⁻¹ = d.x₃ (((β : (d.Γ₀)ˣ) : d.Γ₀) * a) := fun a => by
    rw [hhb, hA_apply, d.torus_x₃, coe_unitsIncl, ← Subfield.coe_mul, ← hcoe,
      show β ^ 2 * β⁻¹ = β by group]
  have hc₂ : ∀ a, hb * d.x₂ a * hb⁻¹ = d.x₂ (((β ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) * a) := fun a => by
    rw [hhb, hA_apply, d.torus_x₂]
  have hc₅ : ∀ a, hb * d.x₅ a * hb⁻¹ = d.x₅ (((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀) * a) := fun a => by
    rw [hhb, hA_apply, d.torus_x₅, coe_unitsIncl]
    congr 1
    refine congrArg (· * a) (Subtype.ext ?_)
    rw [Subfield.coe_mul, coe_fixedNorm, hσ, hσ, ← Subfield.coe_mul, ← Subfield.coe_mul,
      ← Subfield.coe_mul, ← hcoe, ← hcoe, ← hcoe, show β ^ 2 * (β⁻¹ * β⁻¹ * β⁻¹) = β⁻¹ by group]
  have hx₁K : ∀ a, d.tr a = 0 → d.x₁ a ∈ K := fun a ha => hmem _ (by
    rw [← commutatorElement_eq_one_iff_mul_comm, d.comm₁₄, mul_one]
    change d.x₅ (d.tr a) = 1
    rw [ha, d.x₅_zero])
  have hx₃K : ∀ a, d.tr a = 0 → d.x₃ a ∈ K := fun a ha => hmem _ (by
    rw [← commutatorElement_eq_one_iff_mul_comm, d.comm₃₄, mul_one]
    change d.x₆ (d.tr a) = 1
    rw [ha, d.x₆_zero])
  have hx₂K : ∀ a, d.x₂ a ∈ K := fun a => hmem _ (d.commute₂₄ a 1)
  have hx₅K : ∀ a, d.x₅ a ∈ K := fun a => hmem _ (d.commute₄₅ 1 a).symm
  have htr : ∀ (μ : d.Γ₀) (a : d.Γ), d.tr a = 0 → d.tr (((μ : d.Γ) - 1)⁻¹ * a) = 0 := by
    intro μ a ha
    have e : ((μ : d.Γ) - 1)⁻¹ = (((μ - 1)⁻¹ : d.Γ₀) : d.Γ) := by
      rw [Subfield.coe_inv, Subfield.coe_sub, Subfield.coe_one]
    refine Subtype.ext ?_
    rw [e, d.tr_smul, ha, ZeroMemClass.coe_zero, mul_zero]
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a => ?_, fun a => ?_⟩
  · exact mem_commutator_of_conj_eq d.x₁_add hbK (fun h => hβi (Subtype.ext (by simpa using h)))
      hc₁ (hx₁K _ (htr _ a ha))
  · exact mem_commutator_of_conj_eq d.x₃_add hbK (fun h => hβ' (Subtype.ext (by simpa using h)))
      hc₃ (hx₃K _ (htr _ a ha))
  · exact mem_commutator_of_conj_eq d.x₂_add hbK hβ2 hc₂ (hx₂K _)
  · exact mem_commutator_of_conj_eq d.x₅_add hbK hβi hc₅ (hx₅K _)

theorem x₄_one_mem_commutator_commutator (hq : 4 ≤ q) :
    d.x₄ 1 ∈ ⁅⁅centralizer ({d.x₄ 1} : Set X), centralizer ({d.x₄ 1} : Set X)⁆,
      ⁅centralizer ({d.x₄ 1} : Set X), centralizer ({d.x₄ 1} : Set X)⁆⁆ := by
  have := d.finite
  set K := centralizer ({d.x₄ 1} : Set X) with hK
  obtain ⟨hx₁', hx₃', hx₂', hx₅'⟩ := d.root_mem_commutator_centralizer_x₄_one hq
  have hvK : d.v ∈ K := mem_centralizer_singleton_iff.2 (by
    have h := d.v_x₄ 1
    calc d.v * d.x₄ 1 = d.v * d.x₄ 1 * d.v * d.v := by rw [mul_assoc _ d.v, d.v_mul_self, mul_one]
      _ = d.x₄ 1 * d.v := by rw [h])
  have hU₆ : ∀ c, d.x₆ c ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆ := fun c => by
    have h := commutator_mem_commutator (hx₂' 1) (hx₅' c)
    rwa [d.comm₂₅, one_mul] at h
  have hU₅ : ∀ c, d.x₅ c ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆ := fun c => by
    have h := conj_mem_commutator_commutator hvK (hU₆ c)
    have e : d.v * d.x₆ c * d.v⁻¹ = d.x₅ c := by
      rw [← d.v_x₅ c, d.v_inv]
      calc d.v * (d.v * d.x₅ c * d.v) * d.v = (d.v * d.v) * d.x₅ c * (d.v * d.v) := by group
        _ = d.x₅ c := by rw [d.v_mul_self, one_mul, mul_one]
    rwa [e] at h
  obtain ⟨a, b, ha, hb', hab⟩ := d.exists_qComm_eq_one
  have h := commutator_mem_commutator (hx₁' a ha) (hx₃' b hb')
  rw [d.comm₁₃] at h
  change d.x₄ (d.qComm a b) * _ * _ ∈ _ at h
  rw [hab] at h
  have h' := mul_mem (mul_mem h (inv_mem (hU₆ (d.tr (a * d.σ b * d.σ (d.σ b))))))
    (inv_mem (hU₅ (d.tr (a * d.σ a * d.σ (d.σ b)))))
  rwa [mul_inv_cancel_right, mul_inv_cancel_right] at h'

theorem x₆_one_mem_commutator_commutator_S : d.x₆ 1 ∈ ⁅⁅d.S, d.S⁆, ⁅d.S, d.S⁆⁆ := by
  rw [d.commutator_S_eq, d.commutator_F_eq]
  exact d.x₆_mem_V 1

theorem S_le_centralizer_x₆_one : d.S ≤ centralizer ({d.x₆ 1} : Set X) := fun _ hs =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (d.S_le_centralizer_V hs) _
    (d.x₆_mem_V 1)).symm

end TrialityD4Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem zpow_eq_one_or_eq (h : Setup G L f t) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  have hk : t ^ k = t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.ht]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk, h0, zpow_zero]
  · right
    rw [hk, h1, zpow_one]

theorem mem_sup_zpowers_iff (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L) {x : G} :
    x ∈ E ⊔ zpowers t ↔ x ∈ E ∨ t * x ∈ E := by
  have hcomm : ∀ e ∈ E, ∀ y ∈ zpowers t, e * y = y * e := fun e he y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL e (hEL he) : Commute e t) k).eq
  constructor
  · intro hx
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (zpowers t) hcomm).2
    have hx' : x ∈ ((E ⊔ zpowers t : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨e, he, y, hy, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    beta_reduce
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · left
      rw [hk, mul_one]
      exact he
    · right
      rw [hk, hcomm e he t (mem_zpowers t), ← mul_assoc, h.t_mul_t, one_mul]
      exact he
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have e : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hx)

theorem mem_or_mul_mem_of_mem_sup_kernel (h : Setup G L f t) {x : G}
    (hx : x ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) (hx2 : x * x = 1) :
    x ∈ L ∨ t * x ∈ L := by
  have hx' : x ∈ ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) :
      Set G) := hx
  rw [h.coe_sup_kernel] at hx'
  obtain ⟨l, hl, c, hc, rfl⟩ := hx'
  beta_reduce at hx2 ⊢
  have hc' : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hc
  have hcL : c ∈ centralizer (L : Set G) := (Subgroup.mem_inf.1 hc').1
  have hlc : l * c = c * l := mem_centralizer_iff.1 hcL l hl
  have hll : l * l * (c * c) = 1 := by
    rw [← hx2]
    calc l * l * (c * c) = l * (l * c) * c := by group
      _ = l * (c * l) * c := by rw [hlc]
      _ = l * c * (l * c) := by group
  have hc2 : c * c = 1 := by
    have hmem : l * l ∈ L ⊓ centralizer (L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem hl hl, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hll]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hcL hcL)
    rw [h.inf_centralizer_eq_bot, mem_bot] at hmem
    rwa [hmem, one_mul] at hll
  by_cases hc1 : c = 1
  · left
    rw [hc1, mul_one]
    exact hl
  · right
    have hct : c = t := h.kernel.2.2.1 c hc' (orderOf_eq_prime (by rw [sq]; exact hc2) hc1)
    rw [hct] at hlc ⊢
    rw [hlc, ← mul_assoc, h.t_mul_t, one_mul]
    exact hl

section YamadaR

variable {q : ℕ}

theorem S_le_centralizer (h : Setup G L f t) (d : TrialityD4Data L q) :
    d.S.map L.subtype ≤ centralizer ({t} : Set G) :=
  (map_subtype_le _).trans h.L_le_centralizer

theorem yamadaR_le_centralizer (h : Setup G L f t) (d : TrialityD4Data L q) :
    yamadaR d t ≤ centralizer ({t} : Set G) :=
  sup_le (h.S_le_centralizer d) inf_le_right

omit [Finite G] in
theorem S_commute_kernel (d : TrialityD4Data L q) (t : G) :
    ∀ x ∈ d.S.map L.subtype, ∀ y ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G),
      x * y = y * x :=
  fun x hx _ hy => mem_centralizer_iff.1 (mem_inf.1 hy).1 x (map_subtype_le _ hx)

theorem coe_yamadaR (_h : Setup G L f t) (d : TrialityD4Data L q) :
    ((yamadaR d t : Subgroup G) : Set G) = ((d.S.map L.subtype : Subgroup G) : Set G) *
      ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
  (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ (S_commute_kernel d t)).2

theorem card_yamadaR (h : Setup G L f t) (d : TrialityD4Data L q) :
    Nat.card (yamadaR d t) =
      Nat.card d.S *
        Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ (S_commute_kernel d t)).1
  have hinf : d.S.map L.subtype ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf (map_subtype_le _) inf_le_left).trans h.inf_centralizer_eq_bot.le)
  rw [hinf, Subgroup.card_bot, mul_one, card_map_of_injective L.subtype_injective] at hc
  exact hc

theorem yamadaR_inf_L (h : Setup G L f t) (d : TrialityD4Data L q) :
    yamadaR d t ⊓ L = d.S.map L.subtype := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left (map_subtype_le _))
  obtain ⟨hxR, hxL⟩ := mem_inf.1 hx
  have hx' : x ∈ ((yamadaR d t : Subgroup G) : Set G) := hxR
  rw [h.coe_yamadaR d] at hx'
  obtain ⟨s, hs, c, hc, rfl⟩ := hx'
  beta_reduce at hxL ⊢
  have hcL : c ∈ L := by
    have := mul_mem (inv_mem (map_subtype_le _ hs)) hxL
    rwa [inv_mul_cancel_left] at this
  have hc1 : c = 1 := by
    have : c ∈ L ⊓ centralizer (L : Set G) := ⟨hcL, (mem_inf.1 hc).1⟩
    rwa [h.inf_centralizer_eq_bot, mem_bot] at this
  rw [hc1, mul_one]
  exact hs

theorem isSylowOf_yamadaR (h : Setup G L f t) (d : TrialityD4Data L q) :
    IsSylowOf 2 (yamadaR d t) (L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardLT : Nat.card (L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :
      Subgroup G) = Nat.card L *
        Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L
      (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
      fun l hl _ hc => mem_centralizer_iff.1 (mem_inf.1 hc).1 l hl).1
    have hinf : L ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf le_rfl inf_le_left).trans h.inf_centralizer_eq_bot.le)
    rwa [hinf, Subgroup.card_bot, mul_one] at hc
  have hT : Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) =
      2 ^ (Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :
        Subgroup G)).factorization 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h.kernel.2.1
    rw [hn, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hS : Nat.card d.S = 2 ^ (Nat.card L).factorization 2 := by
    rw [← hP, Sylow.card_eq_multiplicity]
  refine isSylowOf_of_card (sup_le_sup_right (map_subtype_le _) _) ?_
  rw [h.card_yamadaR d, hS, hcardLT,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add, ← hT]

theorem exists_isSylowOf_le (h : Setup G L f t) (d : TrialityD4Data L q) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (centralizer ({t} : Set G)) ∧ yamadaR d t ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRC := h.yamadaR_le_centralizer d
  have hR2 : IsPGroup 2 ((yamadaR d t).subgroupOf (centralizer ({t} : Set G))) :=
    (h.isSylowOf_yamadaR d).isPGroup.comap_subtype
  obtain ⟨Q, hQ⟩ := hR2.exists_le_sylow
  refine ⟨(Q : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype,
    ⟨Q, rfl⟩, fun r hr => ⟨⟨r, hRC hr⟩, hQ (mem_subgroupOf.2 hr), rfl⟩⟩

end YamadaR

section Derived

variable {q : ℕ}

theorem commutator_le_sup_kernel (h : Setup G L f t) (d : TrialityD4Data L q) :
    ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ ≤
      L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  rw [commutator_le]
  intro a ha b hb
  have hab := (h.act_mem_range_conj_iff ⁅(⟨a, ha⟩ : centralizer ({t} : Set G)), ⟨b, hb⟩⁆).1 (by
    rw [map_commutatorElement]
    exact d.commutatorElement_mem_range_conj _ _)
  exact hab

theorem commutator_le_of_le_sup_kernel (h : Setup G L f t) {H : Subgroup G}
    (hH : H ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) : ⁅H, H⁆ ≤ L := by
  rw [commutator_le]
  intro a ha b hb
  have ha' : a ∈ ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) :
      Set G) := hH ha
  have hb' : b ∈ ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) :
      Set G) := hH hb
  rw [h.coe_sup_kernel] at ha' hb'
  obtain ⟨l, hl, c, hc, rfl⟩ := ha'
  obtain ⟨l', hl', c', hc', rfl⟩ := hb'
  rw [commutatorElement_mul_mul_of_commute' (mem_centralizer_iff.1 hc.1 l' hl').symm
    (h.kernel_comm hc hc') (mem_centralizer_iff.1 hc'.1 l hl).symm]
  have hll := commutator_mem_commutator hl hl'
  rwa [h.commutator_L] at hll

theorem commutator_commutator_le (h : Setup G L f t) (d : TrialityD4Data L q) :
    ⁅⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆,
      ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆⁆ ≤ L :=
  h.commutator_le_of_le_sup_kernel (h.commutator_le_sup_kernel d)

theorem le_sup_kernel_of_isPGroup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : Odd f) {E : Subgroup G} (hE : IsPGroup 2 E) (hEC : E ≤ centralizer ({t} : Set G)) :
    E ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  intro x hx
  obtain ⟨m, hm⟩ := hE ⟨x, hx⟩
  have hm' : (⟨x, hEC hx⟩ : centralizer ({t} : Set G)) ^ 2 ^ m = 1 :=
    Subtype.ext (by
      have := congrArg Subtype.val hm
      simpa using this)
  refine (h.act_mem_range_conj_iff ⟨x, hEC hx⟩).1 ?_
  refine d.mem_range_conj_of_pow_eq_one (f := f) rfl hf (m := m) ?_
  rw [← map_pow, hm', map_one]

theorem commutator_le_of_isPGroup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : Odd f) {E : Subgroup G} (hE : IsPGroup 2 E) (hEC : E ≤ centralizer ({t} : Set G)) :
    ⁅E, E⁆ ≤ L :=
  h.commutator_le_of_le_sup_kernel (h.le_sup_kernel_of_isPGroup d hf hE hEC)

end Derived

section Yamada421

theorem card_sup_zpowers (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L) :
    Nat.card (E ⊔ zpowers t : Subgroup G) = 2 * Nat.card E := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL x (hEL hx) : Commute x t) k).eq
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (zpowers t) hcomm).1
  rw [inf_comm, h.zpowers_inf_L hEL, Subgroup.card_bot, mul_one, h.card_zpowers_t] at hc
  rw [hc, mul_comm]

theorem card_le_of_isElemAbelian (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {E : Subgroup G} (hEC : E ≤ centralizer ({t} : Set G)) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 * Nat.card (h.act.comp (inclusion hEC)).range ∧
      Nat.card (h.act.comp (inclusion hEC)).range ≤ (2 ^ f) ^ 5 := by
  set ψ := h.act.comp (inclusion hEC) with hψ
  have hker : Nat.card ψ.ker ≤ 2 := by
    have := h.kernel.1
    let κ : ψ.ker →* (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
      (E.subtype.comp ψ.ker.subtype).codRestrict _ fun x =>
        ⟨(h.act_eq_one_iff _).1 (MonoidHom.mem_ker.1 x.2), hEC (x : E).2⟩
    have hκ : Function.Injective κ := by
      intro x y hxy
      have h1 := congrArg
        (fun z : (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have : IsCyclic ψ.ker := isCyclic_of_injective κ hκ
    exact card_le_two_of_isCyclic' fun x => Subtype.ext (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
      exact hE.2 _ (x : E).2))
  refine ⟨?_, (d.card_le_of_isElemAbelian_aut rfl (isElemAbelian_range' hE ψ)).1⟩
  rw [← Subgroup.card_ker_mul_card_range ψ]
  exact Nat.mul_le_mul_right _ hker

theorem isElemAbelian_W_sup_zpowers (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsElemAbelian 2 (d.W.map L.subtype ⊔ zpowers t) ∧
      Nat.card (d.W.map L.subtype ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 5 := by
  have hW : IsElemAbelian 2 d.W :=
    ⟨⟨⟨fun a b => Subtype.ext (d.mul_comm_of_mem_W a.2 b.2)⟩⟩,
      fun x hx => by rw [sq]; exact d.mul_self_eq_one_of_mem_W hx⟩
  obtain ⟨hE, hcard⟩ := h.isElemAbelian_sup_zpowers (E := d.W.map L.subtype) (map_subtype_le _)
    (SectionRank.isElemAbelian_map hW L.subtype)
  exact ⟨hE, by rw [hcard, card_map_of_injective L.subtype_injective, d.card_W]⟩

theorem W_sup_zpowers_le_yamadaR (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    d.W.map L.subtype ⊔ zpowers t ≤ yamadaR d t :=
  sup_le_sup (map_mono d.W_le_S) ((zpowers_le).2 h.t_mem_kernel)

theorem pRank_centralizer_of_data (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    CFSG.Open.pRank 2 (centralizer ({t} : Set G)) = 5 * f + 1 := by
  have hq : 2 * (2 ^ f) ^ 5 = 2 ^ (5 * f + 1) := by
    rw [← pow_mul, pow_succ, mul_comm, mul_comm f 5]
  apply le_antisymm
  · refine SectionRank.pRank_le one_lt_two fun E hEC hE => ?_
    obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hEC hE
    rw [← hq]
    exact h1.trans (Nat.mul_le_mul_left 2 h2)
  · obtain ⟨hE, hcard⟩ := h.isElemAbelian_W_sup_zpowers d
    exact SectionRank.le_pRank one_lt_two
      ((h.W_sup_zpowers_le_yamadaR d).trans (h.yamadaR_le_centralizer d)) hE (hcard.trans hq)

theorem pRank_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {Q : Subgroup G}
    (hQC : Q ≤ centralizer ({t} : Set G)) (hRQ : yamadaR d t ≤ Q) :
    CFSG.Open.pRank 2 Q = 5 * f + 1 := by
  apply le_antisymm
  · rw [← h.pRank_centralizer_of_data d]
    exact SectionRank.pRank_mono one_lt_two hQC
  · obtain ⟨hE, hcard⟩ := h.isElemAbelian_W_sup_zpowers d
    refine SectionRank.le_pRank one_lt_two ((h.W_sup_zpowers_le_yamadaR d).trans hRQ) hE ?_
    rw [hcard, ← pow_mul, pow_succ, mul_comm, mul_comm f 5]

theorem le_yamadaR_of_isMulCommutative (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({t} : Set G))
    (hRQ : yamadaR d t ≤ Q) {V : Subgroup G} (hVQ : V ≤ Q) (hV : IsMulCommutative V)
    (hrV : 5 * f + 1 ≤ CFSG.Open.pRank 2 V) : V ≤ yamadaR d t := by
  have hrQ := h.pRank_eq d hQC hRQ
  have hrV' : CFSG.Open.pRank 2 V = 5 * f + 1 :=
    le_antisymm (hrQ ▸ SectionRank.pRank_mono one_lt_two hVQ) hrV
  set ψQ := h.act.comp (inclusion hQC) with hψQ
  have hQ' : IsPGroup 2 ψQ.range := hQ2.of_surjective ψQ.rangeRestrict ψQ.rangeRestrict_surjective
  have hSQ' : d.S.map MulAut.conj ≤ ψQ.range := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨⟨(s : G), hRQ (mem_sup_left ⟨s, hs, rfl⟩)⟩, h.act_of_mem_L s.2⟩
  have hVC := hVQ.trans hQC
  set ψV := h.act.comp (inclusion hVC) with hψV
  have hV'Q' : ψV.range ≤ ψQ.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨v, hVQ v.2⟩, rfl⟩
  have hV' : IsMulCommutative ψV.range := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨z, hz⟩ := b.2
    change (a : MulAut L) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm' x z]
  have hrV2 : 5 * f ≤ CFSG.Open.pRank 2 ψV.range := by
    obtain ⟨E, hEV, hE, hcardE⟩ := SectionRank.exists_pRank one_lt_two V
    rw [hrV'] at hcardE
    have hEC := hEV.trans hVC
    obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hEC hE
    have hcard' : Nat.card (h.act.comp (inclusion hEC)).range = 2 ^ (5 * f) := by
      apply le_antisymm
      · rw [← pow_mul, mul_comm] at h2
        exact h2
      · rw [hcardE, pow_succ, mul_comm] at h1
        exact Nat.le_of_mul_le_mul_left h1 two_pos
    refine SectionRank.le_pRank one_lt_two ?_ (isElemAbelian_range' hE _) hcard'
    rintro _ ⟨e, rfl⟩
    exact ⟨⟨e, hEV e.2⟩, rfl⟩
  have key := (d.yamada_3_14 rfl hQ' hSQ').1 _ hV'Q' hV' hrV2
  intro v hv
  obtain ⟨s, hs, hse⟩ := key ⟨⟨v, hv⟩, rfl⟩
  have hsC := h.L_le_centralizer s.2
  have hc : (s : G)⁻¹ * v ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨(h.act_eq_one_iff ⟨_, mul_mem (inv_mem hsC) (hVC hv)⟩).1 ?_,
      mul_mem (inv_mem hsC) (hVC hv)⟩
    have e : (⟨(s : G)⁻¹ * v, mul_mem (inv_mem hsC) (hVC hv)⟩ : centralizer ({t} : Set G)) =
        (⟨(s : G), hsC⟩ : centralizer ({t} : Set G))⁻¹ * ⟨v, hVC hv⟩ := rfl
    have hse' : h.act ⟨v, hVC hv⟩ = MulAut.conj s := hse.symm
    rw [e, map_mul, map_inv, h.act_of_mem_L s.2, hse']
    exact inv_mul_cancel _
  rw [show v = (s : G) * ((s : G)⁻¹ * v) by group]
  exact mul_mem (mem_sup_left ⟨s, hs, rfl⟩) (mem_sup_right hc)

theorem rankThompson_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({t} : Set G))
    (hRQ : yamadaR d t ≤ Q) :
    rankJr Q =
      yamadaR d t := by
  have hrQ := h.pRank_eq d hQC hRQ
  unfold rankJr
  apply le_antisymm
  · exact iSup₂_le fun V ⟨hVQ, hV, hrV⟩ =>
      h.le_yamadaR_of_isMulCommutative d hQ2 hQC hRQ hVQ hV (hrV.trans hrQ).ge
  · have := h.kernel.1
    have hfam : ∀ A : Subgroup L, A ≤ d.S → IsMulCommutative A →
        CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 d.S →
        A.map L.subtype ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) ≤
          rankJr Q := by
      intro A hAS hA hrA
      have hAQ : A.map L.subtype ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) ≤ Q :=
        (sup_le_sup_right (map_mono hAS) _).trans hRQ
      have : IsMulCommutative (A.map L.subtype) := isMulCommutative_map hA _
      refine le_iSup₂_of_le (A.map L.subtype ⊔ (centralizer (L : Set G) ⊓
        centralizer ({t} : Set G))) ⟨hAQ, isMulCommutative_sup' fun a ha c hc =>
          S_commute_kernel d t a (map_mono hAS ha) c hc, ?_⟩ le_rfl
      refine le_antisymm (SectionRank.pRank_mono one_lt_two hAQ) ?_
      obtain ⟨E, hEA, hE, hcardE⟩ := SectionRank.exists_pRank one_lt_two A
      rw [hrA, (d.yamada_3_11_3 rfl).1] at hcardE
      obtain ⟨hE', hcard⟩ := h.isElemAbelian_sup_zpowers (E := E.map L.subtype)
        (map_subtype_le _) (SectionRank.isElemAbelian_map hE _)
      refine hrQ ▸ SectionRank.le_pRank one_lt_two
        (sup_le_sup (map_mono hEA) ((zpowers_le).2 h.t_mem_kernel)) hE' ?_
      rw [hcard, card_map_of_injective L.subtype_injective, hcardE, ← pow_succ']
    have hS : d.S.map L.subtype ≤
        rankJr Q := by
      rw [← (d.yamada_3_11_3 rfl).2.2, map_le_iff_le_comap]
      exact iSup₂_le fun A ⟨hAS, hA, hrA⟩ =>
        map_le_iff_le_comap.1 (le_sup_left.trans (hfam A hAS hA hrA))
    have hW : IsElemAbelian 2 d.W :=
      ⟨⟨⟨fun a b => Subtype.ext (d.mul_comm_of_mem_W a.2 b.2)⟩⟩,
        fun x hx => by rw [sq]; exact d.mul_self_eq_one_of_mem_W hx⟩
    have hrW : CFSG.Open.pRank 2 d.W = CFSG.Open.pRank 2 d.S := by
      rw [(d.yamada_3_11_3 rfl).1]
      exact d.pRank_eq_of_le rfl le_rfl hW d.card_W
    exact sup_le hS (le_sup_right.trans (hfam d.W d.W_le_S hW.1 hrW))

end Yamada421

section Yamada422

omit [Finite G] in
theorem map_conj_le_centralizer {K : Subgroup G} {g : G}
    (hK : K ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    K.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have hky : k * (g * t * g⁻¹) = g * t * g⁻¹ * k := mem_centralizer_singleton_iff.1 (hK hk)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc g⁻¹ * k * g * t = g⁻¹ * (k * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹ * k) * g := by rw [hky]
    _ = t * (g⁻¹ * k * g) := by group

theorem conj_ne_of_mem_commutator_commutator (h : Setup G L f t) {q : ℕ}
    (d : TrialityD4Data L q) {K : Subgroup G} {y : G} (hKy : K ≤ centralizer ({y} : Set G))
    (hy : y ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆) (g : G) : g * t * g⁻¹ ≠ y := by
  intro hg
  rw [← hg] at hKy hy
  have hK'C := map_conj_le_centralizer hKy
  have h1 := commutator_mono (commutator_mono hK'C hK'C) (commutator_mono hK'C hK'C)
  have h2 : t ∈ ⁅⁅K.map (MulAut.conj g⁻¹).toMonoidHom, K.map (MulAut.conj g⁻¹).toMonoidHom⁆,
      ⁅K.map (MulAut.conj g⁻¹).toMonoidHom, K.map (MulAut.conj g⁻¹).toMonoidHom⁆⁆ := by
    rw [← map_commutator, ← map_commutator]
    refine ⟨g * t * g⁻¹, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  exact h.t_not_mem_L ((h1.trans (h.commutator_commutator_le d)) h2)

theorem conj_ne_of_mem_commutator_of_isPGroup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : Odd f) {K : Subgroup G} (hK : IsPGroup 2 K) {y : G}
    (hKy : K ≤ centralizer ({y} : Set G)) (hy : y ∈ ⁅K, K⁆) (g : G) : g * t * g⁻¹ ≠ y := by
  intro hg
  rw [← hg] at hKy hy
  have hK'C := map_conj_le_centralizer hKy
  have h2 : t ∈ ⁅K.map (MulAut.conj g⁻¹).toMonoidHom, K.map (MulAut.conj g⁻¹).toMonoidHom⁆ := by
    rw [← map_commutator]
    refine ⟨g * t * g⁻¹, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  exact h.t_not_mem_L (h.commutator_le_of_isPGroup d hf (hK.map _) hK'C h2)

theorem conj_not_mem_L (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (g : G) :
    g * t * g⁻¹ ∉ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hy
  set y : L := ⟨g * t * g⁻¹, hy⟩ with hydef
  have hy2 : orderOf y = 2 := by
    rw [← orderOf_injective L.subtype L.subtype_injective y]
    change orderOf (MulAut.conj g t) = 2
    rw [MulEquiv.orderOf_eq, h.ht]
  obtain ⟨m, hm⟩ := d.involution_conj y hy2
  have hg' : (m : G) * g * t * ((m : G) * g)⁻¹ = ((m * y * m⁻¹ : L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hydef]
    group
  have hcent : ∀ {K : Subgroup L} {z : L}, K ≤ centralizer ({z} : Set L) →
      K.map L.subtype ≤ centralizer ({(z : G)} : Set G) := by
    intro K z hK
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hK hk))
  rcases hm with hm | hm
  · rw [hm] at hg'
    refine h.conj_ne_of_mem_commutator_commutator d (K := d.S.map L.subtype)
      (hcent d.S_le_centralizer_x₆_one) ?_ ((m : G) * g) hg'
    rw [← map_commutator, ← map_commutator]
    exact ⟨_, d.x₆_one_mem_commutator_commutator_S, rfl⟩
  · rw [hm] at hg'
    rcases Nat.even_or_odd f with hf | hf
    · have hq : 4 ≤ 2 ^ f := by
        obtain ⟨e, rfl⟩ := hf
        have he : 1 ≤ e := by have := h.one_le; omega
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (e + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine h.conj_ne_of_mem_commutator_commutator d
        (K := (centralizer ({d.x₄ 1} : Set L)).map L.subtype) (hcent le_rfl) ?_ ((m : G) * g) hg'
      rw [← map_commutator, ← map_commutator]
      exact ⟨_, d.x₄_one_mem_commutator_commutator hq, rfl⟩
    · have hS2 : IsPGroup 2 d.S := by
        obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
        rw [← hP]
        exact P.isPGroup'
      refine h.conj_ne_of_mem_commutator_of_isPGroup d hf
        (K := (d.S ⊓ centralizer ({d.x₄ 1} : Set L)).map L.subtype)
        ((hS2.to_le inf_le_left).map _) (hcent inf_le_right) ?_ ((m : G) * g) hg'
      rw [← map_commutator]
      exact ⟨_, d.x₄_one_mem_commutator_S_inf, rfl⟩

end Yamada422

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
