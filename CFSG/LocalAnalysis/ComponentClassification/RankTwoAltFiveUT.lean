module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveScalar

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

omit [Finite G] h hPC in
theorem P_comm_V₀ {w x : G} (hw : w ∈ V₀) (hx : x ∈ P) : x * w = w * x :=
  (mem_centralizer_iff.mp (hP.le hx).2.1 w hw).symm

omit [Finite G] h hPC in
theorem P_mod {x v : G} (hx : x ∈ P) (hv : v ∈ R ⊔ T) : v⁻¹ * (x * v * x⁻¹) ∈ V₀ :=
  (hP.le hx).2.2 v hv

theorem P_fixed {x v : G} (hx : x ∈ P) (hxV : x ∉ R ⊔ T) (hv : v ∈ R ⊔ T)
    (hfix : x * v * x⁻¹ = v) : v ∈ V₀ := by
  refine h.mem_V₀_of_fixed (hP.le hx) (fun hxC => hxV ?_) hv hfix
  rw [← hPC]
  exact mem_inf.mpr ⟨hx, hxC⟩

theorem P_sq_mem_V {x : G} (hx : x ∈ P) : x * x ∈ R ⊔ T := by
  rw [← hPC]
  exact mem_inf.mpr ⟨mul_mem hx hx, h.mul_self_mem_centralizer (hP.le hx)⟩

theorem P_sq_mem_V₀ {x : G} (hx : x ∈ P) (hxV : x ∉ R ⊔ T) : x * x ∈ V₀ := by
  refine h.P_fixed hP hPC hx hxV (h.P_sq_mem_V hP hPC hx) ?_
  group

theorem P_comm_mem_V {x x' : G} (hx : x ∈ P) (hx' : x' ∈ P) :
    x * x' * x⁻¹ * x'⁻¹ ∈ R ⊔ T := by
  rw [← hPC]
  exact mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hx hx') (inv_mem hx)) (inv_mem hx'),
    h.commutator_mem_centralizer (hP.le hx) (hP.le hx')⟩

theorem P_invol_coset {c v : G} (hc : c ∈ P) (hcV : c ∉ R ⊔ T) (hc2 : c * c = 1)
    (hv : v ∈ R ⊔ T) (hcv : c * v * (c * v) = 1) : v ∈ V₀ := by
  refine h.P_fixed hP hPC hc hcV hv ?_
  have hci : c⁻¹ = c := by
    calc c⁻¹ = c⁻¹ * (c * c) := by rw [hc2, mul_one]
      _ = c := by group
  have hvv : v * v = 1 := h.mul_self hv
  calc c * v * c⁻¹ = c * v * c⁻¹ * (v * v) := by rw [hvv, mul_one]
    _ = (c * v * (c * v)) * v := by rw [hci]; group
    _ = v := by rw [hcv, one_mul]

theorem P_exists_invol {x : G} (hx : x ∈ P) (hxV : x ∉ R ⊔ T) :
    ∃ v ∈ R ⊔ T, x * v * (x * v) = 1 := by
  have hx2 := h.P_sq_mem_V₀ hP hPC hx hxV
  let φ : ↥(R ⊔ T) →* ↥V₀ :=
    { toFun := fun v => ⟨(v : G)⁻¹ * (x * v * x⁻¹), P_mod hP hx v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have ha := P_mod hP hx a.2
        have hcomm := h.comm (h.V₀_le ha) (inv_mem b.2)
        simp only [coe_mul]
        calc ((a : G) * b)⁻¹ * (x * (a * b) * x⁻¹) =
            (b : G)⁻¹ * ((a : G)⁻¹ * (x * a * x⁻¹)) * (x * b * x⁻¹) := by group
          _ = ((a : G)⁻¹ * (x * a * x⁻¹)) * (b : G)⁻¹ * (x * b * x⁻¹) := by rw [← hcomm]
          _ = ((a : G)⁻¹ * (x * a * x⁻¹)) * ((b : G)⁻¹ * (x * b * x⁻¹)) := by group }
  have hker : Nat.card φ.ker = 4 := by
    have h1 : φ.ker = V₀.subgroupOf (R ⊔ T) := by
      ext v
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro hv
        have h2 : (v : G)⁻¹ * (x * v * x⁻¹) = 1 := congrArg Subtype.val hv
        refine h.P_fixed hP hPC hx hxV v.2 ?_
        calc x * v * x⁻¹ = v * ((v : G)⁻¹ * (x * v * x⁻¹)) := by group
          _ = v := by rw [h2, mul_one]
      · intro hv
        apply Subtype.ext
        change (v : G)⁻¹ * (x * v * x⁻¹) = 1
        rw [P_comm_V₀ hP hv hx]
        group
    rw [h1, ← h.card_V₀]
    exact Nat.card_congr (subgroupOfEquivOfLe h.V₀_le).toEquiv
  have hsurj : Function.Surjective φ := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, h.loc.card] at h1
    have h2 : Nat.card φ.range = 4 := by omega
    have htop : φ.range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h2, h.card_V₀])
    exact MonoidHom.range_eq_top.mp htop
  obtain ⟨v, hv⟩ := hsurj ⟨(x * x)⁻¹, inv_mem hx2⟩
  have hv' : (v : G)⁻¹ * (x * v * x⁻¹) = (x * x)⁻¹ := congrArg Subtype.val hv
  refine ⟨v, v.2, ?_⟩
  have hvv : (v : G) * v = 1 := h.mul_self v.2
  have e : x * v * x⁻¹ = v * (x * x)⁻¹ := by
    calc x * v * x⁻¹ = v * ((v : G)⁻¹ * (x * v * x⁻¹)) := by group
      _ = v * (x * x)⁻¹ := by rw [hv']
  calc x * v * (x * v) = (x * v * x⁻¹) * (x * x) * v := by group
    _ = v * (x * x)⁻¹ * (x * x) * v := by rw [e]
    _ = v * v := by group
    _ = 1 := hvv

theorem le_or_le_of_elemAbelian {V' : Subgroup G}
    (hV' : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (hV₀V' : V₀ ≤ V') {E : Subgroup G}
    (hEP : E ≤ P) (hE : IsElemAbelian 2 E) : E ≤ R ⊔ T ∨ E ≤ V' := by
  by_cases hEV' : E ≤ V'
  · exact Or.inr hEV'
  left
  obtain ⟨e, he, heV'⟩ := IsConcreteLE.not_le_iff_exists.mp hEV'
  have he2 : e * e = 1 := by rw [← sq]; exact hE.2 e he
  have heV : e ∈ R ⊔ T := by
    by_contra hnot
    exact heV' (hV' e (hEP he) he2 hnot)
  have he0 : e ∉ V₀ := fun h0 => heV' (hV₀V' h0)
  intro x hx
  by_contra hxV
  have hcomm : x * e * x⁻¹ = e := by
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨e, he⟩)
    simp only [coe_mul] at this
    rw [this]
    group
  exact he0 (h.P_fixed hP hPC (hEP hx) hxV heV hcomm)

theorem P_mul_self_mem_V₀ {x : G} (hx : x ∈ P) : x * x ∈ V₀ := by
  by_cases hxV : x ∈ R ⊔ T
  · rw [h.mul_self hxV]
    exact one_mem _
  · exact h.P_sq_mem_V₀ hP hPC hx hxV

theorem P_comm_mem_V₀_of_sq {x x' : G} (hx : x ∈ P) (hx' : x' ∈ P) :
    x * x' * x⁻¹ * x'⁻¹ ∈ V₀ := by
  have e : x * x' * x⁻¹ * x'⁻¹ = (x * x) * ((x⁻¹ * x') * (x⁻¹ * x')) * (x' * x')⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (h.P_mul_self_mem_V₀ hP hPC hx)
    (h.P_mul_self_mem_V₀ hP hPC (mul_mem (inv_mem hx) hx')))
    (inv_mem (h.P_mul_self_mem_V₀ hP hPC hx'))

theorem exists_Vprime_of_comm (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hcomm : ∀ {c₁ c₂ : G}, c₁ ∈ P → c₁ ∉ R ⊔ T → c₁ * c₁ = 1 → c₂ ∈ P → c₂ ∉ R ⊔ T →
      c₂ * c₂ = 1 → c₁ * c₂ = c₂ * c₁) :
    ∃ V' : Subgroup G, V' ≤ P ∧ IsElemAbelian 2 V' ∧ Nat.card V' = 16 ∧
      (R ⊔ T) ⊓ V' = V₀ ∧ (R ⊔ T) ⊔ V' = P ∧
      (∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') ∧
      ∀ x ∈ V', x * x = 1 ∧ (x ∈ R ⊔ T → x ∈ V₀) := by
  have hcV : ∀ {a b : G}, a ∈ V₀ → b ∈ P → a * b ∈ R ⊔ T → b ∈ R ⊔ T := fun {a b} ha hb hab => by
    have := mul_mem (inv_mem (h.V₀_le ha)) hab
    simpa using this
  let V' : Subgroup G :=
    { carrier := {x | x ∈ P ∧ x * x = 1 ∧ (x ∈ R ⊔ T → x ∈ V₀)}
      mul_mem' := by
        rintro a b ⟨haP, ha2, haV⟩ ⟨hbP, hb2, hbV⟩
        refine ⟨mul_mem haP hbP, ?_, fun hab => ?_⟩
        · by_cases haV' : a ∈ R ⊔ T
          · have hab := P_comm_V₀ hP (haV haV') hbP
            calc a * b * (a * b) = a * (b * a) * b := by group
              _ = a * (a * b) * b := by rw [hab]
              _ = (a * a) * (b * b) := by group
              _ = 1 := by rw [ha2, hb2, one_mul]
          by_cases hbV' : b ∈ R ⊔ T
          · have hab := P_comm_V₀ hP (hbV hbV') haP
            calc a * b * (a * b) = a * (b * a) * b := by group
              _ = a * (a * b) * b := by rw [hab]
              _ = (a * a) * (b * b) := by group
              _ = 1 := by rw [ha2, hb2, one_mul]
          have hab := hcomm haP haV' ha2 hbP hbV' hb2
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hab]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
        · by_cases haV' : a ∈ R ⊔ T
          · have hbV' : b ∈ R ⊔ T := hcV (haV haV') hbP hab
            exact mul_mem (haV haV') (hbV hbV')
          have hai : a⁻¹ = a := by
            calc a⁻¹ = a⁻¹ * (a * a) := by rw [ha2, mul_one]
              _ = a := by group
          refine h.P_invol_coset hP hPC haP haV' ha2 hab ?_
          calc a * (a * b) * (a * (a * b)) = (a * a) * b * ((a * a) * b) := by group
            _ = 1 := by rw [ha2, one_mul, hb2]
      one_mem' := ⟨one_mem P, by simp, fun _ => one_mem V₀⟩
      inv_mem' := by
        rintro a ⟨haP, ha2, haV⟩
        have hai : a⁻¹ = a := by
          calc a⁻¹ = a⁻¹ * (a * a) := by rw [ha2, mul_one]
            _ = a := by group
        rw [hai]
        exact ⟨haP, ha2, haV⟩ }
  have hV'P : V' ≤ P := fun x hx => hx.1
  have hV'2 : ∀ x ∈ V', x * x = 1 := fun x hx => hx.2.1
  have hV'e : IsElemAbelian 2 V' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => by rw [sq]; exact hV'2 x hx⟩
    have h1 := hV'2 _ (mul_mem a.2 b.2)
    have h2 := hV'2 _ a.2
    have h3 := hV'2 _ b.2
    simp only [coe_mul]
    calc (a : G) * b = ((a : G) * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
      _ = (b : G) * a := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
  have hinf : (R ⊔ T) ⊓ V' = V₀ := by
    ext x
    constructor
    · rintro ⟨hxV, hxV'⟩
      exact hxV'.2.2 hxV
    · intro hx
      exact ⟨h.V₀_le hx, hVP (h.V₀_le hx), h.mul_self (h.V₀_le hx), fun _ => hx⟩
  have hsup : (R ⊔ T) ⊔ V' = P := by
    refine le_antisymm (sup_le hVP hV'P) fun x hx => ?_
    by_cases hxV : x ∈ R ⊔ T
    · exact mem_sup_left hxV
    obtain ⟨v, hv, hxv⟩ := h.P_exists_invol hP hPC hx hxV
    have hxvV : x * v ∉ R ⊔ T := fun he => hxV (by
      have := mul_mem he (inv_mem hv)
      simpa using this)
    have hxvV' : x * v ∈ V' := ⟨mul_mem hx (hVP hv), hxv, fun he => absurd he hxvV⟩
    have : x = (x * v) * v⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_right hxvV') (mem_sup_left (inv_mem hv))
  have hcard : Nat.card V' = 16 := by
    have hV'N : V' ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := fun x hx => (hP.le (hV'P hx)).1
    have h1 := card_sup_mul_card_inf_of_le hV'N
    rw [sup_comm, hsup, inf_comm, hinf, hP64, h.card_V₀, h.loc.card] at h1
    omega
  exact ⟨V', hV'P, hV'e, hcard, hinf, hsup, fun x hx hx2 hxV => ⟨hx, hx2, fun he => absurd he hxV⟩,
    fun x hx => ⟨hx.2.1, hx.2.2⟩⟩


section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem P_comm_mem_V₀ {x x' : G} (hx : x ∈ P) (hx' : x' ∈ P) :
    x * x' * x⁻¹ * x'⁻¹ ∈ V₀ := by
  obtain ⟨t, htP, htV, htN₀, -, htq, htPV⟩ := h.exists_scalar_P hIIa hP hPC
  have hc := h.P_comm_mem_V hP hPC hx hx'
  by_contra hc0
  apply htq _ hc hc0
  set v := x⁻¹ * (t * x * t⁻¹) with hv
  set v' := x'⁻¹ * (t * x' * t⁻¹) with hv'
  have hvV : v ∈ R ⊔ T := htPV x hx
  have hv'V : v' ∈ R ⊔ T := htPV x' hx'
  obtain ⟨w, hw, hcomm⟩ := comm_mul_mul (P := P) (V := R ⊔ T) h.V₀_le
    (fun w hw y hy => P_comm_V₀ hP hw hy) (fun a ha b hb => h.comm ha hb)
    (fun y hy v hv => P_mod hP hy hv) hx hx' hvV hv'V
  have h1 : t * (x * x' * x⁻¹ * x'⁻¹) * t⁻¹ =
      (x * v) * (x' * v') * (x * v)⁻¹ * (x' * v')⁻¹ := by
    rw [hv, hv']; group
  rw [h1, hcomm]
  have h2 : (x * x' * x⁻¹ * x'⁻¹)⁻¹ * ((x * x' * x⁻¹ * x'⁻¹) * w) = w := by group
  rw [h2]
  exact hw

theorem P_invol_comm {c₁ c₂ : G} (hc₁ : c₁ ∈ P) (hc₁V : c₁ ∉ R ⊔ T) (hc₁2 : c₁ * c₁ = 1)
    (hc₂ : c₂ ∈ P) (hc₂V : c₂ ∉ R ⊔ T) (hc₂2 : c₂ * c₂ = 1) : c₁ * c₂ = c₂ * c₁ := by
  obtain ⟨t, htP, htV, htN₀, htf, -, htPV⟩ := h.exists_scalar_P hIIa hP hPC
  have hcV₀ := h.P_comm_mem_V₀ hP hPC hIIa hc₁ hc₂
  have hw : ∀ c ∈ P, c ∉ R ⊔ T → c * c = 1 → c⁻¹ * (t * c * t⁻¹) ∈ V₀ := by
    intro c hc hcV hc2
    refine h.P_invol_coset hP hPC hc hcV hc2 (htPV c hc) ?_
    calc c * (c⁻¹ * (t * c * t⁻¹)) * (c * (c⁻¹ * (t * c * t⁻¹))) = t * (c * c) * t⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hw₁ := hw c₁ hc₁ hc₁V hc₁2
  have hw₂ := hw c₂ hc₂ hc₂V hc₂2
  set w₁ := c₁⁻¹ * (t * c₁ * t⁻¹) with hw₁def
  set w₂ := c₂⁻¹ * (t * c₂ * t⁻¹) with hw₂def
  have e₁ : t * c₁ * t⁻¹ = c₁ * w₁ := by rw [hw₁def]; group
  have e₂ : t * c₂ * t⁻¹ = c₂ * w₂ := by rw [hw₂def]; group
  have hz₁ : ∀ y ∈ P, y * w₁ = w₁ * y := fun y hy => P_comm_V₀ hP hw₁ hy
  have hz₂ : ∀ y ∈ P, y * w₂ = w₂ * y := fun y hy => P_comm_V₀ hP hw₂ hy
  have hfix : t * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * t⁻¹ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
    calc t * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * t⁻¹ =
        (t * c₁ * t⁻¹) * (t * c₂ * t⁻¹) * (t * c₁ * t⁻¹)⁻¹ * (t * c₂ * t⁻¹)⁻¹ := by group
      _ = (c₁ * w₁) * (c₂ * w₂) * (c₁ * w₁)⁻¹ * (c₂ * w₂)⁻¹ := by rw [e₁, e₂]
      _ = c₁ * (w₁ * c₂) * w₂ * w₁⁻¹ * c₁⁻¹ * w₂⁻¹ * c₂⁻¹ := by group
      _ = c₁ * c₂ * (w₁ * w₂ * w₁⁻¹) * c₁⁻¹ * w₂⁻¹ * c₂⁻¹ := by rw [← hz₁ c₂ hc₂]; group
      _ = c₁ * c₂ * w₂ * c₁⁻¹ * w₂⁻¹ * c₂⁻¹ := by
        rw [h.comm (h.V₀_le hw₁) (h.V₀_le hw₂)]; group
      _ = c₁ * c₂ * c₁⁻¹ * (w₂ * w₂⁻¹) * c₂⁻¹ := by
        rw [mul_assoc (c₁ * c₂) w₂ c₁⁻¹, ← hz₂ _ (inv_mem hc₁)]; group
      _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by group
  by_contra hne
  have hc1 : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ≠ 1 := fun he => hne (by
    calc c₁ * c₂ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ * (c₂ * c₁) := by group
      _ = c₂ * c₁ := by rw [he, one_mul])
  exact htf _ hcV₀ hc1 hfix

theorem exists_Vprime (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) :
    ∃ V' : Subgroup G, V' ≤ P ∧ IsElemAbelian 2 V' ∧ Nat.card V' = 16 ∧
      (R ⊔ T) ⊓ V' = V₀ ∧ (R ⊔ T) ⊔ V' = P ∧
      (∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') ∧
      ∀ x ∈ V', x * x = 1 ∧ (x ∈ R ⊔ T → x ∈ V₀) :=
  h.exists_Vprime_of_comm hP hPC hP64 hVP fun hc₁ hc₁V hc₁2 hc₂ hc₂V hc₂2 =>
    h.P_invol_comm hP hPC hIIa hc₁ hc₁V hc₁2 hc₂ hc₂V hc₂2

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
