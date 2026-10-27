module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsInv

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools
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
  (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
  {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V')
include hP hPC hIIa hV'

variable {y : G} (hyV : rightConjugate (R ⊔ T) y = V') (hyV' : rightConjugate V' y = R ⊔ T)
  (hyC : y ∈ centralizer (V₀ : Set G)) (hy2 : y * y = 1)
include hyV hyV' hyC hy2

theorem swap_inf_centralizer_le : P ⊓ centralizer ({y} : Set G) ≤ V₀ := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hyi : y⁻¹ = y := by
    calc y⁻¹ = y⁻¹ * (y * y) := by rw [hy2, mul_one]
      _ = y := by group
  have hyVV' : ∀ v ∈ R ⊔ T, y * v * y⁻¹ ∈ V' := fun v hv => by
    rw [← hyV'] at hv
    exact (mem_rightConjugate_iff _ _ _).mp hv
  have hyV'V : ∀ f ∈ V', y * f * y⁻¹ ∈ R ⊔ T := fun f hf => by
    rw [← hyV] at hf
    exact (mem_rightConjugate_iff _ _ _).mp hf
  have hyw : ∀ w ∈ V₀, y * w * y⁻¹ = w := fun w hw => by
    rw [← mem_centralizer_iff.mp hyC w hw]
    group
  have hVN' : ∀ v ∈ R ⊔ T, ∀ f ∈ V', v⁻¹ * f * v ∈ V' := by
    intro v hv f hf
    have hc := h.P_comm_mem_V₀ hP hPC hIIa (inv_mem (hV'.le hf)) (inv_mem (hVP hv))
    have e : v⁻¹ * f * v = f * (f⁻¹ * v⁻¹ * f⁻¹⁻¹ * v⁻¹⁻¹) := by group
    rw [e]
    exact mul_mem hf (hV₀V' hc)
  have hV'N : V' ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := fun f hf =>
    (hP.le (hV'.le hf)).1
  intro p hp
  obtain ⟨hpP, hpC⟩ := mem_inf.mp hp
  have hpy : y * p * y⁻¹ = p := by
    rw [← mem_centralizer_singleton_iff.mp hpC]
    group
  have hp' : p ∈ (((R ⊔ T) ⊔ V' : Subgroup G) : Set G) := by
    rw [hV'.sup]
    exact hpP
  rw [coe_mul_of_right_le_normalizer_left (R ⊔ T) V' hV'N] at hp'
  obtain ⟨v, hv, f, hf, hvf⟩ := hp'
  change v * f = p at hvf
  subst hvf
  have hvP : v ∈ P := hVP hv
  have hfP : f ∈ P := hV'.le hf
  have hab : (y * v * y⁻¹) * (y * f * y⁻¹) = v * f := by
    rw [← hpy]
    group
  have hw : v⁻¹ * (y * f * y⁻¹) ∈ V₀ := by
    rw [← hV'.inf]
    refine mem_inf.mpr ⟨mul_mem (inv_mem hv) (hyV'V f hf), ?_⟩
    have e : v⁻¹ * (y * f * y⁻¹) = (v⁻¹ * (y * v * y⁻¹)⁻¹ * v) * f := by
      calc v⁻¹ * (y * f * y⁻¹) =
          v⁻¹ * (y * v * y⁻¹)⁻¹ * ((y * v * y⁻¹) * (y * f * y⁻¹)) := by group
        _ = v⁻¹ * (y * v * y⁻¹)⁻¹ * (v * f) := by rw [hab]
        _ = (v⁻¹ * (y * v * y⁻¹)⁻¹ * v) * f := by group
    rw [e]
    exact mul_mem (hVN' v hv _ (inv_mem (hyVV' v hv))) hf
  obtain ⟨w, hwdef⟩ : ∃ w, w = v⁻¹ * (y * f * y⁻¹) := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hbw : y * f * y⁻¹ = v * w := by
    rw [hwdef]
    group
  have ha : y * v * y⁻¹ = f * w⁻¹ := by
    have e1 : f = (y * v * y⁻¹) * w := by
      calc f = (y * y) * f * (y⁻¹ * y⁻¹) := by rw [hy2, hyi, hy2]; group
        _ = y * (y * f * y⁻¹) * y⁻¹ := by group
        _ = y * (v * w) * y⁻¹ := by rw [hbw]
        _ = (y * v * y⁻¹) * (y * w * y⁻¹) := by group
        _ = (y * v * y⁻¹) * w := by rw [hyw w hw]
    calc y * v * y⁻¹ = (y * v * y⁻¹) * w * w⁻¹ := by group
      _ = f * w⁻¹ := by rw [← e1]
  have hwv : v * w = w * v := P_comm_V₀ hP hw hvP
  have hfv : f * v = v * f := by
    calc f * v = f * w⁻¹ * (w * v) := by group
      _ = f * w⁻¹ * (v * w) := by rw [hwv]
      _ = (y * v * y⁻¹) * (y * f * y⁻¹) := by rw [ha, hbw]
      _ = v * f := hab
  by_cases hfV : f ∈ R ⊔ T
  · have hf0 : f ∈ V₀ := hV'.inf ▸ mem_inf.mpr ⟨hfV, hf⟩
    have hv0 : v ∈ V₀ := by
      have e : v = f * w⁻¹ := by
        calc v = v * w * w⁻¹ := by group
          _ = f * w⁻¹ := by rw [← hbw, hyw f hf0]
      rw [e]
      exact mul_mem hf0 (inv_mem hw)
    exact mul_mem hv0 hf0
  · exfalso
    have hv0 : v ∈ V₀ := h.P_fixed hP hPC hfP hfV hv (by rw [hfv]; group)
    apply hfV
    have e : f = y * v * y⁻¹ * w := by
      rw [ha]
      group
    rw [e, hyw v hv0]
    exact h.V₀_le (mul_mem hv0 hw)

omit hyV in
theorem swap_exists_conj_eq_mul {w : G} (hw : w ∈ V₀) : ∃ q ∈ P, q⁻¹ * y * q = y * w := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hyi : y⁻¹ = y := by
    calc y⁻¹ = y⁻¹ * (y * y) := by rw [hy2, mul_one]
      _ = y := by group
  have hyVV' : ∀ v ∈ R ⊔ T, y * v * y⁻¹ ∈ V' := fun v hv => by
    rw [← hyV'] at hv
    exact (mem_rightConjugate_iff _ _ _).mp hv
  have hyw : ∀ w ∈ V₀, y * w * y⁻¹ = w := fun w hw => by
    rw [← mem_centralizer_iff.mp hyC w hw]
    group
  have hyy : ∀ t : G, y * (y * t * y⁻¹) * y⁻¹ = t := fun t => by
    calc y * (y * t * y⁻¹) * y⁻¹ = (y * y) * t * (y⁻¹ * y⁻¹) := by group
      _ = t := by rw [hy2, hyi, hy2]; group
  have hcomm : ∀ {s t : G}, s ∈ P → t ∈ P → s * t * s⁻¹ * t⁻¹ ∈ V₀ := fun hs ht =>
    h.P_comm_mem_V₀ hP hPC hIIa hs ht
  have hcen : ∀ {c t : G}, c ∈ V₀ → t ∈ P → t * c * t⁻¹ = c := fun hc ht => by
    rw [P_comm_V₀ hP hc ht]
    group
  have hab₀ : ∀ {c d : G}, c ∈ V₀ → d ∈ V₀ → c * d = d * c := fun hc hd =>
    h.comm (h.V₀_le hc) (h.V₀_le hd)
  let γ : ↥(R ⊔ T) →* ↥V₀ :=
    { toFun := fun v => ⟨y * v * y⁻¹ * v * (y * v * y⁻¹)⁻¹ * (v : G)⁻¹,
        hcomm (hV'.le (hyVV' v v.2)) (hVP v.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        obtain ⟨v₁, hv₁⟩ := a
        obtain ⟨v₂, hv₂⟩ := b
        simp only [coe_mul]
        have hv₁P := hVP hv₁
        have hv₂P := hVP hv₂
        obtain ⟨a₁, ha₁⟩ : ∃ a, a = y * v₁ * y⁻¹ := ⟨_, rfl⟩
        obtain ⟨a₂, ha₂⟩ : ∃ a, a = y * v₂ * y⁻¹ := ⟨_, rfl⟩
        have ha₁P : a₁ ∈ P := ha₁ ▸ hV'.le (hyVV' v₁ hv₁)
        have ha₂P : a₂ ∈ P := ha₂ ▸ hV'.le (hyVV' v₂ hv₂)
        have ha₁₂ : y * (v₁ * v₂) * y⁻¹ = a₁ * a₂ := by
          rw [ha₁, ha₂]
          group
        rw [ha₁₂, ← ha₁, ← ha₂]
        have hsym : a₁ * v₂ * a₁⁻¹ * v₂⁻¹ = (a₂ * v₁ * a₂⁻¹ * v₁⁻¹)⁻¹ := by
          have h1 : y * (a₁ * v₂ * a₁⁻¹ * v₂⁻¹) * y⁻¹ = (a₂ * v₁ * a₂⁻¹ * v₁⁻¹)⁻¹ := by
            calc y * (a₁ * v₂ * a₁⁻¹ * v₂⁻¹) * y⁻¹ =
                (y * a₁ * y⁻¹) * (y * v₂ * y⁻¹) * (y * a₁ * y⁻¹)⁻¹ * (y * v₂ * y⁻¹)⁻¹ := by
                  group
              _ = v₁ * a₂ * v₁⁻¹ * a₂⁻¹ := by rw [ha₁, hyy v₁, ← ha₂]
              _ = (a₂ * v₁ * a₂⁻¹ * v₁⁻¹)⁻¹ := by group
          rw [← h1, hyw _ (hcomm ha₁P hv₂P)]
        have hc₂ := hcomm ha₂P (mul_mem hv₁P hv₂P)
        calc a₁ * a₂ * (v₁ * v₂) * (a₁ * a₂)⁻¹ * (v₁ * v₂)⁻¹ =
            a₁ * (a₂ * (v₁ * v₂) * a₂⁻¹ * (v₁ * v₂)⁻¹) * a₁⁻¹ *
              (a₁ * (v₁ * v₂) * a₁⁻¹ * (v₁ * v₂)⁻¹) := by group
          _ = (a₂ * (v₁ * v₂) * a₂⁻¹ * (v₁ * v₂)⁻¹) *
              (a₁ * (v₁ * v₂) * a₁⁻¹ * (v₁ * v₂)⁻¹) := by rw [hcen hc₂ ha₁P]
          _ = (a₂ * v₁ * a₂⁻¹ * v₁⁻¹) * (v₁ * (a₂ * v₂ * a₂⁻¹ * v₂⁻¹) * v₁⁻¹) *
              ((a₁ * v₁ * a₁⁻¹ * v₁⁻¹) * (v₁ * (a₁ * v₂ * a₁⁻¹ * v₂⁻¹) * v₁⁻¹)) := by group
          _ = (a₂ * v₁ * a₂⁻¹ * v₁⁻¹) * (a₂ * v₂ * a₂⁻¹ * v₂⁻¹) *
              ((a₁ * v₁ * a₁⁻¹ * v₁⁻¹) * (a₁ * v₂ * a₁⁻¹ * v₂⁻¹)) := by
                rw [hcen (hcomm ha₂P hv₂P) hv₁P, hcen (hcomm ha₁P hv₂P) hv₁P]
          _ = (a₂ * v₁ * a₂⁻¹ * v₁⁻¹) * ((a₂ * v₂ * a₂⁻¹ * v₂⁻¹) * (a₁ * v₁ * a₁⁻¹ * v₁⁻¹)) *
              (a₂ * v₁ * a₂⁻¹ * v₁⁻¹)⁻¹ := by rw [hsym]; group
          _ = ((a₂ * v₂ * a₂⁻¹ * v₂⁻¹) * (a₁ * v₁ * a₁⁻¹ * v₁⁻¹)) *
              (a₂ * v₁ * a₂⁻¹ * v₁⁻¹) * (a₂ * v₁ * a₂⁻¹ * v₁⁻¹)⁻¹ := by
                rw [hab₀ (hcomm ha₂P hv₁P) (mul_mem (hcomm ha₂P hv₂P) (hcomm ha₁P hv₁P))]
          _ = (a₁ * v₁ * a₁⁻¹ * v₁⁻¹) * (a₂ * v₂ * a₂⁻¹ * v₂⁻¹) := by
                rw [mul_inv_cancel_right, hab₀ (hcomm ha₂P hv₂P) (hcomm ha₁P hv₁P)] }
  have hker : Nat.card γ.ker = 4 := by
    have h1 : γ.ker = V₀.subgroupOf (R ⊔ T) := by
      ext ⟨v, hv⟩
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro hγ
        have h2 : y * v * y⁻¹ * v * (y * v * y⁻¹)⁻¹ * v⁻¹ = 1 := congrArg Subtype.val hγ
        have hav : (y * v * y⁻¹) * v * (y * v * y⁻¹)⁻¹ = v := by
          calc (y * v * y⁻¹) * v * (y * v * y⁻¹)⁻¹ =
              (y * v * y⁻¹ * v * (y * v * y⁻¹)⁻¹ * v⁻¹) * v := by group
            _ = v := by rw [h2, one_mul]
        by_cases haV : y * v * y⁻¹ ∈ R ⊔ T
        · have ha0 : y * v * y⁻¹ ∈ V₀ := hV'.inf ▸ mem_inf.mpr ⟨haV, hyVV' v hv⟩
          have hay := mem_centralizer_iff.mp hyC _ ha0
          have e : v = y⁻¹ * (y * v * y⁻¹) * y := by group
          have e2 : y⁻¹ * (y * v * y⁻¹) * y = y * v * y⁻¹ := by
            calc y⁻¹ * (y * v * y⁻¹) * y = y⁻¹ * ((y * v * y⁻¹) * y) := mul_assoc _ _ _
              _ = y⁻¹ * (y * (y * v * y⁻¹)) := by rw [hay]
              _ = y * v * y⁻¹ := by group
          show v ∈ V₀
          rw [e, e2]
          exact ha0
        · exact h.P_fixed hP hPC (hV'.le (hyVV' v hv)) haV hv hav
      · intro hv0
        apply Subtype.ext
        change y * v * y⁻¹ * v * (y * v * y⁻¹)⁻¹ * v⁻¹ = 1
        rw [hyw v hv0]
        group
    rw [h1, ← h.card_V₀]
    exact Nat.card_congr (subgroupOfEquivOfLe h.V₀_le).toEquiv
  have hsurj : Function.Surjective γ := by
    have h1 := Subgroup.card_ker_mul_card_range γ
    rw [hker, h.loc.card] at h1
    have h2 : Nat.card γ.range = 4 := by omega
    have htop : γ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h2, h.card_V₀])
    exact MonoidHom.range_eq_top.mp htop
  obtain ⟨⟨v, hv⟩, hvw⟩ := hsurj ⟨w, hw⟩
  have hvw' : y * v * y⁻¹ * v * (y * v * y⁻¹)⁻¹ * v⁻¹ = w := congrArg Subtype.val hvw
  refine ⟨v⁻¹ * (y * v * y⁻¹)⁻¹, mul_mem (inv_mem (hVP hv)) (inv_mem (hV'.le (hyVV' v hv))), ?_⟩
  have hflip : y * v⁻¹ * y⁻¹ = y⁻¹ * v⁻¹ * y := by rw [hyi]
  calc (v⁻¹ * (y * v * y⁻¹)⁻¹)⁻¹ * y * (v⁻¹ * (y * v * y⁻¹)⁻¹) =
      y * v * y⁻¹ * v * y * v⁻¹ * (y * v⁻¹ * y⁻¹) := by group
    _ = y * v * y⁻¹ * v * y * v⁻¹ * (y⁻¹ * v⁻¹ * y) := by rw [hflip]
    _ = (y * v * y⁻¹ * v * (y * v * y⁻¹)⁻¹ * v⁻¹) * y := by group
    _ = w * y := by rw [hvw']
    _ = y * w := mem_centralizer_iff.mp hyC w hw

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
