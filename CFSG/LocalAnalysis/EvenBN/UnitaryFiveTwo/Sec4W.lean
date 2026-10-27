module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4Y
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckW

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement

theorem klein_norm_comm {G : Type*} [Group G] {Y : Subgroup G} {a b c x : G}
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y * z = z * y) (hx : x ∈ Y)
    (ha : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) (hb : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = c) (hba : b * a = c) :
    x * (a * x * a⁻¹) * (b * x * b⁻¹) * (c * x * c⁻¹) ∈ Y ∧
      a * (x * (a * x * a⁻¹) * (b * x * b⁻¹) * (c * x * c⁻¹)) =
        x * (a * x * a⁻¹) * (b * x * b⁻¹) * (c * x * c⁻¹) * a ∧
      b * (x * (a * x * a⁻¹) * (b * x * b⁻¹) * (c * x * c⁻¹)) =
        x * (a * x * a⁻¹) * (b * x * b⁻¹) * (c * x * c⁻¹) * b := by
  have h₂ := ha x hx
  have h₃ := hb x hx
  have h₄ : c * x * c⁻¹ ∈ Y := by
    have := ha _ h₃
    rwa [show a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ by group, hab] at this
  have key : ∀ g : G, g * (x * (a * x * a⁻¹) * (b * x * b⁻¹) * (c * x * c⁻¹)) * g⁻¹ =
      g * x * g⁻¹ * (g * a * x * (g * a)⁻¹) * (g * b * x * (g * b)⁻¹) *
        (g * c * x * (g * c)⁻¹) := fun g => by group
  have sw₁ : ∀ p₁ p₂ p₃ p₄ : G, p₂ * p₁ = p₁ * p₂ → p₄ * p₃ = p₃ * p₄ →
      p₂ * p₁ * p₄ * p₃ = p₁ * p₂ * p₃ * p₄ := fun p₁ p₂ p₃ p₄ h₁₂ h₃₄ => by
    rw [h₁₂, mul_assoc (p₁ * p₂) p₄ p₃, h₃₄, ← mul_assoc (p₁ * p₂) p₃ p₄]
  have sw₂ : ∀ p₁ p₂ p₃ p₄ : G, p₃ * p₄ * (p₁ * p₂) = p₁ * p₂ * (p₃ * p₄) →
      p₃ * p₄ * p₁ * p₂ = p₁ * p₂ * p₃ * p₄ := fun p₁ p₂ p₃ p₄ h => by
    rw [mul_assoc (p₃ * p₄) p₁ p₂, h, ← mul_assoc (p₁ * p₂) p₃ p₄]
  have hac : a * c = b := by rw [← hab, ← mul_assoc, haa, one_mul]
  have hbc : b * c = a := by rw [← hba, ← mul_assoc, hbb, one_mul]
  refine ⟨mul_mem (mul_mem (mul_mem hx h₂) h₃) h₄, ?_, ?_⟩
  · rw [← mul_inv_eq_iff_eq_mul, key, haa, hab, hac]
    simp only [one_mul, inv_one, mul_one]
    exact sw₁ _ _ _ _ (hY _ h₂ _ hx) (hY _ h₄ _ h₃)
  · rw [← mul_inv_eq_iff_eq_mul, key, hba, hbb, hbc]
    simp only [one_mul, inv_one, mul_one]
    exact sw₂ _ _ _ _ (hY _ (mul_mem h₃ h₄) _ (mul_mem hx h₂))

@[expose] def Data.W {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.Y ⊓ centralizer (d.S : Set G)

namespace Data

variable {G : Type} [Group G] (d : Data G)

theorem S_eq_sup : d.S = d.A₂ ⊔ d.X₂ := by
  rw [Data.S, Ssub_eq_sup, d.pull_sup]
  rfl

theorem W_le_Y : d.W ≤ d.Y := inf_le_left

theorem W_le_centralizer : d.W ≤ centralizer (d.S : Set G) := inf_le_right

theorem ZX₄_le_F : d.ZX₄ ≤ d.F := d.pull_mono (le_sup_right : ZX₄sub ≤ Fsub)

theorem ι_x₂SU_mem_S (c : F4) : d.ι (x₂SU c) ∈ d.S :=
  d.pull_mono (le_sup_right.trans (le_sup_left.trans le_sup_left) : X₂sub ≤ Ssub)
    ⟨x₂SU c, x₂SU_mem c, rfl⟩

end Data

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Y_comm
    (h : d.Hyp) {x y : G}
    (hx : x ∈ d.Y) (hy : y ∈ d.Y) : x * y = y * x := by
  rw [h.Y_eq_E₂] at hx hy
  exact h.E₂_comm hx hy

theorem omega_Y_cases
    (h : d.Hyp) :
    (∀ y ∈ d.Y, y * y = 1 → y ∈ d.F) ∨ ∀ y ∈ d.Y, y * y = 1 := by
  have hYE := h.Y_eq_E₂
  let Ω : Subgroup G :=
    { carrier := {y | y ∈ d.Y ∧ y * y = 1}
      one_mem' := ⟨one_mem _, mul_one 1⟩
      mul_mem' := by
        rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
        refine ⟨mul_mem hx hy, ?_⟩
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [h.Y_comm hy hx]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx2, hy2, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hx2⟩
        refine ⟨inv_mem hx, ?_⟩
        rw [← mul_inv_rev, hx2, inv_one] }
  have hΩY : ∀ {y}, y ∈ Ω → y ∈ d.U := fun hy => h.E₂_le_U (hYE ▸ hy.1)
  set R : Subgroup SU52 :=
    ((crossedHom h.t_mul_t d.F Ω (fun y hy => mem_centralizer_iff.2 fun f hf =>
      (h.U_comm_F (hΩY hy) hf).symm) fun y hy => h.U_crossed_mem_F (hΩY hy)).range.map
      d.F.subtype).comap d.ι with hR
  have hmemR : ∀ α : SU52, α ∈ R ↔ ∃ y ∈ Ω, y⁻¹ * d.t * y * d.t = d.ι α := by
    intro α
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, e⟩
      exact ⟨y, y.2, e⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, e⟩
  have hRF : R ≤ Fsub := fun α hα => by
    obtain ⟨y, hy, e⟩ := (hmemR α).1 hα
    exact d.ι_mem_pull_iff.1 (e ▸ h.U_crossed_mem_F (hΩY hy))
  have hL : ∀ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∀ r ∈ R,
      levSU A hA * r * (levSU A hA)⁻¹ ∈ R := by
    intro A hA r hr
    obtain ⟨y, ⟨hyY, hy2⟩, e⟩ := (hmemR r).1 hr
    have hl : d.ι (levSU A hA) ∈ d.Lev :=
      ⟨levSU A hA, ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA.ne_zero, rfl⟩, rfl⟩
    have hlY : d.ι (levSU A hA) * y * (d.ι (levSU A hA))⁻¹ ∈ d.Y := by
      rw [hYE] at hyY ⊢
      exact (mem_normalizer_iff.1 ((h.le_normalizer_E₂).1 hl) y).1 hyY
    refine (hmemR _).2 ⟨_, ⟨hlY, ?_⟩, ?_⟩
    · rw [show d.ι (levSU A hA) * y * (d.ι (levSU A hA))⁻¹ *
          (d.ι (levSU A hA) * y * (d.ι (levSU A hA))⁻¹) =
          d.ι (levSU A hA) * (y * y) * (d.ι (levSU A hA))⁻¹ by group, hy2, mul_one,
        mul_inv_cancel]
    · rw [crossed_conj (h.Lev_comm_t hl), e, ι_conj]
  rcases eq_bot_or_eq_Fsub_or_eq_A₂sub (hRF.trans Fsub_le_A₂sub) hL with hb | hF | hA
  · left
    intro y hy hy2
    have hyH : y ∈ d.U ⊓ d.H := by
      refine Subgroup.mem_inf.2 ⟨hΩY (show y ∈ Ω from ⟨hy, hy2⟩), ?_⟩
      obtain ⟨α, hα, e⟩ := h.U_crossed_mem_F (hΩY (show y ∈ Ω from ⟨hy, hy2⟩))
      have hαR : α ∈ R := (hmemR α).2 ⟨y, ⟨hy, hy2⟩, e.symm⟩
      rw [hb, mem_bot] at hαR
      rw [hαR, map_one] at e
      exact mem_centralizer_singleton_iff.2 ((crossed_eq_one_iff h.t_mul_t).1 e.symm)
    rw [h.U_inf_H] at hyH
    exact h.mem_F_of_mem_withT_F_of_mem_L hyH (by
      have := h.E₂_inf_H
      have hyE : y ∈ d.E₂ ⊓ d.H := Subgroup.mem_inf.2 ⟨hYE ▸ hy,
        (Subgroup.mem_inf.1 (show y ∈ d.U ⊓ d.H from h.U_inf_H ▸ hyH)).2⟩
      rw [this] at hyE
      exact h.F_le_L hyE)
  · right
    have honto : ∀ a ∈ d.F, ∃ y ∈ Ω, y⁻¹ * d.t * y * d.t = a := by
      rintro _ ⟨α, hα, rfl⟩
      exact (hmemR α).1 (hF ▸ hα)
    have hcard := card_eq_of_crossed_onto h.t_mul_t (Y := Ω)
      (fun y hy => mem_centralizer_iff.2 fun f hf => (h.U_comm_F (hΩY hy) hf).symm)
      (fun y hy => h.U_crossed_mem_F (hΩY hy)) honto
    have hFΩ : d.F ≤ Ω ⊓ centralizer ({d.t} : Set G) := fun f hf =>
      Subgroup.mem_inf.2 ⟨⟨hYE ▸ h.F_le_E₂ hf, h.F_sq hf⟩,
        mem_centralizer_singleton_iff.2 (h.t_comm_F hf)⟩
    have h1 := Subgroup.card_le_of_le hFΩ
    have hΩle : Ω ≤ d.Y := fun y hy => hy.1
    have hYc : Nat.card d.Y = 2 ^ 8 := hYE ▸ h.card_E₂
    have hΩeq : Ω = d.Y := by
      refine Subgroup.eq_of_le_of_card_ge hΩle ?_
      rw [hYc, hcard, d.card_F]
      rw [d.card_F] at h1
      nlinarith
    intro y hy
    have : y ∈ Ω := hΩeq ▸ hy
    exact this.2
  · exfalso
    have := Subgroup.card_le_of_le (hA ▸ hRF)
    rw [card_A₂sub, card_Fsub] at this
    norm_num at this

theorem conj_t_not_mem_Y
    (h : d.Hyp) (g : G) :
    g⁻¹ * d.t * g ∉ d.Y := by
  intro hy
  have hy2 : g⁻¹ * d.t * g * (g⁻¹ * d.t * g) = 1 := by
    rw [show g⁻¹ * d.t * g * (g⁻¹ * d.t * g) = g⁻¹ * (d.t * d.t) * g by group, h.t_mul_t]
    group
  rcases h.omega_Y_cases with hF | hE
  · exact h.conj_t_not_mem_L g (h.F_le_L (hF _ hy hy2))
  ·
    set E := d.Y.map (MulAut.conj g).toMonoidHom with hE'
    have hEH : E ≤ d.H := by
      rintro _ ⟨y, hyY, rfl⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have e := h.Y_comm hyY hy
      change g * y * g⁻¹ * d.t = d.t * (g * y * g⁻¹)
      calc g * y * g⁻¹ * d.t = g * (y * (g⁻¹ * d.t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * d.t * g) * y) * g⁻¹ := by rw [e]
        _ = d.t * (g * y * g⁻¹) := by group
    have hle := h.card_le_of_elemAb hEH
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy', rfl⟩
        change g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹)
        rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, h.Y_comm hx hy']
        group)
      (by
        rintro _ ⟨x, hx, rfl⟩
        change g * x * g⁻¹ * (g * x * g⁻¹) = 1
        rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hE x hx, mul_one,
          mul_inv_cancel])
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, h.Y_eq_E₂,
      h.card_E₂] at hle
    norm_num at hle

theorem Y_comm_A₂
    (h : d.Hyp) {y a : G} (hy : y ∈ d.Y) (ha : a ∈ d.A₂) :
    a * y = y * a :=
  mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).1 a (h.A₂_le_D₀ ha)

theorem mem_W_of_comm
    (h : d.Hyp) {y : G} (hy : y ∈ d.Y)
    (h1 : y * d.ι (x₂SU 1) = d.ι (x₂SU 1) * y)
    (hω : y * d.ι (x₂SU F4.ω) = d.ι (x₂SU F4.ω) * y) : y ∈ d.W := by
  refine Subgroup.mem_inf.2 ⟨hy, ?_⟩
  have hX₂ : d.X₂ ≤ centralizer ({y} : Set G) := by
    have hcl : closure ({d.ι (x₂SU 1), d.ι (x₂SU F4.ω)} : Set G) ≤ centralizer ({y} : Set G) :=
      (closure_le _).2 (by
        rintro _ (rfl | rfl)
        · exact mem_centralizer_singleton_iff.2 h1.symm
        · exact mem_centralizer_singleton_iff.2 hω.symm)
    refine le_trans ?_ hcl
    rw [Data.X₂, Data.pull]
    refine (map_mono X₂sub_le_closure).trans ?_
    rw [MonoidHom.map_closure, Set.image_pair]
  have hA₂ : d.A₂ ≤ centralizer ({y} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (h.Y_comm_A₂ hy ha)
  refine mem_centralizer_iff.2 fun s hs => ?_
  rw [d.S_eq_sup] at hs
  exact mem_centralizer_singleton_iff.1 ((sup_le hA₂ hX₂) hs)

theorem W_inf_H
    (h : d.Hyp) :
    d.W ⊓ d.H = d.ZX₄ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hxH⟩ := Subgroup.mem_inf.1 hx
    have hxF : x ∈ d.F := by
      rw [← h.E₂_inf_H, ← h.Y_eq_E₂]
      exact Subgroup.mem_inf.2 ⟨d.W_le_Y hxW, hxH⟩
    obtain ⟨ξ, hξ, rfl⟩ := hxF
    have hc : ∀ c : F4, ξ * x₂SU c = x₂SU c * ξ := fun c => d.ι_injective (by
      rw [map_mul, map_mul]
      exact (mem_centralizer_iff.1 (d.W_le_centralizer hxW) _ (d.ι_x₂SU_mem_S c)).symm)
    exact ⟨ξ, mem_ZX₄sub_of_comm hξ (hc 1) (hc F4.ω), rfl⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    have hF : d.ι ζ ∈ d.F := d.ZX₄_le_F ⟨ζ, hζ, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨h.Y_eq_E₂ ▸ h.F_le_E₂ hF, ?_⟩,
      h.withT_F_le_H (mem_sup_left hF)⟩
    rintro _ ⟨σ, hσ, rfl⟩
    rw [← map_mul, ← map_mul, ZX₄sub_comm hζ hσ]

theorem exists_W_crossed_eq
    (h : d.Hyp) :
    ∃ w ∈ d.W, w⁻¹ * d.t * w * d.t = d.ι (x₄SU 0 1 zero_one_rel) := by
  have hYE := h.Y_eq_E₂
  obtain ⟨x, hx, hxt⟩ := h.exists_E₂_crossed_eq
    (d.ι_mem_pull_iff.2 (genFSU_mem 0) : d.ι (x₁SU 0 1 zero_one_rel) ∈ d.F)
  have hxY : x ∈ d.Y := hYE ▸ hx
  have hsq : ∀ c : F4, d.ι (x₂SU c) * d.ι (x₂SU c) = 1 := fun c => by
    rw [← map_mul, x₂SU_mul, CharTwo.add_self_eq_zero,
      show x₂SU 0 = 1 from ext_mat (by rw [mat_x₂SU, x₂Mat_zero, mat_one]), map_one]
  have hX : ∀ c : F4, d.ι (x₂SU c) ∈ d.Lev := fun c => X₂_le_Lev ⟨x₂SU c, x₂SU_mem c, rfl⟩
  have hconjY : ∀ c : F4, ∀ y ∈ d.Y, d.ι (x₂SU c) * y * (d.ι (x₂SU c))⁻¹ ∈ d.Y :=
    fun c y hy => hYE ▸ (mem_normalizer_iff.1 ((h.le_normalizer_E₂).1 (hX c)) y).1 (hYE ▸ hy)
  obtain ⟨hwY, hwa, hwb⟩ := klein_norm_comm (c := d.ι (x₂SU (F4.ω + 1)))
    (fun y hy z hz => h.Y_comm hy hz) hxY (hconjY 1) (hconjY F4.ω) (hsq 1) (hsq F4.ω)
    (by rw [← map_mul, x₂SU_mul, add_comm]) (by rw [← map_mul, x₂SU_mul])
  refine ⟨_, h.mem_W_of_comm hwY hwa.symm hwb.symm, ?_⟩
  have hU : ∀ {y}, y ∈ d.Y → y ∈ d.U := fun hy => h.E₂_le_U (hYE ▸ hy)
  have hcm : ∀ {y z}, y ∈ d.Y → z ∈ d.Y →
      (y * z)⁻¹ * d.t * (y * z) * d.t = (y⁻¹ * d.t * y * d.t) * (z⁻¹ * d.t * z * d.t) :=
    fun hy hz => crossed_mul h.t_mul_t (h.U_comm_F (hU hz) (h.U_crossed_mem_F (hU hy))).symm
  have hct : ∀ c : F4, (d.ι (x₂SU c) * x * (d.ι (x₂SU c))⁻¹)⁻¹ * d.t *
      (d.ι (x₂SU c) * x * (d.ι (x₂SU c))⁻¹) * d.t = d.ι (conjX₁ c) := fun c => by
    rw [crossed_conj (h.Lev_comm_t (hX c)), hxt, conjX₁, map_mul, map_mul, map_inv]
  rw [hcm (mul_mem (mul_mem hxY (hconjY 1 x hxY)) (hconjY F4.ω x hxY))
      (hconjY (F4.ω + 1) x hxY), hcm (mul_mem hxY (hconjY 1 x hxY)) (hconjY F4.ω x hxY),
    hcm hxY (hconjY 1 x hxY), hxt, hct 1, hct F4.ω, hct (F4.ω + 1), ← norm_conjX₁, map_mul,
    map_mul, map_mul, ← x₁_eq_conjX₁]

theorem sec4_9_W
    (h : d.Hyp) :
    Nat.card d.W = 4 ∧ d.W ⊓ d.H = d.ZX₄ ∧
      (∀ a ∈ d.ZX₄, ∃ w ∈ d.W, w⁻¹ * d.t * w = a * d.t) ∧ (∀ g : G, g⁻¹ * d.t * g ∉ d.Y) ∧
      (∀ x ∈ d.W, ∀ y ∈ d.W, x * y = y * x) ∧ d.W ≤ centralizer (d.A₁ : Set G) := by
  obtain ⟨w, hwW, hwt⟩ := h.exists_W_crossed_eq
  have hWU : ∀ {y}, y ∈ d.W → y ∈ d.U := fun hy => h.E₂_le_U (h.Y_eq_E₂ ▸ d.W_le_Y hy)
  have hcrZ : ∀ y ∈ d.W, y⁻¹ * d.t * y * d.t ∈ d.ZX₄ := by
    intro y hy
    obtain ⟨ξ, hξ, e⟩ := h.U_crossed_mem_F (hWU hy)
    have hc : ∀ c : F4, ξ * x₂SU c = x₂SU c * ξ := fun c => d.ι_injective (by
      have hyc := mem_centralizer_iff.1 (d.W_le_centralizer hy) _ (d.ι_x₂SU_mem_S c)
      have hcomm := crossed_conj (x := y) (h := d.ι (x₂SU c))
        (h.Lev_comm_t (X₂_le_Lev ⟨x₂SU c, x₂SU_mem c, rfl⟩))
      rw [show d.ι (x₂SU c) * y * (d.ι (x₂SU c))⁻¹ = y by rw [hyc, mul_inv_cancel_right],
        ← e] at hcomm
      rw [map_mul, map_mul]
      calc d.ι ξ * d.ι (x₂SU c) = d.ι (x₂SU c) * d.ι ξ * (d.ι (x₂SU c))⁻¹ * d.ι (x₂SU c) := by
            rw [← hcomm]
        _ = d.ι (x₂SU c) * d.ι ξ := by group)
    rw [← e]
    exact ⟨ξ, mem_ZX₄sub_of_comm hξ (hc 1) (hc F4.ω), rfl⟩
  have honto : ∀ b ∈ d.ZX₄, ∃ y ∈ d.W, y⁻¹ * d.t * y * d.t = b := by
    rintro _ ⟨ζ, hζ, rfl⟩
    obtain ⟨α, β, hα, hζm⟩ := mem_x₄Sub.1 hζ
    subst hα
    rcases eq_zero_or_one_of_valid β (x₄_coord_rel hζm) with rfl | rfl
    · refine ⟨1, one_mem _, ?_⟩
      rw [show ζ = 1 from ext_mat (by rw [hζm, x₄Mat_zero, mat_one]), map_one, inv_one,
        one_mul, mul_one, h.t_mul_t]
    · exact ⟨w, hwW, by rw [hwt, show ζ = x₄SU 0 1 zero_one_rel from ext_mat hζm]⟩
  have hWZ : d.W ≤ centralizer (d.ZX₄ : Set G) := fun y hy =>
    mem_centralizer_iff.2 fun z hz => (h.U_comm_F (hWU hy) (d.ZX₄_le_F hz)).symm
  have hcard := card_eq_of_crossed_onto h.t_mul_t hWZ hcrZ honto
  rw [show (d.W ⊓ centralizer ({d.t} : Set G) : Subgroup G) = d.ZX₄ from h.W_inf_H,
    Data.ZX₄, d.card_pull, card_ZX₄sub] at hcard
  refine ⟨by rw [hcard], h.W_inf_H, fun a ha => ?_, h.conj_t_not_mem_Y,
    fun x hx y hy => h.Y_comm (d.W_le_Y hx) (d.W_le_Y hy), fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := honto a ha
    exact ⟨y, hy, by rw [← e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]⟩
  · exact mem_centralizer_iff.2 fun a ha =>
      mem_centralizer_iff.1 (d.W_le_centralizer hx) a (d.A₁_le_S ha)

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
