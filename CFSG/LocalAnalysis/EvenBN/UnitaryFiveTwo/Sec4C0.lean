module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4C0Prelim
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4C0Two
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDBasic
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.Open CFSG.EvenSmallLie.UnitarySix.YamadaD

@[expose] def Data.C₀ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  oTwo (normalizer ((d.withT d.F : Subgroup G) : Set G))

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem X₀_le_centralizer
    (h : d.Hyp) : X₀ d ≤ centralizer (d.F : Set G) :=
  fun _ hx => mem_centralizer_iff.2 fun _ hf => (h.comm_F_of_mem_X₀ hx hf).symm

theorem crossed_mem_F
    (h : d.Hyp) {x : G} (hx : x ∈ X₀ d) :
    x⁻¹ * d.t * x * d.t ∈ d.F := by
  have := h.conj_t_mul_inv_mem_F hx
  rwa [h.t_inv] at this

theorem crossed_image_cases
    (h : d.Hyp) :
    (∀ x ∈ X₀ d, x * d.t = d.t * x) ∨ ∀ a ∈ d.F, ∃ x ∈ X₀ d, x⁻¹ * d.t * x * d.t = a := by
  set φ := crossedHom h.t_mul_t d.F (X₀ d) h.X₀_le_centralizer fun _ hy => h.crossed_mem_F hy
  set R : Subgroup SU52 := (φ.range.map d.F.subtype).comap d.ι with hR
  have hmemR : ∀ α : SU52, α ∈ R ↔ ∃ x ∈ X₀ d, x⁻¹ * d.t * x * d.t = d.ι α := by
    intro α
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, e⟩
      exact ⟨y, y.2, e⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, e⟩
  have hRF : R ≤ Fsub := fun α hα => by
    obtain ⟨x, hx, e⟩ := (hmemR α).1 hα
    exact d.ι_mem_pull_iff.1 (e ▸ h.crossed_mem_F hx)
  have hL : ∀ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∀ r ∈ R,
      levSU A hA * r * (levSU A hA)⁻¹ ∈ R := by
    intro A hA r hr
    obtain ⟨x, hx, e⟩ := (hmemR r).1 hr
    have hmX := h.ι_mem_normalizer fun a ha => levSU_conj_mem_A₂sub A hA ha
    have hmt : d.ι (levSU A hA) * d.t = d.t * d.ι (levSU A hA) :=
      comm_of_mem_centralizer h.t_mem (d.ι_mem _)
    refine (hmemR _).2 ⟨_, conj_mem_X₀ hmX hx, ?_⟩
    rw [crossed_conj hmt, e, ι_conj]
  rcases eq_bot_or_eq_Fsub_or_eq_A₂sub (hRF.trans Fsub_le_A₂sub) hL with hb | hF | hA
  · left
    intro x hx
    obtain ⟨α, hα, e⟩ := h.crossed_mem_F hx
    have hαR : α ∈ R := (hmemR α).2 ⟨x, hx, e.symm⟩
    rw [hb, mem_bot] at hαR
    rw [hαR, map_one] at e
    exact (crossed_eq_one_iff h.t_mul_t).1 e.symm
  · right
    rintro _ ⟨α, hα, rfl⟩
    exact (hmemR α).1 (hF ▸ hα)
  · exfalso
    have := Subgroup.card_le_of_le (hA ▸ hRF)
    rw [card_A₂sub, card_Fsub] at this
    norm_num at this

theorem not_seven_dvd_card_H
    (h : d.Hyp) : ¬ 7 ∣ Nat.card d.H := by
  have hidx := h.index_le_two
  rw [h.centralizer_inf_H_eq] at hidx
  have hLt : Nat.card (d.L ⊔ zpowers d.t : Subgroup G) = 2 * Nat.card d.L :=
    card_sup_zpowers h.t_mul_t (fun b hb => comm_of_mem_centralizer h.t_mem hb) h.t_not_mem_L
  have hL : Nat.card d.L = 13685760 := by rw [Nat.card_congr d.η.toEquiv, card_SU52.1]
  have hle : d.L ⊔ zpowers d.t ≤ d.H := sup_le h.L_le_H (zpowers_le.2 h.t_mem_H)
  have hcard := Subgroup.card_mul_index ((d.L ⊔ zpowers d.t).subgroupOf d.H)
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hLt, hL] at hcard
  have hpos : 0 < ((d.L ⊔ zpowers d.t).subgroupOf d.H).index := Nat.pos_of_ne_zero
    (Subgroup.index_ne_zero_of_finite)
  rw [← hcard]
  interval_cases ((d.L ⊔ zpowers d.t).subgroupOf d.H).index <;> norm_num

theorem relIndex_H_normalizer
    (h : d.Hyp) :
    (centralizer ({d.t} : Set G)).relIndex (normalizer ((d.withT d.A₂ : Subgroup G) : Set G)) =
      16 := by
  rw [relIndex_centralizer_eq_ncard]
  have e : {y : G | ∃ x ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G), x⁻¹ * d.t * x = y} =
      (fun a => a * d.t) '' (d.F : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hmem : x⁻¹ * d.t * x ∈ d.withT d.F := by
        have := (mem_normalizer_iff.1 (inv_mem (h.normalizer_A₂t_le hx)) d.t).1
          (mem_sup_right (mem_zpowers _))
        simpa using this
      obtain ⟨a, ha, e⟩ := h.conj_mem_F_mul_t hmem
      exact ⟨a, ha, e.symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact h.mul_t_mem_Delta ha
  rw [e, Set.ncard_image_of_injective _ (mul_left_injective d.t), ← Nat.card_coe_set_eq]
  change Nat.card d.F = 16
  rw [d.card_F]
  norm_num

theorem relIndex_X₀_dvd
    (h : d.Hyp) :
    (X₀ d).relIndex (normalizer ((d.withT d.A₂ : Subgroup G) : Set G)) ∣ 20160 := by
  have e : (X₀ d).relIndex (normalizer ((d.withT d.A₂ : Subgroup G) : Set G)) =
      (secHom (d.withT d.A₂)).ker.index := by
    rw [relIndex, X₀, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
  rw [e]
  obtain ⟨hcomm, hsq⟩ := h.section_hyps
  exact index_ker_secHom_dvd _ (fun z => (h.mem_center_A₂t_iff).symm) h.card_withT_A₂ hcomm hsq

theorem dvd_card_normalizer_inf_H
    (h : d.Hyp) :
    2 ^ 11 * 9 * 5 ∣ Nat.card (normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ⊓ d.H :
      Subgroup G) := by
  set M := normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ⊓ d.H with hM
  have htM : d.t ∈ M := ⟨(d.withT d.A₂).le_normalizer (mem_sup_right (mem_zpowers _)), h.t_mem_H⟩
  have hSM : d.withT d.S ≤ M := by
    refine sup_le ?_ (zpowers_le.2 htM)
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨h.ι_mem_normalizer fun a ha => Ssub_conj_mem_A₂sub hσ ha, h.L_le_H (d.ι_mem σ)⟩
  have hS : Nat.card (d.withT d.S) = 2 ^ 11 := by
    rw [Data.withT, card_sup_zpowers (B := d.S) h.t_mul_t
      (fun b hb => comm_of_mem_centralizer h.t_mem (d.pull_le_L _ hb))
      (fun hS => h.t_not_mem_L (d.pull_le_L _ hS)), d.card_S]
    norm_num
  have hyM : d.ι y₅SU ∈ M :=
    ⟨h.ι_mem_normalizer fun a ha =>
      conj_mem_A₂sub_of_mem_normalizer (N0sub_le_normalizer y₅SU_mem_N0sub) ha,
      h.L_le_H (d.ι_mem _)⟩
  have h2 : 2 ^ 11 ∣ Nat.card M := hS ▸ Subgroup.card_dvd_of_le hSM
  have h9 : 9 ∣ Nat.card M := by
    have := Subgroup.card_dvd_of_le h.torus_le
    rwa [d.card_pull, card_Esub] at this
  have h5 : 5 ∣ Nat.card M := by
    have := Subgroup.card_dvd_of_le (zpowers_le.2 hyM)
    rwa [Nat.card_zpowers, orderOf_injective d.ι d.ι_injective, orderOf_y₅SU] at this
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h9) h5

theorem not_forall_comm_t
    (h : d.Hyp) : ¬ ∀ x ∈ X₀ d, x * d.t = d.t * x := by
  intro hX
  set P := d.withT d.A₂ with hP
  set X := normalizer ((P : Subgroup G) : Set G) with hXdef
  set M := X ⊓ d.H with hMdef
  have hX₀ : X₀ d = P := le_antisymm
    (fun x hx => h.mem_withT_A₂_of_mem_X₀ hx (mem_centralizer_singleton_iff.2 (hX x hx)))
    h.withT_A₂_le_X₀
  have hcX₀ : Nat.card (X₀ d) = 2 ^ 9 := by rw [hX₀, h.card_withT_A₂_eq]
  have e1 := Subgroup.relIndex_mul_card (X₀ d) X
  rw [inf_eq_left.2 X₀_le, hcX₀] at e1
  have e3 := Subgroup.relIndex_mul_card (centralizer ({d.t} : Set G)) X
  rw [h.relIndex_H_normalizer, show (centralizer ({d.t} : Set G) ⊓ X : Subgroup G) = M by
    rw [hMdef, inf_comm]; rfl] at e3
  obtain ⟨m, hm⟩ := h.dvd_card_normalizer_inf_H
  have hr : (X₀ d).relIndex X = 2880 * m := by
    have : (X₀ d).relIndex X * 2 ^ 9 = 2880 * m * 2 ^ 9 := by
      rw [e1, ← e3, hm]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this
  have hm7 : m ∣ 7 := by
    obtain ⟨k, hk⟩ := h.relIndex_X₀_dvd
    rw [hr] at hk
    exact ⟨k, by nlinarith⟩
  have hm1 : m = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hm7 with h1 | h7
    · exact h1
    · exfalso
      refine h.not_seven_dvd_card_H
        (Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le (inf_le_right : M ≤ d.H)))
      rw [hm, h7]
      exact Dvd.intro_left _ rfl
  rw [hm1, mul_one] at hr
  obtain ⟨hcomm, hsq⟩ := h.section_hyps
  obtain ⟨hc, hs⟩ := innSub_comm_sq P (fun z => (h.mem_center_A₂t_iff).symm) hcomm hsq
  have hcard := card_innSub P (fun z => (h.mem_center_A₂t_iff).symm) h.card_withT_A₂
  have hAut := card_mulAut_of_elemAb_sixteen hc hs hcard
  have : IsSimpleGroup (MulAut (innSub P)) := isSimpleGroup_mulAut_of_elemAb_sixteen hc hs hcard
  have hker : (secHom P).ker.index = 2880 := by
    rw [← hr, relIndex, X₀, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
  have hrange : Nat.card (secHom P).range = 2880 := by
    rw [← hker, Subgroup.index_ker]
  have hidx := Subgroup.card_mul_index (secHom P).range
  rw [hrange, hAut] at hidx
  have h7 : (secHom P).range.index = 7 := by omega
  have htop := eq_top_of_index_le_seven hAut h7.le
  rw [htop, index_top] at h7
  exact absurd h7 (by norm_num)

theorem exists_crossed_eq
    (h : d.Hyp) {a : G} (ha : a ∈ d.F) :
    ∃ x ∈ X₀ d, x⁻¹ * d.t * x * d.t = a :=
  (h.crossed_image_cases.resolve_left h.not_forall_comm_t) a ha

theorem card_X₀
    (h : d.Hyp) : Nat.card (X₀ d) = 2 ^ 13 := by
  have := card_eq_of_crossed_onto h.t_mul_t h.X₀_le_centralizer
    (fun _ hy => h.crossed_mem_F hy) fun _ hb => h.exists_crossed_eq hb
  rw [show (X₀ d ⊓ centralizer ({d.t} : Set G) : Subgroup G) = d.withT d.A₂ from h.X₀_inf_H_eq,
    h.card_withT_A₂_eq, d.card_F] at this
  rw [this]
  norm_num

theorem normalizer_le_normalizer_X₀
    (h : d.Hyp) :
    normalizer ((d.withT d.F : Subgroup G) : Set G) ≤ normalizer (X₀ d : Set G) := by
  rw [h.normalizer_withT_F_eq]
  exact fun x hx => mem_normalizer_fintype fun k hk => conj_mem_X₀ hx hk

theorem X₀_le_C₀
    (h : d.Hyp) : X₀ d ≤ d.C₀ :=
  le_oTwo (h.normalizer_withT_F_eq ▸ X₀_le) h.normalizer_le_normalizer_X₀
    (IsPGroup.of_card h.card_X₀)

theorem C₀_le_normalizer
    (h : d.Hyp) :
    d.C₀ ≤ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) :=
  h.normalizer_withT_F_eq ▸ oTwo_le _

theorem C₀_inf_H_le_X₀
    (h : d.Hyp) : d.C₀ ⊓ d.H ≤ X₀ d := by
  set P := d.withT d.A₂ with hP
  set Z := d.withT d.F with hZ
  set Q := d.C₀ ⊓ d.H with hQdef
  have hQ : IsPGroup 2 Q := (isPGroup_oTwo _).to_le inf_le_left
  have hQP : Q ≤ normalizer (P : Set G) := inf_le_left.trans h.C₀_le_normalizer
  have hcen : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z := fun z hz => ((h.mem_center_A₂t_iff).2 hz).2
  have hZn : ∀ x ∈ normalizer (P : Set G), ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := fun x hx z hz =>
    (mem_normalizer_iff.1 (h.normalizer_A₂t_le hx) z).1 hz
  have hιP : ∀ α ∈ A₂sub, d.ι α ∈ P := fun α hα => mem_sup_left (d.ι_mem_pull_iff.2 hα)
  have hQM : ∀ m ∈ normalizer (P : Set G), m ∈ d.H → ∀ q ∈ Q, m⁻¹ * q * m ∈ Q := by
    intro m hmX hmH q hq
    obtain ⟨hqC, hqH⟩ := Subgroup.mem_inf.1 hq
    have hmN : m⁻¹ ∈ normalizer (Z : Set G) := inv_mem (h.normalizer_A₂t_le hmX)
    have := conj_mem_oTwo hmN hqC
    rw [inv_inv] at this
    exact Subgroup.mem_inf.2 ⟨this, mul_mem (mul_mem (inv_mem hmH) hqH) hmH⟩
  let W : Subgroup SU52 :=
    { carrier := {α | α ∈ A₂sub ∧ ∀ q ∈ Q, q * d.ι α * q⁻¹ * (d.ι α)⁻¹ ∈ Z}
      mul_mem' := by
        rintro α β ⟨hα, hαQ⟩ ⟨hβ, hβQ⟩
        refine ⟨mul_mem hα hβ, fun q hq => ?_⟩
        have hzβ := hβQ q hq
        have e : d.ι α * (q * d.ι β * q⁻¹ * (d.ι β)⁻¹) * (d.ι α)⁻¹ =
            q * d.ι β * q⁻¹ * (d.ι β)⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul]
          exact (hcen _ hzβ _ (hιP α hα)).symm
        rw [show q * d.ι (α * β) * q⁻¹ * (d.ι (α * β))⁻¹ =
            (q * d.ι α * q⁻¹ * (d.ι α)⁻¹) *
              (d.ι α * (q * d.ι β * q⁻¹ * (d.ι β)⁻¹) * (d.ι α)⁻¹) by
              rw [map_mul]
              group, e]
        exact mul_mem (hαQ q hq) hzβ
      one_mem' := ⟨one_mem _, fun q _ => by
        rw [map_one, mul_one, mul_inv_cancel, inv_one, mul_one]
        exact one_mem _⟩
      inv_mem' := by
        rintro α ⟨hα, hαQ⟩
        refine ⟨inv_mem hα, fun q hq => ?_⟩
        have hz := inv_mem (hαQ q hq)
        have e : (d.ι α)⁻¹ * (q * d.ι α * q⁻¹ * (d.ι α)⁻¹)⁻¹ * d.ι α =
            (q * d.ι α * q⁻¹ * (d.ι α)⁻¹)⁻¹ := by
          rw [mul_assoc, hcen _ hz _ (hιP α hα), ← mul_assoc, inv_mul_cancel, one_mul]
        rw [show q * d.ι α⁻¹ * q⁻¹ * (d.ι α⁻¹)⁻¹ =
            (d.ι α)⁻¹ * (q * d.ι α * q⁻¹ * (d.ι α)⁻¹)⁻¹ * d.ι α by
              rw [map_inv]
              group, e]
        exact hz }
  have hWA : W ≤ A₂sub := fun _ hα => hα.1
  have hFW : Fsub ≤ W := fun α hα => ⟨Fsub_le_A₂sub hα, fun q hq =>
    mul_mem (hZn q (hQP hq) _ (mem_sup_left (d.ι_mem_pull_iff.2 hα)))
      (inv_mem (mem_sup_left (d.ι_mem_pull_iff.2 hα)))⟩
  have hWL : ∀ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∀ r ∈ W,
      levSU A hA * r * (levSU A hA)⁻¹ ∈ W := by
    rintro A hA α ⟨hα, hαQ⟩
    refine ⟨levSU_conj_mem_A₂sub A hA hα, fun q hq => ?_⟩
    set m := d.ι (levSU A hA) with hm
    have hmX : m ∈ normalizer (P : Set G) := h.ι_mem_normalizer fun a ha =>
      levSU_conj_mem_A₂sub A hA ha
    have hmH : m ∈ d.H := h.L_le_H (d.ι_mem _)
    have hq' := hαQ _ (hQM m hmX hmH q hq)
    rw [show q * d.ι (levSU A hA * α * (levSU A hA)⁻¹) * q⁻¹ *
          (d.ι (levSU A hA * α * (levSU A hA)⁻¹))⁻¹ =
        m * (m⁻¹ * q * m * d.ι α * (m⁻¹ * q * m)⁻¹ * (d.ι α)⁻¹) * m⁻¹ by
          rw [map_mul, map_mul, map_inv, ← hm]
          group]
    exact hZn m hmX _ hq'
  obtain ⟨p₀, hp₀, hp₀Z, hp₀Q⟩ := exists_fixed_of_isPGroup P
    (fun z => (h.mem_center_A₂t_iff).symm) h.card_withT_A₂ hQ hQP
  have hW : W = A₂sub := by
    rcases eq_bot_or_eq_Fsub_or_eq_A₂sub hWA hWL with hb | hF | hA
    · exfalso
      have := Subgroup.card_le_of_le (hb ▸ hFW)
      rw [card_Fsub, card_bot] at this
      norm_num at this
    · exfalso
      obtain ⟨_, ⟨α, hα, rfl⟩, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp₀
      have hαW : α ∈ W := ⟨hα, fun q hq => by
        have hw : q * c⁻¹ * q⁻¹ * c ∈ Z :=
          mul_mem (hZn q (hQP hq) _ (inv_mem (mem_sup_right hc))) (mem_sup_right hc)
        have e : d.ι α * c * (q * c⁻¹ * q⁻¹ * c) * (d.ι α * c)⁻¹ = q * c⁻¹ * q⁻¹ * c := by
          rw [mul_inv_eq_iff_eq_mul]
          exact (hcen _ hw _ hp₀).symm
        rw [show q * d.ι α * q⁻¹ * (d.ι α)⁻¹ =
            (q * (d.ι α * c) * q⁻¹ * (d.ι α * c)⁻¹) *
              (d.ι α * c * (q * c⁻¹ * q⁻¹ * c) * (d.ι α * c)⁻¹) by group, e]
        exact mul_mem (hp₀Q q hq) hw⟩
      rw [hF] at hαW
      exact hp₀Z (mul_mem (mem_sup_left (d.ι_mem_pull_iff.2 hαW)) (mem_sup_right hc))
    · exact hA
  intro q hq
  have hqX := hQP hq
  refine ⟨⟨q, hqX⟩, ?_, rfl⟩
  change secHom P ⟨q, hqX⟩ = 1
  rw [secHom_eq_one_iff]
  intro p hp r hr
  obtain ⟨_, ⟨α, hα, rfl⟩, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp
  have hαW : α ∈ W := hW ▸ hα
  have hz₁ := hαW.2 q hq
  have hz₂ : q * c * q⁻¹ * c⁻¹ ∈ Z :=
    mul_mem (hZn q hqX _ (mem_sup_right hc)) (inv_mem (mem_sup_right hc))
  have e : d.ι α * (q * c * q⁻¹ * c⁻¹) * (d.ι α)⁻¹ = q * c * q⁻¹ * c⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcen _ hz₂ _ (hιP α hα)).symm
  have hmem : q * (d.ι α * c) * q⁻¹ * (d.ι α * c)⁻¹ ∈ Z := by
    rw [show q * (d.ι α * c) * q⁻¹ * (d.ι α * c)⁻¹ =
        (q * d.ι α * q⁻¹ * (d.ι α)⁻¹) * (d.ι α * (q * c * q⁻¹ * c⁻¹) * (d.ι α)⁻¹) by group, e]
    exact mul_mem hz₁ hz₂
  exact hcen _ hmem r hr

theorem C₀_eq_X₀
    (h : d.Hyp) : d.C₀ = X₀ d := by
  refine le_antisymm (fun c hc => ?_) h.X₀_le_C₀
  have hcX := h.C₀_le_normalizer hc
  have hmem : c⁻¹ * d.t * c ∈ d.withT d.F := by
    have := (mem_normalizer_iff.1 (inv_mem (h.normalizer_A₂t_le hcX)) d.t).1
      (mem_sup_right (mem_zpowers _))
    simpa using this
  obtain ⟨a, ha, e⟩ := h.conj_mem_F_mul_t hmem
  obtain ⟨y, hy, ey⟩ := h.exists_crossed_eq ha
  have e2 : c⁻¹ * d.t * c = y⁻¹ * d.t * y := by
    rw [e, ← ey, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
  have hq : c * y⁻¹ ∈ d.C₀ ⊓ d.H := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hc (inv_mem (h.X₀_le_C₀ hy)), ?_⟩
    refine mem_centralizer_singleton_iff.2 ?_
    calc c * y⁻¹ * d.t = c * (y⁻¹ * d.t * y) * y⁻¹ := by group
      _ = c * (c⁻¹ * d.t * c) * y⁻¹ := by rw [e2]
      _ = d.t * (c * y⁻¹) := by group
  have := mul_mem (h.C₀_inf_H_le_X₀ hq) hy
  rwa [inv_mul_cancel_right] at this

theorem normalizer_withT_A₂_eq
    (h : d.Hyp) :
    normalizer ((d.withT d.A₂ : Subgroup G) : Set G) =
      (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.C₀ := by
  refine le_antisymm (fun n hn => ?_)
    (sup_le (h.normalizer_inf_H_eq ▸ inf_le_left) h.C₀_le_normalizer)
  have hmem : n⁻¹ * d.t * n ∈ d.withT d.F := by
    have := (mem_normalizer_iff.1 (inv_mem (h.normalizer_A₂t_le hn)) d.t).1
      (mem_sup_right (mem_zpowers _))
    simpa using this
  obtain ⟨a, ha, e⟩ := h.conj_mem_F_mul_t hmem
  obtain ⟨y, hy, ey⟩ := h.exists_crossed_eq ha
  have e2 : n⁻¹ * d.t * n = y⁻¹ * d.t * y := by
    rw [e, ← ey, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
  have hyX : y ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) := X₀_le hy
  have hm : n * y⁻¹ ∈ normalizer (d.A₂ : Set G) ⊓ d.H := by
    rw [← h.normalizer_inf_H_eq]
    refine Subgroup.mem_inf.2 ⟨mul_mem hn (inv_mem hyX), mem_centralizer_singleton_iff.2 ?_⟩
    calc n * y⁻¹ * d.t = n * (y⁻¹ * d.t * y) * y⁻¹ := by group
      _ = n * (n⁻¹ * d.t * n) * y⁻¹ := by rw [e2]
      _ = d.t * (n * y⁻¹) := by group
  have := mul_mem (mem_sup_left hm : n * y⁻¹ ∈ (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.C₀)
    (mem_sup_right ((h.C₀_eq_X₀).symm ▸ hy))
  rwa [inv_mul_cancel_right] at this

theorem H_inf_C₀
    (h : d.Hyp) : d.H ⊓ d.C₀ = d.withT d.A₂ := by
  rw [inf_comm, h.C₀_eq_X₀, h.X₀_inf_H_eq]

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
