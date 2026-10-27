module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

namespace S56

variable {Γ : Type*} [Group Γ]

theorem card_sup_mul_card_inf_of_le_normalizer {H N : Subgroup Γ}
    (hHN : H ≤ normalizer (N : Set Γ)) :
    Nat.card (H ⊔ N : Subgroup Γ) * Nat.card (H ⊓ N : Subgroup Γ) =
      Nat.card H * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h3 : Nat.card (N.subgroupOf H) = Nat.card (H ⊓ N : Subgroup Γ) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (H ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem card_sup_zpowers_eq_two_mul [Finite Γ] {A : Subgroup Γ} {y : Γ}
    (hy : ∀ a ∈ A, a * y = y * a) (hy2 : y * y ∈ A) (hyA : y ∉ A) :
    Nat.card (A ⊔ zpowers y : Subgroup Γ) = 2 * Nat.card A := by
  have hle := s56_card_sup_zpowers_le hy hy2
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ zpowers y)
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hpos' : 0 < Nat.card (A ⊔ zpowers y : Subgroup Γ) := Nat.card_pos
  have hne : Nat.card (A ⊔ zpowers y : Subgroup Γ) ≠ Nat.card A := fun h => hyA (by
    have := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ A ⊔ zpowers y) h.le
    rw [this]
    exact mem_sup_right (mem_zpowers y))
  have hm2 : m < 3 := by
    by_contra h
    have h3 : 3 ≤ m := not_lt.1 h
    nlinarith
  interval_cases m <;> omega

theorem card_le_mul_card_inf_centralizer [Finite Γ] {E Z : Subgroup Γ} {k : Γ}
    (hEZ : ∀ e ∈ E, ∀ w ∈ Z, e * w = w * e) (hk : ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ Z) :
    Nat.card E ≤ Nat.card Z * Nat.card (E ⊓ centralizer ({k} : Set Γ) : Subgroup Γ) := by
  obtain ⟨f, hf⟩ : ∃ f : ↥E → Γ, ∀ e, f e = k * (e : Γ) * k⁻¹ * (e : Γ)⁻¹ := ⟨_, fun _ => rfl⟩
  have hmul : ∀ a b : ↥E, f (a * b) = f a * f b := by
    intro a b
    have hc := hEZ (a : Γ) a.2 _ (hk (b : Γ) b.2)
    rw [hf, hf, hf]
    calc k * ((a * b : ↥E) : Γ) * k⁻¹ * ((a * b : ↥E) : Γ)⁻¹
        = (k * (a : Γ) * k⁻¹ * (a : Γ)⁻¹) *
            ((a : Γ) * (k * (b : Γ) * k⁻¹ * (b : Γ)⁻¹) * (a : Γ)⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
      _ = (k * (a : Γ) * k⁻¹ * (a : Γ)⁻¹) * (k * (b : Γ) * k⁻¹ * (b : Γ)⁻¹) := by
          rw [hc]
          group
  let ψ : ↥E →* Γ := MonoidHom.mk' f hmul
  have hrange : ψ.range ≤ Z := by
    rintro _ ⟨e, rfl⟩
    show f e ∈ Z
    rw [hf]
    exact hk e e.2
  have hker : ψ.ker = (E ⊓ centralizer ({k} : Set Γ)).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    show f e = 1 ↔ _
    rw [hf]
    constructor
    · intro h
      refine ⟨e.2, ?_⟩
      have h1 : k * (e : Γ) * k⁻¹ = e := mul_inv_eq_one.1 h
      calc (e : Γ) * k = k * (e : Γ) * k⁻¹ * k := by rw [h1]
        _ = k * (e : Γ) := by group
    · rintro ⟨-, h⟩
      calc k * (e : Γ) * k⁻¹ * (e : Γ)⁻¹ = (e * k) * k⁻¹ * (e : Γ)⁻¹ := by rw [h]
        _ = 1 := by group
  have h := Subgroup.card_ker_mul_card_range ψ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ centralizer
    ({k} : Set Γ) ≤ E)).toEquiv] at h
  have h2 : Nat.card ψ.range ≤ Nat.card Z := Subgroup.card_le_of_le hrange
  calc Nat.card E = Nat.card (E ⊓ centralizer ({k} : Set Γ) : Subgroup Γ) * Nat.card ψ.range :=
        h.symm
    _ ≤ Nat.card (E ⊓ centralizer ({k} : Set Γ) : Subgroup Γ) * Nat.card Z :=
        Nat.mul_le_mul_left _ h2
    _ = Nat.card Z * Nat.card (E ⊓ centralizer ({k} : Set Γ) : Subgroup Γ) := Nat.mul_comm _ _

end S56

namespace N

section Core

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_centralizer_zpowers_x5_iff {c : G} :
    c ∈ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) ↔ d.x₅ * c = c * d.x₅ := by
  rw [mem_centralizer_iff]
  refine ⟨fun h => h d.x₅ (mem_zpowers _), fun h g hg => ?_⟩
  obtain ⟨n, rfl⟩ := hg
  exact (Commute.zpow_left (show Commute d.x₅ c from h) n).eq

theorem mem_CQ2X_iff {w : G} : w ∈ CQ2X d ↔ w ∈ d.s56Q2 ∧ d.x₅ * w = w * d.x₅ := by
  unfold CQ2X Xg
  rw [mem_inf, mem_centralizer_zpowers_x5_iff]

theorem CQ2X_le_Q2 (d : Data G) : CQ2X d ≤ d.s56Q2 := fun _ h => (mem_CQ2X_iff.1 h).1

theorem Q2_le_M (d : Data G) : d.s56Q2 ≤ d.M := inf_le_left

theorem CQ2X_le_normalizer_E (hd : d.Hyp) : CQ2X d ≤ normalizer (d.E : Set G) :=
  ((CQ2X_le_Q2 d).trans (Q2_le_M d)).trans hd.s56_ME

theorem z_mem_CQ2X (hd : d.Hyp) : d.z ∈ CQ2X d :=
  mem_CQ2X_iff.2 ⟨hd.s56_E_le_Q2 hd.s56_z_mem_E, hd.s56_x5_comm_z⟩

theorem t_mem_Q2 (hd : d.Hyp) : d.t ∈ d.s56Q2 :=
  Data.s56_mem_Q2_iff.2 ⟨d.s56_t_mem_M, fun e he => hd.L_comm_t (Data.s56_E_le_L d he)⟩

theorem z0_mem_CQ2X {z₀ : G} (hz : d.S56Z0 z₀) : z₀ ∈ CQ2X d :=
  mem_CQ2X_iff.2 ⟨hz.mem_Q2, hz.comm_x⟩

theorem CQ2X_inf_E (hd : d.Hyp) : CQ2X d ⊓ d.E = zpowers d.z := by
  apply le_antisymm
  · rintro e ⟨heZ, heE⟩
    exact hd.s56_E_cent_x5 heE (mem_CQ2X_iff.1 heZ).2.symm
  · exact le_inf (zpowers_le.2 (z_mem_CQ2X hd)) (zpowers_le.2 hd.s56_z_mem_E)

theorem CA_le_Q2 : centralizer (d.A : Set G) ≤ d.s56Q2 := fun c hc =>
  Data.s56_mem_Q2_iff.2 ⟨d.s56_centralizer_A_le_M hc, fun e he =>
    mem_centralizer_iff.1 hc e (Data.s56_E_le_A d he)⟩

theorem mem_CA_of_Q2_eps (hd : d.Hyp) {c : G} (hc : c ∈ d.s56Q2) (hε : d.s56Eps c = 1) :
    c ∈ centralizer (d.A : Set G) := by
  refine (hd.s56_mem_centralizer_A_iff).2 ⟨((Data.s56_mem_Q2_iff).1 hc).2, ?_⟩
  have h1 := hd.s56_conj_t c
  rw [hε, mul_one] at h1
  calc c * d.t = c * d.t * c⁻¹ * c := by group
    _ = d.t * c := by rw [h1]

theorem eps_conj_of_mem_Q2 (hd : d.Hyp) {m w : G} (hm : m ∈ d.M) (hw : w ∈ d.s56Q2) :
    d.s56Eps (m * w * m⁻¹) = m * d.s56Eps w * m⁻¹ := by
  have hwM : w ∈ d.M := ((Data.s56_mem_Q2_iff).1 hw).1
  have h1 : d.s56Eps (m * (w * m⁻¹)) = d.s56Eps m * (m * d.s56Eps (w * m⁻¹) * m⁻¹) :=
    hd.s56_eps_mul m _
  have h2 : d.s56Eps (w * m⁻¹) = d.s56Eps w * d.s56Eps m⁻¹ :=
    hd.s56_eps_mul_Q2 hw (inv_mem hm)
  have h3 : d.s56Eps (m * m⁻¹) = d.s56Eps m * (m * d.s56Eps m⁻¹ * m⁻¹) :=
    hd.s56_eps_mul m m⁻¹
  rw [mul_inv_cancel, hd.s56_eps_one] at h3
  have hE1 : d.s56Eps m ∈ d.E := hd.s56_eps_mem_E hm
  have hE2 : d.s56Eps w ∈ d.E := hd.s56_eps_mem_E hwM
  have hmE : m * d.s56Eps w * m⁻¹ ∈ d.E := (mem_normalizer_iff.1 (hd.s56_ME hm) _).1 hE2
  have hc : d.s56Eps m * (m * d.s56Eps w * m⁻¹) = (m * d.s56Eps w * m⁻¹) * d.s56Eps m :=
    hd.s56_E_comm hE1 hmE
  calc d.s56Eps (m * w * m⁻¹) = d.s56Eps (m * (w * m⁻¹)) := by rw [mul_assoc]
    _ = d.s56Eps m * (m * (d.s56Eps w * d.s56Eps m⁻¹) * m⁻¹) := by rw [h1, h2]
    _ = d.s56Eps m * (m * d.s56Eps w * m⁻¹) * (m * d.s56Eps m⁻¹ * m⁻¹) := by group
    _ = (m * d.s56Eps w * m⁻¹) * d.s56Eps m * (m * d.s56Eps m⁻¹ * m⁻¹) := by rw [hc]
    _ = (m * d.s56Eps w * m⁻¹) * (d.s56Eps m * (m * d.s56Eps m⁻¹ * m⁻¹)) := by group
    _ = m * d.s56Eps w * m⁻¹ := by rw [← h3, mul_one]

theorem eps_mem_zpowers_of_mem_CQ2X (hd : d.Hyp) {w : G} (hw : w ∈ CQ2X d) :
    d.s56Eps w ∈ zpowers d.z := by
  obtain ⟨hwQ2, hwx⟩ := mem_CQ2X_iff.1 hw
  have hwM : w ∈ d.M := ((Data.s56_mem_Q2_iff).1 hwQ2).1
  have hε : d.s56Eps w ∈ d.E := hd.s56_eps_mem_E hwM
  have h1 := hd.s56_eps_conj hd.s56_x5_comm_t w
  have hwc : d.x₅ * w * d.x₅⁻¹ = w := by rw [hwx]; group
  rw [hwc] at h1
  refine hd.s56_E_cent_x5 hε ?_
  calc d.s56Eps w * d.x₅ = d.x₅ * d.s56Eps w * d.x₅⁻¹ * d.x₅ := by rw [← h1]
    _ = d.x₅ * d.s56Eps w := by group

theorem Q0_cent_x5_mem_Q2 (h49 : d.Thm49Statement) (hd : d.Hyp) {k : G} (hk : k ∈ d.s56Q0)
    (hkx : d.x₅ * k = k * d.x₅) : k ∈ d.s56Q2 := by
  have hkM : k ∈ d.M := hd.s56_Q0_le_M h49 hk
  have hkE := ((hd.s56_mem_Q0_iff h49).1 hk).2
  have hxM := hd.s56_x5_mem_M
  have hEZ : ∀ e ∈ d.E, ∀ w ∈ zpowers d.z, e * w = w * e := fun e he w hw =>
    hd.s56_E_comm he (hd.s56_zpowers_le_E hw)
  have hzD : zpowers d.z ≤ d.E ⊓ centralizer ({k} : Set G) := by
    refine zpowers_le.2 (mem_inf.2 ⟨hd.s56_z_mem_E, ?_⟩)
    rw [mem_centralizer_singleton_iff]
    exact (hd.s56_M_comm_z hkM).symm
  have hxD : d.x₅ ∈ normalizer ((d.E ⊓ centralizer ({k} : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (mem_inf.2 ⟨hd.s56_ME hxM,
      Subgroup.le_normalizer (mem_centralizer_singleton_iff.2 hkx)⟩)
  rcases hd.s56_stable_sub_E hzD inf_le_left hxD with hDz | hDE
  · exfalso
    have h := S56.card_le_mul_card_inf_centralizer hEZ hkE
    rw [hDz, hd.s56_card_zpowers_z, hd.A_facts.1] at h
    omega
  · refine Data.s56_mem_Q2_iff.2 ⟨hkM, fun e he => ?_⟩
    have : e ∈ d.E ⊓ centralizer ({k} : Set G) := by rw [hDE]; exact he
    exact mem_centralizer_singleton_iff.1 this.2

theorem Q0_inf_centralizer_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.s56Q0 ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) = CQ2X d := by
  apply le_antisymm
  · rintro k ⟨hk, hkX⟩
    have hkx : d.x₅ * k = k * d.x₅ := mem_centralizer_zpowers_x5_iff.1 hkX
    exact mem_CQ2X_iff.2 ⟨Q0_cent_x5_mem_Q2 h49 hd hk hkx, hkx⟩
  · intro w hw
    obtain ⟨hwQ2, hwx⟩ := mem_CQ2X_iff.1 hw
    exact mem_inf.2 ⟨hd.s56_Q2_le_Q0 h49 hwQ2, mem_centralizer_zpowers_x5_iff.2 hwx⟩

theorem Q0_eq_Q_sup_CQ2X (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.s56Q0 = d.s56Q ⊔ CQ2X d := by
  refine le_antisymm (fun q hq => ?_) (sup_le hd.s56_Q_le_Q0
    (fun w hw => hd.s56_Q2_le_Q0 h49 (CQ2X_le_Q2 d hw)))
  obtain ⟨c, hc, k, hk, rfl⟩ := hd.s56_Q0_decomp hq
  have hk' : k ∈ CQ2X d := by
    rw [← Q0_inf_centralizer_eq h49 hd]
    exact hk
  exact mul_mem (mem_sup_left hc) (mem_sup_right hk')

theorem comm_Q_CQ2X_le_E (h49 : d.Thm49Statement) (hd : d.Hyp) : ⁅d.s56Q, CQ2X d⁆ ≤ d.E := by
  refine Subgroup.commutator_le.2 fun q hq w hw => ?_
  rw [commutatorElement_def]
  obtain ⟨hwQ2, -⟩ := mem_CQ2X_iff.1 hw
  have hwM : w ∈ d.M := ((Data.s56_mem_Q2_iff).1 hwQ2).1
  have hqM : q ∈ d.M := hd.s56_Q0_le_M h49 (hd.s56_Q_le_Q0 hq)
  have hεw := eps_mem_zpowers_of_mem_CQ2X hd hw
  have hgQ2 : q * w * q⁻¹ * w⁻¹ ∈ d.s56Q2 :=
    mul_mem (hd.s56_Q2_conj_mem hqM hwQ2) (inv_mem hwQ2)
  have hgQ : q * w * q⁻¹ * w⁻¹ ∈ d.s56Q := by
    have e : q * w * q⁻¹ * w⁻¹ = q * (w * q⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem hq
      ((mem_normalizer_iff.1 (hd.s56_M_le_normalizer_Q h49 hwM) q⁻¹).1 (inv_mem hq))
  have hεg : d.s56Eps (q * w * q⁻¹ * w⁻¹) = 1 := by
    rw [hd.s56_eps_mul_Q2' (hd.s56_Q2_conj_mem hqM hwQ2) (inv_mem hwQ2),
      hd.s56_eps_inv_Q2 hwQ2, eps_conj_of_mem_Q2 hd hqM hwQ2, hd.s56_M_conj_zpowers hqM hεw]
    exact hd.s56_zpowers_sq hεw
  rw [← hd.s56_Q_inf_C h49]
  exact mem_inf.2 ⟨hgQ, mem_CA_of_Q2_eps hd hgQ2 hεg⟩

theorem card_zpowers_z_sup_z0 (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    Nat.card (zpowers d.z ⊔ zpowers z₀ : Subgroup G) = 4 := by
  have hnot : z₀ ∉ zpowers d.z := fun h => by
    have h1 : d.s56Eps z₀ = 1 :=
      hd.s56_eps_of_comm (hd.L_comm_t (Data.s56_E_le_L d (hd.s56_zpowers_le_E h)))
    rw [hz.eps] at h1
    exact hd.s56_z_ne_one h1
  have h := S56.card_sup_zpowers_eq_two_mul (A := zpowers d.z) (y := z₀)
    (fun a ha => (hz.cen (hd.s56_zpowers_le_E ha)).symm) hz.sq hnot
  rw [h, hd.s56_card_zpowers_z]

theorem Q_inf_CQ2X (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    d.s56Q ⊓ CQ2X d = zpowers d.z ⊔ zpowers z₀ := by
  have hCQX := hd.s56_CQX_eq h49 hz.mem_Q hz.mem_Q2 hz.eps hz.comm_x hz.dich
  apply le_antisymm
  · rintro q ⟨hqQ, hqZ⟩
    rw [← hCQX]
    exact mem_inf.2 ⟨hqQ, mem_centralizer_zpowers_x5_iff.2 (mem_CQ2X_iff.1 hqZ).2⟩
  · exact sup_le (zpowers_le.2 (mem_inf.2 ⟨hd.s56_E_le_Q h49 hd.s56_z_mem_E, z_mem_CQ2X hd⟩))
      (zpowers_le.2 (mem_inf.2 ⟨hz.mem_Q, z0_mem_CQ2X hz⟩))

theorem Q_inf_CQ2X_sup_E (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    d.s56Q ⊓ (CQ2X d ⊔ d.E) = d.E ⊔ zpowers z₀ := by
  apply le_antisymm
  · rintro q ⟨hqQ, hqK⟩
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (CQ2X d) d.E
      (CQ2X_le_normalizer_E hd)
    have hqK' : q ∈ (CQ2X d : Set G) * (d.E : Set G) := by
      rw [← hmul]
      exact hqK
    obtain ⟨w, hw, e, he, rfl⟩ := hqK'
    have hwQ : w ∈ d.s56Q := by
      have e1 : w = (w * e) * e⁻¹ := by group
      rw [e1]
      exact mul_mem hqQ (inv_mem (hd.s56_E_le_Q h49 he))
    have hwzz : w ∈ zpowers d.z ⊔ zpowers z₀ := by
      rw [← Q_inf_CQ2X h49 hd hz]
      exact mem_inf.2 ⟨hwQ, hw⟩
    exact mul_mem ((sup_le_sup_right (zpowers_le.2 hd.s56_z_mem_E) (zpowers z₀)) hwzz)
      (mem_sup_left he)
  · exact sup_le (le_inf (hd.s56_E_le_Q h49) le_sup_right)
      (zpowers_le.2 (mem_inf.2 ⟨hz.mem_Q, mem_sup_left (z0_mem_CQ2X hz)⟩))

theorem card_CA (h49 : d.Thm49Statement) (hd : d.Hyp) :
    (d.ρ.range = titsD.subgroupOf titsA → Nat.card (centralizer (d.A : Set G)) = 2 ^ 6) ∧
      (d.ρ.range = ⊤ → Nat.card (centralizer (d.A : Set G)) = 2 ^ 7) := by
  have hM := (hd.s56_structure_M h49).1
  rcases hd.card_M_N_values h49 with ⟨hR, hMc, -⟩ | ⟨hR, hMc, -⟩
  · refine ⟨fun _ => ?_, fun h => absurd (hR.symm.trans h) Data.s56_subgroupOf_ne_top⟩
    rw [hMc] at hM
    norm_num at hM ⊢
    omega
  · refine ⟨fun h => absurd (hR.symm.trans h).symm Data.s56_subgroupOf_ne_top, fun _ => ?_⟩
    rw [hMc] at hM
    norm_num at hM ⊢
    omega

theorem card_CQ2X_eq (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    Nat.card (CQ2X d) = 2 * Nat.card (centralizer (d.A : Set G) ⊓
      centralizer ((zpowers d.x₅ : Subgroup G) : Set G) : Subgroup G) := by
  let φ : ↥(CQ2X d) →* G := MonoidHom.mk' (fun w => d.s56Eps (w : G)) (fun a b =>
    hd.s56_eps_mul_Q2' (mem_CQ2X_iff.1 a.2).1 (mem_CQ2X_iff.1 b.2).1)
  have hrange : φ.range = zpowers d.z := by
    refine le_antisymm ?_ (zpowers_le.2 ⟨⟨z₀, z0_mem_CQ2X hz⟩, hz.eps⟩)
    rintro _ ⟨w, rfl⟩
    exact eps_mem_zpowers_of_mem_CQ2X hd w.2
  have hK0le : centralizer (d.A : Set G) ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) ≤
      CQ2X d := fun k hk => mem_CQ2X_iff.2 ⟨CA_le_Q2 hk.1, mem_centralizer_zpowers_x5_iff.1 hk.2⟩
  have hker : φ.ker = (centralizer (d.A : Set G) ⊓
      centralizer ((zpowers d.x₅ : Subgroup G) : Set G)).subgroupOf (CQ2X d) := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    show d.s56Eps (w : G) = 1 ↔ _
    constructor
    · intro h
      exact ⟨mem_CA_of_Q2_eps hd (CQ2X_le_Q2 d w.2) h,
        mem_centralizer_zpowers_x5_iff.2 (mem_CQ2X_iff.1 w.2).2⟩
    · rintro ⟨h, -⟩
      exact hd.s56_eps_of_comm ((hd.s56_mem_centralizer_A_iff.1 h).2)
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0le).toEquiv,
    hd.s56_card_zpowers_z] at h
  rw [← h]
  ring

theorem card_CQ2X (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    (d.ρ.range = titsD.subgroupOf titsA → Nat.card (CQ2X d) = 8) ∧
      (d.ρ.range = ⊤ → Nat.card (CQ2X d) = 16) := by
  have hcard := card_CQ2X_eq hd hz
  set K0 : Subgroup G := centralizer (d.A : Set G) ⊓
    centralizer ((zpowers d.x₅ : Subgroup G) : Set G) with hK0
  have hxM := hd.s56_x5_mem_M
  have hK0C : K0 ≤ centralizer (d.A : Set G) := inf_le_left
  have hxK0 : d.x₅ ∈ normalizer (K0 : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro k hk
    exact (mem_centralizer_zpowers_x5_iff.1 hk.2).symm
  have hmod := S56.card_modEq_of_centralizer_le hd.s56_orderOf_x5 hK0C le_rfl hxK0
    (Data.s56_M_le_normalizer_C d hxM)
    (fun c hc hcx => mem_inf.2 ⟨hc, mem_centralizer_zpowers_x5_iff.2 hcx⟩)
  have hzK0 : zpowers d.z ≤ K0 :=
    zpowers_le.2 (mem_inf.2 ⟨hd.s56_E_le_C hd.s56_z_mem_E,
      mem_centralizer_zpowers_x5_iff.2 hd.s56_x5_comm_z⟩)
  have hK0E : K0 ⊓ d.E = zpowers d.z := by
    apply le_antisymm
    · rintro e ⟨⟨-, hex⟩, heE⟩
      exact hd.s56_E_cent_x5 heE (mem_centralizer_zpowers_x5_iff.1 hex).symm
    · exact le_inf hzK0 (zpowers_le.2 hd.s56_z_mem_E)
  have hK0N : K0 ≤ normalizer (d.E : Set G) :=
    hK0C.trans ((d.s56_centralizer_A_le_M).trans hd.s56_ME)
  have hprod := S56.card_sup_mul_card_inf_of_le_normalizer hK0N
  have hle := Subgroup.card_le_of_le (sup_le hK0C hd.s56_E_le_C : K0 ⊔ d.E ≤ centralizer
    (d.A : Set G))
  rw [hK0E, hd.s56_card_zpowers_z, hd.A_facts.1] at hprod
  have heven : 2 ∣ Nat.card K0 := by
    have := Subgroup.card_dvd_of_le hzK0
    rwa [hd.s56_card_zpowers_z] at this
  have hpos : 0 < Nat.card K0 := Nat.card_pos
  unfold Nat.ModEq at hmod
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · have hC := (card_CA h49 hd).1 hR
    rw [hC] at hmod hle
    omega
  · have hC := (card_CA h49 hd).2 hR
    rw [hC] at hmod hle
    omega

theorem relIndex_E_CQ2X_sup (hd : d.Hyp) :
    d.E.relIndex (CQ2X d ⊔ d.E) * 2 = Nat.card (CQ2X d) := by
  have hprod := S56.card_sup_mul_card_inf_of_le_normalizer (H := CQ2X d) (N := d.E)
    (CQ2X_le_normalizer_E hd)
  rw [CQ2X_inf_E hd, hd.s56_card_zpowers_z, hd.A_facts.1] at hprod
  have h2 := Subgroup.relIndex_mul_card (H := d.E) (K := CQ2X d ⊔ d.E)
  rw [inf_of_le_left le_sup_right, hd.A_facts.1] at h2
  omega

theorem isElemAbQuot_CQ2X_sup_E (h49 : d.Thm49Statement) (hd : d.Hyp) {n : ℕ}
    (hn : Nat.card (CQ2X d) = 2 ^ (n + 1)) : IsElemAbQuot (CQ2X d ⊔ d.E) d.E n := by
  have hKQ2 : CQ2X d ⊔ d.E ≤ d.s56Q2 := sup_le (CQ2X_le_Q2 d) hd.s56_E_le_Q2
  have hKM : CQ2X d ⊔ d.E ≤ d.M := hKQ2.trans (Q2_le_M d)
  refine ⟨le_sup_right, Subgroup.normal_subgroupOf_of_le_normalizer (hKM.trans hd.s56_ME),
    fun k hk => hd.s56_Q2_sq_mem_E_all h49 k (hKQ2 hk),
    fun a ha b hb => hd.s56_Q2_comm_mem_E h49 (hKQ2 ha) (hKQ2 hb), ?_⟩
  have h := relIndex_E_CQ2X_sup hd
  rw [hn, pow_succ] at h
  omega

theorem Q0_eq_mul_CA (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) {q : G}
    (hq : q ∈ d.s56Q0) : ∃ a ∈ d.s56Q, ∃ c ∈ centralizer (d.A : Set G), q = a * c := by
  obtain ⟨j, hj, w, hw, rfl⟩ := hd.s56_Q0_eq_J_mul_Q2 h49 hq
  obtain ⟨v, hv, hvε⟩ := hd.s56_V_eps_surj h49 hz (d.s56Eps w)
    (hd.s56_eps_mem_E ((Data.s56_mem_Q2_iff).1 hw).1)
  have hvQ2 : v ∈ d.s56Q2 := hv.2
  refine ⟨j * v, mul_mem (hd.s56_J_le_Q h49 hj) hv.1, v⁻¹ * w, ?_, by group⟩
  refine mem_CA_of_Q2_eps hd (mul_mem (inv_mem hvQ2) hw) ?_
  rw [hd.s56_eps_mul_Q2' (inv_mem hvQ2) hw, hd.s56_eps_inv_Q2 hvQ2, hvε]
  exact hd.s56_E_sq (hd.s56_eps_mem_E ((Data.s56_mem_Q2_iff).1 hw).1)

theorem CA_eq_A_of_range (hd : d.Hyp) (hR : d.ρ.range = titsD.subgroupOf titsA) :
    centralizer (d.A : Set G) = d.A := by
  rcases hd.centralizer_A with ⟨-, hC⟩ | ⟨hR', -⟩
  · exact hC
  · exact absurd (hR.symm.trans hR') Data.s56_subgroupOf_ne_top

theorem CA_eq_A_sup_of_IsV5 (hd : d.Hyp) {y : G} (hy : IsV5 d y) :
    centralizer (d.A : Set G) = d.A ⊔ zpowers y := by
  obtain ⟨hyC, hyρ⟩ := hy
  rcases hd.centralizer_A with ⟨hR, -⟩ | ⟨-, hC⟩
  · exfalso
    have h : d.ρ ⟨y, hyC⟩ ∈ d.ρ.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
    rw [hR, mem_subgroupOf, hyρ] at h
    exact Model.parrottV_five.2.1 h
  · exact hC y hyC hyρ

theorem A_le_Q_sup_t (h49 : d.Thm49Statement) (hd : d.Hyp) : d.A ≤ d.s56Q ⊔ zpowers d.t :=
  sup_le ((hd.s56_E_le_Q h49).trans le_sup_left) le_sup_right

theorem Q0_eq_Q_sup_t (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hR : d.ρ.range = titsD.subgroupOf titsA) : d.s56Q0 = d.s56Q ⊔ zpowers d.t := by
  refine le_antisymm (fun q hq => ?_) (sup_le hd.s56_Q_le_Q0
    (zpowers_le.2 (hd.s56_Q2_le_Q0 h49 (t_mem_Q2 hd))))
  obtain ⟨a, ha, c, hc, rfl⟩ := Q0_eq_mul_CA h49 hd hz hq
  rw [CA_eq_A_of_range hd hR] at hc
  exact mul_mem (mem_sup_left ha) (A_le_Q_sup_t h49 hd hc)

theorem Q0_eq_Q_sup_t_sup_y (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {y : G} (hy : IsV5 d y) : d.s56Q0 = d.s56Q ⊔ zpowers d.t ⊔ zpowers y := by
  have hC := CA_eq_A_sup_of_IsV5 hd hy
  refine le_antisymm (fun q hq => ?_) (sup_le (sup_le hd.s56_Q_le_Q0
    (zpowers_le.2 (hd.s56_Q2_le_Q0 h49 (t_mem_Q2 hd)))) (zpowers_le.2 ?_))
  · obtain ⟨a, ha, c, hc, rfl⟩ := Q0_eq_mul_CA h49 hd hz hq
    rw [hC] at hc
    exact mul_mem (mem_sup_left (mem_sup_left ha))
      ((sup_le_sup_right (A_le_Q_sup_t h49 hd) (zpowers y)) hc)
  · have hyC : y ∈ centralizer (d.A : Set G) := by
      rw [hC]
      exact mem_sup_right (mem_zpowers y)
    exact hd.s56_Q2_le_Q0 h49 (CA_le_Q2 hyC)

theorem card_Q (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    Nat.card d.s56Q = 2 ^ 14 := by
  have hZQ : CQ2X d ≤ normalizer (d.s56Q : Set G) :=
    ((CQ2X_le_Q2 d).trans (Q2_le_M d)).trans (hd.s56_M_le_normalizer_Q h49)
  have hprod := S56.card_sup_mul_card_inf_of_le_normalizer hZQ
  rw [sup_comm, ← Q0_eq_Q_sup_CQ2X h49 hd, inf_comm, Q_inf_CQ2X h49 hd hz,
    card_zpowers_z_sup_z0 hd hz] at hprod
  have hQ0 := (hd.s56_structure_M h49).2.2.2.2.1
  rcases hd.range_ρ with hR | hR
  · rw [hQ0, (card_CA h49 hd).1 hR, (card_CQ2X h49 hd hz).1 hR] at hprod
    norm_num at hprod ⊢
    omega
  · rw [hQ0, (card_CA h49 hd).2 hR, (card_CQ2X h49 hd hz).2 hR] at hprod
    norm_num at hprod ⊢
    omega

theorem node05_core (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    (d.ρ.range = titsD.subgroupOf titsA → d.s56Q0 = d.s56Q ⊔ zpowers d.t) ∧
    (∀ y, IsV5 d y → d.s56Q0 = d.s56Q ⊔ zpowers d.t ⊔ zpowers y) ∧
    ⁅d.s56Q, CQ2X d⁆ ≤ d.E ∧ d.s56Q0 = d.s56Q ⊔ CQ2X d ∧
    d.s56Q ⊓ (CQ2X d ⊔ d.E) = d.E ⊔ zpowers z₀ ∧
    (d.ρ.range = titsD.subgroupOf titsA → IsElemAbQuot (CQ2X d ⊔ d.E) d.E 2) ∧
    (d.ρ.range = ⊤ → IsElemAbQuot (CQ2X d ⊔ d.E) d.E 3) ∧
    Nat.card d.s56Q = 2 ^ 14 :=
  ⟨fun hR => Q0_eq_Q_sup_t h49 hd hz hR, fun _ hy => Q0_eq_Q_sup_t_sup_y h49 hd hz hy,
    comm_Q_CQ2X_le_E h49 hd, Q0_eq_Q_sup_CQ2X h49 hd, Q_inf_CQ2X_sup_E h49 hd hz,
    fun hR => isElemAbQuot_CQ2X_sup_E h49 hd (n := 2)
      (by rw [(card_CQ2X h49 hd hz).1 hR]; norm_num),
    fun hR => isElemAbQuot_CQ2X_sup_E h49 hd (n := 3)
      (by rw [(card_CQ2X h49 hd hz).2 hR]; norm_num),
    card_Q h49 hd hz⟩

end Core

end N

end CFSG.LocalAnalysis.EvenBN.Tits
