module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD10

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Cq_le_center (hb : ZJBound t) (hZ : ∀ m ∈ Mc, m ∉ Q → m * m ∉ Y)
    (hsq : ∀ m ∈ Mc, m * m ∈ Q ⊓ centralizer ({t * τ} : Set H)) {x : H} (hx : x ∈ Mc)
    (hxQ : x ∉ Q) :
    ∀ c ∈ Q ⊓ centralizer ({t * τ} : Set H), ∀ m ∈ Mc, m * c = c * m := by
  let S : Set H := {u | (∃ m ∈ Mc, u = m * m) ∨ u ∈ V}
  let U : Subgroup H := Subgroup.closure S
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hUC : U ≤ Q ⊓ centralizer ({t * τ} : Set H) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro u (⟨m, hm, rfl⟩ | hv)
    · exact hsq m hm
    · exact h.V_le_Cq hv
  have hVU : V ≤ U := fun v hv => Subgroup.subset_closure (Or.inr hv)
  have hρU : ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem a ha =>
        rcases ha with ⟨m, hm, rfl⟩ | hv
        · have hc : ρ * m * ρ⁻¹ ∈ Mc := h.Mc_conj_rho hMh hMc hm
          have heq : ρ * (m * m) * ρ⁻¹ = (ρ * m * ρ⁻¹) * (ρ * m * ρ⁻¹) := by group
          rw [heq]
          exact Subgroup.subset_closure (Or.inl ⟨ρ * m * ρ⁻¹, hc, rfl⟩)
        · exact Subgroup.subset_closure (Or.inr (h.rho_norm_V a hv))
    | one => simpa using U.one_mem
    | mul a b _ _ iha ihb =>
        have heq : ρ * (a * b) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) := by group
        rw [heq]
        exact U.mul_mem iha ihb
    | inv a _ iha =>
        have heq : ρ * a⁻¹ * ρ⁻¹ = (ρ * a * ρ⁻¹)⁻¹ := by group
        rw [heq]
        exact U.inv_mem iha
  have hx2U : x * x ∈ U := Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)
  have hx2V : x * x ∉ V := fun hv => hZ x hx hxQ (hVY hv)
  have hUeq : U = Q ⊓ centralizer ({t * τ} : Set H) :=
    h.eq_Cq_of_rho_inv hMh hMc hb hUC hVU hρU hx2U hx2V
  have hcentU : ∀ u ∈ U, ∀ m ∈ Mc, m * u = u * m := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem a ha =>
        rcases ha with ⟨m₀, hm₀, rfl⟩ | hv
        · intro m hm
          exact (h.Mc_sq_central hMh hMc hm₀ hm).symm
        · intro m hm
          have hc := h.Mh_cent_V hMh (h.Mc_le_Mh hMh hMc hm) hv
          calc m * a = (m * a * m⁻¹) * m := by group
            _ = a * m := by rw [hc]
    | one => intro m _; rw [mul_one, one_mul]
    | mul a b _ _ iha ihb =>
        intro m hm
        exact Commute.mul_right (iha m hm) (ihb m hm)
    | inv a _ iha =>
        intro m hm
        exact Commute.inv_right (iha m hm)
  intro c hc m hm
  have hcU : c ∈ U := by rw [hUeq]; exact hc
  exact hcentU c hcU m hm

theorem cent_tt_comm
    (hcen : ∀ c ∈ Q ⊓ centralizer ({t * τ} : Set H), ∀ m ∈ Mc, m * c = c * m) :
    ∀ a ∈ Mc ⊓ centralizer ({t * τ} : Set H), ∀ b ∈ Mc ⊓ centralizer ({t * τ} : Set H),
      a * b = b * a := by
  let C : Subgroup H := Mc ⊓ centralizer ({t * τ} : Set H)
  let Cq : Subgroup H := Q ⊓ centralizer ({t * τ} : Set H)
  change ∀ a ∈ C, ∀ b ∈ C, a * b = b * a
  haveI hQn : Q.Normal := ⟨fun x hx g => h.normal_Q g x hx⟩
  intro a ha b hb
  by_cases hcover : ∀ w ∈ C, w ∈ Q
  · exact h.Q_comm a (hcover a ha) b (hcover b hb)
  · push Not at hcover
    obtain ⟨c, hcC, hcQ⟩ := hcover
    have hcMc : c ∈ Mc := (Subgroup.mem_inf.mp hcC).1
    have hcKh : c ∈ centralizer ({t * τ} : Set H) := (Subgroup.mem_inf.mp hcC).2
    have hc'Mc : ρ * c * ρ⁻¹ ∈ Mc := h.Mc_conj_rho hMh hMc hcMc
    have hc'Kh : ρ * c * ρ⁻¹ ∈ centralizer ({t * τ} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hcKh ⊢
      have hρ : ρ * (t * τ) = (t * τ) * ρ := by
        calc ρ * (t * τ) = (ρ * t) * τ := by group
          _ = (t * ρ) * τ := by rw [h.t_rho]
          _ = t * (ρ * τ) := by group
          _ = t * (τ * ρ) := by rw [h.tau_rho]
          _ = (t * τ) * ρ := by group
      have hρi : ρ⁻¹ * (t * τ) = (t * τ) * ρ⁻¹ := by
        have hcong := congrArg (fun x => ρ⁻¹ * x * ρ⁻¹) hρ
        have h' : (t * τ) * ρ⁻¹ = ρ⁻¹ * (t * τ) := by simpa [mul_assoc] using hcong
        exact h'.symm
      calc (ρ * c * ρ⁻¹) * (t * τ)
          = ρ * (c * (ρ⁻¹ * (t * τ))) := by group
        _ = ρ * (c * ((t * τ) * ρ⁻¹)) := by rw [hρi]
        _ = ρ * (c * (t * τ)) * ρ⁻¹ := by group
        _ = ρ * ((t * τ) * c) * ρ⁻¹ := by rw [hcKh]
        _ = (ρ * (t * τ)) * (c * ρ⁻¹) := by group
        _ = ((t * τ) * ρ) * (c * ρ⁻¹) := by rw [hρ]
        _ = (t * τ) * (ρ * c * ρ⁻¹) := by group
    have hcc' : c * (ρ * c * ρ⁻¹) = (ρ * c * ρ⁻¹) * c := h.Mc_comm_rho_eq_one hMh hMc hcMc
    let W : Subgroup H := Subgroup.closure ({c, ρ * c * ρ⁻¹} : Set H)
    have hWMc : W ≤ Mc := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g (rfl | rfl)
      · exact hcMc
      · exact hc'Mc
    have hWKh : W ≤ centralizer ({t * τ} : Set H) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g (rfl | rfl)
      · exact hcKh
      · exact hc'Kh
    have hWC : W ≤ C := fun w hw => Subgroup.mem_inf.mpr ⟨hWMc hw, hWKh hw⟩
    have hcW : ∀ w ∈ W, c * w = w * c := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem g hg =>
          rcases hg with rfl | rfl
          · rfl
          · exact hcc'
      | one => simp
      | mul u v _ _ ihu ihv => exact Commute.mul_right ihu ihv
      | inv u _ ihu => exact Commute.inv_right ihu
    have hc'W : ∀ w ∈ W, (ρ * c * ρ⁻¹) * w = w * (ρ * c * ρ⁻¹) := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem g hg =>
          rcases hg with rfl | rfl
          · exact hcc'.symm
          · rfl
      | one => simp
      | mul u v _ _ ihu ihv => exact Commute.mul_right ihu ihv
      | inv u _ ihu => exact Commute.inv_right ihu
    have hWcomm : ∀ w₁ ∈ W, ∀ w₂ ∈ W, w₁ * w₂ = w₂ * w₁ := by
      intro w₁ hw₁
      induction hw₁ using Subgroup.closure_induction with
      | mem g hg =>
          rcases hg with rfl | rfl
          · exact hcW
          · exact hc'W
      | one => intro w₂ _; rw [one_mul, mul_one]
      | mul u v _ _ ihu ihv =>
          intro w₂ hw₂
          exact Commute.mul_left (ihu w₂ hw₂) (ihv w₂ hw₂)
      | inv u _ ihu =>
          intro w₂ hw₂
          exact Commute.inv_left (ihu w₂ hw₂)
    have hMcLeWQ : Mc ≤ W ⊔ Q := h.Mc_le_closure hMh hMc hcMc hcQ
    have haWQ : a ∈ W ⊔ Q := hMcLeWQ (Subgroup.mem_inf.mp ha).1
    have hbWQ : b ∈ W ⊔ Q := hMcLeWQ (Subgroup.mem_inf.mp hb).1
    obtain ⟨wa, hwa, qa, hqa, hwaq⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := W) (t := Q) (x := a)).mp haWQ
    obtain ⟨wb, hwb, qb, hqb, hwbq⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := W) (t := Q) (x := b)).mp hbWQ
    have hqa_eq : qa = wa⁻¹ * a := by rw [← hwaq]; group
    have hqaC : qa ∈ C := by
      rw [hqa_eq]
      exact Subgroup.mul_mem C (Subgroup.inv_mem C (hWC hwa)) ha
    have hqaCq : qa ∈ Cq :=
      Subgroup.mem_inf.mpr ⟨hqa, (Subgroup.mem_inf.mp hqaC).2⟩
    have hqb_eq : qb = wb⁻¹ * b := by rw [← hwbq]; group
    have hqbC : qb ∈ C := by
      rw [hqb_eq]
      exact Subgroup.mul_mem C (Subgroup.inv_mem C (hWC hwb)) hb
    have hqbCq : qb ∈ Cq :=
      Subgroup.mem_inf.mpr ⟨hqb, (Subgroup.mem_inf.mp hqbC).2⟩
    have hwa_wbqb : Commute wa (wb * qb) :=
      Commute.mul_right (hWcomm wa hwa wb hwb) (hcen qb hqbCq wa (hWMc hwa))
    have hqa_wbqb : Commute qa (wb * qb) :=
      Commute.mul_right ((hcen qa hqaCq wb (hWMc hwb)).symm) (h.Q_comm qa hqa qb hqb)
    have hmain : (wa * qa) * (wb * qb) = (wb * qb) * (wa * qa) :=
      Commute.mul_left hwa_wbqb hqa_wbqb
    rw [← hwaq, ← hwbq]
    exact hmain

theorem exists_c_fourth (hb : ZJBound t) (hZ : ∀ m ∈ Mc, m ∉ Q → m * m ∉ Y)
    (hsq : ∀ m ∈ Mc, m * m ∈ Q ⊓ centralizer ({t * τ} : Set H))
    (hab : ∀ a ∈ Mc ⊓ centralizer ({t * τ} : Set H), ∀ b ∈ Mc ⊓ centralizer ({t * τ} : Set H),
      a * b = b * a)
    (hcard : 64 ≤ Nat.card ↥(Mc ⊓ centralizer ({t * τ} : Set H))) {v : H} (hv : v ∈ V) :
    ∃ c ∈ Mc ⊓ centralizer ({t * τ} : Set H), c * c * (c * c) = v := by
  let C : Subgroup H := Mc ⊓ centralizer ({t * τ} : Set H)
  let Cq : Subgroup H := Q ⊓ centralizer ({t * τ} : Set H)
  change ∃ c ∈ C, c * c * (c * c) = v
  change 64 ≤ Nat.card ↥C at hcard
  let φ : C →* H := MonoidHom.mk' (fun c : C => (c : H) ^ 4) (fun a b => by
    show (((a * b : C) : H)) ^ 4 = (a : H) ^ 4 * (b : H) ^ 4
    rw [show (((a * b : C) : H)) = (a : H) * (b : H) from rfl]
    exact Commute.mul_pow (hab a a.2 b b.2) 4)
  have hφV : ∀ c : C, φ c ∈ V := by
    intro c
    change (c : H) ^ 4 ∈ V
    have hsqQ : (c : H) ^ 2 ∈ Q := by
      simpa [pow_two] using (Subgroup.mem_inf.mp (hsq (c : H) c.2.1)).1
    have h2 : ((c : H) ^ 2) ^ 2 ∈ V := h.sq_mem_V ((c : H) ^ 2) hsqQ
    have h4 : (c : H) ^ 4 = ((c : H) ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    rw [h4]
    exact h2
  have hkerQ : ∀ c : C, φ c = 1 ↔ (c : H) ∈ Q := by
    intro c
    constructor
    · intro hphi
      change (c : H) ^ 4 = 1 at hphi
      by_contra hcQ
      have hsqQ : (c : H) ^ 2 ∈ Q := by
        simpa [pow_two] using (Subgroup.mem_inf.mp (hsq (c : H) c.2.1)).1
      have h4 : (c : H) ^ 4 = ((c : H) ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      rw [h4] at hphi
      have h2 : ((c : H) ^ 2) * ((c : H) ^ 2) = 1 := by
        simpa [pow_two] using hphi
      have hY : (c : H) * (c : H) ∈ Y := by
        simpa [pow_two] using h.Y_mem ((c : H) ^ 2) hsqQ h2
      exact hZ (c : H) c.2.1 hcQ hY
    · intro hcQ
      change (c : H) ^ 4 = 1
      have hsq : (c : H) ^ 2 ∈ V := h.sq_mem_V (c : H) hcQ
      have hsqY : (c : H) ^ 2 ∈ Y := by rw [h.Y_eq]; exact Subgroup.mem_sup_left hsq
      have h2 : ((c : H) ^ 2) ^ 2 = 1 := by
        simpa [pow_two] using h.Y_sq ((c : H) ^ 2) hsqY
      have h4 : (c : H) ^ 4 = ((c : H) ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      rw [h4]
      exact h2
  have hCqC : Cq ≤ C := by
    intro z hz
    obtain ⟨hzQ, hzK⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨h.Q_le_Mc hMh hMc hzQ, hzK⟩
  have hφker : φ.ker = Cq.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact Subgroup.mem_inf.mpr ⟨(hkerQ c).mp h, (Subgroup.mem_inf.mp c.2).2⟩
    · intro h
      exact (hkerQ c).mpr (Subgroup.mem_inf.mp h).1
  have hkerCard : Nat.card φ.ker = 16 := by
    rw [hφker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCqC).toEquiv]
    exact h.card_Cq hMh hMc hb
  have hrangeCard : 4 ≤ Nat.card φ.range := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hkerCard] at hmul
    omega
  have hφrangeV : φ.range ≤ V := by
    intro w hw
    rw [MonoidHom.mem_range] at hw
    obtain ⟨c, rfl⟩ := hw
    exact hφV c
  have hrangeEq : Nat.card V ≤ Nat.card φ.range := by
    rw [h.card_V]
    exact hrangeCard
  have hφrange : φ.range = V := Subgroup.eq_of_le_of_card_ge hφrangeV hrangeEq
  have hv' : v ∈ φ.range := by rw [hφrange]; exact hv
  rw [MonoidHom.mem_range] at hv'
  obtain ⟨c, hc⟩ := hv'
  refine ⟨(c : H), c.2, ?_⟩
  change (c : H) ^ 4 = v at hc
  have h4 : (c : H) ^ 4 = (c : H) * (c : H) * ((c : H) * (c : H)) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    simp only [pow_two]
  rw [← h4]
  exact hc

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
