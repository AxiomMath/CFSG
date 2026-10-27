module

public import CFSG.CGT.T75D.ComponentSplit
public import CFSG.CGT.T75D.LayerBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75F

open CFSG.Open CFSG.Goldschmidt CFSG.CGT.T75D

section Mixed

variable {Q : Type} [Group Q]

theorem not_odd_of_mixed {A B : Subgroup Q} (hAB : A ⊓ B = ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {a a' b b' : Q} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (ha2 : a * a = 1) (ha'2 : a' * a' = 1) (hb2 : b * b = 1) (hb'2 : b' * b' = 1)
    (haa' : a * a' = a' * a) (hne : a ≠ a') (hbb' : b * b' ≠ b' * b) :
    ¬ (orderOf ((a * b) * (a' * b')) ∣ 2 ∨ Odd (orderOf ((a * b) * (a' * b')))) := by
  have hP : (a * b) * (a' * b') = (a * a') * (b * b') := by
    calc (a * b) * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
      _ = (a * a') * (b * b') := by group
  have hu : a * a' ∈ A := A.mul_mem ha ha'
  have hw : b * b' ∈ B := B.mul_mem hb hb'
  have huw : Commute (a * a') (b * b') := hcomm _ hu _ hw
  have hu2 : (a * a') ^ 2 = 1 := by
    calc (a * a') ^ 2 = (a * a') * (a * a') := by rw [pow_two]
      _ = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [haa']
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [ha2, ha'2, one_mul]
  have hu1 : a * a' ≠ 1 := by
    intro h1
    apply hne
    have : a' = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, inv_eq_of_mul_eq_one_right ha2]
  have hw2 : (b * b') ^ 2 ≠ 1 := by
    intro h1
    apply hbb'
    have h2 : (b * b') * (b * b') = 1 := by rw [← pow_two]; exact h1
    have : b * b' = (b * b')⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this, mul_inv_rev, inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right hb'2]
  rw [hP]
  rintro (hd | hodd)
  ·
    have h1 : ((a * a') * (b * b')) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    rw [huw.mul_pow, hu2, one_mul] at h1
    exact hw2 h1
  ·
    set n := orderOf ((a * a') * (b * b')) with hn
    have h1 : ((a * a') * (b * b')) ^ n = 1 := pow_orderOf_eq_one _
    rw [huw.mul_pow] at h1
    have h2 : (a * a') ^ n = ((b * b') ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (a * a') ^ n ∈ A ⊓ B :=
      ⟨A.pow_mem hu n, by rw [h2]; exact B.inv_mem (B.pow_mem hw n)⟩
    rw [hAB, Subgroup.mem_bot] at h3
    have h4 : orderOf (a * a') ∣ n := orderOf_dvd_of_pow_eq_one h3
    have h5 : orderOf (a * a') = 2 := orderOf_eq_prime hu2 hu1
    rw [h5] at h4
    obtain ⟨c, hc⟩ := hodd
    omega

end Mixed

section Direct

variable {Q : Type} [Group Q] {A B : Subgroup Q}

theorem decomp_unique (hAB : A ⊓ B = ⊥) {a₁ a₂ b₁ b₂ : Q} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h : a₁ * b₁ = a₂ * b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
    calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
      _ = b₂ * b₁⁻¹ := by group
  have h2 : a₂⁻¹ * a₁ ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem ha₂) ha₁, by rw [h1]; exact B.mul_mem hb₂ (B.inv_mem hb₁)⟩
  rw [hAB, Subgroup.mem_bot] at h2
  have ha : a₁ = a₂ := (inv_mul_eq_one.1 h2).symm
  refine ⟨ha, ?_⟩
  rw [ha] at h
  exact mul_left_cancel h

theorem conj_decomp (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {a a₁ b b₁ : Q} (ha : a ∈ A)
    (ha₁ : a₁ ∈ A) (hb : b ∈ B) (hb₁ : b₁ ∈ B) :
    a₁ * b₁ * (a * b) * (a₁ * b₁)⁻¹ = (a₁ * a * a₁⁻¹) * (b₁ * b * b₁⁻¹) := by
  have hb'B : b₁ * b * b₁⁻¹ ∈ B := B.mul_mem (B.mul_mem hb₁ hb) (B.inv_mem hb₁)
  have e1 : b₁ * a = a * b₁ := (hcomm a ha b₁ hb₁).symm
  have e2 : (b₁ * b * b₁⁻¹) * a₁⁻¹ = a₁⁻¹ * (b₁ * b * b₁⁻¹) :=
    (hcomm a₁⁻¹ (A.inv_mem ha₁) _ hb'B).symm
  calc a₁ * b₁ * (a * b) * (a₁ * b₁)⁻¹ = a₁ * (b₁ * a) * b * b₁⁻¹ * a₁⁻¹ := by group
    _ = a₁ * (a * b₁) * b * b₁⁻¹ * a₁⁻¹ := by rw [e1]
    _ = a₁ * a * ((b₁ * b * b₁⁻¹) * a₁⁻¹) := by group
    _ = a₁ * a * (a₁⁻¹ * (b₁ * b * b₁⁻¹)) := by rw [e2]
    _ = (a₁ * a * a₁⁻¹) * (b₁ * b * b₁⁻¹) := by group

theorem exists_noncomm_conj (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZ : Subgroup.center Q = ⊥) {E : Set Q} (hEcl : ∀ d ∈ E, ∀ e ∈ E, ∃ g : Q, e = g * d * g⁻¹)
    (hdec : ∀ q : Q, ∃ a ∈ A, ∃ b ∈ B, q = a * b) (hgen : Subgroup.closure E = ⊤) {a b : Q}
    (ha : a ∈ A) (hb : b ∈ B) (hd : a * b ∈ E) (hb1 : b ≠ 1) :
    ∃ β ∈ B, b * (β * b * β⁻¹) ≠ (β * b * β⁻¹) * b := by
  by_contra hcon
  push Not at hcon
  have hEc : ∀ e ∈ E, e * b = b * e := by
    intro e he
    obtain ⟨g, rfl⟩ := hEcl _ hd e he
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdec g
    rw [conj_decomp hcomm ha ha₁ hb hb₁]
    have ha' : a₁ * a * a₁⁻¹ ∈ A := A.mul_mem (A.mul_mem ha₁ ha) (A.inv_mem ha₁)
    have h1 := hcomm _ ha' b hb
    have h2 := hcon b₁ hb₁
    calc a₁ * a * a₁⁻¹ * (b₁ * b * b₁⁻¹) * b
        = a₁ * a * a₁⁻¹ * ((b₁ * b * b₁⁻¹) * b) := by group
      _ = a₁ * a * a₁⁻¹ * (b * (b₁ * b * b₁⁻¹)) := by rw [← h2]
      _ = (a₁ * a * a₁⁻¹ * b) * (b₁ * b * b₁⁻¹) := by group
      _ = (b * (a₁ * a * a₁⁻¹)) * (b₁ * b * b₁⁻¹) := by rw [h1]
      _ = b * (a₁ * a * a₁⁻¹ * (b₁ * b * b₁⁻¹)) := by group
  have hbz : b ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure E := by rw [hgen]; exact Subgroup.mem_top g
    have hle : Subgroup.closure E ≤ Subgroup.centralizer ({b} : Set Q) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hEc x hx
    have := hle hg
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  rw [hZ, Subgroup.mem_bot] at hbz
  exact hb1 hbz

theorem contra_mixed (hAB : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZ : Subgroup.center Q = ⊥) {E : Set Q} (hEconj : ∀ x ∈ E, ∀ g : Q, g * x * g⁻¹ ∈ E)
    (hE2 : ∀ x ∈ E, x * x = 1) (hEcl : ∀ d ∈ E, ∀ e ∈ E, ∃ g : Q, e = g * d * g⁻¹)
    (hdec : ∀ q : Q, ∃ a ∈ A, ∃ b ∈ B, q = a * b) (hgen : Subgroup.closure E = ⊤)
    (hodd : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)))
    {d e a b a' b' : Q} (hd : d ∈ E) (he : e ∈ E) (ha : a ∈ A) (hb : b ∈ B) (ha' : a' ∈ A)
    (hb' : b' ∈ B) (hdab : d = a * b) (heab : e = a' * b') (hcommde : d * e = e * d)
    (hb1 : b ≠ 1) (hne : a ≠ a') (hconj : ∃ b₁ ∈ B, b' = b₁ * b * b₁⁻¹) : False := by
  have hsq : ∀ {x y : Q}, x ∈ A → y ∈ B → (x * y) * (x * y) = 1 → x * x = 1 ∧ y * y = 1 := by
    intro x y hx hy h1
    have h2 : (x * x) * (y * y) = 1 * 1 := by
      calc (x * x) * (y * y) = x * (x * y) * y := by group
        _ = x * (y * x) * y := by rw [hcomm x hx y hy]
        _ = (x * y) * (x * y) := by group
        _ = 1 * 1 := by rw [h1, one_mul]
    exact decomp_unique hAB (A.mul_mem hx hx) A.one_mem (B.mul_mem hy hy) B.one_mem h2
  obtain ⟨ha2, hb2⟩ := hsq ha hb (by rw [← hdab]; exact hE2 d hd)
  obtain ⟨ha'2, hb'2⟩ := hsq ha' hb' (by rw [← heab]; exact hE2 e he)
  have hcomm2 : (a * a') * (b * b') = (a' * a) * (b' * b) := by
    have h1 : d * e = (a * a') * (b * b') := by
      rw [hdab, heab]
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
        _ = (a * a') * (b * b') := by group
    have h2 : e * d = (a' * a) * (b' * b) := by
      rw [hdab, heab]
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [← hcomm a ha b' hb']
        _ = (a' * a) * (b' * b) := by group
    rw [← h1, ← h2]
    exact hcommde
  obtain ⟨haa', hbb'⟩ := decomp_unique hAB (A.mul_mem ha ha') (A.mul_mem ha' ha)
    (B.mul_mem hb hb') (B.mul_mem hb' hb) hcomm2
  obtain ⟨β₀, hβ₀, hβ₀ne⟩ := exists_noncomm_conj hcomm hZ hEcl hdec hgen ha hb (hdab ▸ hd) hb1
  obtain ⟨b₁, hb₁, hb'eq⟩ := hconj
  set β := β₀ * b₁⁻¹ with hβ
  have hβB : β ∈ B := B.mul_mem hβ₀ (B.inv_mem hb₁)
  set b'' := β₀ * b * β₀⁻¹ with hb''
  have hb''B : b'' ∈ B := B.mul_mem (B.mul_mem hβ₀ hb) (B.inv_mem hβ₀)
  have hb''2 : b'' * b'' = 1 := by
    calc b'' * b'' = β₀ * (b * b) * β₀⁻¹ := by rw [hb'']; group
      _ = 1 := by rw [hb2]; group
  have he₀ : β * e * β⁻¹ = a' * b'' := by
    have h1 : β * a' = a' * β := (hcomm a' ha' β hβB).symm
    calc β * e * β⁻¹ = β * (a' * b') * β⁻¹ := by rw [heab]
      _ = (β * a') * b' * β⁻¹ := by group
      _ = (a' * β) * b' * β⁻¹ := by rw [h1]
      _ = a' * (β * b' * β⁻¹) := by group
      _ = a' * b'' := by rw [hb'eq, hβ, hb'']; group
  have he₀E : a' * b'' ∈ E := he₀ ▸ hEconj e he β
  have hodd' := hodd d hd _ he₀E
  rw [hdab] at hodd'
  exact not_odd_of_mixed hAB hcomm ha ha' hb hb''B ha2 ha'2 hb2 hb''2 haa' hne hβ₀ne hodd'

end Direct

section Simple

variable {Q : Type} [Group Q] [Finite Q]

theorem simple_of_layer (hM : CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q = ⊤)
    (hP : CFSG.Open.pCore 2 Q = ⊥) (hZ : Subgroup.center Q = ⊥) {E : Set Q}
    (hEconj : ∀ x ∈ E, ∀ g : Q, g * x * g⁻¹ ∈ E) (hE2 : ∀ x ∈ E, x * x = 1)
    (hE1 : ∀ x ∈ E, x ≠ 1) (hEcl : ∀ d ∈ E, ∀ e ∈ E, ∃ g : Q, e = g * d * g⁻¹)
    (hgen : Subgroup.closure E = ⊤) (hne : E.Nonempty)
    (hodd : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)))
    (hcomm : ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧ x * y = y * x) : IsSimpleGroup Q := by
  have hlayer : goldschmidtLayer Q = ⊤ := by rwa [hP, bot_sup_eq] at hM
  obtain ⟨X, hX⟩ : ∃ X : Subgroup Q, IsComponentOf X ⊤ := by
    by_contra hno
    push Not at hno
    have hempty : {K : Subgroup Q | IsComponentOf K ⊤} = ∅ := by
      ext K
      simp [hno K]
    have h1 : goldschmidtLayer Q = ⊥ := by rw [goldschmidtLayer, hempty, sSup_empty]
    rw [h1] at hlayer
    obtain ⟨d, hd⟩ := hne
    have hd1 : d ∈ (⊤ : Subgroup Q) := Subgroup.mem_top d
    rw [← hlayer] at hd1
    exact hE1 d hd (Subgroup.mem_bot.1 hd1)
  have hXn : X.Normal := comp_normal hM hX
  have hsup : X ⊔ Subgroup.centralizer (X : Set Q) = ⊤ := comp_sup_centralizer hM hX
  set C := Subgroup.centralizer (X : Set Q) with hC
  have hcommXC : ∀ a ∈ X, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb a ha
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hC, Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by simpa using hXn.conj_mem x hx g⁻¹
    have := hcommXC _ hx' c hc
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * x := by group
  have hdec : ∀ q : Q, ∃ a ∈ X, ∃ b ∈ C, q = a * b := by
    intro q
    have hq : q ∈ ((X ⊔ C : Subgroup Q) : Set Q) := by rw [hsup]; exact Subgroup.mem_top q
    rw [Subgroup.mul_normal] at hq
    obtain ⟨a, ha, b, hb, hab⟩ := hq
    exact ⟨a, ha, b, hb, hab.symm⟩
  have hXC : X ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxz : x ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨a, ha, c, hc, rfl⟩ := hdec g
      have h1 : a * x = x * a := hcommXC a ha x hx.2
      have h2 : x * c = c * x := hcommXC x hx.1 c hc
      calc a * c * x = a * (c * x) := by group
        _ = a * (x * c) := by rw [h2]
        _ = (a * x) * c := by group
        _ = (x * a) * c := by rw [h1]
        _ = x * (a * c) := by group
    rw [hZ, Subgroup.mem_bot] at hxz
    exact hxz
  have hXnt : X ≠ ⊥ := by
    intro hX0
    have h1 : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hX.2.2.2
    have h1' := h1.toNontrivial
    have : Subsingleton ↥X := by
      rw [hX0]
      infer_instance
    have : Subsingleton (↥X ⧸ Subgroup.center ↥X) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim a b]
    exact not_subsingleton _ this
  by_cases hCbot : C = ⊥
  ·
    have hXtop : X = ⊤ := by rw [hCbot, sup_bot_eq] at hsup; exact hsup
    have hcenX : Subgroup.center ↥X = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      have hyC : (y : Q) ∈ C := by
        rw [hC, Subgroup.mem_centralizer_iff]
        intro x hx
        have := Subgroup.mem_center_iff.1 hy ⟨x, hx⟩
        exact congrArg Subtype.val this
      have : (y : Q) ∈ X ⊓ C := ⟨y.2, hyC⟩
      rw [hXC, Subgroup.mem_bot] at this
      exact Subtype.ext this
    let e1 : (↥X ⧸ Subgroup.center ↥X) ≃* ↥X :=
      (QuotientGroup.quotientMulEquivOfEq hcenX).trans QuotientGroup.quotientBot
    have hsX : IsSimpleGroup ↥X := by
      have : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hX.2.2.2
      exact e1.symm.isSimpleGroup
    let e2 : ↥X ≃* Q := (MulEquiv.subgroupCongr hXtop).trans Subgroup.topEquiv
    exact e2.symm.isSimpleGroup
  · exfalso
    obtain ⟨d, hd, e, he, hde, hcommde⟩ := hcomm
    obtain ⟨x, hx, c, hc, hdxc⟩ := hdec d
    have hdn : ∀ y ∈ E, y ∈ X → False := by
      intro y hy hyX
      have hEX : E ⊆ (X : Set Q) := by
        intro z hz
        obtain ⟨g, rfl⟩ := hEcl y hy z hz
        simpa using hXn.conj_mem y hyX g
      have hX1 : X = ⊤ := by
        rw [eq_top_iff, ← hgen, Subgroup.closure_le]
        exact hEX
      apply hCbot
      have : (⊤ : Subgroup Q) ⊓ C = ⊥ := by rw [← hX1]; exact hXC
      rwa [top_inf_eq] at this
    have hdn' : ∀ y ∈ E, y ∈ C → False := by
      intro y hy hyC
      have hEC : E ⊆ (C : Set Q) := by
        intro z hz
        obtain ⟨g, rfl⟩ := hEcl y hy z hz
        simpa using hCn.conj_mem y hyC g
      have hC1 : C = ⊤ := by
        rw [eq_top_iff, ← hgen, Subgroup.closure_le]
        exact hEC
      apply hXnt
      have : X ⊓ (⊤ : Subgroup Q) = ⊥ := by rw [← hC1]; exact hXC
      rwa [inf_top_eq] at this
    have hc1 : c ≠ 1 := by
      intro h1
      apply hdn d hd
      rw [hdxc, h1, mul_one]
      exact hx
    have hx1 : x ≠ 1 := by
      intro h1
      apply hdn' d hd
      rw [hdxc, h1, one_mul]
      exact hc
    obtain ⟨g, hge⟩ := hEcl d hd e he
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdec g
    have hconjd := conj_decomp hcommXC hx ha₁ hc hb₁
    rw [← hdxc] at hconjd
    rw [hconjd] at hge
    have hx'X : a₁ * x * a₁⁻¹ ∈ X := X.mul_mem (X.mul_mem ha₁ hx) (X.inv_mem ha₁)
    have hc'C : b₁ * c * b₁⁻¹ ∈ C := C.mul_mem (C.mul_mem hb₁ hc) (C.inv_mem hb₁)
    by_cases hxx : x = a₁ * x * a₁⁻¹
    ·
      have hcc : c ≠ b₁ * c * b₁⁻¹ := by
        intro h1
        apply hde
        rw [hdxc, hge, ← hxx, ← h1]
      refine contra_mixed (A := C) (B := X) (by rw [inf_comm]; exact hXC)
        (fun a ha b hb => (hcommXC b hb a ha).symm) hZ hEconj hE2 hEcl
        (fun q => by
          obtain ⟨a, ha, b, hb, hab⟩ := hdec q
          exact ⟨b, hb, a, ha, by rw [hab]; exact hcommXC a ha b hb⟩)
        hgen hodd hd he hc hx hc'C hx'X ?_ ?_ hcommde hx1 hcc ⟨a₁, ha₁, rfl⟩
      · rw [hdxc]; exact hcommXC x hx c hc
      · rw [hge, ← hxx]; exact (hcommXC x hx _ hc'C)
    · refine contra_mixed (A := X) (B := C) hXC hcommXC hZ hEconj hE2 hEcl hdec hgen hodd hd he hx
        hc
        hx'X hc'C hdxc hge hcommde hc1 hxx ⟨b₁, hb₁, rfl⟩

end Simple

end CFSG.CGT.T75F
