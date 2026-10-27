module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Fit
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Refl
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Util

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final

section Reflect'

variable {Y : Type} [Group Y] [Finite Y] {Sb Rb Lk Lk' : Subgroup Y} {r r' : ℕ}

omit [Finite Y] in
theorem Pair.inf_cases (h : Pair Lk Lk' r r') {z₀ : Y} (hz : z₀ ∈ Lk ⊓ Lk') (hz1 : z₀ ≠ 1)
    {x : Y} (hx : x ∈ Lk ⊓ Lk') : x = 1 ∨ x = z₀ := by
  by_contra hcon
  push Not at hcon
  have h2 := h.inf
  rw [Nat.card_eq_two_iff' (1 : ↥(Lk ⊓ Lk'))] at h2
  obtain ⟨y, -, hy⟩ := h2
  have h1 : (⟨x, hx⟩ : ↥(Lk ⊓ Lk')) = y := hy _ (fun h => hcon.1 (congrArg Subtype.val h))
  have h2 : (⟨z₀, hz⟩ : ↥(Lk ⊓ Lk')) = y := hy _ (fun h => hz1 (congrArg Subtype.val h))
  exact hcon.2 (congrArg Subtype.val (h1.trans h2.symm))

theorem Factor.reflect' (h : Factor Sb Rb Lk Lk' r r') (hn' : Lk'.Normal) {a a' e : Y} (ha : a ∈ Lk)
    (ha' : a' ∈ Lk') (ha2 : a * a ≠ 1) (hsq : ∀ c ∈ Lk, c * (a * a) = (a * a) * c)
    (hsq' : a' * a' = a * a) (he2 : e * e = 1) (het : e * (a * a') = (a * a') * e)
    (he1 : e ∉ Lk ⊓ Lk') (he3 : e * (a * a') ∉ Lk ⊓ Lk') :
    ∀ k ∈ Lk, Odd (orderOf k) → k * a = a * k → e * k * e⁻¹ = k⁻¹ := by
  have hnL := h.normal
  have p := h.toPair
  have hcomm : ∀ x ∈ Lk, ∀ y ∈ Lk', x * y = y * x := p.comm
  have hea : e * a * e⁻¹ * a⁻¹ ∈ Lk ⊓ Lk' := by
    have hu : e * a * e⁻¹ ∈ Lk := by simpa using hnL.conj_mem a ha e
    have hv : e * a' * e⁻¹ ∈ Lk' := by simpa using hn'.conj_mem a' ha' e
    refine ⟨Lk.mul_mem hu (Lk.inv_mem ha), ?_⟩
    have huv : (e * a * e⁻¹) * (e * a' * e⁻¹) = a * a' := by
      calc (e * a * e⁻¹) * (e * a' * e⁻¹) = e * (a * a') * e⁻¹ := by group
        _ = a * a' := by rw [het]; group
    have h3 : e * a * e⁻¹ = a * a' * (e * a' * e⁻¹)⁻¹ := by
      rw [← huv]; group
    have h2 : e * a * e⁻¹ * a⁻¹ = a' * (e * a' * e⁻¹)⁻¹ := by
      rw [h3]
      have h4 := hcomm a ha (a' * (e * a' * e⁻¹)⁻¹) (Lk'.mul_mem ha' (Lk'.inv_mem hv))
      calc a * a' * (e * a' * e⁻¹)⁻¹ * a⁻¹ = a * (a' * (e * a' * e⁻¹)⁻¹) * a⁻¹ := by group
        _ = (a' * (e * a' * e⁻¹)⁻¹) * a * a⁻¹ := by rw [h4]
        _ = a' * (e * a' * e⁻¹)⁻¹ := by group
    rw [h2]
    exact Lk'.mul_mem ha' (Lk'.inv_mem hv)
  have hE1 : ¬ ∀ x ∈ Lk, e * x = x * e := fun hc => he1 (h.mem_inf_of_cen he2 hc)
  have hE2 : ¬ ∀ x ∈ Lk, (e * a) * x = x * (e * a) := by
    intro hc
    apply he3
    have hc' : ∀ x ∈ Lk, (e * (a * a')) * x = x * (e * (a * a')) := by
      intro x hx
      have h1 := hc x hx
      have h2 := hcomm x hx a' ha'
      calc e * (a * a') * x = (e * a) * (a' * x) := by group
        _ = (e * a) * (x * a') := by rw [← h2]
        _ = ((e * a) * x) * a' := by group
        _ = (x * (e * a)) * a' := by rw [h1]
        _ = x * (e * (a * a')) := by group
    have haaI : a * a ∈ Lk ⊓ Lk' := ⟨mul_mem ha ha, hsq' ▸ mul_mem ha' ha'⟩
    have hy2 : (e * (a * a')) * (e * (a * a')) = 1 := by
      calc e * (a * a') * (e * (a * a')) = e * ((a * a') * e) * (a * a') := by group
        _ = e * (e * (a * a')) * (a * a') := by rw [← het]
        _ = (e * e) * ((a * a') * (a * a')) := by group
        _ = (a * a') * (a * a') := by rw [he2, one_mul]
        _ = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [← hcomm a ha a' ha']
        _ = (a * a) * (a' * a') := by group
        _ = (a * a) * (a * a) := by rw [hsq']
        _ = 1 := p.sq_of_mem_inf haaI
    exact h.mem_inf_of_cen hy2 hc'
  exact h.reflect ha ha2 hsq he2 hea hE1 hE2

end Reflect'

section Big

variable {Y : Type} [Group Y] [Finite Y] {Sb Rb L₁ L₂ : Subgroup Y} {r₁ r₂ : ℕ}

omit [Finite Y] in
theorem Pair.conj_div_mem {Lk Lk' : Subgroup Y} {r r' : ℕ} (p : Pair Lk Lk' r r') (hn : Lk.Normal)
    (hn' : Lk'.Normal) {a a' m : Y} (ha : a ∈ Lk) (ha' : a' ∈ Lk')
    (hm : m * (a * a') = (a * a') * m) : m * a * m⁻¹ * a⁻¹ ∈ Lk' := by
  have hq : m * a * m⁻¹ ∈ Lk := by simpa using hn.conj_mem a ha m
  have hq' : m * a' * m⁻¹ ∈ Lk' := by simpa using hn'.conj_mem a' ha' m
  have hqq : (m * a * m⁻¹) * (m * a' * m⁻¹) = a * a' := by
    calc (m * a * m⁻¹) * (m * a' * m⁻¹) = m * (a * a') * m⁻¹ := by group
      _ = a * a' := by rw [hm]; group
  have h1 : m * a * m⁻¹ = a * a' * (m * a' * m⁻¹)⁻¹ := by rw [← hqq]; group
  have hX : a' * (m * a' * m⁻¹)⁻¹ ∈ Lk' := Lk'.mul_mem ha' (Lk'.inv_mem hq')
  have hc := p.comm a ha _ hX
  have h2 : m * a * m⁻¹ * a⁻¹ = a' * (m * a' * m⁻¹)⁻¹ := by
    rw [h1]
    calc a * a' * (m * a' * m⁻¹)⁻¹ * a⁻¹ = a * (a' * (m * a' * m⁻¹)⁻¹) * a⁻¹ := by group
      _ = (a' * (m * a' * m⁻¹)⁻¹) * a * a⁻¹ := by rw [hc]
      _ = a' * (m * a' * m⁻¹)⁻¹ := by group
  rw [h2]
  exact hX

omit [Finite Y] in
theorem Pair.comm_prod {Lk Lk' : Subgroup Y} {r r' : ℕ} (p : Pair Lk Lk' r r') {a a' k : Y}
    (ha' : a' ∈ Lk') (hk : k ∈ Lk) (hka : k * a = a * k) : k * (a * a') = (a * a') * k := by
  have h1 := p.comm k hk a' ha'
  calc k * (a * a') = (k * a) * a' := by group
    _ = (a * k) * a' := by rw [hka]
    _ = a * (k * a') := by group
    _ = a * (a' * k) := by rw [h1]
    _ = (a * a') * k := by group

theorem ykey_big (f₁ : Factor Sb Rb L₁ L₂ r₁ r₂) (f₂ : Factor Sb Rb L₂ L₁ r₂ r₁)
    (hF : generalizedFitting Y ≤ L₁ ⊔ L₂)
    {t e : Y} (ht : t ∈ L₁ ⊔ L₂) (ht2 : t * t = 1) (htI : t ∉ L₁ ⊓ L₂)
    (he2 : e * e = 1) (het : e * t = t * e) (heI : e ∉ L₁ ⊓ L₂) (hetI : e * t ∉ L₁ ⊓ L₂)
    {Bb : Subgroup Y} (hBodd : Odd (Nat.card ↥Bb)) (hBt : ∀ b ∈ Bb, b * t = t * b)
    (hBn : ∀ m : Y, m * t = t * m → ∀ b ∈ Bb, m * b * m⁻¹ ∈ Bb)
    (hBe : ∀ b ∈ Bb, e * b = b * e) : Bb = ⊥ := by
  by_contra hne
  have hn₁ : L₁.Normal := f₁.normal
  have hn₂ : L₂.Normal := f₂.normal
  have p₁ := f₁.toPair
  have p₂ := f₂.toPair
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := p₁.exists_mul ht
  have hc12 : a₁ * a₂ = a₂ * a₁ := p₁.comm a₁ ha₁ a₂ ha₂
  have hprod : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [hc12]
      _ = (a₁ * a₂) * (a₁ * a₂) := by group
      _ = 1 := ht2
  have hI : a₁ * a₁ ∈ L₁ ⊓ L₂ := by
    refine ⟨L₁.mul_mem ha₁ ha₁, ?_⟩
    have : a₁ * a₁ = (a₂ * a₂)⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [this]; exact L₂.inv_mem (L₂.mul_mem ha₂ ha₂)
  have hsq : a₁ * a₁ = a₂ * a₂ := by
    have h1 := p₁.sq_of_mem_inf hI
    have : a₂ * a₂ = (a₁ * a₁)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [this]; exact (inv_eq_of_mul_eq_one_right h1).symm
  have ha₁2 : a₁ * a₁ ≠ 1 := by
    intro h1
    apply htI
    have h2 : a₂ * a₂ = 1 := by rw [← hsq]; exact h1
    have h3 : a₂ ∈ L₁ ⊓ L₂ := p₁.mem_inf_of_sq ha₂ h2
    have h4 : a₁ ∈ L₂ ⊓ L₁ := p₂.mem_inf_of_sq ha₁ h1
    rw [inf_comm] at h4
    exact (L₁ ⊓ L₂).mul_mem h4 h3
  have ha₂2 : a₂ * a₂ ≠ 1 := by rw [← hsq]; exact ha₁2
  have hsq₁ : ∀ c ∈ L₁, c * (a₁ * a₁) = (a₁ * a₁) * c := fun c hc => p₁.comm c hc _ hI.2
  have hI' : a₂ * a₂ ∈ L₁ := by rw [← hsq]; exact hI.1
  have hsq₂ : ∀ c ∈ L₂, c * (a₂ * a₂) = (a₂ * a₂) * c := fun c hc => p₂.comm c hc _ hI'
  have hcen : ∀ m ∈ centralizer ({a₁ * a₂} : Set Y), m * (a₁ * a₂) = (a₁ * a₂) * m := fun m hm =>
    (Subgroup.mem_centralizer_iff.1 hm _ rfl).symm
  obtain ⟨W, hWB, hWne, hWab, hWn⟩ := exists_abelian_normalized hBodd hne
    (centralizer ({a₁ * a₂} : Set Y)) (fun m hm b hb => hBn m (hcen m hm) b hb)
  have hWM : W ≤ centralizer ({a₁ * a₂} : Set Y) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hBt w (hWB hw)).symm
  have hWodd : Odd (Nat.card ↥W) := hBodd.of_dvd_nat (Subgroup.card_dvd_of_le hWB)
  have hkM : ∀ {k : Y}, (k * (a₁ * a₂) = (a₁ * a₂) * k) → k ∈ centralizer ({a₁ * a₂} : Set Y) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hk.symm
  have hfit₁ := fit_factor (Lk := L₁) (r := r₁) p₁.odd p₁.gt p₁.hm ha₁ ha₁2 hsq₁
    (centralizer ({a₁ * a₂} : Set Y))
    (fun m hm c hc => p₁.comm c hc _ (p₁.conj_div_mem hn₁ hn₂ ha₁ ha₂ (hcen m hm)))
    W hWM hWodd hWab
    (fun k hk _ hka => ⟨k, hkM (p₁.comm_prod ha₂ hk hka), fun x _ => rfl,
      fun w hw => hWn k (hkM (p₁.comm_prod ha₂ hk hka)) w hw⟩)
  have hcen' : ∀ m ∈ centralizer ({a₁ * a₂} : Set Y), m * (a₂ * a₁) = (a₂ * a₁) * m := by
    intro m hm; rw [← hc12]; exact hcen m hm
  have hfit₂ := fit_factor (Lk := L₂) (r := r₂) p₂.odd p₂.gt p₂.hm ha₂ ha₂2 hsq₂
    (centralizer ({a₁ * a₂} : Set Y))
    (fun m hm c hc => p₂.comm c hc _ (p₂.conj_div_mem hn₂ hn₁ ha₂ ha₁ (hcen' m hm)))
    W hWM hWodd hWab
    (fun k hk _ hka => ⟨k, hkM (by rw [hc12]; exact p₂.comm_prod ha₁ hk hka), fun x _ => rfl,
      fun w hw => hWn k (hkM (by rw [hc12]; exact p₂.comm_prod ha₁ hk hka)) w hw⟩)
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hWne (eq_bot_iff.2 fun x hx => by simpa using hcon x hx)
  obtain ⟨k₁, hk₁, hk₁o, hk₁a, hk₁act⟩ := hfit₁ w hwW
  obtain ⟨k₂, hk₂, hk₂o, hk₂a, hk₂act⟩ := hfit₂ w hwW
  have hr₁ : e * k₁ * e⁻¹ = k₁⁻¹ :=
    f₁.reflect' hn₂ ha₁ ha₂ ha₁2 hsq₁ hsq.symm he2 het heI hetI k₁ hk₁ hk₁o hk₁a
  have hr₂ : e * k₂ * e⁻¹ = k₂⁻¹ :=
    f₂.reflect' hn₁ ha₂ ha₁ ha₂2 hsq₂ hsq he2 (by rw [← hc12]; exact het)
      (by rw [inf_comm]; exact heI) (by rw [inf_comm, ← hc12]; exact hetI) k₂ hk₂ hk₂o hk₂a
  have hwk₁ : w * k₁ * w⁻¹ = k₁ := by rw [hk₁act k₁ hk₁]; group
  have hwk₂ : w * k₂ * w⁻¹ = k₂ := by rw [hk₂act k₂ hk₂]; group
  have hk12 : k₁ * k₂ = k₂ * k₁ := p₁.comm k₁ hk₁ k₂ hk₂
  have hk12c : Commute k₁ k₂ := hk12
  have hwk₁' : w * k₁ = k₁ * w := mul_inv_eq_iff_eq_mul.1 hwk₁
  have hwk₂' : w * k₂ = k₂ * w := mul_inv_eq_iff_eq_mul.1 hwk₂
  have hw12 : w * (k₁ * k₂) = (k₁ * k₂) * w := by
    calc w * (k₁ * k₂) = (w * k₁) * k₂ := by group
      _ = (k₁ * w) * k₂ := by rw [hwk₁']
      _ = k₁ * (w * k₂) := by group
      _ = k₁ * (k₂ * w) := by rw [hwk₂']
      _ = (k₁ * k₂) * w := by group
  set u := (k₁ * k₂)⁻¹ * w with hu
  have hu1 : ∀ x ∈ L₁, u * x = x * u := by
    intro x hx
    have h1 := hk₁act x hx
    have h2 : Commute k₂ x := (p₁.comm x hx k₂ hk₂).symm
    have h2' : k₂⁻¹ * x = x * k₂⁻¹ := h2.inv_left.eq
    have h3 : w * x = k₁ * x * k₁⁻¹ * w := by
      calc w * x = (w * x * w⁻¹) * w := by group
        _ = k₁ * x * k₁⁻¹ * w := by rw [h1]
    calc (k₁ * k₂)⁻¹ * w * x = (k₁ * k₂)⁻¹ * (w * x) := by group
      _ = (k₁ * k₂)⁻¹ * (k₁ * x * k₁⁻¹ * w) := by rw [h3]
      _ = k₂⁻¹ * x * k₁⁻¹ * w := by group
      _ = x * k₂⁻¹ * k₁⁻¹ * w := by rw [h2']
      _ = x * ((k₁ * k₂)⁻¹ * w) := by group
  have hu2 : ∀ x ∈ L₂, u * x = x * u := by
    intro x hx
    have h1 := hk₂act x hx
    have h2 : Commute k₁ x := p₂.comm x hx k₁ hk₁ |>.symm
    have h2' : k₁⁻¹ * x = x * k₁⁻¹ := h2.inv_left.eq
    have h3 : w * x = k₂ * x * k₂⁻¹ * w := by
      calc w * x = (w * x * w⁻¹) * w := by group
        _ = k₂ * x * k₂⁻¹ * w := by rw [h1]
    calc (k₁ * k₂)⁻¹ * w * x = (k₁ * k₂)⁻¹ * (w * x) := by group
      _ = (k₁ * k₂)⁻¹ * (k₂ * x * k₂⁻¹ * w) := by rw [h3]
      _ = k₂⁻¹ * (k₁⁻¹ * k₂) * x * k₂⁻¹ * w := by group
      _ = k₂⁻¹ * (k₂ * k₁⁻¹) * x * k₂⁻¹ * w := by rw [hk12c.inv_left.eq]
      _ = k₁⁻¹ * x * k₂⁻¹ * w := by group
      _ = x * k₁⁻¹ * k₂⁻¹ * w := by rw [h2']
      _ = x * ((k₁⁻¹ * k₂⁻¹) * w) := by group
      _ = x * ((k₁ * k₂)⁻¹ * w) := by rw [mul_inv_rev, hk12c.inv_inv.eq]
  have hucen : u ∈ centralizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := p₁.exists_mul hx
    calc x₁ * x₂ * u = x₁ * (x₂ * u) := by group
      _ = x₁ * (u * x₂) := by rw [← hu2 x₂ hx₂]
      _ = (x₁ * u) * x₂ := by group
      _ = (u * x₁) * x₂ := by rw [← hu1 x₁ hx₁]
      _ = u * (x₁ * x₂) := by group
  have huF : u ∈ generalizedFitting Y :=
    CFSG.centralizer_generalizedFitting_le Y (Subgroup.centralizer_le hF hucen)
  have huLL : u ∈ L₁ ⊔ L₂ := hF huF
  have hu2L : u ∈ L₂ := p₁.mem_of_cen huLL (fun c hc => hu1 c hc)
  have hu1L : u ∈ L₁ := p₂.mem_of_cen (by rw [sup_comm]; exact huLL) (fun c hc => hu2 c hc)
  have hu2sq : u * u = 1 := p₁.sq_of_mem_inf ⟨hu1L, hu2L⟩
  have hwodd : Odd (orderOf w) := by
    have := Subgroup.orderOf_dvd_natCard Bb (hWB hwW)
    exact hBodd.of_dvd_nat this
  have huo : Odd (orderOf u) := by
    have h1 : Odd (orderOf (k₁ * k₂)⁻¹) := by
      rw [orderOf_inv]; exact odd_orderOf_mul_of_commute hk12c hk₁o hk₂o
    exact odd_orderOf_mul_of_commute (Commute.inv_left (show Commute (k₁ * k₂) w from hw12.symm)) h1 hwodd
  have hu_one : u = 1 := eq_one_of_mul_self_of_odd hu2sq huo
  have hwk : w = k₁ * k₂ := (inv_mul_eq_one.1 hu_one).symm
  have hew : e * w = w * e := hBe w (hWB hwW)
  have hww : w * w = 1 := by
    have h1 : e * w * e⁻¹ = w := by rw [hew]; group
    have h2 : e * (k₁ * k₂) * e⁻¹ = k₁⁻¹ * k₂⁻¹ := by
      calc e * (k₁ * k₂) * e⁻¹ = (e * k₁ * e⁻¹) * (e * k₂ * e⁻¹) := by group
        _ = k₁⁻¹ * k₂⁻¹ := by rw [hr₁, hr₂]
    rw [hwk] at h1
    rw [h2] at h1
    rw [hwk]
    calc (k₁ * k₂) * (k₁ * k₂) = (k₁ * k₂) * (k₁⁻¹ * k₂⁻¹) := by rw [h1]
      _ = k₁ * (k₂ * k₁⁻¹) * k₂⁻¹ := by group
      _ = k₁ * (k₁⁻¹ * k₂) * k₂⁻¹ := by rw [hk12c.inv_left.eq.symm]
      _ = 1 := by group
  exact hw1 (eq_one_of_mul_self_of_odd hww hwodd)

end Big

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
