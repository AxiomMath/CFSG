module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cConjE

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Core

variable {Y : Type} [Group Y] [Finite Y]

theorem comm_of_comm_eq_one {a b : Y} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

theorem comm_shift {e x s s' : Y} (hse : s * e = e * s) (hsx : s * x = x * s) (hss : s * s' = s' * s)
    (hs'e : s' * e = e * s') (hs'x : s' * x = x * s') :
    e * s * (x * s') * (e * s)⁻¹ * (x * s')⁻¹ = e * x * e⁻¹ * x⁻¹ := by
  have h1 : s' * e⁻¹ = e⁻¹ * s' := (show Commute s' e from hs'e).inv_right.eq
  have h2 : s * s' * s⁻¹ = s' := by rw [hss]; group
  calc e * s * (x * s') * (e * s)⁻¹ * (x * s')⁻¹
      = e * (s * x) * s' * s⁻¹ * e⁻¹ * s'⁻¹ * x⁻¹ := by group
    _ = e * (x * s) * s' * s⁻¹ * e⁻¹ * s'⁻¹ * x⁻¹ := by rw [hsx]
    _ = e * x * (s * s' * s⁻¹) * e⁻¹ * s'⁻¹ * x⁻¹ := by group
    _ = e * x * s' * e⁻¹ * s'⁻¹ * x⁻¹ := by rw [h2]
    _ = e * x * (s' * e⁻¹) * s'⁻¹ * x⁻¹ := by group
    _ = e * x * (e⁻¹ * s') * s'⁻¹ * x⁻¹ := by rw [h1]
    _ = e * x * e⁻¹ * x⁻¹ := by group

namespace TwinStr

variable {c t j a d : Y} {X E K₃ K₄ : Subgroup Y} {ρ : Y → AEQ 6} {α : Finset (Fin 6)} {h : α.card = 4}
  {b : Bool} (S : EStr c X E ρ) (T : TwinStr c t j a d X E K₃ K₄ ρ α h b)

include S T

theorem rho_comm_lab {g : Y} (hg : g ∈ Subgroup.centralizer ({c} : Set Y)) (h3 : ∀ k ∈ K₃, g * k = k * g)
    (h4 : ∀ k ∈ K₄, g * k = k * g) :
    (∀ k ∈ memBar α h b, k * ρ g = ρ g * k) ∧ (∀ k ∈ memBar α h (!b), k * ρ g = ρ g * k) := by
  constructor
  · intro k hk
    obtain ⟨k₃, hk₃, rfl⟩ := T.K₃_lab.2 k hk
    exact S.rho_comm (S.XC (T.K₃X k₃ hk₃)) hg (h3 k₃ hk₃).symm
  · intro k hk
    obtain ⟨k₄, hk₄, rfl⟩ := T.K₄_lab.2 k hk
    exact S.rho_comm (S.XC (T.K₄X k₄ hk₄)) hg (h4 k₄ hk₄).symm

theorem card_inf_le (F : AE6Fin) : 16 ≤ Nat.card ↥(E ⊓ conjE j E) := by
  classical
  obtain ⟨f, hfinj, hf⟩ := F.twin2 α h b
  have hex : ∀ i, ∃ e ∈ E ⊓ conjE j E, ρ e = f i := by
    intro i
    obtain ⟨hp, k, hk, k', hk', hfk⟩ := hf i
    obtain ⟨k₃, hk₃, hρ₃⟩ := T.K₃_lab.2 k hk
    obtain ⟨k₄, hk₄, hρ₄⟩ := T.K₄_lab.2 k' hk'
    have hX : k₃ * k₄ ∈ X := X.mul_mem (T.K₃X k₃ hk₃) (T.K₄X k₄ hk₄)
    have hρ : ρ (k₃ * k₄) = f i := by
      rw [S.rho_mul k₃ (S.XC (T.K₃X k₃ hk₃)) k₄ (S.XC (T.K₄X k₄ hk₄)), hρ₃, hρ₄, hfk]
    have hE : k₃ * k₄ ∈ E := (S.E_iff _).2 ⟨hX, by rw [hρ]; exact hp⟩
    have hEj : k₃ * k₄ ∈ conjE j E := by
      rw [mem_conjE]
      have hj : j⁻¹ * (k₃ * k₄) * j = k₃ * k₄ := by
        have e3 : j * k₃ = k₃ * j := T.j_K₃ k₃ hk₃
        have e4 : j * k₄ = k₄ * j := T.j_K₄ k₄ hk₄
        calc j⁻¹ * (k₃ * k₄) * j = j⁻¹ * (k₃ * (k₄ * j)) := by group
          _ = j⁻¹ * (k₃ * (j * k₄)) := by rw [e4]
          _ = j⁻¹ * (k₃ * j) * k₄ := by group
          _ = j⁻¹ * (j * k₃) * k₄ := by rw [e3]
          _ = k₃ * k₄ := by group
      rw [hj]
      exact hE
    exact ⟨k₃ * k₄, ⟨hE, hEj⟩, hρ⟩
  choose e he hρe using hex
  let F' : Fin 8 × Bool → ↥(E ⊓ conjE j E) := fun p =>
    if p.2 then ⟨c * e p.1, (E ⊓ conjE j E).mul_mem ⟨S.c_mem_E, c_mem_Ej S T⟩ (he p.1)⟩ else ⟨e p.1, he p.1⟩
  have hρF : ∀ p, ρ (F' p : Y) = f p.1 := by
    rintro ⟨i, s⟩
    cases s
    · simp [F', hρe]
    · have hcC : c ∈ Subgroup.centralizer ({c} : Set Y) := S.XC S.c_mem
      have heC : e i ∈ Subgroup.centralizer ({c} : Set Y) := S.E_le_C (he i).1
      simp only [F', if_true]
      rw [S.rho_mul c hcC (e i) heC, S.rho_c, one_mul, hρe]
  have hinj : Function.Injective F' := by
    rintro ⟨i, s⟩ ⟨i', s'⟩ hFF
    have h1 : f i = f i' := by
      have := congrArg (fun z : ↥(E ⊓ conjE j E) => ρ (z : Y)) hFF
      simpa [hρF] using this
    have hi : i = i' := hfinj h1
    subst hi
    have hss : s = s' := by
      by_contra hne
      have hcne : c * e i = e i → False := fun hh => S.hc1 (by simpa using hh)
      cases s <;> cases s'
      · exact hne rfl
      · have := congrArg Subtype.val hFF
        simp only [F', Bool.false_eq_true, if_false, if_true] at this
        exact hcne this.symm
      · have := congrArg Subtype.val hFF
        simp only [F', Bool.false_eq_true, if_false, if_true] at this
        exact hcne this
      · exact hne rfl
    rw [hss]
  have := Nat.card_le_card_of_injective F' hinj
  simpa using this

theorem exists_dd (F : AE6Fin) : ∃ dd : Y, dd ∈ Subgroup.centralizer ({c} : Set Y) ∧
    TC.Thin.permQ 6 (ρ dd) = 1 ∧ (∀ k ∈ K₃, dd * k = k * dd) ∧ (∀ k ∈ K₄, dd * k = k * dd) ∧
    ρ dd ≠ 1 ∧ ρ dd ≠ zBar α h ∧ (j⁻¹ * dd * j = dd ∨ j⁻¹ * dd * j = dd * t) := by
  have htC := S.E_le_C T.t_mem
  have hρa2 : ρ a * ρ a = zBar α h := by rw [← S.rho_mul a T.a_C a T.a_C, T.a_sq, T.rho_t]
  have hρd2 : ρ d * ρ d = 1 := by rw [← S.rho_mul d T.d_C d T.d_C, T.d_sq, S.rho_one]
  have hρda : ρ d * ρ a * (ρ d)⁻¹ = ρ a * zBar α h := by
    rw [← S.rho_conj T.d_C T.a_C, T.d_a, S.rho_mul a T.a_C t htC, T.rho_t]
  obtain ⟨ha1, ha2⟩ := rho_comm_lab S T T.a_C T.a_K₃ T.a_K₄
  obtain ⟨hd1, hd2⟩ := rho_comm_lab S T T.d_C T.d_K₃ T.d_K₄
  have key := F.twin3 α h b (ρ a) (ρ d) ha1 ha2 hd1 hd2 hρa2 hρd2 hρda
  have ht2 := tt S T
  have hai : a⁻¹ = a * t := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, T.a_sq, ht2])
  have had : a * d * a⁻¹ = d * t := by
    have hda : d * a = a * t * d := by
      calc d * a = (d * a * d⁻¹) * d := by group
        _ = a * t * d := by rw [T.d_a]
    calc a * d * a⁻¹ = a * d * (a * t) := by rw [hai]
      _ = a * (d * a) * t := by group
      _ = a * (a * t * d) * t := by rw [hda]
      _ = (a * a) * t * d * t := by group
      _ = t * t * d * t := by rw [T.a_sq]
      _ = d * t := by rw [ht2, one_mul]
  have hz1 : zBar α h ≠ 1 := zBar_ne_one (by norm_num) α h
  have hne : ∀ dd : Y, dd ∈ Subgroup.centralizer ({c} : Set Y) → a * dd * a⁻¹ = dd * t →
      ρ dd ≠ 1 ∧ ρ dd ≠ zBar α h := by
    intro dd hddC hadd
    have hr : ρ a * ρ dd * (ρ a)⁻¹ = ρ dd * zBar α h := by
      rw [← S.rho_conj T.a_C hddC, hadd, S.rho_mul dd hddC t htC, T.rho_t]
    constructor
    · intro h0
      rw [h0] at hr
      apply hz1
      simpa using hr.symm
    · intro h0
      rw [h0] at hr
      have hcomm : ρ a * zBar α h = zBar α h * ρ a := by
        rw [← T.rho_t]
        exact S.rho_comm T.a_C htC T.a_t
      have h5 : ρ a * zBar α h * (ρ a)⁻¹ = zBar α h := by rw [hcomm]; group
      rw [h5, zBar_mul_self] at hr
      exact hz1 hr
  rcases key with hk | hk
  · obtain ⟨hn1, hn2⟩ := hne d T.d_C had
    exact ⟨d, T.d_C, hk, T.d_K₃, T.d_K₄, hn1, hn2, Or.inl T.j_d⟩
  · have hdaC : d * a ∈ Subgroup.centralizer ({c} : Set Y) := Subgroup.mul_mem _ T.d_C T.a_C
    have hada : a * (d * a) * a⁻¹ = (d * a) * t := by
      calc a * (d * a) * a⁻¹ = (a * d * a⁻¹) * a := by group
        _ = d * t * a := by rw [had]
        _ = d * (t * a) := by group
        _ = d * (a * t) := by rw [T.a_t]
        _ = (d * a) * t := by group
    obtain ⟨hn1, hn2⟩ := hne (d * a) hdaC hada
    refine ⟨d * a, hdaC, ?_, ?_, ?_, hn1, hn2, Or.inr ?_⟩
    · rw [S.rho_mul d T.d_C a T.a_C]
      exact hk
    · intro k hk3
      calc d * a * k = d * (a * k) := by group
        _ = d * (k * a) := by rw [T.a_K₃ k hk3]
        _ = (d * k) * a := by group
        _ = (k * d) * a := by rw [T.d_K₃ k hk3]
        _ = k * (d * a) := by group
    · intro k hk4
      calc d * a * k = d * (a * k) := by group
        _ = d * (k * a) := by rw [T.a_K₄ k hk4]
        _ = (d * k) * a := by group
        _ = (k * d) * a := by rw [T.d_K₄ k hk4]
        _ = k * (d * a) := by group
    · calc j⁻¹ * (d * a) * j = (j⁻¹ * d * j) * (j⁻¹ * a * j) := by group
        _ = d * (a * t) := by rw [T.j_d, T.j_a]
        _ = d * a * t := by group

theorem pair_core (F : AE6Fin) : ∀ e ∈ E, ∀ e' ∈ E, e * (j * e' * j⁻¹) = (j * e' * j⁻¹) * e := by
  classical
  intro e he e' he'
  have hx : j * e' * j⁻¹ ∈ conjE j E := conj_mem_conjE he'
  have hEjc : Nat.card (conjE j E) = 32 := by rw [card_conjE, S.E_card]
  have hH16 := card_inf_le S T F
  have hdvd : Nat.card ↥(E ⊓ conjE j E) ∣ 32 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : E ⊓ conjE j E ≤ E)
    rwa [S.E_card] at this
  by_cases hEle : E ≤ conjE j E
  · exact Ej_abel S T (hEle he) hx
  obtain ⟨e₀, he₀, he₀'⟩ := SetLike.not_le_iff_exists.mp hEle
  have hcard : Nat.card ↥(E ⊓ conjE j E) = 16 := by
    have hmem : Nat.card ↥(E ⊓ conjE j E) ∈ Nat.divisors 32 :=
      Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · exact h
    · exfalso
      apply hEle
      have heq : E ⊓ conjE j E = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [S.E_card, h])
      calc E = E ⊓ conjE j E := heq.symm
        _ ≤ conjE j E := inf_le_right
  have hmE : ∀ x ∈ E, ∀ y ∈ E, x * y ∈ conjE j E ↔ (x ∈ conjE j E ↔ y ∈ conjE j E) :=
    fun x hx y hy => mul_mem_iff_of_card S.E_card (by rw [inf_comm]; exact hcard) hx hy
  have hmEj : ∀ x ∈ conjE j E, ∀ y ∈ conjE j E, x * y ∈ E ↔ (x ∈ E ↔ y ∈ E) :=
    fun x hx y hy => mul_mem_iff_of_card hEjc hcard hx hy
  have hnle : ¬ conjE j E ≤ E := by
    intro hle
    have heq : conjE j E = E := Subgroup.eq_of_le_of_card_ge hle (by rw [hEjc, S.E_card])
    exact hEle heq.ge
  obtain ⟨e₀', he₀'Ej, he₀'E⟩ := SetLike.not_le_iff_exists.mp hnle
  have hindep : ∀ e₁ ∈ E, e₁ ∉ conjE j E → ∀ x₁ ∈ conjE j E, x₁ ∉ E → ∀ f₁ ∈ E, f₁ ∉ conjE j E →
      ∀ y₁ ∈ conjE j E, y₁ ∉ E → e₁ * x₁ * e₁⁻¹ * x₁⁻¹ = f₁ * y₁ * f₁⁻¹ * y₁⁻¹ := by
    intro e₁ he₁ he₁' x₁ hx₁ hx₁' f₁ hf₁ hf₁' y₁ hy₁ hy₁'
    have hs : e₁⁻¹ * f₁ ∈ E ⊓ conjE j E := by
      refine ⟨E.mul_mem (E.inv_mem he₁) hf₁, ?_⟩
      refine (hmE _ (E.inv_mem he₁) _ hf₁).2 (iff_of_false (fun hh => he₁' ?_) hf₁')
      simpa using (conjE j E).inv_mem hh
    have hs' : x₁⁻¹ * y₁ ∈ E ⊓ conjE j E := by
      refine ⟨?_, (conjE j E).mul_mem ((conjE j E).inv_mem hx₁) hy₁⟩
      refine (hmEj _ ((conjE j E).inv_mem hx₁) _ hy₁).2 (iff_of_false (fun hh => hx₁' ?_) hy₁')
      simpa using E.inv_mem hh
    obtain ⟨s, hsdef⟩ : ∃ s, s = e₁⁻¹ * f₁ := ⟨_, rfl⟩
    obtain ⟨s', hs'def⟩ : ∃ s', s' = x₁⁻¹ * y₁ := ⟨_, rfl⟩
    rw [← hsdef] at hs
    rw [← hs'def] at hs'
    have hf' : f₁ = e₁ * s := by rw [hsdef]; group
    have hy' : y₁ = x₁ * s' := by rw [hs'def]; group
    rw [hf', hy']
    have hse : s * e₁ = e₁ * s := S.E_comm hs.1 he₁
    have hsx : s * x₁ = x₁ * s := Ej_abel S T hs.2 hx₁
    have hss : s * s' = s' * s := S.E_comm hs.1 hs'.1
    have hs'e : s' * e₁ = e₁ * s' := S.E_comm hs'.1 he₁
    have hs'x : s' * x₁ = x₁ * s' := Ej_abel S T hs'.2 hx₁
    exact (comm_shift hse hsx hss hs'e hs'x).symm
  obtain ⟨cm, hcmdef⟩ : ∃ cm, cm = e₀ * e₀' * e₀⁻¹ * e₀'⁻¹ := ⟨_, rfl⟩
  have hB1 : ∀ e₁ ∈ E, ∀ x₁ ∈ conjE j E,
      e₁ * x₁ * e₁⁻¹ * x₁⁻¹ = 1 ∨ e₁ * x₁ * e₁⁻¹ * x₁⁻¹ = cm := by
    intro e₁ he₁ x₁ hx₁
    by_cases h1 : e₁ ∈ conjE j E
    · left
      have := Ej_abel S T h1 hx₁
      rw [this]
      group
    by_cases h2 : x₁ ∈ E
    · left
      have := S.E_comm he₁ h2
      rw [this]
      group
    · right
      rw [hcmdef]
      exact hindep e₁ he₁ h1 x₁ hx₁ h2 e₀ he₀ he₀' e₀' he₀'Ej he₀'E
  have hcmEj : cm ∈ conjE j E := by
    rw [hcmdef]
    exact (conjE j E).mul_mem (E_conj_Ej S T he₀ he₀'Ej) ((conjE j E).inv_mem he₀'Ej)
  have hcmE : cm ∈ E := by
    rw [hcmdef]
    have h1 : e₀' * e₀⁻¹ * e₀'⁻¹ ∈ E := Ej_conj_E S T he₀'Ej (E.inv_mem he₀)
    have : e₀ * e₀' * e₀⁻¹ * e₀'⁻¹ = e₀ * (e₀' * e₀⁻¹ * e₀'⁻¹) := by group
    rw [this]
    exact E.mul_mem he₀ h1
  have hcmK : ∀ k : Y, (k ∈ K₃ ∨ k ∈ K₄) → k * cm = cm * k := by
    intro k hk
    have hkX : k ∈ X := hk.elim (T.K₃X k) (T.K₄X k)
    have hjk : j * k = k * j := hk.elim (T.j_K₃ k) (T.j_K₄ k)
    have hjk' : j * k⁻¹ = k⁻¹ * j := (show Commute j k from hjk).inv_right.eq
    have h1 : k * e₀ * k⁻¹ ∈ E := K_conj_E S T hkX he₀
    have h1' : k * e₀ * k⁻¹ ∉ conjE j E := by
      intro hh
      have := K_conj_Ej S T (X.inv_mem hkX) hjk' hh
      have e2 : k⁻¹ * (k * e₀ * k⁻¹) * k⁻¹⁻¹ = e₀ := by group
      rw [e2] at this
      exact he₀' this
    have h2 : k * e₀' * k⁻¹ ∈ conjE j E := K_conj_Ej S T hkX hjk he₀'Ej
    have h2' : k * e₀' * k⁻¹ ∉ E := by
      intro hh
      have := K_conj_E S T (X.inv_mem hkX) hh
      have e2 : k⁻¹ * (k * e₀' * k⁻¹) * k⁻¹⁻¹ = e₀' := by group
      rw [e2] at this
      exact he₀'E this
    have hh := hindep _ h1 h1' _ h2 h2' e₀ he₀ he₀' e₀' he₀'Ej he₀'E
    have e1 : k * cm * k⁻¹ = cm := by
      rw [hcmdef]
      calc k * (e₀ * e₀' * e₀⁻¹ * e₀'⁻¹) * k⁻¹
          = (k * e₀ * k⁻¹) * (k * e₀' * k⁻¹) * (k * e₀ * k⁻¹)⁻¹ * (k * e₀' * k⁻¹)⁻¹ := by group
        _ = e₀ * e₀' * e₀⁻¹ * e₀'⁻¹ := hh
    calc k * cm = k * cm * k⁻¹ * k := by group
      _ = cm * k := by rw [e1]
  have hρcm : ρ cm = 1 ∨ ρ cm = zBar α h := by
    have hU : InU (ρ cm) := S.rho_E hcmE
    have hcmC := S.E_le_C hcmE
    refine F.centU α h b (ρ cm) hU ?_ ?_
    · intro k hk
      obtain ⟨k₃, hk₃, rfl⟩ := T.K₃_lab.2 k hk
      exact S.rho_comm (S.XC (T.K₃X k₃ hk₃)) hcmC (hcmK k₃ (Or.inl hk₃))
    · intro k hk
      obtain ⟨k₄, hk₄, rfl⟩ := T.K₄_lab.2 k hk
      exact S.rho_comm (S.XC (T.K₄X k₄ hk₄)) hcmC (hcmK k₄ (Or.inr hk₄))
  have hcmcases : cm = 1 ∨ cm = c ∨ cm = t ∨ cm = t * c := by
    rcases hρcm with h0 | h0
    · rcases S.ker_E hcmE h0 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have htC := S.E_le_C T.t_mem
      have hz : ρ (t⁻¹ * cm) = 1 := by
        rw [S.rho_mul t⁻¹ (Subgroup.inv_mem _ htC) cm (S.E_le_C hcmE), S.rho_inv htC, T.rho_t, h0,
          inv_mul_cancel]
      rcases S.ker_E (E.mul_mem (E.inv_mem T.t_mem) hcmE) hz with h | h
      · right; right; left
        calc cm = t * (t⁻¹ * cm) := by group
          _ = t := by rw [h, mul_one]
      · right; right; right
        calc cm = t * (t⁻¹ * cm) := by group
          _ = t * c := by rw [h]
  have hgC : e₀' ∈ Subgroup.centralizer ({c} : Set Y) := Ej_C S T he₀'Ej
  rcases hcmcases with h1 | h2 | h34
  ·
    rcases hB1 e he _ hx with h | h
    · exact comm_of_comm_eq_one h
    · rw [h1] at h
      exact comm_of_comm_eq_one h
  ·
    exfalso
    have hcomU : ∀ x : AEQ 6, InU x → ρ e₀' * x = x * ρ e₀' := by
      intro x hxU
      obtain ⟨e₁, he₁, rfl⟩ := S.E_surj hxU
      have hr := S.rho_comm_el (S.E_le_C he₁) hgC
      have h0 : ρ (e₁ * e₀' * e₁⁻¹ * e₀'⁻¹) = 1 := by
        rcases hB1 e₁ he₁ e₀' he₀'Ej with h | h
        · rw [h, S.rho_one]
        · rw [h, h2, S.rho_c]
      rw [hr] at h0
      exact (comm_of_comm_eq_one h0).symm
    have hV := centV (ρ e₀') hcomU
    have hcent := S.cent_of_V F hgC hV
    have hcomm := hcent e₀ he₀
    apply S.hc1
    rw [← h2, hcmdef]
    calc e₀ * e₀' * e₀⁻¹ * e₀'⁻¹ = (e₀' * e₀) * e₀⁻¹ * e₀'⁻¹ := by rw [hcomm]
      _ = 1 := by group
  ·
    exfalso
    have hρz : ρ cm = zBar α h := by
      rcases h34 with h | h
      · rw [h, T.rho_t]
      · rw [h, S.rho_mul t (S.E_le_C T.t_mem) c (S.XC S.c_mem), S.rho_c, mul_one, T.rho_t]
    have hH1 : ∀ x : AEQ 6, InU x → x * ρ e₀' * x⁻¹ * (ρ e₀')⁻¹ = 1 ∨
        x * ρ e₀' * x⁻¹ * (ρ e₀')⁻¹ = zBar α h := by
      intro x hxU
      obtain ⟨e₁, he₁, rfl⟩ := S.E_surj hxU
      rw [← S.rho_comm_el (S.E_le_C he₁) hgC]
      rcases hB1 e₁ he₁ e₀' he₀'Ej with h | h
      · left
        rw [h, S.rho_one]
      · right
        rw [h, hρz]
    have hH2 : ∃ x : AEQ 6, InU x ∧ x * ρ e₀' * x⁻¹ * (ρ e₀')⁻¹ = zBar α h := by
      refine ⟨ρ e₀, S.rho_E he₀, ?_⟩
      rw [← S.rho_comm_el (S.E_le_C he₀) hgC, ← hcmdef, hρz]
    obtain ⟨dd, hddC, hddV, hdd3, hdd4, hdd1, hddz, hddj⟩ := exists_dd S T F
    have hddE := S.cent_of_V F hddC hddV
    have hddg : dd * e₀' = e₀' * dd := by
      have hm := mem_conjE.1 he₀'Ej
      have hcomm : (j⁻¹ * dd * j) * (j⁻¹ * e₀' * j) = (j⁻¹ * e₀' * j) * (j⁻¹ * dd * j) := by
        rcases hddj with h | h
        · rw [h]
          exact hddE _ hm
        · rw [h]
          have h1 := hddE _ hm
          have h2 := S.E_comm T.t_mem hm
          calc dd * t * (j⁻¹ * e₀' * j) = dd * (t * (j⁻¹ * e₀' * j)) := by group
            _ = dd * ((j⁻¹ * e₀' * j) * t) := by rw [h2]
            _ = (dd * (j⁻¹ * e₀' * j)) * t := by group
            _ = ((j⁻¹ * e₀' * j) * dd) * t := by rw [h1]
            _ = (j⁻¹ * e₀' * j) * (dd * t) := by group
      calc dd * e₀' = j * ((j⁻¹ * dd * j) * (j⁻¹ * e₀' * j)) * j⁻¹ := by group
        _ = j * ((j⁻¹ * e₀' * j) * (j⁻¹ * dd * j)) * j⁻¹ := by rw [hcomm]
        _ = e₀' * dd := by group
    have hρcomm : ρ dd * ρ e₀' = ρ e₀' * ρ dd := S.rho_comm hddC hgC hddg
    obtain ⟨hk1, hk2⟩ := rho_comm_lab S T hddC hdd3 hdd4
    apply F.twin4 α h b (ρ e₀') hH1 hH2 (ρ dd) hddV hk1 hk2 hdd1 hddz
    calc ρ e₀' * ρ dd * (ρ e₀')⁻¹ = ρ dd * ρ e₀' * (ρ e₀')⁻¹ := by rw [← hρcomm]
      _ = ρ dd := by group

end TwinStr

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
