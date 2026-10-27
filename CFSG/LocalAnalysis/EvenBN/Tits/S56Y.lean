module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.SixModel
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4CtSplit
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Five
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Ten

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

section NoCerts

variable {G : Type} [Group G]

theorem s56y_exists_eps {t : G} (htt : t * t = 1) {A₀ : Subgroup G}
    (hcov : ∀ x ∈ centralizer ({t} : Set G), x ∈ A₀ ∨ t * x ∈ A₀) :
    ∃ ε : ↥(centralizer ({t} : Set G)) →* ℤˣ,
      ∀ x : ↥(centralizer ({t} : Set G)), ε x = 1 ↔ (x : G) ∈ A₀ := by
  classical
  have hmul : ∀ x y : ↥(centralizer ({t} : Set G)), (x : G) ∉ A₀ → (y : G) ∉ A₀ →
      (x : G) * y ∈ A₀ := by
    intro x y hx hy
    have hx' := (hcov x x.2).resolve_left hx
    have hy' := (hcov y y.2).resolve_left hy
    have hxt : (x : G) * t = t * x := mem_centralizer_singleton_iff.1 x.2
    have e : t * (x : G) * (t * y) = x * y := by
      calc t * (x : G) * (t * y) = t * ((x : G) * t) * y := by group
        _ = t * (t * x) * y := by rw [hxt]
        _ = (t * t) * x * y := by group
        _ = x * y := by rw [htt, one_mul]
    rw [← e]
    exact mul_mem hx' hy'
  refine ⟨{ toFun := fun x => if (x : G) ∈ A₀ then 1 else -1
            map_one' := by simp
            map_mul' := fun x y => ?_ }, fun x => ?_⟩
  · by_cases hx : (x : G) ∈ A₀ <;> by_cases hy : (y : G) ∈ A₀
    · have hxy : (x : G) * y ∈ A₀ := mul_mem hx hy
      simp [hx, hy, hxy]
    · have hxy : (x : G) * y ∉ A₀ := fun h => hy (by simpa using mul_mem (inv_mem hx) h)
      simp [hx, hy, hxy]
    · have hxy : (x : G) * y ∉ A₀ := fun h => hx (by simpa using mul_mem h (inv_mem hy))
      simp [hx, hy, hxy]
    · have hxy : (x : G) * y ∈ A₀ := hmul x y hx hy
      simp [hx, hy, hxy]
  · by_cases hx : (x : G) ∈ A₀ <;> simp [hx]

theorem s56y_mem_sup_zpowers {A : Subgroup G} {y : G} (hy : ∀ a ∈ A, y * a = a * y)
    (hy2 : y * y ∈ A) {c : G} (hc : c ∈ A ⊔ zpowers y) : c ∈ A ∨ ∃ a ∈ A, c = y * a := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ A ∨ ∃ a ∈ A, x = y * a}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        rintro x w (hx | ⟨a, ha, rfl⟩) (hw | ⟨b, hb, rfl⟩)
        · exact Or.inl (mul_mem hx hw)
        · refine Or.inr ⟨x * b, mul_mem hx hb, ?_⟩
          calc x * (y * b) = (x * y) * b := by group
            _ = (y * x) * b := by rw [hy x hx]
            _ = y * (x * b) := by group
        · exact Or.inr ⟨a * w, mul_mem ha hw, by group⟩
        · refine Or.inl ?_
          have e : y * a * (y * b) = (y * y) * (a * b) := by
            calc y * a * (y * b) = y * (a * y) * b := by group
              _ = y * (y * a) * b := by rw [hy a ha]
              _ = (y * y) * (a * b) := by group
          rw [e]
          exact mul_mem hy2 (mul_mem ha hb)
      inv_mem' := by
        rintro x (hx | ⟨a, ha, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨a⁻¹ * (y * y)⁻¹, mul_mem (inv_mem ha) (inv_mem hy2), ?_⟩
          have hb : y * (a⁻¹ * (y * y)⁻¹) = (a⁻¹ * (y * y)⁻¹) * y :=
            hy _ (mul_mem (inv_mem ha) (inv_mem hy2))
          calc (y * a)⁻¹ = a⁻¹ * y⁻¹ := by group
            _ = a⁻¹ * (y * y)⁻¹ * y := by group
            _ = y * (a⁻¹ * (y * y)⁻¹) := hb.symm }
  have hle : A ⊔ zpowers y ≤ S := by
    apply sup_le
    · intro a ha
      exact Or.inl ha
    · rw [zpowers_le]
      exact Or.inr ⟨1, one_mem _, by simp⟩
  exact hle hc

end NoCerts

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56y_eps_L (hd : d.Hyp) (ε : ↥(centralizer ({d.t} : Set G)) →* ℤˣ) {l : G}
    (hl : l ∈ d.L) : ε ⟨l, hd.L_le hl⟩ = 1 := by
  have hs : IsSimpleGroup titsD := titsD_simple
  let ψ : titsD →* ℤˣ := (ε.comp (Subgroup.inclusion hd.L_le)).comp d.θ.symm.toMonoidHom
  have hψ : ψ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exfalso
      have hle := Nat.card_le_card_of_injective ψ ((MonoidHom.ker_eq_bot_iff ψ).1 h)
      rw [card_titsD, Nat.card_eq_fintype_card, Fintype.card_units_int] at hle
      omega
    · exact h
  have h1 : ψ (d.θ ⟨l, hl⟩) = 1 := MonoidHom.mem_ker.1 (hψ ▸ mem_top _)
  have h2 : ψ (d.θ ⟨l, hl⟩) = ε ⟨l, hd.L_le hl⟩ := by
    show ε (Subgroup.inclusion hd.L_le (d.θ.symm (d.θ ⟨l, hl⟩))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  exact h2.symm.trans h1

theorem Hyp.s56_L_le_A0 (hd : d.Hyp) {A₀ : Subgroup G} (htA : d.t ∉ A₀)
    (hcov : ∀ x ∈ centralizer ({d.t} : Set G), x ∈ A₀ ∨ d.t * x ∈ A₀) : d.L ≤ A₀ := by
  obtain ⟨ε, hε⟩ := s56y_exists_eps hd.t_mul_self hcov
  intro l hl
  exact (hε ⟨l, hd.L_le hl⟩).1 (hd.s56y_eps_L ε hl)

theorem Hyp.s56y_ρ_inj (hd : d.Hyp) {A₀ : Subgroup G} (htA : d.t ∉ A₀) {a b : G}
    (ha : a ∈ centralizer ({d.t} : Set G)) (hb : b ∈ centralizer ({d.t} : Set G))
    (haA : a ∈ A₀) (hbA : b ∈ A₀)
    (h : (d.ρ ⟨a, ha⟩ : Equiv.Perm (Fin 1755)) = (d.ρ ⟨b, hb⟩ : Equiv.Perm (Fin 1755))) :
    a = b := by
  have hab : a⁻¹ * b ∈ centralizer ({d.t} : Set G) := mul_mem (inv_mem ha) hb
  have h1 : d.ρ ⟨a⁻¹ * b, hab⟩ = 1 := by
    have e : (⟨a⁻¹ * b, hab⟩ : centralizer ({d.t} : Set G)) = (⟨a, ha⟩)⁻¹ * ⟨b, hb⟩ := rfl
    have h' : d.ρ ⟨a, ha⟩ = d.ρ ⟨b, hb⟩ := Subtype.ext h
    rw [e, map_mul, map_inv, h', inv_mul_cancel]
  have hk : a⁻¹ * b ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) :=
    mem_inf.2 ⟨(hd.ρ_eq_one_iff _).1 h1, hab⟩
  rw [Model.kernel_eq_zpowers_of_hyp hd, Model.mem_zpowers_of_orderOf_two hd.t_two] at hk
  rcases hk with hk | hk
  · exact inv_mul_eq_one.1 hk
  · exfalso
    apply htA
    rw [← hk]
    exact mul_mem (inv_mem haA) hbA

theorem Hyp.s56y_ρ_mem_titsD_of_mem_A (hd : d.Hyp) {a : G} (ha : a ∈ d.A)
    (haC : a ∈ centralizer ({d.t} : Set G)) :
    (d.ρ ⟨a, haC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
  rcases ((hd.tSup_facts (s56_E_le_L d)).1 a).1 ha with h | h
  · rw [hd.ρ_eq_θ ⟨a, s56_E_le_L d h⟩]
    exact (d.θ _).2
  · have htaC : d.t * a ∈ centralizer ({d.t} : Set G) := mul_mem d.t_mem_centralizer haC
    have e : (⟨a, haC⟩ : centralizer ({d.t} : Set G)) =
        ⟨d.t, d.t_mem_centralizer⟩ * ⟨d.t * a, htaC⟩ :=
      Subtype.ext (by
        show a = d.t * (d.t * a)
        rw [← mul_assoc, hd.t_mul_self, one_mul])
    rw [e, map_mul, hd.ρ_t, one_mul, hd.ρ_eq_θ ⟨d.t * a, s56_E_le_L d h⟩]
    exact (d.θ _).2

theorem Hyp.s56_exists_y (hd : d.Hyp) (hR : d.ρ.range = ⊤) :
    ∃ (y : G) (hy : y ∈ centralizer ({d.t} : Set G)),
      (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 5 ∧ y * y = d.z := by
  obtain ⟨A₀, -, htA, hcov⟩ := hd.exists_compl_zpowers_t
  have hLA : d.L ≤ A₀ := hd.s56_L_le_A0 htA hcov
  have h5 : Model.parrottV 5 ∈ titsA :=
    Model.twoF4H_le_titsA (Model.twoF4S_le_twoF4H Model.parrottV_five.1)
  have hmem : (⟨Model.parrottV 5, h5⟩ : titsA) ∈ d.ρ.range := hR ▸ mem_top _
  obtain ⟨y₀, hy₀⟩ := hmem
  have hy₀ρ : (d.ρ y₀ : Equiv.Perm (Fin 1755)) = Model.parrottV 5 := congrArg Subtype.val hy₀
  obtain ⟨y, hyC, hyA, hyρ⟩ : ∃ y : G, ∃ hy : y ∈ centralizer ({d.t} : Set G), y ∈ A₀ ∧
      (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 5 := by
    rcases hcov y₀ y₀.2 with h | h
    · exact ⟨y₀, y₀.2, h, hy₀ρ⟩
    · refine ⟨d.t * y₀, mul_mem d.t_mem_centralizer y₀.2, h, ?_⟩
      have e : (⟨d.t * (y₀ : G), mul_mem d.t_mem_centralizer y₀.2⟩ :
          centralizer ({d.t} : Set G)) = ⟨d.t, d.t_mem_centralizer⟩ * y₀ := rfl
      rw [e, map_mul, hd.ρ_t, one_mul, hy₀ρ]
  refine ⟨y, hyC, hyρ, ?_⟩
  have hyyC : y * y ∈ centralizer ({d.t} : Set G) := mul_mem hyC hyC
  have hzC : d.z ∈ centralizer ({d.t} : Set G) := hd.L_le d.z_mem
  refine hd.s56y_ρ_inj htA hyyC hzC (mul_mem hyA hyA) (hLA d.z_mem) ?_
  have e : (⟨y * y, hyyC⟩ : centralizer ({d.t} : Set G)) = ⟨y, hyC⟩ * ⟨y, hyC⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul, hyρ, Model.parrottV_five.2.2,
    hd.ρ_eq_θ ⟨d.z, d.z_mem⟩, d.θ_z]

theorem Hyp.s56y_C_structure (hd : d.Hyp) :
    centralizer (d.A : Set G) = d.A ∨
    ∃ (y : G) (hy : y ∈ centralizer ({d.t} : Set G)),
      (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 5 ∧ y * y = d.z ∧
      centralizer (d.A : Set G) = d.A ⊔ zpowers y ∧ (∀ a ∈ d.A, y * a = a * y) ∧ y ∉ d.A ∧
      y * d.pv 7 * y⁻¹ = d.pv 7 * d.pv 11 ∧
      (∀ c ∈ centralizer (d.A : Set G), c ∈ d.A ∨ ∃ a ∈ d.A, c = y * a) := by
  rcases hd.centralizer_A with ⟨-, hC⟩ | ⟨hR, hC⟩
  · exact Or.inl hC
  · right
    obtain ⟨y, hyC, hyρ, hyy⟩ := hd.s56_exists_y hR
    have hCy := hC y hyC hyρ
    have hycent : y ∈ centralizer (d.A : Set G) := by
      rw [hCy]
      exact mem_sup_right (mem_zpowers _)
    have hycomm : ∀ a ∈ d.A, y * a = a * y := fun a ha =>
      (mem_centralizer_iff.1 hycent a ha).symm
    refine ⟨y, hyC, hyρ, hyy, hCy, hycomm, ?_, ?_, ?_⟩
    · intro hyA
      have h := hd.s56y_ρ_mem_titsD_of_mem_A hyA hyC
      rw [hyρ] at h
      exact Model.parrottV_five.2.1 h
    · have hv7F : Model.parrottV 7 ∈ Model.parrottF := Model.parrottV_mem_parrottF (by simp)
      have hv7D : Model.parrottV 7 ∈ titsD := Model.parrottF_le_titsD hv7F
      have hv11D : Model.parrottV 11 ∈ titsD :=
        Model.parrottF_le_titsD Model.parrottV_eleven_mem_parrottF
      have hrel : (d.ρ ⟨y, hyC⟩ : Equiv.Perm (Fin 1755)) * Model.parrottV 7 =
          (Model.parrottV 7 * Model.parrottV 11) * d.ρ ⟨y, hyC⟩ := by
        rw [hyρ]
        calc Model.parrottV 5 * Model.parrottV 7
            = (Model.parrottV 5 * Model.parrottV 7 * (Model.parrottV 5)⁻¹) * Model.parrottV 5 := by
              group
          _ = (Model.parrottV 7 * Model.parrottV 11) * Model.parrottV 5 := by
              rw [Model.parrottV_five_conj_seven]
      have h := hd.conj_lift_eq hyC hv7D (mul_mem hv7D hv11D) hrel
      rw [d.lift_mul hv7D hv11D] at h
      exact h
    · intro c hc
      rw [hCy] at hc
      exact s56y_mem_sup_zpowers hycomm
        (hyy ▸ s56_E_le_A d hd.s56_z_mem_E) hc

theorem Hyp.s56_C_inf_L (hd : d.Hyp) {c : G} (hc : c ∈ centralizer (d.A : Set G))
    (hcL : c ∈ d.L) : c ∈ d.E := by
  have hAL : ∀ x, x ∈ d.A → x ∈ d.L → x ∈ d.E := hd.A_facts.2.2.2.2
  rcases hd.s56y_C_structure with h | ⟨y, hyC, hyρ, -, -, -, -, -, hcov⟩
  · rw [h] at hc
    exact hAL c hc hcL
  · rcases hcov c hc with h | ⟨a, haA, rfl⟩
    · exact hAL c h hcL
    · exfalso
      have haC : a ∈ centralizer ({d.t} : Set G) := hd.A_facts.2.1 haA
      have hρa : (d.ρ ⟨a, haC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD :=
        hd.s56y_ρ_mem_titsD_of_mem_A haA haC
      have hcC : y * a ∈ centralizer ({d.t} : Set G) := mul_mem hyC haC
      have hρc : (d.ρ ⟨y * a, hcC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
        rw [hd.ρ_eq_θ ⟨y * a, hcL⟩]
        exact (d.θ _).2
      have e : (⟨y * a, hcC⟩ : centralizer ({d.t} : Set G)) = ⟨y, hyC⟩ * ⟨a, haC⟩ := rfl
      rw [e, map_mul, Subgroup.coe_mul, hyρ] at hρc
      have h5 : Model.parrottV 5 ∈ titsA :=
        Model.twoF4H_le_titsA (Model.twoF4S_le_twoF4H Model.parrottV_five.1)
      exact Model.parrottV_five.2.1
        (((Model.mul_mem_titsD_iff h5 (d.ρ ⟨a, haC⟩).2).1 hρc).2 hρa)

section X5


theorem Hyp.s56_C_cases (hd : d.Hyp) :
    centralizer (d.A : Set G) = d.A ∨
    ∃ y : G, y * y = d.z ∧ centralizer (d.A : Set G) = d.A ⊔ zpowers y ∧
      (∀ a ∈ d.A, y * a = a * y) ∧ y * d.x₅ = d.x₅ * y ∧ y ∉ d.A ∧
      y * d.pv 7 * y⁻¹ = d.pv 7 * d.pv 11 ∧
      (∀ c ∈ centralizer (d.A : Set G), c ∈ d.A ∨ ∃ a ∈ d.A, c = y * a) ∧
      y ∈ centralizer ({d.t} : Set G) := by
  rcases hd.s56y_C_structure with h | ⟨y, hyC, hyρ, hyy, hCy, hycomm, hyA, hconj, hcov⟩
  · exact Or.inl h
  · refine Or.inr ⟨y, hyy, hCy, hycomm, ?_, hyA, hconj, hcov, hyC⟩
    have hXD : Model.hatX ∈ titsD := titsH_le_titsD Model.hatX_facts.1
    refine (hd.commute_lift_iff hyC hXD).2 ?_
    rw [hyρ]
    exact Model.hatX_facts.2.2.2.1

end X5

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
