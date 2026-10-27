module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GH74.M12.HypGroup
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Abstract

variable {Γ : Type*} [Group Γ]

structure BarCfg (R : Subgroup Γ) [R.Normal] (z : Γ) : Prop where
  pgroup : IsPGroup 2 ↥R
  card : Nat.card ↥R = 32
  quot : Nonempty (Γ ⧸ R ≃* Equiv.Perm (Fin 3))
  z_mem : z ∈ R
  z_sq : z * z = 1
  z_central : ∀ g : Γ, g * z = z * g
  z_comm : ∃ r₁ ∈ R, ∃ r₂ ∈ R, ⁅r₁, r₂⁆ = z
  cent_X : ∀ X : Sylow 3 Γ, ∀ r ∈ R, (∀ w ∈ X, w * r = r * w) → r ∈ zpowers z

variable {R : Subgroup Γ} [R.Normal] {z : Γ}

@[expose] noncomputable def BarCfg.phi (c : BarCfg R z) : Γ →* Equiv.Perm (Fin 3) :=
  c.quot.some.toMonoidHom.comp (QuotientGroup.mk' R)

theorem BarCfg.phi_surj (c : BarCfg R z) : Function.Surjective c.phi :=
  c.quot.some.surjective.comp (QuotientGroup.mk'_surjective R)

theorem BarCfg.phi_eq_one (c : BarCfg R z) {g : Γ} : c.phi g = 1 ↔ g ∈ R := by
  have : c.phi g = c.quot.some (QuotientGroup.mk' R g) := rfl
  rw [this, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem BarCfg.card_Γ (c : BarCfg R z) : Nat.card Γ = 192 := by
  have h1 := Subgroup.card_mul_index R
  have h2 : R.index = 6 := by
    rw [Subgroup.index_eq_card, Nat.card_congr c.quot.some.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [← h1, c.card, h2]

theorem BarCfg.sylow3_card [Finite Γ] (c : BarCfg R z) (X : Sylow 3 Γ) : Nat.card X = 3 := by
  rw [Sylow.card_eq_multiplicity, c.card_Γ]
  have : (Nat.factorization 192) 3 = 1 := by decide +kernel
  rw [this]; norm_num

theorem BarCfg.isSolvable [Finite Γ] (c : BarCfg R z) : Group.IsSolvable Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥R := c.pgroup.isNilpotent
  have : Group.IsSolvable ↥R := inferInstance
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have : Group.IsSolvable (Γ ⧸ R) :=
    Group.isSolvable_of_isSolvable_injective (f := c.quot.some.toMonoidHom) c.quot.some.injective
  exact Group.isSolvable_of_subgroup_quotient R

theorem BarCfg.pCore_eq [Finite Γ] (c : BarCfg R z) : pCore 2 Γ = R := by
  apply le_antisymm
  · intro q hq
    have hQn : (pCore 2 Γ).Normal := pCore_normal
    have hQ2 : IsPGroup 2 ↥(pCore 2 Γ) := pCore_isPGroup
    have hmapn : ((pCore 2 Γ).map c.phi).Normal := Subgroup.Normal.map hQn c.phi c.phi_surj
    have hbot := CFSG.GH74.M12.Hyp.eq_bot_of_normal_isPGroup_perm_three
      ((pCore 2 Γ).map c.phi) (hQ2.map c.phi)
    have hmem : c.phi q ∈ (pCore 2 Γ).map c.phi := ⟨q, hq, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact c.phi_eq_one.1 hmem
  · exact le_sSup ⟨inferInstance, c.pgroup⟩

theorem BarCfg.fitting_eq [Finite Γ] (c : BarCfg R z) (h : pPrimeCore 2 Γ = ⊥) :
    fittingSubgroup Γ = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Fitting_eq_pcore Γ 2 h, c.pCore_eq]

theorem layer_eq_bot_of_isSolvable' {G : Type*} [Group G] [Group.IsSolvable G] : layer G = ⊥ :=
  CFSG.WholeGroup.layer_eq_bot_of_isSolvable

theorem BarCfg.generalizedFitting_eq [Finite Γ] (c : BarCfg R z) (h : pPrimeCore 2 Γ = ⊥) :
    generalizedFitting Γ = R := by
  have := c.isSolvable
  rw [generalizedFitting, layer_eq_bot_of_isSolvable', sup_bot_eq, c.fitting_eq h]


theorem BarCfg.commutator_eq [Finite Γ] (c : BarCfg R z) (X : Sylow 3 Γ) :
    ⁅R, (X : Subgroup Γ)⁆ = R := by
  have hXc := c.sylow3_card X
  obtain ⟨x₀, hx₀X, hXgen, hx₀3⟩ := exists_gen_card_three hXc
  set Q := ⁅R, (X : Subgroup Γ)⁆ with hQ
  have hQR : Q ≤ R := by
    rw [hQ, Subgroup.commutator_le]
    intro r hr x hx
    have h1 : x * r⁻¹ * x⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem _ (R.inv_mem hr) x
    have : ⁅r, x⁆ = r * (x * r⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact R.mul_mem hr h1
  have hQX : ∀ y ∈ (X : Subgroup Γ), ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
    intro y hy q hq
    have hq' : q ∈ Subgroup.closure {g | ∃ g₁ ∈ R, ∃ g₂ ∈ (X : Subgroup Γ), ⁅g₁, g₂⁆ = g} := by
      rwa [hQ, Subgroup.commutator_def] at hq
    clear hq
    induction hq' using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((inferInstance : R.Normal).conj_mem a ha y)
        (mul_mem (mul_mem hy hb) (inv_mem hy))
    | one => simp
    | mul g h _ _ ihg ihh =>
      have : y * (g * h) * y⁻¹ = (y * g * y⁻¹) * (y * h * y⁻¹) := by group
      rw [this]; exact Q.mul_mem ihg ihh
    | inv g _ ih =>
      have : y * g⁻¹ * y⁻¹ = (y * g * y⁻¹)⁻¹ := by group
      rw [this]; exact Q.inv_mem ih
  have h3Q : ¬ 3 ∣ Nat.card Q := by
    intro h
    have h1 : Nat.card Q ∣ Nat.card R := Subgroup.card_dvd_of_le hQR
    rw [c.card] at h1
    have : 3 ∣ 32 := h.trans h1
    omega
  have hcommR : ∀ r ∈ R, ∃ e : ℤ, ∃ q ∈ Q, r = z ^ e * q := by
    intro r hr
    have hc' : r⁻¹ * x₀ * r * x₀⁻¹ ∈ Q := by
      have h1 : ⁅r⁻¹, x₀⁆ ∈ Q := Subgroup.commutator_mem_commutator (R.inv_mem hr) hx₀X
      simpa [commutatorElement_def] using h1
    obtain ⟨q, hq, hfix⟩ := exists_fixed_coset Q x₀ r hx₀3
      (fun q hq => hQX x₀ hx₀X q hq) hc' h3Q
    have hrq : r * q ∈ R := R.mul_mem hr (hQR hq)
    have hcomm : ∀ w ∈ (X : Subgroup Γ), w * (r * q) = (r * q) * w := by
      intro w hw
      rw [hXgen] at hw
      obtain ⟨n, rfl⟩ := hw
      exact (Commute.zpow_left (show Commute x₀ (r * q) from hfix) n).eq
    obtain ⟨e, he⟩ := c.cent_X X (r * q) hrq hcomm
    refine ⟨e, q⁻¹, Q.inv_mem hq, ?_⟩
    have : r = z ^ e * q⁻¹ := by
      have h2 : z ^ e = r * q := he
      rw [h2]; group
    exact this
  have hzQ : z ∈ Q := by
    obtain ⟨r₁, hr₁, r₂, hr₂, hz⟩ := c.z_comm
    obtain ⟨e₁, q₁, hq₁, rfl⟩ := hcommR r₁ hr₁
    obtain ⟨e₂, q₂, hq₂, rfl⟩ := hcommR r₂ hr₂
    have hzc : ∀ (e : ℤ) (g : Γ), z ^ e * g = g * z ^ e := fun e g =>
      (Commute.zpow_left (show Commute z g from (c.z_central g).symm) e).eq
    rw [commutator_central_mul (hzc e₁) (hzc e₂)] at hz
    rw [← hz]
    simp only [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hq₁ hq₂) (Q.inv_mem hq₁)) (Q.inv_mem hq₂)
  apply le_antisymm hQR
  intro r hr
  obtain ⟨e, q, hq, rfl⟩ := hcommR r hr
  exact Q.mul_mem (Q.zpow_mem hzQ e) hq

theorem BarCfg.index_sup [Finite Γ] (c : BarCfg R z) (X : Sylow 3 Γ) :
    (R ⊔ (X : Subgroup Γ)).index = 2 := by
  set Y := R ⊔ (X : Subgroup Γ) with hY
  have hXc := c.sylow3_card X
  have h96 : 96 ∣ Nat.card Y := by
    have h1 : Nat.card R ∣ Nat.card Y := Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card (X : Subgroup Γ) ∣ Nat.card Y := Subgroup.card_dvd_of_le le_sup_right
    rw [c.card] at h1
    rw [hXc] at h2
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 32 3) h1 h2
    simpa using this
  have hmul : Nat.card Y * Y.index = 192 := by
    rw [← c.card_Γ]; exact Subgroup.card_mul_index Y
  obtain ⟨k, hk⟩ := h96
  have hk2 : k * Y.index = 2 := by
    rw [hk] at hmul
    nlinarith
  have hkcases : k = 1 ∨ k = 2 := by
    have : k ∣ 2 := Dvd.intro _ hk2
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hkcases with h | h
  · subst h; omega
  · exfalso
    subst h
    have hY1 : Y.index = 1 := by omega
    have hYtop : Y = ⊤ := Subgroup.index_eq_one.1 hY1
    have hmap : Y.map c.phi = (X : Subgroup Γ).map c.phi := by
      rw [hY, Subgroup.map_sup]
      have : R.map c.phi = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨r, hr, rfl⟩
        exact (Subgroup.mem_bot).2 (c.phi_eq_one.2 hr)
      rw [this, bot_sup_eq]
    have htop : (X : Subgroup Γ).map c.phi = ⊤ := by
      rw [← hmap, hYtop, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact c.phi_surj
    have hdvd : Nat.card ((X : Subgroup Γ).map c.phi) ∣ Nat.card X :=
      Subgroup.card_map_dvd (H := (X : Subgroup Γ)) c.phi
    rw [htop, Subgroup.card_top, hXc] at hdvd
    have : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [this] at hdvd
    omega

theorem BarCfg.oResidual_eq [Finite Γ] (c : BarCfg R z) (X : Sylow 3 Γ) :
    oResidual 2 Γ = R ⊔ (X : Subgroup Γ) := by
  have hXc := c.sylow3_card X
  have hidx := c.index_sup X
  have : (R ⊔ (X : Subgroup Γ)).Normal := Subgroup.normal_of_index_eq_two hidx
  have : (oResidual 2 Γ).Normal := oResidual_normal 2 Γ
  apply le_antisymm
  · apply oResidual_le_of_isPGroup_quotient
    apply IsPGroup.of_card (n := 1)
    rw [pow_one, ← Subgroup.index_eq_card]
    exact hidx
  · apply sup_le
    · rw [← c.commutator_eq X]
      rw [Subgroup.commutator_le]
      intro r hr x hx
      have hxO : x ∈ oResidual 2 Γ := by
        apply Subgroup.subset_closure
        show Nat.Coprime (orderOf x) 2
        have : orderOf x ∣ 3 := by
          have := Subgroup.orderOf_dvd_natCard (X : Subgroup Γ) hx
          rwa [hXc] at this
        exact Nat.Coprime.coprime_dvd_left this (by norm_num)
      have e : ⁅r, x⁆ = (r * x * r⁻¹) * x⁻¹ := by simp [commutatorElement_def]
      rw [e]
      exact Subgroup.mul_mem _ ((inferInstance : (oResidual 2 Γ).Normal).conj_mem x hxO r)
        (Subgroup.inv_mem _ hxO)
    · intro x hx
      apply Subgroup.subset_closure
      show Nat.Coprime (orderOf x) 2
      have : orderOf x ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard (X : Subgroup Γ) hx
        rwa [hXc] at this
      exact Nat.Coprime.coprime_dvd_left this (by norm_num)

theorem BarCfg.mem_R_of_pElt [Finite Γ] (c : BarCfg R z) (X : Sylow 3 Γ) {g : Γ}
    (hg : g ∈ R ⊔ (X : Subgroup Γ)) {k : ℕ} (hk : g ^ (2 ^ k) = 1) : g ∈ R := by
  have hXc := c.sylow3_card X
  have hmem : c.phi g ∈ (X : Subgroup Γ).map c.phi := by
    have : c.phi g ∈ (R ⊔ (X : Subgroup Γ)).map c.phi := ⟨g, hg, rfl⟩
    rw [Subgroup.map_sup] at this
    have hR : R.map c.phi = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.mem_bot).2 (c.phi_eq_one.2 hr)
    rwa [hR, bot_sup_eq] at this
  have h3 : orderOf (c.phi g) ∣ 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard ((X : Subgroup Γ).map c.phi) hmem
    have h2 := Subgroup.card_map_dvd (H := (X : Subgroup Γ)) c.phi
    rw [hXc] at h2
    exact (h1.trans h2)
  have h2k : orderOf (c.phi g) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hk, map_one]
  have h1 : orderOf (c.phi g) = 1 := by
    have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.eq_one_of_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd h3 h2k)
  exact c.phi_eq_one.1 (orderOf_eq_one_iff.1 h1)

theorem BarCfg.pCore_oResidual [Finite Γ] (c : BarCfg R z) (X : Sylow 3 Γ) :
    (pCore 2 ↥(oResidual 2 Γ)).map (oResidual 2 Γ).subtype = R := by
  have hO := c.oResidual_eq X
  have hRle : R ≤ oResidual 2 Γ := by rw [hO]; exact le_sup_left
  apply le_antisymm
  · rintro p ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥(oResidual 2 Γ))) ⟨y, hy⟩
    have hyk : (y : Γ) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val (congrArg Subtype.val hk)
      simpa using this
    exact c.mem_R_of_pElt X (hO ▸ y.2) hyk
  · intro r hr
    have hsub : R.subgroupOf (oResidual 2 Γ) ≤ pCore 2 ↥(oResidual 2 Γ) := by
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      exact c.pgroup.comap_subtype (K := oResidual 2 Γ)
    refine ⟨⟨r, hRle hr⟩, hsub ?_, rfl⟩
    exact hr

theorem BarCfg.oPrimeResidual_eq_top [Finite Γ] (c : BarCfg R z) : oPrimeResidual 2 Γ = ⊤ := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hTn : (oPrimeResidual 2 Γ).Normal := oPrimeResidual_normal 2 Γ
  have hRT : R ≤ oPrimeResidual 2 Γ := by
    intro r hr
    apply Subgroup.subset_closure
    obtain ⟨k, hk⟩ := c.pgroup ⟨r, hr⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨x₀, hx₀⟩ := c.phi_surj (Equiv.swap (0 : Fin 3) 1)
  have hsq : c.phi x₀ ^ (2 ^ 1) = 1 := by
    rw [hx₀]; decide
  obtain ⟨x, i, hxi, hx⟩ := exists_lift_pElement c.phi hp x₀ hsq
  have hxT : x ∈ oPrimeResidual 2 Γ := Subgroup.subset_closure ⟨i, hxi⟩
  have hφT : ((oPrimeResidual 2 Γ).map c.phi) = ⊤ := by
    have : ((oPrimeResidual 2 Γ).map c.phi).Normal :=
      Subgroup.Normal.map hTn c.phi c.phi_surj
    apply perm3_normal_top
    refine ⟨c.phi x, ⟨x, hxT, rfl⟩, ?_, ?_⟩
    · rw [hx, hx₀]; decide
    · rw [hx, hx₀]; decide
  rw [eq_top_iff]
  intro g _
  have : c.phi g ∈ (oPrimeResidual 2 Γ).map c.phi := by rw [hφT]; trivial
  obtain ⟨t, ht, hgt⟩ := this
  have hgt' : g * t⁻¹ ∈ R := by
    apply c.phi_eq_one.1
    rw [map_mul, map_inv, hgt, mul_inv_cancel]
  have : g = (g * t⁻¹) * t := by group
  rw [this]
  exact Subgroup.mul_mem _ (hRT hgt') ht

theorem BarCfg.summary [Finite Γ] (c : BarCfg R z) (hO : pPrimeCore 2 Γ = ⊥) :
    ∃ A : Subgroup Γ, Nonempty (↥A ≃* Multiplicative (ZMod 3)) ∧ oResidual 2 Γ = R ⊔ A ∧
      generalizedFitting Γ = R ∧ ⁅R, A⁆ = R ∧
      (∀ w ∈ R, (∀ a ∈ A, a * w = w * a) → w ∈ zpowers z) ∧
      (pCore 2 ↥(oResidual 2 Γ)).map (oResidual 2 Γ).subtype = R ∧ oPrimeResidual 2 Γ = ⊤ ∧
      (∀ g ∈ R ⊔ A, ∀ k : ℕ, g ^ (2 ^ k) = 1 → g ∈ R) := by
  obtain ⟨X⟩ : Nonempty (Sylow 3 Γ) := inferInstance
  have hXc := c.sylow3_card X
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : IsCyclic ↥(X : Subgroup Γ) := isCyclic_of_prime_card (p := 3) hXc
  refine ⟨X, ⟨?_⟩, c.oResidual_eq X, c.generalizedFitting_eq hO, c.commutator_eq X,
    fun w hw h => c.cent_X X w hw h, c.pCore_oResidual X, c.oPrimeResidual_eq_top,
    fun g hg k hk => c.mem_R_of_pElt X hg hk⟩
  exact mulEquivOfCyclicCardEq (by rw [hXc]; simp [Nat.card_eq_fintype_card])

end Abstract

end CFSG.GH74.GLS.Stage1.Thm6.Prod
