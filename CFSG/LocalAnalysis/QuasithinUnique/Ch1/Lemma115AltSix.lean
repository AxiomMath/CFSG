module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import Certificates.Certificate4099
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount

public section

namespace CFSG.QuasithinUnique.Ch1

open Equiv Equiv.Perm CFSG.QuasithinUnique

namespace AltSix

theorem stabilizer_trivial :
    ∀ σ : Perm (Fin 6), (∀ i, act σ (total i) = total i) → σ = 1 :=
  Certificates.certificate4099.1

theorem epsPerm_apply (σ : Perm (Fin 6)) (i : Fin 6) : epsPerm σ i = epsFun σ i := rfl

theorem epsPerm_injective : Function.Injective epsPerm := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply stabilizer_trivial
  intro i
  have : epsFun σ i = i := by
    have := DFunLike.congr_fun hσ i
    simpa [epsPerm_apply] using this
  rw [act_total_epsFun, this]

theorem flat_eq (σ : Perm (Fin 6)) : flat σ = σ := Equiv.ext fun i => tabOf_getD σ i

theorem epsFast_eq : ∀ a : Perm (Fin 6), epsFast a = epsPerm a :=
  Certificates.certificate4099.2.1

theorem sign_epsFast :
    ∀ σ : Perm (Fin 6), Perm.sign (epsFast σ) = Perm.sign σ :=
  Certificates.certificate4099.2.2.1

theorem sign_epsPerm (σ : Perm (Fin 6)) : Perm.sign (epsPerm σ) = Perm.sign σ := by
  rw [← epsFast_eq]
  exact sign_epsFast σ

theorem support_epsPerm_threeCycle :
    (epsPerm (swap 0 1 * swap 1 2)).support.card = 6 :=
  Certificates.certificate4099.2.2.2.1

@[expose] def epsAutHom : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
  (epsPerm.comp (alternatingGroup (Fin 6)).subtype).codRestrict (alternatingGroup (Fin 6))
    fun a => by
      show epsPerm (a : Perm (Fin 6)) ∈ alternatingGroup (Fin 6)
      rw [Perm.mem_alternatingGroup, sign_epsPerm]
      exact Perm.mem_alternatingGroup.mp a.2

theorem epsAutHom_bijective : Function.Bijective epsAutHom := by
  have hinj : Function.Injective epsAutHom := fun a b hab => by
    have h : epsPerm (a : Perm (Fin 6)) = epsPerm (b : Perm (Fin 6)) := congrArg Subtype.val hab
    exact Subtype.ext (epsPerm_injective h)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

@[expose] noncomputable def epsAut : MulAut (alternatingGroup (Fin 6)) :=
  MulEquiv.ofBijective epsAutHom epsAutHom_bijective

theorem epsAut_apply (a : alternatingGroup (Fin 6)) :
    ((epsAut a : alternatingGroup (Fin 6)) : Perm (Fin 6)) = epsPerm (a : Perm (Fin 6)) := rfl

theorem central6 :
    ∀ τ : Perm (Fin 6), τ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * τ →
    τ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * τ →
    τ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * τ →
    τ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * τ → τ = 1 :=
  Certificates.certificate4099.2.2.2.2.1

theorem conj_inj {σ τ : Perm (Fin 6)}
    (h : ∀ a : Perm (Fin 6), Perm.sign a = 1 → σ * a * σ⁻¹ = τ * a * τ⁻¹) : σ = τ := by
  have h' : ∀ a : Perm (Fin 6), Perm.sign a = 1 → (τ⁻¹ * σ) * a = a * (τ⁻¹ * σ) := by
    intro a ha
    have := h a ha
    calc τ⁻¹ * σ * a = τ⁻¹ * (σ * a * σ⁻¹) * σ := by group
      _ = τ⁻¹ * (τ * a * τ⁻¹) * σ := by rw [this]
      _ = a * (τ⁻¹ * σ) := by group
  have h1 := central6 (τ⁻¹ * σ) (h' _ (by decide)) (h' _ (by decide)) (h' _ (by decide))
    (h' _ (by decide))
  exact (inv_mul_eq_one.mp h1).symm

theorem phi_false (σ x : Perm (Fin 6)) : phi σ false x = σ * x * σ⁻¹ := rfl

theorem phi_true (σ x : Perm (Fin 6)) : phi σ true x = σ * epsPerm x * σ⁻¹ := by
  simp only [phi, twist, epsFast_eq]

@[expose] noncomputable def autOf (σ : Perm (Fin 6)) :
    Bool → MulAut (alternatingGroup (Fin 6))
  | false => MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ
  | true => epsAut.trans (MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ)

theorem autOf_apply (σ : Perm (Fin 6)) (b : Bool) (a : alternatingGroup (Fin 6)) :
    ((autOf σ b a : alternatingGroup (Fin 6)) : Perm (Fin 6)) = phi σ b (a : Perm (Fin 6)) := by
  cases b
  · simp [autOf, phi_false, MulAut.conjNormal_apply]
  · simp [autOf, phi_true, MulAut.conjNormal_apply, epsAut_apply]

theorem autOf_injective : Function.Injective fun p : Perm (Fin 6) × Bool => autOf p.1 p.2 := by
  rintro ⟨σ, b⟩ ⟨τ, c⟩ h
  have hall : ∀ a : alternatingGroup (Fin 6), phi σ b (a : Perm (Fin 6)) = phi τ c (a : Perm (Fin 6)) :=
    fun a => by
      rw [← autOf_apply, ← autOf_apply]
      exact congrArg (fun f : MulAut (alternatingGroup (Fin 6)) =>
        ((f a : alternatingGroup (Fin 6)) : Perm (Fin 6))) h
  have hsupp : ∀ (ρ : Perm (Fin 6)) (x : Perm (Fin 6)),
      (ρ * x * ρ⁻¹).support.card = x.support.card :=
    fun ρ x => by rw [Equiv.Perm.support_conj, Finset.card_map]
  have hnot : ∀ ρ : Perm (Fin 6), ¬ ∀ a : alternatingGroup (Fin 6),
      epsPerm (a : Perm (Fin 6)) = ρ * (a : Perm (Fin 6)) * ρ⁻¹ := by
    intro ρ hρ
    have h1 : epsPerm (swap 0 1 * swap 1 2) = ρ * (swap 0 1 * swap 1 2) * ρ⁻¹ :=
      hρ ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩
    have h2 := hsupp ρ (swap 0 1 * swap 1 2)
    rw [← h1, support_epsPerm_threeCycle] at h2
    have h3 : (swap (0 : Fin 6) 1 * swap 1 2).support.card = 3 := by decide
    omega
  cases b <;> cases c
  ·
    have : σ = τ := conj_inj fun a ha => by
      have h' := hall ⟨a, Perm.mem_alternatingGroup.mpr ha⟩
      rwa [phi_false, phi_false] at h'
    rw [this]
  ·
    exfalso
    refine hnot (τ⁻¹ * σ) fun a => ?_
    have h' : σ * (a : Perm (Fin 6)) * σ⁻¹ = τ * epsPerm (a : Perm (Fin 6)) * τ⁻¹ := by
      have := hall a
      rwa [phi_false, phi_true] at this
    calc epsPerm (a : Perm (Fin 6)) = τ⁻¹ * (τ * epsPerm (a : Perm (Fin 6)) * τ⁻¹) * τ := by group
      _ = τ⁻¹ * (σ * (a : Perm (Fin 6)) * σ⁻¹) * τ := by rw [← h']
      _ = (τ⁻¹ * σ) * (a : Perm (Fin 6)) * (τ⁻¹ * σ)⁻¹ := by group
  ·
    exfalso
    refine hnot (σ⁻¹ * τ) fun a => ?_
    have h' : σ * epsPerm (a : Perm (Fin 6)) * σ⁻¹ = τ * (a : Perm (Fin 6)) * τ⁻¹ := by
      have := hall a
      rwa [phi_true, phi_false] at this
    calc epsPerm (a : Perm (Fin 6)) = σ⁻¹ * (σ * epsPerm (a : Perm (Fin 6)) * σ⁻¹) * σ := by group
      _ = σ⁻¹ * (τ * (a : Perm (Fin 6)) * τ⁻¹) * σ := by rw [h']
      _ = (σ⁻¹ * τ) * (a : Perm (Fin 6)) * (σ⁻¹ * τ)⁻¹ := by group
  ·
    have : σ = τ := by
      apply conj_inj
      intro a ha
      obtain ⟨a', ha'⟩ := epsAut.surjective ⟨a, Perm.mem_alternatingGroup.mpr ha⟩
      have h' : σ * epsPerm (a' : Perm (Fin 6)) * σ⁻¹ = τ * epsPerm (a' : Perm (Fin 6)) * τ⁻¹ := by
        have := hall a'
        rwa [phi_true, phi_true] at this
      have hea : epsPerm (a' : Perm (Fin 6)) = a := by
        have := congrArg (fun y : alternatingGroup (Fin 6) => (y : Perm (Fin 6))) ha'
        exact this
      rw [hea] at h'
      exact h'
    rw [this]

theorem autOf_surjective (B : MulAut (alternatingGroup (Fin 6))) : ∃ (σ : Perm (Fin 6)) (b : Bool),
    autOf σ b = B := by
  have hcard : Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ Nat.card (Perm (Fin 6) × Bool) := by
    have h1 := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    have h2 : Nat.card (Perm (Fin 6) × Bool) = 1440 := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin, Fintype.card_bool]
      norm_num [Nat.factorial]
    omega
  obtain ⟨⟨σ, b⟩, hσb⟩ := (autOf_injective.bijective_of_nat_card_le hcard).2 B
  exact ⟨σ, b, hσb⟩

theorem classification :
    ∀ (σ : Perm (Fin 6)) (b : Bool), DatumPremise σ b →
    b = false ∧ σ * σ = 1 ∧ σ ≠ 1 :=
  Certificates.certificate4099.2.2.2.2.2.1

theorem involution_types_fast :
    ∀ σ : Perm (Fin 6), σ * σ = 1 → σ ≠ 1 →
    Perm.sign σ = 1 ∨ σ.support.card = 2 ∨ (epsFast σ).support.card = 2 :=
  Certificates.certificate4099.2.2.2.2.2.2

theorem involution_types (σ : Perm (Fin 6)) (h1 : σ * σ = 1) (h2 : σ ≠ 1) :
    Perm.sign σ = 1 ∨ σ.support.card = 2 ∨ (epsPerm σ).support.card = 2 := by
  rw [← epsFast_eq]
  exact involution_types_fast σ h1 h2

section Assembly

variable {K : Type} [Group K] [Finite K]

theorem invCases_of_altSix (e : K ≃* alternatingGroup (Fin 6)) {β : K ≃* K} (h : InvDatum K β)
    (hz : Subgroup.center K = ⊥) : InvCases K β := by
  classical
  let B : MulAut (alternatingGroup (Fin 6)) := (e.symm.trans β).trans e
  have hB : ∀ x : K, B (e x) = e (β x) := fun x => by simp [B]
  obtain ⟨σ, b, hσb⟩ := autOf_surjective B
  have hBa : ∀ a : alternatingGroup (Fin 6),
      ((B a : alternatingGroup (Fin 6)) : Perm (Fin 6)) = phi σ b (a : Perm (Fin 6)) :=
    fun a => by rw [← hσb]; exact autOf_apply σ b a
  have hinv : ∀ a : Perm (Fin 6), Perm.sign a = 1 → phi σ b (phi σ b a) = a := by
    intro a ha
    have h1 : ∀ a' : alternatingGroup (Fin 6), B (B a') = a' := by
      intro a'
      obtain ⟨x, rfl⟩ := e.surjective a'
      rw [hB, hB, h.involutory]
    have h2 : ((B (B ⟨a, Perm.mem_alternatingGroup.mpr ha⟩) : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) = a := congrArg Subtype.val (h1 _)
    rw [hBa, hBa] at h2
    exact h2
  have hdvd : 8 ∣ (Finset.univ.filter fun a : Perm (Fin 6) =>
      Perm.sign a = 1 ∧ phi σ b a = a).card := by
    obtain ⟨P, hP⟩ := h.sylow
    have hle : (P : Subgroup K) ≤ fixedSubgroup β := fun t ht => hP t ht
    have h1 : Nat.card (P : Subgroup K) ∣ Nat.card (fixedSubgroup β) :=
      Subgroup.card_dvd_of_le hle
    have h2 : Nat.card (P : Subgroup K) = 8 := by
      have hK : Nat.card K = 360 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.card_alternating_six
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Sylow.card_eq_multiplicity, hK]
      have h360 : (360 : ℕ).factorization 2 = 3 := by
        rw [Nat.factorization_def _ Nat.prime_two]
        have h' : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
        rw [h', padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd (by norm_num)]
      rw [h360]
      norm_num
    have h3 : Nat.card (fixedSubgroup β) =
        (Finset.univ.filter fun a : Perm (Fin 6) => Perm.sign a = 1 ∧ phi σ b a = a).card := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr
        { toFun := fun x => ⟨(e x.1 : Perm (Fin 6)), Perm.mem_alternatingGroup.mp (e x.1).2, ?_⟩
          invFun := fun y => ⟨e.symm ⟨y.1, Perm.mem_alternatingGroup.mpr y.2.1⟩, ?_⟩
          left_inv := fun x => ?_
          right_inv := fun y => ?_ }
      · rw [← hBa, hB]
        have : β x.1 = x.1 := x.2
        rw [this]
      · show β (e.symm ⟨y.1, _⟩) = e.symm ⟨y.1, _⟩
        apply e.injective
        apply Subtype.ext
        rw [← hB, MulEquiv.apply_symm_apply, hBa]
        exact y.2.2
      · exact Subtype.ext (by simp)
      · exact Subtype.ext (by simp)
    rw [← h3, ← h2]
    exact h1
  have hnt : ∃ a : Perm (Fin 6), Perm.sign a = 1 ∧ phi σ b a ≠ a := by
    obtain ⟨x, hx⟩ := h.nontrivial
    rw [hz, Subgroup.mem_bot] at hx
    have hbx : β x ≠ x := fun hh => hx (by rw [hh, inv_mul_cancel])
    refine ⟨(e x : Perm (Fin 6)), Perm.mem_alternatingGroup.mp (e x).2, fun hc => hbx ?_⟩
    apply e.injective
    apply Subtype.ext
    rw [← hB, hBa]
    exact hc
  obtain ⟨hb, hsq, hne⟩ := classification σ b ⟨hinv, hdvd, hnt⟩
  subst hb
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hsq
  have hBe : ∀ x : K, ((e (β x) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      σ * ((e x : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ⁻¹ := fun x => by
    rw [← hB, hBa]
    rfl
  let ψ : K ≃* K ⧸ Subgroup.center K := mulEquivQuotientOfCenterEqBot hz
  have hψ : ∀ y : K, ψ.symm (QuotientGroup.mk y) = y := fun y => ψ.symm_apply_apply y
  have hcenter : Nat.card (Subgroup.center K) = 1 ∨ Nat.card (Subgroup.center K) = 3 :=
    Or.inl (by rw [hz]; exact Subgroup.card_bot)
  rcases involution_types σ hsq hne with hs | hs | hs
  ·
    refine Or.inl ⟨h.isSimpleGroup hz, Or.inr (Or.inl ⟨e⟩),
      e.symm ⟨σ, Perm.mem_alternatingGroup.mpr hs⟩, fun x => ?_⟩
    apply e.injective
    apply Subtype.ext
    rw [hBe x]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hσinv]
  ·
    refine Or.inr (Or.inr (Or.inl ⟨ψ.symm.trans e, σ, hcenter,
      Equiv.Perm.card_support_eq_two.mp hs, fun x => ?_⟩))
    show (((ψ.symm.trans e) (QuotientGroup.mk (β x)) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      σ⁻¹ * (((ψ.symm.trans e) (QuotientGroup.mk x) : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψ, hψ, hBe x, hσinv]
  ·
    have hτ : (epsPerm σ)⁻¹ = epsPerm σ := by rw [← map_inv, hσinv]
    refine Or.inr (Or.inr (Or.inl ⟨(ψ.symm.trans e).trans epsAut, epsPerm σ, hcenter,
      Equiv.Perm.card_support_eq_two.mp hs, fun x => ?_⟩))
    show ((epsAut ((ψ.symm.trans e) (QuotientGroup.mk (β x))) : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) = (epsPerm σ)⁻¹ * ((epsAut ((ψ.symm.trans e) (QuotientGroup.mk x)) :
        alternatingGroup (Fin 6)) : Perm (Fin 6)) * epsPerm σ
    rw [epsAut_apply, epsAut_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hψ, hψ, hBe x,
      hσinv, map_mul, map_mul, hτ]

end Assembly

end AltSix

theorem simpleInspection_altSix :
    SimpleInspection (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 6))) := by
  intro K _ _ β h hz ⟨e⟩
  exact AltSix.invCases_of_altSix e h hz

end CFSG.QuasithinUnique.Ch1
