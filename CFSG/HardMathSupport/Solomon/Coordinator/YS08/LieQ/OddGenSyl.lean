module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutB
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStated

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut

@[expose] def SylowRigid (q : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ (U : Sylow q S) (α : MulAut S), (∀ u ∈ (U : Subgroup S), α u = u) →
    Nat.Coprime (orderOf α) q → α = 1

section SylowRigidBasic

variable {q : ℕ} [Fact q.Prime]

theorem SylowRigid.of_one {S : Type*} [Group S] [Finite S] (U₀ : Sylow q S)
    (h : ∀ α : MulAut S, (∀ u ∈ (U₀ : Subgroup S), α u = u) → Nat.Coprime (orderOf α) q → α = 1) :
    SylowRigid q S := by
  intro U α hfix hcop
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S U₀ U
  have hU : (U : Subgroup S) = (U₀ : Subgroup S).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set c : MulAut S := MulAut.conj g with hc
  set β : MulAut S := c⁻¹ * α * c with hβ
  have hβfix : ∀ u ∈ (U₀ : Subgroup S), β u = u := by
    intro u hu
    have hmem : c u ∈ (U : Subgroup S) := by
      rw [hU]
      exact ⟨u, hu, rfl⟩
    have h1 := hfix _ hmem
    simp only [hβ, MulAut.mul_apply]
    rw [h1]
    simp
  have hβpow : β ^ orderOf α = 1 := by
    have h1 : (c⁻¹ * α * c⁻¹⁻¹) ^ orderOf α = c⁻¹ * α ^ orderOf α * c⁻¹⁻¹ := conj_pow
    rw [inv_inv] at h1
    rw [hβ, h1, pow_orderOf_eq_one, mul_one, inv_mul_cancel]
  have hβcop : Nat.Coprime (orderOf β) q :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hβpow) hcop
  have hβ1 := h β hβfix hβcop
  have : α = c * β * c⁻¹ := by
    rw [hβ]
    group
  rw [this, hβ1]
  group

theorem SylowRigid.of_mulEquiv {S S' : Type*} [Group S] [Group S'] [Finite S'] (e : S ≃* S')
    (h : SylowRigid q S) : SylowRigid q S' := by
  intro U' α' hfix hcop
  have hsurj : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  set U : Sylow q S := Sylow.mapSurjective hsurj U' with hU
  have hUc : (U : Subgroup S) = (U' : Subgroup S').map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective hsurj U'
  set α : MulAut S := MulAut.congr e.symm α' with hα
  have hαapp : ∀ s : S, α s = e.symm (α' (e s)) := fun s => rfl
  have hαfix : ∀ u ∈ (U : Subgroup S), α u = u := by
    intro u hu
    rw [hUc] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    rw [hαapp]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [hfix u' hu']
  have hord : orderOf α = orderOf α' :=
    orderOf_injective (MulAut.congr e.symm).toMonoidHom (MulAut.congr e.symm).injective α'
  have hαcop : Nat.Coprime (orderOf α) q := by
    rw [hord]
    exact hcop
  have h1 := h U α hαfix hαcop
  apply (MulAut.congr e.symm).injective
  rw [← hα, h1, map_one]

theorem radRigid_of_sylowRigid {S : Type*} [Group S] [Finite S] (hBT : HoldsTits S q)
    (hLI : ∀ R : Subgroup S, IsRadical q R → ∀ x : S, (∀ r ∈ R, x * r = r * x) → x ∈ R)
    (hS : SylowRigid q S) : RadRigid q S := by
  intro R hR α hfix hord
  have hα : α ^ orderOf α = 1 := pow_orderOf_eq_one α
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  obtain ⟨-, -, -, -, -, U, hU⟩ := canonical_parabolic_tits hBT h0 hp
  rw [radInf_eq_of_pCoreOf hc] at hU
  have hUfix : ∀ u ∈ (U : Subgroup S), α u = u := fun u hu =>
    fixes_normalizer_of_fixes R hp (hLI R ⟨h0, hp, hc, hnt⟩) α hord hα hfix u (hU hu)
  exact hS U α hUfix hord

end SylowRigidBasic

section PSL2

open CFSG.GorensteinWalter

variable {q : ℕ} [Fact q.Prime]

theorem sylowRigid_psl2 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = q ^ n) :
    SylowRigid q (PSL2 F) := by
  intro W α hfix hcop
  obtain ⟨w, hw, rfl⟩ := CFSG.GH74.GLS.Stage2.Signalizer.L46E.l46e_aut_fix_sylow hF W α hfix
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 W.isPGroup') ⟨w, hw⟩
  have hk' : orderOf w = q ^ k := by
    rw [← Subgroup.orderOf_coe (⟨w, hw⟩ : (W : Subgroup (PSL2 F)))] at hk
    exact hk
  have hwk : w ^ (q ^ k) = 1 := by
    rw [← hk']
    exact pow_orderOf_eq_one w
  have hcw : (MulAut.conj w) ^ (q ^ k) = 1 := by
    rw [← map_pow, hwk, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hcw
  have h9 : Nat.Coprime (orderOf (MulAut.conj w)) (q ^ k) := hcop.pow_right k
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h9 hdvd)

theorem sylowRigid_of_PSL_two {f : ℕ} {S : Type} [Group S] [Finite S]
    (h : StatedClassicalModel S .PSL 2 q f) : SylowRigid q S := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  exact (sylowRigid_psl2 (q := q) (F := K) hcard).of_mulEquiv
    (e.trans (CFSG.ComponentClassification.AutL2Facts.statedEquiv (RingEquiv.refl K))).symm

end PSL2

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
