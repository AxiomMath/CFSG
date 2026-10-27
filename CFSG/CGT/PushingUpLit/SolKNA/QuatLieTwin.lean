module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieDatum
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTwinCheck
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.ClassicalInvolution.Q3 (TightDatum)
open CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Certificates CFSG.Sporadic.Schreier

@[expose] def TwinAt {G : Type*} [Group G] (t : G) : Prop :=
  ∀ a ∈ Subgroup.centralizer ({t} : Set G), a ^ 2 = t →
    ∃ g ∈ Subgroup.centralizer ({t} : Set G),
      (a * (g * a * g⁻¹)) ^ 2 = 1 ∧ a * (g * a * g⁻¹) ≠ 1 ∧ a * (g * a * g⁻¹) ≠ t

theorem TwinAt.map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {t : G} (h : TwinAt t) :
    TwinAt (e t) := by
  intro a' ha' ha2
  have ha : e.symm a' ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at ha' ⊢
    apply e.injective
    simpa using ha'
  have ha2' : (e.symm a') ^ 2 = t := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ha2]
  obtain ⟨g, hg, h2, h1, ht⟩ := h _ ha ha2'
  refine ⟨e g, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    simpa using congrArg e hg
  · have key : e ((e.symm a' * (g * e.symm a' * g⁻¹)) ^ 2) = e 1 := congrArg e h2
    simp only [map_pow, map_mul, map_inv, map_one, MulEquiv.apply_symm_apply] at key
    exact key
  · intro h1'
    apply h1
    apply e.injective
    simpa using h1'
  · intro ht'
    apply ht
    apply e.injective
    simpa using ht'

theorem TwinAt.conj {G : Type*} [Group G] {t : G} (h : TwinAt t) (x : G) :
    TwinAt (x * t * x⁻¹) := by
  simpa [MulAut.conj_apply] using TwinAt.map (MulAut.conj x) h

theorem exists_sq_eq_of_tightDatum {G : Type*} [Group G] {P : Subgroup G} {SP : Sylow 2 P} {t : G}
    (h : TightDatum P SP t) : ∃ a ∈ P, a ^ 2 = t := by
  obtain ⟨r, -, ⟨e⟩⟩ := h.quat
  obtain ⟨s, hsSP, hst⟩ := Subgroup.mem_map.mp h.mem
  obtain ⟨u, -, huniq, -⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  have hne : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have h4 : orderOf (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ (r - 2))) = 4 :=
    QuaternionGroup.orderOf_xa 0
  have h2 : orderOf ((QuaternionGroup.xa 0 : QuaternionGroup (2 ^ (r - 2))) ^ 2) = 2 := by
    rw [orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), h4]
    norm_num
  have hsq : orderOf (e.symm (QuaternionGroup.xa 0) ^ 2) = 2 := by
    rw [← map_pow, MulEquiv.orderOf_eq]
    exact h2
  have hs2 : orderOf (⟨s, hsSP⟩ : ↥(SP : Subgroup ↥P)) = 2 := by
    have : orderOf (s : G) = 2 := by rw [show (s : G) = t from hst]; exact h.order
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact this
  have hs : (⟨s, hsSP⟩ : ↥(SP : Subgroup ↥P)) = e.symm (QuaternionGroup.xa 0) ^ 2 :=
    (huniq _ hs2).trans (huniq _ hsq).symm
  refine ⟨(((e.symm (QuaternionGroup.xa 0) : ↥(SP : Subgroup ↥P)) : ↥P) : G),
    ((e.symm (QuaternionGroup.xa 0) : ↥(SP : Subgroup ↥P)) : ↥P).2, ?_⟩
  have hst' : (s : G) = t := hst
  have := congrArg (fun z : ↥(SP : Subgroup ↥P) => ((z : ↥P) : G)) hs
  simpa [hst'] using this.symm

theorem false_of_twinAt_datum {G : Type*} [Group G] {K P : Subgroup G} {SP : Sylow 2 P} {t : G}
    (hD : TightDatum P SP t) (hPK : P ≤ K) (hK : ∀ u ∈ K, orderOf u = 2 → u = t)
    (htw : TwinAt t) : False := by
  obtain ⟨a, haP, ha2⟩ := exists_sq_eq_of_tightDatum hD
  have haC : a ∈ Subgroup.centralizer ({t} : Set G) := hD.cent haP
  obtain ⟨g, hg, hs2, hs1, hst⟩ := htw a haC ha2
  have hconj : g * a * g⁻¹ ∈ P := by
    have := hD.normal.conj_mem ⟨a, haC⟩ (Subgroup.mem_subgroupOf.mpr haP) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hs : a * (g * a * g⁻¹) ∈ K := hPK (P.mul_mem haP hconj)
  exact hst (hK _ hs (orderOf_eq_prime hs2 hs1))

theorem not_quaternion_of_twin_classes {X : Type} [Group X] [Finite X]
    (hcl : ∀ t : X, orderOf t = 2 → ∃ s : X, TwinAt s ∧ ∃ x : X, x * s * x⁻¹ = t)
    {K : Subgroup X} (S : STSetting X K) (R : Sylow 2 K) :
    ¬ IsQuaternionTwoGroup (sylowImg R) := by
  intro hq
  obtain ⟨t, P, SP, hD, hPK, hKt, -⟩ := pieceTightDatum X K S R hq
  obtain ⟨s, hs, x, hx⟩ := hcl t hD.order
  exact false_of_twinAt_datum hD hPK hKt (hx ▸ hs.conj x)

theorem twinAt_subgroup_of_perm {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))}
    {t : Equiv.Perm (Fin n)} (ht : t ∈ P)
    (h : ∀ a ∈ P, a * t = t * a → a ^ 2 = t →
      ∃ g ∈ P, g * t = t * g ∧ (a * (g * a * g⁻¹)) ^ 2 = 1 ∧
        a * (g * a * g⁻¹) ≠ 1 ∧ a * (g * a * g⁻¹) ≠ t) :
    TwinAt (⟨t, ht⟩ : ↥P) := by
  intro a ha ha2
  rw [Subgroup.mem_centralizer_singleton_iff] at ha
  have ha' : (a : Equiv.Perm (Fin n)) * t = t * a := by
    simpa using congrArg Subtype.val ha
  have ha2' : (a : Equiv.Perm (Fin n)) ^ 2 = t := by
    simpa using congrArg Subtype.val ha2
  obtain ⟨g, hgP, hgc, h2, h1, hst⟩ := h a a.2 ha' ha2'
  refine ⟨⟨g, hgP⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hgc)
  · exact Subtype.ext (by simpa using h2)
  · intro h1'
    exact h1 (by simpa using congrArg Subtype.val h1')
  · intro hst'
    exact hst (by simpa using congrArg Subtype.val hst')

theorem not_quaternion_of_perm_model {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {X : Type} [Group X] [Finite X] (e : X ≃* Q.originalSubgroup)
    (ts : List (Equiv.Perm (Fin n))) (hcov : invCoverCheckA n (enumA Q) (ts.map toA) = true)
    (htw : ∀ t ∈ ts, twinCheckA n (enumA Q) (toA t) = true)
    {K : Subgroup X} (S : STSetting X K) (R : Sylow 2 K) :
    ¬ IsQuaternionTwoGroup (sylowImg R) := by
  refine not_quaternion_of_twin_classes (fun x hx => ?_) S R
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have h2 : ((e x : Q.originalSubgroup) : Equiv.Perm (Fin n)) ^ 2 = 1 := by
    simpa using congrArg Subtype.val (show (e x) ^ 2 = 1 by rw [← map_pow, hx2, map_one])
  have h1 : ((e x : Q.originalSubgroup) : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    apply hx1
    apply e.injective
    exact Subtype.ext (by simpa using h)
  obtain ⟨t, ht, g, hgQ, hgt⟩ := invCoverCheckA_sound Q hQ hcov _ (e x).2 h2 h1
  have htQ : t ∈ Q.originalSubgroup := by
    have : t = g⁻¹ * (e x : Equiv.Perm (Fin n)) * g := by rw [← hgt]; group
    rw [this]
    exact Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem (Q.originalSubgroup.inv_mem hgQ)
      (e x).2) hgQ
  have htw' := twinCheckA_sound Q hQ (htw t ht)
  refine ⟨e.symm ⟨t, htQ⟩, ?_, e.symm ⟨g, hgQ⟩, ?_⟩
  · exact TwinAt.map e.symm (twinAt_subgroup_of_perm htQ htw')
  · apply e.injective
    apply Subtype.ext
    simpa using hgt

end CFSG.CGT.PushingUpLit.SolKNA
