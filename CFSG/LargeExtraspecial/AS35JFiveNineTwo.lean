module

public import CFSG.LargeExtraspecial.AS35JFiveNine
public import CFSG.LargeExtraspecial.AS35HSixEleven
public import CFSG.LargeExtraspecial.AS35HSixEightA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace S14

@[expose] def AschbacherFiveNineHypStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.SixFiveConcl →
    ∀ t ∈ S.DSet, ∀ (htM : t ∈ S.M) (U : Subgroup S.O), U ≤ S.Mbar →
      (∀ u ∈ U, u * u = 1) → S.ρ ⟨t, htM⟩ ∈ U →
      (∀ c ∈ S.Mbar, c * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) →
        U ≤ zpowers (S.ρ ⟨t, htM⟩)

end S14

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_two_mem_delta_J {t h : G} (ht : t ∈ S.DSet) (hh : h * S.z * h⁻¹ = t) :
    ∃ p p' : G, p ∈ S.zConj (S.HAt h) ∧ p ≠ S.z ∧ p ≠ t ∧ p' ∈ S.zConj (S.HAt h) ∧
      p' ≠ S.z ∧ p' ≠ t ∧ p ≠ p' := by
  have htH := S.mem_zConj_of_mem_ESet ht.1 hh
  have h5 := (S.isHStar_of_mem_ESet ht.1 hh).2
  have htz := S.ne_z_of_mem_ESet ht.1
  have hsub : ({S.z, t} : Set G) ⊆ S.zConj (S.HAt h) := by
    rintro w (rfl | rfl)
    · exact Asc77.self_mem_conjIn _ _
    · exact htH
  have h3 : (S.zConj (S.HAt h) \ {S.z, t}).ncard = 3 := by
    rw [Set.ncard_sdiff hsub, h5, Set.ncard_pair htz.symm]
  obtain ⟨p, p', hp, hp', hne⟩ := (Set.one_lt_ncard_iff
    (s := S.zConj (S.HAt h) \ {S.z, t}) (Set.toFinite _)).mp (by omega)
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp hp'
  exact ⟨p, p', hp.1, hp.2.1, hp.2.2, hp'.1, hp'.2.1, hp'.2.2, hne⟩

theorem exists_swap_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet) (hh : h * S.z * h⁻¹ = t) :
    ∃ g : G, g * S.z * g⁻¹ = t ∧ g * t * g⁻¹ = S.z := by
  classical
  have hH := (S.isHStar_of_mem_ESet ht.1 hh).1
  obtain ⟨_, _, -, -, -, -, hsurj⟩ := (hS.sixFour _ hH).1.1
  have htH := S.mem_zConj_of_mem_ESet ht.1 hh
  have htz := S.ne_z_of_mem_ESet ht.1
  obtain ⟨p, p', hpH, hpz, hpt, hp'H, hp'z, hp't, hne⟩ := S.exists_two_mem_delta_J ht hh
  set Z : S.zConj (S.HAt h) := ⟨S.z, Asc77.self_mem_conjIn _ _⟩
  set T : S.zConj (S.HAt h) := ⟨t, htH⟩
  set P : S.zConj (S.HAt h) := ⟨p, hpH⟩
  set P' : S.zConj (S.HAt h) := ⟨p', hp'H⟩
  have hne' : ∀ {x y : S.zConj (S.HAt h)}, (x : G) ≠ y → x ≠ y :=
    fun h h' => h (congrArg Subtype.val h')
  have hσ : Equiv.Perm.sign (Equiv.swap Z T * Equiv.swap P P') = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (hne' htz.symm), Equiv.Perm.sign_swap (hne' hne)]
    decide
  have hZP : Z ≠ P := hne' (Ne.symm hpz)
  have hZP' : Z ≠ P' := hne' (Ne.symm hp'z)
  have hTP : T ≠ P := hne' (Ne.symm hpt)
  have hTP' : T ≠ P' := hne' (Ne.symm hp't)
  obtain ⟨k, hk⟩ := hsurj _ hσ
  refine ⟨k, ?_, ?_⟩
  · have e := congrArg Subtype.val (DFunLike.congr_fun hk Z)
    rw [Asc77.conjAct_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hZP hZP',
      Equiv.swap_apply_left] at e
    exact e
  · have e := congrArg Subtype.val (DFunLike.congr_fun hk T)
    rw [Asc77.conjAct_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hTP hTP',
      Equiv.swap_apply_right] at e
    exact e

theorem exists_commute_rho_eq_J (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) (htM : t ∈ S.M)
    {m : G} (hmM : m ∈ S.M)
    (hm : S.ρ ⟨m, hmM⟩ * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * S.ρ ⟨m, hmM⟩) :
    ∃ m' : G, ∃ hm' : m' ∈ S.M, m' * t = t * m' ∧ S.ρ ⟨m', hm'⟩ = S.ρ ⟨m, hmM⟩ := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
  have hsD : m * t * m⁻¹ ∈ S.DSet := S.conj_mem_DSet hmM ht
  have hsM : m * t * m⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)
  have hρs : S.ρ ⟨m * t * m⁻¹, hsM⟩ = S.ρ ⟨t, htM⟩ := by
    have e : (⟨m * t * m⁻¹, hsM⟩ : S.M) = ⟨m, hmM⟩ * ⟨t, htM⟩ * ⟨m, hmM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hm]
    group
  have hsH := S.mem_zConj_of_rho_eq hS hsD ht hh hsM htM hρs
  obtain ⟨q, hq, hqs⟩ := S.exists_conj_eq_of_mem_zConj hS ht hh hsH (S.ne_z_of_mem_ESet hsD.1)
  have hqM := S.QG_le_M hq
  refine ⟨q⁻¹ * m, S.M.mul_mem (S.M.inv_mem hqM) hmM, ?_, ?_⟩
  · calc q⁻¹ * m * t = q⁻¹ * (m * t * m⁻¹) * m := by group
      _ = q⁻¹ * (q * t * q⁻¹) * m := by rw [hqs]
      _ = t * (q⁻¹ * m) := by group
  · have e : (⟨q⁻¹ * m, S.M.mul_mem (S.M.inv_mem hqM) hmM⟩ : S.M) =
        (⟨q, hqM⟩ : S.M)⁻¹ * ⟨m, hmM⟩ := rfl
    rw [e, map_mul, map_inv, (S.ρ_eq_one_iff _).mpr hq, inv_one, one_mul]

theorem commute_of_mem_inf_Qa_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {w : G} (hw : w ∈ S.QG ⊓ S.Qa h) :
    ∀ b ∈ S.QG ⊓ centralizer ({t} : Set G), b * w = w * b := by
  obtain ⟨hwQ, hwQt⟩ := mem_inf.mp hw
  intro b hb
  obtain ⟨hbQ, hbt⟩ := mem_inf.mp hb
  have hbt' : b * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * b := by
    rw [hh]
    exact mem_centralizer_singleton_iff.mp hbt
  have h1 : w * b * w⁻¹ * b⁻¹ ∈ S.Qa h := by
    rw [show w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) by group]
    exact (S.Qa h).mul_mem hwQt (S.conj_mem_Qa_of_commute_asc hbt' ((S.Qa h).inv_mem hwQt))
  rcases S.commutator_eq_one_or_z hwQ hbQ with h2 | h2
  · calc b * w = (w * b * w⁻¹ * b⁻¹)⁻¹ * (w * b) := by group
      _ = w * b := by rw [h2, inv_one, one_mul]
  · exact absurd (h2 ▸ h1) (S.z_not_mem_Qa hS.weak (hh ▸ S.ne_z_of_mem_ESet ht.1))

theorem mem_zConj_of_mul_mem_J (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {a : G} (haz : IsConj S.z a) (haQ : a * t ∈ S.QG)
    (haQt : a * S.z ∈ S.Qa h) :
    a ∈ S.zConj (S.HAt h) := by
  have hS4 := hS.sixFour
  have htM := S.mem_M_of_mem_ESet hS4 ht.1
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hzt : t * S.z = S.z * t := S.mem_M_iff.mp htM
  have htQt : t ∈ S.Qa h := by
    rw [S.mem_Qa_iff_inv_conj_mem, ← hh]
    rw [show h⁻¹ * (h * S.z * h⁻¹) * h = S.z by group]
    exact S.z_mem_QG
  have hwQ : a * t * S.z ∈ S.QG := S.QG.mul_mem haQ S.z_mem_QG
  have hwQt : a * t * S.z ∈ S.Qa h := by
    rw [mul_assoc, hzt, ← mul_assoc]
    exact (S.Qa h).mul_mem haQt htQt
  have hcl := S.cl_mem_commSpace_of_commute hS4 hS.weak ht htM hwQ
    (S.commute_of_mem_inf_Qa_J hS ht hh (mem_inf.mpr ⟨hwQ, hwQt⟩))
  obtain ⟨v, hv⟩ := mem_commSpace.mp hcl
  obtain ⟨q, hq, rfl⟩ := S.exists_cl v
  obtain ⟨h1, h2⟩ := S.cl_conj_mul_eq htM htt hq
  have hqH : q * t * q⁻¹ ∈ S.zConj (S.HAt h) :=
    Asc77.conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa h) hq) (S.mem_zConj_of_mem_ESet ht.1 hh)
  have e1 : a = a * t * S.z * (S.z * t) := by
    rw [show a * t * S.z * (S.z * t) = a * (t * (S.z * S.z) * t) by group, S.z_mul_z, mul_one,
      htt, mul_one]
  have e2 : t * (S.z * t) = S.z := by
    calc t * (S.z * t) = (t * S.z) * t := by group
      _ = (S.z * t) * t := by rw [hzt]
      _ = S.z := by rw [mul_assoc, htt, mul_one]
  have e3 : t * S.z * (S.z * t) = 1 := by
    rw [show t * S.z * (S.z * t) = t * (S.z * S.z) * t by group, S.z_mul_z, mul_one, htt]
  rcases (S.cl_eq_cl_iff h1 hwQ).mp (h2.trans hv) with h3 | h3
  ·
    exfalso
    apply ht.2
    have hqz : q⁻¹ * S.z = S.z * q⁻¹ := S.z_comm_QG (S.QG.inv_mem hq)
    have h4 : a = q * (S.z * t) * q⁻¹ := by
      calc a = a * t * S.z * (S.z * t) := e1
        _ = q * t * q⁻¹ * t * (S.z * t) := by rw [h3]
        _ = q * t * q⁻¹ * (t * (S.z * t)) := by group
        _ = q * t * (q⁻¹ * S.z) := by rw [e2]; group
        _ = q * t * (S.z * q⁻¹) := by rw [hqz]
        _ = q * (t * S.z) * q⁻¹ := by group
        _ = q * (S.z * t) * q⁻¹ := by rw [hzt]
    exact haz.trans (isConj_iff.mpr ⟨q⁻¹, by rw [h4]; group⟩)
  ·
    have h4 : a = q * t * q⁻¹ := by
      calc a = a * t * S.z * (S.z * t) := e1
        _ = q * t * q⁻¹ * t * S.z * (S.z * t) := by rw [h3]
        _ = q * t * q⁻¹ * (t * S.z * (S.z * t)) := by group
        _ = q * t * q⁻¹ := by rw [e3, mul_one]
    rw [h4]
    exact hqH

theorem fiveNineTwo_J (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (hR : S14.AschbacherFiveNineHypStmt) {t : G} (ht : t ∈ S.DSet) {c : G}
    (hc : c * (S.z * t) = S.z * t * c) : c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = t := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
  have hS4 := hS.sixFour
  have htM := S.mem_M_of_mem_ESet hS4 ht.1
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have htQ := S.not_mem_QG_of_mem_ESet hS.weak ht.1
  set Γ : Set G := {a | ∃ x : G, x * S.z * x⁻¹ = a ∧ x⁻¹ * (S.z * t) * x ∈ S.QG} with hΓ
  have hΓc : ∀ d : G, d * (S.z * t) = S.z * t * d → ∀ a ∈ Γ, d * a * d⁻¹ ∈ Γ := by
    rintro d hd _ ⟨x, rfl, hx⟩
    refine ⟨d * x, by group, ?_⟩
    have hd' : d⁻¹ * (S.z * t) * d = S.z * t := by rw [mul_assoc, ← hd]; group
    rwa [show (d * x)⁻¹ * (S.z * t) * (d * x) = x⁻¹ * (d⁻¹ * (S.z * t) * d) * x by group, hd']
  have hΔΓ : ∀ p ∈ S.zConj (S.HAt h), p ≠ S.z → p ≠ t → p ∈ Γ := by
    intro p hp hpz hpt
    obtain ⟨k, hk, hkQ⟩ := S.exists_conj_mem_QG_J hS ht hh hp hpz hpt
    exact ⟨k, hk, hkQ⟩
  have hzΓ : S.z ∉ Γ := by
    rintro ⟨x, hx, hxQ⟩
    apply htQ
    have h1 := S.conj_mem_QG (S.mem_M_of_conj_eq_z hx) hxQ
    rw [show x * (x⁻¹ * (S.z * t) * x) * x⁻¹ = S.z * t by group] at h1
    have h2 := S.QG.mul_mem S.z_mem_QG h1
    rwa [← mul_assoc, S.z_mul_z, one_mul] at h2
  have hΓM : ∀ a ∈ Γ, a ∈ S.M := by
    rintro _ ⟨x, rfl, hx⟩
    exact S.mem_M_iff.mpr (S.conj_z_commute_J hS ht hh hx)
  have hΓΓ : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a := by
    rintro _ ⟨x, rfl, hx⟩ _ ⟨y, rfl, hy⟩
    exact (S.commute_of_mem_oTwoCent_J hS ht hx (S.conj_z_mem_oTwoCent_J hS ht hy)).symm
  have hΓ2 : ∀ a ∈ Γ, a * a = 1 := by
    rintro _ ⟨x, rfl, -⟩
    rw [show x * S.z * x⁻¹ * (x * S.z * x⁻¹) = x * (S.z * S.z) * x⁻¹ by group, S.z_mul_z]
    group
  set B : Set S.O := {σ | ∃ a ∈ Γ, ∃ ha : a ∈ S.M, S.ρ ⟨a, ha⟩ = σ} with hB
  have hUM : closure B ≤ S.Mbar := by
    rw [closure_le]
    rintro _ ⟨a, -, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hU2 : ∀ u ∈ closure B, u * u = 1 := by
    intro u hu
    have h1 := AS35J.mul_self_mem_pair_of_mem_closure (A := B) (e := (1 : S.O)) (mul_one 1)
      (by rintro _ ⟨a, haΓ, ha, rfl⟩; exact S.ρ_mul_self_eq_one ha (hΓ2 a haΓ))
      (fun _ _ => by group)
      (by
        rintro _ ⟨a, haΓ, ha, rfl⟩ _ ⟨b, hbΓ, hb, rfl⟩
        left
        have hab : S.ρ ⟨a, ha⟩ * S.ρ ⟨b, hb⟩ = S.ρ ⟨b, hb⟩ * S.ρ ⟨a, ha⟩ := by
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hΓΓ a haΓ b hbΓ)
        rw [hab]
        group) u hu
    rcases h1 with h1 | h1 <;> exact h1
  obtain ⟨p, -, hpH, hpz, hpt, -⟩ := S.exists_two_mem_delta_J ht hh
  have htU : S.ρ ⟨t, htM⟩ ∈ closure B := by
    have hpΓ := hΔΓ p hpH hpz hpt
    have hpM := hΓM p hpΓ
    have hpt' := (S.mul_mem_QG_of_mem_zConj hS ht hh htM hpH hpz).1
    have e : S.ρ ⟨p, hpM⟩ = S.ρ ⟨t, htM⟩ := by
      have h1 : S.ρ ⟨p, hpM⟩ * S.ρ ⟨t, htM⟩ = 1 := by
        rw [← map_mul]
        exact (S.ρ_eq_one_iff _).mpr hpt'
      calc S.ρ ⟨p, hpM⟩ = S.ρ ⟨p, hpM⟩ * (S.ρ ⟨t, htM⟩ * S.ρ ⟨t, htM⟩) := by
            rw [S.ρ_mul_self_eq_one htM htt, mul_one]
        _ = S.ρ ⟨t, htM⟩ := by rw [← mul_assoc, h1, one_mul]
    rw [← e]
    exact subset_closure ⟨p, hpΓ, hpM, rfl⟩
  have hUn : ∀ c' ∈ S.Mbar, c' * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * c' →
      ∀ u ∈ closure B, c' * u * c'⁻¹ ∈ closure B := by
    rintro _ ⟨⟨m, hmM⟩, rfl⟩ hcm u hu
    obtain ⟨m', hm'M, hm't, hm'ρ⟩ := S.exists_commute_rho_eq_J hS ht htM hmM hcm
    rw [← hm'ρ]
    have hm'zt : m' * (S.z * t) = S.z * t * m' := by
      calc m' * (S.z * t) = m' * S.z * t := by group
        _ = S.z * (m' * t) := by rw [S.mem_M_iff.mp hm'M]; group
        _ = S.z * t * m' := by rw [hm't]; group
    induction hu using closure_induction with
    | mem σ hσ =>
      obtain ⟨a, haΓ, ha, rfl⟩ := hσ
      have hmaM : m' * a * m'⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hm'M ha) (S.M.inv_mem hm'M)
      refine subset_closure ⟨m' * a * m'⁻¹, hΓc m' hm'zt a haΓ, hmaM, ?_⟩
      have e : (⟨m' * a * m'⁻¹, hmaM⟩ : S.M) = ⟨m', hm'M⟩ * ⟨a, ha⟩ * ⟨m', hm'M⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    | one => simp
    | mul u₁ u₂ _ _ ih₁ ih₂ =>
      rw [show S.ρ ⟨m', hm'M⟩ * (u₁ * u₂) * (S.ρ ⟨m', hm'M⟩)⁻¹ =
        S.ρ ⟨m', hm'M⟩ * u₁ * (S.ρ ⟨m', hm'M⟩)⁻¹ * (S.ρ ⟨m', hm'M⟩ * u₂ * (S.ρ ⟨m', hm'M⟩)⁻¹)
        by group]
      exact mul_mem ih₁ ih₂
    | inv u _ ih =>
      rw [show S.ρ ⟨m', hm'M⟩ * u⁻¹ * (S.ρ ⟨m', hm'M⟩)⁻¹ =
        (S.ρ ⟨m', hm'M⟩ * u * (S.ρ ⟨m', hm'M⟩)⁻¹)⁻¹ by group]
      exact inv_mem ih
  have hle := hR G S hS h65 t ht htM (closure B) hUM hU2 htU hUn
  have hΓt : ∀ a ∈ Γ, a * t ∈ S.QG := by
    intro a haΓ
    have haM := hΓM a haΓ
    have h1 : S.ρ ⟨a, haM⟩ ∈ zpowers (S.ρ ⟨t, htM⟩) := hle (subset_closure ⟨a, haΓ, haM, rfl⟩)
    rw [mem_zpowers_iff_of_mul_self (S.ρ_mul_self_eq_one htM htt)] at h1
    rcases h1 with h1 | h1
    · exfalso
      have haQ : a ∈ S.QG := (S.ρ_eq_one_iff _).mp h1
      obtain ⟨x, rfl, hx⟩ := haΓ
      exact hzΓ ⟨x, hS.weak x haQ, hx⟩
    · have e : (⟨a * t, S.M.mul_mem haM htM⟩ : S.M) = ⟨a, haM⟩ * ⟨t, htM⟩ := rfl
      exact (S.ρ_eq_one_iff ⟨a * t, S.M.mul_mem haM htM⟩).mp
        (by rw [e, map_mul, h1, S.ρ_mul_self_eq_one htM htt])
  obtain ⟨g, hg1, hg2⟩ := S.exists_swap_J hS ht hh
  have hgzt : g⁻¹ * (S.z * t) = S.z * t * g⁻¹ := by
    have e : g * (S.z * t) * g⁻¹ = S.z * t := by
      rw [show g * (S.z * t) * g⁻¹ = (g * S.z * g⁻¹) * (g * t * g⁻¹) by group, hg1, hg2]
      exact S.mem_M_iff.mp htM
    calc g⁻¹ * (S.z * t) = g⁻¹ * (g * (S.z * t) * g⁻¹) := by rw [e]
      _ = S.z * t * g⁻¹ := by group
  have hΓz : ∀ a ∈ Γ, a * S.z ∈ S.Qa h := by
    intro a haΓ
    have h1 := hΓt _ (hΓc g⁻¹ hgzt a haΓ)
    rw [← S.Qa_eq_of_conj_eq (hg1.trans hh.symm), S.mem_Qa_iff_inv_conj_mem]
    have e : g⁻¹ * S.z * g = t := by rw [← hg2]; group
    rwa [show g⁻¹ * (a * S.z) * g = g⁻¹ * a * g⁻¹⁻¹ * t by rw [← e]; group]
  have hΓΩ : ∀ a ∈ Γ, a ∈ S.zConj (S.HAt h) := by
    intro a haΓ
    have haz : IsConj S.z a := by
      obtain ⟨x, rfl, -⟩ := haΓ
      exact isConj_iff.mpr ⟨x, rfl⟩
    exact S.mem_zConj_of_mul_mem_J hS ht hh haz (hΓt a haΓ) (hΓz a haΓ)
  obtain ⟨p₁, p₂, hp₁H, hp₁z, hp₁t, hp₂H, hp₂z, hp₂t, hne⟩ := S.exists_two_mem_delta_J ht hh
  have hc₁ := hΓΩ _ (hΓc c hc p₁ (hΔΓ p₁ hp₁H hp₁z hp₁t))
  have hc₂ := hΓΩ _ (hΓc c hc p₂ (hΔΓ p₂ hp₂H hp₂z hp₂t))
  have hzH := S.conj_mem_zConj_J hS ht hh hp₁H hp₂H hne hc₁ hc₂ (Asc77.self_mem_conjIn S.z _)
  by_contra hcon
  push Not at hcon
  have hcinv : c⁻¹ * (S.z * t) = S.z * t * c⁻¹ := by
    calc c⁻¹ * (S.z * t) = c⁻¹ * (S.z * t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * (S.z * t)) * c⁻¹ := by rw [hc]
      _ = S.z * t * c⁻¹ := by group
  have h1 := hΓc c⁻¹ hcinv _ (hΔΓ _ hzH hcon.1 hcon.2)
  rw [show c⁻¹ * (c * S.z * c⁻¹) * c⁻¹⁻¹ = S.z by group] at h1
  exact hzΓ h1

end Setting

namespace S14

theorem aschbacherFiveNineTwoStmt_of (hR : AschbacherFiveNineHypStmt) :
    AschbacherFiveNineTwoStmt :=
  fun _ _ _ S hS h65 _ ht _ hc => S.fiveNineTwo_J hS h65 hR ht hc

end S14

end CFSG.LargeExtraspecial
