module

public import CFSG.LargeExtraspecial.AS35HLocal
public import CFSG.LargeExtraspecial.AS35ESixNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem rhoL_mul_mem {a b : G} (ha : a ∈ S.M) (hb : b ∈ S.M) :
    S.rhoL (S.M.mul_mem ha hb) = S.rhoL ha * S.rhoL hb := by
  change ((S.ρ (⟨a, ha⟩ * ⟨b, hb⟩) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = _
  rw [map_mul]
  rfl

omit [Finite G] in
theorem commSpace_le_fixSpace_of_commute_disjoint {a b : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hab : a * b = b * a) (hdis : commSpace a ⊓ commSpace b = ⊥) :
    commSpace b ≤ fixSpace a := by
  intro w hw
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
  rw [mem_fixSpace, ← sub_eq_zero]
  have h1 : a (b u - u) - (b u - u) ∈ commSpace a := sub_mem_commSpace a _
  have h2 : a (b u - u) - (b u - u) ∈ commSpace b := by
    have hc : a (b u) = b (a u) := by
      rw [← LinearEquiv.mul_apply, hab, LinearEquiv.mul_apply]
    rw [map_sub, hc, show b (a u) - a u - (b u - u) = (b (a u) - a u) - (b u - u) from rfl]
    exact Submodule.sub_mem _ (sub_mem_commSpace b _) (sub_mem_commSpace b _)
  rw [eq_bot_iff] at hdis
  exact (Submodule.mem_bot _).mp (hdis (Submodule.mem_inf.mpr ⟨h1, h2⟩))

theorem orderOf_mul_eq_three_of_not_commute (hS : S.SixHyp) (h65 : S.SixFiveConcl) {r t : G}
    (hr : r ∈ S.DSet) (ht : t ∈ S.DSet) (hrM : r ∈ S.M) (htM : t ∈ S.M)
    (hrt : S.ρ ⟨r, hrM⟩ * S.ρ ⟨t, htM⟩ ≠ S.ρ ⟨t, htM⟩ * S.ρ ⟨r, hrM⟩) :
    orderOf (r * t) = 3 := by
  have hrr : r * r = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet hr.1)
  have htt : t * t = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hcomm : r * t ≠ t * r := by
    intro h
    apply hrt
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  rcases S.sixSix hS h65 hr ht with h1 | h2 | h3
  · exfalso
    apply hcomm
    have h4 : r * t = 1 := orderOf_eq_one_iff.mp h1
    have h5 : t = r := by
      calc t = r * r * t := by rw [hrr, one_mul]
        _ = r := by rw [mul_assoc, h4, mul_one]
    rw [h5]
  · exfalso
    apply hcomm
    have h4 : r * t * (r * t) = 1 := by rw [← pow_two, ← h2]; exact pow_orderOf_eq_one _
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    calc r * t = (r * t)⁻¹ := (inv_eq_of_mul_eq_one_right h4).symm
      _ = t * r := by rw [mul_inv_rev, hrinv, htinv]
  · exact h3

theorem commSpace_le_fixSpace_rt (h65 : S.SixFiveConcl) {r s t : G} (hr : r ∈ S.DSet)
    (hs : s ∈ S.DSet) (ht : t ∈ S.DSet) (hrM : r ∈ S.M) (hsM : s ∈ S.M) (htM : t ∈ S.M)
    (hrs : S.ρ ⟨r, hrM⟩ * S.ρ ⟨s, hsM⟩ = S.ρ ⟨s, hsM⟩ * S.ρ ⟨r, hrM⟩)
    (hrs' : S.ρ ⟨r, hrM⟩ ≠ S.ρ ⟨s, hsM⟩)
    (hts : S.ρ ⟨t, htM⟩ * S.ρ ⟨s, hsM⟩ = S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩)
    (hts' : S.ρ ⟨t, htM⟩ ≠ S.ρ ⟨s, hsM⟩) :
    commSpace (S.rhoL hsM) ≤ fixSpace (S.rhoL (S.M.mul_mem hrM htM)) := by
  have key : ∀ {a : G} (ha : a ∈ S.DSet) (haM : a ∈ S.M),
      S.ρ ⟨a, haM⟩ * S.ρ ⟨s, hsM⟩ = S.ρ ⟨s, hsM⟩ * S.ρ ⟨a, haM⟩ →
      S.ρ ⟨a, haM⟩ ≠ S.ρ ⟨s, hsM⟩ → commSpace (S.rhoL hsM) ≤ fixSpace (S.rhoL haM) := by
    intro a ha haM hc hne
    refine S.commSpace_le_fixSpace_of_commute_disjoint ?_
      (h65.disjoint _ (S.ρ_mem_DbarAsc ha haM) _ (S.ρ_mem_DbarAsc hs hsM) hc hne)
    have := congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) hc
    simp only [Subgroup.coe_mul] at this
    exact this
  intro v hv
  have h1 := key hr hrM hrs hrs' hv
  have h2 := key ht htM hts hts' hv
  rw [mem_fixSpace] at h1 h2 ⊢
  rw [S.rhoL_mul_mem hrM htM, LinearEquiv.mul_apply, h2, h1]

omit [Finite G] in
theorem conj_mem_Qa_of_commute_asc {h b y : G} (hb : b * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * b)
    (hy : y ∈ S.Qa h) : b * y * b⁻¹ ∈ S.Qa h := by
  rw [S.mem_Qa_iff_inv_conj_mem] at hy ⊢
  have hbM : h⁻¹ * b * h ∈ S.M := by
    rw [S.mem_M_iff]
    calc h⁻¹ * b * h * S.z = h⁻¹ * (b * (h * S.z * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * S.z * h⁻¹ * b) * h := by rw [hb]
      _ = S.z * (h⁻¹ * b * h) := by group
  have := S.conj_mem_QG hbM hy
  rwa [show h⁻¹ * b * h * (h⁻¹ * y * h) * (h⁻¹ * b * h)⁻¹ = h⁻¹ * (b * y * b⁻¹) * h by group]
    at this

theorem conj_eq_of_mem_inf_Qa (hS : S.SixHyp) {s h x : G} (hs : s ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = s) (hsM : s ∈ S.M) (hxM : x ∈ S.M) (hx3 : x ^ 3 = 1)
    (hfix : commSpace (S.rhoL hsM) ≤ fixSpace (S.rhoL hxM)) {a : G}
    (ha : a ∈ S.QG ⊓ S.Qa h) : x * a * x⁻¹ = a := by
  obtain ⟨haQ, haQs⟩ := mem_inf.mp ha
  have hc : ∀ b ∈ S.QG ⊓ centralizer ({s} : Set G), b * a = a * b := by
    intro b hb
    obtain ⟨hbQ, hbs⟩ := mem_inf.mp hb
    have hbs' : b * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * b := by
      rw [hh]
      exact mem_centralizer_singleton_iff.mp hbs
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ S.Qa h := by
      rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact (S.Qa h).mul_mem haQs (S.conj_mem_Qa_of_commute_asc hbs' ((S.Qa h).inv_mem haQs))
    rcases S.commutator_eq_one_or_z haQ hbQ with h2 | h2
    · calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
        _ = a * b := by rw [h2, inv_one, one_mul]
    · exact absurd (h2 ▸ h1) (S.z_not_mem_Qa hS.weak (hh ▸ S.ne_z_of_mem_ESet hs.1))
  have h1 := S.cl_mem_commSpace_of_commute hS.sixFour hS.weak hs hsM haQ hc
  have h2 := hfix h1
  rw [mem_fixSpace, S.rhoL_cl hxM haQ] at h2
  exact S.conj_eq_of_cl_conj_eq_of_pow_three hxM hx3 haQ h2

theorem exists_cqx_not_commute (hS : S.SixHyp) {d k y : G} (hd : d ∈ S.DSet)
    (hk : k * S.z * k⁻¹ = d) (hdM : d ∈ S.M) (hyM : y ∈ S.M) (hy3 : y ^ 3 = 1)
    (hyc : ∀ a ∈ S.QG ⊓ S.Qa k, y * a * y⁻¹ = a) :
    ∃ q ∈ S.QG ⊓ centralizer ({y} : Set G), q * d ≠ d * q := by
  classical
  have hdH := S.mem_zConj_of_mem_ESet hd.1 hk
  have h5 := (S.isHStar_of_mem_ESet hd.1 hk).2
  have hdz := S.ne_z_of_mem_ESet hd.1
  have hsub : ({S.z, d} : Set G) ⊆ S.zConj (S.HAt k) := by
    rintro w (rfl | rfl)
    · exact Asc77.self_mem_conjIn _ _
    · exact hdH
  have h3 : (S.zConj (S.HAt k) \ {S.z, d}).ncard = 3 := by
    rw [Set.ncard_sdiff hsub, h5, Set.ncard_pair hdz.symm]
  obtain ⟨p, p', hp, hp', hne⟩ := (Set.one_lt_ncard_iff
    (s := S.zConj (S.HAt k) \ {S.z, d}) (Set.toFinite _)).mp (by omega)
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp hp'
  obtain ⟨hpH, hpz, hpd⟩ := hp
  obtain ⟨hp'H, hp'z, hp'd⟩ := hp'
  obtain ⟨ha, hca, hca0⟩ := S.mul_mem_QG_inf_Qa hS hd hk hdM hpH hp'H hpz hpd hp'z hp'd hne
  by_contra hcon
  push Not at hcon
  have hle : fixSpace (S.rhoL hyM) ≤ fixSpace (S.rhoL hdM) := by
    rw [← S.cqxSub_eq_fixSpace_of_pow_three hyM hy3,
      ← (S.fiveOne_two hS.sixFour hS.weak hd hdM).2.2]
    refine S.clSub_mono fun q hq => mem_inf.mpr ⟨(mem_inf.mp hq).1, ?_⟩
    exact mem_centralizer_singleton_iff.mpr (hcon q hq)
  have hle' : commSpace (S.rhoL hdM) ≤ commSpace (S.rhoL hyM) := by
    rw [← S.orthogonal_fixSpace_of_isometry (S.rhoL_mem hdM),
      ← S.orthogonal_fixSpace_of_isometry (S.rhoL_mem hyM)]
    exact LinearMap.BilinForm.orthogonal_le hle
  have hfa : S.cl (p * p') ∈ fixSpace (S.rhoL hyM) := by
    rw [mem_fixSpace, S.rhoL_cl hyM (mem_inf.mp ha).1, hyc _ ha]
  have h0 := S.commSpace_inf_fixSpace_of_pow_three hyM hy3
  rw [eq_bot_iff] at h0
  exact hca0 ((Submodule.mem_bot _).mp (h0 (Submodule.mem_inf.mpr ⟨hle' hca, hfa⟩)))

theorem exists_Qa_conj_ne (hS : S.SixHyp) {s h x : G} (hs : s ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = s) (hx3 : x ^ 3 = 1) (hxs : x * s = s * x)
    (hxc : ∀ a ∈ S.QG ⊓ S.Qa h, x * a * x⁻¹ = a) :
    ∃ c ∈ S.Qa h, c * x = x * c ∧ c * S.z * c⁻¹ ≠ S.z := by
  have hS4 := hS.sixFour
  have hd : h⁻¹ * S.z * h⁻¹⁻¹ ∈ S.DSet := by
    rw [inv_inv]
    exact S.mem_DAt.mp (S.z_mem_DAt hS4 hs hh)
  have hdM := S.mem_M_of_mem_ESet hS4 hd.1
  have hyM : h⁻¹ * x * h ∈ S.M := by
    rw [S.mem_M_iff]
    calc h⁻¹ * x * h * S.z = h⁻¹ * (x * (h * S.z * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * S.z * h⁻¹ * x) * h := by rw [hh, hxs]
      _ = S.z * (h⁻¹ * x * h) := by group
  have hy3 : (h⁻¹ * x * h) ^ 3 = 1 := by
    rw [show h⁻¹ * x * h = h⁻¹ * x * h⁻¹⁻¹ by rw [inv_inv], conj_pow, hx3]
    group
  have hyc : ∀ a ∈ S.QG ⊓ S.Qa h⁻¹, h⁻¹ * x * h * a * (h⁻¹ * x * h)⁻¹ = a := by
    intro a ha
    obtain ⟨haQ, haQ'⟩ := mem_inf.mp ha
    have h1 : h * a * h⁻¹ ∈ S.QG := by
      have := (S.mem_Qa_iff_inv_conj_mem).mp haQ'
      rwa [inv_inv] at this
    have h2 : h * a * h⁻¹ ∈ S.Qa h := by
      rw [S.mem_Qa_iff_inv_conj_mem]
      rwa [show h⁻¹ * (h * a * h⁻¹) * h = a by group]
    have h3 := hxc _ (mem_inf.mpr ⟨h1, h2⟩)
    calc h⁻¹ * x * h * a * (h⁻¹ * x * h)⁻¹ = h⁻¹ * (x * (h * a * h⁻¹) * x⁻¹) * h := by group
      _ = a := by rw [h3]; group
  obtain ⟨q, hq, hqd⟩ := S.exists_cqx_not_commute hS hd rfl hdM hyM hy3 hyc
  obtain ⟨hqQ, hqy⟩ := mem_inf.mp hq
  have hqy' := mem_centralizer_singleton_iff.mp hqy
  refine ⟨h * q * h⁻¹, ?_, ?_, ?_⟩
  · rw [S.mem_Qa_iff_inv_conj_mem]
    rwa [show h⁻¹ * (h * q * h⁻¹) * h = q by group]
  · calc h * q * h⁻¹ * x = h * (q * (h⁻¹ * x * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * x * h) * q) * h⁻¹ := by rw [hqy']
      _ = x * (h * q * h⁻¹) := by group
  · intro h1
    apply hqd
    have h2 : q * (h⁻¹ * S.z * h) * q⁻¹ = h⁻¹ * S.z * h := by
      calc q * (h⁻¹ * S.z * h) * q⁻¹ = h⁻¹ * (h * q * h⁻¹ * S.z * (h * q * h⁻¹)⁻¹) * h := by
            group
        _ = h⁻¹ * S.z * h := by rw [h1]
    rw [inv_inv]
    calc q * (h⁻¹ * S.z * h) = q * (h⁻¹ * S.z * h) * q⁻¹ * q := by group
      _ = h⁻¹ * S.z * h * q := by rw [h2]

theorem mem_zConj_of_rho_eq (hS : S.SixHyp) {s t h : G} (hs : s ∈ S.DSet) (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) (hsM : s ∈ S.M) (htM : t ∈ S.M)
    (heq : S.ρ ⟨s, hsM⟩ = S.ρ ⟨t, htM⟩) : s ∈ S.zConj (S.HAt h) := by
  have hS4 := hS.sixFour
  have htt : t * t = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hxQ : s * t ∈ S.QG := by
    rw [← S.ρ_eq_one_iff ⟨s * t, S.M.mul_mem hsM htM⟩]
    change S.ρ (⟨s, hsM⟩ * ⟨t, htM⟩) = 1
    rw [map_mul, heq, ← map_mul]
    exact (S.ρ_eq_one_iff _).mpr (by simp [htt])
  have hxt : s * t * t ∈ S.DSet := by rwa [mul_assoc, htt, mul_one]
  have hcl := S.cl_mem_commSpace_of_mul_mem hS4 hS.weak ht htM hxQ hxt
  obtain ⟨w, hw⟩ := mem_commSpace.mp hcl
  obtain ⟨q, hq, rfl⟩ := S.exists_cl w
  obtain ⟨h1, h2⟩ := S.cl_conj_mul_eq htM htt hq
  have htH := S.mem_zConj_of_mem_ESet ht.1 hh
  have hpH : q * t * q⁻¹ ∈ S.zConj (S.HAt h) :=
    Asc77.conj_mem_conjIn_of_mem (le_sup_left (b := S.Qa h) hq) htH
  rcases (S.cl_eq_cl_iff h1 hxQ).mp (h2.trans hw) with h3 | h3
  · have : s = q * t * q⁻¹ := by
      calc s = s * t * t := by rw [mul_assoc, htt, mul_one]
        _ = q * t * q⁻¹ * t * t := by rw [h3]
        _ = q * t * q⁻¹ := by rw [mul_assoc (q * t * q⁻¹) t t, htt, mul_one]
    rw [this]
    exact hpH
  · exfalso
    have hpz : q * t * q⁻¹ ≠ S.z := by
      intro h4
      apply S.ne_z_of_mem_ESet ht.1
      calc t = q⁻¹ * (q * t * q⁻¹) * q := by group
        _ = q⁻¹ * S.z * q⁻¹⁻¹ := by rw [h4, inv_inv]
        _ = S.z := S.conj_z_of_mem_M (S.M.inv_mem (S.QG_le_M hq))
    have hpD := S.zConj_diff_subset_DSet hS4 ht hh hpH hpz
    have hpM := S.mem_M_of_mem_ESet hS4 hpD.1
    apply hpD.2
    have h4 : s = q * t * q⁻¹ * S.z := by
      calc s = s * t * t := by rw [mul_assoc, htt, mul_one]
        _ = q * t * q⁻¹ * t * S.z * t := by rw [h3]
        _ = q * t * q⁻¹ * ((t * S.z) * t) := by group
        _ = q * t * q⁻¹ * ((S.z * t) * t) := by rw [S.z_comm htM]
        _ = q * t * q⁻¹ * (S.z * (t * t)) := by rw [mul_assoc S.z t t]
        _ = q * t * q⁻¹ * S.z := by rw [htt, mul_one]
    rw [← S.mem_M_iff.mp hpM, ← h4]
    exact S.isConj_of_mem_ESet hs.1

theorem mem_DAt_of_mem_zConj' (hS : S.SixHyp) {s t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) (hsH : s ∈ S.zConj (S.HAt h)) (hst : s ≠ t) : s ∈ S.DAt h := by
  obtain ⟨g, hg, hgt⟩ := S.mem_zConj_of_mem_ESet ht.1 hh
  rw [S.DAt_eq_of_conj_eq (hgt.trans hh.symm).symm]
  exact S.mem_DAt_of_mem_zConj hS.sixFour ht hh hg hsH (by rw [hgt]; exact hst)

end Setting

end CFSG.LargeExtraspecial
