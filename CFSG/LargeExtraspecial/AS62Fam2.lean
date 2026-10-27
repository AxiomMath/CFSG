module

public import CFSG.LargeExtraspecial.AS62Defs
public import CFSG.LargeExtraspecial.AS62Fam1
public import CFSG.LargeExtraspecial.AS62Inv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace AS62

variable {G : Type} [Group G] (S : Setting G)

theorem eq_or_eq_of_mem_Gamma {u s y : G} (hu : u ∈ S.QG) (huu : u * u = 1)
    (hcomm : ∀ a ∈ Gamma S u, ∀ b ∈ Gamma S u, a * b = b * a)
    (hK : ∀ a ∈ Gamma S u, ∀ b ∈ Gamma S u, ∀ c ∈ Gamma S u, a * b * c = u →
      a = S.z ∨ b = S.z ∨ c = S.z)
    (hs : s ∈ Gamma S u) (hr : S.z * s * u ∈ Gamma S u) (hy : y ∈ Gamma S u)
    (hyz : y ≠ S.z) : y = s ∨ y = S.z * s * u := by
  have hzΓ := self_mem_Gamma S u
  obtain ⟨c, hc, hcy⟩ := hy
  have hyΓ : y ∈ Gamma S u := hcy ▸ ⟨c, hc, rfl⟩
  have hcu : c * u * c⁻¹ = u := by rw [mem_centralizer_singleton_iff.mp hc]; group
  have hzu : S.z * u = u * S.z := (S.z_comm_QG hu).symm
  have hyz' : y * S.z = S.z * y := hcomm _ hyΓ _ hzΓ
  have hyy := mul_self_of_mem_Gamma S hyΓ
  have hzz := S.z_mul_z
  have hconj3 : ∀ a b d : G, c * a * c⁻¹ * (c * b * c⁻¹) * (c * d * c⁻¹) = c * (a * b * d) * c⁻¹ :=
    fun a b d => by group
  have hzsr : S.z * s * (S.z * s * u) = u := by
    have h1 : S.z * s = s * S.z := hcomm _ hzΓ _ hs
    calc S.z * s * (S.z * s * u) = S.z * (s * S.z) * s * u := by group
      _ = S.z * (S.z * s) * s * u := by rw [h1]
      _ = (S.z * S.z) * (s * s) * u := by group
      _ = u := by rw [hzz, mul_self_of_mem_Gamma S hs, one_mul, one_mul]
  have h1 := hK _ (conj_mem_Gamma S hc hzΓ) _ (conj_mem_Gamma S hc hs) _ (conj_mem_Gamma S hc hr)
    (by rw [hconj3, hzsr, hcu])
  rw [hcy] at h1
  have hv : S.z * y * u ∈ Gamma S u := by
    rcases h1 with h1 | h1 | h1
    · exact absurd h1 hyz
    · have e : y * (c * s * c⁻¹) * (c * (S.z * s * u) * c⁻¹) = u := by
        rw [hcy.symm, hconj3, hzsr, hcu]
      rw [h1] at e
      have e' : c * (S.z * s * u) * c⁻¹ = S.z * y * u := by
        calc c * (S.z * s * u) * c⁻¹ = (y * S.z)⁻¹ * (y * S.z * (c * (S.z * s * u) * c⁻¹)) := by
              group
          _ = S.z * y * u := by
              rw [e, mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right hyy]
      rw [← e']
      exact conj_mem_Gamma S hc hr
    · have e : y * (c * s * c⁻¹) * (c * (S.z * s * u) * c⁻¹) = u := by
        rw [hcy.symm, hconj3, hzsr, hcu]
      rw [h1] at e
      have e' : c * s * c⁻¹ = S.z * y * u := by
        calc c * s * c⁻¹ = y⁻¹ * (y * (c * s * c⁻¹) * S.z) * S.z⁻¹ := by group
          _ = y * u * S.z := by
              rw [e, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right hyy]
          _ = S.z * y * u := by rw [mul_assoc, ← hzu, ← mul_assoc, hyz']
      rw [← e']
      exact conj_mem_Gamma S hc hs
  have hzyv : S.z * y * (S.z * y * u) = u := by
    calc S.z * y * (S.z * y * u) = S.z * (y * S.z) * y * u := by group
      _ = S.z * (S.z * y) * y * u := by rw [hyz']
      _ = (S.z * S.z) * (y * y) * u := by group
      _ = u := by rw [hzz, hyy, one_mul, one_mul]
  have h2 := hK _ (conj_mem_Gamma S hc hzΓ) _ (conj_mem_Gamma S hc hyΓ) _ (conj_mem_Gamma S hc hv)
    (by rw [hconj3, hzyv, hcu])
  rw [hcy] at h2
  have hinj := Setting.conj_injective c
  rcases h1 with h1 | h1 | h1
  · exact absurd h1 hyz
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 hyz
    · exact Or.inl (hinj (h2.trans h1.symm))
    · have e : S.z * y * u = s := hinj (h2.trans h1.symm)
      right
      rw [← e]
      calc y = (S.z * S.z) * y * (u * u) := by rw [hzz, huu, one_mul, mul_one]
        _ = S.z * (S.z * y * u) * u := by group
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 hyz
    · exact Or.inr (hinj (h2.trans h1.symm))
    · have e : S.z * y * u = S.z * s * u := hinj (h2.trans h1.symm)
      exact Or.inl (mul_left_cancel (mul_right_cancel e))

variable [Finite G]

theorem mul_mem_QG_of_rhoL_eq {x y : G} (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hxx : x * x = 1)
    (h : S.rhoL hxM = S.rhoL hyM) : x * y ∈ S.QG := by
  by_contra hQ
  apply S.rhoL_ne_one (S.M.mul_mem hxM hyM) hQ
  have h1 : S.rhoL (S.M.mul_mem hxM hyM) = S.rhoL hxM * S.rhoL hyM := by
    unfold Setting.rhoL
    rw [show (⟨x * y, S.M.mul_mem hxM hyM⟩ : S.M) = ⟨x, hxM⟩ * ⟨y, hyM⟩ from rfl, map_mul]
    rfl
  rw [h1, ← h, S.rhoL_mul_self hxM hxx]

theorem eq_z_or_of_mul_mul_eq (hw : S.width = 2)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {u : G} (hu : u ∈ S.QG)
    (hcu0 : S.cl u ≠ 0)
    (hA : ∀ x ∈ Gamma S u, x ≠ S.z → ∃ hxM : x ∈ S.M,
      IsTypeA S.q (S.rhoL hxM) 2 ∧ S.cl u ∈ commSpace (S.rhoL hxM))
    {a b c : G} (ha : a ∈ Gamma S u) (hb : b ∈ Gamma S u) (hc : c ∈ Gamma S u)
    (habc : a * b * c = u) : a = S.z ∨ b = S.z ∨ c = S.z := by
  by_contra! hne
  obtain ⟨haz, hbz, hcz⟩ := hne
  obtain ⟨haM, hAa, hua⟩ := hA a ha haz
  obtain ⟨hbM, hAb, hub⟩ := hA b hb hbz
  obtain ⟨hcM, hAc, huc⟩ := hA c hc hcz
  have hzQ : ∀ x ∈ Gamma S u, x ∈ S.QG → x = S.z := by
    rintro _ ⟨g, -, rfl⟩ hx
    exact hW g hx
  have haa := mul_self_of_mem_Gamma S ha
  have hcc := mul_self_of_mem_Gamma S hc
  by_cases hab : commSpace (S.rhoL haM) = commSpace (S.rhoL hbM)
  ·
    have h1 := mul_mem_QG_of_rhoL_eq S haM hbM haa
      (S.rhoL_eq_of_commSpace_eq hw haM hbM hAa hAb hab)
    apply hcz (hzQ c hc _)
    have e : c = (a * b)⁻¹ * u := by rw [← habc]; group
    rw [e]
    exact S.QG.mul_mem (S.QG.inv_mem h1) hu
  · rcases S.eq_or_eq_of_tsPlane hw hcu0 hAc.2.2.2.1 hAa.2.2.2.1 hAb.2.2.2.1 hAc.2.2.2.2
        hAa.2.2.2.2 hAb.2.2.2.2 huc hua hub hab with hca | hcb
    ·
      have h1 := mul_mem_QG_of_rhoL_eq S haM hcM haa
        (S.rhoL_eq_of_commSpace_eq hw haM hcM hAa hAc hca.symm)
      apply hbz (hzQ b hb _)
      have e : (a * u * a⁻¹) * (a * c) = b := by
        rw [← habc]
        calc a * (a * b * c) * a⁻¹ * (a * c) = (a * a) * b * (c * c) := by group
          _ = b := by rw [haa, hcc, one_mul, mul_one]
      rw [← e]
      exact S.QG.mul_mem (S.conj_mem_QG haM hu) h1
    ·
      have h1 := mul_mem_QG_of_rhoL_eq S hbM hcM (mul_self_of_mem_Gamma S hb)
        (S.rhoL_eq_of_commSpace_eq hw hbM hcM hAb hAc hcb.symm)
      apply haz (hzQ a ha _)
      have e : a = u * (b * c)⁻¹ := by rw [← habc]; group
      rw [e]
      exact S.QG.mul_mem hu (S.QG.inv_mem h1)

variable {S}

theorem Gamma_eq_of_isTypeA (hS : S.SixFourConcl) (hw : S.width = 2)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {t₁ h₁ : G} (ht₁ : t₁ ∈ S.DSet)
    (hh₁ : h₁ * S.z * h₁⁻¹ = t₁) (h₁M : t₁ ∈ S.M) {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1)
    (huz : u ≠ S.z) (hcu : S.cl u ∈ commSpace (S.rhoL h₁M)) (hzO : S.ZInOTwo u)
    (hA : ∀ x ∈ Gamma S u, x ≠ S.z → ∀ hxM : x ∈ S.M, IsTypeA S.q (S.rhoL hxM) 2) :
    ∃ s ∈ S.zConj (S.HAt h₁), s ≠ S.z ∧ S.z * s * u ∈ S.zConj (S.HAt h₁) ∧
      S.z * s * u ≠ S.z ∧ Gamma S u = {S.z, s, S.z * s * u} := by
  have hnc : ¬ IsConj S.z u := fun hc => by
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    exact huz (hg.symm.trans (hW g (by rw [hg]; exact hu)))
  have huu : u * u = 1 := by
    have h0 := (S.fiveOne_two hS hW ht₁ h₁M).1.2.2.2.2 _ hcu
    rwa [S.q_cl_eq_zero_iff hu, pow_two] at h0
  have hcu0 : S.cl u ≠ 0 := fun h0 => by
    rcases (S.cl_eq_zero_iff hu).mp h0 with h1 | h1
    · exact hu1 h1
    · exact huz h1
  obtain ⟨s, hsΩ, hsz, hrΩ, hrz, hsΓ, hrΓ⟩ := exists_mem_Gamma hS ht₁ hh₁ h₁M hu hu1 huz hcu
  have hcomm : ∀ a ∈ Gamma S u, ∀ b ∈ Gamma S u, a * b = b * a :=
    fun a ha b hb => commute_of_mem_Gamma S hu hu1 huz hnc hzO ha hb
  have hA' : ∀ x ∈ Gamma S u, x ≠ S.z → ∃ hxM : x ∈ S.M,
      IsTypeA S.q (S.rhoL hxM) 2 ∧ S.cl u ∈ commSpace (S.rhoL hxM) := by
    intro x hx hxz
    have hxM := mem_M_of_mem_Gamma S hu hu1 huz hnc hzO hx
    have hAx := hA x hx hxz hxM
    have hxu : x * u * x⁻¹ = u := by rw [commute_u_of_mem_Gamma S hu hx]; group
    refine ⟨hxM, hAx, ?_⟩
    rw [← S.fixSpace_eq_commSpace_of_typeA hw hxM hAx, mem_fixSpace, S.rhoL_cl hxM hu, hxu]
  refine ⟨s, hsΩ, hsz, hrΩ, hrz, ?_⟩
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hy
    by_cases hyz : y = S.z
    · exact Or.inl hyz
    · exact Or.inr (eq_or_eq_of_mem_Gamma S hu huu hcomm
        (fun a ha b hb c hc habc => eq_z_or_of_mul_mul_eq S hw hW hu hcu0 hA' ha hb hc habc)
        hsΓ hrΓ hy hyz)
  · rintro (rfl | rfl | rfl)
    · exact self_mem_Gamma S u
    · exact hsΓ
    · exact hrΓ

private theorem sixFourConcl_of (h22 : S14.AschbacherTwoTwoStmt)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) : S.SixFourConcl := by
  intro H hH
  obtain ⟨g, hgH, hgM⟩ := Set.not_subset.mp hH.1.2.2
  exact ⟨(S.sixFour h22 hW hH hgH hgM).1,
    fun g' hg'H hg'M => (S.sixFour h22 hW hH hg'H hg'M).2⟩

theorem Gamma_eq (h22 : S14.AschbacherTwoTwoStmt) (h : W2Hyp S) {t₁ h₁ : G}
    (ht₁ : t₁ ∈ S.DSet) (hh₁ : h₁ * S.z * h₁⁻¹ = t₁) (h₁M : t₁ ∈ S.M) {u : G} (hu : u ∈ S.QG)
    (hu1 : u ≠ 1) (huz : u ≠ S.z) (hcu : S.cl u ∈ commSpace (S.rhoL h₁M)) :
    ∃ s ∈ S.zConj (S.HAt h₁), s ≠ S.z ∧ S.z * s * u ∈ S.zConj (S.HAt h₁) ∧
      S.z * s * u ≠ S.z ∧ Gamma S u = {S.z, s, S.z * s * u} := by
  have hS := sixFourConcl_of h22 h.hW
  have huu : u * u = 1 := by
    have h0 := (S.fiveOne_two hS h.hW ht₁ h₁M).1.2.2.2.2 _ hcu
    rwa [S.q_cl_eq_zero_iff hu, pow_two] at h0
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  refine Gamma_eq_of_isTypeA hS h.hw h.hW ht₁ hh₁ h₁M hu hu1 huz hcu (h.hO u hu hu2) ?_
  rintro x ⟨g, hg, rfl⟩ hxz hxM
  have hgM : g ∉ S.M := fun hgM => hxz (S.conj_z_of_mem_M hgM)
  have hI : S.QG ⊓ S.Qa g ≠ ⊥ := fun hb => hu1 (by
    have h1 : u ∈ S.QG ⊓ S.Qa g := mem_inf.mpr ⟨hu, mem_Qa_of_mem_centralizer S hu hg⟩
    rwa [hb, mem_bot] at h1)
  exact S.isTypeA_of_inf_ne_bot h.hw h.hW hgM rfl hxM hI

theorem commSpace_eq_of_mem_Gamma (h22 : S14.AschbacherTwoTwoStmt) (h : W2Hyp S) {t₁ : G}
    (ht₁ : t₁ ∈ S.DSet) (h₁M : t₁ ∈ S.M) {u : G} (hu : u ∈ S.QG) (hu1 : u ≠ 1) (huz : u ≠ S.z)
    (hcu : S.cl u ∈ commSpace (S.rhoL h₁M)) {y : G} (hy : y ∈ Gamma S u) (hyz : y ≠ S.z)
    (hyM : y ∈ S.M) : commSpace (S.rhoL hyM) = commSpace (S.rhoL h₁M) := by
  have hS := sixFourConcl_of h22 h.hW
  obtain ⟨h₁, hh₁, -⟩ := ht₁.1
  obtain ⟨s, hsΩ, hsz, hrΩ, hrz, hΓ⟩ := Gamma_eq h22 h ht₁ hh₁ h₁M hu hu1 huz hcu
  have hy' : y ∈ ({S.z, s, S.z * s * u} : Set G) := hΓ ▸ hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy'
  rcases hy' with rfl | rfl | rfl
  · exact absurd rfl hyz
  · exact commSpace_eq_of_mem_zConj hS h.hW ht₁ hh₁ h₁M hsΩ hsz hyM
  · exact commSpace_eq_of_mem_zConj hS h.hW ht₁ hh₁ h₁M hrΩ hrz hyM

theorem false_of_two_lines (h22 : S14.AschbacherTwoTwoStmt) (h : W2Hyp S) {t₁ t₂ : G}
    (ht₁ : t₁ ∈ S.DSet) (ht₂ : t₂ ∈ S.DSet) (h₁M : t₁ ∈ S.M) (h₂M : t₂ ∈ S.M)
    (hline : finrank (ZMod 2) ↥(commSpace (S.rhoL h₁M) ⊓ commSpace (S.rhoL h₂M)) = 1) :
    False := by
  have hS := sixFourConcl_of h22 h.hW
  have hne : commSpace (S.rhoL h₁M) ⊓ commSpace (S.rhoL h₂M) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hline
    exact absurd hline (by norm_num)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, hu, rfl⟩ := S.exists_cl v
  have hu1 : u ≠ 1 := fun h1 => hv0 (by rw [h1, S.cl_one])
  have huz : u ≠ S.z := fun h1 => hv0 (by rw [h1, S.cl_z])
  obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.mp hv
  obtain ⟨h₂, hh₂, -⟩ := ht₂.1
  obtain ⟨s, hsΩ, hsz, -, -, hsΓ, -⟩ := exists_mem_Gamma hS ht₂ hh₂ h₂M hu hu1 huz hv₂
  have hsM := mem_M_of_mem_zConj hS ht₂ hh₂ hsΩ
  have e₂ := commSpace_eq_of_mem_zConj hS h.hW ht₂ hh₂ h₂M hsΩ hsz hsM
  have e₁ := commSpace_eq_of_mem_Gamma h22 h ht₁ h₁M hu hu1 huz hv₁ hsΓ hsz hsM
  rw [e₁.symm.trans e₂, inf_idem] at hline
  have h2 := (S.fiveOne_two hS h.hW ht₂ h₂M).1.2.2.2.1
  omega

end AS62

end CFSG.LargeExtraspecial
