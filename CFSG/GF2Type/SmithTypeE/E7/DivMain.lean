module

public import CFSG.GF2Type.SmithTypeE.E7.DivBase
public import CFSG.GF2Type.SmithTypeE.E7.TrLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.DMod CFSG.SmithD6 CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 z_not_mem_Qa)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Main

variable
  [IsSimpleGroup G]
  {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {ψ : S.Mbar ≃* TD6}

theorem commute_not_mem_Qa_iff (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h h' : G}
    (haQ : h * S.z * h⁻¹ ∈ S.QG) (hane : h * S.z * h⁻¹ ≠ S.z) (hbQ : h' * S.z * h'⁻¹ ∈ S.QG)
    (hbne : h' * S.z * h'⁻¹ ≠ S.z) :
    (Commute (h' * S.z * h'⁻¹) (h * S.z * h⁻¹) ∧ h' * S.z * h'⁻¹ ∉ S.Qa h) ↔
      Mid (planeOf S φ h) (planeOf S φ h') := by
  have hai := cl_eq_wtV_planeOf I hw hO hΦ haQ hane
  have hbj := cl_eq_wtV_planeOf I hw hO hΦ hbQ hbne
  have hq := mem_Qa_iff_adjW I hw hO hΦ haQ hane hbQ hbne (planeOf S φ h) (planeOf S φ h') hai hbj
  have hc : Commute (h' * S.z * h'⁻¹) (h * S.z * h⁻¹) ↔ ¬ Opp (planeOf S φ h).val
      (planeOf S φ h').val := by
    have e1 := S.polar_cl_eq_zero_iff hbQ haQ
    rw [← isometry hΦ, hbj, hai, fModel_wtV (planeOf S φ h').2 (planeOf S φ h).2] at e1
    show _ * _ = _ * _ ↔ _
    rw [← e1]
    have hopp : Opp (planeOf S φ h').val (planeOf S φ h).val ↔
        Opp (planeOf S φ h).val (planeOf S φ h').val := by
      unfold Opp
      rw [disjoint_comm]
    by_cases ho : Opp (planeOf S φ h').val (planeOf S φ h).val
    · simp [ho, hopp.mp ho]
    · simp [ho, mt hopp.mpr ho]
  rw [hq, hc]
  unfold Mid
  simp only [Bool.not_eq_true]
  exact and_comm


theorem sub_eq_add_V32' (a b : Fin 32 → ZMod 2) : a - b = a + b := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize a i = x
  generalize b i = y
  revert x y
  decide

omit [IsSimpleGroup G] in
theorem q_wtV_eq_zero
    (hcl2 : ∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = wtV i) :
    ∀ i < 75735, S.q (φ.symm (wtV i)) = 0 := by
  intro i hi
  obtain ⟨c, hc, hcQ, hcw⟩ := hcl2 i hi
  rw [← hcw, LinearEquiv.symm_apply_apply, S.q_cl_eq_zero_iff hcQ]
  obtain ⟨h, rfl⟩ := isConj_iff.mp hc
  rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]

theorem not_opp_of_not_isConj
    (hcl2 : ∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = wtV i)
    (hiso : ∀ u v : S.Qt, fModel (φ u) (φ v) = polar S.q u v)
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) (E : Fin 75735) :
    ¬ Opp E.val ((ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩)) • E).val := by
  intro hopp
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hsing := S.q_eq_zero_of_mem_commQt hxM hx2 (fixQt_eq_of_not_isConj S hxM hxz)
  obtain ⟨xm, hxm⟩ : ∃ xm : S.M, xm = ⟨g * S.z * g⁻¹, hxM⟩ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : TD6, u = ψ (rhoM S xm) := ⟨_, rfl⟩
  have hu' : ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) = u := by rw [hu, hxm]
  rw [hu'] at hopp
  have hPhi : Phi S φ xm = rhoMod u := by rw [hu]; exact hΦ xm
  have hint : ∀ v, Phi S φ xm (φ v) = φ (((S.ρ xm : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    rw [Phi_apply, LinearEquiv.symm_apply_apply]
  have hcs : commSpace (rhoMod u) =
      (S.commQt (g * S.z * g⁻¹)).map (φ : S.Qt →ₗ[ZMod 2] (Fin 32 → ZMod 2)) := by
    rw [← hPhi, commSpace_eq_map_of_intertwine φ hint, S.commQt_of_mem hxM, hxm]
  have hmem : rhoMod u (wtV E.val) - wtV E.val ∈ commSpace (rhoMod u) := sub_mem_commSpace _ _
  rw [hcs] at hmem
  obtain ⟨t, ht, htv⟩ := hmem
  have hq0 : S.q t = 0 := hsing t ht
  have hAw : rhoMod u (wtV E.val) = wtV ((u • E).val) := rhoMod_wtV u E
  have htφ : φ t = wtV ((u • E).val) + wtV E.val := by
    have h1 : (φ : S.Qt →ₗ[ZMod 2] (Fin 32 → ZMod 2)) t = φ t := rfl
    rw [← h1, htv, hAw, sub_eq_add_V32']
  have ht' : t = φ.symm (wtV ((u • E).val)) + φ.symm (wtV E.val) := by
    rw [← map_add, ← htφ, LinearEquiv.symm_apply_apply]
  have hwt := q_wtV_eq_zero hcl2
  have hf : fModel (wtV ((u • E).val)) (wtV E.val) = 1 := by
    rw [fModel_wtV (u • E).2 E.2]
    have : Opp (u • E).val E.val := by
      unfold Opp at hopp ⊢
      rw [disjoint_comm]
      exact hopp
    simp [this]
  have hq1 : S.q t = 1 := by
    rw [ht', QuadraticMap.map_add (⇑S.q), hwt _ (u • E).2, hwt _ E.2]
    have := hiso (φ.symm (wtV ((u • E).val))) (φ.symm (wtV E.val))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hf] at this
    rw [← this]
    simp
  rw [hq0] at hq1
  exact absurd hq1 (by decide)


theorem not_isConj_mul_z (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {k : G}
    (hvQ : k * S.z * k⁻¹ ∈ S.QG) (hvne : k * S.z * k⁻¹ ≠ S.z) {b : G} (hb : IsOm S k b) :
    ¬ IsConj S.z (k * b * k⁻¹ * S.z) := by
  intro hc
  obtain ⟨hbz, hbQ, hba, hbQa⟩ := hb
  have hka : k⁻¹ * S.z * k⁻¹⁻¹ = k⁻¹ * S.z * k := by rw [inv_inv]
  have hzQv : S.z ∈ S.Qa k := S.z_mem_Qa hvQ hvne
  have haQ' : k⁻¹ * S.z * k ∈ S.QG := (SME.mem_Qa_iff S k S.z).mp hzQv
  have haQ : k⁻¹ * S.z * k⁻¹⁻¹ ∈ S.QG := by rw [hka]; exact haQ'
  have hane : k⁻¹ * S.z * k⁻¹⁻¹ ≠ S.z := by
    intro h
    apply hvne
    calc k * S.z * k⁻¹ = k * (k⁻¹ * S.z * k⁻¹⁻¹) * k⁻¹ := by rw [h]
      _ = S.z := by group
  have hzQa : S.z ∈ S.Qa k⁻¹ := S.z_mem_Qa haQ hane
  have haQa : k⁻¹ * S.z * k ∈ S.Qa k⁻¹ := by
    rw [SME.mem_Qa_iff, inv_inv]
    have : k * (k⁻¹ * S.z * k) * k⁻¹ = S.z := by group
    rw [this]
    exact S.z_mem_QG
  obtain ⟨h', hh'⟩ := isConj_iff.mp hbz
  subst hh'
  have hbne : h' * S.z * h'⁻¹ ≠ S.z := fun h => hbQa (by rw [h]; exact hzQa)
  have e : k⁻¹ * (k * (h' * S.z * h'⁻¹) * k⁻¹ * S.z) * k⁻¹⁻¹ =
      h' * S.z * h'⁻¹ * (k⁻¹ * S.z * k) := by group
  have hba' : IsConj S.z (h' * S.z * h'⁻¹ * (k⁻¹ * S.z * k)) :=
    hc.trans (isConj_iff.mpr ⟨k⁻¹, e⟩)
  obtain ⟨h'', hh''⟩ := isConj_iff.mp hba'
  have hcQ : h'' * S.z * h''⁻¹ ∈ S.QG := by
    rw [hh'']
    exact S.QG.mul_mem hbQ haQ'
  have hcne : h'' * S.z * h''⁻¹ ≠ S.z := by
    intro h
    rw [hh''] at h
    apply hbQa
    have hinv : (k⁻¹ * S.z * k)⁻¹ = k⁻¹ * S.z * k := by
      have hzz : S.z * S.z = 1 := by rw [← pow_two, S.z_sq]
      have h2 : (k⁻¹ * S.z * k) * (k⁻¹ * S.z * k) = 1 := by
        calc (k⁻¹ * S.z * k) * (k⁻¹ * S.z * k) = k⁻¹ * (S.z * S.z) * k := by group
          _ = 1 := by rw [hzz]; group
      exact inv_eq_of_mul_eq_one_right h2
    have hb' : h' * S.z * h'⁻¹ = S.z * (k⁻¹ * S.z * k) := by
      have h3 : h' * S.z * h'⁻¹ =
          (h' * S.z * h'⁻¹ * (k⁻¹ * S.z * k)) * (k⁻¹ * S.z * k)⁻¹ :=
        (mul_inv_cancel_right _ _).symm
      rw [h3, h, hinv]
    rw [hb']
    exact (S.Qa k⁻¹).mul_mem hzQa haQa
  obtain ⟨i₃, hi₃⟩ : ∃ i₃ : Fin 75735, φ (S.cl (h' * S.z * h'⁻¹ * (k⁻¹ * S.z * k))) =
      wtV i₃.val := by
    rw [← hh'']
    exact exists_weight_of_conj I hw hO hΦ hcQ hcne
  have hai := cl_eq_wtV_planeOf I hw hO hΦ haQ hane
  have hbj := cl_eq_wtV_planeOf I hw hO hΦ hbQ hbne
  rw [S.cl_mul hbQ haQ', map_add, ← hka, hai, hbj] at hi₃
  have hadj : adjW (planeOf S φ k⁻¹).val (planeOf S φ h').val = true := by
    rw [adjW_iff (planeOf S φ k⁻¹).2 (planeOf S φ h').2]
    exact Or.inr ⟨i₃, by rw [add_comm]; exact hi₃⟩
  exact hbQa ((mem_Qa_iff_adjW I hw hO hΦ haQ hane hbQ hbne (planeOf S φ k⁻¹)
    (planeOf S φ h') hai hbj).2 hadj)


theorem fK_eq_conj_of_smul (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {k : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG)
    {c₀ : G} (hx'Q : c₀ * S.z * c₀⁻¹ ∈ S.QG) (hx'ne : c₀ * S.z * c₀⁻¹ ≠ S.z)
    (hx'a : Commute (c₀ * S.z * c₀⁻¹) (k⁻¹ * S.z * k)) (c : cMa S k) {h' : G}
    (hbQ : h' * S.z * h'⁻¹ ∈ S.QG) (hbne : h' * S.z * h'⁻¹ ≠ S.z)
    (hpl : ψ (rhoM S (c : S.M)) • planeOf S φ c₀ = planeOf S φ h') :
    fK S k ψ (h' * S.z * h'⁻¹) = psiM S ψ (conjK S k c) * fK S k ψ (c₀ * S.z * c₀⁻¹) *
      (psiM S ψ (conjK S k c))⁻¹ := by
  obtain ⟨y, hy⟩ : ∃ y : G, y = ((c : S.M) : G) := ⟨_, rfl⟩
  have hyM : y ∈ S.M := hy ▸ (c : S.M).2
  have hya : Commute y (k⁻¹ * S.z * k) := hy ▸ (mem_cMa S k).mp c.2
  have e1 : y * c₀ * S.z * (y * c₀)⁻¹ = y * (c₀ * S.z * c₀⁻¹) * y⁻¹ := by group
  have hcx : y * c₀ * S.z * (y * c₀)⁻¹ ∈ S.QG := by
    rw [e1]
    exact S.conj_mem_QG hyM hx'Q
  have hcxne : y * c₀ * S.z * (y * c₀)⁻¹ ≠ S.z := by
    intro h
    apply hx'ne
    have e : c₀ * S.z * c₀⁻¹ = y⁻¹ * (y * c₀ * S.z * (y * c₀)⁻¹) * y := by group
    rw [e, h, mul_assoc, ← S.z_comm hyM, ← mul_assoc, inv_mul_cancel, one_mul]
  have hpl' : planeOf S φ (y * c₀) = planeOf S φ h' := by
    have := planeOf_mul I hw hO hΦ (c : S.M) hx'Q hx'ne
    rw [← hy] at this
    rw [this, hpl]
  have hcl := cl_eq_of_planeOf_eq I hw hO hΦ hcx hcxne hbQ hbne hpl'
  have hcx_a : Commute (y * c₀ * S.z * (y * c₀)⁻¹) (k⁻¹ * S.z * k) := by
    rw [e1]
    exact (hya.mul_left hx'a).mul_left hya.inv_left
  have hconj := fK_conj S k ψ c hx'a
  rw [← hy, ← e1] at hconj
  rw [← hconj]
  rcases (S.cl_eq_cl_iff hbQ hcx).mp hcl.symm with h2 | h2
  · rw [h2]
  · have hzz : S.z * S.z = 1 := by rw [← pow_two, S.z_sq]
    have h3 : h' * S.z * h'⁻¹ = (y * c₀ * S.z * (y * c₀)⁻¹) * S.z := by
      rw [h2, mul_assoc (h' * S.z * h'⁻¹), hzz, mul_one]
    rw [h3, fK_mul_z S ψ hvQ hcx_a]

theorem exists_commute_smul (hUW : UWInput) (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hane : h * S.z * h⁻¹ ≠ S.z) {j j' : Fin 75735} (hj : Mid (planeOf S φ h) j)
    (hj' : Mid (planeOf S φ h) j') :
    ∃ c : S.M, Commute (c : G) (h * S.z * h⁻¹) ∧ ψ (rhoM S c) • j = j' := by
  obtain ⟨g, hg, hgj⟩ := exists_stab_mid_general hUW hj hj'
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm g)
  have hψm : ψ (rhoM S m) = g := by rw [hm, MulEquiv.apply_symm_apply]
  have hfix := (psi_smul_eq_iff hΦ (cl_eq_wtV_planeOf I hw hO hΦ haQ hane) (rhoM S m)).mp
    (by rw [hψm]; exact MulAction.mem_stabilizer_iff.mp hg)
  obtain ⟨c, hc, hcm⟩ := exists_commute_rhoM_eq S haQ hane m hfix
  exact ⟨c, hc, by rw [hcm, hψm]; exact hgj⟩


theorem psi_eq_tvP_of_mem_Qa_zero (hUW : UWInput) (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)))
    (hcl2 : ∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = wtV i)
    {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) {k : G}
    (hv : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa g) (hk0 : φ (S.cl (k * S.z * k⁻¹)) = wtV 0) :
    ∃ p : Fin 365211, ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) = ⟨tvP p, tvP_mem p⟩ := by
  have hiso := isometry hΦ
  have hvQ : k * S.z * k⁻¹ ∈ S.QG := hv.1
  have hvne : k * S.z * k⁻¹ ≠ S.z := fun h => z_not_mem_Qa S hxQ (h ▸ hv.2)
  have hzQv : S.z ∈ S.Qa k := S.z_mem_Qa hvQ hvne
  have hka : k⁻¹ * S.z * k⁻¹⁻¹ = k⁻¹ * S.z * k := by rw [inv_inv]
  have haQ : k⁻¹ * S.z * k⁻¹⁻¹ ∈ S.QG := by
    rw [hka]
    exact (SME.mem_Qa_iff S k S.z).mp hzQv
  have hane : k⁻¹ * S.z * k⁻¹⁻¹ ≠ S.z := by
    intro h
    apply hvne
    calc k * S.z * k⁻¹ = k * (k⁻¹ * S.z * k⁻¹⁻¹) * k⁻¹ := by rw [h]
      _ = S.z := by group
  have hzQa : S.z ∈ S.Qa k⁻¹ := S.z_mem_Qa haQ hane
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = k⁻¹ * g := ⟨_, rfl⟩
  have hx' : c₀ * S.z * c₀⁻¹ = k⁻¹ * (g * S.z * g⁻¹) * k := by rw [hc₀]; group
  have hvx : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹ := fun h => hxQ (h ▸ hvQ)
  have hx'Q : c₀ * S.z * c₀⁻¹ ∈ S.QG := by
    rw [hx']
    exact SME.mem_Qa_symm S ((SME.mem_Qa_iff S g _).mp hv.2) hvx
  have hzx : Commute (g * S.z * g⁻¹) S.z := mem_centralizer_singleton_iff.mp hxM
  have hx'a : Commute (c₀ * S.z * c₀⁻¹) (k⁻¹ * S.z * k) := by
    rw [hx']
    exact (SmithGraph.commute_conj_iff k _ _).mpr hzx
  have hx'Qa : c₀ * S.z * c₀⁻¹ ∉ S.Qa k⁻¹ := by
    intro h
    apply hxQ
    have := (SME.mem_Qa_iff S k⁻¹ _).mp h
    rwa [hx', show k⁻¹⁻¹ * (k⁻¹ * (g * S.z * g⁻¹) * k) * k⁻¹ = g * S.z * g⁻¹ by group] at this
  have hx'ne : c₀ * S.z * c₀⁻¹ ≠ S.z := fun h => hx'Qa (by rw [h]; exact hzQa)
  have hx'Om : IsOm S k (c₀ * S.z * c₀⁻¹) := ⟨isConj_iff.mpr ⟨c₀, rfl⟩, hx'Q, hx'a, hx'Qa⟩
  have hF₀ : fK S k ψ (c₀ * S.z * c₀⁻¹) = ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) := by
    have e : (⟨k * (c₀ * S.z * c₀⁻¹) * k⁻¹, conj_mem_M_of_commute S k hx'a⟩ : S.M) =
        ⟨g * S.z * g⁻¹, hxM⟩ := Subtype.ext (by
      show k * (c₀ * S.z * c₀⁻¹) * k⁻¹ = g * S.z * g⁻¹
      rw [hx']
      group)
    rw [fK_of_mem S k ψ (conj_mem_M_of_commute S k hx'a), e]
  have hmid : ∀ {h' : G}, h' * S.z * h'⁻¹ ∈ S.QG → IsOm S k (h' * S.z * h'⁻¹) →
      Mid (planeOf S φ k⁻¹) (planeOf S φ h') := by
    intro h' hbQ hb
    have hbne : h' * S.z * h'⁻¹ ≠ S.z := fun h => hb.2.2.2 (by rw [h]; exact hzQa)
    refine (commute_not_mem_Qa_iff I hw hO hΦ haQ hane hbQ hbne).mp ⟨?_, hb.2.2.2⟩
    rw [hka]
    exact hb.2.2.1
  have hx'mid := hmid hx'Q hx'Om
  have hKmem : ∀ {b : G}, IsOm S k b → fK S k ψ b ∈ K0 ∧ fK S k ψ b ≠ 1 := by
    intro b hb
    have hbM := conj_mem_M_of_commute S k hb.2.2.1
    have hL : k * b * k⁻¹ ∈ S.L0 k :=
      ⟨(SME.mem_Qa_iff S k _).mpr (by
        rw [show k⁻¹ * (k * b * k⁻¹) * k = b by group]
        exact hb.2.1), hbM⟩
    rw [fK_of_mem S k ψ hbM]
    refine ⟨?_, fun hb1 => ?_⟩
    · rw [← map_Lbar_eq_K0 I hw hO hΦ hvQ hvne hk0]
      exact ⟨rhoM S ⟨_, hbM⟩, mem_subgroupOf.mpr ⟨⟨_, hbM⟩, mem_subgroupOf.mpr hL, rfl⟩, rfl⟩
    · have h1 : rhoM S ⟨_, hbM⟩ = 1 := ψ.injective (hb1.trans (map_one ψ).symm)
      have h2 := congrArg Subtype.val h1
      have h3 : k * b * k⁻¹ ∈ S.QG := (S.ρ_eq_one_iff _).mp h2
      apply hb.2.2.2
      rw [SME.mem_Qa_iff, inv_inv]
      exact h3
  have hO' : ∀ u ∈ fK S k ψ '' {b | IsOm S k b}, u ∈ K0 := by
    rintro _ ⟨b, hb, rfl⟩
    exact (hKmem hb).1
  have h1 : (1 : TD6) ∉ fK S k ψ '' {b | IsOm S k b} := by
    rintro ⟨b, hb, hb1⟩
    exact (hKmem hb).2 hb1
  have hne : (fK S k ψ '' {b | IsOm S k b}).Nonempty := ⟨_, _, hx'Om, rfl⟩
  have hlift : ∀ g' ∈ Stab0, ∃ c : cMa S k, psiM S ψ (conjK S k c) = g' := by
    intro g' hg'
    obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm g')
    have hψm : ψ (rhoM S m) = g' := by rw [hm, MulEquiv.apply_symm_apply]
    have hfix := (psi_smul_eq_iff hΦ hk0 (rhoM S m)).mp (by
      rw [hψm]
      exact MulAction.mem_stabilizer_iff.mp hg')
    obtain ⟨m', hm'v, hm'm⟩ := exists_commute_rhoM_eq S hvQ hvne m hfix
    have hcM : k⁻¹ * (m' : G) * k ∈ S.M := by
      rw [mem_centralizer_singleton_iff]
      have := (SmithGraph.commute_conj_iff k (m' : G) (k * S.z * k⁻¹)).mpr hm'v
      rw [show k⁻¹ * (k * S.z * k⁻¹) * k = S.z by group] at this
      exact this.eq
    have hca : Commute (k⁻¹ * (m' : G) * k) (k⁻¹ * S.z * k) :=
      (SmithGraph.commute_conj_iff k (m' : G) S.z).mpr (mem_centralizer_singleton_iff.mp m'.2)
    refine ⟨⟨⟨_, hcM⟩, (mem_cMa S k).mpr hca⟩, ?_⟩
    have e : conjK S k ⟨⟨_, hcM⟩, (mem_cMa S k).mpr hca⟩ = m' := Subtype.ext (by
      show k * (k⁻¹ * (m' : G) * k) * k⁻¹ = m'
      group)
    rw [e, psiM_apply, hm'm, hψm]
  have hinv : ∀ g' ∈ Stab0, ∀ u ∈ fK S k ψ '' {b | IsOm S k b},
      g' * u * g'⁻¹ ∈ fK S k ψ '' {b | IsOm S k b} := by
    rintro g' hg' _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := hlift g' hg'
    rw [← hc, ← fK_conj S k ψ c hb.2.2.1]
    exact ⟨_, isOm_conj S k c hb, rfl⟩
  have hcomm : ∀ c : cMa S k, Commute ((c : S.M) : G) (k⁻¹ * S.z * k⁻¹⁻¹) := fun c => by
    rw [hka]
    exact (mem_cMa S k).mp c.2
  have hdvd : (fK S k ψ '' {b | IsOm S k b}).ncard ∣ 41664 := by
    obtain ⟨σ, hσ⟩ : ∃ σ : cMa S k →* TD6, σ = (psiM S ψ).comp (conjK S k) := ⟨_, rfl⟩
    obtain ⟨τ, hτ⟩ : ∃ τ : cMa S k →* Equiv.Perm (Fin 75735), τ =
        ((MulAction.toPermHom TD6 (Fin 75735)).comp (psiM S ψ)).comp (cMa S k).subtype :=
      ⟨_, rfl⟩
    have hσc : ∀ c, σ c = psiM S ψ (conjK S k c) := fun c => by rw [hσ]; rfl
    have hτc : ∀ c j, τ c j = ψ (rhoM S (c : S.M)) • j := fun c j => by rw [hτ]; rfl
    have hr1 : (Set.range fun c : cMa S k => σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) * (σ c)⁻¹) =
        fK S k ψ '' {b | IsOm S k b} := by
      ext u
      constructor
      · rintro ⟨c, rfl⟩
        refine ⟨_, isOm_conj S k c hx'Om, ?_⟩
        dsimp only
        rw [hσc]
        exact fK_conj S k ψ c hx'a
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨h', rfl⟩ := isConj_iff.mp hb.1
        have hbQ := hb.2.1
        have hbne : h' * S.z * h'⁻¹ ≠ S.z := fun h => hb.2.2.2 (by rw [h]; exact hzQa)
        obtain ⟨c, hc, hpl⟩ := exists_commute_smul hUW I hw hO hΦ haQ hane hx'mid (hmid hbQ hb)
        have hc' : c ∈ cMa S k := (mem_cMa S k).mpr (by rw [← hka]; exact hc)
        refine ⟨⟨c, hc'⟩, ?_⟩
        dsimp only
        rw [hσc]
        exact (fK_eq_conj_of_smul I hw hO hΦ hvQ hx'Q hx'ne hx'a ⟨c, hc'⟩ hbQ hbne hpl).symm
    have hr2 : (Set.range fun c : cMa S k => τ c (planeOf S φ c₀)) =
        {j : Fin 75735 | Mid (planeOf S φ k⁻¹) j} := by
      ext j
      constructor
      · rintro ⟨c, rfl⟩
        show Mid (planeOf S φ k⁻¹) (τ c (planeOf S φ c₀))
        rw [hτc]
        have hfix := smul_planeOf_of_commute hΦ (cl_eq_wtV_planeOf I hw hO hΦ haQ hane) haQ
          (c : S.M) (hcomm c)
        have := (mid_smul (ψ (rhoM S (c : S.M))) (planeOf S φ k⁻¹) (planeOf S φ c₀)).2 hx'mid
        rwa [hfix] at this
      · intro hj
        obtain ⟨c, hc, hpl⟩ := exists_commute_smul hUW I hw hO hΦ haQ hane hx'mid hj
        exact ⟨⟨c, (mem_cMa S k).mpr (by rw [← hka]; exact hc)⟩, by
          dsimp only
          rw [hτc]
          exact hpl⟩
    have hK : (MulAction.stabilizer (Equiv.Perm (Fin 75735)) (planeOf S φ c₀)).comap τ ≤
        (centralizer ({fK S k ψ (c₀ * S.z * c₀⁻¹)} : Set TD6)).comap σ := by
      intro c hc
      rw [mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, hτc] at hc
      have h : fK S k ψ (c₀ * S.z * c₀⁻¹) =
          σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) * (σ c)⁻¹ := by
        rw [hσc]
        exact fK_eq_conj_of_smul I hw hO hΦ hvQ hx'Q hx'ne hx'a c hx'Q hx'ne hc
      rw [mem_comap, mem_centralizer_singleton_iff]
      show σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) = fK S k ψ (c₀ * S.z * c₀⁻¹) * σ c
      calc σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) =
          (σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) * (σ c)⁻¹) * σ c := by group
        _ = fK S k ψ (c₀ * S.z * c₀⁻¹) * σ c := by rw [← h]
    have e1 := card_conj_orbit σ (fK S k ψ (c₀ * S.z * c₀⁻¹))
    rw [hr1] at e1
    have e2 := card_perm_orbit τ (planeOf S φ c₀)
    rw [hr2] at e2
    rw [← Nat.card_coe_set_eq, e1]
    have h41664 := ncard_mid_general hUW (planeOf S φ k⁻¹)
    rw [← Nat.card_coe_set_eq, e2] at h41664
    rw [← h41664]
    exact Subgroup.index_dvd_of_le hK
  have hts : ∀ u ∈ fK S k ψ '' {b | IsOm S k b}, ∀ E : Fin 75735, ¬ Opp E.val (u • E).val := by
    rintro _ ⟨b, hb, rfl⟩ E
    obtain ⟨h', rfl⟩ := isConj_iff.mp hb.1
    have hbM := conj_mem_M_of_commute S k hb.2.2.1
    have hyM : (k * h') * S.z * (k * h')⁻¹ ∈ S.M := by
      rwa [show k * (h' * S.z * h'⁻¹) * k⁻¹ = (k * h') * S.z * (k * h')⁻¹ by group] at hbM
    have hFy : fK S k ψ (h' * S.z * h'⁻¹) =
        ψ (rhoM S ⟨(k * h') * S.z * (k * h')⁻¹, hyM⟩) := by
      have e : (⟨k * (h' * S.z * h'⁻¹) * k⁻¹, hbM⟩ : S.M) =
          ⟨(k * h') * S.z * (k * h')⁻¹, hyM⟩ := Subtype.ext (by
        show k * (h' * S.z * h'⁻¹) * k⁻¹ = (k * h') * S.z * (k * h')⁻¹
        group)
      rw [fK_of_mem S k ψ hbM, e]
    have hyz : ¬ IsConj S.z ((k * h') * S.z * (k * h')⁻¹ * S.z) := by
      have := not_isConj_mul_z I hw hO hΦ hvQ hvne hb
      rwa [show k * (h' * S.z * h'⁻¹) * k⁻¹ = (k * h') * S.z * (k * h')⁻¹ by group] at this
    rw [hFy]
    exact not_opp_of_not_isConj hcl2 hiso hΦ hyM hyz E
  obtain ⟨p, -, hp⟩ := hUW.orbit_roots _ hne hO' h1 hinv hdvd hts
    (fK S k ψ (c₀ * S.z * c₀⁻¹)) ⟨_, hx'Om, rfl⟩
  exact ⟨p, by rw [← hF₀]; exact hp⟩


theorem acts_tv_of_mem_Qa (hUW : UWInput) (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)))
    (hcl2 : ∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = wtV i)
    {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) {k : G}
    (hv : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa g) :
    ∃ p : Fin 365211, Phi S φ ⟨g * S.z * g⁻¹, hxM⟩ = tvEquiv p.val := by
  have hvQ : k * S.z * k⁻¹ ∈ S.QG := hv.1
  have hvne : k * S.z * k⁻¹ ≠ S.z := fun h => z_not_mem_Qa S hxQ (h ▸ hv.2)
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq (planeOf S φ k) 0
  obtain ⟨m, hm⟩ := exists_rhoM_eq (ψ.symm g₀)
  have hψm : ψ (rhoM S m) = g₀ := by rw [hm, MulEquiv.apply_symm_apply]
  have hm' : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ =
      ((m : G) * g) * S.z * ((m : G) * g)⁻¹ := by group
  have hxM' : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.M := by
    rw [← hm']
    exact S.M.mul_mem (S.M.mul_mem m.2 hxM) (S.M.inv_mem m.2)
  have hxQ' : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∉ S.QG := by
    intro h
    apply hxQ
    rw [← hm'] at h
    have := S.conj_mem_QG (S.M.inv_mem m.2) h
    rwa [show (m : G)⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * (m : G)⁻¹⁻¹ =
      g * S.z * g⁻¹ by group] at this
  have hv' : ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ∈ S.QG ⊓ S.Qa ((m : G) * g) := by
    refine ⟨?_, ?_⟩
    · rw [show ((m : G) * k) * S.z * ((m : G) * k)⁻¹ =
        (m : G) * (k * S.z * k⁻¹) * (m : G)⁻¹ by group]
      exact S.conj_mem_QG m.2 hvQ
    · refine S.mem_Qa_mul_iff.mpr ?_
      have e : (m : G)⁻¹ * (((m : G) * k) * S.z * ((m : G) * k)⁻¹) * (m : G) =
          k * S.z * k⁻¹ := by group
      rw [e]
      exact hv.2
  have hk0 : φ (S.cl (((m : G) * k) * S.z * ((m : G) * k)⁻¹)) = wtV 0 := by
    rw [phi_cl_mul hΦ m hvQ, cl_eq_wtV_planeOf I hw hO hΦ hvQ hvne, rhoMod_wtV, hψm, hg₀]
    rfl
  obtain ⟨p', hp'⟩ := psi_eq_tvP_of_mem_Qa_zero hUW I hw hO hΦ hcl2 hxM' hxQ' hv' hk0
  have hxm' : (⟨(m : G) * g * S.z * ((m : G) * g)⁻¹, hxM'⟩ : S.M) =
      m * ⟨g * S.z * g⁻¹, hxM⟩ * m⁻¹ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group)
  have hPhi' : Phi S φ ⟨(m : G) * g * S.z * ((m : G) * g)⁻¹, hxM'⟩ = tvEquiv p'.val := by
    rw [hΦ, hp', rhoMod_tvP]
  rw [hxm', map_mul, map_mul, map_inv, hΦ m, hψm] at hPhi'
  refine ⟨((g₀⁻¹ : TD6) : Equiv.Perm (Fin 365211)) p', ?_⟩
  have := rhoMod_conj_tvEquiv g₀⁻¹ p'
  rw [← this, map_inv, ← hPhi']
  group

end Main

end CFSG.GF2Type.SmithTypeE.E7
