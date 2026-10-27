module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TrialityPoints
public import CFSG.LargeExtraspecial.S14SMKDelta32
public import CFSG.LargeExtraspecial.S11Alt4A
public import CFSG.GF2Type.Smith1980Orth.Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Tri

open CFSG CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.CGT.Timmesfeld75 CFSG.RankThree.OrthogonalInvolutions
open scoped MatrixGroups
open Subgroup Module QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_centralizer_le_mul (hM : Nat.card S.Mbar ∣ 1512) (h : G) :
    Nat.card (S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G) : Subgroup G) ≤
      8 * Nat.card (S.QG ⊓ S.Qa h : Subgroup G) := by
  set T := S.conjBy h
  have hTz : T.z = h * S.z * h⁻¹ := CFSG.LargeExtraspecial.Setting.conjBy_z S h
  have e : h⁻¹ * T.z * h⁻¹⁻¹ = S.z := by
    rw [hTz, inv_inv]
    group
  have hQa : T.Qa h⁻¹ = S.QG := CFSG.LargeExtraspecial.Setting.QG_eq_of_z_eq _ _ e
  have hL0 : T.L0 h⁻¹ = S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G) := by
    rw [CFSG.LargeExtraspecial.Setting.L0, hQa]
    rfl
  have hinf : T.QG ⊓ T.Qa h⁻¹ = S.QG ⊓ S.Qa h := by
    rw [hQa, inf_comm]
    rfl
  have hL2 : IsPGroup 2 (T.Lbar h⁻¹) := CFSG.LargeExtraspecial.S11.isPGroup_Lbar h⁻¹
  have hdvdM : Nat.card (T.Lbar h⁻¹) ∣ Nat.card T.Mbar := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (T.Lbar_le_Mbar h⁻¹)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd : Nat.card (T.Lbar h⁻¹) ∣ 1512 := by
    refine hdvdM.trans ?_
    rw [Nat.card_congr (S.mbarEquivConjBy h).toEquiv]
    exact hM
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hL2
  have h8dvd : 2 ^ m ∣ 8 := by
    rw [hm] at hdvd
    have h1512 : (1512 : ℕ) = 8 * 189 := by norm_num
    rw [h1512] at hdvd
    exact (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 189)).dvd_of_dvd_mul_right hdvd
  have h8 : Nat.card (T.Lbar h⁻¹) ≤ 8 := by
    rw [hm]
    exact Nat.le_of_dvd (by norm_num) h8dvd
  have hcard := T.card_Lbar_mul h⁻¹
  rw [hL0, hinf] at hcard
  calc Nat.card (S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G) : Subgroup G)
      = Nat.card (T.Lbar h⁻¹) * Nat.card (S.QG ⊓ S.Qa h : Subgroup G) := hcard.symm
    _ ≤ 8 * Nat.card (S.QG ⊓ S.Qa h : Subgroup G) := Nat.mul_le_mul_right _ h8

theorem mem_QG_of_isConj_of_mem_M (hM : Nat.card S.Mbar ∣ 1512) (hw : S.width = 4)
    (H : Hyp4 S g) (C : Cons311 S g) (hirr : ¬ S.IsReducible)
    (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3) (hno : S11.NoA2All S)
    {x : G} (hx : IsConj S.z x) (hxM : x ∈ S.M) : x ∈ S.QG := by
  by_contra hxQ
  obtain ⟨h, rfl⟩ := isConj_iff.mp hx
  set x := h * S.z * h⁻¹ with hxdef
  have hxc : IsConj S.z x := isConj_iff.mpr ⟨h, rfl⟩
  have hx2 : x * x = 1 := by
    rw [hxdef]
    calc (h * S.z * h⁻¹) * (h * S.z * h⁻¹) = h * (S.z * S.z) * h⁻¹ := by group
      _ = 1 := by rw [S.z_mul_z]; group
  have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have ht1 : S.ρ ⟨x, hxM⟩ ≠ 1 := fun h1 => hxQ ((S.ρ_eq_one_iff ⟨x, hxM⟩).mp h1)
  obtain ⟨v, hv, hvq⟩ := exists_q_ne_zero_of_ne_one hw H C hirr h8
    (t := S.ρ ⟨x, hxM⟩) (MonoidHom.mem_range.mpr ⟨⟨x, hxM⟩, rfl⟩) ht1
  set m := finrank (ZMod 2) (commSpace (S.rhoL hxM)) with hmdef
  rcases S.fourFive hxM hx2 hxQ with ⟨hA, hcard1, -⟩ | ⟨hBC, hcard2, -, hxz⟩ | ⟨hA3, hcard3, -, hzx⟩
  · exact hvq (hA.2.2.2.2 v hv)
  ·
    have hQ : Nat.card S.QG = 2 ^ 9 := by
      rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw]
    have hm4 : m ≤ 4 := by
      have h1 := finrank_commSpace_add_finrank_fixSpace (S.rhoL hxM)
      rw [S.finrank_Qt_eq_two_mul_width, hw] at h1
      have h2 := Submodule.finrank_mono
        (commSpace_le_fixSpace (S.rhoL_mul_self hxM hx2))
      omega
    have hCcard : Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) = 2 ^ (8 - m) := by
      have hpow : (2 : ℕ) ^ 9 = 2 ^ (m + 1) * 2 ^ (8 - m) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hQ, hpow] at hcard2
      exact (Nat.eq_of_mul_eq_mul_left (by positivity) hcard2).symm
    by_cases hJ : ∃ y ∈ S.QG ⊓ S.Qa h, y ∈ S.clPre (S.commQt x) ∧ y ≠ 1
    ·
      obtain ⟨y, hyD, hyJ, hy1⟩ := hJ
      have hyJ' : y ∈ (⁅zpowers x, S.QG⁆ : Subgroup G) := by
        rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2']
        exact hyJ
      have hyx : Commute x y :=
        (mem_centralizer_singleton_iff.mp (SMK.mem_centralizer_of_mem_Qa S hyD.2)).symm
      have hres := SMF.isConj_of_mem_J S hxM hxQ hy1 hyJ' hyx hyD.2
      have hxy : IsConj S.z y := by
        rcases hres with h | h
        · exact h
        · exact hxc.trans (hxz.trans h)
      have hyz : y ≠ S.z := fun hys => SMK.z_not_mem_Qa S hxQ (hys ▸ hyD.2)
      obtain ⟨k, hk⟩ := isConj_iff.mp hxy
      have hyQ : y ∈ S.QG := hyD.1
      have hzk : S.z ∈ S.Qa k := S.z_mem_Qa (g := k) (by rw [hk]; exact hyQ) (by rw [hk]; exact hyz)
      have hxQak : x ∈ S.Qa k := by
        refine S.mem_Qa_symm (g₁ := k) (g₂ := h) ?_ ?_
        · rw [hk]
          intro hyx
          refine hxQ ?_
          rwa [hxdef.trans hyx.symm]
        · rw [hk]
          exact hyD.2
      have hbQ : k⁻¹ * S.z * k ∈ S.QG := (SME.mem_Qa_iff S k S.z).mp hzk
      have hcQ : k⁻¹ * x * k ∈ S.QG := (SME.mem_Qa_iff S k x).mp hxQak
      have hb : IsConj S.z (k⁻¹ * S.z * k) := by
        refine isConj_iff.mpr ⟨k⁻¹, ?_⟩
        group
      have hc : IsConj S.z (k⁻¹ * x * k) :=
        hxc.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)
      have hbz : k⁻¹ * S.z * k ≠ S.z := by
        intro hbs
        apply hyz
        calc y = k * S.z * k⁻¹ := hk.symm
          _ = k * (k⁻¹ * S.z * k) * k⁻¹ := by rw [hbs]
          _ = S.z := by group
      have hcz : k⁻¹ * x * k ≠ S.z := by
        intro hcs
        apply hxQ
        have : x = k * S.z * k⁻¹ := by
          calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
            _ = k * S.z * k⁻¹ := by rw [hcs]
        rw [this, hk]
        exact hyQ
      have hcomm : x * S.z = S.z * x := S.z_comm hxM
      have hbc : (k⁻¹ * S.z * k) * (k⁻¹ * x * k) = (k⁻¹ * x * k) * (k⁻¹ * S.z * k) := by
        calc (k⁻¹ * S.z * k) * (k⁻¹ * x * k) = k⁻¹ * (S.z * x) * k := by group
          _ = k⁻¹ * (x * S.z) * k := by rw [← hcomm]
          _ = (k⁻¹ * x * k) * (k⁻¹ * S.z * k) := by group
      rcases eq_or_eq_mul_z_of_commute hw H C hirr h8 hno hb hc hbQ hcQ hbz hcz hbc with h | h
      · apply hxQ
        have hxeq : x = S.z := by
          have h' := congrArg (fun w => k * w * k⁻¹) h
          simpa [mul_assoc] using h'
        rw [hxeq]
        exact S.z_mem_QG
      · apply hxQ
        have hxeq : x = S.z * y := by
          have h' := congrArg (fun w => k * w * k⁻¹) h
          calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
            _ = k * ((k⁻¹ * S.z * k) * S.z) * k⁻¹ := by rw [h]
            _ = S.z * (k * S.z * k⁻¹) := by group
            _ = S.z * y := by rw [hk]
        rw [hxeq]
        exact S.QG.mul_mem S.z_mem_QG hyQ
    ·
      push Not at hJ
      have hD1 := SMK.finrank_clSub_Dl_le_one S hxM hxQ hJ
      have hDcard : Nat.card (S.QG ⊓ S.Qa h : Subgroup G) ≤ 2 := by
        rw [← SMK.card_clSub_Dl S hxQ, S.card_submodule]
        calc (2 : ℕ) ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa h)) ≤ 2 ^ 1 :=
              Nat.pow_le_pow_right (by norm_num) hD1
          _ = 2 := by norm_num
      have hB := card_centralizer_le_mul (S := S) hM h
      have hCle : Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 16 := by
        calc Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 8 * Nat.card (S.QG ⊓ S.Qa h : Subgroup G) := hB
          _ ≤ 8 * 2 := Nat.mul_le_mul_left 8 hDcard
          _ = 16 := by norm_num
      have hm4 : m = 4 := by
        have hle : 2 ^ (8 - m) ≤ 16 := by
          rw [← hCcard]
          exact hCle
        have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
        rw [h16] at hle
        have h84 : 8 - m ≤ 4 := Nat.pow_le_pow_iff_right (by norm_num) |>.mp hle
        omega
      have heq : S.commQt x = S.fixQt x := by
        refine Submodule.eq_of_le_of_finrank_eq (S.commQt_le_fixQt hxM hx2') ?_
        rw [S.commQt_of_mem hxM, S.fixQt_of_mem hxM]
        change finrank (ZMod 2) (commSpace (S.rhoL hxM)) =
          finrank (ZMod 2) (fixSpace (S.rhoL hxM))
        rw [← hmdef]
        have h1 := finrank_commSpace_add_finrank_fixSpace (S.rhoL hxM)
        rw [S.finrank_Qt_eq_two_mul_width, hw] at h1
        omega
      have hDsub : (S.QG ⊓ S.Qa h : Subgroup G) ≤ S.clPre (S.commQt x) := by
        intro d hd
        have hdKz : d ∈ (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) := SMK.Dl_le_Kz S hd
        refine S.mem_clPre.mpr ⟨hd.1, ?_⟩
        have hcl : S.cl d ∈ S.clSub (S.QG ⊓ centralizer ({x} : Set G)) :=
          S.cl_mem_clSub hdKz hdKz.1
        rw [heq]
        exact S.clSub_centralizer_le_fixQt hxM hcl
      have hDbot : (S.QG ⊓ S.Qa h : Subgroup G) = ⊥ := by
        rw [eq_bot_iff]
        intro d hd
        rw [hJ d hd (hDsub hd)]
        exact Subgroup.one_mem _
      have hDcard1 : Nat.card (S.QG ⊓ S.Qa h : Subgroup G) = 1 := by
        rw [hDbot]
        exact Subgroup.card_bot
      have h16 : Nat.card (S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) = 16 := by
        rw [hCcard, hm4]
        norm_num
      rw [← hxdef] at hB
      rw [h16, hDcard1] at hB
      norm_num at hB
  · exact hvq (hA3.2.2.2.2 v hv)

end CFSG.GF2Type.Smith1979.W4Tri
