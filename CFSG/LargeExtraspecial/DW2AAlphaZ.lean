module

public import CFSG.LargeExtraspecial.DW2AAlphaGamma
public import CFSG.LargeExtraspecial.OrthoF2PairsCases
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Alpha

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

omit [Finite G] in
theorem eq_of_finrank_le_one [FiniteDimensional (ZMod 2) S.Qt] {U : Submodule (ZMod 2) S.Qt}
    (hU : finrank (ZMod 2) U ≤ 1) {v v' : S.Qt} (hv : v ∈ U) (hv' : v' ∈ U) (hv0 : v ≠ 0)
    (hv'0 : v' ≠ 0) : v = v' := by
  have hspan : U = ZMod 2 ∙ v := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hv
    · rw [finrank_span_singleton hv0]
      exact hU
  rw [hspan] at hv'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv'
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul] at hv'0
    exact absurd rfl hv'0
  · rw [one_smul]

variable (hA : Hyp S W)
include hA

theorem exists_two_mem_Abar [IsSimpleGroup G] (h2 : 2 ≤ S.width) {h : G} (hx : IsDx S W h) :
    ∃ t₁ ∈ Abar S (S.clPre W) h, ∃ t₂ ∈ Abar S (S.clPre W) h, t₁ ≠ 1 ∧ t₂ ≠ 1 ∧ t₁ ≠ t₂ := by
  classical
  have hcard := card_Abar hA hx
  rw [S.card_submodule] at hcard
  have hm := hA.two_le_finrank h2
  have h4 : 4 ≤ Nat.card (Abar S (S.clPre W) h) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ finrank (ZMod 2) W := Nat.pow_le_pow_right (by norm_num) hm
  have : Finite (Abar S (S.clPre W) h) := Finite.of_injective _ Subtype.val_injective
  by_contra hcon
  push Not at hcon
  have hsub : ∀ t ∈ Abar S (S.clPre W) h, ∀ t' ∈ Abar S (S.clPre W) h, t ≠ 1 → t' ≠ 1 →
      t = t' := fun t ht t' ht' h1 h1' => hcon t ht t' ht' h1 h1'
  have hle : Nat.card (Abar S (S.clPre W) h) ≤ 2 := by
    by_cases hex : ∃ t₀ ∈ Abar S (S.clPre W) h, t₀ ≠ 1
    · obtain ⟨t₀, ht₀, ht₀1⟩ := hex
      have hsubset : ((Abar S (S.clPre W) h : Set S.O)) ⊆ {1, t₀} := by
        intro t ht
        by_cases ht1 : t = 1
        · exact Or.inl ht1
        · exact Or.inr (hsub t ht t₀ ht₀ ht1 ht₀1)
      calc Nat.card (Abar S (S.clPre W) h) = Nat.card ((Abar S (S.clPre W) h : Set S.O)) :=
            rfl
        _ ≤ Nat.card ({1, t₀} : Set S.O) := Nat.card_mono (Set.toFinite _) hsubset
        _ ≤ 2 := by
          rw [Nat.card_eq_card_toFinset, Set.toFinset_insert, Set.toFinset_singleton]
          exact Finset.card_insert_le _ _
    · push Not at hex
      have : Abar S (S.clPre W) h = ⊥ := eq_bot_iff.mpr fun t ht => hex t ht
      rw [this, card_bot]
      norm_num
  omega

theorem commSpace_le_Pspan {h : G} (hx : IsDx S W h) {t : S.O}
    (ht : t ∈ Abar S (S.clPre W) h) (ht1 : t ≠ 1) :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Pspan S W := by
  obtain ⟨htA, hxt⟩ := Abar_isTypeA hA hx ht ht1
  obtain ⟨b, hb, hbx⟩ := exists_adj hA hx
  set x := S.cl (h * S.z * h⁻¹)
  set c := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b with hc
  have hcC : c ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := sub_mem_commSpace _ b
  have htM : t ∈ S.Mbar := Abar_le_Mbar _ _ ht
  have htb : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) b ∈ Dset S W := by
    obtain ⟨m, rfl⟩ := htM
    exact ρ_mem_Dset hA m hb
  have hcP : c ∈ Pspan S W :=
    Submodule.mem_sup_left (sub_mem (Submodule.subset_span htb) (Submodule.subset_span hb))
  have hxP : x ∈ Pspan S W := Submodule.mem_sup_left (Submodule.subset_span ⟨h, hx, rfl⟩)
  have hbc : polar S.q b c = 0 := by
    have hcs := htA.2.2.2.2 c hcC
    have h1 : S.q ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) b) = S.q b := htA.1 b
    have e : b + c = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) b := by rw [hc]; abel
    rw [polar, e, h1, hcs, sub_self, sub_zero]
  have hbx' : polar S.q b x = 1 := by rw [polar_comm]; exact hbx
  have hcx : c ∉ ZMod 2 ∙ x := by
    intro hcx
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hcx
    rw [← hμ, polar_smul_right, hbx', smul_eq_mul, mul_one] at hbc
    rw [hbc, zero_smul] at hμ
    have htb' : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b := by
      rw [← sub_eq_zero]
      exact hμ.symm
    have hO := OrthoF2.mem_orthogonal_commSpace_iff S.q_nondegenerate t.2 |>.mpr htb'
    have := LinearMap.BilinForm.mem_orthogonal_iff.mp hO x hxt
    rw [QuadraticMap.polarBilin_apply_apply, polar_comm, hbx'] at this
    exact one_ne_zero this
  have hx0 : x ≠ 0 := hx.cl_ne_zero
  have hspan : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Submodule.span (ZMod 2) {x, c} := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hxt
      · exact hcC
    · rw [htA.2.2.2.1, finrank_span_pair_of_not_mem hx0 hcx]
  rw [hspan, Submodule.span_le]
  rintro _ (rfl | rfl)
  · exact hxP
  · exact hcP

theorem Xbar_sub_mem_Pspan {t : S.O} (ht : t ∈ Xbar S W) (v : S.Qt) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Pspan S W := by
  have hPinv := isMbarInvariant_Pspan hA
  have hinv : ∀ y ∈ Xbar S W, ∀ p ∈ Pspan S W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ Pspan S W := by
    intro y hy p hp
    obtain ⟨m, hm⟩ := Xbar_le_Mbar hy
    rw [← hm]
    exact hPinv m p hp
  induction ht using closure_induction generalizing v with
  | mem t ht =>
    obtain ⟨h, hx, ht⟩ := ht
    by_cases ht1 : t = 1
    · have e : ((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by rw [ht1]; rfl
      rw [e, sub_self]
      exact zero_mem _
    exact commSpace_le_Pspan hA hx ht ht1 (sub_mem_commSpace _ v)
  | one =>
    have e : ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := rfl
    rw [e, sub_self]
    exact zero_mem _
  | mul x y hx' hy' hx hy =>
    have e : ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) +
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
      rw [map_sub]
      change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - v = _
      abel
    rw [e]
    exact add_mem (hinv x hx' _ (hy v)) (hx v)
  | inv x hx' hx =>
    have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
        -(((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) := by
      rw [map_sub]
      have : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
        change ((x⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
        rw [inv_mul_cancel]
        rfl
      rw [this]
      abel
    rw [e]
    exact neg_mem (hinv _ ((Xbar S W).inv_mem hx') _ (hx v))

theorem fix_of_mem_centralizer [IsSimpleGroup G] (h2 : 2 ≤ S.width) {y : S.O}
    (hc : ∀ t ∈ Xbar S W, t * y = y * t) {h : G} (hx : IsDx S W h) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹) := by
  obtain ⟨t₁, ht₁, t₂, ht₂, h1, h2', h12⟩ := exists_two_mem_Abar hA h2 hx
  obtain ⟨hA₁, hx₁⟩ := Abar_isTypeA hA hx ht₁ h1
  obtain ⟨hA₂, hx₂⟩ := Abar_isTypeA hA hx ht₂ h2'
  set x := S.cl (h * S.z * h⁻¹)
  have hpres : ∀ t ∈ Xbar S W, ∀ v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro t ht v hv
    have e : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        (y : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      have h1 : y * t * y⁻¹ = t := by rw [← hc t ht]; group
      have := congrArg (fun u : S.O => (u : S.Qt ≃ₗ[ZMod 2] S.Qt)) h1
      simpa using this
    rw [← e, commSpace_conj]
    exact ⟨v, hv, rfl⟩
  have hy1 := hpres t₁ (Abar_le_Xbar hx ht₁) x hx₁
  have hy2 := hpres t₂ (Abar_le_Xbar hx ht₂) x hx₂
  have hne : commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    fun e => h12 (Subtype.ext (OrthoF2.eq_of_commSpace_eq S.q_nondegenerate hA₁ hA₂ e))
  have hdim : finrank (ZMod 2) (commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) : Submodule (ZMod 2) S.Qt) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have hle : commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hA₁.2.2.2.1]; omega)
    have hle' : commSpace (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        commSpace (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [hA₂.2.2.2.1]; omega)
    exact hne (hle.symm.trans hle')
  have hyx0 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) x ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact hx.cl_ne_zero
  exact eq_of_finrank_le_one hdim ⟨hy1, hy2⟩ ⟨hx₁, hx₂⟩ hyx0 hx.cl_ne_zero

theorem eq_one_of_mem_center [IsSimpleGroup G] (h2 : 2 ≤ S.width) {y : S.O}
    (hy : y ∈ Xbar S W) (hc : ∀ t ∈ Xbar S W, t * y = y * t) : y = 1 := by
  set Z : Subgroup S.O := Xbar S W ⊓ centralizer (Xbar S W : Set S.O) with hZ
  have hyZ : y ∈ Z := ⟨hy, mem_centralizer_iff.mpr hc⟩
  have hfixP : ∀ u ∈ Z, ∀ p ∈ Pspan S W, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
    intro u hu p hp
    have hcu : ∀ t ∈ Xbar S W, t * u = u * t := fun t ht => mem_centralizer_iff.mp hu.2 t ht
    have key : ∀ d ∈ Submodule.span (ZMod 2) (Dset S W), (u : S.Qt ≃ₗ[ZMod 2] S.Qt) d = d := by
      intro d hd
      induction hd using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨h, hx, rfl⟩ := hv
        exact fix_of_mem_centralizer hA h2 hcu hx
      | zero => exact map_zero _
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | smul c a _ ha => rw [map_smul, ha]
    obtain ⟨d, hd, w, hw, rfl⟩ := Submodule.mem_sup.mp hp
    rw [map_add, Xbar_fix hA hu.1 hw, key d hd]
  have hsq : ∀ u ∈ Z, u * u = 1 := by
    intro u hu
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    change (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
    have h1 := hfixP u hu _ (Xbar_sub_mem_Pspan hA hu.1 v)
    rw [map_sub] at h1
    have e : (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + (u : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [← h1]
      abel
    rw [e, sub_add_eq_add_sub, add_self_zmod2, zero_sub, neg_eq_iff_add_eq_zero,
      add_self_zmod2]
  have hZ2 : IsPGroup 2 Z := by
    intro u
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two]
    exact hsq u u.2
  have hZM : Z ≤ S.Mbar := inf_le_left.trans Xbar_le_Mbar
  have hnorm : S.Mbar ≤ normalizer (Z : Set S.O) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro u
    have hX := mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar hA hm)
    constructor
    · rintro ⟨huX, huC⟩
      refine ⟨(hX u).mp huX, mem_centralizer_iff.mpr fun t ht => ?_⟩
      have ht' : m⁻¹ * t * m ∈ Xbar S W := by
        have := (hX (m⁻¹ * t * m)).mpr (by simpa [mul_assoc] using ht)
        exact this
      have := mem_centralizer_iff.mp huC _ ht'
      calc t * (m * u * m⁻¹) = m * ((m⁻¹ * t * m) * u) * m⁻¹ := by group
        _ = m * (u * (m⁻¹ * t * m)) * m⁻¹ := by rw [this]
        _ = m * u * m⁻¹ * t := by group
    · rintro ⟨huX, huC⟩
      have hm' := mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar hA (S.Mbar.inv_mem hm))
      have hu : u = m⁻¹ * (m * u * m⁻¹) * m⁻¹⁻¹ := by group
      refine ⟨by rw [hu]; exact (hm' _).mp huX, mem_centralizer_iff.mpr fun t ht => ?_⟩
      have ht' : m * t * m⁻¹ ∈ Xbar S W := (hX t).mp ht
      have := mem_centralizer_iff.mp huC _ ht'
      calc t * u = m⁻¹ * ((m * t * m⁻¹) * (m * u * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * u * m⁻¹) * (m * t * m⁻¹)) * m := by rw [this]
        _ = u * t := by group
  have hZbot := S.s12_noNormalTwo_Mbar Z hZM hZ2 hnorm
  rw [hZbot, mem_bot] at hyZ
  exact hyZ

end Alpha

end CFSG.LargeExtraspecial.DW
