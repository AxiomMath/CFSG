module

public import CFSG.GH74.GLS.C3.Layer1.Back93
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.Lemma12hc
public import CFSG.GH74.GLS.IVK.L2.Lemma12k
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.L2.Lemma14j

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.IVK

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem le_sylow_of_le_normalizer {X : Type} [Group X] [Finite X] (S : Sylow 2 X) {H : Subgroup X}
    (hH : IsPGroup 2 ↥H) (hN : H ≤ normalizer ((S : Subgroup X) : Set X)) : H ≤ (S : Subgroup X) := by
  have hsup : IsPGroup 2 ↥((S : Subgroup X) ⊔ H) :=
    S.isPGroup'.to_sup_of_normal_left' hH hN
  have := S.is_maximal' hsup le_sup_left
  rw [← this]
  exact le_sup_right

theorem sq_eq_one_of_isElementaryAbelian' {X : Type} [Group X] {E : Subgroup X}
    (hE : IsElementaryAbelian 2 ↥E) : ∀ x ∈ E, x * x = 1 := by
  intro x hx
  have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
  rwa [pow_two] at this

theorem comm_of_isElementaryAbelian' {X : Type} [Group X] {E : Subgroup X}
    (hE : IsElementaryAbelian 2 ↥E) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  intro x hx y hy
  exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

theorem exists_notation_field_inv (hF : L2Field F) (e : K ≃* L2 F) (B : Subgroup (MulAut K))
    (hB : IsPGroup 2 ↥B) (hSyl : IsSylowOf 2 (B ⊓ innAut K) (innAut K))
    (E : Subgroup (MulAut K)) (hEB : E ≤ B) (hE : IsElementaryAbelian 2 ↥E)
    (hE8 : 8 ≤ Nat.card ↥E) :
    ∃ (e' : K ≃* L2 F) (N : L2Notation e') (σ y p : MulAut K),
      B ≤ (N.T : Subgroup (MulAut K)) ∧ N.P = B ⊓ innAut K ∧ y ∈ E ∧ p ∈ B ⊓ innAut K ∧
      σ ∈ N.R ∧ orderOf σ = 2 ∧ σ = p⁻¹ * y ∧ σ ∉ innAut K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hBT'⟩ := hB.exists_le_sylow
  obtain ⟨e', N, hNT⟩ := ivk_1_2a_exists F hF K e T'
  have hBN : B ≤ (N.T : Subgroup (MulAut K)) := by rw [hNT]; exact hBT'
  have hPeq : N.P = B ⊓ innAut K := by
    have hNP2 : IsPGroup 2 ↥N.P := N.T.isPGroup'.to_inf_left
    exact hSyl.eq_of_le (inf_le_inf_right _ hBN) inf_le_right hNP2
  have hsq := sq_eq_one_of_isElementaryAbelian' hE
  have hcomm := comm_of_isElementaryAbelian' hE
  have hEnot : ¬ E ≤ innDiagSub e' := by
    intro hle
    have := card_le_four_of_le_inf e' hF N.T E (hEB.trans hBN) hle hcomm hsq
    omega
  obtain ⟨y, hyE, hyD⟩ : ∃ y ∈ E, y ∉ innDiagSub e' := by
    by_contra hcon
    push Not at hcon
    exact hEnot hcon
  have hy2 : y * y = 1 := hsq y hyE
  have hy1 : y ≠ 1 := fun h => hyD (h ▸ (innDiagSub e').one_mem)
  have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  set τ : F ≃+* F := fieldProj e' y with hτ
  have hτ1 : τ ≠ 1 := fun h => hyD ((mem_innDiagSub_iff e' y).2 h)
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul, hy2, map_one]
  set σ₀ : MulAut K := fieldAutHom e' τ with hσ₀
  have hσ₀F : σ₀ ∈ fieldAutSub e' := ⟨τ, rfl⟩
  have hσ₀proj : fieldProj e' σ₀ = τ := fieldProj_fieldAutHom e' τ
  have hσ₀1 : σ₀ ≠ 1 := fun h => hτ1 (by rw [← hσ₀proj, h, map_one])
  have hσ₀sq : σ₀ * σ₀ = 1 := by
    rw [hσ₀, ← map_mul, hτ2, map_one]
  have hσ₀ord : orderOf σ₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ₀sq) hσ₀1
  have hσ₀T : σ₀ ∈ (N.T : Subgroup (MulAut K)) := by
    have hH : IsPGroup 2 ↥(zpowers σ₀) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hσ₀ord, pow_one]
    have hN : zpowers σ₀ ≤ normalizer ((N.T : Subgroup (MulAut K)) : Set (MulAut K)) :=
      (zpowers_le).2 (N.T_inv hσ₀F)
    exact le_sylow_of_le_normalizer N.T hH hN (mem_zpowers σ₀)
  have hσ₀R : σ₀ ∈ N.R := ⟨hσ₀T, hσ₀F⟩
  have hyT : y ∈ (N.T : Subgroup (MulAut K)) := hBN (hEB hyE)
  have hinnle : innAut K ≤ innDiagSub e' := by
    have := (ivk_1_2d F hF K e' N).1
    rw [← this]
    exact le_sup_left
  have hcases := ivk_1_2i_c F hF K e' N σ₀ hσ₀R hσ₀ord y hyT hyord
  rcases hcases with h | ⟨h, -⟩ | ⟨p, hpP, hyp⟩
  · exact absurd (hinnle h.2) hyD
  · exact absurd h.2 hyD
  · have hpB : p ∈ B ⊓ innAut K := hPeq ▸ hpP
    have hσ₀D : σ₀ ∉ innDiagSub e' := fun h =>
      hτ1 (by rw [← hσ₀proj]; exact (mem_innDiagSub_iff e' σ₀).1 h)
    refine ⟨e', N, σ₀, y, p, hBN, hPeq, hyE, hpB, hσ₀R, hσ₀ord, ?_, fun h => hσ₀D (hinnle h)⟩
    rw [hyp]
    group

theorem mem_zpowers_of_mul_self {X : Type*} [Group X] {g w : X} (hg : g * g = 1)
    (hw : w ∈ zpowers g) : w = 1 ∨ w = g := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
  rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [sq, hg]
  · right
    rw [zpow_add_one, zpow_mul]
    simp [sq, hg]

omit [Finite K] in
theorem eq_one_of_mem_fieldAutSub_of_mem_innDiagSub (e : K ≃* L2 F) {x : MulAut K}
    (hx : x ∈ fieldAutSub e) (hd : x ∈ innDiagSub e) : x = 1 := by
  obtain ⟨τ, rfl⟩ := hx
  rw [mem_innDiagSub_iff, fieldProj_fieldAutHom] at hd
  rw [hd, map_one]

theorem fus_L2
    (h2hb : IVK_1_2h_b) (hF : L2Field F) {e' : K ≃* L2 F} (N : L2Notation e')
    (B : Subgroup (MulAut K)) (hPeq : N.P = B ⊓ innAut K) {σ z : MulAut K} (hσR : σ ∈ N.R)
    (hσ2 : orderOf σ = 2) (hzP : z ∈ N.P) (hz2 : orderOf z = 2)
    (hzc : ∀ q ∈ N.P, z * q = q * z)
    (hzu : ∀ w ∈ N.P, (∀ q ∈ N.P, w * q = q * w) → w = 1 ∨ w = z) :
    (∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut K → (∀ q ∈ B ⊓ innAut K, σ' * q = q * σ') →
      σ' = σ ∨ σ' = σ * z) ∧
    ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut K → (∀ q ∈ B ⊓ innAut K, σ' * q = q * σ') →
      ∀ u ∈ (B ⊓ innAut K) ⊔ zpowers σ', orderOf u = 2 →
        ∃ g ∈ innAut K, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = σ' ∨ g * u * g⁻¹ = σ' * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσσ : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ2, sq] at this
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hPσ : ∀ q ∈ N.P, σ * q = q * σ := fun q hq => (N.R_cent σ hσR hσ2 q hq).symm
  have hzσ : z * σ = σ * z := (hPσ z hzP).symm
  have hPinn : N.P ≤ innAut K := hPeq ▸ inf_le_right
  have hFσ : ∀ u ∈ N.P ⊔ zpowers σ, orderOf u = 2 →
      ∃ g ∈ innAut K, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = σ ∨ g * u * g⁻¹ = σ * z := by
    intro u hu hu2
    have hcomm : ∀ q ∈ N.P, ∀ w ∈ zpowers σ, q * w = w * q := by
      intro q hq w hw
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_right (show Commute q σ from (hPσ q hq).symm) j).eq
    obtain ⟨q, hq, w, hw, rfl⟩ := Back.exists_mul_of_mem_sup_of_commute hcomm hu
    rcases mem_zpowers_of_mul_self hσσ hw with hw1 | hwσ
    · rw [hw1, mul_one] at hu2 ⊢
      obtain ⟨g, hg, hgq⟩ := (ivk_1_2g F hF K e' N).1 q hq z hzP hu2 hz2
      exact ⟨g, hg, Or.inl hgq⟩
    · rw [hwσ] at hu2 ⊢
      by_cases hq1 : q = 1
      · subst hq1
        exact ⟨1, one_mem _, Or.inr (Or.inl (by simp))⟩
      · have hsq : (q * σ) * (q * σ) = 1 := by
          have := pow_orderOf_eq_one (q * σ)
          rwa [hu2, sq] at this
        have hqq : q * q = 1 := by
          have h1 : (q * σ) * (q * σ) = q * q * (σ * σ) := by
            calc (q * σ) * (q * σ) = q * (σ * q) * σ := by group
              _ = q * (q * σ) * σ := by rw [hPσ q hq]
              _ = q * q * (σ * σ) := by group
          rw [h1, hσσ, mul_one] at hsq
          exact hsq
        obtain ⟨h1, h2⟩ := h2hb F hF K e' N σ hσR hσ2 z hzP hz2 (fun x hx => (hzc x hx).symm)
        by_cases hq0 : q ∈ ((oResidual 2 ↥(fixedSubgroup K σ)).map (fixedSubgroup K σ).subtype).map
            (MulAut.conj : K →* MulAut K)
        · obtain ⟨g, hg, hgq⟩ := h1 q hq hq0 hq1 hu2
          exact ⟨g, hg, Or.inr (Or.inr hgq)⟩
        · obtain ⟨g, hg, hgq⟩ := h2 q hq hq0 hu2
          exact ⟨g, hg, Or.inr (Or.inl hgq)⟩
  obtain ⟨E, hEcyc, hEF, -, hcent, -, -⟩ := ivk_1_4j F hF K e' N
  have hEcentral : ∀ ε ∈ E, ∀ q ∈ N.P, q * ε = ε * q := by
    intro ε hε q hq
    have : ε ∈ centralizer (N.P : Set (MulAut K)) := by
      rw [hcent]
      exact Subgroup.mem_sup_right hε
    exact mem_centralizer_iff.1 this q hq
  have hZE : ∀ ζ ∈ (center ↥N.P).map N.P.subtype, ∀ ε ∈ E, ζ * ε = ε * ζ := by
    intro ζ hζ ε hε
    obtain ⟨ζ', _, rfl⟩ := hζ
    exact hEcentral ε hε ζ' ζ'.2
  have hdecomp : ∀ w ∈ centralizer (N.P : Set (MulAut K)), ∃ ζ ∈ N.P, (ζ = 1 ∨ ζ = z) ∧
      ∃ ε ∈ E, ζ * ε = ε * ζ ∧ w = ζ * ε := by
    intro w hw
    rw [hcent] at hw
    obtain ⟨ζ, hζ, ε, hε, rfl⟩ := Back.exists_mul_of_mem_sup_of_commute hZE hw
    have hcomm := hZE ζ hζ ε hε
    obtain ⟨ζ', hζ', rfl⟩ := hζ
    refine ⟨ζ', ζ'.2, hzu ζ' ζ'.2 (fun q hq => ?_), ε, hε, hcomm, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hζ' ⟨q, hq⟩).symm
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ2
    omega
  have hσE : σ ∈ E := by
    have hσc : σ ∈ centralizer (N.P : Set (MulAut K)) :=
      mem_centralizer_iff.2 fun q hq => (hPσ q hq).symm
    obtain ⟨ζ, hζP, hζ, ε, hε, -, hσeq⟩ := hdecomp σ hσc
    rcases hζ with h | h
    · rw [hσeq, h, one_mul]
      exact hε
    · exfalso
      have hzF : z ∈ fieldAutSub e' := by
        have h1 : z = σ * ε⁻¹ := by rw [← h, hσeq]; group
        rw [h1]
        exact (fieldAutSub e').mul_mem hσR.2 ((fieldAutSub e').inv_mem (hEF hε))
      have hzD : z ∈ innDiagSub e' := innAut_le_innDiagSub e' (hPinn hzP)
      have hz1 := eq_one_of_mem_fieldAutSub_of_mem_innDiagSub e' hzF hzD
      rw [hz1, orderOf_one] at hz2
      omega
  have hcls : ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut K →
      (∀ q ∈ B ⊓ innAut K, σ' * q = q * σ') → σ' = σ ∨ σ' = σ * z := by
    intro σ' hσ'B hσ'2 hσ'inn hσ'c
    have hσ'N : σ' ∈ centralizer (N.P : Set (MulAut K)) :=
      mem_centralizer_iff.2 fun q hq => (hσ'c q (hPeq ▸ hq)).symm
    obtain ⟨ζ, hζP, hζ, ε, hε, hζε, hσ'eq⟩ := hdecomp σ' hσ'N
    have hσ'σ' : σ' * σ' = 1 := by
      have := pow_orderOf_eq_one σ'
      rwa [hσ'2, sq] at this
    have hζζ : ζ * ζ = 1 := by
      rcases hζ with h | h
      · rw [h, one_mul]
      · rw [h]
        exact hzz
    have hεε : ε * ε = 1 := by
      have h1 : σ' * σ' = ζ * ζ * (ε * ε) := by
        rw [hσ'eq]
        calc ζ * ε * (ζ * ε) = ζ * (ε * ζ) * ε := by group
          _ = ζ * (ζ * ε) * ε := by rw [hζε]
          _ = ζ * ζ * (ε * ε) := by group
      rw [h1, hζζ, one_mul] at hσ'σ'
      exact hσ'σ'
    have hε1σ : ε = 1 ∨ ε = σ := by
      by_cases hε1 : ε = 1
      · exact Or.inl hε1
      · right
        have := hEcyc
        have h := DihedralAux.cyclic_unique_involution (G := ↥E) (a := ⟨ε, hε⟩) (b := ⟨σ, hσE⟩)
          (fun h => hε1 (congrArg Subtype.val h)) (fun h => hσ1 (congrArg Subtype.val h))
          (Subtype.ext hεε) (Subtype.ext hσσ)
        exact congrArg Subtype.val h
    rcases hζ with hζ | hζ <;> rcases hε1σ with hε | hε
    · exfalso
      rw [hσ'eq, hζ, hε, mul_one] at hσ'2
      rw [orderOf_one] at hσ'2
      omega
    · left
      rw [hσ'eq, hζ, hε, one_mul]
    · exfalso
      apply hσ'inn
      rw [hσ'eq, hζ, hε, mul_one]
      exact hPinn hzP
    · right
      rw [hσ'eq, hζ, hε, hzσ]
  refine ⟨hcls, ?_⟩
  intro σ' hσ'B hσ'2 hσ'inn hσ'c u hu hu2
  have hσ'cls := hcls σ' hσ'B hσ'2 hσ'inn hσ'c
  rcases hσ'cls with h | h
  · rw [h] at hu ⊢
    exact hFσ u (by rw [hPeq]; exact hu) hu2
  · have hle : (B ⊓ innAut K) ⊔ zpowers σ' ≤ N.P ⊔ zpowers σ := by
      refine sup_le (by rw [hPeq]; exact le_sup_left) ?_
      rw [zpowers_le, h]
      exact mul_mem (Subgroup.mem_sup_right (mem_zpowers σ)) (Subgroup.mem_sup_left hzP)
    obtain ⟨g, hg, hgu⟩ := hFσ u (hle hu) hu2
    refine ⟨g, hg, ?_⟩
    rcases hgu with h1 | h1 | h1
    · exact Or.inl h1
    · right
      right
      rw [h, h1, mul_assoc, hzz, mul_one]
    · right
      left
      rw [h]
      exact h1

omit [Finite F] [Finite K] in
theorem fieldAutHom_twist (e : K ≃* L2 F) (d : MulAut K) (τ : F ≃+* F) :
    fieldAutHom ((d : K ≃* K).trans e) τ = d⁻¹ * fieldAutHom e τ * d := by
  ext k
  simp [fieldAutHom, toPSL, MulAut.congr_symm_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem fa_L2 (hF : L2Field F) {e' : K ≃* L2 F} (N : L2Notation e') (B : Subgroup (MulAut K))
    (hPeq : N.P = B ⊓ innAut K) {σ z : MulAut K} (hσR : σ ∈ N.R) (hσ2 : orderOf σ = 2)
    (hzP : z ∈ N.P)
    (hcls : ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut K → (∀ q ∈ B ⊓ innAut K, σ' * q = q * σ') →
      σ' = σ ∨ σ' = σ * z) :
    ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ innAut K → (∀ q ∈ B ⊓ innAut K, σ' * q = q * σ') →
      ∃ e : K ≃* L2 F, σ' ∈ fieldAutSub e := by
  intro σ' hσ'B hσ'2 hσ'inn hσ'c
  have hPinn : N.P ≤ innAut K := hPeq ▸ inf_le_right
  rcases hcls σ' hσ'B hσ'2 hσ'inn hσ'c with h | h
  · exact ⟨e', by rw [h]; exact hσR.2⟩
  ·
    have hzσ : z * σ = σ * z := (N.R_cent σ hσR hσ2 z hzP)
    have hzσ2 : orderOf (z * σ) = 2 := by rw [hzσ, ← h]; exact hσ'2
    obtain ⟨d, hd, hdσ⟩ := ivk_1_2h_c F hF K e' N σ hσR hσ2 z
      (innAut_le_innDiagSub e' (hPinn hzP)) hzσ2
    obtain ⟨τ₀, hτ₀⟩ := hσR.2
    refine ⟨(d : K ≃* K).trans e', ⟨τ₀, ?_⟩⟩
    have hzσ' : z * σ = d⁻¹ * σ * d := by
      have h1 : z * σ = d⁻¹ * (d * (z * σ) * d⁻¹) * d := by group
      rw [hdσ] at h1
      exact h1
    rw [fieldAutHom_twist, hτ₀, h, ← hzσ]
    exact hzσ'.symm

theorem isSolvable_dihedral (z : ℕ) [NeZero z] : Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = z := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
    exact (Nat.eq_of_mul_eq_mul_right hz h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem solv_L2 (hF : L2Field F) (e : K ≃* L2 F) (k₀ : K) (hk₀ : orderOf k₀ = 2) :
    Group.IsSolvable ↥(centralizer ({k₀} : Set K)) := by
  have hq3 : 3 < Nat.card F := hF.2
  have hqodd : Odd (Nat.card F) := hF.1
  obtain ⟨ε, hε, hcong⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    have h4 : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
      obtain ⟨m, hm⟩ := hqodd
      omega
    rcases h4 with h | h
    · exact ⟨1, Or.inl rfl, by rw [Int.ModEq]; omega⟩
    · exact ⟨-1, Or.inr rfl, by rw [Int.ModEq]; omega⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
    ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by rcases hε with rfl | rfl <;> omega)⟩
  obtain ⟨-, hdih, -⟩ := ivk_1_3a F hF K e ε hε hcong d hd k₀ hk₀
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hdih
  have : NeZero k := ⟨by omega⟩
  have := isSolvable_dihedral k
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

@[expose] def GoodC (Kb : Type) [Group Kb] (σ : MulAut Kb) : Prop :=
  ∃ (Y : Type) (_ : Group Y) (_ : Finite Y), pPrimeCore 2 Y = ⊥ ∧
    (∃ Kh : Subgroup Y, IsComponent Kh) ∧ Nonempty (↥(fixedSubgroup Kb σ) ≃* Y)

end CFSG.GH74.GLS.C3.Layer1.Thm1
