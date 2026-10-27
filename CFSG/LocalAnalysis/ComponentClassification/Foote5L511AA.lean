module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511W
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511S
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter CFSG.GH74.GLS.IVK.Lifted

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem dsdData_Q_of_mul_t_L511AA (hTS : Foote5TwoSubgroupOverInner) (h𝕊 : FooteSimpleType 𝕊)
    (hD : Foote5AutData 𝕊 Lin) (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hQ : 4 < Nat.card Q) (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T)
    (hsS : s ∉ S) (hz : z = s⁻¹ * t * s)
    (hRsQt : ∀ b ∈ conjugate (S ⊓ L) s, b ∈ Q ∨ b * t ∈ Q) : DSDData ↥Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hs'zs : s⁻¹ * z * s = t := by
    rw [hz]
    have h1 := h.tZ _ hss
    calc s⁻¹ * (s⁻¹ * t * s) * s = (s * s)⁻¹ * (t * (s * s)) := by group
      _ = (s * s)⁻¹ * ((s * s) * t) := by rw [← h1]
      _ = t := by group
  set Q' := conjugate Q s⁻¹ with hQ'def
  have hQ'S : Q' ≤ S := conjugate_le_of_mem_normalizer (inv_mem hsN) h.QS
  have hQQ' : Q ⊓ Q' = ⊥ := h.inf_conjugate_Q_inv_L513 hsT hz
  have hQ'N : Q' ≤ normalizer (L : Set G) := hQ'S.trans h.S_le
  have hzS := h.zS_mem
  have hz1 : actG L ε z = 1 := (h.actG_eq_one_iff_mem_Q ε hzS).mpr h.zQ
  have hRQ' : ∀ ρ ∈ S ⊓ L, ∃ ρ' ∈ Q', ρ' ∈ S ∧ actG L ε ρ' = actG L ε ρ ∧
      (ρ' = ρ ∨ ρ' = ρ * z) := by
    intro ρ hρ
    have hρS := (mem_inf.mp hρ).1
    have hmem : s⁻¹ * ρ * s ∈ conjugate (S ⊓ L) s := by
      rw [mem_conjugate_iff, show s * (s⁻¹ * ρ * s) * s⁻¹ = ρ by group]
      exact hρ
    rcases hRsQt _ hmem with h1 | h1
    · refine ⟨ρ, ?_, hρS, rfl, Or.inl rfl⟩
      rw [hQ'def, mem_conjugate_iff, inv_inv]
      exact h1
    · refine ⟨ρ * z, ?_, mul_mem hρS hzS, ?_, Or.inr rfl⟩
      · rw [hQ'def, mem_conjugate_iff, inv_inv,
          show s⁻¹ * (ρ * z) * s = s⁻¹ * ρ * s * (s⁻¹ * z * s) by group, hs'zs]
        exact h1
      · rw [actG_mul ε (h.S_le hρS) (h.S_le hzS), hz1, mul_one]
  let φ : ↥Q' →* MulAut 𝕊 :=
    { toFun := fun q => actG L ε q
      map_one' := actG_one ε
      map_mul' := fun a b => actG_mul ε (hQ'N a.2) (hQ'N b.2) }
  have hφ : ∀ q : ↥Q', φ q = actG L ε q := fun q => rfl
  have hker : ∀ q ∈ Q', actG L ε q = 1 → q = 1 := by
    intro q hq h1
    have h2 : q ∈ Q := (h.actG_eq_one_iff_mem_Q ε (hQ'S hq)).mp h1
    have h3 : q ∈ Q ⊓ Q' := mem_inf.mpr ⟨h2, hq⟩
    rwa [hQQ', mem_bot] at h3
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : actG L ε ((a : G)⁻¹ * b) = 1 := by
      rw [actG_mul ε (inv_mem (hQ'N a.2)) (hQ'N b.2), actG_inv ε (hQ'N a.2), ← hφ, ← hφ, hab,
        inv_mul_cancel]
    exact Subtype.ext (by
      have h2 := hker _ (mul_mem (inv_mem a.2) b.2) h1
      rw [inv_mul_eq_one] at h2
      exact h2)
  set P := φ.range with hPdef
  let eP : ↥Q' ≃* ↥P := MonoidHom.ofInjective hφinj
  have hmapeq : Q.map (MulAut.conj s).toMonoidHom = Q' := by
    rw [hQ'def, conjugate, inv_inv]
  let eQ : ↥Q ≃* ↥Q' := (Q.equivMapOfInjective _ (MulAut.conj s).injective).trans
    (MulEquiv.subgroupCongr hmapeq)
  have hP2 : IsPGroup 2 P := (h.isPGroup_S.to_le hQ'S).of_equiv eP
  have hRP : (h.Rbar ε : Subgroup 𝕊).map (MulAut.conj : 𝕊 →* MulAut 𝕊) ≤ P := by
    rintro _ ⟨ρ, hρ, rfl⟩
    obtain ⟨ρ₀, hρ₀R, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ
    obtain ⟨ρ', hρ'Q', -, hρ'act, -⟩ := hRQ' _ hρ₀R
    refine ⟨⟨ρ', hρ'Q'⟩, ?_⟩
    rw [hφ, hρ'act, actG_of_mem_self ε ρ₀.2]
  rcases hTS 𝕊 h𝕊 (h.Rbar ε) P hP2 hRP with ⟨-, hshape⟩ | ⟨β, hβP, hβ2, hβinn, R', hR'⟩
  · refine dsdData_of_dihedral_or_semidihedral_L512 ?_ hQ
    rcases hshape with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
    · exact Or.inl ⟨n, hn, ⟨(eQ.trans eP).trans f⟩⟩
    · exact Or.inr ⟨n, hn, ⟨(eQ.trans eP).trans f⟩⟩
  · exfalso
    obtain ⟨⟨q₀, hq₀⟩, rfl⟩ := hβP
    rw [hφ] at hβ2 hβinn hR'
    have hq₀S := hQ'S hq₀
    have hq₀N := h.S_le hq₀S
    have hβlin : actG L ε q₀ ∉ Lin := by
      intro hlin
      have hmap : (R' : Subgroup 𝕊).map (actG L ε q₀).toMonoidHom = R' := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [MulEquiv.coe_toMonoidHom, hR' y hy]
          exact hy
        · intro hx
          exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, hR' x hx]⟩
      have h1 := hD.pgl_fixed R' _ hlin hβinn hβ2 hmap
      have h2 : (R' : Subgroup 𝕊) ≤ (R' : Subgroup 𝕊) ⊓
          MonoidHom.eqLocus (actG L ε q₀).toMonoidHom (MonoidHom.id 𝕊) :=
        fun x hx => mem_inf.mpr ⟨hx, hR' x hx⟩
      have h3 := card_le_of_le h2
      have h4 : Nat.card (R' : Subgroup 𝕊) = Nat.card (h.Rbar ε : Subgroup 𝕊) := by
        rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
      have h8 := h.eight_le_card_R hna
      rw [← h.card_Rbar ε] at h8
      omega
    obtain ⟨ρ₀', hρ₀', -, hact⟩ := hD.field_inner (h.Rbar ε) _ hβlin hβ2
      (h.actG_map_Rbar ε hq₀S)
    obtain ⟨ρ₁', hρ₁R, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ₀'
    set ρ₁ : G := (ρ₁' : G) with hρ₁
    have hρ₁L : ρ₁ ∈ L := ρ₁'.2
    have hρ₁S := (mem_inf.mp hρ₁R).1
    have hρ₁N := h.S_le hρ₁S
    obtain ⟨ρ₂, hρ₂Q', hρ₂S, hρ₂act, -⟩ := hRQ' _ hρ₁R
    have hρ₂N := h.S_le hρ₂S
    set y := q₀ * ρ₂⁻¹ with hy
    have hyQ' : y ∈ Q' := mul_mem hq₀ (inv_mem hρ₂Q')
    have hyS := hQ'S hyQ'
    have hyN := h.S_le hyS
    have hyact : actG L ε y = actG L ε q₀ * (actG L ε ρ₁)⁻¹ := by
      rw [hy, actG_mul ε hq₀N (inv_mem hρ₂N), actG_inv ε hρ₂N, hρ₂act]
    have hyfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε y ρ = ρ := by
      intro ρ hρ
      have hψ : psi L ε ρ₁' ∈ (h.Rbar ε : Subgroup 𝕊) := hρ₀'
      have hmem : (psi L ε ρ₁')⁻¹ * ρ * psi L ε ρ₁' ∈ (h.Rbar ε : Subgroup 𝕊) :=
        mul_mem (mul_mem (inv_mem hψ) hρ) hψ
      rw [hyact, actG_of_mem_self ε hρ₁L]
      simp only [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
      rw [show (⟨ρ₁, hρ₁L⟩ : L) = ρ₁' from rfl, map_inv, hact _ hmem]
      group
    have hyR := (h.actG_fix_iff ε hyS).mp hyfix
    have hylin : actG L ε y ∉ Lin := fun h1 => hβlin (by
      have h2 : actG L ε q₀ = actG L ε y * actG L ε ρ₁ := by rw [hyact, inv_mul_cancel_right]
      rw [h2]
      exact mul_mem h1 (hD.inn_le (by rw [actG_of_mem_self ε hρ₁L]; exact ⟨_, rfl⟩)))
    have hyy : y * y = 1 := by
      have hC : actG L ε y * actG L ε y = 1 := by
        set C := S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) with hCdef
        have hCN : C ≤ normalizer (L : Set G) := inf_le_left.trans h.S_le
        have hP2' : IsPGroup 2 (actImage L ε C) := isPGroup_actImage ε (h.isPGroup_S.to_le
          inf_le_left)
        have hfixC : ∀ α ∈ actImage L ε C, ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
          intro α hα
          obtain ⟨c, hc, rfl⟩ := (mem_actImage ε hCN).mp hα
          exact (h.actG_fix_iff ε (mem_inf.mp hc).1).mpr fun ρ' hρ' =>
            (mem_centralizer_iff.mp (mem_inf.mp hc).2 ρ' hρ').symm
        have hyC : y ∈ C := mem_inf.mpr ⟨hyS, mem_centralizer_iff.mpr fun ρ hρ =>
          (hyR ρ hρ).symm⟩
        exact (hD.centralizer_sylow (h.Rbar ε) _ hP2' hfixC).1 _
          (actG_mem_actImage ε hCN hyC)
      exact hker _ (mul_mem hyQ' hyQ') (by rw [actG_mul ε hyN hyN, hC])
    obtain ⟨x, hxR, hx2, ρ, hρR, hxρ⟩ := h.exists_noncentral_involution_R hna
    obtain ⟨x', hx'Q', hx'S, hx'act, hx'x⟩ := hRQ' _ hxR
    have ht2 := h.t_mul_self
    have hxS := (mem_inf.mp hxR).1
    have hzx : z * x = x * z := (h.zS x hxS).symm
    have hzL : z ∉ L := fun h1 => by
      have h2 : z ∈ Q ⊓ L := mem_inf.mpr ⟨h.zQ, h1⟩
      rw [h.Q_inf_L, mem_bot] at h2
      have h3 := h.z2
      rw [h2, orderOf_one] at h3
      omega
    have hx'2 : x' * x' = 1 := by
      rcases hx'x with h1 | h1 <;> rw [h1]
      · exact hx2
      · rw [show x * z * (x * z) = x * (z * x) * z by group, hzx,
          show x * (x * z) * z = (x * x) * (z * z) by group, hx2, h.z_mul_self, one_mul]
    have hx't : x' * t = t * x' := h.tZ x' hx'S
    have hx'1 : x' ≠ 1 := by
      rcases hx'x with h1 | h1 <;> rw [h1]
      · exact fun h2 => hxρ (by rw [h2, one_mul, mul_one])
      · intro h2
        apply hzL
        rw [show z = x⁻¹ by rw [← mul_eq_one_iff_inv_eq.mp h2]]
        exact inv_mem (mem_inf.mp hxR).2
    have hx'tne : x' ≠ t := by
      rcases hx'x with h1 | h1 <;> rw [h1]
      · exact fun h2 => hxρ (by rw [h2]; exact h.tZ ρ (mem_inf.mp hρR).1)
      · intro h2
        apply hzL
        rw [show z = x⁻¹ * t by rw [← h2]; group]
        exact mul_mem (inv_mem (mem_inf.mp hxR).2) h.tL
    have htQ' : t ∈ Q' := t_mem_conjugate_Q_L513 h.zQ hz
    set V := kleinFourOfCommutingInvolutions x' t hx'2 ht2 hx't with hVdef
    have hV4 : Nat.card V = 4 :=
      (isKleinFour_kleinFourOfCommutingInvolutions x' t hx'2 ht2 hx'1 h.t_ne_one hx'tne
        hx't).card_four
    have hVQ' : V ≤ Q' := fun v hv => by
      rcases (mem_kleinFour_iff hx'2 ht2 hx't).mp hv with h1 | h1 | h1 | h1 <;> rw [h1]
      · exact mul_mem hx'Q' htQ'
      · exact hx'Q'
      · exact htQ'
      · exact one_mem _
    have hVinn : ∀ v ∈ V, actG L ε v ∈ innAut5 𝕊 := fun v hv => by
      have hx'inn : actG L ε x' ∈ innAut5 𝕊 := by
        rw [hx'act, actG_of_mem_self ε (mem_inf.mp hxR).2]
        exact ⟨_, rfl⟩
      have htinn : actG L ε t ∈ innAut5 𝕊 := by
        rw [actG_of_mem_self ε h.tL]
        exact ⟨_, rfl⟩
      rcases (mem_kleinFour_iff hx'2 ht2 hx't).mp hv with h1 | h1 | h1 | h1 <;> rw [h1]
      · rw [actG_mul ε (h.S_le hx'S) (h.S_le h.tS)]
        exact mul_mem hx'inn htinn
      · exact hx'inn
      · exact htinn
      · rw [actG_one]
        exact one_mem _
    have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
      rcases (mem_kleinFour_iff hx'2 ht2 hx't).mp hv with h1 | h1 | h1 | h1 <;> rw [h1]
      · rw [show x' * t * (x' * t) = x' * (t * x') * t by group, ← hx't,
          show x' * (x' * t) * t = (x' * x') * (t * t) by group, hx'2, ht2, one_mul]
      · exact hx'2
      · exact ht2
      · exact one_mul 1
    have hyx' : y * x' = x' * y := by
      rcases hx'x with h1 | h1 <;> rw [h1]
      · exact hyR x hxR
      · rw [← mul_assoc, hyR x hxR, mul_assoc, (h.zS y hyS), mul_assoc]
    have hVy : ∀ v ∈ V, ∀ w ∈ zpowers y, v * w = w * v := by
      intro v hv w hw
      rcases eq_one_or_eq_of_mem_zpowers_sq hyy hw with h1 | h1 <;> rw [h1]
      · rw [mul_one, one_mul]
      · rcases (mem_kleinFour_iff hx'2 ht2 hx't).mp hv with h2 | h2 | h2 | h2 <;> rw [h2]
        · rw [mul_assoc, ← h.tZ y hyS, ← mul_assoc, ← hyx', mul_assoc]
        · exact hyx'.symm
        · exact (h.tZ y hyS).symm
        · rw [one_mul, mul_one]
    have hdisj : V ⊓ zpowers y = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rcases eq_one_or_eq_of_mem_zpowers_sq hyy (mem_inf.mp hw).2 with h1 | h1
      · rw [h1]; exact one_mem _
      · exfalso
        apply hylin
        rw [← h1]
        exact hD.inn_le (hVinn w (mem_inf.mp hw).1)
    have hy1 : y ≠ 1 := fun h1 => hylin (by rw [h1, actG_one]; exact one_mem _)
    have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
    have h8 : Nat.card ↥(V ⊔ zpowers y) = 8 := by
      rw [card_sup_eq_mul_of_disjoint_of_le_normalizer V (zpowers y)
        (le_normalizer_of_commute hVy) (disjoint_iff.mpr hdisj), hV4, Nat.card_zpowers, hyo]
    have hEQ' : V ⊔ zpowers y ≤ Q' := sup_le hVQ' (zpowers_le.mpr hyQ')
    have hEsq : ∀ w ∈ V ⊔ zpowers y, w ^ 2 = 1 := fun w hw => by
      rw [sq]
      exact sq_eq_one_of_mem_sup hVsq (fun w hw => by
        rcases eq_one_or_eq_of_mem_zpowers_sq hyy hw with h1 | h1 <;> rw [h1]
        · exact one_mul 1
        · exact hyy) hVy hw
    set F := conjugate (V ⊔ zpowers y) s with hFdef
    have hFQ : F ≤ Q := fun w hw => by
      rw [hFdef, mem_conjugate_iff] at hw
      have h1 := hEQ' hw
      rw [hQ'def, mem_conjugate_iff] at h1
      rwa [show s⁻¹ * (s * w * s⁻¹) * s⁻¹⁻¹ = w by group] at h1
    have hFsq : ∀ w ∈ F, w ^ 2 = 1 := fun w hw => by
      rw [hFdef, mem_conjugate_iff] at hw
      have h1 := hEsq _ hw
      rw [sq] at h1 ⊢
      calc w * w = s⁻¹ * ((s * w * s⁻¹) * (s * w * s⁻¹)) * s := by group
        _ = 1 := by rw [h1]; group
    have h3 := Foote47.three_le_pRank_of_card_eight hFQ hFsq
      (by rw [hFdef, card_conjugate_eq_card, h8])
    rw [h.pRank_Q] at h3
    omega

end Sec5

theorem foote5DiagonalNotInQ_of_inputs
    (hMW : MacWilliamsStatement)
    (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups) : Foote5DiagonalNotInQ := by
  intro G _ _ L₀ L Q S T z t h hAut hna hQ hCt hT2 s hsT hsS r hr hr2 hrtQ
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  obtain ⟨h', hRR⟩ := h.repoint_conj_t_of_lemmas ε hD hna hCt hT2 hsT hsS
  obtain ⟨ε'⟩ := h'.quotient_simple.2
  rw [← hRR] at hna hr
  have h𝕊 := h'.sec4.footeFamilyType
  rcases h'.cases_of_not_le_Q ε' hD hna hCt hT2 hsT hsS with ⟨x, hx, hx2, hxlin⟩ | hcase
  · obtain ⟨E, hES, hTE, hEsq, hE8, htE, hzE⟩ := h'.exists_normal_e8_zt ε' hMW hGH hKG hD hna hCt
      hT2 hsT hsS
    exact h'.false_of_field_involution ε' foote5FieldCentralizerC_holds h𝕊 hD hna hQ hT2 hsT hsS
      rfl hx hx2 hxlin hES hTE hEsq hE8 htE hzE
  · have hDQ := h'.dsdData_Q_of_mul_t_L511AA ε' foote5TwoSubgroupOverInner_holds h𝕊 hD hna hQ hT2
      hsT hsS rfl hcase
    obtain ⟨hb2, hb1, hbz, T', hT'2, hT'C, hT'card⟩ :=
      h'.exists_sylow_centralizer_diag_L511V ε' hD hna hT2 hsT hsS rfl hr hr2 hrtQ
    exact h'.false_of_card_le_four_L511W ε' hrtQ hb2 hb1 hbz
      (fun W hW2 hWC hWz hWb hbW => h'.card_le_four_of_dsd_Q_L511W hDQ hb2 hb1 hbz hW2 hWC hWz
        hWb hbW) hT'2 hT'C hT'card

end CFSG.ComponentClassification.Foote5
