module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511R
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsE
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoSub
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LieType.SteinbergBRSmallAltSylow

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem lemma511iii_of_lemmas (hTS : Foote5TwoSubgroupOverInner) (h𝕊 : FooteSimpleType 𝕊)
    (hD : Foote5AutData 𝕊 Lin) (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hQ : 4 < Nat.card Q) (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T)
    (hsS : s ∉ S) (hRsQ : conjugate (S ⊓ L) s ≤ Q) :
    (AschbacherTheorem3.IsDihedralTwoGroup Q ∨ AschbacherTheorem3.IsSemidihedralTwoGroup Q) ∧
      Nat.card Q ≤ 2 * Nat.card (conjugate (S ⊓ L) s) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  set Q' := conjugate Q s⁻¹ with hQ'def
  have hRQ' : S ⊓ L ≤ Q' := fun ρ hρ => by
    rw [hQ'def, mem_conjugate_iff]
    refine hRsQ ?_
    rw [mem_conjugate_iff, show s * (s⁻¹ * ρ * s⁻¹⁻¹) * s⁻¹ = ρ by group]
    exact hρ
  have hQ'S : Q' ≤ S := conjugate_le_of_mem_normalizer (inv_mem hsN) h.QS
  have hne : conjugate Q 1 ≠ conjugate Q s⁻¹ := by
    intro h1
    rw [conjugate_one] at h1
    have h2 := mem_normalizer_of_conjugate_eq h1.symm
    exact h.not_mem_normalizer_Q hsT hsS (by simpa using inv_mem h2)
  have hQQ' : Q ⊓ Q' = ⊥ := by
    have h1 := (h.lemma58 hQ (one_mem T) (inv_mem hsT) hne).1
    rwa [conjugate_one] at h1
  have hQ'N : Q' ≤ normalizer (L : Set G) := hQ'S.trans h.S_le
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
    refine ⟨⟨ρ₀, hRQ' hρ₀R⟩, ?_⟩
    rw [hφ, actG_of_mem_self ε ρ₀.2]
  have hcardQ : Nat.card Q = Nat.card P := (Nat.card_congr (eQ.trans eP).toEquiv)
  rcases hTS 𝕊 h𝕊 (h.Rbar ε) P hP2 hRP with ⟨hcard, hshape⟩ | ⟨β, hβP, hβ2, hβinn, R', hR'⟩
  · refine ⟨?_, ?_⟩
    · rcases hshape with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
      · exact Or.inl ⟨n, hn, ⟨(eQ.trans eP).trans f⟩⟩
      · exact Or.inr ⟨n, hn, ⟨(eQ.trans eP).trans f⟩⟩
    · rw [hcardQ, card_conjugate_eq_card, ← h.card_Rbar ε]
      exact hcard
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
    set y := q₀ * ρ₁⁻¹ with hy
    have hyQ' : y ∈ Q' := mul_mem hq₀ (inv_mem (hRQ' hρ₁R))
    have hyS := hQ'S hyQ'
    have hyN := h.S_le hyS
    have hyfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε y ρ = ρ := by
      intro ρ hρ
      have hψ : psi L ε ρ₁' ∈ (h.Rbar ε : Subgroup 𝕊) := hρ₀'
      have hmem : (psi L ε ρ₁')⁻¹ * ρ * psi L ε ρ₁' ∈ (h.Rbar ε : Subgroup 𝕊) :=
        mul_mem (mul_mem (inv_mem hψ) hρ) hψ
      rw [hy, actG_mul ε hq₀N (inv_mem hρ₁N), actG_inv ε hρ₁N, actG_of_mem_self ε hρ₁L]
      simp only [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
      rw [show (⟨ρ₁, hρ₁L⟩ : L) = ρ₁' from rfl, map_inv, hact _ hmem]
      group
    have hyR := (h.actG_fix_iff ε hyS).mp hyfix
    have hyact : actG L ε y ∉ Lin := fun h1 => hβlin (by
      have h2 : actG L ε q₀ = actG L ε y * actG L ε ρ₁ := by
        rw [← actG_mul ε hyN hρ₁N, hy, inv_mul_cancel_right]
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
    have ht2 := h.t_mul_self
    have hxt : x * t = t * x := h.tZ x (mem_inf.mp hxR).1
    have hx1 : x ≠ 1 := fun h1 => hxρ (by rw [h1, one_mul, mul_one])
    have hxtne : x ≠ t := fun h1 => hxρ (by rw [h1]; exact h.tZ ρ (mem_inf.mp hρR).1)
    set V := kleinFourOfCommutingInvolutions x t hx2 ht2 hxt with hVdef
    have hV4 : Nat.card V = 4 :=
      (isKleinFour_kleinFourOfCommutingInvolutions x t hx2 ht2 hx1 h.t_ne_one hxtne hxt).card_four
    have hVR : V ≤ S ⊓ L := fun v hv => by
      rcases (mem_kleinFour_iff hx2 ht2 hxt).mp hv with h1 | h1 | h1 | h1 <;> rw [h1]
      · exact mul_mem hxR h.tR
      · exact hxR
      · exact h.tR
      · exact one_mem _
    have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
      rcases (mem_kleinFour_iff hx2 ht2 hxt).mp hv with h1 | h1 | h1 | h1 <;> rw [h1]
      · rw [show x * t * (x * t) = x * (t * x) * t by group, ← hxt,
          show x * (x * t) * t = (x * x) * (t * t) by group, hx2, ht2, one_mul]
      · exact hx2
      · exact ht2
      · exact one_mul 1
    have hVy : ∀ v ∈ V, ∀ w ∈ zpowers y, v * w = w * v := by
      intro v hv w hw
      rcases eq_one_or_eq_of_mem_zpowers_sq hyy hw with h1 | h1 <;> rw [h1]
      · rw [mul_one, one_mul]
      · exact (hyR v (hVR hv)).symm
    have hdisj : V ⊓ zpowers y = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rcases eq_one_or_eq_of_mem_zpowers_sq hyy (mem_inf.mp hw).2 with h1 | h1
      · rw [h1]; exact one_mem _
      · exfalso
        apply hyact
        rw [← h1, actG_of_mem_self ε (mem_inf.mp (hVR (mem_inf.mp hw).1)).2]
        exact hD.inn_le ⟨_, rfl⟩
    have hy1 : y ≠ 1 := fun h1 => hyact (by rw [h1, actG_one]; exact one_mem _)
    have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
    have h8 : Nat.card ↥(V ⊔ zpowers y) = 8 := by
      rw [card_sup_eq_mul_of_disjoint_of_le_normalizer V (zpowers y)
        (le_normalizer_of_commute hVy) (disjoint_iff.mpr hdisj), hV4, Nat.card_zpowers, hyo]
    have hEQ' : V ⊔ zpowers y ≤ Q' := sup_le (hVR.trans hRQ') (zpowers_le.mpr hyQ')
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

end CFSG.ComponentClassification.Foote5
