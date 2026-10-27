module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoCfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE

section Gen

variable {Q : Type} [Group Q] {Φ : Set (Subgroup Q)}

theorem AECover.map_eq_zBar (D : AECover Q Φ) {L : Subgroup Q} (hL : L ∈ Φ) {α : Finset (Fin 6)} {h : α.card = 4}
    {b : Bool} (hlab : L.map D.φ = memBar α h b) {u : Q} (hu : IsUniqueInvolution L u) :
    D.φ u = zBar α h := by
  have hmem : D.φ u ∈ memBar α h b := by
    rw [← hlab]
    exact ⟨u, hu.mem, rfl⟩
  have hsq : D.φ u * D.φ u = 1 := by
    rw [← map_mul, hu.sq, map_one]
  rcases eq_of_mem_memBar_mul_self (by norm_num : 5 ≤ 6) hmem hsq with h1 | h1
  · exfalso
    apply hu.ne_one
    exact D.inj L hL u hu.mem 1 L.one_mem (by rw [h1, map_one])
  · exact h1

theorem AECover.center_card (D : AECover Q Φ) : Nat.card (Subgroup.center Q) ≤ 2 := by
  rw [← D.toAEData.ker_eq_center]
  exact D.ker_card

theorem AECover.eq_of_central_involutions [Finite Q] (D : AECover Q Φ) {a b : Q}
    (ha : a ∈ Subgroup.center Q) (hb : b ∈ Subgroup.center Q)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have hcard := AECover.center_card D
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hza : Subgroup.zpowers a = Subgroup.center Q :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha) (by
      rw [Nat.card_zpowers, hord]
      exact hcard)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hza ▸ hb)
  rw [← zpow_mod_orderOf, hord] at hk
  push_cast at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk
    exact absurd hk.symm hb1
  · rw [h1, zpow_one] at hk
    exact hk


theorem AECover.map_twin_mem (D : AECover Q Φ) {σ : Q ≃* Q}
    (hσΦ : ∀ L ∈ Φ, L.map σ.toMonoidHom ∈ Φ) {z₀ : Q} (hσz : σ z₀ = z₀) {A A' : Subgroup Q}
    (hA : A ∈ Φ) (hA' : A' ∈ Φ) {β : Finset (Fin 6)} {hβ : β.card = 4} {b₀ : Bool}
    (hlA : A.map D.φ = memBar β hβ b₀) (hlA' : A'.map D.φ = memBar β hβ (!b₀))
    (hz : D.φ z₀ = zBar β hβ) {L : Subgroup Q} (hL : L = A ∨ L = A') (hzL : z₀ ∈ L) :
    L.map σ.toMonoidHom = A ∨ L.map σ.toMonoidHom = A' := by
  have hLΦ : L ∈ Φ := by
    rcases hL with rfl | rfl
    · exact hA
    · exact hA'
  have hσL := hσΦ L hLΦ
  obtain ⟨β', hβ', b', hlab⟩ := D.label _ hσL
  have hmem : D.φ z₀ ∈ memBar β' hβ' b' := by
    rw [← hlab]
    exact ⟨σ z₀, ⟨z₀, hzL, rfl⟩, congrArg D.φ hσz⟩
  have hsq : D.φ z₀ * D.φ z₀ = 1 := by
    rw [hz]
    exact zBar_mul_self β hβ
  rcases eq_of_mem_memBar_mul_self (by norm_num : 5 ≤ 6) hmem hsq with h1 | h1
  · exact absurd (hz.symm.trans h1) (zBar_ne_one (by norm_num) β hβ)
  · have hββ' : β = β' := eq_of_zBar_eq (by norm_num : (6 : ℕ) ≠ 8) (hz.symm.trans h1)
    subst hββ'
    by_cases hb : b' = b₀
    · subst hb
      left
      exact D.label_inj _ hσL _ hA (hlab.trans hlA.symm)
    · right
      have hb' : b' = !b₀ := by cases b' <;> cases b₀ <;> simp_all
      subst hb'
      exact D.label_inj _ hσL _ hA' (hlab.trans hlA'.symm)

theorem AECover.isPGroup_twin_sup (D : AECover Q Φ) {A A' : Subgroup Q} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    {β : Finset (Fin 6)} {hβ : β.card = 4} {b₀ : Bool} (hlA : A.map D.φ = memBar β hβ b₀)
    (hlA' : A'.map D.φ = memBar β hβ (!b₀)) : IsPGroup 2 (A ⊔ A' : Subgroup Q) := by
  have h2 : ∀ L ∈ Φ, IsPGroup 2 L := fun L hL => IsPGroup.of_card (n := 3) (by
    rw [D.card8 L hL]; norm_num)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A', x * y = y * x := by
    cases b₀
    · intro x hx y hy
      exact (D.twin_comm β hβ A' hA' A hA (by simpa using hlA') hlA y hy x hx).symm
    · exact D.twin_comm β hβ A hA A' hA' hlA (by simpa using hlA')
  have hN : A ≤ Subgroup.normalizer (A' : Set Q) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hcomm x hx _ hy
      have h2' : x * y * x⁻¹ = y := mul_left_cancel (h1.trans (show x * y * x⁻¹ * x = x * y by group))
      rwa [h2'] at hy
  exact (h2 A hA).to_sup_of_normal_right' (h2 A' hA') hN

end Gen


section YSide


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem secAut_mul (hc : P23Cfg n Y R S t K' W u e g) (g₁ g₂ : ↥(Subgroup.centralizer ({e} : Set Y)))
    (q : SecQ R e) :
    TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) (g₁ * g₂) q =
      TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) g₁
        (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) g₂ q) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hnorm := TwinExitPf6.normal_coreHull (hΩ_of hc) (hc2e_of hc)
  set h₂ : ↥(coreHull (Om R) e) :=
    ⟨g₂ * (h : ↥(Subgroup.centralizer ({e} : Set Y))) * g₂⁻¹, hnorm.conj_mem _ h.2 g₂⟩ with hh₂
  set h₁₂ : ↥(coreHull (Om R) e) :=
    ⟨g₁ * (h₂ : ↥(Subgroup.centralizer ({e} : Set Y))) * g₁⁻¹, hnorm.conj_mem _ h₂.2 g₁⟩ with hh₁₂
  rw [TwinExitPf6.secAut_mk (hΩ_of hc) (hc2e_of hc) g₂ h h₂ rfl,
    TwinExitPf6.secAut_mk (hΩ_of hc) (hc2e_of hc) g₁ h₂ h₁₂ rfl,
    TwinExitPf6.secAut_mk (hΩ_of hc) (hc2e_of hc) (g₁ * g₂) h h₁₂ (by
      show g₁ * (g₂ * (h : ↥(Subgroup.centralizer ({e} : Set Y))) * g₂⁻¹) * g₁⁻¹ = _
      group)]

theorem secAut_preserves (hc : P23Cfg n Y R S t K' W u e g) (c : ↥(Subgroup.centralizer ({e} : Set Y)))
    {L : Subgroup (SecQ R e)} (hL : L ∈ TwinDisc.secFam (Om R) e) :
    L.map (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) c).toMonoidHom ∈
      TwinDisc.secFam (Om R) e :=
  TwinExitPf10.secAut_map_secFam (hΩ_of hc) (hc2e_of hc) c hL

@[expose] noncomputable def tbar (hc : P23Cfg n Y R S t K' W u e g) : SecQ R e :=
  piE hc ⟨t, (t_e_mem_rLayer hc).1⟩

theorem piE_mk (hc : P23Cfg n Y R S t K' W u e g) (h : ↥(coreHull (Om R) e))
    (hx : ((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈ rLayer (Om R) e) :
    piE hc ⟨((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y), hx⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h := by
  show QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))
    ((TwinPerpV3.hullEquiv (hmap_of hc)).symm ⟨_, hx⟩) = _
  congr 1
  apply (TwinPerpV3.hullEquiv (hmap_of hc)).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [TwinPerpV3.hullEquiv_coe]

theorem secAut_t (hc : P23Cfg n Y R S t K' W u e g) (htC : t ∈ Subgroup.centralizer ({e} : Set Y))
    (q : SecQ R e) :
    TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨t, htC⟩ q = tbar hc * q * (tbar hc)⁻¹ := by
  obtain ⟨x, rfl⟩ := piE_surjective hc q
  have hE := (t_e_mem_rLayer hc).1
  have hcx : t * (x : Y) * t⁻¹ ∈ rLayer (Om R) e :=
    (rLayer (Om R) e).mul_mem ((rLayer (Om R) e).mul_mem hE x.2) ((rLayer (Om R) e).inv_mem hE)
  rw [secAut_piE hc htC x hcx]
  show piE hc ⟨t * (x : Y) * t⁻¹, hcx⟩ = piE hc ⟨t, hE⟩ * piE hc x * (piE hc ⟨t, hE⟩)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl


theorem twin_labels (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) :
    ∃ (β : Finset (Fin 6)) (hβ : β.card = 4) (b₀ : Bool),
      (secImg (Om R) e (tightCore R)).map D.φ = memBar β hβ b₀ ∧
      (secImg (Om R) e K').map D.φ = memBar β hβ (!b₀) ∧ D.φ (tbar hc) = zBar β hβ ∧
      tbar hc ∈ secImg (Om R) e (tightCore R) ∧ tbar hc ∈ secImg (Om R) e K' ∧
      secImg (Om R) e (tightCore R) ≠ secImg (Om R) e K' := by
  classical
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hKtq := (twins_tq hc).1
  have hK'tq := (twins_tq hc).2
  obtain ⟨htC, htY, hzA⟩ := isUniqueInvolution_secImg (hΩ_of hc) (hc2e_of hc) hKtq hz
  obtain ⟨htC', htY', hzA'⟩ := isUniqueInvolution_secImg (hΩ_of hc) (hc2e_of hc) hK'tq hz'
  have hne_img := secImg_ne_of_twins (hΩ_of hc) (hc2e_of hc) hKtq hK'tq hc.std.hne hz hz'
  have htb : tbar hc = QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))
      ⟨⟨t, htC⟩, htY⟩ := piE_mk hc ⟨⟨t, htC⟩, htY⟩ _
  have hA := secImg_mem_secFam hKtq
  have hA' := secImg_mem_secFam hK'tq
  obtain ⟨β, hβ, b₀, hlab⟩ := D.label _ hA
  obtain ⟨γ, hγ, c, hlab'⟩ := D.label _ hA'
  have e1 : D.φ (tbar hc) = zBar β hβ := by
    rw [htb]
    exact D.map_eq_zBar hA hlab hzA
  have e2 : D.φ (tbar hc) = zBar γ hγ := by
    rw [htb]
    exact D.map_eq_zBar hA' hlab' hzA'
  have hγβ : γ = β := eq_of_zBar_eq (by norm_num : (6 : ℕ) ≠ 8) (e2.symm.trans e1)
  subst hγβ
  have hc' : c = !b₀ := by
    by_contra hcb
    have : c = b₀ := by cases c <;> cases b₀ <;> simp_all
    subst this
    exact hne_img (D.label_inj _ hA _ hA' (hlab.trans hlab'.symm))
  subst hc'
  exact ⟨γ, hγ, b₀, hlab, hlab', e1, by rw [htb]; exact hzA.mem, by rw [htb]; exact hzA'.mem, hne_img⟩


theorem secAut_fix_member (hc : P23Cfg n Y R S t K' W u e g) {y : Y}
    (hyC : y ∈ Subgroup.centralizer ({e} : Set Y))
    (hfield : ∀ l ∈ tightCore R ⊔ K', y * l * y⁻¹ * l⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)))
    {K : Subgroup Y} (hKK : K ≤ tightCore R ⊔ K')
    (hP2 : IsPGroup 2 (secImg (Om R) e (tightCore R) ⊔ secImg (Om R) e K' : Subgroup (SecQ R e)))
    (hKP : secImg (Om R) e K ≤ secImg (Om R) e (tightCore R) ⊔ secImg (Om R) e K')
    (hσP : (secImg (Om R) e K).map
        (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩).toMonoidHom ≤
      secImg (Om R) e (tightCore R) ⊔ secImg (Om R) e K') :
    ∀ a ∈ secImg (Om R) e K,
      TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ a = a := by
  classical
  intro a ha
  obtain ⟨h, hh, rfl⟩ := ha
  have hhK : (((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈
      TwinADescent.coreAt e K := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh)
  have hhl : (((h : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈
      tightCore R ⊔ K' := hKK (TwinADescent.coreAt_le_left e K hhK)
  have hnorm := TwinExitPf6.normal_coreHull (hΩ_of hc) (hc2e_of hc)
  set g₀ : ↥(Subgroup.centralizer ({e} : Set Y)) := ⟨y, hyC⟩ with hg₀
  set h' : ↥(coreHull (Om R) e) :=
    ⟨g₀ * (h : ↥(Subgroup.centralizer ({e} : Set Y))) * g₀⁻¹, hnorm.conj_mem _ h.2 g₀⟩ with hh'
  have hσ := TwinExitPf6.secAut_mk (hΩ_of hc) (hc2e_of hc) g₀ h h' rfl
  rw [hσ]
  set d : ↥(coreHull (Om R) e) := h' * h⁻¹ with hd
  have hdY : (((d : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) =
      y * (((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) * y⁻¹ *
        (((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y))⁻¹ := rfl
  have hdO : (((d : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
    rw [hdY]
    exact hfield _ hhl
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (((d : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) ∣
        Nat.card (oddCoreOf (Subgroup.centralizer ({t} : Set Y))) :=
      Subgroup.orderOf_dvd_natCard _ hdO
    have h2 := (oddCoreOf_odd_natCard (Subgroup.centralizer ({t} : Set Y))).of_dvd_nat h1
    rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at h2
  have hmd : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) d ∈
      secImg (Om R) e (tightCore R) ⊔ secImg (Om R) e K' := by
    rw [hd, map_mul, map_inv]
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (hKP ⟨h, hh, rfl⟩))
    refine hσP ⟨_, ⟨h, hh, rfl⟩, ?_⟩
    exact hσ
  have h1 := TwinExitPf6.eq_one_of_odd_orderOf hP2 hmd (Odd.of_dvd_nat hodd (orderOf_map_dvd _ _))
  rw [hd, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1


theorem y_cases (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {y : Y}
    (hyC : y ∈ Subgroup.centralizer ({e} : Set Y)) (hyt : y * t = t * y)
    (hfield : ∀ l ∈ tightCore R ⊔ K', y * l * y⁻¹ * l⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y))) :
    ∃ (β : Finset (Fin 6)) (hβ : β.card = 4) (w : Wr 6),
      D.toAEData.Acts (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) w ∧
      D.φ (tbar hc) = zBar β hβ ∧
      (Equiv.Perm.sign w.perm = -1 ∨ mkQ 6 w = 1 ∨
        ∃ c₀ : Fin 6, c₀ ∉ β ∧ ∀ (γ : Finset (Fin 6)) (hγ : γ.card = 4), c₀ ∉ γ → ∀ b : Bool,
          ∀ x ∈ memBar γ hγ b,
            mkQ 6 (w * zOf (emb β hβ)) * x * (mkQ 6 (w * zOf (emb β hβ)))⁻¹ = x) := by
  classical
  obtain ⟨β, hβ, b₀, hlA, hlA', hz, htA, htA', hneA⟩ := twin_labels hc D
  set σy := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ with hσy
  have hσΦ : ∀ L ∈ TwinDisc.secFam (Om R) e,
      L.map σy.toMonoidHom ∈ TwinDisc.secFam (Om R) e :=
    fun L hL => secAut_preserves hc ⟨y, hyC⟩ hL
  have hKtq := (twins_tq hc).1
  have hK'tq := (twins_tq hc).2
  have hA := secImg_mem_secFam hKtq
  have hA' := secImg_mem_secFam hK'tq
  have hE := (t_e_mem_rLayer hc).1
  have hσt : σy (tbar hc) = tbar hc := by
    have hyt' : y * t * y⁻¹ = t := by rw [hyt]; group
    have hcx : y * t * y⁻¹ ∈ rLayer (Om R) e := by rw [hyt']; exact hE
    have h1 := secAut_piE hc hyC ⟨t, hE⟩ hcx
    have h2 : (⟨y * t * y⁻¹, hcx⟩ : ↥(rLayer (Om R) e)) = ⟨t, hE⟩ := Subtype.ext hyt'
    exact h1.trans (congrArg (piE hc) h2)
  have hP2 := D.isPGroup_twin_sup hA hA' hlA hlA'
  have hσA := D.map_twin_mem hσΦ hσt hA hA' hlA hlA' hz (Or.inl rfl) htA
  have hσA' := D.map_twin_mem hσΦ hσt hA hA' hlA hlA' hz (Or.inr rfl) htA'
  have hfixA := secAut_fix_member hc hyC hfield (K := tightCore R) le_sup_left hP2 le_sup_left (by
    rcases hσA with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right)
  have hfixA' := secAut_fix_member hc hyC hfield (K := K') le_sup_right hP2 le_sup_right (by
    rcases hσA' with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right)
  obtain ⟨w, hw⟩ := D.toAEData.exists_wr σy hσΦ
  refine ⟨β, hβ, w, hw, hz, ?_⟩
  apply classify hβ w
  intro b x hx
  have key : ∀ (L : Subgroup (SecQ R e)), (∀ a ∈ L, σy a = a) → x ∈ L.map D.φ →
      mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    intro L hL hxL
    obtain ⟨a, ha, rfl⟩ := hxL
    rw [← hw a, hL a ha]
  by_cases hb : b = b₀
  · subst hb
    exact key _ hfixA (by rw [hlA]; exact hx)
  · have hb' : b = !b₀ := by cases b <;> cases b₀ <;> simp_all
    subst hb'
    exact key _ hfixA' (by rw [hlA']; exact hx)

end YSide

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
