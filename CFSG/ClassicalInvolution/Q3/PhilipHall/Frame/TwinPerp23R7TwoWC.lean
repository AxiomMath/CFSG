module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWT
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf67Print
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoW
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Gen

variable {G : Type} [Group G]

theorem orderOf_eq_four_of_sq {y : G} (h2 : y * y ≠ 1) (h4 : y * y * (y * y) = 1) :
    orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y) (by rw [pow_one, sq]; exact h2)
    (by rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, sq]; exact h4)
  simpa using h

theorem exists_eq_mul_of_q8 {R₁ R₂ : Subgroup G} (e₁ : ↥R₁ ≃* QuaternionGroup 2)
    (hc : Commutes R₁ R₂) {x a : G} (hx : x ∈ R₁) (hx2 : x * x ≠ 1)
    (hR₂ : ∀ r ∈ R₂, r * r = 1 → r = 1 ∨ r = x * x) (ha : a ∈ R₁ ⊔ R₂)
    (hax : a * x = x * a) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ x * x) :
    ∃ y ∈ R₂, y * y = x * x ∧ (a = x * y ∨ a = x⁻¹ * y) := by
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc ha
  have ht : x * x * (x * x) = 1 := sq_sq_eq_one_of_q8 e₁ hx
  have hti : (x * x)⁻¹ = x * x := inv_eq_of_mul_eq_one_right ht
  have hc₁ : r₁ * x = x * r₁ := by
    have h1 : r₁ * r₂ * x = r₁ * x * r₂ := by rw [mul_assoc, ← hc x hx r₂ hr₂, mul_assoc]
    have h2 : r₁ * x * r₂ = x * r₁ * r₂ := by rw [← h1, hax, mul_assoc]
    exact mul_right_cancel h2
  have hsq : r₁ * r₁ * (r₂ * r₂) = 1 := by
    have h12 := hc r₁ hr₁ r₂ hr₂
    calc r₁ * r₁ * (r₂ * r₂) = r₁ * (r₁ * r₂) * r₂ := by group
      _ = r₁ * (r₂ * r₁) * r₂ := by rw [h12]
      _ = r₁ * r₂ * (r₁ * r₂) := by group
      _ = 1 := ha2
  have hr₂sq : r₂ * r₂ = (r₁ * r₁)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  rcases eq_of_commute_of_q8 e₁ hx hr₁ hx2 hc₁ with h₁ | h₁ | h₁
  · exfalso
    rcases hR₂ r₂ hr₂ (by rw [hr₂sq, h₁]; simp) with h₂ | h₂
    · exact ha1 (by rw [h₁, h₂, one_mul])
    · exact hat (by rw [h₁, h₂, one_mul])
  · exfalso
    rcases hR₂ r₂ hr₂ (by rw [hr₂sq, h₁, ht, inv_one]) with h₂ | h₂
    · exact hat (by rw [h₁, h₂, mul_one])
    · exact ha1 (by rw [h₁, h₂, ht])
  · have h11 : r₁ * r₁ = x * x := by
      rcases h₁ with h₁ | h₁
      · rw [h₁]
      · rw [h₁, ← mul_inv_rev, hti]
    refine ⟨r₂, hr₂, by rw [hr₂sq, h11, hti], ?_⟩
    rcases h₁ with h₁ | h₁
    · exact Or.inl (by rw [h₁])
    · exact Or.inr (by rw [h₁])

theorem centralizer_le_of_conj {H : Subgroup G} {c u v : G} (hcH : c ∈ H)
    (hCu : Subgroup.centralizer ({u} : Set G) ≤ H) (h : c * u * c⁻¹ = v) :
    Subgroup.centralizer ({v} : Set G) ≤ H := by
  intro w hw
  have hw' : c⁻¹ * w * c ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    have hu : u = c⁻¹ * v * c := by rw [← h]; group
    calc c⁻¹ * w * c * u = c⁻¹ * (w * v) * c := by rw [hu]; group
      _ = c⁻¹ * (v * w) * c := by rw [hw]
      _ = u * (c⁻¹ * w * c) := by rw [hu]; group
  have e : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
  rw [e]
  exact H.mul_mem (H.mul_mem hcH (hCu hw')) (H.inv_mem hcH)

end Gen

section Assembly

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem hyp23Setting_of_cfg (hc : P23Cfg n Y R S t K' W u e g) :
    CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t := by
  have hC := CoreData.of_S hc.std.perp.core
  exact ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc,
    Inner.isUniqueInvolution_core hC.datum, hc.std.hK', hc.std.hne,
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)⟩

theorem cx_of_wProd (hc : P23Cfg n Y R S t K' W u e g) (hWP : P23WProd n) :
    ∀ W₁ ∈ WSet (Om R), t ∈ W₁ → ∀ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      IsSylow2In R₂ K' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂, x ∈ W₁ → y ∈ W₁ → orderOf x = 4 →
        orderOf y = 4 → Subgroup.centralizer ({x * y} : Set Y) ≤
          Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) := by
  intro W₁ hW₁ htW₁ R₁ R₂ hR₁ hR₂ hcm x hx y hy hxW hyW ox oy
  have hz : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  obtain ⟨c, hct, hcu⟩ := hWP Y R S t K' W u e g hc W₁ hW₁ htW₁ (tightCore R)
    (mem_twinSet_self (CoreAssembly.mem_conjClass_self _) hz) K' hc.std.hK' hc.std.hne R₁ R₂ hR₁
    hR₂ hcm x hx y hy hxW hyW ox oy
  exact centralizer_le_of_conj (Subgroup.mem_sup_right hct) le_sup_left hcu

theorem cent_twin (hc : P23Cfg n Y R S t K' W u e g) (hWP : P23WProd n) {W₁ : Subgroup Y}
    (hW₁ : W₁ ∈ WSet (Om R)) (htW₁ : t ∈ W₁) {M₀ J R₁ R₂ : Subgroup Y}
    (hM₀ : M₀ ∈ twinSet (Om R) (tightCore R)) (hJ : J ∈ twinSet (Om R) (tightCore R))
    (hR₁ : IsSylow2In R₁ M₀) (hR₂ : IsSylow2In R₂ J) (hcm : Commutes R₁ R₂ ∨ R₂ = R₁) {x a : Y}
    (hx : x ∈ R₁) (hxW : x ∈ W₁) (ox : orderOf x = 4) (ha : a ∈ R₁ ⊔ R₂) (haW : a ∈ W₁)
    (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    Subgroup.centralizer ({a} : Set Y) ≤
      Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzM : IsUniqueInvolution M₀ t := isUniqueInvolution_of_mem_twinSet hz hM₀
  have hzJ : IsUniqueInvolution J t := isUniqueInvolution_of_mem_twinSet hz hJ
  have hat : a ∈ M₀ → Subgroup.centralizer ({a} : Set Y) ≤
      Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) := fun haM => by
    rcases hzM.unique a haM ha2 with h | h
    · exact absurd h ha1
    · rw [h]; exact le_sup_right
  by_cases hJM : J = M₀
  · subst hJM
    exact hat (sup_le hR₁.1 hR₂.1 ha)
  rcases hcm with hcm | hcm
  swap
  · subst hcm
    exact hat (hR₁.1 (by simpa using ha))
  have hxx : x * x = t := TwinPerp.sq_eq_of_orderOf_four hzM (hR₁.1 hx) ox
  have hx2 : x * x ≠ 1 := by rw [hxx]; exact hzM.ne_one
  by_cases hat' : a = t
  · rw [hat']; exact le_sup_right
  obtain ⟨e₁⟩ := nonempty_q8_of_isSylow2In hC hM₀.1 hR₁
  obtain ⟨y, hy, hyy, hay⟩ := exists_eq_mul_of_q8 e₁ hcm hx hx2
    (fun r hr hr2 => by rw [hxx]; exact hzJ.unique r (hR₂.1 hr) hr2) ha
    (Q3CL.Thompson.commutes_of_mem_WSet hΩ hW₁ a haW x hxW) ha2 ha1 (by rw [hxx]; exact hat')
  have hy4 : orderOf y = 4 :=
    orderOf_eq_four_of_sq (by rw [hyy]; exact hx2) (by rw [hyy]; exact sq_sq_eq_one_of_q8 e₁ hx)
  rcases hay with h | h
  · have hyW : y ∈ W₁ := by
      have : y = x⁻¹ * a := by rw [h]; group
      rw [this]; exact W₁.mul_mem (W₁.inv_mem hxW) haW
    obtain ⟨c, hct, hcu⟩ := hWP Y R S t K' W u e g hc W₁ hW₁ htW₁ M₀ hM₀ J hJ hJM R₁ R₂ hR₁ hR₂
      hcm x hx y hy hxW hyW ox hy4
    exact centralizer_le_of_conj (Subgroup.mem_sup_right hct) le_sup_left (hcu.trans h.symm)
  · have hyW : y ∈ W₁ := by
      have : y = x * a := by rw [h]; group
      rw [this]; exact W₁.mul_mem hxW haW
    obtain ⟨c, hct, hcu⟩ := hWP Y R S t K' W u e g hc W₁ hW₁ htW₁ M₀ hM₀ J hJ hJM R₁ R₂ hR₁ hR₂
      hcm x⁻¹ (R₁.inv_mem hx) y hy (W₁.inv_mem hxW) hyW (by rw [orderOf_inv]; exact ox) hy4
    exact centralizer_le_of_conj (Subgroup.mem_sup_right hct) le_sup_left (hcu.trans h.symm)

theorem centPairs_of_wProd (hc : P23Cfg n Y R S t K' W u e g) (hWP : P23WProd n)
    {W₁ : Subgroup Y} (hW₁ : W₁ ∈ WSet (Om R)) (htW₁ : t ∈ W₁) {S₀ : Subgroup Y}
    (hS₀ : IsPGroup 2 S₀) (hWS : W₁ ≤ S₀) (hSN : S₀ ≤ Subgroup.normalizer (W₁ : Set Y)) :
    TwinThmEW.CentPairs (Om R) S₀ W₁
      (Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y)) := by
  intro M hM _ J hJ R₁ R₂ hR₁ hR₁M hR₁S hR₂ hR₂J _ hcm a ha haW ha1 ha2
  set H := Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) with hH
  have hs := hyp23Setting_of_cfg hc
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hKt := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} := hs.perp
  have hJΩ : J ∈ Om R := by
    rcases hJ with rfl | hJ
    · exact hM
    · exact hJ.1
  have hR₁M' : IsSylow2In R₁ M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hM hR₁ hR₁M
  have hR₂J' : IsSylow2In R₂ J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hR₂ hR₂J
  have hR₁D : R₁ ∈ DSet (Om R) W₁ := ⟨hR₁, hR₁S.trans hSN⟩
  obtain ⟨-, -, hcyc, -, hcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW₁ hR₁D hM hR₁M'
  have h4 : Nat.card ↥(R₁ ⊓ W₁) = 4 := by
    have := hs.stand.card8 M hM R₁ hR₁M'
    omega
  obtain ⟨x₀, hx₀⟩ := hcyc.exists_generator
  have ox : orderOf (x₀ : Y) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx₀, h4]
  have hx : (x₀ : Y) ∈ R₁ := (Subgroup.mem_inf.1 x₀.2).1
  have hxW : (x₀ : Y) ∈ W₁ := (Subgroup.mem_inf.1 x₀.2).2
  have hTw : ∀ {L : Subgroup Y}, L ∈ twinSet (Om R) (tightCore R) → ∀ {J' : Subgroup Y},
      J' ∈ KPerp (Om R) L → J' ∈ twinSet (Om R) (tightCore R) := fun hL J' hJ' => by
    rw [A7T22.kPerp_eq_of_twin hΩ hK hL, hperp] at hJ'
    rw [hKt]; exact hJ'
  obtain ⟨h, hhH, hKM, hcase⟩ := key_of_cx hs le_sup_right hW₁ htW₁
    (cx_of_wProd hc hWP W₁ hW₁ htW₁) M hM ⟨R₁, hR₁D, hR₁M'⟩
  rcases hcase with rfl | hMK' | hhN
  · rw [conjSub_one] at hKM
    subst hKM
    have hM₀ := mem_twinSet_self hK hz
    exact cent_twin hc hWP hW₁ htW₁ hM₀ (hTw hM₀ hJ) hR₁M' hR₂J' hcm hx hxW ox ha haW ha1 ha2
  · subst hMK'
    exact cent_twin hc hWP hW₁ htW₁ hc.std.hK' (hTw hc.std.hK' hJ) hR₁M' hR₂J' hcm hx hxW ox ha
      haW ha1 ha2
  ·
    have hhN' : h⁻¹ ∈ Subgroup.normalizer (W₁ : Set Y) := Subgroup.inv_mem _ hhN
    have hconjW : ∀ {w : Y}, w ∈ W₁ → h⁻¹ * w * h⁻¹⁻¹ ∈ W₁ := fun hw =>
      (Subgroup.mem_normalizer_iff.1 hhN' _).1 hw
    have hKM' : conjSub h⁻¹ M = tightCore R := by rw [← hKM, conjSub_inv_conjSub]
    have hM₀ := mem_twinSet_self hK hz
    have hJ' : conjSub h⁻¹ J ∈ KPerp (Om R) (tightCore R) := by
      have := KPerp_conj hΩ.conjInvariant hJ h⁻¹
      rwa [hKM'] at this
    have hR₁' : IsSylow2In (conjSub h⁻¹ R₁) (tightCore R) := by
      have := hR₁M'.conj h⁻¹
      rwa [hKM'] at this
    have hcm' : Commutes (conjSub h⁻¹ R₁) (conjSub h⁻¹ R₂) ∨ conjSub h⁻¹ R₂ = conjSub h⁻¹ R₁ := by
      rcases hcm with hcm | hcm
      · left
        intro p hp q hq
        rw [mem_conjSub_iff] at hp hq
        have := hcm _ hp _ hq
        calc p * q = h⁻¹ * ((h⁻¹⁻¹ * p * h⁻¹) * (h⁻¹⁻¹ * q * h⁻¹)) * h⁻¹⁻¹ := by group
          _ = h⁻¹ * ((h⁻¹⁻¹ * q * h⁻¹) * (h⁻¹⁻¹ * p * h⁻¹)) * h⁻¹⁻¹ := by rw [this]
          _ = q * p := by group
      · right; rw [hcm]
    have ha' : h⁻¹ * a * h⁻¹⁻¹ ∈ conjSub h⁻¹ R₁ ⊔ conjSub h⁻¹ R₂ := by
      have := conj_mem_conjSub (n := h⁻¹) ha
      simpa only [conjSub, Subgroup.map_sup] using this
    have hCa := cent_twin hc hWP hW₁ htW₁ hM₀ (hTw hM₀ hJ') hR₁' (hR₂J'.conj h⁻¹) hcm'
      (conj_mem_conjSub hx) (hconjW hxW) (by
        have := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective (x₀ : Y)
        simpa [MulAut.conj_apply, ox] using this) ha' (hconjW haW)
      (fun h1 => ha1 (by
        calc a = h * (h⁻¹ * a * h⁻¹⁻¹) * h⁻¹ := by group
          _ = 1 := by rw [h1]; group)) (by
        calc h⁻¹ * a * h⁻¹⁻¹ * (h⁻¹ * a * h⁻¹⁻¹) = h⁻¹ * (a * a) * h⁻¹⁻¹ := by group
          _ = 1 := by rw [ha2]; group)
    exact centralizer_le_of_conj hhH hCa (by group)

theorem p23Two_of_wTrans (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hT : P23WTrans n) : P23Two n := by
  intro Y _ _ R S t K' W u e g hc
  have hWP := p23WProd_of_wTrans hT
  have hs := hyp23Setting_of_cfg hc
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  obtain ⟨W', ⟨S₀, R₀, hR₀, hR₀S, hW', hW'S, hWn, K'', hK'', hne'', R', hR', hR'K, hR'S⟩, -⟩ :=
    TwinPerpV3.exists_printedWT hΩ hK hc.std.hK' hc.std.hne
  have hSN : (S₀ : Subgroup Y) ≤ Subgroup.normalizer (W' : Set Y) := fun s hs =>
    mem_normalizer_iff_conjSub_eq.mpr (hWn s hs)
  have htW' : t ∈ W' := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW' hK
    ⟨mem_RSet_of_isSylow2In hK hR₀, hR₀S.trans hSN⟩ hR₀ hz).2
  have htrans := trans_of_cx hs le_sup_right (cx_of_wProd hc hWP)
  have hcent := centPairs_of_wProd hc hWP hW' htW' S₀.isPGroup' hW'S hSN
  exact TwinThmEW.twinThmEPrintedAllT_of_thmEQ8 hE hcit hP Y R S t hc.std.perp.core.toHyp
    (tightCore R) _ W' S₀ hK ⟨R₀, hR₀, hR₀S, hW', hW'S, hWn, K'', hK'', hne'', R', hR', hR'K, hR'S⟩
    ⟨htrans, hcent⟩

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
