module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Str
public import CFSG.ClassicalInvolution.Q3.Sec13L94Tight
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Asc77.AscC25W1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1

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

variable {G : Type} [Group G] [Finite G]

theorem exists_oddCore_conj_le {E F A : Subgroup G} (hE : E ≤ oddCoreOf E ⊔ (E ⊓ F))
    (hA2 : IsPGroup 2 A) (hAE : A ≤ E) : ∃ o ∈ oddCoreOf E, ∀ v ∈ A, o⁻¹ * v * o ∈ F := by
  have hEq : E = (E ⊓ F) ⊔ oddCoreOf E :=
    le_antisymm (by rw [sup_comm]; exact hE) (sup_le inf_le_left (oddCoreOf_le_self E))
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot (p := 2) (G := G)) (bot_le : ⊥ ≤ E ⊓ F)
  have hPE : IsSylow2In P E := T8R.isSylow2In_of_eq_sup_oddCoreOf inf_le_left hEq hP
  obtain ⟨a, haE, hAa⟩ := exists_conj_of_isSylow2In hPE hA2 hAE
  have hBN : E ⊓ F ≤ Subgroup.normalizer (oddCoreOf E : Set G) :=
    inf_le_left.trans (Sec7.le_normalizer_oddCoreOf E)
  have ha' : a ∈ ((oddCoreOf E ⊔ (E ⊓ F) : Subgroup G) : Set G) := by
    rw [sup_comm, ← hEq]
    exact haE
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at ha'
  obtain ⟨o, ho, b, hb, rfl⟩ := ha'
  refine ⟨o, ho, fun v hv => ?_⟩
  have h1 : v ∈ conjSub (o * b) P := hAa hv
  rw [conjSub_mul, mem_conjSub_iff] at h1
  have h2 : o⁻¹ * v * o ∈ conjSub b (E ⊓ F) := conjSub_mono hP.1 h1
  rw [conjSub_eq_self_of_mem hb] at h2
  exact h2.2

theorem exists_conj_zpowers_of_mul_mem_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {a x : G}
    (ha : a * a = 1) (hx : x * x = 1) (hax : a⁻¹ * x ∈ N) :
    ∃ v ∈ Subgroup.zpowers (a * x), a = v * x * v⁻¹ := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  set d := a * x with hd
  have hdN : d ∈ N := by rw [hd, ← hainv]; exact hax
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf d ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk d hdN]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hN h1
  obtain ⟨k, hk⟩ := hodd
  set w := d ^ (k + 1) with hwdef
  have hw2 : w * w = d := by
    rw [hwdef, ← pow_add, show k + 1 + (k + 1) = orderOf d + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hconj : a * d * a⁻¹ = d⁻¹ := by
    rw [hd, mul_inv_rev, hxinv, hainv]
    calc a * (a * x) * a = (a * a) * x * a := by group
      _ = x * a := by rw [ha, one_mul]
  have hconjw : a * w * a⁻¹ = w⁻¹ := by
    rw [hwdef, ← conj_pow, hconj, inv_pow]
  have haw : a * w = w⁻¹ * a := by
    calc a * w = (a * w * a⁻¹) * a := by group
      _ = w⁻¹ * a := by rw [hconjw]
  have hx' : w⁻¹ * a * w = x := by
    calc w⁻¹ * a * w = w⁻¹ * (a * w) := by group
      _ = w⁻¹ * (w⁻¹ * a) := by rw [haw]
      _ = (w * w)⁻¹ * a := by group
      _ = d⁻¹ * a := by rw [hw2]
      _ = x := by rw [hd, mul_inv_rev, hxinv, hainv, mul_assoc, ha, mul_one]
  refine ⟨w, Subgroup.pow_mem _ (Subgroup.mem_zpowers d) _, ?_⟩
  rw [← hx']
  group

theorem exists_cent_conj_of_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {t w s : G}
    (hw2 : w * w = 1) (hs2 : s * s = 1) (hwt : w * t = t * w) (hst : s * t = t * s)
    (hws : w⁻¹ * s ∈ N) : ∃ h ∈ Subgroup.centralizer ({t} : Set G), s = h * w * h⁻¹ := by
  have hN₀ : Odd (Nat.card ↥(N ⊓ Subgroup.centralizer ({t} : Set G))) :=
    hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hwC : w ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwt
  have hsC : s ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst
  have hsw : s⁻¹ * w ∈ N ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ hsC) hwC⟩
    have := N.inv_mem hws
    rwa [mul_inv_rev, inv_inv] at this
  obtain ⟨v, hv, hconj⟩ := exists_conj_zpowers_of_mul_mem_odd hN₀ hs2 hw2 hsw
  exact ⟨v, (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ hsC hwC)) hv, hconj⟩

theorem conjSub_rLayer_eq {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {x g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) : conjSub g (rLayer Ω x) = rLayer Ω x := by
  have h : ∀ g : G, g ∈ Subgroup.centralizer ({x} : Set G) →
      conjSub g (rLayer Ω x) ≤ rLayer Ω x := by
    intro g hg
    unfold rLayer
    show Subgroup.map (MulAut.conj g).toMonoidHom _ ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hR => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hRx => ?_
    have hR' : conjSub g R ∈ RSet Ω := Q3CL.Thompson.conjSub_mem_RSet hΩ hR g
    have hC : conjSub g R ≤ Subgroup.centralizer ({x} : Set G) := by
      have h1 := conjSub_mono (n := g) hRx
      rwa [conjSub_eq_self_of_mem hg] at h1
    exact le_iSup₂_of_le (conjSub g R) hR' (le_iSup_of_le hC le_rfl)
  refine le_antisymm (h g hg) ?_
  have hg' : g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.inv_mem _ hg
  have h2 := conjSub_mono (n := g) (h g⁻¹ hg')
  rwa [conjSub_conjSub_inv] at h2

end Gen



section E7F

variable {n : ℕ}

theorem p23E7Fus_proved : P23E7Fus n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ x hxC hxG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have htrans : ∀ J ∈ Om R, ∃ a : Y, conjSub a (tightCore R) = J := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ a : Y, conjSub a K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hNe : Subgroup.normalizer (W : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) :=
    normalizer_le_centralizer_e hd
  have hWe : W ≤ Subgroup.centralizer ({e} : Set Y) := Subgroup.le_normalizer.trans hNe
  have hKt : tightCore R ⊔ K' ≤ Subgroup.centralizer ({t} : Set Y) :=
    sup_le (le_centralizer_of_unique hz) (le_centralizer_of_unique hz')
  obtain ⟨S₀, hWS₀, hwc, -⟩ := exists_weaklyClosed_conj_of_muIsoS4 hPG htr hd.hW hd.hS4
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hWt : W ≤ Subgroup.centralizer ({t} : Set Y) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  obtain ⟨S₂, hS₂, hWS₂⟩ := IsSylow2In.exists_ge hW2 hWt
  obtain ⟨S₁, hSS₁⟩ := hS₂.2.1.exists_le_sylow
  obtain ⟨a, ha⟩ := exists_conjSub_eq_of_sylow S₀ S₁
  have e2 : conjSub a⁻¹ W = W := hwc a⁻¹ (by
    rw [conjSub_le_iff, inv_inv, ha]
    exact hWS₂.trans hSS₁)
  have e3 : conjSub a W = W := by
    conv_lhs => rw [← e2]
    exact conjSub_conjSub_inv a W
  have hS₂N : S₂ ≤ Subgroup.normalizer (W : Set Y) := by
    intro s hs
    have hs₀ : a⁻¹ * s * a ∈ (S₀ : Subgroup Y) := by
      have := hSS₁ hs
      rw [← ha] at this
      exact mem_conjSub_iff.mp this
    have e4 : conjSub (a⁻¹ * s * a) W = W :=
      hwc _ ((conjSub_mono hWS₀).trans (conjSub_eq_self_of_mem hs₀).le)
    have e5 : conjSub s W = W := by
      have : s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, conjSub_mul, e2, e4, e3]
    exact mem_normalizer_iff_conjSub_eq.mpr e5
  have hS₂e : S₂ ≤ Subgroup.centralizer ({e} : Set Y) := hS₂N.trans hNe
  obtain ⟨R₁, R₁', -, -, hR₁, hR₁', hR₁D, hR₁'D, -, -, -, -, -, -, hne_ue⟩ := e_decomp hc
  have hT : ∀ M ∈ Om R, ∀ R' : Subgroup Y, IsSylow2In R' M → R' ∈ DSet (Om R) W → ∀ r : Y,
      IsUniqueInvolution M r → ∃ m ∈ Subgroup.centralizer ({e} : Set Y), m * t * m⁻¹ = r := by
    intro M hM R' hR'M hR'D r hr
    obtain ⟨m, hm, -, hmt⟩ := Sec13.L94T.exists_mGrp_conj hPG hd.hW hK htrans hz hc.std.hK'
      hc.std.hne hperp hd.hS4 hR₁ hR₁D hM hR'M hR'D hr
    exact ⟨m, hNe (Thompson.MGrp_le_normalizer _ _ hm), hmt⟩
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hge : g⁻¹ * e * g = e := by rw [mul_assoc, ← T7K.comm_e hd hgN, inv_mul_cancel_left]
  have hgz : g⁻¹ * (u * e) * g = t := by rw [← hd.hgt]; group
  have hgu : g⁻¹ * u * g = e * t := by
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hd.he2
    calc g⁻¹ * u * g = g⁻¹ * (u * e) * g * (g⁻¹ * e⁻¹ * g) := by group
      _ = t * e := by rw [hgz, hei, hge]
      _ = e * t := hWab t hd.hzW e heW
  have hZ' : t ∈ zStarOf (Subgroup.centralizer ({e * t} : Set Y)) := by
    have hZ1 := C25W.conj_mem_zStarOf_conjSub _ g⁻¹ hZ
    rw [← C25W.centralizer_conj, inv_inv, hgz, hgu] at hZ1
    exact hZ1
  have htwK : ∀ M ∈ Om R, IsUniqueInvolution M t → M = tightCore R ∨ M = K' := by
    intro M hM htM
    by_cases hMK : M = tightCore R
    · exact Or.inl hMK
    have hMp : M ∈ KPerp (Om R) (tightCore R) :=
      Set.mem_insert_of_mem _ (Q3CL.T3.twin_mem_omegaNbr hΩ hK hM hMK hz htM)
    rw [hperp] at hMp
    simpa [hMK] using hMp
  have htw : ∀ L ∈ Om R, ∀ s : Y, IsUniqueInvolution L s → ∃ L' ∈ Om R, L ≠ L' ∧
      IsUniqueInvolution L' s ∧ ∀ M ∈ Om R, IsUniqueInvolution M s → M = L ∨ M = L' := by
    intro L hL s hs
    obtain ⟨g₁, rfl⟩ := htrans L hL
    obtain rfl : s = g₁ * t * g₁⁻¹ := hs.eq (hz.conj g₁)
    refine ⟨conjSub g₁ K', hΩ.conjInvariant g₁ K' hK'Ω,
      fun h => hc.std.hne (conjSub_injective g₁ h).symm, hz'.conj g₁, fun M hM hsM => ?_⟩
    have h1 : IsUniqueInvolution (conjSub g₁⁻¹ M) t := by
      have := hsM.conj g₁⁻¹
      rwa [show g₁⁻¹ * (g₁ * t * g₁⁻¹) * g₁⁻¹⁻¹ = t by group] at this
    rcases htwK _ (hΩ.conjInvariant g₁⁻¹ M hM) h1 with h | h
    · left; rw [← h, conjSub_conjSub_inv]
    · right; rw [← h, conjSub_conjSub_inv]
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  obtain ⟨c, hcC, y₁, hy₁, hcy⟩ := Sec13.L94T.exists_conj_fusion hΩ
    (Q8P.ascStand_of_twinCore hC).card8 hd.hW hWab hd.hzW heW hd.he2 hS₂ hWS₂ hS₂e hT hZ' htw
    hK hz hxG hxt
  have hEe : rLayer (Om R) e ≤ Subgroup.centralizer ({e} : Set Y) := rLayer_le_centralizer _ _
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hR₁D.2.trans hNe
  have hR₁y : conjSub y₁ R₁ ≤ rLayer (Om R) e := by
    have hRS : conjSub y₁ R₁ ∈ RSet (Om R) := Q3CL.Thompson.conjSub_mem_RSet hΩ hR₁D.1 y₁
    have hRe : conjSub y₁ R₁ ≤ Subgroup.centralizer ({e} : Set Y) := by
      have := conjSub_mono (n := y₁) hR₁e
      rwa [conjSub_eq_self_of_mem hy₁] at this
    unfold rLayer
    exact le_iSup₂_of_le (conjSub y₁ R₁) hRS (le_iSup_of_le hRe le_rfl)
  obtain ⟨o, ho, hoN⟩ := exists_oddCore_conj_le hE (hR₁.conj y₁).2.1 hR₁y
  have hoe : o ∈ Subgroup.centralizer ({e} : Set Y) := hEe (oddCoreOf_le_self _ ho)
  set y₂ := o⁻¹ * y₁ with hy₂def
  have hy₂ : y₂ ∈ Subgroup.centralizer ({e} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hoe) hy₁
  have hR₂D : conjSub y₂ R₁ ∈ DSet (Om R) W := by
    refine ⟨Q3CL.Thompson.conjSub_mem_RSet hΩ hR₁D.1 y₂, fun v hv => ?_⟩
    rw [hy₂def, conjSub_mul, mem_conjSub_iff, inv_inv] at hv
    have := hoN _ hv
    simpa [mul_assoc] using this
  obtain ⟨n₁, hn₁, hn₁K, -⟩ := Sec13.L94T.exists_mGrp_conj hPG hd.hW hK htrans hz hc.std.hK'
    hc.std.hne hperp hd.hS4 hR₁ hR₁D (hΩ.conjInvariant y₂ _ hK) (hR₁.conj y₂) hR₂D (hz.conj y₂)
  have hn₁N : n₁ ∈ Subgroup.normalizer (W : Set Y) := Thompson.MGrp_le_normalizer _ _ hn₁
  have hw : n₁ * t * n₁⁻¹ = y₂ * t * y₂⁻¹ := by
    have h1 := hz.conj n₁
    rw [hn₁K] at h1
    exact h1.eq (hz.conj y₂)
  have hgK : conjSub g (tightCore R) ≠ tightCore R := fun h => hne_ue (by
    have h1 := hz.conj g
    rw [h] at h1
    rw [← hd.hgt]
    exact (hz.eq h1).symm)
  have hgK' : conjSub g (tightCore R) ≠ K' := fun h => hne_ue (by
    have h1 := hz.conj g
    rw [h] at h1
    rw [← hd.hgt]
    exact (hz'.eq h1).symm)
  have hwcases : n₁ * t * n₁⁻¹ = t ∨ ∃ m ∈ Subgroup.centralizer ({t} : Set Y),
      n₁ * t * n₁⁻¹ = m * (u * e) * m⁻¹ := by
    rcases Sec13.L94T.conjSub_cases_of_mem_normalizer hPG hd.hW hK htrans hz hc.std.hK'
      hc.std.hne hperp hd.hS4 hR₁ hR₁D hR₁' hR₁'D hgN hgK hgK' hn₁N with h | h | ⟨m, hm, hmK⟩
    · left
      have h1 := hz.conj n₁
      rw [h] at h1
      exact (hz.eq h1).symm
    · left
      have h1 := hz.conj n₁
      rw [h] at h1
      exact (hz'.eq h1).symm
    · right
      refine ⟨m, hKt hm, ?_⟩
      have h1 := (hz.conj g).conj m
      rw [hmK, hd.hgt] at h1
      exact ((hz.conj n₁).eq h1)
  set w := n₁ * t * n₁⁻¹ with hwdef
  have hwW : w ∈ W := (Subgroup.mem_normalizer_iff.mp hn₁N t).mp hd.hzW
  have hw2 : w * w = 1 := (hz.conj n₁).sq
  have hwt : w * t = t * w := hWab w hwW t hd.hzW
  have hs : y₁ * t * y₁⁻¹ = o * w * o⁻¹ := by
    rw [hw, hy₂def]
    group
  have hs2 : (y₁ * t * y₁⁻¹) * (y₁ * t * y₁⁻¹) = 1 := (hz.conj y₁).sq
  have hsC : y₁ * t * y₁⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [← hcy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hxC) (Subgroup.inv_mem _ hcC)
  have hwE : w ∈ Subgroup.normalizer (rLayer (Om R) e : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_rLayer_eq hΩ (hWe hwW))
  have hws : w⁻¹ * (y₁ * t * y₁⁻¹) ∈ oddCoreOf (rLayer (Om R) e) := by
    rw [hs]
    have h1 : w⁻¹ * o * w⁻¹⁻¹ ∈ oddCoreOf (rLayer (Om R) e) :=
      mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.inv_mem _ hwE) ho
    have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ho)
    simpa [mul_assoc] using h2
  obtain ⟨h, hhC, hsh⟩ := exists_cent_conj_of_odd (oddCoreOf_odd_natCard _) hw2 hs2 hwt
    (Subgroup.mem_centralizer_singleton_iff.mp hsC) hws
  have hx : x = (c⁻¹ * h) * w * (c⁻¹ * h)⁻¹ := by
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = c⁻¹ * (h * w * h⁻¹) * c := by rw [hcy, hsh]
      _ = (c⁻¹ * h) * w * (c⁻¹ * h)⁻¹ := by group
  have hch : c⁻¹ * h ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hcC) hhC
  rcases hwcases with hwt' | ⟨m, hm, hwm⟩
  · left
    rw [hx, hwt']
    have := Subgroup.mem_centralizer_singleton_iff.mp hch
    calc c⁻¹ * h * t * (c⁻¹ * h)⁻¹ = t * (c⁻¹ * h) * (c⁻¹ * h)⁻¹ := by rw [this]
      _ = t := by group
  · right
    refine ⟨c⁻¹ * h * m, Subgroup.mul_mem _ hch hm, ?_⟩
    rw [hx, hwm]
    group

end E7F

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
