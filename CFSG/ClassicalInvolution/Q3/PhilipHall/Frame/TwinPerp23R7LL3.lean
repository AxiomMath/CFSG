module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E64Facts

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7L3

variable {G : Type} [Group G] [Finite G]

theorem exists_oddCore_conj_comm {X A : Subgroup G} (hAX : A ≤ X) (hA2 : IsPGroup 2 A) {x : G}
    (hxX : x ∈ X) (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (hcomm : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf X) :
    ∃ o ∈ oddCoreOf X, ∀ a ∈ A, (o⁻¹ * a * o) * x = x * (o⁻¹ * a * o) := by
  set O := oddCoreOf X with hOdef
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard X
  have hXN : X ≤ Subgroup.normalizer (O : Set G) := Sec7.le_normalizer_oddCoreOf X
  have hAN : A ≤ Subgroup.normalizer (O : Set G) := hAX.trans hXN
  have hxO : ∀ o ∈ O, x * o * x⁻¹ ∈ O := fun o ho =>
    (Subgroup.mem_normalizer_iff.mp (hXN hxX) o).mp ho
  set M := O ⊔ A with hMdef
  have hxM : ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    have hle : M ≤ M.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun o ho => Subgroup.mem_sup_left (hxO o ho)) (fun r hr => ?_)
      show x * r * x⁻¹ ∈ M
      have h1 : x * r * x⁻¹ * r⁻¹ ∈ O := by
        have h := O.inv_mem (hcomm r hr)
        have e : (r * x * r⁻¹ * x⁻¹)⁻¹ = x * r * x⁻¹ * r⁻¹ := by group
        rwa [e] at h
      have h2 := M.mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hr)
      have e : x * r * x⁻¹ * r⁻¹ * r = x * r * x⁻¹ := by group
      rwa [e] at h2
    exact fun m hm => hle hm
  have hxN : x ∈ Subgroup.normalizer (M : Set G) := by
    have hle : conjSub x M ≤ M := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have h := hxM _ hy
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rwa [e] at h
    refine mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [show Nat.card (conjSub x M) = Nat.card M from
      Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hHN : M ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (M : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN)
  obtain ⟨T, hT, hxT⟩ :=
    IsSylow2In.exists_ge hx2 (le_sup_right : Subgroup.zpowers x ≤ M ⊔ Subgroup.zpowers x)
  have hTM : IsSylow2In (T ⊓ M) M := Asc77.isSylow2In_inf_of_le_normalizer hT le_sup_left hHN
  obtain ⟨a, haM, hAa⟩ := Asc77.exists_conj_of_isSylow2In hTM hA2 (le_sup_right : A ≤ M)
  have ha' : a ∈ ((A ⊔ O : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact haM
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at ha'
  obtain ⟨r, hr, o, ho, rfl⟩ := ha'
  refine ⟨o, ho, fun y hy => ?_⟩
  have hyT : o⁻¹ * y * o ∈ T := by
    have hy' : r * y * r⁻¹ ∈ A := A.mul_mem (A.mul_mem hr hy) (A.inv_mem hr)
    have h1 := hAa hy'
    rw [mem_conjSub_iff] at h1
    have h2 : (r * o)⁻¹ * (r * y * r⁻¹) * (r * o) = o⁻¹ * y * o := by group
    rw [h2] at h1
    exact h1.1
  have hxT' : x ∈ T := hxT (Subgroup.mem_zpowers x)
  have hcT : (o⁻¹ * y * o) * x * (o⁻¹ * y * o)⁻¹ * x⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem hyT hxT') (T.inv_mem hyT)) (T.inv_mem hxT')
  have hcO : (o⁻¹ * y * o) * x * (o⁻¹ * y * o)⁻¹ * x⁻¹ ∈ O := by
    have hc1 : o * (x * o⁻¹ * x⁻¹) ∈ O := O.mul_mem ho (hxO _ (O.inv_mem ho))
    have hc2 : y * (o * (x * o⁻¹ * x⁻¹)) * y⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hAN hy) _).mp hc1
    have e : (o⁻¹ * y * o) * x * (o⁻¹ * y * o)⁻¹ * x⁻¹ =
        o⁻¹ * (y * (o * (x * o⁻¹ * x⁻¹)) * y⁻¹) * (y * x * y⁻¹ * x⁻¹) * (x * o * x⁻¹) := by
      group
    rw [e]
    exact O.mul_mem (O.mul_mem (O.mul_mem (O.inv_mem ho) hc2) (hcomm y hy)) (hxO o ho)
  have h1 := Sec13.L94T.eq_one_of_isPGroup_of_odd hT.2.1 hOodd hcT hcO
  calc (o⁻¹ * y * o) * x = (o⁻¹ * y * o) * x * (o⁻¹ * y * o)⁻¹ * x⁻¹ * (x * (o⁻¹ * y * o)) := by
        group
    _ = x * (o⁻¹ * y * o) := by rw [h1, one_mul]

theorem eq_of_odd_orderOf_conj {E : Subgroup G} {t t' o₁ o₂ : G} (ht : t ∈ E) (ht' : t' ∈ E)
    (htt : t * t' = t' * t) (ht2 : t * t = 1) (ht'2 : t' * t' = 1)
    (ho₁ : o₁ ∈ oddCoreOf E) (ho₂ : o₂ ∈ oddCoreOf E)
    (hodd : Odd (orderOf ((o₁⁻¹ * t * o₁)⁻¹ * (o₂⁻¹ * t' * o₂)))) : t = t' := by
  have ho₁E : o₁ ∈ E := oddCoreOf_le_self E ho₁
  have ho₂E : o₂ ∈ E := oddCoreOf_le_self E ho₂
  have hπ₁ : F7I.piC E ⟨o₁, ho₁E⟩ = 1 := (F7I.piC_eq_one_iff _).mpr ho₁
  have hπ₂ : F7I.piC E ⟨o₂, ho₂E⟩ = 1 := (F7I.piC_eq_one_iff _).mpr ho₂
  have hc2 : (t⁻¹ * t') * (t⁻¹ * t') = 1 := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [htinv]
    calc t * t' * (t * t') = t * (t' * t) * t' := by group
      _ = t * (t * t') * t' := by rw [← htt]
      _ = (t * t) * (t' * t') := by group
      _ = 1 := by rw [ht2, ht'2, one_mul]
  obtain ⟨w, hw⟩ : ∃ w : ↥E, w = (⟨o₁, ho₁E⟩⁻¹ * ⟨t, ht⟩ * ⟨o₁, ho₁E⟩)⁻¹ *
      (⟨o₂, ho₂E⟩⁻¹ * ⟨t', ht'⟩ * ⟨o₂, ho₂E⟩) := ⟨_, rfl⟩
  have hπw : F7I.piC E w = F7I.piC E (⟨t, ht⟩⁻¹ * ⟨t', ht'⟩) := by
    rw [hw]
    simp only [map_mul, map_inv, hπ₁, hπ₂, inv_one, one_mul, mul_one]
  have hwodd : Odd (orderOf (F7I.piC E w)) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd _ w)
    rw [← Subgroup.orderOf_coe, hw]
    exact hodd
  have hsq : F7I.piC E w * F7I.piC E w = 1 := by
    rw [hπw, ← map_mul]
    have h1 : (⟨t, ht⟩⁻¹ * ⟨t', ht'⟩ * (⟨t, ht⟩⁻¹ * ⟨t', ht'⟩) : ↥E) = 1 := Subtype.ext hc2
    rw [h1, map_one]
  have hord : orderOf (F7I.piC E w) = 1 := by
    have h1 : orderOf (F7I.piC E w) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hwodd
      exact absurd hwodd (by decide)
  have h1 : F7I.piC E (⟨t, ht⟩⁻¹ * ⟨t', ht'⟩) = 1 := by
    rw [← hπw]
    exact orderOf_eq_one_iff.mp hord
  have hO : t⁻¹ * t' ∈ oddCoreOf E := (F7I.piC_eq_one_iff _).mp h1
  have h2 : t⁻¹ * t' = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) hO
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2)
  exact inv_mul_eq_one.mp h2

end F7L3


section Pairs

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y}

theorem p23_e_mem_rLayer (hc : P23Cfg n Y R S t K' W u e g) : e ∈ rLayer (Om R) e := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  obtain ⟨S', hWS'⟩ := hW2.exists_le_sylow
  exact E4I.le_rLayer_of_mem_WSet hΩ h2 hc2 hd.hW hWS' (normalizer_le_centralizer_e hd)
    (T7K.e_mem_inf hd).1

theorem p23_mem_rLayer_self (hc : P23Cfg n Y R S t K' W u e g) {f : Y}
    (hf : f ∈ p23Orb Z t e) : f ∈ rLayer (Om R) f := by
  obtain ⟨m, -, rfl⟩ := hf
  rw [rLayer_conj]
  exact conj_mem_conjSub (p23_e_mem_rLayer hc)

theorem p23_cover_f (hc : P23Cfg n Y R S t K' W u e g) (hZd : P23ZData t u e Z)
    {U : Subgroup Y} (hUZ : U ≤ Z) {f : Y} (hf : f ∈ p23Orb Z t e) (hUf : U ≤ aSub R Z f) :
    rLayer (Om R) f ≤ oddCoreOf (rLayer (Om R) f) ⊔
      (rLayer (Om R) f ⊓ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f)) := by
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hfZ : f ∈ Z := hZd.orb_le hf
  have hZf := hZd.le_cent hfZ
  have hVZ : U ⊔ Subgroup.zpowers f ≤ Z := sup_le hUZ (Subgroup.zpowers_le.mpr hfZ)
  have hfA : f ∈ aSub R Z f := by
    refine (mem_aSub_iff hZf).mpr ⟨hfZ, fun b hb => ?_⟩
    have hbf := Subgroup.mem_centralizer_singleton_iff.mp (F7C.rLayer_le_centralizer f hb)
    have h1 : f * b * f⁻¹ * b⁻¹ = 1 := by rw [← hbf]; group
    rw [h1]
    exact Subgroup.one_mem _
  have hVA : U ⊔ Subgroup.zpowers f ≤ aSub R Z f := sup_le hUf (Subgroup.zpowers_le.mpr hfA)
  refine F7C.rLayer_le_cover hΩ (hZd.isPGroup.to_le hVZ) (hVZ.trans hZf) fun v hv a ha => ?_
  exact ((mem_aSub_iff hZf).mp (hVA hv)).2 a ha

theorem p23_ll3_pairs (hc : P23Cfg n Y R S t K' W u e g) (hZd : P23ZData t u e Z)
    {U : Subgroup Y} (hUZ : U ≤ Z) {f : Y} (hf : f ∈ p23Orb Z t e) (hUf : U ≤ aSub R Z f) :
    ∃ (A₁ A₁' A₂ A₂' : Subgroup Y) (s₁ s₂ : Y),
      (A₁ ∈ RSet (Om R) ∧ A₁' ∈ RSet (Om R) ∧ A₂ ∈ RSet (Om R) ∧ A₂' ∈ RSet (Om R)) ∧
      (A₁ ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) ∧
        A₁' ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) ∧
        A₂ ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) ∧
        A₂' ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f)) ∧
      (IsUniqueInvolution A₁ s₁ ∧ IsUniqueInvolution A₁' s₁ ∧ IsUniqueInvolution A₂ s₂ ∧
        IsUniqueInvolution A₂' s₂) ∧
      Commutes A₁ A₁' ∧ Commutes A₂ A₂' ∧ ¬ Odd (orderOf (s₁⁻¹ * s₂)) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R, ob₁, ob', -, hue⟩ :=
    e_decomp hc
  have hu1 : IsUniqueInvolution R₁ t :=
    ⟨ob₁ ▸ R₁.mul_mem hb₁R hb₁R, hz.ne_one, hz.sq, fun y hy h => hz.unique y (hR₁.1 hy) h⟩
  have hu1' : IsUniqueInvolution R₁' t :=
    ⟨ob' ▸ R₁'.mul_mem hb'R hb'R, hz.ne_one, hz.sq, fun y hy h => hz'.unique y (hR₁'.1 hy) h⟩
  have hNe := normalizer_le_centralizer_e hd
  have hR₁E : R₁ ≤ rLayer (Om R) e := F7C.le_rLayer hRD.1 (hRD.2.trans hNe)
  have hR₁'E : R₁' ≤ rLayer (Om R) e := F7C.le_rLayer hR'D.1 (hR'D.2.trans hNe)
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) :=
    (iSup₂_le fun X hX => hX.2 :
      (⨆ X ∈ DSet (Om R) W, X) ≤ Subgroup.normalizer (W : Set Y)) hd.hg
  have hgE : conjSub g (rLayer (Om R) e) = rLayer (Om R) e := conjSub_rLayer_eq hΩ (hNe hgN)
  have hB2 : IsPGroup 2 (R₁ ⊔ R₁' : Subgroup Y) := by
    have hN : R₁ ≤ Subgroup.normalizer (R₁' : Set Y) := fun x hx =>
      mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hx hcomm)
    exact IsPGroup.to_sup_of_normal_right' (F7C.isPGroup_of_mem_RSet hRD.1)
      (F7C.isPGroup_of_mem_RSet hR'D.1) hN
  have hBE : R₁ ⊔ R₁' ≤ rLayer (Om R) e := sup_le hR₁E hR₁'E
  have hcov := p23_cover_f hc hZd hUZ hf hUf
  obtain ⟨m, hm, rfl⟩ := hf
  have hmt : m * t = t * m :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hm).1
  have hEf : rLayer (Om R) (m * e * m⁻¹) = conjSub m (rLayer (Om R) e) := rLayer_conj m e
  set X := rLayerSub (Om R) (U ⊔ Subgroup.zpowers (m * e * m⁻¹)) with hXdef
  have hB₁ : conjSub m (R₁ ⊔ R₁') ≤ rLayer (Om R) (m * e * m⁻¹) := by
    rw [hEf]
    exact conjSub_mono hBE
  have hB₂ : conjSub (m * g) (R₁ ⊔ R₁') ≤ rLayer (Om R) (m * e * m⁻¹) := by
    rw [hEf, conjSub_mul, ← hgE]
    exact conjSub_mono (conjSub_mono hBE)
  obtain ⟨o₁, ho₁, h₁⟩ := exists_oddCore_conj_le hcov (hB2.map _) hB₁
  obtain ⟨o₂, ho₂, h₂⟩ := exists_oddCore_conj_le hcov (hB2.map _) hB₂
  have hle : ∀ (o x : Y) (Q : Subgroup Y), (∀ v ∈ conjSub x (R₁ ⊔ R₁'), o⁻¹ * v * o ∈ X) →
      Q ≤ R₁ ⊔ R₁' → conjSub (o⁻¹ * x) Q ≤ X := by
    intro o x Q h hQ y hy
    rw [mem_conjSub_iff] at hy
    have h1 := h (x * ((o⁻¹ * x)⁻¹ * y * (o⁻¹ * x)) * x⁻¹) (conj_mem_conjSub (hQ hy))
    have e1 : o⁻¹ * (x * ((o⁻¹ * x)⁻¹ * y * (o⁻¹ * x)) * x⁻¹) * o = y := by group
    rwa [e1] at h1
  refine ⟨conjSub (o₁⁻¹ * m) R₁, conjSub (o₁⁻¹ * m) R₁', conjSub (o₂⁻¹ * (m * g)) R₁,
    conjSub (o₂⁻¹ * (m * g)) R₁', (o₁⁻¹ * m) * t * (o₁⁻¹ * m)⁻¹,
    (o₂⁻¹ * (m * g)) * t * (o₂⁻¹ * (m * g))⁻¹,
    ⟨Q3CL.Thompson.conjSub_mem_RSet hΩ hRD.1 _, Q3CL.Thompson.conjSub_mem_RSet hΩ hR'D.1 _,
      Q3CL.Thompson.conjSub_mem_RSet hΩ hRD.1 _, Q3CL.Thompson.conjSub_mem_RSet hΩ hR'D.1 _⟩,
    ⟨hle o₁ m R₁ h₁ le_sup_left, hle o₁ m R₁' h₁ le_sup_right, hle o₂ (m * g) R₁ h₂ le_sup_left,
      hle o₂ (m * g) R₁' h₂ le_sup_right⟩,
    ⟨hu1.conj _, hu1'.conj _, hu1.conj _, hu1'.conj _⟩, hcomm.conjSub _, hcomm.conjSub _, ?_⟩
  intro hodd
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have htE : t ∈ rLayer (Om R) (m * e * m⁻¹) := by
    rw [hEf]
    have h1 := conj_mem_conjSub (n := m) (hR₁E hu1.mem)
    rwa [show m * t * m⁻¹ = t by rw [hmt]; group] at h1
  have ht'E : m * (u * e) * m⁻¹ ∈ rLayer (Om R) (m * e * m⁻¹) := by
    rw [hEf]
    refine conj_mem_conjSub ?_
    rw [← hd.hgt, ← hgE]
    exact conj_mem_conjSub (hR₁E hu1.mem)
  have hue' : t * (u * e) = (u * e) * t := by
    rw [← mul_assoc, hWab t hd.hzW u hd.huW, mul_assoc, hWab t hd.hzW e heW, mul_assoc]
  have hmt' : m⁻¹ * t = t * m⁻¹ := by
    calc m⁻¹ * t = m⁻¹ * (t * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * t) * m⁻¹ := by rw [hmt]
      _ = t * m⁻¹ := by group
  have htt : t * (m * (u * e) * m⁻¹) = (m * (u * e) * m⁻¹) * t := by
    calc t * (m * (u * e) * m⁻¹) = (t * m) * (u * e) * m⁻¹ := by group
      _ = (m * t) * (u * e) * m⁻¹ := by rw [hmt]
      _ = m * (t * (u * e)) * m⁻¹ := by group
      _ = m * ((u * e) * t) * m⁻¹ := by rw [hue']
      _ = m * (u * e) * (t * m⁻¹) := by group
      _ = m * (u * e) * (m⁻¹ * t) := by rw [hmt']
      _ = (m * (u * e) * m⁻¹) * t := by group
  have hue2 : (u * e) * (u * e) = 1 := by
    calc (u * e) * (u * e) = u * (e * u) * e := by group
      _ = u * (u * e) * e := by rw [hWab e heW u hd.huW]
      _ = (u * u) * (e * e) := by group
      _ = 1 := by rw [hd.hu2, hd.he2, one_mul]
  have ht'2 : (m * (u * e) * m⁻¹) * (m * (u * e) * m⁻¹) = 1 := by
    calc (m * (u * e) * m⁻¹) * (m * (u * e) * m⁻¹) = m * ((u * e) * (u * e)) * m⁻¹ := by group
      _ = 1 := by rw [hue2]; group
  have e1 : (o₁⁻¹ * m) * t * (o₁⁻¹ * m)⁻¹ = o₁⁻¹ * t * o₁ := by
    calc (o₁⁻¹ * m) * t * (o₁⁻¹ * m)⁻¹ = o₁⁻¹ * (m * t) * m⁻¹ * o₁ := by group
      _ = o₁⁻¹ * t * o₁ := by rw [hmt]; group
  have e2 : (o₂⁻¹ * (m * g)) * t * (o₂⁻¹ * (m * g))⁻¹ = o₂⁻¹ * (m * (u * e) * m⁻¹) * o₂ := by
    rw [← hd.hgt]
    group
  rw [e1, e2] at hodd
  have h3 := F7L3.eq_of_odd_orderOf_conj htE ht'E htt hz.sq ht'2 ho₁ ho₂ hodd
  apply hue
  calc u * e = m⁻¹ * (m * (u * e) * m⁻¹) * m := by group
    _ = m⁻¹ * (t * m) := by rw [← h3]; group
    _ = m⁻¹ * (m * t) := by rw [hmt]
    _ = t := by group

end Pairs

section LL3

variable {n : ℕ}

theorem p23E7LL3_of_lemLId (hL : P23E7LemLId n) :
    P23E7LL3 n := by
  classical
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Z hZd f₁ hf₁ hf₁e U hU hUne
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hUZ : U ≤ Z := hU.trans (inf_le_left.trans (aSub_le R Z e))
  have heO : e ∈ p23Orb Z t e := ⟨1, ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, by group⟩
  obtain ⟨hspan, ⟨I⟩, ha⟩ := hL hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd U hUZ hUne e heO
    f₁ hf₁ (Ne.symm hf₁e) (hU.trans inf_le_left) (hU.trans inf_le_right)
  set YU := rLayerSub (Om R) U with hYU
  set P := p23SecFamV R U with hPdef
  have hmemP : ∀ x : SecQuot YU, x ∈ TC.Thin.pSpan P := fun x => by
    rw [hspan]
    exact Subgroup.mem_top x
  let ι : SecQuot YU →* ↥(TC.Thin.pSpan P) :=
    { toFun := fun x => ⟨x, hmemP x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hΦ1 : ∀ x, I.φ (ι x) ∈ AE.e64Sub := fun x => I.range_eq.le ⟨ι x, rfl⟩
  have hΦc : ∀ x, I.φ (ι x) = 1 → x ∈ Subgroup.center (SecQuot YU) := by
    intro x hx
    have hk := I.ker_le (MonoidHom.mem_ker.mpr hx)
    exact Subgroup.mem_center_iff.mpr fun y =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hk (ι y))
  have hEc : ∀ f ∈ p23Orb Z t e, U ≤ aSub R Z f → ∀ y ∈ secImage YU (rLayer (Om R) f ⊓ YU),
      y ∈ Subgroup.center (SecQuot YU) → y = 1 := by
    intro f hf hUf y hy hyc
    have h : y ∈ secImage YU (rLayer (Om R) f ⊓ YU) ⊓ Subgroup.center (SecQuot YU) := ⟨hy, hyc⟩
    rw [ha f hf hUf] at h
    exact Subgroup.mem_bot.mp h
  have h8 : ∀ B ∈ RSet (Om R), Nat.card B = 8 := fun B hB => by
    obtain ⟨J, hJ, hBJ⟩ := exists_isSylow2In_of_mem_RSet hB
    exact (CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC).card8 J hJ B hBJ
  have hcm : ∀ (B : Subgroup (SecQuot YU)) (c : Bool) {α : Finset (Fin 7)} {hα : α.card = 4},
      (B.subgroupOf (TC.Thin.pSpan P)).map I.φ = AE.memBar α hα c → ∀ x : SecQuot YU,
      (∀ y ∈ B, x * y = y * x) → E64F.CentMem ⟨I.φ (ι x), hΦ1 x⟩ α hα c := by
    intro B c α hα hlab x hx y hy
    rw [← hlab] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    show I.φ (ι x) * I.φ w = I.φ w * I.φ (ι x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hx _ hw)
  have hpair : ∀ A A' : Subgroup Y, A ∈ RSet (Om R) → A' ∈ RSet (Om R) →
      A ≤ Subgroup.centralizer (U : Set Y) → A' ≤ Subgroup.centralizer (U : Set Y) →
      ∀ s : Y, IsUniqueInvolution A s → IsUniqueInvolution A' s → Commutes A A' →
      ∀ x : SecQuot YU, (∀ y ∈ secImage YU A, x * y = y * x) →
        (∀ y ∈ secImage YU A', x * y = y * x) →
        ∃ α ∈ AE.e64Sets, ∃ hα : α.card = 4, E64F.CentPair ⟨I.φ (ι x), hΦ1 x⟩ α hα ∧
          ∀ hs : s ∈ YU, I.φ (ι (F7I.piC YU ⟨s, hs⟩)) = AE.zBar α hα := by
    intro A A' hA hA' hAU hA'U s hs hs' hAA' x hxA hxA'
    have hAY : A ≤ YU := F7C.le_rLayerSub hA hAU
    have hA'Y : A' ≤ YU := F7C.le_rLayerSub hA' hA'U
    have hsY : s ∈ YU := hAY hs.mem
    have hLP : secImage YU A ∈ P := ⟨A, hA, hAU, rfl⟩
    have hL'P : secImage YU A' ∈ P := ⟨A', hA', hA'U, rfl⟩
    obtain ⟨huL, h8L, hnL⟩ := F7I.q8_image hAY hsY hs (h8 A hA)
      (Sec6Gen.isQuatSub_of_mem_RSet hΩ hA).exists_not_commute
    obtain ⟨huL', h8L', -⟩ := F7I.q8_image hA'Y hsY hs' (h8 A' hA')
      (Sec6Gen.isQuatSub_of_mem_RSet hΩ hA').exists_not_commute
    obtain ⟨α, hα, hαc, b, hlab⟩ := I.label _ hLP
    obtain ⟨α', hα', hαc', b', hlab'⟩ := I.label _ hL'P
    have hz1 := TC.Thin.phi_map_eq_zBar I.φ (by norm_num) hLP h8L hlab huL
    have hz2 := TC.Thin.phi_map_eq_zBar I.φ (by norm_num) hL'P h8L' hlab' huL'
    obtain rfl : α = α' := AE.eq_of_zBar_eq (by norm_num) (hz1.symm.trans hz2)
    have hb : b' = !b := by
      by_contra hne
      have hbb : b' = b := by
        cases b <;> cases b' <;> first | rfl | exact absurd rfl hne
      obtain ⟨x₁, hx₁, y₁, hy₁, hxy⟩ := hnL
      have hy₁' : I.φ ⟨y₁, TC.Thin.le_pSpan hLP hy₁⟩ ∈ AE.memBar α hαc b := by
        rw [← hlab]
        exact ⟨⟨y₁, TC.Thin.le_pSpan hLP hy₁⟩, Subgroup.mem_subgroupOf.mpr hy₁, rfl⟩
      rw [← hbb, ← hlab'] at hy₁'
      obtain ⟨w, hw, hwy⟩ := hy₁'
      have hcomm : x₁ * (w : SecQuot YU) = (w : SecQuot YU) * x₁ := by
        obtain ⟨a₁, ha₁, rfl⟩ := F7I.mem_map_piC.mp hx₁
        obtain ⟨a₂, ha₂, ha₂w⟩ := F7I.mem_map_piC.mp (Subgroup.mem_subgroupOf.mp hw)
        rw [← ha₂w, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hAA' _ ha₁ _ ha₂)
      apply hxy
      refine TC.Thin.phi_injOn I.φ (by norm_num) hLP h8L hlab
        ((secImage YU A).mul_mem hx₁ hy₁) ((secImage YU A).mul_mem hy₁ hx₁) ?_
      have hwy' : I.φ (ι y₁) = I.φ w := hwy.symm
      have hcw : ι x₁ * w = w * ι x₁ := Subtype.ext hcomm
      show I.φ (ι (x₁ * y₁)) = I.φ (ι (y₁ * x₁))
      simp only [map_mul]
      rw [hwy', ← map_mul, hcw, map_mul]
    have h1 := hcm _ b hlab x hxA
    have h2 := hcm _ b' hlab' x hxA'
    refine ⟨α, hα, hαc, ?_, fun _ => hz1⟩
    rw [hb] at h2
    cases b
    · exact ⟨h2, h1⟩
    · exact ⟨h1, h2⟩
  have hkey : ∀ f, f ∈ p23Orb Z t e → U ≤ aSub R Z f → ∃ hfY : f ∈ YU,
      (⟨I.φ (ι (F7I.piC YU ⟨f, hfY⟩)), hΦ1 _⟩ : ↥AE.e64Sub) ∈
        {a : ↥AE.e64Sub | a * a = 1 ∧ a ≠ 1 ∧ ∃ α ∈ AE.e64Sets, ∃ β ∈ AE.e64Sets, α ≠ β ∧
          ∃ (hα : α.card = 4) (hβ : β.card = 4), E64F.CentPair a α hα ∧
            E64F.CentPair a β hβ} := by
    intro f hf hUf
    have hfZ : f ∈ Z := hZd.orb_le hf
    have hf2 : f * f = 1 := hZd.sq f hfZ
    have hfp : IsPGroup 2 (Subgroup.zpowers f) :=
      CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf2
    have hfE : f ∈ rLayer (Om R) f := p23_mem_rLayer_self hc hf
    have hfX : f ∈ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) :=
      F7C.mem_rLayerSub_of_cover (p23_cover_f hc hZd hUZ hf hUf) hfE hfp
    have hXY : rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) ≤ YU := by
      unfold rLayerSub
      exact iSup₂_le fun R' hR' => iSup_le fun h => F7C.le_rLayerSub hR'
        (h.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)))
    have hfY : f ∈ YU := hXY hfX
    refine ⟨hfY, ?_⟩
    set x := F7I.piC YU ⟨f, hfY⟩ with hxdef
    have hf1 : f ≠ 1 := by
      obtain ⟨m, -, rfl⟩ := hf
      intro h
      exact hc.data.he1 (conj_eq_one_iff.mp h)
    have hxE : x ∈ secImage YU (rLayer (Om R) f ⊓ YU) :=
      F7I.mem_map_piC.mpr ⟨⟨f, hfY⟩, ⟨hfE, hfY⟩, rfl⟩
    have hx1 : I.φ (ι x) ≠ 1 := by
      intro h
      have hO := (F7I.piC_eq_one_iff _).mp (hEc f hf hUf x hxE (hΦc x h))
      exact hf1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard YU) hO hfp)
    have hxx : x * x = 1 := by
      rw [hxdef, ← map_mul]
      have h1 : (⟨f, hfY⟩ : ↥YU) * ⟨f, hfY⟩ = 1 := Subtype.ext hf2
      rw [h1, map_one]
    have hx2 : I.φ (ι x) * I.φ (ι x) = 1 := by
      rw [← map_mul, ← map_mul, hxx, map_one, map_one]
    obtain ⟨A₁, A₁', A₂, A₂', s₁, s₂, ⟨hA₁, hA₁', hA₂, hA₂'⟩, ⟨hX₁, hX₁', hX₂, hX₂'⟩,
      ⟨hu₁, hu₁', hu₂, hu₂'⟩, hc₁, hc₂, hodd⟩ := p23_ll3_pairs hc hZd hUZ hf hUf
    have hXC : rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) ≤
        Subgroup.centralizer ((U ⊔ Subgroup.zpowers f : Subgroup Y) : Set Y) :=
      F7C.rLayerSub_le_centralizer _
    have hXU : ∀ B : Subgroup Y, B ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) →
        B ≤ Subgroup.centralizer (U : Set Y) := fun B hB =>
      (hB.trans hXC).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
    have hXf : ∀ B : Subgroup Y, B ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) →
        ∀ a ∈ B, f * a = a * f := fun B hB a ha =>
      Subgroup.mem_centralizer_iff.mp (hXC (hB ha)) f
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))
    have hcent : ∀ B : Subgroup Y, B ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) →
        ∀ y ∈ secImage YU B, x * y = y * x := by
      intro B hB y hy
      obtain ⟨c, hc', rfl⟩ := F7I.mem_map_piC.mp hy
      rw [hxdef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hXf B hB _ hc')
    have hXE : ∀ B : Subgroup Y, B ∈ RSet (Om R) →
        B ≤ rLayerSub (Om R) (U ⊔ Subgroup.zpowers f) → B ≤ rLayer (Om R) f := fun B hB hBX =>
      F7C.le_rLayer hB fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hXf B hBX a ha).symm
    obtain ⟨α, hα, hαc, hcα, hzα⟩ := hpair A₁ A₁' hA₁ hA₁' (hXU _ hX₁) (hXU _ hX₁') s₁ hu₁
      hu₁' hc₁ x (hcent _ hX₁) (hcent _ hX₁')
    obtain ⟨β, hβ, hβc, hcβ, hzβ⟩ := hpair A₂ A₂' hA₂ hA₂' (hXU _ hX₂) (hXU _ hX₂') s₂ hu₂
      hu₂' hc₂ x (hcent _ hX₂) (hcent _ hX₂')
    refine ⟨Subtype.ext hx2, fun h => hx1 (congrArg Subtype.val h), α, hα, β, hβ, ?_, hαc, hβc,
      hcα, hcβ⟩
    rintro rfl
    have hs₁Y : s₁ ∈ YU := hXY (hX₁ hu₁.mem)
    have hs₂Y : s₂ ∈ YU := hXY (hX₂ hu₂.mem)
    have hs₁E : s₁ ∈ rLayer (Om R) f := hXE A₁ hA₁ hX₁ hu₁.mem
    have hs₂E : s₂ ∈ rLayer (Om R) f := hXE A₂ hA₂ hX₂ hu₂.mem
    have heq : I.φ (ι (F7I.piC YU ⟨s₁, hs₁Y⟩)) = I.φ (ι (F7I.piC YU ⟨s₂, hs₂Y⟩)) :=
      (hzα hs₁Y).trans (hzβ hs₂Y).symm
    have hwc : (F7I.piC YU ⟨s₁, hs₁Y⟩)⁻¹ * F7I.piC YU ⟨s₂, hs₂Y⟩ ∈
        Subgroup.center (SecQuot YU) :=
      hΦc _ (by rw [map_mul, map_mul, map_inv, map_inv, heq, inv_mul_cancel])
    have hwE : (F7I.piC YU ⟨s₁, hs₁Y⟩)⁻¹ * F7I.piC YU ⟨s₂, hs₂Y⟩ ∈
        secImage YU (rLayer (Om R) f ⊓ YU) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (F7I.mem_map_piC.mpr ⟨_, ⟨hs₁E, hs₁Y⟩, rfl⟩))
        (F7I.mem_map_piC.mpr ⟨_, ⟨hs₂E, hs₂Y⟩, rfl⟩)
    have h1 := hEc f hf hUf _ hwE hwc
    have hO : s₁⁻¹ * s₂ ∈ oddCoreOf YU := (F7I.piC_eq_iff _ _).mp (inv_mul_eq_one.mp h1)
    exact hodd (Odd.of_dvd_nat (oddCoreOf_odd_natCard YU) (Subgroup.orderOf_dvd_natCard _ hO))
  have hinj : ∀ f, f ∈ p23Orb Z t e → U ≤ aSub R Z f → ∀ f', f' ∈ p23Orb Z t e →
      U ≤ aSub R Z f' → ∀ (hfY : f ∈ YU) (hf'Y : f' ∈ YU),
      I.φ (ι (F7I.piC YU ⟨f, hfY⟩)) = I.φ (ι (F7I.piC YU ⟨f', hf'Y⟩)) → f = f' := by
    intro f hf hUf f' hf' hUf' hfY hf'Y heq
    have hfZ : f ∈ Z := hZd.orb_le hf
    have hf'Z : f' ∈ Z := hZd.orb_le hf'
    have hfp : IsPGroup 2 (Subgroup.zpowers f) :=
      CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one (hZd.sq f hfZ)
    have hf'p : IsPGroup 2 (Subgroup.zpowers f') :=
      CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one (hZd.sq f' hf'Z)
    have hc' : (F7I.piC YU ⟨f, hfY⟩)⁻¹ * F7I.piC YU ⟨f', hf'Y⟩ ∈
        Subgroup.center (SecQuot YU) :=
      hΦc _ (by rw [map_mul, map_mul, map_inv, map_inv, heq, inv_mul_cancel])
    have hc'' := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc')
    have hxE : F7I.piC YU ⟨f, hfY⟩ ∈ secImage YU (rLayer (Om R) f ⊓ YU) :=
      F7I.mem_map_piC.mpr ⟨⟨f, hfY⟩, ⟨p23_mem_rLayer_self hc hf, hfY⟩, rfl⟩
    have hX'Q : rLayerSub (Om R) (U ⊔ Subgroup.zpowers f') ≤
        ((secImage YU (rLayer (Om R) f ⊓ YU)).comap (F7I.piC YU)).map YU.subtype := by
      unfold rLayerSub
      refine iSup₂_le fun R' hR' => iSup_le fun hR'C => ?_
      have hR'U : R' ≤ Subgroup.centralizer (U : Set Y) :=
        hR'C.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      have hR'Y : R' ≤ YU := F7C.le_rLayerSub hR' hR'U
      have hR'f' : ∀ r ∈ R', f' * r = r * f' := fun r hr =>
        Subgroup.mem_centralizer_iff.mp (hR'C hr) f'
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers f'))
      have hcomm : ∀ r ∈ R', r * f * r⁻¹ * f⁻¹ ∈ oddCoreOf YU := by
        intro r hr
        have hrx' : Commute (F7I.piC YU ⟨r, hR'Y hr⟩) (F7I.piC YU ⟨f', hf'Y⟩) := by
          show F7I.piC YU ⟨r, hR'Y hr⟩ * F7I.piC YU ⟨f', hf'Y⟩ =
            F7I.piC YU ⟨f', hf'Y⟩ * F7I.piC YU ⟨r, hR'Y hr⟩
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hR'f' r hr).symm
        have hrc : Commute (F7I.piC YU ⟨r, hR'Y hr⟩)
            ((F7I.piC YU ⟨f, hfY⟩)⁻¹ * F7I.piC YU ⟨f', hf'Y⟩)⁻¹ := hc'' _
        have hrx := hrx'.mul_right hrc
        rw [show F7I.piC YU ⟨f', hf'Y⟩ * ((F7I.piC YU ⟨f, hfY⟩)⁻¹ * F7I.piC YU ⟨f', hf'Y⟩)⁻¹ =
          F7I.piC YU ⟨f, hfY⟩ by group] at hrx
        have hmem : r * f * r⁻¹ * f⁻¹ ∈ YU :=
          YU.mul_mem (YU.mul_mem (YU.mul_mem (hR'Y hr) hfY) (YU.inv_mem (hR'Y hr)))
            (YU.inv_mem hfY)
        refine (F7I.piC_eq_one_iff ⟨_, hmem⟩).mp ?_
        rw [show (⟨r * f * r⁻¹ * f⁻¹, hmem⟩ : ↥YU) =
          ⟨r, hR'Y hr⟩ * ⟨f, hfY⟩ * (⟨r, hR'Y hr⟩ : ↥YU)⁻¹ * (⟨f, hfY⟩ : ↥YU)⁻¹ from rfl,
          map_mul, map_mul, map_mul, map_inv, map_inv, hrx.eq]
        group
      obtain ⟨o, ho, hof⟩ := F7L3.exists_oddCore_conj_comm hR'Y (F7C.isPGroup_of_mem_RSet hR')
        hfY hfp hcomm
      have hoY : o ∈ YU := oddCoreOf_le_self YU ho
      have hR'o : conjSub o⁻¹ R' ≤ rLayer (Om R) f := by
        refine F7C.le_rLayer (Q3CL.Thompson.conjSub_mem_RSet hΩ hR' o⁻¹) fun y hy => ?_
        rw [mem_conjSub_iff, inv_inv] at hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := hof _ hy
        rwa [show o⁻¹ * (o * y * o⁻¹) * o = y by group] at h
      intro r hr
      have hrY : o⁻¹ * r * o ∈ YU := YU.mul_mem (YU.mul_mem (YU.inv_mem hoY) (hR'Y hr)) hoY
      have hrE : o⁻¹ * r * o ∈ rLayer (Om R) f := by
        have h := conj_mem_conjSub (n := o⁻¹) hr
        rw [inv_inv] at h
        exact hR'o h
      refine ⟨⟨r, hR'Y hr⟩, ?_, rfl⟩
      show F7I.piC YU ⟨r, hR'Y hr⟩ ∈ secImage YU (rLayer (Om R) f ⊓ YU)
      have he : F7I.piC YU ⟨r, hR'Y hr⟩ = F7I.piC YU ⟨o⁻¹ * r * o, hrY⟩ := by
        rw [F7I.piC_eq_iff]
        show r⁻¹ * (o⁻¹ * r * o) ∈ oddCoreOf YU
        have h1 : r⁻¹ * o⁻¹ * r⁻¹⁻¹ ∈ oddCoreOf YU :=
          mem_normalizer_oddCoreOf_of_mem_normalizer
            (Subgroup.le_normalizer (YU.inv_mem (hR'Y hr))) (Subgroup.inv_mem _ ho)
        have e : r⁻¹ * (o⁻¹ * r * o) = (r⁻¹ * o⁻¹ * r⁻¹⁻¹) * o := by group
        rw [e]
        exact Subgroup.mul_mem _ h1 ho
      rw [he]
      exact F7I.mem_map_piC.mpr ⟨_, ⟨hrE, hrY⟩, rfl⟩
    obtain ⟨y, hy, hyf⟩ := hX'Q (F7C.mem_rLayerSub_of_cover (p23_cover_f hc hZd hUZ hf' hUf')
      (p23_mem_rLayer_self hc hf') hf'p)
    have hy' : y = ⟨f', hf'Y⟩ := Subtype.ext hyf
    have hx'E : F7I.piC YU ⟨f', hf'Y⟩ ∈ secImage YU (rLayer (Om R) f ⊓ YU) := by
      rw [← hy']
      exact hy
    have h1 := hEc f hf hUf _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxE) hx'E) hc'
    have hO : f⁻¹ * f' ∈ oddCoreOf YU := (F7I.piC_eq_iff _ _).mp (inv_mul_eq_one.mp h1)
    have hsq : (f⁻¹ * f') * (f⁻¹ * f') = 1 := hZd.sq _ (Z.mul_mem (Z.inv_mem hfZ) hf'Z)
    have h3 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard YU) hO
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq)
    exact inv_mul_eq_one.mp h3
  have hcount : {f | f ∈ p23Orb Z t e ∧ U ≤ aSub R Z f}.ncard ≤
      {a : ↥AE.e64Sub | a * a = 1 ∧ a ≠ 1 ∧ ∃ α ∈ AE.e64Sets, ∃ β ∈ AE.e64Sets, α ≠ β ∧
        ∃ (hα : α.card = 4) (hβ : β.card = 4), E64F.CentPair a α hα ∧
          E64F.CentPair a β hβ}.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun f => if h : f ∈ YU then
      (⟨I.φ (ι (F7I.piC YU ⟨f, h⟩)), hΦ1 _⟩ : ↥AE.e64Sub) else 1) ?_ ?_
    · intro f hf
      obtain ⟨hfY, hmem⟩ := hkey f hf.1 hf.2
      simp only [dif_pos hfY]
      exact hmem
    · intro f hf f' hf' h
      obtain ⟨hfY, -⟩ := hkey f hf.1 hf.2
      obtain ⟨hf'Y, -⟩ := hkey f' hf'.1 hf'.2
      simp only [dif_pos hfY, dif_pos hf'Y] at h
      exact hinj f hf.1 hf.2 f' hf'.1 hf'.2 hfY hf'Y (congrArg Subtype.val h)
  exact hcount.trans E64F.ncard_twinInv_le

theorem p23E7LL3_of_lemL (hL : P23E7LemL n) : P23E7LL3 n :=
  p23E7LL3_of_lemLId (p23E7LemLId_of_lemL hL)

end LL3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
