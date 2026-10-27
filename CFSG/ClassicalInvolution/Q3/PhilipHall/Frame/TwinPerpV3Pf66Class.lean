module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtSylow
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu
public import CFSG.ClassicalInvolution.SmallCases.A7Q1B
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPrintedDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2208
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson

section Class

theorem q8_centralizer_aux : ∀ w x : QuaternionGroup 2, w ^ 2 ≠ 1 → x * w = w * x →
    x = 1 ∨ x = w ∨ x = w ^ 2 ∨ x = w ^ 3 := by
  decide

variable {G : Type} [Group G]

theorem eq_of_comm_q8 {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2) {w x : G} (hw : w ∈ R)
    (hx : x ∈ R) (hw2 : w * w ≠ 1) (hc : x * w = w * x) :
    x = 1 ∨ x = w ∨ x = w * w ∨ x = w * w * w := by
  have hw2' : (e ⟨w, hw⟩) ^ 2 ≠ 1 := by
    intro h1
    apply hw2
    have : (⟨w, hw⟩ : ↥R) ^ 2 = 1 := e.injective (by rw [map_pow, h1, map_one])
    simpa [pow_two] using congrArg Subtype.val this
  have hc' : e ⟨x, hx⟩ * e ⟨w, hw⟩ = e ⟨w, hw⟩ * e ⟨x, hx⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hc)
  rcases q8_centralizer_aux _ _ hw2' hc' with h | h | h | h
  · left
    have := e.injective (h.trans (map_one e).symm)
    simpa using congrArg Subtype.val this
  · right; left
    have := e.injective h
    simpa using congrArg Subtype.val this
  · right; right; left
    have := e.injective (h.trans (by rw [← map_pow]))
    simpa [pow_two] using congrArg Subtype.val this
  · right; right; right
    have := e.injective (h.trans (by rw [← map_pow]))
    simpa [pow_succ, mul_assoc] using congrArg Subtype.val this

theorem q8_of_sylow [Finite G] {K R P : Subgroup G} (hR : IsSylow2In R K) (hP : IsSylow2In P K)
    (e : Nonempty (↥P ≃* QuaternionGroup 2)) : Nonempty (↥R ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := e
  obtain ⟨x, -, hx⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hR hP
  exact ⟨(Subgroup.equivMapOfInjective R (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).trans
    ((MulEquiv.subgroupCongr hx).trans e)⟩

theorem sq_cases_of_cyc {x w t : G} (e : w * w = t) (ht2 : t * t = 1)
    (h : x = 1 ∨ x = w ∨ x = w * w ∨ x = w * w * w) :
    (x * x = 1 ∧ (x = 1 ∨ x = t)) ∨ (x * x = t ∧ (x = w ∨ x = w⁻¹)) := by
  have h3 : w * w * w = w⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc w * w * w * w = (w * w) * (w * w) := by group
      _ = 1 := by rw [e]; exact ht2
  rcases h with rfl | rfl | rfl | rfl
  · left; exact ⟨by simp, Or.inl rfl⟩
  · right; exact ⟨e, Or.inl rfl⟩
  · left
    exact ⟨by rw [e]; exact ht2, Or.inr e⟩
  · right
    refine ⟨?_, Or.inr h3⟩
    rw [h3]
    calc w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
      _ = t⁻¹ := by rw [e]
      _ = t := inv_eq_of_mul_eq_one_right ht2

end Class

section Cases



variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem inv_cases_of_mem_sup_inf_W (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {t : G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hne : J ≠ K) (hz : IsUniqueInvolution K t) (hzJ : IsUniqueInvolution J t)
    (hq8K : ∀ R, IsSylow2In R K → Nonempty (↥R ≃* QuaternionGroup 2))
    (hq8J : ∀ R, IsSylow2In R J → Nonempty (↥R ≃* QuaternionGroup 2))
    {W : Subgroup G} (hW2 : IsPGroup 2 W) (hcommW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {wK wJ : G} (hwKK : wK ∈ K) (hwKW : wK ∈ W) (hwJJ : wJ ∈ J) (hwJW : wJ ∈ W)
    (oK : orderOf wK = 4) (oJ : orderOf wJ = 4) {a : G} (ha : a ∈ K ⊔ J) (haW : a ∈ W)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ R₁ R₂ : Subgroup G, IsSylow2In R₁ K ∧ IsSylow2In R₂ J ∧ Commutes R₁ R₂ ∧ wK ∈ R₁ ∧
      wJ ∈ R₂ ∧ (a = t ∨ a = wK * wJ ∨ a = wK⁻¹ * wJ ∨ a = wK * wJ⁻¹ ∨ a = wK⁻¹ * wJ⁻¹) := by
  have hzJ' : J ∈ twinSet Ω K := ⟨hJ, t, hz, hzJ⟩
  have hKN : K ≤ Subgroup.normalizer (J : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hJ hne.symm hz hzJ
  have hJN : J ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hJ hK hne hzJ hz
  have hKJ : K ⊔ J ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hJN
  have hKJ' : K ⊔ J ≤ Subgroup.normalizer (J : Set G) := sup_le hKN Subgroup.le_normalizer
  set A : Subgroup G := Subgroup.closure ({wK, wJ, a} : Set G) with hA
  have hAW : A ≤ W := by
    rw [hA, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hwKW
    · exact hwJW
    · exact haW
  have hA2 : IsPGroup 2 A := hW2.to_le hAW
  have hAKJ : A ≤ K ⊔ J := by
    rw [hA, Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left hwKK
    · exact Subgroup.mem_sup_right hwJJ
    · exact ha
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, -, -, h2grp⟩ := TwinFrameTgt.exists_twinSylow_normalized_gen hΩ hK hz
    hzJ' hne hA2 (hAKJ.trans hKJ) (hAKJ.trans hKJ')
  have hsyl : IsSylow2In (R₁ ⊔ R₂) (K ⊔ J) :=
    A7Q.Gen.isSylow2In_sup_of_twin hΩ hK hJ hne hz hzJ hR₁ hR₂ hc
  have hQle : (A ⊔ R₁) ⊔ R₂ ≤ K ⊔ J :=
    sup_le (sup_le hAKJ (hR₁.1.trans le_sup_left)) (hR₂.1.trans le_sup_right)
  have hQeq := hsyl.2.2 _ hQle h2grp (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hAle : A ≤ R₁ ⊔ R₂ := (le_sup_left.trans le_sup_left : A ≤ (A ⊔ R₁) ⊔ R₂).trans hQeq.le
  have hwK : wK ∈ R₁ := by
    have hQ2 : IsPGroup 2 ↥(R₁ ⊔ Subgroup.zpowers wK) :=
      h2grp.to_le (sup_le (le_sup_right.trans le_sup_left)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.subset_closure (by simp : wK ∈ ({wK, wJ, a} : Set G)))))))
    have := hR₁.2.2 _ (sup_le hR₁.1 (Subgroup.zpowers_le.mpr hwKK)) hQ2 le_sup_left
    have h := (Subgroup.mem_sup_right (Subgroup.mem_zpowers wK) : wK ∈ R₁ ⊔ Subgroup.zpowers wK)
    rwa [this] at h
  have hwJ : wJ ∈ R₂ := by
    have hQ2 : IsPGroup 2 ↥(R₂ ⊔ Subgroup.zpowers wJ) :=
      h2grp.to_le (sup_le le_sup_right
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.subset_closure (by simp : wJ ∈ ({wK, wJ, a} : Set G)))))))
    have := hR₂.2.2 _ (sup_le hR₂.1 (Subgroup.zpowers_le.mpr hwJJ)) hQ2 le_sup_left
    have h := (Subgroup.mem_sup_right (Subgroup.mem_zpowers wJ) : wJ ∈ R₂ ⊔ Subgroup.zpowers wJ)
    rwa [this] at h
  refine ⟨R₁, R₂, hR₁, hR₂, hc, hwK, hwJ, ?_⟩
  have haR : a ∈ R₁ ⊔ R₂ := hAle (Subgroup.subset_closure (by simp))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left R₁ R₂
    (T7A.le_normalizer_of_commutes hc)] at haR
  obtain ⟨ρ, hρ, ρ', hρ', hρa⟩ := haR
  have hρa' : ρ * ρ' = a := hρa
  subst hρa'
  obtain ⟨eK⟩ := hq8K R₁ hR₁
  obtain ⟨eJ⟩ := hq8J R₂ hR₂
  have e1 : wK * wK = t := T7A.sq_eq_of_orderOf_four hz hwKK oK
  have e2 : wJ * wJ = t := T7A.sq_eq_of_orderOf_four hzJ hwJJ oJ
  have ht2 : t * t = 1 := hz.sq
  have ht1 : t ≠ 1 := hz.ne_one
  have hρK : ρ ∈ K := hR₁.1 hρ
  have hρ'J : ρ' ∈ J := hR₂.1 hρ'
  have c1 : ρ * wK = wK * ρ := by
    have h1 := hcommW _ haW _ hwKW
    have h2 : (ρ * wK) * ρ' = (wK * ρ) * ρ' := by
      calc (ρ * wK) * ρ' = ρ * (wK * ρ') := by group
        _ = ρ * (ρ' * wK) := by rw [hc wK hwK ρ' hρ']
        _ = (ρ * ρ') * wK := by group
        _ = wK * (ρ * ρ') := h1
        _ = (wK * ρ) * ρ' := by group
    exact mul_right_cancel h2
  have c2 : ρ' * wJ = wJ * ρ' := by
    have h1 := hcommW _ haW _ hwJW
    have h2 : ρ * (ρ' * wJ) = ρ * (wJ * ρ') := by
      calc ρ * (ρ' * wJ) = (ρ * ρ') * wJ := by group
        _ = wJ * (ρ * ρ') := h1
        _ = (wJ * ρ) * ρ' := by group
        _ = (ρ * wJ) * ρ' := by rw [hc ρ hρ wJ hwJ]
        _ = ρ * (wJ * ρ') := by group
    exact mul_left_cancel h2
  have hρc := sq_cases_of_cyc e1 ht2 (eq_of_comm_q8 eK hwK hρ (by rw [e1]; exact ht1) c1)
  have hρ'c := sq_cases_of_cyc e2 ht2 (eq_of_comm_q8 eJ hwJ hρ' (by rw [e2]; exact ht1) c2)
  have hcomm : ρ * ρ' = ρ' * ρ := hc ρ hρ ρ' hρ'
  have hsqa : (ρ * ρ') * (ρ * ρ') = (ρ * ρ) * (ρ' * ρ') := by
    calc (ρ * ρ') * (ρ * ρ') = ρ * (ρ' * ρ) * ρ' := by group
      _ = ρ * (ρ * ρ') * ρ' := by rw [hcomm]
      _ = (ρ * ρ) * (ρ' * ρ') := by group
  rcases hρc with ⟨s1, h1 | h1⟩ | ⟨s1, h1 | h1⟩ <;>
    rcases hρ'c with ⟨s2, h2 | h2⟩ | ⟨s2, h2 | h2⟩ <;>
    first
    | (exfalso; apply ht1; rw [hsqa, s1, s2] at ha2; simpa using ha2)
    | (refine absurd ?_ ha1; rw [h1, h2]; simp [ht2]; done)
    | (rw [h1, h2]; simp; done)

end Cases

section Cent



variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {t u₁ u₂ u₃ : G}

theorem exists_orderOf_four_of_mem_USet (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∀ R, IsSylow2In R L → Nonempty (↥R ≃* QuaternionGroup 2)) {U : Subgroup G}
    (hU : U ∈ USet Ω) : ∃ g ∈ U, orderOf g = 4 := by
  obtain ⟨R, -, J, hJ, hRJ, -, hcyc, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨e⟩ := hq8 J hJ R hRJ
  have h8 : Nat.card R = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h4 : Nat.card U = 4 := by omega
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  refine ⟨(g : G), g.2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, h4]

theorem centralizersPrinted_of_adapted (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ t u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    (hq8 : ∀ L ∈ Ω, ∀ R, IsSylow2In R L → Nonempty (↥R ≃* QuaternionGroup 2))
    {H : Subgroup G} (hCz : Subgroup.centralizer ({t} : Set G) ≤ H)
    (hCent : ∀ (J L₃ : Subgroup G) (x₁ x₂ x₃ : G), A7T22.Hyp22G Ω K J L₃ t x₁ x₂ x₃ →
      (∃ W' ∈ WSet Ω, x₁ ∈ W' ∧ x₂ ∈ W') → Subgroup.centralizer ({x₁ * x₂} : Set G) ≤ H)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hKW : K ⊓ W ∈ USet Ω) :
    TwinDisc.CentralizersPrinted Ω K W H := by
  have hΩ : HypOmegaGen Ω := hd.hyp
  intro J hJ a ha haW ha1 ha2
  have hJt : J ∈ twinSet Ω K := by rw [← hperp]; exact hJ
  by_cases hJK : J = K
  · rw [hJK, sup_idem] at ha
    have : a = t := (hd.hz.unique a ha ha2).resolve_left ha1
    rw [this]
    exact hCz
  · obtain ⟨wK, hwK, oK⟩ := exists_orderOf_four_of_mem_USet hΩ hq8 hKW
    have hwKK : wK ∈ K := (inf_le_left : K ⊓ W ≤ K) hwK
    have hwKW : wK ∈ W := (inf_le_right : K ⊓ W ≤ W) hwK
    have e1 : wK * wK = t := T7A.sq_eq_of_orderOf_four hd.hz hwKK oK
    have htW : t ∈ W := e1 ▸ W.mul_mem hwKW hwKW
    have hzJ : IsUniqueInvolution J t := isUniqueInvolution_of_mem_twinSet hd.hz hJt
    have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
    obtain ⟨ρJ, hρJ⟩ := Q3.TL4.exists_rep_of_involution_mem_gen c hP.cls hJt.1 hzJ htW
    obtain ⟨wJ, hwJ, oJ⟩ := Q3T8.Asc77.C22G.exists_orderOf_four_mem_inf_W c ρJ
    rw [hρJ] at hwJ
    have hwJJ : wJ ∈ J := hwJ.1
    have hwJW : wJ ∈ W := hwJ.2
    obtain ⟨R₁, R₂, hR₁, hR₂, hc, hwK1, hwJ2, hcases⟩ := inv_cases_of_mem_sup_inf_W hΩ hd.mem hJt.1
      hJK hd.hz hzJ (fun R hR => hq8 K hd.mem R hR) (fun R hR => hq8 J hJt.1 R hR)
      (Thompson.isPGroup_of_mem_WSet hW) (fun x hx y hy => c.comm_W x hx y hy) hwKK hwKW hwJJ hwJW
      oK oJ ha haW ha2 ha1
    have key : ∀ x₁ x₂ : G, x₁ ∈ R₁ → x₂ ∈ R₂ → x₁ ∈ W → x₂ ∈ W → orderOf x₁ = 4 →
        orderOf x₂ = 4 → Subgroup.centralizer ({x₁ * x₂} : Set G) ≤ H := by
      intro x₁ x₂ hx₁ hx₂ hx₁W hx₂W o₁ o₂
      obtain ⟨L₃, w, hd''⟩ := hd.exists_datum_of_pair (mem_twinSet_self hd.mem hd.hz) hJt hJK hR₁
        hR₂ hc hx₁ hx₂ o₁ o₂
      exact hCent J L₃ x₁ x₂ w hd'' ⟨W, hW, hx₁W, hx₂W⟩
    have hKi : wK⁻¹ ∈ R₁ := R₁.inv_mem hwK1
    have hJi : wJ⁻¹ ∈ R₂ := R₂.inv_mem hwJ2
    rcases hcases with h | h | h | h | h <;> rw [h]
    · exact hCz
    · exact key _ _ hwK1 hwJ2 hwKW hwJW oK oJ
    · exact key _ _ hKi hwJ2 (W.inv_mem hwKW) hwJW (by rw [orderOf_inv]; exact oK) oJ
    · exact key _ _ hwK1 hJi hwKW (W.inv_mem hwJW) oK (by rw [orderOf_inv]; exact oJ)
    · exact key _ _ hKi hJi (W.inv_mem hwKW) (W.inv_mem hwJW) (by rw [orderOf_inv]; exact oK)
        (by rw [orderOf_inv]; exact oJ)

end Cent

section Q8All



theorem q8_all_of_core {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (hC : CoreData n Y R S t) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ R' : Subgroup Y, IsSylow2In R' L →
      Nonempty (↥R' ≃* QuaternionGroup 2) := by
  rintro _ ⟨g', rfl⟩ R' hR'
  obtain ⟨P, hP', ⟨e⟩⟩ := hC.datum.exists_sylow_q8 hC.q8
  exact q8_of_sylow hR' (hP'.conj g') ⟨(Subgroup.equivMapOfInjective P (MulAut.conj g').toMonoidHom
    (MulAut.conj g').injective).symm.trans e⟩

end Q8All

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
