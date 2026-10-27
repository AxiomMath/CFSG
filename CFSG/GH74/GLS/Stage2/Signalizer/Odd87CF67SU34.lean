module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SBender
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S

open Subgroup Matrix CFSG CFSG.GH74.Uniqueness.Bender CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
  CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

theorem not_orderOf_fifteen {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 60)
    (x : G) : orderOf x ≠ 15 := by
  intro hx
  have hH : Nat.card (zpowers x) = 15 := by rw [Nat.card_zpowers, hx]
  have hidx : (zpowers x).index = 4 := by
    have := Subgroup.card_mul_index (zpowers x)
    rw [hH, hG] at this
    omega
  have hne : zpowers x ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hG] at hH
    omega
  have hcore : (zpowers x).normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x).normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ (zpowers x).normalCore_le)) hne
  have h1 := (zpowers x).index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot, hG, hidx] at h1
  norm_num [Nat.factorial] at h1

theorem core_abstract {P : Type} [Group P] [Finite P] (hP : Nat.card P = 62400) (J₀ A₀ : Subgroup P)
    (hJ₀card : Nat.card J₀ = 60) [IsSimpleGroup J₀] (hA₀card : Nat.card A₀ = 5)
    (hcomm_JA : ∀ x ∈ J₀, ∀ y ∈ A₀, x * y = y * x) (hinf : J₀ ⊓ A₀ = ⊥)
    (hcent : ∀ x₀ ∈ A₀, x₀ ≠ 1 → ∀ w : P, x₀ * w = w * x₀ → w ∈ J₀ ⊔ A₀)
    (V : Subgroup P) (hV : Nat.card V = 25) (k : P) (hk1 : k ≠ 1) (hs : k ^ 3 = 1 ∨ k ^ 13 = 1)
    (hcomm : ∀ v ∈ V, v * k = k * v) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 5 (show 5 ∣ Nat.card J₀ by rw [hJ₀card]; norm_num)
  set σ' : P := (σ : P) with hσ'def
  have hσ' : orderOf σ' = 5 := by rw [hσ'def, Subgroup.orderOf_coe σ]; exact hσ
  have hσJ : σ' ∈ J₀ := σ.2
  have hA₀ne : A₀ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hA₀card; omega
  obtain ⟨⟨x₀, hx₀A⟩, hx₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA₀ne
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  set Z₅ : Subgroup P := zpowers σ' with hZ₅
  have hZ₅J : Z₅ ≤ J₀ := (Subgroup.zpowers_le).mpr hσJ
  have hZ₅card : Nat.card Z₅ = 5 := by rw [Nat.card_zpowers, hσ']
  have hZA_comm : ∀ x ∈ Z₅, ∀ y ∈ A₀, x * y = y * x := fun x hx y hy => hcomm_JA x (hZ₅J hx) y hy
  have hZA_inf : Z₅ ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_right _ hZ₅J
  have hV₀card : Nat.card ↥(Z₅ ⊔ A₀) = 25 := by
    have := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hZA_comm
    rw [hZA_inf, Subgroup.card_bot, hZ₅card, hA₀card] at this
    omega
  have hV₀p : IsPGroup 5 ↥(Z₅ ⊔ A₀) := IsPGroup.of_card (n := 2) (by rw [hV₀card]; norm_num)
  have hVp : IsPGroup 5 ↥V := IsPGroup.of_card (n := 2) (by rw [hV]; norm_num)
  have hidx₀ : (Z₅ ⊔ A₀).index = 2496 := by
    have := Subgroup.card_mul_index (Z₅ ⊔ A₀)
    rw [hV₀card, hP] at this
    omega
  have hidxV : V.index = 2496 := by
    have := Subgroup.card_mul_index V
    rw [hV, hP] at this
    omega
  obtain ⟨c, hc⟩ := exists_conj_of_prime_index 5 hV₀p hVp
    (by rw [hidx₀]; norm_num) (by rw [hidxV]; norm_num)
  set k' : P := c⁻¹ * k * c with hk'def
  have hk'comm : ∀ w ∈ Z₅ ⊔ A₀, w * k' = k' * w := by
    intro w hw
    have hxV : c * w * c⁻¹ ∈ V := by
      apply (hc _).mpr
      have : c⁻¹ * (c * w * c⁻¹) * c = w := by group
      rw [this]; exact hw
    have := hcomm _ hxV
    calc w * k' = c⁻¹ * ((c * w * c⁻¹) * k) * c := by rw [hk'def]; group
      _ = c⁻¹ * (k * (c * w * c⁻¹)) * c := by rw [this]
      _ = k' * w := by rw [hk'def]; group
  have hk'1 : k' ≠ 1 := by
    intro h
    apply hk1
    have : k = c * k' * c⁻¹ := by rw [hk'def]; group
    rw [this, h]; group
  have hk'pow : ∀ n : ℕ, k' ^ n = c⁻¹ * k ^ n * c := by
    intro n
    have := conj_pow (a := c⁻¹) (b := k) (i := n)
    simp only [inv_inv] at this
    rw [hk'def]; exact this
  have hk'sup : k' ∈ J₀ ⊔ A₀ :=
    hcent x₀ hx₀A hx₀1' k' (hk'comm x₀ ((le_sup_right : A₀ ≤ Z₅ ⊔ A₀) hx₀A))
  have hJAcard : Nat.card ↥(J₀ ⊔ A₀) = 300 := by
    have := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomm_JA
    rw [hinf, Subgroup.card_bot, hJ₀card, hA₀card] at this
    omega
  rcases hs with h3 | h13
  ·
    have hk'3 : k' ^ 3 = 1 := by rw [hk'pow, h3]; group
    obtain ⟨j, hjJ, a, haA, hja⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.exists_mul_of_mem_sup' hcomm_JA hk'sup
    have hacomm : Commute j a := hcomm_JA j hjJ a haA
    have hja3 : j ^ 3 * a ^ 3 = 1 := by rw [← hacomm.mul_pow, ← hja]; exact hk'3
    have ha3 : a ^ 3 = 1 := by
      have h1 : a ^ 3 ∈ J₀ ⊓ A₀ := by
        refine ⟨?_, A₀.pow_mem haA 3⟩
        rw [eq_inv_of_mul_eq_one_right hja3]
        exact J₀.inv_mem (J₀.pow_mem hjJ 3)
      rw [hinf] at h1
      exact Subgroup.mem_bot.mp h1
    have ha1 : a = 1 := by
      have h5 : orderOf a ∣ 5 := hA₀card ▸ Subgroup.orderOf_dvd_natCard A₀ haA
      have h3' : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
      have := Nat.dvd_gcd h5 h3'
      have h35 : Nat.gcd 5 3 = 1 := by norm_num
      rw [h35] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
    rw [ha1, mul_one] at hja
    have hk'J : k' ∈ J₀ := hja ▸ hjJ
    have hσk : σ' * k' = k' * σ' := hk'comm σ' ((le_sup_left : Z₅ ≤ Z₅ ⊔ A₀) (Subgroup.mem_zpowers σ'))
    set jj : ↥J₀ := ⟨k', hk'J⟩ with hjj
    have hjj1 : jj ≠ 1 := fun h => hk'1 (congrArg Subtype.val h)
    have hjj3 : jj ^ 3 = 1 := Subtype.ext (by simpa using hk'3)
    have hojj : orderOf jj = 3 := orderOf_eq_prime hjj3 hjj1
    have hcomm' : Commute σ jj := Subtype.ext (by simpa using hσk)
    have hcop : Nat.Coprime (orderOf σ) (orderOf jj) := by rw [hσ, hojj]; norm_num
    have := hcomm'.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [hσ, hojj] at this
    exact not_orderOf_fifteen hJ₀card (σ * jj) (by rw [this])
  ·
    have hk'13 : k' ^ 13 = 1 := by rw [hk'pow, h13]; group
    have h1 : orderOf k' ∣ 13 := orderOf_dvd_of_pow_eq_one hk'13
    have h2 : orderOf k' ∣ 300 := hJAcard ▸ Subgroup.orderOf_dvd_natCard (J₀ ⊔ A₀) hk'sup
    have h3 : orderOf k' ∣ Nat.gcd 13 300 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 13 300 = 1 := by norm_num
    rw [h4] at h3
    exact hk'1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))

theorem charP_two_of_card {E : Type} [Field E] [Finite E] {k : ℕ} (h : Nat.card E = 2 ^ k) :
    CharP E 2 := by
  have : Fintype E := Fintype.ofFinite E
  have hp : (ringChar E).Prime := CharP.char_is_prime E _
  have : CharP E (ringChar E) := ringChar.charP E
  obtain ⟨n, -, hn⟩ := FiniteField.card E (ringChar E)
  have hcard : Nat.card E = (ringChar E) ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have h2 : ringChar E ∣ 2 ^ k := by
    rw [← h, hcard]
    exact dvd_pow_self _ n.pos.ne'
  have hc : ringChar E = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
  have h3 := ringChar.charP E
  rwa [hc] at h3

theorem psu34_core {E : Type} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = (2 ^ 2) ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ 2)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hP : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 62400)
    (V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hV : Nat.card V = 25)
    (k : ProjectiveSpecialUnitaryMatrixGroup J) (hk1 : k ≠ 1) (hs : k ^ 3 = 1 ∨ k ^ 13 = 1)
    (hcomm : ∀ v ∈ V, v * k = k * v) : False := by
  classical
  have hA₀card : Nat.card (torusP J hJ) = 5 := by
    have := card_torusP J hJ 2 le_rfl hcard hfixed
    rw [this]; norm_num
  obtain ⟨eJ⟩ := nonempty_sublineP_equiv J hJ 2 le_rfl hcard hfixed
  have hBJ : BenderType (PSL2Model 2) 2 1 1 := .linear 2 le_rfl (MulEquiv.refl _)
  have hJ₀card : Nat.card (sublineP J hJ) = 60 := by
    rw [Nat.card_congr eJ.toEquiv, hBJ.card_eq]; norm_num
  have : IsSimpleGroup (PSL2Model 2) := hBJ.isSimple
  have hJ₀simple : IsSimpleGroup ↥(sublineP J hJ) := MulEquiv.isSimpleGroup eJ
  exact core_abstract hP (sublineP J hJ) (torusP J hJ) hJ₀card hA₀card
    (sublineP_commute_torusP J hJ) (sublineP_inf_torusP J hJ)
    (fun x₀ hx₀ hx₀1 w hw =>
      (mul_comm_iff_mem_sup_of_mem_torusP J hJ 2 le_rfl hcard hfixed hx₀ hx₀1 w).mp hw)
    V hV k hk1 hs hcomm

theorem noN2_of_benderU34 {Y : Type} [Group Y] [Finite Y]
    (hB : BenderType Y 2 3 5) {E : Type} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hcard : Nat.card E = (2 ^ 2) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ 2)
    (φ : Y ≃* ProjectiveSpecialUnitaryMatrixGroup J) : NoN2 Y := by
  classical
  have hc := hB.center_eq_bot
  have hinj := conj_injective_of_center_bot hc
  have hY : Nat.card Y = 62400 := by rw [hB.card_eq]; norm_num
  have hO : Nat.card (Outer Y) = 4 := by
    obtain ⟨Dd, hn, -, hd, -, hq⟩ := hB.outer_unitary
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Dd
    rw [hq, hd] at h1
    norm_num at h1
    exact h1
  have hA : Nat.card (MulAut Y) = 249600 := by rw [card_mulAut_eq_outer_mul hc, hY, hO]
  intro r V Z h
  have hsq := n2_sq_dvd h
  rw [hA] at hsq
  obtain ⟨s, y, hs, hsodd, hsr, hys, hy1, -, hVy⟩ := n2_exists_prime_elt h
  obtain ⟨hr, hr2, hVe, hVc, -⟩ := h
  have : Fact s.Prime := ⟨hs⟩
  have hfac : (249600 : ℕ) = 2 ^ 8 * 3 * 5 ^ 2 * 13 := by norm_num
  have hr5 : r = 5 := by
    have h1 : r ∣ 2 ^ 8 * 3 * 5 ^ 2 * 13 := by
      have : r ∣ r ^ 2 := dvd_pow_self r two_ne_zero
      exact hfac ▸ this.trans hsq
    rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
        · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4)
          subst this
          exact absurd hr2 (by decide)
        · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h4
          subst this
          omega
      · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp (hr.dvd_of_dvd_pow h3)
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h2
      subst this
      omega
  subst hr5
  have hs313 : s = 3 ∨ s = 13 := by
    have hord : orderOf y = s := orderOf_eq_prime hys hy1
    have hdvd : s ∣ 249600 := by
      rw [← hA, ← hord]
      exact orderOf_dvd_natCard y
    have h1 : s ∣ 2 ^ 8 * 3 * 5 ^ 2 * 13 := hfac ▸ hdvd
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hs).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hs).mp h3 with h4 | h4
        · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h4)
          subst this
          exact absurd hsodd (by decide)
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp h4)
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).mp (hs.dvd_of_dvd_pow h3)) hsr
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h2)
  have hVin : ∀ v ∈ V, ∃ g : Y, MulAut.conj g = v := by
    intro v hv
    have hv5 : v ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
    exact mem_inner_of_pow_eq_one hv5 (by rw [hO]; norm_num)
  have hyin : y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y :=
    mem_inner_of_pow_eq_one hys (by rw [hO]; rcases hs313 with rfl | rfl <;> norm_num)
  obtain ⟨k, rfl⟩ : ∃ k : Y, MulAut.conj k = y := hyin
  set V₀ : Subgroup Y := V.comap (MulAut.conj : Y →* MulAut Y) with hV₀
  have hV₀map : V₀.map (MulAut.conj : Y →* MulAut Y) = V := by
    rw [hV₀, Subgroup.map_comap_eq]
    have hVle : V ≤ (MulAut.conj : Y →* MulAut Y).range := fun v hv => by
      obtain ⟨g, hg⟩ := hVin v hv
      exact ⟨g, hg⟩
    exact inf_eq_right.mpr hVle
  have hV₀card : Nat.card V₀ = 25 := by
    have := Subgroup.card_map_of_injective (f := (MulAut.conj : Y →* MulAut Y)) (K := V₀) hinj
    rw [hV₀map, hVc] at this
    omega
  have hk1 : k ≠ 1 := by rintro rfl; exact hy1 (map_one _)
  have hks : k ^ 3 = 1 ∨ k ^ 13 = 1 := by
    rcases hs313 with rfl | rfl
    · left; apply hinj; rw [map_pow, hys, map_one]
    · right; apply hinj; rw [map_pow, hys, map_one]
  have hkcomm : ∀ v ∈ V₀, v * k = k * v := by
    intro v hv
    apply hinj
    rw [map_mul, map_mul]
    exact hVy _ hv
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Y φ.toEquiv
  have hP : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 62400 := by
    rw [← Nat.card_congr φ.toEquiv, hY]
  have hV₁card : Nat.card (V₀.map φ.toMonoidHom) = 25 := by
    rw [Subgroup.card_map_of_injective φ.injective, hV₀card]
  refine psu34_core J hJ hcard hfixed hP (V₀.map φ.toMonoidHom) hV₁card (φ k) (by
    intro h; exact hk1 (φ.injective (by rw [h, map_one]))) ?_ ?_
  · rcases hks with h3 | h13
    · left; rw [← map_pow, h3, map_one]
    · right; rw [← map_pow, h13, map_one]
  · rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg φ (hkcomm v hv)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.Uniqueness.Bender
  CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI

theorem noN2_U34 (Y : Type) [Group Y] (h : LieModel Y .PSU 3 2 2) :
    NoN2 Y := by
  classical
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (S := Y) (f := 2) le_rfl h
  have hmodel : PSU3Model 2 = CFSG.Open.PSU3 2 2 := by simp only [CFSG.Open.PSU3, PSU3Model]
  let e' : Y ≃* PSU3Model 2 := e.trans (MulEquiv.subgroupCongr hmodel.symm)
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e₂⟩⟩ := exists_psu3_concrete (n := 2) le_rfl
  have : Finite E := hF
  have : CharP E 2 := CF67S.charP_two_of_card (k := 4) (by rw [hcard]; norm_num)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_injective _ Subtype.coe_injective
  let φ : Y ≃* ProjectiveSpecialUnitaryMatrixGroup J := e'.trans e₂
  have : Finite Y := Finite.of_equiv _ φ.symm.toEquiv
  have hB : BenderType Y 2 3 5 := by
    have := BenderType.unitary 2 le_rfl e'
    norm_num at this
    exact this
  exact CF67S.noN2_of_benderU34 hB J hJ hcard hfixed φ

end CFSG.GH74.GLS.Stage2.Bender.Thm1
