module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TailAbs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.RankThree.PartOne.SRC.LiftP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_normal_order_three_of_tail_in_group {Y : Type*} [Group Y] [Finite Y]
    (hcon : HasPrimeConstraint (G := Y) 3)
    {C W D : Subgroup Y} (hCn : C.Normal)
    (hCsmall : ∀ E : Subgroup Y, E ≤ C → IsPGroup 3 E → Nat.card E ≤ 9)
    (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ W.index)
    (hDW : D ≤ W) (hDC : D ≤ C) (hD9 : Nat.card D = 9)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD3 : ∀ d ∈ D, d ^ 3 = 1)
    (hR : ∀ a ∈ W ⊓ Subgroup.centralizer (D : Set Y), ∀ b ∈ W ⊓ Subgroup.centralizer (D : Set Y),
      a * b = b * a)
    (hA : ∃ A : Subgroup Y, A ≤ W ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
      Nat.card A = 27)
    (hmax : ∀ A : Subgroup Y, A ≤ W → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ 3 = 1) → Nat.card A ≤ 27)
    {s : Y} (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D) (hs2 : ∀ d ∈ D, s ^ 2 * d * (s ^ 2)⁻¹ = d⁻¹) :
    ∃ P₀ : Subgroup Y, P₀ ≤ W ∧ Nat.card P₀ = 3 ∧
      (P₀ ⊔ primeComplementCore (G := Y) 3).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup Y := primeComplementCore (G := Y) 3 with hO
  have hOn : O.Normal := primeComplementCore_normal 3
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : Y →* Y ⧸ O := QuotientGroup.mk' O with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  have hO1 : ∀ {E : Subgroup Y}, IsPGroup 3 E → ∀ x ∈ E, π x = 1 → x = 1 := by
    intro E hE x hxE hx
    have hxO : x ∈ O := by rw [← hker]; exact hx
    obtain ⟨k, hk⟩ := hE ⟨x, hxE⟩
    have h1 : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : x ^ Nat.card O = 1 := by
      have h : (⟨x, hxO⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
      have := congrArg Subtype.val h
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hd1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h1
    have hd2 : orderOf x ∣ Nat.card O := orderOf_dvd_of_pow_eq_one h2
    have hc : Nat.Coprime (orderOf x) (Nat.card O) :=
      (Nat.Coprime.pow_left k hOcop).coprime_dvd_left hd1
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc hd2)
  have hinj : ∀ {E : Subgroup Y}, IsPGroup 3 E → Set.InjOn π (E : Set Y) := by
    intro E hE a ha b hb hab
    have h1 : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.1 (hO1 hE _ (E.mul_mem (E.inv_mem ha) hb) h1)
  have hcard : ∀ {E : Subgroup Y}, IsPGroup 3 E → Nat.card (E.map π) = Nat.card E := by
    intro E hE
    have h1 := Nat.card_image_of_injOn (hinj hE)
    have e1 : Nat.card (E.map π) = Nat.card (π '' (E : Set Y)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    rw [e1, h1]
    rfl

  have hOeq : O = CFSG.pPrimeCore 3 Y := rfl
  have hX1 : ∀ K : Subgroup (Y ⧸ O), K.Normal → Nat.Coprime 3 (Nat.card K) → K = ⊥ := by
    have h := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := Y) 3
    exact (CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := Y ⧸ O)).1 h
  obtain ⟨Q, hQn, hQp, hQc⟩ := hcon
  have hWbp : IsPGroup 3 (W.map π) := hWp.map π
  have hWbidx : ¬ 3 ∣ (W.map π).index := fun h =>
    hWidx (h.trans (Subgroup.index_map_dvd W hπsurj))
  have hCbn : (C.map π).Normal := hCn.map π hπsurj
  have hDp : IsPGroup 3 D := hWp.to_le hDW
  have hCO : ∀ {E : Subgroup Y}, IsPGroup 3 E → E.map π ≤ C.map π → E ≤ C := by
    intro E hE hEC e he
    obtain ⟨c, hcC, hce⟩ := hEC (Subgroup.mem_map_of_mem π he)
    obtain ⟨k, hk⟩ := hE ⟨e, he⟩
    have h1 : e ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    set φ : Y →* Y ⧸ C := QuotientGroup.mk' C with hφ
    have ho : e * c⁻¹ ∈ O := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← hce, mul_inv_cancel]
    have h2 : (e * c⁻¹) ^ Nat.card O = 1 := by
      have h : (⟨e * c⁻¹, ho⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
      have := congrArg Subtype.val h
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hφc : φ c = 1 := (QuotientGroup.eq_one_iff c).2 hcC
    have h3 : φ e = φ (e * c⁻¹) := by
      rw [map_mul, map_inv, hφc, inv_one, mul_one]
    have hd1 : orderOf (φ e) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h1, map_one])
    have hd2 : orderOf (φ e) ∣ Nat.card O := by
      rw [h3]
      exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h2, map_one])
    have hc : Nat.Coprime (orderOf (φ e)) (Nat.card O) :=
      (Nat.Coprime.pow_left k hOcop).coprime_dvd_left hd1
    have h4 : φ e = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc hd2)
    exact (QuotientGroup.eq_one_iff e).1 h4
  have hNsmall : ∀ S : Subgroup (Y ⧸ O), S ≤ C.map π → IsPGroup 3 S → Nat.card S ≤ 9 := by
    intro S hSC hSp
    obtain ⟨E, hEO, hEmap⟩ := CFSG.RankThree.PartOne.SRC.exists_lift_pGroup O hOcop.symm S hSp
    have hEp : IsPGroup 3 E := by
      intro e
      obtain ⟨k, hk⟩ := hSp ⟨π e.1, by rw [← hEmap]; exact Subgroup.mem_map_of_mem π e.2⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (π e.1) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 : e.1 ^ 3 ^ k ∈ E ⊓ O := ⟨E.pow_mem e.2 _, by
        show e.1 ^ 3 ^ k ∈ O
        rw [← hker, MonoidHom.mem_ker, map_pow, h1]⟩
      rw [hEO, Subgroup.mem_bot] at h2
      simpa using h2
    have hEC : E ≤ C := hCO hEp (by rw [hEmap]; exact hSC)
    have := hCsmall E hEC hEp
    rw [← hEmap, hcard hEp]
    exact this
  have hDp : IsPGroup 3 D := hWp.to_le hDW
  have hDb9 : Nat.card (D.map π) = 9 := by rw [hcard hDp, hD9]
  have hDbab : ∀ a ∈ D.map π, ∀ b ∈ D.map π, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hDab a ha b hb]
  have hDb3 : ∀ d ∈ D.map π, d ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hD3 a ha, map_one]
  have hlift : ∀ a ∈ W.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup (Y ⧸ O)) :
      Set (Y ⧸ O)), ∃ w ∈ W ⊓ Subgroup.centralizer (D : Set Y), π w = a := by
    rintro a ⟨⟨w, hwW, rfl⟩, hac⟩
    refine ⟨w, ⟨hwW, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hac (π d) (Subgroup.mem_map_of_mem π hd)
    have h2 : π (d * w * (w * d)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, h1, mul_inv_cancel]
    have h3 := hO1 hWp (d * w * (w * d)⁻¹)
      (W.mul_mem (W.mul_mem (hDW hd) hwW) (W.inv_mem (W.mul_mem hwW (hDW hd)))) h2
    exact mul_inv_eq_one.1 h3
  have hRX : ∀ a ∈ W.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup (Y ⧸ O)) :
      Set (Y ⧸ O)), ∀ b ∈ W.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup (Y ⧸ O)) :
      Set (Y ⧸ O)), a * b = b * a := by
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := hlift a ha
    obtain ⟨v, hv, rfl⟩ := hlift b hb
    rw [← map_mul, ← map_mul, hR u hu v hv]
  have hAX : ∃ A : Subgroup (Y ⧸ O), A ≤ W.map π ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ a ∈ A, a ^ 3 = 1) ∧ Nat.card A = 27 := by
    obtain ⟨A, hAW, hAab, hA3, hA27⟩ := hA
    have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩
    refine ⟨A.map π, Subgroup.map_mono hAW, ?_, ?_, by rw [hcard hAp, hA27]⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hAab a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA3 a ha, map_one]
  have hmaxX : ∀ A : Subgroup (Y ⧸ O), A ≤ W.map π → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ 3 = 1) → Nat.card A ≤ 27 := by
    intro Abar hAbarW hAbarab hAbar3
    set A : Subgroup Y := Abar.comap π ⊓ W with hAdef
    have hAW : A ≤ W := inf_le_right
    have hAmap : A.map π = Abar := by
      ext z
      constructor
      · rintro ⟨a, ⟨ha1, _⟩, rfl⟩
        exact ha1
      · intro hz
        obtain ⟨w, hwW, hwz⟩ := hAbarW hz
        have hw : w ∈ Abar.comap π := by rw [Subgroup.mem_comap, hwz]; exact hz
        exact ⟨w, ⟨hw, hwW⟩, hwz⟩
    have hAp : IsPGroup 3 A := hWp.to_le hAW
    have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      have h1 := hAbarab (π a) ha.1 (π b) hb.1
      have h2 : π (a * b * (b * a)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, h1, mul_inv_cancel]
      exact mul_inv_eq_one.1 (hO1 hAp _
        (A.mul_mem (A.mul_mem ha hb) (A.inv_mem (A.mul_mem hb ha))) h2)
    have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha =>
      hO1 hAp _ (A.pow_mem ha 3) (by rw [map_pow]; exact hAbar3 _ ha.1)
    have := hmax A hAW hAab hA3
    rw [← hAmap, hcard hAp]
    exact this
  have hsDX : ∀ d ∈ D.map π, π s * d * (π s)⁻¹ ∈ D.map π := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨s * d * s⁻¹, hsD d hd, by simp⟩
  have hs2X : ∀ d ∈ D.map π, (π s) ^ 2 * d * ((π s) ^ 2)⁻¹ = d⁻¹ := by
    rintro _ ⟨d, hd, rfl⟩
    have := congrArg π (hs2 d hd)
    simpa [map_mul, map_pow, map_inv] using this
  obtain ⟨Pbar, hPbarn, hPbarW, hPbar3⟩ := exists_normal_of_tail_data hX1 hQn hQp hQc hWbp hWbidx
    hCbn hNsmall (Subgroup.map_mono hDC) (Subgroup.map_mono hDW) hDb9 hDbab hDb3 hRX hAX hmaxX hsDX
    hs2X
  set P₀ : Subgroup Y := Pbar.comap π ⊓ W with hP₀
  have hP₀W : P₀ ≤ W := inf_le_right
  have hP₀map : P₀.map π = Pbar := by
    ext z
    constructor
    · rintro ⟨a, ⟨ha1, _⟩, rfl⟩
      exact ha1
    · intro hz
      obtain ⟨w, hwW, hwz⟩ := hPbarW hz
      have hw : w ∈ Pbar.comap π := by rw [Subgroup.mem_comap, hwz]; exact hz
      exact ⟨w, ⟨hw, hwW⟩, hwz⟩
  have hP₀p : IsPGroup 3 P₀ := hWp.to_le hP₀W
  have hP₀card : Nat.card P₀ = 3 := by rw [← hcard hP₀p, hP₀map, hPbar3]
  have hsup : P₀ ⊔ O = Pbar.comap π := by
    apply le_antisymm
    · refine sup_le (fun x hx => hx.1) (fun x hx => ?_)
      have hπx : π x = 1 := (QuotientGroup.eq_one_iff x).2 hx
      show π x ∈ Pbar
      rw [hπx]
      exact Pbar.one_mem
    · intro x hx
      have hx' : π x ∈ P₀.map π := by rw [hP₀map]; exact hx
      obtain ⟨p, hp, hpx⟩ := hx'
      have hO' : p⁻¹ * x ∈ O := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
      have hxe : x = p * (p⁻¹ * x) := by group
      rw [hxe]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hO')
  refine ⟨P₀, hP₀W, hP₀card, ?_⟩
  rw [hsup]
  exact hPbarn.comap π

end CFSG.LocalAnalysis.RankThreeTheoremC
