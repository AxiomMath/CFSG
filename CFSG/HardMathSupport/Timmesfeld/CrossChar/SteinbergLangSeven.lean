module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangE78
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

set_option linter.unusedSectionVars false


section Balance

variable (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
  (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
  (hex : LangComponentsQuasisimple .exc)

include hsub hin hsu htw hex

theorem steinbergLang_langTorusPlaneBalance_E7_seven_split
    (w : WeylGroup Tag.E7) : LangTorusPlaneBalance Tag.E7 w 7 fun q => 7 ∣ q - 1 :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inl rfl) Nat.prime_seven
    (fun _ _ b hb => (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven b
      hb).le) e7Neg_smul (fun q hq2 hQ => ⟨by omega, by omega⟩) hsub hin hsu htw hex w

theorem steinbergLang_langTorusPlaneBalance_E8_seven_split
    (w : WeylGroup Tag.E8) : LangTorusPlaneBalance Tag.E8 w 7 fun q => 7 ∣ q - 1 :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inr rfl) Nat.prime_seven
    (fun _ _ b hb => (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven b
      hb).le) e8Neg_smul (fun q hq2 hQ => ⟨by omega, by omega⟩) hsub hin hsu htw hex w

end Balance

theorem steinbergLang_innerPlaneBalance_of_toralPlane {τ : Tag} {p : ℕ} (hp : p.Prime)
    (htor : LangToralPlane τ p) {Q : ℕ → Prop}
    (hT1 : ∀ w : WeylGroup τ, LangTorusPlaneBalance τ w p Q) (K : Type) [Field K] [Finite K]
    (hpK : ¬ p ∣ Nat.card K) (hQ : Q (Nat.card K)) : InnerPlaneBalance p (adjointGroup τ K) := by
  intro D hDin hD hcard H hH
  have hinj := mulAut_conj_injective_adjointGroup (τ := τ) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = p ^ 2 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ p = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ p = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := htor K hpK D₀ hpow₀ hD₀card
  refine localDeltaIn_eq_bot_of_conj_sub hH (E := D₀) hDD.le c ?_
  refine hT1 w K hQ Fr hFr g0 hg0C hg0 _ ?_ ?_ ?_ H hH
  · rintro _ ⟨x, hx, rfl⟩
    change (c * x * c⁻¹) ^ p = 1
    rw [conj_pow, hpow₀ x hx, mul_one, mul_inv_cancel]
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hD₀card]
    have := hp.two_le
    nlinarith
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx

section Frontier

variable (hsub : LangSubnormal)
  (hin : LangComponentsQuasisimple .inner)
  (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
  (hex : LangComponentsQuasisimple .exc)

include hsub hin hsu htw hex

theorem steinbergLang_innerPlaneBalanceAtP_E7_one_seven
    (htor : LangToralPlane Tag.E7 7) : InnerPlaneBalanceAtP .E7 1 fun p => p = 7 := by
  intro q hv p hp hp7 hR hpq he
  subst hR
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have h1 : 7 ∣ Nat.card K - 1 := by
    rw [hK]
    exact dvd_sub_one_of_orderOf_eq_one (hK ▸ Nat.card_pos) he
  have hpK : ¬ 7 ∣ Nat.card K := by
    have : 1 ≤ Nat.card K := Nat.card_pos
    omega
  exact InnerPlaneBalance.of_mulEquiv e (steinbergLang_innerPlaneBalance_of_toralPlane
    Nat.prime_seven htor (steinbergLang_langTorusPlaneBalance_E7_seven_split hsub hin hsu htw hex)
    K hpK h1)

theorem steinbergLang_innerPlaneBalanceAtP_E8_one_seven
    (htor : LangToralPlane Tag.E8 7) : InnerPlaneBalanceAtP .E8 1 fun p => p = 7 := by
  intro q hv p hp hp7 hR hpq he
  subst hR
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have h1 : 7 ∣ Nat.card K - 1 := by
    rw [hK]
    exact dvd_sub_one_of_orderOf_eq_one (hK ▸ Nat.card_pos) he
  have hpK : ¬ 7 ∣ Nat.card K := by
    have : 1 ≤ Nat.card K := Nat.card_pos
    omega
  exact InnerPlaneBalance.of_mulEquiv e (steinbergLang_innerPlaneBalance_of_toralPlane
    Nat.prime_seven htor (steinbergLang_langTorusPlaneBalance_E8_seven_split hsub hin hsu htw hex)
    K hpK h1)

theorem steinbergLang_hE7c1 :
    InnerPlaneBalanceAtP .E7 1 fun p => p = 7 :=
  steinbergLang_innerPlaneBalanceAtP_E7_one_seven hsub hin hsu htw hex
    (Torality.langToralPlane_of_bar Nat.prime_seven planesToralBar_E7_seven)

theorem steinbergLang_hE8c1 :
    InnerPlaneBalanceAtP .E8 1 fun p => p = 7 :=
  steinbergLang_innerPlaneBalanceAtP_E8_one_seven hsub hin hsu htw hex
    (Torality.langToralPlane_of_bar Nat.prime_seven planesToralBar_E8_seven)

end Frontier

end CFSG.HardMathSupport.Timmesfeld.CrossChar
