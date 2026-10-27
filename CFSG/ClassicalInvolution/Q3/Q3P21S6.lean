module

public import CFSG.ClassicalInvolution.Q3.Q3P21S5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution.RouteD.SU4Pattern

section Pair

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.WeakCT.SU4 CFSG.Timmesfeld CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
open scoped Matrix MatrixGroups

variable {p f : ℕ} [Fact p.Prime]


theorem twistedPair_of_equiv3 (hp2' : (2 : GaloisField p f) ≠ 0)
    (hRZ : ∀ {L : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
      {i : Su (GaloisField p (2 * f)) p f 4},
      IsLongRootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) L i →
        ∀ z ∈ L, z ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) → z = 1)
    {b c : GaloisField p f}
    [Fact (∀ r : GaloisField p f, r ^ 2 ≠ -c + b * r)]
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hg6 : SpinMinus6Generated hirr)
    (e : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      Su (GaloisField p (2 * f)) p f 4)
    {R : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (hlb : (spinMinusModel hirr).lb.range.map e.toMonoidHom = R) {X : Type} [Group X]
    (ψ : Su (GaloisField p (2 * f)) p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4)) :
    TwistedB2BlockPair hirr (ψ.comp e.toMonoidHom).range (R.map ψ)
        (((spinMinusModel hirr).sb.range.map e.toMonoidHom).map ψ) ∧
      R ⊔ (spinMinusModel hirr).sb.range.map e.toMonoidHom = ⊤ := by
  have h2 : (2 : GaloisField p f) ≠ 0 := hp2'
  obtain ⟨i, hi⟩ := hR
  refine ⟨⟨ψ.comp e.toMonoidHom, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hy1 : e y ∈ ψ.ker := hy
    have hc := hker hy1
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro w
    apply e.injective
    rw [map_mul, map_mul]
    exact hc (e w)
  · intro a b hab
    apply injective_minusLongBlock hirr h2
    apply e.injective
    have hab' : ψ (e ((spinMinusModel hirr).lb a)) = ψ (e ((spinMinusModel hirr).lb b)) := hab
    have ha : e ((spinMinusModel hirr).lb a) ∈ R := by
      rw [← hlb]
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
    have hb : e ((spinMinusModel hirr).lb b) ∈ R := by
      rw [← hlb]
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
    have hw : (e ((spinMinusModel hirr).lb a))⁻¹ * e ((spinMinusModel hirr).lb b) ∈ R :=
      R.mul_mem (R.inv_mem ha) hb
    have hwk : (e ((spinMinusModel hirr).lb a))⁻¹ * e ((spinMinusModel hirr).lb b) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    exact inv_mul_eq_one.mp (hRZ hi _ hw (hker hwk))
  · rw [← Subgroup.map_map, hlb]
  · exact (Subgroup.map_map _ _ _).symm
  · rw [← hlb, ← Subgroup.map_sup, hg6, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective


theorem exists_fixed_shortPair_linear3 (hp2 : p ≠ 2) (hf : f ≠ 0) (hqq : p ^ f = 3)
    (hq3 : p ^ f % 4 = 3) (hperf : Group.IsPerfect (Su (GaloisField p (2 * f)) p f 4))
    (hZ3 : ∀ z ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4), ¬ 3 ∣ orderOf z)
    (hRZ : ∀ {L : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
      {i : Su (GaloisField p (2 * f)) p f 4},
      IsLongRootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) L i →
        ∀ z ∈ L, z ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) → z = 1)
    {b c : GaloisField p f} [Fact (∀ r : GaloisField p f, r ^ 2 ≠ -c + b * r)]
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hg6 : SpinMinus6Generated hirr)
    {X : Type} [Group X] (ψ : Su (GaloisField p (2 * f)) p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4))
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    {R : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (θ : SL(2, GaloisField p f) →* X) (hθ : θ.range = R.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (hlin : LinearLift ψ τ) :
    ∃ (S : Subgroup (Su (GaloisField p (2 * f)) p f 4)) (W : Subgroup X),
      TwistedB2BlockPair hirr W (R.map ψ) (S.map ψ) ∧ R ⊔ S = ⊤ ∧
        ∀ y ∈ S, τ (ψ y) = ψ y := by
  classical
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    card_galoisField_two_mul p f (Nat.one_le_iff_ne_zero.mpr hf)
  obtain ⟨g₁, hg₁⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
    (by norm_num : 2 ≤ 4)).mp hR
  set ψ₁ : Su (GaloisField p (2 * f)) p f 4 →* X := ψ.comp (MulAut.conj g₁).toMonoidHom with hψ₁
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    intro y hy
    have h1 : (MulAut.conj g₁).toMonoidHom y ∈ ψ.ker := hy
    have h2 := hker h1
    exact (MulEquivClass.apply_mem_center_iff (MulAut.conj g₁)).1 h2
  have hθ₁ : θ.range = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ := by
    rw [hθ, hg₁, Subgroup.map_map]
  have hlin₁ : LinearLift ψ₁ τ := hlin.comp_conj g₁
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hcardk : Nat.card (fixedSubfield (GaloisField p (2 * f)) p f) = p ^ f :=
    card_fixedSubfield hK
  obtain ⟨ε⟩ : Nonempty (GaloisField p f ≃+* fixedSubfield (GaloisField p (2 * f)) p f) := by
    have := Fintype.ofFinite (GaloisField p f)
    have := Fintype.ofFinite (fixedSubfield (GaloisField p (2 * f)) p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF, hcardk])⟩
  have hcore := core_fixed_short_linear3 hK hp2 (by omega) hqq hq3 ε ψ₁ hψ₁ker
    (fun x hx => hZ3 x (hψ₁ker hx))
    (fun z hz hzk => hRZ (isLongRootSU2_standard (by norm_num : 2 ≤ 4)) z hz (hψ₁ker hzk))
    hperf τ hτ θ hθ₁ hθτ hlin₁
  obtain ⟨Q, hQ, hsupp, hfix⟩ := hcore
  obtain ⟨Φ, hΦlevi, hΦlb⟩ := exists_phiSU_bridge hp2 hf hirr
  set e' : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      Su (GaloisField p (2 * f)) p f 4 := Φ.trans (conjEquiv Q hQ) with he'
  have hlb : (spinMinusModel hirr).lb.range.map e'.toMonoidHom =
      rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) := hΦlb Q hQ hsupp
  have hR₀ : rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) ∈
      longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4) :=
    ⟨_, isLongRootSU2_standard (by norm_num : 2 ≤ 4)⟩
  obtain ⟨hpair, hsup⟩ := twistedPair_of_equiv3 (ModelFacts.two_ne_zero_galoisField f hp2) hRZ hg6
    e' hR₀ hlb ψ₁ hψ₁ker
  set S₀ : Subgroup (Su (GaloisField p (2 * f)) p f 4) :=
    (spinMinusModel hirr).sb.range.map e'.toMonoidHom with hS₀
  refine ⟨S₀.map (MulAut.conj g₁).toMonoidHom, (ψ₁.comp e'.toMonoidHom).range, ?_, ?_, ?_⟩
  · have h1 : R.map ψ = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ := by
      rw [hg₁, Subgroup.map_map]
    have h2 : (S₀.map (MulAut.conj g₁).toMonoidHom).map ψ = S₀.map ψ₁ := by
      rw [Subgroup.map_map]
    rw [h1, h2]
    exact hpair
  · rw [hg₁, ← Subgroup.map_sup, hsup, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g₁).surjective
  · rintro _ ⟨y₀, hy₀, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hy₀
    have hψy : ψ ((MulAut.conj g₁).toMonoidHom (e'.toMonoidHom x₀)) =
        ψ₁ (e'.toMonoidHom x₀) := rfl
    rw [hψy]
    refine hfix (e'.toMonoidHom x₀)
      (((Φ x₀ : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4) :
        GL (Fin 4) (GaloisField p (2 * f))) : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f)))
      (hΦlevi x₀ hx₀) ?_
    show (((conjEquiv Q hQ (Φ x₀) : Su (GaloisField p (2 * f)) p f 4) :
      GL (Fin 4) (GaloisField p (2 * f))) : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) = _
    rw [coe_conjEquiv, Units.val_mul, Units.val_mul]

end Pair

section Three

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
open scoped Matrix MatrixGroups


theorem isPerfect_su4_three : Group.IsPerfect (Su (GaloisField 3 (2 * 1)) 3 1 4) :=
  ⟨(open_isQuasisimple_su_of_three_le Q3W.card_gf9 (by norm_num : 3 ≤ 4) (by decide)).1⟩

theorem cop_center_su4_three :
    ∀ z ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4), ¬ 3 ∣ orderOf z := by
  intro z hz h3
  have h8 := orderOf_dvd_of_pow_eq_one (Q3W.centerExp_su3 (by norm_num : 3 ≤ 4) hz)
  exact absurd (h3.trans h8) (by norm_num)

theorem long_inf_center_su4_three {L : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)}
    {i : Su (GaloisField 3 (2 * 1)) 3 1 4}
    (h : IsLongRootSU2 (GaloisField 3 (2 * 1)) 3 1 (by norm_num : 2 ≤ 4) L i) :
    ∀ z ∈ L, z ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) → z = 1 :=
  fun z hz hzc => Q3W.eq_one_of_mem_ker_of_isLongRootSU2_3 (by norm_num : 3 ≤ 4) h
    (θ := QuotientGroup.mk' (Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4)))
    (QuotientGroup.ker_mk' _).le z hz ((QuotientGroup.eq_one_iff z).mpr hzc)

theorem exists_fixed_shortPair_linear_three {b c : GaloisField 3 1}
    [Fact (∀ r : GaloisField 3 1, r ^ 2 ≠ -c + b * r)]
    {hirr : ∀ s : GaloisField 3 1, s ^ 2 + b * s + c ≠ 0} (hg6 : SpinMinus6Generated hirr)
    {X : Type} [Group X] (ψ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))
    (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    {R : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)}
    (hR : R ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) (by norm_num : 2 ≤ 4))
    (θ : SL(2, GaloisField 3 1) →* X) (hθ : θ.range = R.map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (hlin : LinearLift ψ τ) :
    ∃ (S : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)) (W : Subgroup X),
      TwistedB2BlockPair hirr W (R.map ψ) (S.map ψ) ∧ R ⊔ S = ⊤ ∧
        ∀ y ∈ S, τ (ψ y) = ψ y :=
  exists_fixed_shortPair_linear3 (p := 3) (f := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) isPerfect_su4_three cop_center_su4_three long_inf_center_su4_three hg6 ψ hker τ hτ
    hR θ hθ hθτ hlin

end Three

end CFSG.ClassicalInvolution.Q3.Q3P21
