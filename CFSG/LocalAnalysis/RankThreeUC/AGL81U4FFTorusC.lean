module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFKStr
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSocle

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Quasithin Subgroup

private theorem comp_aeval_eq {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B] (f : Module.End (ZMod 2) A)
    (g : Module.End (ZMod 2) B) (ι : A →ₗ[ZMod 2] B) (hι : ∀ x, ι (f x) = g (ι x))
    (p : Polynomial (ZMod 2)) (x : A) :
    ι (Polynomial.aeval f p x) = Polynomial.aeval g p (ι x) := by
  induction p using Polynomial.induction_on generalizing x with
  | C a =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply, map_smul]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    have hsplit : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial (ZMod 2)) =
        Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    rw [hsplit, map_mul (Polynomial.aeval f), map_mul (Polynomial.aeval g), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih (f x), hι x]

theorem lemma52_module {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] [Nontrivial E]
    (φ : Module.End (ZMod 2) E) {m : Polynomial (ZMod 2)} (hm : Irreducible m)
    (hφ : Polynomial.aeval φ m = 0)
    (𝒢 : Subgroup (E ≃ₗ[ZMod 2] E)) (hcomm : ∀ g ∈ 𝒢, ∀ h ∈ 𝒢, g * h = h * g)
    (h2 : ∀ g ∈ 𝒢, g * g = 1) (hφ𝒢 : ∀ g ∈ 𝒢, ∀ x, g (φ x) = φ (g x))
    (hfix : Nat.card {x : E // ∀ g ∈ 𝒢, g x = x} ≤ 2 ^ m.natDegree) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card E = 2 ^ (m.natDegree * k) ∧
      Nat.card {x : E // ∀ g ∈ 𝒢, g x = x} = 2 ^ m.natDegree ∧
      Nat.card 𝒢 ≤ 2 ^ (m.natDegree * (k - 1)) := by
  haveI : Fact (Irreducible m) := ⟨hm⟩
  obtain ⟨hKfin, hKchar, hKcard⟩ := natCard_adjoinRoot hm
  obtain ⟨hmod, -, -, hlin⟩ := exists_adjoinRoot_module φ m hm hφ
  have hKlin : ∀ g ∈ 𝒢, ∀ (c : AdjoinRoot m) (x : E), g (c • x) = c • g x := fun g hg =>
    hlin (g : E →ₗ[ZMod 2] E) (LinearMap.ext fun x => hφ𝒢 g hg x)
  obtain ⟨ι, hι⟩ : ∃ ι : 𝒢 →* (E ≃ₗ[AdjoinRoot m] E), ∀ (g : 𝒢) (x : E), ι g x = g.1 x :=
    ⟨{ toFun := fun g =>
        { toFun := fun x => g.1 x
          map_add' := fun x y => g.1.map_add x y
          map_smul' := fun c x => hKlin g.1 g.2 c x
          invFun := fun x => g.1.symm x
          left_inv := fun x => g.1.symm_apply_apply x
          right_inv := fun x => g.1.apply_symm_apply x }
       map_one' := LinearEquiv.ext fun x => rfl
       map_mul' := fun g h => LinearEquiv.ext fun x => rfl }, fun g x => rfl⟩
  have hιinj : Function.Injective ι := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hx : ι g x = ι h x := congrArg (fun γ : E ≃ₗ[AdjoinRoot m] E => γ x) hgh
    rw [hι, hι] at hx
    exact hx
  have hcard𝒢 : Nat.card 𝒢 = Nat.card ι.range :=
    Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv
  haveI : Module.Finite (AdjoinRoot m) E := Module.finite_iff_finite.mpr inferInstance
  have hEcard : Nat.card E = Nat.card (AdjoinRoot m) ^ Module.finrank (AdjoinRoot m) E :=
    Module.natCard_eq_pow_finrank
  have hkpos : 0 < Module.finrank (AdjoinRoot m) E := Module.finrank_pos
  have hdeg : m.natDegree ≠ 0 := hm.natDegree_pos.ne'
  have h2E : 2 ∣ Nat.card E := by
    rw [hEcard, hKcard]
    exact dvd_pow (dvd_pow_self 2 hdeg) hkpos.ne'
  letI : MulAction 𝒢 E :=
    { smul := fun g x => (g : E ≃ₗ[ZMod 2] E) x
      one_smul := fun x => rfl
      mul_smul := fun g h x => rfl }
  have hP : IsPGroup 2 𝒢 := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    simpa [pow_two] using h2 (g : E ≃ₗ[ZMod 2] E) g.2
  have hfix0 : (0 : E) ∈ MulAction.fixedPoints 𝒢 E :=
    MulAction.mem_fixedPoints.mpr fun g => map_zero (g : E ≃ₗ[ZMod 2] E)
  obtain ⟨v, hvfixed, hv0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point E h2E hfix0
  have hv : v ≠ 0 := fun h => hv0 h.symm
  have hvfix : ∀ g ∈ 𝒢, g v = v := fun g hg => MulAction.mem_fixedPoints.mp hvfixed ⟨g, hg⟩
  obtain ⟨ev, hev⟩ : ∃ ev : AdjoinRoot m → {x : E // ∀ g ∈ 𝒢, g x = x},
      ∀ c, (ev c).1 = c • v :=
    ⟨fun c => ⟨c • v, fun g hg => by rw [hKlin g hg c v, hvfix g hg]⟩, fun c => rfl⟩
  have hevinj : Function.Injective ev := fun c c' h => by
    have h' := congrArg Subtype.val h
    rw [hev, hev] at h'
    exact smul_left_injective (AdjoinRoot m) hv h'
  have hcardeq : Nat.card {x : E // ∀ g ∈ 𝒢, g x = x} = Nat.card (AdjoinRoot m) :=
    le_antisymm (hfix.trans_eq hKcard.symm) (Nat.card_le_card_of_injective ev hevinj)
  have hbij : Function.Bijective ev :=
    (Nat.bijective_iff_injective_and_card ev).mpr ⟨hevinj, hcardeq.symm⟩
  have hline0 : ∀ x : E, (∀ g ∈ 𝒢, g x = x) → ∃ c : AdjoinRoot m, x = c • v := by
    intro x hx
    obtain ⟨c, hc⟩ := hbij.2 ⟨x, hx⟩
    have hc' := congrArg Subtype.val hc
    rw [hev] at hc'
    exact ⟨c, hc'.symm⟩
  have hcomm𝒟 : ∀ d ∈ ι.range, ∀ e ∈ ι.range, d * e = e * d := by
    intro d hd e he
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hd
    obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp he
    have hgg : g * g' = g' * g := Subtype.ext (hcomm g.1 g.2 g'.1 g'.2)
    rw [← map_mul, ← map_mul, hgg]
  have h2𝒟 : ∀ d ∈ ι.range, d * d = 1 := by
    intro d hd
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hd
    have hgg : g * g = 1 := Subtype.ext (h2 g.1 g.2)
    rw [← map_mul, hgg, map_one]
  have hvfix𝒟 : ∀ d ∈ ι.range, d v = v := by
    intro d hd
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hd
    rw [hι]
    exact hvfix g.1 g.2
  have hline𝒟 : ∀ x : E, (∀ d ∈ ι.range, d x = x) → ∃ c : AdjoinRoot m, x = c • v := by
    intro x hx
    refine hline0 x fun g hg => ?_
    have hx' := hx (ι ⟨g, hg⟩) (MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩)
    rwa [hι] at hx'
  have hbound := card_le_pow_of_fixed_line ι.range hcomm𝒟 h2𝒟 hv hvfix𝒟 hline𝒟
  refine ⟨Module.finrank (AdjoinRoot m) E, hkpos, ?_, hcardeq.trans hKcard, ?_⟩
  · rw [hEcard, hKcard, pow_mul]
  · rw [hcard𝒢]
    calc Nat.card ι.range ≤ Nat.card (AdjoinRoot m) ^ (Module.finrank (AdjoinRoot m) E - 1) :=
          hbound
      _ = 2 ^ (m.natDegree * (Module.finrank (AdjoinRoot m) E - 1)) := by
          rw [hKcard, pow_mul]

variable {V : Type} [CommGroup V] [Finite V]

theorem lemma52_transfer [IsF2Space V] {D : Subgroup (MulAut V)}
    (hDcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) (hD2 : ∀ d ∈ D, d * d = 1)
    {R : Subgroup V} (hRD : D ≤ stabSub R) {θ : MulAut V} (hθR : θ ∈ stabSub R)
    (hDθ : ∀ d ∈ D, d * θ = θ * d) {m : Polynomial (ZMod 2)} (hm : Irreducible m)
    (hkill : ∀ x ∈ R, polyAct θ m x = 1)
    (hfix : Nat.card ↥(R ⊓ fixV D) ≤ 2 ^ m.natDegree) (hR : R ≠ ⊥) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card R = 2 ^ (m.natDegree * k) ∧
      Nat.card ↥(R ⊓ fixV D) = 2 ^ m.natDegree ∧
      Nat.card (autSub D R) ≤ 2 ^ (m.natDegree * (k - 1)) := by
  haveI hRF2 : IsF2Space R :=
    ⟨fun v => Subtype.ext (by simpa using IsF2Space.sq_eq_one (v : V))⟩
  haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : MulAut R →* (Additive R ≃ₗ[ZMod 2] Additive R),
      ∀ (α : MulAut R) (x : Additive R), Ψ α x = Additive.ofMul (α (Additive.toMul x)) :=
    ⟨{ toFun := fun α =>
        { toLinearMap := AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive α).toAddMonoidHom
          invFun := fun x => (MulEquiv.toAdditive α).symm x
          left_inv := fun x => (MulEquiv.toAdditive α).symm_apply_apply x
          right_inv := fun x => (MulEquiv.toAdditive α).apply_symm_apply x }
       map_one' := LinearEquiv.ext fun x => rfl
       map_mul' := fun α β => LinearEquiv.ext fun x => rfl }, fun α x => rfl⟩
  have hΨinj : Function.Injective Ψ := by
    intro α β h
    ext u
    have h1 : Additive.toMul (Ψ α (Additive.ofMul u)) =
        Additive.toMul (Ψ β (Additive.ofMul u)) := by
      rw [h]
    rw [hΨ, hΨ] at h1
    exact congrArg Subtype.val h1
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.End (ZMod 2) (Additive R),
      ∀ x, φ x = Ψ (resHom R ⟨θ, hθR⟩) x :=
    ⟨(Ψ (resHom R ⟨θ, hθR⟩)).toLinearMap, fun x => rfl⟩
  obtain ⟨𝒢, h𝒢⟩ : ∃ 𝒢 : Subgroup (Additive R ≃ₗ[ZMod 2] Additive R),
      𝒢 = (autSub D R).map Ψ := ⟨_, rfl⟩
  have hmem𝒢 : ∀ g, g ∈ 𝒢 ↔ ∃ α ∈ autSub D R, Ψ α = g := fun g => by
    rw [h𝒢]
    exact Subgroup.mem_map
  have hAcomm : ∀ α ∈ autSub D R, ∀ β ∈ autSub D R, α * β = β * α := by
    intro α hα β hβ
    obtain ⟨g, hg, rfl⟩ := CFSG.Quasithin.mem_autSub.mp hα
    obtain ⟨g', hg', rfl⟩ := CFSG.Quasithin.mem_autSub.mp hβ
    rw [← map_mul, ← map_mul]
    exact congrArg (resHom R) (Subtype.ext (hDcomm _ hg _ hg'))
  have hAinv : ∀ α ∈ autSub D R, α * α = 1 := by
    intro α hα
    obtain ⟨g, hg, rfl⟩ := CFSG.Quasithin.mem_autSub.mp hα
    rw [← map_mul, show g * g = 1 from Subtype.ext (hD2 _ hg), map_one]
  have hAθ : ∀ α ∈ autSub D R, α * resHom R ⟨θ, hθR⟩ = resHom R ⟨θ, hθR⟩ * α := by
    intro α hα
    obtain ⟨g, hg, rfl⟩ := CFSG.Quasithin.mem_autSub.mp hα
    rw [← map_mul, ← map_mul]
    exact congrArg (resHom R) (Subtype.ext (hDθ _ hg))
  have hGcomm : ∀ g ∈ 𝒢, ∀ h ∈ 𝒢, g * h = h * g := by
    intro g hg h hh
    obtain ⟨α, hα, rfl⟩ := (hmem𝒢 g).mp hg
    obtain ⟨β, hβ, rfl⟩ := (hmem𝒢 h).mp hh
    rw [← map_mul, ← map_mul, hAcomm α hα β hβ]
  have hGinv : ∀ g ∈ 𝒢, g * g = 1 := by
    intro g hg
    obtain ⟨α, hα, rfl⟩ := (hmem𝒢 g).mp hg
    rw [← map_mul, hAinv α hα, map_one]
  have hGφ : ∀ g ∈ 𝒢, ∀ x, g (φ x) = φ (g x) := by
    intro g hg x
    obtain ⟨α, hα, rfl⟩ := (hmem𝒢 g).mp hg
    have hc : Ψ α * Ψ (resHom R ⟨θ, hθR⟩) = Ψ (resHom R ⟨θ, hθR⟩) * Ψ α := by
      rw [← map_mul, ← map_mul, hAθ α hα]
    rw [hφ, hφ]
    exact congrArg (fun γ : Additive R ≃ₗ[ZMod 2] Additive R => γ x) hc
  obtain ⟨ι, hι⟩ : ∃ ι : Additive R →ₗ[ZMod 2] Additive V,
      ∀ x, ι x = Additive.ofMul ((Additive.toMul x : R) : V) :=
    ⟨AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive R.subtype), fun x => rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b hab
    rw [hι, hι] at hab
    exact Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul hab))
  have hιφ : ∀ x, ι (φ x) = linOf θ (ι x) := fun x => by
    rw [hφ, hι, hι, linOf_apply, hΨ]
    rfl
  have hφm : Polynomial.aeval φ m = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    apply hιinj
    rw [comp_aeval_eq φ (linOf θ) ι hιφ m x, map_zero, hι]
    have h1 : Additive.toMul (Polynomial.aeval (linOf θ) m
        (Additive.ofMul ((Additive.toMul x : R) : V))) = 1 :=
      hkill _ (Additive.toMul x).2
    exact congrArg Additive.ofMul h1
  have hfixd : ∀ x : Additive R, (∀ g ∈ 𝒢, g x = x) ↔
      ∀ d ∈ D, d ((Additive.toMul x : R) : V) = ((Additive.toMul x : R) : V) := by
    intro x
    constructor
    · intro h d hd
      have hdR : resHom R ⟨d, hRD hd⟩ ∈ autSub D R :=
        CFSG.Quasithin.mem_autSub.mpr ⟨⟨d, hRD hd⟩, hd, rfl⟩
      have h1 := h (Ψ (resHom R ⟨d, hRD hd⟩)) ((hmem𝒢 _).mpr ⟨_, hdR, rfl⟩)
      rw [hΨ] at h1
      exact congrArg Subtype.val (congrArg Additive.toMul h1)
    · intro h g hg
      obtain ⟨α, hα, rfl⟩ := (hmem𝒢 g).mp hg
      obtain ⟨dR, hdD, rfl⟩ := CFSG.Quasithin.mem_autSub.mp hα
      have h3 : resHom R dR (Additive.toMul x) = Additive.toMul x :=
        Subtype.ext (h dR.1 hdD)
      rw [hΨ, h3]
      rfl
  have hFix : Nat.card {x : Additive R // ∀ g ∈ 𝒢, g x = x} = Nat.card ↥(R ⊓ fixV D) := by
    have hmemL : ∀ x : {x : Additive R // ∀ g ∈ 𝒢, g x = x},
        ((Additive.toMul x.1 : R) : V) ∈ R ⊓ fixV D := fun x =>
      Subgroup.mem_inf.mpr ⟨(Additive.toMul x.1).2,
        CFSG.Quasithin.mem_fixV.mpr ((hfixd x.1).mp x.2)⟩
    have hmemR : ∀ y : ↥(R ⊓ fixV D), ∀ g ∈ 𝒢,
        g (Additive.ofMul ⟨(y : V), (Subgroup.mem_inf.mp y.2).1⟩) =
          Additive.ofMul ⟨(y : V), (Subgroup.mem_inf.mp y.2).1⟩ := fun y =>
      (hfixd _).mpr fun d hd => CFSG.Quasithin.mem_fixV.mp (Subgroup.mem_inf.mp y.2).2 d hd
    let e : {x : Additive R // ∀ g ∈ 𝒢, g x = x} ≃ ↥(R ⊓ fixV D) :=
      { toFun := fun x => ⟨((Additive.toMul x.1 : R) : V), hmemL x⟩
        invFun := fun y => ⟨Additive.ofMul ⟨(y : V), (Subgroup.mem_inf.mp y.2).1⟩, hmemR y⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    exact Nat.card_congr e
  have hcardG : Nat.card (autSub D R) = Nat.card 𝒢 := by
    rw [h𝒢]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (autSub D R) Ψ hΨinj).toEquiv
  obtain ⟨k, hk, hE, hF, hG⟩ :=
    lemma52_module φ hm hφm 𝒢 hGcomm hGinv hGφ (hFix.le.trans hfix)
  refine ⟨k, hk, ?_, hFix.symm.trans hF, ?_⟩
  · exact (Nat.card_congr Additive.ofMul).trans hE
  · rw [hcardG]
    exact hG

end CFSG.LocalAnalysis.RankThreeUC
