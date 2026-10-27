module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtBasic
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6ActionParameters

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem tauHom_sp6ν₂ {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (z : G) {d : G}
    {B : ↥(binarySymMatrices 3)} (hB : z⁻¹ * (d⁻¹ * z * d) = tauHom φ he (Multiplicative.ofAdd B)) :
    sp6ν₂ φ he z d = B := by
  have h1 : z⁻¹ * (d⁻¹ * z * d) =
      tauHom φ he (Multiplicative.ofAdd (sp6ν₂ φ he z d)) :=
    Classical.epsilon_spec (p := fun B : ↥(binarySymMatrices 3) =>
      z⁻¹ * (d⁻¹ * z * d) = tauHom φ he (Multiplicative.ofAdd B)) ⟨B, hB⟩
  exact Multiplicative.ofAdd.injective (tauHom_injective φ he (h1.symm.trans hB))

theorem lagBase_of_setting {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₁ := pullSub φ (pointRadical b hb u f)
    let D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((A₁ ⊔ zpowers z : Subgroup G) : Set G))
    (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
    Monoid.exponent (sp6C₂ φ he z) = 4 →
    ∃ (hzC : z ∈ centralizer (L : Set G))
      (σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
        GL (Fin 3) (ZMod 2)),
      L ⊔ zpowers z = centralizer ({z} : Set G) ∧ L ⊓ zpowers z = ⊥ ∧
      LagBase he φ hzC hz (sp6D₂ φ e z) (sp6C₂ φ he z) (sp6E₂ φ he z) (sp6ν₂ φ he z) σ ∧
      ((sp6E₂ φ he z : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative (sp6E₂ φ he z) ∧
        Nat.card (sp6E₂ φ he z) = 512 ∧
        ∀ E' : Subgroup G, (E' : Set G) ⊆ sp6F₂ φ he z → IsMulCommutative E' →
          Nat.card E' = 512 → E' = sp6E₂ φ he z) := by
  intro u f E n Q r θ₁ A₁ D₁ hlam hexp
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, hRc, -, -, -, -, hker, -, -, -, ⟨σ, hσsurj, hσker, hσcol, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂', ν₂', hD₂, hFD₂, hD₂N, hRF₂, hD₂n, hF₂'n, hD₂card, -, hν₂z, hν₂eq, hν₂surj,
    hact₂, hF₂'mem, hprod₂, hD₂H, -, -, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  subst hD₂
  have hκ : ∀ d ∈ CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G)),
      ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)) := by
    intro d hd C B ε h
    have h1 := Multiplicative.ofAdd.injective
      (radHom_injective φ he hzC hz hinf ((hν₂z d hd).symm.trans h))
    have h2 : ν₂' d = C := congrArg Prod.fst h1
    rw [← h2]
    exact hact₂ d hd B ε
  have hcomp := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion hG hL hLn
    hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  obtain ⟨hκ0, C₁, E₂, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hC₁sq, hE₁c, hJc, hJ₀c, hJmul, hIJ₀,
    hK₀c, hMc, hK₀comm, hK₀z, hK₀A, hE₂n, hE₂F, hE₂c, hE₂card, hE₂uniq, hE₂sq, hA₂E₂, hF₂zE,
    hE₂R, hC₂n, hC₂card, hDzC, hC₂R, hC₂F, hEC, hEcen, hC₁C₂, hC₁E₂, hPc, hPcard, ν₂, ε,
    hνz, hνmul, hνs, hνk, hνlevi, hδs, hδk, hδlevi, hεf, hε0, hε1, -, hlam1⟩ :=
    hcomp κ 1 hκ (fun d hd a v ε h => by rw [one_mul]; exact hlam d hd a v ε h)
  subst hκ0
  set D₂ := CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G)) with hD₂
  have hE₂s : sp6E₂ φ he z = E₂ := by
    have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
      (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂, hE₂F, hE₂c, hE₂card⟩
    exact hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2
  have hC₂s : sp6C₂ φ he z = D₂ ⊓ centralizer (E₂ : Set G) := by
    rw [show sp6C₂ φ he z = sp6D₂ φ e z ⊓ centralizer (sp6E₂ φ he z : Set G) from rfl, hE₂s]
    rfl
  have hε : ε = 1 := by
    rcases zmod_two_eq_zero_or_eq_one ε with h0 | h1
    · exfalso
      obtain ⟨hsq0, -, -⟩ := hε0 h0
      have hdvd : Monoid.exponent (sp6C₂ φ he z) ∣ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          have hg : (g : G) ∈ D₂ ⊓ centralizer (E₂ : Set G) := by
            rw [← hC₂s]
            exact g.2
          exact hsq0 g hg)
      rw [hexp] at hdvd
      norm_num at hdvd
    · exact h1
  subst hε
  obtain ⟨-, -, -, -, hinv⟩ := hε1 rfl
  have hν₂s : ∀ d ∈ D₂, sp6ν₂ φ he z d = ν₂ d := fun d hd => tauHom_sp6ν₂ φ he z (hνz d hd)
  have hν₂s' : ∀ d ∈ D₂, sp6ν₂ φ he z d = ν₂' d := fun d hd =>
    tauHom_sp6ν₂ φ he z (tauHom_nu he φ hzC hz hν₂z hd).symm
  have hC₂D : D₂ ⊓ centralizer (E₂ : Set G) ≤ D₂ := inf_le_left
  refine ⟨hzC, σ, hsup, hinf, ?_, ?_⟩
  · refine
      { hRc := hRc
        hσ := hσ
        hfull := hfull
        hD₂N := hD₂N
        hD₂n := hD₂n
        hRD₂ := hRF₂.trans hFD₂
        hD₂card := hD₂card
        hD₂H := hD₂H
        hprod₂ := hprod₂
        hν₂z := fun d hd => by rw [hν₂s' d hd]; exact hν₂z d hd
        hpure := fun d hd B ε => by
          rw [hν₂s' d hd]
          have h1 := hact₂ d hd B ε
          rwa [zero_smul, add_zero] at h1
        hE₂c := by rw [hE₂s]; exact hE₂c
        hE₂card := by rw [hE₂s]; exact hE₂card
        hE₂sq := by rw [hE₂s]; exact hE₂sq
        hA₂E₂ := by rw [hE₂s]; exact hA₂E₂
        hE₂R := by rw [hE₂s]; exact hE₂R
        hC₂ := rfl
        hC₂n := by rw [hC₂s]; exact hC₂n
        hC₂card := by rw [hC₂s]; exact hC₂card
        hDzC := by rw [hC₂s]; exact hDzC
        hC₂R := by rw [hC₂s]; exact hC₂R
        hEC := by rw [hC₂s, hE₂s]; exact hEC
        hinv := by rw [hC₂s, hE₂s]; exact hinv
        hνs := fun B => by
          obtain ⟨c, hc, hcB⟩ := hνs B
          refine ⟨c, by rw [hC₂s]; exact hc, ?_⟩
          rw [hν₂s c (hC₂D hc), hcB]
        hνk := fun c hc => by
          rw [hC₂s] at hc
          rw [hν₂s c (hC₂D hc)]
          exact hνk c hc
        hδs := fun w => by
          obtain ⟨c, hc, hcw⟩ := hδs w
          refine ⟨c, by rw [hC₂s]; exact hc, ?_⟩
          rw [hν₂s c (hC₂D hc), hcw]
        hδk := fun c hc => by
          rw [hC₂s] at hc
          rw [hν₂s c (hC₂D hc), hE₂s]
          exact hδk c hc
        hsq := fun c hc => by
          rw [hC₂s] at hc
          rw [hν₂s c (hC₂D hc), (hεf c hc c hc).1]
          change tauHom φ he _ * z ^ (0 : ZMod 2).val = _
          rw [ZMod.val_zero, pow_zero, mul_one] }
  · rw [hE₂s]
    exact ⟨hE₂F, hE₂c, hE₂card, hE₂uniq⟩

theorem ptBase_of_setting {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₁ := pullSub φ (pointRadical b hb u f)
    let D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((A₁ ⊔ zpowers z : Subgroup G) : Set G))
    (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
    Monoid.exponent (sp6C₂ φ he z) = 4 →
    ∃ (hzC : z ∈ centralizer (L : Set G))
      (σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
        GL (Fin 3) (ZMod 2)),
      ∃ (C₁ F₁ : Subgroup G) (ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2),
      PtBase he hb φ hzC hz (sp6D₂ φ e z) (sp6C₂ φ he z) (sp6E₂ φ he z) (sp6ν₂ φ he z) σ
        (CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G))) C₁ F₁ ν₁ ∧
      ((sp6E₂ φ he z : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative (sp6E₂ φ he z) ∧
        Nat.card (sp6E₂ φ he z) = 512 ∧
        ∀ E' : Subgroup G, (E' : Set G) ⊆ sp6F₂ φ he z → IsMulCommutative E' →
          Nat.card E' = 512 → E' = sp6E₂ φ he z) := by
  intro u f E n Q r θ₁ A₁ D₁ hlam hexp
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, hRc, -, -, -, -, hker, -, -, -, ⟨σ, hσsurj, hσker, hσcol, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂', ν₂', hD₂, hFD₂, hD₂N, hRF₂, hD₂n, hF₂'n, hD₂card, -, hν₂z, hν₂eq, hν₂surj,
    hact₂, hF₂'mem, hprod₂, hD₂H, -, -, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  subst hD₂
  have hκ : ∀ d ∈ CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G)),
      ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)) := by
    intro d hd C B ε h
    have h1 := Multiplicative.ofAdd.injective
      (radHom_injective φ he hzC hz hinf ((hν₂z d hd).symm.trans h))
    have h2 : ν₂' d = C := congrArg Prod.fst h1
    rw [← h2]
    exact hact₂ d hd B ε
  have hcomp := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion hG hL hLn
    hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  obtain ⟨hκ0, C₁, E₂, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hC₁sq, hE₁c, hJc, hJ₀c, hJmul, hIJ₀,
    hK₀c, hMc, hK₀comm, hK₀z, hK₀A, hE₂n, hE₂F, hE₂c, hE₂card, hE₂uniq, hE₂sq, hA₂E₂, hF₂zE,
    hE₂R, hC₂n, hC₂card, hDzC, hC₂R, hC₂F, hEC, hEcen, hC₁C₂, hC₁E₂, hPc, hPcard, ν₂, ε,
    hνz, hνmul, hνs, hνk, hνlevi, hδs, hδk, hδlevi, hεf, hε0, hε1, -, hlam1⟩ :=
    hcomp κ 1 hκ (fun d hd a v ε h => by rw [one_mul]; exact hlam d hd a v ε h)
  subst hκ0
  set D₂ := CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G)) with hD₂
  have hE₂s : sp6E₂ φ he z = E₂ := by
    have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
      (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂, hE₂F, hE₂c, hE₂card⟩
    exact hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2
  have hC₂s : sp6C₂ φ he z = D₂ ⊓ centralizer (E₂ : Set G) := by
    rw [show sp6C₂ φ he z = sp6D₂ φ e z ⊓ centralizer (sp6E₂ φ he z : Set G) from rfl, hE₂s]
    rfl
  have hε : ε = 1 := by
    rcases zmod_two_eq_zero_or_eq_one ε with h0 | h1
    · exfalso
      obtain ⟨hsq0, -, -⟩ := hε0 h0
      have hdvd : Monoid.exponent (sp6C₂ φ he z) ∣ 2 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          have hg : (g : G) ∈ D₂ ⊓ centralizer (E₂ : Set G) := by
            rw [← hC₂s]
            exact g.2
          exact hsq0 g hg)
      rw [hexp] at hdvd
      norm_num at hdvd
    · exact h1
  subst hε
  obtain ⟨-, -, -, -, hinv⟩ := hε1 rfl
  have hν₂s : ∀ d ∈ D₂, sp6ν₂ φ he z d = ν₂ d := fun d hd => tauHom_sp6ν₂ φ he z (hνz d hd)
  have hν₂s' : ∀ d ∈ D₂, sp6ν₂ φ he z d = ν₂' d := fun d hd =>
    tauHom_sp6ν₂ φ he z (tauHom_nu he φ hzC hz hν₂z hd).symm
  have hC₂D : D₂ ⊓ centralizer (E₂ : Set G) ≤ D₂ := inf_le_left
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hsup hinf hz hV hD₂N
    hD₂n hν₂z hν₂eq hν₂surj hact₂
  obtain ⟨lam₀, D₁', F₁, ν₁, hD₁, hFD₁, hD₁N, hBF₁, hD₁n, hF₁n, hD₁card, hF₁card, -, -, -,
    hν₁z, hν₁eq, hν₁surj, hact₁, hF₁mem, hprod₁, hD₁H, hA₁n, hb₁c, hZF₁, -, -, -, -, hlam1₁,
    ⟨hγD₁, -, hγF₁, -⟩, -, hγeq⟩ := degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  subst hD₁
  have hlam₀ : lam₀ = 1 := by
    have he₂ : e (Sum.inl 1) ∈ pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) :=
      mem_pairOrth_inl_one he
    have hf₂ : e (Sum.inr 1) ∈ pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) :=
      inr_mem_pairOrth he (by decide)
    have hlam' : ∀ d ∈ CFSG.Assembly.pCoreOf 2
        (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)),
        ∀ (v : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2) (ε : ZMod 2),
        d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
          ptHom he hb φ hzC hz (Multiplicative.ofAdd
            (v + (b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))),
              (1 : ZMod 2)) + ε • ν₁ d, ε)) := fun d hd v ε => hlam d hd (ν₁ d) v ε (hν₁z d hd)
    obtain ⟨d, hd, hdν⟩ := hν₁surj (⟨e (Sum.inl 1), he₂⟩, 0)
    have h1 := hact₁ d hd (⟨e (Sum.inr 1), hf₂⟩, 0) 0
    have h2 := hlam' d hd (⟨e (Sum.inr 1), hf₂⟩, 0) 0
    have h3 := ptHom_injective he hb φ hzC hz hinf (h1.symm.trans h2)
    have hbv : b ((ν₁ d).1 : V) (e (Sum.inr 1)) = 1 := by
      rw [hdν]
      change b (e (Sum.inl 1)) (e (Sum.inr 1)) = 1
      rw [bilin_inl he, Basis.repr_self, Finsupp.single_eq_same]
    have h4 := congrArg (fun p => (Multiplicative.toAdd p).1.2) h3
    simp only [toAdd_ofAdd, Prod.snd_add, Prod.smul_snd, smul_eq_mul, zero_mul, add_zero,
      mul_one] at h4
    rw [hbv] at h4
    simpa using h4
  subst hlam₀
  obtain ⟨hZD₁, hAD₁, -⟩ := hlam1₁ rfl
  have hact₁' : ∀ d ∈ CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)),
      ∀ (v : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))),
            (1 : ZMod 2)) + ε • ν₁ d, ε)) := fun d hd v ε => by
    rw [hact₁ d hd v ε, one_mul]
  obtain ⟨-, hD₁₂, hN₁₂, hO₁₂⟩ := degree64_intersections he hb hnd φ hzC hsup hinf hz hD₂N hD₂n
    hν₂z hν₂eq hν₂surj hact₂ (hRF₂.trans hFD₂) hD₂H hD₁N hD₁n (hBF₁.trans hFD₁) hD₁H hν₁z hact₁
    hprod₁ σ hσcol hσker hσsurj hfull₁ hfull
  have hb₁ : ptB₁ he hb φ hzC hz = ((φ.symm (pointElt hb (mem_pairOrth_left
      (0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))).2) 1) : L) : G) := ptB₁_eq he hb φ hzC hz
  obtain ⟨hC₁comm, hC₁sq', hZ₁card, hZ₁A, hE₁', hZ₁C₂, hK₀', -, -, hZ₁iso, hZ₁sq⟩ := hlam1 rfl
  have hF₁s : (C₁ ⊓ F₁ : Subgroup G) = ((C₁ : Set G) ∩
      {d | d ∈ CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) ∧
        z⁻¹ * (d⁻¹ * z * d) ∈ zpowers ((φ.symm (pointElt hb (mem_pairOrth_left
          (0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))).2) 1) : L) : G)}) := by
    ext d
    rw [coe_inf, Set.mem_inter_iff, Set.mem_inter_iff]
    refine and_congr_right fun _ => ?_
    rw [SetLike.mem_coe, ← hb₁]
    exact ⟨fun h => ⟨hFD₁ h, (hγF₁ d (hFD₁ h)).2 h⟩, fun h => (hγF₁ d h.1).1 h.2⟩
  have hME : ((C₁ ⊓ sp6E₂ φ he z : Subgroup G) : Set G) = (C₁ : Set G) ∩ E₂ := by
    rw [coe_inf, hE₂s]
  have hLB : LagBase he φ hzC hz (sp6D₂ φ e z) (sp6C₂ φ he z) (sp6E₂ φ he z) (sp6ν₂ φ he z) σ :=
    { hRc := hRc
      hσ := hσ
      hfull := hfull
      hD₂N := hD₂N
      hD₂n := hD₂n
      hRD₂ := hRF₂.trans hFD₂
      hD₂card := hD₂card
      hD₂H := hD₂H
      hprod₂ := hprod₂
      hν₂z := fun d hd => by rw [hν₂s' d hd]; exact hν₂z d hd
      hpure := fun d hd B ε => by
        rw [hν₂s' d hd]
        have h1 := hact₂ d hd B ε
        rwa [zero_smul, add_zero] at h1
      hE₂c := by rw [hE₂s]; exact hE₂c
      hE₂card := by rw [hE₂s]; exact hE₂card
      hE₂sq := by rw [hE₂s]; exact hE₂sq
      hA₂E₂ := by rw [hE₂s]; exact hA₂E₂
      hE₂R := by rw [hE₂s]; exact hE₂R
      hC₂ := rfl
      hC₂n := by rw [hC₂s]; exact hC₂n
      hC₂card := by rw [hC₂s]; exact hC₂card
      hDzC := by rw [hC₂s]; exact hDzC
      hC₂R := by rw [hC₂s]; exact hC₂R
      hEC := by rw [hC₂s, hE₂s]; exact hEC
      hinv := by rw [hC₂s, hE₂s]; exact hinv
      hνs := fun B => by
        obtain ⟨c, hc, hcB⟩ := hνs B
        refine ⟨c, by rw [hC₂s]; exact hc, ?_⟩
        rw [hν₂s c (hC₂D hc), hcB]
      hνk := fun c hc => by
        rw [hC₂s] at hc
        rw [hν₂s c (hC₂D hc)]
        exact hνk c hc
      hδs := fun w => by
        obtain ⟨c, hc, hcw⟩ := hδs w
        refine ⟨c, by rw [hC₂s]; exact hc, ?_⟩
        rw [hν₂s c (hC₂D hc), hcw]
      hδk := fun c hc => by
        rw [hC₂s] at hc
        rw [hν₂s c (hC₂D hc), hE₂s]
        exact hδk c hc
      hsq := fun c hc => by
        rw [hC₂s] at hc
        rw [hν₂s c (hC₂D hc), (hεf c hc c hc).1]
        change tauHom φ he _ * z ^ (0 : ZMod 2).val = _
        rw [ZMod.val_zero, pow_zero, mul_one] }
  refine ⟨hzC, σ, C₁, F₁, ν₁,
    { toLagBase := hLB
      hnd := hnd
      hV := hV
      hsup := hsup
      hinf := hinf
      hD₁ := rfl
      hFD₁ := hFD₁
      hD₁N := hD₁N
      hBF₁ := hBF₁
      hD₁n := hD₁n
      hF₁n := hF₁n
      hD₁card := hD₁card
      hF₁card := hF₁card
      hν₁z := hν₁z
      hν₁eq := hν₁eq
      hν₁surj := hν₁surj
      hact₁ := hact₁'
      hF₁mem := hF₁mem
      hprod₁ := hprod₁
      hD₁H := hD₁H
      hA₁n := hA₁n
      hb₁c := hb₁c
      hZF₁ := hZF₁
      hZD₁ := hZD₁
      hAD₁ := hAD₁
      hγD₁ := hγD₁
      hγF₁ := hγF₁
      hγeq := hγeq
      hC₁D := hC₁D
      hC₁n := hC₁n
      hC₁card := hC₁c
      hC₁z := hC₁z
      hC₁B := hC₁B
      hC₁sq := by rw [hb₁]; exact hC₁sq'
      hC₁comm := by rw [hb₁]; exact hC₁comm
      hZ₁card := hZ₁card
      hZ₁A := by rw [hb₁]; exact hZ₁A
      hE₁ := SetLike.coe_injective (hF₁s.trans hE₁')
      hZ₁C₂ := by rw [hC₂s]; exact hZ₁C₂
      hK₀ := by rw [hME, hC₁E₂]; exact hK₀'
      hZ₁iso := hZ₁iso rfl
      hZ₁sq := by rw [hb₁, hZ₁sq, ZMod.val_one, pow_one]
      hE₁card := by rw [← SetLike.coe_sort_coe, hF₁s]; exact hE₁c
      hK₀card := hK₀c
      hMcard := by rw [← SetLike.coe_sort_coe, hME, hC₁E₂]; exact hMc
      hK₀comm := hK₀comm
      hK₀z := hK₀z
      hK₀A := hK₀A
      hC₁C₂ := by rw [hC₂s]; exact hC₁C₂
      hPcomm := hPc
      hPcard := hPcard
      hN₁₂ := hN₁₂
      hO₁₂ := hO₁₂
      hD₁₂ := hD₁₂ }, ?_⟩
  rw [hE₂s]
  exact ⟨hE₂F, hE₂c, hE₂card, hE₂uniq⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
