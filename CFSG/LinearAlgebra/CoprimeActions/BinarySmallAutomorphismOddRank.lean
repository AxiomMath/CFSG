module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank

open scoped IsMulCommutative

section General

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [Group E] [CFSG.IsElementaryAbelian p E]

@[expose] noncomputable def mulAutToGL {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) (Additive E)) :
    MulAut E →* Matrix.GeneralLinearGroup (Fin n) (ZMod p) :=
  MonoidHom.toHomUnits
    { toFun := fun σ => LinearMap.toMatrix b b
        ((MulEquiv.toAdditive σ).toAddMonoidHom.toZModLinearMap p)
      map_one' := by
        rw [← LinearMap.toMatrix_id b]
        congr 1
      map_mul' := fun σ τ => by
        rw [← LinearMap.toMatrix_mul]
        congr 1 }

theorem mulAutToGL_injective {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) (Additive E)) :
    Function.Injective (mulAutToGL (E := E) b) := by
  intro σ τ h
  have h1 := congrArg Units.val h
  change LinearMap.toMatrix b b _ = LinearMap.toMatrix b b _ at h1
  have h2 := (LinearMap.toMatrix b b).injective h1
  apply MulEquiv.ext
  intro x
  have h3 := LinearMap.congr_fun h2 (Additive.ofMul x)
  exact h3

theorem card_mulAut_dvd_GL [Finite E] {n : ℕ} (hE : Nat.card E = p ^ n) :
    Nat.card (MulAut E) ∣ ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
  have hdim : Module.finrank (ZMod p) (Additive E) = n := by
    have : Module.Finite (ZMod p) (Additive E) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    rw [Nat.card_zmod] at h
    change Nat.card E = _ at h
    rw [hE] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hdim
  haveI : Fintype (ZMod p) := ZMod.fintype p
  have hGL := Matrix.card_GL_field n (𝔽 := ZMod p)
  rw [ZMod.card] at hGL
  rw [← hGL]
  exact Subgroup.card_dvd_of_injective _ (mulAutToGL_injective b)

end General

theorem card_mulAut_dvd_168 {V : Type*} [Group V] [Finite V] [CFSG.IsElementaryAbelian 2 V]
    (h : CFSG.pRank 2 V ≤ 3) : Nat.card (MulAut V) ∣ 168 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.IsElementaryAbelian.isPGroup 2 V)
  have hn3 : n ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
    have hE : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup V) :=
      ⟨⟨⟨fun a b => Subtype.ext (Std.Commutative.comm (op := (· * ·)) (a : V) (b : V))⟩⟩,
        fun x _ => by
          have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (CFSG.IsElementaryAbelian.exponent_dvd_p 2 V) x
          exact this⟩
    have := CFSG.SectionRank.le_pRank Nat.prime_two.one_lt le_top hE
      (k := n) (by rw [Subgroup.card_top]; exact hn)
    omega
  have := card_mulAut_dvd_GL (E := V) hn
  refine this.trans ?_
  interval_cases n <;> decide

theorem pRank_le_one_of_card_dvd_168 {A : Type*} [Group A] [Finite A] (hdvd : Nat.card A ∣ 168)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.pRank p A ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  by_contra hlt
  replace hlt := not_le.mp hlt
  obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup A)
  have h1 : p ^ 2 ∣ Nat.card E := hcard ▸ pow_dvd_pow p hlt
  have h2 : p ^ 2 ∣ 168 := h1.trans ((Subgroup.card_subgroup_dvd_card E).trans hdvd)
  have h3 : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h2
  have h4 : p ≤ 12 := by nlinarith
  interval_cases p <;> first | exact absurd rfl hp2 | (exfalso; norm_num at hp; done) | (exfalso; norm_num at h2; done)

theorem pRank_le_one_of_injective {V : Type*} [Group V] [Finite V] [CFSG.IsElementaryAbelian 2 V]
    (h : CFSG.pRank 2 V ≤ 3) {H : Type*} [Group H] [Finite H] (f : H →* MulAut V)
    (hf : Function.Injective f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pRank p H ≤ 1 :=
  pRank_le_one_of_card_dvd_168
    ((Subgroup.card_dvd_of_injective f hf).trans (card_mulAut_dvd_168 h)) hp hp2

end CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank
