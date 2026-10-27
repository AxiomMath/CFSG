module

public import Certificates.Data.FzBU
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def fzbMul (c : Bool) (x y : ℕ) : ℕ :=
  Certificates.FzBU.Mod.mul (Certificates.FzBU.modl c ()) x y

@[expose] def fzbIsM (x : ℕ) : Prop := x / 64 % 2 = 0

instance : DecidablePred fzbIsM := fun x => inferInstanceAs (Decidable (x / 64 % 2 = 0))

@[expose] def fzbW0 (x : ℕ) : Prop := x < 4 ∨ 128 ≤ x ∧ x < 132

instance : DecidablePred fzbW0 := fun x => inferInstanceAs (Decidable (x < 4 ∨ 128 ≤ x ∧ x < 132))

structure FzbChart {G : Type} [Group G] (c : Bool) (T₂ P : Subgroup G) (x₁ x₂ t q s lam : G)
    (β : ℕ → G) : Prop where
  mem : ∀ x < 1024, β x ∈ T₂
  surj : ∀ g ∈ T₂, ∃ x < 1024, β x = g
  inj : ∀ x < 1024, ∀ y < 1024, β x = β y → x = y
  one : β 0 = 1
  mul : ∀ x < 1024, ∀ y < 1024, β (fzbMul c x y) = β x * β y
  q_eq : β 64 = q
  s_eq : β 256 = s
  lam_eq : β 512 = lam
  t_eq : β 128 = t
  P_eq : ∀ g, g ∈ P ↔ ∃ x < 64, β x = g
  Z_eq : ∀ g, g ∈ fourGrp x₁ x₂ ↔ ∃ x < 4, β x = g

structure FzbIsEmb (c : Bool) (u : ℕ) (ψ : ℕ → ℕ) : Prop where
  map_u : ψ u = 128
  map_one : ψ 0 = 0
  lt : ∀ x < 1024, fzbMul c x u = fzbMul c u x → ψ x < 1024
  comm_t : ∀ x < 1024, fzbMul c x u = fzbMul c u x →
    fzbMul c (ψ x) 128 = fzbMul c 128 (ψ x)
  map_mul : ∀ x < 1024, ∀ y < 1024, fzbMul c x u = fzbMul c u x → fzbMul c y u = fzbMul c u y →
    ψ (fzbMul c x y) = fzbMul c (ψ x) (ψ y)
  inj : ∀ x < 1024, ∀ y < 1024, fzbMul c x u = fzbMul c u x → fzbMul c y u = fzbMul c u y →
    ψ x = ψ y → x = y

structure FzbFactsGen (c : Bool) : Prop where
  mul_lt : ∀ x < 1024, ∀ y < 1024, fzbMul c x y < 1024
  t_eq : fzbMul c 64 64 = 128
  qs_eq : fzbMul c 64 256 = 320
  qsy_eq : fzbMul c 320 512 = 832
  card_M : ((Finset.range 1024).filter fzbIsM).card = 512
  M_mul : ∀ x < 1024, fzbIsM x → ∀ y < 1024, fzbIsM y → fzbIsM (fzbMul c x y)
  M_sq : ∀ m < 1024, fzbIsM m → fzbMul c m m < 64
  F3 : ∀ z, 0 < z → z < 4 →
    256 < ((Finset.range 1024).filter (fun n => fzbMul c n z = fzbMul c z n)).card
  V2 : ∀ v < 1024, ¬ fzbIsM v → fzbMul c v v = 0 →
    ∃ g < 1024, fzbMul c g v = fzbMul c 320 g ∨ fzbMul c g v = fzbMul c 832 g
  W0_mul : ∀ x < 1024, fzbW0 x → ∀ y < 1024, fzbW0 y → fzbW0 (fzbMul c x y)
  comm_z_t : fzbMul c 1 128 = fzbMul c 128 1
  comm_z_u : fzbMul c 1 832 = fzbMul c 832 1
  comm_t_u : fzbMul c 128 832 = fzbMul c 832 128
  sq_z : fzbMul c 1 1 = 0
  sq_t : fzbMul c 128 128 = 0
  sq_u : fzbMul c 832 832 = 0
  nodup : [128, fzbMul c 128 1, 832, fzbMul c 832 1, fzbMul c 128 832,
    fzbMul c (fzbMul c 128 832) 1].Nodup
  conj_tz : ∃ g < 1024, fzbMul c g 128 = fzbMul c (fzbMul c 128 1) g
  conj_uz : ∃ g < 1024, fzbMul c g 832 = fzbMul c (fzbMul c 832 1) g
  conj_tu : ∃ g < 1024, fzbMul c g 832 = fzbMul c (fzbMul c 128 832) g
  conj_tuz : ∃ g < 1024, fzbMul c g 832 = fzbMul c (fzbMul c (fzbMul c 128 832) 1) g

structure FzbFacts (c : Bool) : Prop extends FzbFactsGen c where
  H2 : ∀ ψ, FzbIsEmb c 832 ψ → fzbW0 (ψ 1) ∧ fzbW0 (ψ 128)

@[expose] def FzbH1 : Prop :=
  ∀ n₀, 4 ≤ n₀ → n₀ < 64 → fzbMul true n₀ n₀ = 0 →
    ∃ L : Finset ℕ, L.card = 32 ∧ 0 ∈ L ∧
      (∀ x ∈ L, x < 1024 ∧ fzbMul true x x = 0 ∧ fzbMul true x n₀ = fzbMul true n₀ x) ∧
      ∀ x ∈ L, ∀ y ∈ L, fzbMul true x y = fzbMul true y x ∧ fzbMul true x y ∈ L

@[expose] def FzbV1 : Prop :=
  ∀ m < 1024, fzbIsM m → fzbMul false (fzbMul false m m) (fzbMul false m m) = 0 →
    fzbMul false m m < 4

@[expose] def FzbFactsI : Prop := FzbFacts true ∧ FzbH1

@[expose] def FzbFactsII : Prop := FzbFacts false ∧ FzbV1

end CFSG.OddStandard.SmallF3.FritzII
