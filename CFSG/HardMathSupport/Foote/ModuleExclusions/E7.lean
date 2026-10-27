module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Common
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspTrans
public import CFSG.HardMathSupport.Foote.ModuleExclusions.ExcSigns
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistReduction
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign CFSG.CGT.PushingUpLit.CGT6M
open CFSG.RankThree.PartOne (ExceptionalCenterSmallPrimes)

set_option linter.unusedSectionVars false


section PairInj

variable {τ : Tag} (K : Type) [Field K]

theorem pinnedX_pair_inj' {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ ∧ 0 < height γ)
    (hδ : IsRoot τ δ ∧ 0 < height δ) (hne : γ ≠ δ) {c d c' d' : K}
    (h : pinnedX τ K γ c * pinnedX τ K δ d = pinnedX τ K γ c' * pinnedX τ K δ d') :
    c = c' ∧ d = d' := by
  classical
  have hnd : [γ, δ].Nodup := by simp [hne]
  have hprod : ∀ x y : K,
      ([γ, δ].map fun ε => pinnedX τ K ε (if ε = γ then x else y)).prod =
        pinnedX τ K γ x * pinnedX τ K δ y := fun x y => by simp [hne.symm]
  have heq : ([γ, δ].map fun ε => pinnedX τ K ε (if ε = γ then c else d)).prod =
      ([γ, δ].map fun ε => pinnedX τ K ε (if ε = γ then c' else d')).prod := by
    rw [hprod, hprod, h]
  have key := pinnedX_list_prod_injective [γ, δ] hnd (by simp [hγ, hδ]) _ _ heq
  have h1 := key γ (by simp)
  have h2 := key δ (by simp)
  simp only [ite_true, hne.symm, ite_false] at h1 h2
  exact ⟨h1, h2⟩

end PairInj

section Transport

variable {Q M : Type*} [Group Q] [Group M]

theorem invData_of_transport (ι : Q →* M) (hι : Function.Injective ι) (g D X Y : M) {t : Q}
    (hgt : g * ι t * g⁻¹ = D) (hX : ∃ x : Q, ι x = g⁻¹ * X * g)
    (hY : ∃ y : Q, ι y = g⁻¹ * Y * g) (hX5 : X ^ 5 = 1) (hY5 : Y ^ 5 = 1) (hXY : Commute X Y)
    (hind : ∀ i j : ZMod 5, X ^ i.val * Y ^ j.val = 1 → i = 0 ∧ j = 0)
    (hDX : D * X * D⁻¹ = X⁻¹) (hDY : D * Y * D⁻¹ = Y⁻¹) : InvData Q t := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  let c : M →* M := (MulAut.conj g⁻¹).toMonoidHom
  have hc : ∀ Z, c Z = g⁻¹ * Z * g := fun Z => by simp [c]
  have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective
  have hxc : ι x = c X := by rw [hx, hc]
  have hyc : ι y = c Y := by rw [hy, hc]
  have htc : ι t = g⁻¹ * D * g := by rw [← hgt]; group
  refine invData_of_pair (X := x) (Y := y) ?_ ?_ ?_ ?_ ?_ ?_
  · apply hι
    rw [map_pow, hxc, ← map_pow, hX5, map_one, map_one]
  · apply hι
    rw [map_pow, hyc, ← map_pow, hY5, map_one, map_one]
  · show x * y = y * x
    apply hι
    rw [map_mul, map_mul, hxc, hyc, ← map_mul, ← map_mul, hXY.eq]
  · intro i j hij
    apply hind i j
    apply hcinj
    calc c (X ^ i.val * Y ^ j.val) = ι (x ^ i.val * y ^ j.val) := by
          rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, hxc, hyc]
      _ = c 1 := by rw [hij, map_one, map_one]
  · show t * x * t⁻¹ = x⁻¹
    apply hι
    rw [map_mul, map_mul, map_inv, map_inv, htc, hxc, hc]
    calc g⁻¹ * D * g * (g⁻¹ * X * g) * (g⁻¹ * D * g)⁻¹ = g⁻¹ * (D * X * D⁻¹) * g := by group
      _ = g⁻¹ * X⁻¹ * g := by rw [hDX]
      _ = (g⁻¹ * X * g)⁻¹ := by group
  · show t * y * t⁻¹ = y⁻¹
    apply hι
    rw [map_mul, map_mul, map_inv, map_inv, htc, hyc, hc]
    calc g⁻¹ * D * g * (g⁻¹ * Y * g) * (g⁻¹ * D * g)⁻¹ = g⁻¹ * (D * Y * D⁻¹) * g := by group
      _ = g⁻¹ * Y⁻¹ * g := by rw [hDY]
      _ = (g⁻¹ * Y * g)⁻¹ := by group

end Transport

section FivePower

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem rootDiagUnit_pow_nat (a : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, rootDiagUnit_mul]

theorem rootDiagUnit_pow_card (a : Fin τ.rank → Kˣ) :
    rootDiagUnit τ a ^ Nat.card K = rootDiagUnit τ a := by
  have : Fintype K := Fintype.ofFinite K
  have h1 : a ^ Nat.card K = a := by
    funext i
    refine Units.ext ?_
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  rw [rootDiagUnit_pow_nat, h1]

theorem rootDiag_mul_mem_of_pow_five {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (a : Fin τ.rank → Kˣ) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (h5 : (rootDiagUnit τ a * g) ^ 5 = 1) : rootDiagUnit τ a * g ∈ adjointGroup τ K := by
  set d := rootDiagUnit τ a with hd
  have hdinv : ∀ {y : ModGL τ K}, y ∈ adjointGroup τ K → d⁻¹ * y * d ∈ adjointGroup τ K := by
    intro y hy
    have := conj_rootDiagUnit_mem_adjointGroup (a⁻¹) hy
    rw [← rootDiagUnit_inv, inv_inv] at this
    exact this
  have hn : ∀ n : ℕ, ∃ y ∈ adjointGroup τ K, (d * g) ^ n = d ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨y, hy, hyn⟩ := ih
      refine ⟨(d⁻¹ * y * d) * g, mul_mem (hdinv hy) hg, ?_⟩
      rw [pow_succ, hyn, pow_succ]
      group
  obtain ⟨y, hy, hy5⟩ := hn 5
  rw [h5] at hy5
  have hd5 : d ^ 5 ∈ adjointGroup τ K := by
    have : d ^ 5 = y⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hy5.symm
    rw [this]
    exact inv_mem hy
  have hq : 5 * 5 ^ (f - 1) = Nat.card K := by
    rw [hK, ← pow_succ']
    congr 1
    omega
  have hdA : d ∈ adjointGroup τ K := by
    have h1 : d = (d ^ 5) ^ (5 ^ (f - 1)) := by
      calc d = d ^ Nat.card K := (rootDiagUnit_pow_card a).symm
        _ = (d ^ 5) ^ (5 ^ (f - 1)) := by rw [← pow_mul, hq]
    rw [h1]
    exact pow_mem hd5 _
  exact mul_mem hdA hg

end FivePower

section Descent

variable {τ : Tag} {f : ℕ} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [CharP L 5] [Fact (Nat.Prime 5)]

theorem conj_mem_map_of_twistFixed (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (hFr : ∀ c, iterateFrobenius L 5 f c = c ^ Nat.card K)
    {g₁ N Z : ModGL τ L} (hg₁ : g₁ ∈ adjointGroup τ L)
    (hcoc : g₁ * (entrywiseFrobGL τ L 5 f g₁)⁻¹ = N) (hZ : Z ∈ adjointGroup τ L)
    (hZF : N * entrywiseFrobGL τ L 5 f Z * N⁻¹ = Z) (hZ5 : Z ^ 5 = 1) :
    ∃ z : ↥(adjointGroup τ K), baseChangeGL (algebraMap K L) (z : ModGL τ K) = g₁⁻¹ * Z * g₁ := by
  set E := entrywiseFrobGL τ L 5 f with hE
  have hEg : E g₁ = N⁻¹ * g₁ := by
    have h1 : (E g₁)⁻¹ = g₁⁻¹ * N := by rw [← hcoc]; group
    calc E g₁ = ((E g₁)⁻¹)⁻¹ := (inv_inv _).symm
      _ = N⁻¹ * g₁ := by rw [h1]; group
  have hEZ : E Z = N⁻¹ * Z * N := by
    calc E Z = N⁻¹ * (N * E Z * N⁻¹) * N := by group
      _ = N⁻¹ * Z * N := by rw [hZF]
  have hZ₁G : g₁⁻¹ * Z * g₁ ∈ adjointGroup τ L := mul_mem (mul_mem (inv_mem hg₁) hZ) hg₁
  have hZ₁F : Units.map (entrywiseHom (iterateFrobenius L 5 f)) (g₁⁻¹ * Z * g₁) =
      g₁⁻¹ * Z * g₁ := by
    change E (g₁⁻¹ * Z * g₁) = _
    rw [map_mul, map_mul, map_inv, hEg, hEZ]
    group
  obtain ⟨a, u, hu, hZ₁⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed τ (iterateFrobenius L 5 f)
    hFr hZ₁G hZ₁F
  obtain ⟨g'', hg'', rfl⟩ := Subgroup.mem_map.1 hu
  have hinj := baseChangeGL_injective (τ := τ) (algebraMap K L)
  have hZ₁5 : (g₁⁻¹ * Z * g₁) ^ 5 = 1 := by
    have := conj_pow (a := g₁⁻¹) (b := Z) (i := 5)
    rw [inv_inv] at this
    rw [this, hZ5]
    group
  have hZ₀5 : (rootDiagUnit τ a * g'') ^ 5 = 1 := by
    apply hinj
    rw [map_pow, map_mul, ← hZ₁, hZ₁5, map_one]
  exact ⟨⟨_, rootDiag_mul_mem_of_pow_five hf hK a hg'' hZ₀5⟩, (map_mul _ _ _).trans hZ₁.symm⟩

end Descent

section Pairs

variable {τ : Tag} {L : Type} [Field L] [CharP L 5]

@[expose] def InvPair (E : ModGL τ L →* ModGL τ L) (N D X Y : ModGL τ L) : Prop :=
  X ∈ adjointGroup τ L ∧ Y ∈ adjointGroup τ L ∧ N * E X * N⁻¹ = X ∧ N * E Y * N⁻¹ = Y ∧
    X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧ Commute X Y ∧
    (∀ i j : ZMod 5, X ^ i.val * Y ^ j.val = 1 → i = 0 ∧ j = 0) ∧
    D * X * D⁻¹ = X⁻¹ ∧ D * Y * D⁻¹ = Y⁻¹

theorem pinnedX_pow_nat (α : Fin τ.rank → ℤ) (n : ℕ) (c : L) :
    pinnedX τ L α c ^ n = pinnedX τ L α ((n : L) * c) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← pinnedX_add]
    congr 1
    push_cast
    ring

theorem pinnedX_pow_five (α : Fin τ.rank → ℤ) (c : L) : pinnedX τ L α c ^ 5 = 1 := by
  rw [pinnedX_pow_nat]
  have h5 : ((5 : ℕ) : L) = 0 := CharP.cast_eq_zero L 5
  rw [h5, zero_mul, pinnedX_zero]

theorem pinnedX_conj_neg {a : Fin τ.rank → Lˣ} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (ha : rootChar a α = -1) (c : L) :
    rootDiagUnit τ a * pinnedX τ L α c * (rootDiagUnit τ a)⁻¹ = pinnedX τ L α (-c) := by
  rw [rootDiagUnit_conj_pinnedX a hα, ha]
  simp

theorem frob_eq_of_mul_self_eq_one [Fact (Nat.Prime 5)] (f : ℕ) {ε : L} (hε : ε * ε = 1) :
    iterateFrobenius L 5 f ε = ε := by
  have h : (ε - 1) * (ε + 1) = 0 := by linear_combination hε
  rcases mul_eq_zero.1 h with h | h
  · have : ε = 1 := by linear_combination h
    rw [this, map_one]
  · have : ε = -1 := by linear_combination h
    rw [this, map_neg, map_one]

theorem exists_fixed_scalar [IsAlgClosed L] [Fact (Nat.Prime 5)] (f : ℕ) (hf : 1 ≤ f) {ε : L}
    (hε : ε * ε = 1) : ∃ c : L, c ≠ 0 ∧ ε * iterateFrobenius L 5 f c = c := by
  have hpos : 0 < 5 ^ f - 1 := by
    have : 5 ^ 1 ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ε hpos
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hc
    exact hε0 hc.symm
  refine ⟨c, hc0, ?_⟩
  rw [iterateFrobenius_def]
  have h1 : c ^ (5 ^ f) = c * ε := by
    rw [← hc, ← pow_succ']
    congr 1
    omega
  rw [h1]
  linear_combination c * hε

end Pairs

section Types

variable {τ : Tag} {L : Type} [Field L] [CharP L 5] [IsAlgClosed L] [Fact (Nat.Prime 5)]

theorem exists_fixed_root_element (f : ℕ) (hf : 1 ≤ f) (l : List (Fin τ.rank))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hωγ : ToralSign.wordElt τ l • γ = γ) :
    ∃ c : L, c ≠ 0 ∧ wordWeylMatrix τ L l * entrywiseFrobGL τ L 5 f (pinnedX τ L γ c) *
      (wordWeylMatrix τ L l)⁻¹ = pinnedX τ L γ c := by
  obtain ⟨ε, hε, hN⟩ := wordWeylMatrix_conj_pinnedX (k := L) l hγ
  obtain ⟨c, hc0, hc⟩ := exists_fixed_scalar f hf hε
  refine ⟨c, hc0, ?_⟩
  rw [entrywiseFrobGL_pinnedX, hN, hωγ, hc]

theorem invPair_type1 (f : ℕ) (hf : 1 ≤ f) (l : List (Fin τ.rank)) (a : Fin τ.rank → Lˣ)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hhα : 0 < height α)
    (hhβ : 0 < height β) (hne : α ≠ β) (h0 : iform α β = 0) (hnot : ¬ IsRoot τ (α + β))
    (hωα : ToralSign.wordElt τ l • α = α) (hωβ : ToralSign.wordElt τ l • β = β)
    (haα : rootChar a α = -1) (haβ : rootChar a β = -1) :
    ∃ X Y, InvPair (entrywiseFrobGL τ L 5 f) (wordWeylMatrix τ L l) (rootDiagUnit τ a) X Y := by
  obtain ⟨c₁, hc₁, hF₁⟩ := exists_fixed_root_element (L := L) f hf l hα hωα
  obtain ⟨c₂, hc₂, hF₂⟩ := exists_fixed_root_element (L := L) f hf l hβ hωβ
  refine ⟨pinnedX τ L α c₁, pinnedX τ L β c₂, pinnedX_mem_adjointGroup α c₁,
    pinnedX_mem_adjointGroup β c₂, hF₁, hF₂, pinnedX_pow_five α c₁, pinnedX_pow_five β c₂,
    pinnedX_commute_of_iform_eq_zero L hα hβ h0 hnot c₁ c₂, ?_, ?_, ?_⟩
  · intro i j hij
    rw [pinnedX_pow_nat, pinnedX_pow_nat] at hij
    have hij' : pinnedX τ L α (((i.val : ℕ) : L) * c₁) * pinnedX τ L β (((j.val : ℕ) : L) * c₂) =
        pinnedX τ L α 0 * pinnedX τ L β 0 := by
      rw [pinnedX_zero, pinnedX_zero, mul_one]
      exact hij
    obtain ⟨h1, h2⟩ := pinnedX_pair_inj' L ⟨hα, hhα⟩ ⟨hβ, hhβ⟩ hne hij'
    exact ⟨zmod_eq_zero_of_cast_eq_zero ((mul_eq_zero.1 h1).resolve_right hc₁),
      zmod_eq_zero_of_cast_eq_zero ((mul_eq_zero.1 h2).resolve_right hc₂)⟩
  · rw [pinnedX_conj_neg hα haα, ← pinnedX_neg]
  · rw [pinnedX_conj_neg hβ haβ, ← pinnedX_neg]

theorem exists_zeta (f : ℕ) (hf : 1 ≤ f) :
    ∃ ζ : L, iterateFrobenius L 5 f (iterateFrobenius L 5 f ζ) = ζ ∧
      ∀ i j : ZMod 5, ((i.val : ℕ) : L) + ((j.val : ℕ) : L) * ζ = 0 → i = 0 ∧ j = 0 := by
  let F := GaloisField 5 (2 * f)
  have hF : Nat.card F = 5 ^ (2 * f) := GaloisField.card 5 (2 * f) (by omega)
  have : Fintype F := Fintype.ofFinite F
  have h5 : 5 < Nat.card F := by
    rw [hF]
    calc 5 = 5 ^ 1 := by norm_num
      _ < 5 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨z, hz⟩ := exists_pair_indep (K := F) h5
  let _ : Algebra (ZMod 5) L := ZMod.algebra L 5
  have : Algebra.IsAlgebraic (ZMod 5) F := Algebra.IsAlgebraic.of_finite (ZMod 5) F
  let φ : F →ₐ[ZMod 5] L := IsAlgClosed.lift
  refine ⟨φ z, ?_, fun i j hij => hz i j ?_⟩
  · rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← map_pow]
    have h : 5 ^ f * 5 ^ f = Fintype.card F := by
      rw [← Nat.card_eq_fintype_card, hF, ← pow_add]
      congr 1
      omega
    rw [h, FiniteField.pow_card]
  · apply φ.injective
    rw [map_add, map_mul, map_natCast, map_natCast, map_zero]
    exact hij


theorem exists_fixed_scalar_sq (f : ℕ) (hf : 1 ≤ f) {ε : L} (hε : ε * ε = 1) :
    ∃ c : L, c ≠ 0 ∧ ε * iterateFrobenius L 5 f (iterateFrobenius L 5 f c) = c := by
  have hq : 5 ≤ 5 ^ f := by
    have : 5 ^ 1 ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hpos : 0 < 5 ^ f * 5 ^ f - 1 := by
    have : 25 ≤ 5 ^ f * 5 ^ f := by nlinarith
    omega
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ε hpos
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hc
    exact hε0 hc.symm
  refine ⟨c, hc0, ?_⟩
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul]
  have h1 : c ^ (5 ^ f * 5 ^ f) = c * ε := by
    rw [← hc, ← pow_succ']
    congr 1
    omega
  rw [h1]
  linear_combination c * hε

theorem invPair_type2 (f : ℕ) (hf : 1 ≤ f) (l : List (Fin τ.rank)) (a : Fin τ.rank → Lˣ)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hhα : 0 < height α)
    (hhβ : 0 < height β) (hne : α ≠ β) (h0 : iform α β = 0) (hnot : ¬ IsRoot τ (α + β))
    (hωα : ToralSign.wordElt τ l • α = β) (hωβ : ToralSign.wordElt τ l • β = α)
    (haα : rootChar a α = -1) (haβ : rootChar a β = -1) :
    ∃ X Y, InvPair (entrywiseFrobGL τ L 5 f) (wordWeylMatrix τ L l) (rootDiagUnit τ a) X Y := by
  set Fr := iterateFrobenius L 5 f with hFr
  obtain ⟨εα, hεα, hNα⟩ := wordWeylMatrix_conj_pinnedX (k := L) l hα
  obtain ⟨εβ, hεβ, hNβ⟩ := wordWeylMatrix_conj_pinnedX (k := L) l hβ
  rw [hωα] at hNα
  rw [hωβ] at hNβ
  have hFrα : Fr εα = εα := frob_eq_of_mul_self_eq_one f hεα
  have hcomm : ∀ c d : L, pinnedX τ L α c * pinnedX τ L β d = pinnedX τ L β d * pinnedX τ L α c :=
    fun c d => pinnedX_commute_of_iform_eq_zero L hα hβ h0 hnot c d
  let Xf : L → ModGL τ L := fun c => pinnedX τ L α c * pinnedX τ L β (εα * Fr c)
  have Xadd : ∀ c c' : L, Xf (c + c') = Xf c * Xf c' := by
    intro c c'
    change pinnedX τ L α (c + c') * pinnedX τ L β (εα * Fr (c + c')) = _
    rw [map_add, mul_add, pinnedX_add, pinnedX_add]
    change _ = (pinnedX τ L α c * pinnedX τ L β (εα * Fr c)) *
      (pinnedX τ L α c' * pinnedX τ L β (εα * Fr c'))
    calc pinnedX τ L α c * pinnedX τ L α c' *
          (pinnedX τ L β (εα * Fr c) * pinnedX τ L β (εα * Fr c'))
        = pinnedX τ L α c * (pinnedX τ L α c' * pinnedX τ L β (εα * Fr c)) *
            pinnedX τ L β (εα * Fr c') := by group
      _ = pinnedX τ L α c * (pinnedX τ L β (εα * Fr c) * pinnedX τ L α c') *
            pinnedX τ L β (εα * Fr c') := by rw [hcomm c' (εα * Fr c)]
      _ = _ := by group
  have Xzero : Xf 0 = 1 := by simp [Xf, pinnedX_zero]
  have Xpow : ∀ (n : ℕ) (c : L), Xf c ^ n = Xf ((n : L) * c) := by
    intro n c
    induction n with
    | zero => simp [Xzero]
    | succ n ih =>
      rw [pow_succ, ih, ← Xadd]
      congr 1
      push_cast
      ring
  have h5 : ((5 : ℕ) : L) = 0 := CharP.cast_eq_zero L 5
  have X5 : ∀ c, Xf c ^ 5 = 1 := fun c => by rw [Xpow, h5, zero_mul, Xzero]
  have Xneg : ∀ c, Xf (-c) = (Xf c)⁻¹ := fun c => by
    rw [eq_inv_iff_mul_eq_one, ← Xadd, neg_add_cancel, Xzero]
  have Xfix : ∀ c : L, εβ * (εα * Fr (Fr c)) = c →
      wordWeylMatrix τ L l * entrywiseFrobGL τ L 5 f (Xf c) * (wordWeylMatrix τ L l)⁻¹ = Xf c := by
    intro c hc
    set N := wordWeylMatrix τ L l with hN
    have hE : entrywiseFrobGL τ L 5 f (Xf c) =
        pinnedX τ L α (Fr c) * pinnedX τ L β (εα * Fr (Fr c)) := by
      change entrywiseFrobGL τ L 5 f (pinnedX τ L α c * pinnedX τ L β (εα * Fr c)) = _
      rw [map_mul, entrywiseFrobGL_pinnedX, entrywiseFrobGL_pinnedX, map_mul, hFrα]
    rw [hE]
    calc N * (pinnedX τ L α (Fr c) * pinnedX τ L β (εα * Fr (Fr c))) * N⁻¹ =
          (N * pinnedX τ L α (Fr c) * N⁻¹) * (N * pinnedX τ L β (εα * Fr (Fr c)) * N⁻¹) := by
          group
      _ = pinnedX τ L β (εα * Fr c) * pinnedX τ L α (εβ * (εα * Fr (Fr c))) := by
          rw [hNα, hNβ]
      _ = Xf c := by
          rw [hc]
          exact (hcomm _ _).symm
  have hη : (εβ * εα) * (εβ * εα) = 1 := by
    calc (εβ * εα) * (εβ * εα) = (εβ * εβ) * (εα * εα) := by ring
      _ = 1 := by rw [hεα, hεβ, one_mul]
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_fixed_scalar_sq f hf hη
  obtain ⟨ζ, hζ, hζind⟩ := exists_zeta (L := L) f hf
  have hc₀' : εβ * (εα * Fr (Fr c₀)) = c₀ := by rw [← mul_assoc]; exact hc₀
  have hc₁' : εβ * (εα * Fr (Fr (c₀ * ζ))) = c₀ * ζ := by
    rw [map_mul, map_mul, hζ]
    calc εβ * (εα * (Fr (Fr c₀) * ζ)) = (εβ * (εα * Fr (Fr c₀))) * ζ := by ring
      _ = c₀ * ζ := by rw [hc₀']
  have hD : ∀ c, rootDiagUnit τ a * Xf c * (rootDiagUnit τ a)⁻¹ = Xf (-c) := by
    intro c
    change rootDiagUnit τ a * (pinnedX τ L α c * pinnedX τ L β (εα * Fr c)) *
      (rootDiagUnit τ a)⁻¹ = pinnedX τ L α (-c) * pinnedX τ L β (εα * Fr (-c))
    rw [show rootDiagUnit τ a * (pinnedX τ L α c * pinnedX τ L β (εα * Fr c)) *
        (rootDiagUnit τ a)⁻¹ = (rootDiagUnit τ a * pinnedX τ L α c * (rootDiagUnit τ a)⁻¹) *
          (rootDiagUnit τ a * pinnedX τ L β (εα * Fr c) * (rootDiagUnit τ a)⁻¹) by group,
      pinnedX_conj_neg hα haα, pinnedX_conj_neg hβ haβ, map_neg, mul_neg]
  have hmemX : ∀ c, Xf c ∈ adjointGroup τ L := fun c =>
    mul_mem (pinnedX_mem_adjointGroup α c) (pinnedX_mem_adjointGroup β _)
  refine ⟨Xf c₀, Xf (c₀ * ζ), hmemX _, hmemX _, Xfix _ hc₀', Xfix _ hc₁', X5 _, X5 _, ?_, ?_,
    ?_, ?_⟩
  · show Xf c₀ * Xf (c₀ * ζ) = Xf (c₀ * ζ) * Xf c₀
    rw [← Xadd, ← Xadd, add_comm]
  · intro i j hij
    rw [Xpow, Xpow, ← Xadd] at hij
    have hij' : pinnedX τ L α (((i.val : ℕ) : L) * c₀ + ((j.val : ℕ) : L) * (c₀ * ζ)) *
        pinnedX τ L β (εα * Fr (((i.val : ℕ) : L) * c₀ + ((j.val : ℕ) : L) * (c₀ * ζ))) =
        pinnedX τ L α 0 * pinnedX τ L β 0 := by
      rw [pinnedX_zero, pinnedX_zero, mul_one]
      exact hij
    obtain ⟨h1, -⟩ := pinnedX_pair_inj' L ⟨hα, hhα⟩ ⟨hβ, hhβ⟩ hne hij'
    have h2 : c₀ * (((i.val : ℕ) : L) + ((j.val : ℕ) : L) * ζ) = 0 := by
      linear_combination h1
    exact hζind i j ((mul_eq_zero.1 h2).resolve_left hc₀0)
  · rw [hD, Xneg]
  · rw [hD, Xneg]

end Types

section Table

theorem wordElt_smul {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    ToralSign.wordElt τ l • v = l.foldl (fun v i => reflect τ i v) v := by
  induction l generalizing v with
  | nil => simp [ToralSign.wordElt]
  | cons i l ih =>
    have h : ToralSign.wordElt τ (i :: l) = ToralSign.wordElt τ l * simple τ i := by
      simp only [ToralSign.wordElt, List.reverse_cons, CoxeterSystem.wordProd_append,
        CoxeterSystem.wordProd_singleton]
    rw [h, mul_smul, simple_smul, ih, List.foldl_cons]

theorem not_isRoot_of_isRootB_eq_false {τ : Tag} {v : Fin τ.rank → ℤ}
    (h : RootOps.isRootB τ v = false) : ¬ IsRoot τ v := fun hr => by
  rw [← RootOps.isRootB_iff, h] at hr
  exact Bool.false_ne_true hr

theorem rootChar_signMaskTuple_eq {τ : Tag} {L : Type} [Field L] (m : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (signMaskTuple τ L m) v =
      (-1 : Lˣ) ^ (∑ k : Fin τ.rank, ((m / 2 ^ (k : ℕ) % 2 : ℕ) : ℤ) * v k) := by
  have h : ∀ k : Fin τ.rank, (signMaskTuple τ L m k) ^ v k =
      (-1 : Lˣ) ^ (((m / 2 ^ (k : ℕ) % 2 : ℕ) : ℤ) * v k) := fun k => by
    rw [zpow_mul, signMaskTuple, zpow_natCast]
  rw [rootChar, Finset.prod_congr rfl fun k _ => h k, prod_zpow_sum]

theorem rootChar_signMaskTuple_of_odd {τ : Tag} {L : Type} [Field L] {m : ℕ}
    {v : Fin τ.rank → ℤ} (h : (∑ k : Fin τ.rank, ((m / 2 ^ (k : ℕ) % 2 : ℕ) : ℤ) * v k) % 2 = 1) :
    rootChar (signMaskTuple τ L m) v = -1 := by
  rw [rootChar_signMaskTuple_eq]
  exact (Int.odd_iff.2 h).neg_one_zpow

def e7vec (l : List ℤ) : Fin Tag.E7.rank → ℤ := fun i => l.getD i 0

def e7Refl (l : List (Fin Tag.E7.rank)) (v : Fin Tag.E7.rank → ℤ) : Fin Tag.E7.rank → ℤ :=
  l.foldl (fun v i => reflect Tag.E7 i v) v

end Table

section Main

variable {L : Type} [Field L] [CharP L 5] [IsAlgClosed L] [Fact (Nat.Prime 5)]

theorem e7_invPair_type1 (f : ℕ) (hf : 1 ≤ f) (m : ℕ) (l : List (Fin Tag.E7.rank))
    (α β : Fin Tag.E7.rank → ℤ)
    (h : RootOps.isRootB .E7 α = true ∧ RootOps.isRootB .E7 β = true ∧ 0 < height α ∧
      0 < height β ∧ α ≠ β ∧ iform α β = 0 ∧ RootOps.isRootB .E7 (α + β) = false ∧
      e7Refl l α = α ∧ e7Refl l β = β ∧
      (∑ k : Fin Tag.E7.rank, ((m / 2 ^ (k : ℕ) % 2 : ℕ) : ℤ) * α k) % 2 = 1 ∧
      (∑ k : Fin Tag.E7.rank, ((m / 2 ^ (k : ℕ) % 2 : ℕ) : ℤ) * β k) % 2 = 1) :
    ∃ X Y, InvPair (entrywiseFrobGL .E7 L 5 f) (wordWeylMatrix .E7 L l)
      (rootDiagUnit .E7 (signMaskTuple .E7 L m)) X Y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact invPair_type1 f hf l _ (RootOps.isRootB_iff.1 h1) (RootOps.isRootB_iff.1 h2) h3 h4 h5 h6
    (not_isRoot_of_isRootB_eq_false h7) (by rw [wordElt_smul]; exact h8)
    (by rw [wordElt_smul]; exact h9) (rootChar_signMaskTuple_of_odd h10)
    (rootChar_signMaskTuple_of_odd h11)

theorem e7_invPair_type2 (f : ℕ) (hf : 1 ≤ f) (m : ℕ) (l : List (Fin Tag.E7.rank))
    (α β : Fin Tag.E7.rank → ℤ)
    (h : RootOps.isRootB .E7 α = true ∧ RootOps.isRootB .E7 β = true ∧ 0 < height α ∧
      0 < height β ∧ α ≠ β ∧ iform α β = 0 ∧ RootOps.isRootB .E7 (α + β) = false ∧
      e7Refl l α = β ∧ e7Refl l β = α ∧
      (∑ k : Fin Tag.E7.rank, ((m / 2 ^ (k : ℕ) % 2 : ℕ) : ℤ) * α k) % 2 = 1 ∧
      (∑ k : Fin Tag.E7.rank, ((m / 2 ^ (k : ℕ) % 2 : ℕ) : ℤ) * β k) % 2 = 1) :
    ∃ X Y, InvPair (entrywiseFrobGL .E7 L 5 f) (wordWeylMatrix .E7 L l)
      (rootDiagUnit .E7 (signMaskTuple .E7 L m)) X Y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact invPair_type2 f hf l _ (RootOps.isRootB_iff.1 h1) (RootOps.isRootB_iff.1 h2) h3 h4 h5 h6
    (not_isRoot_of_isRootB_eq_false h7) (by rw [wordElt_smul]; exact h8)
    (by rw [wordElt_smul]; exact h9) (rootChar_signMaskTuple_of_odd h10)
    (rootChar_signMaskTuple_of_odd h11)

theorem e7_exists_invPair (f : ℕ) (hf : 1 ≤ f) {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    (hm : r.mask ≠ 0) {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords) :
    ∃ X Y, InvPair (entrywiseFrobGL .E7 L 5 f) (wordWeylMatrix .E7 L l)
      (rootDiagUnit .E7 (signMaskTuple .E7 L r.mask)) X Y := by
  simp only [e7SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact absurd rfl hm
  · simp only [e7OmegaWords1, List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl
    exact e7_invPair_type1 f hf 1 [] (e7vec [1, 1, 2, 2, 2, 1, 0]) (e7vec [1, 1, 2, 3, 2, 1, 1])
      (by decide +kernel)
  · simp only [e7OmegaWords2, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact e7_invPair_type1 f hf 2 [] (e7vec [1, 1, 2, 2, 2, 1, 0]) (e7vec [1, 1, 2, 3, 2, 1, 1])
        (by decide +kernel)
    · exact e7_invPair_type1 f hf 2 e7Word2_1 (e7vec [1, 1, 1, 2, 1, 1, 0])
        (e7vec [1, 1, 2, 2, 1, 1, 1]) (by decide +kernel)
  · simp only [e7OmegaWords3, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact e7_invPair_type1 f hf 3 [] (e7vec [0, 1, 1, 2, 2, 1, 1]) (e7vec [1, 0, 1, 1, 1, 0, 0])
        (by decide +kernel)
    · exact e7_invPair_type2 f hf 3 e7Word3_1 (e7vec [1, 2, 2, 3, 2, 2, 1])
        (e7vec [1, 0, 1, 1, 0, 0, 0]) (by decide +kernel)

end Main

section Final

theorem e7_five_invData {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) (t : ↥(adjointGroup .E7 K)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    InvData ↥(adjointGroup .E7 K) t := by
  classical
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd (Nat.card K) := by rw [hK]; exact Odd.pow (by decide)
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 5 := charP_five_of_card hK
  set L := AlgebraicClosure K with hL
  have hLchar : CharP L 5 := charP_of_injective_algebraMap (algebraMap K L).injective 5
  set ι := algebraMap K L with hι
  set Fr := iterateFrobenius L 5 f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, hK]
  obtain ⟨hinj, -, -, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L ι
  obtain ⟨-, hHR, -, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hodd L Fr hFr
  set x := baseChangeGL ι (t : ModGL .E7 K) with hx_def
  have hF1 : frobTwistGL .E7 L 5 f 1 = Units.map (entrywiseHom Fr) :=
    MonoidHom.ext fun y => by rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hRR : fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L 5 f 1) =
      adjointGroup .E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    rw [hF1]
  have hxR : x ∈ fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L 5 f 1) := by
    rw [hRR]
    exact hHR (Subgroup.mem_map_of_mem _ t.2)
  have ht2' : (t : ModGL .E7 K) ^ 2 = 1 := by
    rw [sq]
    exact congrArg Subtype.val ht2
  have hx2 : x ^ 2 = 1 := by
    rw [hx_def, ← map_pow, ht2', map_one]
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, hg₁G, hconj, hcoc, -⟩ :=
    isFiniteToralTwistReduction_of_reps_exact 5 hp2 (e := f) hf (map_conj_one_adjointGroup _ L)
      1 (fun b hb => by
        rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign 5 f hb, one_mul, inv_one,
          mul_one]
        rfl)
      e7SignDiagramReps h7.permChar_eq h7.exists_rep h7.coe_kernelPosStabilizer
      (finite_fixedPointsIn_frobTwistGL 5 hf le_rfl (map_one _) (one_pow 1)) hxR hx2
  rw [signCharTuple_signMaskChar] at hconj
  have hcoc' : g₁ * (entrywiseFrobGL .E7 L 5 f g₁)⁻¹ = wordWeylMatrix .E7 L l := by
    rw [← hcoc, frobTwistGL_apply, one_mul, inv_one, mul_one]
  let ι₀ : ↥(adjointGroup .E7 K) →* ModGL .E7 L :=
    (baseChangeGL ι).comp (adjointGroup .E7 K).subtype
  have hι₀ : Function.Injective ι₀ := hinj.comp (adjointGroup .E7 K).subtype_injective
  by_cases hm0 : r.mask = 0
  · exfalso
    apply ht1
    apply hι₀
    have h0 : signMaskTuple .E7 L r.mask = 1 := by
      funext j
      simp [signMaskTuple, hm0]
    rw [h0, rootDiagUnit_one] at hconj
    rw [map_one]
    calc ι₀ t = g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁ := by
          change x = _
          group
      _ = 1 := by rw [hconj]; group
  obtain ⟨X, Y, hXG, hYG, hXF, hYF, hX5, hY5, hXY, hind, hDX, hDY⟩ :=
    e7_exists_invPair (L := L) f hf hr hm0 hl
  have hAlg : Algebra.IsAlgebraic K L := inferInstance
  refine invData_of_transport ι₀ hι₀ g₁ _ X Y (t := t) hconj ?_ ?_ hX5 hY5 hXY hind hDX hDY
  · obtain ⟨z, hz⟩ := conj_mem_map_of_twistFixed hf hK hFr hg₁G hcoc' hXG hXF hX5
    exact ⟨z, hz⟩
  · obtain ⟨z, hz⟩ := conj_mem_map_of_twistFixed hf hK hFr hg₁G hcoc' hYG hYF hY5
    exact ⟨z, hz⟩

theorem coverInv_e7_charFive (hECS : ExceptionalCenterSmallPrimes) {f : ℕ} (Q : Type) [Group Q]
    (hQ : ChevalleyExceptionalModel Q .E7 5 f) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e0⟩⟩ := hQ
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7
    (⟨K, hKf, hKfin, hKc, ⟨e0⟩⟩ : UntwistedChevalleyModel Q .E7 (5 ^ f))
  refine coverInv_of_data (fun w hw1 hw2 => ?_) (fun L _ _ hq hodd ⟨e'⟩ => ?_)
  · have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
    have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
    exact invData_of_equiv e (e7_five_invData hf K' hK'c (e w) hew1 hew2)
  · have hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .E7 5 f :=
      ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e0⟩⟩
    exact hECS L (isQuasisimple_of_open hq)
      (Or.inl ⟨.E7, 5, f, by simp [chevalleyExceptionalTags], hmod⟩) 5 Nat.prime_five
      (by norm_num)

end Final

end CFSG.HardMathSupport.Foote.ModuleExclusions
