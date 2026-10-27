module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjE7
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjDisp
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinCard

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors


variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem adj132_sub_one_eq (g : adjointGroup .E7 K) :
    adj132 K g - 1 = (e7Z K).mapQ (e7Z K) (adjRep .E7 K g - 1) (fun v hv => by
      have h1 := e7Z_le_comap g hv
      simp only [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at h1 ⊢
      exact Submodule.sub_mem _ h1 hv) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (e7Z K) x
  rw [LinearMap.sub_apply, adj132_apply, Module.End.one_apply, Submodule.mapQ_apply,
    LinearMap.sub_apply, Module.End.one_apply, Submodule.Quotient.mk_sub]

set_option maxHeartbeats 800000 in
theorem adj132_finrank_ker_le (a : adjointGroup .E7 K) (ha : a ≠ 1) (ha2 : a ^ 2 = 1) :
    Module.finrank K (LinearMap.ker (adj132 K a - 1)) ≤ 99 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha, pow_one]
  obtain ⟨g, hg⟩ := adjoint_conj_into_U K .E7 (Subgroup.zpowers a) hP
  set u : adjointGroup .E7 K := g * a * g⁻¹ with hu_def
  have hu : u ∈ Uad K .E7 := hg ⟨a, Subgroup.mem_zpowers a, rfl⟩
  have hu' : ((u : adjointGroup .E7 K) : ModGL .E7 K) ∈ posUnipotent .E7 K := hu
  have hu1 : ((u : adjointGroup .E7 K) : ModGL .E7 K) ≠ 1 := by
    intro h
    apply ha
    have : u = 1 := Subtype.ext h
    rw [hu_def] at this
    have := congrArg (fun x => g⁻¹ * x * g) this
    simpa [mul_assoc] using this
  have hZ : Module.finrank K (e7Z K) ≤ 1 := by
    rw [show Module.finrank K (e7Z K) = 1 from finrank_span_singleton e7Hc_ne_zero]
  have hcomap : e7Z K ≤ (e7Z K).comap
      ((((u : adjointGroup .E7 K) : ModGL .E7 K) : Module.End K (RootModule .E7 K)) - 1) := by
    intro v hv
    have h1 := e7Z_le_comap u hv
    simp only [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at h1 ⊢
    exact Submodule.sub_mem _ h1 hv
  have hd := displacement_E7_quotient K hu' hu1 (e7Z K) hZ hcomap
  have hru : 33 ≤ Module.finrank K (LinearMap.range (adj132 K u - 1)) := by
    rw [adj132_sub_one_eq]
    exact hd
  have hgg : adj132 K g * adj132 K g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hconj : adj132 K u - 1 = (1 : K) • (adj132 K g * (adj132 K a - 1) * adj132 K g⁻¹) := by
    calc adj132 K u - 1 = adj132 K g * adj132 K a * adj132 K g⁻¹ - adj132 K g * adj132 K g⁻¹ := by
          rw [hgg, hu_def, map_mul, map_mul]
      _ = (1 : K) • (adj132 K g * (adj132 K a - 1) * adj132 K g⁻¹) := by
          rw [one_smul, mul_sub, sub_mul, mul_one]
  have hra : Module.finrank K (LinearMap.range (adj132 K u - 1)) =
      Module.finrank K (LinearMap.range (adj132 K a - 1)) := by
    have hgg' : adj132 K g⁻¹ * adj132 K g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hconj]
    exact finrank_range_conj (adj132 K g) (adj132 K g⁻¹) (adj132 K a - 1) hgg hgg' 1 one_ne_zero
  have hrn := LinearMap.finrank_range_add_finrank_ker (adj132 K a - 1)
  rw [finrank_adj132] at hrn
  omega

theorem adj132_fix_bound (A : Subgroup (adjointGroup .E7 K)) (hA : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card K ^ Module.finrank K
      (Representation.invariants ((adj132 K).comp A.subtype)) < Nat.card K ^ 132 := by
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
  have ha1' : (a : adjointGroup .E7 K) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hcard := e7_adjoint_abelian_card_bound K A hel
  have hle : Representation.invariants ((adj132 K).comp A.subtype) ≤
      LinearMap.ker (adj132 K a - 1) := by
    intro v hv
    have := hv ⟨a, haA⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at this
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, this, sub_self]
  have hfin := Submodule.finrank_mono hle
  have hker := adj132_finrank_ker_le K a ha1' (hel a haA)
  have hK2 : 2 ≤ Nat.card K := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  calc Nat.card A * Nat.card K ^ Module.finrank K
        (Representation.invariants ((adj132 K).comp A.subtype))
      ≤ Nat.card K ^ 27 * Nat.card K ^ 99 :=
        Nat.mul_le_mul hcard (Nat.pow_le_pow_right (by omega) (hfin.trans hker))
    _ = Nat.card K ^ 126 := by rw [← pow_add]
    _ < Nat.card K ^ 132 := Nat.pow_lt_pow_right (by omega) (by norm_num)

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
