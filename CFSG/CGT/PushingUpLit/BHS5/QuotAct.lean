module

public import CFSG.CGT.PushingUpLit.BHS.GlaubSylow
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V]

@[expose] noncomputable def quotAut (Z : Subgroup V) (g : stabSub Z) : MulAut (V ⧸ Z) :=
  QuotientGroup.congr Z Z (g.1 : MulAut V) (by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (g.2 y).2 hy
    · intro hx
      refine ⟨g.1.symm x, ?_, g.1.apply_symm_apply x⟩
      rw [← g.2 (g.1.symm x), g.1.apply_symm_apply]
      exact hx)

@[expose] noncomputable def quotAct (Z : Subgroup V) : stabSub Z →* MulAut (V ⧸ Z) where
  toFun := quotAut Z
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v => rfl

theorem quotAct_mk (Z : Subgroup V) (g : stabSub Z) (v : V) :
    quotAct Z g (QuotientGroup.mk v) = QuotientGroup.mk (g.1 v) := rfl

theorem mem_ker_quotAct (Z : Subgroup V) (g : stabSub Z) :
    g ∈ (quotAct Z).ker ↔ ∀ v : V, g.1 v * v⁻¹ ∈ Z := by
  have key : ∀ v : V, g.1 v * v⁻¹ = ((g.1 v)⁻¹ * v)⁻¹ := fun v => by
    rw [mul_inv_rev, inv_inv, mul_comm]
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v
    have h1 := congrArg (fun φ : MulAut (V ⧸ Z) => φ (QuotientGroup.mk v)) h
    simp only [quotAct_mk, MulAut.one_apply] at h1
    rw [key v]
    exact Z.inv_mem (QuotientGroup.eq.1 h1)
  · intro h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [quotAct_mk, MulAut.one_apply]
      refine QuotientGroup.eq.2 ?_
      have := Z.inv_mem (h v)
      rwa [key v, inv_inv] at this

theorem apply_eq_of_quad_odd (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V} (hx : Odd (orderOf x))
    {v : V} (hq : x (x v * v⁻¹) = x v * v⁻¹) : x v = v := by
  set w : V := x v * v⁻¹ with hw
  have hpow : ∀ i : ℕ, (x ^ i) w = w := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih, hq]
  have hdiv : ∀ i : ℕ, (x ^ i) w = (x ^ (i + 1)) v / (x ^ i) v := by
    intro i
    rw [hw, map_mul, map_inv, div_eq_mul_inv, ← MulAut.mul_apply, ← pow_succ]
  have hprod : ∏ _i ∈ Finset.range (orderOf x), w = 1 := by
    have h1 : ∏ i ∈ Finset.range (orderOf x), (x ^ i) w = 1 := by
      rw [Finset.prod_congr rfl fun i _ => hdiv i, Finset.prod_range_div (fun i => (x ^ i) v)]
      simp [pow_orderOf_eq_one]
    rwa [Finset.prod_congr rfl fun i _ => hpow i] at h1
  rw [Finset.prod_const, Finset.card_range] at hprod
  obtain ⟨k, hk⟩ := hx
  have hw1 : w = 1 := by
    rw [hk, pow_succ, pow_mul, hV w, one_pow, one_mul] at hprod
    exact hprod
  exact mul_inv_eq_one.1 hw1

theorem fix_of_quad_oddGen (hV : ∀ v : V, v ^ 2 = 1) {K : Subgroup (MulAut V)}
    (hK : K ≤ Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)}) {v : V}
    (hq : ∀ k ∈ K, ∀ k' ∈ K, k' (k v * v⁻¹) = k v * v⁻¹) : ∀ k ∈ K, k v = v := by
  have hle : Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} ≤
      MulAction.stabilizer (MulAut V) v := by
    rw [Subgroup.closure_le]
    rintro x ⟨hxK, hxo⟩
    exact apply_eq_of_quad_odd hV hxo (hq x hxK x hxK)
  intro k hk
  exact MulAction.mem_stabilizer_iff.1 (hle (hK hk))

end CFSG.CGT.PushingUpLit.BHS5
