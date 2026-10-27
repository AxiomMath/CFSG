module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowPerm
import CFSG.LocalAnalysis.AGLEmbedding.RankRefinedAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 CFSG.SectionRank.Native CFSG.Monster.B.Co2
open scoped commutatorElement

theorem isPGroup_closure_of_normalForm {X : Type*} [Group X] {p : ℕ} (hp : 0 < p) {x y : X}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcube : ∀ i < p, ∀ j < p, ∀ k < p, (x ^ i * y ^ j * ⁅x, y⁆ ^ k) ^ p = 1) :
    IsPGroup p (Subgroup.closure ({x, y} : Set X)) := by
  intro g
  obtain ⟨i, j, k, hi, hj, hk, hg⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp hx hy hzx hzy g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, hg, Subgroup.coe_one]
  exact hcube i hi j hj k hk

theorem centralizer_le_narrowGamma_of_commute {p : ℕ} {X : Type*} [Group X] [Finite X]
    (hp : p.Prime) {Q : Subgroup X} {w u : X} (hwQ : w ∈ Q) (huQ : u ∈ Q) (hw : w ^ p = 1)
    (hu : u ^ p = 1) (hw1 : w ≠ 1) (hwu : Commute w u) (huw : ∀ k < p, u ≠ w ^ k) :
    Subgroup.centralizer ({w} : Set X) ≤ narrowGamma p Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have huz : u ∉ Subgroup.zpowers w := by
    classical
    intro hz
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime hw hw1] at hz
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 hz
    exact huw k (Finset.mem_range.1 hk) hke.symm
  have hcard := card_closure_pair_sq hwu hw hu hw1 huz
  have hE : IsElemAbelian p (Subgroup.closure ({w, u} : Set X)) :=
    IsElemAbelian.closure_of_commute
      (by rintro a (rfl | rfl) b (rfl | rfl); exacts [rfl, hwu.eq, hwu.symm.eq, rfl])
      (by rintro a (rfl | rfl); exacts [hw, hu])
  refine centralizer_le_narrowGamma hwQ (orderOf_eq_prime hw hw1) ?_
  refine CFSG.SectionRank.le_pRank hp.one_lt (le_inf ?_ ?_) hE hcard
  · rw [Subgroup.closure_le]
    rintro a (rfl | rfl)
    exacts [hwQ, huQ]
  · rw [Subgroup.closure_le]
    rintro a (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hwu.symm.eq

theorem narrowGamma_eq_top_of_hpData {p : ℕ} (hp : p.Prime) {X K : Type} [Group X] [Finite X]
    [Group K] [Finite K] (eX : X ≃* K) {a b x y s₁ s₂ : X}
    (hab : Subgroup.closure ({a, b} : Set X) = ⊤) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcube : ∀ i < p, ∀ j < p, ∀ k < p, (x ^ i * y ^ j * ⁅x, y⁆ ^ k) ^ p = 1)
    (hzxk : ∀ k < p, ⁅x, y⁆ ≠ x ^ k) (hzyk : ∀ k < p, ⁅x, y⁆ ≠ y ^ k) (h₁ : s₁ * x = x * s₁)
    (h₂ : s₂ * y = y * s₂) (ha : a ∈ Subgroup.closure ({s₁, s₂} : Set X))
    (hb : b ∈ Subgroup.closure ({s₁, s₂} : Set X)) (T : Sylow p K) :
    narrowGamma p (T : Subgroup K) = ⊤ := by
  set Q := Subgroup.closure ({x, y} : Set X) with hQ
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hzQ : ⁅x, y⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hxQ hyQ) (Q.inv_mem hxQ)) (Q.inv_mem hyQ)
  have hz : ⁅x, y⁆ ^ p = 1 := by
    rw [CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]
  have hx1 : x ≠ 1 := fun h => hzxk 0 hp.pos (by rw [h, commutatorElement_one_left, pow_zero])
  have hy1 : y ≠ 1 := fun h => hzyk 0 hp.pos (by rw [h, commutatorElement_one_right, pow_zero])
  have hs : Subgroup.closure ({s₁, s₂} : Set X) ≤ narrowGamma p Q := by
    rw [Subgroup.closure_le]
    rintro s (rfl | rfl)
    · exact centralizer_le_narrowGamma_of_commute hp hxQ hzQ hx hz hx1 hzx.symm hzxk
        (Subgroup.mem_centralizer_singleton_iff.2 h₁)
    · exact centralizer_le_narrowGamma_of_commute hp hyQ hzQ hy hz hy1 hzy.symm hzyk
        (Subgroup.mem_centralizer_singleton_iff.2 h₂)
  have hΓ : narrowGamma p Q = ⊤ := by
    rw [eq_top_iff, ← hab, Subgroup.closure_le]
    rintro c (rfl | rfl)
    exacts [hs ha, hs hb]
  exact narrowGamma_eq_top_of_le_sylow hp eX
    (isPGroup_closure_of_normalForm hp.pos hx hy hzx hzy hcube) hΓ T

theorem normalForm_pow_eq_one {X : Type} [Group X] {p : ℕ} (hodd : Odd p) {x y : X}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (i j k : ℕ) : (x ^ i * y ^ j * ⁅x, y⁆ ^ k) ^ p = 1 := by
  set z := ⁅x, y⁆ with hzdef
  have hz : z ^ p = 1 := by
    rw [hzdef, CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]
  have hzn : ∀ m : ℕ, (z ^ m) ^ p = 1 := fun m => by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have hxy : x * y = y * x * z := by
    have e : x * y = z * (y * x) := by rw [hzdef, commutatorElement_def]; group
    rw [e, ((hzy.mul_right hzx).eq)]
  have hxiy : x ^ i * y = y * x ^ i * z ^ i :=
    CFSG.AGLEmbedding.classTwo_pow_mul y x z hxy hzx.eq i
  have hzi : Commute (z ^ i)⁻¹ y := (hzy.pow_left i).inv_left
  have hyxi : y * x ^ i = x ^ i * y * (z ^ i)⁻¹ := by
    rw [hxiy, mul_inv_cancel_right]
  have hyjxi : y ^ j * x ^ i = x ^ i * y ^ j * ((z ^ i)⁻¹) ^ j :=
    CFSG.AGLEmbedding.classTwo_pow_mul (x ^ i) y (z ^ i)⁻¹ hyxi hzi.eq j
  set d := ((z ^ i)⁻¹) ^ j with hd
  have hdp : d ^ p = 1 := by
    rw [hd, ← pow_mul, mul_comm, pow_mul, inv_pow, hzn, inv_one, one_pow]
  have hab : (x ^ i * y ^ j) ^ p = 1 := by
    rw [CFSG.AGLEmbedding.classTwo_mul_pow (x ^ i) (y ^ j) d hyjxi
      (((hzx.pow_left i).inv_left.pow_left j).pow_right i).eq ((hzi.pow_left j).pow_right j).eq,
      ← pow_mul, mul_comm, pow_mul, hx, one_pow, ← pow_mul, mul_comm,
      pow_mul, hy, one_pow, one_mul, one_mul]
    obtain ⟨m, rfl⟩ := hodd
    have hc : (2 * m + 1).choose 2 = (2 * m + 1) * m := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel]
      have e : (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) := by ring
      rw [e, Nat.mul_div_cancel_left _ two_pos]
    rw [hc, pow_mul, hdp, one_pow]
  have hck : Commute (x ^ i * y ^ j) (z ^ k) :=
    ((hzx.pow_left k).pow_right i |>.mul_right ((hzy.pow_left k).pow_right j)).symm
  rw [hck.mul_pow, hab, hzn, one_mul]

theorem narrowGamma_eq_top_of_permHPFacts {n p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {H : Subgroup (Equiv.Perm (Fin n))} {x y s₁ s₂ : Equiv.Perm (Fin n)}
    (hs : Subgroup.closure {s₁, s₂} = H) (hxH : x ∈ H) (hyH : y ∈ H) (hx : x ^ p = 1)
    (hy : y ^ p = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hzxk : ∀ k < p, ⁅x, y⁆ ≠ x ^ k) (hzyk : ∀ k < p, ⁅x, y⁆ ≠ y ^ k) (h₁ : s₁ * x = x * s₁)
    (h₂ : s₂ * y = y * s₂) {K : Type} [Group K] [Finite K] (eK : H ≃* K) (T : Sylow p K) :
    narrowGamma p (T : Subgroup K) = ⊤ := by
  have hs₁ : s₁ ∈ H := hs ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hs₂ : s₂ ∈ H := hs ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set x' : H := ⟨x, hxH⟩
  set y' : H := ⟨y, hyH⟩
  have hc : ((⁅x', y'⁆ : H) : Equiv.Perm (Fin n)) = ⁅x, y⁆ := by
    simp [x', y', commutatorElement_def]
  have hx' : x' ^ p = 1 := Subtype.ext (by simpa using hx)
  have hy' : y' ^ p = 1 := Subtype.ext (by simpa using hy)
  have hzx' : Commute ⁅x', y'⁆ x' := Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]; exact hzx.eq)
  have hzy' : Commute ⁅x', y'⁆ y' := Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]; exact hzy.eq)
  refine narrowGamma_eq_top_of_hpData hp eK (a := ⟨s₁, hs₁⟩) (b := ⟨s₂, hs₂⟩) (x := x') (y := y')
    (s₁ := ⟨s₁, hs₁⟩) (s₂ := ⟨s₂, hs₂⟩) (closure_pair_subtype_eq_top hs hs₁ hs₂) hx' hy' hzx' hzy'
    (fun i _ j _ k _ => normalForm_pow_eq_one hodd hx' hy' hzx' hzy' i j k)
    (fun k hk h => hzxk k hk (by rw [← hc, h]; simp [x']))
    (fun k hk h => hzyk k hk (by rw [← hc, h]; simp [y']))
    (Subtype.ext (by simpa using h₁)) (Subtype.ext (by simpa using h₂))
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) T

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
