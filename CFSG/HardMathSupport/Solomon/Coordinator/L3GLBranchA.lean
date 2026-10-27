module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLBranchB
public import CFSG.HardMathSupport.Solomon.Proving.ExtremalCentre
public import CFSG.RankThree.PartTwo.KFacts.L34Models

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts.L34

theorem l3gl_cube_of_card_nine {k : Type} [Field k] (hk : Nat.card k = 4)
    {E : Subgroup (projectiveSL 3 k)} (hE9 : Nat.card E = 9)
    (x : Matrix.SpecialLinearGroup (Fin 3) k) (hx : proj 3 k x ∈ E) : x ^ 3 = 1 := by
  obtain ⟨-, -, hexp⟩ := isHeisThree_comap_proj hk hE9
  have hx' : x ∈ E.comap (proj 3 k) := hx
  have h1 := Monoid.pow_exponent_eq_one (⟨x, hx'⟩ : ↥(E.comap (proj 3 k)))
  rw [hexp] at h1
  exact congrArg Subtype.val h1

variable {G : Type} [Group G] [Finite G]

theorem l3gl_hasOrderThreeLift_branchA (h31 : Lemma31) (h59 : Lemma59) {m : ℕ}
    (hS : GLStanding G m 3) (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hLC : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) (hΛ : L ≤ lambdaOf 3 B b)
    (hψ : ¬ L ≤ psiStarGroup 3 B) (hty : IsExtremalType (barOf 3 L)) {y : G} (hy : y ∈ L)
    (hyB : y ∈ B) (hy1 : y ≠ 1) :
    HasOrderThreeLift (barOf 3 L) (QuotientGroup.mk (⟨y, hy⟩ : ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBel : IsElemAbelian 3 B := hB.1.1
  obtain ⟨-, -, hL34, hrel, hinn⟩ :=
    lemma31iii_of_alternative_a h31 h59 hS hC hB hb hb1 hLC hΛ hψ
  have hZ : Subgroup.center (barOf 3 L) = ⊥ := Proving.center_eq_bot_of_isExtremalType hty
  have hL34' : IsLThreeFour (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) :=
    isLThreeFour_barOf_center hLC hL34
  have hL34'' : IsLThreeFour (barOf 3 L) :=
    UniquenessMaximal.IsLThreeFour.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hL34'
  obtain ⟨K, _, _, hK4, ⟨θ₀⟩⟩ := hL34''
  let θ : barOf 3 L ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 3 K) := θ₀
  have hBtInn := autBar_le_innerAut hLC hinn
  have hBt9 := card_autBar_eq_of_relIndex hLC hrel
  set P0 : Subgroup (barOf 3 L) :=
    (autBar 3 B L).comap (MulAut.conj : barOf 3 L →* MulAut (barOf 3 L)) with hP0def
  have hP0 : Nat.card P0 = 9 := by
    rw [hP0def, card_comap_conj _ hBtInn, hBt9, hZ, Subgroup.card_bot, one_mul]
  set e : barOf 3 L ≃* projectiveSL 3 K :=
    θ.trans (psiPSL K) with he
  set E : Subgroup (projectiveSL 3 K) := P0.map e.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective e.injective, hP0]
  have hyP0 : (QuotientGroup.mk (⟨y, hy⟩ : ↥L) : barOf 3 L) ∈ P0 := l3gl_conj_mem_autBar hy hyB
  obtain ⟨s, hs⟩ := proj_surjective 3 K (e (QuotientGroup.mk (⟨y, hy⟩ : ↥L)))
  have hsE : proj 3 K s ∈ E := by
    rw [hs]
    exact Subgroup.mem_map_of_mem _ hyP0
  have hs3 := l3gl_cube_of_card_nine hK4 hE9 s hsE
  have hθ : θ (QuotientGroup.mk (⟨y, hy⟩ : ↥L)) =
      QuotientGroup.mk (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K s) := by
    apply (psiPSL K).injective
    rw [psiPSL_mk, hs]
    rfl
  have hŷ3 : (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K s) ^ 3 = 1 := by
    rw [← map_pow, hs3, map_one]
  have hŷ1 : CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K s ≠ 1 := by
    intro h1
    apply l3gl_mk_ne_one hBel hy hyB hy1
    apply θ.injective
    rw [hθ, h1, QuotientGroup.mk_one, map_one]
  refine Or.inl ⟨K, inferInstance, inferInstance, θ, by rw [hK4], _, orderOf_eq_prime hŷ3 hŷ1, hθ⟩

end CFSG.HardMathSupport.Solomon.Coordinator
