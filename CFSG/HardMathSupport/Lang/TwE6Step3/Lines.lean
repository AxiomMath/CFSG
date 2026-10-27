module

public import CFSG.HardMathSupport.Lang.TwE6Step3.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.OrderSix
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
open scoped Matrix

set_option linter.unusedSectionVars false

theorem mem_hyperClosure_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {p : ℕ}
    {E : Subgroup G} {k : G} (h : e k ∈ hyperClosure p ⊤ (E.map e.toMonoidHom)) :
    k ∈ hyperClosure p ⊤ E := by
  set S : Set G := {k : G | k ∈ (⊤ : Subgroup G) ∧ ∃ F : Subgroup G, F ≤ E ∧ F.relIndex E = p ∧
    ∀ f ∈ F, f * k = k * f} with hS
  have hle : hyperClosure p ⊤ (E.map e.toMonoidHom) ≤ (Subgroup.closure S).map e.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro k' ⟨-, F', hF'E, hF'r, hF'c⟩
    refine ⟨e.symm k', Subgroup.subset_closure ⟨Subgroup.mem_top _, F'.map e.symm.toMonoidHom, ?_,
      ?_, ?_⟩, by simp⟩
    · intro f hf
      obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hF'E hf')
      simpa using hx
    · have := Subgroup.relIndex_map_map_of_injective (f := e.symm.toMonoidHom) F'
        (E.map e.toMonoidHom) e.symm.injective
      rw [Subgroup.map_map] at this
      have h2 : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id G := by
        ext x; simp
      rw [h2, Subgroup.map_id] at this
      rw [this]
      exact hF'r
    · intro f hf
      obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
      have := hF'c f' hf'
      apply e.injective
      simpa using this
  obtain ⟨k', hk', hkk'⟩ := hle h
  have hk : k' = k := e.injective hkk'
  rw [← hk]
  exact hk'


theorem psiT_one {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]
    (g0 : ModGL Tag.E6 L) (c : twistedE6RootGroup K σ) : psiT g0 c 1 = 1 := by
  simp [psiT]

theorem psiT_pow {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]
    (g0 : ModGL Tag.E6 L) (c x : twistedE6RootGroup K σ) (n : ℕ) :
    psiT g0 c (x ^ n) = psiT g0 c x ^ n := by
  induction n with
  | zero => simp [psiT_one]
  | succ n ih => rw [pow_succ, psiT_mul, ih, pow_succ]


theorem twE6SixLines_of_types (h2 : LinesOfType IsA2A2Kernel) (h4 : LinesOfType IsD4Kernel) :
    TwE6SixLines := by
  intro q hv p hp hp3 hpq hord E hE hEc y hy hy1 k hk
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  obtain ⟨hdvd, -⟩ := CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_sub_add_one_of_orderOf_eq_six
    hp hord
  have hx0 : ((q.card : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hord
    exact absurd hord (by norm_num)
  have h6 : 6 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    obtain ⟨m, hm⟩ := h6
    omega
  have hp3' : 3 < p := by omega
  have hp5 : 5 < p := by omega
  have hq1 : 1 ≤ q.card := by rw [hcard]; exact Nat.one_le_pow _ _ q.prime_p.pos
  have hpq' : (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 - ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
    rw [← hcard]
    have hle : q.card ≤ q.card ^ 2 := Nat.le_self_pow (by norm_num) _
    have : ((q.card ^ 2 - q.card + 1 : ℕ) : ℤ) = ((q.card : ℕ) : ℤ) ^ 2 - (q.card : ℤ) + 1 := by
      push_cast [hle]
      ring
    rw [← this]
    exact Int.natCast_dvd_natCast.2 hdvd
  let L := AlgebraicClosure K
  have : CharP L q.p := charP_of_injective_algebraMap (algebraMap K L).injective q.p
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := tw6_frame K hf hK σ hσ hp hp3' hpq' L
  set E' := E.map e.toMonoidHom with hE'def
  have hE' : IsElemAbelian p E' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hE'c : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective e.injective, hEc]
  have hE'p : IsPGroup p E' := IsPGroup.of_card hE'c
  obtain ⟨c, hc⟩ := hconj E' hE'p
  have hT : ∀ x ∈ E', psiT g0 c x ∈
      twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L q.p q.exponent)) := hc
  have hy' : e y ∈ E' := ⟨y, hy, rfl⟩
  have hy'1 : e y ≠ 1 := by
    intro h
    exact hy1 (e.injective (h.trans e.map_one.symm))
  have hk' : e k * e y = e y * e k := by rw [← map_mul, hk, map_mul]
  have hFr : ∀ c, (iterateFrobenius L q.p q.exponent) c = c ^ (q.p ^ q.exponent) :=
    fun c => iterateFrobenius_def q.p q.exponent c
  have hq0 : ((q.p ^ q.exponent : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow q.exponent_pos.ne']
  obtain ⟨-, ⟨ζ, hζ⟩, -⟩ := tw6_prime_setup (L := L) hq0 hp hpq'
  have : NeZero p := ⟨hp.ne_zero⟩
  have hxp : psiT g0 c (e y) ^ p = 1 := by
    rw [← psiT_pow, hE'.2 _ hy', psiT_one]
  have hx1 : psiT g0 c (e y) ≠ 1 := by
    intro h
    exact hy'1 (psiT_injective g0 c (h.trans (psiT_one g0 c).symm))
  obtain ⟨z, -, hz, hker, hz0⟩ := exists_column_of_tw6Torus hFr hζ (hT _ hy') hxp
  rcases phi3_kernel_types hp5 z (hz0 hx1) _ hz with h0 | hA2 | hA2A2 | hD4
  · refine mem_hyperClosure_of_mulEquiv e ?_
    exact le_hyperClosure_of_kernel_empty K hf hK σ hσ hp3' hpq' L hg0C hg0 hperf hE' hE'c c hT
      hy' hy'1 (hker.trans h0) hk'
  · refine mem_hyperClosure_of_mulEquiv e ?_
    exact le_hyperClosure_of_kernel_A2 K hf hK σ hσ hp3' hpq' L hg0C hg0 hperf hE' hE'c c hT
      hy' hy'1 (by rw [hker]; exact hA2) hk'
  · refine mem_hyperClosure_of_mulEquiv e ?_
    exact h2 K hf hK σ hσ hp3' hpq' L g0 hg0C hg0 hperf E' hE' hE'c c hT (e y) hy' hy'1
      (by rw [hker]; exact hA2A2) (e k) hk'
  · refine mem_hyperClosure_of_mulEquiv e ?_
    exact h4 K hf hK σ hσ hp3' hpq' L g0 hg0C hg0 hperf E' hE' hE'c c hT (e y) hy' hy'1
      (by rw [hker]; exact hD4) (e k) hk'

end CFSG.HardMathSupport.Lang.TwE6Step3
