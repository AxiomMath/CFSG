module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcE
public import CFSG.RankThree.PartOne.S11d.FixedFactsE6TwDescent
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwCat
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti
open CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.Sec66T
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem apply_zpow_eq_of_apply_eq {G : Type*} [Group G] (f : MulAut G) {z : G} (h : f z = z)
    (s : ℤ) : (f ^ s) z = z := by
  have hz : f ∈ MulAction.stabilizer (MulAut G) z := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  exact (MulAction.mem_stabilizer_iff.1 (Subgroup.zpow_mem _ hz s))

section


theorem fixesPair_twistedE6 {L : Type} [Group L] [Finite L] {f p : ℕ} (hf : 1 ≤ f)
    (hCEM : ChevalleyExceptionalModel L .twistedE6 2 f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk1 : ¬ RankLE1 p L) (hrk2 : RankLE2 p L) {α : MulAut L} (hαp : α ^ p = 1)
    (hα : α ∉ inner L) : FixesIndepPair p α := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K₁, hKf₁, hKfin₁, σ₁, hKcard₁, hσ₁, ⟨eK⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hCEM
  have hK₁2 : Nat.card K₁ = 2 ^ (2 * f) := by rw [hKcard₁, ← pow_mul, mul_comm]
  haveI : Finite (graphFixedRootGroup TwistTag.E6 K₁ σ₁.toRingHom) := Finite.of_equiv L eK.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp eK hαp hα
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K₁ hKcard₁ σ₁ hσ₁
  obtain ⟨-, hpf, -, -⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial
      Nat.prime_two hf K₁ hK₁2 σ₁ hσ₁ Θ hΘ hp (by omega) ⊤ le_top
      ⟨MulAut.congr eK α, Subgroup.mem_top _⟩ hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f₀, rfl⟩ := hpf
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · subst h; omega
    · exact h
  have hM : LieModel L .twistedE6 0 2 (p * f₀) := lieModel_twistedE6_iff.mpr ⟨rfl, hCEM⟩
  obtain ⟨K, hKf, hKfin, σ, κ, ε, σ₀, φ, hKcard, hσ, hκ, hε, hσ₀, ⟨s, hs, hcongr⟩, -, hcanon, -,
    ⟨eJ⟩, -⟩ := twistedE6_descent hp hp5 hf₀ hM α hαp hα
  obtain ⟨-, hK₀card, hJC, -, hcomm, -⟩ := hcanon
  haveI : Finite (fixSubfield κ) := Subtype.finite
  have hK2 : Nat.card K = (2 ^ (f₀ * p)) ^ 2 := by rw [hKcard, ← pow_mul]; ring_nf
  have hpK : ¬ p ∣ 2 ^ (f₀ * p) := by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hrk1C : ¬ RankLE1 p (twistedE6RootGroup K σ) := fun h => hrk1 (RankLE1.of_mulEquiv φ.symm h)
  have hrk2C : RankLE2 p (twistedE6RootGroup K σ) := RankLE2.of_mulEquiv φ hrk2
  have hc1 : 2 ≤ degCountTw (orderOf (((2 ^ (f₀ * p) : ℕ)) : ZMod p)) := by
    by_contra h
    exact hrk1C (rankLE1_twistedE6 Nat.prime_two (Nat.mul_pos hf₀ hp.pos) K hK2 σ hσ hp hpK
      (by omega))
  have hc3 : degCountTw (orderOf (((2 ^ (f₀ * p) : ℕ)) : ZMod p)) ≤ 2 := by
    by_contra h
    exact not_rankLE2_twistedE6 Nat.prime_two (Nat.mul_pos hf₀ hp.pos) K hK2 σ hσ hp (by omega)
      hpK (by omega) hrk2C
  have he : orderOf (((2 ^ f₀ : ℕ)) : ZMod p) = orderOf (((2 ^ (f₀ * p) : ℕ)) : ZMod p) := by
    rw [pow_mul]
    push_cast
    rw [ZMod.pow_card]
  have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ 2 ^ f₀ := fun c =>
    Subtype.ext (by rw [hσ₀ c]; rfl)
  have hK₀ : Nat.card (fixSubfield κ) = (2 ^ f₀) ^ 2 := by rw [hK₀card, ← pow_mul, mul_comm]
  have hpair₀ : HasIndepPair p (twistedE6RootGroup (fixSubfield κ) σ₀) := by
    have h34 := degCountTw_eq_two (by omega : degCountTw (orderOf (((2 ^ (f₀ * p) : ℕ)) :
      ZMod p)) = 2)
    rcases h34 with h3 | h4
    · obtain ⟨E, hE, hEc⟩ := (sylowTorus_twistedE6_three Nat.prime_two hf₀ (fixSubfield κ) hK₀ σ₀
        hσ₀' hp (he.trans h3)).exists_elemAbelian
      exact hasIndepPair_of_elemAbelian_sq hp hE hEc
    · obtain ⟨E, hE, hEc⟩ := (sylowTorus_twistedE6_four Nat.prime_two hf₀ (fixSubfield κ) hK₀ σ₀
        hσ₀' hp (he.trans h4)).exists_elemAbelian
      exact hasIndepPair_of_elemAbelian_sq hp hE hEc
  obtain ⟨y₁, y₂, hc, h1, h2, hi⟩ := HasIndepPair.of_mulEquiv eJ.symm hpair₀
  let jC : ↥(CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subgroup.inclusion hJC
  have hjC : Function.Injective jC := Subgroup.inclusion_injective hJC
  have hfixε : ∀ y, fieldActor σ ε (jC y) = jC y := by
    intro y
    have hy : jC y ∈ ⁅MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
        MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))⁆ := by
      rw [hcomm, Subgroup.mem_subgroupOf]
      exact y.2
    exact Subgroup.commutator_le_self _ hy
  have hfixα : ∀ y, MulAut.congr φ α (jC y) = jC y := fun y => by
    rw [hcongr]
    exact apply_zpow_eq_of_apply_eq _ (hfixε y) s
  have hfp : FixesIndepPair p (MulAut.congr φ α) := by
    refine ⟨jC y₁, jC y₂, hc.map jC, ?_, ?_, fun i j hij => ?_, hfixα y₁, hfixα y₂⟩
    · rw [← map_pow, h1, map_one]
    · rw [← map_pow, h2, map_one]
    · rw [← map_zpow, ← map_zpow, ← map_mul] at hij
      exact hi i j (hjC (hij.trans (map_one jC).symm))
  exact FixesIndepPair.of_mulEquiv φ hfp

theorem chevTwoOuterFixesPair_twistedE6 : ChevTwoOuterFixesPair LieIndexTwistedE6 := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 := hchar
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_twistedE6_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      have hCEM0 := CFSG.HardMathSupport.Timmesfeld.CrossChar.chevalleyModel_cat_twistedE6 hv
      rw [hq2] at hCEM0
      have hCEM : ChevalleyExceptionalModel L .twistedE6 2 q.exponent := by
        obtain ⟨hadm, K, hF', hfin, hK, σ, hσ, ⟨φ⟩⟩ := hCEM0
        exact ⟨hadm, K, hF', hfin, hK, σ, hσ, ⟨e.trans φ⟩⟩
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk (MulEquiv.refl L)
      exact fixesPair_twistedE6 q.exponent_pos hCEM hp hp5 (not_rankLE1_of_sq hp hE hEc) hrk2 hαp
        hα
  | A _ _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | B _ _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | C _ _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | D _ _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | E6 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | E7 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | E8 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | F4 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | G2 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | suzuki _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | reeG2 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | reeF4 _ => exact absurd hF (by simp [LieIndexTwistedE6])
  | tits => exact absurd hF (by simp [LieIndexTwistedE6])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
