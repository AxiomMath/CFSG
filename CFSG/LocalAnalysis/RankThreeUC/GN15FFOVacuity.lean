module

public import CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.L34Exclusion
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbedding CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X7Sec
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Meierfrankenfeld.L34Offender

open scoped MatrixGroups Matrix

private theorem exists_cube_root_of_dvd {F : Type} [Field F] [Fintype F] {f : ℕ}
    (hF : Fintype.card F = 2 ^ f) (h3 : 3 ∣ 2 ^ f - 1) : ∃ ω : Fˣ, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have hcard : Fintype.card Fˣ = 2 ^ f - 1 := by rw [Fintype.card_units, hF]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card 3 (by rw [hcard]; exact h3)
  refine ⟨ω, fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hω
    omega
  · rw [← hω]
    exact pow_orderOf_eq_one ω

namespace FFO

@[expose] def PSLNoOffenderAt (m f r : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ (L E : Subgroup (MulAut V)), X1.IsIrrOn L → Group.IsPerfect ↥L →
      ¬ r ∣ Nat.card (Subgroup.center ↥L) →
      StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL m 2 f →
      E ≤ Subgroup.normalizer (L : Set (MulAut V)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
      Nat.card E * Nat.card (fixV E) < Nat.card V

@[expose] def PSUNoOffenderAt (m f r : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ (L E : Subgroup (MulAut V)), X1.IsIrrOn L → Group.IsPerfect ↥L →
      ¬ r ∣ Nat.card (Subgroup.center ↥L) →
      StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU m 2 f →
      E ≤ Subgroup.normalizer (L : Set (MulAut V)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
      Nat.card E * Nat.card (fixV E) < Nat.card V

@[expose] def PSLNoOffender : Prop :=
  ∀ m f r : ℕ, 4 ≤ m → r.Prime → r ≠ 2 → r ∣ Nat.gcd m (2 ^ f - 1) → PSLNoOffenderAt m f r

@[expose] def PSUNoOffender : Prop :=
  ∀ m f r : ℕ, 4 ≤ m → r.Prime → r ≠ 2 → r ∣ Nat.gcd m (2 ^ f + 1) → PSUNoOffenderAt m f r

end FFO

theorem psl3Exclusion
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (L E : Subgroup (MulAut V)) (hirr : X1.IsIrrOn L) (hperf : Group.IsPerfect ↥L)
    (hc : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) {f : ℕ} (hf : 2 ≤ f) (h3 : 3 ∣ 2 ^ f - 1)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE1 : E ≠ ⊥)
    (hEel : IsElemAbelian2 E) (hEq : IsQuadratic E) :
    Nat.card E * Nat.card (fixV E) < Nat.card V := by
  classical
  by_contra hnot
  push Not at hnot
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    Family.odd_card_center_of_irreducible hV hirr.2
  obtain ⟨F, iF, iFin, φ, hFcard, hcov⟩ :=
    exists_cover_of_model hperf hodd (by omega : 1 ≤ f) hmodel
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card]; exact hFcard
  have hchar : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV
  have hntV : Nontrivial V := hirr.1
  have hntW : Nontrivial W := by
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have hker := B42SL3.repOf_ker θ hcov
  have hirrρ := B42SL3.repOf_irreducible θ hirr.2 hcov.surjective
  have hEel' : CFSG.IsElementaryAbelian 2 ↥(E.map (binPsi θ).toMonoidHom) :=
    (isElemAbelian2_iff_map θ E).1 hEel
  have hE1' : E.map (binPsi θ).toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective E (binPsi θ).injective]
    exact hE1
  have hoff : Nat.card W ≤ Nat.card ↥(E.map (binPsi θ).toMonoidHom) *
      Nat.card {u : W // ∀ a ∈ E.map (binPsi θ).toMonoidHom, a u = u} := by
    rw [B42SL3.card_fix_map, Subgroup.card_map_of_injective (binPsi θ).injective,
      ← natCard_eq θ]
    exact hnot
  obtain ⟨ψ, hψ, E', hE'⟩ := B42SL3.natural_of_offender (B42SL3.repOf θ φ) hker
    (E.map (binPsi θ).toMonoidHom)
    (B42SL3.intertwines_map θ hcov.surjective hEN) hf hF hirrρ hE1'
    (B42SL3.quad_map θ hEq) hoff
  obtain ⟨ω, hω1, hω3⟩ := exists_cube_root_of_dvd hF h3
  have hω3' : (ω : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω3]; exact Units.val_one
  let s : SL(3, F) := ⟨Matrix.scalar (Fin 3) (ω : F), by
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simpa [Finset.prod_const] using hω3'⟩
  have hs : s ∈ scalars 3 F := ⟨ω, hω3, rfl⟩
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    calc ((s ^ 3 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = (Matrix.scalar (Fin 3) (ω : F)) ^ 3 := by
          rw [Matrix.SpecialLinearGroup.coe_pow]
      _ = Matrix.scalar (Fin 3) ((ω : F) ^ 3) := (map_pow (Matrix.scalar (Fin 3)) (ω : F) 3).symm
      _ = 1 := by rw [hω3', map_one]
  have hφs : φ s = 1 := by
    have hmem : φ s ∈ Subgroup.center ↥L := by
      have : φ s ∈ (scalars 3 F).map φ := Subgroup.mem_map_of_mem φ hs
      rwa [hcov.map_scalars] at this
    have hφ3 : (φ s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
    have hd3 : orderOf (φ s) ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
    have hdZ : orderOf (φ s) ∣ Nat.card (Subgroup.center ↥L) := by
      have := orderOf_dvd_natCard (⟨φ s, hmem⟩ : Subgroup.center ↥L)
      simpa [Subgroup.orderOf_mk] using this
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h1 | h3'
    · exact orderOf_eq_one_iff.1 h1
    · exact absurd (h3' ▸ hdZ) hc
  have hρs : ∀ u, B42SL3.repOf θ φ s u = u := by
    intro u
    rw [B42SL3.repOf_apply, hφs]
    simp
  have hψs : ψ s = 1 := by
    have hall : ∀ x : Fin 3 → F, ((ψ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
      intro x
      obtain ⟨u, rfl⟩ := E'.surjective x
      rw [← hE', hρs]
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    have := congrFun (hall (Pi.single j 1)) i
    simp [Matrix.mulVec_single] at this
    rw [this]
    simp [Matrix.one_apply, Pi.single_apply]
  have hs1 : s = 1 := by
    have := hψ s
    rw [hψs, map_one] at this
    exact this.symm
  have hmat : ((s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by
    rw [hs1]; simp
  have hω : (ω : F) = 1 := by
    simpa [s] using hmat
  exact hω1 (Units.ext hω)


open scoped commutatorElement

theorem psl3NoOffenderAt
    {f : ℕ} (hf : 2 ≤ f) (h3 : 3 ∣ 2 ^ f - 1) :
    FFO.PSLNoOffenderAt 3 f 3 :=
  fun V _ _ hV L E hirr hperf hZ hmodel hEN hE1 hEel hEq =>
    psl3Exclusion V hV L E hirr hperf hZ hf h3 hmodel hEN hE1 hEel hEq

theorem psuThreeNoOffenderAt
    {f : ℕ} (hf : 2 ≤ f) (r : ℕ) : FFO.PSUNoOffenderAt 3 f r :=
  fun V _ _ hV L E hirr hperf _ hmodel hEN hE1 hEel _ =>
    CFSG.QuasithinUnique.Setup.X5.evenUnitaryThreeNoOffender f hf V hV hirr.1 L E hperf hirr.2 hmodel
      hE1 hEel hEN

private theorem card_center_range_dvd {L H : Type} [Group L] [Group H] (hLq : CFSG.IsQuasisimple L)
    (φ : L →* H) (hφ0 : φ.range ≠ ⊥) :
    Nat.card (Subgroup.center ↥φ.range) ∣ Nat.card (Subgroup.center L) := by
  have hker : φ.ker ≤ Subgroup.center L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq φ.normal_ker with h | h
    · exfalso
      apply hφ0
      rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff]
      exact h
    · exact h
  obtain ⟨-, -, hmap⟩ := CFSG.LocalCores.quasisimple_central_quotient hLq φ.ker hker
  let e₁ : L ⧸ φ.ker ≃* φ.range := QuotientGroup.quotientKerEquivRange φ
  have h1 : (Subgroup.center (L ⧸ φ.ker)).map e₁.toMonoidHom = Subgroup.center φ.range :=
    CFSG.QuasithinUnique.Setup.X5.map_center_mulEquiv e₁
  rw [hmap, Subgroup.map_map] at h1
  rw [← h1]
  exact Subgroup.card_map_dvd (Subgroup.center L) _

theorem commutator_eq_bot_of_psl_noOffenderAt {m f r : ℕ} (hvac : FFO.PSLNoOffenderAt m f r)
    (G : Type) [Group G] [Finite G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ)
    (hO2 : CFSG.pCore 2 G = ⊥) (A : Subgroup G) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hAb : CFSG.RankThree.FFModules.IsBestOffender ρ A) (L : Subgroup G)
    (hL : CFSG.Open.IsComponentOf L ⊤) (hZ : ¬ r ∣ Nat.card (Subgroup.center ↥L))
    (hmodel : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL m 2 f) :
    ⁅L, A⁆ = ⊥ := by
  by_contra hLA
  obtain ⟨V, _, _, φ, E, hV, hφ0, hirr, hEN, hE0, hEel, hEq, hoff⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.componentSectionProp G W ρ hρ hO2 A hAel hAb
      L hL hLA
  have hLq : CFSG.IsQuasisimple ↥L := ((CFSG.isComponent_iff_open L).mpr hL).1
  obtain ⟨hq0, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hLq φ hφ0
  have hc0 : ¬ r ∣ Nat.card (Subgroup.center ↥φ.range) := fun h =>
    hZ (h.trans (card_center_range_dvd hLq φ hφ0))
  have hmodel0 := CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmodel
  have hnt : Nontrivial V := hirr.1
  have := hvac V hV φ.range E hirr hq0.1 hc0 hmodel0 hEN hE0 hEel hEq
  omega

theorem commutator_eq_bot_of_psu_noOffenderAt {m f r : ℕ} (hvac : FFO.PSUNoOffenderAt m f r)
    (G : Type) [Group G] [Finite G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ)
    (hO2 : CFSG.pCore 2 G = ⊥) (A : Subgroup G) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hAb : CFSG.RankThree.FFModules.IsBestOffender ρ A) (L : Subgroup G)
    (hL : CFSG.Open.IsComponentOf L ⊤) (hZ : ¬ r ∣ Nat.card (Subgroup.center ↥L))
    (hmodel : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU m 2 f) :
    ⁅L, A⁆ = ⊥ := by
  by_contra hLA
  obtain ⟨V, _, _, φ, E, hV, hφ0, hirr, hEN, hE0, hEel, hEq, hoff⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.componentSectionProp G W ρ hρ hO2 A hAel hAb
      L hL hLA
  have hLq : CFSG.IsQuasisimple ↥L := ((CFSG.isComponent_iff_open L).mpr hL).1
  obtain ⟨hq0, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hLq φ hφ0
  have hc0 : ¬ r ∣ Nat.card (Subgroup.center ↥φ.range) := fun h =>
    hZ (h.trans (card_center_range_dvd hLq φ hφ0))
  have hmodel0 := CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmodel
  have hnt : Nontrivial V := hirr.1
  have := hvac V hV φ.range E hirr hq0.1 hc0 hmodel0 hEN hE0 hEel hEq
  omega

theorem commutator_eq_bot_of_psl_three
    (G : Type) [Group G] [Finite G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ)
    (hO2 : CFSG.pCore 2 G = ⊥) (A : Subgroup G) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hAb : CFSG.RankThree.FFModules.IsBestOffender ρ A) (L : Subgroup G)
    (hL : CFSG.Open.IsComponentOf L ⊤) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) {f : ℕ}
    (hf : 2 ≤ f) (h3 : 3 ∣ 2 ^ f - 1)
    (hmodel : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) :
    ⁅L, A⁆ = ⊥ :=
  commutator_eq_bot_of_psl_noOffenderAt (psl3NoOffenderAt hf h3) G W ρ hρ hO2 A hAel hAb L hL hZ hmodel

theorem commutator_eq_bot_of_psu_three
    (G : Type) [Group G] [Finite G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ)
    (hO2 : CFSG.pCore 2 G = ⊥) (A : Subgroup G) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hAb : CFSG.RankThree.FFModules.IsBestOffender ρ A) (L : Subgroup G)
    (hL : CFSG.Open.IsComponentOf L ⊤) {f : ℕ}
    (hmodel : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 f) :
    ⁅L, A⁆ = ⊥ := by
  have hf : 2 ≤ f := by
    obtain ⟨-, h1, -, h3⟩ := hmodel.1
    by_contra hlt
    have : f = 1 := by omega
    subst this
    exact h3 (by norm_num)
  exact commutator_eq_bot_of_psu_noOffenderAt (psuThreeNoOffenderAt hf (Nat.card (Subgroup.center ↥L) + 1))
    G W ρ hρ hO2 A hAel hAb L hL
    (Nat.not_dvd_of_pos_of_lt Nat.card_pos (Nat.lt_succ_self _)) hmodel

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
