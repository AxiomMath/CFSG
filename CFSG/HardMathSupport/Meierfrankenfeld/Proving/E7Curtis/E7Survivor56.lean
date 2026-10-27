module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7Reduction
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7BaseChange56
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7TorusGen
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.InvariantsBridge
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.InvariantsTransport
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinOffenderE7

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

@[expose] def conjRep {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (e : V ≃ₗ[k] W) :
    Representation k G W where
  toFun g := (e.toLinearMap ∘ₗ ρ g) ∘ₗ e.symm.toLinearMap
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp [map_mul]

theorem conjRep_apply {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (e : V ≃ₗ[k] W) (g : G) (w : W) :
    conjRep ρ e g w = e (ρ g (e.symm w)) := rfl

section Main


theorem e7_d_eq : e7Data.d = 56 := by decide +kernel

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e7_fix_bound (A : Subgroup ↥(adjointGroup .E7 K)) (hA : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A * Nat.card K ^ Module.finrank K ↥(Representation.invariants
      ((e7Rep56 K).comp A.subtype)) < Nat.card K ^ 56 := by
  have hinj : Function.Injective (e7Psi K) := (e7Equiv (K := K)).symm.injective
  set Am : Subgroup ↥(e7Data_valid.minGroup K) := A.map (e7Psi K) with hAm
  have hAmne : Am ≠ ⊥ := fun h => hA ((Subgroup.map_eq_bot_iff_of_injective A hinj).1 h)
  have hAmel : ∀ a ∈ Am, a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hel a ha, map_one]
  have hcard : Nat.card Am = Nat.card A := (Nat.card_congr (A.equivMapOfInjective _ hinj).toEquiv).symm
  have hfix : fixedSub (hV := e7Data_valid) (k := K) Am =
      Representation.invariants ((e7Rep56 K).comp A.subtype) := by
    ext v
    simp only [fixedSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Representation.mem_invariants]
    constructor
    · intro h a
      exact h (e7Psi K a) ⟨a, a.2, rfl⟩
    · rintro h _ ⟨a, ha, rfl⟩
      exact h ⟨a, ha⟩
  have key := (e7_56_no_offender K Am hAmne hAmel).1
  rw [hcard, hfix] at key
  have hpow : Nat.card ↥(Representation.invariants ((e7Rep56 K).comp A.subtype)) =
      Nat.card K ^ Module.finrank K ↥(Representation.invariants ((e7Rep56 K).comp A.subtype)) :=
    Module.natCard_eq_pow_finrank (K := K)
      (V := ↥(Representation.invariants ((e7Rep56 K).comp A.subtype)))
  rwa [hpow] at key

theorem e7_fix_base {k : Type} [Field k] (ι : K →+* k) (A : Subgroup ↥(adjointGroup .E7 K)) :
    Module.finrank k ↥(Representation.invariants ((e7Rep56k ι).comp A.subtype)) ≤
      Module.finrank K ↥(Representation.invariants ((e7Rep56 K).comp A.subtype)) := by
  classical
  have : Finite A := inferInstance
  let e1K : (Fin e7Data.d →₀ K) ≃ₗ[K] (Fin e7Data.d → K) :=
    Finsupp.linearEquivFunOnFinite K K (Fin e7Data.d)
  let e1 : (Fin e7Data.d →₀ k) ≃ₗ[k] (Fin e7Data.d → k) :=
    Finsupp.linearEquivFunOnFinite k k (Fin e7Data.d)
  let ρK : Representation K A (Fin e7Data.d →₀ K) := (e7Rep56 K).comp A.subtype
  let ρι : Representation k A (Fin e7Data.d →₀ k) := (e7Rep56k ι).comp A.subtype
  let τ : Representation K A (Fin e7Data.d → K) := conjRep ρK e1K
  let σ : Representation k A (Fin e7Data.d → k) := conjRep ρι e1
  let N : A → Matrix (Fin e7Data.d) (Fin e7Data.d) K := fun a => LinearMap.toMatrix' (τ a)
  have hN : ∀ a, σ a = Matrix.toLin' ((N a).map ι) := by
    intro a
    refine (Pi.basisFun k (Fin e7Data.d)).ext fun j => ?_
    simp only [Pi.basisFun_apply]
    ext i
    have h1 : e1.symm (Pi.single j 1 : Fin e7Data.d → k) = Finsupp.single j 1 := by
      ext i'; simp [e1, Finsupp.linearEquivFunOnFinite, Finsupp.single_apply]
    have h2 : e1K.symm (Pi.single j 1 : Fin e7Data.d → K) = Finsupp.single j 1 := by
      ext i'; simp [e1K, Finsupp.linearEquivFunOnFinite, Finsupp.single_apply]
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp only [σ, conjRep_apply, h1, ρι, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Matrix.col_apply, Matrix.map_apply, N, LinearMap.toMatrix'_apply, τ, ρK, h2]
    have h3 := baseChangeLin_single ι (e7Rep56 K (a : ↥(adjointGroup .E7 K))) j
    change e1 ((baseChangeLin ι (e7Rep56 K (a : ↥(adjointGroup .E7 K)))) (Finsupp.single j 1)) i = _
    rw [h3]
    rfl
  have step1 : Module.finrank k ↥(Representation.invariants ρι) =
      Module.finrank k ↥(Representation.invariants σ) :=
    finrank_invariants_of_linearEquiv ρι σ e1 fun g v => by simp [σ, conjRep_apply]
  have step2 := finrank_invariants_le_of_matrix ι σ N hN
  have step3 : (⨅ a : A, LinearMap.ker (Matrix.toLin' (N a) - 1)) = Representation.invariants τ := by
    rw [invariants_eq_iInf_ker τ]
    refine iInf_congr fun a => ?_
    rw [show Matrix.toLin' (N a) = τ a from Matrix.toLin'_toMatrix' (τ a)]
  have step4 : Module.finrank K ↥(Representation.invariants ρK) =
      Module.finrank K ↥(Representation.invariants τ) :=
    finrank_invariants_of_linearEquiv ρK τ e1K fun g v => by simp [τ, conjRep_apply]
  rw [step3] at step2
  exact step1.trans_le (step2.trans_eq step4.symm)

theorem e7SurvivorBound_n7 {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    E7SurvivorBound n7 K n := by
  classical
  intro k _ _ _ _ m ρ y χ b hρ hinj ht hb hχ A hA hel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    exact ⟨2 ^ t - 1, by omega⟩
  let ι : K →+* k := (algebraMap K k).comp (iterateFrobenius K 2 b)
  have hιz : ∀ z : K, ι z = algebraMap K k z ^ 2 ^ b := fun z => by
    simp [ι, iterateFrobenius_def, map_pow]
  have htm := e7Rep56k_isChevType ι
  have hd : ∀ (s : Fin Tag.E7.rank) (t : Kˣ), χ (dC .E7 K s t) = e7Chi56k ι (dC .E7 K s t) := by
    intro s t
    rw [e7Chi56k_dC]
    by_cases hs : s = e7n6
    · subst hs
      simp only [↓reduceIte, zpow_one]
      rw [hιz]
      exact hχ t
    · simp only [hs, ↓reduceIte, zpow_zero, Units.val_one, map_one]
      have hsJ : s ∈ Finset.univ.erase n7 := Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩
      exact ((ht.2.2.2 s).1 hsJ).1 t
  have htm' : IsChevType .E7 K 2 exists_weyl_neg_E7 (e7Rep56k ι) (mapVec ι e7Y56) χ
      (Finset.univ.erase n7) := by
    have hf := htm.1
    have hne := htm.2.1
    have hH := htm.2.2.1
    have hJ := htm.2.2.2
    refine ⟨hf, hne, fun h hh => ?_, fun i => ?_⟩
    · rw [hH h hh, ← chi_eq_of_dC_eq hodd ht htm hd h hh]
    · constructor
      · intro hi
        obtain ⟨h1, h2⟩ := (hJ i).1 hi
        exact ⟨fun t => (hd i t).trans (h1 t), h2⟩
      · rintro ⟨h1, h2⟩
        exact (hJ i).2 ⟨fun t => (hd i t).symm.trans (h1 t), h2⟩
  obtain ⟨β, hβ⟩ := iso_of_isChevType hρ (isSimpleRep_e7Rep56k ι) ht htm'
  have hm : m = 56 := by
    have h1 := β.finrank_eq
    rw [Module.finrank_fin_fun, Module.finrank_finsupp_self, Fintype.card_fin] at h1
    rw [h1, e7_d_eq]
  have hdim : Module.finrank k ↥(Representation.invariants (ρ.comp A.subtype)) =
      Module.finrank k ↥(Representation.invariants ((e7Rep56k ι).comp A.subtype)) :=
    finrank_invariants_of_linearEquiv _ _ β fun g v => hβ g v
  have h1 := e7_fix_base ι A
  have h2 := e7_fix_bound A hA hel
  have hpow : Nat.card K ^ 56 = Nat.card K ^ m := by rw [hm]
  refine lt_of_le_of_lt ?_ (h2.trans_eq hpow)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Finite.card_pos (hdim ▸ h1))

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
