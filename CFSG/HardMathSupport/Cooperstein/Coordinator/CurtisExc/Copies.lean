module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.WeylConj
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ChevIndep

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Copies

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

@[expose] def repEquiv {G : Type*} [Group G] (ρ : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (ρ g) (ρ g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem copies_finrank_orbit [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} {m : ℕ}
    (u : Fin m → WeylGroup τ)
    (hu : ∀ i, u i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) :
    m * Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) ≤ Module.finrank k V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := ρ.comp (rankOne τ K s) with hσ
  set D := chevDatum τ K 2 hw with hD
  obtain ⟨hxN, hyN⟩ := Us_normalized (hw := hw) (K := K) s
  set v : Fin m → V := fun i => ρ (nWC τ K (u i)) y with hv
  have hcomm : ∀ i (g' : SL(2, K)) (w : V), σ g' (ρ (nWC τ K (u i)) w) =
      ρ (nWC τ K (u i)) (σ g' w) := by
    intro i g' w
    show ρ (rankOne τ K s g') (ρ (nWC τ K (u i)) w) = ρ (nWC τ K (u i)) (ρ (rankOne τ K s g') w)
    rw [act_mul, act_mul, ← nWC_commute_rankOne hw (u i) s (hu i) g']
  set Fix : Fin m → Submodule k V := fun i =>
    (fixSub ρ (D.Us s)).map (ρ (nWC τ K (u i))) with hFix
  have hyFix : y ∈ fixSub ρ (D.Us s) := fun q hq => ht.1 q (D.Us_le s hq)
  have hyu : ∀ c : K, σ (uElt c) y = y := by
    intro c
    show ρ (rankOne τ K s (uElt c)) y = y
    rw [rankOne_u]
    exact ht.1 _ (D.X_le s (xC_mem_X s c))
  have hmap_inj : ∀ i, Function.Injective (ρ (nWC τ K (u i))) :=
    fun i => (repEquiv ρ (nWC τ K (u i))).injective
  have hres := finrank_iSup_orbitSpan σ v Fix
    (fun i => Submodule.mem_map_of_mem hyFix)
    (by
      rintro i g' _ ⟨f, hf, rfl⟩
      rw [hcomm]
      exact Submodule.mem_map_of_mem (fixSub_stable_rankOne ρ s (D.Us s) hxN hyN g' hf))
    (by
      rintro i _ ⟨f0, hf0, rfl⟩ hfu
      have h1 : ∀ c : K, ρ (xC τ K s c) f0 = f0 := by
        intro c
        have := hfu c
        rw [hcomm] at this
        have h2 : σ (uElt c) f0 = f0 := hmap_inj i this
        have h3 : ρ (rankOne τ K s (uElt c)) f0 = f0 := h2
        rw [rankOne_u] at h3
        exact h3
      obtain ⟨c, hc⟩ := fix_of_highest hρ ht s hf0 h1
      exact ⟨c, by rw [hc, map_smul]⟩)
    (fun i c => by rw [hcomm, hyu c])
    Finset.univ (hli.comp (fun x : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) => (x : Fin m))
      Subtype.val_injective)
  obtain ⟨hdim, -, -⟩ := hres
  have hN : ∀ i, Module.finrank k (orbitSpan σ (v i)) = Module.finrank k (orbitSpan σ y) := by
    intro i
    have : orbitSpan σ (v i) = (orbitSpan σ y).map (ρ (nWC τ K (u i))) := by
      rw [orbitSpan, orbitSpan, Submodule.map_span, ← Set.range_comp]
      congr 1
      ext w
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨g', rfl⟩
        exact ⟨g', (hcomm i g' y).symm⟩
      · rintro ⟨g', rfl⟩
        exact ⟨g', hcomm i g' y⟩
    rw [this]
    exact (repEquiv ρ (nWC τ K (u i))).finrank_map_eq _
  calc m * Module.finrank k (orbitSpan σ y) = ∑ i : Fin m, Module.finrank k (orbitSpan σ (v i)) := by
        simp [hN]
    _ = Module.finrank k (⨆ i ∈ (Finset.univ : Finset (Fin m)), orbitSpan σ (v i) : Submodule k V) :=
        hdim.symm
    _ ≤ Module.finrank k V := Submodule.finrank_le _

theorem copies_finrank [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g)
    (hgn : g ∣ n) (hper : ∀ z : Kˣ, χ (dC τ K s z) ^ (2 ^ g) = χ (dC τ K s z)) {m : ℕ}
    (u : Fin m → WeylGroup τ)
    (hu : ∀ i, u i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) :
    m * 2 ^ (n / g) ≤ Module.finrank k V :=
  calc m * 2 ^ (n / g) ≤ m * Module.finrank k (orbitSpan (ρ.comp (rankOne τ K s)) y) :=
        Nat.mul_le_mul_left _ (two_pow_le_finrank_orbitSpan hn hK hρ ht hs hg hgn hper)
    _ ≤ Module.finrank k V := copies_finrank_orbit hρ ht u hu hli

theorem copies_linearIndependent [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} {m : ℕ}
    (u : Fin m → WeylGroup τ)
    (hu : ∀ i, u i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (nWC τ K (u i)) y)) {e : V}
    (he : e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y) (he0 : e ≠ 0) :
    LinearIndependent k (fun i => ρ (nWC τ K (u i)) e) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := ρ.comp (rankOne τ K s) with hσ
  set D := chevDatum τ K 2 hw with hD
  obtain ⟨hxN, hyN⟩ := Us_normalized (hw := hw) (K := K) s
  set v : Fin m → V := fun i => ρ (nWC τ K (u i)) y with hv
  have hcomm : ∀ i (g' : SL(2, K)) (w : V), σ g' (ρ (nWC τ K (u i)) w) =
      ρ (nWC τ K (u i)) (σ g' w) := by
    intro i g' w
    show ρ (rankOne τ K s g') (ρ (nWC τ K (u i)) w) = ρ (nWC τ K (u i)) (ρ (rankOne τ K s g') w)
    rw [act_mul, act_mul, ← nWC_commute_rankOne hw (u i) s (hu i) g']
  set Fix : Fin m → Submodule k V := fun i =>
    (fixSub ρ (D.Us s)).map (ρ (nWC τ K (u i))) with hFix
  have hyFix : y ∈ fixSub ρ (D.Us s) := fun q hq => ht.1 q (D.Us_le s hq)
  have hyu : ∀ c : K, σ (uElt c) y = y := by
    intro c
    show ρ (rankOne τ K s (uElt c)) y = y
    rw [rankOne_u]
    exact ht.1 _ (D.X_le s (xC_mem_X s c))
  have hmap_inj : ∀ i, Function.Injective (ρ (nWC τ K (u i))) :=
    fun i => (repEquiv ρ (nWC τ K (u i))).injective
  have hres := finrank_iSup_orbitSpan σ v Fix
    (fun i => Submodule.mem_map_of_mem hyFix)
    (by
      rintro i g' _ ⟨f, hf, rfl⟩
      rw [hcomm]
      exact Submodule.mem_map_of_mem (fixSub_stable_rankOne ρ s (D.Us s) hxN hyN g' hf))
    (by
      rintro i _ ⟨f0, hf0, rfl⟩ hfu
      have h1 : ∀ c : K, ρ (xC τ K s c) f0 = f0 := by
        intro c
        have := hfu c
        rw [hcomm] at this
        have h2 : σ (uElt c) f0 = f0 := hmap_inj i this
        have h3 : ρ (rankOne τ K s (uElt c)) f0 = f0 := h2
        rw [rankOne_u] at h3
        exact h3
      obtain ⟨c, hc⟩ := fix_of_highest hρ ht s hf0 h1
      exact ⟨c, by rw [hc, map_smul]⟩)
    (fun i c => by rw [hcomm, hyu c])
    Finset.univ (hli.comp (fun x : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) => (x : Fin m))
      Subtype.val_injective)
  obtain ⟨-, -, hsup⟩ := hres
  have hind : iSupIndep (fun i : Fin m => orbitSpan σ (v i)) :=
    Finset.SupIndep.iSupIndep_of_univ hsup
  refine hind.linearIndependent _ (fun i => ?_) (fun i h0 => he0 (hmap_inj i (by rw [h0, map_zero])))
  have : orbitSpan σ (v i) = (orbitSpan σ y).map (ρ (nWC τ K (u i))) := by
    rw [orbitSpan, orbitSpan, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext w
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g', (hcomm i g' y).symm⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g', hcomm i g' y⟩
  rw [this]
  exact Submodule.mem_map_of_mem he

theorem linearIndependent_translates_of_isChevType {ρ : Representation k (adjointGroup τ K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hs : s ∉ J) {v₀ : Fin τ.rank → ℤ}
    (hv : ∀ j, j ≠ s → reflect τ j v₀ = v₀) {m : ℕ} (w : Fin m → WeylGroup τ)
    (hinj : ∀ i j, i ≠ j → w i • v₀ ≠ w j • v₀) :
    LinearIndependent k (fun i => ρ (nWC τ K (w i)) y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  refine linearIndependent_translates hρ hμ w fun i j hij ω hω hωe =>
    ⟨s, ?_, mu_eq_dScalar_of_notMem ht hμ hs⟩
  refine exists_letter_of_smul_ne hv fun h => hinj i j hij ?_
  rw [hωe, mul_smul] at h
  have := congrArg (fun z => w i • z) h
  simpa [smul_smul] using this.symm

end Copies

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
