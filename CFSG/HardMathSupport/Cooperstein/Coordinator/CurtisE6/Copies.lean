module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.StrBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Indep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem mu_eq_dScalar_of_notMem {ρ : Representation k ↥(e6Data_valid.minGroup K) V} {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {μ : N6 → k}
    (hμ : (e6CoverData K).datum.IsCurtisType ρ y χ μ) {s : N6} (hs : s ∉ J) :
    μ s = (e6CoverData K).datum.dScalar χ s := by
  have : Fintype Kˣ := Fintype.ofFinite _
  exact IsCoverType.mu_eq_dScalar e6Cover_hodd ht hμ hs

theorem foldr_reflect_eq_of_fix {v : N6 → ℤ} {l : List N6}
    (h : ∀ j ∈ l, reflect Tag.E6 j v = v) : l.foldr (reflect Tag.E6) v = v := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]
    exact h j List.mem_cons_self

theorem exists_letter_moving {v : N6 → ℤ} {l : List N6}
    (h : (coxeterSystem Tag.E6).wordProd l • v ≠ v) : ∃ j ∈ l, reflect Tag.E6 j v ≠ v := by
  by_contra hcon
  push Not at hcon
  exact h (by rw [wordProd_smul_foldr]; exact foldr_reflect_eq_of_fix hcon)

theorem linearIndependent_translates_support
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {v : N6 → ℤ}
    (hv : ∀ j, reflect Tag.E6 j v ≠ v → j ∉ J) {m : ℕ} (w : Fin m → WeylGroup Tag.E6)
    (hinj : ∀ i j, i ≠ j → w i • v ≠ w j • v) :
    LinearIndependent k (fun i => ρ (canonMin K (w i)) y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (e6Cover_split k)
  refine CurtisExc.linearIndependent_translates hρ hμ w fun i j hij ω hω hωe => ?_
  have hωe' : (coxeterSystem Tag.E6).wordProd (ω : List N6) = (w i)⁻¹ * w j := hωe
  have hne : (coxeterSystem Tag.E6).wordProd (ω : List N6) • v ≠ v := by
    intro h
    apply hinj i j hij
    rw [hωe', mul_smul] at h
    have := congrArg (fun z => w i • z) h
    simpa [smul_smul] using this.symm
  obtain ⟨l, hl, hlv⟩ := exists_letter_moving (l := (ω : List N6)) hne
  exact ⟨l, hl, mu_eq_dScalar_of_notMem ht hμ (hv l hlv)⟩

theorem card_le_finrank_support [Module.Finite k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {v : N6 → ℤ}
    (hv : ∀ j, reflect Tag.E6 j v ≠ v → j ∉ J) {m : ℕ} (w : Fin m → WeylGroup Tag.E6)
    (hinj : ∀ i j, i ≠ j → w i • v ≠ w j • v) : m ≤ Module.finrank k V := by
  simpa using (linearIndependent_translates_support hρ ht hv w hinj).fintype_card_le_finrank

theorem sign_eq_one {σ : K} (h : IsSign σ) : σ = 1 := by
  rcases h with h | h
  · exact h
  · rw [h]; exact CharTwo.neg_eq (1 : K)

theorem nProd_conj_xm {γ : N6 → ℤ} (hγ : IsRoot Tag.E6 γ) (c : K) (l : List N6) :
    IsRoot Tag.E6 (l.foldr (reflect Tag.E6) γ) ∧
      nProd K l * e6Data_valid.xm K γ c * (nProd K l)⁻¹ =
        e6Data_valid.xm K (l.foldr (reflect Tag.E6) γ) c := by
  induction l with
  | nil => exact ⟨hγ, by simp [nProd_nil]⟩
  | cons j l ih =>
    obtain ⟨hroot, hconj⟩ := ih
    obtain ⟨σ, hσ, h⟩ := e6Data_valid.nm_conj_xm K hroot j
    refine ⟨IsRoot.reflect j hroot, ?_⟩
    rw [nProd_cons, List.foldr_cons]
    calc e6Data_valid.nm K j * nProd K l * e6Data_valid.xm K γ c *
          (e6Data_valid.nm K j * nProd K l)⁻¹
        = e6Data_valid.nm K j * (nProd K l * e6Data_valid.xm K γ c * (nProd K l)⁻¹) *
          (e6Data_valid.nm K j)⁻¹ := by group
      _ = _ := by rw [hconj, h c, sign_eq_one hσ, one_mul]

theorem canonMin_commute_rankOne (w : WeylGroup Tag.E6) (s : N6)
    (hws : w • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1) (g : SL(2, K)) :
    canonMin K w * rankOne6 K s g = rankOne6 K s g * canonMin K w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  have hcm : canonMin K ((coxeterSystem Tag.E6).wordProd ω) = nProd K ω := canonMin_wordProd hω
  rw [hcm]
  have hf1 : ω.foldr (reflect Tag.E6) (Pi.single s 1 : N6 → ℤ) = Pi.single s 1 := by
    rw [← wordProd_smul_foldr]; exact hws
  have hf2 : ω.foldr (reflect Tag.E6) (-Pi.single s 1 : N6 → ℤ) = -Pi.single s 1 := by
    rw [← wordProd_smul_foldr, smul_neg, hws]
  have hcl := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K)
  set S : Subgroup (SL(2, K)) :=
    (Subgroup.centralizer ({nProd K ω} : Set ↥(e6Data_valid.minGroup K))).comap (rankOne6 K s)
    with hS
  have hmem : ∀ x : SL(2, K), x ∈ S ↔ nProd K ω * rankOne6 K s x = rankOne6 K s x * nProd K ω := by
    intro x
    simp only [hS, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
  have hle : Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper K) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower K)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c ∈ S
      have e : CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c = uElt c := rfl
      rw [e, hmem, rankOne6_u]
      have := (nProd_conj_xm (isRoot_single Tag.E6 s) c ω).2
      rw [hf1, mul_inv_eq_iff_eq_mul] at this
      exact this
    · show CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c ∈ S
      have e : CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = lElt c := rfl
      rw [e, hmem, rankOne6_l]
      have := (nProd_conj_xm (isRoot_neg_single Tag.E6 s) c ω).2
      rw [hf2, mul_inv_eq_iff_eq_mul] at this
      exact this
  have : g ∈ S := hle (by rw [hcl]; exact Subgroup.mem_top g)
  exact (hmem g).1 this

@[expose] def repEquiv {G : Type*} [Group G] (ρ : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem copies_finrank_orbit [Module.Finite k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {s : N6} {m : ℕ}
    (u : Fin m → WeylGroup Tag.E6)
    (hu : ∀ i, u i • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (canonMin K (u i)) y)) :
    m * Module.finrank k (orbitSpan (ρ.comp (rankOne6 K s)) y) ≤ Module.finrank k V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := ρ.comp (rankOne6 K s) with hσ
  set D := D6 K with hD
  obtain ⟨hxN, hyN⟩ := Us_normalized (K := K) s
  set v : Fin m → V := fun i => ρ (canonMin K (u i)) y with hv
  have hcomm : ∀ i (g' : SL(2, K)) (w : V), σ g' (ρ (canonMin K (u i)) w) =
      ρ (canonMin K (u i)) (σ g' w) := by
    intro i g' w
    show ρ (rankOne6 K s g') (ρ (canonMin K (u i)) w) = ρ (canonMin K (u i)) (ρ (rankOne6 K s g') w)
    rw [act_mul, act_mul, ← canonMin_commute_rankOne (u i) s (hu i) g']
  set Fix : Fin m → Submodule k V := fun i =>
    (fixSub ρ (D.Us s)).map (ρ (canonMin K (u i))) with hFix
  have hyFix : y ∈ fixSub ρ (D.Us s) := fun q hq => ht.1 q (D.Us_le s hq)
  have hyu : ∀ c : K, σ (uElt c) y = y := by
    intro c
    show ρ (rankOne6 K s (uElt c)) y = y
    rw [rankOne6_u]
    exact ht.1 _ (D.X_le s (xm_mem_X s c))
  have hmap_inj : ∀ i, Function.Injective (ρ (canonMin K (u i))) :=
    fun i => (repEquiv ρ (canonMin K (u i))).injective
  have hres := finrank_iSup_orbitSpan σ v Fix
    (fun i => Submodule.mem_map_of_mem hyFix)
    (by
      rintro i g' _ ⟨f, hf, rfl⟩
      rw [hcomm]
      exact Submodule.mem_map_of_mem (fixSub_stable_rankOne ρ s (D.Us s) hxN hyN g' hf))
    (by
      rintro i _ ⟨f0, hf0, rfl⟩ hfu
      have h1 : ∀ c : K, ρ (e6Data_valid.xm K (Pi.single s 1) c) f0 = f0 := by
        intro c
        have := hfu c
        rw [hcomm] at this
        have h2 : σ (uElt c) f0 = f0 := hmap_inj i this
        have h3 : ρ (rankOne6 K s (uElt c)) f0 = f0 := h2
        rw [rankOne6_u] at h3
        exact h3
      obtain ⟨c, hc⟩ := fix_of_highest hρ ht s hf0 h1
      exact ⟨c, by rw [hc, map_smul]⟩)
    (fun i c => by rw [hcomm, hyu c])
    Finset.univ (hli.comp (fun x : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) => (x : Fin m))
      Subtype.val_injective)
  obtain ⟨hdim, -, -⟩ := hres
  have hN : ∀ i, Module.finrank k (orbitSpan σ (v i)) = Module.finrank k (orbitSpan σ y) := by
    intro i
    have : orbitSpan σ (v i) = (orbitSpan σ y).map (ρ (canonMin K (u i))) := by
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
    exact (repEquiv ρ (canonMin K (u i))).finrank_map_eq _
  calc m * Module.finrank k (orbitSpan σ y)
      = ∑ i : Fin m, Module.finrank k (orbitSpan σ (v i)) := by simp [hN]
    _ = Module.finrank k (⨆ i ∈ (Finset.univ : Finset (Fin m)), orbitSpan σ (v i) : Submodule k V) :=
        hdim.symm
    _ ≤ Module.finrank k V := Submodule.finrank_le _

theorem copies_finrank [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {s : N6} (hs : s ∉ J) {g : ℕ} (hg : 1 ≤ g)
    (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) ^ (2 ^ g) = χ (e6Data_valid.hm K s z)) {m : ℕ}
    (u : Fin m → WeylGroup Tag.E6)
    (hu : ∀ i, u i • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (canonMin K (u i)) y)) :
    m * 2 ^ (n / g) ≤ Module.finrank k V :=
  calc m * 2 ^ (n / g)
      ≤ m * Module.finrank k (orbitSpan (ρ.comp (rankOne6 K s)) y) :=
        Nat.mul_le_mul_left _ (two_pow_le_finrank_orbitSpan hn hK hρ ht hs hg hgn hper)
    _ ≤ Module.finrank k V := copies_finrank_orbit hρ ht u hu hli

theorem copies_linearIndependent [Module.Finite k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {s : N6} {m : ℕ}
    (u : Fin m → WeylGroup Tag.E6)
    (hu : ∀ i, u i • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1)
    (hli : LinearIndependent k (fun i => ρ (canonMin K (u i)) y)) {e : V}
    (he : e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y) (he0 : e ≠ 0) :
    LinearIndependent k (fun i => ρ (canonMin K (u i)) e) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := ρ.comp (rankOne6 K s) with hσ
  set D := D6 K with hD
  obtain ⟨hxN, hyN⟩ := Us_normalized (K := K) s
  set v : Fin m → V := fun i => ρ (canonMin K (u i)) y with hv
  have hcomm : ∀ i (g' : SL(2, K)) (w : V), σ g' (ρ (canonMin K (u i)) w) =
      ρ (canonMin K (u i)) (σ g' w) := by
    intro i g' w
    show ρ (rankOne6 K s g') (ρ (canonMin K (u i)) w) = ρ (canonMin K (u i)) (ρ (rankOne6 K s g') w)
    rw [act_mul, act_mul, ← canonMin_commute_rankOne (u i) s (hu i) g']
  set Fix : Fin m → Submodule k V := fun i =>
    (fixSub ρ (D.Us s)).map (ρ (canonMin K (u i))) with hFix
  have hyFix : y ∈ fixSub ρ (D.Us s) := fun q hq => ht.1 q (D.Us_le s hq)
  have hyu : ∀ c : K, σ (uElt c) y = y := by
    intro c
    show ρ (rankOne6 K s (uElt c)) y = y
    rw [rankOne6_u]
    exact ht.1 _ (D.X_le s (xm_mem_X s c))
  have hmap_inj : ∀ i, Function.Injective (ρ (canonMin K (u i))) :=
    fun i => (repEquiv ρ (canonMin K (u i))).injective
  have hres := finrank_iSup_orbitSpan σ v Fix
    (fun i => Submodule.mem_map_of_mem hyFix)
    (by
      rintro i g' _ ⟨f, hf, rfl⟩
      rw [hcomm]
      exact Submodule.mem_map_of_mem (fixSub_stable_rankOne ρ s (D.Us s) hxN hyN g' hf))
    (by
      rintro i _ ⟨f0, hf0, rfl⟩ hfu
      have h1 : ∀ c : K, ρ (e6Data_valid.xm K (Pi.single s 1) c) f0 = f0 := by
        intro c
        have := hfu c
        rw [hcomm] at this
        have h2 : σ (uElt c) f0 = f0 := hmap_inj i this
        have h3 : ρ (rankOne6 K s (uElt c)) f0 = f0 := h2
        rw [rankOne6_u] at h3
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
  have : orbitSpan σ (v i) = (orbitSpan σ y).map (ρ (canonMin K (u i))) := by
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

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
