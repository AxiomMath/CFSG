module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticRigidLines
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerGraph

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.ComponentClassification
open scoped IsMulCommutative

variable {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

section Mixing

theorem SpPlaneSetupQ.mul_comm_elem (S : SpPlaneSetupQ ℓ f p r K Ahat) (y z : ↥Ahat) :
    y * z = z * y := by
  have := S.elem
  exact (IsMulCommutative.is_comm (M := ↥Ahat)).comm y z

theorem SpPlaneSetupQ.spLineSpace_stable (S : SpPlaneSetupQ ℓ f p r K Ahat)
    {M : Subgroup ↥Ahat} (y : ↥Ahat) {s : Fin r ⊕ Fin r → K} (hs : s ∈ spLineSpace M) :
    spEnd (y : StatedSp r K) s ∈ spLineSpace M := by
  refine ⟨?_, ?_⟩
  · change spEnd (y : StatedSp r K) s ∈ fixSub (spRep Ahat) M
    rw [mem_fixSub]
    intro d hd
    have h1 : spRep Ahat d s = s := mem_fixSub.mp hs.1 d hd
    have h2 : spEnd (d : StatedSp r K) s = s := h1
    change spEnd (d : StatedSp r K) (spEnd (y : StatedSp r K) s) = spEnd (y : StatedSp r K) s
    have hcomm : (d : StatedSp r K) * (y : StatedSp r K) =
        (y : StatedSp r K) * (d : StatedSp r K) :=
      congrArg Subtype.val (S.mul_comm_elem d y)
    rw [← Module.End.mul_apply, ← spEnd_mul, hcomm, spEnd_mul, Module.End.mul_apply, h2]
  · rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hyu : spEnd (y : StatedSp r K) u = u := mem_fixSub.mp hu y (Subgroup.mem_top y)
    have h3 := spRep_isometry Ahat y u s
    change spForm r K (spEnd (y : StatedSp r K) u) (spEnd (y : StatedSp r K) s) = spForm r K u s
      at h3
    rw [hyu] at h3
    rw [h3]
    exact hs.2 u hu

theorem SpPlaneSetupQ.primaryFactor_dvd_pow_sub_one (S : SpPlaneSetupQ ℓ f p r K Ahat)
    {x : StatedSp r K} (hxA : x ∈ Ahat) {g : K[X]} (hg : g ∈ primaryFactors (spEnd x)) :
    g ∣ X ^ p - 1 := by
  have hpow : spEnd x ^ p = 1 := spEnd_pow (S.pow_eq_one hxA)
  refine (mem_primaryFactors.mp hg).2.2.trans (minpoly.dvd K _ ?_)
  simp [hpow]

theorem SpPlaneSetupQ.exists_factor_of_line (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) {L N : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {x : StatedSp r K} (hxA : x ∈ Ahat)
    (hxN : (⟨x, hxA⟩ : ↥Ahat) ∈ N) (hx1 : x ≠ 1) (hVL : spLineSpace L ≠ ⊥) :
    ∃ g ∈ primaryFactors (spEnd x), g ≠ X - 1 ∧ ∃ v ∈ spLineSpace L,
      v ∈ primaryComponent (spEnd x) g ∧ v ≠ 0 := by
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVL
  have hsq : Squarefree (minpoly K (spEnd x)) :=
    (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one hxA)).squarefree
  obtain ⟨g, hg, v, hvL, hvg, hv0⟩ := exists_primaryFactor_mem hsq
    (fun s hs => S.spLineSpace_stable ⟨x, hxA⟩ hs) hv₀ hv₀0
  refine ⟨g, hg, ?_, v, hvL, hvg, hv0⟩
  rintro rfl
  have hfix : spEnd x v = v := by
    have := mem_primaryComponent.mp hvg
    simpa [sub_eq_zero] using this
  exact hv0 (D.eq_zero_of_fixed_spLineSpace hL hN hLN hxA hxN hx1 hvL hfix)

theorem SpPlaneSetupQ.exists_mixing_factor (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) {L N : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) (hVL : spLineSpace L ≠ ⊥) (hVN : spLineSpace N ≠ ⊥) :
    ∃ x : StatedSp r K, x ∈ Ahat ∧ x ≠ 1 ∧ ∃ h ∈ primaryFactors (spEnd x), h ≠ X - 1 ∧
      2 ≤ primaryMultiplicity (spEnd x) h ∧
      (∃ v ∈ spLineSpace L, v ∈ primaryComponent (spEnd x) h ∧ v ≠ 0) ∧
      (∃ w ∈ spLineSpace N, w ∈ primaryComponent (spEnd x) h ∧ w ≠ 0) := by
  classical
  have := S.finite
  have hex : ∀ M : Subgroup ↥Ahat, Nat.card M = p → ∃ t : ↥Ahat, t ∈ M ∧ t ≠ 1 := by
    intro M hM
    have h1 : Nontrivial ↥M :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact S.prime_p.one_lt)
    obtain ⟨t, ht⟩ := exists_ne (1 : ↥M)
    exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
  obtain ⟨tL, htL, htL1⟩ := hex L hL
  obtain ⟨tN, htN, htN1⟩ := hex N hN
  have htL1' : (tL : StatedSp r K) ≠ 1 := fun h => htL1 (Subtype.ext h)
  have htN1' : (tN : StatedSp r K) ≠ 1 := fun h => htN1 (Subtype.ext h)
  obtain ⟨f₁, hf₁, hf₁1, v, hvL, hvf, hv0⟩ :=
    S.exists_factor_of_line D hL hN hLN tN.2 htN htN1' hVL
  obtain ⟨g₁, hg₁, hg₁1, w, hwN, hwg, hw0⟩ :=
    S.exists_factor_of_line D hN hL hLN.symm tL.2 htL htL1' hVN
  have hfd := S.primaryFactor_dvd_pow_sub_one tN.2 hf₁
  have hgd := S.primaryFactor_dvd_pow_sub_one tL.2 hg₁
  have hfmon := monic_of_mem_primaryFactors hf₁
  have hfirr := irreducible_of_mem_primaryFactors hf₁
  have hX : (X - 1 : K[X]) = X - C 1 := by rw [map_one]
  obtain ⟨j, hj0, hjp, hdvd⟩ := exists_pow_dvd_comp S.prime_p hfmon hfirr hfd
    (by rwa [← hX]) (monic_of_mem_primaryFactors hg₁) (irreducible_of_mem_primaryFactors hg₁) hgd
    (by rwa [← hX])
  set a : ↥Ahat := tL ^ j * tN with ha
  set T : Module.End K (Fin r ⊕ Fin r → K) := spEnd (a : StatedSp r K) with hT
  have hcoe : ((tL ^ j : ↥Ahat) : StatedSp r K) = (tL : StatedSp r K) ^ j :=
    Subgroup.coe_pow Ahat tL j
  have hTfac : T = (spEnd (tL : StatedSp r K)) ^ j * spEnd (tN : StatedSp r K) := by
    rw [hT, ha, Subgroup.coe_mul, spEnd_mul, hcoe, spEnd_npow]
  have hTL : ∀ s ∈ spLineSpace L, T s = spEnd (tN : StatedSp r K) s := by
    intro s hs
    have hs' := S.spLineSpace_stable tN hs
    have h1 : spEnd ((tL ^ j : ↥Ahat) : StatedSp r K) (spEnd (tN : StatedSp r K) s) =
        spEnd (tN : StatedSp r K) s := mem_fixSub.mp hs'.1 (tL ^ j) (pow_mem htL j)
    rw [hTfac, Module.End.mul_apply, ← spEnd_npow, ← hcoe]
    exact h1
  have hTN : ∀ s ∈ spLineSpace N, T s = (spEnd (tL : StatedSp r K) ^ j) s := by
    intro s hs
    have h1 : spEnd (tN : StatedSp r K) s = s := mem_fixSub.mp hs.1 tN htN
    rw [hTfac, Module.End.mul_apply, h1]
  have hUstab : ∀ s ∈ spLineSpace N, (spEnd (tL : StatedSp r K) ^ j) s ∈ spLineSpace N := by
    intro s hs
    rw [← spEnd_npow, ← hcoe]
    exact S.spLineSpace_stable (tL ^ j) hs
  have hfv : aeval T f₁ v = 0 := by
    rw [aeval_apply_eq_of_agree (fun s hs => S.spLineSpace_stable tN hs) hTL f₁ hvL]
    exact mem_primaryComponent.mp hvf
  have hfw : aeval T f₁ w = 0 := by
    rw [aeval_apply_eq_of_agree hUstab hTN f₁ hwN]
    have hcomp : aeval (spEnd (tL : StatedSp r K)) (f₁.comp (X ^ j)) =
        aeval (spEnd (tL : StatedSp r K) ^ j) f₁ := by
      rw [Polynomial.aeval_comp, aeval_X_pow]
    obtain ⟨q, hq⟩ := hdvd
    rw [← hcomp, hq, mul_comm, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hwg,
      map_zero]
  have hmem : f₁ ∈ primaryFactors T := mem_primaryFactors_of_apply_eq_zero hfirr hfmon hfv hv0
  have : Fact (Irreducible f₁) := ⟨hfirr⟩
  have hm2 : 2 ≤ primaryMultiplicity T f₁ :=
    two_le_primaryMultiplicity (T := T) (a := f₁) (S₁ := spLineSpace L) (S₂ := spLineSpace N)
      (fun s hs => S.spLineSpace_stable a hs) (fun s hs => S.spLineSpace_stable a hs)
      (D.disjoint_lineSpace hL hN hLN) hvL hwN (mem_primaryComponent.mpr hfv)
      (mem_primaryComponent.mpr hfw) hv0 hw0
  have ha1 : (a : StatedSp r K) ≠ 1 := by
    intro h1
    apply htN1'
    have h2 : tN = (tL ^ j)⁻¹ := by
      have h3 : a = 1 := Subtype.ext h1
      rw [ha] at h3
      exact eq_inv_of_mul_eq_one_right h3
    have h3 : tN ∈ L ⊓ N := ⟨h2 ▸ L.inv_mem (L.pow_mem htL j), htN⟩
    rw [inf_eq_bot_of_card_prime S.prime_p hL hN hLN] at h3
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h3)
  exact ⟨a, a.2, ha1, f₁, hmem, hf₁1, hm2, ⟨v, hvL, mem_primaryComponent.mpr hfv, hv0⟩,
    ⟨w, hwN, mem_primaryComponent.mpr hfw, hw0⟩⟩

theorem SpPlaneSetupQ.mem_spInnerSummand_stable (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (i : Option {M : Subgroup ↥Ahat // Nat.card M = p}) {x : StatedSp r K} (hxA : x ∈ Ahat)
    {u : Fin r ⊕ Fin r → K} (hu : u ∈ spInnerSummand p Ahat i) :
    spEnd x u ∈ spInnerSummand p Ahat i := by
  rcases i with _ | ⟨M, hM⟩
  · have h1 : spRep Ahat ⟨x, hxA⟩ u = u := mem_fixSub.mp hu ⟨x, hxA⟩ (Subgroup.mem_top _)
    change spEnd x u ∈ spPlaneFix Ahat
    have h2 : spEnd x u = u := h1
    rw [h2]
    exact hu
  · exact S.spLineSpace_stable ⟨x, hxA⟩ hu

open _root_.Classical in
theorem SpPlaneSetupQ.semilinMap_comm_of_scalar_summands (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) (A : gsp r K)
    (hscal : ∀ i, ∃ l : K, ∀ u ∈ spInnerSummand p Ahat i,
      semilinMap A (RingEquiv.refl K) u = l • u)
    {x : StatedSp r K} (hxA : x ∈ Ahat) (u : Fin r ⊕ Fin r → K) :
    semilinMap A (RingEquiv.refl K) (spEnd x u) = spEnd x (semilinMap A (RingEquiv.refl K) u) := by
  have htop : u ∈ ⨆ i, spInnerSummand p Ahat i := by
    rw [D.internal.submodule_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction (spInnerSummand p Ahat)
    (motive := fun u => semilinMap A (RingEquiv.refl K) (spEnd x u) =
      spEnd x (semilinMap A (RingEquiv.refl K) u)) htop ?_ ?_ ?_
  · intro i u hu
    obtain ⟨l, hl⟩ := hscal i
    rw [hl u hu, hl _ (S.mem_spInnerSummand_stable i hxA hu), map_smul]
  · simp [semilinMap_zero]
  · intro u v hu hv
    rw [map_add, semilinMap_add, semilinMap_add, map_add, hu, hv]

theorem SpPlaneSetupQ.eq_of_mixing [NeZero r] (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) (A : gsp r K) {α : MulAut (StatedProj (StatedSp r K))}
    (hα : α = conjAut r K A * fieldAut r K (RingEquiv.refl K))
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x)
    (hscal : ∀ i, ∃ l : K, ∀ u ∈ spInnerSummand p Ahat i,
      semilinMap A (RingEquiv.refl K) u = l • u)
    {L N : Subgroup ↥Ahat} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hVL : spLineSpace L ≠ ⊥) (hVN : spLineSpace N ≠ ⊥) {lL lN : K}
    (hlL : ∀ u ∈ spLineSpace L, semilinMap A (RingEquiv.refl K) u = lL • u)
    (hlN : ∀ u ∈ spLineSpace N, semilinMap A (RingEquiv.refl K) u = lN • u) : lL = lN := by
  obtain ⟨x, hxA, hx1, h, hmem, hh1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    S.exists_mixing_factor D hL hN hLN hVL hVN
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  have facts := spBlockFacts_of_ne_X_sub_one_q S.four_le_q (S.blocks hxA hx1) ⟨h, hmem⟩ hh1
  have hinj := S.conj_injective
  have hcommx : ∀ u, ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      (spEnd x u) = spEnd x (((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u) := fun u =>
    S.semilinMap_comm_of_scalar_summands D A hscal hxA u
  have hYx : (Matrix.GeneralLinearGroup.toLin (A : GL (Fin r ⊕ Fin r) K) :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) ∈
        KCUnitary.gl_centralizer (spLin r K x) :=
    KCUnitary.mem_gl_centralizer.mpr (commute_toLin_spLin (A : GL (Fin r ⊕ Fin r) K) x hcommx
      |>.units_val)
  have hperf := isPerfect_spPull facts hm2
  have hblock : ∀ g ∈ KCUnitary.specialBlock (spForm r K) (spLin r K x) (h : K[X]),
      Commute (Matrix.GeneralLinearGroup.toLin (A : GL (Fin r ⊕ Fin r) K) :
        LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) g := by
    intro g hg
    have hle : KCUnitary.specialBlock (spForm r K) (spLin r K x) (h : K[X]) ≤
        sesqUnitaryGroup (spForm r K) := fun g hg =>
      (KCUnitary.mem_unitaryCentralizer.mp (KCUnitary.specialBlock_le_unitaryCentralizer hg)).1
    obtain ⟨g', rfl⟩ : g ∈ (spLin r K).range := by rw [range_spLin]; exact hle hg
    have hg' : g' ∈ (KCUnitary.specialBlock (spForm r K) (spLin r K x) (h : K[X])).comap
        (spLin r K) := hg
    have hcomm : ∀ y ∈ (KCUnitary.specialBlock (spForm r K) (spLin r K x) (h : K[X])).comap
        (spLin r K), (conjAut r K A * fieldAut r K (RingEquiv.refl K)) *
          MulAut.conj (proj r K y) = MulAut.conj (proj r K y) *
            (conjAut r K A * fieldAut r K (RingEquiv.refl K)) := fun y hy =>
      hα ▸ (hcent x hxA hx1).2 h hmem hh1 hm2 (proj r K y) (Subgroup.mem_map_of_mem _ hy)
    have hfix := semiConj_eq_of_commute hinj A (RingEquiv.refl K) (Or.inl hperf) hcomm g' hg'
    exact commute_toLin_spLin (A : GL (Fin r ⊕ Fin r) K) g' (fun u => by
      have := semilinMap_comm A (RingEquiv.refl K) hfix u
      exact this)
  obtain ⟨c, hc⟩ := facts.scalar _ hYx (fun _ g hg => hblock g hg)
  exact KCUnitaryScalar.eq_of_eScalar (x := spEnd x) (a := h) hc hvh hwh hv0 hw0
    (by rw [← hlL v hvL]; rfl) (by rw [← hlN w hwN]; rfl)

open _root_.Classical in
theorem SpPlaneSetupQ.exists_global_scalar [NeZero r] (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) (A : gsp r K) {α : MulAut (StatedProj (StatedSp r K))}
    (hα : α = conjAut r K A * fieldAut r K (RingEquiv.refl K))
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x)
    (hline : ∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ →
      ∃ l : K, ∀ u ∈ spPlaneFix Ahat ⊔ spLineSpace M,
        semilinMap A (RingEquiv.refl K) u = l • u) :
    ∃ l : K, ∀ u, semilinMap A (RingEquiv.refl K) u = l • u := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hne, hV₁, hV₂⟩ := D.two_active
  choose! lam hlam using hline
  have hbot : ∀ M : Subgroup ↥Ahat, spLineSpace M = ⊥ → ∀ u ∈ spLineSpace M,
      semilinMap A (RingEquiv.refl K) u = (0 : K) • u := by
    intro M hV u hu
    have : u = 0 := by
      rw [hV] at hu
      exact (Submodule.mem_bot K).mp hu
    rw [this, semilinMap_zero, zero_smul]
  have hscal : ∀ i, ∃ l : K, ∀ u ∈ spInnerSummand p Ahat i,
      semilinMap A (RingEquiv.refl K) u = l • u := by
    intro i
    rcases i with _ | ⟨M, hM⟩
    · exact ⟨lam M₁, fun u hu => hlam M₁ hM₁ hV₁ u (Submodule.mem_sup_left hu)⟩
    · by_cases hV : spLineSpace M = ⊥
      · exact ⟨0, hbot M hV⟩
      · exact ⟨lam M, fun u hu => hlam M hM hV u (Submodule.mem_sup_right hu)⟩
  have heq : ∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ → lam M = lam M₁ := by
    intro M hM hV
    by_cases hMM : M = M₁
    · rw [hMM]
    · exact (S.eq_of_mixing D A hα hcent hscal hM₁ hM (Ne.symm hMM) hV₁ hV
        (fun u hu => hlam M₁ hM₁ hV₁ u (Submodule.mem_sup_right hu))
        (fun u hu => hlam M hM hV u (Submodule.mem_sup_right hu))).symm
  refine ⟨lam M₁, fun u => ?_⟩
  have htop : u ∈ ⨆ i, spInnerSummand p Ahat i := by
    rw [D.internal.submodule_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction (spInnerSummand p Ahat)
    (motive := fun u => semilinMap A (RingEquiv.refl K) u = lam M₁ • u) htop ?_ ?_ ?_
  · intro i u hu
    rcases i with _ | ⟨M, hM⟩
    · exact hlam M₁ hM₁ hV₁ u (Submodule.mem_sup_left hu)
    · by_cases hV : spLineSpace M = ⊥
      · have hu0 : u = 0 := by
          have hu' : u ∈ spLineSpace M := hu
          rw [hV] at hu'
          exact (Submodule.mem_bot K).mp hu'
        rw [hu0, semilinMap_zero, smul_zero]
      · rw [hlam M hM hV u (Submodule.mem_sup_right hu), heq M hM hV]
  · rw [semilinMap_zero, smul_zero]
  · intro u v hu hv
    rw [semilinMap_add, hu, hv, smul_add]

end Mixing

section Rigidity

theorem SpPlaneSetupQ.exists_ne_one_mem (S : SpPlaneSetupQ ℓ f p r K Ahat)
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) : ∃ t : ↥Ahat, t ∈ M ∧ t ≠ 1 := by
  have := S.finite
  have h1 : Nontrivial ↥M :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact S.prime_p.one_lt)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥M)
  exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩

theorem SpPlaneSetupQ.rigidity_of_semilinear [NeZero r] (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (A : gsp r K) (σ : K ≃+* K) {α : MulAut (StatedProj (StatedSp r K))}
    (hα : α = conjAut r K A * fieldAut r K σ)
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x) : α = 1 := by
  have D := S.decomp
  obtain ⟨M₁, M₂, hM₁, hM₂, hne, hV₁, hV₂⟩ := D.two_active
  obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
  have ht₁1' : (t₁ : StatedSp r K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  have hσ : σ = RingEquiv.refl K :=
    (S.line_scalar D hM₁ hV₁ t₁.2 ht₁ ht₁1' A σ hα (hcent _ t₁.2 ht₁1')).1
  subst hσ
  have hline : ∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ →
      ∃ l : K, ∀ u ∈ spPlaneFix Ahat ⊔ spLineSpace M,
        semilinMap A (RingEquiv.refl K) u = l • u := by
    intro M hM hVM
    obtain ⟨t, ht, ht1⟩ := S.exists_ne_one_mem hM
    have ht1' : (t : StatedSp r K) ≠ 1 := fun h => ht1 (Subtype.ext h)
    obtain ⟨-, l, hl, -⟩ := S.line_scalar D hM hVM t.2 ht ht1' A (RingEquiv.refl K) hα
      (hcent _ t.2 ht1')
    refine ⟨l, fun u hu => hl u ?_⟩
    rw [D.ker_eq_sup hM t.2 ht ht1']
    exact hu
  obtain ⟨l, hl⟩ := S.exists_global_scalar D A hα hcent hline
  rw [hα]
  exact alpha_eq_one_of_scalar A hl

theorem SpPlaneSetupQ.exists_semilinear_of_ne_exceptional (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (hne : ¬ (ℓ = 2 ∧ r = 2)) (α : MulAut (StatedProj (StatedSp r K))) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ := by
  have := S.finite
  have := S.charP
  by_cases hr3 : 3 ≤ r
  · exact (automorphism_generation (K := K) hr3).2 α
  · have hℓ2 : ℓ ≠ 2 := fun h => hne ⟨h, by have := S.two_le_r; omega⟩
    have hodd : ringChar K ≠ 2 := by
      rw [ringChar.eq K ℓ]
      exact hℓ2
    exact (odd_symplectic_automorphism_semilinear_representation hodd S.two_le_r).1 α

theorem SpPlaneSetupQ.inner_of_rank_two_even {Ahat₂ : Subgroup (StatedSp 2 K)}
    (S : SpPlaneSetupQ ℓ f p 2 K Ahat₂) (hℓ : ℓ = 2)
    {α : MulAut (StatedProj (StatedSp 2 K))}
    (hcent : ∀ x ∈ Ahat₂, x ≠ 1 → CentralizesListed α x) :
    α ∈ OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) := by
  have := S.finite
  have D := S.decomp
  obtain ⟨M₁, M₂, hM₁, hM₂, hne, hV₁, hV₂⟩ := D.two_active
  obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
  have ht₁1' : (t₁ : StatedSp 2 K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  obtain ⟨hlisted, h2dim⟩ := S.spFixedListed D hM₁ hV₁ t₁.2 ht₁ ht₁1'
  have hdim := spFixedDim_eq_finrank_ker (t₁ : StatedSp 2 K)
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ LinearMap.ker (spEnd (t₁ : StatedSp 2 K) - 1), u ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have h0 : Module.finrank K (LinearMap.ker (spEnd (t₁ : StatedSp 2 K) - 1)) = 0 := by
      rw [h]
      exact finrank_bot K _
    omega
  have hq4 := S.four_le_card
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by have := S.one_le_f; omega
    have := S.four_le_q
    rw [hf1, hℓ] at this
    omega
  have hK : Nat.card K = 2 ^ f := by rw [S.card_K, hℓ]
  have himg : spFixedLayerImage (t₁ : StatedSp 2 K) =
      (spFixedFactor (t₁ : StatedSp 2 K)).map (proj 2 K) := by
    have h42 : ¬ (spFixedDim (t₁ : StatedSp 2 K) = 4 ∧ Nat.card K = 2) := fun h => by omega
    simp [spFixedLayerImage, hlisted, h42]
  have hα' : ∀ t : K, α (proj 2 K (spTransvection u t)) = proj 2 K (spTransvection u t) := by
    intro t
    have hmem : spTransvection u t ∈ spFixedFactor (t₁ : StatedSp 2 K) :=
      spTransvection_mem_spFixedFactor (mem_ker_sub_one_iff.mp hu) t
    have h1 := (hcent _ t₁.2 ht₁1').1 hlisted _ (himg ▸ Subgroup.mem_map_of_mem _ hmem)
    exact (commute_conj_iff S.conj_injective α _).mp h1
  exact even_symplectic_rank_two_inner_of_fixes_transvections hf2 hK u hu0 α hα'

theorem SpPlaneSetupQ.exists_semilinear_of_centralizes (S : SpPlaneSetupQ ℓ f p r K Ahat)
    {α : MulAut (StatedProj (StatedSp r K))}
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ := by
  by_cases hne : ℓ = 2 ∧ r = 2
  · obtain ⟨hℓ, hr⟩ := hne
    subst hr
    exact exists_semilinear_of_inner (S.inner_of_rank_two_even hℓ hcent)
  · exact S.exists_semilinear_of_ne_exceptional hne α

theorem SpPlaneSetupQ.eq_one_of_centralizes (S : SpPlaneSetupQ ℓ f p r K Ahat)
    {α : MulAut (StatedProj (StatedSp r K))}
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x) : α = 1 := by
  have := S.neZero
  obtain ⟨A, σ, hα⟩ := S.exists_semilinear_of_centralizes hcent
  exact S.rigidity_of_semilinear A σ hα hcent

end Rigidity

end CFSG.HardMathSupport.Timmesfeld.CrossChar
