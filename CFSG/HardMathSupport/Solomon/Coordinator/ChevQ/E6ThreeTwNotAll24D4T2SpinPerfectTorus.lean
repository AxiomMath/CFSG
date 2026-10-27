module

public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false


section Torus

variable {L : Type} [Field L] (σ : L ≃+* L)

theorem d4t2sp_torusRootChar_fixed {t : ModGL Tag.E6 L} (ht : t ∈ torusGroup Tag.E6 L)
    (hfix : frobGL σ t = t) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    σ (torusRootChar t α) = torusRootChar t α := by
  have h1 := conj_pinnedX_of_mem_torusGroup ht hα (1 : L)
  have h2 := congrArg (frobGL σ) h1
  rw [map_mul, map_mul, map_inv, hfix, frobGL_pinnedX, frobGL_pinnedX, map_one] at h2
  rw [h1] at h2
  have h3 := pinnedX_injective Tag.E6 L α h2
  simpa using h3.symm

theorem d4t2sp_fixed_of_relations {G : Type*} [CommGroup G] (K : Subgroup G) {x1 x2 x3 x4 : G}
    (h0 : x2⁻¹ ∈ K) (h5 : x4⁻¹ ∈ K) (h2 : x2 ^ 2 * x3⁻¹ ∈ K)
    (h3 : x1⁻¹ * x2⁻¹ * x3 ^ 2 * x4⁻¹ ∈ K) : x1 ∈ K ∧ x2 ∈ K ∧ x3 ∈ K ∧ x4 ∈ K := by
  have hx2 : x2 ∈ K := by simpa using h0
  have hx4 : x4 ∈ K := by simpa using h5
  have hx3 : x3 ∈ K := by
    have := mul_mem (inv_mem (pow_mem hx2 2)) h2
    simpa using this
  have hx1 : x1 ∈ K := by
    have := mul_mem h3 (mul_mem (mul_mem hx2 (inv_mem (pow_mem hx3 2))) hx4)
    have e : x1⁻¹ * x2⁻¹ * x3 ^ 2 * x4⁻¹ * (x2 * (x3 ^ 2)⁻¹ * x4) = x1⁻¹ := by
      calc x1⁻¹ * x2⁻¹ * x3 ^ 2 * x4⁻¹ * (x2 * (x3 ^ 2)⁻¹ * x4)
          = x1⁻¹ * (x2⁻¹ * x2) * (x3 ^ 2 * (x3 ^ 2)⁻¹) * (x4⁻¹ * x4) := by ac_rfl
        _ = x1⁻¹ := by simp
    rw [e] at this
    simpa using this
  exact ⟨hx1, hx2, hx3, hx4⟩

theorem d4t2sp_prod_d4 {M : Type*} [CommMonoid M] [Fintype ↥(d4Nodes Tag.E6)]
    (f : Fin Tag.E6.rank → M) :
    ∏ j : ↥(d4Nodes Tag.E6), f j = f ⟨1, by decide⟩ * f ⟨2, by decide⟩ * f ⟨3, by decide⟩ *
      f ⟨4, by decide⟩ := by
  have hs : ∀ x : Fin Tag.E6.rank, x ∈ ({⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
      ⟨4, by decide⟩} : Finset (Fin Tag.E6.rank)) ↔ x ∈ d4Nodes Tag.E6 := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, d4Nodes, Set.mem_setOf_eq, Fin.ext_iff]
    omega
  rw [← Finset.prod_subtype _ hs f]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, mul_assoc, mul_assoc]

theorem d4t2sp_cartan_values :
    Tag.E6.cartan ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨2, by decide⟩ ⟨0, by decide⟩ = -1 ∧
    Tag.E6.cartan ⟨3, by decide⟩ ⟨0, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨4, by decide⟩ ⟨0, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨1, by decide⟩ ⟨5, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨2, by decide⟩ ⟨5, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨3, by decide⟩ ⟨5, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨4, by decide⟩ ⟨5, by decide⟩ = -1 ∧
    Tag.E6.cartan ⟨1, by decide⟩ ⟨2, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨2, by decide⟩ ⟨2, by decide⟩ = 2 ∧
    Tag.E6.cartan ⟨3, by decide⟩ ⟨2, by decide⟩ = -1 ∧
    Tag.E6.cartan ⟨4, by decide⟩ ⟨2, by decide⟩ = 0 ∧
    Tag.E6.cartan ⟨1, by decide⟩ ⟨3, by decide⟩ = -1 ∧
    Tag.E6.cartan ⟨2, by decide⟩ ⟨3, by decide⟩ = -1 ∧
    Tag.E6.cartan ⟨3, by decide⟩ ⟨3, by decide⟩ = 2 ∧
    Tag.E6.cartan ⟨4, by decide⟩ ⟨3, by decide⟩ = -1 := by
  decide

theorem d4t2sp_coords_fixed [Fintype ↥(d4Nodes Tag.E6)] {a : ↥(d4Nodes Tag.E6) → Lˣ}
    (h : ∀ i : Fin Tag.E6.rank,
      σ ((∏ j : ↥(d4Nodes Tag.E6), a j ^ Tag.E6.cartan j i : Lˣ) : L) =
        ((∏ j : ↥(d4Nodes Tag.E6), a j ^ Tag.E6.cartan j i : Lˣ) : L))
    (j : ↥(d4Nodes Tag.E6)) : σ (a j : L) = (a j : L) := by
  classical
  obtain ⟨c10, c20, c30, c40, c15, c25, c35, c45, c12, c22, c32, c42, c13, c23, c33, c43⟩ :=
    d4t2sp_cartan_values
  let K : Subgroup Lˣ :=
    { carrier := {u | σ (u : L) = (u : L)}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at hx hy ⊢
        rw [hx, hy]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
        rw [hx] }
  have hK : ∀ u : Lˣ, u ∈ K ↔ σ (u : L) = (u : L) := fun u => Iff.rfl
  set a' : Fin Tag.E6.rank → Lˣ :=
    fun k => if hk : k ∈ d4Nodes Tag.E6 then a ⟨k, hk⟩ else 1 with ha'
  have ha'a : ∀ j : ↥(d4Nodes Tag.E6), a' j = a j := fun j => by simp [ha', j.2]
  have hprod : ∀ i : Fin Tag.E6.rank, (∏ j : ↥(d4Nodes Tag.E6), a j ^ Tag.E6.cartan j i : Lˣ) =
      a' ⟨1, by decide⟩ ^ Tag.E6.cartan ⟨1, by decide⟩ i *
      a' ⟨2, by decide⟩ ^ Tag.E6.cartan ⟨2, by decide⟩ i *
      a' ⟨3, by decide⟩ ^ Tag.E6.cartan ⟨3, by decide⟩ i *
      a' ⟨4, by decide⟩ ^ Tag.E6.cartan ⟨4, by decide⟩ i := by
    intro i
    calc (∏ j : ↥(d4Nodes Tag.E6), a j ^ Tag.E6.cartan j i : Lˣ)
        = ∏ j : ↥(d4Nodes Tag.E6), a' j ^ Tag.E6.cartan j i :=
          Finset.prod_congr rfl (fun j _ => by rw [ha'a])
      _ = _ := d4t2sp_prod_d4 (fun k => a' k ^ Tag.E6.cartan k i)
  have h0 := h ⟨0, by decide⟩
  have h5 := h ⟨5, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  rw [hprod, c10, c20, c30, c40] at h0
  rw [hprod, c15, c25, c35, c45] at h5
  rw [hprod, c12, c22, c32, c42] at h2
  rw [hprod, c13, c23, c33, c43] at h3
  simp only [zpow_zero, zpow_neg_one, zpow_ofNat, pow_zero, mul_one, one_mul] at h0 h5 h2 h3
  obtain ⟨k1, k2, k3, k4⟩ := d4t2sp_fixed_of_relations K ((hK _).2 h0) ((hK _).2 h5)
    ((hK _).2 h2) ((hK _).2 h3)
  obtain ⟨k, hk⟩ := j
  have hk' : 1 ≤ k.val ∧ k.val ≤ 4 := hk
  have hcases : k = ⟨1, by decide⟩ ∨ k = ⟨2, by decide⟩ ∨ k = ⟨3, by decide⟩ ∨
      k = ⟨4, by decide⟩ := by
    simp only [Fin.ext_iff]
    omega
  have haj : a ⟨k, hk⟩ = a' k := (ha'a ⟨k, hk⟩).symm
  rw [haj]
  rcases hcases with rfl | rfl | rfl | rfl
  exacts [(hK _).1 k1, (hK _).1 k2, (hK _).1 k3, (hK _).1 k4]

open CFSG.HardMathSupport.Lang.TwE6Step3 in
theorem d4t2sp_exists_fixed_coords {t : ModGL Tag.E6 L}
    (ht : t ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (hfix : frobGL σ t = t) :
    ∃ a : ↥(d4Nodes Tag.E6) → Lˣ,
      supportedTorusHom Tag.E6 L (d4Nodes Tag.E6) a = t ∧ ∀ j, σ (a j : L) = (a j : L) := by
  classical
  haveI : Fintype ↥(d4Nodes Tag.E6) := Fintype.ofFinite _
  have htT : t ∈ torusGroup Tag.E6 L := (Subgroup.mem_inf.1 ht).1
  rw [torusGroup_inf_rootSpan_parabolicRoots] at ht
  obtain ⟨a, rfl⟩ := ht
  refine ⟨a, rfl, d4t2sp_coords_fixed σ (fun i => ?_)⟩
  have h1 := d4t2sp_torusRootChar_fixed σ htT hfix (isRoot_single Tag.E6 i)
  rw [torusRootChar_supportedTorusHom _ a (isRoot_single Tag.E6 i)] at h1
  have hs : ∀ j : ↥(d4Nodes Tag.E6),
      ∑ k, Tag.E6.cartan j k * (Pi.single i 1 : Fin Tag.E6.rank → ℤ) k = Tag.E6.cartan j i :=
    fun j => by
      rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]
  simpa only [hs] using h1

theorem d4t2sp_torusElt_mem {C : Subgroup (ModGL Tag.E6 L)}
    (hC : ∀ γ ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), ∀ c : L, σ c = c →
      pinnedX Tag.E6 L γ c ∈ C)
    {j : Fin Tag.E6.rank} (hj : j ∈ d4Nodes Tag.E6) {c : Lˣ} (hc : σ (c : L) = (c : L)) :
    torusElt Tag.E6 L j c ∈ C := by
  have hx : ∀ u : L, σ u = u → xUnit Tag.E6 L j u ∈ C := fun u hu => by
    rw [← pinnedX_single]
    exact hC _ (single_mem_parabolicRoots hj) u hu
  have hy : ∀ u : L, σ u = u → yUnit Tag.E6 L j u ∈ C := fun u hu => by
    rw [← pinnedX_neg_single]
    exact hC _ (neg_mem_parabolicRoots (single_mem_parabolicRoots hj)) u hu
  have hw : ∀ t : Lˣ, σ (t : L) = (t : L) → weylElt Tag.E6 L j t ∈ C := by
    intro t ht
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    refine mul_mem (mul_mem (hx _ ht) (hy _ ?_)) (hx _ ht)
    simp [ht]
  have h1 : σ (((-1 : Lˣ)) : L) = ((-1 : Lˣ) : L) := by simp
  exact mul_mem (hw c hc) (hw (-1) h1)

open CFSG.HardMathSupport.Lang.TwE6Step3 in
theorem d4t2sp_native_torus_mem {C : Subgroup (ModGL Tag.E6 L)}
    (hC : ∀ γ ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), ∀ c : L, σ c = c →
      pinnedX Tag.E6 L γ c ∈ C)
    {t : ModGL Tag.E6 L}
    (ht : t ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (hfix : frobGL σ t = t) : t ∈ C := by
  classical
  obtain ⟨a, rfl, ha⟩ := d4t2sp_exists_fixed_coords σ ht hfix
  rw [supportedTorusHom_apply]
  exact Subgroup.noncommProd_mem _ _ (fun j _ => d4t2sp_torusElt_mem σ hC j.2 (ha j))

open CFSG.HardMathSupport.Lang.TwE6Step3 in
theorem d4t2sp_torus_fixed_mem {v : WeylGroup Tag.E6} {C : Subgroup (ModGL Tag.E6 L)}
    (hC : ∀ γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6), ∀ c : L, σ c = c →
      pinnedX Tag.E6 L γ c ∈ C)
    {t : ModGL Tag.E6 L} (htT : t ∈ torusGroup Tag.E6 L)
    (htS : t ∈ rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (hfix : frobGL σ t = t) : t ∈ C := by
  set n := canonicalRep (coxeterSystem Tag.E6) L v with hn
  have hnfix : frobGL σ n = n := entrywise_canonicalRep σ v
  have htm : n⁻¹ * t * n ∈ torusGroup Tag.E6 L ⊓
      rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
    refine Subgroup.mem_inf.2 ⟨canonicalRep_inv_conj_mem_torusGroup v htT, ?_⟩
    refine canonicalRep_inv_conj_mem_rootSpan (S := (fun α => v • α) '' parabolicRoots Tag.E6
      (d4Nodes Tag.E6)) (S' := parabolicRoots Tag.E6 (d4Nodes Tag.E6)) v ?_ htS
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul hα.1 v, by rw [inv_smul_smul]; exact hα⟩
  have hfixm : frobGL σ (n⁻¹ * t * n) = n⁻¹ * t * n := by
    rw [map_mul, map_mul, map_inv, hnfix, hfix]
  have hC' : ∀ γ ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), ∀ c : L, σ c = c →
      pinnedX Tag.E6 L γ c ∈ C.comap (MulAut.conj n).toMonoidHom := by
    intro γ hγ c hc
    obtain ⟨ε, hε1, hε⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L v hγ.1
    have hεσ : σ ε = ε := sq_eq_one_fixed σ hε1
    rw [Subgroup.mem_comap]
    show n * pinnedX Tag.E6 L γ c * n⁻¹ ∈ C
    rw [hε c]
    exact hC _ ⟨γ, hγ, rfl⟩ _ (by rw [map_mul, hεσ, hc])
  have := d4t2sp_native_torus_mem σ hC' htm hfixm
  rw [Subgroup.mem_comap] at this
  have e : (MulAut.conj n).toMonoidHom (n⁻¹ * t * n) = t := by
    show n * (n⁻¹ * t * n) * n⁻¹ = t
    group
  rwa [e] at this

theorem d4t2sp_fixed_mem_CQ {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {i : KernelComponent χ} {v : WeylGroup Tag.E6}
    (hΨ : componentRoots χ i = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    {y : ModGL Tag.E6 L} (hy : y ∈ rootSpan Tag.E6 L (componentRoots χ i))
    (hfix : frobGL σ y = y) : y ∈ CQ σ i := by
  have hy' : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    unfold unionRootSpan
    rw [unionRoots_singleton]
    exact hy
  obtain ⟨t, ht, x, hx, hyt, hft⟩ := exists_decomp (σ := σ) (i := i) hy' (one_mem _)
    (by rw [hfix, one_mul])
  have htT : t ∈ torusGroup Tag.E6 L := (Subgroup.mem_inf.1 ht).2
  have htS : t ∈ rootSpan Tag.E6 L (componentRoots χ i) := by
    have h := (Subgroup.mem_inf.1 ht).1
    unfold unionRootSpan at h
    rwa [unionRoots_singleton] at h
  have htC : t ∈ CQ σ i := by
    refine d4t2sp_torus_fixed_mem σ (v := v) (C := CQ σ i) (fun γ hγ c hc => ?_) htT
      (hΨ ▸ htS) (by rw [hft, one_mul])
    exact pinnedX_mem_CQ (by rw [unionRoots_singleton, hΨ]; exact hγ) hc
  rw [hyt]
  exact mul_mem htC hx

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
