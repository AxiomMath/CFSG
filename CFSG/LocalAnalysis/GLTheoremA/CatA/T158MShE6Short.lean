module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgE6Res2
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Orbit
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem e6ShortOrbit_holds :
    E6ShortOrbit := by
  intro L _ _ _ p₀ S a hT hap h1 i hqs y hyC _ hyR hyM
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  obtain ⟨ζ, w₀, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3L hap
  have hcnt := ncard_kernelRoots_eq_cntB hζ w₀ hchar
  rcases kernelCount_cases_of_kac_E6 m0 m1 m2 m3 m4 m5 hsum with hconn | h24 | h18 | h72
  ·
    exfalso
    have hk : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 30, 40} : Set ℕ) := by
      rw [hcnt]
      rcases hconn with h | h | h <;> simp [h]
    have hW := e6_stab_le_kernelReflectionGroup_of_conn a hap hk
    rw [toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 L a hW] at hyC
    exact hyM hyC
  ·
    exact Or.inr (hcnt.trans h24)
  rotate_left
  ·
    exfalso
    obtain ⟨x, hx, -, hncard, -, -⟩ := hcl i
    exact h1 (rootDiagUnit_eq_one_of_ncard i (by rw [hncard, h72 x hx]; decide))
  have h18' : (kernelRoots (rootCharHom a)).ncard = 18 := hcnt.trans h18
  obtain ⟨c, hc, -⟩ := kernel_classes_of_ncard_eighteen h3L hap h18'
  rcases orbit_dichotomy S hT hc with ⟨j₀, hj₀⟩ | hall
  swap
  · exact Or.inl ⟨h18', (hall i).1⟩
  exfalso
  apply hyM
  have hnab : ¬ ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      ∀ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, x * z = z * x := by
    intro hcomm
    obtain ⟨-, -, c', d', hcd⟩ := hqs
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c'
    obtain ⟨d', rfl⟩ := QuotientGroup.mk_surjective d'
    apply hcd
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcomm _ c'.2 _ d'.2)
  have hRX : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) :=
    (Subgroup.commutator_le_self _).trans inf_le_left
  have hRF : ∀ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, S.D.step r = r := by
    intro r hr
    have hrM : r ∈ S.D.model :=
      Subgroup.commutator_le_self _ (((Subgroup.commutator_le_self _).trans inf_le_right) hr)
    exact (S.D.mem_model.1 hrM).2
  have hyR' : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj y).toMonoidHom =
      rationalComponent S.ρ S.Γ (rootCharHom a) i := hyR
  have hCy : ∀ x ∈ Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)),
      y * x * y⁻¹ ∈ Subgroup.centralizer
        (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro r hr
    rw [← hyR'] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have hxr := hx r' hr'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * r' * y⁻¹ * (y * x * y⁻¹) = y * (r' * x) * y⁻¹ := by group
      _ = y * (x * r') * y⁻¹ := by rw [hxr]
      _ = y * x * y⁻¹ * (y * r' * y⁻¹) := by group
  have hstepC : ∀ T : Subgroup (ModGL Tag.E6 L),
      T ≤ Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) →
      T.map S.D.step ≤
        Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
    rintro T hT _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h := congrArg S.D.step (Subgroup.mem_centralizer_iff.1 (hT hx) r hr)
    rwa [map_mul, map_mul, hRF r hr] at h
  obtain ⟨w, hwa, h, hh, u, hu, v, hv, hy⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 L a).1 _ hyC
  have hm₁ : h * u ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right (rootSpan_mono
      Set.inter_subset_left hu))
  have hm₂ : v ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  set n := canonicalRep (coxeterSystem Tag.E6) L w
  have hwχ : IsCharConj (rootCharHom a) (rootCharHom a) w := by
    intro x
    have hw' : w⁻¹ ∈ rootCharStabilizerSubgroup a := (rootCharStabilizerSubgroup a).inv_mem hwa
    exact (hw' x).symm
  have himgw : ∀ k : KernelComponent (rootCharHom a), ∃ k' : KernelComponent (rootCharHom a),
      (fun α => w • α) '' componentRoots (rootCharHom a) k = componentRoots (rootCharHom a) k' := by
    intro k
    obtain ⟨k', hk'⟩ := KacData.componentRoots_smul_of_isCharConj hwχ k
    refine ⟨k', ?_⟩
    rw [hk', Set.image_image]
    simp
  have hfwd : ∀ k k' : KernelComponent (rootCharHom a),
      (fun α => w • α) '' componentRoots (rootCharHom a) k = componentRoots (rootCharHom a) k' →
      ∀ x ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) k),
        y * x * y⁻¹ ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) k') := by
    intro k k' hkk' x hx
    have htrans := (canonical_weyl_root_transport Tag.E6 L).1 w (componentRoots (rootCharHom a) k)
      (fun α hα => hα.1.1)
    rw [hkk'] at htrans
    have hx1 : v * x * v⁻¹ ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) k) :=
      (mem_componentRootSpan_iff_conj_of_mem hm₂ k x).1 hx
    have hx2 : n * (v * x * v⁻¹) * n⁻¹ ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) k') := by
      have := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hx1
      rw [htrans] at this
      simpa [MulAut.conj_apply] using this
    have hx3 := (mem_componentRootSpan_iff_conj_of_mem hm₁ k' _).1 hx2
    have e : y * x * y⁻¹ = h * u * (n * (v * x * v⁻¹) * n⁻¹) * (h * u)⁻¹ := by
      rw [hy]
      group
    rw [e]
    exact hx3
  have hbwd : ∀ k k' : KernelComponent (rootCharHom a),
      (fun α => w • α) '' componentRoots (rootCharHom a) k = componentRoots (rootCharHom a) k' →
      ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) k'),
        ∃ x ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) k), y * x * y⁻¹ = z := by
    intro k k' hkk' z hz
    have htrans := (canonical_weyl_root_transport Tag.E6 L).1 w (componentRoots (rootCharHom a) k)
      (fun α hα => hα.1.1)
    rw [hkk'] at htrans
    have hz1 : (h * u)⁻¹ * z * (h * u) ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) k') := by
      refine (mem_componentRootSpan_iff_conj_of_mem hm₁ k' _).2 ?_
      have e : h * u * ((h * u)⁻¹ * z * (h * u)) * (h * u)⁻¹ = z := by group
      rw [e]
      exact hz
    rw [← htrans] at hz1
    obtain ⟨g, hg, hge⟩ := hz1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hge
    refine ⟨v⁻¹ * g * v, ?_, ?_⟩
    · refine (mem_componentRootSpan_iff_conj_of_mem hm₂ k _).2 ?_
      have e : v * (v⁻¹ * g * v) * v⁻¹ = g := by group
      rw [e]
      exact hg
    · rw [hy]
      calc h * u * n * v * (v⁻¹ * g * v) * (h * u * n * v)⁻¹ =
          h * u * (n * g * n⁻¹) * (h * u)⁻¹ := by group
        _ = z := by rw [hge]; group
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : KernelComponent (rootCharHom a),
      (fun α => w • α) '' componentRoots (rootCharHom a) k₀ = componentRoots (rootCharHom a) k₀ := by
    by_cases hs : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i
    ·
      have hRi : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
        refine hRX.trans (rootSpan_mono ?_)
        rintro _ ⟨k, δ, hδ, rfl⟩
        induction k with
        | zero => exact hδ
        | succ k ih =>
          rw [Function.iterate_succ_apply', ← hs]
          exact Set.mem_image_of_mem _ ih
      obtain ⟨i', hi'⟩ := himgw i
      refine ⟨i, ?_⟩
      have hRi' : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) i') := by
        intro r hr
        rw [← hyR'] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        exact hfwd i i' hi' x (hRi hx)
      have hii : i' = i := by
        by_contra hne
        apply hnab
        intro x hx z hz
        have hxC := componentRootSpan_le_centralizer L hne (hRi' hx)
        exact (Subgroup.mem_centralizer_iff.1 hxC z (hRi hz)).symm
      rw [hi', hii]
    ·
      have hj₀s : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) j₀ =
          componentRoots (rootCharHom a) j₀ := by
        have h := (outer_componentOrbitLength_spec S hT j₀).2.1
        rwa [hj₀, Function.iterate_one] at h
      obtain ⟨m, hm, hm', -, hmj, hij, hall3⟩ := e6_rho_swap_of_stable S h3L hT hap h18' hj₀s hs
      refine ⟨j₀, ?_⟩
      have hrat : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i,
          γ ∈ componentRoots (rootCharHom a) i ∨ γ ∈ componentRoots (rootCharHom a) m := by
        rintro _ ⟨k, δ, hδ, rfl⟩
        induction k with
        | zero => exact Or.inl hδ
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          rcases ih with h | h
          · right
            rw [← hm]
            exact Set.mem_image_of_mem _ h
          · left
            rw [← hm']
            exact Set.mem_image_of_mem _ h
      have hXle : ∀ T : Subgroup (ModGL Tag.E6 L),
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ≤ T →
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) m) ≤ T →
          rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ T := by
        intro T hiT hmT
        refine hRX.trans (iSup₂_le fun γ hγ => ?_)
        rcases hrat γ hγ with h | h
        · exact le_trans (show rootSubgroup Tag.E6 L γ ≤
            rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) from le_iSup₂_of_le γ h le_rfl) hiT
        · exact le_trans (show rootSubgroup Tag.E6 L γ ≤
            rootSpan Tag.E6 L (componentRoots (rootCharHom a) m) from le_iSup₂_of_le γ h le_rfl) hmT
      have hj₀C : rootSpan Tag.E6 L (componentRoots (rootCharHom a) j₀) ≤
          Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
        rw [Subgroup.le_centralizer_iff]
        exact hXle _ (componentRootSpan_le_centralizer L hij) (componentRootSpan_le_centralizer L hmj)
      have hFim : (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i)).map S.D.step =
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) m) := by
        rw [map_rootSpan_step S _ (fun γ hγ => hγ.1.1), hm]
      have hFmi : (rootSpan Tag.E6 L (componentRoots (rootCharHom a) m)).map S.D.step =
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
        rw [map_rootSpan_step S _ (fun γ hγ => hγ.1.1), hm']
      have hiC : ¬ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ≤
          Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
        intro hiC
        have hmC : rootSpan Tag.E6 L (componentRoots (rootCharHom a) m) ≤
            Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
          rw [← hFim]
          exact hstepC _ hiC
        apply hnab
        intro x hx z hz
        exact Subgroup.mem_centralizer_iff.1 (hXle _ hiC hmC hz) x hx
      have hmC : ¬ rootSpan Tag.E6 L (componentRoots (rootCharHom a) m) ≤
          Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
        intro hmC
        apply hiC
        rw [← hFmi]
        exact hstepC _ hmC
      obtain ⟨k, hk⟩ := himgw j₀
      have hkC : rootSpan Tag.E6 L (componentRoots (rootCharHom a) k) ≤
          Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := hbwd j₀ k hk z hz
        exact hCy x (hj₀C hx)
      rcases hall3 k with h | h | h
      · rw [h] at hkC
        exact absurd hkC hiC
      · rw [h] at hkC
        exact absurd hkC hmC
      · rw [hk, h]
  have hwk : ∀ α ∈ componentRoots (rootCharHom a) k₀, w • α ∈ componentRoots (rootCharHom a) k₀ := by
    intro α hα
    rw [← hk₀]
    exact ⟨α, hα, rfl⟩
  have hwS := mem_kernelReflectionGroup_of_mapsTo_a2CubeClass h3L hap h18' hwa k₀ hwk
  have hnM : n ∈ toralRootGroup Tag.E6 L a := by
    have hker := kernelReflectionGroup_le_ker (K := L) a
      (x := (⟨w, hwa⟩ : rootCharStabilizerSubgroup a)) (Subgroup.mem_subgroupOf.2 hwS)
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  rw [hy]
  exact mul_mem (mul_mem hm₁ hnM) hm₂

end CFSG.LocalAnalysis.GLTheoremA.T158

end
