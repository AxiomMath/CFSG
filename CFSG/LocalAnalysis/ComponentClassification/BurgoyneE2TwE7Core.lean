module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Layer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Four
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CentData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Q3 CFSG.LieType.HighestRoot CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ComponentClassification.CatLeafProof
open scoped commutatorElement Pointwise


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_twisted_layer (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    {x : ModGL .E7 k} {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords) (hl0 : l ≠ [])
    {g₁ : ModGL .E7 k} (hg₁ : g₁ ∈ adjointGroup .E7 k)
    (hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 r.mask)))
    (hcoc : g₁ * (frobTwistGL .E7 k p e 1 g₁)⁻¹ = wordWeylMatrix .E7 k l) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (c u : ModGL .E7 k),
      Exc3Frob D c ∧ D.e = e ∧ D.χ = signMaskChar .E7 r.mask ∧
      (∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 l) 1 γ)) ∧
      Subsingleton (KernelComponent D.χ) ∧ CFSG.IsQuasisimple D.orbitGroup ∧
      u ∈ torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (signMaskChar .E7 r.mask)) ∧
      D.orbitGroup.map (MulAut.conj u).toMonoidHom ≤
        (twCent p k e x).map (MulAut.conj g₁).toMonoidHom ∧
      ∀ y ∈ (twCent p k e x).map (MulAut.conj g₁).toMonoidHom,
        (D.orbitGroup.map (MulAut.conj u).toMonoidHom).map (MulAut.conj y).toMonoidHom =
          D.orbitGroup.map (MulAut.conj u).toMonoidHom := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  obtain ⟨D, c, u, hfrob, hDe, hDχ, hDθ, hsub, hqs, hu, hconj⟩ :=
    exists_twisted_datum hp2 he hk hr hl hl0
  refine ⟨D, c, u, hfrob, hDe, hDχ, hDθ, hsub, hqs, hu, ?_⟩
  set F := frobTwistGL .E7 k p e 1 with hF
  set R := fixedPointsIn (adjointGroup .E7 k) F with hR
  set N := wordWeylMatrix .E7 k l with hN
  set F₀ := frobTwistGL .E7 k p e (N * 1) with hF₀
  set χ := signMaskChar .E7 r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk2 χ
  set M := torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots χ) with hM
  set X₀ := fixedPointsIn M F₀ with hX₀
  have hF₀F : ∀ w, F₀ w = N * F w * N⁻¹ := by
    intro w
    simp only [hF₀, hF, frobTwistGL_apply, mul_one, one_mul, inv_one]
  have hFg₁ : F g₁ = N⁻¹ * g₁ := by
    have h1 : (F g₁)⁻¹ = g₁⁻¹ * N := by rw [← hcoc]; group
    calc F g₁ = ((F g₁)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (g₁⁻¹ * N)⁻¹ := by rw [h1]
      _ = N⁻¹ * g₁ := by group
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hMeq : M = toralRootGroup .E7 k a := by rw [hM, toralRootGroup, hker]
  set G := twCent p k e x with hG
  set φ := (MulAut.conj g₁).toMonoidHom with hφ
  have hφapp : ∀ y, φ y = g₁ * y * g₁⁻¹ := fun y => rfl
  have hYn : ∀ y ∈ G.map φ, ∀ v ∈ X₀, y * v * y⁻¹ ∈ X₀ := by
    rintro _ ⟨y, hy, rfl⟩ v hv
    obtain ⟨hZ, hFy⟩ := conj_mem_of_mem_twCent hg₁ hg₁x hcoc hy
    obtain ⟨hvM, hvF⟩ := mem_fixedPointsIn.1 hv
    have hnorm := (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hZ) v).1
      (by rw [← hMeq]; exact hvM)
    refine mem_fixedPointsIn.2 ⟨by rw [hMeq]; exact hnorm, ?_⟩
    rw [hφapp, map_mul, map_mul, map_inv, hFy, hvF]
  have hMG : M ≤ adjointGroup .E7 k :=
    sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup k _)
  have hCmX : ∀ c' ∈ D.orbitGroup, u * c' * u⁻¹ ∈ X₀ := by
    intro c' hc'
    have h1 : c' ∈ D.totalFixedGroup.map (adjointGroup .E7 k).subtype :=
      exc3_fixedGroup_le_totalFixedGroup D (exc3_orbitGroup_le_fixedGroup D hc')
    have h2 : u * c' * u⁻¹ ∈ (D.totalFixedGroup.map (adjointGroup .E7 k).subtype).map
        (MulAut.conj u).toMonoidHom := Subgroup.mem_map_of_mem _ h1
    rw [hconj] at h2
    exact h2
  set P₁ := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hP₁
  set P := P₁.map (MulAut.conj g₁⁻¹).toMonoidHom with hP
  have hperf : ⁅D.orbitGroup, D.orbitGroup⁆ = D.orbitGroup := Subgroup.isPerfect_iff.1 hqs.1
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, hP₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hperf]
  have hP₁X : ∀ w ∈ P₁, w ∈ X₀ := by
    rintro _ ⟨c', hc', rfl⟩
    exact hCmX c' hc'
  have hPR : P ≤ R := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwM, hwF⟩ := mem_fixedPointsIn.1 (hP₁X w hw)
    have hFw : F w = N⁻¹ * w * N := by
      have h := hF₀F w
      rw [hwF] at h
      calc F w = N⁻¹ * (N * F w * N⁻¹) * N := by group
        _ = N⁻¹ * w * N := by rw [← h]
    refine mem_fixedPointsIn.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem hg₁) (hMG hwM)) hg₁
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [map_mul, map_mul, map_inv, hFg₁, hFw]
      group
  have hPG : P ≤ G := by
    have hPR' : P ≤ ⁅R, R⁆ := by
      rw [← hPperf]
      exact Subgroup.commutator_mono hPR hPR
    refine le_inf hPR' ?_
    rintro _ ⟨w, hw, rfl⟩
    have hwM := (mem_fixedPointsIn.1 (hP₁X w hw)).1
    have hwZ := toralRootGroup_le a (hMeq ▸ hwM)
    have hd := (mem_toralCentralizer.1 hwZ).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxd : x = g₁⁻¹ * rootDiagUnit .E7 a * g₁ := by rw [← hg₁x]; group
    have hdw : rootDiagUnit .E7 a * w = w * rootDiagUnit .E7 a := by
      calc rootDiagUnit .E7 a * w = (rootDiagUnit .E7 a * w * (rootDiagUnit .E7 a)⁻¹) *
          rootDiagUnit .E7 a := by group
        _ = w * rootDiagUnit .E7 a := by rw [hd]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hxd]
    calc g₁⁻¹ * w * g₁⁻¹⁻¹ * (g₁⁻¹ * rootDiagUnit .E7 a * g₁) =
        g₁⁻¹ * (w * rootDiagUnit .E7 a) * g₁ := by group
      _ = g₁⁻¹ * (rootDiagUnit .E7 a * w) * g₁ := by rw [hdw]
      _ = (g₁⁻¹ * rootDiagUnit .E7 a * g₁) * (g₁⁻¹ * w * g₁⁻¹⁻¹) := by group
  refine ⟨fun w hw => ⟨g₁⁻¹ * w * g₁, hPG ⟨w, hw, rfl⟩, ?_⟩, fun y hy => ?_⟩
  · rw [hφapp]
    group
  have hX0 : ∀ y ∈ G.map φ, X₀.map (MulAut.conj y).toMonoidHom = X₀ := by
    intro y hy
    refine le_antisymm ?_ fun v hv => ⟨y⁻¹ * v * y⁻¹⁻¹, hYn _ (inv_mem hy) v hv, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact hYn y hy v hv
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hCeq : P₁ = ⁅⁅X₀, X₀⁆, ⁅X₀, X₀⁆⁆ := by
    rw [hP₁, orbitGroup_eq_derived D hqs, Subgroup.map_commutator, Subgroup.map_commutator,
      hconj]
  rw [hCeq, Subgroup.map_commutator, Subgroup.map_commutator, hX0 y hy]

theorem twisted_two_oddNormal_eq_bot (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    {x : ModGL .E7 k} {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps) (hm : r.mask = 2)
    {g₁ : ModGL .E7 k} (hg₁ : g₁ ∈ adjointGroup .E7 k)
    (hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 r.mask)))
    (hcoc : g₁ * (frobTwistGL .E7 k p e 1 g₁)⁻¹ = wordWeylMatrix .E7 k e7Word2_1)
    (N : Subgroup (ModGL .E7 k)) (hN : N ≤ twCent p k e x)
    (hNn : ∀ y ∈ twCent p k e x, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  classical
  obtain ⟨D, c, u, hfrob, hDe, hDχ, hDθ, hsub, hqs, hu, hCY, hYn⟩ := exists_twisted_layer hp2 he hk
    hr (e7Word2_1_mem_omegaWords hr (Or.inl hm)) e7Word2_1_ne_nil hg₁ hg₁x hcoc
  have hχ2 : D.χ = signMaskChar .E7 2 := by rw [hDχ, hm]
  have hq := three_le_q D
  set C' := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC'
  set φ := (MulAut.conj g₁).toMonoidHom with hφ
  set Y := (twCent p k e x).map φ with hY
  set N' := N.map φ with hN'
  have hMG : torusGroup .E7 k ⊔ rootSpan .E7 k (kernelRoots (signMaskChar .E7 r.mask)) ≤
      adjointGroup .E7 k := sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup k _)
  have huG : u ∈ adjointGroup .E7 k := hMG hu
  have hYG : ∀ y ∈ Y, y ∈ adjointGroup .E7 k := by
    rintro _ ⟨y, hy, rfl⟩
    have hyR := (Subgroup.commutator_le_of_le le_rfl le_rfl :
      ⁅fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1),
        fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)⁆ ≤
          fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1)) (Subgroup.mem_inf.1 hy).1
    exact mul_mem (mul_mem hg₁ (mem_fixedPointsIn.1 hyR).1) (inv_mem hg₁)
  have hN'Y : N' ≤ Y := Subgroup.map_mono hN
  have hN'n : ∀ y ∈ Y, ∀ n ∈ N', y * n * y⁻¹ ∈ N' := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨n, hn, rfl⟩
    have h := Subgroup.mem_map_of_mem φ (hNn y hy n hn)
    rw [map_mul, map_mul, map_inv] at h
    exact h
  have hC'n : ∀ y ∈ Y, ∀ w ∈ C', y * w * y⁻¹ ∈ C' := by
    intro y hy w hw
    have h := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hw
    rw [hYn y hy] at h
    exact h
  have hodd' : Odd (Nat.card N') := by
    rwa [← Nat.card_congr (N.equivMapOfInjective φ (MulAut.conj g₁).injective).toEquiv]
  have hordN : ∀ n ∈ N', Odd (orderOf n) := fun n hn => by
    have h1 : orderOf (⟨n, hn⟩ : N') ∣ Nat.card N' := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd' h1
  have hcent : ∀ z ∈ adjointGroup .E7 k, (∀ w ∈ C', z * w = w * z) → z ^ 2 = 1 := by
    intro z hz hzc
    have h1 : ∀ w ∈ D.orbitGroup, (u⁻¹ * z * u) * w = w * (u⁻¹ * z * u) := by
      intro w hw
      have h := hzc (u * w * u⁻¹) ⟨w, hw, rfl⟩
      calc u⁻¹ * z * u * w = u⁻¹ * (z * (u * w * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * w * u⁻¹) * z) * u := by rw [h]
        _ = w * (u⁻¹ * z * u) := by group
    have h2 := sq_eq_one_of_commute_orbitGroup_two (p := p) D hq hχ2 hDθ
      (mul_mem (mul_mem (inv_mem huG) hz) huG) h1
    calc z ^ 2 = u * ((u⁻¹ * z * u) * (u⁻¹ * z * u)) * u⁻¹ := by rw [sq]; group
      _ = 1 := by rw [← sq, h2]; group
  have hΔ : Pi.single (e7Node 4) 1 ∈ D.simpleRootsJ := by
    rw [simpleRootsJ_eq_simpleUnion, hχ2, simpleUnion_e7_two]
    exact ⟨3, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨w₀, hw₀, hw₀1, hw₀2⟩ := exists_involution_orbitGroup D hDθ hΔ
  have hqC' : CFSG.IsQuasisimple C' :=
    (isQuasisimple_congr (D.orbitGroup.equivMapOfInjective _
      (MulAut.conj u).injective)).1 hqs
  have hinter : ∀ n ∈ N', n ∈ C' → n = 1 := by
    intro n hn hnC
    set I : Subgroup C' := (N' ⊓ C').subgroupOf C' with hI_def
    have hI : I.Normal := ⟨fun i hi c => by
      obtain ⟨hi1, hi2⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hi)
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · exact hN'n _ (hCY c.2) _ hi1
      · exact mul_mem (mul_mem c.2 hi2) (inv_mem c.2)⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqC' hI with htop | hcen
    · exfalso
      have hw : u * w₀ * u⁻¹ ∈ N' := by
        have h1 : (⟨u * w₀ * u⁻¹, ⟨w₀, hw₀, rfl⟩⟩ : C') ∈ I := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h1)).1
      have h1 := hordN _ hw
      have h2 : (u * w₀ * u⁻¹) ^ 2 = 1 := by
        calc (u * w₀ * u⁻¹) ^ 2 = u * (w₀ * w₀) * u⁻¹ := by rw [sq]; group
          _ = 1 := by rw [hw₀2]; group
      have h3 := eq_one_of_sq_eq_one_of_odd h2 h1
      apply hw₀1
      calc w₀ = u⁻¹ * (u * w₀ * u⁻¹) * u := by group
        _ = 1 := by rw [h3]; group
    · have hnZ := hcen (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hn, hnC⟩) :
        (⟨n, hnC⟩ : C') ∈ I)
      have hzc : ∀ w ∈ C', n * w = w * n := fun w hw =>
        congrArg Subtype.val ((Subgroup.mem_center_iff.1 hnZ ⟨w, hw⟩).symm)
      exact eq_one_of_sq_eq_one_of_odd (hcent n (hYG n (hN'Y hn)) hzc) (hordN n hn)
  have hcomm : ∀ n ∈ N', ∀ w ∈ C', n * w = w * n := by
    intro n hn w hw
    have h1 : n * w * n⁻¹ * w⁻¹ ∈ N' := by
      have e : n * w * n⁻¹ * w⁻¹ = n * (w * n⁻¹ * w⁻¹) := by group
      rw [e]
      exact mul_mem hn (hN'n w (hCY hw) _ (inv_mem hn))
    have h2 : n * w * n⁻¹ * w⁻¹ ∈ C' := mul_mem (hC'n n (hN'Y hn) w hw) (inv_mem hw)
    have h3 := hinter _ h1 h2
    calc n * w = n * w * n⁻¹ * w⁻¹ * (w * n) := by group
      _ = w * n := by rw [h3, one_mul]
  have hN'bot : N' = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    exact eq_one_of_sq_eq_one_of_odd (hcent n (hYG n (hN'Y hn)) (hcomm n hn)) (hordN n hn)
  exact (Subgroup.map_eq_bot_iff_of_injective N (MulAut.conj g₁).injective).1 hN'bot

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
