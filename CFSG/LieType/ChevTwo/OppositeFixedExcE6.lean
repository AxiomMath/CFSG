module

public import CFSG.LieType.ChevTwo.OppositeFixedExcE78
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiag rootDiagUnit rootChar
  rootDiag_single rootChar_add rootChar_zero root_diagonal_conjugation end_ext_single)

variable {τ : Tag} {K : Type} [Field K]

section Cert


theorem coe_rootDiagUnitT (a : Fin τ.rank → Kˣ) :
    ((rootDiagUnit τ a : ModGL τ K) : Module.End K (RootModule τ K)) = rootDiag a :=
  rfl

theorem rootDiag_applyT (a : Fin τ.rank → Kˣ) (x : RootModule τ K) (b : Label τ) :
    rootDiag a x b = (rootChar a (labelWt τ b) : K) * x b := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hx, hy, mul_add]
  | single b' c =>
    have e : (Finsupp.single b' c : RootModule τ K) = c • Finsupp.single b' 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e, map_smul, rootDiag_single, smul_smul, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul, Finsupp.single_apply]
    split_ifs with h
    · subst h
      ring
    · simp

theorem rootDiag_mem_gradedT (a : Fin τ.rank → Kˣ) {J : Set (Fin τ.rank)} {d : ℤ}
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J d) :
    rootDiag a x ∈ parabolicGraded τ K J d := by
  rw [parabolicGraded_eq_supported] at hx ⊢
  rw [Finsupp.mem_supported K] at hx ⊢
  intro b hb
  refine hx (Finsupp.mem_support_iff.2 fun h0 => ?_)
  rw [Finset.mem_coe, Finsupp.mem_support_iff, rootDiag_applyT, h0, mul_zero] at hb
  exact hb rfl

theorem conj_rootDiagUnit_mem_rootSpanT (a : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {u : ModGL τ K} (hu : u ∈ rootSpan τ K S) :
    rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ ∈ rootSpan τ K S := by
  have h : (rootSpan τ K S).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = rootSpan τ K S :=
    map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a (hS α hα)
  have hmem : rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ ∈
      (rootSpan τ K S).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom := ⟨u, hu, rfl⟩
  rwa [h] at hmem

theorem conj_rootDiagUnit_mem_levelRadicalT (a : Fin τ.rank → Kˣ) {J : Set (Fin τ.rank)}
    {d : ℤ} {u : ModGL τ K} (hu : u ∈ levelRadical τ K J d) :
    rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ ∈ levelRadical τ K J d :=
  conj_rootDiagUnit_mem_rootSpanT a (fun _ hα => hα.1) hu

theorem conj_rootDiagUnit_mem_parabolicRadicalT (a : Fin τ.rank → Kˣ) {J : Set (Fin τ.rank)}
    {u : ModGL τ K} (hu : u ∈ parabolicRadical τ K J) :
    rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ ∈ parabolicRadical τ K J :=
  conj_rootDiagUnit_mem_rootSpanT a (fun _ hα => hα.1.1) hu

theorem conj_rootDiagUnit_mem_parabolicLeviT (a : Fin τ.rank → Kˣ) {J : Set (Fin τ.rank)}
    {m : ModGL τ K} (hm : m ∈ parabolicLevi τ K J) :
    rootDiagUnit τ a * m * (rootDiagUnit τ a)⁻¹ ∈ parabolicLevi τ K J := by
  have hle : parabolicLevi τ K J ≤
      (parabolicLevi τ K J).comap (MulAut.conj (rootDiagUnit τ a)).toMonoidHom := by
    refine sup_le (fun h hh => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_comap]
      change rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ ∈ _
      rw [conj_rootDiagUnit_of_mem_torusGroup a hh]
      exact Subgroup.mem_sup_left hh
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change rootDiagUnit τ a * xUnit τ K j c * (rootDiagUnit τ a)⁻¹ ∈ _
        rw [(root_diagonal_conjugation τ K a).1 j c]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, _, Or.inl rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change rootDiagUnit τ a * yUnit τ K j c * (rootDiagUnit τ a)⁻¹ ∈ _
        rw [(root_diagonal_conjugation τ K a).2.1 j c]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, _, Or.inr rfl⟩)
  exact hle hm

theorem conj_rootDiagUnit_mem_parabolicSubgroupT (a : Fin τ.rank → Kˣ) {J : Set (Fin τ.rank)}
    {g : ModGL τ K} (hg : g ∈ parabolicSubgroup τ K J) :
    rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ ∈ parabolicSubgroup τ K J := by
  obtain ⟨hQP, -, -, hMP, -, -, hdec, -⟩ := parabolic_root_radical_Levi_factors τ K J
  obtain ⟨qm, ⟨hq, hm, rfl⟩, -⟩ := hdec g hg
  have e : rootDiagUnit τ a * (qm.1 * qm.2) * (rootDiagUnit τ a)⁻¹ =
      (rootDiagUnit τ a * qm.1 * (rootDiagUnit τ a)⁻¹) *
        (rootDiagUnit τ a * qm.2 * (rootDiagUnit τ a)⁻¹) := by
    group
  rw [e]
  exact mul_mem (hQP (conj_rootDiagUnit_mem_parabolicRadicalT a hq))
    (hMP (conj_rootDiagUnit_mem_parabolicLeviT a hm))

theorem fieldAutHom_rootDiagUnitT (σ : RingAut K) (a : Fin τ.rank → Kˣ) :
    fieldAutHom τ K σ (rootDiagUnit τ a) =
      rootDiagUnit τ (fun i => Units.map (σ : K →+* K).toMonoidHom (a i)) :=
  Units.ext (by
    change entrywise (σ : K →+* K) (rootDiag a) = rootDiag _
    exact entrywise_rootDiag (σ : K →+* K) a)

@[expose] noncomputable def diagLayer (a : Fin τ.rank → Kˣ) (J : Set (Fin τ.rank)) (n : ℕ) :
    Layer τ K J n →* Layer τ K J n :=
  QuotientGroup.map _ _
    (((MulAut.conj (rootDiagUnit τ a)).toMonoidHom.comp
      (levelRadical τ K J (n + 1)).subtype).codRestrict
      (levelRadical τ K J (n + 1)) (fun u => conj_rootDiagUnit_mem_levelRadicalT a u.2))
    (fun u hu => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact conj_rootDiagUnit_mem_levelRadicalT a (Subgroup.mem_subgroupOf.1 hu))

theorem diagLayer_mk (a : Fin τ.rank → Kˣ) (J : Set (Fin τ.rank)) (n : ℕ)
    (u : levelRadical τ K J (n + 1)) :
    diagLayer a J n (QuotientGroup.mk u) = QuotientGroup.mk
      (⟨rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹, conj_rootDiagUnit_mem_levelRadicalT a u.2⟩ :
        levelRadical τ K J (n + 1)) :=
  rfl

theorem layerMap_rootDiagT (a : Fin τ.rank → Kˣ) (J : Set (Fin τ.rank)) (n : ℕ)
    (x : RootModule τ K) :
    layerMap J n (rootDiag a x) = diagLayer a J n (layerMap J n x) := by
  classical
  unfold layerMap
  rw [map_prod]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [rootDiag_applyT]
  unfold layerFactor
  split_ifs with h
  · exact congrArg QuotientGroup.mk
      (Subtype.ext (rootDiagUnit_conj_pinnedX a β.2 (x (Sum.inr β))).symm)
  · rw [map_one]

theorem rootPairing_rootDiagT (a : Fin τ.rank → Kˣ) (x y : RootModule τ K) :
    rootPairing τ K (rootDiag a x) (rootDiag a y) = rootPairing τ K x y := by
  rw [rootPairing_apply, rootPairing_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [rootDiag_applyT, rootDiag_applyT, mul_mul_mul_comm, ← Units.val_mul, ← rootChar_add]
  change ((rootChar a (β.1 + -β.1) : Kˣ) : K) * _ = _
  rw [add_neg_cancel, rootChar_zero, Units.val_one, one_mul]

theorem rootChar_weylT (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) (u : Fin τ.rank → ℤ) :
    rootChar (fun i => rootChar b (w • (Pi.single i 1 : Fin τ.rank → ℤ))) u =
      rootChar b (w • u) := by
  have hw : w • u = ∑ i, u i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [eq_sum_smul_single u]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (u i) _
  rw [hw, rootChar_sum]
  simp only [rootChar_zsmul]
  rfl

theorem exists_conj_canonicalRep_rootDiagUnitT (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    ∃ a : Fin τ.rank → Kˣ, canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ = rootDiagUnit τ a :=
  ⟨_, ((rootDiagUnit_eq_conj_canonicalRep_iff
    (fun i => rootChar b (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))) b w).2 fun v => by
      rw [rootChar_weylT, inv_smul_smul]).symm⟩

theorem eq_one_of_mem_parabolicRadical_of_preservesT {J : Set (Fin τ.rank)} {g : ModGL τ K}
    (hgQ : g ∈ parabolicRadical τ K J)
    (hgV : ∀ (d : ℤ) (x : RootModule τ K), x ∈ parabolicGraded τ K J d →
      (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d) : g = 1 := by
  refine Units.ext (end_ext_single fun b => ?_)
  set d := parabolicDegree τ J (labelWt τ b)
  have hbV : (Finsupp.single b 1 : RootModule τ K) ∈ parabolicGraded τ K J d := by
    rw [parabolicGraded_eq_supported]
    exact Finsupp.single_mem_supported K 1 rfl
  have hbF : (Finsupp.single b 1 : RootModule τ K) ∈ parabolicFiltration τ K J d := by
    rw [parabolicFiltration_eq_supported]
    exact Finsupp.single_mem_supported K 1 (show d ≤ d from le_rfl)
  have h1 := hgV d _ hbV
  have h2 := (parabolicRadical_unipotent hgQ d hbF).2
  have h3 : (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) - Finsupp.single b 1 ∈
      parabolicGraded τ K J d ⊓ parabolicFiltration τ K J (d + 1) :=
    Submodule.mem_inf.2 ⟨Submodule.sub_mem _ h1 hbV, h2⟩
  rw [parabolicGraded_inf_filtration_succ, Submodule.mem_bot, sub_eq_zero] at h3
  rw [h3, Units.val_one, Module.End.one_apply]

@[expose] def LeviT (J : Set (Fin τ.rank)) (s : GamL τ K) : Prop :=
  ∃ m ∈ parabolicLevi τ K J, ∃ a : Fin τ.rank → Kˣ, s.left = m * rootDiagUnit τ a

theorem smul_eq_of_leviT {s : GamL τ K} {m : ModGL τ K} {a : Fin τ.rank → Kˣ}
    (h : s.left = m * rootDiagUnit τ a) (x : RootModule τ K) :
    s • x = (m : Module.End K (RootModule τ K)) (rootDiag a (vtw s.right x)) := by
  rw [smul_def, h, Units.val_mul, Module.End.mul_apply, coe_rootDiagUnitT]

theorem smul_mem_gradedT {J : Set (Fin τ.rank)} {s : GamL τ K} (hs : LeviT J s) (d : ℤ)
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J d) :
    s • x ∈ parabolicGraded τ K J d := by
  obtain ⟨m, hm, a, ha⟩ := hs
  rw [smul_eq_of_leviT ha]
  exact parabolicLevi_preserves hm d (rootDiag_mem_gradedT a (vtw_mem_graded s.right hx))

theorem conjAct_eq_of_leviT {s : GamL τ K} {m : ModGL τ K} {a : Fin τ.rank → Kˣ}
    (h : s.left = m * rootDiagUnit τ a) (u : ModGL τ K) :
    conjAct τ K s u =
      m * (rootDiagUnit τ a * fieldAutHom τ K s.right u * (rootDiagUnit τ a)⁻¹) * m⁻¹ := by
  rw [conjAct_apply, h, fieldAutHom_apply]
  group

theorem conjAct_mem_levelRadicalT {J : Set (Fin τ.rank)} {s : GamL τ K} (hs : LeviT J s)
    {d : ℤ} (hd : 1 ≤ d) {u : ModGL τ K} (hu : u ∈ levelRadical τ K J d) :
    conjAct τ K s u ∈ levelRadical τ K J d := by
  obtain ⟨m, hm, a, ha⟩ := hs
  rw [conjAct_eq_of_leviT ha]
  exact (Subgroup.mem_normalizer_iff.1 (parabolicLevi_le_normalizer J hd hm) _).1
    (conj_rootDiagUnit_mem_levelRadicalT a (fieldAut_mem_levelRadical s.right hu))

theorem layerMap_smulT (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    (J : Set (Fin τ.rank)) (n : ℕ) {s : GamL τ K} (hs : LeviT J s)
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1))
    {u : ModGL τ K} (hu : u ∈ levelRadical τ K J (n + 1))
    (hxu : layerMap J n x = QuotientGroup.mk (⟨u, hu⟩ : levelRadical τ K J (n + 1))) :
    layerMap J n (s • x) = QuotientGroup.mk (⟨conjAct τ K s u,
      conjAct_mem_levelRadicalT hs (one_le_succ n) hu⟩ : levelRadical τ K J (n + 1)) := by
  obtain ⟨m, hm, a, ha⟩ := id hs
  rw [smul_eq_of_leviT ha, layerMap_parabolicLevi hτ h2 J n hm
      (rootDiag_mem_gradedT a (vtw_mem_graded s.right hx)), layerMap_rootDiagT, layerMap_vtw,
    hxu, phiLayer_mk, diagLayer_mk, levelConj_mk]
  congr 1
  refine Subtype.ext ?_
  change m * (rootDiagUnit τ a * fieldAutHom τ K s.right u * (rootDiagUnit τ a)⁻¹) * m⁻¹ =
    conjAct τ K s u
  rw [conjAct_eq_of_leviT ha]

theorem pairing_smulT (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    (J : Set (Fin τ.rank)) (n : ℕ) {s : GamL τ K} (hs : LeviT J s)
    {x y : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1))
    (hy : y ∈ parabolicGraded τ K J (-(n + 1))) :
    trK (rootPairing τ K (s • x) (s • y)) = trK (rootPairing τ K x y) := by
  obtain ⟨m, hm, a, ha⟩ := hs
  rw [smul_eq_of_leviT ha, smul_eq_of_leviT ha, rootPairing_parabolicLevi hτ h2 J n hm
      (rootDiag_mem_gradedT a (vtw_mem_graded _ hx)) (rootDiag_mem_gradedT a (vtw_mem_graded _ hy)),
    rootPairing_rootDiagT, rootPairing_vtw, trK_ringAut]

theorem leviT_conj_longest {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) {s : GamL τ K} (hs : LeviT J s) :
    LeviT (δ '' J) ((SemidirectProduct.inl (canonicalRep (coxeterSystem τ) K w₀) : GamL τ K) *
      s * (SemidirectProduct.inl (canonicalRep (coxeterSystem τ) K w₀))⁻¹) := by
  obtain ⟨m, hm, a, ha⟩ := hs
  obtain ⟨a', ha'⟩ := exists_conj_canonicalRep_rootDiagUnitT (K := K) w₀ a
  refine ⟨canonicalRep (coxeterSystem τ) K w₀ * m * (canonicalRep (coxeterSystem τ) K w₀)⁻¹,
    map_conj_parabolicLevi_le hδ J (Subgroup.mem_map.2 ⟨m, hm, rfl⟩), a', ?_⟩
  rw [inl_conj_left (canonicalRep (coxeterSystem τ) K w₀) (fun σ => entrywise_canonicalRep σ w₀) s,
    ha, ← ha']
  group

theorem exists_fixed_vector_semiT [Finite K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {S : Subgroup (GamL τ K)}
    (hS : ∀ s ∈ S, LeviT J s) {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K J (n + 1)) (hu' : u ∉ levelRadical τ K J (n + 1 + 1))
    (hfix : ∀ s ∈ S, conjAct τ K s u = u) :
    ∃ x ∈ parabolicGraded τ K J (n + 1), x ≠ 0 ∧ ∀ s ∈ S, s • x = x := by
  obtain ⟨x, hx, hxu⟩ := exists_layerMap_eq J n
    ((⟨u, hu⟩ : levelRadical τ K J (n + 1)) : Layer τ K J n)
  refine ⟨x, hx, fun h0 => ?_, fun s hs => ?_⟩
  · rw [h0, layerMap_zero] at hxu
    exact hu' (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hxu.symm))
  · refine layerMap_injOn J n (smul_mem_gradedT (hS s hs) _ hx) hx ?_
    rw [layerMap_smulT hτ h2 J n (hS s hs) hx hu hxu, hxu]
    congr 1
    exact Subtype.ext (hfix s hs)

theorem exists_invariant_coset_semiT [Finite K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {S : Subgroup (GamL τ K)}
    (hS : ∀ s ∈ S, LeviT J s) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (n + 1)) (hx0 : x ≠ 0) (hfix : ∀ s ∈ S, s • x = x) :
    ∃ u ∈ levelRadical τ K J (n + 1), u ∉ levelRadical τ K J (n + 1 + 1) ∧
      ∀ s ∈ S, u⁻¹ * conjAct τ K s u ∈ levelRadical τ K J (n + 1 + 1) := by
  obtain ⟨⟨u, hu⟩, hux⟩ := QuotientGroup.mk_surjective (layerMap J n x)
  refine ⟨u, hu, fun hu' => hx0 ?_, fun s hs => ?_⟩
  · refine layerMap_injOn J n hx (Submodule.zero_mem _) ?_
    rw [layerMap_zero, ← hux]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu')
  · have h1 := layerMap_smulT hτ h2 J n (hS s hs) hx hu hux.symm
    rw [hfix s hs, ← hux] at h1
    have h3 := QuotientGroup.eq.1 h1
    rw [Subgroup.mem_subgroupOf] at h3
    simpa using h3

theorem exists_fixed_neg_semiT [Finite K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {S : Subgroup (GamL τ K)}
    (hS : ∀ s ∈ S, LeviT J s) (hodd : Odd (Nat.card S))
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1)) (hx0 : x ≠ 0)
    (hfix : ∀ s ∈ S, s • x = x) :
    ∃ y ∈ parabolicGraded τ K J (-(n + 1)), y ≠ 0 ∧ ∀ s ∈ S, s • y = y := by
  classical
  have : Finite S := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (by
    rintro h; rw [h] at hodd; exact absurd hodd (by decide))).ne'
  let _ : Fintype S := Fintype.ofFinite S
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (Finsupp.ext h)
  have hbL : b ∈ gradedLabels τ J (n + 1) := by
    have hx' := hx
    rw [parabolicGraded_eq_supported] at hx'
    exact (Finsupp.mem_supported K x).1 hx' (Finsupp.mem_support_iff.2 hb)
  obtain ⟨α, hα, hbeq⟩ := mem_layerRoots_of_mem_gradedLabels hbL
  have hαr : IsRoot τ α := hα.1
  have hb' : x (Sum.inr ⟨α, hαr⟩) ≠ 0 := by rw [hbeq] at hb; exact hb
  obtain ⟨c, hc⟩ := exists_trK_ne_zero hb'
  have hy₀ : c • rootVec τ K (-α) ∈ parabolicGraded τ K J (-(n + 1)) :=
    Submodule.smul_mem _ _ (rootVec_mem_parabolicGraded (IsRoot.neg hαr)
      (by rw [parabolicDegree_neg, hα.2.2]))
  set y₀ : RootModule τ K := c • rootVec τ K (-α) with hy₀def
  set y : RootModule τ K := ∑ s : S, (s : GamL τ K) • y₀ with hy
  have hyG : y ∈ parabolicGraded τ K J (-(n + 1)) :=
    Submodule.sum_mem _ fun s _ => smul_mem_gradedT (hS s s.2) _ hy₀
  have hpr : rootPairing τ K x (rootVec τ K (-α)) = x (Sum.inr ⟨α, hαr⟩) :=
    rootPairing_rootVec_neg hαr x
  have hterm : ∀ s : S, trK (rootPairing τ K x ((s : GamL τ K) • y₀)) =
      trK (x (Sum.inr ⟨α, hαr⟩) * c) := fun s => by
    conv_lhs => rw [← hfix s s.2]
    rw [pairing_smulT hτ h2 J n (hS s s.2) hx hy₀, hy₀def, map_smul, hpr, smul_eq_mul, mul_comm]
  have hsum : rootPairing τ K x y = ∑ s : S, rootPairing τ K x ((s : GamL τ K) • y₀) := by
    rw [hy, map_sum]
  have htr : trK (rootPairing τ K x y) =
      ∑ s : S, trK (rootPairing τ K x ((s : GamL τ K) • y₀)) := by
    rw [hsum]
    exact map_sum trKHom _ Finset.univ
  have hpair : trK (rootPairing τ K x y) = trK (x (Sum.inr ⟨α, hαr⟩) * c) := by
    rw [htr, Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_eq_nat_card, natCast_eq_one_of_odd h2 hodd, one_mul]
  refine ⟨y, hyG, fun h0 => hc ?_, fun s hs => ?_⟩
  · rw [← hpair, h0, map_zero, trK_zero]
  · rw [hy, smul_sum']
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨s, hs⟩ : S)) _ _ fun t => ?_
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_smul]

theorem exists_fixed_mem_oppRadical_semiT [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {J : Set (Fin τ.rank)}
    {S : Subgroup (GamL τ K)} (hS : ∀ s ∈ S, LeviT J s)
    (hodd : Odd (Nat.card S)) {u : ModGL τ K} (hu : u ∈ parabolicRadical τ K J) (hu1 : u ≠ 1)
    (hfix : ∀ s ∈ S, conjAct τ K s u = u) :
    ∃ v ∈ oppRadical τ K J, v ≠ 1 ∧ ∀ s ∈ S, conjAct τ K s v = v := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨n, hun, hun'⟩ := exists_level hu hu1
  obtain ⟨x, hx, hx0, hxS⟩ := exists_fixed_vector_semiT hτ h2 J n hS hun hun' hfix
  obtain ⟨y, hy, hy0, hyS⟩ := exists_fixed_neg_semiT hτ h2 J n hS hodd hx hx0 hxS
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ := exists_longest τ
  set n₀ := canonicalRep (coxeterSystem τ) K w₀ with hn₀
  set c₀ : GamL τ K := SemidirectProduct.inl n₀ with hc₀
  set S' : Subgroup (GamL τ K) := S.map (MulAut.conj c₀).toMonoidHom with hS'
  have hS'M : ∀ s' ∈ S', LeviT (δ '' J) s' := by
    rintro _ ⟨s, hs, rfl⟩
    exact leviT_conj_longest hδ J (hS s hs)
  have hodd' : Odd (Nat.card S') := by
    rwa [hS', Subgroup.card_map_of_injective (MulAut.conj c₀).injective]
  have hx' : (n₀ : Module.End K (RootModule τ K)) y ∈
      parabolicGraded τ K (δ '' J) (n + 1) :=
    longest_mem_parabolicGraded hinj hδ J (n + 1) hy
  have hx'0 : (n₀ : Module.End K (RootModule τ K)) y ≠ 0 := fun h => hy0 (by
    rw [← units_inv_apply_apply n₀ y, h, map_zero])
  have hc₀y : c₀ • y = (n₀ : Module.End K (RootModule τ K)) y := by
    rw [smul_def, hc₀, SemidirectProduct.left_inl, SemidirectProduct.right_inl, vtw_one]
  have hx'S : ∀ s' ∈ S', s' • ((n₀ : Module.End K (RootModule τ K)) y) =
      (n₀ : Module.End K (RootModule τ K)) y := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc₀y, ← mul_smul, inv_mul_cancel_right, mul_smul, hyS s hs]
  obtain ⟨u', hu', hu'', hcos⟩ :=
    exists_invariant_coset_semiT hτ h2 (δ '' J) n hS'M hx' hx'0 hx'S
  have hN1 : ∀ b ∈ S', ∀ z ∈ levelRadical τ K (δ '' J) (n + 1),
      conjAct τ K b z ∈ levelRadical τ K (δ '' J) (n + 1) := fun b hb z hz =>
    conjAct_mem_levelRadicalT (hS'M b hb) (one_le_succ n) hz
  have hN2 : ∀ b ∈ S', ∀ z ∈ levelRadical τ K (δ '' J) (n + 1 + 1),
      conjAct τ K b z ∈ levelRadical τ K (δ '' J) (n + 1 + 1) := fun b hb z hz =>
    conjAct_mem_levelRadicalT (hS'M b hb) (one_le_succ_succ n) hz
  letI : MulDistribMulAction S' (levelRadical τ K (δ '' J) (n + 1)) :=
    actSub S' _ hN1
  have hinv : CFSG.IsInvariant S' (levelRadical τ K (δ '' J) (n + 1))
      ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf (levelRadical τ K (δ '' J) (n + 1))) :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun a z hz => by
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact hN2 a a.2 z hz
  have hp : IsPGroup 2 ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
      (levelRadical τ K (δ '' J) (n + 1))) :=
    (isPGroup_levelRadical (δ '' J) (n + 1 + 1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (levelRadical_succ_le (δ '' J) (n + 1))).symm
  have hsolv : Group.IsSolvable ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
      (levelRadical τ K (δ '' J) (n + 1))) := by
    have := hp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card S')
      (Nat.card ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
        (levelRadical τ K (δ '' J) (n + 1)))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd')
  have : Finite S' := Nat.finite_of_card_ne_zero (by
    rintro h; rw [h] at hodd'; exact absurd hodd' (by decide))
  obtain ⟨c, hc, hcu⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf (levelRadical τ K (δ '' J) (n + 1)))
    hinv hsolv hcop ⟨u', hu'⟩ fun b => by
      rw [Subgroup.mem_subgroupOf]
      exact hcos b b.2
  have hcN : (c : ModGL τ K) ∉ levelRadical τ K (δ '' J) (n + 1 + 1) := fun h => hu'' (by
    have h' := Subgroup.mem_subgroupOf.1 hcu
    have e : u' = (c : ModGL τ K) * ((c⁻¹ * ⟨u', hu'⟩ : levelRadical τ K (δ '' J) (n + 1)) :
      ModGL τ K) := by simp
    rw [e]
    exact mul_mem h h')
  have hconjc : conjAct τ K c₀⁻¹ = MulAut.conj n₀⁻¹ := by
    rw [map_inv, hc₀, conjAct_inl, ← map_inv]
  refine ⟨n₀⁻¹ * c * n₀, ?_, fun h => hcN ?_, fun s hs => ?_⟩
  · have hcQ : (c : ModGL τ K) ∈ parabolicRadical τ K (δ '' J) :=
      levelRadical_le_parabolicRadical _ (one_le_succ n) c.2
    have := map_conj_longest_parabolicRadical_le (K := K) hinj hδ hsq h₀ J
      (Subgroup.mem_map_of_mem _ hcQ)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  · have e : (c : ModGL τ K) = n₀ * (n₀⁻¹ * c * n₀) * n₀⁻¹ := by group
    rw [e, h, mul_one, mul_inv_cancel]
    exact one_mem _
  · have hcs := congrArg Subtype.val (hc ⟨c₀ * s * c₀⁻¹, ⟨s, hs, rfl⟩⟩)
    change conjAct τ K (c₀ * s * c₀⁻¹) (c : ModGL τ K) = c at hcs
    rw [map_mul, map_mul, hconjc, hc₀, conjAct_inl] at hcs
    simp only [MulAut.mul_apply, MulAut.conj_apply] at hcs
    calc conjAct τ K s (n₀⁻¹ * c * n₀) =
        n₀⁻¹ * (n₀ * conjAct τ K s (n₀⁻¹ * c * n₀) * n₀⁻¹) * n₀ := by group
      _ = n₀⁻¹ * c * n₀ := by rw [show n₀ * conjAct τ K s (n₀⁻¹ * c * n₀) * n₀⁻¹ = c from hcs]

@[expose] noncomputable def torusMul (H : Subgroup (ModGL τ K))
    (hH : ∀ (a : Fin τ.rank → Kˣ), ∀ h ∈ H, rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ ∈ H) :
    Subgroup (ModGL τ K) where
  carrier := {g | ∃ h ∈ H, ∃ a : Fin τ.rank → Kˣ, g = h * rootDiagUnit τ a}
  one_mem' := ⟨1, one_mem H, 1, by rw [rootDiagUnit_one, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨h, hh, a, rfl⟩ ⟨h', hh', a', rfl⟩
    refine ⟨h * (rootDiagUnit τ a * h' * (rootDiagUnit τ a)⁻¹), mul_mem hh (hH a h' hh'),
      a * a', ?_⟩
    rw [rootDiagUnit_mul]
    group
  inv_mem' := by
    rintro _ ⟨h, hh, a, rfl⟩
    refine ⟨rootDiagUnit τ a⁻¹ * h⁻¹ * (rootDiagUnit τ a⁻¹)⁻¹, hH a⁻¹ _ (inv_mem hh), a⁻¹, ?_⟩
    rw [← rootDiagUnit_inv]
    group

theorem mem_torusMul {H : Subgroup (ModGL τ K)}
    {hH : ∀ (a : Fin τ.rank → Kˣ), ∀ h ∈ H, rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ ∈ H}
    {g : ModGL τ K} :
    g ∈ torusMul H hH ↔ ∃ h ∈ H, ∃ a : Fin τ.rank → Kˣ, g = h * rootDiagUnit τ a :=
  Iff.rfl

theorem fieldAut_mem_torusMul {H : Subgroup (ModGL τ K)}
    {hH : ∀ (a : Fin τ.rank → Kˣ), ∀ h ∈ H, rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ ∈ H}
    (hσH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom τ K σ h ∈ H) (σ : RingAut K) {g : ModGL τ K}
    (hg : g ∈ torusMul H hH) : fieldAutHom τ K σ g ∈ torusMul H hH := by
  obtain ⟨h, hh, a, rfl⟩ := hg
  exact ⟨fieldAutHom τ K σ h, hσH σ h hh, fun i => Units.map (σ : K →+* K).toMonoidHom (a i),
    by rw [map_mul, fieldAutHom_rootDiagUnitT]⟩

variable (τ K) in
@[expose] noncomputable def adjT : Subgroup (ModGL τ K) :=
  torusMul (adjointGroup τ K) fun a _ hh => conj_rootDiagUnit_mem_adjointGroup a hh

variable (τ K) in
@[expose] noncomputable def gamAdjT : Subgroup (GamL τ K) :=
  gamSub (adjT τ K) fun σ _ hh =>
    fieldAut_mem_torusMul (fun σ' _ hh' => fieldAut_mem_adjointGroup σ' hh') σ hh

theorem mem_gamAdjT {s : GamL τ K} :
    s ∈ gamAdjT τ K ↔ ∃ g ∈ adjointGroup τ K, ∃ a : Fin τ.rank → Kˣ,
      s.left = g * rootDiagUnit τ a :=
  Iff.rfl

theorem exists_conj_into_leviT [Finite K] [CharP K 2] [Finite (ModGL τ K)]
    (J : Set (Fin τ.rank)) {T : Subgroup (GamL τ K)}
    (hT : ∀ s ∈ T, ∃ g ∈ parabolicSubgroup τ K J, ∃ a : Fin τ.rank → Kˣ,
      s.left = g * rootDiagUnit τ a)
    (hodd : ¬ 2 ∣ Nat.card T) :
    ∃ y ∈ parabolicRadical τ K J, ∀ s ∈ T,
      LeviT J ((SemidirectProduct.inl y : GamL τ K) * s * (SemidirectProduct.inl y)⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinσ : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hfinΓ : Finite (GamL τ K) :=
    Finite.of_equiv (ModGL τ K × RingAut K) (SemidirectProduct.equivProd).symm
  obtain ⟨hQP, -, -, -, -, -, hdec, -⟩ := parabolic_root_radical_Levi_factors τ K J
  have hQ2 : IsPGroup 2 (parabolicRadical τ K J) :=
    (isPGroup_posUnipotent 2 τ).to_le (parabolicRadical_le_posUnipotent J)
  let PT : Subgroup (ModGL τ K) :=
    torusMul (parabolicSubgroup τ K J) fun a _ hh => conj_rootDiagUnit_mem_parabolicSubgroupT a hh
  let MT : Subgroup (ModGL τ K) :=
    torusMul (parabolicLevi τ K J) fun a _ hh => conj_rootDiagUnit_mem_parabolicLeviT a hh
  let Ppar : Subgroup (GamL τ K) := gamSub PT fun σ _ hh =>
    fieldAut_mem_torusMul (fun σ' _ hh' => fieldAut_mem_parabolicSubgroup σ' hh') σ hh
  let Mlev : Subgroup (GamL τ K) := gamSub MT fun σ _ hh =>
    fieldAut_mem_torusMul (fun σ' _ hh' => fieldAut_mem_parabolicLevi σ' hh') σ hh
  let Qrad : Subgroup (GamL τ K) := (parabolicRadical τ K J).map SemidirectProduct.inl
  have hQrad2 : IsPGroup 2 Qrad := hQ2.map _
  have hQradPpar : Qrad ≤ Ppar := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_gamSub.2 (mem_torusMul.2 ⟨q, hQP hq, 1, by
      rw [SemidirectProduct.left_inl, rootDiagUnit_one, mul_one]⟩)
  have hPparN : Ppar ≤ Subgroup.normalizer (Qrad : Set (GamL τ K)) := by
    refine le_normalizer_of_conj_mem fun s hs y hy => ?_
    obtain ⟨q, hq, rfl⟩ := hy
    rw [conj_inl]
    refine ⟨conjAct τ K s q, ?_, rfl⟩
    obtain ⟨g, hg, a, ha⟩ := mem_torusMul.1 (mem_gamSub.1 hs)
    rw [conjAct_eq_of_leviT ha]
    exact (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical J hg) _).1
      (conj_rootDiagUnit_mem_parabolicRadicalT a (fieldAut_mem_parabolicRadical s.right hq))
  have hQradMlev : Qrad ⊓ Mlev = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨q, hq, rfl⟩, hxM⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨m, hm, a, ha⟩ := mem_torusMul.1 (mem_gamSub.1 hxM)
    have ha' : q = m * rootDiagUnit τ a := ha
    have hq1 : q = 1 := by
      refine eq_one_of_mem_parabolicRadical_of_preservesT hq fun d x hx => ?_
      rw [ha', Units.val_mul, Module.End.mul_apply, coe_rootDiagUnitT]
      exact parabolicLevi_preserves hm d (rootDiag_mem_gradedT a hx)
    rw [hq1, map_one]
    exact Subgroup.one_mem _
  have hdec' : ∀ g ∈ Ppar, ∃ q ∈ Qrad, ∃ m ∈ Mlev, q * m = g := by
    intro g hg
    obtain ⟨p, hp, a, ha⟩ := mem_torusMul.1 (mem_gamSub.1 hg)
    obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdec p hp
    refine ⟨SemidirectProduct.inl qm.1, ⟨qm.1, hq, rfl⟩, ⟨qm.2 * rootDiagUnit τ a, g.right⟩,
      mem_gamSub.2 (mem_torusMul.2 ⟨qm.2, hm, a, rfl⟩), ?_⟩
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        map_one, MulAut.one_apply, ha, hx]
      exact (mul_assoc _ _ _).symm
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  have hTP : T ≤ Ppar := fun s hs => mem_gamSub.2 (mem_torusMul.2 (hT s hs))
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_le_of_complement (p := 2) (P := Ppar) (Q := Qrad)
    (M := Mlev) hQrad2 hQradPpar hPparN hQradMlev hdec' hTP hodd
  obtain ⟨y₀, hy₀, rfl⟩ := hyQ
  refine ⟨y₀, hy₀, fun s hs => ?_⟩
  exact mem_torusMul.1 (mem_gamSub.1 (hyM (Subgroup.mem_map_of_mem _ hs)))

theorem conj_mul_rootDiag_eq_oneT {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (a : Fin τ.rank → Kˣ) (σ : RingAut K)
    (hfix : ∀ h ∈ adjointGroup τ K, g * rootDiagUnit τ a * fieldAutHom τ K σ h *
      (g * rootDiagUnit τ a)⁻¹ = h) :
    g * rootDiagUnit τ a = 1 ∧ σ = 1 := by
  have e : exactNormalAut τ K a σ 0 = MulAut.conj (⟨g, hg⟩ : adjointGroup τ K)⁻¹ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have h1 := hfix h h.2
    have h2 : rootDiagUnit τ a * fieldAutHom τ K σ h * (rootDiagUnit τ a)⁻¹ =
        g⁻¹ * h * g := by
      calc _ = g⁻¹ * (g * rootDiagUnit τ a * fieldAutHom τ K σ h * (g * rootDiagUnit τ a)⁻¹) *
            g := by group
        _ = g⁻¹ * h * g := by rw [h1]
    rw [coe_exactNormalAut_zero]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact h2
  have hA : MulAut.conj (⟨g, hg⟩ : adjointGroup τ K)⁻¹ ∈ unipotentPairAut τ K := by
    rw [← e]
    exact exactNormalAut_mem a σ 0
  obtain ⟨hU, hV⟩ := hA
  have hNU := mem_normalizer_of_map_conj_subgroupOf posUnipotent_le_adjointGroup hU
  have hNV := mem_normalizer_of_map_conj_subgroupOf negUnipotent_le_adjointGroup hV
  have hB : g⁻¹ ∈ borelGroup τ K := by
    rw [← (borel_self_normalizers τ K).1]
    exact Subgroup.mem_inf.2 ⟨inv_mem hg, hNU⟩
  have hB' : g⁻¹ ∈ oppositeBorel τ K := by
    rw [← oppositeBorel_normalizer τ K]
    exact Subgroup.mem_inf.2 ⟨inv_mem hg, hNV⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  have hT : g⁻¹ ∈ torusGroup τ K := by
    rw [← (opposite_Borel_intersection τ K w₀ hw₀).2.2.1]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have e2 : exactNormalAut τ K b 1 0 = exactNormalAut τ K a σ 0 := by
    rw [e]
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_exactNormalAut_zero, ← hb]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    congr 2
    exact Units.ext (entrywise_id _)
  obtain ⟨hab, hσ⟩ := exactNormalAut_zero_injective e2
  subst hab
  exact ⟨by rw [← hb, mul_inv_cancel], hσ.symm⟩

theorem lift_uniqueT {s s' : GamL τ K} (hs : s ∈ gamAdjT τ K) (hs' : s' ∈ gamAdjT τ K)
    (h : ∀ x ∈ adjointGroup τ K, conjAct τ K s x = conjAct τ K s' x) : s = s' := by
  have ht : s'⁻¹ * s ∈ gamAdjT τ K := mul_mem (inv_mem hs') hs
  obtain ⟨g, hg, a, ha⟩ := mem_gamAdjT.1 ht
  have hfix : ∀ x ∈ adjointGroup τ K, conjAct τ K (s'⁻¹ * s) x = x := fun x hx => by
    rw [map_mul, MulAut.mul_apply, h x hx, map_inv, MulAut.inv_apply_self]
  obtain ⟨h1, h2⟩ := conj_mul_rootDiag_eq_oneT hg a (s'⁻¹ * s).right fun x hx => by
    have := hfix x hx
    rw [conjAct_apply, ha] at this
    rw [fieldAutHom_apply]
    exact this
  have h3 : s'⁻¹ * s = 1 := SemidirectProduct.ext (by rw [ha, h1, SemidirectProduct.one_left])
    (by rw [h2, SemidirectProduct.one_right])
  exact (inv_mul_eq_one.1 h3).symm

section LiftR

variable {R : Subgroup (MulAut ↥(adjointGroup τ K))}
  (hR : ∀ α ∈ R, ∃ s : GamL τ K, s ∈ gamAdjT τ K ∧ ∀ h : ↥(adjointGroup τ K),
    ((α h : ↥(adjointGroup τ K)) : ModGL τ K) = conjAct τ K s h)

@[expose] noncomputable def liftT (α : R) : GamL τ K :=
  (hR α α.2).choose

theorem liftT_mem (α : R) : liftT hR α ∈ gamAdjT τ K :=
  (hR α α.2).choose_spec.1

theorem liftT_spec (α : R) (h : ↥(adjointGroup τ K)) :
    (((α : MulAut ↥(adjointGroup τ K)) h : ↥(adjointGroup τ K)) : ModGL τ K) =
      conjAct τ K (liftT hR α) h :=
  (hR α α.2).choose_spec.2 h

theorem liftT_spec' (α : R) {x : ModGL τ K} (hx : x ∈ adjointGroup τ K) :
    (((α : MulAut ↥(adjointGroup τ K)) ⟨x, hx⟩ : ↥(adjointGroup τ K)) : ModGL τ K) =
      conjAct τ K (liftT hR α) x :=
  liftT_spec hR α ⟨x, hx⟩

theorem liftT_mul (α β : R) : liftT hR (α * β) = liftT hR α * liftT hR β :=
  lift_uniqueT (liftT_mem hR _) (mul_mem (liftT_mem hR α) (liftT_mem hR β)) fun x hx => by
    rw [map_mul, MulAut.mul_apply, ← liftT_spec' hR (α * β) hx, ← liftT_spec' hR β hx,
      ← liftT_spec hR α, Subgroup.coe_mul, MulAut.mul_apply]

theorem liftT_one : liftT hR 1 = 1 := by
  have h := liftT_mul hR 1 1
  rw [mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

@[expose] noncomputable def liftHomT : R →* GamL τ K where
  toFun := liftT hR
  map_one' := liftT_one hR
  map_mul' := liftT_mul hR

theorem liftHomT_apply (α : R) : liftHomT hR α = liftT hR α :=
  rfl

theorem liftHomT_injective : Function.Injective (liftHomT hR) := fun α β h => by
  refine Subtype.ext (MulEquiv.ext fun x => Subtype.ext ?_)
  rw [liftT_spec hR α, liftT_spec hR β]
  exact congrArg (fun s => conjAct τ K s (x : ModGL τ K)) h

end LiftR

theorem lift_left_mem_parabolicT (J : Set (Fin τ.rank)) {α : MulAut ↥(adjointGroup τ K)}
    {s : GamL τ K} (hs : s ∈ gamAdjT τ K)
    (hspec : ∀ h : ↥(adjointGroup τ K),
      ((α h : ↥(adjointGroup τ K)) : ModGL τ K) = conjAct τ K s h)
    (hα : (radG τ K J).map α.toMonoidHom = radG τ K J)
    (hNQ : Subgroup.normalizer ((radG τ K J : Subgroup ↥(adjointGroup τ K)) :
      Set ↥(adjointGroup τ K)) = parG τ K J) :
    ∃ g ∈ parabolicSubgroup τ K J, ∃ a : Fin τ.rank → Kˣ, s.left = g * rootDiagUnit τ a := by
  obtain ⟨g, hg, a, ha⟩ := mem_gamAdjT.1 hs
  refine ⟨g, ?_, a, ha⟩
  have hmem : (⟨g, hg⟩ : ↥(adjointGroup τ K)) ∈ Subgroup.normalizer
      ((radG τ K J : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx1 : (rootDiagUnit τ a)⁻¹ * (x : ModGL τ K) * rootDiagUnit τ a ∈ adjointGroup τ K := by
      have := conj_rootDiagUnit_mem_adjointGroup a⁻¹ x.2
      rwa [← rootDiagUnit_inv, inv_inv] at this
    obtain ⟨x'', hx''⟩ : ∃ x'' : ↥(adjointGroup τ K), (x'' : ModGL τ K) =
        fieldAutHom τ K s.right⁻¹ ((rootDiagUnit τ a)⁻¹ * (x : ModGL τ K) * rootDiagUnit τ a) :=
      ⟨⟨_, fieldAut_mem_adjointGroup _ hx1⟩, rfl⟩
    have hαx : ((α x'' : ↥(adjointGroup τ K)) : ModGL τ K) = g * (x : ModGL τ K) * g⁻¹ := by
      rw [hspec x'', conjAct_eq_of_leviT ha, hx'', fieldAut_mul_inv_apply]
      group
    have e : (⟨g, hg⟩ * x * (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ : ↥(adjointGroup τ K)) = α x'' :=
      Subtype.ext (by rw [hαx]; rfl)
    have h1 : (α x'' ∈ radG τ K J) ↔ x'' ∈ radG τ K J := by
      constructor
      · intro h
        rw [← hα] at h
        obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 h
        have : q = x'' := α.injective hqe
        exact this ▸ hq
      · intro h
        rw [← hα]
        exact Subgroup.mem_map_of_mem _ h
    have h2 : x'' ∈ radG τ K J ↔ x ∈ radG τ K J := by
      rw [radG, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hx'']
      constructor
      · intro h
        have h3 := conj_rootDiagUnit_mem_parabolicRadicalT a
          (fieldAut_mem_parabolicRadical s.right h)
        rw [fieldAut_mul_inv_apply] at h3
        have e3 : rootDiagUnit τ a * ((rootDiagUnit τ a)⁻¹ * (x : ModGL τ K) *
            rootDiagUnit τ a) * (rootDiagUnit τ a)⁻¹ = x := by
          group
        rwa [e3] at h3
      · intro h
        refine fieldAut_mem_parabolicRadical _ ?_
        have h3 := conj_rootDiagUnit_mem_parabolicRadicalT a⁻¹ h
        rwa [← rootDiagUnit_inv, inv_inv] at h3
    rw [e]
    exact h2.symm.trans h1.symm
  rw [hNQ] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem autCentralizer_inf_radG_eq_bot_T [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (J : Set (Fin τ.rank)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut ↥(adjointGroup τ K))} (hR : IsPGroup p R)
    (hlift : ∀ α ∈ R, ∃ s : GamL τ K, s ∈ gamAdjT τ K ∧ ∀ h : ↥(adjointGroup τ K),
      ((α h : ↥(adjointGroup τ K)) : ModGL τ K) = conjAct τ K s h)
    (hQR : ∀ α ∈ R, (radG τ K J).map α.toMonoidHom = radG τ K J)
    (hNQ : Subgroup.normalizer ((radG τ K J : Subgroup ↥(adjointGroup τ K)) :
      Set ↥(adjointGroup τ K)) = parG τ K J)
    (hC : autCentralizer R ≤ parG τ K J) :
    autCentralizer R ⊓ radG τ K J = ⊥ := by
  classical
  have hfinM : Finite (ModGL τ K) := finite_modGL
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨⟨w₁, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hwC, hwQ⟩ := Subgroup.mem_inf.1 hw
  have hw1' : (w₁ : ModGL τ K) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  obtain ⟨hQP, -⟩ := parabolic_root_radical_Levi_factors τ K J
  set T : Subgroup (GamL τ K) := (liftHomT hlift).range with hT
  have hTcard : Nat.card T = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective (liftHomT_injective hlift)).toEquiv).symm
  have hRodd : Nat.card R % 2 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)
  have hTodd : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]; exact Nat.two_dvd_ne_zero.2 hRodd
  have hTP : ∀ s ∈ T, ∃ g ∈ parabolicSubgroup τ K J, ∃ a : Fin τ.rank → Kˣ,
      s.left = g * rootDiagUnit τ a := by
    rintro _ ⟨α, rfl⟩
    exact lift_left_mem_parabolicT J (liftT_mem hlift α) (liftT_spec hlift α) (hQR α α.2) hNQ
  obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_leviT J hTP hTodd
  set y : GamL τ K := SemidirectProduct.inl y₀ with hy
  set S : Subgroup (GamL τ K) := T.map (MulAut.conj y).toMonoidHom with hS
  have hSM : ∀ s ∈ S, LeviT J s := by
    rintro _ ⟨s, hs, rfl⟩
    exact hyM s hs
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj y).injective, hTcard]
    exact Nat.odd_iff.2 hRodd
  have hconjy : ∀ g : ModGL τ K, conjAct τ K y g = y₀ * g * y₀⁻¹ := fun g => by
    rw [hy, conjAct_inl, MulAut.conj_apply]
  have hconjyinv : ∀ g : ModGL τ K, conjAct τ K y⁻¹ g = y₀⁻¹ * g * y₀ := fun g => by
    rw [map_inv, hy, conjAct_inl, ← map_inv, MulAut.conj_apply, inv_inv]
  have hu : (w₁ : ModGL τ K) ∈ parabolicRadical τ K J := Subgroup.mem_subgroupOf.1 hwQ
  have hy₀P : y₀ ∈ parabolicSubgroup τ K J := hQP hy₀
  have hu' : y₀ * (w₁ : ModGL τ K) * y₀⁻¹ ∈ parabolicRadical τ K J :=
    (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical J hy₀P) _).1 hu
  have hu'1 : y₀ * (w₁ : ModGL τ K) * y₀⁻¹ ≠ 1 := fun h => hw1' (by
    have := congrArg (fun z => y₀⁻¹ * z * y₀) h
    simpa [mul_assoc] using this)
  have hfixT : ∀ s ∈ T, conjAct τ K s (w₁ : ModGL τ K) = w₁ := by
    rintro _ ⟨α, rfl⟩
    rw [liftHomT_apply, ← liftT_spec hlift α, hwC α α.2]
  have hfix : ∀ s ∈ S, conjAct τ K s (y₀ * (w₁ : ModGL τ K) * y₀⁻¹) =
      y₀ * (w₁ : ModGL τ K) * y₀⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : conjAct τ K y⁻¹ (y₀ * (w₁ : ModGL τ K) * y₀⁻¹) = w₁ := by
      rw [hconjyinv]; group
    rw [conjAct_conj, h1, hfixT s hs, hconjy]
  obtain ⟨v, hvQ, hv1, hvfix⟩ := exists_fixed_mem_oppRadical_semiT hτ hSM hSodd hu' hu'1 hfix
  have hvG : v ∈ adjointGroup τ K := rootSpan_le_adjointGroup K _ hvQ
  have hy₀G : y₀ ∈ adjointGroup τ K := rootSpan_le_adjointGroup K _ hy₀
  have hwG : y₀⁻¹ * v * y₀ ∈ adjointGroup τ K := mul_mem (mul_mem (inv_mem hy₀G) hvG) hy₀G
  have hwfix : ∀ s ∈ T, conjAct τ K s (y₀⁻¹ * v * y₀) = y₀⁻¹ * v * y₀ := by
    intro s hs
    have h := hvfix _ (Subgroup.mem_map_of_mem _ hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [conjAct_conj, hconjyinv, hconjy] at h
    calc conjAct τ K s (y₀⁻¹ * v * y₀) =
        y₀⁻¹ * (y₀ * conjAct τ K s (y₀⁻¹ * v * y₀) * y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * v * y₀ := by rw [h]
  have hwC' : (⟨y₀⁻¹ * v * y₀, hwG⟩ : ↥(adjointGroup τ K)) ∈ autCentralizer R := by
    intro α hα
    refine Subtype.ext ?_
    exact (liftT_spec hlift ⟨α, hα⟩ _).trans (hwfix (liftHomT hlift ⟨α, hα⟩) ⟨⟨α, hα⟩, rfl⟩)
  have hwP : y₀⁻¹ * v * y₀ ∈ parabolicSubgroup τ K J := Subgroup.mem_subgroupOf.1 (hC hwC')
  have hvP : v ∈ parabolicSubgroup τ K J := by
    have e : v = y₀ * (y₀⁻¹ * v * y₀) * y₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hy₀P hwP) (inv_mem hy₀P)
  have h0 := Subgroup.mem_inf.2 ⟨hvP, hvQ⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hv1 (Subgroup.mem_bot.1 h0)

theorem oppositeFixed_adjointGroup_of_liftT [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hL : ∀ α : MulAut ↥(adjointGroup τ K), ∀ k : ℕ, Odd k → α ^ k = 1 →
      ∃ s : GamL τ K, s ∈ gamAdjT τ K ∧ ∀ h : ↥(adjointGroup τ K),
        ((α h : ↥(adjointGroup τ K)) : ModGL τ K) = conjAct τ K s h) :
    OppositeFixed ↥(adjointGroup τ K) := by
  intro p hp hp2 R hR Q hQ0 hQ2 hcore hne hRQ hC
  classical
  have hfinM : Finite (ModGL τ K) := finite_modGL
  have hQ₀ne : Q.map (adjointGroup τ K).subtype ≠ ⊥ := fun h =>
    hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q (adjointGroup τ K).subtype_injective).1 h)
  obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_ordinary (Subgroup.map_subtype_le Q)
    (hQ2.map (adjointGroup τ K).subtype) hQ₀ne
  have hQJle : parabolicRadical τ K J ≤ adjointGroup τ K := fun x hx =>
    rootSpan_le_adjointGroup K _ hx
  have hQJ2 : IsPGroup 2 (radG τ K J) := by
    have h2 : IsPGroup 2 (parabolicRadical τ K J) :=
      (isPGroup_posUnipotent 2 τ).to_le (parabolicRadical_le_posUnipotent J)
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe hQJle).symm
  have hPJ : parG τ K J ≤ Subgroup.normalizer
      ((radG τ K J : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := parabolicSubgroup_le_normalizer_parabolicRadical J (Subgroup.mem_subgroupOf.1 hx)
    simp only [radG, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  have hN : ∀ x ∈ Subgroup.normalizer (Q : Set ↥(adjointGroup τ K)),
      (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ * x * ⟨g, hg⟩ ∈ parG τ K J :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype hx))
  have hQ : ∀ q ∈ Q, (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ * q * ⟨g, hg⟩ ∈ radG τ K J :=
    fun q hq => Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  obtain ⟨hQ', hNQ⟩ := std_position (⟨g, hg⟩ : ↥(adjointGroup τ K)) hcore hQJ2 hPJ hN hQ
  set γ : MulAut ↥(adjointGroup τ K) := MulAut.conj (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ with hγ
  set R' : Subgroup (MulAut ↥(adjointGroup τ K)) := R.map (MulAut.conj γ).toMonoidHom with hR'
  have hR'p : IsPGroup p R' := hR.map _
  have hQmap : Q.map γ.toMonoidHom = radG τ K J := hQ'
  have hQR' : ∀ α' ∈ R', (radG τ K J).map α'.toMonoidHom = radG τ K J := by
    rintro _ ⟨α, hα, rfl⟩
    have e : ((MulAut.conj γ).toMonoidHom α).toMonoidHom.comp γ.toMonoidHom =
        γ.toMonoidHom.comp α.toMonoidHom := by
      ext x; simp [MulAut.conj_apply]
    rw [← hQmap, Subgroup.map_map, e, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer R' ≤ parG τ K J := by
    intro x hx
    have hx' : γ⁻¹ x ∈ autCentralizer R := by
      intro α hα
      have h := hx ((MulAut.conj γ).toMonoidHom α) ⟨α, hα, rfl⟩
      have h2 : γ (α (γ⁻¹ x)) = x := by simpa [MulAut.conj_apply] using h
      calc α (γ⁻¹ x) = γ⁻¹ (γ (α (γ⁻¹ x))) := by simp
        _ = γ⁻¹ x := by rw [h2]
    have hN' : γ⁻¹ x ∈ Subgroup.normalizer (Q : Set ↥(adjointGroup τ K)) := hC hx'
    have h3 : x ∈ Subgroup.normalizer ((Q.map γ.toMonoidHom : Subgroup ↥(adjointGroup τ K)) :
        Set ↥(adjointGroup τ K)) := by
      rw [← Subgroup.map_equiv_normalizer_eq Q γ]
      exact ⟨γ⁻¹ x, hN', by simp⟩
    rw [hQmap, hNQ] at h3
    exact h3
  have hlift : ∀ α' ∈ R', ∃ s : GamL τ K, s ∈ gamAdjT τ K ∧ ∀ h : ↥(adjointGroup τ K),
      ((α' h : ↥(adjointGroup τ K)) : ModGL τ K) = conjAct τ K s h := by
    intro α' hα'
    obtain ⟨k, hk⟩ := hR'p ⟨α', hα'⟩
    refine hL α' (p ^ k) ((hp.eq_two_or_odd'.resolve_left hp2).pow) ?_
    have := congrArg Subtype.val hk
    simpa using this
  have key := autCentralizer_inf_radG_eq_bot_T hτ J hp hp2 hR'p hlift hQR' hNQ hC'
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzC, hzQ⟩ := Subgroup.mem_inf.1 hz
  have hz1 : γ z ∈ autCentralizer R' ⊓ radG τ K J := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      have h := hzC α hα
      change (γ * α * γ⁻¹) (γ z) = γ z
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h]
    · rw [← hQmap]
      exact Subgroup.mem_map_of_mem _ hzQ
  rw [key] at hz1
  exact Subgroup.mem_bot.2 ((MulEquiv.map_eq_one_iff γ).1 (Subgroup.mem_bot.1 hz1))

theorem exists_lift_E6 [Finite K] (α : MulAut ↥(adjointGroup Tag.E6 K)) (k : ℕ) (hk : Odd k)
    (hα : α ^ k = 1) :
    ∃ s : GamL Tag.E6 K, s ∈ gamAdjT Tag.E6 K ∧ ∀ h : ↥(adjointGroup Tag.E6 K),
      ((α h : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) = conjAct Tag.E6 K s h := by
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgα⟩ := hnf α
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hε : (ε : ℕ) = 0 := by
    have h1 : Θ α ^ k = 1 := by rw [← map_pow, hα, map_one]
    rw [hΘ α g a σ ε hgα] at h1
    have h2 : (Multiplicative.ofAdd (((ε : ℕ) : ZMod (exactE Tag.E6)))) ^ k = 1 := by
      have := congrArg Prod.snd h1
      rwa [Prod.pow_snd, Prod.snd_one] at this
    rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff] at h2
    have hlt : (ε : ℕ) < 2 := ε.isLt
    by_contra hne
    have h1' : (ε : ℕ) = 1 := by omega
    rw [h1', mul_one] at h2
    change 2 ∣ k at h2
    have := Nat.odd_iff.1 hk
    omega
  refine ⟨⟨(g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a, σ⟩, mem_gamAdjT.2 ⟨g, g.2, a, rfl⟩,
    fun h => ?_⟩
  rw [hgα h, hε, exactQ_zero, inv_one, mul_one, mul_one, conjAct_apply]
  change _ = (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a *
    Units.map (entrywiseHom (σ : K →+* K)) (h : ModGL Tag.E6 K) *
      ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a)⁻¹
  simp only [RingEquiv.toRingHom_eq_coe]
  group

theorem oppositeFixed_adjointGroup_E6 [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : OppositeFixed ↥(adjointGroup Tag.E6 K) := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact oppositeFixed_adjointGroup_of_liftT (Or.inr (Or.inl rfl)) fun α k hk hα =>
    exists_lift_E6 α k hk hα

theorem oppositeFixed_of_untwistedChevalleyModel_E6 {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : UntwistedChevalleyModel S Tag.E6 (2 ^ f)) : OppositeFixed S := by
  obtain ⟨K', _, hfin, hcard, ⟨e⟩⟩ := h
  have e' : S ≃* ↥(adjointGroup Tag.E6 K') := e.trans
    ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E6) (K := K'))).trans
      QuotientGroup.quotientBot)
  exact oppositeFixed_of_mulEquiv e' (oppositeFixed_adjointGroup_E6 hf hcard)

end Cert

end CFSG.LieType.ChevTwo.Semi
