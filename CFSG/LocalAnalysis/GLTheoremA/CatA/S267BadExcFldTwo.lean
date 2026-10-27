module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRoot
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldFrame
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (rootSL2_injective_of_field range_rootSL2_of_isRoot)

@[expose] def frameTwoRoot (τ : Tag) : Fin τ.rank → ℤ :=
  if h : 1 < frameSize τ then frameRoot τ ⟨1, h⟩ else 0

@[expose] def frameTwoNodes : (τ : Tag) → Finset (Fin τ.rank)
  | .F4 => ({0, 3} : Finset (Fin 4))
  | .E6 => ({0, 1, 5} : Finset (Fin 6))
  | .E7 => ({0, 5} : Finset (Fin 7))
  | .E8 => ({0, 7} : Finset (Fin 8))
  | _ => ∅

@[expose] def frameTwoPair (τ : Tag) (i : Fin τ.rank) : ℤ :=
  2 * iform (frameTwoRoot τ) (Pi.single i 1) / iform (frameTwoRoot τ) (frameTwoRoot τ)

@[expose] def frameTwoCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun m =>
    (decide (τ.rootCertificate.root m (highNode τ) % 2 = 0 ∧
        (∑ i, frameTwoPair τ i * τ.rootCertificate.root m i) % 2 = 0) ==
      decide ((∀ j ∈ frameTwoNodes τ, τ.rootCertificate.root m j = 0) ∨
        τ.rootCertificate.root m = highRoot τ ∨ τ.rootCertificate.root m = -highRoot τ ∨
        τ.rootCertificate.root m = frameTwoRoot τ ∨
        τ.rootCertificate.root m = -frameTwoRoot τ)) &&
    (!decide (∀ j ∈ frameTwoNodes τ, τ.rootCertificate.root m j = 0) ||
      (decide (iform (frameTwoRoot τ) (τ.rootCertificate.root m) = 0) &&
        !RootOps.isRootB τ (frameTwoRoot τ + τ.rootCertificate.root m) &&
        !RootOps.isRootB τ (frameTwoRoot τ - τ.rootCertificate.root m)))

theorem frameTwoCheck_eq_true {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    frameTwoCheck τ = true := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem frameRoot_frame1 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    frameRoot τ (frame1 hτ) = frameTwoRoot τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> rfl

theorem highNode_mem_frameTwoNodes {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highNode τ ∈ frameTwoNodes τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide

section Signs

variable {K : Type} [Field K]

theorem prod_zpow_eq_zpow_sum_fin {G : Type*} [CommGroup G] {n : ℕ} (a : G) (f : Fin n → ℤ) :
    ∏ i, a ^ f i = a ^ ∑ i, f i := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem neg_one_zpow_eq_one_iff_emod (hK2 : ringChar K ≠ 2) (n : ℤ) :
    (-1 : Kˣ) ^ n = 1 ↔ n % 2 = 0 := by
  have hne : (-1 : Kˣ) ≠ 1 := fun h =>
    hK2 ((neg_one_eq_one_iff (R := K)).1 (by simpa using congrArg Units.val h))
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [zpow_mul]
    norm_num
  · refine ⟨fun h1 => absurd ?_ hne, fun h0 => by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [zpow_add, zpow_mul, zpow_one] at h1
    norm_num at h1
    exact h1

end Signs


variable {τ : Tag}

theorem frameTwoCheck_sound (h : frameTwoCheck τ = true) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    ((β (highNode τ) % 2 = 0 ∧ (∑ i, frameTwoPair τ i * β i) % 2 = 0) ↔
      ((∀ j ∈ frameTwoNodes τ, β j = 0) ∨ β = highRoot τ ∨ β = -highRoot τ ∨
        β = frameTwoRoot τ ∨ β = -frameTwoRoot τ)) ∧
    ((∀ j ∈ frameTwoNodes τ, β j = 0) → iform (frameTwoRoot τ) β = 0 ∧
      ¬ IsRoot τ (frameTwoRoot τ + β) ∧ ¬ IsRoot τ (frameTwoRoot τ - β)) := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hβ
  simp only [frameTwoCheck, List.all_eq_true, List.mem_range] at h
  have hm' := h m hm
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_decide] at hm'
  refine ⟨hm'.1, fun hL => ?_⟩
  have h2 := hm'.2
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at h2
  rcases h2 with h2 | ⟨⟨h0, hp⟩, hm2⟩
  · exact absurd hL h2
  · refine ⟨h0, fun hr => ?_, fun hr => ?_⟩
    · rw [← RootOps.isRootB_iff, hp] at hr
      exact Bool.false_ne_true hr
    · rw [← RootOps.isRootB_iff, hm2] at hr
      exact Bool.false_ne_true hr

theorem isRoot_frameTwoRoot (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    IsRoot τ (frameTwoRoot τ) := by
  rw [← frameRoot_frame1 hτ]
  exact isRoot_frameRoot hτ _

variable {K : Type} [Field K]

@[expose] def frameTwoChar (τ : Tag) (K : Type) [Field K] : Fin τ.rank → Kˣ :=
  fun i => (-1 : Kˣ) ^ frameTwoPair τ i

theorem rootTorusSL2_frameTwo (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    rootTorusSL2 τ K (frameTwoRoot τ) (-1) = rootDiagUnit τ (frameTwoChar τ K) :=
  CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair
    (isRoot_frameTwoRoot hτ) (-1)

theorem rootChar_frameTwoChar (β : Fin τ.rank → ℤ) :
    rootChar (frameTwoChar τ K) β = (-1 : Kˣ) ^ ∑ i, frameTwoPair τ i * β i := by
  unfold rootChar frameTwoChar
  simp_rw [← zpow_mul]
  exact prod_zpow_eq_zpow_sum_fin (-1 : Kˣ) _

theorem rootCharKernel_frameTwo_eq (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK2 : ringChar K ≠ 2) :
    rootCharKernel (Pi.mulSingle (highNode τ) (-1 : Kˣ)) ∩ rootCharKernel (frameTwoChar τ K) =
      leviRootsOff τ (frameTwoNodes τ) ∪
        {highRoot τ, -highRoot τ, frameTwoRoot τ, -frameTwoRoot τ} := by
  have hc := frameTwoCheck_eq_true hτ
  ext β
  constructor
  · rintro ⟨⟨hβ, h1⟩, ⟨-, h2⟩⟩
    rw [rootChar_mulSingle, neg_one_zpow_eq_one_iff_emod hK2] at h1
    rw [rootChar_frameTwoChar, neg_one_zpow_eq_one_iff_emod hK2] at h2
    rcases (frameTwoCheck_sound hc hβ).1.1 ⟨h1, h2⟩ with h | h | h | h | h
    · exact Or.inl ⟨hβ, h⟩
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
  · intro hβ
    have hroot : IsRoot τ β := by
      rcases hβ with hβ | hβ
      · exact hβ.1
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
        rcases hβ with rfl | rfl | rfl | rfl
        · exact isRoot_highRoot τ
        · exact IsRoot.neg (isRoot_highRoot τ)
        · exact isRoot_frameTwoRoot hτ
        · exact IsRoot.neg (isRoot_frameTwoRoot hτ)
    have hev := (frameTwoCheck_sound hc hroot).1.2 (by
      rcases hβ with hβ | hβ
      · exact Or.inl hβ.2
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
        tauto)
    refine ⟨⟨hroot, ?_⟩, ⟨hroot, ?_⟩⟩
    · rw [rootChar_mulSingle, neg_one_zpow_eq_one_iff_emod hK2]
      exact hev.1
    · rw [rootChar_frameTwoChar, neg_one_zpow_eq_one_iff_emod hK2]
      exact hev.2

theorem exists_smul_highRoot_eq_frameTwoRoot (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ w : WeylGroup τ, w • highRoot τ = frameTwoRoot τ := by
  rcases hτ with rfl | hE
  · obtain ⟨w, hw⟩ := F4Pilot.exists_smul_eq_rootR (isRoot_frameTwoRoot (Or.inl rfl))
      (by decide)
    refine ⟨w⁻¹, ?_⟩
    have hR : highRoot Tag.F4 = F4Pilot.rootR := rfl
    rw [hR, ← hw, inv_smul_smul]
  · exact exists_smul_highRoot_eq hE (isRoot_frameTwoRoot (Or.inr hE))

theorem map_range_rootSL2_canonicalRep (w : WeylGroup τ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    (rootSL2 τ K β).range.map (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      (rootSL2 τ K (w • β)).range := by
  have h1 : (rootSL2 τ K β).range = rootSpan τ K {β, -β} :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.rootRankOneGroup_eq_rootSpan_pair hβ
  have h2 : (rootSL2 τ K (w • β)).range = rootSpan τ K {w • β, -(w • β)} :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.rootRankOneGroup_eq_rootSpan_pair
      (IsRoot.smul hβ w)
  rw [h1, h2, (canonical_weyl_root_transport τ K).1 w _ (by
    rintro α (rfl | rfl)
    · exact hβ
    · exact IsRoot.neg hβ)]
  congr 1
  rw [Set.image_pair, smul_neg]

theorem centralizer_rootSL2_frameTwo_le (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {A : SL2 K} (hAp : A ^ p = 1) (hA1 : A ≠ 1) :
    adjointGroup τ K ⊓ Subgroup.centralizer {rootSL2 τ K (frameTwoRoot τ) A} ≤
      toralCentralizer τ K (frameTwoChar τ K) := by
  classical
  have hd := hrRootData_of hτ
  obtain ⟨w, hw⟩ := exists_smul_highRoot_eq_frameTwoRoot hτ
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hnX : n ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w
  set ρ := rootSL2 τ K (highRoot τ) with hρ
  set ρ₁ := rootSL2 τ K (frameTwoRoot τ) with hρ₁
  have hmap : ρ.range.map (MulAut.conj n).toMonoidHom = ρ₁.range := by
    rw [hρ, map_range_rootSL2_canonicalRep w (isRoot_highRoot τ), hw]
  have hconj : ∀ B : SL2 K, ∃ B' : SL2 K, n * ρ B' * n⁻¹ = ρ₁ B := by
    intro B
    have hB : ρ₁ B ∈ ρ.range.map (MulAut.conj n).toMonoidHom := by rw [hmap]; exact ⟨B, rfl⟩
    obtain ⟨_, ⟨B', rfl⟩, hB'⟩ := hB
    exact ⟨B', hB'⟩
  have hHSL1 : HSL (-1 : Kˣ) ≠ 1 := by
    intro h
    have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [coe_HSL] at this
    exact hK2 ((neg_one_eq_one_iff (R := K)).1 this)
  have ht : n * ρ (HSL (-1)) * n⁻¹ = ρ₁ (HSL (-1)) := by
    have hmem : n * ρ (HSL (-1)) * n⁻¹ ∈ ρ₁.range := by
      rw [← hmap]
      exact ⟨_, ⟨HSL (-1), rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := hmem
    have hsc : s ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro B
      obtain ⟨B', hB'⟩ := hconj B
      apply rootSL2_injective_of_field (τ := τ) (K := K) (frameTwoRoot τ)
      change ρ₁ (B * s) = ρ₁ (s * B)
      rw [map_mul, map_mul, hs, ← hB']
      calc n * ρ B' * n⁻¹ * (n * ρ (HSL (-1)) * n⁻¹)
          = n * (ρ B' * ρ (HSL (-1))) * n⁻¹ := by group
        _ = n * (ρ (HSL (-1)) * ρ B') * n⁻¹ := by
            rw [← map_mul, ← map_mul, ← HSL_neg_one_mul_comm]
        _ = n * ρ (HSL (-1)) * n⁻¹ * (n * ρ B' * n⁻¹) := by group
    obtain ⟨r, hr2, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hsc
    have hr2' : r ^ 2 = 1 := by simpa using hr2
    have hr : r = 1 ∨ r = -1 := by
      have h : (r - 1) * (r + 1) = 0 := by linear_combination hr2'
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hr with rfl | rfl
    · exfalso
      have hs1 : s = 1 := Subtype.ext (by rw [← hrs, map_one, Matrix.SpecialLinearGroup.coe_one])
      rw [hs1, map_one] at hs
      apply hHSL1
      apply rootSL2_injective_of_field (τ := τ) (K := K) (highRoot τ)
      change ρ (HSL (-1)) = ρ 1
      rw [map_one]
      have : ρ (HSL (-1)) = n⁻¹ * (n * ρ (HSL (-1)) * n⁻¹) * n := by group
      rw [this, ← hs, mul_one, inv_mul_cancel]
    · have hsH : s = HSL (-1) := by
        refine Subtype.ext ?_
        rw [← hrs, coe_HSL]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [← hs, hsH]
  have ht₁ : ρ₁ (HSL (-1)) = rootDiagUnit τ (frameTwoChar τ K) := by
    rw [← rootTorusSL2_frameTwo hτ]
    rfl
  have htθ : ρ (HSL (-1)) = rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Kˣ)) := by
    rw [← rootTorusSL2_highRoot hτ]
    rfl
  intro g hg
  obtain ⟨hgX, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  refine Subgroup.mem_inf.2 ⟨hgX, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  obtain ⟨A', hA'⟩ := hconj A
  have hA'p : A' ^ p = 1 := by
    apply rootSL2_injective_of_field (τ := τ) (K := K) (highRoot τ)
    change ρ (A' ^ p) = ρ 1
    rw [map_pow, map_one]
    have : ρ A' = n⁻¹ * ρ₁ A * n := by rw [← hA']; group
    rw [this, inv_mul_mul_pow_eq, ← map_pow, hAp, map_one, mul_one, inv_mul_cancel]
  have hA'1 : A' ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one, mul_inv_cancel] at hA'
    exact hA1 (rootSL2_injective_of_field (τ := τ) (K := K) (frameTwoRoot τ) (by
      change ρ₁ A = ρ₁ 1
      rw [map_one, hA']))
  have hC : ∀ c : (AlgebraicClosure K)ˣ, c ≠ 1 → c ^ 2 ≠ 1 →
      toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) c) ≤
        toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) (-1)) :=
    fun c hc1 hc2 => toralCentralizer_mulSingle_le hc1 hc2 hd.abs_le hd.highRoot_highNode (-1)
  set g' := n⁻¹ * g * n with hg'
  have hg'X : g' ∈ adjointGroup τ K := mul_mem (mul_mem (inv_mem hnX) hgX) hnX
  have hg'c : g' * ρ A' = ρ A' * g' := by
    have : ρ A' = n⁻¹ * ρ₁ A * n := by rw [← hA']; group
    rw [this, hg']
    calc n⁻¹ * g * n * (n⁻¹ * ρ₁ A * n) = n⁻¹ * (g * ρ₁ A) * n := by group
      _ = n⁻¹ * (ρ₁ A * g) * n := by rw [hgc]
      _ = n⁻¹ * ρ₁ A * n * (n⁻¹ * g * n) := by group
  have hg't := Subgroup.mem_centralizer_singleton_iff.1
    (Subgroup.mem_inf.1 (centralizer_rootSL2_highRoot_le hτ hp hp2 hpK hA'p hA'1 hC
      (Subgroup.mem_inf.2 ⟨hg'X, Subgroup.mem_centralizer_singleton_iff.2 hg'c⟩))).2
  rw [← htθ] at hg't
  rw [← ht₁, ← ht]
  calc g * (n * ρ (HSL (-1)) * n⁻¹) = n * (g' * ρ (HSL (-1))) * n⁻¹ := by rw [hg']; group
    _ = n * (ρ (HSL (-1)) * g') * n⁻¹ := by rw [hg't]
    _ = n * ρ (HSL (-1)) * n⁻¹ * g := by rw [hg']; group

theorem rootSubgroup_frameTwo_le_centralizer (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    rootSubgroup τ K (ε • frameTwoRoot τ) ≤
      Subgroup.centralizer (rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) : Set (ModGL τ K)) := by
  have hc := frameTwoCheck_eq_true hτ
  have hγ := isRoot_frameTwoRoot hτ
  have hsub : rootSubgroup τ K (ε • frameTwoRoot τ) ≤ rootRankOneGroup τ K (frameTwoRoot τ) := by
    rw [(exceptional_Lang_root_rank_one_torus_transport τ K hγ).1]
    rcases hε with rfl | rfl
    · rw [one_smul]
      exact le_sup_left
    · rw [neg_one_smul]
      exact le_sup_right
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  have hle : rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) ≤
      Subgroup.centralizer ({x} : Set (ModGL τ K)) := by
    refine iSup₂_le fun δ hδ y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨h0, hp, hm⟩ := (frameTwoCheck_sound hc hδ.1).2 hδ.2
    have hy' : y ∈ rootRankOneGroup τ K δ := by
      rw [(exceptional_Lang_root_rank_one_torus_transport τ K hδ.1).1]
      exact (le_sup_left : rootSubgroup τ K δ ≤ rootSubgroup τ K δ ⊔ rootSubgroup τ K (-δ)) hy
    exact (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K hγ hδ.1 h0 hp hm
      x (hsub hx) y hy').symm
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem rootSpan_frameTwoKernel_le_normalizer (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    rootSpan τ K (leviRootsOff τ (frameTwoNodes τ) ∪
        {highRoot τ, -highRoot τ, frameTwoRoot τ, -frameTwoRoot τ}) ≤
      Subgroup.normalizer (rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) : Set (ModGL τ K)) := by
  have hd := hrRootData_of hτ
  have hLJ : rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) ≤ rootSpan τ K (perpRoots τ) :=
    rootSpan_mono fun β hβ => ⟨hβ.1, hβ.2 _ (highNode_mem_frameTwoNodes hτ)⟩
  have hθ : ∀ {ε : ℤ}, (ε = 1 ∨ ε = -1) → rootSubgroup τ K (ε • highRoot τ) ≤
      Subgroup.normalizer (rootSpan τ K (leviRootsOff τ (frameTwoNodes τ)) :
        Set (ModGL τ K)) := fun hε =>
    ((rootSubgroup_highRoot_le_centralizer (K := K) hε hd.abs_le hd.eq_highRoot
      hd.highRoot_highNode).trans (Subgroup.centralizer_le (G := ModGL τ K)
        fun x hx => hLJ hx)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine iSup₂_le fun β hβ => ?_
  rcases hβ with hβ | hβ
  · exact (le_iSup₂_of_le β hβ le_rfl :
      rootSubgroup τ K β ≤ rootSpan τ K (leviRootsOff τ (frameTwoNodes τ))).trans
      Subgroup.le_normalizer
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl | rfl | rfl
    · have := hθ (Or.inl rfl)
      rwa [one_smul] at this
    · have := hθ (Or.inr rfl)
      rwa [neg_one_smul] at this
    · have := rootSubgroup_frameTwo_le_centralizer (K := K) hτ (Or.inl rfl)
      rw [one_smul] at this
      exact this.trans (Subgroup.centralizer_le_normalizer _)
    · have := rootSubgroup_frameTwo_le_centralizer (K := K) hτ (Or.inr rfl)
      rw [neg_one_smul] at this
      exact this.trans (Subgroup.centralizer_le_normalizer _)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
