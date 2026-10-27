module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.SplitFrame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Normalizer
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Malle.SeitzCube.Landing
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux16

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

section TwE8

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Malle.SeitzCube

set_option linter.unusedSectionVars false


theorem e8Ten_row (i : Fin TwClass.e8Ten.tag.rank) :
    ((TwClass.e8Ten.w)⁻¹ • (Pi.single i 1 : Fin TwClass.e8Ten.tag.rank → ℤ))
        ⟨4, by decide⟩ % 5 = if i = ⟨4, by decide⟩ then 4 else 0 := by
  have h : ∀ i : Fin Tag.E8.rank,
      (((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten)⁻¹ •
          (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) ⟨4, by decide⟩ % 5 =
        if i = ⟨4, by decide⟩ then 4 else 0 := by
    intro i
    rw [← CoxeterSystem.wordProd_reverse, wordProd_smul_eq_wordMat_mulVec]
    fin_cases i <;> decide +kernel
  exact h i

theorem zpow_eq_of_emod_five {G : Type*} [Group G] {x : G} (hx : orderOf x = 5) {m n : ℤ}
    (h : m % 5 = n % 5) : x ^ m = x ^ n := by
  rw [zpow_eq_zpow_iff_modEq, hx]
  exact h

theorem natCast_five_ne_zero {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (h : ¬ 5 ∣ Nat.card K) : ((5 : ℕ) : L) ≠ 0 := by
  intro h0
  have hK0 : ((5 : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap K L)] at h0
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h0
  have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).1 hK0
  haveI := ringChar.charP K
  haveI : Fintype K := Fintype.ofFinite K
  have hne : ringChar K ≠ 0 := CharP.char_ne_zero_of_finite K (ringChar K)
  have hp : (ringChar K).Prime := (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hne
  have h5 : ringChar K = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hdvd
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  apply h
  rw [Nat.card_eq_fintype_card, hcard, h5]
  exact dvd_pow_self 5 n.ne_zero

theorem exists_fifth_root_langLevi (K : Type) [Field K] [Finite K] (hnd : ¬ 5 ∣ Nat.card K)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) : ∃ ζ : D.Lˣ, orderOf ζ = 5 := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hne5 : ((5 : ℕ) : D.L) ≠ 0 := natCast_five_ne_zero (K := K) hnd
  haveI : NeZero ((5 : ℕ) : D.L) := ⟨hne5⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot D.L 5
  have hζu : IsUnit ζ := hζ.isUnit (by norm_num)
  obtain ⟨ω, hωζ⟩ : ∃ ω : D.Lˣ, (ω : D.L) = ζ := ⟨hζu.unit, hζu.unit_spec⟩
  refine ⟨ω, ?_⟩
  rw [← orderOf_units, hωζ]
  exact hζ.eq_orderOf.symm

theorem e8TwistedFrame_of (K : Type) [Field K] [Finite K] (hK : 5 ∣ Nat.card K + 1)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (ζ : D.Lˣ) (hζ : orderOf ζ = 5) :
    ∃ z : adjointGroup TwClass.e8Ten.tag K,
      baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.e8Ten.tag K) =
        D.g * rootDiagUnit TwClass.e8Ten.tag (Pi.mulSingle (⟨4, by decide⟩ : Fin
          TwClass.e8Ten.tag.rank) ζ) * D.g⁻¹ ∧
      z ≠ 1 ∧ z ^ 5 = 1 ∧
        ∃ X : Subgroup (adjointGroup TwClass.e8Ten.tag K), ClosingFrameAt z X := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set i₁ : Fin TwClass.e8Ten.tag.rank := ⟨4, by decide⟩ with hi₁
  set a : Fin TwClass.e8Ten.tag.rank → D.Lˣ := Pi.mulSingle i₁ ζ with ha
  have hchar : ∀ α : Fin TwClass.e8Ten.tag.rank → ℤ, rootChar a α = ζ ^ (α i₁) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single i₁]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hq : ((Nat.card K : ℕ) : ℤ) % 5 = 4 := by omega
  have hweyl : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct TwClass.e8Ten.w
      (fun i => Units.map D.Fr.toMonoidHom (a i)) = a := by
    funext i
    unfold CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
    rw [← map_rootChar D.Fr a, hchar]
    have hFrζ : Units.map D.Fr.toMonoidHom ζ = ζ ^ Nat.card K :=
      Units.ext (by simpa using D.hFr (ζ : D.L))
    have hm := e8Ten_row i
    set m : ℤ := ((TwClass.e8Ten.w)⁻¹ • (Pi.single i 1 : Fin TwClass.e8Ten.tag.rank → ℤ)) i₁
      with hmdef
    rw [map_zpow, hFrζ, ← zpow_natCast, ← zpow_mul]
    by_cases hi : i = i₁
    · have hai : a i = ζ := by rw [hi]; simp [ha]
      have h2 : m % 5 = 4 := by
        rw [if_pos (show i = ⟨4, by decide⟩ from hi)] at hm
        exact hm
      rw [hai]
      have key : ζ ^ (((Nat.card K : ℕ) : ℤ) * m) = ζ ^ (1 : ℤ) := by
        apply zpow_eq_of_emod_five hζ
        rw [Int.mul_emod, hq, h2]
        norm_num
      rw [key, zpow_one]
    · have hai : a i = 1 := by rw [ha]; exact Pi.mulSingle_eq_of_ne hi _
      have h0 : m % 5 = 0 := by
        rw [if_neg (show ¬ i = ⟨4, by decide⟩ from hi)] at hm
        exact hm
      rw [hai]
      have key : ζ ^ (((Nat.card K : ℕ) : ℤ) * m) = ζ ^ (0 : ℤ) := by
        apply zpow_eq_of_emod_five hζ
        rw [Int.mul_emod, hq, h0]
        norm_num
      rw [key, zpow_zero]
  set n := canonicalRep (coxeterSystem TwClass.e8Ten.tag) D.L TwClass.e8Ten.w with hn
  have hzF : Units.map (entrywiseHom D.Fr) (D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹) =
      D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹ := by
    have h1 := D.lang
    have h2 := units_map_entrywiseHom_rootDiagUnit (τ := TwClass.e8Ten.tag) D.Fr a
    have h4 : n * rootDiagUnit TwClass.e8Ten.tag (fun i => Units.map D.Fr.toMonoidHom (a i)) *
        n⁻¹ = rootDiagUnit TwClass.e8Ten.tag a := by
      rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit, hweyl]
    rw [map_mul, map_mul, map_inv, h1, h2]
    calc D.g * n * rootDiagUnit TwClass.e8Ten.tag (fun i => Units.map D.Fr.toMonoidHom (a i)) *
          (D.g * n)⁻¹ = D.g * (n * rootDiagUnit TwClass.e8Ten.tag
            (fun i => Units.map D.Fr.toMonoidHom (a i)) * n⁻¹) * D.g⁻¹ := by group
      _ = D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹ := by rw [h4]
  have hgG : D.g ∈ adjointGroup TwClass.e8Ten.tag D.L :=
    parabolicLevi_le_adjointGroup (K := D.L) (τ := TwClass.e8Ten.tag) _ D.g_mem
  have hzhatT : rootDiagUnit TwClass.e8Ten.tag a ∈ adjointGroup TwClass.e8Ten.tag D.L :=
    CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_adjointGroup_E8 a
  have hzLG : D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹ ∈
      adjointGroup TwClass.e8Ten.tag D.L :=
    mul_mem (mul_mem hgG hzhatT) (inv_mem hgG)
  obtain ⟨z, hz, hzbc⟩ : ∃ z : ModGL TwClass.e8Ten.tag K, z ∈ adjointGroup TwClass.e8Ten.tag K ∧
      baseChangeGL (algebraMap K D.L) z = D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹ :=
    Subgroup.mem_map.1 (mem_map_baseChange_of_frobenius_fixed_E8 (K := K) (L := D.L)
      D.Fr D.hFr hzLG hzF)
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    omega
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hcube : rootDiagUnit TwClass.e8Ten.tag a ^ 5 = 1 := by
    change (rootDiagUnitHom TwClass.e8Ten.tag D.L a) ^ 5 = 1
    rw [← map_pow]
    have : a ^ 5 = 1 := by
      funext i
      by_cases hi : i = i₁
      · have hai : a i = ζ := by rw [hi]; simp [ha]
        simp [hai, h5]
      · have hai : a i = 1 := by rw [ha]; exact Pi.mulSingle_eq_of_ne hi _
        simp [hai]
    rw [this, map_one]
  have hS : ∀ S : Set (Fin TwClass.e8Ten.tag.rank → ℤ), (∀ α ∈ S, 5 ∣ α i₁) →
      (∀ α ∈ S, IsRoot TwClass.e8Ten.tag α) → ∀ α ∈ S, IsRoot TwClass.e8Ten.tag α ∧
        rootChar a α = 1 := by
    intro S h5S hrS α hα
    refine ⟨hrS α hα, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hζ]
    exact_mod_cast h5S α hα
  have hS₁ : ∀ α ∈ TwClass.e8Ten.S₁, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ e8ListB} := by rw [← QuasiE8Ten.S₁_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.E8 4 5 := by
      rw [e8_coset_eq]
      exact Or.inr hα'
    exact hmem.2
  have hS₂ : ∀ α ∈ TwClass.e8Ten.S₂, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ e8ListA} := by rw [← QuasiE8Ten.S₂_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.E8 4 5 := by
      rw [e8_coset_eq]
      exact Or.inl hα'
    exact hmem.2
  have hcomm : ∀ S : Set (Fin TwClass.e8Ten.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwClass.e8Ten.tag α ∧ rootChar a α = 1) →
      D.frame S ≤ Subgroup.centralizer ({z} : Set (ModGL TwClass.e8Ten.tag K)) := by
    intro S hS' x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc := rootSpan_le_centralizer_rootDiagUnit (K := D.L) a hS' hx.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_mul, map_mul, hzbc]
    calc baseChangeGL (algebraMap K D.L) x * (D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹)
        = D.g * ((D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g⁻¹⁻¹) *
            rootDiagUnit TwClass.e8Ten.tag a) * D.g⁻¹ := by group
      _ = D.g * (rootDiagUnit TwClass.e8Ten.tag a * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x *
            D.g⁻¹⁻¹)) * D.g⁻¹ := by rw [hxc]
      _ = (D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x := by
          group
  have hKq : TwClass.e8Ten.minQ ≤ Nat.card K := by
    show 2 ≤ Nat.card K
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hle : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ adjointGroup TwClass.e8Ten.tag K :=
    sup_le inf_le_left inf_le_left
  have hq3 := twQuasi_of_ne_e6Six TwClass.e8Ten (by decide) K hKq D
  refine ⟨⟨z, hz⟩, hzbc, ?_, ?_, frameIn (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D), ?_⟩
  · intro h1
    have h1' : z = 1 := congrArg Subtype.val h1
    have h2 : D.g * rootDiagUnit TwClass.e8Ten.tag a * D.g⁻¹ = 1 := by rw [← hzbc, h1', map_one]
    have h3' : rootDiagUnit TwClass.e8Ten.tag a = 1 := by
      have := congrArg (fun x => D.g⁻¹ * x * D.g) h2
      simpa [mul_assoc] using this
    have h4 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
      (h3'.trans (rootDiagUnit_one (τ := TwClass.e8Ten.tag) (K := D.L)).symm)
    have h5' := congrFun h4 i₁
    have hai : a i₁ = ζ := by simp [ha]
    rw [hai] at h5'
    exact hζ1 (by simpa using h5')
  · apply Subtype.ext
    change z ^ 5 = 1
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_pow, hzbc, map_one]
    have := map_pow (MulAut.conj D.g) (rootDiagUnit TwClass.e8Ten.tag a) 5
    simp only [MulAut.conj_apply] at this
    rw [← this, hcube]
    simp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hy' : (y : ModGL TwClass.e8Ten.tag K) ∈
          TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D := hy
      have hsup : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤
          Subgroup.centralizer ({z} : Set (ModGL TwClass.e8Ten.tag K)) :=
        sup_le (hcomm _ hS₁) (hcomm _ hS₂)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hy')
    · refine nonsolvable_frameIn hle ?_
      intro hs
      haveI := hs
      haveI h2 : Group.IsSolvable ↥(TwClass.e8Ten.X₂ D) :=
        solvable_of_solvable_injective (Subgroup.inclusion_injective
          (le_sup_right : TwClass.e8Ten.X₂ D ≤ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D))
      obtain ⟨hperf, -, a₀, b₀, hab⟩ := hq3.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
      haveI : Nontrivial ↥(TwClass.e8Ten.X₂ D) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
      exact (IsSolvable.commutator_lt_top_of_nontrivial
        (↥(TwClass.e8Ten.X₂ D))).ne hperf.commutator_eq_top
    · have h3 : 3 ≤ Nat.card K := by
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        omega
      exact closing_of_twFrameClosing hle (E8TenAux.twClosing_e8Ten_three K D h3)
    · exact normalizerSolvable_of_twFrame hle (twNormalizer_e8Ten K hKq D)

end TwE8

end CFSG.LieType.SeitzGeneration.ExcHigh
