module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.SplitFrame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Closing
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Normalizer
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section TwF4

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice


theorem f4Six_row (i : Fin Tag.F4.rank) :
    (((coxeterSystem Tag.F4).wordProd TwClass.wordF4)⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ)) 1
      % 3 = if i = 1 then 2 else 0 := by
  rw [← CoxeterSystem.wordProd_reverse, wordProd_smul_eq_wordMat_mulVec]
  fin_cases i <;> decide +kernel


theorem natCast_three_ne_zero {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (h : ¬ 3 ∣ Nat.card K) : ((3 : ℕ) : L) ≠ 0 := by
  intro h0
  have hK0 : ((3 : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap K L)] at h0
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h0
  have hdvd : ringChar K ∣ 3 := (ringChar.spec K 3).1 hK0
  haveI := ringChar.charP K
  haveI : Fintype K := Fintype.ofFinite K
  have hne : ringChar K ≠ 0 := CharP.char_ne_zero_of_finite K (ringChar K)
  have hp : (ringChar K).Prime := (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hne
  have h3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  apply h
  rw [Nat.card_eq_fintype_card, hcard, h3]
  exact dvd_pow_self 3 n.ne_zero


theorem f4Six_row' (i : Fin TwClass.f4Six.tag.rank) :
    ((TwClass.f4Six.w)⁻¹ • (Pi.single i 1 : Fin TwClass.f4Six.tag.rank → ℤ))
        ⟨1, by decide⟩ % 3 = if i = ⟨1, by decide⟩ then 2 else 0 := by
  have h : ∀ i : Fin Tag.F4.rank,
      (((coxeterSystem Tag.F4).wordProd TwClass.wordF4)⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ))
        ⟨1, by decide⟩ % 3 = if i = ⟨1, by decide⟩ then 2 else 0 := by
    intro i
    rw [← CoxeterSystem.wordProd_reverse, wordProd_smul_eq_wordMat_mulVec]
    fin_cases i <;> decide +kernel
  exact h i

theorem zpow_eq_of_emod {G : Type*} [Group G] {x : G} (hx : orderOf x = 3) {m n : ℤ}
    (h : m % 3 = n % 3) : x ^ m = x ^ n := by
  rw [zpow_eq_zpow_iff_modEq, hx]
  exact h

theorem exists_cube_root_langLevi (K : Type) [Field K] [Finite K] (hnd : ¬ 3 ∣ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) : ∃ ω : D.Lˣ, orderOf ω = 3 := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hne3 : ((3 : ℕ) : D.L) ≠ 0 := natCast_three_ne_zero (K := K) hnd
  haveI : NeZero ((3 : ℕ) : D.L) := ⟨hne3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot D.L 3
  have hζu : IsUnit ζ := hζ.isUnit (by norm_num)
  obtain ⟨ω, hωζ⟩ : ∃ ω : D.Lˣ, (ω : D.L) = ζ := ⟨hζu.unit, hζu.unit_spec⟩
  refine ⟨ω, ?_⟩
  rw [← orderOf_units, hωζ]
  exact hζ.eq_orderOf.symm

theorem f4TwistedFrame_of (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (h3 : 3 ≤ Nat.card K) (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ)
    (hω3 : orderOf ω = 3) :
    ∃ z : adjointGroup TwClass.f4Six.tag K,
      baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
        D.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
          TwClass.f4Six.tag.rank) ω) * D.g⁻¹ ∧
      z ≠ 1 ∧ z ^ 3 = 1 ∧ ∃ X : Subgroup (adjointGroup TwClass.f4Six.tag K), ClosingFrameAt z X := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set i₁ : Fin TwClass.f4Six.tag.rank := ⟨1, by decide⟩ with hi₁
  set a : Fin TwClass.f4Six.tag.rank → D.Lˣ := Pi.mulSingle i₁ ω with ha
  have hchar : ∀ α : Fin TwClass.f4Six.tag.rank → ℤ, rootChar a α = ω ^ (α i₁) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single i₁]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hq : ((Nat.card K : ℕ) : ℤ) % 3 = 2 := by omega
  have hweyl : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct TwClass.f4Six.w
      (fun i => Units.map D.Fr.toMonoidHom (a i)) = a := by
    funext i
    unfold CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
    rw [← map_rootChar D.Fr a, hchar]
    have hFrω : Units.map D.Fr.toMonoidHom ω = ω ^ Nat.card K :=
      Units.ext (by simpa using D.hFr (ω : D.L))
    have hm := f4Six_row' i
    set m : ℤ := ((TwClass.f4Six.w)⁻¹ • (Pi.single i 1 : Fin TwClass.f4Six.tag.rank → ℤ)) i₁ with hmdef
    rw [map_zpow, hFrω, ← zpow_natCast, ← zpow_mul]
    by_cases hi : i = i₁
    · have hai : a i = ω := by rw [hi]; simp [ha]
      have h2 : m % 3 = 2 := by
        rw [if_pos (show i = ⟨1, by decide⟩ from hi)] at hm
        exact hm
      rw [hai]
      refine (zpow_eq_of_emod hω3 (n := 1) ?_).trans (zpow_one ω)
      rw [Int.mul_emod, hq, h2]
      norm_num
    · have hai : a i = 1 := by rw [ha]; exact Pi.mulSingle_eq_of_ne hi _
      have h0 : m % 3 = 0 := by
        rw [if_neg (show ¬ i = ⟨1, by decide⟩ from hi)] at hm
        exact hm
      rw [hai]
      refine (zpow_eq_of_emod hω3 (n := 0) ?_).trans (zpow_zero ω)
      rw [Int.mul_emod, hq, h0]
      norm_num
  set n := canonicalRep (coxeterSystem TwClass.f4Six.tag) D.L TwClass.f4Six.w with hn
  have hzF : Units.map (entrywiseHom D.Fr) (D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹) =
      D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹ := by
    have h1 := D.lang
    have h2 := units_map_entrywiseHom_rootDiagUnit (τ := TwClass.f4Six.tag) D.Fr a
    have h4 : n * rootDiagUnit TwClass.f4Six.tag (fun i => Units.map D.Fr.toMonoidHom (a i)) *
        n⁻¹ = rootDiagUnit TwClass.f4Six.tag a := by
      rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit, hweyl]
    rw [map_mul, map_mul, map_inv, h1, h2]
    calc D.g * n * rootDiagUnit TwClass.f4Six.tag (fun i => Units.map D.Fr.toMonoidHom (a i)) *
          (D.g * n)⁻¹ = D.g * (n * rootDiagUnit TwClass.f4Six.tag
            (fun i => Units.map D.Fr.toMonoidHom (a i)) * n⁻¹) * D.g⁻¹ := by group
      _ = D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹ := by rw [h4]
  have hgG : D.g ∈ adjointGroup TwClass.f4Six.tag D.L :=
    parabolicLevi_le_adjointGroup (K := D.L) (τ := TwClass.f4Six.tag) _ D.g_mem
  have hzhatT : rootDiagUnit TwClass.f4Six.tag a ∈ adjointGroup TwClass.f4Six.tag D.L :=
    torusGroup_le_adjointGroup_F4 (F4_rootDiagUnit_mem_torusGroup a)
  have hzLG : D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹ ∈
      adjointGroup TwClass.f4Six.tag D.L :=
    mul_mem (mul_mem hgG hzhatT) (inv_mem hgG)
  have hbij : Function.Bijective D.Fr := by
    refine ⟨D.Fr.injective, fun y => ?_⟩
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.card_pos (α := K))
    exact ⟨x, by rw [D.hFr]; exact hx⟩
  obtain ⟨z, hz, hzbc⟩ := mem_map_adjointGroup_of_frobenius_fixed (τ := TwClass.f4Six.tag)
    (k := K) (M := D.L) (Or.inr rfl) D.Fr D.hFr hbij hzLG hzF
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω3
    omega
  have hcube : rootDiagUnit TwClass.f4Six.tag a ^ 3 = 1 := by
    change (rootDiagUnitHom TwClass.f4Six.tag D.L a) ^ 3 = 1
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      funext i
      by_cases hi : i = i₁
      · have hai : a i = ω := by rw [hi]; simp [ha]
        have h3' : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
        simp [hai, h3']
      · have hai : a i = 1 := by rw [ha]; exact Pi.mulSingle_eq_of_ne hi _
        simp [hai]
    rw [this, map_one]
  have hS : ∀ S : Set (Fin TwClass.f4Six.tag.rank → ℤ), (∀ α ∈ S, 3 ∣ α i₁) →
      (∀ α ∈ S, IsRoot TwClass.f4Six.tag α) → ∀ α ∈ S, IsRoot TwClass.f4Six.tag α ∧
        rootChar a α = 1 := by
    intro S h3S hrS α hα
    refine ⟨hrS α hα, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hω3]
    exact_mod_cast h3S α hα
  have hS₁ : ∀ α ∈ TwClass.f4Six.S₁, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ f4LongList} := by rw [← QuasiF4.S₁_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.F4 1 3 := by
      rw [coset_eq]
      exact Or.inl hα'
    exact hmem.2
  have hS₂ : ∀ α ∈ TwClass.f4Six.S₂, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ f4ShortList} := by rw [← QuasiF4.S₂_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.F4 1 3 := by
      rw [coset_eq]
      exact Or.inr hα'
    exact hmem.2
  have hcomm : ∀ S : Set (Fin TwClass.f4Six.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1) →
      D.frame S ≤ Subgroup.centralizer ({z} : Set (ModGL TwClass.f4Six.tag K)) := by
    intro S hS' x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc := rootSpan_le_centralizer_rootDiagUnit (K := D.L) a hS' hx.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_mul, map_mul, hzbc]
    calc baseChangeGL (algebraMap K D.L) x * (D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹)
        = D.g * ((D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g⁻¹⁻¹) *
            rootDiagUnit TwClass.f4Six.tag a) * D.g⁻¹ := by group
      _ = D.g * (rootDiagUnit TwClass.f4Six.tag a * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x *
            D.g⁻¹⁻¹)) * D.g⁻¹ := by rw [hxc]
      _ = (D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x := by
          group
  have hKq : TwClass.f4Six.minQ ≤ Nat.card K := by
    show 3 ≤ Nat.card K
    exact h3
  have hle : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤ adjointGroup TwClass.f4Six.tag K :=
    sup_le inf_le_left inf_le_left
  have hq3 := twQuasi_of_ne_e6Six TwClass.f4Six (by decide) K hKq D
  refine ⟨⟨z, hz⟩, hzbc, ?_, ?_, frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D), ?_⟩
  · intro h1
    have h1' : z = 1 := congrArg Subtype.val h1
    have h2 : D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹ = 1 := by rw [← hzbc, h1', map_one]
    have h3' : rootDiagUnit TwClass.f4Six.tag a = 1 := by
      have := congrArg (fun x => D.g⁻¹ * x * D.g) h2
      simpa [mul_assoc] using this
    have h4 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
      (h3'.trans (rootDiagUnit_one (τ := TwClass.f4Six.tag) (K := D.L)).symm)
    have h5 := congrFun h4 i₁
    have hai : a i₁ = ω := by simp [ha]
    rw [hai] at h5
    exact hω1 (by simpa using h5)
  · apply Subtype.ext
    change z ^ 3 = 1
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_pow, hzbc, map_one]
    have := map_pow (MulAut.conj D.g) (rootDiagUnit TwClass.f4Six.tag a) 3
    simp only [MulAut.conj_apply] at this
    rw [← this, hcube]
    simp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hy' : (y : ModGL TwClass.f4Six.tag K) ∈
          TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D := hy
      have hsup : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤
          Subgroup.centralizer ({z} : Set (ModGL TwClass.f4Six.tag K)) :=
        sup_le (hcomm _ hS₁) (hcomm _ hS₂)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hy')
    · refine nonsolvable_frameIn hle ?_
      intro hs
      haveI := hs
      haveI h2 : Group.IsSolvable ↥(TwClass.f4Six.X₂ D) :=
        solvable_of_solvable_injective (Subgroup.inclusion_injective
          (le_sup_right : TwClass.f4Six.X₂ D ≤ TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D))
      obtain ⟨hperf, -, a₀, b₀, hab⟩ := hq3.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
      haveI : Nontrivial ↥(TwClass.f4Six.X₂ D) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
      exact (IsSolvable.commutator_lt_top_of_nontrivial
        (↥(TwClass.f4Six.X₂ D))).ne hperf.commutator_eq_top
    · exact closing_of_twFrameClosing hle (twClosing_f4Six K h3 D)
    · exact normalizerSolvable_of_twFrame hle (twNormalizer_f4Six K hKq D)

end TwF4

end CFSG.LieType.SeitzGeneration.ExcHighThree
