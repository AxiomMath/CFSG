module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerData
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerDecomp

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4

section Twisted25

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem exists_hom_phi4m_twentyfive (hF : IsReeFrob 2 F) :
    ∃ Φ : (rootsOfUnity 25 L) × (rootsOfUnity 25 L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4m) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) planeU) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted_aux_explicit hF wPhi4m (m := 25) (by decide)
    (toMat 4 [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]])
    planeU 0 1 (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num⟩
  · intro s k
    have e : (ReeTag.F4.perm k : Fin 4) = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := perm_vec k
    have h2 : (ReeTag.F4.relationExponent 2 (ReeTag.F4.perm k) : ℤ) =
        (![2 ^ 2, 2 ^ 2, 2 ^ (2 + 1), 2 ^ (2 + 1)] : Fin 4 → ℤ) (ReeTag.F4.perm k) :=
      relExp_vec 2 _
    rw [h2, e]
    fin_cases s <;> fin_cases k <;> simp [toMat, lget, planeU] <;> decide

end Twisted25

section Frame25

variable (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]

structure Plane25 where
  D : ReeFrameData K (AlgebraicClosure K) 2
  g₀ : ModGL ReeTag.F4.tag (AlgebraicClosure K)
  hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K)
  hFg₀ : Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) wPhi4m
  Ψ : (rootsOfUnity 25 (AlgebraicClosure K)) × (rootsOfUnity 25 (AlgebraicClosure K)) →*
    ReeTag.F4.reeGamma K 2
  Ψinj : Function.Injective Ψ
  hΨ : ∀ z, reeConj g₀ (Ψ z) = rootDiagUnit ReeTag.F4.tag
    (expTuple ((z.1 : (AlgebraicClosure K)ˣ)) (z.2 : (AlgebraicClosure K)ˣ) planeU)

variable {K}

theorem plane25_nonempty (hK : Nat.card K = 2 ^ (2 * 2 + 1)) : Nonempty (Plane25 K) := by
  classical
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Φ, hΦinj, hΦF, hΦ⟩ := exists_hom_phi4m_twentyfive D.isFrob
  obtain ⟨g₀, hg₀, hFg₀, Ψ, hΨinj, hΨ⟩ := exists_hom_reeGamma_explicit D wPhi4m Φ hΦinj hΦF
  refine ⟨⟨D, g₀, hg₀, hFg₀, Ψ, hΨinj, fun z => ?_⟩⟩
  rw [reeConj_apply, hΨ z, ← hΦ z]
  group

end Frame25

section PlaneDecomp

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem ncard_kernel_inter_long {L : Type} [Field L] {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 25)
    (a b : ℕ) :
    (rootCharKernel (expTuple (ξ ^ a) (ξ ^ b) planeU) ∩ ReeTag.F4.longRoots).ncard =
      ((kerFin a b).filter fun α => ReeTag.F4.quadForm α = 4).card := by
  rw [← Set.ncard_coe_finset, rootCharKernel_expTuple_pow hξ, ReeTag.longRoots_eq]
  congr 1
  ext α
  simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter]
  have h4 : (2 * (ReeTag.F4.prime : ℤ)) = 4 := by simp [ReeTag.prime]
  rw [h4]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Finset.mem_filter.1 h1).1, h2⟩

theorem ncard_kernel_inter_short {L : Type} [Field L] {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 25)
    (a b : ℕ) :
    (rootCharKernel (expTuple (ξ ^ a) (ξ ^ b) planeU) ∩ ReeTag.F4.shortRoots).ncard =
      ((kerFin a b).filter fun α => ReeTag.F4.quadForm α = 2).card := by
  rw [← Set.ncard_coe_finset, rootCharKernel_expTuple_pow hξ, ReeTag.shortRoots_eq]
  congr 1
  ext α
  simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (Finset.mem_filter.1 h1).1, h2⟩


theorem sylowShape_five (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    SylowShape 5 2 2 (ReeTag.F4.reeGamma K 2) := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have := sylowShape_ree_phi4 (K := K) (a := 2) hK Nat.prime_five (by norm_num) (by norm_num)
  rwa [factorization_five_phi4] at this

theorem card_sylow_five (hK : Nat.card K = 2 ^ (2 * 2 + 1)) (P : Sylow 5 (ReeTag.F4.reeGamma K 2)) :
    Nat.card (P : Subgroup (ReeTag.F4.reeGamma K 2)) = 625 := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := sylowShape_five hK (P : Subgroup (ReeTag.F4.reeGamma K 2)) P.isPGroup'
    P.not_dvd_index
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  simp


theorem exists_plane_of_sylow (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (P : Sylow 5 (ReeTag.F4.reeGamma K 2)) :
    ∃ E : Subgroup (ReeTag.F4.reeGamma K 2), E ≤ (P : Subgroup (ReeTag.F4.reeGamma K 2)) ∧
      CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := sylowShape_five hK (P : Subgroup (ReeTag.F4.reeGamma K 2)) P.isPGroup'
    P.not_dvd_index
  let f : V5 →* ReeTag.F4.reeGamma K 2 :=
    (P : Subgroup (ReeTag.F4.reeGamma K 2)).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  refine ⟨(powMonoidHom 5 : V5 →* V5).ker.map f, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact (e.symm k).2
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨_, ⟨k₁, hk₁, rfl⟩⟩ := a
    obtain ⟨_, ⟨k₂, hk₂, rfl⟩⟩ := b
    refine Subtype.ext ?_
    show f k₁ * f k₂ = f k₂ * f k₁
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨k, hk, rfl⟩
    rw [← map_pow]
    have : k ^ 5 = 1 := hk
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hf, card_ker5]
    norm_num


omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem exists_primitive_twentyfive (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ ξ : Lˣ, IsPrimitiveRoot ξ 25 := by
  have hp : (25 : L) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff L 2 25).1 (by exact_mod_cast h)
    omega
  have : NeZero (25 : ℕ) := ⟨by norm_num⟩
  have : NeZero ((25 : ℕ) : L) := ⟨by exact_mod_cast hp⟩
  obtain ⟨ξ₀, hξ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 25
  lift ξ₀ to Lˣ using hξ₀.isUnit (by norm_num)
  rw [IsPrimitiveRoot.coe_units_iff] at hξ₀
  exact ⟨ξ₀, hξ₀⟩

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem card_rootsOfUnity_twentyfive (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] :
    Nat.card (rootsOfUnity 25 L) = 25 := by
  have hp : (5 : L) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff L 2 5).1 (by exact_mod_cast h)
    omega
  have := card_rootsOfUnity_pow (p := 5) (e := 2) (L := L) hp
  norm_num at this
  exact this

theorem card_range_plane25 (F : Plane25 K) : Nat.card F.Ψ.range = 625 := by
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  rw [← Nat.card_congr (MonoidHom.ofInjective F.Ψinj).toEquiv, Nat.card_prod,
    card_rootsOfUnity_twentyfive]


omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem zpow_pow_five_aux {L : Type} [Field L] {x : Lˣ} (hx : x ^ 5 = 1) (n : ℤ) :
    (x ^ n) ^ 5 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem mem_rootsOfUnity_pow_aux {L : Type} [Field L] {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ 25) (s : ℕ) :
    ξ ^ s ∈ rootsOfUnity 25 L := by
  rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]

theorem plane_decomp (hK : Nat.card K = 2 ^ (2 * 2 + 1)) (F : Plane25 K)
    (z : (rootsOfUnity 25 (AlgebraicClosure K)) × (rootsOfUnity 25 (AlgebraicClosure K)))
    (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1) :
    ∃ A Sg : Subgroup (ReeTag.F4.reeGamma K 2), A ≤ F.Ψ.range ∧ Nat.card A = 25 ∧ IsCyclic A ∧
      (∀ α ∈ A, ∀ s ∈ Sg, α * s = s * α) ∧ A ⊓ Sg = ⊥ ∧
      A ⊔ Sg = Subgroup.centralizer ({F.Ψ z} : Set (ReeTag.F4.reeGamma K 2)) ∧ F.Ψ z ∈ A ∧
      Nonempty (Sg ≃* suzukiGroup 2 K) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ξ, hξ⟩ := exists_primitive_twentyfive (AlgebraicClosure K)
  have hexp : ∀ w : rootsOfUnity 25 (AlgebraicClosure K), ∃ s < 25, (w : (AlgebraicClosure K)ˣ) = ξ ^ s :=
    fun w => by
      obtain ⟨i, hi, h⟩ := hξ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 25 _).1 w.2)
      exact ⟨i, hi, h.symm⟩
  obtain ⟨a, ha, ha'⟩ := hexp z.1
  obtain ⟨b, hb, hb'⟩ := hexp z.2
  have hz5' : (z.1 : (AlgebraicClosure K)ˣ) ^ 5 = 1 ∧ (z.2 : (AlgebraicClosure K)ˣ) ^ 5 = 1 := by
    have h1 := congrArg Prod.fst hz5
    have h2 := congrArg Prod.snd hz5
    exact ⟨by simpa using congrArg Subtype.val h1, by simpa using congrArg Subtype.val h2⟩
  have h5a : 5 ∣ a := by
    have := hz5'.1
    rw [ha', ← pow_mul, hξ.pow_eq_one_iff_dvd] at this
    omega
  have h5b : 5 ∣ b := by
    have := hz5'.2
    rw [hb', ← pow_mul, hξ.pow_eq_one_iff_dvd] at this
    omega
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hz1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [ha', h.1, pow_zero]; rfl
    · rw [hb', h.2, pow_zero]; rfl
  have hcnt := kerFin_counts a (Finset.mem_range.2 ha) b (Finset.mem_range.2 hb) h5a h5b hab
  set b₀ : Fin ReeTag.F4.tag.rank → (AlgebraicClosure K)ˣ :=
    expTuple (z.1 : (AlgebraicClosure K)ˣ) (z.2 : (AlgebraicClosure K)ˣ) planeU with hb₀
  have hb₀' : b₀ = expTuple (ξ ^ a) (ξ ^ b) planeU := by rw [hb₀, ha', hb']
  have hxb : reeConj F.g₀ (F.Ψ z) = rootDiagUnit ReeTag.F4.tag b₀ := F.hΨ z
  have hbF : rootDiagUnit ReeTag.F4.tag b₀ ∈ twistedFixed F.D.F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) wPhi4m) := by
    rw [← hxb]
    exact reeConj_mem_twistedFixed F.D F.hg₀ F.hFg₀ _
  have hbp : ∀ i, b₀ i ^ 5 = 1 := by
    intro i
    show ((z.1 : (AlgebraicClosure K)ˣ) ^ planeU 0 i * (z.2 : (AlgebraicClosure K)ˣ) ^ planeU 1 i) ^ 5 = 1
    rw [mul_pow, zpow_pow_five_aux hz5'.1, zpow_pow_five_aux hz5'.2, mul_one]
  have hb1 : b₀ ≠ 1 := by
    intro h
    apply hz1
    apply F.Ψinj
    apply reeConj_injective F.g₀
    rw [hxb, h, rootDiagUnit_one, map_one, map_one]
  have hlong : (rootCharKernel b₀ ∩ ReeTag.F4.longRoots).ncard = 4 := by
    rw [hb₀', ncard_kernel_inter_long hξ]
    exact (kerFin_counts a (Finset.mem_range.2 ha) b (Finset.mem_range.2 hb) h5a h5b hab).1
  have hshort : (rootCharKernel b₀ ∩ ReeTag.F4.shortRoots).ncard = 4 := by
    rw [hb₀', ncard_kernel_inter_short hξ]
    exact (kerFin_counts a (Finset.mem_range.2 ha) b (Finset.mem_range.2 hb) h5a h5b hab).2
  obtain ⟨A, Sg, hAmem, hSgmem, hcomm, hinf, hsup, hxA, hSz⟩ :=
    exists_decomp_of_kernel F.D hK wPhi4m F.hg₀ F.hFg₀ hbF hbp hb1 hlong hshort (F.Ψ z) hxb
  have hT₀card : Nat.card F.Ψ.range = 625 := card_range_plane25 F
  obtain ⟨P₁⟩ : Nonempty (Sylow 5 (ReeTag.F4.reeGamma K 2)) := inferInstance
  have hfac : 5 ^ (Nat.card (ReeTag.F4.reeGamma K 2)).factorization 5 = 625 := by
    rw [← Sylow.card_eq_multiplicity P₁]
    exact card_sylow_five hK P₁
  let P₀ : Sylow 5 (ReeTag.F4.reeGamma K 2) := Sylow.ofCard F.Ψ.range (by rw [hfac, hT₀card])
  have hP₀ : (P₀ : Subgroup (ReeTag.F4.reeGamma K 2)) = F.Ψ.range := Sylow.coe_ofCard _ _
  obtain ⟨E₀, hE₀P, hE₀ab, hE₀c⟩ := exists_plane_of_sylow hK P₀
  have hcent := centralizer_plane_eq_sylow hK P₀ E₀ hE₀P hE₀ab hE₀c
  rw [hP₀] at hcent hE₀P
  have hAle : A ≤ F.Ψ.range := by
    intro γ hγ
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨w, rfl⟩ := hE₀P he
    obtain ⟨c, -, hc⟩ := mem_ZGrp.1 ((hAmem γ).1 hγ)
    apply reeConj_injective F.g₀
    rw [map_mul, map_mul, F.hΨ w, ← hc, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hAeq : ∀ w : (rootsOfUnity 25 (AlgebraicClosure K)) × (rootsOfUnity 25 (AlgebraicClosure K)),
      F.Ψ w ∈ A ↔ ∀ α ∈ rootCharKernel b₀,
        rootChar (expTuple (w.1 : (AlgebraicClosure K)ˣ) (w.2 : (AlgebraicClosure K)ˣ) planeU) α = 1 := by
    intro w
    rw [hAmem, F.hΨ w]
    constructor
    · intro h
      obtain ⟨c, hc, hcw⟩ := mem_ZGrp.1 h
      have := rootDiagUnit_injective hcw
      rw [← this]
      exact hc
    · intro h
      exact mem_ZGrp.2 ⟨_, h, rfl⟩
  let X := {w : (rootsOfUnity 25 (AlgebraicClosure K)) × (rootsOfUnity 25 (AlgebraicClosure K)) //
    ∀ α ∈ rootCharKernel b₀,
      rootChar (expTuple (w.1 : (AlgebraicClosure K)ˣ) (w.2 : (AlgebraicClosure K)ˣ) planeU) α = 1}
  have hAX : Nat.card A = Nat.card X := by
    symm
    refine Nat.card_eq_of_bijective (fun w => ⟨F.Ψ w.1, (hAeq w.1).2 w.2⟩) ⟨?_, ?_⟩
    · intro w w' h
      exact Subtype.ext (F.Ψinj (congrArg Subtype.val h))
    · intro γ
      obtain ⟨w, hw⟩ := hAle γ.2
      exact ⟨⟨w, (hAeq w).1 (hw ▸ γ.2)⟩, Subtype.ext hw⟩
  have hker : rootCharKernel b₀ = ↑(kerFin a b) := by
    rw [hb₀']
    exact rootCharKernel_expTuple_pow hξ a b
  have hXL : Nat.card X = (kerLat a b).card := by
    rw [← Nat.card_eq_finsetCard]
    symm
    refine Nat.card_eq_of_bijective
      (fun st => (⟨(⟨ξ ^ st.1.1, mem_rootsOfUnity_pow_aux hξ _⟩,
          ⟨ξ ^ st.1.2, mem_rootsOfUnity_pow_aux hξ _⟩), ?_⟩ : X)) ⟨?_, ?_⟩
    · intro α hα
      rw [hker] at hα
      have hst := (Finset.mem_filter.1 st.2).2 α hα
      exact (rootChar_expTuple_pow_eq_one_iff hξ _ _ α).2 hst
    · intro st st' h
      have h1 := congrArg (fun x : X => ((x.1.1 : (rootsOfUnity 25 (AlgebraicClosure K))) :
        (AlgebraicClosure K)ˣ)) h
      have h2 := congrArg (fun x : X => ((x.1.2 : (rootsOfUnity 25 (AlgebraicClosure K))) :
        (AlgebraicClosure K)ˣ)) h
      have hs := (Finset.mem_filter.1 st.2).1
      have hs' := (Finset.mem_filter.1 st'.2).1
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hs hs'
      refine Subtype.ext (Prod.ext (hξ.pow_inj hs.1 hs'.1 h1) (hξ.pow_inj hs.2 hs'.2 h2))
    · rintro ⟨w, hw⟩
      obtain ⟨s, hs, hs'⟩ := hexp w.1
      obtain ⟨t, ht, ht'⟩ := hexp w.2
      refine ⟨⟨(s, t), Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_range.2 hs, Finset.mem_range.2 ht⟩, fun α hα => ?_⟩⟩, ?_⟩
      · have := hw α (by rw [hker]; exact hα)
        rw [hs', ht'] at this
        exact (rootChar_expTuple_pow_eq_one_iff hξ _ _ α).1 this
      · refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
        · exact hs'.symm
        · exact ht'.symm
  have hcardA : Nat.card A = 25 := by
    rw [hAX, hXL]
    exact (kerLat_card a (Finset.mem_range.2 ha) b (Finset.mem_range.2 hb) h5a h5b hab).1
  refine ⟨A, Sg, hAle, hcardA, ?_, hcomm, hinf, hsup, hxA, hSz⟩
  obtain ⟨⟨s, t⟩, hst, hst5⟩ :=
    (kerLat_card a (Finset.mem_range.2 ha) b (Finset.mem_range.2 hb) h5a h5b hab).2
  have hst' := Finset.mem_filter.1 hst
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hst'
  let w₀ : (rootsOfUnity 25 (AlgebraicClosure K)) × (rootsOfUnity 25 (AlgebraicClosure K)) :=
    (⟨ξ ^ s, mem_rootsOfUnity_pow_aux hξ _⟩, ⟨ξ ^ t, mem_rootsOfUnity_pow_aux hξ _⟩)
  have hw₀A : F.Ψ w₀ ∈ A := by
    rw [hAeq]
    intro α hα
    rw [hker] at hα
    exact (rootChar_expTuple_pow_eq_one_iff hξ s t α).2 (hst'.2 α hα)
  have hord : orderOf w₀ = 25 := by
    have h25 : w₀ ^ (5 ^ 2) = 1 := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show (ξ ^ s) ^ (5 ^ 2) = 1
        rw [← pow_mul, mul_comm, pow_mul, show (5 ^ 2 : ℕ) = 25 by norm_num, hξ.pow_eq_one, one_pow]
      · show (ξ ^ t) ^ (5 ^ 2) = 1
        rw [← pow_mul, mul_comm, pow_mul, show (5 ^ 2 : ℕ) = 25 by norm_num, hξ.pow_eq_one, one_pow]
    have h5 : ¬ w₀ ^ (5 ^ 1) = 1 := by
      intro h
      have h1 : (ξ ^ s) ^ 5 = 1 := by simpa using congrArg (fun x => ((x.1 : (AlgebraicClosure K)ˣ))) h
      have h2 : (ξ ^ t) ^ 5 = 1 := by simpa using congrArg (fun x => ((x.2 : (AlgebraicClosure K)ˣ))) h
      rw [← pow_mul, hξ.pow_eq_one_iff_dvd] at h1 h2
      rcases hst5 with h | h <;> [exact h (by omega); exact h (by omega)]
    have := orderOf_eq_prime_pow (p := 5) (n := 1) h5 (by simpa using h25)
    simpa using this
  have hordΨ : orderOf (F.Ψ w₀) = 25 := by
    rw [orderOf_injective F.Ψ F.Ψinj, hord]
  exact isCyclic_of_orderOf_eq_card (⟨F.Ψ w₀, hw₀A⟩ : A) (by
    rw [Subgroup.orderOf_mk, hordΨ, hcardA])

end PlaneDecomp
end CFSG.HardMathSupport.Malle.LocalAction
