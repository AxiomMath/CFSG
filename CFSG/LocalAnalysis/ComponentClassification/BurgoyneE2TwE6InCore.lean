module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InLayer
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Descent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InCent

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
theorem thetaMap_e6_alpha4 :
    thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm (Pi.single (e6Node 3) 1) =
      Pi.single (e6Node 3) 1 := by
  rw [thetaMap_e6_nil_apply]
  funext j
  change (Pi.single (e6Node 3) 1 : Fin (Tag.rank .E6) → ℤ) (TwistTag.E6.perm.symm j) =
    (Pi.single (e6Node 3) 1 : Fin (Tag.rank .E6) → ℤ) j
  have h : ∀ i : Fin 6, (Pi.single 3 1 : Fin 6 → ℤ)
      ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm i) = (Pi.single 3 1 : Fin 6 → ℤ) i := by
    decide
  exact h j

theorem orbitGroup_two_cases
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (h5 : 5 ≤ D.q)
    (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) :
    (D.withOrbit J').orbitGroup = ⊥ ∨ (IsQuasisimple (D.withOrbit J').orbitGroup ∧
      ∃ w ∈ (D.withOrbit J').orbitGroup, w ≠ 1 ∧ w * w = 1) := by
  set D' := D.withOrbit J' with hD'
  have hθ' : ∀ γ, D'.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ) := hθ
  rcases e6_two_simpleRootsJ D hχ hθ J' with h0 | hA | hT
  · exact Or.inl (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
  ·
    right
    have h4 : Pi.single (e6Node 3) 1 ∈ D'.simpleRootsJ := by
      rw [hA]
      exact ⟨2, by funext i; fin_cases i <;> rfl⟩
    have h1 : Pi.single (e6Node 0) 1 ∈ D'.simpleRootsJ := by
      rw [hA]
      exact ⟨0, by funext i; fin_cases i <;> rfl⟩
    have hθ4 : D'.θ (toReal (Pi.single (e6Node 3) 1)) = toReal (Pi.single (e6Node 3) 1) := by
      rw [hθ', thetaMap_e6_alpha4]
    refine ⟨?_, exists_involution_orbitGroup_of_fixed D' h4 hθ4⟩
    refine (orthogonal_semilinear_fixed_root_quasisimplicity D').2.2.1 ?_
    have hO4 : thetaOrbit D'.θ (Pi.single (e6Node 3) 1) ∈ D'.orbits := ⟨_, h4, rfl⟩
    have hO1 : thetaOrbit D'.θ (Pi.single (e6Node 0) 1) ∈ D'.orbits := ⟨_, h1, rfl⟩
    have hne : thetaOrbit D'.θ (Pi.single (e6Node 3) 1) ≠
        thetaOrbit D'.θ (Pi.single (e6Node 0) 1) := by
      intro h
      have hmem : Pi.single (e6Node 0) 1 ∈ thetaOrbit D'.θ (Pi.single (e6Node 3) 1) := by
        rw [h]
        exact self_mem_thetaOrbit D'.θ _
      rw [thetaOrbit_eq_singleton D'.θ hθ4, Set.mem_singleton_iff] at hmem
      have h04 : (Pi.single (e6Node 0) 1 : Fin (Tag.rank .E6) → ℤ) ≠ Pi.single (e6Node 3) 1 := by
        decide
      exact h04 hmem
    have hfin : D'.orbits.Finite := by
      have hS : D'.simpleRootsJ.Finite := by
        rw [hA]
        exact Set.finite_range _
      refine (hS.image fun β => thetaOrbit D'.θ β).subset ?_
      rintro O ⟨β, hβ, rfl⟩
      exact ⟨β, hβ, rfl⟩
    calc 2 = ({thetaOrbit D'.θ (Pi.single (e6Node 3) 1),
          thetaOrbit D'.θ (Pi.single (e6Node 0) 1)} : Set (Set (Fin (Tag.rank .E6) → ℤ))).ncard :=
          (Set.ncard_pair hne).symm
      _ ≤ D'.orbits.ncard := Set.ncard_le_ncard (Set.insert_subset hO4
          (Set.singleton_subset_iff.2 hO1)) hfin
  ·
    right
    have hθθ : D'.θ (toReal hiE6) = toReal hiE6 := by
      rw [hθ', thetaMap_e6_hiE6]
    have hmem : hiE6 ∈ D'.simpleRootsJ := by
      rw [hT]
      exact Set.mem_singleton _
    refine ⟨?_, exists_involution_orbitGroup_of_fixed D' hmem hθθ⟩
    have horb : D'.orbits = {{hiE6}} := by
      ext O
      constructor
      · rintro ⟨β, hβ, rfl⟩
        rw [hT, Set.mem_singleton_iff] at hβ
        rw [hβ, thetaOrbit_eq_singleton D'.θ hθθ]
        exact Set.mem_singleton _
      · intro hO
        rw [Set.mem_singleton_iff] at hO
        exact ⟨hiE6, hmem, by rw [hO, thetaOrbit_eq_singleton D'.θ hθθ]⟩
    have hO : ({hiE6} : Set (Fin (Tag.rank .E6) → ℤ)) ∈ D'.orbits := by
      rw [horb]
      exact Set.mem_singleton _
    refine (orthogonal_semilinear_fixed_root_quasisimplicity D').2.2.2.1 {hiE6} horb ?_
    have hc1 : orbitCard ({hiE6} : Set (Fin (Tag.rank .E6) → ℤ)) = 1 := Set.ncard_singleton _
    rw [TwE7.card_orbitField D' hO, hc1, pow_one]
    change 3 < D.q
    omega

theorem twE6_two_oddNormal_eq_bot
    {e : ℕ} (h5 : 5 ≤ p ^ e) {x : ModGL .E6 k}
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (w : ModGL .E6 k)
    (hDχ : D.χ = signMaskChar .E6 2) (hDe : D.e = e)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ))
    (hcent : (fixedPointsIn (adjointGroup .E6 k)
        (frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k)) ⊓
          Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom =
        D.totalFixedGroup.map (adjointGroup .E6 k).subtype)
    (N : Subgroup (ModGL .E6 k))
    (hN : N ≤ ⁅fixedPointsIn (adjointGroup .E6 k)
        (frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup .E6 k)
            (frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k))⁆ ⊓
        Subgroup.centralizer {x})
    (hNn : ∀ y ∈ ⁅fixedPointsIn (adjointGroup .E6 k)
        (frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup .E6 k)
            (frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k))⁆ ⊓
        Subgroup.centralizer {x}, ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  classical
  set F := frobTwistGL .E6 k p e (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup .E6 k) F with hR
  set G := ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL .E6 k)) with hG
  set φ := (MulAut.conj w).toMonoidHom with hφ
  set Y := G.map φ with hY
  set Xh := D.totalFixedGroup.map (adjointGroup .E6 k).subtype with hXh
  set N' := N.map φ with hN'
  have hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ) := fun γ =>
    (hDθ γ).trans (congrArg toReal (thetaMap_e6_nil_apply γ).symm)
  have hq5 : 5 ≤ D.q := by
    change 5 ≤ p ^ D.e
    rw [hDe]
    exact h5
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hYX : Y ≤ Xh := by
    rw [← hcent]
    exact Subgroup.map_mono (inf_le_inf_right _ hRsub)
  have hpull : ∀ y ∈ Xh, ∃ z ∈ R ⊓ Subgroup.centralizer ({x} : Set (ModGL .E6 k)),
      y = w * z * w⁻¹ := by
    intro y hy
    rw [← hcent] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, rfl⟩
  have hYG : ∀ y ∈ Y, y ∈ adjointGroup .E6 k := by
    intro y hy
    obtain ⟨y', -, rfl⟩ := hYX hy
    exact y'.2
  have hCX : ∀ J' : Set.range D.classOrbit, ∀ c ∈ (D.withOrbit J').orbitGroup, c ∈ Xh := by
    intro J' c hc
    have h1 := (D.withOrbit J').orbitGroupC_le_fixedGroup ((D.withOrbit J').mk_mem_orbitGroupC hc)
    have h2 := D.kernelFixedGroup_le_totalFixedGroup
      (D.fixedGroup_withOrbit_le_kernelFixedGroup J' h1)
    exact ⟨_, h2, rfl⟩
  have hCY : ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      (D.withOrbit J').orbitGroup ≤ Y := by
    intro J' hq c hc
    set C := (D.withOrbit J').orbitGroup with hC
    have hperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 hq.1
    set P := C.map (MulAut.conj w⁻¹).toMonoidHom with hP
    have hPR : P ≤ R := by
      rintro _ ⟨y', hy', rfl⟩
      obtain ⟨z', hz', hyz'⟩ := hpull y' (hCX J' y' hy')
      have e : (MulAut.conj w⁻¹).toMonoidHom y' = z' := by
        rw [hyz']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact (Subgroup.mem_inf.1 hz').1
    have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hperf]
    have hPH : P ≤ ⁅R, R⁆ := by
      rw [← hPperf]
      exact Subgroup.commutator_mono hPR hPR
    obtain ⟨z, hz, hcz⟩ := hpull c (hCX J' c hc)
    have hzP : z ∈ P := ⟨c, hc, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hcz]
      group⟩
    refine ⟨z, Subgroup.mem_inf.2 ⟨hPH hzP, (Subgroup.mem_inf.1 hz).2⟩, ?_⟩
    rw [hcz]
    rfl
  have hCn : ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      ∀ y ∈ Y, ∀ c ∈ (D.withOrbit J').orbitGroup, y * c * y⁻¹ ∈ (D.withOrbit J').orbitGroup := by
    intro J' hq y hy c hc
    obtain ⟨y', hy', rfl⟩ := hYX hy
    exact conj_mem_orbitGroup_withOrbit D hq hy' hc
  have hN'Y : N' ≤ Y := Subgroup.map_mono hN
  have hN'n : ∀ y ∈ Y, ∀ n ∈ N', y * n * y⁻¹ ∈ N' := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨n, hn, rfl⟩
    have h := Subgroup.mem_map_of_mem φ (hNn y hy n hn)
    rw [map_mul, map_mul, map_inv] at h
    exact h
  have hodd' : Odd (Nat.card N') := by
    rwa [← Nat.card_congr (N.equivMapOfInjective φ (MulAut.conj w).injective).toEquiv]
  have hordN : ∀ n ∈ N', Odd (orderOf n) := fun n hn => by
    have h1 : orderOf (⟨n, hn⟩ : N') ∣ Nat.card N' := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd' h1
  have hcent2 : ∀ z ∈ adjointGroup .E6 k,
      (∀ J' : Set.range D.classOrbit, ∀ c ∈ (D.withOrbit J').orbitGroup, z * c = c * z) →
        z ^ 2 = 1 := fun z hz hzc =>
    sq_eq_one_of_commute_orbitGroups_two D (le_trans (by norm_num) hq5) hDχ hθ hz hzc
  have hcomm : ∀ J' : Set.range D.classOrbit, ∀ n ∈ N', ∀ c ∈ (D.withOrbit J').orbitGroup,
      n * c = c * n := by
    intro J' n hn c hc
    rcases orbitGroup_two_cases D hq5 hDχ hθ J' with hbot | ⟨hq, w₀, hw₀, hw₀1, hw₀2⟩
    · rw [hbot, Subgroup.mem_bot] at hc
      rw [hc, mul_one, one_mul]
    set C := (D.withOrbit J').orbitGroup with hC
    have hinter : ∀ m ∈ N', m ∈ C → m = 1 := by
      intro m hm hmC
      set I : Subgroup C := (N' ⊓ C).subgroupOf C with hI_def
      have hI : I.Normal := ⟨fun i hi c' => by
        obtain ⟨hi1, hi2⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hi)
        refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
        · exact hN'n _ (hCY J' hq c'.2) _ hi1
        · exact mul_mem (mul_mem c'.2 hi2) (inv_mem c'.2)⟩
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hI with htop | hcen
      · exfalso
        have hw : w₀ ∈ N' := by
          have h1 : (⟨w₀, hw₀⟩ : C) ∈ I := by
            rw [htop]
            exact Subgroup.mem_top _
          exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h1)).1
        exact hw₀1 (eq_one_of_sq_eq_one_of_odd (by rw [sq]; exact hw₀2) (hordN _ hw))
      · have hmZ := hcen (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hm, hmC⟩) :
          (⟨m, hmC⟩ : C) ∈ I)
        have hzc : ∀ J'' : Set.range D.classOrbit, ∀ c'' ∈ (D.withOrbit J'').orbitGroup,
            m * c'' = c'' * m := by
          intro J'' c'' hc''
          by_cases hJ : J'' = J'
          · subst hJ
            exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hmZ ⟨c'', hc''⟩).symm)
          · exact (commute_orbitGroup_of_ne D (Ne.symm hJ) hmC hc'').eq
        exact eq_one_of_sq_eq_one_of_odd (hcent2 m (hYG m (hN'Y hm)) hzc) (hordN m hm)
    have h1 : n * c * n⁻¹ * c⁻¹ ∈ N' := by
      have e : n * c * n⁻¹ * c⁻¹ = n * (c * n⁻¹ * c⁻¹) := by group
      rw [e]
      exact mul_mem hn (hN'n c (hCY J' hq hc) _ (inv_mem hn))
    have h2 : n * c * n⁻¹ * c⁻¹ ∈ C := mul_mem (hCn J' hq n (hN'Y hn) c hc) (inv_mem hc)
    have h3 := hinter _ h1 h2
    calc n * c = n * c * n⁻¹ * c⁻¹ * (c * n) := by group
      _ = c * n := by rw [h3, one_mul]
  have hN'bot : N' = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    exact eq_one_of_sq_eq_one_of_odd (hcent2 n (hYG n (hN'Y hn)) fun J' c hc =>
      hcomm J' n hn c hc) (hordN n hn)
  exact (Subgroup.map_eq_bot_iff_of_injective N (MulAut.conj w).injective).1 hN'bot

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In
