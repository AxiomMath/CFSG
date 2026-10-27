module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
import CFSG.RankThree.PartOne.KE.E8TwoA2Family
import CFSG.RankThree.PartOne.SEITZ7.SzPair
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem exists_coord_sq_eq_one_inv {θ : Fin TwistTag.E6.tag.rank → ℤ}
    (hθ : IsRoot TwistTag.E6.tag θ) : ∃ j, θ j * θ j = 1 := by
  have h : ∀ α ∈ rootFinset TwistTag.E6.tag, ∃ j, α j * α j = 1 := by decide +kernel
  exact h θ (mem_rootFinset.2 hθ)

private theorem rootChar_mul_inv {τ : Tag} {K : Type} [Field K] (a b : Fin τ.rank → Kˣ)
    (v : Fin τ.rank → ℤ) : rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem rootChar_pow_inv {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (n : ℕ)
    (v : Fin τ.rank → ℤ) : rootChar (a ^ n) v = rootChar a v ^ n := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (a i ^ v i), ← zpow_mul, mul_comm]

private theorem rootChar_mulSingle_inv {τ : Tag} {K : Type} [Field K] (j : Fin τ.rank) (c : Kˣ)
    (v : Fin τ.rank → ℤ) : rootChar (Pi.mulSingle j c) v = c ^ v j := by
  rw [rootChar, Finset.prod_eq_single j
    (fun k _ hk => by rw [Pi.mulSingle_eq_of_ne hk, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]

private theorem rootChar_coroot_inv {τ : Tag} {K : Type} [Field K] (β : Fin τ.rank → ℤ)
    (c : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => c ^ iform β (Pi.single i 1)) v = c ^ iform β v :=
  CFSG.ClassicalInvolution.ModelFacts.Levi.rootChar_thetaDiag β c v

private theorem iform_neg_left_inv {τ : Tag} (x y : Fin τ.rank → ℤ) :
    iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left, neg_one_mul]

private theorem iform_neg_right_inv {τ : Tag} (x y : Fin τ.rank → ℤ) :
    iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right, neg_one_mul]

private theorem rootChar_eq_one_of_commute_inv {L : Type} [Field L]
    (a : Fin TwistTag.E6.tag.rank → Lˣ) {θ : Fin TwistTag.E6.tag.rank → ℤ}
    (hθ : IsRoot TwistTag.E6.tag θ)
    (h : rootDiagUnit TwistTag.E6.tag a * pinnedX TwistTag.E6.tag L θ 1 =
      pinnedX TwistTag.E6.tag L θ 1 * rootDiagUnit TwistTag.E6.tag a) :
    rootChar a θ = 1 := by
  have h1 := CFSG.LieType.Chevalley.rootDiagUnit_conj_pinnedX a hθ (1 : L)
  rw [h, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective TwistTag.E6.tag L θ h1
  apply Units.ext
  simpa using h2.symm

private theorem rootDiagUnit_commute_inv {L : Type} [Field L]
    (b : Fin TwistTag.E6.tag.rank → Lˣ) {θ : Fin TwistTag.E6.tag.rank → ℤ}
    (hθ : IsRoot TwistTag.E6.tag θ) (hbθ : rootChar b θ = 1) :
    ∀ z ∈ rootSpan TwistTag.E6.tag L {θ, -θ},
      rootDiagUnit TwistTag.E6.tag b * z = z * rootDiagUnit TwistTag.E6.tag b := by
  have hbθ' : rootChar b (-θ) = 1 := by
    have h0 := rootChar_sub b 0 θ
    rw [zero_sub, rootChar_zero, hbθ] at h0
    simpa using h0
  have hle : rootSpan TwistTag.E6.tag L {θ, -θ} ≤ Subgroup.centralizer
      ({rootDiagUnit TwistTag.E6.tag b} : Set (ModGL TwistTag.E6.tag L)) := by
    refine iSup₂_le fun α hα => ?_
    have hαb : IsRoot TwistTag.E6.tag α ∧ rootChar b α = 1 := by
      rcases hα with rfl | rfl
      · exact ⟨hθ, hbθ⟩
      · exact ⟨IsRoot.neg hθ, hbθ'⟩
    rw [rootSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h := CFSG.LieType.Chevalley.rootDiagUnit_conj_pinnedX (K := L) b hαb.1 c
    rw [hαb.2, Units.val_one, one_mul] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  intro z hz
  exact (Subgroup.mem_centralizer_iff.1 (hle hz)) (rootDiagUnit TwistTag.E6.tag b) rfl

private theorem exists_pow_succ_eq_inv {L : Type} [Field L] [IsAlgClosed L] (q : ℕ)
    {θ : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    (a : Fin TwistTag.E6.tag.rank → Lˣ) (ha : rootChar a θ = 1) :
    ∃ b : Fin TwistTag.E6.tag.rank → Lˣ, b ^ (q + 1) = a ∧ rootChar b θ = 1 := by
  have hroot : ∀ k, ∃ z : Lˣ, z ^ (q + 1) = a k := fun k => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a k : Lˣ) : L) (Nat.succ_pos q)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero q)] at hz
      exact (a k).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose b₀ hb₀ using hroot
  have hb₀' : b₀ ^ (q + 1) = a := funext hb₀
  obtain ⟨j, hj⟩ := exists_coord_sq_eq_one_inv hθ
  have hζ : rootChar b₀ θ ^ (q + 1) = 1 := by
    rw [← rootChar_pow_inv, hb₀', ha]
  have hε : (Pi.mulSingle j (rootChar b₀ θ ^ (-θ j)) : Fin TwistTag.E6.tag.rank → Lˣ) ^ (q + 1) =
      1 := by
    funext k
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases hk : k = j
    · rw [hk, Pi.mulSingle_eq_same, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hζ, one_zpow]
    · rw [Pi.mulSingle_eq_of_ne hk, one_pow]
  refine ⟨b₀ * Pi.mulSingle j (rootChar b₀ θ ^ (-θ j)), ?_, ?_⟩
  · rw [mul_pow, hε, mul_one, hb₀']
  · rw [rootChar_mul_inv, rootChar_mulSingle_inv, ← zpow_mul, neg_mul, hj, zpow_neg_one,
      mul_inv_cancel]

private theorem conj_coroot_inv {L : Type} [Field L] {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) {m : ModGL TwistTag.E6.tag L}
    (hm : m ∈ monomialSubgroup TwistTag.E6.tag L)
    (hmW : MapsRootLines (m : (Module.End L (RootModule TwistTag.E6.tag L))ˣ)
      (rootReflection β)) (d : Lˣ) :
    m * rootDiagUnit TwistTag.E6.tag (fun i => d ^ iform β (Pi.single i 1)) * m⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i => d⁻¹ ^ iform β (Pi.single i 1)) := by
  have hc := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
    (⟨m, hm⟩ : monomialSubgroup TwistTag.E6.tag L) (fun i => d ^ iform β (Pi.single i 1))
  rw [weylQuotientHom_eq (g := ⟨m, hm⟩) hmW] at hc
  refine hc.trans ?_
  congr 1
  refine CFSG.HardMathSupport.Timmesfeld.Tables.T1b.eq_of_rootChar_eq fun u => ?_
  rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct, rootChar_coroot_inv,
    rootChar_coroot_inv, ← iform_smul (rootReflection β) β ((rootReflection β)⁻¹ • u),
    smul_inv_smul, rootReflection_smul_self hβ, iform_neg_left_inv, zpow_neg, inv_zpow]

private theorem exists_reflection_inv {L : Type} [Field L]
    (F' : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L)
    (hFn : ∀ u : WeylGroup TwistTag.E6.tag,
      F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) ∈ monomialSubgroup TwistTag.E6.tag L ∧
        MapsRootLines (F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) :
          (Module.End L (RootModule TwistTag.E6.tag L))ˣ) u)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    ∃ y ∈ rootSpan TwistTag.E6.tag L {β, -β}, y ∈ adjointGroup TwistTag.E6.tag L ∧
      y ∈ monomialSubgroup TwistTag.E6.tag L ∧
      MapsRootLines (y : (Module.End L (RootModule TwistTag.E6.tag L))ˣ) (rootReflection β) ∧
      F' y ∈ monomialSubgroup TwistTag.E6.tag L ∧
      MapsRootLines (F' y : (Module.End L (RootModule TwistTag.E6.tag L))ˣ) (rootReflection β) := by
  obtain ⟨w, i, hwi⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [rootReflection_eq_conj hwi]
  have hmono : ∀ u : WeylGroup TwistTag.E6.tag,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L u ∈ monomialSubgroup TwistTag.E6.tag L :=
    fun u => Subgroup.mem_sup_right (canonicalRep_mem_closure _ _ u)
  have hC : ∀ u : WeylGroup TwistTag.E6.tag,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L u ∈ adjointGroup TwistTag.E6.tag L :=
    fun u => canonicalRep_mem_adjointGroup _ L u
  have hsS : canonicalRep (coxeterSystem TwistTag.E6.tag) L (simple TwistTag.E6.tag i) ∈
      rootSpan TwistTag.E6.tag L
        {(Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ), -Pi.single i 1} := by
    rw [canonicalRep_simple]
    exact CFSG.RankThree.PartOne.SEITZ7.weylElt_mem_rootSpan' (τ := TwistTag.E6.tag) (K := L)
      (S := {(Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ), -Pi.single i 1}) (j := i)
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _)) 1
  have hroots : ∀ α ∈ ({(Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ), -Pi.single i 1} :
      Set (Fin TwistTag.E6.tag.rank → ℤ)), IsRoot TwistTag.E6.tag α := by
    intro α hα
    rcases hα with rfl | rfl
    · exact isRoot_single TwistTag.E6.tag i
    · exact IsRoot.neg (isRoot_single TwistTag.E6.tag i)
  have hmap := (canonical_weyl_root_transport TwistTag.E6.tag L).1 w _ hroots
  have himg : (fun α => w • α) '' ({(Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ),
      -Pi.single i 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)) = {β, -β} := by
    rw [Set.image_pair, smul_neg, hwi]
  rw [himg] at hmap
  have hyS : canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (simple TwistTag.E6.tag i) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹ ∈
        rootSpan TwistTag.E6.tag L {β, -β} := by
    rw [← hmap]
    exact ⟨_, hsS, rfl⟩
  have hFy : F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (simple TwistTag.E6.tag i) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹) =
      F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L w) *
        F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L (simple TwistTag.E6.tag i)) *
        (F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L w))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨_, hyS, mul_mem (mul_mem (hC w) (hC _)) (inv_mem (hC w)),
    mul_mem (mul_mem (hmono w) (hmono _)) (inv_mem (hmono w)),
    ((mapsRootLines_canonicalRep w).mul (mapsRootLines_canonicalRep _)).mul
      (mapsRootLines_canonicalRep w).inv, ?_, ?_⟩
  · rw [hFy]
    exact mul_mem (mul_mem (hFn w).1 (hFn _).1) (inv_mem (hFn w).1)
  · rw [hFy]
    exact ((hFn w).2.mul (hFn _).2).mul (hFn w).2.inv

private theorem exists_fixed_inverter_aux {L : Type} [Field L] [IsAlgClosed L] {q : ℕ}
    (F' : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L)
    (hFd : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
      F' (rootDiagUnit TwistTag.E6.tag b) = rootDiagUnit TwistTag.E6.tag (b ^ q)⁻¹)
    (hFn : ∀ u : WeylGroup TwistTag.E6.tag,
      F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) ∈ monomialSubgroup TwistTag.E6.tag L ∧
        MapsRootLines (F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) :
          (Module.End L (RootModule TwistTag.E6.tag L))ˣ) u)
    (hFS : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ →
      ∀ g ∈ rootSpan TwistTag.E6.tag L {γ, -γ}, F' g ∈ rootSpan TwistTag.E6.tag L {γ, -γ})
    {θ β : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    (hβ : IsRoot TwistTag.E6.tag β) (hθβ : iform θ β = 0) :
    ∃ m ∈ adjointGroup TwistTag.E6.tag L, F' m = m ∧
      (∀ d : Lˣ, m * rootDiagUnit TwistTag.E6.tag (fun i => d ^ iform β (Pi.single i 1)) * m⁻¹ =
        rootDiagUnit TwistTag.E6.tag (fun i => d⁻¹ ^ iform β (Pi.single i 1))) ∧
      ∀ z ∈ rootSpan TwistTag.E6.tag L {θ, -θ}, m * z = z * m := by
  have hpair : ∀ {γ : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag γ →
      ∀ α ∈ ({γ, -γ} : Set (Fin TwistTag.E6.tag.rank → ℤ)), IsRoot TwistTag.E6.tag α := by
    intro γ hγ α hα
    rcases hα with rfl | rfl
    · exact hγ
    · exact IsRoot.neg hγ
  have hcomm : ∀ x ∈ rootSpan TwistTag.E6.tag L {β, -β},
      ∀ z ∈ rootSpan TwistTag.E6.tag L {θ, -θ}, x * z = z * x := by
    refine CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (τ := TwistTag.E6.tag) (L := L)
      (Or.inr (Or.inl rfl)) (hpair hβ) (hpair hθ) ?_
    have h0 : iform β θ = 0 := by rw [iform_comm, hθβ]
    intro α hα γ hγ
    rw [dotProduct_mulVec_eq_iform]
    rcases hα with rfl | rfl <;> rcases hγ with rfl | rfl <;>
      simp only [iform_neg_left_inv, iform_neg_right_inv, h0, neg_zero]
  obtain ⟨y, hyS, hyC, hyM, hyW, hFyM, hFyW⟩ := exists_reflection_inv F' hFn hβ
  have hFyS : F' y ∈ rootSpan TwistTag.E6.tag L {β, -β} := hFS β hβ y hyS
  have ht : y⁻¹ * F' y ∈ torusGroup TwistTag.E6.tag L := by
    refine CFSG.LieType.Chevalley.mem_torusGroup_of_mapsRootLines_one
      (mul_mem (inv_mem hyM) hFyM) ?_
    have h := hyW.inv.mul hFyW
    rwa [inv_mul_cancel] at h
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hFya : F' y = y * rootDiagUnit TwistTag.E6.tag a := by
    rw [← ha, mul_inv_cancel_left]
  have hXθ : pinnedX TwistTag.E6.tag L θ 1 ∈ rootSpan TwistTag.E6.tag L {θ, -θ} := by
    have h1 : pinnedX TwistTag.E6.tag L θ 1 ∈ rootSubgroup TwistTag.E6.tag L θ :=
      Subgroup.subset_closure ⟨1, rfl⟩
    exact (le_iSup₂ (f := fun δ (_ : δ ∈ ({θ, -θ} : Set (Fin TwistTag.E6.tag.rank → ℤ))) =>
      rootSubgroup TwistTag.E6.tag L δ) θ (Set.mem_insert _ _)) h1
  have hχa : rootChar a θ = 1 := by
    refine rootChar_eq_one_of_commute_inv a hθ ?_
    rw [← ha]
    exact ((Commute.inv_left (hcomm y hyS _ hXθ)).mul_left (hcomm _ hFyS _ hXθ)).eq
  obtain ⟨b, hb, hbθ⟩ := exists_pow_succ_eq_inv q hθ a hχa
  have hbz := rootDiagUnit_commute_inv (L := L) b hθ hbθ
  have hbT : rootDiagUnit TwistTag.E6.tag b ∈ torusGroup TwistTag.E6.tag L :=
    rootDiagUnit_mem_torusGroup (τ := TwistTag.E6.tag) (K := L) b
  refine ⟨y * rootDiagUnit TwistTag.E6.tag b, ?_, ?_, fun d => ?_, fun z hz => ?_⟩
  · have hTC : torusGroup TwistTag.E6.tag L ≤ adjointGroup TwistTag.E6.tag L :=
      (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
    exact mul_mem hyC (hTC hbT)
  · rw [map_mul, hFya, hFd, mul_assoc, ← CFSG.LieType.Chevalley.rootDiagUnit_mul]
    congr 2
    rw [← hb, pow_succ, mul_comm (b ^ q) b, mul_assoc, mul_inv_cancel, mul_one]
  · refine conj_coroot_inv hβ (mul_mem hyM (Subgroup.mem_sup_left hbT)) ?_ d
    have h := hyW.mul (mapsRootLines_of_mem_torusGroup hbT)
    rwa [mul_one] at h
  · have h1 : y * z = z * y := hcomm y hyS z hz
    calc y * rootDiagUnit TwistTag.E6.tag b * z = y * (rootDiagUnit TwistTag.E6.tag b * z) :=
          mul_assoc _ _ _
      _ = y * (z * rootDiagUnit TwistTag.E6.tag b) := by rw [hbz z hz]
      _ = y * z * rootDiagUnit TwistTag.E6.tag b := (mul_assoc _ _ _).symm
      _ = z * y * rootDiagUnit TwistTag.E6.tag b := by rw [h1]
      _ = z * (y * rootDiagUnit TwistTag.E6.tag b) := mul_assoc _ _ _

theorem exists_fixed_coroot_inverter {L : Type} [Field L] [IsAlgClosed L] {q : ℕ}
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ q) {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    {θ β : Fin TwistTag.E6.tag.rank → ℤ} (hθ : IsRoot TwistTag.E6.tag θ)
    (hβ : IsRoot TwistTag.E6.tag β) (hθβ : CFSG.LieType.Steinberg.Adjoint.iform θ β = 0) :
    ∃ m ∈ adjointGroup TwistTag.E6.tag L,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v * twistHom TwistTag.E6 L Fr m *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ = m ∧
      (∀ d : Lˣ, m * rootDiagUnit TwistTag.E6.tag
          (fun i => d ^ CFSG.LieType.Steinberg.Adjoint.iform β (Pi.single i 1)) * m⁻¹ =
        rootDiagUnit TwistTag.E6.tag
          (fun i => d⁻¹ ^ CFSG.LieType.Steinberg.Adjoint.iform β (Pi.single i 1))) ∧
      ∀ y ∈ rootSpan TwistTag.E6.tag L {θ, -θ}, m * y = y * m := by
  have hρρ : ∀ x : Fin TwistTag.E6.tag.rank → ℤ,
      permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm x) = x :=
    fun x => Lang.E6Descent.TwistedDiag.permLattice_permLattice' x
  have hvw : v = Lang.E6Descent.twE6W0 := by
    refine ext_single fun k => ?_
    have h1 : v • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        -(permLattice TwistTag.E6.perm (Pi.single k 1)) := by
      have h := hv (permLattice TwistTag.E6.perm (Pi.single k 1))
      rwa [hρρ] at h
    exact h1.trans (Lang.E6Descent.twE6W0_smul _).symm
  subst hvw
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h := hFr 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  have hsurj : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hq0)
    exact ⟨z, by rw [hFr, hz]⟩
  set F' : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) L
      Lang.E6Descent.twE6W0)).toMonoidHom.comp (twistHom TwistTag.E6 L Fr) with hF'
  have hFd : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
      F' (rootDiagUnit TwistTag.E6.tag b) = rootDiagUnit TwistTag.E6.tag (b ^ q)⁻¹ :=
    fun b => Lang.E6Descent.TwistedDiag.theta_rootDiagUnit Fr hFr b
  have hFn : ∀ u : WeylGroup TwistTag.E6.tag,
      F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) ∈ monomialSubgroup TwistTag.E6.tag L ∧
        MapsRootLines (F' (canonicalRep (coxeterSystem TwistTag.E6.tag) L u) :
          (Module.End L (RootModule TwistTag.E6.tag L))ˣ) u :=
    fun u => ⟨Lang.E6Descent.TwistedDiag.mem_monomial_theta_canonicalRep Fr u,
      Lang.E6Descent.TwistedDiag.mapsRootLines_theta_canonicalRep Fr u⟩
  have hFS : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ →
      ∀ g ∈ rootSpan TwistTag.E6.tag L {γ, -γ}, F' g ∈ rootSpan TwistTag.E6.tag L {γ, -γ} := by
    intro γ hγ g hg
    have hS : ∀ α ∈ ({γ, -γ} : Set (Fin TwistTag.E6.tag.rank → ℤ)), IsRoot TwistTag.E6.tag α := by
      intro α hα
      rcases hα with rfl | rfl
      · exact hγ
      · exact IsRoot.neg hγ
    have hS' : ∀ α ∈ permLattice TwistTag.E6.perm ''
        ({γ, -γ} : Set (Fin TwistTag.E6.tag.rank → ℤ)), IsRoot TwistTag.E6.tag α := by
      rintro _ ⟨α, hα, rfl⟩
      exact (hS α hα).permLattice TwistTag.E6.cartan_perm
    have h1 : twistHom TwistTag.E6 L Fr g ∈
        rootSpan TwistTag.E6.tag L (permLattice TwistTag.E6.perm '' {γ, -γ}) := by
      rw [← map_twistHom_rootSpan TwistTag.E6 L hsurj hS]
      exact Subgroup.mem_map_of_mem _ hg
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) L
      Lang.E6Descent.twE6W0)).toMonoidHom h1
    rw [(canonical_weyl_root_transport TwistTag.E6.tag L).1 Lang.E6Descent.twE6W0 _ hS'] at h2
    simp only [Set.image_image, Set.image_insert_eq, Set.image_singleton, hv, neg_neg] at h2
    rw [Set.pair_comm] at h2
    exact h2
  obtain ⟨m, hm, hFm, hinv, hcen⟩ := exists_fixed_inverter_aux F' hFd hFn hFS hθ hβ hθβ
  exact ⟨m, hm, hFm, hinv, hcen⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
