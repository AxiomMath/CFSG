module

public import CFSG.LieType.Chevalley.E6SignedGraphRankOne
public import CFSG.LieType.Chevalley.E6RootInvolutionNoInverted
public import CFSG.LieType.Chevalley.E6SignedGraphWeyl
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

theorem rootDiagUnit_signTuple :
    rootDiagUnit TwistTag.E6.tag (signTuple K) =
      torusElt TwistTag.E6.tag K ⟨0, by decide⟩ (-1) *
        torusElt TwistTag.E6.tag K ⟨3, by decide⟩ (-1) *
          torusElt TwistTag.E6.tag K ⟨5, by decide⟩ (-1) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  have h2 : (-1 : Kˣ) ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, neg_one_sq]
  have hpar : ∀ j : Fin TwistTag.E6.tag.rank,
      (TwistTag.E6.tag.cartan ⟨0, by decide⟩ j + TwistTag.E6.tag.cartan ⟨3, by decide⟩ j +
        TwistTag.E6.tag.cartan ⟨5, by decide⟩ j) % 2 = if j = ⟨1, by decide⟩ then 1 else 0 := by
    decide +kernel
  simp only [Pi.mul_apply, ← _root_.zpow_add]
  rw [zpow_eq_zpow_emod _ h2, hpar j]
  split_ifs with hj
  · rw [hj, zpow_one]
    rfl
  · rw [zpow_zero, signTuple_of_ne hj]

theorem rootDiagUnit_signTuple_mem_torusGroup :
    rootDiagUnit TwistTag.E6.tag (signTuple K) ∈ torusGroup TwistTag.E6.tag K := by
  rw [rootDiagUnit_signTuple]
  exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
    (torusElt_mem_torusGroup _ _)

theorem orbitImage_pair
    {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.orbit a =
      {TwistTag.E6.orbitMin a, TwistTag.E6.perm (TwistTag.E6.orbitMin a)})
    (w : WeylGroup TwistTag.E6.tag) :
    orbitImage w a = {w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec),
      w • (Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 : E6Vec)} := by
  rw [orbitImage, h, Finset.image_insert, Finset.image_singleton]

theorem orbitImage_single
    {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a}) (w : WeylGroup TwistTag.E6.tag) :
    orbitImage w a = {w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)} := by
  rw [orbitImage, h, Finset.image_singleton]

theorem smul_single_ne
    {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a)
    (w : WeylGroup TwistTag.E6.tag) :
    w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec) ≠
      w • (Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 : E6Vec) :=
  fun e => h (TwistTag.E6.injective_smul_single w e).symm

theorem exists_orbitImage_eq
    {O : Finset E6Vec} (hO : O ∈ orbits) :
    ∃ w ∈ relWeylTwist TwistTag.E6, ∃ a, orbitImage w a = O := by
  obtain ⟨⟨α, hα, rfl⟩, -⟩ := hO
  obtain ⟨w, hw, a, he⟩ := TwistTag.E6.exists_diagramOrbit_eq hα
  exact ⟨w, hw, a, he.symm⟩

theorem orbitSign_eq_one_of_mem_orbits
    {w : WeylGroup TwistTag.E6.tag}
    {a : Fin TwistTag.E6.foldedTag.rank} (hO : orbitImage w a ∈ orbits)
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a) :
    orbitSign K w a = 1 := by
  rcases orbit_pair_or_single a with ⟨h', -, -⟩ | ⟨-, ho, -⟩
  · exact absurd h h'
  obtain ⟨-, hc⟩ := hO
  rw [orbitImage_single ho, Finset.card_singleton] at hc
  rcases hc with hc | ⟨-, he⟩
  · exact absurd hc (by decide)
  rw [orbitSign]
  exact (he _ (Finset.mem_singleton_self _)).neg_one_zpow

theorem orbitFixed_eq_bot_of_not_mem
    (hK : ringChar K ≠ 2) {O : Finset E6Vec}
    (hO : O ∈ TwistTag.E6.diagramRootOrbits) (hΩ : O ∉ orbits) : orbitFixed K O = ⊥ := by
  obtain ⟨α, hα, rfl⟩ := hO
  obtain ⟨w, hw, a, he⟩ := TwistTag.E6.exists_diagramOrbit_eq hα
  have he' : TwistTag.E6.diagramOrbit α = orbitImage w a := he
  rcases orbit_pair_or_single a with ⟨h, ho, -⟩ | ⟨h, ho, -⟩
  · refine absurd ⟨⟨α, hα, rfl⟩, Or.inl ?_⟩ hΩ
    rw [he', orbitImage_pair ho, Finset.card_pair (smul_single_ne h w)]
  · rw [he']
    refine orbitFixed_orbitImage_eq_bot hK hw h fun hs => hΩ ⟨⟨α, hα, rfl⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [he', orbitImage_single ho, Finset.card_singleton]
    · rw [he', orbitImage_single ho]
      intro β hβ
      rw [Finset.mem_singleton.1 hβ]
      exact (orbitSign_eq_one_iff hK w a).1 hs

theorem coe_diagConj (s : Kˣ) (M : SL2 K) :
    ((diagConj K s M : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      !![(s : K), 0; 0, 1] * (M : Matrix (Fin 2) (Fin 2) K) *
        !![((s⁻¹ : Kˣ) : K), 0; 0, 1] := by
  rw [diagConj_apply]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [diagConjFun, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · field_simp
  · ring

theorem orbitSL2_single
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a}) (M : SL2 K) :
    orbitSL2 K w a M = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a) M *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  have hp : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a := by
    have := TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a)
    rwa [h, Finset.mem_singleton] at this
  rw [orbitSL2_apply, orbitBase_of_eq hp]

theorem orbitSL2_pair
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    {j : Fin TwistTag.E6.tag.rank} (h : TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a, j})
    (hj : j ≠ TwistTag.E6.orbitMin a) :
    j = TwistTag.E6.perm (TwistTag.E6.orbitMin a) ∧ ∀ M : SL2 K, orbitSL2 K w a M =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a) M *
          simpleRootSL2 TwistTag.E6.tag K j (diagConj K (orbitSign K w a) M)) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  have hjm : j ∈ TwistTag.E6.orbit a := by
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  rcases orbit_pair_or_single a with ⟨hp, ho, -⟩ | ⟨-, ho, -⟩
  · rw [ho, Finset.mem_insert, Finset.mem_singleton] at hjm
    obtain rfl := hjm.resolve_left hj
    exact ⟨rfl, fun M => by rw [orbitSL2_apply, orbitBase_of_ne hp]⟩
  · rw [ho, Finset.mem_singleton] at hjm
    exact absurd hjm hj

theorem range_orbitSL2
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    {a : Fin TwistTag.E6.foldedTag.rank}
    (hs : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a →
      orbitSign K w a = 1) :
    (orbitSL2 K w a).range =
      orbitFixed K (orbitImage w a) ⊔ orbitFixed K ((orbitImage w a).image fun α => -α) := by
  have hU := (orbitFixed_orbitImage_upper hw hs).2
  have hL := (orbitFixed_orbitImage_lower hw hs).2
  rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower (K := K), MonoidHom.map_closure,
    Set.image_union]
  change Subgroup.closure (orbitSL2 K w a '' Set.range uSL ∪ orbitSL2 K w a '' Set.range vSL) = _
  rw [← Set.range_comp, ← Set.range_comp]
  change Subgroup.closure (Set.range (fun c => orbitSL2 K w a (uSL c)) ∪
    Set.range (fun c => orbitSL2 K w a (vSL c))) = _
  rw [hU, hL, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]

theorem orbitSL2_nSL_pair
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) (t : Kˣ) :
    orbitSL2 K w a (nSL t) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      (weylElt TwistTag.E6.tag K (TwistTag.E6.orbitMin a) t *
        weylElt TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
          (orbitSign K w a * t)) * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_ne h, diagConj_nSL, simpleRootSL2_nSL, simpleRootSL2_nSL]

theorem orbitSL2_nSL_single
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a) (t : Kˣ) :
    orbitSL2 K w a (nSL t) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      weylElt TwistTag.E6.tag K (TwistTag.E6.orbitMin a) t *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_eq h, simpleRootSL2_nSL]

theorem orbitSL2_HSL_pair
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) (t : Kˣ) :
    orbitSL2 K w a (HSL t) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      (torusElt TwistTag.E6.tag K (TwistTag.E6.orbitMin a) t *
        torusElt TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) t) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_ne h, diagConj_HSL, simpleRootSL2_HSL, simpleRootSL2_HSL]

theorem orbitSL2_HSL_single
    (w : WeylGroup TwistTag.E6.tag) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a) (t : Kˣ) :
    orbitSL2 K w a (HSL t) = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
      torusElt TwistTag.E6.tag K (TwistTag.E6.orbitMin a) t *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
  rw [orbitSL2_apply, orbitBase_of_eq h, simpleRootSL2_HSL]

theorem weylElt_unit_mem_monomialSubgroup
    (k : Fin TwistTag.E6.tag.rank) (t : Kˣ) :
    weylElt TwistTag.E6.tag K k t ∈ monomialSubgroup TwistTag.E6.tag K := by
  rw [weylElt_eq_torusElt_mul_weylElt_one]
  exact mul_mem (torusElt_mem_monomialSubgroup k t) (weylElt_mem_monomialSubgroup k)

theorem mapsRootLines_weylElt_unit
    (k : Fin TwistTag.E6.tag.rank) (t : Kˣ) :
    MapsRootLines (weylElt TwistTag.E6.tag K k t) (simple TwistTag.E6.tag k) := by
  rw [weylElt_eq_torusElt_mul_weylElt_one]
  simpa using (mapsRootLines_of_mem_torusGroup (torusElt_mem_torusGroup k t)).mul
    (mapsRootLines_weylElt (R := K) k)

theorem simple_mul_simple_perm
    (a : Fin TwistTag.E6.foldedTag.rank) :
    simple TwistTag.E6.tag (TwistTag.E6.orbitMin a) *
        simple TwistTag.E6.tag (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) =
      simple TwistTag.E6.tag (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) *
        simple TwistTag.E6.tag (TwistTag.E6.orbitMin a) := by
  refine ext_single fun k => ?_
  simp only [mul_smul, simple_smul]
  revert k
  fin_cases a <;> decide +kernel

theorem orbitRefl_orbitImage
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitRefl (orbitImage w a) = w * TwistTag.E6.orbitReflection a * w⁻¹ := by
  rcases orbit_pair_or_single a with ⟨h, ho, hword⟩ | ⟨-, ho, hword⟩
  · have hc : Commute (rootReflection (w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)))
        (rootReflection
          (w • (Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 : E6Vec))) := by
      rw [rootReflection_eq_conj rfl, rootReflection_eq_conj rfl]
      change _ * _ = _ * _
      calc w * simple TwistTag.E6.tag (TwistTag.E6.orbitMin a) * w⁻¹ *
            (w * simple TwistTag.E6.tag (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) * w⁻¹) =
          w * (simple TwistTag.E6.tag (TwistTag.E6.orbitMin a) *
            simple TwistTag.E6.tag (TwistTag.E6.perm (TwistTag.E6.orbitMin a))) * w⁻¹ := by group
        _ = w * (simple TwistTag.E6.tag (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) *
            simple TwistTag.E6.tag (TwistTag.E6.orbitMin a)) * w⁻¹ := by
          rw [simple_mul_simple_perm]
        _ = _ := by group
    rw [orbitImage_pair ho, orbitRefl_pair (smul_single_ne h w) hc, rootReflection_eq_conj rfl,
      rootReflection_eq_conj rfl, TwistTag.orbitReflection, hword, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton]
    group
  · rw [orbitImage_single ho, orbitRefl_singleton, rootReflection_eq_conj rfl,
      TwistTag.orbitReflection, hword, CoxeterSystem.wordProd_singleton]

theorem orbitSL2_nSL_mem_monomialSubgroup
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (t : Kˣ) :
    orbitSL2 K w a (nSL t) ∈ monomialSubgroup TwistTag.E6.tag K := by
  have hn := canonicalRep_mem_monomialSubgroup K w
  by_cases h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a
  · rw [orbitSL2_nSL_single w h]
    exact mul_mem (mul_mem hn (weylElt_unit_mem_monomialSubgroup _ _)) (inv_mem hn)
  · rw [orbitSL2_nSL_pair w h]
    exact mul_mem (mul_mem hn (mul_mem (weylElt_unit_mem_monomialSubgroup _ _)
      (weylElt_unit_mem_monomialSubgroup _ _))) (inv_mem hn)

theorem mapsRootLines_orbitSL2_nSL
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (t : Kˣ) :
    MapsRootLines (orbitSL2 K w a (nSL t)) (orbitRefl (orbitImage w a)) := by
  rw [orbitRefl_orbitImage]
  have hn := mapsRootLines_canonicalRep (R := K) (τ := TwistTag.E6.tag) w
  rcases orbit_pair_or_single a with ⟨h, -, hword⟩ | ⟨h, -, hword⟩
  · rw [orbitSL2_nSL_pair w h, TwistTag.orbitReflection, hword, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton]
    exact (hn.mul ((mapsRootLines_weylElt_unit _ _).mul (mapsRootLines_weylElt_unit _ _))).mul
      hn.inv
  · rw [orbitSL2_nSL_single w h, TwistTag.orbitReflection, hword,
      CoxeterSystem.wordProd_singleton]
    exact (hn.mul (mapsRootLines_weylElt_unit _ _)).mul hn.inv

theorem weylQuotientHom_orbitSL2_nSL
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (t : Kˣ) :
    weylQuotientHom TwistTag.E6.tag K ⟨_, orbitSL2_nSL_mem_monomialSubgroup w a t⟩ =
      orbitRefl (orbitImage w a) :=
  weylQuotientHom_eq (mapsRootLines_orbitSL2_nSL w a t)

theorem orbitSL2_HSL_mem_torusGroup
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) (t : Kˣ) :
    orbitSL2 K w a (HSL t) ∈ torusGroup TwistTag.E6.tag K := by
  have key : ∀ g ∈ torusGroup TwistTag.E6.tag K,
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w * g *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ ∈ torusGroup TwistTag.E6.tag K :=
    fun g hg => (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) g).1 hg
  by_cases h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) = TwistTag.E6.orbitMin a
  · rw [orbitSL2_HSL_single w h]
    exact key _ (torusElt_mem_torusGroup _ _)
  · rw [orbitSL2_HSL_pair w h]
    exact key _ (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))

theorem map_orbitFixed_conj
    {z : ModGL TwistTag.E6.tag K}
    (hz : z ∈ monomialSubgroup TwistTag.E6.tag K) {r : WeylGroup TwistTag.E6.tag}
    (hzr : MapsRootLines z r) (hzΓ : z ∈ fixedGroup K) {S : Finset E6Vec}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α) :
    (orbitFixed K S).map (MulAut.conj z).toMonoidHom = orbitFixed K (S.image fun α => r • α) := by
  have hS' : ∀ α ∈ ((S.image fun α => r • α : Finset E6Vec) : Set E6Vec),
      IsRoot TwistTag.E6.tag α := by
    intro α hα
    rw [Finset.coe_image] at hα
    obtain ⟨β, hβ, rfl⟩ := hα
    exact IsRoot.smul (hS β hβ) r
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxU, hxΓ⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hzΓ hxΓ) (inv_mem hzΓ)⟩
    have := conj_mem_rootSpan_of_mapsRootLines hz hzr (S := (S : Set E6Vec)) hS hxU
    rw [Finset.coe_image]
    exact this
  · obtain ⟨hyU, hyΓ⟩ := Subgroup.mem_inf.1 hy
    have h1 := conj_mem_rootSpan_of_mapsRootLines (inv_mem hz) hzr.inv hS' hyU
    rw [Finset.coe_image, Set.image_image] at h1
    simp only [inv_smul_smul, Set.image_id'] at h1
    refine ⟨z⁻¹ * y * z⁻¹⁻¹, Subgroup.mem_inf.2 ⟨h1, mul_mem (mul_mem (inv_mem hzΓ) hyΓ)
      (inv_mem (inv_mem hzΓ))⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem sum_cartan_smul_inv
    (w : WeylGroup TwistTag.E6.tag) (k : Fin TwistTag.E6.tag.rank)
    (γ : E6Vec) :
    ∑ m, TwistTag.E6.tag.cartan k m * (w⁻¹ • γ) m = iform (w • (Pi.single k 1 : E6Vec)) γ := by
  conv_rhs => rw [← smul_inv_smul w γ]
  rw [iform_smul, iform_single_left, show TwistTag.E6.tag.symmetrizer = 1 from rfl,
    Matrix.one_apply_eq, one_mul]

theorem torus_conj_canonicalRep_xUnit
    (w w' : WeylGroup TwistTag.E6.tag)
    (k l : Fin TwistTag.E6.tag.rank) (t : Kˣ) (c : K) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K w * torusElt TwistTag.E6.tag K k t *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w' * xUnit TwistTag.E6.tag K l c *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w * torusElt TwistTag.E6.tag K k t *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w' *
          xUnit TwistTag.E6.tag K l
            (((t ^ iform (w • (Pi.single k 1 : E6Vec)) (w' • (Pi.single l 1 : E6Vec)) : Kˣ) : K) *
              c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')⁻¹ := by
  obtain ⟨ε, -, h⟩ := canonicalRep_conj_xUnit (K := K) w' l
  rw [h, h, canonicalRep_conj_torusElt_conj_pinnedX w k t (IsRoot.smul (isRoot_single _ l) w'),
    sum_cartan_smul_inv]
  congr 1
  ring

theorem orbitTorus_conj
    (w w' : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank)
    (t : Kˣ) (l : Fin TwistTag.E6.tag.rank) (c : K) :
    orbitSL2 K w a (HSL t) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w' * xUnit TwistTag.E6.tag K l c *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')⁻¹) *
        (orbitSL2 K w a (HSL t))⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w' *
          xUnit TwistTag.E6.tag K l
            (((t ^ iform (∑ α ∈ orbitImage w a, α) (w' • (Pi.single l 1 : E6Vec)) : Kˣ) : K) *
              c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')⁻¹ := by
  rcases orbit_pair_or_single a with ⟨h, ho, -⟩ | ⟨h, ho, -⟩
  · rw [orbitSL2_HSL_pair w h, orbitImage_pair ho, Finset.sum_pair (smul_single_ne h w),
      iform_add_left, _root_.zpow_add, Units.val_mul]
    set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w
    have e : ∀ x y g : ModGL TwistTag.E6.tag K, n * (x * y) * n⁻¹ * g * (n * (x * y) * n⁻¹)⁻¹ =
        n * x * n⁻¹ * (n * y * n⁻¹ * g * (n * y * n⁻¹)⁻¹) * (n * x * n⁻¹)⁻¹ :=
      fun x y g => by group
    rw [e, torus_conj_canonicalRep_xUnit, torus_conj_canonicalRep_xUnit, mul_assoc
      ((t ^ iform (w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)) _ : Kˣ) : K)]
  · rw [orbitSL2_HSL_single w h, orbitImage_single ho, Finset.sum_singleton,
      torus_conj_canonicalRep_xUnit]

theorem smul_single_perm_eq_rho
    {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (k : Fin TwistTag.E6.tag.rank) :
    w • (Pi.single (TwistTag.E6.perm k) 1 : E6Vec) = rho (w • (Pi.single k 1 : E6Vec)) := by
  rw [← permLattice_single, (mem_relWeylTwist_iff_smul TwistTag.E6).1 hw]
  rfl

theorem rho_orbitSum
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    rho (∑ α ∈ orbitImage w a, α) = ∑ α ∈ orbitImage w a, α := by
  have hadd : ∀ x y : E6Vec, rho (x + y) = rho x + rho y := fun x y => rfl
  rcases orbit_pair_or_single a with ⟨h, ho, -⟩ | ⟨h, ho, -⟩
  · rw [orbitImage_pair ho, Finset.sum_pair (smul_single_ne h w), hadd,
      ← smul_single_perm_eq_rho hw, ← smul_single_perm_eq_rho hw, perm_perm, add_comm]
  · rw [orbitImage_single ho, Finset.sum_singleton, ← smul_single_perm_eq_rho hw, h]

theorem iform_orbitSum_perm
    {w w' : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (hw' : w' ∈ relWeylTwist TwistTag.E6)
    (a : Fin TwistTag.E6.foldedTag.rank) (k : Fin TwistTag.E6.tag.rank) :
    iform (∑ α ∈ orbitImage w a, α) (w' • (Pi.single (TwistTag.E6.perm k) 1 : E6Vec)) =
      iform (∑ α ∈ orbitImage w a, α) (w' • (Pi.single k 1 : E6Vec)) := by
  have e := iform_permLattice_E6 (∑ α ∈ orbitImage w a, α) (w' • (Pi.single k 1 : E6Vec))
  change iform (rho _) (rho _) = _ at e
  rwa [rho_orbitSum hw, ← smul_single_perm_eq_rho hw'] at e

theorem iform_single_single_E6 (k : Fin TwistTag.E6.tag.rank) :
    iform (Pi.single k 1 : E6Vec) (Pi.single k 1) = 2 := by
  revert k
  decide +kernel

theorem iform_pair_self (a : Fin TwistTag.E6.foldedTag.rank)
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a) :
    iform ((Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec) +
        Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1)
      ((Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec) +
        Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) = 4 := by
  revert h
  revert a
  decide +kernel

theorem orbitVec_orbitImage_pair
    {w : WeylGroup TwistTag.E6.tag}
    {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a)
    (ho : TwistTag.E6.orbit a =
      {TwistTag.E6.orbitMin a, TwistTag.E6.perm (TwistTag.E6.orbitMin a)}) :
    orbitVec (orbitImage w a) = ∑ α ∈ orbitImage w a, α := by
  rw [orbitVec, orbitImage_pair ho, Finset.card_pair (smul_single_ne h w)]
  exact one_smul ℕ _

theorem orbitVec_orbitImage_single
    {w : WeylGroup TwistTag.E6.tag}
    {a : Fin TwistTag.E6.foldedTag.rank} (ho : TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a}) :
    orbitVec (orbitImage w a) = 2 • ∑ α ∈ orbitImage w a, α := by
  rw [orbitVec, orbitImage_single ho, Finset.card_singleton]

theorem iform_orbitSum_orbitVec
    {w w' : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (hw' : w' ∈ relWeylTwist TwistTag.E6)
    (a a' : Fin TwistTag.E6.foldedTag.rank) :
    iform (∑ α ∈ orbitImage w a, α) (orbitVec (orbitImage w' a')) =
      2 * iform (∑ α ∈ orbitImage w a, α)
        (w' • (Pi.single (TwistTag.E6.orbitMin a') 1 : E6Vec)) := by
  rcases orbit_pair_or_single a' with ⟨h, ho, -⟩ | ⟨-, ho, -⟩
  · rw [orbitVec_orbitImage_pair h ho, orbitImage_pair ho, Finset.sum_pair (smul_single_ne h w'),
      iform_add_right, iform_orbitSum_perm hw hw']
    ring
  · rw [orbitVec_orbitImage_single ho, orbitImage_single ho, Finset.sum_singleton, two_nsmul,
      iform_add_right]
    ring

theorem iform_orbitSum_self_pair
    {w : WeylGroup TwistTag.E6.tag}
    {a : Fin TwistTag.E6.foldedTag.rank}
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a)
    (ho : TwistTag.E6.orbit a =
      {TwistTag.E6.orbitMin a, TwistTag.E6.perm (TwistTag.E6.orbitMin a)}) :
    iform (∑ α ∈ orbitImage w a, α) (∑ α ∈ orbitImage w a, α) = 4 := by
  rw [orbitImage_pair ho, Finset.sum_pair (smul_single_ne h w), ← smul_add, iform_smul,
    iform_pair_self a h]

theorem iform_orbitSum_self_single
    {w : WeylGroup TwistTag.E6.tag}
    {a : Fin TwistTag.E6.foldedTag.rank} (ho : TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a}) :
    iform (∑ α ∈ orbitImage w a, α) (∑ α ∈ orbitImage w a, α) = 2 := by
  rw [orbitImage_single ho, Finset.sum_singleton, iform_smul, iform_single_single_E6]

theorem iform_orbitVec_mul
    {w w' : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (hw' : w' ∈ relWeylTwist TwistTag.E6)
    (a a' : Fin TwistTag.E6.foldedTag.rank) :
    iform (orbitVec (orbitImage w a)) (orbitVec (orbitImage w a)) *
        iform (∑ α ∈ orbitImage w a, α) (w' • (Pi.single (TwistTag.E6.orbitMin a') 1 : E6Vec)) =
      2 * iform (orbitVec (orbitImage w a)) (orbitVec (orbitImage w' a')) := by
  rcases orbit_pair_or_single a with ⟨h, ho, -⟩ | ⟨-, ho, -⟩
  · rw [orbitVec_orbitImage_pair h ho, iform_orbitSum_self_pair h ho,
      iform_orbitSum_orbitVec hw hw']
    ring
  · rw [orbitVec_orbitImage_single ho, two_nsmul, iform_add_left, iform_add_left,
      iform_add_right, iform_orbitSum_self_single ho, iform_orbitSum_orbitVec hw hw']
    ring

theorem iform_orbitVec_self_ne_zero
    (w : WeylGroup TwistTag.E6.tag)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    iform (orbitVec (orbitImage w a)) (orbitVec (orbitImage w a)) ≠ 0 := by
  rcases orbit_pair_or_single a with ⟨h, ho, -⟩ | ⟨-, ho, -⟩
  · rw [orbitVec_orbitImage_pair h ho, iform_orbitSum_self_pair h ho]
    decide
  · rw [orbitVec_orbitImage_single ho, two_nsmul, iform_add_left, iform_add_right,
      iform_orbitSum_self_single ho]
    decide

theorem orbitTorus_conj_orbitSL2_uSL
    {w w' : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) (hw' : w' ∈ relWeylTwist TwistTag.E6)
    (a a' : Fin TwistTag.E6.foldedTag.rank) (t : Kˣ) (c : K) :
    orbitSL2 K w a (HSL t) * orbitSL2 K w' a' (uSL c) * (orbitSL2 K w a (HSL t))⁻¹ =
      orbitSL2 K w' a' (uSL (((t ^ iform (∑ α ∈ orbitImage w a, α)
        (w' • (Pi.single (TwistTag.E6.orbitMin a') 1 : E6Vec)) : Kˣ) : K) * c)) := by
  rcases orbit_pair_or_single a' with ⟨h, -, -⟩ | ⟨h, -, -⟩
  · rw [orbitSL2_uSL_pair w' h, orbitSL2_uSL_pair w' h, conj_conj_mul, orbitTorus_conj,
      orbitTorus_conj, iform_orbitSum_perm hw hw', ← conj_mul, mul_left_comm]
  · rw [orbitSL2_uSL_single w' h, orbitSL2_uSL_single w' h, orbitTorus_conj]

end CFSG.LieType.Chevalley.E6SignedGraph

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  E6SignedGraph

theorem E6_signed_graph_orbit_rank_one_groups
    (K : Type) [Field K] (hK : ringChar K ≠ 2) :
    (rootDiagUnit TwistTag.E6.tag (signTuple K) =
        torusElt TwistTag.E6.tag K ⟨0, by decide⟩ (-1) *
          torusElt TwistTag.E6.tag K ⟨3, by decide⟩ (-1) *
            torusElt TwistTag.E6.tag K ⟨5, by decide⟩ (-1) ∧
      rootDiagUnit TwistTag.E6.tag (signTuple K) ∈ torusGroup TwistTag.E6.tag K) ∧
    (∀ O ∈ TwistTag.E6.diagramRootOrbits, O ∉ orbits → orbitFixed K O = ⊥) ∧
    (∀ O ∈ orbits, ∃ φ : SL2 K →* ModGL TwistTag.E6.tag K, (∀ M, φ M ∈ fixedGroup K) ∧
      φ.ker ≤ Subgroup.center (SL2 K) ∧
      φ.range = orbitFixed K O ⊔ orbitFixed K (O.image fun α => -α) ∧
      Function.Injective (fun c => φ (uSL c)) ∧ Set.range (fun c => φ (uSL c)) = orbitFixed K O ∧
      Function.Injective (fun c => φ (vSL c)) ∧
      Set.range (fun c => φ (vSL c)) = orbitFixed K (O.image fun α => -α)) ∧
    (∀ O ∈ orbits, ∃ w ∈ relWeylTwist TwistTag.E6, ∃ a, orbitImage w a = O) ∧
    (∀ (s : Kˣ) (M : SL2 K), ((diagConj K s M : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      !![(s : K), 0; 0, 1] * (M : Matrix (Fin 2) (Fin 2) K) *
        !![((s⁻¹ : Kˣ) : K), 0; 0, 1]) ∧
    ∀ w ∈ relWeylTwist TwistTag.E6, ∀ a, orbitImage w a ∈ orbits →
      orbitSign K w a =
        (-1) ^ ((w • (Pi.single (TwistTag.E6.orbitMin a) 1 : E6Vec)) ⟨1, by decide⟩) ∧
      (TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a} → orbitSign K w a = 1 ∧
        ∀ M, orbitSL2 K w a M = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a) M *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) ∧
      (∀ j, TwistTag.E6.orbit a = {TwistTag.E6.orbitMin a, j} → j ≠ TwistTag.E6.orbitMin a →
        j = TwistTag.E6.perm (TwistTag.E6.orbitMin a) ∧ ∀ M, orbitSL2 K w a M =
          canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
            (simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a) M *
              simpleRootSL2 TwistTag.E6.tag K j (diagConj K (orbitSign K w a) M)) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹) ∧
      (∀ M, orbitSL2 K w a M ∈ fixedGroup K) ∧
      (orbitSL2 K w a).ker ≤ Subgroup.center (SL2 K) ∧
      (orbitSL2 K w a).range =
        orbitFixed K (orbitImage w a) ⊔ orbitFixed K ((orbitImage w a).image fun α => -α) ∧
      Function.Injective (fun c => orbitSL2 K w a (uSL c)) ∧
      Set.range (fun c => orbitSL2 K w a (uSL c)) = orbitFixed K (orbitImage w a) ∧
      Function.Injective (fun c => orbitSL2 K w a (vSL c)) ∧
      Set.range (fun c => orbitSL2 K w a (vSL c)) =
        orbitFixed K ((orbitImage w a).image fun α => -α) ∧
      (∀ t : Kˣ, ∃ hz : orbitSL2 K w a (nSL t) ∈ monomialSubgroup TwistTag.E6.tag K,
        orbitSL2 K w a (nSL t) ∈ fixedGroup K ∧
          weylQuotientHom TwistTag.E6.tag K ⟨_, hz⟩ = orbitRefl (orbitImage w a)) ∧
      (∀ t : Kˣ, orbitSL2 K w a (HSL t) ∈ torusGroup TwistTag.E6.tag K ∧
        orbitSL2 K w a (HSL t) ∈ fixedGroup K) ∧
      (∀ w' ∈ relWeylTwist TwistTag.E6, ∀ a', orbitImage w' a' ∈ orbits →
        iform (orbitVec (orbitImage w a)) (orbitVec (orbitImage w a)) ∣
          2 * iform (orbitVec (orbitImage w a)) (orbitVec (orbitImage w' a')) ∧
        ∀ (t : Kˣ) (c : K), orbitSL2 K w a (HSL t) * orbitSL2 K w' a' (uSL c) *
            (orbitSL2 K w a (HSL t))⁻¹ =
          orbitSL2 K w' a' (uSL (((t ^ (2 * iform (orbitVec (orbitImage w a))
            (orbitVec (orbitImage w' a')) / iform (orbitVec (orbitImage w a))
              (orbitVec (orbitImage w a))) : Kˣ) : K) * c))) ∧
      ∀ S : Finset E6Vec, (∀ α ∈ S, IsRoot TwistTag.E6.tag α) → ∀ t : Kˣ,
        (orbitFixed K S).map (MulAut.conj (orbitSL2 K w a (nSL t))).toMonoidHom =
          orbitFixed K (S.image fun α => orbitRefl (orbitImage w a) • α) := by
  have hprop : ∀ w ∈ relWeylTwist TwistTag.E6, ∀ a, orbitImage w a ∈ orbits →
      (∀ M, orbitSL2 K w a M ∈ fixedGroup K) ∧
      (orbitSL2 K w a).ker ≤ Subgroup.center (SL2 K) ∧
      (orbitSL2 K w a).range =
        orbitFixed K (orbitImage w a) ⊔ orbitFixed K ((orbitImage w a).image fun α => -α) ∧
      Function.Injective (fun c => orbitSL2 K w a (uSL c)) ∧
      Set.range (fun c => orbitSL2 K w a (uSL c)) = orbitFixed K (orbitImage w a) ∧
      Function.Injective (fun c => orbitSL2 K w a (vSL c)) ∧
      Set.range (fun c => orbitSL2 K w a (vSL c)) =
        orbitFixed K ((orbitImage w a).image fun α => -α) := fun w hw a hO => by
    have hs := orbitSign_eq_one_of_mem_orbits (K := K) hO
    exact ⟨orbitSL2_mem_fixedGroup hw hs, ker_orbitSL2_le_center hK w a, range_orbitSL2 hw hs,
      (orbitFixed_orbitImage_upper hw hs).1, (orbitFixed_orbitImage_upper hw hs).2,
      (orbitFixed_orbitImage_lower hw hs).1, (orbitFixed_orbitImage_lower hw hs).2⟩
  refine ⟨⟨rootDiagUnit_signTuple, rootDiagUnit_signTuple_mem_torusGroup⟩,
    fun O hO hΩ => orbitFixed_eq_bot_of_not_mem hK hO hΩ, fun O hO => ?_,
    fun O hO => exists_orbitImage_eq hO, coe_diagConj, fun w hw a hO => ?_⟩
  · obtain ⟨w, hw, a, rfl⟩ := exists_orbitImage_eq hO
    exact ⟨orbitSL2 K w a, hprop w hw a hO⟩
  have hs := orbitSign_eq_one_of_mem_orbits (K := K) hO
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hprop w hw a hO
  refine ⟨rfl, fun ho => ⟨?_, orbitSL2_single ho⟩, fun j ho hj => orbitSL2_pair ho hj, h1, h2,
    h3, h4, h5, h6, h7, fun t => ⟨orbitSL2_nSL_mem_monomialSubgroup w a t, h1 _,
      weylQuotientHom_orbitSL2_nSL w a t⟩,
    fun t => ⟨orbitSL2_HSL_mem_torusGroup w a t, h1 _⟩, fun w' hw' a' _ => ?_,
    fun S hS t => map_orbitFixed_conj (orbitSL2_nSL_mem_monomialSubgroup w a t)
      (mapsRootLines_orbitSL2_nSL w a t) (h1 _) hS⟩
  · refine hs ?_
    have := TwistTag.E6.perm_mem_orbit (TwistTag.E6.orbitMin_mem a)
    rwa [ho, Finset.mem_singleton] at this
  · have hmul := iform_orbitVec_mul hw hw' a a'
    have hm : 2 * iform (orbitVec (orbitImage w a)) (orbitVec (orbitImage w' a')) /
        iform (orbitVec (orbitImage w a)) (orbitVec (orbitImage w a)) =
          iform (∑ α ∈ orbitImage w a, α)
            (w' • (Pi.single (TwistTag.E6.orbitMin a') 1 : E6Vec)) := by
      rw [← hmul, Int.mul_ediv_cancel_left _ (iform_orbitVec_self_ne_zero w a)]
    refine ⟨⟨_, hmul.symm⟩, fun t c => ?_⟩
    rw [hm]
    exact orbitTorus_conj_orbitSL2_uSL hw hw' a a' t c

end CFSG.LieType.Chevalley
