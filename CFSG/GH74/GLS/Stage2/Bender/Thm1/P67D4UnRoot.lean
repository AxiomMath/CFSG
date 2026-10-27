module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Phi
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnTau

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.coe_a2Phi_unTau (h : A2Core σ d q) (ε : K ≃+* K) (x : twistedGroup σ.toRingHom) :
    (((a2Phi h (unTau σ ε) x : twistedGroup σ.toRingHom) : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) =
      trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) *
        (trialityOpposition K)⁻¹ := by
  show ((((a2Equiv h).symm (unTau σ ε (a2Equiv h x)) : twistedGroup σ.toRingHom) :
    adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = _
  rw [coe_a2Equiv_symm, coe_unTau, coe_a2Equiv]

@[expose] def unAmb (ε : K ≃+* K) : ModGL TwistTag.D4.tag K →* ModGL TwistTag.D4.tag K :=
  (MulAut.conj (trialityOpposition K)).toMonoidHom.comp (Units.map (entrywiseHom ε.toRingHom))

omit
  [Finite K] in
theorem unAmb_apply (ε : K ≃+* K) (g : ModGL TwistTag.D4.tag K) :
    unAmb ε g = trialityOpposition K * Units.map (entrywiseHom ε.toRingHom) g *
      (trialityOpposition K)⁻¹ := rfl

omit
  [Finite K] in
theorem unz_mem_adjointGroup : trialityOpposition K ∈ adjointGroup d4 K :=
  ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K (RingHom.id K)).1
    (graphFixedRootGroup_le TwistTag.D4 K (RingHom.id K)
      (trialityOpposition_mem_graphFixedRootGroup (RingHom.id K)))).1

omit
  [Finite K] in
theorem unAmb_mem_adjointGroup (ε : K ≃+* K) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ adjointGroup d4 K) : unAmb ε g ∈ adjointGroup d4 K := by
  have h1 : Units.map (entrywiseHom ε.toRingHom) g ∈ adjointGroup d4 K := by
    rw [← ((chevalley_root_character_and_field_conjugation TwistTag.D4.tag K).2.2.2.2.1 ε).1]
    exact ⟨g, hg, rfl⟩
  exact mul_mem (mul_mem unz_mem_adjointGroup h1) (inv_mem unz_mem_adjointGroup)

@[expose] def unAdj (ε : K ≃+* K) : adjointGroup d4 K →* adjointGroup d4 K where
  toFun g := ⟨unAmb ε g, unAmb_mem_adjointGroup ε g.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

omit
  [Finite K] in
theorem coe_unAdj (ε : K ≃+* K) (g : adjointGroup d4 K) :
    ((unAdj ε g : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = unAmb ε g := rfl

omit
  [Finite K] in
theorem unAdj_twistC (σ' : K →+* K) (ε : K ≃+* K) (hεσ : ∀ c, σ' (ε c) = ε (σ' c))
    (g : adjointGroup d4 K) :
    twistC TwistTag.D4 K σ' (unAdj ε g) = unAdj ε (twistC TwistTag.D4 K σ' g) := by
  have hz : twistHom TwistTag.D4 K σ' (trialityOpposition K) = trialityOpposition K :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ').1
      (graphFixedRootGroup_le TwistTag.D4 K σ'
        (trialityOpposition_mem_graphFixedRootGroup σ'))).2
  refine Subtype.ext ?_
  rw [coe_twistC, coe_unAdj, coe_unAdj, coe_twistC, unAmb_apply, unAmb_apply, map_mul, map_mul,
    map_inv, hz, twistHom_units_map_entrywiseHom (fun c => (hεσ c).symm)]

omit
  [Finite K] in
theorem unAdj_mem_rootGroup (ε : K ≃+* K) {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α)
    {g : adjointGroup d4 K} (hg : g ∈ rootGroup (rootOperatorFamily d4) K α) :
    unAdj ε g ∈ rootGroup (rootOperatorFamily d4) K (-α) := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hα g).1 hg
  obtain ⟨μ, hμ⟩ := conj_pinnedX_of_smul_eq_neg
    (trialityOpposition_mem_monomialSubgroup (K := K)) weylQuotientHom_trialityOpposition_smul hα
  refine (mem_rootGroup_iff (IsRoot.neg hα) _).2
    ⟨a2Sign K (-α) * ((μ : K) * ε (a2Sign K α * c)), Subtype.ext ?_⟩
  rw [coe_unAdj, unAmb_apply, coe_xPar_a2 (IsRoot.neg hα), coe_xPar_a2 hα,
    show Units.map (entrywiseHom ε.toRingHom) (pinnedX d4 K α (a2Sign K α * c)) =
      pinnedX d4 K α (ε (a2Sign K α * c)) from Units.ext (entrywise_pinnedX ε.toRingHom α _),
    hμ, ← mul_assoc, a2Sign_mul_self, one_mul]

theorem map_twistedRootSubgroup_neg {ι κ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Group G] {Φ : Set (ι → ℤ)} {o : ι → κ} {X : (ι → ℤ) → Subgroup G}
    {F T : G →* G} (hΦ : ∀ α ∈ Φ, -α ∈ Φ) (hX : ∀ α ∈ Φ, ∀ g ∈ X α, T g ∈ X (-α))
    (hFT : ∀ g, F (T g) = T (F g)) {β : κ → ℤ} {g : G}
    (hg : g ∈ twistedRootSubgroup Φ o X F β) : T g ∈ twistedRootSubgroup Φ o X F (-β) := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have hneg : ∀ α : ι → ℤ, orbitSum o (-α) = -orbitSum o α := fun α => by
    funext c
    simp [orbitSum, Finset.sum_neg_distrib]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hle : (⨆ α ∈ Φ, ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum o α = c • β), X α) ≤
        (⨆ α ∈ Φ, ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum o α = c • (-β)), X α).comap T := by
      refine iSup₂_le fun α hα => iSup_le fun hc x hx => ?_
      obtain ⟨c, hc0, hcα⟩ := hc
      refine Subgroup.mem_comap.2 ?_
      exact Subgroup.mem_iSup_of_mem (-α) (Subgroup.mem_iSup_of_mem (hΦ α hα)
        (Subgroup.mem_iSup_of_mem ⟨c, hc0, by rw [hneg, hcα, smul_neg]⟩ (hX α hα x hx)))
    exact Subgroup.mem_comap.1 (hle hg1)
  · change F (T g) = T g
    rw [hFT]
    exact congrArg T hg2

omit
  [Finite K] in
theorem unAdj_mem_twistedRootSubgroupD4 (ε : K ≃+* K) (hεσ : ∀ c, σ (ε c) = ε (σ c))
    {β : Fin (Tag.rank .G2) → ℤ} {g : adjointGroup d4 K}
    (hg : g ∈ twistedRootSubgroupD4 σ.toRingHom β) :
    unAdj ε g ∈ twistedRootSubgroupD4 σ.toRingHom (-β) :=
  map_twistedRootSubgroup_neg (Φ := {α | IsRoot d4 α}) (o := orbitMap)
    (X := rootGroup (rootOperatorFamily d4) K) (F := twistC TwistTag.D4 K σ.toRingHom)
    (T := unAdj ε) (fun _ hα => IsRoot.neg hα) (fun _ hα _ hg => unAdj_mem_rootGroup ε hα hg)
    (fun g => unAdj_twistC σ.toRingHom ε hεσ g) hg

theorem hexPos_neg_of_isRoot {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k) :
    hexPos (-k) = -hexPos k := by
  obtain ⟨h0, h6⟩ := hk
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have e := hexPos_neg (i := -k) (by omega) (by omega)
    rw [neg_neg] at e
    rw [e, neg_neg]
  · exact hexPos_neg (by omega) (by omega)

theorem A2Core.unTau_mem_hexGroup (h : A2Core σ d q) (ε : K ≃+* K) (hεσ : ∀ c, σ (ε c) = ε (σ c))
    {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k) {x : twistedGroup σ.toRingHom}
    (hx : x ∈ hexGroup (twistedX σ.toRingHom) k) :
    a2Phi h (unTau σ ε) x ∈ hexGroup (twistedX σ.toRingHom) (-k) := by
  have hx' : ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      twistedRootSubgroupD4 σ.toRingHom (hexPos k) := hx
  have key : unAdj ε ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
      twistedRootSubgroupD4 σ.toRingHom (hexPos (-k)) := by
    rw [hexPos_neg_of_isRoot hk]
    exact unAdj_mem_twistedRootSubgroupD4 ε hεσ hx'
  have e : ((a2Phi h (unTau σ ε) x : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
      unAdj ε ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) :=
    Subtype.ext (coe_a2Phi_unTau h ε x)
  change ((a2Phi h (unTau σ ε) x : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
    twistedRootSubgroupD4 σ.toRingHom (hexPos (-k))
  rw [e]
  exact key

omit
  [Finite K] in
theorem unAmb_rootDiagUnit (ε : K ≃+* K) (b : Fin d4.rank → Kˣ) :
    unAmb ε (rootDiagUnit TwistTag.D4.tag b) =
      rootDiagUnit TwistTag.D4.tag (fun i => (Units.map ε.toRingHom.toMonoidHom (b i))⁻¹) := by
  rw [unAmb_apply, units_map_entrywiseHom_rootDiagUnit (t := TwistTag.D4), unz_conj_rootDiagUnit]
  rfl

omit
  [Finite K] in
theorem unAmb_torusElt (ε : K ≃+* K) (i : Fin d4.rank) (t : Kˣ) :
    unAmb ε (torusElt d4 K i t) = torusElt d4 K i (Units.map ε.toRingHom.toMonoidHom t)⁻¹ := by
  rw [torusElt_eq_rootDiagUnit, unAmb_rootDiagUnit, torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  simp [map_zpow]

omit
  [Finite K] in
theorem unAmb_torus_stable (ε : K ≃+* K) (hεσ : ∀ c, σ (ε c) = ε (σ c))
    (i : Fin (Tag.rank .G2)) {g : adjointGroup d4 K} (hg : g ∈ hHatE σ.toRingHom i) :
    ∃ g' ∈ hHatE σ.toRingHom i,
      (g' : ModGL TwistTag.D4.tag K) = unAmb ε (g : ModGL TwistTag.D4.tag K) := by
  have hu : ∀ t : Kˣ, Units.map σ.toRingHom.toMonoidHom (Units.map ε.toRingHom.toMonoidHom t) =
      Units.map ε.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t) :=
    fun t => Units.ext (hεσ t)
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨t, ht, rfl⟩ := a2tor_exists_of_mem_hHatE_zero hg
    refine ⟨torusElement d4 K (nd 2) (Units.map ε.toRingHom.toMonoidHom t)⁻¹,
      a2tor_mem_hHatE_zero ?_, ?_⟩
    · have ht' : Units.map σ.toRingHom.toMonoidHom t = t := Units.ext ht
      have := congrArg (fun u : Kˣ => (u : K))
        (show Units.map σ.toRingHom.toMonoidHom (Units.map ε.toRingHom.toMonoidHom t)⁻¹ =
          (Units.map ε.toRingHom.toMonoidHom t)⁻¹ by rw [map_inv, hu, ht'])
      exact this
    · change torusElt d4 K (nd 2) _ = unAmb ε (torusElt d4 K (nd 2) t)
      rw [unAmb_torusElt]
  | ⟨1, _⟩ =>
    obtain ⟨t, rfl⟩ := a2tor_exists_of_mem_hHatE_one hg
    refine ⟨hShortHom σ.toRingHom (Units.map ε.toRingHom.toMonoidHom t)⁻¹,
      a2tor_mem_hHatE_one _, ?_⟩
    rw [hShortHom_apply, hShortHom_apply]
    simp only [Subgroup.coe_mul, a2tor_coe_torusElement, map_mul, unAmb_torusElt, map_inv, hu]

theorem A2Core.unTau_mem_torus (h : A2Core σ d q) (ε : K ≃+* K) (hεσ : ∀ c, σ (ε c) = ε (σ c))
    {x : twistedGroup σ.toRingHom} (hx : x ∈ ⨆ i, hHat σ.toRingHom i) :
    a2Phi h (unTau σ ε) x ∈ ⨆ i, hHat σ.toRingHom i := by
  refine Subgroup.iSup_induction (C := fun x => a2Phi h (unTau σ ε) x ∈ ⨆ i, hHat σ.toRingHom i)
    (fun i => hHat σ.toRingHom i) hx ?_ ?_ ?_
  · intro i y hy
    have hy' : ((y : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈ hHatE σ.toRingHom i := hy
    obtain ⟨g', hg', hg'eq⟩ := unAmb_torus_stable ε hεσ i hy'
    have e : (((a2Phi h (unTau σ ε) y : twistedGroup σ.toRingHom) : adjointGroup d4 K)) = g' :=
      Subtype.ext ((coe_a2Phi_unTau h ε y).trans hg'eq.symm)
    exact Subgroup.mem_iSup_of_mem i (by
      change ((a2Phi h (unTau σ ε) y : twistedGroup σ.toRingHom) : adjointGroup d4 K) ∈
        hHatE σ.toRingHom i
      rw [e]; exact hg')
  · rw [map_one]; exact one_mem _
  · intro x y hx hy
    rw [map_mul]
    exact mul_mem hx hy

omit
  [Finite K] in
theorem coe_nHatE_zero : ((nHatE K (ng 0) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
    weylElt d4 K (nd 2) 1 := rfl

omit
  [Finite K] in
theorem coe_nHatE_one : ((nHatE K (ng 1) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
    weylElt d4 K (nd 0) 1 * weylElt d4 K (nd 1) 1 * weylElt d4 K (nd 3) 1 := by
  rw [nHatE_one]
  rfl

omit
  [Finite K] in
theorem nHatE_mem_monomial (i : Fin (Tag.rank .G2)) :
    ((nHatE K i : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) ∈
      monomialSubgroup TwistTag.D4.tag K := by
  match i with
  | ⟨0, _⟩ =>
    rw [show (⟨0, by decide⟩ : Fin (Tag.rank .G2)) = ng 0 from rfl, coe_nHatE_zero]
    exact weylElt_mem_monomialSubgroup (nd 2)
  | ⟨1, _⟩ =>
    rw [show (⟨1, by decide⟩ : Fin (Tag.rank .G2)) = ng 1 from rfl, coe_nHatE_one]
    exact mul_mem (mul_mem (weylElt_mem_monomialSubgroup (nd 0))
      (weylElt_mem_monomialSubgroup (nd 1))) (weylElt_mem_monomialSubgroup (nd 3))

omit
  [Finite K] in
theorem entrywise_nHatE (ε : K ≃+* K) (i : Fin (Tag.rank .G2)) :
    Units.map (entrywiseHom ε.toRingHom)
        ((nHatE K i : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((nHatE K i : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  match i with
  | ⟨0, _⟩ =>
    rw [show (⟨0, by decide⟩ : Fin (Tag.rank .G2)) = ng 0 from rfl, coe_nHatE_zero]
    exact entrywise_weylElt_one ε (nd 2)
  | ⟨1, _⟩ =>
    rw [show (⟨1, by decide⟩ : Fin (Tag.rank .G2)) = ng 1 from rfl, coe_nHatE_one, map_mul,
      map_mul, entrywise_weylElt_one, entrywise_weylElt_one, entrywise_weylElt_one]

theorem unz_oppositionWeyl_comm (u : WeylGroup TwistTag.D4.tag) :
    trialityOppositionWeyl * u = u * trialityOppositionWeyl := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, trialityOppositionWeyl_smul, trialityOppositionWeyl_smul, smul_neg]

omit [Finite K]
  in
theorem unz_comm_mem_torus {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ monomialSubgroup TwistTag.D4.tag K) :
    x⁻¹ * trialityOpposition K * x * (trialityOpposition K)⁻¹ ∈ torusGroup TwistTag.D4.tag K := by
  obtain ⟨w, hxw⟩ := exists_mapsRootLines_of_mem hx
  have hz := trialityOpposition_mem_monomialSubgroup (K := K)
  refine mem_torusGroup_of_mapsRootLines_one
    (mul_mem (mul_mem (mul_mem (inv_mem hx) hz) hx) (inv_mem hz)) ?_
  have h := (((hxw.inv).mul (mapsRootLines_trialityOpposition (K := K))).mul hxw).mul
    (mapsRootLines_trialityOpposition (K := K)).inv
  have hc : w⁻¹ * trialityOppositionWeyl * w * trialityOppositionWeyl⁻¹ = 1 := by
    calc w⁻¹ * trialityOppositionWeyl * w * trialityOppositionWeyl⁻¹
        = w⁻¹ * (trialityOppositionWeyl * w) * trialityOppositionWeyl⁻¹ := by group
      _ = w⁻¹ * (w * trialityOppositionWeyl) * trialityOppositionWeyl⁻¹ := by
          rw [unz_oppositionWeyl_comm]
      _ = 1 := by group
  rwa [hc] at h

omit
  [Finite K] in
theorem mem_iSup_hHat_of_mem_hHatE (σ' : K →+* K) (hσ : ∀ c, σ' (σ' (σ' c)) = c)
    {x : twistedGroup σ'} (hx : (x : adjointGroup d4 K) ∈ ⨆ i, hHatE σ' i) :
    x ∈ ⨆ i, hHat σ' i := by
  have key : ∀ g : adjointGroup d4 K, g ∈ ⨆ i, hHatE σ' i →
      ∃ hg : g ∈ twistedGroup σ', (⟨g, hg⟩ : twistedGroup σ') ∈ ⨆ i, hHat σ' i := by
    intro g hg
    refine Subgroup.iSup_induction (C := fun g => ∃ hg : g ∈ twistedGroup σ',
      (⟨g, hg⟩ : twistedGroup σ') ∈ ⨆ i, hHat σ' i) (fun i => hHatE σ' i) hg ?_ ?_ ?_
    · intro i y hy
      exact ⟨hHatE_le_twistedGroup hσ i hy, Subgroup.mem_iSup_of_mem i
        (show (⟨y, hHatE_le_twistedGroup hσ i hy⟩ : twistedGroup σ') ∈ hHat σ' i from hy)⟩
    · exact ⟨one_mem _, one_mem _⟩
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      exact ⟨mul_mem hx hy, mul_mem hx' hy'⟩
  obtain ⟨hg, hmem⟩ := key _ hx
  exact hmem

theorem A2Core.unTau_nHat_mem (h : A2Core σ d q) (ε : K ≃+* K) (hεσ : ∀ c, σ (ε c) = ε (σ c))
    (i : Fin 2) :
    (nHat σ.toRingHom i)⁻¹ * a2Phi h (unTau σ ε) (nHat σ.toRingHom i) ∈
      ⨆ i, hHat σ.toRingHom i := by
  have _ := hεσ
  set z := trialityOpposition K with hz
  set n : ModGL TwistTag.D4.tag K := ((nHatE K i : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)
    with hn
  set e : twistedGroup σ.toRingHom :=
    (nHat σ.toRingHom i)⁻¹ * a2Phi h (unTau σ ε) (nHat σ.toRingHom i) with he
  have hεn : Units.map (entrywiseHom ε.toRingHom) n = n := entrywise_nHatE ε i
  have hσn : Units.map (entrywiseHom σ.toRingHom) n = n := entrywise_nHatE σ i
  have hEmat : ((e : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = n⁻¹ * z * n * z⁻¹ := by
    rw [he]
    change (((nHat σ.toRingHom i : twistedGroup σ.toRingHom) : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K)⁻¹ *
      (((a2Phi h (unTau σ ε) (nHat σ.toRingHom i) : twistedGroup σ.toRingHom) :
        adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = _
    rw [coe_a2Phi_unTau]
    change n⁻¹ * (z * Units.map (entrywiseHom ε.toRingHom) n * z⁻¹) = n⁻¹ * z * n * z⁻¹
    rw [hεn]
    group
  have hT : n⁻¹ * z * n * z⁻¹ ∈ torusGroup TwistTag.D4.tag K :=
    unz_comm_mem_torus (nHatE_mem_monomial i)
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hσfix : Units.map (entrywiseHom σ.toRingHom) (n⁻¹ * z * n * z⁻¹) = n⁻¹ * z * n * z⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσn,
      units_map_entrywiseHom_trialityOpposition]
  rw [hc, units_map_entrywiseHom_rootDiagUnit (t := TwistTag.D4)] at hσfix
  have hσc : ∀ j, Units.map σ.toRingHom.toMonoidHom (c j) = c j :=
    congrFun (rootDiagUnit_injective hσfix)
  have hF : twistHom TwistTag.D4 K σ.toRingHom (rootDiagUnit TwistTag.D4.tag c) =
      rootDiagUnit TwistTag.D4.tag c := by
    rw [← hc, ← hEmat]
    have := (mem_twistFixed TwistTag.D4 K σ.toRingHom).1
      (twistedGroup_le_twistFixed σ.toRingHom e.2)
    exact congrArg (fun g : adjointGroup d4 K => (g : ModGL TwistTag.D4.tag K)) this
  have hcomp := compat_of_twistHom_rootDiagUnit (t := TwistTag.D4) hF
  have c1 : c (nd 1) = c (nd 0) := (hcomp (nd 0)).trans (hσc (nd 0))
  have c3 : c (nd 3) = c (nd 0) := ((hcomp (nd 1)).trans (by rw [c1]; exact hσc (nd 0))).trans rfl
  have hcv : c = ![c (nd 0), c (nd 0), c (nd 2), c (nd 0)] := by
    funext j
    fin_cases j
    · rfl
    · exact c1
    · rfl
    · exact c3
  obtain ⟨g, hg, hgc⟩ := a2_torus_mem h (hσc (nd 0)) (hσc (nd 2))
  refine mem_iSup_hHat_of_mem_hHatE σ.toRingHom h.cube_apply (x := e) ?_
  have : ((e : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K) := by
    rw [hEmat, hc, hgc, ← hcv]
  rw [show (e : adjointGroup d4 K) = g from Subtype.ext this]
  exact hg

end CFSG.GH74.GLS.Stage2.Bender.Thm1
