module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots

public section

namespace CFSG.AGLEmbeddingD2.SquareSpinMinus

open CFSG.Assembly.LowTwoRank QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabPrime CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbedding.ToralCensus CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.SquareGeneric

section Restrict

variable {G : Type*} [Group G] {F : Type} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

@[expose] noncomputable def restrictHom (ρ : G →* (V ≃ₗ[F] V)) (M : Subgroup G)
    (U : Submodule F V) (hU : ∀ g ∈ M, ∀ u ∈ U, ρ g u ∈ U) :
    ↥M →* LinearMap.GeneralLinearGroup F U :=
  MonoidHom.toHomUnits
    { toFun := fun g => ((ρ g : V ≃ₗ[F] V) : V →ₗ[F] V).restrict (fun u hu => hU g g.2 u hu)
      map_one' := by
        ext u
        simp
      map_mul' := fun g h => by
        ext u
        simp }

theorem restrictHom_injective (ρ : G →* (V ≃ₗ[F] V)) (M : Subgroup G) (U : Submodule F V)
    (hU : ∀ g ∈ M, ∀ u ∈ U, ρ g u ∈ U)
    (hinj : ∀ g ∈ M, (∀ u ∈ U, ρ g u = u) → g = 1) :
    Function.Injective (restrictHom ρ M U hU) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ u ∈ U, ρ g u = u := by
    intro u hu
    have := congrArg (fun x : LinearMap.GeneralLinearGroup F U => ((x : U →ₗ[F] U) ⟨u, hu⟩ : V)) hg
    simpa [restrictHom] using this
  exact Subtype.ext (hinj g g.2 h1)

variable [Finite F] [Module.Finite F V]

theorem isCyclic_of_restrict {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f)
    (ρ : G →* (V ≃ₗ[F] V)) (M : Subgroup G) (U : Submodule F V)
    (hU : ∀ g ∈ M, ∀ u ∈ U, ρ g u ∈ U) (hinj : ∀ g ∈ M, (∀ u ∈ U, ρ g u = u) → g = 1)
    (hdim : Module.finrank F U ≤ 7) :
    ∀ P : Subgroup G, P ≤ M → IsPGroup 5 P → IsCyclic P := by
  intro P hPM hP
  have := Fintype.ofFinite F
  have hk : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hc := CyclicSylowGL.isCyclic_of_isPGroup_five_of_injective_GeneralLinearGroup_two_pow hf hk
    hdim (restrictHom ρ M U hU) (restrictHom_injective ρ M U hU hinj) (P.subgroupOf M)
    hP.comap_subtype
  exact (Subgroup.subgroupOfEquivOfLe hPM).isCyclic.mp hc

theorem eq_bot_of_restrict {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f)
    (ρ : G →* (V ≃ₗ[F] V)) (M : Subgroup G) (U : Submodule F V)
    (hU : ∀ g ∈ M, ∀ u ∈ U, ρ g u ∈ U) (hinj : ∀ g ∈ M, (∀ u ∈ U, ρ g u = u) → g = 1)
    (hdim : Module.finrank F U ≤ 3) :
    ∀ P : Subgroup G, P ≤ M → IsPGroup 5 P → P = ⊥ := by
  intro P hPM hP
  have := Fintype.ofFinite F
  have hk : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hc := CyclicSylowGL.eq_bot_of_isPGroup_five_of_injective_GeneralLinearGroup_two_pow hf hk
    hdim (restrictHom ρ M U hU) (restrictHom_injective ρ M U hU hinj) (P.subgroupOf M)
    hP.comap_subtype
  have h1 : (P.subgroupOf M).map M.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPM]
  rw [← h1, hc, Subgroup.map_bot]

end Restrict

section Support

variable {σ : Type*} {F : Type*} [Field F]

@[expose] def supp (F : Type*) [Field F] {σ : Type*} (T : Set σ) : Submodule F (σ → F) where
  carrier := {v | ∀ a, a ∉ T → v a = 0}
  add_mem' := fun {u v} hu hv a ha => by simp [hu a ha, hv a ha]
  zero_mem' := fun a _ => rfl
  smul_mem' := fun c v hv a ha => by simp [hv a ha]

theorem single_mem_supp [DecidableEq σ] {T : Set σ} {a : σ} (ha : a ∈ T) (c : F) :
    (Pi.single a c : σ → F) ∈ supp F T := by
  intro b hb
  have hba : b ≠ a := by rintro rfl; exact hb ha
  simp [hba]

theorem finrank_supp_le [Fintype σ] [DecidableEq σ] (T : Finset σ) :
    Module.finrank F (supp F (T : Set σ)) ≤ T.card := by
  have h : Function.Injective
      ((LinearMap.funLeft F F ((↑) : T → σ)).comp (supp F (T : Set σ)).subtype) := by
    intro v w hvw
    ext a
    by_cases ha : a ∈ T
    · exact congrFun hvw ⟨a, ha⟩
    · rw [v.2 a (by simpa using ha), w.2 a (by simpa using ha)]
  have := LinearMap.finrank_le_finrank_of_injective h
  simpa using this

variable {G : Type*} [Group G]

theorem act_inv_act (ρ : G →* ((σ → F) ≃ₗ[F] (σ → F))) (g : G) (v : σ → F) :
    ρ g (ρ g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem inv_act_act (ρ : G →* ((σ → F) ≃ₗ[F] (σ → F))) (g : G) (v : σ → F) :
    ρ g⁻¹ (ρ g v) = v := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

@[expose] def actsIn (ρ : G →* ((σ → F) ≃ₗ[F] (σ → F))) (T : Set σ) : Subgroup G where
  carrier := {g | (∀ v a, a ∉ T → ρ g v a = v a) ∧ (∀ v, (∀ b ∈ T, v b = 0) → ρ g v = v)}
  mul_mem' := fun {g h} hg hh => by
    refine ⟨fun v a ha => ?_, fun v hv => ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply, hg.1 _ a ha, hh.1 v a ha]
    · rw [map_mul, LinearEquiv.mul_apply, hh.2 v hv, hg.2 v hv]
  one_mem' := ⟨fun v a _ => by simp, fun v _ => by simp⟩
  inv_mem' := fun {g} hg => by
    refine ⟨fun v a ha => ?_, fun v hv => ?_⟩
    · have := hg.1 (ρ g⁻¹ v) a ha
      rwa [act_inv_act, eq_comm] at this
    · have := hg.2 v hv
      calc ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [this]
        _ = v := inv_act_act ρ g v

theorem actsIn_mono (ρ : G →* ((σ → F) ≃ₗ[F] (σ → F))) {T T' : Set σ} (h : T ⊆ T') :
    actsIn ρ T ≤ actsIn ρ T' := fun _ hg =>
  ⟨fun v a ha => hg.1 v a fun h' => ha (h h'), fun v hv => hg.2 v fun b hb => hv b (h hb)⟩

@[expose] def stabSub (ρ : G →* ((σ → F) ≃ₗ[F] (σ → F))) (T : Set σ) : Subgroup G where
  carrier := {g | ∀ v ∈ supp F T, ρ g v ∈ supp F T ∧ ρ g⁻¹ v ∈ supp F T}
  mul_mem' := fun {g h} hg hh v hv => by
    refine ⟨?_, ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply]
      exact (hg _ (hh v hv).1).1
    · rw [mul_inv_rev, map_mul, LinearEquiv.mul_apply]
      exact (hh _ (hg v hv).2).2
  one_mem' := fun v hv => by simpa using hv
  inv_mem' := fun {g} hg v hv => by
    refine ⟨(hg v hv).2, ?_⟩
    rw [inv_inv]
    exact (hg v hv).1

theorem eq_one_of_fix_single [Fintype σ] [DecidableEq σ]
    {ρ : G →* ((σ → F) ≃ₗ[F] (σ → F))} (hρ : Function.Injective ρ) {g : G}
    (h : ∀ a, ρ g (Pi.single a 1) = Pi.single a 1) : g = 1 := by
  apply hρ
  rw [map_one]
  apply LinearEquiv.toLinearMap_injective
  exact (Pi.basisFun F σ).ext fun a => by simpa using h a

end Support

section Spin

variable {n : ℕ} {F : Type} [Field F] {b c : F}

abbrev Idx (n : ℕ) : Type := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2

theorem spinAction_longRoot_apply {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (x : F)
    (v : Vm n F) (a : Idx n) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longRoot hij s t (.ofAdd x)) v a =
      v a + x * v (minusPos n j (!t)) * (if a = minusPos n i s then 1 else 0) -
        x * v (minusPos n i (!s)) * (if a = minusPos n j t then 1 else 0) := by
  rw [HypFrame.spinAction_longRoot]
  simp only [minusFrame_vec]
  rw [polar_minusVec_eq_apply, polar_minusVec_eq_apply]
  simp only [minusVec_eq_single, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]

theorem spinAction_twShortRoot_apply (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (s : Bool) (p : Fin 2 → F) (v : Vm n F) (a : Idx n) :
    spinAction (quadMinus n F b c) (twShortRoot n hirr i s (.ofAdd p)) v a =
      v a + v (minusPos n i (!s)) * planeVec n p a -
        (polar (quadMinus n F b c) v (planeVec n p) + planeNorm b c p * v (minusPos n i (!s))) *
          (if a = minusPos n i s then 1 else 0) := by
  rw [spinAction_twShortRoot, polar_minusVec_eq_apply]
  simp only [minusVec_eq_single, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  ring

theorem polar_planeVec_eq_zero {v : Vm n F} (hv : ∀ t, v (.inr (.inr t)) = 0) (p : Fin 2 → F) :
    polar (quadMinus n F b c) v (planeVec n p) = 0 := by
  rw [polar_quadMinus]
  simp [planeVec, hv]

@[expose] def eCoords (n : ℕ) (S : Finset (Fin (n - 1))) : Finset (Idx n) := S.image Sum.inl

@[expose] def fCoords (n : ℕ) (S : Finset (Fin (n - 1))) : Finset (Idx n) :=
  S.image fun k => Sum.inr (Sum.inl k)

@[expose] def planeCoords (n : ℕ) : Finset (Idx n) := {Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)}

theorem inl_mem_eCoords {S : Finset (Fin (n - 1))} {k : Fin (n - 1)} :
    (Sum.inl k : Idx n) ∈ eCoords n S ↔ k ∈ S :=
  Sum.inl_injective.mem_finset_image

theorem inr_inl_mem_fCoords {S : Finset (Fin (n - 1))} {k : Fin (n - 1)} :
    (Sum.inr (Sum.inl k) : Idx n) ∈ fCoords n S ↔ k ∈ S :=
  (Sum.inr_injective.comp Sum.inl_injective).mem_finset_image

theorem inl_not_mem_fCoords (S : Finset (Fin (n - 1))) (k : Fin (n - 1)) :
    (Sum.inl k : Idx n) ∉ fCoords n S := by
  simp [fCoords]

theorem inr_inl_not_mem_eCoords (S : Finset (Fin (n - 1))) (k : Fin (n - 1)) :
    (Sum.inr (Sum.inl k) : Idx n) ∉ eCoords n S := by
  simp [eCoords]

theorem inr_inr_mem_planeCoords (t : Fin 2) : (Sum.inr (Sum.inr t) : Idx n) ∈ planeCoords n := by
  fin_cases t <;> simp [planeCoords]

theorem not_mem_planeCoords {a : Idx n} (ha : a ∉ planeCoords n) (p : Fin 2 → F) :
    planeVec n p a = 0 := by
  rcases a with k | k | t
  · rfl
  · rfl
  · exact absurd (inr_inr_mem_planeCoords t) ha

theorem minusPos_mem_frame {S : Finset (Fin (n - 1))} {k : Fin (n - 1)} (hk : k ∈ S) (s : Bool) :
    minusPos n k s ∈ eCoords n S ∪ fCoords n S := by
  cases s
  · exact Finset.mem_union_right _ (inr_inl_mem_fCoords.2 hk)
  · exact Finset.mem_union_left _ (inl_mem_eCoords.2 hk)

theorem longRoot_inv {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (x : F) :
    ((minusFrame n b c).longRoot hij s t (.ofAdd x))⁻¹ =
      (minusFrame n b c).longRoot hij s t (.ofAdd (-x)) := by
  rw [← map_inv, ← ofAdd_neg]

theorem longRoot_mem_actsIn (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hij : i ≠ j)
    (hi : i ∈ S) (hj : j ∈ S) (s t : Bool) (x : F) :
    (minusFrame n b c).longRoot hij s t (.ofAdd x) ∈
      actsIn (spinAction (quadMinus n F b c)) ((eCoords n S ∪ fCoords n S : Finset (Idx n)) :
        Set (Idx n)) := by
  refine ⟨fun v a ha => ?_, fun v hv => ?_⟩
  · rw [spinAction_longRoot_apply]
    have h1 : a ≠ minusPos n i s := fun h => ha (by
      rw [h]; exact Finset.mem_coe.2 (minusPos_mem_frame hi s))
    have h2 : a ≠ minusPos n j t := fun h => ha (by
      rw [h]; exact Finset.mem_coe.2 (minusPos_mem_frame hj t))
    rw [ite_eq_right h1, ite_eq_right h2]
    ring
  · funext a
    rw [spinAction_longRoot_apply, hv _ (Finset.mem_coe.2 (minusPos_mem_frame hj (!t))),
      hv _ (Finset.mem_coe.2 (minusPos_mem_frame hi (!s)))]
    ring

theorem spinAction_longRoot_apply_tf {i j : Fin (n - 1)} (hij : i ≠ j) (x : F) (v : Vm n F)
    (a : Idx n) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longRoot hij true false (.ofAdd x)) v a =
      v a + x * v (.inl j) * (if a = .inl i then 1 else 0) -
        x * v (.inr (.inl i)) * (if a = .inr (.inl j) then 1 else 0) :=
  spinAction_longRoot_apply hij true false x v a

theorem longRoot_stab_eCoords (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hij : i ≠ j)
    (hi : i ∈ S) (x : F) {v : Vm n F} (hv : v ∈ supp F (eCoords n S : Set (Idx n))) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longRoot hij true false (.ofAdd x)) v ∈
      supp F (eCoords n S : Set (Idx n)) := by
  intro a ha
  have ha' : a ∉ eCoords n S := ha
  have h1 : ¬ (a = .inl i) := fun h => ha' (h ▸ inl_mem_eCoords.2 hi)
  rw [spinAction_longRoot_apply_tf, hv a ha, hv (.inr (.inl i)) (inr_inl_not_mem_eCoords S i),
    ite_eq_right h1]
  ring

theorem longRoot_stab_fCoords (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hij : i ≠ j)
    (hj : j ∈ S) (x : F) {v : Vm n F} (hv : v ∈ supp F (fCoords n S : Set (Idx n))) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longRoot hij true false (.ofAdd x)) v ∈
      supp F (fCoords n S : Set (Idx n)) := by
  intro a ha
  have ha' : a ∉ fCoords n S := ha
  have h1 : ¬ (a = .inr (.inl j)) := fun h => ha' (h ▸ inr_inl_mem_fCoords.2 hj)
  rw [spinAction_longRoot_apply_tf, hv a ha, hv (.inl j) (inl_not_mem_fCoords S j),
    ite_eq_right h1]
  ring

theorem longRoot_mem_actsLevi (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hij : i ≠ j)
    (hi : i ∈ S) (hj : j ∈ S) (x : F) :
    (minusFrame n b c).longRoot hij true false (.ofAdd x) ∈
      actsIn (spinAction (quadMinus n F b c))
        ((eCoords n S ∪ fCoords n S : Finset (Idx n)) : Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (eCoords n S : Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (fCoords n S : Set (Idx n)) := by
  refine ⟨⟨longRoot_mem_actsIn S hij hi hj true false x, fun v hv => ⟨?_, ?_⟩⟩,
    fun v hv => ⟨?_, ?_⟩⟩
  · exact longRoot_stab_eCoords S hij hi x hv
  · rw [longRoot_inv]
    exact longRoot_stab_eCoords S hij hi (-x) hv
  · exact longRoot_stab_fCoords S hij hj x hv
  · rw [longRoot_inv]
    exact longRoot_stab_fCoords S hij hj (-x) hv

theorem twShortRoot_mem_actsIn (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (S : Finset (Fin (n - 1)))
    {i : Fin (n - 1)} (hi : i ∈ S) (s : Bool) (p : Fin 2 → F) :
    twShortRoot n hirr i s (.ofAdd p) ∈
      actsIn (spinAction (quadMinus n F b c))
        ((eCoords n S ∪ fCoords n S ∪ planeCoords n : Finset (Idx n)) : Set (Idx n)) := by
  refine ⟨fun v a ha => ?_, fun v hv => ?_⟩
  · have ha' : a ∉ eCoords n S ∪ fCoords n S ∪ planeCoords n := ha
    have h1 : a ≠ minusPos n i s := fun h => ha' (by
      rw [h]; exact Finset.mem_union_left _ (minusPos_mem_frame hi s))
    have h2 : a ∉ planeCoords n := fun h => ha' (Finset.mem_union_right _ h)
    rw [spinAction_twShortRoot_apply, not_mem_planeCoords h2, ite_eq_right h1]
    ring
  · have hv1 : v (minusPos n i (!s)) = 0 := hv _ (Finset.mem_coe.2 (Finset.mem_union_left _
      (minusPos_mem_frame hi (!s))))
    have hv2 : ∀ t, v (.inr (.inr t)) = 0 := fun t => hv _ (Finset.mem_coe.2
      (Finset.mem_union_right _ (inr_inr_mem_planeCoords t)))
    funext a
    rw [spinAction_twShortRoot_apply, hv1, polar_planeVec_eq_zero hv2]
    ring

section Levi

theorem leviM_le_actsIn (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (I : Set (Fin (n - 1)))
    (S : Finset (Fin (n - 1)))
    (hI : ∀ k ∈ I, k ∈ S ∧ ∀ hk : k.val + 1 < n - 1, (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ S) :
    leviM (minusDatum n hirr) I ≤
      actsIn (spinAction (quadMinus n F b c))
        ((eCoords n S ∪ fCoords n S ∪ planeCoords n : Finset (Idx n)) : Set (Idx n)) := by
  refine iSup₂_le fun (k : Fin (n - 1)) hk => ?_
  obtain ⟨hkS, hk'S⟩ := hI k hk
  have hsub : ((eCoords n S ∪ fCoords n S : Finset (Idx n)) : Set (Idx n)) ⊆
      ((eCoords n S ∪ fCoords n S ∪ planeCoords n : Finset (Idx n)) : Set (Idx n)) := by
    intro a ha
    exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha))
  by_cases hk1 : k.val + 1 < n - 1
  · refine sup_le ?_ ?_
    · change minusRootGroup n hirr (Pi.single k 1) ≤ _
      rw [minusRootGroup_single_of_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact actsIn_mono (spinAction (quadMinus n F b c)) hsub
        (longRoot_mem_actsIn S (succ_ne_of_lt n hk1) hkS (hk'S hk1) true false x.toAdd)
    · change minusRootGroup n hirr (-Pi.single k 1) ≤ _
      rw [minusRootGroup_neg_single_of_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact actsIn_mono (spinAction (quadMinus n F b c)) hsub
        (longRoot_mem_actsIn S (succ_ne_of_lt n hk1).symm (hk'S hk1) hkS true false x.toAdd)
  · refine sup_le ?_ ?_
    · change minusRootGroup n hirr (Pi.single k 1) ≤ _
      rw [minusRootGroup_single_of_not_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact twShortRoot_mem_actsIn hirr S hkS true x.toAdd
    · change minusRootGroup n hirr (-Pi.single k 1) ≤ _
      rw [minusRootGroup_neg_single_of_not_lt n hirr hk1]
      rintro _ ⟨x, rfl⟩
      exact twShortRoot_mem_actsIn hirr S hkS false x.toAdd

theorem leviM_le_actsLevi (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (I : Set (Fin (n - 1)))
    (S : Finset (Fin (n - 1)))
    (hI : ∀ k ∈ I, ∃ hk : k.val + 1 < n - 1, k ∈ S ∧ (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ S) :
    leviM (minusDatum n hirr) I ≤
      actsIn (spinAction (quadMinus n F b c))
        ((eCoords n S ∪ fCoords n S : Finset (Idx n)) : Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (eCoords n S : Set (Idx n)) ⊓
      stabSub (spinAction (quadMinus n F b c)) (fCoords n S : Set (Idx n)) := by
  refine iSup₂_le fun (k : Fin (n - 1)) hk => ?_
  obtain ⟨hk1, hkS, hk'S⟩ := hI k hk
  refine sup_le ?_ ?_
  · change minusRootGroup n hirr (Pi.single k 1) ≤ _
    rw [minusRootGroup_single_of_lt n hirr hk1]
    rintro _ ⟨x, rfl⟩
    exact longRoot_mem_actsLevi S (succ_ne_of_lt n hk1) hkS hk'S x.toAdd
  · change minusRootGroup n hirr (-Pi.single k 1) ≤ _
    rw [minusRootGroup_neg_single_of_lt n hirr hk1]
    rintro _ ⟨x, rfl⟩
    exact longRoot_mem_actsLevi S (succ_ne_of_lt n hk1).symm hk'S hkS x.toAdd

theorem spinAction_injective [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (spinAction (quadMinus n F b c)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← ker_spinMatrix]
  exact ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero

theorem eq_one_of_fix_eCoords [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (S : Finset (Fin (n - 1))) {g : spinGroup (quadMinus n F b c)}
    (hg1 : g ∈ actsIn (spinAction (quadMinus n F b c))
      ((eCoords n S ∪ fCoords n S : Finset (Idx n)) : Set (Idx n)))
    (hg2 : g ∈ stabSub (spinAction (quadMinus n F b c)) (fCoords n S : Set (Idx n)))
    (h : ∀ u ∈ supp F (eCoords n S : Set (Idx n)), spinAction (quadMinus n F b c) g u = u) :
    g = 1 := by
  refine eq_one_of_fix_single (spinAction_injective hirr) fun a => ?_
  by_cases ha : a ∈ eCoords n S
  · exact h _ (single_mem_supp (Finset.mem_coe.2 ha) 1)
  by_cases hb : a ∈ fCoords n S
  · obtain ⟨k, hkS, rfl⟩ := Finset.mem_image.1 hb
    have hk : (Pi.single (Sum.inr (Sum.inl k)) 1 : Vm n F) ∈ supp F (fCoords n S : Set (Idx n)) :=
      single_mem_supp (Finset.mem_coe.2 hb) 1
    have hmem := sub_mem ((hg2 _ hk).1) hk
    have hzero : spinAction (quadMinus n F b c) g (Pi.single (Sum.inr (Sum.inl k)) 1) -
        Pi.single (Sum.inr (Sum.inl k)) 1 = 0 := by
      funext x
      by_cases hx : x ∈ fCoords n S
      · obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.1 hx
        have hpol := polar_spinAction (quadMinus n F b c) g (Pi.single (Sum.inr (Sum.inl k)) 1)
          (Pi.single (Sum.inl j) 1)
        rw [h _ (single_mem_supp (Finset.mem_coe.2 (inl_mem_eCoords.2 hjS)) 1),
          polar_quadMinus_single_inl, polar_quadMinus_single_inl] at hpol
        simp only [Pi.sub_apply, Pi.zero_apply]
        rw [hpol, sub_self]
      · exact hmem x hx
    exact sub_eq_zero.1 hzero
  · refine hg1.2 _ fun x hx => ?_
    have hxa : x ≠ a := fun h' => by
      subst h'
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with h1 | h1
      · exact ha h1
      · exact hb h1
    exact Pi.single_eq_of_ne hxa 1

theorem isCyclic_leviM_long [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f) (I : Set (Fin (n - 1)))
    (S : Finset (Fin (n - 1)))
    (hI : ∀ k ∈ I, ∃ hk : k.val + 1 < n - 1, k ∈ S ∧ (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ S)
    (hS : S.card ≤ 7) :
    ∀ P : Subgroup (spinGroup (quadMinus n F b c)), P ≤ leviM (minusDatum n hirr) I →
      IsPGroup 5 P → IsCyclic P := by
  have hle := leviM_le_actsLevi hirr I S hI
  refine isCyclic_of_restrict hf hF (spinAction (quadMinus n F b c)) (leviM (minusDatum n hirr) I)
    (supp F (eCoords n S : Set (Idx n))) (fun g hg u hu => ((hle hg).1.2 u hu).1)
    (fun g hg h => eq_one_of_fix_eCoords hirr S (hle hg).1.1 (hle hg).2 h) ?_
  exact (finrank_supp_le _).trans (Finset.card_image_le.trans hS)

theorem eq_bot_leviM_long [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f) (I : Set (Fin (n - 1)))
    (S : Finset (Fin (n - 1)))
    (hI : ∀ k ∈ I, ∃ hk : k.val + 1 < n - 1, k ∈ S ∧ (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ S)
    (hS : S.card ≤ 3) :
    ∀ P : Subgroup (spinGroup (quadMinus n F b c)), P ≤ leviM (minusDatum n hirr) I →
      IsPGroup 5 P → P = ⊥ := by
  have hle := leviM_le_actsLevi hirr I S hI
  refine eq_bot_of_restrict hf hF (spinAction (quadMinus n F b c)) (leviM (minusDatum n hirr) I)
    (supp F (eCoords n S : Set (Idx n))) (fun g hg u hu => ((hle hg).1.2 u hu).1)
    (fun g hg h => eq_one_of_fix_eCoords hirr S (hle hg).1.1 (hle hg).2 h) ?_
  exact (finrank_supp_le _).trans (Finset.card_image_le.trans hS)

theorem isCyclic_leviM_two [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f) (I : Set (Fin (n - 1)))
    (S : Finset (Fin (n - 1)))
    (hI : ∀ k ∈ I, k ∈ S ∧ ∀ hk : k.val + 1 < n - 1, (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ S)
    (hS : S.card ≤ 2) :
    ∀ P : Subgroup (spinGroup (quadMinus n F b c)), P ≤ leviM (minusDatum n hirr) I →
      IsPGroup 5 P → IsCyclic P := by
  have hle := leviM_le_actsIn hirr I S hI
  refine isCyclic_of_restrict hf hF (spinAction (quadMinus n F b c)) (leviM (minusDatum n hirr) I)
    (supp F ((eCoords n S ∪ fCoords n S ∪ planeCoords n : Finset (Idx n)) : Set (Idx n)))
    (fun g hg u hu a ha => by rw [(hle hg).1 u a ha]; exact hu a ha)
    (fun g hg h => ?_) ?_
  · refine eq_one_of_fix_single (spinAction_injective hirr) fun a => ?_
    by_cases ha : a ∈ eCoords n S ∪ fCoords n S ∪ planeCoords n
    · exact h _ (single_mem_supp (Finset.mem_coe.2 ha) 1)
    · refine (hle hg).2 _ fun x hx => ?_
      have hxa : x ≠ a := fun h' => ha (h' ▸ Finset.mem_coe.1 hx)
      exact Pi.single_eq_of_ne hxa 1
  · refine (finrank_supp_le _).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (eCoords n S ∪ fCoords n S).card ≤ S.card + S.card :=
      (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
    have h2 : (planeCoords n : Finset (Idx n)).card ≤ 2 := by
      simp only [planeCoords]
      exact Finset.card_le_two
    omega

end Levi

end Spin

section Product

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commutes {A C : Subgroup G} (h : Commutes A C) {x : G}
    (hx : x ∈ A ⊔ C) : ∃ a ∈ A, ∃ c ∈ C, x = a * c := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩
    · exact ⟨1, one_mem _, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, (one_mul 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    obtain ⟨a', ha', c', hc', rfl⟩ := hy
    refine ⟨a * a', mul_mem ha ha', c * c', mul_mem hc hc', ?_⟩
    have := h a' ha' c hc
    calc a * c * (a' * c') = a * (c * a') * c' := by group
      _ = a * (a' * c) * c' := by rw [this]
      _ = a * a' * (c * c') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    refine ⟨a⁻¹, inv_mem ha, c⁻¹, inv_mem hc, ?_⟩
    have := h a ha c hc
    calc (a * c)⁻¹ = (c * a)⁻¹ := by rw [this]
      _ = a⁻¹ * c⁻¹ := by group

theorem isCyclic_sup_of_commutes [Finite G] {A C : Subgroup G} (h : Commutes A C)
    (hA : ∀ P : Subgroup G, P ≤ A → IsPGroup 5 P → P = ⊥)
    (hC : ∀ P : Subgroup G, P ≤ C → IsPGroup 5 P → IsCyclic P) :
    ∀ P : Subgroup G, P ≤ A ⊔ C → IsPGroup 5 P → IsCyclic P := by
  intro P hP hP5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : ∀ a ∈ A, ¬ 5 ∣ orderOf a := by
    intro a ha h5
    have hne : orderOf a ≠ 0 := (orderOf_pos a).ne'
    have hb : orderOf (a ^ (orderOf a / 5)) = 5 := orderOf_pow_orderOf_div hne h5
    have hbA : a ^ (orderOf a / 5) ∈ A := pow_mem ha _
    have h5g : IsPGroup 5 (Subgroup.zpowers (a ^ (orderOf a / 5))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
    have h1 := hA _ (Subgroup.zpowers_le.2 hbA) h5g
    rw [Subgroup.zpowers_eq_bot] at h1
    rw [h1, orderOf_one] at hb
    omega
  have hPC : P ≤ C := by
    intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commutes h (hP hx)
    have hcomm : Commute a c := h a ha c hc
    have h1 : (a * c) ^ orderOf a = c ^ orderOf a := by
      rw [hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
    obtain ⟨k, hk⟩ := hP5 ⟨a * c, hx⟩
    have hk' : (a * c) ^ 5 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1
      (orderOf_dvd_of_pow_eq_one hk')
    have h2 : Nat.Coprime (orderOf a) (orderOf (a * c)) := by
      rw [hj]
      exact Nat.Coprime.pow_right _
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 (hord a ha)).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h2
    rw [← hm, h1, ← pow_mul]
    exact pow_mem hc _
  exact hC P hPC hP5

theorem commutes_iSup_iSup {ι : Type*} {I J : Set ι} {L : ι → Subgroup G}
    (h : ∀ i ∈ I, ∀ j ∈ J, Commutes (L i) (L j)) :
    Commutes (⨆ i ∈ I, L i) (⨆ j ∈ J, L j) := by
  rw [commutes_iff_le_centralizer]
  refine iSup₂_le fun i hi => ?_
  rw [← commutes_iff_le_centralizer]
  refine Commutes.symm ?_
  rw [commutes_iff_le_centralizer]
  exact iSup₂_le fun j hj => commutes_iff_le_centralizer.1 (h i hi j hj).symm

end Product

section Coords

variable {n : ℕ}

@[expose] noncomputable def coordsF (n : ℕ) (I : Set (Fin (n - 1))) : Finset (Fin (n - 1)) := by
  classical
  exact Finset.univ.filter fun a => ∃ i ∈ I, i.val + 1 < n - 1 ∧ (a = i ∨ a.val = i.val + 1)

theorem mem_coordsF {I : Set (Fin (n - 1))} {a : Fin (n - 1)} :
    a ∈ coordsF n I ↔ ∃ i ∈ I, i.val + 1 < n - 1 ∧ (a = i ∨ a.val = i.val + 1) := by
  classical
  simp [coordsF]

theorem self_mem_coordsF {I : Set (Fin (n - 1))} {i : Fin (n - 1)} (hi : i ∈ I)
    (hk : i.val + 1 < n - 1) : i ∈ coordsF n I :=
  mem_coordsF.2 ⟨i, hi, hk, Or.inl rfl⟩

theorem succ_mem_coordsF {I : Set (Fin (n - 1))} {i : Fin (n - 1)} (hi : i ∈ I)
    (hk : i.val + 1 < n - 1) : (⟨i.val + 1, hk⟩ : Fin (n - 1)) ∈ coordsF n I :=
  mem_coordsF.2 ⟨i, hi, hk, Or.inr rfl⟩

theorem exists_min_val {m : ℕ} (I : Set (Fin m)) (hne : I.Nonempty) :
    ∃ a ∈ I, ∀ x ∈ I, a.val ≤ x.val := by
  classical
  obtain ⟨x, hx⟩ := hne
  have h : ∃ k, ∃ y ∈ I, y.val = k := ⟨x.val, x, hx, rfl⟩
  obtain ⟨y, hy, hyk⟩ := Nat.find_spec h
  exact ⟨y, hy, fun z hz => hyk ▸ Nat.find_min' h ⟨z, hz, rfl⟩⟩

theorem card_coordsF_le_six (I : Set (Fin (n - 1)))
    (hI : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val) :
    (coordsF n I).card ≤ 6 := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn Fin.castSucc ?_
    (Fin.castSucc_injective _).injOn) (SquareLinear.card_coords_le_six I hI)
  intro a ha
  obtain ⟨i, hi, hk, h⟩ := mem_coordsF.1 (Finset.mem_coe.1 ha)
  simp only [SquareLinear.coords, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  refine ⟨i, hi, ?_⟩
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Fin.ext (by simp [h]))

theorem card_coordsF_le_three (I : Set (Fin (n - 1)))
    (hI : ¬ ∃ a ∈ I, ∃ b ∈ I, a.val + 2 ≤ b.val) : (coordsF n I).card ≤ 3 := by
  by_cases hne : I.Nonempty
  · obtain ⟨a, ha, hamin⟩ := exists_min_val I hne
    have hall : ∀ x ∈ I, x.val ≤ a.val + 1 := by
      intro x hx
      by_contra h
      exact hI ⟨a, ha, x, hx, by omega⟩
    refine le_trans (Finset.card_le_card_of_injOn (fun y => y.val)
      (t := Finset.Icc a.val (a.val + 2)) ?_ ?_) (by rw [Nat.card_Icc]; omega)
    · intro y hy
      obtain ⟨i, hi, hk, h⟩ := mem_coordsF.1 (Finset.mem_coe.1 hy)
      have h1 := hamin i hi
      have h2 := hall i hi
      simp only [Finset.coe_Icc, Set.mem_Icc]
      rcases h with rfl | h <;> omega
    · intro y _ z _ h
      exact Fin.ext h
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    classical
    have : coordsF n (∅ : Set (Fin (n - 1))) = ∅ := by
      ext a
      simp [mem_coordsF]
    rw [this]
    simp

end Coords

section Residual

variable {n : ℕ} {F : Type} [Field F] {b c : F}

theorem cartan_minusDatum_eq_zero (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)}
    (hij : i.val + 2 ≤ j.val) : (minusDatum n hirr).cartan i j = 0 := by
  have h1 : i ≠ j := fun h => by rw [h] at hij; omega
  have h2 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by omega
  change cartanB (n - 1) i j = 0
  simp only [cartanB, Matrix.of_apply, h1, h2, ite_false]

@[expose] def lastPlanes (n : ℕ) : Finset (Fin (n - 1)) :=
  Finset.univ.filter fun k => n - 3 ≤ k.val

theorem card_lastPlanes_le (n : ℕ) : (lastPlanes n).card ≤ 2 := by
  refine le_trans (Finset.card_le_card_of_injOn (fun y => y.val)
    (t := Finset.Icc (n - 3) (n - 2)) ?_ ?_) (by rw [Nat.card_Icc]; omega)
  · intro y hy
    have h1 : n - 3 ≤ y.val := by simpa [lastPlanes] using hy
    have h2 := y.isLt
    simp only [Finset.coe_Icc, Set.mem_Icc]
    omega
  · intro y _ z _ h
    exact Fin.ext h

theorem isCyclic_leviM_residual [Finite F] [CharP F 2] [Finite (spinGroup (quadMinus n F b c))]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Odd f) (hF : Nat.card F = 2 ^ f)
    (I : Set (Fin (n - 1)))
    (hno3 : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val)
    (hB3 : ¬ ∀ k : Fin (n - 1), n - 4 ≤ k.val → k ∈ I) :
    ∀ P : Subgroup (spinGroup (quadMinus n F b c)), P ≤ leviM (minusDatum n hirr) I →
      IsPGroup 5 P → IsCyclic P := by
  have hext := minusDatum_steinbergExtras n hirr
  by_cases hs : ∃ s ∈ I, s.val + 2 = n
  · obtain ⟨s, hsI, hsval⟩ := hs
    let IA : Set (Fin (n - 1)) := {k | k ∈ I ∧ k.val + 4 ≤ n}
    let IB : Set (Fin (n - 1)) := {k | k ∈ I ∧ n ≤ k.val + 3}
    have hAlong : ∀ k ∈ IA, ∃ hk : k.val + 1 < n - 1, k ∈ coordsF n IA ∧
        (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ coordsF n IA := by
      intro k hk
      have hk1 : k.val + 1 < n - 1 := by have := hk.2; omega
      exact ⟨hk1, self_mem_coordsF hk hk1, succ_mem_coordsF hk hk1⟩
    have hA2 : ¬ ∃ a ∈ IA, ∃ b ∈ IA, a.val + 2 ≤ b.val := by
      rintro ⟨a, ha, b, hb, hab⟩
      exact hno3 ⟨a, ha.1, b, hb.1, s, hsI, hab, by have := hb.2; omega⟩
    have hA := eq_bot_leviM_long hirr hf hF IA (coordsF n IA) hAlong (card_coordsF_le_three IA hA2)
    have hB := isCyclic_leviM_two hirr hf hF IB (lastPlanes n) (fun k hk => by
      refine ⟨by simpa [lastPlanes] using (by have := hk.2; omega : n - 3 ≤ k.val), fun hk' => ?_⟩
      simp only [lastPlanes, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hk.2
      omega) (card_lastPlanes_le n)
    have hcomm : Commutes (leviM (minusDatum n hirr) IA) (leviM (minusDatum n hirr) IB) := by
      refine commutes_iSup_iSup fun i hi j hj => ?_
      have hjlt : j.val < n - 1 := j.isLt
      have hij : i.val + 2 ≤ j.val := by
        by_cases h5 : i.val + 5 ≤ n
        · have := hj.2
          omega
        · by_cases hj3 : j.val + 3 = n
          · exfalso
            apply hB3
            intro k hk
            have hkc : k.val = i.val ∨ k.val = j.val ∨ k.val = s.val := by
              have := k.isLt
              have := hi.2
              omega
            rcases hkc with h | h | h
            · exact (Fin.ext h) ▸ hi.1
            · exact (Fin.ext h) ▸ hj.1
            · exact (Fin.ext h) ▸ hsI
          · have := hj.2
            have := hi.2
            omega
      exact commutes_rankOne_of_cartan_eq_zero hext (fun h => by rw [h] at hij; omega)
        (cartan_minusDatum_eq_zero hirr hij)
    have hle : leviM (minusDatum n hirr) I ≤
        leviM (minusDatum n hirr) IA ⊔ leviM (minusDatum n hirr) IB := by
      refine iSup₂_le fun k hk => ?_
      by_cases hk4 : k.val + 4 ≤ n
      · exact (rankOne_le_leviM (D := minusDatum n hirr) (I := IA) ⟨hk, hk4⟩).trans le_sup_left
      · exact (rankOne_le_leviM (D := minusDatum n hirr) (I := IB)
          ⟨hk, by omega⟩).trans le_sup_right
    intro P hP hP5
    exact isCyclic_sup_of_commutes hcomm hA hB P (hP.trans hle) hP5
  · push Not at hs
    have hlong : ∀ k ∈ I, ∃ hk : k.val + 1 < n - 1, k ∈ coordsF n I ∧
        (⟨k.val + 1, hk⟩ : Fin (n - 1)) ∈ coordsF n I := by
      intro k hk
      have h1 := hs k hk
      have h2 := k.isLt
      have hk1 : k.val + 1 < n - 1 := by omega
      exact ⟨hk1, self_mem_coordsF hk hk1, succ_mem_coordsF hk hk1⟩
    exact isCyclic_leviM_long hirr hf hF I (coordsF n I) hlong
      ((card_coordsF_le_six I hno3).trans (by norm_num))

end Residual

section Roots

variable {n : ℕ}

theorem toStdB_root_not_three {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) {x y z : Fin (n - 1)} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    toStdB (n - 1) γ x = 0 ∨ toStdB (n - 1) γ y = 0 ∨ toStdB (n - 1) γ z = 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy, hz⟩ := h
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, h'⟩ | ⟨i, s, h'⟩
  · rw [h'] at hx hy hz
    have h1 := SpinFrame.eq_or_eq_of_single_add_single_apply_ne_zero hx
    have h2 := SpinFrame.eq_or_eq_of_single_add_single_apply_ne_zero hy
    have h3 := SpinFrame.eq_or_eq_of_single_add_single_apply_ne_zero hz
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with h3 | h3 <;> simp_all
  · rw [h'] at hx hy
    have h1 : x = i := by
      by_contra h1
      exact hx (Pi.single_eq_of_ne h1 _)
    have h2 : y = i := by
      by_contra h2
      exact hy (Pi.single_eq_of_ne h2 _)
    exact hxy (h1.trans h2.symm)

theorem toStdB_weylAction_simple {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k : Fin (minusDatum n hirr).rank)
    (v : Fin (minusDatum n hirr).rank → ℤ) :
    toStdB (minusDatum n hirr).rank (weylAction (minusDatum n hirr).isFiniteType
      ((coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem.simple k) v) =
      stdReflB (minusDatum n hirr).rank k (toStdB (minusDatum n hirr).rank v) := by
  rw [weylAction_simple]
  exact toStdB_reflection (minusDatum n hirr).rank k v

theorem toStdB_weylAction_w {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p l s : Fin (minusDatum n hirr).rank}
    (hpl : p.val + 1 = l.val) (hls : l.val + 1 = s.val) (hs : s.val + 2 = n) :
    toStdB (minusDatum n hirr).rank (weylAction (minusDatum n hirr).isFiniteType
      ((coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem.simple l *
        (coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem.simple s *
        (coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem.simple l)
      (Pi.single p 1)) = Pi.single p 1 + Pi.single l 1 := by
  have hr : (minusDatum n hirr).rank = n - 1 := rfl
  rw [weylAction_mul_apply, weylAction_mul_apply, toStdB_weylAction_simple,
    toStdB_weylAction_simple, toStdB_weylAction_simple,
    toStdB_single_of_lt (minusDatum n hirr).rank (show p.val + 1 < (minusDatum n hirr).rank by
      have := s.isLt; omega)]
  have hl1 : l.val + 1 < (minusDatum n hirr).rank := by have := s.isLt; omega
  have hs1 : ¬ s.val + 1 < (minusDatum n hirr).rank := by omega
  rw [stdReflB_of_lt _ hl1, stdReflB_of_not_lt _ hs1, stdReflB_of_lt _ hl1]
  have hpl' : (⟨p.val + 1, by have := s.isLt; omega⟩ : Fin (minusDatum n hirr).rank) = l :=
    Fin.ext hpl
  have hls' : (⟨l.val + 1, hl1⟩ : Fin (minusDatum n hirr).rank) = s := Fin.ext hls
  rw [hpl', hls']
  funext a
  simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply, Pi.single_apply,
    Equiv.swap_apply_def]
  have hps : p ≠ s := fun h => by rw [h] at hpl; omega
  have hpl2 : p ≠ l := fun h => by rw [h] at hpl; omega
  have hls2 : l ≠ s := fun h => by rw [h] at hls; omega
  split_ifs <;> simp_all

section Cones

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem openCone_p_eq_empty {p l : Fin (minusDatum n hirr).rank} (hpl : p.val + 1 = l.val)
    {β : Fin (minusDatum n hirr).rank → ℤ}
    (hβ : toStdB (minusDatum n hirr).rank β = Pi.single p 1 + Pi.single l 1) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    openCone (minusDatum n hirr).roots (Pi.single p 1) (σ • β) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  have hp1 : p.val + 1 < (minusDatum n hirr).rank := by have := l.isLt; omega
  have hpl' : (⟨p.val + 1, hp1⟩ : Fin (minusDatum n hirr).rank) = l := Fin.ext hpl
  have hne : p ≠ l := fun h => by rw [h] at hpl; omega
  have h1 : toStdB (minusDatum n hirr).rank (a • Pi.single p 1 + b • σ • β) p = 0 ∨
      toStdB (minusDatum n hirr).rank (a • Pi.single p 1 + b • σ • β) p = 1 ∨
      toStdB (minusDatum n hirr).rank (a • Pi.single p 1 + b • σ • β) p = -1 :=
    toStdB_apply_mem_of_mem_roots n hε p
  have h2 : toStdB (minusDatum n hirr).rank (a • Pi.single p 1 + b • σ • β) l = 0 ∨
      toStdB (minusDatum n hirr).rank (a • Pi.single p 1 + b • σ • β) l = 1 ∨
      toStdB (minusDatum n hirr).rank (a • Pi.single p 1 + b • σ • β) l = -1 :=
    toStdB_apply_mem_of_mem_roots n hε l
  rw [SpinOdd.toStdB_comb, toStdB_smul, hβ, toStdB_single_of_lt _ hp1, hpl'] at h1 h2
  simp [hne, hne.symm] at h1 h2
  rcases hσ with rfl | rfl <;> omega

theorem openCone_s_eq_empty {p l s : Fin (minusDatum n hirr).rank} (hpl : p.val + 1 = l.val)
    (hls : l.val + 1 = s.val) (hs : s.val + 2 = n) {β : Fin (minusDatum n hirr).rank → ℤ}
    (hβ : toStdB (minusDatum n hirr).rank β = Pi.single p 1 + Pi.single l 1) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    openCone (minusDatum n hirr).roots (Pi.single s 1) (σ • β) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  have hr : (minusDatum n hirr).rank = n - 1 := rfl
  have hs1 : ¬ s.val + 1 < (minusDatum n hirr).rank := by omega
  have hps : p ≠ s := fun h => by rw [h] at hpl; omega
  have hpl2 : p ≠ l := fun h => by rw [h] at hpl; omega
  have hls2 : l ≠ s := fun h => by rw [h] at hls; omega
  have h := toStdB_root_not_three (n := n) (γ := a • Pi.single s 1 + b • σ • β) hε hpl2 hps hls2
  change toStdB (minusDatum n hirr).rank (a • Pi.single s 1 + b • σ • β) p = 0 ∨
    toStdB (minusDatum n hirr).rank (a • Pi.single s 1 + b • σ • β) l = 0 ∨
    toStdB (minusDatum n hirr).rank (a • Pi.single s 1 + b • σ • β) s = 0 at h
  rw [SpinOdd.toStdB_comb, toStdB_smul, hβ, toStdB_single_of_not_lt _ hs1] at h
  simp [hps, hls2, hpl2, hps.symm, hls2.symm, hpl2.symm] at h
  rcases hσ with rfl | rfl <;> omega

theorem linIndepPair_p {p l : Fin (minusDatum n hirr).rank} (hpl : p.val + 1 = l.val)
    {β : Fin (minusDatum n hirr).rank → ℤ}
    (hβ : toStdB (minusDatum n hirr).rank β = Pi.single p 1 + Pi.single l 1) :
    LinIndepPair (Pi.single p 1) β := by
  intro a b hab
  have hp1 : p.val + 1 < (minusDatum n hirr).rank := by have := l.isLt; omega
  have hpl' : (⟨p.val + 1, hp1⟩ : Fin (minusDatum n hirr).rank) = l := Fin.ext hpl
  have hne : p ≠ l := fun h => by rw [h] at hpl; omega
  have h1 := congrArg (fun v => toStdB (minusDatum n hirr).rank v p) hab
  have h2 := congrArg (fun v => toStdB (minusDatum n hirr).rank v l) hab
  simp only [toStdB_add, toStdB_smul, toStdB_zero, hβ, toStdB_single_of_lt _ hp1, hpl',
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul] at h1 h2
  simp [hne, hne.symm] at h1 h2
  omega

theorem linIndepPair_s {p l s : Fin (minusDatum n hirr).rank} (hpl : p.val + 1 = l.val)
    (hls : l.val + 1 = s.val) (hs : s.val + 2 = n) {β : Fin (minusDatum n hirr).rank → ℤ}
    (hβ : toStdB (minusDatum n hirr).rank β = Pi.single p 1 + Pi.single l 1) :
    LinIndepPair (Pi.single s 1) β := by
  intro a b hab
  have hr : (minusDatum n hirr).rank = n - 1 := rfl
  have hs1 : ¬ s.val + 1 < (minusDatum n hirr).rank := by omega
  have hps : p ≠ s := fun h => by rw [h] at hpl; omega
  have hpl2 : p ≠ l := fun h => by rw [h] at hpl; omega
  have hls2 : l ≠ s := fun h => by rw [h] at hls; omega
  have h1 := congrArg (fun v => toStdB (minusDatum n hirr).rank v p) hab
  have h2 := congrArg (fun v => toStdB (minusDatum n hirr).rank v s) hab
  simp only [toStdB_add, toStdB_smul, toStdB_zero, hβ, toStdB_single_of_not_lt _ hs1,
    Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1 h2
  simp [hps, hps.symm, hpl2, hls2.symm] at h1 h2
  omega

end Cones

end Roots

section B3

variable {n : ℕ} {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem three_le_pRank_of_B3 {Y : Type*} [Group Y]
    {π : spinGroup (quadMinus n F b c) →* Y} {M : ℕ} {J : Subgroup Y}
    (hb : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π M)
    (hBJ : borel (minusDatum n hirr) (minusTorus n hirr) ≤ J.comap π)
    (hr : ∀ i, CFSG.AGLEmbeddingD2.ParabRealThree.HasRealOrderThree (minusDatum n hirr) i)
    {X : Type*} [Group X] [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) {p l s : Fin (minusDatum n hirr).rank}
    (hpl : p.val + 1 = l.val) (hls : l.val + 1 = s.val) (hs : s.val + 2 = n)
    (hp : p ∈ negIndices (minusDatum n hirr) (J.comap π))
    (hl : l ∈ negIndices (minusDatum n hirr) (J.comap π))
    (hs' : s ∈ negIndices (minusDatum n hirr) (J.comap π)) :
    3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  have hct := hb.ct
  have hext := hb.extras
  have hps : p ≠ s := fun h => by rw [h] at hpl; omega
  have hx := ((actsAs_n hct l).mul (actsAs_n hct s)).mul (actsAs_n hct l)
  have hβ := toStdB_weylAction_w hirr hpl hls hs
  have hxJ : π (minusWeyl n hirr l * minusWeyl n hirr s * minusWeyl n hirr l) ∈ J := by
    have hL : ∀ k ∈ negIndices (minusDatum n hirr) (J.comap π), π (minusWeyl n hirr k) ∈ J :=
      fun k hk => rankOne_le_of_mem_negIndices hBJ hk (hct.n_mem k)
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem (hL l hl) (hL s hs')) (hL l hl)
  refine three_le_pRank_of_triple hb.ker_central ρ hρ hρker
    (commutes_rankOne_of_cartan_eq_zero hext hps
      (cartan_minusDatum_eq_zero hirr (i := p) (j := s) (by omega)))
    (commutes_rankOne_map_conj hext hx p p (linIndepPair_p hirr hpl hβ)
      (by simpa using openCone_p_eq_empty hirr hpl hβ (Or.inl rfl))
      (by simpa using openCone_p_eq_empty hirr hpl hβ (Or.inr rfl)))
    (commutes_rankOne_map_conj hext hx s p (linIndepPair_s hirr hpl hls hs hβ)
      (by simpa using openCone_s_eq_empty hirr hpl hls hs hβ (Or.inl rfl))
      (by simpa using openCone_s_eq_empty hirr hpl hls hs hβ (Or.inr rfl)))
    (realThreeOver_rankOne hBJ hp (hr p)) (realThreeOver_rankOne hBJ hs' (hr s))
    ((realThreeOver_rankOne hBJ hp (hr p)).conj hxJ)

end B3

section Even

variable {n : ℕ} {F : Type} [Field F] {b c : F}

theorem eq_one_of_diagSL2_eq_one {ω : Fˣ} (h : diagSL2 ω = 1) : ω = 1 := by
  have h0 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simpa using h0

theorem exists_torus_three (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {ω : Fˣ} (hω : orderOf ω = 3)
    (k : Fin (n - 1)) : ∃ x ∈ minusTorus n hirr k, x ^ 3 = 1 ∧ x ≠ 1 := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
  by_cases hk : k.val + 1 < n - 1
  · refine ⟨(minusFrame n b c).longTorus (succ_ne_of_lt n hk) true false ω, ?_, ?_, ?_⟩
    · rw [minusTorus_of_lt n hirr hk]
      exact ⟨ω, rfl⟩
    · rw [← map_pow, hω3, map_one]
    · intro h
      rw [HypFrame.longTorus_apply] at h
      have := SpinFrame.longSL2_injective (minusFrame n b c).toHypFrame (succ_ne_of_lt n hk) true
        false (h.trans (map_one _).symm)
      have h1 := eq_one_of_diagSL2_eq_one this
      rw [h1, orderOf_one] at hω
      omega
  · refine ⟨(minusFrame n b c).shortTorus k true ω, ?_, ?_, ?_⟩
    · rw [minusTorus_of_not_lt n hirr hk, minusFrame_shortTorus_eq n hirr k ω]
      exact shortTorusElt_mem n hirr k (smul_ne_zero ω.ne_zero planeOne_ne_zero)
    · rw [← map_pow, hω3, map_one]
    · intro h
      rw [OddFrame.shortTorus_apply] at h
      have := SpinOdd.shortSL2_injective (minusFrame n b c) k true (h.trans (map_one _).symm)
      have h1 := eq_one_of_diagSL2_eq_one this
      rw [h1, orderOf_one] at hω
      omega

theorem ker_comp_spinToStatedProj_eq_bot [Finite F] [CharP F 2] (hn : 4 ≤ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) :
    (e.symm.toMonoidHom.comp (spinToStatedProj (quadMinus n F b c)
      (range_spinMatrix_quadMinus hn hirr))).ker = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have h1 : spinToStatedProj (quadMinus n F b c) (range_spinMatrix_quadMinus hn hirr) x = 1 := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.symm.injective] at hx
    exact hx
  have h2 : x ∈ (spinToStatedProj (quadMinus n F b c) (range_spinMatrix_quadMinus hn hirr)).ker :=
    h1
  rw [ker_spinToStatedProj] at h2
  obtain ⟨u, hu⟩ : spinMatrix (quadMinus n F b c) x ∈ StatedScalars _ F := h2
  have hmem : Matrix.GeneralLinearGroup.scalar _ u ∈ StatedOmega (StatedQuadMinus n F b c) := by
    rw [hu, ← range_spinMatrix_quadMinus hn hirr]
    exact ⟨x, rfl⟩
  have hu1 : (u : F) = 1 := CharTwo.sq_inj.1 (by
    rw [sq_eq_one_of_scalar_mem_statedOmega (coe_quadMinus n F b c)
      ⟨planeVec n planeOne, by rw [quadMinus_planeOne]; exact one_ne_zero⟩ hmem, one_pow])
  have hx1 : x ∈ (spinMatrix (quadMinus n F b c)).ker := by
    rw [MonoidHom.mem_ker, ← hu]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, hu1, map_one, Units.val_one])
  rw [ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero] at hx1
  exact Subgroup.mem_bot.1 hx1

end Even

set_option linter.unusedVariables false in
theorem three_le_pRank_spinMinus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) {X : Type} [Group X]
    [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (hρ3 : Nat.Coprime 3 (Nat.card ρ.ker)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (hQ : LeviSection.HasSubquotient J (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  classical
  have := Fintype.ofFinite F
  have hfin : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_spinMinus hirr hn e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have hM := hasSubquotient_leviM_of_parab hb' hBJ hQ
  have hr : ∀ i, CFSG.AGLEmbeddingD2.ParabRealThree.HasRealOrderThree (minusDatum n hirr) i :=
    CFSG.AGLEmbeddingD2.ParabRealThree.hasRealOrderThree_spinMinus hirr
  rcases Nat.even_or_odd (f : ℕ) with hfe | hfo
  ·
    obtain ⟨k, hk⟩ := hfe
    have hk1 : 1 ≤ k := by have := f.pos; omega
    have hq : Nat.card F = 4 ^ k := by rw [hfc, hk, ← two_mul, pow_mul]; norm_num
    have hq3 : 3 ∣ Nat.card F - 1 := by
      rw [hq]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
    obtain ⟨ω, hω⟩ := SquareLinear.exists_orderOf_eq_three hq3
    have hπ3 : Nat.Coprime 3 (Nat.card π'.ker) := by
      rw [hker', ker_comp_spinToStatedProj_eq_bot hn hirr e]
      simp
    obtain ⟨x, hxH, hx3, hx1⟩ := exists_torus_three hirr hω (⟨0, by omega⟩ : Fin (n - 1))
    obtain ⟨y, hyH, hy3, hy1⟩ := exists_torus_three hirr hω (⟨1, by omega⟩ : Fin (n - 1))
    obtain ⟨z, hzH, hz3, hz1⟩ := exists_torus_three hirr hω (⟨2, by omega⟩ : Fin (n - 1))
    exact (three_le_pRank_of_torus hb'.extras hπ3 hBJ
      (a := (⟨0, by omega⟩ : Fin (n - 1))) (b := (⟨1, by omega⟩ : Fin (n - 1)))
      (c := (⟨2, by omega⟩ : Fin (n - 1)))
      (fun h => absurd (congrArg Fin.val h) (by simp)) (fun h => absurd (congrArg Fin.val h)
        (by simp)) (fun h => absurd (congrArg Fin.val h) (by simp)) hxH hyH hzH hx3 hy3 hz3 hx1 hy1
      hz1).trans
      (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
  ·
    by_cases ho : ∃ a ∈ negIndices (minusDatum n hirr) (J.comap π'),
        ∃ b ∈ negIndices (minusDatum n hirr) (J.comap π'),
        ∃ c ∈ negIndices (minusDatum n hirr) (J.comap π'), a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val
    · obtain ⟨a, ha, b', hb2, c', hc, hab, hbc⟩ := ho
      exact three_le_pRank_of_orth hb'.extras hb'.ker_central ρ hρ hρker hBJ hr
        (fun h => by rw [h] at hab; omega) (fun h => by rw [h] at hab; omega)
        (fun h => by rw [h] at hbc; omega) (cartan_minusDatum_eq_zero hirr hab)
        (cartan_minusDatum_eq_zero hirr (by omega)) (cartan_minusDatum_eq_zero hirr hbc) ha hb2 hc
    · by_cases hB3 : ∀ k : Fin (n - 1), n - 4 ≤ k.val →
          k ∈ negIndices (minusDatum n hirr) (J.comap π')
      · exact three_le_pRank_of_B3 hirr hb' hBJ hr ρ hρ hρker
          (p := (⟨n - 4, by omega⟩ : Fin (n - 1))) (l := (⟨n - 3, by omega⟩ : Fin (n - 1)))
          (s := (⟨n - 2, by omega⟩ : Fin (n - 1))) (by simp; omega) (by simp; omega)
          (by simp; omega) (hB3 _ (by simp)) (hB3 _ (by simp; omega)) (hB3 _ (by simp; omega))
      · exfalso
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        exact hM.false_of_isCyclic (isCyclic_leviM_residual hirr hfo hfc _ ho hB3)
          LeviSection.exists_not_isCyclic_five

end CFSG.AGLEmbeddingD2.SquareSpinMinus




