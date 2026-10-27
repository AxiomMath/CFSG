module

public import CFSG.LieType.Steinberg.PartBHalfSpace

public noncomputable section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal
open scoped commutatorElement

section Presented

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*} [Field k]
  (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ)

@[expose] def chevGen (γ : ι → ℤ) (c : k) : ChevPresented Φ k O C :=
  PresentedGroup.mk _ (chevOf γ c)

variable {O C}

theorem chevGen_eq_of {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (c : k) :
    chevGen O C γ c = PresentedGroup.of (⟨γ, hγ⟩, c) := by
  simp [chevGen, chevOf, hγ, PresentedGroup.of]

variable (O C) in
theorem chevRels_chevGen : ChevRels O C (chevGen O C (k := k)) where
  add γ hγ c d := by
    have h := PresentedGroup.one_of_mem (rels := relA Φ k ∪ relB Φ k O C)
      (Or.inl ⟨γ, hγ, c, d, rfl⟩)
    rw [map_mul, map_mul, map_inv, mul_inv_eq_one] at h
    exact h.symm
  comm α hα β hβ hαβ c d := by
    have h := PresentedGroup.one_of_mem (rels := relA Φ k ∪ relB Φ k O C)
      (Or.inr ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
    rw [map_mul, map_inv, mul_inv_eq_one, map_commutatorElement, map_list_prod, List.map_map] at h
    exact h

variable {K : Type*} [Group K]

omit [Field k] in
theorem lift_chevEval_chevOf (x : (ι → ℤ) → k → K) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (c : k) :
    FreeGroup.lift (chevEval x) (chevOf (Φ := Φ) γ c) = x γ c := by
  simp [chevOf, hγ, chevEval]

theorem chevEval_rels {x : (ι → ℤ) → k → K}
    (hadd : ∀ γ ∈ Φ.roots, ∀ c d, x γ (c + d) = x γ c * x γ d)
    (hcomm : CommutatorFormula x O C) :
    ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval x) r = 1 := by
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · simp only [map_mul, map_inv, lift_chevEval_chevOf x hγ, hadd γ hγ, mul_inv_cancel]
  · rw [map_mul, map_inv, map_commutatorElement, lift_chevEval_chevOf x hα,
      lift_chevEval_chevOf x hβ, map_list_prod, List.map_map, mul_inv_eq_one,
      hcomm α hα β hβ hαβ c d]
    refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
    rw [Function.comp_apply, lift_chevEval_chevOf x ((O.mem_iff α hα β hβ hαβ p).1 hp).2.2]

end Presented

section Symbols

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {K : Type*} [Group K]
  {X : (ι → ℤ) → Subgroup K}

theorem piF_apply_of (s : Symbol Φ X) : piF Φ X (FreeGroup.of s) = s.1.2 := by
  rw [piF, FreeGroup.lift_apply_of]

theorem stPi_apply_mk (w : FreeSt Φ X) : stPi Φ X (QuotientGroup.mk w) = piF Φ X w :=
  QuotientGroup.lift_mk _ _ _

end Symbols

section Main

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

local notation "ΦD" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem ChevalleyExtras.rels (hE : ChevalleyExtras D k x C O) :
    ∀ r ∈ relA (ΦD) k ∪ relB (ΦD) k O C, FreeGroup.lift (chevEval x) r = 1 :=
  chevEval_rels (fun γ hγ => (hE.param γ hγ).2.1) hE.comm

theorem ChevalleyExtras.toGroup_chevGen (hE : ChevalleyExtras D k x C O) :
    ∀ γ ∈ D.roots, ∀ c, PresentedGroup.toGroup hE.rels (chevGen O C γ c) = x γ c :=
  fun γ hγ c => by
    rw [chevGen_eq_of hγ, PresentedGroup.toGroup.of]
    rfl

@[expose] def ChevalleyExtras.symbol (hE : ChevalleyExtras D k x C O) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (c : k) : Symbol (ΦD) D.rootGroup :=
  ⟨(γ, x γ c), hγ, ((hE.param γ hγ).1 _).2 ⟨c, rfl⟩⟩

@[expose] def ChevalleyExtras.coord (hE : ChevalleyExtras D k x C O)
    (s : Symbol (ΦD) D.rootGroup) : k :=
  (((hE.param s.1.1 s.2.1).1 s.1.2).1 s.2.2).choose

theorem ChevalleyExtras.x_coord (hE : ChevalleyExtras D k x C O) (s : Symbol (ΦD) D.rootGroup) :
    x s.1.1 (hE.coord s) = s.1.2 :=
  (((hE.param s.1.1 s.2.1).1 s.1.2).1 s.2.2).choose_spec

theorem ChevalleyExtras.coord_symbol (hE : ChevalleyExtras D k x C O) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (c : k) : hE.coord (hE.symbol hγ c) = c :=
  (hE.param γ hγ).2.2 (hE.x_coord (hE.symbol hγ c))

variable {G : Type*} [Group G] {xh : (Fin D.rank → ℤ) → k → G} {π : G →* K}

theorem injOn_chevSub_pair [Finite k] (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hR : ChevRels O C xh) (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) (i : Fin D.rank) :
    Set.InjOn π (chevSub xh {Pi.single i 1, -Pi.single i 1}) := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (ΦD).single_mem i
  have hα' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (ΦD).neg_mem _ hα
  obtain ⟨φ, hφ, hU, hL⟩ := hE.rankOne i
  let R : RankOneRels G k :=
    { x := xh (Pi.single i 1)
      y := xh (-Pi.single i 1)
      x_add := hR.add _ hα
      y_add := hR.add _ hα'
      conj_x := fun t ht a => chevWeyl_conj_single hD hE hR hπ i ht a }
  have hle : chevSub xh {Pi.single i 1, -Pi.single i 1} ≤ R.sub := by
    refine iSup₂_le fun γ hγ => ?_
    rcases hγ with rfl | rfl
    · exact Subgroup.closure_mono Set.subset_union_left
    · exact Subgroup.closure_mono Set.subset_union_right
  exact (R.injOn_sub π φ hφ (fun a => (hπ _ hα a).trans (hU a).symm)
    (fun a => (hπ _ hα' a).trans (hL a).symm)).mono hle

theorem ChevalleyExtras.surjective_toGroup (hE : ChevalleyExtras D k x C O)
    (hsurj : Function.Surjective (stPi (ΦD) D.rootGroup)) :
    Function.Surjective (PresentedGroup.toGroup hE.rels) := by
  intro g
  obtain ⟨s, rfl⟩ := hsurj g
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  change ∃ a, _ = piF (ΦD) D.rootGroup w
  refine FreeGroup.induction_on w ⟨1, by simp⟩ (fun s => ?_) (fun s ⟨a, ha⟩ => ?_)
    (fun u v ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩)
  · refine ⟨chevGen O C s.1.1 (hE.coord s), ?_⟩
    rw [hE.toGroup_chevGen _ s.2.1, hE.x_coord, piF_apply_of]
  · exact ⟨a⁻¹, by rw [map_inv, ha, map_inv]⟩

@[expose] def ChevalleyExtras.symbolGen (hE : ChevalleyExtras D k x C O)
    (s : Symbol (ΦD) D.rootGroup) : ChevPresented (ΦD) k O C :=
  chevGen O C s.1.1 (hE.coord s)

theorem ChevalleyExtras.toGroup_lift_symbolGen (hE : ChevalleyExtras D k x C O)
    (w : FreeSt (ΦD) D.rootGroup) :
    PresentedGroup.toGroup hE.rels (FreeGroup.lift hE.symbolGen w) = piF (ΦD) D.rootGroup w := by
  have h : (PresentedGroup.toGroup hE.rels).comp (FreeGroup.lift hE.symbolGen) =
      piF (ΦD) D.rootGroup :=
    FreeGroup.ext_hom _ _ fun s => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, ChevalleyExtras.symbolGen,
        hE.toGroup_chevGen _ s.2.1, hE.x_coord, piF_apply_of]
  exact DFunLike.congr_fun h w

theorem ChevalleyExtras.lift_symbolGen_mem (hE : ChevalleyExtras D k x C O)
    {Ψ : Set (Fin D.rank → ℤ)} {w : FreeSt (ΦD) D.rootGroup}
    (hw : w ∈ freeSub (ΦD) D.rootGroup Ψ) :
    FreeGroup.lift hE.symbolGen w ∈ chevSub (chevGen O C) Ψ := by
  have hle : (freeSub (ΦD) D.rootGroup Ψ).map (FreeGroup.lift hE.symbolGen) ≤
      chevSub (chevGen O C) Ψ := by
    rw [freeSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, FreeGroup.lift_apply_of]
    exact xh_mem_chevSub hs _
  exact hle ⟨w, hw, rfl⟩

theorem ChevalleyExtras.lift_symbolGen_eq_one [Finite k] (hD : D.divisible = ∅)
    (hE : ChevalleyExtras D k x C O) :
    ∀ w ∈ rel1 (ΦD) D.rootGroup ∪ rel2 (ΦD) D.rootGroup, FreeGroup.lift hE.symbolGen w = 1 := by
  have hR := chevRels_chevGen O C (k := k)
  rintro w (⟨α, hα, β, hβ, hneg, hw, h1⟩ | ⟨i, hw, h1⟩)
  · exact injOn_chevSub_cone hD hE hR hE.toGroup_chevGen hα hβ hneg (hE.lift_symbolGen_mem hw)
      (one_mem _) (by rw [hE.toGroup_lift_symbolGen, h1, map_one])
  · exact injOn_chevSub_pair hD hE hR hE.toGroup_chevGen i (hE.lift_symbolGen_mem hw)
      (one_mem _) (by rw [hE.toGroup_lift_symbolGen, h1, map_one])

theorem ChevalleyExtras.injective_toGroup [Finite k] (hD : D.divisible = ∅)
    (hE : ChevalleyExtras D k x C O) (hbij : Function.Bijective (stPi (ΦD) D.rootGroup)) :
    Function.Injective (PresentedGroup.toGroup hE.rels) := by
  have hN : relN (ΦD) D.rootGroup ≤ (FreeGroup.lift hE.symbolGen).ker :=
    Subgroup.normalClosure_le_normal fun w hw => hE.lift_symbolGen_eq_one hD w hw
  let ψ : StGroup (ΦD) D.rootGroup →* ChevPresented (ΦD) k O C :=
    QuotientGroup.lift (relN (ΦD) D.rootGroup) (FreeGroup.lift hE.symbolGen) hN
  let e := MulEquiv.ofBijective (stPi (ΦD) D.rootGroup) hbij
  have hleft : (ψ.comp e.symm.toMonoidHom).comp (PresentedGroup.toGroup hE.rels) =
      MonoidHom.id _ := by
    refine PresentedGroup.ext fun g => ?_
    obtain ⟨⟨γ, hγ⟩, a⟩ := g
    have hγ' : γ ∈ D.roots := hγ
    have he : e.symm (x γ a) = QuotientGroup.mk (FreeGroup.of (hE.symbol hγ' a)) := by
      rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, stPi_apply_mk, piF_apply_of]
      rfl
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, PresentedGroup.toGroup.of,
      MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
    change ψ (e.symm (x γ a)) = _
    rw [he]
    change QuotientGroup.lift _ (FreeGroup.lift hE.symbolGen) _ (QuotientGroup.mk _) = _
    rw [QuotientGroup.lift_mk, FreeGroup.lift_apply_of, ChevalleyExtras.symbolGen,
      hE.coord_symbol hγ']
    exact chevGen_eq_of hγ a
  exact Function.LeftInverse.injective (g := ψ.comp e.symm.toMonoidHom)
    fun g => DFunLike.congr_fun hleft g

theorem chevPresented_bijective [Finite k] (hD : D.divisible = ∅)
    (hE : ChevalleyExtras D k x C O) (hbij : Function.Bijective (stPi (ΦD) D.rootGroup)) :
    ∃ h : ∀ r ∈ relA (ΦD) k ∪ relB (ΦD) k O C, FreeGroup.lift (chevEval x) r = 1,
      Function.Bijective (PresentedGroup.toGroup h) :=
  ⟨hE.rels, hE.injective_toGroup hD hbij, hE.surjective_toGroup hbij.2⟩

theorem bijective_of_comp {A B N : Type*} [Group A] [Group B] [Group N] {σ : A →* B}
    {p : B →* N} {q : A →* N} (hcomp : ∀ a, p (σ a) = q a) (hσ : Function.Surjective σ)
    (hq : Function.Bijective q) : Function.Bijective p := by
  refine ⟨fun b₁ b₂ hb => ?_, fun n => ?_⟩
  · obtain ⟨a₁, rfl⟩ := hσ b₁
    obtain ⟨a₂, rfl⟩ := hσ b₂
    rw [hcomp, hcomp] at hb
    rw [hq.1 hb]
  · obtain ⟨a, rfl⟩ := hq.2 n
    exact ⟨σ a, hcomp a⟩

@[expose] def ChevalleyExtras.genSymbol (hE : ChevalleyExtras D k x C O) (g : ChevGen (ΦD) k) :
    FreeSt (ΦD) D.rootGroup :=
  FreeGroup.of (hE.symbol g.1.2 g.2)

theorem ChevalleyExtras.piF_lift_genSymbol (hE : ChevalleyExtras D k x C O)
    (r : FreeGroup (ChevGen (ΦD) k)) :
    piF (ΦD) D.rootGroup (FreeGroup.lift hE.genSymbol r) = FreeGroup.lift (chevEval x) r := by
  have h : (piF (ΦD) D.rootGroup).comp (FreeGroup.lift hE.genSymbol) =
      FreeGroup.lift (chevEval x) :=
    FreeGroup.ext_hom _ _ fun g => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
        ChevalleyExtras.genSymbol, piF_apply_of]
      rfl
  exact DFunLike.congr_fun h r

theorem ChevalleyExtras.lift_genSymbol_chevOf_mem (hE : ChevalleyExtras D k x C O)
    {Ψ : Set (Fin D.rank → ℤ)} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hΨ : γ ∈ Ψ) (a : k) :
    FreeGroup.lift hE.genSymbol (chevOf (Φ := ΦD) γ a) ∈ freeSub (ΦD) D.rootGroup Ψ := by
  have hγ' : γ ∈ (ΦD).roots := hγ
  simp only [chevOf, hγ', ↓reduceDIte, FreeGroup.lift_apply_of]
  exact Subgroup.subset_closure ⟨hE.symbol hγ a, hΨ, rfl⟩

theorem ChevalleyExtras.lift_genSymbol_mem_rel1 (hD : D.divisible = ∅)
    (hE : ChevalleyExtras D k x C O) :
    ∀ r ∈ relA (ΦD) k ∪ relB (ΦD) k O C,
      FreeGroup.lift hE.genSymbol r ∈ rel1 (ΦD) D.rootGroup := by
  rintro r (⟨γ, hγ, a, b, rfl⟩ | ⟨α, hα, β, hβ, hαβ, a, b, rfl⟩)
  · have hc := mem_cone_left (Ψ := D.roots) γ hγ
    refine ⟨γ, hγ, γ, hγ, not_isNegMultiple_self ((ΦD).ne_zero_of_mem hγ), ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      exact mul_mem (mul_mem (hE.lift_genSymbol_chevOf_mem hγ hc a)
        (hE.lift_genSymbol_chevOf_mem hγ hc b)) (inv_mem (hE.lift_genSymbol_chevOf_mem hγ hc _))
    · rw [hE.piF_lift_genSymbol]
      exact hE.rels _ (Or.inl ⟨γ, hγ, a, b, rfl⟩)
  · refine ⟨α, hα, β, hβ, not_isNegMultiple_of_add_ne_zero D.isFiniteType hD hα hβ hαβ, ?_, ?_⟩
    · rw [map_mul, map_inv, map_commutatorElement, map_list_prod, List.map_map]
      have hα' := hE.lift_genSymbol_chevOf_mem hα (mem_cone_left (Ψ := D.roots) β hα) a
      have hβ' := hE.lift_genSymbol_chevOf_mem hβ (mem_cone_right (Ψ := D.roots) α hβ) b
      refine mul_mem ?_ (inv_mem (Subgroup.list_prod_mem _ fun z hz => ?_))
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hα' hβ') (inv_mem hα')) (inv_mem hβ')
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
        have hp' := (O.mem_iff α hα β hβ hαβ p).1 hp
        exact hE.lift_genSymbol_chevOf_mem (Ψ := cone (ΦD).roots α β) hp'.2.2
          ⟨hp'.2.2, p.1, p.2, rfl⟩ _
    · rw [hE.piF_lift_genSymbol]
      exact hE.rels _ (Or.inr ⟨α, hα, β, hβ, hαβ, a, b, rfl⟩)

theorem redundantR2 [Finite k] (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hbij : Function.Bijective (stPi (ΦD) D.rootGroup)) : RedundantR2 (ΦD) D.rootGroup := by
  obtain ⟨h, hb⟩ := chevPresented_bijective hD hE hbij
  set N1 := Subgroup.normalClosure (rel1 (ΦD) D.rootGroup)
  have hσ : ∀ r ∈ relA (ΦD) k ∪ relB (ΦD) k O C,
      FreeGroup.lift ((QuotientGroup.mk' N1) ∘ hE.genSymbol) r = 1 := by
    intro r hr
    have e : FreeGroup.lift ((QuotientGroup.mk' N1) ∘ hE.genSymbol) =
        (QuotientGroup.mk' N1).comp (FreeGroup.lift hE.genSymbol) :=
      FreeGroup.ext_hom _ _ fun g => by
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
        rfl
    rw [e, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure (hE.lift_genSymbol_mem_rel1 hD r hr)
  have hle : N1 ≤ (piF (ΦD) D.rootGroup).ker := Subgroup.normalClosure_le_normal (by
    rintro w ⟨-, -, -, -, -, -, hw⟩
    exact hw)
  have hcomp : ∀ g, QuotientGroup.lift N1 (piF (ΦD) D.rootGroup) hle
      (PresentedGroup.toGroup hσ g) = PresentedGroup.toGroup h g := by
    have h' : (QuotientGroup.lift N1 (piF (ΦD) D.rootGroup) hle).comp
        (PresentedGroup.toGroup hσ) = PresentedGroup.toGroup h :=
      PresentedGroup.ext fun g => by
        rw [MonoidHom.comp_apply, PresentedGroup.toGroup.of, PresentedGroup.toGroup.of,
          Function.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
          ChevalleyExtras.genSymbol, piF_apply_of]
        rfl
    exact fun g => DFunLike.congr_fun h' g
  have hσsurj : Function.Surjective (PresentedGroup.toGroup hσ) := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    refine FreeGroup.induction_on w ⟨1, by simp⟩ (fun s => ?_) (fun s ⟨a, ha⟩ => ?_)
      (fun u v ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩)
    · refine ⟨PresentedGroup.of (⟨s.1.1, s.2.1⟩, hE.coord s), ?_⟩
      rw [PresentedGroup.toGroup.of]
      change QuotientGroup.mk (FreeGroup.of (hE.symbol s.2.1 (hE.coord s))) = _
      congr 2
      exact Subtype.ext (Prod.ext rfl (hE.x_coord s))
    · exact ⟨a⁻¹, by rw [map_inv, ha]; rfl⟩
  exact bijective_of_comp hcomp hσsurj hb

end Main

end CFSG.LieType.Steinberg
