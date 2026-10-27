module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutD
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Actors

variable {τ : Tag} {K : Type} [Field K]

theorem exactPerm_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) (ε : ℕ) (j : Fin τ.rank) :
    exactPerm τ ε j = j := by
  rcases hτ with rfl | rfl <;> rfl

variable (K) in
theorem exactQ_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) (ε : ℕ) : exactQ τ K ε = 1 := by
  rcases hτ with rfl | rfl <;> rfl


theorem exactNormalAutGL_torusElt_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ)
    (σ : K ≃+* K) (ε : ℕ) (j : Fin τ.rank) (μ : Kˣ) :
    exactNormalAutGL τ K a σ ε (torusElt τ K j μ) =
      torusElt τ K j (Units.map σ.toRingHom.toMonoidHom μ) := by
  have h1 : Units.map (entrywiseHom σ.toRingHom) (torusElt τ K j μ) =
      torusElt τ K j (Units.map σ.toRingHom.toMonoidHom μ) := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    congr 1
    funext k
    rw [map_zpow]
  rw [exactNormalAutGL_apply, h1, exactQ_E7_E8 K hτ, mul_one, inv_one, mul_one]
  exact conj_rootDiagUnit_of_mem_torusGroup a (torusElt_mem_torusGroup _ _)


theorem exactNormalAutGL_pinnedX_single_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ)
    (σ : K ≃+* K) (ε : ℕ) (j : Fin τ.rank) (c : K) :
    exactNormalAutGL τ K a σ ε (pinnedX τ K (Pi.single j 1) c) =
      pinnedX τ K (Pi.single j 1) ((a j : K) * σ c) := by
  rw [pinnedX_single, pinnedX_single, exactNormalAutGL_xUnit, exactPerm_E7_E8 hτ]

end Actors

section Main

variable {τ : Tag} {K : Type} [Field K]


theorem exists_eq_conj_of_fix_perpLevi_of_exists (hτ : τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) (β : MulAut (adjointGroup τ K))
    (hβ : ∀ x ∈ (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K), β x = x) :
    ∃ g : adjointGroup τ K, β = MulAut.conj g ∧
      g ∈ centralizer (((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) :
        Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨l, hl1⟩ : ∃ l : Kˣ, l ≠ 1 := by
    obtain ⟨c0, hc0, hc1⟩ := hK
    exact ⟨Units.mk0 c0 hc0, fun h => hc1 (by simpa using congrArg Units.val h)⟩
  have hr := isRoot_highRoot τ
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form τ hτ' K
  obtain ⟨g, a, σ, ε, hga⟩ := hex β
  have hβψ : ∀ x : adjointGroup τ K, (β x : ModGL τ K) =
      (g : ModGL τ K) * exactNormalAutGL τ K a σ ε (x : ModGL τ K) * (g : ModGL τ K)⁻¹ := by
    intro x
    rw [hga x, exactNormalAutGL_apply]
    simp only [mul_assoc]
  have hfix : ∀ {x : ModGL τ K}, x ∈ rootSpan τ K (EPilot.perpRoots τ) →
      (g : ModGL τ K) * exactNormalAutGL τ K a σ ε x * (g : ModGL τ K)⁻¹ = x := by
    intro x hx
    have hxC : x ∈ adjointGroup τ K := EPilot.rootSpan_le_adjointGroup' _ hx
    have e := congrArg Subtype.val (hβ ⟨x, hxC⟩ (mem_subgroupOf.2 hx))
    rw [hβψ] at e
    exact e
  have hg1 : (g : ModGL τ K) ∈ toralCentralizer τ K 1 := by
    refine mem_toralCentralizer.2 ⟨g.2, ?_⟩
    rw [rootDiagUnit_one, one_mul, inv_one, mul_one]
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ K 1).1 g hg1
  have huU : u ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu
  have hvI : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  obtain ⟨σl, hσl⟩ : ∃ σl : Kˣ, σl = Units.map σ.toRingHom.toMonoidHom l := ⟨_, rfl⟩
  have hσl1 : σl ≠ 1 := by
    intro h1
    apply hl1
    refine Units.map_injective (f := σ.toRingHom.toMonoidHom) σ.injective ?_
    rw [← hσl, h1, map_one]
  have htor : ∀ j : Fin τ.rank, j ≠ highNode τ →
      rootDiagUnit τ (fun k => l ^ τ.cartan j k) * u *
          (rootDiagUnit τ (fun k => l ^ τ.cartan j k))⁻¹ = u ∧
        rootDiagUnit τ (fun k => σl ^ τ.cartan j k) * v *
          (rootDiagUnit τ (fun k => σl ^ τ.cartan j k))⁻¹ = v := by
    intro j hj
    have hx := hfix (EPilot.torusElt_mem_rootSpan_perpRoots hj l)
    rw [exactNormalAutGL_torusElt_E7_E8 hτ, ← hσl, torusElt_eq_rootDiagUnit,
      torusElt_eq_rootDiagUnit, hgdec] at hx
    have hconj : h * u * canonicalRep (coxeterSystem τ) K w * v *
          rootDiagUnit τ (fun k => σl ^ τ.cartan j k) =
        rootDiagUnit τ (fun k => l ^ τ.cartan j k) *
          (h * u * canonicalRep (coxeterSystem τ) K w * v) := by
      rw [← hx]
      group
    obtain ⟨h1, h2, -⟩ := E6Pilot.twisted_torus_bruhat hh huU hvI
      (by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _)
      (by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _) hconj
    exact ⟨h1, h2⟩
  have hcomm : ∀ {t x : ModGL τ K}, t * x * t⁻¹ = x →
      x ∈ centralizer ({t} : Set (ModGL τ K)) := by
    intro t x htx
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mul_inv_eq_iff_eq_mul.1 htx
  have hposcl : ∀ α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α},
      ∀ β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}, ∀ m n : ℕ, 1 ≤ m →
        1 ≤ n → IsRoot τ (m • α + n • β) →
          m • α + n • β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} := by
    intro α hα β hβ m n hm hn hmn
    refine ⟨hmn, ?_⟩
    rw [height_nsmul_add_nsmul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith [hα.2, hβ.2]
  have hur : u ∈ rootSubgroup τ K (highRoot τ) :=
    EPilot.mem_rootSubgroup_highRoot_of_forall hτ' hl1 (fun α hα => hα) hposcl huU
      fun j hj => hcomm (htor j hj).1
  have hvr : v ∈ rootSubgroup τ K (highRoot τ) :=
    EPilot.mem_rootSubgroup_highRoot_of_forall hτ' hσl1
      (fun α hα => inversionSet_pos hα) (inversionSet_closed w) hvI fun k hk =>
        hcomm (htor k hk).2
  have hJD := EPilot.highRootSL2_le_centralizer_perpLevi (K := K) hτ'
  have hJ : ∀ {x : ModGL τ K}, x ∈ rootSubgroup τ K (highRoot τ) →
      x ∈ EPilot.highRootSL2 τ K := fun hx => Subgroup.mem_sup_left hx
  have hu' : h * u * h⁻¹ ∈ rootSubgroup τ K (highRoot τ) :=
    (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup hr hh) u).1 hur
  have hm : ∀ {x : ModGL τ K}, x ∈ rootSpan τ K (EPilot.perpRoots τ) →
      exactNormalAutGL τ K a σ ε x ∈ rootSpan τ K (EPilot.perpRoots τ) →
      (h * canonicalRep (coxeterSystem τ) K w) * exactNormalAutGL τ K a σ ε x *
        (h * canonicalRep (coxeterSystem τ) K w)⁻¹ = x := by
    intro x hx hψx
    have e := hfix hx
    rw [hgdec] at e
    have hvc : v * exactNormalAutGL τ K a σ ε x * v⁻¹ = exactNormalAutGL τ K a σ ε x := by
      rw [← Subgroup.mem_centralizer_iff.1 (hJD (hJ hvr)) _ hψx, mul_inv_cancel_right]
    have hkc : (h * u * h⁻¹)⁻¹ * x * (h * u * h⁻¹) = x := by
      rw [mul_assoc, Subgroup.mem_centralizer_iff.1 (hJD (hJ hu')) _ hx, inv_mul_cancel_left]
    calc (h * canonicalRep (coxeterSystem τ) K w) * exactNormalAutGL τ K a σ ε x *
          (h * canonicalRep (coxeterSystem τ) K w)⁻¹ =
        (h * canonicalRep (coxeterSystem τ) K w) *
          (v * exactNormalAutGL τ K a σ ε x * v⁻¹) *
            (h * canonicalRep (coxeterSystem τ) K w)⁻¹ := by rw [hvc]
      _ = (h * u * h⁻¹)⁻¹ * (h * u * canonicalRep (coxeterSystem τ) K w * v *
          exactNormalAutGL τ K a σ ε x *
            (h * u * canonicalRep (coxeterSystem τ) K w * v)⁻¹) * (h * u * h⁻¹) := by
          group
      _ = (h * u * h⁻¹)⁻¹ * x * (h * u * h⁻¹) := by rw [e]
      _ = x := hkc
  have hroot : ∀ j : Fin τ.rank, j ≠ highNode τ → ∀ c : K,
      pinnedX τ K (w • (Pi.single j 1 : Fin τ.rank → ℤ))
          (torusRootChar h (w • (Pi.single j 1 : Fin τ.rank → ℤ)) * ((a j : K) * σ c)) =
        pinnedX τ K (Pi.single j 1) c := by
    intro j hj c
    have e := hm (EPilot.pinnedX_single_mem_perpLevi hj c)
      (by
        rw [exactNormalAutGL_pinnedX_single_E7_E8 hτ]
        exact EPilot.pinnedX_single_mem_perpLevi hj _)
    rw [exactNormalAutGL_pinnedX_single_E7_E8 hτ] at e
    rw [← conj_pinnedX_of_mem_torusGroup hh (IsRoot.smul (isRoot_single _ _) w),
      ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single _ _), ← e]
    group
  have hw : ∀ j : Fin τ.rank, j ≠ highNode τ →
      w • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j 1 := fun j hj =>
    EPilot.eq_of_pinnedX_eq_pinnedX_of_pos (IsRoot.smul (isRoot_single _ _) w)
      (isRoot_single _ j) (by rw [height_single]; norm_num) one_ne_zero (hroot j hj 1)
  have hscal : ∀ j : Fin τ.rank, j ≠ highNode τ → ∀ c : K,
      torusRootChar h (Pi.single j 1) * ((a j : K) * σ c) = c := by
    intro j hj c
    have e := hroot j hj c
    rw [hw j hj] at e
    exact pinnedX_injective τ K _ e
  obtain ⟨j1, hj1⟩ : ∃ j : Fin τ.rank, j ≠ highNode τ := by
    rcases hτ with rfl | rfl <;> decide
  have hσ : ∀ c : K, σ c = c := by
    intro c
    have e1 := hscal _ hj1 1
    have ec := hscal _ hj1 c
    rw [map_one, mul_one] at e1
    calc σ c = (torusRootChar h (Pi.single j1 1) * (a j1 : K)) * σ c := by rw [e1, one_mul]
      _ = c := by rw [mul_assoc]; exact ec
  have hσ1 : σ = RingEquiv.refl K := RingEquiv.ext hσ
  subst hσ1
  have hTC : torusGroup τ K ≤ adjointGroup τ K :=
    (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
  obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hchar : ∀ j : Fin τ.rank,
      torusRootChar (rootDiagUnit τ l') (Pi.single j 1) = (l' j : K) := by
    intro j
    have e1 := conj_pinnedX_of_mem_torusGroup hh (isRoot_single τ j) 1
    rw [rootDiagUnit_conj_pinnedX l' (isRoot_single τ j), EPilot.rootChar_single_eq] at e1
    have e2 := pinnedX_injective τ K _ e1
    rw [mul_one, mul_one] at e2
    exact e2.symm
  have hb : ∀ j : Fin τ.rank, j ≠ highNode τ → (l' * a) j = 1 := by
    intro j hj
    have e := hscal j hj 1
    rw [hchar, RingEquiv.refl_apply, mul_one] at e
    exact Units.ext (by simpa using e)
  have hbd : l' * a = EPilot.highDiag τ ((l' * a) (highNode τ)) := by
    funext j
    by_cases hj : j = highNode τ
    · subst hj
      rw [EPilot.highDiag, Pi.mulSingle_eq_same]
    · rw [EPilot.highDiag, Pi.mulSingle_eq_of_ne hj, hb j hj]
  have hdaC : rootDiagUnit τ a ∈ adjointGroup τ K := by
    have e : rootDiagUnit τ a = (rootDiagUnit τ l')⁻¹ * rootDiagUnit τ (l' * a) := by
      rw [rootDiagUnit_mul, inv_mul_cancel_left]
    rw [e, hbd]
    exact mul_mem (inv_mem (hTC hh)) (EPilot.highRootSL2_le_adjointGroup
      (EPilot.rootDiagUnit_highDiag_mem_highRootSL2 hτ' _))
  have hβc : β = MulAut.conj (⟨(g : ModGL τ K) * rootDiagUnit τ a, mul_mem g.2 hdaC⟩ :
      adjointGroup τ K) := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL τ K) = x :=
      Units.ext (entrywise_id _)
    rw [hga x, MulAut.conj_apply, exactQ_E7_E8 K hτ, e1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_one, inv_one, mul_inv_rev]
    group
  refine ⟨_, hβc, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have e := hβ y hy
  rw [hβc, MulAut.conj_apply] at e
  calc y * _ = _ * y * _⁻¹ * _ := by rw [e]
    _ = _ := by group

theorem exists_eq_conj_of_forall_eq_zero_or_eq_one (hτ : τ = .E7 ∨ τ = .E8) [Finite K]
    (hK : ∀ c : K, c = 0 ∨ c = 1) (β : MulAut (adjointGroup τ K)) :
    ∃ g : adjointGroup τ K, β = MulAut.conj g := by
  have hunit : ∀ u : Kˣ, u = 1 := fun u => Units.ext ((hK u).resolve_left u.ne_zero)
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form τ (Or.inr hτ) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex β
  have ha : a = 1 := funext fun i => hunit (a i)
  have hσ : σ = RingEquiv.refl K := RingEquiv.ext fun c => by
    rcases hK c with rfl | rfl
    · rw [map_zero, RingEquiv.refl_apply]
    · rw [map_one, RingEquiv.refl_apply]
  subst ha hσ
  refine ⟨g, MulEquiv.ext fun x => Subtype.ext ?_⟩
  have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL τ K) = x :=
    Units.ext (entrywise_id _)
  rw [hga x, e1, rootDiagUnit_one, exactQ_E7_E8 K hτ, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_one, inv_one]

theorem exists_eq_conj_of_card_eq_two (hτ : τ = .E7 ∨ τ = .E8) [Finite K]
    (hK2 : Nat.card K = 2) (β : MulAut (adjointGroup τ K)) :
    ∃ g : adjointGroup τ K, β = MulAut.conj g := by
  have hunit : ∀ u : Kˣ, u = 1 := by
    have hc : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hc).1
    exact fun u => Subsingleton.elim u 1
  refine exists_eq_conj_of_forall_eq_zero_or_eq_one hτ (fun c => ?_) β
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr (congrArg Units.val (hunit (Units.mk0 c hc)))

theorem exists_eq_conj_of_fix_perpLevi (hτ : τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    (β : MulAut (adjointGroup τ K))
    (hβ : ∀ x ∈ (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K), β x = x) :
    ∃ g : adjointGroup τ K, β = MulAut.conj g ∧
      g ∈ centralizer (((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) :
        Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
  by_cases hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1
  · exact exists_eq_conj_of_fix_perpLevi_of_exists hτ hK β hβ
  · have hK' : ∀ c : K, c = 0 ∨ c = 1 := fun c => by
      by_cases h0 : c = 0
      · exact Or.inl h0
      · by_cases h1 : c = 1
        · exact Or.inr h1
        · exact absurd ⟨c, h0, h1⟩ hK
    obtain ⟨g, rfl⟩ := exists_eq_conj_of_forall_eq_zero_or_eq_one hτ hK' β
    refine ⟨g, rfl, mem_centralizer_iff.2 fun y hy => ?_⟩
    have := hβ y hy
    rw [MulAut.conj_apply] at this
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group

theorem eq_one_of_fix_perpLevi_of_center_eq_bot (hτ : τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    {X Y : Subgroup (adjointGroup τ K)}
    (hZ : center ((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K)) = ⊥)
    (hXc : centralizer (X : Set (adjointGroup τ K)) ≤
      Y ⊔ (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K))
    (hY : Y ≤ centralizer (((rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K) :
      Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)))
    (hYodd : Odd (Nat.card Y)) (β : MulAut (adjointGroup τ K)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ (rootSpan τ K (EPilot.perpRoots τ)).subgroupOf (adjointGroup τ K), β d = d)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  obtain ⟨g, rfl, hgD⟩ := exists_eq_conj_of_fix_perpLevi hτ β hβD
  have hgX : g ∈ centralizer (X : Set (adjointGroup τ K)) := mem_centralizer_iff.2 fun x hx => by
    have := hβX x hx
    rw [MulAut.conj_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  have hgn : g ^ 2 ^ n = 1 := by
    have hc : MulAut.conj (g ^ 2 ^ n) = 1 := by rw [map_pow, hβn]
    have hz : g ^ 2 ^ n ∈ center (adjointGroup τ K) := by
      rw [mem_center_iff]
      intro y
      have := congrArg (fun γ : MulAut _ => γ y) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 2 ^ n = g ^ 2 ^ n * y * (g ^ 2 ^ n)⁻¹ * g ^ 2 ^ n := by rw [this]
        _ = g ^ 2 ^ n * y := by group
    rw [center_adjointGroup_eq_bot] at hz
    exact hz
  rw [F4Pilot.eq_one_of_mem_sup_of_mem_centralizer hY hZ hYodd (hXc hgX) hgD hgn, map_one]

end Main

section E8

variable {K : Type} [Field K]


theorem exists_eq_conj_of_fix_e7Levi [Finite K] [CharP K 2] (β : MulAut (adjointGroup .E8 K))
    (hβ : ∀ x ∈ e7Levi K, β x = x) :
    ∃ g : adjointGroup .E8 K, β = MulAut.conj g ∧
      g ∈ centralizer (e7Levi K : Set (adjointGroup .E8 K)) :=
  exists_eq_conj_of_fix_perpLevi (Or.inr rfl) β hβ

theorem exists_eq_conj_E8_of_card_eq_two [Finite K] (hK2 : Nat.card K = 2)
    (β : MulAut (adjointGroup .E8 K)) : ∃ g : adjointGroup .E8 K, β = MulAut.conj g :=
  exists_eq_conj_of_card_eq_two (Or.inr rfl) hK2 β

theorem exists_eq_conj_mem_highRootSL2_of_fix_e7Levi [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (β : MulAut (adjointGroup .E8 K)) (hβ : ∀ x ∈ e7Levi K, β x = x) :
    ∃ g : adjointGroup .E8 K, β = MulAut.conj g ∧
      g ∈ (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K) := by
  obtain ⟨g, hg, hgD⟩ := exists_eq_conj_of_fix_e7Levi β hβ
  refine ⟨g, hg, ?_⟩
  rw [← EPilot.centralizer_perpLevi_subgroupOf (Or.inr (Or.inr rfl)) hq]
  exact hgD


theorem eq_one_of_fix_e7Levi [Finite K] [CharP K 2] {X Y : Subgroup (adjointGroup .E8 K)}
    (hXc : centralizer (X : Set (adjointGroup .E8 K)) ≤ Y ⊔ e7Levi K)
    (hY : Y ≤ centralizer (e7Levi K : Set (adjointGroup .E8 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut (adjointGroup .E8 K)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ e7Levi K, β d = d) (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 :=
  eq_one_of_fix_perpLevi_of_center_eq_bot (Or.inr rfl) center_e7Levi_eq_bot hXc hY hYodd β hβX hβD
    n hβn

end E8

end CFSG.SeitzReduction.E8Pilot
