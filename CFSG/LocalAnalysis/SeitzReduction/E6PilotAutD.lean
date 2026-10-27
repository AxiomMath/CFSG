module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Levi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Bruhat

variable {τ : Tag} {K : Type} [Field K]


theorem twisted_torus_bruhat {w : WeylGroup τ} {h u v : ModGL τ K} (hh : h ∈ torusGroup τ K)
    (hu : u ∈ posUnipotent τ K) (hv : v ∈ rootSpan τ K (inversionSet w))
    {a b : Fin τ.rank → Kˣ} (ha : rootDiagUnit τ a ∈ torusGroup τ K)
    (hb : rootDiagUnit τ b ∈ torusGroup τ K)
    (hconj : h * u * canonicalRep (coxeterSystem τ) K w * v * rootDiagUnit τ b =
      rootDiagUnit τ a * (h * u * canonicalRep (coxeterSystem τ) K w * v)) :
    rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u ∧
      rootDiagUnit τ b * v * (rootDiagUnit τ b)⁻¹ = v ∧
      rootDiagUnit τ a = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  set n := canonicalRep (coxeterSystem τ) K w with hn
  set da := rootDiagUnit τ a with hda
  set db := rootDiagUnit τ b with hdb
  set s := n * db * n⁻¹ with hs
  have hsT : s ∈ torusGroup τ K :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := K) w) db).1 hb
  set t := da * s⁻¹ with ht
  have htT : t ∈ torusGroup τ K := mul_mem ha (inv_mem hsT)
  have hdu : da * u * da⁻¹ ∈ posUnipotent τ K := by
    have := ((chevalley_root_character_and_field_conjugation τ K).2.2.2.1 a).2.1
    rw [← this]
    exact ⟨u, hu, rfl⟩
  have hdv : db * v * db⁻¹ ∈ rootSpan τ K (inversionSet w) := by
    have : (rootSpan τ K (inversionSet w)).map (MulAut.conj db).toMonoidHom =
        rootSpan τ K (inversionSet w) :=
      map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup b hα.1
    rw [← this]
    exact ⟨v, hv, rfl⟩
  have hu' : t⁻¹ * (da * u * da⁻¹) * t ∈ posUnipotent τ K := by
    have hN := hTB.2.2.1 (inv_mem htT)
    have := (Subgroup.mem_normalizer_iff.1 hN (da * u * da⁻¹)).1 hdu
    simpa using this
  have hg' : da * (h * u * n * v) * db⁻¹ = h * u * n * v := by
    rw [← hconj, mul_inv_cancel_right]
  have heq : h * t * (t⁻¹ * (da * u * da⁻¹) * t) * n * (db * v * db⁻¹) = h * u * n * v := by
    calc h * t * (t⁻¹ * (da * u * da⁻¹) * t) * n * (db * v * db⁻¹) =
        (h * da) * u * n * v * db⁻¹ := by
          simp only [ht, hs]
          group
      _ = da * (h * u * n * v) * db⁻¹ := by
          have hcomm : da * h = h * da := rootDiagUnit_mul_comm_of_mem_torusGroup a hh
          rw [← hcomm]
          group
      _ = h * u * n * v := hg'
  obtain ⟨-, h1, h2, h3⟩ := (Chevalley_toral_centralizer_Bruhat_factors τ K a).2.1 w w (h * t) h
    _ u _ v (mul_mem hh htT) hh hu' hu hdv hv heq
  have ht1 : t = 1 := by rwa [mul_eq_left] at h1
  refine ⟨?_, h3, ?_⟩
  · rw [ht1, inv_one, one_mul, mul_one] at h2
    exact h2
  · rw [ht, mul_inv_eq_one] at ht1
    exact ht1

end Bruhat

section Perm

theorem exactPerm_E6_eq_highNode_iff : ∀ (ε : Fin (exactE .E6)) (j : Fin Tag.E6.rank),
    exactPerm .E6 ε j = highNode .E6 ↔ j = highNode .E6 := by
  decide

theorem exactPerm_E6_involutive : ∀ (ε : Fin (exactE .E6)) (j : Fin Tag.E6.rank),
    exactPerm .E6 ε (exactPerm .E6 ε j) = j := by
  decide

theorem iform_single_exactPerm_E6 : ∀ (ε : Fin (exactE .E6)) (i j : Fin Tag.E6.rank),
    iform (Pi.single (exactPerm .E6 ε i) 1 : Fin Tag.E6.rank → ℤ)
        (Pi.single (exactPerm .E6 ε j) 1) =
      iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) := by
  decide

theorem eq_zero_of_exactPerm_E6_zero : ∀ ε : Fin (exactE .E6),
    exactPerm .E6 ε (⟨0, by decide⟩ : Fin Tag.E6.rank) = ⟨0, by decide⟩ → ε = ⟨0, by decide⟩ := by
  decide

theorem exactPerm_E6_zero_apply (j : Fin Tag.E6.rank) :
    exactPerm .E6 ((⟨0, by decide⟩ : Fin (exactE .E6)) : ℕ) j = j :=
  rfl

theorem eq_of_single_eq_single_E6 {i j : Fin Tag.E6.rank}
    (h : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1) : i = j := by
  by_contra hij
  have := congrFun h i
  simp [hij] at this

end Perm

section Actors

variable {K : Type} [Field K]

theorem exactQ_E6_conj_torusElt (ε : Fin (exactE .E6)) (j : Fin Tag.E6.rank) (μ : Kˣ) :
    exactQ .E6 K ε * torusElt .E6 K j μ * (exactQ .E6 K ε)⁻¹ =
      torusElt .E6 K (exactPerm .E6 ε j) μ := by
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with h | h
  · rw [h, exactQ_zero, one_mul, inv_one, mul_one]
    rfl
  · have hQ : exactQ .E6 K ε = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) := by
      simp only [exactQ, h, pow_one]
      rfl
    have hP : exactPerm .E6 ε = TwistTag.E6.perm := by
      simp only [exactPerm, h, pow_one]
      rfl
    rw [hQ, hP, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
    have e := diagramMap_mul_rootDiagUnit (t := TwistTag.E6) (K := K)
      (fun k => μ ^ Tag.E6.cartan j k)
    have e' : diagramMap TwistTag.E6 K *
        rootDiagUnit TwistTag.E6.tag (fun k => μ ^ Tag.E6.cartan j k) *
          (diagramMap TwistTag.E6 K)⁻¹ =
        rootDiagUnit TwistTag.E6.tag (fun k => μ ^ Tag.E6.cartan (TwistTag.E6.perm j) k) := by
      rw [e, mul_inv_cancel_right]
      congr 1
      funext k
      have hc := TwistTag.cartan_perm TwistTag.E6 j (TwistTag.E6.perm.symm k)
      rw [Equiv.apply_symm_apply] at hc
      exact congrArg (fun n : ℤ => μ ^ n) hc.symm
    exact e'

theorem exactNormalAutGL_E6_torusElt (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K)
    (ε : Fin (exactE .E6)) (j : Fin Tag.E6.rank) (μ : Kˣ) :
    exactNormalAutGL .E6 K a σ ε (torusElt .E6 K j μ) =
      torusElt .E6 K (exactPerm .E6 ε j) (Units.map σ.toRingHom.toMonoidHom μ) := by
  have h1 : Units.map (entrywiseHom σ.toRingHom) (torusElt .E6 K j μ) =
      torusElt .E6 K j (Units.map σ.toRingHom.toMonoidHom μ) := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      units_map_entrywiseHom_rootDiagUnit_ringEquiv]
    congr 1
    funext k
    rw [map_zpow]
  rw [exactNormalAutGL_apply, h1]
  have e : rootDiagUnit .E6 a * exactQ .E6 K ε *
      torusElt .E6 K j (Units.map σ.toRingHom.toMonoidHom μ) * (exactQ .E6 K ε)⁻¹ *
        (rootDiagUnit .E6 a)⁻¹ = rootDiagUnit .E6 a * (exactQ .E6 K ε *
      torusElt .E6 K j (Units.map σ.toRingHom.toMonoidHom μ) * (exactQ .E6 K ε)⁻¹) *
        (rootDiagUnit .E6 a)⁻¹ := by
    group
  rw [e, exactQ_E6_conj_torusElt]
  exact conj_rootDiagUnit_of_mem_torusGroup a (torusElt_mem_torusGroup _ _)


theorem exactNormalAutGL_E6_pinnedX_single (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K)
    (ε : Fin (exactE .E6)) (j : Fin Tag.E6.rank) (c : K) :
    exactNormalAutGL .E6 K a σ ε (pinnedX .E6 K (Pi.single j 1) c) =
      pinnedX .E6 K (Pi.single (exactPerm .E6 ε j) 1) ((a (exactPerm .E6 ε j) : K) * σ c) := by
  rw [pinnedX_single, pinnedX_single, exactNormalAutGL_xUnit]

end Actors

section Main

variable {K : Type} [Field K]


theorem exists_eq_conj_of_fix_a5Levi_of_exists [Finite K] [CharP K 2]
    (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) (β : MulAut (adjointGroup .E6 K))
    (hβ : ∀ x ∈ a5Levi K, β x = x) :
    ∃ g : adjointGroup .E6 K, β = MulAut.conj g ∧
      g ∈ centralizer (a5Levi K : Set (adjointGroup .E6 K)) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  obtain ⟨l, hl1⟩ : ∃ l : Kˣ, l ≠ 1 := by
    obtain ⟨c0, hc0, hc1⟩ := hK
    exact ⟨Units.mk0 c0 hc0, fun h => hc1 (by simpa using congrArg Units.val h)⟩
  have hr := isRoot_highRoot Tag.E6
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex β
  have hβψ : ∀ x : adjointGroup .E6 K, (β x : ModGL .E6 K) =
      (g : ModGL .E6 K) * exactNormalAutGL .E6 K a σ ε (x : ModGL .E6 K) *
        (g : ModGL .E6 K)⁻¹ := by
    intro x
    rw [hga x, exactNormalAutGL_apply]
    simp only [mul_assoc]
  have hfix : ∀ {x : ModGL .E6 K}, x ∈ rootSpan .E6 K (EPilot.perpRoots .E6) →
      (g : ModGL .E6 K) * exactNormalAutGL .E6 K a σ ε x * (g : ModGL .E6 K)⁻¹ = x := by
    intro x hx
    have hxC : x ∈ adjointGroup .E6 K := EPilot.rootSpan_le_adjointGroup' _ hx
    have e := congrArg Subtype.val (hβ ⟨x, hxC⟩ (mem_a5Levi_iff.2 hx))
    rw [hβψ] at e
    exact e
  have hg1 : (g : ModGL .E6 K) ∈ toralCentralizer .E6 K 1 := by
    refine mem_toralCentralizer.2 ⟨g.2, ?_⟩
    rw [rootDiagUnit_one, one_mul, inv_one, mul_one]
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E6 K 1).1 g hg1
  have huU : u ∈ posUnipotent .E6 K := rootSpan_mono Set.inter_subset_right hu
  have hvI : v ∈ rootSpan .E6 K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  obtain ⟨σl, hσl⟩ : ∃ σl : Kˣ, σl = Units.map σ.toRingHom.toMonoidHom l := ⟨_, rfl⟩
  have hσl1 : σl ≠ 1 := by
    intro h1
    apply hl1
    refine Units.map_injective (f := σ.toRingHom.toMonoidHom) σ.injective ?_
    rw [← hσl, h1, map_one]
  have htor : ∀ j : Fin Tag.E6.rank, j ≠ highNode .E6 →
      rootDiagUnit .E6 (fun k => l ^ Tag.E6.cartan j k) * u *
          (rootDiagUnit .E6 (fun k => l ^ Tag.E6.cartan j k))⁻¹ = u ∧
        rootDiagUnit .E6 (fun k => σl ^ Tag.E6.cartan (exactPerm .E6 ε j) k) * v *
          (rootDiagUnit .E6 (fun k => σl ^ Tag.E6.cartan (exactPerm .E6 ε j) k))⁻¹ = v := by
    intro j hj
    have hx := hfix (EPilot.torusElt_mem_rootSpan_perpRoots hj l)
    rw [exactNormalAutGL_E6_torusElt, ← hσl, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      hgdec] at hx
    have hconj : h * u * canonicalRep (coxeterSystem Tag.E6) K w * v *
          rootDiagUnit .E6 (fun k => σl ^ Tag.E6.cartan (exactPerm .E6 ε j) k) =
        rootDiagUnit .E6 (fun k => l ^ Tag.E6.cartan j k) *
          (h * u * canonicalRep (coxeterSystem Tag.E6) K w * v) := by
      rw [← hx]
      group
    obtain ⟨h1, h2, -⟩ := twisted_torus_bruhat hh huU hvI
      (by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _)
      (by rw [← torusElt_eq_rootDiagUnit]; exact torusElt_mem_torusGroup _ _) hconj
    exact ⟨h1, h2⟩
  have hcomm : ∀ {t x : ModGL .E6 K}, t * x * t⁻¹ = x →
      x ∈ centralizer ({t} : Set (ModGL .E6 K)) := by
    intro t x htx
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mul_inv_eq_iff_eq_mul.1 htx
  have hposcl : ∀ α ∈ {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧ 0 < height α},
      ∀ β ∈ {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧ 0 < height α}, ∀ m n : ℕ, 1 ≤ m →
        1 ≤ n → IsRoot .E6 (m • α + n • β) →
          m • α + n • β ∈ {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧ 0 < height α} := by
    intro α hα β hβ m n hm hn hmn
    refine ⟨hmn, ?_⟩
    rw [height_nsmul_add_nsmul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith [hα.2, hβ.2]
  have hur : u ∈ rootSubgroup .E6 K (highRoot .E6) :=
    EPilot.mem_rootSubgroup_highRoot_of_forall hτ hl1 (fun α hα => hα) hposcl huU
      fun j hj => hcomm (htor j hj).1
  have hvr : v ∈ rootSubgroup .E6 K (highRoot .E6) := by
    refine EPilot.mem_rootSubgroup_highRoot_of_forall hτ hσl1
      (fun α hα => inversionSet_pos hα) (inversionSet_closed w) hvI fun k hk => ?_
    have hk' : exactPerm .E6 ε k ≠ highNode .E6 := fun e =>
      hk ((exactPerm_E6_eq_highNode_iff ε k).1 e)
    have := (htor (exactPerm .E6 ε k) hk').2
    rw [exactPerm_E6_involutive] at this
    exact hcomm this
  have hJD := EPilot.highRootSL2_le_centralizer_perpLevi (K := K) hτ
  have hJ : ∀ {x : ModGL .E6 K}, x ∈ rootSubgroup .E6 K (highRoot .E6) →
      x ∈ EPilot.highRootSL2 .E6 K := fun hx => Subgroup.mem_sup_left hx
  have hu' : h * u * h⁻¹ ∈ rootSubgroup .E6 K (highRoot .E6) :=
    (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup hr hh) u).1 hur
  have hm : ∀ {x : ModGL .E6 K}, x ∈ rootSpan .E6 K (EPilot.perpRoots .E6) →
      exactNormalAutGL .E6 K a σ ε x ∈ rootSpan .E6 K (EPilot.perpRoots .E6) →
      (h * canonicalRep (coxeterSystem Tag.E6) K w) * exactNormalAutGL .E6 K a σ ε x *
        (h * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ = x := by
    intro x hx hψx
    have e := hfix hx
    rw [hgdec] at e
    have hvc : v * exactNormalAutGL .E6 K a σ ε x * v⁻¹ = exactNormalAutGL .E6 K a σ ε x := by
      rw [← Subgroup.mem_centralizer_iff.1 (hJD (hJ hvr)) _ hψx, mul_inv_cancel_right]
    have hkc : (h * u * h⁻¹)⁻¹ * x * (h * u * h⁻¹) = x := by
      rw [mul_assoc, Subgroup.mem_centralizer_iff.1 (hJD (hJ hu')) _ hx, inv_mul_cancel_left]
    calc (h * canonicalRep (coxeterSystem Tag.E6) K w) * exactNormalAutGL .E6 K a σ ε x *
          (h * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ =
        (h * canonicalRep (coxeterSystem Tag.E6) K w) *
          (v * exactNormalAutGL .E6 K a σ ε x * v⁻¹) *
            (h * canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ := by rw [hvc]
      _ = (h * u * h⁻¹)⁻¹ * (h * u * canonicalRep (coxeterSystem Tag.E6) K w * v *
          exactNormalAutGL .E6 K a σ ε x *
            (h * u * canonicalRep (coxeterSystem Tag.E6) K w * v)⁻¹) * (h * u * h⁻¹) := by
          group
      _ = (h * u * h⁻¹)⁻¹ * x * (h * u * h⁻¹) := by rw [e]
      _ = x := hkc
  have hroot : ∀ j : Fin Tag.E6.rank, j ≠ highNode .E6 → ∀ c : K,
      pinnedX .E6 K (w • (Pi.single (exactPerm .E6 ε j) 1 : Fin Tag.E6.rank → ℤ))
          (torusRootChar h (w • (Pi.single (exactPerm .E6 ε j) 1 : Fin Tag.E6.rank → ℤ)) *
            ((a (exactPerm .E6 ε j) : K) * σ c)) =
        pinnedX .E6 K (Pi.single j 1) c := by
    intro j hj c
    have hj' : exactPerm .E6 ε j ≠ highNode .E6 := fun e =>
      hj ((exactPerm_E6_eq_highNode_iff ε j).1 e)
    have e := hm (EPilot.pinnedX_single_mem_perpLevi hj c)
      (by
        rw [exactNormalAutGL_E6_pinnedX_single]
        exact EPilot.pinnedX_single_mem_perpLevi hj' _)
    rw [exactNormalAutGL_E6_pinnedX_single] at e
    rw [← conj_pinnedX_of_mem_torusGroup hh (IsRoot.smul (isRoot_single _ _) w),
      ← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single _ _), ← e]
    group
  have hw : ∀ j : Fin Tag.E6.rank, j ≠ highNode .E6 →
      w • (Pi.single (exactPerm .E6 ε j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := fun j hj =>
    EPilot.eq_of_pinnedX_eq_pinnedX_of_pos (IsRoot.smul (isRoot_single _ _) w)
      (isRoot_single _ j) (by rw [height_single]; norm_num) one_ne_zero (hroot j hj 1)
  have hscal : ∀ j : Fin Tag.E6.rank, j ≠ highNode .E6 → ∀ c : K,
      torusRootChar h (Pi.single j 1) * ((a (exactPerm .E6 ε j) : K) * σ c) = c := by
    intro j hj c
    have e := hroot j hj c
    rw [hw j hj] at e
    exact pinnedX_injective .E6 K _ e
  have j1 : (⟨0, by decide⟩ : Fin Tag.E6.rank) ≠ highNode .E6 := by decide
  have hσ : ∀ c : K, σ c = c := by
    intro c
    have e1 := hscal _ j1 1
    have ec := hscal _ j1 c
    rw [map_one, mul_one] at e1
    calc σ c = (torusRootChar h (Pi.single ⟨0, by decide⟩ 1) *
          (a (exactPerm .E6 ε ⟨0, by decide⟩) : K)) * σ c := by rw [e1, one_mul]
      _ = c := by rw [mul_assoc]; exact ec
  have hj0 : exactPerm .E6 ε (highNode .E6) = highNode .E6 :=
    (exactPerm_E6_eq_highNode_iff ε (highNode .E6)).2 rfl
  have hw0 := EPilot.eq_single_or_sub_highRoot_of_iform_eq hτ
    (IsRoot.smul (isRoot_single Tag.E6 (highNode .E6)) w) fun j hj => by
      have e := iform_single_exactPerm_E6 ε (highNode .E6) (exactPerm .E6 ε j)
      rw [hj0, exactPerm_E6_involutive] at e
      calc iform (w • (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ)) (Pi.single j 1) =
          iform (w • (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ))
            (w • (Pi.single (exactPerm .E6 ε j) 1 : Fin Tag.E6.rank → ℤ)) := by rw [hw j hj]
        _ = iform (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ)
            (Pi.single (exactPerm .E6 ε j) 1) := iform_smul w _ _
        _ = iform (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) := e.symm
  have hwk : ∀ k : Fin Tag.E6.rank, k ≠ highNode .E6 →
      w • (Pi.single k 1 : Fin Tag.E6.rank → ℤ) = Pi.single (exactPerm .E6 ε k) 1 := by
    intro k hk
    have hk' : exactPerm .E6 ε k ≠ highNode .E6 := fun e =>
      hk ((exactPerm_E6_eq_highNode_iff ε k).1 e)
    have := hw (exactPerm .E6 ε k) hk'
    rwa [exactPerm_E6_involutive] at this
  have hπ : ∀ j : Fin Tag.E6.rank, j ≠ highNode .E6 → exactPerm .E6 ε j = j := by
    rcases hw0 with h0 | h0
    ·
      have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
        by_cases hi : i = highNode .E6
        · subst hi
          rw [h0, height_single]
          norm_num
        · rw [hwk i hi, height_single]
          norm_num
      intro j hj
      have e := hw j hj
      rw [hw1, one_smul] at e
      exact eq_of_single_eq_single_E6 e
    ·
      obtain ⟨v', i, hv'⟩ := isRoot_iff_exists_smul_single.1 hr
      have hsx := EPilot.smul_conj_simple_eq hτ hv'
      have hsw : (v' * simple Tag.E6 i * v'⁻¹) * w = 1 := eq_one_of_forall_height_pos fun k => by
        by_cases hk : k = highNode .E6
        · subst hk
          rw [mul_smul, h0, hsx]
          have e : (Pi.single (highNode .E6) 1 - highRoot .E6 : Fin Tag.E6.rank → ℤ) -
              (Pi.single (highNode .E6) 1 - highRoot .E6 : Fin Tag.E6.rank → ℤ) (highNode .E6) •
                highRoot .E6 = Pi.single (highNode .E6) 1 := by
            rw [Pi.sub_apply, Pi.single_eq_same, EPilot.highRoot_highNode hτ]
            ext k
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [e, height_single]
          norm_num
        · have hk' : exactPerm .E6 ε k ≠ highNode .E6 := fun e =>
            hk ((exactPerm_E6_eq_highNode_iff ε k).1 e)
          rw [mul_smul, hwk k hk, hsx, Pi.single_eq_of_ne (Ne.symm hk'), zero_smul, sub_zero,
            height_single]
          norm_num
      intro j hj
      have e : ((v' * simple Tag.E6 i * v'⁻¹) * w) •
          (Pi.single (exactPerm .E6 ε j) 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
        rw [mul_smul, hw j hj, hsx, Pi.single_eq_of_ne (Ne.symm hj), zero_smul, sub_zero]
      rw [hsw, one_smul] at e
      exact eq_of_single_eq_single_E6 e
  have hε0 : ε = ⟨0, by decide⟩ := eq_zero_of_exactPerm_E6_zero ε (hπ _ j1)
  subst hε0
  have hσ1 : σ = RingEquiv.refl K := RingEquiv.ext hσ
  subst hσ1
  have hTC : torusGroup Tag.E6 K ≤ adjointGroup Tag.E6 K :=
    (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
  obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hchar : ∀ j : Fin Tag.E6.rank,
      torusRootChar (rootDiagUnit .E6 l') (Pi.single j 1) = (l' j : K) := by
    intro j
    have e1 := conj_pinnedX_of_mem_torusGroup hh (isRoot_single Tag.E6 j) 1
    rw [rootDiagUnit_conj_pinnedX l' (isRoot_single Tag.E6 j), EPilot.rootChar_single_eq] at e1
    have e2 := pinnedX_injective .E6 K _ e1
    rw [mul_one, mul_one] at e2
    exact e2.symm
  have hb : ∀ j : Fin Tag.E6.rank, j ≠ highNode .E6 → (l' * a) j = 1 := by
    intro j hj
    have e := hscal j hj 1
    rw [exactPerm_E6_zero_apply, hchar, RingEquiv.refl_apply, mul_one] at e
    exact Units.ext (by simpa using e)
  have hbd : l' * a = EPilot.highDiag .E6 ((l' * a) (highNode .E6)) := by
    funext j
    by_cases hj : j = highNode .E6
    · subst hj
      rw [EPilot.highDiag, Pi.mulSingle_eq_same]
    · rw [EPilot.highDiag, Pi.mulSingle_eq_of_ne hj, hb j hj]
  have hdaC : rootDiagUnit .E6 a ∈ adjointGroup .E6 K := by
    have e : rootDiagUnit .E6 a = (rootDiagUnit .E6 l')⁻¹ * rootDiagUnit .E6 (l' * a) := by
      rw [rootDiagUnit_mul, inv_mul_cancel_left]
    rw [e, hbd]
    exact mul_mem (inv_mem (hTC hh)) (EPilot.highRootSL2_le_adjointGroup
      (EPilot.rootDiagUnit_highDiag_mem_highRootSL2 hτ _))
  have hβc : β = MulAut.conj (⟨(g : ModGL .E6 K) * rootDiagUnit .E6 a, mul_mem g.2 hdaC⟩ :
      adjointGroup .E6 K) := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL .E6 K) = x :=
      Units.ext (entrywise_id _)
    have hQ0 : exactQ .E6 K ((⟨0, by decide⟩ : Fin (exactE .E6)) : ℕ) = 1 := exactQ_zero _ _
    rw [hga x, MulAut.conj_apply, hQ0, e1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_one, inv_one, mul_inv_rev]
    group
  refine ⟨_, hβc, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have e := hβ y hy
  rw [hβc, MulAut.conj_apply] at e
  calc y * _ = _ * y * _⁻¹ * _ := by rw [e]
    _ = _ := by group

theorem exists_eq_conj_of_fix_a5Levi [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (β : MulAut (adjointGroup .E6 K)) (hβ : ∀ x ∈ a5Levi K, β x = x) :
    ∃ g : adjointGroup .E6 K, β = MulAut.conj g ∧
      g ∈ centralizer (a5Levi K : Set (adjointGroup .E6 K)) :=
  exists_eq_conj_of_fix_a5Levi_of_exists (EPilot.exists_ne_zero_ne_one_of_four_le_card hq) β hβ

theorem eq_one_of_fix_a5Levi_of_four_le [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    {X Y : Subgroup (adjointGroup .E6 K)}
    (hXc : centralizer (X : Set (adjointGroup .E6 K)) ≤ Y ⊔ a5Levi K)
    (hY : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut (adjointGroup .E6 K)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ a5Levi K, β d = d) (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  obtain ⟨g, rfl, hgD⟩ := exists_eq_conj_of_fix_a5Levi hq β hβD
  have hgX : g ∈ centralizer (X : Set (adjointGroup .E6 K)) := mem_centralizer_iff.2 fun x hx => by
    have := hβX x hx
    rw [MulAut.conj_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  have hgn : g ^ 2 ^ n = 1 := by
    have hc : MulAut.conj (g ^ 2 ^ n) = 1 := by rw [map_pow, hβn]
    have hz : g ^ 2 ^ n ∈ center (adjointGroup .E6 K) := by
      rw [mem_center_iff]
      intro y
      have := congrArg (fun γ : MulAut _ => γ y) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 2 ^ n = g ^ 2 ^ n * y * (g ^ 2 ^ n)⁻¹ * g ^ 2 ^ n := by rw [this]
        _ = g ^ 2 ^ n * y := by group
    rw [center_adjointGroup_eq_bot] at hz
    exact hz
  rw [F4Pilot.eq_one_of_mem_sup_of_mem_centralizer hY center_a5Levi_eq_bot hYodd (hXc hgX) hgD
    hgn, map_one]

theorem eq_one_of_fix_a5Levi {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {X Y : Subgroup (adjointGroup .E6 K)}
    (hXc : centralizer (X : Set (adjointGroup .E6 K)) ≤ Y ⊔ a5Levi K)
    (hY : Y ≤ centralizer (a5Levi K : Set (adjointGroup .E6 K))) (hYodd : Odd (Nat.card Y))
    (β : MulAut (adjointGroup .E6 K)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ a5Levi K, β d = d) (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact eq_one_of_fix_a5Levi_of_four_le hq hXc hY hYodd β hβX hβD n hβn

end Main

end CFSG.SeitzReduction.E6Pilot
