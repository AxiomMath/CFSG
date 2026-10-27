module

public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.E6RootInvolutionNoInverted
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem E6_perm_perm : ∀ i : Fin 6, TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  intro i
  fin_cases i <;> rfl

theorem E6_perm_symm_eq : TwistTag.E6.perm.symm = TwistTag.E6.perm :=
  Equiv.ext fun i => by
    rw [Equiv.symm_apply_eq]
    exact (E6_perm_perm i).symm

theorem permLattice_permLattice_E6
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm v) = v := by
  have h := permLattice_symm_permLattice TwistTag.E6.perm v
  rwa [E6_perm_symm_eq] at h

theorem diagramMap_E6_inv :
    (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K :=
  inv_eq_of_mul_eq_one_right diagramMap_E6_mul_self

theorem mapsRootLines_diagramMap_conj
    {n : ModGL TwistTag.E6.tag K}
    {w : WeylGroup TwistTag.E6.tag} (h : MapsRootLines n w) :
    MapsRootLines (diagramMap TwistTag.E6 K * n * (diagramMap TwistTag.E6 K)⁻¹)
      (weylTwist TwistTag.E6 w) := by
  intro α hα
  obtain ⟨c, hc⟩ := h (permLattice TwistTag.E6.perm α) (hα.permLattice TwistTag.E6.cartan_perm)
  refine ⟨c, ?_⟩
  rw [diagramMap_E6_inv, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    diagramMap_rootVec _ _ α hα, hc, map_smul,
    diagramMap_rootVec _ _ _ (IsRoot.smul (hα.permLattice TwistTag.E6.cartan_perm) w),
    weylTwist_smul, E6_perm_symm_eq]

theorem weylQuotientHom_diagramMap_conj
    {n : ModGL TwistTag.E6.tag K}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag K) :
    weylQuotientHom TwistTag.E6.tag K
        ⟨_, diagramMap_conj_mem_monomialSubgroup (t := TwistTag.E6) hn⟩ =
      weylTwist TwistTag.E6 (weylQuotientHom TwistTag.E6.tag K ⟨n, hn⟩) :=
  weylQuotientHom_eq (mapsRootLines_diagramMap_conj (mapsRootLines_weylQuotientHom ⟨n, hn⟩))

theorem smul_permLattice_involutive
    {n : ModGL TwistTag.E6.tag K}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag K) (hnP : (n * diagramMap TwistTag.E6 K) ^ 2 = 1)
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    weylQuotientHom TwistTag.E6.tag K ⟨n, hn⟩ • permLattice TwistTag.E6.perm
      (weylQuotientHom TwistTag.E6.tag K ⟨n, hn⟩ • permLattice TwistTag.E6.perm v) = v := by
  set P := diagramMap TwistTag.E6 K with hP
  set w := weylQuotientHom TwistTag.E6.tag K ⟨n, hn⟩ with hw
  have hPN := diagramMap_conj_mem_monomialSubgroup (t := TwistTag.E6) hn
  have h1 : n * (P * n * P⁻¹) = 1 := by
    calc n * (P * n * P⁻¹) = (n * P) ^ 2 * (P * P)⁻¹ := by rw [sq]; group
      _ = 1 := by rw [hnP, hP, diagramMap_E6_mul_self, inv_one, one_mul]
  have h2 : w * weylTwist TwistTag.E6 w = 1 := by
    have e : (⟨n, hn⟩ * ⟨_, hPN⟩ : monomialSubgroup TwistTag.E6.tag K) = 1 := Subtype.ext h1
    have := congrArg (weylQuotientHom TwistTag.E6.tag K) e
    rwa [map_mul, map_one, weylQuotientHom_diagramMap_conj] at this
  rw [← weylTwist_smul_permLattice, ← mul_smul, h2, one_smul, permLattice_permLattice_E6]

@[expose] def invertedRoots
    (w : WeylGroup TwistTag.E6.tag) : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  {β | IsRoot TwistTag.E6.tag β ∧ w • permLattice TwistTag.E6.perm β = -β}

theorem invertedRoots_finite
    (w : WeylGroup TwistTag.E6.tag) : (invertedRoots w).Finite :=
  (finite_setOf_isRoot _).subset fun _ hβ => hβ.1

theorem invertedRoots_reflection_subset
    {w : WeylGroup TwistTag.E6.tag}
    (hinv : ∀ v, w • permLattice TwistTag.E6.perm (w • permLattice TwistTag.E6.perm v) = v)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ invertedRoots w) :
    invertedRoots (rootReflection β * w) ⊆ invertedRoots w \ {β} := by
  obtain ⟨hβr, hωβ⟩ := hβ
  set ω : (Fin TwistTag.E6.tag.rank → ℤ) → (Fin TwistTag.E6.tag.rank → ℤ) :=
    fun v => w • permLattice TwistTag.E6.perm v with hω
  have hiso : ∀ x y, iform (ω x) (ω y) = iform x y := fun x y => by
    simp only [hω]
    rw [iform_smul, iform_permLattice_E6]
  have hadj : ∀ x y, iform (ω x) y = iform x (ω y) := fun x y => by
    calc iform (ω x) y = iform (ω x) (ω (ω y)) := by rw [show ω (ω y) = y from hinv y]
      _ = iform x (ω y) := hiso x (ω y)
  have hneg : ∀ x y : Fin TwistTag.E6.tag.rank → ℤ, iform x (-y) = -iform x y := fun x y => by
    simp [iform, Finset.sum_neg_distrib]
  have hωβ' : ω β = -β := hωβ
  rintro γ ⟨hγ, hγeq⟩
  rw [mul_smul] at hγeq
  change rootReflection β • ω γ = -γ at hγeq
  have hsβ : ∀ x, iform (rootReflection β • x) β = -iform x β := fun x => by
    calc iform (rootReflection β • x) β =
          iform (rootReflection β • x) (rootReflection β • (rootReflection β • β)) := by
          rw [← mul_smul, rootReflection_mul_self hβr, one_smul]
      _ = -iform x β := by rw [iform_smul, rootReflection_smul_self hβr, hneg]
  have h0 : iform γ β = 0 := by
    have e1 := hsβ (ω γ)
    rw [hγeq, hadj, hωβ', hneg] at e1
    have e2 : iform (-γ) β = -iform γ β := by
      rw [iform_comm, hneg, iform_comm]
    rw [e2] at e1
    linarith
  have h0' : iform β (ω γ) = 0 := by
    rw [iform_comm, hadj, hωβ', hneg, h0, neg_zero]
  rw [rootReflection_smul_of_iform_eq_zero hβr h0'] at hγeq
  refine ⟨⟨hγ, hγeq⟩, fun hγβ => ?_⟩
  rw [Set.mem_singleton_iff] at hγβ
  subst hγβ
  have := iform_self_pos_of_isRoot hβr
  rw [h0] at this
  exact lt_irrefl 0 this

theorem E6_graph_monomial_involution_toral_conjugacy
    (k : Type) [Field k] [IsAlgClosed k]
    (hk : ringChar k ≠ 2) {n : ModGL TwistTag.E6.tag k}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag k) (hnP : (n * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    ∃ g ∈ adjointGroup TwistTag.E6.tag k, ∃ a : Fin TwistTag.E6.tag.rank → kˣ,
      g * (n * diagramMap TwistTag.E6 k) * g⁻¹ =
          rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 k ∧
        ∀ i, a i * a (TwistTag.E6.perm i) = 1 := by
  classical
  set P := diagramMap TwistTag.E6 k with hP
  have stepA : ∀ (m : ℕ) (n : ModGL TwistTag.E6.tag k)
      (hn : n ∈ monomialSubgroup TwistTag.E6.tag k),
      (n * P) ^ 2 = 1 → (invertedRoots (weylQuotientHom TwistTag.E6.tag k ⟨n, hn⟩)).ncard = m →
      ∃ g ∈ adjointGroup TwistTag.E6.tag k, ∃ n' : ModGL TwistTag.E6.tag k,
        ∃ hn' : n' ∈ monomialSubgroup TwistTag.E6.tag k,
          g * (n * P) * g⁻¹ = n' * P ∧ (n' * P) ^ 2 = 1 ∧
            invertedRoots (weylQuotientHom TwistTag.E6.tag k ⟨n', hn'⟩) = ∅ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn hnP hm
      by_cases hne : invertedRoots (weylQuotientHom TwistTag.E6.tag k ⟨n, hn⟩) = ∅
      · exact ⟨1, one_mem _, n, hn, by group, hnP, hne⟩
      obtain ⟨β, hβ⟩ := Set.nonempty_iff_ne_empty.2 hne
      obtain ⟨y, hyL, n₁, hn₁, hy, hπ₁⟩ :=
        E6_graph_inverted_root_SL2_rotation k hk hn hnP hβ.1 hβ.2
      have hyC : y ∈ adjointGroup TwistTag.E6.tag k :=
        (exceptional_Lang_root_rank_one_data TwistTag.E6.tag k β).2.2.2.2.2.1 hyL
      have hn₁P : (n₁ * P) ^ 2 = 1 := by
        rw [← hy, sq]
        calc y * (n * P) * y⁻¹ * (y * (n * P) * y⁻¹) = y * ((n * P) ^ 2) * y⁻¹ := by
              rw [sq]; group
          _ = 1 := by rw [hnP]; group
      have hsub := invertedRoots_reflection_subset (smul_permLattice_involutive hn hnP) hβ
      rw [← hπ₁] at hsub
      have hlt : (invertedRoots (weylQuotientHom TwistTag.E6.tag k ⟨n₁, hn₁⟩)).ncard < m := by
        rw [← hm]
        refine Set.ncard_lt_ncard ?_ (invertedRoots_finite _)
        refine ⟨hsub.trans Set.sdiff_subset, fun h => ?_⟩
        exact (hsub (h hβ)).2 rfl
      obtain ⟨g, hg, n', hn', hg', hn'P, hn'inv⟩ := ih _ hlt n₁ hn₁ hn₁P rfl
      refine ⟨g * y, mul_mem hg hyC, n', hn', ?_, hn'P, hn'inv⟩
      calc g * y * (n * P) * (g * y)⁻¹ = g * (y * (n * P) * y⁻¹) * g⁻¹ := by group
        _ = n' * P := by rw [hy, hg']
  obtain ⟨g₁, hg₁, n', hn', hg₁', hn'P, hn'inv⟩ := stepA _ n hn hnP rfl
  set w' := weylQuotientHom TwistTag.E6.tag k ⟨n', hn'⟩ with hw'
  obtain ⟨u, hu⟩ := E6_root_involution_without_inverted_roots w'
    (smul_permLattice_involutive hn' hn'P)
    (fun β hβ h => (Set.eq_empty_iff_forall_notMem.1 hn'inv) β ⟨hβ, h⟩)
  set z := canonicalRep (coxeterSystem TwistTag.E6.tag) k u with hz
  have hzC : z ∈ adjointGroup TwistTag.E6.tag k :=
    canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) k u
  have hzN : z ∈ monomialSubgroup TwistTag.E6.tag k := canonicalRep_mem_monomialSubgroup k u
  have hzπ : weylQuotientHom TwistTag.E6.tag k ⟨z, hzN⟩ = u :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep u)
  have hPz := diagramMap_conj_mem_monomialSubgroup (t := TwistTag.E6) (inv_mem hzN)
  set n'' := z * n' * (P * z⁻¹ * P⁻¹) with hn''
  have hn''N : n'' ∈ monomialSubgroup TwistTag.E6.tag k := mul_mem (mul_mem hzN hn') hPz
  have hn''P : z * (n' * P) * z⁻¹ = n'' * P := by
    rw [hn'']
    group
  have hπ'' : weylQuotientHom TwistTag.E6.tag k ⟨n'', hn''N⟩ =
      u * w' * weylTwist TwistTag.E6 u⁻¹ := by
    have e : (⟨n'', hn''N⟩ : monomialSubgroup TwistTag.E6.tag k) =
        ⟨z, hzN⟩ * ⟨n', hn'⟩ * ⟨_, hPz⟩ := rfl
    rw [e, map_mul, map_mul, weylQuotientHom_diagramMap_conj (inv_mem hzN)]
    have e2 : (⟨z⁻¹, inv_mem hzN⟩ : monomialSubgroup TwistTag.E6.tag k) = (⟨z, hzN⟩)⁻¹ := rfl
    rw [e2, map_inv, hzπ]
  have hπ1 : weylQuotientHom TwistTag.E6.tag k ⟨n'', hn''N⟩ = 1 := by
    rw [hπ'']
    refine eq_of_smul_eq_smul (α := Fin TwistTag.E6.tag.rank → ℤ) fun x => ?_
    rw [one_smul]
    have hx := hu (permLattice TwistTag.E6.perm x)
    rw [permLattice_permLattice_E6] at hx
    rw [← permLattice_permLattice_E6 x, mul_smul, mul_smul, weylTwist_smul_permLattice,
      permLattice_permLattice_E6]
    exact hx
  obtain ⟨w₀, h, hh, he⟩ := monomialSubgroup_le_torusWeylCosets hn''N
  have hw₀ : weylQuotientHom TwistTag.E6.tag k ⟨n'', hn''N⟩ = w₀ := weylQuotientHom_eq (by
    change MapsRootLines n'' w₀
    rw [he]
    simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w₀))
  rw [hπ1] at hw₀
  rw [← hw₀, canonicalRep_one, mul_one] at he
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  refine ⟨z * g₁, mul_mem hzC hg₁, a, ?_, fun i => ?_⟩
  · calc z * g₁ * (n * P) * (z * g₁)⁻¹ = z * (g₁ * (n * P) * g₁⁻¹) * z⁻¹ := by group
      _ = rootDiagUnit TwistTag.E6.tag a * P := by rw [hg₁', hn''P, ← he]
  ·
    have hsq : (rootDiagUnit TwistTag.E6.tag a * P) ^ 2 = 1 := by
      have e : rootDiagUnit TwistTag.E6.tag a * P = (z * g₁) * (n * P) * (z * g₁)⁻¹ := by
        calc rootDiagUnit TwistTag.E6.tag a * P = z * (g₁ * (n * P) * g₁⁻¹) * z⁻¹ := by
              rw [hg₁', hn''P, ← he]
          _ = _ := by group
      rw [e, sq]
      calc z * g₁ * (n * P) * (z * g₁)⁻¹ * (z * g₁ * (n * P) * (z * g₁)⁻¹) =
            (z * g₁) * (n * P) ^ 2 * (z * g₁)⁻¹ := by rw [sq]; group
        _ = 1 := by rw [hnP]; group
    have e2 : (rootDiagUnit TwistTag.E6.tag a * P) ^ 2 =
        rootDiagUnit TwistTag.E6.tag (a * fun j => a (TwistTag.E6.perm.symm j)) := by
      calc (rootDiagUnit TwistTag.E6.tag a * P) ^ 2 =
            rootDiagUnit TwistTag.E6.tag a * (P * rootDiagUnit TwistTag.E6.tag a) * P := by
            rw [sq]; group
        _ = rootDiagUnit TwistTag.E6.tag a *
            (rootDiagUnit TwistTag.E6.tag (fun j => a (TwistTag.E6.perm.symm j)) * P) * P := by
            rw [hP, diagramMap_mul_rootDiagUnit]
        _ = rootDiagUnit TwistTag.E6.tag a *
            rootDiagUnit TwistTag.E6.tag (fun j => a (TwistTag.E6.perm.symm j)) * (P * P) := by
            group
        _ = _ := by rw [hP, diagramMap_E6_mul_self, mul_one, ← rootDiagUnit_mul]
    rw [e2, ← rootDiagUnit_one] at hsq
    have := congrFun (rootDiagUnit_injective hsq) i
    rw [E6_perm_symm_eq] at this
    exact this

end CFSG.LieType.Chevalley
