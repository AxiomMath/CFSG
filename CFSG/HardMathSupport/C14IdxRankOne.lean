module

public import CFSG.HardMathSupport.C14IdxCorootConj
public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)

private theorem map_rootReflection_smul
    {τ : Tag}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    θ (rootReflection β • v) = rootReflection (θ β) • θ v := by
  have hcor : corootPair (θ β) (θ v) = corootPair β v := by
    rw [corootPair, corootPair, hθ β v, hθ β β]
  rw [rootReflection_smul hβ, rootReflection_smul (hθΦ β hβ), hcor]
  rw [map_sub, map_zsmul]

private theorem map_reflectionWordProd_smul
    {τ : Tag}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    {l : List (Fin τ.rank → ℤ)} (hl : ∀ β ∈ l, IsRoot τ β) (v : Fin τ.rank → ℤ) :
    θ (reflectionWordProd l • v) = reflectionWordProd (l.map θ) • θ v := by
  induction l generalizing v with
  | nil => rfl
  | cons β l ih =>
    rw [reflectionWordProd_cons, mul_smul, map_rootReflection_smul hθ hθΦ
      (hl β List.mem_cons_self), ih (fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)),
      List.map_cons, reflectionWordProd_cons, mul_smul]

private theorem reflectionWordProd_map_eq_of_mem
    {τ : Tag} {O : Finset (Fin τ.rank → ℤ)}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hOθ : ∀ β ∈ O, θ β ∈ O)
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hOroot : ∀ β ∈ O, IsRoot τ β)
    (hOorth : ∀ β ∈ O, ∀ γ ∈ O, β ≠ γ → iform β γ = 0) :
    reflectionWordProd (O.toList.map θ) = reflectionWordProd O.toList := by
  classical
  have himage : O.image θ = O := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro γ hγ
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hγ
      exact hOθ β hβ
    · rw [Finset.card_image_of_injective O θ.injective]
  have hnd₁ : (O.toList.map θ).Nodup :=
    List.Nodup.map θ.injective (Finset.nodup_toList O)
  have hnd₂ : O.toList.Nodup := Finset.nodup_toList O
  have hmem : ∀ x, x ∈ O.toList.map θ ↔ x ∈ O.toList := by
    intro x
    constructor
    · intro hx
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact Finset.mem_toList.2 (hOθ β (Finset.mem_toList.1 hβ))
    · intro hx
      have hxO : x ∈ O := Finset.mem_toList.1 hx
      have hx' : x ∈ O.image θ := by rw [himage]; exact hxO
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hx'
      exact List.mem_map.2 ⟨β, Finset.mem_toList.2 hβ, rfl⟩
  have hcomm : ∀ x ∈ O.toList.map θ, ∀ y ∈ O.toList.map θ, x ≠ y →
      Commute (rootReflection x) (rootReflection y) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    have haO : a ∈ O := Finset.mem_toList.1 ha
    have hbO : b ∈ O := Finset.mem_toList.1 hb
    have hne : a ≠ b := fun e => hxy (by rw [e])
    exact rootReflection_commute_of_iform_eq_zero (hθΦ a (hOroot a haO))
      (hθΦ b (hOroot b hbO)) (by rw [hθ]; exact hOorth a haO b hbO hne)
  exact list_prod_map_eq_of_mem_iff hnd₁ hnd₂ hmem rootReflection hcomm

private theorem corootPair_neg_left
    {τ : Tag} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    corootPair (-β) v = -corootPair β v := by
  have h1 := corootPair_mul hβ v
  have h2 := corootPair_mul (IsRoot.neg hβ) v
  have hn : iform (-β) v = -iform β v := by
    simp only [iform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have hnn : iform (-β) (-β) = iform β β := by
    simp only [iform, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  apply mul_right_cancel₀ (iform_self_pos_of_isRoot hβ).ne'
  rw [neg_mul, h1, ← hnn, h2, hn]
  ring

theorem reflectionWordProd_mem_unionWeylGroup_of_mem
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {l : List (Fin τ.rank → ℤ)} (hl : ∀ β ∈ l, β ∈ unionRoots χ J) :
    reflectionWordProd l ∈ unionWeylGroup χ J := by
  rw [reflectionWordProd]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨u, hu, δ, hδ, hδβ⟩ := exists_smul_unionSimpleRoot (hl β hβ)
    rw [hδβ, rootReflection_smul_root u (isRoot_of_mem_unionSimpleRoots hδ)]
    exact mul_mem (mul_mem hu (rootReflection_mem_unionWeylGroup hδ)) (inv_mem hu)

theorem rootDiagUnit_coordTuple_mem_closure_of_orthogonal
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)} {e : ℕ}
    {Q : ModGL τ L} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (hθΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α))
    (hQX : ∀ α, IsRoot τ α → ∀ c : L, Q * pinnedX τ L α c * Q⁻¹ = pinnedX τ L (θ α) c)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t')
    (hΨ : Set.BijOn θ (unionRoots χ J) (unionRoots χ J))
    {O : Finset (Fin τ.rank → ℤ)} (hOΨ : ∀ β ∈ O, β ∈ unionRoots χ J)
    (hOθ : ∀ β ∈ O, θ β ∈ O) (hOorth : ∀ β ∈ O, ∀ γ ∈ O, β ≠ γ → iform β γ = 0)
    (c : (Fin τ.rank → ℤ) → Lˣ) (hc : ∀ β ∈ O, c (θ β) = c β ^ 2 ^ e) :
    rootDiagUnit τ (coordTuple O c) ∈ Subgroup.closure {x : ModGL τ L |
      x ∈ unionRootSpan L χ J ∧ frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  classical
  let w : WeylGroup τ := reflectionWordProd O.toList
  let n : ModGL τ L := canonicalRep (coxeterSystem τ) L w
  let d : ModGL τ L := rootDiagUnit τ (coordTuple O c)
  let x : ModGL τ L := d * n
  have hOroot : ∀ β ∈ O, IsRoot τ β := fun β hβ => isRoot_of_mem_unionRoots (hOΨ β hβ)
  have horth : O.toList.Pairwise (fun β γ => iform β γ = 0) :=
    (Finset.nodup_toList O).pairwise_of_forall_ne fun β hβ γ hγ hne =>
      hOorth β (Finset.mem_toList.1 hβ) γ (Finset.mem_toList.1 hγ) hne
  have hwneg : ∀ β ∈ O, w • β = -β := by
    intro β hβ
    exact reflectionWordProd_smul_of_mem
      (fun γ hγ => hOroot γ (Finset.mem_toList.1 hγ)) horth (Finset.mem_toList.2 hβ)
  have hw2 : w * w = 1 := reflectionWordProd_mul_self
    (fun γ hγ => hOroot γ (Finset.mem_toList.1 hγ)) horth
  have hw : w ∈ unionWeylGroup χ J := reflectionWordProd_mem_unionWeylGroup_of_mem
    (fun β hβ => hOΨ β (Finset.mem_toList.1 hβ))
  have hnS : n ∈ unionRootSpan L χ J := canonicalRep_mem_rootSpan_unionRoots hw
  have hn2 : n * n = 1 := CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_self_charTwo hw2
  have hdS : d ∈ unionRootSpan L χ J :=
    unionTorus_le_unionRootSpan (rootDiagUnit_coordTuple_mem_unionTorus hOΨ c)
  have hdσ : frobTwistGL τ L 2 e Q d = d := by
    have himageθ : O.image θ = O := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro γ hγ
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hγ
        exact hOθ β hβ
      · rw [Finset.card_image_of_injective O θ.injective]
    have hpow : coordTuple O (c ^ 2 ^ e) = (coordTuple O c) ^ 2 ^ e :=
      map_pow (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom O)
        c (2 ^ e)
    have hFr : entrywiseFrobGL τ L 2 e d =
        rootDiagUnit τ (coordTuple O (c ^ 2 ^ e)) := by
      rw [show d = rootDiagUnit τ (coordTuple O c) from rfl,
        entrywiseFrobGL_rootDiagUnit_eq_map, hpow]
      congr 1
    have hgX : ∀ α, IsRoot τ α → ∃ ε : Lˣ, ∀ x : L,
        Q * pinnedX τ L α x * Q⁻¹ = pinnedX τ L (θ α) (ε * x) :=
      fun α hα => ⟨1, fun x => by simpa using hQX α hα x⟩
    have hQd : Q * rootDiagUnit τ (coordTuple O (c ^ 2 ^ e)) * Q⁻¹ =
        rootDiagUnit τ (coordTuple (O.image θ) fun γ => (c ^ 2 ^ e) (θ.symm γ)) :=
      conj_rootDiagUnit_coordTuple (g := Q) (π := θ) hθ hθΦ hgX hQT hOroot (c ^ 2 ^ e)
    have hcβ : ∀ β ∈ O, (c ^ 2 ^ e) (θ.symm β) = c β := by
      intro β hβ
      have hβim : β ∈ O.image θ := by rw [himageθ]; exact hβ
      obtain ⟨γ, hγ, hγβ⟩ := Finset.mem_image.1 hβim
      have hγ' : θ.symm β = γ := by
        rw [← hγβ, AddEquiv.symm_apply_apply]
      rw [hγ', Pi.pow_apply]
      exact (hc γ hγ).symm.trans (by rw [hγβ])
    have hcoord : coordTuple (O.image θ) (fun γ => (c ^ 2 ^ e) (θ.symm γ)) =
        coordTuple O c := by
      rw [himageθ]
      exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordTuple_congr hcβ
    rw [frobTwistGL_apply, hFr, hQd, hcoord]
  have hnd : n * d * n⁻¹ = d⁻¹ := by
    let π : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ) :=
      DistribMulAction.toAddEquiv (Fin τ.rank → ℤ) w
    have hπ_apply : ∀ y, π y = w • y := fun y => DistribMulAction.toAddEquiv_apply _ _ _
    have hπ : ∀ y z, iform (π y) (π z) = iform y z := fun y z => by
      rw [hπ_apply, hπ_apply, iform_smul]
    have hπΦ : ∀ α, IsRoot τ α → IsRoot τ (π α) := fun α hα => by
      rw [hπ_apply]; exact IsRoot.smul hα w
    have hgX : ∀ α, IsRoot τ α → ∃ ε : Lˣ, ∀ y : L,
        n * pinnedX τ L α y * n⁻¹ = pinnedX τ L (π α) (ε * y) := by
      intro α hα
      obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hα
      exact ⟨Units.mkOfMulEqOne ε ε hε, fun y => by
        rw [hπ_apply]
        simpa using hεc y⟩
    have hgT : ∀ t, ∃ t', n * rootDiagUnit τ t * n⁻¹ = rootDiagUnit τ t' :=
      fun t => ⟨CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w t,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit w t⟩
    have hconj : n * d * n⁻¹ =
        rootDiagUnit τ (coordTuple (O.image π) fun γ => c (π.symm γ)) := by
      rw [show d = rootDiagUnit τ (coordTuple O c) from rfl]
      exact conj_rootDiagUnit_coordTuple (g := n) (π := π) hπ hπΦ hgX hgT hOroot c
    have hcoord : coordTuple (O.image π) (fun γ => c (π.symm γ)) =
        coordTuple O (fun β => (c β)⁻¹) := by
      funext i
      simp only [coordTuple]
      rw [Finset.prod_image (fun y _ z _ h => π.injective h)]
      refine Finset.prod_congr rfl fun β hβ => ?_
      rw [AddEquiv.symm_apply_apply, hπ_apply, hwneg β hβ,
        corootPair_neg_left (hOroot β hβ) (Pi.single i 1), zpow_neg, inv_zpow]
    have hd_inv : rootDiagUnit τ (coordTuple O (fun β => (c β)⁻¹)) = d⁻¹ := by
      rw [show d = rootDiagUnit τ (coordTuple O c) from rfl, rootDiagUnit_inv]
      congr 1
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom_apply O c,
        ← map_inv,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom_apply]
      rfl
    rw [hconj, hcoord, hd_inv]
  have hnσ : frobTwistGL τ L 2 e Q n = n := by
    have hF : ∀ α ∈ unionRoots χ J,
        frobTwistGL τ L 2 e Q (pinnedX τ L α 1) = pinnedX τ L (θ α) 1 := by
      intro α hα
      rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX]
      rw [show (iterateFrobenius L 2 e) 1 = 1 by simp [iterateFrobenius_def]]
      exact hQX α (isRoot_of_mem_unionRoots hα) 1
    have hprod : reflectionWordProd (O.toList.map θ) = reflectionWordProd O.toList :=
      reflectionWordProd_map_eq_of_mem hOθ hθ hθΦ hOroot hOorth
    have hθref : ∀ γ ∈ unionRoots χ J, ∀ α ∈ unionRoots χ J,
        θ (rootReflection γ • α) = rootReflection (θ γ) • θ α :=
      fun γ hγ α _ => map_rootReflection_smul hθ hθΦ (isRoot_of_mem_unionRoots hγ) α
    have hwθ : ∀ α ∈ unionRoots χ J, θ (w • α) = w • θ α := by
      intro α _
      rw [map_reflectionWordProd_smul hθ hθΦ
        (fun β hβ => hOroot β (Finset.mem_toList.1 hβ)) α, hprod]
    exact map_canonicalRep_eq_self_of_commute (frobTwistGL τ L 2 e Q) (fun y => θ y)
      hΨ hθref hF hw hwθ
  have hxσ : frobTwistGL τ L 2 e Q x = x := by
    change frobTwistGL τ L 2 e Q (d * n) = d * n
    rw [map_mul, hdσ, hnσ]
  have hx2 : x * x = 1 := by
    change (d * n) * (d * n) = 1
    calc (d * n) * (d * n) = d * (n * d * n⁻¹) * (n * n) := by group
      _ = d * d⁻¹ * 1 := by rw [hnd, hn2]
      _ = 1 := by group
  have hxS : x ∈ unionRootSpan L χ J := by
    change d * n ∈ unionRootSpan L χ J
    exact mul_mem hdS hnS
  let D : Subgroup (ModGL τ L) := Subgroup.closure {x : ModGL τ L |
      x ∈ unionRootSpan L χ J ∧ frobTwistGL τ L 2 e Q x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
  have hnD : n ∈ D := Subgroup.subset_closure ⟨hnS, hnσ, 1, by simpa [pow_two] using hn2⟩
  have hxD : x ∈ D := Subgroup.subset_closure ⟨hxS, hxσ, 1, by simpa [pow_two] using hx2⟩
  have hdD : d ∈ D := by
    have hdn : d = x * n⁻¹ := by
      change d = d * n * n⁻¹
      group
    rw [hdn]
    exact D.mul_mem hxD (D.inv_mem hnD)
  exact hdD

end CFSG.HardMathSupport.C14Idx
