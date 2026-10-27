module

public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.LieType.Chevalley.GraphFixedRootNormal

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem torusElt_eq_rootDiagUnit
    (i : Fin τ.rank) (u : Kˣ) :
    torusElt τ K i u = rootDiagUnit τ (fun j => u ^ τ.cartan i j) := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_)
  · rw [torusElt_hVec]
    exact (rootDiag_hVec _ j).symm
  · rw [torusElt_rootVec _ _ hα]
    change _ = rootDiag _ (rootVec τ K α)
    rw [rootDiag_rootVec _ hα]
    congr 2
    rw [rootChar, ← prod_zpow_eq_zpow_sum]
    exact Finset.prod_congr rfl fun j _ => zpow_mul _ _ _

variable (τ K) in
@[expose] def rootDiagUnitHom : (Fin τ.rank → Kˣ) →* ModGL τ K where
  toFun := rootDiagUnit τ
  map_one' := rootDiagUnit_one
  map_mul' := rootDiagUnit_mul

@[expose] def cartanChar (c : Fin τ.rank → Kˣ) : Fin τ.rank → Kˣ :=
  fun l => ∏ j, c j ^ τ.cartan j l

theorem list_prod_torusElt_eq_rootDiagUnit
    (c : Fin τ.rank → Kˣ) :
    ((List.finRange τ.rank).map fun j => torusElt τ K j (c j)).prod =
      rootDiagUnit τ (cartanChar c) := by
  have h : ((List.finRange τ.rank).map fun j => torusElt τ K j (c j)) =
      ((List.finRange τ.rank).map fun j => fun l => c j ^ τ.cartan j l).map
        (rootDiagUnitHom τ K) := by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => torusElt_eq_rootDiagUnit j (c j)
  rw [h, ← map_list_prod, ← List.ofFn_eq_map, List.prod_ofFn]
  change rootDiagUnit τ _ = _
  congr 1
  funext l
  rw [Finset.prod_apply]
  rfl

end Torus

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem cartanChar_perm {c : Fin t.tag.rank → Kˣ}
    (hc : ∀ i, c (t.perm i) = Units.map σ.toMonoidHom (c i)) (l : Fin t.tag.rank) :
    cartanChar c (t.perm l) = Units.map σ.toMonoidHom (cartanChar c l) := by
  unfold cartanChar
  rw [map_prod]
  simp only [map_zpow, ← hc]
  exact (Fintype.prod_equiv t.perm (fun j => c (t.perm j) ^ t.tag.cartan j l)
    (fun j => c j ^ t.tag.cartan j (t.perm l)) fun j => by rw [t.cartan_perm]).symm

theorem list_prod_orbitH_eq_rootDiagUnit
    (w : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    ((List.finRange t.foldedTag.rank).map fun a => (orbitH t K σ a (w a) : ModGL t.tag K)).prod =
      rootDiagUnit t.tag (cartanChar (compatDiag t σ w)) := by
  rw [list_prod_orbitH, list_prod_torusElt_eq_rootDiagUnit]

theorem exists_list_prod_orbitH_conj
    (w : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ) :
    ∃ v : (a : Fin t.foldedTag.rank) → (orbitField t K σ a)ˣ,
      compatDiag t σ v = cartanChar (compatDiag t σ w) ∧
      (∀ a, orbitFieldUnit t σ (v a) = cartanChar (compatDiag t σ w) (t.orbitMin a)) ∧
      (∀ a c, ((List.finRange t.foldedTag.rank).map fun a =>
          (orbitH t K σ a (w a) : ModGL t.tag K)).prod * orbitX t K σ a c *
        (((List.finRange t.foldedTag.rank).map fun a =>
          (orbitH t K σ a (w a) : ModGL t.tag K)).prod)⁻¹ =
          orbitX t K σ a ((v a : orbitField t K σ a) * c)) ∧
      ∀ a c, ((List.finRange t.foldedTag.rank).map fun a =>
          (orbitH t K σ a (w a) : ModGL t.tag K)).prod * orbitY t K σ a c *
        (((List.finRange t.foldedTag.rank).map fun a =>
          (orbitH t K σ a (w a) : ModGL t.tag K)).prod)⁻¹ =
          orbitY t K σ a (((v a)⁻¹ : (orbitField t K σ a)ˣ) * c) := by
  obtain ⟨v, hv⟩ := exists_compatDiag_eq (cartanChar_perm (compatDiag_perm w))
  refine ⟨v, hv, fun a => by rw [← compatDiag_orbitMin, hv], fun a c => ?_, fun a c => ?_⟩
  · rw [list_prod_orbitH_eq_rootDiagUnit, ← hv]
    exact compatDiag_conj_orbitX v a c
  · rw [list_prod_orbitH_eq_rootDiagUnit, ← hv]
    exact compatDiag_conj_orbitY v a c

theorem eq_of_compat_of_orbitMin {c c' : Fin t.tag.rank → Kˣ}
    (hc : ∀ i, c (t.perm i) = Units.map σ.toMonoidHom (c i))
    (hc' : ∀ i, c' (t.perm i) = Units.map σ.toMonoidHom (c' i))
    (h : ∀ a, c (t.orbitMin a) = c' (t.orbitMin a)) : c = c' := by
  obtain ⟨w, rfl⟩ := exists_compatDiag_eq hc
  obtain ⟨w', rfl⟩ := exists_compatDiag_eq hc'
  have hw : w = w' := funext fun a => by
    have h1 := h a
    rw [compatDiag_orbitMin, compatDiag_orbitMin] at h1
    exact Units.ext (Subtype.ext (congrArg Units.val h1))
  rw [hw]

section D4

@[expose] def d4Pair (t : (orbitField TwistTag.D4 K σ ⟨0, by decide⟩)ˣ)
    (s : (orbitField TwistTag.D4 K σ ⟨1, by decide⟩)ˣ) :
    (a : Fin TwistTag.D4.foldedTag.rank) → (orbitField TwistTag.D4 K σ a)ˣ
  | ⟨0, _⟩ => t
  | ⟨1, _⟩ => s
  | ⟨n + 2, h⟩ => absurd h (by change ¬ n + 2 < 2; omega)

theorem list_prod_orbitH_d4Pair
    (t : (orbitField TwistTag.D4 K σ ⟨0, by decide⟩)ˣ)
    (s : (orbitField TwistTag.D4 K σ ⟨1, by decide⟩)ˣ) :
    ((List.finRange TwistTag.D4.foldedTag.rank).map fun a =>
        (orbitH TwistTag.D4 K σ a (d4Pair t s a) : ModGL TwistTag.D4.tag K)).prod =
      (orbitH TwistTag.D4 K σ ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ ⟨1, by decide⟩ s := by
  have hl : List.finRange TwistTag.D4.foldedTag.rank = [⟨0, by decide⟩, ⟨1, by decide⟩] := by
    decide
  rw [hl, List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons,
    List.prod_nil, mul_one]
  rfl

theorem compatDiag_D4 (w : (a : Fin TwistTag.D4.foldedTag.rank) → (orbitField TwistTag.D4 K σ a)ˣ) :
    compatDiag TwistTag.D4 σ w = ![orbitFieldUnit TwistTag.D4 σ (w ⟨0, by decide⟩),
      Units.map σ.toMonoidHom (orbitFieldUnit TwistTag.D4 σ (w ⟨0, by decide⟩)),
      orbitFieldUnit TwistTag.D4 σ (w ⟨1, by decide⟩),
      Units.map σ.toMonoidHom
        (Units.map σ.toMonoidHom (orbitFieldUnit TwistTag.D4 σ (w ⟨0, by decide⟩)))] := by
  have e0 : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have e1 : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have p0 : TwistTag.D4.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have p1 : TwistTag.D4.perm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
  have h0 := compatDiag_orbitMin w ⟨0, by decide⟩
  have h2 := compatDiag_orbitMin w ⟨1, by decide⟩
  rw [e0] at h0
  rw [e1] at h2
  have h1 := compatDiag_perm w ⟨0, by decide⟩
  rw [p0, h0] at h1
  have h3 := compatDiag_perm w ⟨1, by decide⟩
  rw [p1, h1] at h3
  funext i
  obtain ⟨n, hn⟩ := i
  have hn' : n < 4 := hn
  interval_cases n
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem cartanChar_D4_zero (c : Fin TwistTag.D4.tag.rank → Kˣ) :
    cartanChar c ⟨0, by decide⟩ = c ⟨0, by decide⟩ ^ 2 * (c ⟨2, by decide⟩)⁻¹ := by
  change ∏ j : Fin 4, c j ^ TwistTag.D4.tag.cartan j ⟨0, by decide⟩ = _
  rw [Fin.prod_univ_four]
  have a0 : TwistTag.D4.tag.cartan (0 : Fin 4) ⟨0, by decide⟩ = 2 := rfl
  have a1 : TwistTag.D4.tag.cartan (1 : Fin 4) ⟨0, by decide⟩ = 0 := rfl
  have a2 : TwistTag.D4.tag.cartan (2 : Fin 4) ⟨0, by decide⟩ = -1 := rfl
  have a3 : TwistTag.D4.tag.cartan (3 : Fin 4) ⟨0, by decide⟩ = 0 := rfl
  rw [a0, a1, a2, a3, zpow_zero, zpow_zero, mul_one, mul_one, zpow_neg_one]
  rfl

theorem cartanChar_D4_two (c : Fin TwistTag.D4.tag.rank → Kˣ) :
    cartanChar c ⟨2, by decide⟩ = (c ⟨0, by decide⟩)⁻¹ * (c ⟨1, by decide⟩)⁻¹ *
      c ⟨2, by decide⟩ ^ 2 * (c ⟨3, by decide⟩)⁻¹ := by
  change ∏ j : Fin 4, c j ^ TwistTag.D4.tag.cartan j ⟨2, by decide⟩ = _
  rw [Fin.prod_univ_four]
  have a0 : TwistTag.D4.tag.cartan (0 : Fin 4) ⟨2, by decide⟩ = -1 := rfl
  have a1 : TwistTag.D4.tag.cartan (1 : Fin 4) ⟨2, by decide⟩ = -1 := rfl
  have a2 : TwistTag.D4.tag.cartan (2 : Fin 4) ⟨2, by decide⟩ = 2 := rfl
  have a3 : TwistTag.D4.tag.cartan (3 : Fin 4) ⟨2, by decide⟩ = -1 := rfl
  rw [a0, a1, a2, a3, zpow_neg_one, zpow_neg_one, zpow_neg_one]
  rfl

theorem orbitH_mul_orbitH_D4
    (t a : (orbitField TwistTag.D4 K σ ⟨0, by decide⟩)ˣ)
    (s b : (orbitField TwistTag.D4 K σ ⟨1, by decide⟩)ˣ)
    (hts : (orbitFieldUnit TwistTag.D4 σ t : K) ^ 2 =
      (orbitFieldUnit TwistTag.D4 σ a : K) * (orbitFieldUnit TwistTag.D4 σ s : K))
    (hN : (orbitFieldUnit TwistTag.D4 σ t : K) * σ (orbitFieldUnit TwistTag.D4 σ t : K) *
        σ (σ (orbitFieldUnit TwistTag.D4 σ t : K)) * (orbitFieldUnit TwistTag.D4 σ b : K) =
      (orbitFieldUnit TwistTag.D4 σ s : K) ^ 2) :
    (orbitH TwistTag.D4 K σ ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ ⟨1, by decide⟩ s =
      rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ (d4Pair a b)) := by
  rw [← list_prod_orbitH_d4Pair, list_prod_orbitH_eq_rootDiagUnit]
  congr 1
  refine eq_of_compat_of_orbitMin (cartanChar_perm (compatDiag_perm _)) (compatDiag_perm _)
    fun c => ?_
  have hs0 : (orbitFieldUnit TwistTag.D4 σ s : K) ≠ 0 := Units.ne_zero _
  have ht0 : (orbitFieldUnit TwistTag.D4 σ t : K) ≠ 0 := Units.ne_zero _
  have c0 : compatDiag TwistTag.D4 σ (d4Pair t s) ⟨0, by decide⟩ =
      orbitFieldUnit TwistTag.D4 σ t := by
    rw [compatDiag_D4]
    rfl
  have c1 : compatDiag TwistTag.D4 σ (d4Pair t s) ⟨1, by decide⟩ =
      Units.map σ.toMonoidHom (orbitFieldUnit TwistTag.D4 σ t) := by
    rw [compatDiag_D4]
    rfl
  have c2 : compatDiag TwistTag.D4 σ (d4Pair t s) ⟨2, by decide⟩ =
      orbitFieldUnit TwistTag.D4 σ s := by
    rw [compatDiag_D4]
    rfl
  have c3 : compatDiag TwistTag.D4 σ (d4Pair t s) ⟨3, by decide⟩ =
      Units.map σ.toMonoidHom (Units.map σ.toMonoidHom (orbitFieldUnit TwistTag.D4 σ t)) := by
    rw [compatDiag_D4]
    rfl
  have d0 : compatDiag TwistTag.D4 σ (d4Pair a b) ⟨0, by decide⟩ =
      orbitFieldUnit TwistTag.D4 σ a := by
    rw [compatDiag_D4]
    rfl
  have d2 : compatDiag TwistTag.D4 σ (d4Pair a b) ⟨2, by decide⟩ =
      orbitFieldUnit TwistTag.D4 σ b := by
    rw [compatDiag_D4]
    rfl
  obtain ⟨n, hn⟩ := c
  have hn' : n < 2 := hn
  interval_cases n
  · have e0 : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
    rw [e0, cartanChar_D4_zero, c0, c2, d0]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    rw [hts]
    field_simp
  · have e1 : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
    rw [e1, cartanChar_D4_two, c0, c1, c2, c3, d2]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    have hσt : σ (orbitFieldUnit TwistTag.D4 σ t : K) ≠ 0 := (map_ne_zero σ).2 ht0
    have hσσt : σ (σ (orbitFieldUnit TwistTag.D4 σ t : K)) ≠ 0 := (map_ne_zero σ).2 hσt
    rw [← hN]
    field_simp

theorem twistHom_rootDiagUnit_eq
    (b : Fin t.tag.rank → Kˣ) :
    twistHom t K σ (rootDiagUnit t.tag b) =
      rootDiagUnit t.tag (fun i => Units.map σ.toMonoidHom (b (t.perm.symm i))) := by
  refine Units.ext ?_
  rw [coe_twistHom]
  change (diagramMap t K : Module.End K (RootModule t.tag K)) * entrywise σ (rootDiag b) *
    (((diagramMap t K)⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) =
      rootDiag (fun i => Units.map σ.toMonoidHom (b (t.perm.symm i)))
  rw [entrywise_rootDiag, diagramMap_mul_rootDiag, mul_assoc, Units.mul_inv, mul_one]

theorem rootDiagUnit_injective
    {τ : Tag} :
    Function.Injective (rootDiagUnit τ : (Fin τ.rank → Kˣ) → ModGL τ K) := by
  intro b b' h
  funext i
  have hv := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))
    (rootVec τ K (Pi.single i 1))) h
  change rootDiag b (rootVec τ K _) = rootDiag b' (rootVec τ K _) at hv
  rw [rootDiag_rootVec _ (isRoot_single τ i), rootDiag_rootVec _ (isRoot_single τ i)] at hv
  have hne : rootVec τ K (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := by
    rw [rootVec_eq_single (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h1 := smul_left_injective K hne hv
  have e : ∀ c : Fin τ.rank → Kˣ, rootChar c (Pi.single i 1) = c i := fun c => by
    have := rootChar_nsmul_single c i 1
    rwa [one_nsmul, pow_one] at this
  rw [e, e] at h1
  exact Units.ext h1

theorem d4Pair_eta (v : (a : Fin TwistTag.D4.foldedTag.rank) → (orbitField TwistTag.D4 K σ a)ˣ) :
    d4Pair (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) = v := by
  funext a
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n <;> rfl

end D4

theorem ringHom_pow_three_apply (σ : K →+* K) (c : K) : (σ ^ 3) c = σ (σ (σ c)) := by
  rw [pow_succ, pow_succ, pow_one, RingHom.coe_mul, RingHom.coe_mul]
  rfl

theorem norm_mul_sq_eq {σ : K →+* K} {A B S T : K} (hA : σ (σ (σ A)) = A) (hB : σ B = B)
    (hS : S = A * σ A * σ (σ A) * B ^ 2) (hT : T ^ 2 = A * S) :
    (T * σ T * σ (σ T) * B) ^ 2 = (S ^ 2) ^ 2 := by
  have hσS : σ S = S := by
    rw [hS, map_mul, map_mul, map_mul, map_pow, hB, hA]
    ring
  have h1 : (σ T) ^ 2 = σ A * S := by rw [← map_pow, hT, map_mul, hσS]
  have h2 : (σ (σ T)) ^ 2 = σ (σ A) * S := by rw [← map_pow, h1, map_mul, hσS]
  calc (T * σ T * σ (σ T) * B) ^ 2 = T ^ 2 * (σ T) ^ 2 * (σ (σ T)) ^ 2 * B ^ 2 := by ring
    _ = (A * S) * (σ A * S) * (σ (σ A) * S) * B ^ 2 := by rw [hT, h1, h2]
    _ = S ^ 3 * (A * σ A * σ (σ A) * B ^ 2) := by ring
    _ = (S ^ 2) ^ 2 := by rw [← hS]; ring

section Triality

variable (σ' : K ≃+* K) (hσ3 : ∀ c, σ' (σ' (σ' c)) = c)
include hσ3

theorem orbitField_D4_zero_eq_top : orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ = ⊤ :=
  eq_top_iff.2 fun c _ => (mem_orbitField).2 (by
    rw [show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide, ringHom_pow_three_apply]
    exact hσ3 c)

omit hσ3 in
theorem mem_orbitField_D4_one {c : K} :
    c ∈ orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ ↔ σ' c = c := by
  rw [mem_orbitField, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
  rfl

theorem norm_mul_sq_mem (A B : K) (hB : σ' B = B) :
    A * σ' A * σ' (σ' A) * B ^ 2 ∈ orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ := by
  rw [mem_orbitField_D4_one]
  rw [map_mul, map_mul, map_mul, map_pow, hB, hσ3]
  ring

omit hσ3 in
theorem torusWord_D4_conj
    (a t : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ)
    (b s : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ)
    (h : (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s =
      rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ'.toRingHom (d4Pair a b))) :
    (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s ∈
      graphFixedRootGroup TwistTag.D4 K σ'.toRingHom ∧
    (∀ c, (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s *
          orbitX TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ c *
        ((orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s)⁻¹ =
      orbitX TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩
        ((a : orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩) * c)) ∧
    (∀ c, (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s *
          orbitY TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ c *
        ((orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s)⁻¹ =
      orbitY TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩
        (((a⁻¹ : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ) :
          orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩) * c)) ∧
    (∀ d, (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s *
          orbitX TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ d *
        ((orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s)⁻¹ =
      orbitX TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩
        ((b : orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩) * d)) ∧
    ∀ d, (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s *
          orbitY TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ d *
        ((orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s)⁻¹ =
      orbitY TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩
        (((b⁻¹ : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ) :
          orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩) * d) := by
  refine ⟨mul_mem (orbitH_mem_graphFixedRootGroup _ _ _ _)
    (orbitH_mem_graphFixedRootGroup _ _ _ _), fun c => ?_, fun c => ?_, fun d => ?_, fun d => ?_⟩
  · rw [h]
    exact compatDiag_conj_orbitX (d4Pair a b) ⟨0, by decide⟩ c
  · rw [h]
    exact compatDiag_conj_orbitY (d4Pair a b) ⟨0, by decide⟩ c
  · rw [h]
    exact compatDiag_conj_orbitX (d4Pair a b) ⟨1, by decide⟩ d
  · rw [h]
    exact compatDiag_conj_orbitY (d4Pair a b) ⟨1, by decide⟩ d

theorem exists_even_triality_torusWord
    [Finite K] (hchar : ringChar K = 2)
    (a : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ)
    (b : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ) :
    ∃ (s : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ)
      (t : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ),
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) =
        (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
          σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
          σ' (σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K)) *
          (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) ^ 2 ∧
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K) ^ 2 =
        (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) ∧
      (∀ t' : K, t' ^ 2 = (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) →
        t' = (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K)) ∧
      (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s =
        rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ'.toRingHom (d4Pair a b)) := by
  have : CharP K 2 := ringChar.of_eq hchar
  have hB : σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) =
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) :=
    (mem_orbitField_D4_one σ').1 b.val.2
  have hA0 := (orbitFieldUnit TwistTag.D4 σ'.toRingHom a).ne_zero
  have hB0 := (orbitFieldUnit TwistTag.D4 σ'.toRingHom b).ne_zero
  have hS0 : (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
      σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
      σ' (σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K)) *
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) ^ 2 ≠ 0 := by
    have h1 := (map_ne_zero σ').2 hA0
    have h2 := (map_ne_zero σ').2 h1
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hA0 h1) h2) (pow_ne_zero 2 hB0)
  set s : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ := Units.mk0
    ⟨_, norm_mul_sq_mem σ' hσ3 _ _ hB⟩ fun h => hS0 (congrArg Subtype.val h) with hs
  obtain ⟨T, hT⟩ := FiniteField.isSquare_of_char_two hchar
    ((orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K))
  have hT0 : T ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hT
    exact mul_ne_zero hA0 hS0 hT
  have hTmem : T ∈ orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ := by
    rw [orbitField_D4_zero_eq_top σ' hσ3]
    trivial
  set t : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ :=
    Units.mk0 ⟨T, hTmem⟩ fun h => hT0 (congrArg Subtype.val h) with ht
  have hts : (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K) ^ 2 =
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
        (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) := by
    change T ^ 2 = _
    rw [hT]
    ring
  have hN := norm_mul_sq_eq (σ := σ'.toRingHom) (hσ3 _) hB rfl hts
  have hN' : (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K) *
      σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K) *
      σ' (σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K)) *
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) =
        (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) ^ 2 :=
    frobenius_inj K 2 (by rw [frobenius_def, frobenius_def]; exact hN)
  refine ⟨s, t, rfl, hts, fun t' h' => frobenius_inj K 2 ?_,
    orbitH_mul_orbitH_D4 t a s b hts hN'⟩
  rw [frobenius_def, frobenius_def, h', hts]

theorem exists_odd_triality_torusWord
    {q : ℕ} (hq : Odd q) [Finite K]
    (hσq : ∀ c, σ' c = c ^ q)
    (a : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ)
    (b : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ) :
    ∃ (s : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ)
      (t : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ),
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) =
        (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
          σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
          σ' (σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K)) *
          (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) ^ 2 ∧
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K) ^ 2 =
        (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) ∧
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K) *
          σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K) *
          σ' (σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom t : K)) *
          (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) =
        (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) ^ 2 ∧
      (orbitH TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩ s =
        rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ'.toRingHom (d4Pair a b)) := by
  have hB : σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) =
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) :=
    (mem_orbitField_D4_one σ').1 b.val.2
  have hA0 := (orbitFieldUnit TwistTag.D4 σ'.toRingHom a).ne_zero
  have hB0 := (orbitFieldUnit TwistTag.D4 σ'.toRingHom b).ne_zero
  have hS0 : (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
      σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) *
      σ' (σ' (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K)) *
      (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) ^ 2 ≠ 0 := by
    have h1 := (map_ne_zero σ').2 hA0
    have h2 := (map_ne_zero σ').2 h1
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hA0 h1) h2) (pow_ne_zero 2 hB0)
  set s : (orbitField TwistTag.D4 K σ'.toRingHom ⟨1, by decide⟩)ˣ := Units.mk0
    ⟨_, norm_mul_sq_mem σ' hσ3 _ _ hB⟩ fun h => hS0 (congrArg Subtype.val h) with hs
  obtain ⟨m, hm⟩ : Even (q + q ^ 2) := by
    rw [sq]
    exact (hq.add_odd (hq.mul hq))
  set A := (orbitFieldUnit TwistTag.D4 σ'.toRingHom a : K) with hAdef
  set B := (orbitFieldUnit TwistTag.D4 σ'.toRingHom b : K) with hBdef
  have hT0sq : (A * B * A ^ m) ^ 2 = A * (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) := by
    change _ = A * (A * σ' A * σ' (σ' A) * B ^ 2)
    rw [hσq, hσq, ← pow_mul, mul_pow, mul_pow, ← pow_mul, show m * 2 = q + q ^ 2 by omega,
      pow_add, sq q]
    ring
  have hN : (A * B * A ^ m * σ' (A * B * A ^ m) * σ' (σ' (A * B * A ^ m)) * B) ^ 2 =
      ((orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) ^ 2) ^ 2 :=
    norm_mul_sq_eq (σ := σ'.toRingHom) (hσ3 _) hB rfl hT0sq
  have hsq := sq_eq_sq_iff_eq_or_eq_neg.1 hN
  obtain ⟨T, hTsq, hTN⟩ : ∃ T : K, T ^ 2 = A * (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) ∧
      T * σ' T * σ' (σ' T) * B = (orbitFieldUnit TwistTag.D4 σ'.toRingHom s : K) ^ 2 := by
    rcases hsq with h | h
    · exact ⟨_, hT0sq, h⟩
    · refine ⟨-(A * B * A ^ m), by rw [neg_sq, hT0sq], ?_⟩
      simp only [map_neg]
      linear_combination -h
  have hT0 : T ≠ 0 := fun h => mul_ne_zero hA0 hS0 (by
    have := hTsq
    rw [h, zero_pow two_ne_zero] at this
    exact this.symm)
  have hTmem : T ∈ orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩ := by
    rw [orbitField_D4_zero_eq_top σ' hσ3]
    trivial
  set t : (orbitField TwistTag.D4 K σ'.toRingHom ⟨0, by decide⟩)ˣ :=
    Units.mk0 ⟨T, hTmem⟩ fun h => hT0 (congrArg Subtype.val h) with ht
  exact ⟨s, t, rfl, hTsq, hTN, orbitH_mul_orbitH_D4 t a s b hTsq hTN⟩

end Triality



theorem exists_rootDiagUnit_eq_of_mem_torusGroup
    {τ : Tag} {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : ∃ l : Fin τ.rank → Kˣ, h = rootDiagUnit τ l := by
  obtain ⟨l, hl⟩ := exists_torus_characters hh
  refine ⟨l, Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_)⟩
  · rw [((triangular_borel_structure.{0, 0} τ K).2.1 _ hh).1 j]
    exact (rootDiag_hVec l j).symm
  · rw [(hl α hα).1]
    exact (rootDiag_rootVec l hα).symm

theorem compat_of_twistHom_rootDiagUnit
    {b : Fin t.tag.rank → Kˣ}
    (h : twistHom t K σ (rootDiagUnit t.tag b) = rootDiagUnit t.tag b) (i : Fin t.tag.rank) :
    b (t.perm i) = Units.map σ.toMonoidHom (b i) := by
  rw [twistHom_rootDiagUnit_eq] at h
  have h1 := congrFun (rootDiagUnit_injective h) (t.perm i)
  rw [Equiv.symm_apply_apply] at h1
  exact h1.symm

theorem even_triality_pair_scalars_inner
    {f : ℕ} (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ ↔ σ c = c) ∧
    ∀ (a : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ)
      (b : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ),
    ∃ (s : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ)
      (t : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ),
      (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) =
        (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          σ (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          σ (σ (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K)) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom b : K) ^ 2 ∧
      (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K) ^ 2 =
        (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) ∧
      (∀ t' : K, t' ^ 2 = (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) →
        t' = (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K)) ∧
      (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      (∀ c, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
          ((a : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) * c)) ∧
      (∀ c, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
          (((a⁻¹ : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ) :
            orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) * c)) ∧
      (∀ d, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ d *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩
          ((b : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) * d)) ∧
      ∀ d, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ d *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩
          (((b⁻¹ : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ) :
            orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) * d) := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = (2 ^ f) ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring,
      ← hcard, FiniteField.pow_card]
  have hf : f ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := K)
    rw [hcard] at this
    norm_num at this
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow (dvd_pow_self 2 hf) (by norm_num)))
  refine ⟨orbitField_D4_zero_eq_top σ hσ3, fun c => mem_orbitField_D4_one σ, fun a b => ?_⟩
  obtain ⟨s, t, hs, hts, huniq, heq⟩ := exists_even_triality_torusWord σ hσ3 hchar a b
  exact ⟨s, t, hs, hts, huniq, torusWord_D4_conj σ a t b s heq⟩

theorem odd_triality_pair_scalars_inner
    {q : ℕ} (hq : Odd q) (K : Type) [Field K]
    (hK : Nat.card K = q ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) :
    orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ ↔ σ c = c) ∧
    ∀ (a : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ)
      (b : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ),
    ∃ (s : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ)
      (t : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ),
      (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) =
        (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          σ (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          σ (σ (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K)) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom b : K) ^ 2 ∧
      (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K) ^ 2 =
        (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) ∧
      (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K) *
          σ (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K) *
          σ (σ (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K)) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom b : K) =
        (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) ^ 2 ∧
      (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      (∀ c, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
          ((a : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) * c)) ∧
      (∀ c, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
          (((a⁻¹ : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ) :
            orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) * c)) ∧
      (∀ d, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ d *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩
          ((b : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) * d)) ∧
      ∀ d, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ d *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩
          (((b⁻¹ : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ) :
            orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) * d) := by
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = q ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show q * (q * q) = q ^ 3 by ring, ← hcard,
      FiniteField.pow_card]
  refine ⟨orbitField_D4_zero_eq_top σ hσ3, fun c => mem_orbitField_D4_one σ, fun a b => ?_⟩
  obtain ⟨s, t, hs, hts, hN, heq⟩ := exists_odd_triality_torusWord σ hσ3 hq hσ a b
  exact ⟨s, t, hs, hts, hN, torusWord_D4_conj σ a t b s heq⟩

theorem even_triality_fixed_group_eq_root_group
    (K : Type) [Field K] [Finite K]
    (hchar : ringChar K = 2) (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    twistedFixedGroup TwistTag.D4 K σ.toRingHom = graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
    orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ ↔ σ c = c) ∧
    ∀ (a : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ)
      (b : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ),
    ∃ (s : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ)
      (t : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ),
      (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) =
        (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          σ (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          σ (σ (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K)) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom b : K) ^ 2 ∧
      (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K) ^ 2 =
        (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) ∧
      (∀ t' : K, t' ^ 2 = (orbitFieldUnit TwistTag.D4 σ.toRingHom a : K) *
          (orbitFieldUnit TwistTag.D4 σ.toRingHom s : K) →
        t' = (orbitFieldUnit TwistTag.D4 σ.toRingHom t : K)) ∧
      (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s ∈
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      (∀ c, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
          ((a : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) * c)) ∧
      (∀ c, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩
          (((a⁻¹ : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ) :
            orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) * c)) ∧
      (∀ d, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ d *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩
          ((b : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) * d)) ∧
      ∀ d, (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s *
            orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ d *
          ((orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
            orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s)⁻¹ =
        orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩
          (((b⁻¹ : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ) :
            orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) * d) := by
  have hH : graphFixedTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    intro h hh
    obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
    have hl := compat_of_twistHom_rootDiagUnit
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hhΓ).2
    obtain ⟨v, rfl⟩ := exists_compatDiag_eq hl
    obtain ⟨s, t, -, -, -, heq⟩ := exists_even_triality_torusWord σ hσ3 hchar
      (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)
    rw [d4Pair_eta] at heq
    rw [← heq]
    exact mul_mem (orbitH_mem_graphFixedRootGroup _ _ _ _)
      (orbitH_mem_graphFixedRootGroup _ _ _ _)
  refine ⟨le_antisymm (fun g hg => ?_) (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom),
    orbitField_D4_zero_eq_top σ hσ3, fun c => mem_orbitField_D4_one σ, fun a b => ?_⟩
  · have hg' : g ∈ (twistedFixedGroup TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) :=
      hg
    rw [coe_twistedFixedGroup_eq_mul σ.surjective] at hg'
    obtain ⟨h, hh, c, hc, rfl⟩ := hg'
    exact mul_mem (hH hh) hc
  · obtain ⟨s, t, hs, hts, huniq, heq⟩ := exists_even_triality_torusWord σ hσ3 hchar a b
    exact ⟨s, t, hs, hts, huniq, torusWord_D4_conj σ a t b s heq⟩

end CFSG.LieType.Chevalley
