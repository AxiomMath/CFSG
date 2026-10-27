module

public import CFSG.LieType.HighestRoot.Defs
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Generic

variable {τ : Tag} {K : Type} [Field K]

theorem rootSpan_pair_eq
    (γ : Fin τ.rank → ℤ) :
    rootSpan τ K {γ, -γ} = rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  rw [rootSpan, iSup_insert, iSup_singleton]

theorem canonicalRep_mem_normalizer_pair
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {w : WeylGroup τ} (hw : w • γ = γ ∨ w • γ = -γ) :
    canonicalRep (coxeterSystem τ) K w ∈ Subgroup.normalizer
      ((rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
  apply mem_normalizer_of_map_eq
  rw [Subgroup.map_sup, (canonical_weyl_root_transport τ K).2.1 w γ hγ,
    (canonical_weyl_root_transport τ K).2.1 w (-γ) (IsRoot.neg hγ), smul_neg]
  rcases hw with h | h
  · rw [h]
  · rw [h, neg_neg, sup_comm]

theorem commute_of_forall_not_isRoot
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • α + b • β)) {x y : ModGL τ K}
    (hx : x ∈ rootSubgroup τ K α) (hy : y ∈ rootSubgroup τ K β) : Commute x y := by
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hα hβ hne hne'
  have hnil : commPairs τ α β = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp =>
    h p.1 p.2 ((hmem p).1 hp).1 ((hmem p).1 hp).2.1 ((hmem p).1 hp).2.2
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  have h1 := hF K c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg] at h1
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)

theorem mem_normalizer_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : ∀ y ∈ A, Commute x y) (hB : ∀ y ∈ B, Commute x y) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hA y hy).eq.symm)
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hB y hy).eq.symm)
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem toralCentralizer_le_normalizer_pair
    {a : Fin τ.rank → Kˣ} {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ)
    (hcomm : ∀ α ∈ rootCharKernel a, α ≠ γ → α ≠ -γ → ∀ x ∈ rootSubgroup τ K α,
      (∀ y ∈ rootSubgroup τ K γ, Commute x y) ∧ ∀ y ∈ rootSubgroup τ K (-γ), Commute x y)
    (hW : ∀ w ∈ rootCharStabilizer a, w • γ = γ ∨ w • γ = -γ) :
    toralCentralizer τ K a ≤ Subgroup.normalizer
      ((rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K a).2.2.2]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [← rootSpan_pair_eq]
    refine torusGroup_le_normalizer_rootSpan ?_
    rintro α (rfl | rfl)
    · exact hγ
    · exact IsRoot.neg hγ
  · refine iSup₂_le fun α hα => ?_
    by_cases h1 : α = γ
    · subst h1
      exact le_sup_left.trans Subgroup.le_normalizer
    by_cases h2 : α = -γ
    · subst h2
      exact le_sup_right.trans Subgroup.le_normalizer
    intro x hx
    obtain ⟨hc1, hc2⟩ := hcomm α hα h1 h2 x hx
    exact mem_normalizer_sup_of_commute hc1 hc2
  · rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact canonicalRep_mem_normalizer_pair hγ (hW w hw)

end Generic

section Roots

variable {τ : Tag}

theorem not_isRoot_nsmul_add_of_iform_eq_zero
    (hτ : NoG2 τ) {α γ : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hγ : IsRoot τ γ) (hlong : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform γ γ)
    (h0 : iform α γ = 0) (hne : α ≠ γ) (hne' : α ≠ -γ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot τ (a • α + b • γ) := by
  intro h
  rcases exponent_pair_cases hτ hα hγ hne hne' ha hb h with ⟨rfl, rfl⟩ | ⟨-, -, -, -, h'⟩ |
    ⟨-, -, -, -, h'⟩
  · rw [one_smul, one_smul] at h
    have h1 := hlong _ h
    have h2 : iform (α + γ) (α + γ) = iform α α + iform γ γ := by
      rw [iform_add_left, iform_add_right, iform_add_right, h0, iform_comm γ α, h0]
      ring
    have h3 := iform_self_pos hα.ne_zero
    omega
  · omega
  · omega

theorem iform_neg_right
    (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

theorem iform_neg_neg
    (x : Fin τ.rank → ℤ) : iform (-x) (-x) = iform x x := by
  rw [← neg_one_smul ℤ x, iform_smul_left, iform_smul_right]
  ring

variable {K : Type} [Field K]

theorem commute_pair_of_iform_eq_zero
    (hτ : NoG2 τ) {α γ : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hγ : IsRoot τ γ) (hlong : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform γ γ) (h0 : iform α γ = 0)
    (hne : α ≠ γ) (hne' : α ≠ -γ) :
    ∀ x ∈ rootSubgroup τ K α,
      (∀ y ∈ rootSubgroup τ K γ, Commute x y) ∧ ∀ y ∈ rootSubgroup τ K (-γ), Commute x y := by
  intro x hx
  refine ⟨fun y hy => commute_of_forall_not_isRoot hα hγ hne hne'
    (fun a b ha hb => not_isRoot_nsmul_add_of_iform_eq_zero hτ hα hγ hlong h0 hne hne' ha hb)
    hx hy, fun y hy => ?_⟩
  have hγ' : IsRoot τ (-γ) := IsRoot.neg hγ
  have hlong' : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform (-γ) (-γ) := by
    rw [iform_neg_neg]
    exact hlong
  have h0' : iform α (-γ) = 0 := by rw [iform_neg_right, h0, neg_zero]
  have hne2 : α ≠ -(-γ) := by rwa [neg_neg]
  exact commute_of_forall_not_isRoot hα hγ' hne' hne2
    (fun a b ha hb => not_isRoot_nsmul_add_of_iform_eq_zero hτ hα hγ' hlong' h0' hne' hne2 ha hb)
    hx hy

theorem smul_eq_or_eq_neg_of_mem_rootCharStabilizer
    {a : Fin τ.rank → Kˣ} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rootCharKernel a)
    (hC1 : ∀ α ∈ rootCharKernel a, α ≠ γ → α ≠ -γ → iform α γ = 0)
    (hC2 : ∀ δ ∈ rootCharKernel a, δ ≠ γ → δ ≠ -γ → ∃ ε ∈ rootCharKernel a, ε ≠ γ ∧ ε ≠ -γ ∧
      ε ≠ δ ∧ ε ≠ -δ ∧ iform δ ε ≠ 0)
    {w : WeylGroup τ} (hw : w ∈ rootCharStabilizer a) : w • γ = γ ∨ w • γ = -γ := by
  have hmem : ∀ {v : Fin τ.rank → ℤ}, v ∈ rootCharKernel a → w • v ∈ rootCharKernel a :=
    fun {v} hv => ⟨IsRoot.smul hv.1 w, by rw [hw v]; exact hv.2⟩
  have hmem' : ∀ {v : Fin τ.rank → ℤ}, v ∈ rootCharKernel a → w⁻¹ • v ∈ rootCharKernel a :=
    fun {v} hv => ⟨IsRoot.smul hv.1 w⁻¹, by rw [← hw (w⁻¹ • v), smul_inv_smul]; exact hv.2⟩
  by_contra hne
  rw [not_or] at hne
  obtain ⟨ε, hε, -, -, hεδ, hεδ', hδε⟩ := hC2 (w • γ) (hmem hγ) hne.1 hne.2
  have h1 : w⁻¹ • ε ≠ γ := fun h => hεδ (by rw [← h, smul_inv_smul])
  have h2 : w⁻¹ • ε ≠ -γ := fun h => hεδ' (by rw [← smul_neg, ← h, smul_inv_smul])
  have h3 := hC1 _ (hmem' hε) h1 h2
  rw [← iform_smul w, smul_inv_smul, iform_comm] at h3
  exact hδε h3

end Roots

section Sign

variable (τ : Tag) (K : Type) [Field K]

@[expose] def signTuple (i : Fin τ.rank) : Fin τ.rank → Kˣ :=
  fun j => (-1 : Kˣ) ^ τ.cartan i j

variable {τ K}

theorem torusElt_neg_one_eq
    (i : Fin τ.rank) :
    torusElt τ K i (-1) = rootDiagUnit τ (signTuple τ K i) :=
  torusElt_eq_rootDiagUnit i (-1)

theorem rootChar_signTuple (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    rootChar (signTuple τ K i) v = (-1 : Kˣ) ^ (∑ j, τ.cartan i j * v j) := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm

theorem neg_one_zpow_eq_one_iff (hK : ringChar K ≠ 2) (n : ℤ) :
    (-1 : Kˣ) ^ n = 1 ↔ Even n := by
  rcases Int.even_or_odd n with h | h
  · exact ⟨fun _ => h, fun _ => h.neg_one_zpow⟩
  · refine ⟨fun h1 => ?_, fun h' => absurd h' (Int.not_even_iff_odd.2 h)⟩
    rw [h.neg_one_zpow] at h1
    exact absurd (congrArg Units.val h1) (by
      simpa using Ring.neg_one_ne_one_of_char_ne_two hK)

theorem mem_rootCharKernel_signTuple (hK : ringChar K ≠ 2) (i : Fin τ.rank)
    (α : Fin τ.rank → ℤ) :
    α ∈ rootCharKernel (signTuple τ K i) ↔ IsRoot τ α ∧ Even (∑ j, τ.cartan i j * α j) := by
  change IsRoot τ α ∧ rootChar (signTuple τ K i) α = 1 ↔ _
  rw [rootChar_signTuple, neg_one_zpow_eq_one_iff hK]

theorem single_mem_rootCharKernel_signTuple
    (hK : ringChar K ≠ 2) (i : Fin τ.rank) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ∈ rootCharKernel (signTuple τ K i) := by
  rw [mem_rootCharKernel_signTuple hK]
  refine ⟨isRoot_single τ i, ?_⟩
  rw [sum_cartan_mul_single]
  exact even_two

theorem iform_eq_zero_of_mem_rootCharKernel_signTuple
    (hK : ringChar K ≠ 2) {i : Fin τ.rank}
    (hlong : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform (Pi.single i 1) (Pi.single i 1))
    {α : Fin τ.rank → ℤ} (hα : α ∈ rootCharKernel (signTuple τ K i))
    (hne : α ≠ Pi.single i 1) (hne' : α ≠ -Pi.single i 1) :
    iform α (Pi.single i 1) = 0 := by
  rw [mem_rootCharKernel_signTuple hK] at hα
  obtain ⟨hα, heven⟩ := hα
  set s := ∑ j, τ.cartan i j * α j with hs
  have hd := symmetrizer_pos τ i
  have hform : iform α (Pi.single i 1) = τ.symmetrizer i i * s := iform_single_right α i
  have hlt := iform_sq_lt hα (isRoot_single τ i) hne hne'
  have hαα := hlong α hα
  rw [iform_single_single, hform] at hlt
  rw [iform_single_single] at hαα
  have hαpos := iform_self_pos hα.ne_zero
  have hsq : s ^ 2 < 4 := by
    by_contra hge
    replace hge := not_lt.1 hge
    have : (τ.symmetrizer i i) ^ 2 * 4 ≤ (τ.symmetrizer i i * s) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hge (by positivity)
    nlinarith
  have hb : -2 < s ∧ s < 2 := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨k, hk⟩ := heven
  have hs0 : s = 0 := by omega
  rw [hform, hs0, mul_zero]

end Sign

section Involution

variable {τ : Tag} {K : Type} [Field K]

theorem neg_one_eq_HSL_neg_one : (-1 : SL2 K) = HSL (-1) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [HSL]

theorem eq_torusElt_neg_one
    (hK : ringChar K ≠ 2) (i : Fin τ.rank) {z : ModGL τ K}
    (hz : z ∈ rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1))
    (h2 : orderOf z = 2) : z = torusElt τ K i (-1) := by
  rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2] at hz
  obtain ⟨A, rfl⟩ := hz
  have hA : orderOf A = 2 := by
    rwa [orderOf_injective _ (simpleRootSL2_injective hK i)] at h2
  have hA' := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K (Ring.two_ne_zero hK) A).1 hA
  rw [hA', CFSG.Semidihedral.OddFieldSL2.minusIdentity, neg_one_eq_HSL_neg_one,
    simpleRootSL2_HSL]

end Involution

section Check

variable (τ : Tag)

@[expose] def corootPair (i : Fin τ.rank) (v : Fin τ.rank → ℤ) : ℤ :=
  ∑ j, τ.cartan i j * v j

@[expose] def isolatedCheck (i : Fin τ.rank) (wit : List ℕ) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    decide (corootPair τ i (τ.rootCertificate.root k) % 2 ≠ 0) ||
      (List.ofFn (τ.rootCertificate.root k) == List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ)) ||
      (List.ofFn (τ.rootCertificate.root k) == List.ofFn (-Pi.single i 1 : Fin τ.rank → ℤ)) ||
      (τ.rootCertificate.roots.contains (wit.getD k 0) &&
        decide (corootPair τ i (decodeVec (wit.getD k 0)) % 2 = 0) &&
        !(List.ofFn (decodeVec (τ := τ) (wit.getD k 0)) ==
          List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ)) &&
        !(List.ofFn (decodeVec (τ := τ) (wit.getD k 0)) ==
          List.ofFn (-Pi.single i 1 : Fin τ.rank → ℤ)) &&
        !(List.ofFn (decodeVec (τ := τ) (wit.getD k 0)) == List.ofFn (τ.rootCertificate.root k)) &&
        !(List.ofFn (decodeVec (τ := τ) (wit.getD k 0)) == List.ofFn (-τ.rootCertificate.root k)) &&
        decide (iform (τ.rootCertificate.root k) (decodeVec (wit.getD k 0)) ≠ 0))

variable {τ}

theorem ofFn_beq_eq_true_iff {u v : Fin τ.rank → ℤ} :
    (List.ofFn u == List.ofFn v) = true ↔ u = v := by
  rw [beq_iff_eq]
  exact ⟨fun h => List.ofFn_injective h, fun h => h ▸ rfl⟩

theorem isRoot_iff_exists_mem_roots {v : Fin τ.rank → ℤ} :
    IsRoot τ v ↔ ∃ c ∈ τ.rootCertificate.roots, decodeVec c = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, List.getElem_mem hk, by
      rw [RootCertificate.root, List.getD_eq_getElem _ _ hk]⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
    exact ⟨k, hk, by rw [RootCertificate.root, List.getD_eq_getElem _ _ hk]⟩

variable {K : Type} [Field K]

theorem exists_of_isolatedCheck
    (hK : ringChar K ≠ 2) {i : Fin τ.rank} {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true) {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ rootCharKernel (signTuple τ K i)) (hne : δ ≠ Pi.single i 1)
    (hne' : δ ≠ -Pi.single i 1) :
    ∃ ε ∈ rootCharKernel (signTuple τ K i), ε ≠ Pi.single i 1 ∧ ε ≠ -Pi.single i 1 ∧
      ε ≠ δ ∧ ε ≠ -δ ∧ iform δ ε ≠ 0 := by
  rw [mem_rootCharKernel_signTuple hK] at hδ
  obtain ⟨hδr, heven⟩ := hδ
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hδr
  have h := List.all_eq_true.1 hc k (List.mem_range.2 hk)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ofFn_beq_eq_true_iff,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, List.contains_iff_mem] at h
  rcases h with ((h | h) | h) | ⟨⟨⟨⟨⟨⟨hmem, hev⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩
  · exact absurd (Int.even_iff.1 heven) h
  · exact absurd h hne
  · exact absurd h hne'
  · have hεr : IsRoot τ (decodeVec (wit.getD k 0)) :=
      isRoot_iff_exists_mem_roots.2 ⟨_, hmem, rfl⟩
    refine ⟨decodeVec (wit.getD k 0), (mem_rootCharKernel_signTuple hK i _).2
      ⟨hεr, Int.even_iff.2 hev⟩, ?_, ?_, ?_, ?_, h5⟩
    · exact fun h => h1 (by rw [h])
    · exact fun h => h2 (by rw [h])
    · exact fun h => h3 (by rw [h])
    · exact fun h => h4 (by rw [h])

end Check

section Datum

variable {τ : Tag} {K : Type} [Field K]

theorem rankOneGroup_adjDatum
    (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) :
    rankOneGroup (adjDatum (rootOperatorFamily τ) K) γ =
      (rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)).subgroupOf (adjointGroup τ K) := by
  change rootGroup (rootOperatorFamily τ) K γ ⊔ rootGroup (rootOperatorFamily τ) K (-γ) = _
  rw [rootGroup_of_isRoot hγ, rootGroup_of_isRoot (IsRoot.neg hγ),
    ← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K ⟨γ, hγ⟩,
    ← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K ⟨-γ, IsRoot.neg hγ⟩,
    Subgroup.subgroupOf_sup (rootSubgroup_le_adjointGroup γ)
      (rootSubgroup_le_adjointGroup (-γ))]

theorem centralizer_le_normalizer_subgroupOf {a : Fin τ.rank → Kˣ} {z : adjointGroup τ K}
    (hz : (z : ModGL τ K) = rootDiagUnit τ a) {L : Subgroup (ModGL τ K)}
    (hL : toralCentralizer τ K a ≤ Subgroup.normalizer (L : Set (ModGL τ K))) :
    Subgroup.centralizer ({z} : Set (adjointGroup τ K)) ≤
      Subgroup.normalizer ((L.subgroupOf (adjointGroup τ K) : Subgroup (adjointGroup τ K)) :
        Set (adjointGroup τ K)) := by
  intro g hg
  have hgz : z * g = g * z := (Subgroup.mem_centralizer_singleton_iff.1 hg).symm
  have hgX : (g : ModGL τ K) ∈ toralCentralizer τ K a := by
    refine mem_toralCentralizer.2 ⟨g.2, ?_⟩
    have := congrArg (fun x : adjointGroup τ K => (x : ModGL τ K)) hgz
    simp only [Subgroup.coe_mul, hz] at this
    rw [this, mul_inv_cancel_right]
  have hN := Subgroup.mem_normalizer_iff.1 (hL hgX)
  rw [Subgroup.mem_normalizer_iff]
  intro n
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hN n

theorem centralizer_le_normalizer_rankOneGroup
    (hτ : NoG2 τ) (hK : ringChar K ≠ 2)
    {i : Fin τ.rank} (hlong : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i) {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true) {z : adjointGroup τ K}
    (hz : z ∈ rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1))
    (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (adjointGroup τ K)) ≤
      Subgroup.normalizer
        ((rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1) :
          Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
  have hγ : IsRoot τ (Pi.single i 1) := isRoot_single τ i
  rw [rankOneGroup_adjDatum _ hγ] at hz ⊢
  have hzC : (z : ModGL τ K) = rootDiagUnit τ (signTuple τ K i) := by
    rw [← torusElt_neg_one_eq]
    refine eq_torusElt_neg_one hK i (Subgroup.mem_subgroupOf.1 hz) ?_
    rwa [Subgroup.orderOf_coe]
  have hlong' : ∀ ε, IsRoot τ ε → iform ε ε ≤ iform (Pi.single i 1) (Pi.single i 1) := by
    intro ε hε
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hε
    rw [hj, iform_single_single]
    linarith [hlong j]
  have hC1 : ∀ α ∈ rootCharKernel (signTuple τ K i), α ≠ Pi.single i 1 →
      α ≠ -Pi.single i 1 → iform α (Pi.single i 1) = 0 := fun α hα hne hne' =>
    iform_eq_zero_of_mem_rootCharKernel_signTuple hK hlong' hα hne hne'
  refine centralizer_le_normalizer_subgroupOf hzC
    (toralCentralizer_le_normalizer_pair hγ (fun α hα hne hne' => ?_) fun w hw => ?_)
  · exact commute_pair_of_iform_eq_zero hτ hα.1 hγ hlong' (hC1 α hα hne hne') hne hne'
  · exact smul_eq_or_eq_neg_of_mem_rootCharStabilizer
      (single_mem_rootCharKernel_signTuple hK i) hC1
      (fun δ hδ hne hne' => exists_of_isolatedCheck hK hc hδ hne hne') hw

end Datum

end CFSG.LieType.HighestRoot
