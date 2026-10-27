module

public import CFSG.RankThree.PartOne.KF4.F4ThreeData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec weylMatrix_pow)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
open scoped Matrix Pointwise

theorem not_isSolvable_of_isQuasisimple' {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  obtain ⟨hperf, -, a, b, hab⟩ := h
  have : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hs : ∀ u v : G ⧸ Subgroup.center G, u = v := fun u v => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
      rw [Subsingleton.elim x y]
    exact hab (hs _ _)
  exact Group.IsPerfect.not_isSolvable G

section Main


theorem ncard_isRoot_F4 : {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α}.ncard = 48 := by
  have h : {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α} = ↑(rootFinset .F4) := by
    ext α
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact mem_rootFinset.symm
  rw [h, Set.ncard_coe_finset, card_rootFinset]
  rfl

theorem exists_offLine_nonsolvable_F4_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p)
    (hΦ : (((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      ((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .F4 L) (hnm : n ∈ monomialSubgroup .F4 L)
    (hnW : ∀ u, weylQuotientHom .F4 L ⟨n, hnm⟩ • u = ((1 : ℤ) • weylMatrix f4W3) *ᵥ u)
    (E : Subgroup (adjointGroup .F4 K)) (hEc : Nat.card E = p ^ 2)
    (hEp : ∀ x ∈ E, x ^ p = 1) {a b : adjointGroup .F4 K} (haE : a ∈ E) (hbE : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
      ∃ P : Subgroup (adjointGroup .F4 K),
        P ≤ Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)) ∧ ¬ Group.IsSolvable ↥P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .F4 L →* ModGL .F4 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .F4 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .F4 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ =
      (fixedCharTuples (f4ThreeM 1) Fr).map (rootDiagUnitHom .F4 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show f4ThreeM 1 = (1 : ℤ) • weylMatrix f4W3 from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set N : ℕ := (((Nat.card K : ℤ) ^ 2 + 1 * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .F4 L) := (f4ThreeZ 1 Fr).map (rootDiagUnitHom .F4 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact f4Three_card_Z 1 (Or.inl rfl) Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := f4ThreeP_eval_ne_zero 1 (Or.inl rfl) hq2
    rwa [f4ThreeP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .F4 K)).factorization p = p ^ N.factorization p :=
    f4Three_ordProj K 1 (Or.inl rfl) hp hp3 hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow_F4 K hf hK L hp hp3 n hnC Z0
    hZ0le hN hZ0card hord
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; positivity)
  obtain ⟨c, hc⟩ := hconj E (IsPGroup.of_card hEc)
  let φ : E →* ModGL .F4 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .F4 K L).comp ((MulAut.conj c).toMonoidHom.comp E.subtype))
  have hφ : ∀ x : E, φ x =
      g0⁻¹ * adjEmb .F4 K L (c * (x : adjointGroup .F4 K) * c⁻¹) * g0 := fun x => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ :=
    (MulAut.conj g0⁻¹).injective.comp (adjEmb_injective.comp
      ((MulAut.conj c).injective.comp E.subtype_injective))
  have hφT : ∀ x : E, φ x ∈ twistedTorusOf n Φ := fun x => by
    rw [hφ]
    exact hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x x.2))
  choose β hβ using fun x : E =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT x)).1 :
      ∃ b : Fin Tag.F4.rank → Lˣ, φ x = rootDiagUnit .F4 b)
  have hβmul : ∀ x y : E, β (x * y) = β x * β y := fun x y => by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .F4) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  let βh : E →* (Fin Tag.F4.rank → Lˣ) :=
    { toFun := β, map_one' := hβone, map_mul' := hβmul }
  have hβinj : Function.Injective β := fun x y h => hφinj (by rw [hβ, hβ, h])
  have hβfix : ∀ x : E, β x ∈ fixedCharTuples (f4ThreeM 1) Fr := fun x => by
    have h := hφT x
    rw [hT, hβ] at h
    obtain ⟨b', hb', hb'e⟩ := h
    have : b' = β x := hinj0 hb'e
    rw [← this]
    exact hb'
  have hxp : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hEp x x.2)
  have hβp : ∀ x : E, ∀ i, β x i ^ p = 1 := fun x i => by
    have h : β x ^ p = 1 := by
      have h0 : βh (x ^ p) = βh x ^ p := map_pow βh x p
      rw [hxp, map_one] at h0
      exact h0.symm
    simpa using congrFun h i
  let χ : (Fin Tag.F4.rank → ℤ) → (E →* Lˣ) := fun α =>
    { toFun := fun x => rootChar (β x) α
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α
      map_mul' := fun x y => by rw [hβmul, CTTorus.rootChar_mul] }
  have hχ : ∀ α (x : E), χ α x = rootChar (β x) α := fun _ _ => rfl
  have hχp : ∀ α (x : E), χ α x ^ p = 1 := fun α x => CTTorus.rootChar_pow_eq_one (hβp x) α
  have hker : ∀ α, ∃ x : E, x ≠ 1 ∧ χ α x = 1 := fun α =>
    exists_ne_one_ker_of_card_sq' hp hEc (χ α) (hχp α)
  have hpow : ∀ (g x : E), x ≠ 1 → x ∈ Subgroup.zpowers g → ∀ α, χ α x = 1 → χ α g = 1 := by
    intro g x hx1 hxg α hα
    obtain ⟨k, rfl⟩ := hxg
    by_contra hne
    have hord' : orderOf (χ α g) = p := orderOf_eq_prime (hχp α g) hne
    have hk : χ α g ^ k = 1 := by rw [← map_zpow]; exact hα
    have hpk : (p : ℤ) ∣ k := by
      rw [← hord']
      exact orderOf_dvd_iff_zpow_eq_one.2 hk
    obtain ⟨m, hm⟩ := hpk
    apply hx1
    show g ^ k = 1
    rw [hm, _root_.zpow_mul, zpow_natCast, hxp, _root_.one_zpow]
  have hsmall : ∀ x : E, x ≠ 1 → (rootCharKernel (β x)).ncard ≤ 9 := by
    intro x hx1
    have hβ1 : β x ≠ 1 := fun h => hx1 (hβinj (by rw [h, hβone]))
    have hfin : ∀ (g : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ),
        {r | ∃ i j : Fin 3, i ≠ j ∧ r = g i j}.ncard ≤ 9 := by
      intro g
      have hsub : {r | ∃ i j : Fin 3, i ≠ j ∧ r = g i j} ⊆
          Set.range (fun ij : Fin 3 × Fin 3 => g ij.1 ij.2) := by
        rintro r ⟨i, j, -, rfl⟩
        exact ⟨(i, j), rfl⟩
      calc _ ≤ (Set.range (fun ij : Fin 3 × Fin 3 => g ij.1 ij.2)).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_range _)
        _ ≤ (Set.univ : Set (Fin 3 × Fin 3)).ncard := by
            rw [← Set.image_univ]
            exact Set.ncard_image_le Set.finite_univ
        _ = 9 := by rw [Set.ncard_univ]; simp
    rcases f4Three_kernel_of_fixed 1 (Or.inl rfl) Fr hFr hp hp3 (hβfix x) (hβp x) hβ1 with
      h0 | ⟨v, ⟨hS, -⟩ | ⟨hS, -⟩⟩
    · rw [h0, Set.ncard_empty]
      omega
    · rw [hS]
      exact hfin _
    · rw [hS]
      exact hfin _
  have hfinK : ∀ x : E, x ≠ 1 → (rootCharKernel (β x)).Finite := by
    intro x hx1
    by_contra hinf
    have := Set.Infinite.ncard hinf
    have h9 := hsmall x hx1
    have hsub : rootCharKernel (β x) ⊆ ↑(rootFinset .F4) := fun α hα => mem_rootFinset.2 hα.1
    exact hinf ((rootFinset .F4).finite_toSet.subset hsub)
  set a' : E := ⟨a, haE⟩ with ha'
  set b' : E := ⟨b, hbE⟩ with hb'
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hoff : ∃ α, IsRoot .F4 α ∧ ∃ x : E, x ≠ 1 ∧ χ α x = 1 ∧ x ∉ Subgroup.zpowers a' ∧
      x ∉ Subgroup.zpowers b' := by
    by_contra hcon
    push Not at hcon
    have hcover : {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α} ⊆
        rootCharKernel (β a') ∪ rootCharKernel (β b') := by
      intro α hα
      obtain ⟨x, hx1, hxα⟩ := hker α
      by_cases hxa : x ∈ Subgroup.zpowers a'
      · exact Or.inl ⟨hα, hpow a' x hx1 hxa α hxα⟩
      · exact Or.inr ⟨hα, hpow b' x hx1 (hcon α hα x hx1 hxα hxa) α hxα⟩
    have h48 := ncard_isRoot_F4
    have hle := Set.ncard_le_ncard hcover ((hfinK a' ha'1).union (hfinK b' hb'1))
    have hun := Set.ncard_union_le (rootCharKernel (β a')) (rootCharKernel (β b'))
    have h1 := hsmall a' ha'1
    have h2 := hsmall b' hb'1
    omega
  obtain ⟨α, hαr, x, hx1, hxα, hxa, hxb⟩ := hoff
  set e : adjointGroup .F4 K := (x : adjointGroup .F4 K) with hedef
  have he1 : e ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hep : e ^ p = 1 := hEp e x.2
  have he : orderOf e = p := orderOf_eq_prime hep he1
  have hh : g0⁻¹ * adjEmb .F4 K L (c * e * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ x]
    exact hφT x
  obtain ⟨ψ, hψinj, -, -, hψK⟩ := f4_three_perx K hf hK 1 (Or.inl rfl) (fun h => absurd h (by decide))
    hp hp3 L n hnm hnW g0 hg0C hg0 hperf hT he c hh
  have hb : rootDiagUnit .F4 (β x) = g0⁻¹ * adjEmb .F4 K L (c * e * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  obtain ⟨Pt, hPq, hcomm, -⟩ := hψK (β x) hb ⟨α, hαr, hxα⟩
  refine ⟨e, x.2, fun h => hxa ?_, fun h => hxb ?_, ?_⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  refine ⟨(commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)))).map
    (Subgroup.centralizer ({e} : Set (adjointGroup .F4 K))).subtype,
    Subgroup.map_subtype_le _, fun hs => ?_⟩
  have hs1 : Group.IsSolvable
      ↥(commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)))) := by
    have := hs
    let e1 := Subgroup.equivMapOfInjective
      (commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .F4 K))))
      (Subgroup.centralizer ({e} : Set (adjointGroup .F4 K))).subtype
      (Subgroup.centralizer ({e} : Set (adjointGroup .F4 K))).subtype_injective
    exact Group.isSolvable_of_surjective (f := e1.symm.toMonoidHom) e1.symm.surjective
  have hmap : (commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)))).map ψ =
      Pt := by
    rw [← hcomm, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  have hs2 : Group.IsSolvable
      ↥((commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)))).map ψ) := by
    have := hs1
    let e2 := Subgroup.equivMapOfInjective
      (commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)))) ψ hψinj
    exact Group.isSolvable_of_surjective (f := e2.toMonoidHom) e2.surjective
  rw [hmap] at hs2
  exact not_isSolvable_of_isQuasisimple' hPq hs2

theorem exists_offLine_nonsolvable_F4 (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0)
    (E : Subgroup (adjointGroup .F4 K)) (hEc : Nat.card E = p ^ 2)
    (hEp : ∀ x ∈ E, x ^ p = 1) {a b : adjointGroup .F4 K} (haE : a ∈ E) (hbE : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
      ∃ P : Subgroup (adjointGroup .F4 K),
        P ≤ Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)) ∧ ¬ Group.IsSolvable ↥P := by
  classical
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hcm := canonicalRep_mem_monomialSubgroup L f4W3
  have hπ : weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W3, hcm⟩ = f4W3 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep f4W3)
  have hnW : ∀ u, weylQuotientHom .F4 L ⟨canonicalRep (coxeterSystem .F4) L f4W3, hcm⟩ • u =
      ((1 : ℤ) • weylMatrix f4W3) *ᵥ u := fun u => by
    rw [hπ, one_smul, weylMatrix_mulVec]
  exact exists_offLine_nonsolvable_F4_aux K hf hK hp hp3 (f4Three_hΦ_one _ hΦ) L _ hcm hnW E hEc
    hEp haE hbE ha1 hb1

end Main

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
