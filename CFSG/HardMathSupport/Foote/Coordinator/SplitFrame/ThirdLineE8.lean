module

public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.ThirdLineF4

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec weylMatrix_pow)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise

section Main


theorem ncard_isRoot_E8 : {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α}.ncard = 240 := by
  have h : {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α} = ↑(rootFinset .E8) := by
    ext α
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact mem_rootFinset.symm
  rw [h, Set.ncard_coe_finset, card_rootFinset]
  rfl

theorem exists_offLine_nonsolvable_E8_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 < p) (hp7 : 7 < p) (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = 5)
    (hpq : ¬ p ∣ Nat.card K)
    (hΦ : (((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 4 +
      (((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 +
      (((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      (((1 : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = ((1 : ℤ) • weylMatrix e8F5U) *ᵥ u)
    (E : Subgroup (adjointGroup .E8 K)) (hEc : Nat.card E = p ^ 2)
    (hEp : ∀ x ∈ E, x ^ p = 1) {a b : adjointGroup .E8 K} (haE : a ∈ E) (hbE : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
      ∃ P : Subgroup (adjointGroup .E8 K),
        P ≤ Subgroup.centralizer ({e} : Set (adjointGroup .E8 K)) ∧ ¬ Group.IsSolvable ↥P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hT : twistedTorusOf n Φ =
      (fixedCharTuples (e8FiveM 1) Fr).map (rootDiagUnitHom .E8 L) := by
    have h := twistedFixedTuples_eq_fixedCharTuples hnW Fr
    rw [show e8FiveM 1 = (1 : ℤ) • weylMatrix e8F5U from rfl, ← h]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G4 := fixedBlockTuples (e8FiveM 1) Fr
    (e8FiveCols 4 1 '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG4
  set G0 := fixedBlockTuples (e8FiveM 1) Fr
    (e8FiveCols 0 1 '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG0
  set N : ℕ := (((Nat.card K : ℤ) ^ 4 + 1 * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
    1 * (Nat.card K : ℤ) + 1).natAbs) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G4 ⊔ G0).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8Five_card_sup 1 (Or.inl rfl) Fr hFr hℓ hℓq hq2
  have hN : N ≠ 0 := by
    refine pow_ne_zero 2 (Int.natAbs_ne_zero.2 ?_)
    have := e8FiveP_eval_ne_zero 1 (Or.inl rfl) hq2
    rwa [e8FiveP_eval] at this
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8Five_ordProj K 1 (Or.inl rfl) hp hp5 (Or.inl rfl) hordq hpq hΦ
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp (by omega) n hnC Z0 hZ0le hN hZ0card hord
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; positivity)
  obtain ⟨c, hc⟩ := hconj E (IsPGroup.of_card hEc)
  let φ : E →* ModGL .E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb .E8 K L).comp ((MulAut.conj c).toMonoidHom.comp E.subtype))
  have hφ : ∀ x : E, φ x =
      g0⁻¹ * adjEmb .E8 K L (c * (x : adjointGroup .E8 K) * c⁻¹) * g0 := fun x => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ :=
    (MulAut.conj g0⁻¹).injective.comp (adjEmb_injective.comp
      ((MulAut.conj c).injective.comp E.subtype_injective))
  have hφT : ∀ x : E, φ x ∈ twistedTorusOf n Φ := fun x => by
    rw [hφ]
    exact hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc x x.2))
  choose β hβ using fun x : E =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT x)).1 :
      ∃ b : Fin Tag.E8.rank → Lˣ, φ x = rootDiagUnit .E8 b)
  have hβmul : ∀ x y : E, β (x * y) = β x * β y := fun x y => by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  let βh : E →* (Fin Tag.E8.rank → Lˣ) :=
    { toFun := β, map_one' := hβone, map_mul' := hβmul }
  have hβinj : Function.Injective β := fun x y h => hφinj (by rw [hβ, hβ, h])
  have hβfix : ∀ x : E, β x ∈ fixedCharTuples (e8FiveM 1) Fr := fun x => by
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
  let χ : (Fin Tag.E8.rank → ℤ) → (E →* Lˣ) := fun α =>
    { toFun := fun x => rootChar (β x) α
      map_one' := by rw [hβone]; exact CTTorus.rootChar_one α
      map_mul' := fun x y => by rw [hβmul, CTTorus.rootChar_mul] }
  have hχ : ∀ α (x : E), χ α x = rootChar (β x) α := fun _ _ => rfl
  have hχp : ∀ α (x : E), χ α x ^ p = 1 := fun α x => CTTorus.rootChar_pow_eq_one (hβp x) α
  have hker : ∀ α, ∃ x : E, x ≠ 1 ∧ χ α x = 1 := fun α =>
    exists_ne_one_ker_of_card_sq hp hEc (χ α) (hχp α)
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
  have hsmall : ∀ x : E, x ≠ 1 → (rootCharKernel (β x)).ncard ≤ 25 := by
    intro x hx1
    have hβ1 : β x ≠ 1 := fun h => hx1 (hβinj (by rw [h, hβone]))
    rcases e8Five_kernel_of_fixed 1 (Or.inl rfl) Fr hFr hp hp5 hΦ (hβfix x) (hβp x) hβ1 with
      h0 | ⟨v, hS, -⟩
    · rw [h0, Set.ncard_empty]
      omega
    · rw [hS]
      have hsub : sigmaSetE8A4 v ⊆
          Set.range (fun ij : Fin 5 × Fin 5 => sigmaRootE8A4 v ij.1 ij.2) := by
        intro r hr
        obtain ⟨i, j, -, rfl⟩ := mem_sigmaSetE8A4_iff.1 hr
        exact ⟨(i, j), rfl⟩
      calc _ ≤ (Set.range (fun ij : Fin 5 × Fin 5 => sigmaRootE8A4 v ij.1 ij.2)).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_range _)
        _ ≤ (Set.univ : Set (Fin 5 × Fin 5)).ncard := by
            rw [← Set.image_univ]
            exact Set.ncard_image_le Set.finite_univ
        _ = 25 := by rw [Set.ncard_univ]; simp
  have hfinK : ∀ x : E, x ≠ 1 → (rootCharKernel (β x)).Finite := by
    intro x hx1
    by_contra hinf
    have := Set.Infinite.ncard hinf
    have h25 := hsmall x hx1
    have hsub : rootCharKernel (β x) ⊆ ↑(rootFinset .E8) := fun α hα => mem_rootFinset.2 hα.1
    exact hinf ((rootFinset .E8).finite_toSet.subset hsub)
  set a' : E := ⟨a, haE⟩ with ha'
  set b' : E := ⟨b, hbE⟩ with hb'
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hoff : ∃ α, IsRoot .E8 α ∧ ∃ x : E, x ≠ 1 ∧ χ α x = 1 ∧ x ∉ Subgroup.zpowers a' ∧
      x ∉ Subgroup.zpowers b' := by
    by_contra hcon
    push Not at hcon
    have hcover : {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α} ⊆
        rootCharKernel (β a') ∪ rootCharKernel (β b') := by
      intro α hα
      obtain ⟨x, hx1, hxα⟩ := hker α
      by_cases hxa : x ∈ Subgroup.zpowers a'
      · exact Or.inl ⟨hα, hpow a' x hx1 hxa α hxα⟩
      · exact Or.inr ⟨hα, hpow b' x hx1 (hcon α hα x hx1 hxα hxa) α hxα⟩
    have h240 := ncard_isRoot_E8
    have hle := Set.ncard_le_ncard hcover ((hfinK a' ha'1).union (hfinK b' hb'1))
    have hun := Set.ncard_union_le (rootCharKernel (β a')) (rootCharKernel (β b'))
    have h1 := hsmall a' ha'1
    have h2 := hsmall b' hb'1
    omega
  obtain ⟨α, hαr, x, hx1, hxα, hxa, hxb⟩ := hoff
  set e : adjointGroup .E8 K := (x : adjointGroup .E8 K) with hedef
  have he1 : e ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hep : e ^ p = 1 := hEp e x.2
  have he : orderOf e = p := orderOf_eq_prime hep he1
  have hh : g0⁻¹ * adjEmb .E8 K L (c * e * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    rw [← hφ x]
    exact hφT x
  obtain ⟨ψ, hψinj, -, -, hψK⟩ := e8_five_perx K hf hK 1 (Or.inl rfl) hp hp5 hp7 hΦ L n hnm hnW g0
    hg0C hg0 hperf hT he c hh
  have hb : rootDiagUnit .E8 (β x) = g0⁻¹ * adjEmb .E8 K L (c * e * c⁻¹) * g0 := by
    rw [← hβ, hφ]
  obtain ⟨Pt, hPq, hcomm, -⟩ := hψK (β x) hb ⟨α, hαr, hxα⟩
  refine ⟨e, x.2, fun h => hxa ?_, fun h => hxb ?_, ?_⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  refine ⟨(commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .E8 K)))).map
    (Subgroup.centralizer ({e} : Set (adjointGroup .E8 K))).subtype,
    Subgroup.map_subtype_le _, fun hs => ?_⟩
  have hs1 : Group.IsSolvable
      ↥(commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .E8 K)))) := by
    have := hs
    let e1 := Subgroup.equivMapOfInjective
      (commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .E8 K))))
      (Subgroup.centralizer ({e} : Set (adjointGroup .E8 K))).subtype
      (Subgroup.centralizer ({e} : Set (adjointGroup .E8 K))).subtype_injective
    exact Group.isSolvable_of_surjective (f := e1.symm.toMonoidHom) e1.symm.surjective
  have hmap : (commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .E8 K)))).map ψ =
      Pt := by
    rw [← hcomm, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  have hs2 : Group.IsSolvable
      ↥((commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .E8 K)))).map ψ) := by
    have := hs1
    let e2 := Subgroup.equivMapOfInjective
      (commutator ↥(Subgroup.centralizer ({e} : Set (adjointGroup .E8 K)))) ψ hψinj
    exact Group.isSolvable_of_surjective (f := e2.toMonoidHom) e2.surjective
  rw [hmap] at hs2
  exact not_isSolvable_of_isQuasisimple' hPq hs2

theorem exists_offLine_nonsolvable_E8 (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = 5)
    (E : Subgroup (adjointGroup .E8 K)) (hEc : Nat.card E = p ^ 2)
    (hEp : ∀ x ∈ E, x ^ p = 1) {a b : adjointGroup .E8 K} (haE : a ∈ E) (hbE : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
      ∃ P : Subgroup (adjointGroup .E8 K),
        P ≤ Subgroup.centralizer ({e} : Set (adjointGroup .E8 K)) ∧ ¬ Group.IsSolvable ↥P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hcm := canonicalRep_mem_monomialSubgroup L e8F5U
  have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8F5U, hcm⟩ = e8F5U :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e8F5U)
  have hnW : ∀ u, weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8F5U, hcm⟩ • u =
      ((1 : ℤ) • weylMatrix e8F5U) *ᵥ u := fun u => by
    rw [hπ, one_smul, weylMatrix_mulVec]
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    intro h
    rw [h, orderOf_eq_zero_iff'.2] at hordq
    · exact absurd hordq (by norm_num)
    · intro n hn h'
      rw [zero_pow hn.ne'] at h'
      exact zero_ne_one h'
  have hpq : ¬ p ∣ Nat.card K := fun h =>
    hq0 ((ZMod.natCast_eq_zero_iff _ _).2 h)
  have h5 : ((Nat.card K : ℕ) : ZMod p) ^ 5 = 1 := hordq ▸ pow_orderOf_eq_one _
  have h1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordq
    exact absurd hordq (by norm_num)
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 + ((Nat.card K : ℕ) : ZMod p) ^ 3 +
      ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
    have hmul : (((Nat.card K : ℕ) : ZMod p) - 1) * (((Nat.card K : ℕ) : ZMod p) ^ 4 +
        ((Nat.card K : ℕ) : ZMod p) ^ 3 + ((Nat.card K : ℕ) : ZMod p) ^ 2 +
        ((Nat.card K : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · exact h
  exact exists_offLine_nonsolvable_E8_aux K hf hK hp (by omega) hp7 hordq hpq
    (e8Five_hΦ_one _ hΦ) L _ hcm hnW E hEc hEp haE hbE ha1 hb1

end Main

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
