module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Torus
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.RankThree.PartOne.KE (dualWeylStabilizer dualWeylStabilizer_eq_bot_of_regular
  not_dvd_card_weylGroup_E)
open scoped MatrixGroups

theorem rootChar_zpow_tuple {τ : Tag} {M : Type} [Field M] (ζ : Mˣ) (z : Fin τ.rank → ℤ)
    (l : Fin τ.rank → ℤ) : rootChar (fun j => ζ ^ z j) l = ζ ^ (∑ j, z j * l j) := by
  simp only [rootChar, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum]


variable {τ : Tag}

theorem toralCentralizer_eq_torusGroup_of_regular (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ7 : 7 < ℓ) {ζ : Lˣ} (hζ : orderOf ζ = ℓ)
    (z : Fin τ.rank → ℤ)
    (hreg : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ¬ (ℓ : ℤ) ∣ ∑ j, z j * α j) :
    toralCentralizer τ L (fun j => ζ ^ z j) = torusGroup τ L := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set a : Fin τ.rank → Lˣ := fun j => ζ ^ z j with ha
  have hchar : ∀ l, rootChar a l = ζ ^ (∑ j, z j * l j) := rootChar_zpow_tuple ζ z
  have hone : ∀ n : ℤ, ζ ^ n = 1 ↔ (ℓ : ℤ) ∣ n := fun n => by
    rw [← hζ]
    exact orderOf_dvd_iff_zpow_eq_one.symm
  have hker : rootCharKernel a = ∅ := Set.eq_empty_of_forall_notMem fun α ⟨hα, h1⟩ =>
    hreg α hα ((hone _).1 (by rw [← hchar]; exact h1))
  set zb : Fin τ.rank → ZMod ℓ := fun j => (z j : ZMod ℓ) with hzb
  have hcv : ∀ l, CFSG.RankThree.E6.charVal zb l = ((∑ j, z j * l j : ℤ) : ZMod ℓ) := by
    intro l
    simp only [CFSG.RankThree.E6.charVal, hzb, Int.cast_sum, Int.cast_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hreg' : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → CFSG.RankThree.E6.charVal zb α ≠ 0 := by
    intro α hα h0
    rw [hcv, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    exact hreg α hα h0
  have hstab := dualWeylStabilizer_eq_bot_of_regular (not_dvd_card_weylGroup_E hℓ hℓ7 hτ) zb
    hreg'
  have hW : ∀ w ∈ rootCharStabilizer a, w = 1 := by
    intro w hw
    have hmem : w ∈ dualWeylStabilizer zb := fun y => by
      have h := hw y
      rw [hchar, hchar] at h
      rw [hcv, hcv]
      have h1 : ζ ^ ((∑ j, z j * (w • y) j) - ∑ j, z j * y j) = 1 := by
        rw [zpow_sub, h, mul_inv_cancel]
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).2 ((hone _).1 h1)
      rwa [Int.cast_sub, sub_eq_zero] at h2
    rw [hstab] at hmem
    exact Subgroup.mem_bot.1 hmem
  have h := (Chevalley_toral_centralizer_Bruhat_factors τ L a).2.2.2
  have h0 : rootSpan τ L (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
  have h1 : Subgroup.closure
      ((fun w => canonicalRep (coxeterSystem τ) L w) '' rootCharStabilizer a) = ⊥ := by
    rw [eq_bot_iff, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_bot]
    rw [hW w hw]
    exact canonicalRep_one (coxeterSystem τ) L
  rw [h, hker, h0, h1, sup_bot_eq, sup_bot_eq]

theorem commute_xOp_yOp_of_commute_baseChange (hτ : τ ≠ .G2) {K : Type} [Field K] [Finite K]
    (hK3 : 3 ≤ Nat.card K) {L : Type} [Field L] (ι : K →+* L) (i : Fin τ.rank)
    {z : Module.End L (RootModule τ L)}
    (hx : ∀ c : K, z * xOp τ L i (ι c) = xOp τ L i (ι c) * z)
    (hy : ∀ c : K, z * yOp τ L i (ι c) = yOp τ L i (ι c) * z) (t : L) :
    z * xOp τ L i t = xOp τ L i t * z ∧ z * yOp τ L i t = yOp τ L i t * z := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hD : entryDegreeBound τ < Fintype.card K := by
    simp only [entryDegreeBound, hτ, ↓reduceIte]
    rw [← Nat.card_eq_fintype_card]
    omega
  refine ⟨commute_of_polynomial_entries (F := xOp τ L i) (fun a b => ?_) z ι ι.injective hD hx t,
    commute_of_polynomial_entries (F := yOp τ L i) (fun a b => ?_) z ι ι.injective hD hy t⟩
  · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
    exact ⟨p, hp, fun c => (hpq c).1⟩
  · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
    exact ⟨q, hq, fun c => (hpq c).2⟩

theorem commute_conj_torusElt_of_commute (hτ : τ ≠ .G2) {K : Type} [Field K] [Finite K]
    (hK3 : 3 ≤ Nat.card K) {L : Type} [Field L] (ι : K →+* L) (w : WeylGroup τ)
    (i : Fin τ.rank) {x : ModGL τ L}
    (hxc : ∀ c : K, Commute x (baseChangeGL ι (canonicalRep (coxeterSystem τ) K w *
      xUnit τ K i c * (canonicalRep (coxeterSystem τ) K w)⁻¹)))
    (hyc : ∀ c : K, Commute x (baseChangeGL ι (canonicalRep (coxeterSystem τ) K w *
      yUnit τ K i c * (canonicalRep (coxeterSystem τ) K w)⁻¹)))
    (s : Lˣ) : Commute x (canonicalRep (coxeterSystem τ) L w * torusElt τ L i s *
      (canonicalRep (coxeterSystem τ) L w)⁻¹) := by
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hnK : baseChangeGL ι (canonicalRep (coxeterSystem τ) K w) = n :=
    baseChangeGL_canonicalRep ι w
  set y := n⁻¹ * x * n with hy
  have hconj : ∀ g : ModGL τ L, Commute x (n * g * n⁻¹) ↔ Commute y g := by
    intro g
    have e : x = n * y * n⁻¹ := by rw [hy]; group
    rw [e, Commute.conj_iff]
  have hx' : ∀ c : K, Commute y (xUnit τ L i (ι c)) := fun c => by
    have h := hxc c
    rw [map_mul, map_mul, map_inv, hnK, baseChangeGL_xUnit] at h
    exact (hconj _).1 h
  have hy' : ∀ c : K, Commute y (yUnit τ L i (ι c)) := fun c => by
    have h := hyc c
    rw [map_mul, map_mul, map_inv, hnK, baseChangeGL_yUnit] at h
    exact (hconj _).1 h
  have hall := commute_xOp_yOp_of_commute_baseChange hτ hK3 ι i (z := (y : Module.End L _))
    (fun c => congrArg Units.val (hx' c).eq) (fun c => congrArg Units.val (hy' c).eq)
  have hle : Subgroup.closure (Set.range (xUnit τ L i) ∪ Set.range (yUnit τ L i)) ≤
      Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    · exact Units.ext (hall t).1.symm
    · exact Units.ext (hall t).2.symm
  have hT : torusElt τ L i s ∈
      Subgroup.closure (Set.range (xUnit τ L i) ∪ Set.range (yUnit τ L i)) := by
    rw [← range_simpleRootSL2]
    exact ⟨HSL s, simpleRootSL2_HSL i s⟩
  refine (hconj _).2 ?_
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hT)).symm

@[expose] def regCoweight (Γ : List ((Fin τ.rank → ℤ) × ℤ)) (j : Fin τ.rank) : ℤ :=
  (Γ.map fun y => y.2 * corootPair y.1 (Pi.single j 1)).sum

theorem exists_commute_torus_prod {M : Type} [Field M] {x : ModGL τ M} (ζ : Mˣ)
    (Γ : List ((Fin τ.rank → ℤ) × ℤ))
    (h : ∀ y ∈ Γ, ∃ (w : WeylGroup τ) (k : Fin τ.rank),
      w • (Pi.single k 1 : Fin τ.rank → ℤ) = y.1 ∧ ∀ s : Mˣ, Commute x
        (canonicalRep (coxeterSystem τ) M w * torusElt τ M k s *
          (canonicalRep (coxeterSystem τ) M w)⁻¹)) :
    ∃ P ∈ torusGroup τ M, Commute x P ∧ ∀ j : Fin τ.rank,
      torusRootChar P (Pi.single j 1) = ((ζ ^ regCoweight Γ j : Mˣ) : M) := by
  induction Γ with
  | nil =>
    refine ⟨1, one_mem _, Commute.one_right x, fun j => ?_⟩
    rw [torusRootChar_one]
    simp [regCoweight]
  | cons y Γ ih =>
    obtain ⟨P, hPT, hxP, hPχ⟩ := ih fun y' hy' => h y' (List.mem_cons_of_mem y hy')
    obtain ⟨w, k, hwk, hc⟩ := h y List.mem_cons_self
    set Q := canonicalRep (coxeterSystem τ) M w * torusElt τ M k (ζ ^ y.2) *
      (canonicalRep (coxeterSystem τ) M w)⁻¹ with hQ
    have hQT : Q ∈ torusGroup τ M :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w) _).1
        (torusElt_mem_torusGroup k _)
    refine ⟨Q * P, mul_mem hQT hPT, (hc _).mul_right hxP, fun j => ?_⟩
    rw [torusRootChar_mul (torusGroup_le_diagonalGroup hQT) (torusGroup_le_diagonalGroup hPT),
      hPχ j, hQ, torusRootChar_conj_torusElt w k _ (isRoot_single τ j), hwk]
    simp only [regCoweight, List.map_cons, List.sum_cons, zpow_add, ← zpow_mul, Units.val_mul]

theorem torusRootChar_baseChangeGL {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (g : ModGL τ K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (baseChangeGL ι g) α = ι (torusRootChar g α) := by
  rw [torusRootChar, torusRootChar, dite_eq_left hα, dite_eq_left hα, rootVec_eq_single hα,
    rootVec_eq_single hα, baseChangeGL_apply_single, Finsupp.mapRange_apply]

theorem exists_eq_rootDiagAut_of_fix_rootPairs (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {η : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hηg : ∀ h : adjointGroup τ K, (η h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (Γ : List ((Fin τ.rank → ℤ) × ℤ)) (hΓ : ∀ y ∈ Γ, IsRoot τ y.1)
    (hfix : ∀ y ∈ Γ, ∀ u : adjointGroup τ K,
      (u : ModGL τ K) ∈ rootSubgroup τ K y.1 ⊔ rootSubgroup τ K (-y.1) → η u = u)
    (B : ℕ) (hreg : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      (∑ j, regCoweight Γ j * α j) ≠ 0 ∧ (∑ j, regCoweight Γ j * α j).natAbs < B) :
    ∃ e : Fin τ.rank → Kˣ, η = rootDiagAut τ K e := by
  classical
  have hτ2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl <;> decide
  have : Fintype K := Fintype.ofFinite K
  have hKodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK
  have hK3 : 3 ≤ Nat.card K := by
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨m, hm⟩ := hKodd
    omega
  set L := AlgebraicClosure K
  set ι : K →+* L := algebraMap K L with hι
  set p := ringChar K with hp
  have hpK : CharP K p := ringChar.charP K
  have hpp : p.Prime := CharP.char_is_prime K p
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (B + p + 8)
  have hℓ7 : 7 < ℓ := by omega
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0
    have hdvd : p ∣ ℓ := (CharP.cast_eq_zero_iff K p ℓ).1 h0
    have := (Nat.prime_dvd_prime_iff_eq hpp hℓ).1 hdvd
    omega
  have : NeZero (ℓ : K) := ⟨hℓK⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L ℓ
  set ζ : Lˣ := (hζ₀.isUnit hℓ.ne_zero).unit with hζdef
  have hζ : orderOf ζ = ℓ := by
    have h1 : IsPrimitiveRoot ζ ℓ := IsPrimitiveRoot.coe_units_iff.1 hζ₀
    exact h1.eq_orderOf.symm
  set aL : Fin τ.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i) with haL
  set x : ModGL τ L := baseChangeGL ι (g : ModGL τ K) * rootDiagUnit τ aL with hx
  obtain ⟨-, hHG, -, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness τ K hKodd L ι
  have hgL : baseChangeGL ι (g : ModGL τ K) ∈ adjointGroup τ L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup τ L :=
    mul_mem hgL (exceptional_Lang_adjoint_diagonal_lift τ L aL).1
  have hdb : baseChangeGL ι (rootDiagUnit τ a) = rootDiagUnit τ aL := baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup τ K,
      x * baseChangeGL ι (h : ModGL τ K) * x⁻¹ = baseChangeGL ι (η h : ModGL τ K) := by
    intro h
    rw [hηg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx]
    group
  have hcomm : ∀ u : adjointGroup τ K, η u = u → Commute x (baseChangeGL ι (u : ModGL τ K)) := by
    intro u hu
    have h := hxconj u
    rw [hu] at h
    calc x * baseChangeGL ι (u : ModGL τ K) =
        x * baseChangeGL ι (u : ModGL τ K) * x⁻¹ * x := by group
      _ = baseChangeGL ι (u : ModGL τ K) * x := by rw [h]
  have hroot : ∀ y ∈ Γ, ∃ (w : WeylGroup τ) (k : Fin τ.rank),
      w • (Pi.single k 1 : Fin τ.rank → ℤ) = y.1 ∧ ∀ s : Lˣ, Commute x
        (canonicalRep (coxeterSystem τ) L w * torusElt τ L k s *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) := by
    intro y hy
    obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 (hΓ y hy)
    obtain ⟨-, -, hQ, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK (hΓ y hy)
    have hQmap := (hQ w k hwk).1
    set n := canonicalRep (coxeterSystem τ) K w with hn
    have hnC : n ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w
    refine ⟨w, k, hwk, commute_conj_torusElt_of_commute hτ2 hK3 ι w k (fun c => ?_)
      (fun c => ?_)⟩
    · have huC : n * xUnit τ K k c * n⁻¹ ∈ adjointGroup τ K :=
        mul_mem (mul_mem hnC (xUnit_mem_adjointGroup k c)) (inv_mem hnC)
      have hmem : n * xUnit τ K k c * n⁻¹ ∈ rootSubgroup τ K y.1 ⊔ rootSubgroup τ K (-y.1) := by
        rw [← hQmap]
        exact ⟨xUnit τ K k c, Subgroup.subset_closure (Or.inl ⟨c, rfl⟩), rfl⟩
      exact hcomm ⟨_, huC⟩ (hfix y hy ⟨_, huC⟩ hmem)
    · have huC : n * yUnit τ K k c * n⁻¹ ∈ adjointGroup τ K :=
        mul_mem (mul_mem hnC (yUnit_mem_adjointGroup k c)) (inv_mem hnC)
      have hmem : n * yUnit τ K k c * n⁻¹ ∈ rootSubgroup τ K y.1 ⊔ rootSubgroup τ K (-y.1) := by
        rw [← hQmap]
        exact ⟨yUnit τ K k c, Subgroup.subset_closure (Or.inr ⟨c, rfl⟩), rfl⟩
      exact hcomm ⟨_, huC⟩ (hfix y hy ⟨_, huC⟩ hmem)
  obtain ⟨P, hPT, hxP, hPχ⟩ := exists_commute_torus_prod ζ Γ hroot
  set z := regCoweight Γ with hz
  have hdz : rootDiagUnit τ (fun j => ζ ^ z j) ∈ torusGroup τ L := by
    obtain ⟨-, t, ht⟩ := exceptional_Lang_adjoint_diagonal_lift τ L (fun j => ζ ^ z j)
    rw [ht]
    refine Subgroup.list_prod_mem _ fun q hq => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hq
    exact torusElt_mem_torusGroup j _
  have hPeq : P = rootDiagUnit τ (fun j => ζ ^ z j) := eq_of_torusRootChar_single hPT hdz
    fun j => by rw [hPχ j, torusRootChar_rootDiagUnit _ (isRoot_single τ j), rootChar_single']
  have hxT : x ∈ torusGroup τ L := by
    rw [← toralCentralizer_eq_torusGroup_of_regular hτ hℓ hℓ7 hζ z fun α hα hdvd => ?_]
    · refine Subgroup.mem_inf.2 ⟨hxG, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hPeq]
      exact hxP.eq
    · obtain ⟨hne, hlt⟩ := hreg α hα
      have h1 : ℓ ∣ (∑ j, z j * α j).natAbs := Int.natCast_dvd.1 hdvd
      have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hne) h1
      omega
  obtain ⟨f, hf⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
  have hgd : baseChangeGL ι (g : ModGL τ K) = rootDiagUnit τ (f * aL⁻¹) := by
    rw [rootDiagUnit_mul, ← rootDiagUnit_inv, ← hf, hx, mul_inv_cancel_right]
  have hev : ∀ j, (((f * aL⁻¹) j : Lˣ) : L) =
      ι (torusRootChar (g : ModGL τ K) (Pi.single j 1)) := by
    intro j
    rw [← torusRootChar_baseChangeGL ι _ (isRoot_single τ j), hgd,
      torusRootChar_rootDiagUnit _ (isRoot_single τ j), rootChar_single']
  have hne : ∀ j, torusRootChar (g : ModGL τ K) (Pi.single j 1) ≠ 0 := fun j h0 => by
    have h1 := hev j
    rw [h0, map_zero] at h1
    exact Units.ne_zero _ h1
  set e : Fin τ.rank → Kˣ := fun j => Units.mk0 _ (hne j) with he
  have hge : (g : ModGL τ K) = rootDiagUnit τ e := by
    apply baseChangeGL_injective ι
    rw [hgd, baseChangeGL_rootDiagUnit]
    congr 1
    funext j
    exact Units.ext ((hev j).trans rfl)
  refine ⟨e * a, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hηg h, coe_rootDiagAut, hge, rootDiagUnit_mul]
  group

end CFSG.ComponentClassification.Burgoyne.E2
