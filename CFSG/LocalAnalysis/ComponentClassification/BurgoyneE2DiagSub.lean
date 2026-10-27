module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Diag

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped MatrixGroups


variable {τ : Tag}

theorem exists_rootDiagUnit_eq_of_commute_subfield (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (ι₀ : k →+* K) {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (Γ : List ((Fin τ.rank → ℤ) × ℤ)) (hΓ : ∀ y ∈ Γ, IsRoot τ y.1)
    (hcomm : ∀ y ∈ Γ, ∀ u : ModGL τ k, u ∈ rootSubgroup τ k y.1 ⊔ rootSubgroup τ k (-y.1) →
      Commute ((g : ModGL τ K) * rootDiagUnit τ a) (baseChangeGL ι₀ u))
    (B : ℕ) (hreg : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      (∑ j, regCoweight Γ j * α j) ≠ 0 ∧ (∑ j, regCoweight Γ j * α j).natAbs < B) :
    ∃ e : Fin τ.rank → Kˣ, (g : ModGL τ K) = rootDiagUnit τ e := by
  classical
  have hτ2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl <;> decide
  have : Fintype K := Fintype.ofFinite K
  have : Fintype k := Fintype.ofFinite k
  have hKodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK
  have hk3 : 3 ≤ Nat.card k := by
    have hkodd : Odd (Nat.card k) := by
      rw [Nat.card_eq_fintype_card, Nat.odd_iff]
      exact FiniteField.odd_card_of_char_ne_two hk
    have h2 : 1 < Nat.card k := Finite.one_lt_card
    obtain ⟨m, hm⟩ := hkodd
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
  have hxeq : x = baseChangeGL ι ((g : ModGL τ K) * rootDiagUnit τ a) := by
    rw [map_mul, hdb]
  have hcommL : ∀ y ∈ Γ, ∀ u : ModGL τ k,
      u ∈ rootSubgroup τ k y.1 ⊔ rootSubgroup τ k (-y.1) →
        Commute x (baseChangeGL (ι.comp ι₀) u) := by
    intro y hy u hu
    rw [hxeq, ← baseChangeGL_baseChangeGL]
    exact (hcomm y hy u hu).map (baseChangeGL ι)
  have hroot : ∀ y ∈ Γ, ∃ (w : WeylGroup τ) (i : Fin τ.rank),
      w • (Pi.single i 1 : Fin τ.rank → ℤ) = y.1 ∧ ∀ s : Lˣ, Commute x
        (canonicalRep (coxeterSystem τ) L w * torusElt τ L i s *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) := by
    intro y hy
    obtain ⟨w, i, hwi⟩ := isRoot_iff_exists_smul_single.1 (hΓ y hy)
    obtain ⟨-, -, hQ, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ k hk (hΓ y hy)
    have hQmap := (hQ w i hwi).1
    set n := canonicalRep (coxeterSystem τ) k w with hn
    refine ⟨w, i, hwi, commute_conj_torusElt_of_commute hτ2 hk3 (ι.comp ι₀) w i (fun c => ?_)
      (fun c => ?_)⟩
    · have hmem : n * xUnit τ k i c * n⁻¹ ∈ rootSubgroup τ k y.1 ⊔ rootSubgroup τ k (-y.1) := by
        rw [← hQmap]
        exact ⟨xUnit τ k i c, Subgroup.subset_closure (Or.inl ⟨c, rfl⟩), rfl⟩
      exact hcommL y hy _ hmem
    · have hmem : n * yUnit τ k i c * n⁻¹ ∈ rootSubgroup τ k y.1 ⊔ rootSubgroup τ k (-y.1) := by
        rw [← hQmap]
        exact ⟨yUnit τ k i c, Subgroup.subset_closure (Or.inr ⟨c, rfl⟩), rfl⟩
      exact hcommL y hy _ hmem
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
  refine ⟨fun j => Units.mk0 _ (hne j), ?_⟩
  apply baseChangeGL_injective ι
  rw [hgd, baseChangeGL_rootDiagUnit]
  congr 1
  funext j
  exact Units.ext ((hev j).trans rfl)

end CFSG.ComponentClassification.Burgoyne.E2
