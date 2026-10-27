module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusAmbient
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Tools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentBasic

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

theorem primeResidual_two_eq_top_of_isDoubleCoverOfAlt {Q : Type} [Group Q] [Finite Q] {m : ℕ}
    (hm : 4 ≤ m) (hQ : IsDoubleCoverOfAlt Q m) : primeResidual 2 Q = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : (primeResidual 2 Q).Characteristic := primeResidual_characteristic 2 Q
  have hN : (primeResidual 2 Q).Normal := inferInstance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ.1 hN with h | h
  · exact h
  · exfalso
    have h1 : (center Q).index ∣ (primeResidual 2 Q).index := Subgroup.index_dvd_of_le h
    obtain ⟨e⟩ := hQ.2.2
    have h2 : (center Q).index = Nat.card (alternatingGroup (Fin m)) := by
      rw [Subgroup.index, Nat.card_congr e.toEquiv]
    have h3 : Even (center Q).index := by
      rw [h2]
      exact even_card_alternatingGroup (α := Fin m) (by rw [Fintype.card_fin]; exact hm)
    have h4 : 2 ∣ (primeResidual 2 Q).index := (even_iff_two_dvd.1 h3).trans h1
    have h5 := primeResidual_coprime_index 2 Q
    exact absurd (Nat.dvd_gcd (dvd_refl 2) h4) (by rw [h5]; decide)

theorem oTwoPrimeOf_eq_map_primeResidual {X : Type} [Group X] [Finite X] (A : Subgroup X) :
    oTwoPrimeOf A = (primeResidual 2 ↥A).map A.subtype := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← closure_pElements_eq_map_primeResidual]
  unfold oTwoPrimeOf
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    refine ⟨hx, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨j, hj⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨hx, k, by rw [← hk]; exact pow_orderOf_eq_one x⟩

theorem exists_piece_abstract {G K : Type} [Group G] [Finite G] [Group K] (θ : G →* K)
    (hker : ¬ 2 ∣ Nat.card θ.ker) {L : Subgroup K} {m : ℕ} (hm : 5 ≤ m)
    (hL : IsDoubleCoverOfAlt ↥L m) (hnorm : ∀ g : G, θ g ∈ normalizer (L : Set K))
    (hsurj : ∀ l ∈ L, ∃ g : G, θ g = l) :
    (L.comap θ).Normal ∧ (oTwoPrimeOf (L.comap θ)).Normal ∧
      ((oTwoPrimeOf (L.comap θ)).subgroupOf (L.comap θ)).Normal ∧
      (oTwoPrimeOf (L.comap θ)).map θ = L ∧ IsTwoGenQuasi ↥(oTwoPrimeOf (L.comap θ)) ∧
      IsDoubleCoverOfAlt
        (↥(oTwoPrimeOf (L.comap θ)) ⧸ pPrimeCore 2 ↥(oTwoPrimeOf (L.comap θ))) m := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := L.comap θ with hM
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hM, Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hnorm g) (θ n)).1 hn
  let θ₀ : ↥M →* ↥L := (θ.comp M.subtype).codRestrict L fun x => x.2
  have hθ₀ : Function.Surjective θ₀ := by
    intro l
    obtain ⟨g, hg⟩ := hsurj l l.2
    exact ⟨⟨g, by rw [hM, Subgroup.mem_comap, hg]; exact l.2⟩, Subtype.ext hg⟩
  have : Finite ↥L := Finite.of_surjective θ₀ hθ₀
  have hLtop : primeResidual 2 ↥L = ⊤ :=
    primeResidual_two_eq_top_of_isDoubleCoverOfAlt (by omega) hL
  have hres : (primeResidual 2 ↥M).map θ₀ = ⊤ := by
    rw [primeResidual_map_surjective 2 θ₀ hθ₀, hLtop]
  have hPmap : (oTwoPrimeOf M).map θ = L := by
    rw [oTwoPrimeOf_eq_map_primeResidual, Subgroup.map_map]
    have hcomp : θ.comp M.subtype = L.subtype.comp θ₀ := rfl
    rw [hcomp, ← Subgroup.map_map, hres, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hPM : oTwoPrimeOf M ≤ M := oTwoPrimeOf_le M
  set P : Subgroup G := oTwoPrimeOf M with hP
  let θ₁ : ↥P →* ↥L := θ₀.comp (Subgroup.inclusion hPM)
  have hθ₁ : Function.Surjective θ₁ := by
    intro l
    have hl : l ∈ (primeResidual 2 ↥M).map θ₀ := by rw [hres]; exact Subgroup.mem_top l
    obtain ⟨x, hx, hxl⟩ := hl
    have hxP : (x : G) ∈ P := by
      rw [hP, oTwoPrimeOf_eq_map_primeResidual]
      exact ⟨x, hx, rfl⟩
    exact ⟨⟨x, hxP⟩, hxl⟩
  have hodd2 : Nat.Coprime 2 (Nat.card θ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hker
  have hker1 : θ₁.ker ≤ pPrimeCore 2 ↥P := by
    have hodd : Nat.Coprime 2 (Nat.card θ₁.ker) := by
      let g : θ₁.ker →* θ.ker :=
        { toFun := fun a => ⟨((a : ↥P) : G), by
            rw [MonoidHom.mem_ker]
            exact congrArg Subtype.val (MonoidHom.mem_ker.1 a.2)⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      have hg : Function.Injective g := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun y : θ.ker => (y : G)) hab
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg) hodd2
    exact le_sSup ⟨inferInstance, hodd⟩
  have hker2 : pPrimeCore 2 ↥P ≤ θ₁.ker := by
    have hN : ((pPrimeCore 2 ↥P).map θ₁).Normal := Subgroup.Normal.map inferInstance θ₁ hθ₁
    have hcard : Nat.card ((pPrimeCore 2 ↥P).map θ₁) ∣ Nat.card (pPrimeCore 2 ↥P) :=
      Subgroup.card_map_dvd _ _
    have hodd : Odd (Nat.card ((pPrimeCore 2 ↥P).map θ₁)) :=
      Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hcard pPrimeCore_coprime_card)
    have hbot := AhatData.CoverSetup.normal_odd_eq_bot hm (AhatData.CoverSetup.ofCover hL) hodd
    rwa [Subgroup.map_eq_bot_iff] at hbot
  have hkerEq : θ₁.ker = pPrimeCore 2 ↥P := le_antisymm hker1 hker2
  let e : ↥P ⧸ pPrimeCore 2 ↥P ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ₁ hθ₁)
  have hPG : (oTwoPrimeOf M).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hMφ : M.map (MulAut.conj g).toMonoidHom = M :=
      map_conj_eq_of_mem_normalizer (by rw [Subgroup.normalizer_eq_top_iff.2 hMn]; trivial)
    have h1 := map_oTwoPrimeOf_le M (MulAut.conj g).toMonoidHom
    rw [hMφ] at h1
    exact h1 (Subgroup.mem_map_of_mem _ hx)
  refine ⟨hMn, hPG, normal_subgroupOf_oTwoPrimeOf M, hPmap, ⟨primeResidual_oTwoPrimeOf M, ?_⟩, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hL.1
  · exact Stage12.McLRec.isDoubleCoverOfAlt_congr e.symm hL

end CFSG.OddStandard.Solomon75
