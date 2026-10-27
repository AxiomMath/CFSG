module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterFilter
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneB
public import Certificates.Certificate25172
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

theorem central_mem_of_trees {K : Subgroup GL24} {sg : Array Rows} {T : GTree}
    {sgG : ℕ → GL24}
    (hsgrep : ∀ l < sg.size, valHom (sgG l) = rowsMatrix 24 sg[l]!) (hsgK : ∀ l, sgG l ∈ K)
    (hT : gtOK sg T = true) (hord : T.pts.size = 2 ^ (Nat.card K).factorization 2)
    {z : GL24} (hzK : z ∈ K) (hz4 : z ^ 4 = 1) (hzc : ∀ g ∈ K, z * g = g * z) :
    ∃ i < T.pts.size, MRep T.pts[i]! z := by
  obtain ⟨f, hf, -, hcl⟩ := prodTree_closure_eq valHom valHom_injective hT sgG hsgrep
  have hScard := prodTree_card valHom valHom_injective hT sgG hsgrep
  have hSK : Subgroup.closure (sgG '' {l | l < sg.size}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, -, rfl⟩
    exact hsgK l
  have hSord : Nat.card (Subgroup.closure (sgG '' {l | l < sg.size})) =
      2 ^ (Nat.card K).factorization 2 := by rw [hScard, hord]
  obtain ⟨c, hcK, hcS⟩ :=
    CFSG.EvenSporadicStandard.HypOne.exists_conj_mem_of_card_pow_four hSK hSord hzK hz4
  have hcz : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hzc c hcK]
      _ = z := by group
  rw [hcz] at hcS
  have hcS' : z ∈ (Subgroup.closure (sgG '' {l | l < sg.size}) : Set GL24) := hcS
  rw [hcl] at hcS'
  obtain ⟨i, hi, hsi⟩ := hcS'
  refine ⟨i, hi, ?_⟩
  unfold MRep
  rw [← hsi]
  exact (hf i hi).symm

theorem eq_one_or_of_sylowCenter {tR : Rows} {t : GL24}
    (ht : MRep tR t) (htG : t ∈ GA) {d₁ : List (List ℤ)} {bidx : List ℕ} {d₂ : List (List ℤ)}
    {sIdx : List ℕ} {ord : ℕ} {K : Subgroup GL24} (hK : K = GA ⊓ Subgroup.centralizer {t})
    (hord : ord = 2 ^ (Nat.card K).factorization 2)
    (h : sylowCheckOf tR d₁ bidx d₂ sIdx ord = true)
    (hf : centerSylowOf tR d₁ bidx d₂ sIdx ord = true) {z : GL24} (hzK : z ∈ K)
    (hz4 : z ^ 4 = 1) (hzc : ∀ g ∈ K, z * g = g * z) : z = 1 ∨ z = t := by
  simp only [sylowCheckOf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hD1, hD2⟩, hBall⟩, hT⟩, hsize⟩, -⟩ := h
  have hrepB := rep_brayElts (bidx := bidx) ht hD1
  have hBGK : ∀ g ∈ brayEltsG t d₁ bidx, g ∈ K := by
    intro g hg
    rw [hK]
    refine Subgroup.mem_inf.2 ⟨brayElts_mem_GA htG g hg, ?_⟩
    obtain ⟨r, hr, hrg⟩ := forall₂_mem_left hrepB hg
    have e := (hBall r hr).1
    have h1 : MRep (Native.mul r tR) (g * t) := hrg.mul ht
    have h2 : MRep (Native.mul tR r) (t * g) := ht.mul hrg
    rw [e] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h2.eq h1).symm
  have hrepD2 := dag_rep hrepB d₂ hD2
  have hD2K : ∀ g ∈ dagG (brayEltsG t d₁ bidx) d₂, g ∈ K := dagG_mem hBGK d₂
  have hpt : ∃ i < (gtBFS ((sIdx.map fun j =>
        (CFSG.Sporadic.Co1Schreier.Native.dag (Native.brayElts (Native.brayRows tR d₁) bidx)
          d₂).1.getD j one).toArray) (ord + 1)).pts.size,
      MRep (gtBFS ((sIdx.map fun j =>
        (CFSG.Sporadic.Co1Schreier.Native.dag (Native.brayElts (Native.brayRows tR d₁) bidx)
          d₂).1.getD j one).toArray) (ord + 1)).pts[i]! z := by
    refine central_mem_of_trees
      (sgG := fun l => (dagG (brayEltsG t d₁ bidx) d₂).getD (sIdx.getD l 0) 1) ?_
      (fun l => getD_mem_of_forall hD2K _) hT (hsize.trans hord) hzK hz4 hzc
    intro l hl
    have hl' : l < sIdx.length := by simpa using hl
    rw [getElem!_toArray_map _ _ hl', List.getD_eq_getElem _ _ hl']
    exact (getD_rep hrepD2 MRep.one sIdx[l]).symm
  obtain ⟨i, hi, hp⟩ := hpt
  have hv := validRows_of_gtOK hT i hi
  exact eq_one_or_of_centerFilter ht hrepB hf hi hv hp (fun g hg => hzc g (hBGK g hg))

theorem centerInvAt_a₁ :
    CenterInvAt a₁ := by
  have key : ∀ a : GA, (a : GL24) = A₁ → CenterInvAt a := by
    intro a ha z hz2 hzc
    have hza : (z : GL24) * A₁ = A₁ * z := by
      have := commute_coe_of_central hzc a.2 rfl
      rwa [ha] at this
    have hzK : (z : GL24) ∈ GA ⊓ Subgroup.centralizer {A₁} :=
      Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 hza⟩
    have hzc' : ∀ g ∈ GA ⊓ Subgroup.centralizer {A₁}, (z : GL24) * g = g * z := by
      intro g hg
      obtain ⟨hgA, hgc⟩ := Subgroup.mem_inf.1 hg
      refine commute_coe_of_central hzc hgA ?_
      rw [ha]
      exact Subgroup.mem_centralizer_singleton_iff.1 hgc
    have hz4 : (z : GL24) ^ 4 = 1 := pow_four_eq_one_of_mul_self hz2
    have hf : centerSylowOf aR twoBD1 twoBBray sylD2B sylIdxB 32768 = true :=
      Certificates.certificate25172
    have hsyl : sylowCheckOf aR twoBD1 twoBBray sylD2B sylIdxB 32768 = true :=
      Certificates.certificate24511
    rcases eq_one_or_of_sylowCenter rep_A₁ A₁_mem rfl two_part_cent_B hsyl hf hzK hz4 hzc' with
      h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (h.trans ha.symm))
  exact key a₁ coe_a₁

end CFSG.EvenSporadicStandard.Solomon78
