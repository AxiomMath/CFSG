module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Red
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CrossCharOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05I1416Spor
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma117

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem k14_catalogIs_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs T Q) : catalogIs S Q :=
  let ⟨i, hi, ⟨f⟩⟩ := h
  ⟨i, hi, ⟨e.trans f⟩⟩

private theorem k14_char_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;> first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

theorem i14chev_of_factsK (G : Type) [Group G] [Finite G]
    (hClos : ChevClosureQAt G 3)
    (hI33 : ∀ (S : Type) [Group S] (q r : ℕ), IsChevSimple q S → IsChevSimple r S → q ≠ r → q = 2 ∨ r = 2)
    (hSpor : CFSG.LocalAnalysis.GLTheoremA.I1431SporSK) (hSporU : K14SporU) (hNotChev : K14NotChevOdd)
    (hNotAlt : K14NotAlt) (h1429 : I1429At G) : I1431Chev2At G := by
  intro b' a Kstar K hX _hab ha3 hKs haN hKc hKtype hnot hrk hCo2
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hap : IsPGroup 3 (Subgroup.zpowers a) := isPGroup_zpowers_of_pow_eq_one ha3
  have hncent : ¬ CentMod 3 Kstar a := fun h => hnot (i1431_le_sup_of_centMod hp hKs hap h hKc)
  have hKcases : catalogIs (PSimple 3 K) S9.isU4two ∨ catalogIs (PSimple 3 K) S9.isU5two ∨
      catalogIs (PSimple 3 K) S9.isSp6two := by
    obtain ⟨jK, hjK, ⟨eK⟩⟩ := hKtype
    rcases hjK with h | h | h
    · exact Or.inl ⟨jK, h, ⟨eK⟩⟩
    · exact Or.inr (Or.inl ⟨jK, h, ⟨eK⟩⟩)
    · exact Or.inr (Or.inr ⟨jK, h, ⟨eK⟩⟩)
  have hcat : IsCatalogGroup (PSimple 3 Kstar) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hKs.1).quotient _)
      (isQuasisimple_pQuot_of_glaPComponent hp hKs)
  have hxN' : Subgroup.zpowers a ≤ Subgroup.normalizer (Kstar : Set G) := Subgroup.zpowers_le.2 haN
  have hcen : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      exact h a (Subgroup.mem_zpowers a)
    · intro h z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_left (show Commute a g from h) m).eq
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a', b'', hab⟩ := (chev_pSimple_simple_nonabelian hp hKs).2
    apply hab
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    by_cases hn8 : n = 5 ∨ n = 6 ∨ n = 8
    ·
      refine Or.inr ⟨TauCeti.CFSGIndex.alternating n hn, ?_, ⟨e⟩⟩
      rcases hn8 with h | h | h <;> subst h <;> simp [ambiguousChev]
    · exfalso
      obtain ⟨m, hm5, ⟨eJ⟩⟩ := i1416AltSmall hp hp2 hKs haN ha3 hncent hKc hn e
      rcases hKcases with hU4 | hU5 | hSp
      · exact i1431_u42_not_alt hm5 hU4 eJ
      · exact hNotAlt _ m hm5 (Or.inl hU5) ⟨eJ⟩
      · exact hNotAlt _ m hm5 (Or.inr hSp) ⟨eJ⟩
  | sporadic s =>
    by_cases hs : s = TauCeti.SporadicName.Co2
    · subst hs
      exact (hCo2 ⟨_, rfl, ⟨e⟩⟩).elim
    · exfalso
      have hβ3 : chevAut 3 Kstar ⟨a, haN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 Kstar haN ha3
      have hβ1 : chevAut 3 Kstar ⟨a, haN⟩ ≠ 1 := fun h => hncent ((chevAut_eq_one_iff hp hKs haN).1 h)
      have hT := glaPComponent_chevTransfer hp haN hap hKc
      obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp haN hap hKc
      have hKPS : CFSG.Open.IsKGroup (PSimple 3 Kstar) := ((hX.of_le hKs.1).quotient _).quotient _
      rcases hKcases with hU4 | hU5 | hSp
      · exact hs (hSpor (PSimple 3 Kstar) s ⟨e⟩ hKPS (chevAut 3 Kstar ⟨a, haN⟩) hβ3 hβ1 (chevTransfer 3 Kstar K) hT
          (k14_catalogIs_congr g.symm hU4))
      · exact hs (hSporU (PSimple 3 Kstar) s ⟨e⟩ (chevAut 3 Kstar ⟨a, haN⟩) hβ3 hβ1 (chevTransfer 3 Kstar K) hT
          (Or.inl (k14_catalogIs_congr g.symm hU5)))
      · exact hs (hSporU (PSimple 3 Kstar) s ⟨e⟩ (chevAut 3 Kstar ⟨a, haN⟩) hβ3 hβ1 (chevTransfer 3 Kstar K) hT
          (Or.inr (k14_catalogIs_congr g.symm hSp)))
  | lie d =>
    by_cases hr2 : d.1.characteristic = 2
    ·
      refine Or.inl ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
      simp only [onLie]
      exact hr2
    · exfalso
      have hr : d.1.characteristic.Prime := k14_char_prime d.1
      have hKr : IsChevSimple d.1.characteristic (PSimple 3 Kstar) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨e⟩⟩
      have hJr : IsChevSimple d.1.characteristic (PSimple 3 K) :=
        hClos hp hp2 d.1.characteristic hr (Subgroup.centralizer ({b'} : Set G)) Kstar (Subgroup.zpowers a) hX hKs
          hKr (i1431_isElemAbelian_zpowers ha3) hxN' K (by rw [hcen]; exact hKc)
      rcases hKcases with hU4 | hU5 | hSp
      · rcases i1431_char_two_or_three hI33 hJr hU4 with h2 | h3
        · exact hr2 h2
        · rw [h3] at hKr
          have h6 := h1429 (Subgroup.centralizer ({b'} : Set G)) Kstar K a hX hKs hKr haN ha3 hncent hKc hU4
          have h7 := S11.twoLocalRank_quot_le Nat.prime_three (by norm_num) Kstar
          have h8 := CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le Nat.prime_three Kstar
          omega
      · exact hNotChev _ (Or.inl hU5) _ hr hr2 hJr
      · exact hNotChev _ (Or.inr hSp) _ hr hr2 hJr

section MainCerts

theorem i14chev_of_residualsK (G : Type) [Group G] [Finite G]
    (hSpor : CFSG.LocalAnalysis.GLTheoremA.I1431SporSK) (hSporU : K14SporU) (hNotChev : K14NotChevOdd)
    (hNotAlt : K14NotAlt) (h1429 : I1429At G) : I1431Chev2At G :=
  i14chev_of_factsK G
    (chevClosureQAt_of_lieComp_lieComps (G := G) lieComp_holds (fun _ hq' h5 => lieCompsOn_holds hq' h5)
      Nat.prime_three (by norm_num))
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.CrossCharOdd.input3_3_OddChar_holds hSpor hSporU hNotChev hNotAlt h1429

theorem i14chev_of_residualK (G : Type) [Group G] [Finite G]
    (hSpor : CFSG.LocalAnalysis.GLTheoremA.I1431SporSK) (hSporU : K14SporU) (hNotChev : K14NotChevOdd)
    (hNotAlt : K14NotAlt) (hI1429 : I1429Residual) : I1431Chev2At G :=
  i14chev_of_residualsK G hSpor hSporU hNotChev hNotAlt (i1429At_of_residual hI1429 G)

end MainCerts

end CFSG.LocalAnalysis.GLTheoremA

end
