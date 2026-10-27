module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitSymThree
import CFSG.LocalAnalysis.AGLEmbedding.SUPairCommute
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroProductSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
import CFSG.RankThree.PartOne.S12.PerfectOddPrime

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.CZeroOrbitRank

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.AS76b (oUpperTwo)

variable {Y : Type} [Group Y] [Finite Y]

theorem map_map_mulAut (H : Subgroup Y) (σ τ : MulAut Y) :
    (H.map τ.toMonoidHom).map σ.toMonoidHom = H.map (σ * τ).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_pow_ne {H : Subgroup Y} {σ : MulAut Y} {p k : ℕ} (hp : p.Prime)
    (hσ : σ ^ p ^ k = 1) (hH : H.map σ.toMonoidHom ≠ H) {i j : ℕ} (hij : i < j) (hjp : j < p) :
    H.map (σ ^ i).toMonoidHom ≠ H.map (σ ^ j).toMonoidHom := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hfix : H.map (σ ^ (d + 1)).toMonoidHom = H := by
    have h1 := congrArg (fun K => K.map ((σ ^ i)⁻¹).toMonoidHom) h
    simp only [map_map_mulAut] at h1
    rw [inv_mul_cancel, show (σ ^ i)⁻¹ * σ ^ (i + d + 1) = σ ^ (d + 1) by
      rw [show i + d + 1 = i + (d + 1) by omega, pow_add, inv_mul_cancel_left]] at h1
    rw [← h1]
    exact Subgroup.map_id H
  have hcop : Nat.Coprime (d + 1) (orderOf σ) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hσ) ?_
    exact Nat.Coprime.pow_right k (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun hpd => absurd (Nat.le_of_dvd (by omega) hpd) (by omega)))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hall : ∀ n : ℕ, H.map ((σ ^ (d + 1)) ^ n).toMonoidHom = H := by
    intro n
    induction n with
    | zero => exact Subgroup.map_id H
    | succ n ih => rw [pow_succ, ← map_map_mulAut, hfix, ih]
  apply hH
  rw [← hm]
  exact hall m

theorem le_pRank_of_family (n : ℕ) (B : Fin n → Subgroup Y) (e : Fin n → Y)
    (hc : ∀ i j, i ≠ j → B j ≤ centralizer (B i : Set Y)) (he : ∀ i, e i ∈ B i)
    (h3 : ∀ i, e i ^ 3 = 1) (hnc : ∀ i, e i ∉ centralizer (B i : Set Y)) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨E, -, hE, hcard⟩ := TenTenClaim.exists_elemAbelian_of_family n B e hc he h3 hnc
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE hcard

theorem card_le_of_pRank_le {E : Subgroup Y} (hE : IsElemAbelian 3 E) {r : ℕ}
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ r) : Nat.card E ≤ 3 ^ r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 _ x.2)⟩
  obtain ⟨s, hs⟩ := hp.exists_card_eq
  have hsle : s ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE hs
  rw [hs]
  exact Nat.pow_le_pow_right (by norm_num) (hsle.trans hr)

theorem rank_of_orbit (hO : CFSG.pCore 2 Y = ⊥) {T : Subgroup Y} (hT : IsSubnormal T ⊤)
    (hshape : IsSymThreeOrSUThreeTwo ↥T ∨ (IsComponentOf T ⊤ ∧ 3 ∣ Nat.card T))
    {p k : ℕ} (hp : p.Prime) (σ : MulAut Y) (hσ : σ ^ p ^ k = 1)
    (hmove : (oUpperTwo T).map σ.toMonoidHom ≠ oUpperTwo T) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) ∧ (5 ≤ p → 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTi : ∀ i : ℕ, IsSubnormal (T.map (σ ^ i).toMonoidHom) ⊤ := by
    intro i
    have := hT.map (σ ^ i).toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ (σ ^ i).surjective] at this
  have hOi : ∀ i : ℕ, oUpperTwo (T.map (σ ^ i).toMonoidHom) =
      (oUpperTwo T).map (σ ^ i).toMonoidHom := fun i => (SUPair.map_oUpperTwo _ T).symm
  have h01 : (oUpperTwo T).map (σ ^ 0).toMonoidHom ≠ (oUpperTwo T).map (σ ^ 1).toMonoidHom := by
    rw [pow_zero, pow_one]
    intro h
    apply hmove
    rw [← h]
    exact Subgroup.map_id _
  have hdistn : ∀ n : ℕ, (n ≤ p ∨ n = 2) → ∀ i j : Fin n, i ≠ j →
      (oUpperTwo T).map (σ ^ (i : ℕ)).toMonoidHom ≠ (oUpperTwo T).map (σ ^ (j : ℕ)).toMonoidHom := by
    intro n hn i j hij
    have hne' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases hn with hn | rfl
    · have hσ1 : (oUpperTwo T).map σ.toMonoidHom ≠ oUpperTwo T := hmove
      rcases lt_or_gt_of_ne hne' with h | h
      · exact map_pow_ne hp hσ hσ1 h (by omega)
      · exact (map_pow_ne hp hσ hσ1 h (by omega)).symm
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact h01
      · exact Ne.symm h01
      · exact absurd rfl hij
  have hfam : ∀ (B : Subgroup Y) (e : Y), e ∈ B → e ^ 3 = 1 → e ∉ centralizer (B : Set Y) →
      (∀ i j : ℕ, B.map (σ ^ i).toMonoidHom ≠ B.map (σ ^ j).toMonoidHom →
        B.map (σ ^ j).toMonoidHom ≤ centralizer (B.map (σ ^ i).toMonoidHom : Set Y)) →
      ∀ n : ℕ, (∀ i j : Fin n, i ≠ j →
        B.map (σ ^ (i : ℕ)).toMonoidHom ≠ B.map (σ ^ (j : ℕ)).toMonoidHom) →
      n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
    intro B e heB he3 hnc hcomm n hn
    refine le_pRank_of_family n (fun i => B.map (σ ^ (i : ℕ)).toMonoidHom)
      (fun i => (σ ^ (i : ℕ)) e) (fun i j hij => hcomm _ _ (hn i j hij))
      (fun i => ⟨e, heB, rfl⟩) (fun i => by rw [← map_pow, he3, map_one]) ?_
    intro i hcen
    apply hnc
    rw [mem_centralizer_iff] at hcen ⊢
    intro b hb
    have := hcen ((σ ^ (i : ℕ)) b) ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact (σ ^ (i : ℕ)).injective this
  rcases hshape with (⟨⟨hS⟩⟩ | hU) | ⟨hC, h3⟩
  ·
    refine ⟨?_, fun hp5 => ?_⟩
    · obtain ⟨a, t, haT, htT, ha3, ha1, ht2, hta, hO2, hasn, haD, hcomm, hsplit⟩ :=
        CZeroOrbit.symThree_data hT ⟨hS⟩
      have hσa : zpowers (σ a) ≠ zpowers a := by
        intro h
        apply hmove
        rw [hO2, MonoidHom.map_zpowers]
        exact h
      have hcomm' : ∀ x ∈ zpowers a, ∀ y ∈ zpowers (σ a), x * y = y * x := by
        intro x hx y hy
        have hB3 : IsPGroup 3 (zpowers (σ a)) := by
          rintro ⟨g, hg⟩
          obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
          refine ⟨1, Subtype.ext ?_⟩
          change ((σ a) ^ m) ^ 3 ^ 1 = 1
          rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow,
            ha3, map_one, one_zpow]
        have hBs : IsSubnormal (zpowers (σ a)) ⊤ := by
          have := hasn.map σ.toMonoidHom
          rwa [MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _ σ.surjective] at this
        exact (SubnormalCommute.commute_oUpperTwo_of_symThree hT ⟨hS⟩ hB3 hBs x (hO2 ▸ hx) y
          hy).symm
      have hEA : ∀ b : Y, b ^ 3 = 1 → IsElemAbelian 3 (zpowers b) := by
        intro b hb
        refine ⟨inferInstance, fun x hx => ?_⟩
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
      have hσa3 : (σ a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
      have hσa1 : σ a ≠ 1 := fun h => ha1 (σ.injective (by rw [h, map_one]))
      have hcard : ∀ b : Y, b ^ 3 = 1 → b ≠ 1 → Nat.card (zpowers b) = 3 := fun b h3 h1 => by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime h3 h1
      have hinf : zpowers a ⊓ zpowers (σ a) = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxa, hxb⟩
        by_contra hx1
        have hx3 : x ^ 3 = 1 := by
          obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxa
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
        have e1 : zpowers x = zpowers a := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxa)
          (by rw [hcard a ha3 ha1, hcard x hx3 hx1])
        have e2 : zpowers x = zpowers (σ a) := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxb)
          (by rw [hcard _ hσa3 hσa1, hcard x hx3 hx1])
        exact hσa (e2.symm.trans e1)
      obtain ⟨hE, hEcard⟩ := TenTenClaim.elemAbelian_sup_card (hEA a ha3) (hEA _ hσa3) hcomm' hinf
      rw [hcard a ha3 ha1, hcard _ hσa3 hσa1] at hEcard
      exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE (k := 2)
        (by rw [hEcard]; norm_num)
    · by_contra hlt
      push Not at hlt
      exact CZeroOrbit.false_of_symThree_orbit hp hp5 σ hσ hT ⟨hS⟩ hmove fun E hE =>
        (card_le_of_pRank_le hE (r := 3) (by omega)).trans (by norm_num)
  ·
    obtain ⟨s, d, z, f, hsT, hdT, hfT, hf4, hfs, hfd, hz, hH, hsO, hdO, hsd⟩ :=
      SUPair.exists_data_of_su hU
    have hshapei : ∀ i : ℕ, IsSymThreeOrSUThreeTwo ↥(T.map (σ ^ i).toMonoidHom) := fun i =>
      IsSymThreeOrSUThreeTwo.of_mulEquiv (T.equivMapOfInjective _ (σ ^ i).injective) (Or.inr hU)
    have hcommO : ∀ i j : ℕ, (oUpperTwo T).map (σ ^ i).toMonoidHom ≠
        (oUpperTwo T).map (σ ^ j).toMonoidHom →
        (oUpperTwo T).map (σ ^ j).toMonoidHom ≤
          centralizer ((oUpperTwo T).map (σ ^ i).toMonoidHom : Set Y) := by
      intro i j hij
      rw [← hOi, ← hOi] at hij ⊢
      have h := CZeroProduct.commutator_oUpperTwo_eq_bot SUPair.subnormalSUThreeTwoCommute_holds
        hO (hTi i) (hTi j) (hshapei i) (hshapei j) hij
      exact commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact h)
    have hs3 : s ^ 3 = 1 := hH.cube s hsO
    have hsnc : s ∉ centralizer (oUpperTwo T : Set Y) := by
      intro hc
      exact hsd ((mem_centralizer_iff.mp hc d hdO).symm)
    have key : ∀ n : ℕ, (n ≤ p ∨ n = 2) → n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := fun n hn =>
      hfam (oUpperTwo T) s hsO hs3 hsnc hcommO n (hdistn n hn)
    exact ⟨key 2 (Or.inr rfl), fun hp5 => key 4 (Or.inl (by omega))⟩
  ·
    have hperf : ⁅T, T⁆ = T := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hC.2.2.1)
    have hOT : oUpperTwo T = T := SevenFourL34.oUpperTwo_eq_of_perfect hperf
    haveI : Group.IsPerfect ↥T := Subgroup.isPerfect_iff.mpr hperf
    obtain ⟨e, he3, hez⟩ :=
      CFSG.RankThree.PartOne.exists_pow_eq_one_not_mem_center_of_isPerfect (p := 3) (by norm_num)
        (inferInstance : Group.IsPerfect ↥T) h3
    have hCi : ∀ i : ℕ, IsComponentOf (T.map (σ ^ i).toMonoidHom) ⊤ := fun i =>
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (σ ^ i) T).2 hC
    have hcommT : ∀ i j : ℕ, (oUpperTwo T).map (σ ^ i).toMonoidHom ≠
        (oUpperTwo T).map (σ ^ j).toMonoidHom →
        (oUpperTwo T).map (σ ^ j).toMonoidHom ≤
          centralizer ((oUpperTwo T).map (σ ^ i).toMonoidHom : Set Y) := by
      intro i j hij y hy
      rw [hOT] at hij hy ⊢
      rw [mem_centralizer_iff]
      intro x hx
      exact commute_of_isComponentOf_ne (hCi i) (hCi j) hij x hx y hy
    have heT : (e : Y) ∈ oUpperTwo T := by rw [hOT]; exact e.2
    have he3' : (e : Y) ^ 3 = 1 := by simpa using congrArg Subtype.val he3
    have henc : (e : Y) ∉ centralizer (oUpperTwo T : Set Y) := by
      intro hc
      apply hez
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hc g (by rw [hOT]; exact g.2))
    have key : ∀ n : ℕ, (n ≤ p ∨ n = 2) → n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := fun n hn =>
      hfam (oUpperTwo T) e heT he3' henc hcommT n (hdistn n hn)
    exact ⟨key 2 (Or.inr rfl), fun hp5 => key 4 (Or.inl (by omega))⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.CZeroOrbitRank
