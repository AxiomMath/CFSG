module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Quasithin.H13.NQBlockPRankProduct
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools

public section

namespace CFSG.GroupTheory

open CFSG.Open
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

theorem pRank_sup_eq_add_of_commute_of_not_dvd {p : ℕ} (hp : p.Prime) {A B : Subgroup Y}
    (hc : A ≤ Subgroup.centralizer (B : Set Y))
    (hAB : ¬ p ∣ Nat.card ↥(A ⊓ B)) :
    CFSG.Open.pRank p (A ⊔ B) = CFSG.Open.pRank p A + CFSG.Open.pRank p B := by
  classical
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hc ha) b hb).symm
  have hcop : Nat.Coprime p (Nat.card ↥(A ⊓ B)) := hp.coprime_iff_not_dvd.mpr hAB
  have hlower : CFSG.Open.pRank p A + CFSG.Open.pRank p B ≤
      CFSG.Open.pRank p (A ⊔ B) :=
    CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime (A := A) (B := B) hp hcomm hcop
  have hmain : CFSG.Open.pRank p (A ⊔ B) =
      CFSG.Open.pRank p A + CFSG.Open.pRank p B := by
    let f : ↥A × ↥B →* Y :=
      MonoidHom.noncommCoprod A.subtype B.subtype (fun a b => hcomm a a.2 b b.2)
    have hf_mem : ∀ x : ↥A × ↥B, f x ∈ (A ⊔ B : Subgroup Y) := by
      rintro ⟨a, b⟩
      rw [show f (a, b) = (a : Y) * (b : Y) from MonoidHom.noncommCoprod_apply _ _ _ (a, b)]
      exact Subgroup.mul_mem_sup a.2 b.2
    have hker_card : Nat.card f.ker = Nat.card ↥(A ⊓ B) := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun x => ⟨(x.1.1 : Y), ⟨x.1.1.2, ?_⟩⟩
          invFun := fun x =>
            ⟨(⟨(x : Y), (Subgroup.mem_inf.mp x.2).1⟩,
              ⟨(x : Y)⁻¹, (Subgroup.mem_inf.mp ((A ⊓ B).inv_mem x.2)).2⟩), ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · have hx : (x.1.1 : Y) * (x.1.2 : Y) = 1 := by
          have h := MonoidHom.mem_ker.mp x.2
          rw [show f x.1 = (x.1.1 : Y) * (x.1.2 : Y) from
            MonoidHom.noncommCoprod_apply _ _ _ _] at h
          exact h
        rw [eq_inv_of_mul_eq_one_left hx]
        exact B.inv_mem x.1.2.2
      · change f (⟨(x : Y), (Subgroup.mem_inf.mp x.2).1⟩,
            ⟨(x : Y)⁻¹, (Subgroup.mem_inf.mp ((A ⊓ B).inv_mem x.2)).2⟩) = 1
        rw [show f (⟨(x : Y), (Subgroup.mem_inf.mp x.2).1⟩,
            ⟨(x : Y)⁻¹, (Subgroup.mem_inf.mp ((A ⊓ B).inv_mem x.2)).2⟩) =
            (x : Y) * (x : Y)⁻¹ from MonoidHom.noncommCoprod_apply _ _ _ _]
        exact mul_inv_cancel _
      · intro x
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          have hx : (x.1.1 : Y) * (x.1.2 : Y) = 1 := by
            have h := MonoidHom.mem_ker.mp x.2
            rw [show f x.1 = (x.1.1 : Y) * (x.1.2 : Y) from
              MonoidHom.noncommCoprod_apply _ _ _ _] at h
            exact h
          exact inv_eq_of_mul_eq_one_right hx
      · intro x
        apply Subtype.ext
        rfl
    have hker : ¬ p ∣ Nat.card f.ker := by
      rw [hker_card]
      exact hAB
    let g : ↥A × ↥B →* ↥(A ⊔ B) := f.codRestrict (A ⊔ B) hf_mem
    have hg_surj : Function.Surjective g := by
      intro y
      have hB : B ≤ Subgroup.centralizer (A : Set Y) := Subgroup.le_centralizer_iff.mp hc
      have hBN : B ≤ Subgroup.normalizer (A : Set Y) :=
        hB.trans (Subgroup.centralizer_le_normalizer (A : Set Y))
      have hcoe : (↑(A ⊔ B) : Set Y) = (A : Set Y) * (B : Set Y) :=
        Subgroup.coe_mul_of_right_le_normalizer_left A B hBN
      have hy : (y : Y) ∈ (A : Set Y) * (B : Set Y) := by
        rw [← hcoe]
        exact y.2
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy
      refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
      apply Subtype.ext
      change f (⟨a, ha⟩, ⟨b, hb⟩) = (y : Y)
      rw [show f (⟨a, ha⟩, ⟨b, hb⟩) = a * b from
        MonoidHom.noncommCoprod_apply _ _ _ _]
      exact hab
    have hker_g : ¬ p ∣ Nat.card g.ker := by
      rw [MonoidHom.ker_codRestrict f (A ⊔ B) hf_mem]
      exact hker
    have hquot : CFSG.Open.pRank p (⊤ : Subgroup ((↥A × ↥B) ⧸ g.ker)) =
        CFSG.Open.pRank p (⊤ : Subgroup (↥A × ↥B)) :=
      CFSG.SectionRank.pRank_quotient_eq (p := p) (hp := ⟨hp⟩) g.ker hker_g
    let e : ((↥A × ↥B) ⧸ g.ker) ≃* ↥(A ⊔ B) :=
      QuotientGroup.quotientKerEquivOfSurjective g hg_surj
    calc CFSG.Open.pRank p (A ⊔ B)
        = CFSG.Open.pRank p (⊤ : Subgroup ↥(A ⊔ B)) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) (A ⊔ B)
      _ = CFSG.Open.pRank p (⊤ : Subgroup ((↥A × ↥B) ⧸ g.ker)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
      _ = CFSG.Open.pRank p (⊤ : Subgroup (↥A × ↥B)) := hquot
      _ = CFSG.pRank p (↥A × ↥B) :=
          (CFSG.SectionRank.pRank_eq_open_pRank_top p (↥A × ↥B)).symm
      _ = CFSG.pRank p ↥A + CFSG.pRank p ↥B :=
          CFSG.Quasithin.H13.NQBlock.pRank_prod_eq hp
      _ = CFSG.Open.pRank p (⊤ : Subgroup ↥A) + CFSG.Open.pRank p (⊤ : Subgroup ↥B) := by
          rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
            CFSG.SectionRank.pRank_eq_open_pRank_top]
      _ = CFSG.Open.pRank p A + CFSG.Open.pRank p B := by
          rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) A,
            ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) B]
  exact le_antisymm hmain.le hlower

theorem pRank_iSup_eq_sum_of_commute_of_not_dvd {ι : Type} [DecidableEq ι] {p : ℕ}
    (hp : p.Prime) (s : Finset ι) (J : ι → Subgroup Y)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → J i ≤ Subgroup.centralizer (J j : Set Y))
    (hZ : ∀ i ∈ s, ¬ p ∣ Nat.card ↥(J i ⊓ Subgroup.centralizer (J i : Set Y))) :
    CFSG.Open.pRank p (⨆ i ∈ s, J i) = ∑ i ∈ s, CFSG.Open.pRank p (J i) := by
  classical
  revert hcomm hZ
  refine Finset.induction_on s ?_ ?_
  · intro hcomm hZ
    have hbot : (⨆ i ∈ (∅ : Finset ι), J i) = ⊥ := by simp
    rw [hbot, Finset.sum_empty]
    refine le_antisymm ?_ (Nat.zero_le _)
    refine CFSG.SectionRank.pRank_le hp.one_lt ?_
    intro E hE _
    rw [le_bot_iff.mp hE, Subgroup.card_bot, pow_zero]
  · intro a s has ih hcomm hZ
    have hcomm' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        J i ≤ Subgroup.centralizer (J j : Set Y) := fun i hi j hj hij =>
      hcomm i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hZ' : ∀ i ∈ s, ¬ p ∣
        Nat.card ↥(J i ⊓ Subgroup.centralizer (J i : Set Y)) := fun i hi =>
      hZ i (Finset.mem_insert_of_mem hi)
    rw [Finset.iSup_insert, Finset.sum_insert has]
    have hcommA : J a ≤ Subgroup.centralizer
        (((⨆ i ∈ s, J i) : Subgroup Y) : Set Y) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hB : ((⨆ i ∈ s, J i) : Subgroup Y) ≤
          Subgroup.centralizer (J a : Set Y) :=
        iSup₂_le fun i hi =>
          hcomm i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
            (fun h => has (h ▸ hi))
      exact (Subgroup.mem_centralizer_iff.mp (hB hy) x hx).symm
    have hAB : ¬ p ∣ Nat.card ↥(J a ⊓ (⨆ i ∈ s, J i)) := by
      intro hdvd
      have hle : J a ⊓ (⨆ i ∈ s, J i) ≤
          J a ⊓ Subgroup.centralizer (J a : Set Y) :=
        inf_le_inf_left (J a) (iSup₂_le fun i hi =>
          hcomm i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
            (fun h => has (h ▸ hi)))
      exact hZ a (Finset.mem_insert_self a s) (hdvd.trans (Subgroup.card_dvd_of_le hle))
    rw [pRank_sup_eq_add_of_commute_of_not_dvd hp hcommA hAB, ih hcomm' hZ']

theorem pRank_iSup_eq_sum_of_inf_centralizer_eq_bot {ι : Type} [DecidableEq ι] {p : ℕ}
    (hp : p.Prime) (s : Finset ι) (J A : ι → Subgroup Y) (i₀ : ι)
    (hAJ : ∀ i ∈ s, A i ≤ J i)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → J i ≤ Subgroup.centralizer (J j : Set Y))
    (hZ : ∀ i ∈ s, i ≠ i₀ → A i ⊓ Subgroup.centralizer (J i : Set Y) = ⊥) :
    CFSG.Open.pRank p (⨆ i ∈ s, A i) = ∑ i ∈ s, CFSG.Open.pRank p (A i) := by
  classical
  have hAcomm : Pairwise fun i j : {i // i ∈ s} =>
      ∀ x y : Y, x ∈ A i → y ∈ A j → Commute x y := by
    intro i j hij x y hx hy
    have hi : (i : ι) ∈ s := i.2
    have hj : (j : ι) ∈ s := j.2
    have hne : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
    exact (Subgroup.mem_centralizer_iff.mp
      (hcomm (i : ι) hi (j : ι) hj hne (hAJ (i : ι) hi hx)) y
        (hAJ (j : ι) hj hy)).symm
  let f : (∀ i : {i // i ∈ s}, A i) →* Y := Subgroup.noncommPiCoprod hAcomm
  have hf_inj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    let commA : ∀ i j : {i // i ∈ s}, i ≠ j → Commute (x i : Y) (x j : Y) :=
      fun i j hij => hAcomm (i := i) (j := j) hij (x i) (x j) (x i).2 (x j).2
    have hprod : (Finset.univ : Finset {i // i ∈ s}).noncommProd
        (fun i => (x i : Y)) (fun i _ j _ hij => commA i j hij) = 1 := by
      simpa [f, Subgroup.noncommPiCoprod_apply] using hx
    have hsingle : ∀ i : {i // i ∈ s}, (i : ι) ≠ i₀ → x i = 1 := by
      intro i hi
      have h1 : ((Finset.univ.erase i).noncommProd (fun j => (x j : Y))
          (fun j _ k _ hjk => commA j k hjk)) * (x i : Y) = 1 := by
        rw [Finset.noncommProd_erase_mul (Finset.univ) (Finset.mem_univ i)
          (fun j => (x j : Y)) (fun j _ k _ hjk => commA j k hjk), hprod]
      have hxinv : (x i : Y) =
          ((Finset.univ.erase i).noncommProd (fun j => (x j : Y))
            (fun j _ k _ hjk => hAcomm (i := j) (j := k) hjk (x j) (x k) (x j).2 (x k).2))⁻¹ :=
        eq_inv_of_mul_eq_one_right h1
      have hPmem : ((Finset.univ.erase i).noncommProd (fun j => (x j : Y))
          (fun j _ k _ hjk => hAcomm (i := j) (j := k) hjk (x j) (x k) (x j).2 (x k).2)) ∈
          Subgroup.centralizer (J (i : ι) : Set Y) := by
        refine Subgroup.noncommProd_mem
          (Subgroup.centralizer (J (i : ι) : Set Y))
          (fun j _ k _ hjk => hAcomm (i := j) (j := k) hjk (x j) (x k) (x j).2 (x k).2)
          (fun j hj => ?_)
        have hji : (j : ι) ≠ (i : ι) := fun h =>
          (Finset.mem_erase.mp hj).1 (Subtype.ext h)
        exact (hAJ (j : ι) j.2).trans
          (hcomm (j : ι) j.2 (i : ι) i.2 hji) (x j).2
      have hxCent : (x i : Y) ∈ Subgroup.centralizer (J (i : ι) : Set Y) := by
        rw [hxinv]
        exact Subgroup.inv_mem _ hPmem
      have hxbot : (x i : Y) ∈
          (A (i : ι) ⊓ Subgroup.centralizer (J (i : ι) : Set Y) : Subgroup Y) :=
        ⟨(x i).2, hxCent⟩
      rw [hZ (i : ι) i.2 hi, Subgroup.mem_bot] at hxbot
      exact Subtype.ext hxbot
    funext i
    by_cases hi : (i : ι) = i₀
    · have hP1 : ((Finset.univ.erase i).noncommProd (fun j => (x j : Y))
          (fun j _ k _ hjk => hAcomm (i := j) (j := k) hjk (x j) (x k) (x j).2 (x k).2)) = 1 := by
        refine Finset.noncommProd_induction _ _ _ (fun y => y = 1) ?_ rfl ?_
        · intro a b ha hb
          rw [ha, hb, mul_one]
        · intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          have hje : (j : ι) ≠ i₀ := by
            intro h
            exact hji (Subtype.ext (h.trans hi.symm))
          exact congrArg Subtype.val (hsingle j hje)
      have h1 : ((Finset.univ.erase i).noncommProd (fun j => (x j : Y))
          (fun j _ k _ hjk => commA j k hjk)) * (x i : Y) = 1 := by
        rw [Finset.noncommProd_erase_mul (Finset.univ) (Finset.mem_univ i)
          (fun j => (x j : Y)) (fun j _ k _ hjk => commA j k hjk), hprod]
      rw [hP1, one_mul] at h1
      exact Subtype.ext h1
    · exact hsingle i hi
  have hrange : f.range = ⨆ i : {i // i ∈ s}, A i := Subgroup.noncommPiCoprod_range
  have hcod : ∀ x : (∀ i : {i // i ∈ s}, A i),
      f x ∈ (⨆ i : {i // i ∈ s}, A i) := by
    intro x
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let φ : (∀ i : {i // i ∈ s}, A i) →* ↥(⨆ i : {i // i ∈ s}, A i) :=
    f.codRestrict _ hcod
  have hφ_inj : Function.Injective φ := fun a b h =>
    hf_inj (Subtype.ext_iff.mp h)
  have hφ_surj : Function.Surjective φ := by
    intro y
    have hy : (y : Y) ∈ f.range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  let e : (∀ i : {i // i ∈ s}, A i) ≃* ↥(⨆ i : {i // i ∈ s}, A i) :=
    MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have hsup_eq : (⨆ i ∈ s, A i) = ⨆ i : {i // i ∈ s}, A i := by
    simpa using (iSup_subtype'' (s : Set ι) (fun i : ι => A i)).symm
  calc CFSG.Open.pRank p (⨆ i ∈ s, A i)
      = CFSG.Open.pRank p (⨆ i : {i // i ∈ s}, A i) := by
        rw [hsup_eq]
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥(⨆ i : {i // i ∈ s}, A i)) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) _
    _ = CFSG.Open.pRank p (⊤ : Subgroup (∀ i : {i // i ∈ s}, A i)) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
    _ = CFSG.pRank p (∀ i : {i // i ∈ s}, A i) :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top p (∀ i : {i // i ∈ s}, A i)).symm
    _ = ∑ i : {i // i ∈ s}, CFSG.pRank p (A i) :=
        CFSG.Quasithin.H13.NQBlock.pRank_pi_eq (fun i : {i // i ∈ s} => A i) hp
    _ = ∑ i : {i // i ∈ s}, CFSG.Open.pRank p (A i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (A i),
          ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    _ = ∑ i ∈ s, CFSG.Open.pRank p (A i) := by
        rw [Finset.sum_coe_sort s (fun i => CFSG.Open.pRank p (A i))]

end CFSG.GroupTheory
