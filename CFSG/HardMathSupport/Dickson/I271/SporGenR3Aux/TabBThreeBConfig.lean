module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.Assembly

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
  CFSG.HardMathSupport.Solomon.Coordinator.B3B
open scoped Matrix

set_option linter.unusedSectionVars false


theorem exists_z_sylow_aut :
    ∃ z : NativeSporadic.B, orderOf z = 3 ∧ rk z = 2916 ∧
      (∃ P : Subgroup NativeSporadic.B,
        P ≤ Subgroup.centralizer ({z} : Set NativeSporadic.B) ∧
        Nat.card P =
          3 ^ (Nat.card (Subgroup.centralizer ({z} : Set NativeSporadic.B))).factorization 3 ∧
        ∀ c ∈ P, (∀ g ∈ P, c * g = g * c) → c ∈ Subgroup.zpowers z) ∧
      ∀ J : Subgroup NativeSporadic.B,
        CFSG.Open.IsComponentOf J (Subgroup.centralizer ({z} : Set NativeSporadic.B)) →
        9 ∣ (Subgroup.center J).index → 3 ^ 8 ∣ Nat.card (MulAut J) := by
  obtain ⟨x, y, z, g, hH, hy3, hgx, hgy, hgz, hrk⟩ := bNF_holds
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hn : 0 < 4 := by norm_num
  have hz3 : z ^ 3 = 1 := hH.zp
  have hdX : ∀ (k : Fin 2) (j : Fin 4), ∀ i < 9,
      (nfXData.getD (4 * k.val + j.val) []).getD i 0 < 3 := by
    set_option maxRecDepth 100000 in decide
  have hdY : ∀ (k : Fin 2) (j : Fin 4), ∀ i < 9,
      (nfYData.getD (4 * k.val + j.val) []).getD i 0 < 3 := by
    set_option maxRecDepth 100000 in decide
  set Q := heisSub x y with hQ
  have hgxQ : ∀ k j, g k * x j * (g k)⁻¹ ∈ Q := fun k j => by
    rw [hgx k j, nfProd_eq_heisNF _ _ _ _ (hdX k j)]
    exact heisNF_mem hH hn _ _
  have hgyQ : ∀ k j, g k * y j * (g k)⁻¹ ∈ Q := fun k j => by
    rw [hgy k j, nfProd_eq_heisNF _ _ _ _ (hdY k j)]
    exact heisNF_mem hH hn _ _
  have hgN : ∀ k, g k ∈ Subgroup.normalizer (Q : Set NativeSporadic.B) := fun k =>
    mem_normalizer_of_conj_mem (hgxQ k) (hgyQ k)
  have hmat : ∀ k : Fin 2, heisMat hH hy3 (g k) = tMat k.val := fun k =>
    heisMat_eq_of_nf hH hy3 hn (tMat k.val)
      (fun j => ⟨_, by
        rw [hgx k j, nfProd_eq_heisNF _ _ _ _ (hdX k j)]
        congr 1
        funext i
        simp [tMat]⟩)
      (fun j => ⟨_, by
        rw [hgy k j, nfProd_eq_heisNF _ _ _ _ (hdY k j)]
        congr 1
        funext i
        simp [tMat]⟩)
  have hmat0 : heisMat hH hy3 (g 0) = tA := by
    have h0 := hmat 0
    simp only [Fin.val_zero] at h0
    rw [h0, tMat_zero]
  have hmat1 : heisMat hH hy3 (g 1) = tB := by
    have h1 := hmat 1
    simp only [Fin.val_one] at h1
    rw [h1, tMat_one]
  set L : Subgroup NativeSporadic.B :=
    Subgroup.closure (Set.range g ∪ (Set.range x ∪ Set.range y)) with hL
  have hQL : Q ≤ L := Subgroup.closure_mono Set.subset_union_right
  have hxQ : ∀ i, x i ∈ Q := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hyQ : ∀ i, y i ∈ Q := fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hLN : L ≤ Subgroup.normalizer (Q : Set NativeSporadic.B) := by
    rw [hL, Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hgN k
    · exact Subgroup.le_normalizer (hxQ i)
    · exact Subgroup.le_normalizer (hyQ i)
  set X := Subgroup.centralizer ({z} : Set NativeSporadic.B) with hX
  have hLX : L ≤ Subgroup.normalizer (X : Set NativeSporadic.B) := by
    rw [hL, Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact mem_normalizer_centralizer_of_conj_eq_sq hz3 (hgz k)
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (hH.zx i))
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (hH.zy i))
  have hgL : ∀ k, g k ∈ L := fun k => Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)
  have hHim : sylH ≤ (heisRepL hH hy3 hn L hLN).range := by
    refine sylH_le.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ (rfl | rfl)
    · exact mem_range_heisRepL hH hy3 hn L hLN (hgL 0) (by rw [hmat0]; rfl)
    · exact mem_range_heisRepL hH hy3 hn L hLN (hgL 1) (by rw [hmat1]; rfl)
  have hG3 : (Nat.card NativeSporadic.B).factorization 3 ≤ 2 * 4 + 1 + 4 := by
    rw [factorization_card_B_three]
  have hCQ := hCQ_of_image hH hy3 hn L hQL hLN 4 sylH hHim card_sylH hG3
  have hhN : ∀ i : Fin 2, (![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] : Fin 2 → NativeSporadic.B) i ∈
      Subgroup.normalizer (Q : Set NativeSporadic.B) := by
    intro i
    fin_cases i
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hgN 0) (hgN 1)) 60
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hgN 1) (hgN 0)) 60
  have hmat60 : ∀ i : Fin 2,
      heisMat hH hy3 ((![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] : Fin 2 → NativeSporadic.B) i) =
        hM i := by
    intro i
    fin_cases i
    · show heisMat hH hy3 ((g 0 * g 1) ^ 60) = hA
      rw [heisMat_pow hH hy3 (Subgroup.mul_mem _ (hgN 0) (hgN 1)),
        heisMat_mul hH hy3 (hgN 0) (hgN 1), hmat0, hmat1]
      exact pow_sixty_tA_tB
    · show heisMat hH hy3 ((g 1 * g 0) ^ 60) = hB
      rw [heisMat_pow hH hy3 (Subgroup.mul_mem _ (hgN 1) (hgN 0)),
        heisMat_mul hH hy3 (hgN 1) (hgN 0), hmat0, hmat1]
      exact pow_sixty_tB_tA
  have hdich : ∀ N : Subgroup NativeSporadic.B, N ≤ Q →
      (∀ a ∈ L, a ^ 60 ∈ Subgroup.normalizer (N : Set NativeSporadic.B)) →
        N ≤ Subgroup.zpowers z ∨ N = Q := by
    intro N hNQ hNn
    refine dich_of_irred hH hy3 hn ![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] hhN
      (fun U hU => irred_hAB U fun i v hv => by
        have := hU i v hv
        rwa [hmat60 i] at this) N hNQ (fun i => ?_)
    fin_cases i
    · exact hNn _ (Subgroup.mul_mem _ (hgL 0) (hgL 1))
    · exact hNn _ (Subgroup.mul_mem _ (hgL 1) (hgL 0))
  have hidx : ¬ (Subgroup.zpowers z).relIndex Q ∣ (6 : ℕ).factorial := by
    rw [hQ, relIndex_zpowers_heisSub hH hy3 hn]
    decide
  have hG : ¬ 9 ^ (6 + 1) ∣ Nat.card NativeSporadic.B := by
    intro hd
    have h14 : 3 ^ 14 ∣ Nat.card NativeSporadic.B := by
      have : (9 : ℕ) ^ (6 + 1) = 3 ^ 14 := by norm_num
      rwa [this] at hd
    have hpos : Nat.card NativeSporadic.B ≠ 0 := Nat.card_pos.ne'
    have := (Nat.prime_three.pow_dvd_iff_le_factorization hpos).1 h14
    rw [factorization_card_B_three] at this
    omega
  have hm : ∀ k, 0 < k → k ≤ 6 → k ∣ 60 := by
    intro k hk0 hk6
    interval_cases k <;> decide
  have main := component_relIndex_dvd_card_mulAut_exp z X Q L 6 60 hm hQL hLN hLX hCQ hdich hidx hG
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzQ : z ∈ Q := z_mem hH hn
  have hQX : Q ≤ X := by
    rw [hQ, heisSub, Subgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hH.zx i)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hH.zy i)
  have hQcard : Nat.card Q = 3 ^ (2 * 4 + 1) := card_heisSub hH hy3 hn
  have hQpg : IsPGroup 3 (Q.subgroupOf X) :=
    IsPGroup.of_card ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv).trans hQcard)
  obtain ⟨S, hS⟩ := hQpg.exists_le_sylow
  set P : Subgroup NativeSporadic.B := (S : Subgroup X).map X.subtype with hPdef
  have hPX : P ≤ X := Subgroup.map_subtype_le _
  have hPcard : Nat.card P = 3 ^ (Nat.card X).factorization 3 := by
    rw [hPdef, Subgroup.card_map_of_injective X.subtype_injective, Sylow.card_eq_multiplicity]
  have hQP : Q ≤ P := fun q hq => ⟨⟨q, hQX hq⟩, hS (Subgroup.mem_subgroupOf.2 hq), rfl⟩
  have hPpg : IsPGroup 3 P := S.isPGroup'.map X.subtype
  refine ⟨z, orderOf_z hH, hrk, ⟨P, hPX, hPcard, ?_⟩, ?_⟩
  · intro c hcP hcomm
    have hzP : z ∈ P := hQP hzQ
    set A : Subgroup NativeSporadic.B := Subgroup.zpowers c ⊔ Subgroup.zpowers z with hAdef
    have hAP : A ≤ P := sup_le (Subgroup.zpowers_le.2 hcP) (Subgroup.zpowers_le.2 hzP)
    have hApg : IsPGroup 3 A := hPpg.to_le hAP
    have hAc : A ≤ Subgroup.centralizer (Q : Set NativeSporadic.B) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro q hq
        exact (hcomm q (hQP hq)).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro q hq
        exact Subgroup.mem_centralizer_singleton_iff.1 (hQX hq)
    have hcardA := hCQ A hAc hApg
    have hz3c : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, orderOf_z hH]
    have hEq : Subgroup.zpowers z = A :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hz3c]; exact hcardA)
    have hcA : c ∈ A := (le_sup_left : Subgroup.zpowers c ≤ A) (Subgroup.mem_zpowers c)
    rwa [← hEq] at hcA
  · intro J hJ h9
    have hd := main J hJ h9
    rw [hQ, relIndex_zpowers_heisSub hH hy3 hn] at hd
    have e : (3 : ℕ) ^ (2 * 4) = 3 ^ 8 := by norm_num
    rwa [e] at hd

end CFSG.HardMathSupport.Dickson.I271
