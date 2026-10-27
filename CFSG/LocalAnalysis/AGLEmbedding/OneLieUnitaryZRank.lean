module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin
open scoped IsMulCommutative

section Rank

variable {Y : Type} [Group Y] [Finite Y]

theorem succ_le_pRank_of_components {q : ℕ} (hq : q.Prime) {ι : Type} [Finite ι]
    (L : ι → Subgroup Y) (hL : ∀ i, IsComponentOf (L i) ⊤) (hinj : Function.Injective L)
    (A C : Subgroup Y) (a : ι → Y) (haA : ∀ i, a i ∈ A) (haL : ∀ i, a i ∈ L i)
    (haZ : ∀ i, a i ∉ Subgroup.centralizer (L i : Set Y)) (haC : ∀ i, a i ^ q ∈ C)
    (hCL : ∀ i, C ≤ Subgroup.centralizer (L i : Set Y)) {w : Y} (hwA : w ∈ A)
    (hwL : ∀ i, w ∈ Subgroup.centralizer (L i : Set Y)) (hwq : w ^ q = 1) (hwC : w ∉ C) :
    Nat.card ι + 1 ≤ Open.pRank q A := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hcommL : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ z ∈ L j, x * z = z * x := by
    intro i j hij x hx z hz
    have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hL i) (hL j)
      (fun h => hij (hinj h))
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h hx
    exact (Subgroup.mem_centralizer_iff.mp hle z hz).symm
  set S : Set Y := Set.range a ∪ {w} with hS
  have hpair : S.Pairwise Commute := by
    have haw : ∀ i, Commute (a i) w := fun i =>
      Subgroup.mem_centralizer_iff.mp (hwL i) (a i) (haL i)
    rintro x (⟨i, rfl⟩ | hx) y (⟨j, rfl⟩ | hy) -
    · by_cases hij : i = j
      · rw [hij]
      · exact hcommL i j hij _ (haL i) _ (haL j)
    · rw [Set.mem_singleton_iff.mp hy]
      exact haw i
    · rw [Set.mem_singleton_iff.mp hx]
      exact (haw j).symm
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  set B : Subgroup Y := Subgroup.closure S with hB
  have : IsMulCommutative B := Subgroup.isMulCommutative_closure hpair
  let _ : CommGroup B := inferInstance
  have hcommB : ∀ x ∈ B, ∀ z ∈ B, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : B) ⟨z, hz⟩)
  have hBA : B ≤ A := (Subgroup.closure_le A).mpr (by
    rintro _ (⟨i, rfl⟩ | hx)
    · exact haA i
    · rw [Set.mem_singleton_iff.mp hx]
      exact hwA)
  have hpow : ∀ b ∈ B, b ^ q ∈ C := by
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | hx
      · exact haC i
      · rw [Set.mem_singleton_iff.mp hx, hwq]
        exact C.one_mem
    | one => simp
    | mul x z hx hz ihx ihz =>
      rw [Commute.mul_pow (hcommB x hx z hz)]
      exact C.mul_mem ihx ihz
    | inv x hx ihx =>
      rw [inv_pow]
      exact C.inv_mem ihx
  have hk : q ^ (Nat.card ι + 1) ≤ (C.subgroupOf B).index := by
    let g : ι → B := fun i => ⟨a i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩
    let wB : B := ⟨w, Subgroup.subset_closure (Or.inr rfl)⟩
    let f : (ι → Fin q) × Fin q → B ⧸ C.subgroupOf B :=
      fun c => (QuotientGroup.mk ((∏ i, g i ^ (c.1 i : ℕ)) * wB ^ (c.2 : ℕ)) :
        B ⧸ C.subgroupOf B)
    have hf : Function.Injective f := by
      rintro ⟨c, ε⟩ ⟨c', ε'⟩ hcc'
      have hmem := QuotientGroup.eq.mp hcc'
      set d : ι → ℤ := fun i => (c' i : ℤ) - (c i : ℤ) with hd
      set δ : ℤ := (ε' : ℤ) - (ε : ℤ) with hδ
      have hprod : ((∏ i, g i ^ (c i : ℕ)) * wB ^ (ε : ℕ))⁻¹ *
          ((∏ i, g i ^ (c' i : ℕ)) * wB ^ (ε' : ℕ)) = (∏ i, g i ^ d i) * wB ^ δ := by
        have h1 : (∏ i, g i ^ (c i : ℕ))⁻¹ * ∏ i, g i ^ (c' i : ℕ) = ∏ i, g i ^ d i := by
          rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hd, zpow_sub, zpow_natCast, zpow_natCast, mul_comm]
        have h2 : (wB ^ (ε : ℕ))⁻¹ * wB ^ (ε' : ℕ) = wB ^ δ := by
          rw [hδ, zpow_sub, zpow_natCast, zpow_natCast, mul_comm]
        rw [mul_inv, mul_mul_mul_comm, h1, h2]
      simp only at hmem
      rw [hprod] at hmem
      have hmemC : (((∏ i, g i ^ d i) * wB ^ δ : B) : Y) ∈ C := Subgroup.mem_subgroupOf.mp hmem
      have hc : c = c' := by
        funext j
        have hwC' : (((∏ i, g i ^ d i) * wB ^ δ : B) : Y) ∈
            Subgroup.centralizer (L j : Set Y) := hCL j hmemC
        have hwδ : ((wB ^ δ : B) : Y) ∈ Subgroup.centralizer (L j : Set Y) := by
          rw [Subgroup.coe_zpow]
          exact Subgroup.zpow_mem _ (hwL j) _
        rw [Subgroup.coe_mul] at hwC'
        have hwC : ((∏ i, g i ^ d i : B) : Y) ∈ Subgroup.centralizer (L j : Set Y) :=
          (Subgroup.mul_mem_cancel_right _ hwδ).mp hwC'
        rw [← Finset.mul_prod_erase Finset.univ (fun i => g i ^ d i) (Finset.mem_univ j),
          Subgroup.coe_mul] at hwC
        have hrest : ((∏ i ∈ Finset.univ.erase j, g i ^ d i : B) : Y) ∈
            Subgroup.centralizer (L j : Set Y) := by
          refine Finset.prod_induction _
            (fun b : B => (b : Y) ∈ Subgroup.centralizer (L j : Set Y))
            (fun b b' hb hb' => by rw [Subgroup.coe_mul]; exact Subgroup.mul_mem _ hb hb')
            (by simp) fun i hi => ?_
          rw [Subgroup.coe_zpow]
          refine Subgroup.zpow_mem _ ?_ _
          exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
            (hcommL i j (Finset.ne_of_mem_erase hi) _ (haL i) z hz).symm
        have hjC : a j ^ d j ∈ Subgroup.centralizer (L j : Set Y) := by
          have := (Subgroup.mul_mem_cancel_right _ hrest).mp hwC
          rwa [Subgroup.coe_zpow] at this
        have hdvd : (q : ℤ) ∣ d j := by
          by_contra hnd
          have hcop : IsCoprime (d j) (q : ℤ) := by
            rw [Int.isCoprime_iff_gcd_eq_one]
            show Nat.gcd (d j).natAbs (q : ℤ).natAbs = 1
            rw [Int.natAbs_natCast]
            exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr
              (fun h => hnd (Int.natCast_dvd.mpr h)))
          obtain ⟨u, v, huv⟩ := hcop
          have haj : a j ∈ Subgroup.centralizer (L j : Set Y) := by
            have hq' : a j ^ q ∈ Subgroup.centralizer (L j : Set Y) := hCL j (haC j)
            have h1 : a j = (a j ^ d j) ^ u * ((a j ^ q) ^ v) := by
              rw [← zpow_mul, ← zpow_natCast (a j) q, ← zpow_mul, ← zpow_add]
              conv_lhs => rw [← zpow_one (a j)]
              congr 1
              linarith
            rw [h1]
            exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hjC u) (Subgroup.zpow_mem _ hq' v)
          exact haZ j haj
        have hd0 : d j = 0 := by
          refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
          have h1 := (c j).isLt
          have h2 := (c' j).isLt
          rw [abs_lt]
          simp only [hd]
          constructor <;> omega
        have : ((c j : ℕ) : ℤ) = ((c' j : ℕ) : ℤ) := by
          have h0 := hd0
          simp only [hd] at h0
          omega
        exact Fin.ext (by exact_mod_cast this)
      refine Prod.ext hc ?_
      have hd0 : ∀ i, d i = 0 := fun i => by simp only [hd, hc, sub_self]
      have hprod1 : (∏ i, g i ^ d i) = 1 := by
        simp only [hd0, zpow_zero, Finset.prod_const_one]
      rw [hprod1, one_mul, Subgroup.coe_zpow] at hmemC
      have hdvd : (q : ℤ) ∣ δ := by
        by_contra hnd
        have hcop : IsCoprime δ (q : ℤ) := by
          rw [Int.isCoprime_iff_gcd_eq_one]
          show Nat.gcd δ.natAbs (q : ℤ).natAbs = 1
          rw [Int.natAbs_natCast]
          exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr
            (fun h => hnd (Int.natCast_dvd.mpr h)))
        obtain ⟨u, v, huv⟩ := hcop
        apply hwC
        have h1 : w = (w ^ δ) ^ u * ((w ^ q) ^ v) := by
          rw [← zpow_mul, ← zpow_natCast w q, ← zpow_mul, ← zpow_add]
          conv_lhs => rw [← zpow_one w]
          congr 1
          linarith
        rw [h1, hwq, one_zpow, mul_one]
        exact C.zpow_mem hmemC u
      have hδ0 : δ = 0 := by
        refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
        have h1 := ε.isLt
        have h2 := ε'.isLt
        rw [abs_lt]
        simp only [hδ]
        constructor <;> omega
      have : ((ε : ℕ) : ℤ) = ((ε' : ℕ) : ℤ) := by
        simp only [hδ] at hδ0
        omega
      exact Fin.ext (by exact_mod_cast this)
    have hcard : Nat.card ((ι → Fin q) × Fin q) = q ^ (Nat.card ι + 1) := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin q), Fintype.card_fin,
        pow_succ]
    rw [← hcard]
    exact Nat.card_le_card_of_injective f hf
  exact (le_pRank_of_pow_mem hq B C hcommB hpow hk).trans
    (PreuniquenessRankFour.Helpers.pRank_mono q hq hBA)

theorem succ_le_pRank_of_not_mem_normalizer {q r : ℕ} (hq : q.Prime) [Fact r.Prime]
    (hrq : r ≠ q) {L : Subgroup Y} (hL : IsComponentOf L ⊤) {t : Y}
    (ht : IsPGroup r (Subgroup.zpowers t)) (htL : t ∉ Subgroup.normalizer (L : Set Y))
    {A : Subgroup Y} (htA : t ∈ A) {y : Y} (hyA : y ∈ A) (hyL : y ∈ L)
    (hyq : IsPGroup q (Subgroup.zpowers y)) (hyZ : y ∉ Subgroup.centralizer (L : Set Y))
    {W : Subgroup Y} (hWA : W ≤ A)
    (hWL : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → W ≤ Subgroup.centralizer (L' : Set Y))
    (htW : ∀ w ∈ W, t * w * t⁻¹ = w) (hWq : ∀ w ∈ W, w ^ q = 1) (hWc : ¬ IsCyclic W) :
    r + 1 ≤ Open.pRank q A := by
  have hr : r.Prime := Fact.out
  obtain ⟨e, he1, he2⟩ := exists_pow_not_mem_centralizer hyq hyZ
  set a := y ^ q ^ e with ha
  have haL : a ∈ L := L.pow_mem hyL _
  have haA : a ∈ A := A.pow_mem hyA _
  set Lc : ℕ → Subgroup Y := fun k => L.map (MulAut.conj (t ^ k)).toMonoidHom with hLcdef
  have hLc : ∀ k, IsComponentOf (Lc k) ⊤ := fun k =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff _ _).mpr hL
  have hconjL : ∀ k : ℕ, ∀ x ∈ L, t ^ k * x * (t ^ k)⁻¹ ∈ Lc k := fun k x hx =>
    ⟨x, hx, rfl⟩
  have hconjC : ∀ k : ℕ, ∀ x ∈ Subgroup.centralizer (L : Set Y),
      t ^ k * x * (t ^ k)⁻¹ ∈ Subgroup.centralizer (Lc k : Set Y) := by
    intro k x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have hlx := Subgroup.mem_centralizer_iff.mp hx l hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc t ^ k * l * (t ^ k)⁻¹ * (t ^ k * x * (t ^ k)⁻¹) = t ^ k * (l * x) * (t ^ k)⁻¹ := by
          group
      _ = t ^ k * (x * l) * (t ^ k)⁻¹ := by rw [hlx]
      _ = t ^ k * x * (t ^ k)⁻¹ * (t ^ k * l * (t ^ k)⁻¹) := by group
  have hconjNC : ∀ k : ℕ, ∀ x, x ∉ Subgroup.centralizer (L : Set Y) →
      t ^ k * x * (t ^ k)⁻¹ ∉ Subgroup.centralizer (Lc k : Set Y) := by
    intro k x hx hmem
    apply hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := Subgroup.mem_centralizer_iff.mp hmem _ (hconjL k l hl)
    have h2 : t ^ k * (l * x) * (t ^ k)⁻¹ = t ^ k * (x * l) * (t ^ k)⁻¹ := by
      calc t ^ k * (l * x) * (t ^ k)⁻¹ = t ^ k * l * (t ^ k)⁻¹ * (t ^ k * x * (t ^ k)⁻¹) := by
            group
        _ = t ^ k * x * (t ^ k)⁻¹ * (t ^ k * l * (t ^ k)⁻¹) := h1
        _ = t ^ k * (x * l) * (t ^ k)⁻¹ := by group
    simpa using h2
  set f : ℕ → Y := fun k => t ^ k * a ^ q * (t ^ k)⁻¹ with hf
  have hfL : ∀ k, f k ∈ Lc k := fun k => hconjL k _ (L.pow_mem haL q)
  have hfC : ∀ k, f k ∈ Subgroup.centralizer (Lc k : Set Y) := fun k => hconjC k _ he2
  have hfCj : ∀ k j : ℕ, f k ∈ Subgroup.centralizer (Lc j : Set Y) := by
    intro k j
    by_cases hkj : Lc k = Lc j
    · rw [← hkj]
      exact hfC k
    · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hLc k) (hLc j)
        hkj
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc (hfL k)
  have hcomm : ∀ i j : ℕ, Commute (t ^ i * a ^ q * (t ^ i)⁻¹) (t ^ j * a ^ q * (t ^ j)⁻¹) :=
    fun i j => Subgroup.mem_centralizer_iff.mp (hfCj j i) (f i) (hfL i)
  have hcop : Nat.Coprime (orderOf t) q := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp ht
    rw [Nat.card_zpowers] at hm
    rw [hm]
    exact Nat.Coprime.pow_left m ((Nat.coprime_primes hr hq).mpr hrq)
  obtain ⟨g, hg⟩ := exists_forall_mem_zpowers_of_conj hcomm hcop
  set C : Subgroup Y := Subgroup.closure (Set.range f) with hC
  obtain ⟨w, hw, hwC⟩ : ∃ w ∈ W, w ∉ C := by
    by_contra hcon
    push Not at hcon
    have hWg : W ≤ Subgroup.zpowers g := fun w hw => hg w (hcon w hw) (htW w hw) (hWq w hw)
    exact hWc (Subgroup.isCyclic_of_le hWg)
  have hCL : ∀ i : ℕ, C ≤ Subgroup.centralizer (Lc i : Set Y) := fun i =>
    (Subgroup.closure_le _).mpr (by rintro _ ⟨k, rfl⟩; exact hfCj k i)
  have h := succ_le_pRank_of_components hq (fun i : Fin r => Lc i) (fun i => hLc i)
    (injective_conj_pow_of_not_mem_normalizer ht htL) A C
    (fun i : Fin r => t ^ (i : ℕ) * a * (t ^ (i : ℕ))⁻¹)
    (fun i => A.mul_mem (A.mul_mem (A.pow_mem htA _) haA) (A.inv_mem (A.pow_mem htA _)))
    (fun i => hconjL i a haL) (fun i => hconjNC i a he1)
    (fun i => by rw [conj_pow]; exact Subgroup.subset_closure ⟨i, rfl⟩) (fun i => hCL i)
    (hWA hw) (fun i => hWL _ (hLc i) hw) (hWq w hw) hwC
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h

end Rank

end CFSG.AGLEmbedding
