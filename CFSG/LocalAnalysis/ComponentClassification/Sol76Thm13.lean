module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux
public import CFSG.Open.AschbacherComponentTypeTheorem5
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Open
open scoped commutatorElement

theorem false_of_isSolomonChoice
        {𝒜 : Thm13Ambient} (h313 : Lemma313InputFor 𝒜) (h316 : Lemma316InputFor 𝒜) {G : Type}
    [Group G] [Finite G] (hbelow : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKH, hCb⟩ := h316 G hbelow N hN
  obtain ⟨h1, h2⟩ := h313 G hbelow N hN _ hKH rfl hCb
  obtain ⟨hKB, hviol, -⟩ := hN
  obtain ⟨r, K, -, hKiff, hr2, hcommN, -, -⟩ := hKB
  set D := solomonKStarOf N with hD
  set H := normalizer (D : Set G) with hH
  have hKmem : ∀ i, K i ∈ kStarComponents N := fun i => (hKiff (K i)).mpr ⟨i, rfl⟩
  have hDgen : ⨆ i, K i = D := by
    apply le_antisymm
    · exact iSup_le fun i => le_iSup₂_of_le (K i) (hKmem i) le_rfl
    · refine iSup₂_le fun J hJ => ?_
      obtain ⟨i, rfl⟩ := (hKiff J).mp hJ
      exact le_iSup K i
  have hKD : ∀ i, K i ≤ D := fun i => hDgen ▸ le_iSup K i
  have hDN : D ≤ N := iSup₂_le fun J hJ => hJ.1.1
  have hKtwo : ∀ i, IsTwoComponentIn (K i) D := fun i =>
    isTwoComponentIn_of_le (hKmem i).1 (hKD i) hDN
  have hcommD : ∀ i j, i ≠ j → ⁅K i, K j⁆ ≤ oddCoreIn D := by
    intro i j hij
    refine le_trans (le_inf (hcommN i j hij) ?_) (oddCoreIn_inf_le hDN)
    exact commutator_le.mpr fun x hx y hy =>
      D.mul_mem (D.mul_mem (D.mul_mem (hKD i hx) (hKD j hy)) (D.inv_mem (hKD i hx)))
        (D.inv_mem (hKD j hy))
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hviol
    have hDn : D.Normal := normalizer_eq_top_iff.mp htop
    rw [← hDgen]
    exact iSup_le fun i => le_solomonKStarOf_top (hKtwo i) hDn (hKmem i).2
  set Abar : Fin r → Subgroup (↥D ⧸ aschbacherThm5OddCore ↥D) :=
    fun i => ((K i).subgroupOf D).map (QuotientGroup.mk' _) with hAbar
  have hpre : ∀ i, aschbacherThm5Preimage D (Abar i) = K i ⊔ oddCoreIn D := fun i =>
    aschbacherThm5Preimage_map_subgroupOf (hKD i)
  have hcore : aschbacherThm5Core D = oddCoreIn D := aschbacherThm5Core_eq_oddCoreIn D
  have hq : ∀ i, CFSG.IsQuasisimple ↥(Abar i) := fun i =>
    isQuasisimple_image (hKtwo i) _ (aschbacherThm5OddCore_eq_pPrimeCore' _)
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    rintro i j hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, aschbacherThm5OddCore_eq_pPrimeCore']
    have hmem : ((a * b)⁻¹ * (b * a) : D) ∈ ((oddCoreIn D).subgroupOf D) := by
      rw [mem_subgroupOf]
      have h3 : (((a * b)⁻¹ * (b * a) : D) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
        group
      rw [h3]
      exact hcommD j i (Ne.symm hij) (commutator_mem_commutator (inv_mem hb) (inv_mem ha))
    rw [mem_subgroupOf] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    rwa [Subtype.ext hyx] at hy
  have hdistinct : Function.Injective Abar := by
    intro i j hij
    by_contra hne
    obtain ⟨-, -, a, b, hab⟩ := hq i
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have hbj : (b : ↥D ⧸ aschbacherThm5OddCore ↥D) ∈ Abar j := by rw [← hij]; exact b.2
    exact Subtype.ext (hcomm i j hne a a.2 b hbj)
  have hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i) := fun i =>
    ⟨1, fun _ => Abar i, one_pos, fun _ => ⟨le_rfl, (hq i).1.commutator_eq_top, (hq i).2.1⟩,
      fun l m hlm => absurd (Subsingleton.elim l m) hlm, iSup_const⟩
  have hgen : ⨆ i, Abar i = ⊤ := iSup_map_subgroupOf_eq_top hKD hDgen _
  have hperm : ∀ h ∈ normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
    intro h hh i
    simp only [hpre]
    exact exists_map_conj_eq hKtwo hDgen hh i
  have hinv : ∀ i, ∃ b ∈ K i, orderOf b = 2 := fun i =>
    exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans
      (two_le_pRank_of_mem_solomonKStar (hKmem i).2))
  have hcov : ∀ i (s : G), (∃ k : ℕ, s ^ (2 ^ k) = 1) →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) s →
      s ∈ H := by
    rintro i s ⟨k, hk⟩ hs
    rw [hcore, hpre] at hs
    obtain ⟨b, hbK, hb⟩ := hinv i
    exact mem_of_centralizes_quotient (hKD i) le_normalizer hbK hb (hCb _ (hKmem i) b hbK hb) hk hs
  have hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set G) := by
    intro i j t g ht htZ hti htj
    have htH := hcov i t ht hti
    have htg : ∃ k : ℕ, (g⁻¹ * t * g) ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := ht
      refine ⟨k, ?_⟩
      rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hk]
      group
    have htgH := hcov j _ htg htj
    rw [hcore, hpre] at hti htj
    exact h1 (K i) (hKmem i) (K j) (hKmem j) t g htH htgH ht htZ
      (fun a ha => hti a (mem_sup_left ha)) (fun a ha => htj a (mem_sup_left ha))
  have hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) →
      g ∈ normalizer (D : Set G) := by
    intro i g X hX hXa
    rw [hcore, hpre] at hXa
    exact h2 (K i) (hKmem i) g X hX (fun a ha => hXa a (mem_sup_left ha))
  rcases Open.aschbacher_component_type_theorem_five G D r (by omega) Abar hdistinct hsemisimple
    hcomm hgen hperm hi hii hHtop with h | ⟨-, hrank⟩
  · omega
  · have h3 := (hrank ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)).2.1
    rw [hpre] at h3
    have h4 := two_le_pRank_of_mem_solomonKStar (hKmem ⟨0, by omega⟩).2
    have h5 := SectionRank.pRank_mono (p := 2) (by norm_num)
      (le_sup_left : K ⟨0, by omega⟩ ≤ K ⟨0, by omega⟩ ⊔ oddCoreIn D)
    omega

theorem solomonThm13Input_of_inputs
        (h313 : Lemma313Input) (h316 : Lemma316Input) : SolomonThm13Input :=
  solomonThm13Input_of_noChoice fun _ _ _ hbelow _ hN =>
    false_of_isSolomonChoice h313 h316 hbelow hN

end CFSG.ComponentClassification.Sol76
