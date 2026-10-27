module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieListInvolveW
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
import CFSG.LocalAnalysis.AGLEmbedding.JStarElimAlt
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedIII
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SpFourEightRank
import CFSG.Sporadic.J3
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem le_three_or_eq_four_of_pow_dvd_factorial {p k : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (h : p ^ k ∣ (3 * p).factorial) : k ≤ 3 ∨ (p = 3 ∧ k = 4) := by
  have hne : (3 * p).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [padicValNat_dvd_iff_le hne, mul_comm, padicValNat_factorial_mul] at h
  rcases eq_or_ne p 3 with rfl | hp3'
  · have h6 : padicValNat 3 (Nat.factorial 3) = 1 := by
      rw [show Nat.factorial 3 = 3 * 2 by decide, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    omega
  · have h6 : padicValNat p (Nat.factorial 3) = 0 := by
      refine padicValNat.eq_zero_of_not_dvd fun hdvd => ?_
      rw [show Nat.factorial 3 = 6 by decide] at hdvd
      have h6 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases p <;> simp_all (config := {decide := true})
    omega

theorem pow_dvd_pow_mul_of_pow_dvd_factorial {p k n : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (hn : 3 ≤ n) (h : p ^ k ∣ (3 * p).factorial) : p ^ k ∣ p ^ n * n := by
  rcases le_three_or_eq_four_of_pow_dvd_factorial hp3 h with hk | ⟨rfl, rfl⟩
  · exact (pow_dvd_pow p (hk.trans hn)).trans (dvd_mul_right _ _)
  · rcases eq_or_lt_of_le hn with rfl | hn4
    · exact dvd_refl _
    · exact (pow_dvd_pow 3 hn4).trans (dvd_mul_right _ _)

theorem card_dvd_factorial_of_alternating {p : ℕ} {L : Type} [Group L]
    (e : L ≃* alternatingGroup (Fin (3 * p))) : Nat.card L ∣ (3 * p).factorial := by
  rw [Nat.card_congr e.toEquiv]
  have h := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin (3 * p)))
  rwa [Nat.card_perm, Nat.card_fin] at h

theorem eq_of_card_linTwo_three_dvd {n N : ℕ} (hn : 3 ≤ n)
    (hN : N = 1451520 ∨ N = 1056706560 ∨ N = 4329310519296 ∨ N = 50232960)
    (h : 3 ^ n * (((3 ^ n) ^ 2 - 1) / 2) ∣ N) : N = 1056706560 ∧ n = 3 := by
  have h3n : 3 ^ n ∣ N := (Dvd.intro _ rfl).trans h
  have hn5 : n ≤ 5 := by
    by_contra hlt
    have h6 : 3 ^ 6 ∣ N := (pow_dvd_pow 3 (by omega)).trans h3n
    rcases hN with rfl | rfl | rfl | rfl <;> exact absurd h6 (by decide)
  interval_cases n <;> rcases hN with rfl | rfl | rfl | rfl <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem not_card_linTwo_five_dvd {n : ℕ} (hn : 3 ≤ n) :
    ¬ 5 ^ n * (((5 ^ n) ^ 2 - 1) / 2) ∣ 1318633155799591447702161609782722560000 := by
  intro h
  have h5n : 5 ^ n ∣ 1318633155799591447702161609782722560000 := (Dvd.intro _ rfl).trans h
  have hn4 : n ≤ 4 := by
    by_contra hlt
    exact absurd ((pow_dvd_pow 5 (by omega : 5 ≤ n)).trans h5n) (by decide)
  interval_cases n <;> exact absurd h (by decide)

theorem jStarElimData_of_subgroup {L : Type} [Group L] [Finite L] {p n : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center L = ⊥) (hcard : ∀ k : ℕ, p ^ k ∣ Nat.card L → p ^ k ∣ p ^ n * n)
    {Y : Subgroup L} (φ : Y →* PSL2GF p n) (hφ : Function.Surjective φ)
    (hφk : p.Coprime (Nat.card φ.ker)) : JStarElimData L p n := by
  have hker : (MulAut.conj : L →* MulAut L).ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgZ : g ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun l => by
      have h1 := congrArg (fun f : MulAut L => f l) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc l * g = g * l * g⁻¹ * g := by rw [h1]
        _ = g * l := by group
    rw [hZ] at hgZ
    exact hgZ
  refine jStarElimData_of_hom MulAut.conj le_rfl (by rw [hker]; exact IsPGroup.of_bot)
    (fun S hS => ?_) φ hφ hφk (by rw [hker, inf_bot_eq])
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  rw [hk]
  exact hcard k (hk ▸ Subgroup.card_subgroup_dvd_card S)

theorem card_of_caseThreeSurvivor {p : ℕ} {L : Type} [Group L] [Finite L]
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hlist : (∃ d : TauCeti.ValidLieTypeIndex, IsP1ChevTwoSurvivor p d ∧
          Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        (p = 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))) :
    (p = 3 ∧ (Nat.card L = 1451520 ∨ Nat.card L = 1056706560 ∨ Nat.card L = 4329310519296 ∨
      Nat.card L = 50232960) ∧
      (Nat.card L = 1056706560 → ∃ d : TauCeti.ValidLieTypeIndex, IsSpFourEightIndex d ∧
        Nonempty (L ≃* CatGroup d))) ∨
    (p = 5 ∧ Nat.card L = 1318633155799591447702161609782722560000) := by
  rcases hlist with ⟨d, hd, ⟨e⟩⟩ | ⟨hp3, ⟨e⟩⟩
  · have hcd : Nat.card L = Nat.card (CatGroup d) := Nat.card_congr e.toEquiv
    rcases hd with ⟨hp3, q, hq, hq1, h⟩ | ⟨hp3, q, hq, hq3, h | h⟩ | ⟨hp5, h⟩
    · have hN : Nat.card L = 1451520 := by
        rw [hcd, card_catGroup_B_even (by norm_num) hq h, hq1]
        decide
      exact Or.inl ⟨hp3, Or.inl hN, fun h' => absurd (hN.symm.trans h') (by decide)⟩
    · have hN : Nat.card L = 1056706560 := by
        rw [hcd, card_catGroup_B2 h, hq, hq3]
        decide
      exact Or.inl ⟨hp3, Or.inr (Or.inl hN), fun _ => ⟨d, ⟨q, hq, hq3, h⟩, ⟨e⟩⟩⟩
    · have hN : Nat.card L = 4329310519296 := by
        rw [hcd, card_catGroup_G2_even hq h, hq3]
        decide
      exact Or.inl ⟨hp3, Or.inr (Or.inr (Or.inl hN)),
        fun h' => absurd (hN.symm.trans h') (by decide)⟩
    · have hN : Nat.card L = 1318633155799591447702161609782722560000 := by
        rw [hcd, card_catGroup_reeF4 h]
        decide
      exact Or.inr ⟨hp5, hN⟩
  · obtain ⟨b⟩ := hbr .J3
    have hN : Nat.card L = 50232960 :=
      (Nat.card_congr (e.trans b.symm).toEquiv).trans CFSG.Sporadic.J3.card_J3
    exact Or.inl ⟨hp3, Or.inr (Or.inr (Or.inr hN)),
      fun h' => absurd (hN.symm.trans h') (by decide)⟩

theorem kFactOneLieListInvolveW_of (hId : KFactOneLieIdent) (hKR8 : KFactReeOrder)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    KFactOneLieListInvolveW := by
  intro K _ _ hs hnab hcat p hp hp2 T hTnc hΓ hbig L _ _ hL hlist Y φ hφ hφk
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup L := hL
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hKL : Nat.card K ∣ Nat.card L :=
    (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card Y)
  have hLnab : ∃ a b : L, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    obtain ⟨a, b, hab⟩ := hnab
    obtain ⟨a', rfl⟩ := hφ a
    obtain ⟨b', rfl⟩ := hφ b
    apply hab
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hc a' b'))
  have hZ : Subgroup.center L = ⊥ := center_bot_of_simple_nonab hLnab
  have hO : Nonempty (L ≃* alternatingGroup (Fin (3 * p))) ∨
      (p = 3 ∧ (Nat.card L = 1451520 ∨ Nat.card L = 1056706560 ∨
        Nat.card L = 4329310519296 ∨ Nat.card L = 50232960) ∧
        (Nat.card L = 1056706560 → ∃ d : TauCeti.ValidLieTypeIndex, IsSpFourEightIndex d ∧
          Nonempty (L ≃* CatGroup d))) ∨
      (p = 5 ∧ Nat.card L = 1318633155799591447702161609782722560000) := by
    rcases hlist with hlie | hA | hJ
    · exact Or.inr (card_of_caseThreeSurvivor hbr (Or.inl hlie))
    · exact Or.inl hA
    · exact Or.inr (card_of_caseThreeSurvivor hbr (Or.inr hJ))
  obtain ⟨d, hfam, ⟨e⟩⟩ := hId K hs hnab hcat p hp hp2 T hTnc hΓ hbig
  have hcK : Nat.card K = Nat.card (CatGroup d) := Nat.card_congr e.toEquiv
  have h6 : ¬ p ^ 6 ∣ Nat.card L := by
    intro h6
    rcases hO with hA | ⟨rfl, hN, -⟩ | ⟨rfl, hN⟩
    · obtain ⟨eA⟩ := hA
      rcases le_three_or_eq_four_of_pow_dvd_factorial hp3
        (h6.trans (card_dvd_factorial_of_alternating eA)) with h | h <;> omega
    · rcases hN with hN | hN | hN | hN <;> rw [hN] at h6 <;> exact absurd h6 (by decide)
    · rw [hN] at h6
      exact absurd h6 (by decide)
  rcases hfam with ⟨n, hn3, hdn⟩ | ⟨hdU, hn2⟩ | hdR
  ·
    have hcard : Nat.card K = p ^ n * (((p ^ n) ^ 2 - 1) / 2) :=
      hcK.trans (card_catGroup_linTwo hp2 (by omega) hdn)
    obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdn
    set φ' : Y →* PSL2GF p n := ((e.trans f : K ≃* PSL2GF p n) : K →* PSL2GF p n).comp φ
    have hφ' : Function.Surjective φ' := (e.trans f).surjective.comp hφ
    have hφ'k : p.Coprime (Nat.card φ'.ker) := by
      rw [MonoidHom.ker_mulEquiv_comp]
      exact hφk
    rcases hO with hA | ⟨rfl, hN, hSp⟩ | ⟨rfl, hN⟩
    · obtain ⟨eA⟩ := hA
      exact kFactJStarElimAlt p n hp2 hn3 L ⟨eA⟩ (jStarElimData_of_subgroup hZ
        (fun k hk => pow_dvd_pow_mul_of_pow_dvd_factorial hp3 hn3
          (hk.trans (card_dvd_factorial_of_alternating eA))) φ' hφ' hφ'k)
    · obtain ⟨hN', rfl⟩ := eq_of_card_linTwo_three_dvd hn3 hN (hcard ▸ hKL)
      obtain ⟨d₁, hd₁, ⟨e₁⟩⟩ := hSp hN'
      refine jStarResidualSp48Three L hL d₁ hd₁ ⟨e₁⟩
        (jStarElimData_of_subgroup hZ (fun k hk => ?_) φ' hφ' hφ'k)
      rw [hN'] at hk
      have hk4 : k ≤ 4 := by
        by_contra hlt
        exact absurd ((pow_dvd_pow 3 (by omega : 5 ≤ k)).trans hk) (by decide)
      exact pow_dvd_pow 3 hk4
    · exact not_card_linTwo_five_dvd hn3 (hN ▸ hcard ▸ hKL)
  ·
    exact h6 ((pow_dvd_pow p (by omega)).trans
      ((pow_dvd_card_catGroup_unitary hdU).trans (hcK ▸ hKL)))
  ·
    obtain ⟨rfl, m, hm⟩ := hdR
    have ha := IsReeGTwoIndex.three_le_fieldExponent (p := 3) ⟨rfl, m, hm⟩
    have : Finite (CatGroup d) := Finite.of_equiv K e.toEquiv
    have hR := hKR8 (CatGroup d) d ⟨rfl, m, hm⟩ ⟨MulEquiv.refl _⟩
    refine h6 ((pow_dvd_pow 3 (by omega : 6 ≤ 3 * d.1.fieldExponent)).trans ?_)
    refine Dvd.dvd.trans ?_ (hcK ▸ hKL : Nat.card (CatGroup d) ∣ Nat.card L)
    rw [hR, pow_mul']
    exact (dvd_mul_right _ _).mul_right _

end CFSG.AGLEmbedding
