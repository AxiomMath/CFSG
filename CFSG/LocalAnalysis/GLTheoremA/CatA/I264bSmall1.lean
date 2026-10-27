module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U5R
public import CFSG.Sporadic.Co2Smith.SmithCo2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Prime3

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_sp62_u42 (hR : Rank23At Y) (hS : StdSubFAt Y) {K B : Subgroup Y} (h : KHyp 3 K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < 3 ^ 3)
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isSp6two i ∨ S9.isU4two i))
    (hOut : ∀ (S : Type) [Group S], catalogIs S (fun i => S9.isSp6two i ∨ S9.isU4two i) →
      ¬ 3 ∣ Nat.card (Outer S)) : False := by
  classical
  have hcomp : GLAPComponent 3 K K := glaPComponent_self_p h.qs h.core
  have hcatP : catalogIs (PSimple 3 K) (fun i => S9.isSp6two i ∨ S9.isU4two i) :=
    ys03_catalogIs_of_mulEquiv (pSimpleEquiv h.core).symm hcat
  have hlist : catalogIs (PSimple 3 K) S9.isList94 := by
    obtain ⟨i, hi, e⟩ := hcatP
    exact ⟨i, by rcases hi with hi | hi <;> [exact Or.inl hi; exact Or.inr (Or.inl hi)], e⟩
  obtain ⟨hZP, -, hrank⟩ := hR K K hcomp hlist
  have e1 : PQuot 3 K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq h.core).trans QuotientGroup.quotientBot
  have hZ : Subgroup.center ↥K = ⊥ := by
    rw [← Subgroup.map_center_eq e1, hZP, Subgroup.map_bot]
  have eZ : PSimple 3 K ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hZP).trans QuotientGroup.quotientBot
  have hcatQ : catalogIs (PQuot 3 K) (fun i => S9.isSp6two i ∨ S9.isU4two i) :=
    ys03_catalogIs_of_mulEquiv eZ hcatP
  have hout : ∀ α : MulAut (PQuot 3 K), α ^ 3 = 1 → α ∈ inner (PQuot 3 K) := fun α hα =>
    forall_cube_inner_of_card_outer (hOut _ hcatQ) α hα
  have hin : ∀ b ∈ B, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹ := by
    intro b hb
    have hbN : b⁻¹ ∈ Subgroup.normalizer (K : Set Y) :=
      Subgroup.normalizer_eq_top_iff.2 h.normal ▸ Subgroup.mem_top _
    have hb3 : (b⁻¹) ^ 3 = 1 := by
      rw [inv_pow, h.elem.2 b hb, inv_one]
    have hind : InducesInnerMod 3 K b⁻¹ :=
      inducesInnerMod_of_inner hbN (hout _ (barAut_pow_three K b⁻¹ hbN hb3))
    obtain ⟨l, hlK, hl⟩ := hind
    refine ⟨l⁻¹, K.inv_mem hlK, fun x hx => ?_⟩
    have := hl x hx
    rw [glaPPrimeCoreOf_eq_bot_p h.core, Subgroup.mem_bot] at this
    have h2 : b * x * b⁻¹ = l⁻¹ * x * l := by
      have h3 : (l⁻¹ * x * l)⁻¹ * (b⁻¹⁻¹ * x * b⁻¹) = 1 := by simpa using this
      have h4 : b⁻¹⁻¹ * x * b⁻¹ = l⁻¹ * x * l := by
        have := inv_mul_eq_one.1 h3
        exact this.symm
      simpa using h4
    simpa using h2
  have hRb : ∀ E T : Subgroup Y, E ≤ K → IsElemAbelian 3 E → T ≤ K → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set Y) → Nat.card E ≤ 9 := by
    intro E T hEK hE hTK hT2 hTne hET
    have hTO : ¬ T ≤ GLAPPrimeCoreOf 3 K := by
      rw [glaPPrimeCoreOf_eq_bot_p h.core]
      exact fun hle => hTne (le_bot_iff.1 hle)
    exact (hrank E T hEK hE hTK hT2 hTO hET).2 hcatP
  obtain ⟨F, T, E, -, -, -, -, -, -, -, -, -, -, hEK, hEel, hEcard, -⟩ :=
    hS K h.qs (by
      obtain ⟨i, hi, e⟩ := hcat
      exact ⟨i, by rcases hi with hi | hi <;> [exact Or.inr (Or.inr hi); exact Or.inl hi], e⟩)
  exact false_of_inner h hZ hin hRb ⟨E, hEK, hEel, by rw [hEcard]; norm_num⟩

end Prime3

theorem card_mulAut_of_simple_out {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {n m : ℕ}
    (hS : Nat.card S = n) (hnp : ¬ n.Prime) (hOut : Nat.card (Outer S) = m) :
    Nat.card (MulAut S) = n * m := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h1 | h1
    · exact h1
    · exfalso
      have hc : IsMulCommutative S := Subgroup.center_eq_top_iff.1 h1
      have hp := (@Group.is_simple_iff_prime_card S _ hc).1 inferInstance
      rw [hS] at hp
      exact hnp hp
  have hinner : Nat.card (inner S) = Nat.card S := by
    have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hc : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
        have := congrArg (fun α : MulAut S => α x) hg
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc x * g = g * x * g⁻¹ * g := by rw [this]
          _ = g * x := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact hc
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have hMul := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner S)
  have hOut' : Nat.card (MulAut S ⧸ inner S) = m := hOut
  rw [hinner, hS, hOut'] at hMul
  rw [hMul, mul_comm]

theorem card_mulAut_sp62 {S : Type} [Group S] (h : catalogIs S S9.isSp6two) :
    Nat.card (MulAut S) = 1451520 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isSp6two h
  have hOut : Nat.card (Outer S) = 1 := by
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq2.trans (by norm_num))
    rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
    · rw [h1, h2] at hm
      exact CFSG.ComponentClassification.Foote5.card_outer_eq_one_of_psp_three_two
        (hm.statedClassicalModel (by decide))
    · rw [h1, h2] at hm
      exact absurd hm.admissible.2.2.2 (by norm_num)
  obtain ⟨eS⟩ := bridge_sp6two h
  haveI : IsSimpleGroup CFSG.Sporadic.Co2Smith.Sp62 := CFSG.Sporadic.Co2Smith.isSimpleGroup_sp62
  haveI hsimple : IsSimpleGroup S := MulEquiv.isSimpleGroup eS
  haveI : Finite S := Finite.of_equiv _ eS.symm.toEquiv
  have hS : Nat.card S = 1451520 := by
    rw [Nat.card_congr eS.toEquiv, CFSG.Sporadic.Co2Smith.natCard_sp62]
  have := card_mulAut_of_simple_out hS (by norm_num) hOut
  simpa using this

theorem eq_three_of_sq_dvd_sp62 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ^ 2 ∣ 1451520) : p = 3 := by
  have hpN : p ∣ 1451520 := (dvd_pow_self p two_ne_zero).trans hdvd
  have h : p ∣ (2 ^ 9 * 3 ^ 4 * 5) * 7 := by norm_num; exact hpN
  have key : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 7 := by
    rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
      · rcases (Nat.Prime.dvd_mul hp).1 h'' with h3 | h3
        · exact Or.inl (hp.dvd_of_dvd_pow h3)
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h3))
      · exact Or.inr (Or.inr (Or.inl h''))
    · exact Or.inr (Or.inr (Or.inr h'))
  rcases key with h2 | h3 | h5 | h7
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  · have h5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5
    subst h5'
    norm_num at hdvd
  · have h7' : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7
    subst h7'
    norm_num at hdvd

theorem kDescFam_u42 (hR : ∀ (Y : Type) [Group Y] [Finite Y], Rank23At Y)
    (hS : ∀ (Y : Type) [Group Y] [Finite Y], StdSubFAt Y) (p : ℕ) : KDescFam p fU42 := by
  intro hp hp2 Y _ _ K B h hc hcB
  have hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two := hc
  by_cases hp3 : p = 3
  · subst hp3
    refine (false_of_sp62_u42 (hR Y) (hS Y) h hcB ?_ ?_).elim
    · obtain ⟨i, hi, e⟩ := hcat
      exact ⟨i, Or.inr hi, e⟩
    · intro S _ hSc
      obtain ⟨i, hi, e⟩ := hSc
      rcases hi with hi | hi
      · exact not_three_dvd_outer_sp6two ⟨i, hi, e⟩
      · exact not_three_dvd_outer_u4two ⟨i, hi, e⟩
  · exact (false_of_not_sq_dvd hp h hcB (MulEquiv.refl _) fun hdvd =>
      hp3 (eq_three_of_sq_dvd hp hp2 (Or.inl (card_mulAut_u4two hcat)) hdvd)).elim

theorem kDescFam_sp62 (hR : ∀ (Y : Type) [Group Y] [Finite Y], Rank23At Y)
    (hS : ∀ (Y : Type) [Group Y] [Finite Y], StdSubFAt Y) (p : ℕ) : KDescFam p fSp62 := by
  intro hp hp2 Y _ _ K B h hc hcB
  have hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isSp6two := hc
  by_cases hp3 : p = 3
  · subst hp3
    refine (false_of_sp62_u42 (hR Y) (hS Y) h hcB ?_ ?_).elim
    · obtain ⟨i, hi, e⟩ := hcat
      exact ⟨i, Or.inl hi, e⟩
    · intro S _ hSc
      obtain ⟨i, hi, e⟩ := hSc
      rcases hi with hi | hi
      · exact not_three_dvd_outer_sp6two ⟨i, hi, e⟩
      · exact not_three_dvd_outer_u4two ⟨i, hi, e⟩
  · refine (false_of_not_sq_dvd hp h hcB (MulEquiv.refl _) fun hdvd => hp3 ?_).elim
    rw [card_mulAut_sp62 hcat] at hdvd
    exact eq_three_of_sq_dvd_sp62 hp hp2 hdvd

end CFSG.LocalAnalysis.GLTheoremA
