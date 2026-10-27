module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Interface
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.PairOdd
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.EntryAll

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ2 CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

section Main

theorem subfieldPairG2_odd_all {K : Type} [Field K] [Finite K] {r : ℕ} [CharP K r]
    (hrp : r.Prime) (hr2 : r ≠ 2) (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hσ : orderOf σ = p) (g : adjointGroup .G2 K)
    (hne : (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ) :
    Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
      ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤ := by
  have hr3 : 3 ≤ r := by
    have := hrp.two_le
    omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K r] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 h')
  set R : Subgroup (adjointGroup .G2 K) := g2Fixed σ with hRdef
  set k : Subfield K := fixSubfield σ with hkdef
  have hKcard : Nat.card K = Nat.card k ^ p := by
    have := card_eq_card_fixSubfield_pow σ
    rwa [hσ] at this
  have hR : ∀ q < 12, ∀ c ∈ k, xp q c ∈ R := fun q hq c hc => rat_root_mem σ hq hc
  have hg : g ∉ R := fun hg => hne (map_conj_eq_self hg)
  obtain ⟨r₁, hr₁, r', hr', hbad⟩ := exists_bad_entryA σ h2 g hg
  set H : Subgroup (adjointGroup .G2 K) :=
    Subgroup.closure ((R : Set (adjointGroup .G2 K)) ∪
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K))) with hH
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : R.map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have hH1 : ∀ c ∈ k, xp 7 c ∈ H := fun c hc => hRH (hR 7 (by norm_num) c hc)
  have hH2 : ∀ c ∈ k, (r₁ * g * r') * xp 7 c * (r₁ * g * r')⁻¹ ∈ H := by
    intro c hc
    have h1 : r' * xp 7 c * r'⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem hr' (hR 7 (by norm_num) c hc)) (R.inv_mem hr')
    have h2 : g * (r' * xp 7 c * r'⁻¹) * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 : r₁ * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r₁⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hRH hr₁) (hRgH h2)) (H.inv_mem (hRH hr₁))
    have e : (r₁ * g * r') * xp 7 c * (r₁ * g * r')⁻¹ =
        r₁ * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r₁⁻¹ := by group
    rw [e]
    exact h3
  have h7 : Full H 7 := full_seven_of_pair_odd hr3 k hp (Or.inr (by omega)) hKcard (r₁ * g * r')
    hH1 hH2 hbad
  have hm1 : (-1 : K) ≠ 1 := fun e => h2 (by linear_combination -e)
  exact eq_top_of_subfield_gen k (t := -1) (k.neg_mem k.one_mem) (neg_ne_zero.2 one_ne_zero) hm1
    (fun q hq c hc => hRH (hR q hq c hc)) h7

theorem subfieldPairG2Odd : SubfieldPairG2Odd := by
  intro K _ _ h2 σ p hp hp5 hσ g hne
  left
  have := ringChar.charP K
  have hrp : (ringChar K).Prime := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with h | h
    · exact h
    · exact absurd h (CharP.char_ne_zero_of_finite K (ringChar K))
  exact subfieldPairG2_odd_all hrp h2 σ hp hp5 hσ g hne

end Main

end CFSG.HardMathSupport.Seitz.G2Noninner
