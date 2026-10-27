module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Pos
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Class

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

structure K94Cfg (K : Type) [Group K] (z : K) (I₁ I₂ : Subgroup K) (F₁ F₂ : Type) [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] : Prop where
  z_ord : orderOf z = 2
  comm : ∀ x ∈ I₁, ∀ y ∈ I₂, x * y = y * x
  inter : I₁ ⊓ I₂ = zpowers z
  e₁ : Nonempty (↥I₁ ≃* SL(2, F₁))
  e₂ : Nonempty (↥I₂ ≃* SL(2, F₂))
  norm : ∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x * z = z * x →
    (∀ a ∈ I₁, x * a * x⁻¹ ∈ I₁) ∧ (∀ a ∈ I₂, x * a * x⁻¹ ∈ I₂)
  cards : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
    ((Nat.card F₁ = p ^ f ∧ Nat.card F₂ = p ^ f) ∨
      (Nat.card F₁ = (p ^ f) ^ 3 ∧ Nat.card F₂ = p ^ f))

@[expose] def K94Excl (P : (K : Type) → [Group K] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → Gen4 K →
    Open.twoRank K = 3 → P K →
    ∀ (z : K) (I₁ I₂ : Subgroup K) (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁] [Finite F₂],
      K94Cfg K z I₁ I₂ F₁ F₂ → False

structure K94Leaves : Prop where
  psp4 : K94Excl fun K _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel K .PSp 2 p f
  ree : K94Excl fun K _ => ∃ f : ℕ, LieModel K .twistedG2 0 3 f
  psl4 : K94Excl fun K _ =>
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧ LieModel K .PSL 4 p f
  psu4 : K94Excl fun K _ =>
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧ LieModel K .PSU 4 p f
  psl5 : K94Excl fun K _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ LieModel K .PSL 5 p f
  psu5 : K94Excl fun K _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ LieModel K .PSU 5 p f
  small : K94Excl fun K _ =>
    LieModel K .PSL 2 2 3 ∨ LieModel K .PSL 2 2 4 ∨ LieModel K .PSL 3 2 2 ∨
      LieModel K .twistedB2 0 2 3
  alt : K94Excl fun K _ => ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (K ≃* alternatingGroup (Fin n))
  spor : K94Excl fun K _ =>
    NativeSporadic.IsSporadic K .M12 ∨ NativeSporadic.IsSporadic K .M22 ∨
      NativeSporadic.IsSporadic K .M23 ∨ NativeSporadic.IsSporadic K .J1 ∨
      NativeSporadic.IsSporadic K .J2 ∨ NativeSporadic.IsSporadic K .J3 ∨
      NativeSporadic.IsSporadic K .McL ∨ NativeSporadic.IsSporadic K .Ly
  three : K94Excl fun K _ => LieModel K .G2 0 3 1 ∨ LieModel K .trialityD4 0 3 1

@[expose] def GH74FilterStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Catalog G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G → Gen4 G → GH74Conclusion G

theorem k94_alt1 (hL : K94Leaves) {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hgen : Gen4 K) (htwo : Open.twoRank K = 3)
    (hconc : GH74Conclusion K) {z : K} {I₁ I₂ : Subgroup K} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (cfg : K94Cfg K z I₁ I₂ F₁ F₂) :
    ∃ p₀ f₀ : ℕ, p₀.Prime ∧ p₀ ≠ 2 ∧ 1 ≤ f₀ ∧
      (LieModel K .G2 0 p₀ f₀ ∨ LieModel K .trialityD4 0 p₀ f₀) := by
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · exact h1
  · exact (hL.psp4 K hs hnab hgen htwo h2 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.ree K hs hnab hgen htwo h3 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.psl4 K hs hnab hgen htwo h4 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.psu4 K hs hnab hgen htwo h5 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.psl5 K hs hnab hgen htwo h6 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.psu5 K hs hnab hgen htwo h7 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.small K hs hnab hgen htwo h8 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.alt K hs hnab hgen htwo h9 z I₁ I₂ F₁ F₂ cfg).elim
  · exact (hL.spor K hs hnab hgen htwo h10 z I₁ I₂ F₁ F₂ cfg).elim

theorem prime_pow_inj {p p₀ f f₀ : ℕ} (hp : p.Prime) (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hf₀ : 1 ≤ f₀)
    (h : p ^ f = p₀ ^ f₀) : p = p₀ ∧ f = f₀ := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨f₀', rfl⟩ : ∃ f', f₀ = f' + 1 := ⟨f₀ - 1, by omega⟩
  obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hp hp₀ h
  exact ⟨h1, by omega⟩


theorem eq_three_of_lt_five {p₀ f₀ : ℕ} (hp₀ : p₀.Prime) (hp₀2 : p₀ ≠ 2) (hf₀ : 1 ≤ f₀)
    (h : p₀ ^ f₀ < 5) : p₀ = 3 ∧ f₀ = 1 := by
  have h1 : p₀ ≤ p₀ ^ f₀ := Nat.le_self_pow (by omega) p₀
  have h3 : 3 ≤ p₀ := by
    have := hp₀.two_le
    omega
  have hp3 : p₀ = 3 := by
    by_contra hne
    have h4 : p₀ = 4 := by omega
    subst h4
    norm_num at hp₀
  subst hp3
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h2 : 2 ≤ f₀ := by omega
  have : 3 ^ 2 ≤ 3 ^ f₀ := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem k94Class_of_leaves (h47 : IVK_4_7ab) (hL : K94Leaves)
    (hfilter : GH74FilterStmt) : K94Class := by
  have key : ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), IsSimpleGroup K →
      (∃ a b : K, a * b ≠ b * a) → Catalog K → Gen4 K → Open.twoRank K = 3 → p.Prime → p ≠ 2 →
      5 ≤ p ^ f → ∀ (z : K) (I₁ I₂ : Subgroup K) (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁]
        [Finite F₂], orderOf z = 2 → (∀ x ∈ I₁, ∀ y ∈ I₂, x * y = y * x) → I₁ ⊓ I₂ = zpowers z →
        Nonempty (↥I₁ ≃* SL(2, F₁)) → Nonempty (↥I₂ ≃* SL(2, F₂)) →
        (∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x * z = z * x →
          (∀ a ∈ I₁, x * a * x⁻¹ ∈ I₁) ∧ (∀ a ∈ I₂, x * a * x⁻¹ ∈ I₂)) →
        ((Nat.card F₁ = p ^ f ∧ Nat.card F₂ = p ^ f) ∨
          (Nat.card F₁ = (p ^ f) ^ 3 ∧ Nat.card F₂ = p ^ f)) →
        ∃ p₀ f₀ : ℕ, p₀.Prime ∧ p₀ ≠ 2 ∧ 1 ≤ f₀ ∧ 5 ≤ p₀ ^ f₀ ∧
          ((LieModel K .G2 0 p₀ f₀ ∧ Nat.card F₁ = p₀ ^ f₀ ∧ Nat.card F₂ = p₀ ^ f₀) ∨
            (LieModel K .trialityD4 0 p₀ f₀ ∧
              ((Nat.card F₁ = (p₀ ^ f₀) ^ 3 ∧ Nat.card F₂ = p₀ ^ f₀) ∨
                (Nat.card F₁ = p₀ ^ f₀ ∧ Nat.card F₂ = (p₀ ^ f₀) ^ 3)))) := by
    intro K _ _ p f hs hnab hcat hgen htwo hp hp2 h5 z I₁ I₂ F₁ F₂ _ _ _ _ hz hcomm hinter he₁ he₂
      hnorm hcards
    obtain ⟨e₁⟩ := he₁
    obtain ⟨e₂⟩ := he₂
    have hconc := hfilter K hcat hnab htwo.ge hgen
    have cfg : K94Cfg K z I₁ I₂ F₁ F₂ :=
      ⟨hz, hcomm, hinter, ⟨e₁⟩, ⟨e₂⟩, hnorm, ⟨p, f, hp, hp2, h5, hcards⟩⟩
    obtain ⟨p₀, f₀, hp₀, hp₀2, hf₀, hmod⟩ := k94_alt1 hL hs hnab hgen htwo hconc cfg
    have h5₀ : 5 ≤ p₀ ^ f₀ := by
      by_contra hlt
      obtain ⟨rfl, rfl⟩ := eq_three_of_lt_five hp₀ hp₀2 hf₀ (not_le.1 hlt)
      exact hL.three K hs hnab hgen htwo (by simpa using hmod) z I₁ I₂ F₁ F₂ cfg
    have h4₁ : 4 ≤ Nat.card F₁ := by
      rcases hcards with ⟨c1, -⟩ | ⟨c1, -⟩
      · rw [c1]; omega
      · rw [c1]; exact le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have h4₂ : 4 ≤ Nat.card F₂ := by
      rcases hcards with ⟨-, c2⟩ | ⟨-, c2⟩ <;> rw [c2] <;> omega
    rcases hmod with hM | hM
    · rcases fields_of_factors h47 (Or.inl rfl) hp₀ hp₀2 h5₀ hM hz hcomm hinter e₁ e₂ h4₁ h4₂
        hnorm with ⟨-, d1, d2⟩ | ⟨h, -⟩
      · exact ⟨p₀, f₀, hp₀, hp₀2, hf₀, h5₀, Or.inl ⟨hM, d1, d2⟩⟩
      · exact absurd h (by decide)
    · rcases fields_of_factors h47 (Or.inr rfl) hp₀ hp₀2 h5₀ hM hz hcomm hinter e₁ e₂ h4₁ h4₂
        hnorm with ⟨h, -⟩ | ⟨-, hd⟩
      · exact absurd h (by decide)
      · exact ⟨p₀, f₀, hp₀, hp₀2, hf₀, h5₀, Or.inr ⟨hM, hd⟩⟩
  constructor
  · intro K _ _ p f hs hnab hcat hgen htwo hp hp2 h5 z I₁ I₂ F₁ F₂ _ _ _ _ hz hcomm hinter he₁ he₂
      hnorm c1 c2
    obtain ⟨p₀, f₀, hp₀, hp₀2, hf₀, h5₀, hres⟩ := key K p f hs hnab hcat hgen htwo hp hp2 h5 z I₁ I₂
      F₁ F₂ hz hcomm hinter he₁ he₂ hnorm (Or.inl ⟨c1, c2⟩)
    have hq₀ : p₀ ^ f₀ < (p₀ ^ f₀) ^ 3 := by
      calc p₀ ^ f₀ = (p₀ ^ f₀) ^ 1 := (pow_one _).symm
        _ < (p₀ ^ f₀) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rcases hres with ⟨hM, d1, d2⟩ | ⟨-, ⟨d1, d2⟩ | ⟨d1, d2⟩⟩
    · have hpf : p ^ f = p₀ ^ f₀ := c1.symm.trans d1
      have hf : 1 ≤ f := by
        rcases Nat.eq_zero_or_pos f with h | h
        · subst h; simp at h5
        · exact h
      obtain ⟨rfl, rfl⟩ := prime_pow_inj hp hp₀ hf hf₀ hpf
      exact hM
    · exfalso
      have : (p₀ ^ f₀) ^ 3 = p₀ ^ f₀ := d1.symm.trans (c1.trans (c2.symm.trans d2))
      omega
    · exfalso
      have : p₀ ^ f₀ = (p₀ ^ f₀) ^ 3 := d1.symm.trans (c1.trans (c2.symm.trans d2))
      omega
  · intro K _ _ p f hs hnab hcat hgen htwo hp hp2 h5 z I₁ I₂ F₁ F₂ _ _ _ _ hz hcomm hinter he₁ he₂
      hnorm c1 c2
    obtain ⟨p₀, f₀, hp₀, hp₀2, hf₀, h5₀, hres⟩ := key K p f hs hnab hcat hgen htwo hp hp2 h5 z I₁ I₂
      F₁ F₂ hz hcomm hinter he₁ he₂ hnorm (Or.inr ⟨c1, c2⟩)
    have hq : p ^ f < (p ^ f) ^ 3 := by
      calc p ^ f = (p ^ f) ^ 1 := (pow_one _).symm
        _ < (p ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    have hq₀ : p₀ ^ f₀ < (p₀ ^ f₀) ^ 3 := by
      calc p₀ ^ f₀ = (p₀ ^ f₀) ^ 1 := (pow_one _).symm
        _ < (p₀ ^ f₀) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rcases hres with ⟨-, d1, d2⟩ | ⟨hM, ⟨d1, d2⟩ | ⟨d1, d2⟩⟩
    · exfalso
      have : (p ^ f) ^ 3 = p ^ f := c1.symm.trans (d1.trans (d2.symm.trans c2))
      omega
    · have hpf : p ^ f = p₀ ^ f₀ := c2.symm.trans d2
      have hf : 1 ≤ f := by
        rcases Nat.eq_zero_or_pos f with h | h
        · subst h; simp at h5
        · exact h
      obtain ⟨rfl, rfl⟩ := prime_pow_inj hp hp₀ hf hf₀ hpf
      exact hM
    · exfalso
      have e1 : (p ^ f) ^ 3 = p₀ ^ f₀ := c1.symm.trans d1
      have e2 : p ^ f = (p₀ ^ f₀) ^ 3 := c2.symm.trans d2
      have : p ^ f < (p ^ f) ^ 3 := hq
      rw [e1, e2] at this
      omega

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
