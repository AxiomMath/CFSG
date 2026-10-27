module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrame
public import CFSG.GroupTheory.WeirSylow.Symplectic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrameForm
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePspBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.GroupTheory.WeirSylow Module

theorem nonempty_spFrame {p : ℕ} [Fact p.Prime] (K : Type) [Field K] [Fintype K]
    (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) {e a r : ℕ}
    (he : orderOf (Fintype.card K : ZMod p) = e) (ha : padicValNat p (Fintype.card K ^ e - 1) = a)
    (hr : (if Even e then 2 * n else n) / e = r) :
    Nonempty (BlockFrame (Multiplicative (ZMod (p ^ a))) r (StatedSp n K)) := by
  subst he ha hr
  have hpp : p.Prime := Fact.out
  set q := Fintype.card K
  set e := orderOf (q : ZMod p) with hedef
  set a := padicValNat p (q ^ e - 1)
  have hq : 1 < q := Fintype.one_lt_card
  have he0 : 0 < e := by
    rw [hedef, ← CFSG.GroupTheory.WeirSylow.ordMod_natCast]
    exact CFSG.GroupTheory.WeirSylow.ordMod_pos (c := (q : ℤ)) (by exact_mod_cast hpK)
  have : NeZero e := ⟨he0.ne'⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let L := FiniteField.Extension K (ringChar K) e
  have hLcard : Nat.card L = q ^ e := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  have hLdim : finrank K L = e := FiniteField.finrank_extension K _ e
  have hdvdL : p ^ a ∣ Nat.card L - 1 := by
    rw [hLcard]
    exact pow_padicValNat_dvd
  by_cases hev : Even e
  ·
    rw [if_pos hev]
    obtain ⟨f, hf⟩ := hev
    have hfe : e = 2 * f := by omega
    have hf0 : 0 < f := by omega
    have hnd : ¬ p ∣ q ^ f - 1 := by
      intro h
      have h' : (p : ℤ) ∣ (q : ℤ) ^ f - 1 := by
        have := Int.natCast_dvd_natCast.2 h
        rwa [Nat.cast_sub (Nat.one_le_pow f q (by omega)), Nat.cast_pow, Nat.cast_one] at this
      rw [CFSG.GroupTheory.WeirSylow.dvd_pow_sub_one_iff,
        CFSG.GroupTheory.WeirSylow.ordMod_natCast, ← hedef] at h'
      exact absurd (Nat.le_of_dvd hf0 h') (by omega)
    have hdvd : p ^ a ∣ q ^ f + 1 := by
      have hcop : (p ^ a).Coprime (q ^ f - 1) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hpp).2 hnd)
      refine hcop.dvd_of_dvd_mul_left ?_
      have hfac : (q ^ f - 1) * (q ^ f + 1) = q ^ e - 1 := by
        have h1 : 1 ≤ q ^ f := Nat.one_le_pow f q (by omega)
        have h2 : 1 ≤ q ^ e := Nat.one_le_pow e q (by omega)
        zify [h1, h2]
        rw [hfe, pow_mul']
        ring
      rw [hfac]
      exact pow_padicValNat_dvd
    obtain ⟨S₀, ρ, J₀, hS₀, hS₀dim, hρ, hJ⟩ :=
      exists_spBlock_aniso K (L := L) (f := f) hf0 (hLdim.trans hfe) (m := p ^ a) hdvd
    have hS₀e : finrank K S₀.V = e := hS₀dim.trans hLdim
    obtain ⟨F₀⟩ := nonempty_blockFrame_pi S₀ ρ hρ J₀ hJ (2 * n / e)
    obtain ⟨F⟩ := nonempty_blockFrame_prod (FormSpace.pi fun _ : Fin (2 * n / e) => S₀)
      (stdSympSpace K ((2 * n - e * (2 * n / e)) / 2)) F₀
    have hdim : finrank K ((FormSpace.pi fun _ : Fin (2 * n / e) => S₀).prod
        (stdSympSpace K ((2 * n - e * (2 * n / e)) / 2))).V = 2 * n := by
      rw [FormSpace.finrank_prod, FormSpace.finrank_pi, finrank_stdSympSpace]
      simp only [hS₀e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have h1 := Nat.mul_div_le (2 * n) e
      have h2 : 2 ∣ e * (2 * n / e) := Dvd.dvd.mul_right ⟨f, hfe⟩ _
      have h3 : 2 * n / e * e = e * (2 * n / e) := Nat.mul_comm _ _
      omega
    obtain ⟨χ, hχ⟩ := exists_injective_isom_statedSp _
      (isSymplecticSpace_prod _ _ (isSymplecticSpace_pi (fun _ : Fin (2 * n / e) => S₀)
        fun _ => hS₀) (isSymplecticSpace_stdSympSpace _)) hdim
    exact ⟨F.map χ (hχ.comp F.T_injective)⟩
  ·
    rw [if_neg hev]
    obtain ⟨S₀, ρ, J₀, hS₀, hS₀dim, hρ, hJ⟩ :=
      exists_spBlock_split K (L := L) (m := p ^ a) hdvdL
    have hS₀e : finrank K S₀.V = 2 * e := by rw [hS₀dim, hLdim]
    obtain ⟨F₀⟩ := nonempty_blockFrame_pi S₀ ρ hρ J₀ hJ (n / e)
    obtain ⟨F⟩ := nonempty_blockFrame_prod (FormSpace.pi fun _ : Fin (n / e) => S₀)
      (stdSympSpace K (n - e * (n / e))) F₀
    have hdim : finrank K ((FormSpace.pi fun _ : Fin (n / e) => S₀).prod
        (stdSympSpace K (n - e * (n / e)))).V = 2 * n := by
      rw [FormSpace.finrank_prod, FormSpace.finrank_pi, finrank_stdSympSpace]
      simp only [hS₀e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have h1 := Nat.mul_div_le n e
      have h2 : n / e * (2 * e) = 2 * (e * (n / e)) := by ring
      omega
    obtain ⟨χ, hχ⟩ := exists_injective_isom_statedSp _
      (isSymplecticSpace_prod _ _ (isSymplecticSpace_pi (fun _ : Fin (n / e) => S₀)
        fun _ => hS₀) (isSymplecticSpace_stdSympSpace _)) hdim
    exact ⟨F.map χ (hχ.comp F.T_injective)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
