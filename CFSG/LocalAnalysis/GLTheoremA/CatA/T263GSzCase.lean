module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GLift
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem t263_sz_dvd_descent {p q₀ : ℕ} (hp : p.Prime) (hq₀ : 1 ≤ q₀)
    (h : p ∣ (q₀ ^ p) ^ 2 * (q₀ ^ p - 1) * ((q₀ ^ p) ^ 2 + 1)) :
    p ∣ q₀ ^ 2 * (q₀ - 1) * (q₀ ^ 2 + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hqp : 1 ≤ q₀ ^ p := Nat.one_le_pow _ _ hq₀
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  push_cast [Nat.cast_sub hqp] at h
  push_cast [Nat.cast_sub hq₀]
  have hF : (q₀ : ZMod p) ^ p = q₀ := ZMod.pow_card _
  rw [hF] at h
  exact h

theorem t263_eq_five_of_dvd_twenty {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 20) : p = 5 := by
  have h' : p ∣ 2 ^ 2 * 5 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1

section SzCase


theorem t263CaseIx_sz : T263CaseIx t263GSz := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT B₀ hB₀ hdich hCc hB₀c hBc b hb hbB₀ hfield
    hlay
  exfalso
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : CFSG.Open.IsElemAbelian p B := hB.1
  have hbp : b ^ p = 1 := hBel.2 b hb
  have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hbN' : b⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hbN
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have e₆ : PSimple p S ≃* ↥S ⧸ Subgroup.center ↥S := pSimpleEquiv hSp
  have hchev : IsChevSimple 2 (PSimple p S) := by
    unfold IsChevSimple at hSc ⊢
    rcases hSc with h | h
    · exact Or.inl ((catalogIs_congr e₆).2 h)
    · exact Or.inr ((catalogIs_congr e₆).2 h)
  obtain ⟨x, hxB₀, hxC⟩ : ∃ x ∈ B₀, x ∉ B ⊓ Subgroup.centralizer (S : Set Ω) := by
    by_contra hcon
    push Not at hcon
    have hle : B₀ ≤ B ⊓ Subgroup.centralizer (S : Set Ω) := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [hB₀c, hCc] at h1
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hxB : x ∈ B := hB₀.1 hxB₀
  have hxC' : x ∉ Subgroup.centralizer (S : Set Ω) := fun h => hxC ⟨hxB, h⟩
  have hxp : x ^ p = 1 := hBel.2 x hxB
  obtain ⟨i, hi, ⟨e0⟩⟩ := hQ
  cases i with
  | cyclic _ _ => exact hi.1.elim
  | alternating _ _ => exact hi.1.elim
  | sporadic _ => exact hi.1.elim
  | lie d =>
    obtain ⟨xx, hv⟩ := d
    cases xx <;> first | exact hi.1.elim | skip
    rename_i m
    have hm2 : m ≠ 2 := by
      intro hm
      subst hm
      exact hi.2 trivial
    have hSzm := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
    obtain ⟨-, a, ha, K, _, _, hfa, hKcard, ⟨e'⟩⟩ := hSzm
    have ham : a = m := by omega
    subst ham
    have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa] at hKcard; simpa using hKcard
    have eS : PSimple p S ≃* CFSG.Blueprint.suzukiGroup a K := (e₆.trans e0).trans e'
    have hcat : catalogIs (PSimple p S) K155X.l154ExcSuz := ⟨_, hi.1, ⟨e₆.trans e0⟩⟩
    have hInn : InnDiagOn p (Subgroup.zpowers x) S :=
      S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hxB₀)
    obtain ⟨s, -, hsp, hs1⟩ := t263_sz_inner_elt hp hp2 hSn hSq hSp hcat hxp hInn hxC'
    have hpS : p ∣ Nat.card (CFSG.Blueprint.suzukiGroup a K) := by
      have h1 : orderOf s ∣ Nat.card (PSimple p S) := orderOf_dvd_natCard s
      rw [orderOf_eq_prime hsp hs1] at h1
      rwa [Nat.card_congr eS.toEquiv] at h1
    rw [CFSG.LieType.Ree.suzuki_order hK] at hpS
    set β := MI.indAut p S b hbN with hβdef
    have hβp : β ^ p = 1 := by
      show chevAut p S ⟨b⁻¹, hbN'⟩ ^ p = 1
      rw [← map_pow]
      have : (⟨b⁻¹, hbN'⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ p = 1 :=
        Subtype.ext (by simp [inv_pow, hbp])
      rw [this, map_one]
    have hβinn : β ∉ (MulAut.conj : PSimple p S →* MulAut (PSimple p S)).range := by
      intro hβ
      have h1 : InducesInnerMod p S b := (MI.indAut_mem_inner_iff hp hcomp hbN).1 hβ
      have h2 : InnDiagOn p (Subgroup.zpowers b) S := MI.inner_innDiag_any hcomp hchev hbN h1
      exact hbB₀ (hB₀.2.2.2.1 b hb h2)
    have hβ1 : β ≠ 1 := fun h => hβinn (h ▸ one_mem _)
    have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
    have hαord : orderOf (MulAut.congr eS β) = p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr eS) β, hβord]
    have hαinn : MulAut.congr eS β ∉ (MulAut.conj : CFSG.Blueprint.suzukiGroup a K →* _).range :=
      fun h => hβinn ((FQ.congr_mem_range_conj eS β).1 h)
    obtain ⟨σ, h, b', k, hkF, hkfin, hσp, hbp', hkcard, hconj, ⟨eH⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 _ hαord hαinn
    have e₁ : ↥(FP.fixSub β) ≃* CFSG.Blueprint.suzukiGroup b' k :=
      (FR.fixSubEquivCongr eS β).trans ((FR.fixSubEquivConj (MulAut.conj h) (MulAut.congr eS β)).trans
        ((MulEquiv.subgroupCongr (by rw [hconj]; rfl)).trans eH))
    have hq : (2 : ℕ) ^ (2 * a + 1) = (2 ^ (2 * b' + 1)) ^ p := by
      rw [← pow_mul, ← hbp']
    rw [hq] at hpS
    have hdesc := t263_sz_dvd_descent hp (Nat.one_le_two_pow) hpS
    rcases Nat.eq_zero_or_pos b' with hb0 | hb1
    ·
      subst hb0
      have hp5 : p = 5 := t263_eq_five_of_dvd_twenty hp hp2 (by simpa using hdesc)
      have hpa : p = 2 * a + 1 := by omega
      exact hm2 (by omega)
    ·
      haveI : IsSimpleGroup (CFSG.Blueprint.suzukiGroup b' k) := (CFSG.LieType.Ree.suzuki_simple hb1 hkcard).2.2
      haveI : IsSimpleGroup ↥(FP.fixSub β) := e₁.isSimpleGroup
      haveI : Finite ↥(FP.fixSub β) := Finite.of_equiv _ e₁.symm.toEquiv
      have hcardD : Nat.card ↥(FP.fixSub β) =
          (2 ^ (2 * b' + 1)) ^ 2 * (2 ^ (2 * b' + 1) - 1) * ((2 ^ (2 * b' + 1)) ^ 2 + 1) := by
        rw [Nat.card_congr e₁.toEquiv]
        exact CFSG.LieType.Ree.suzuki_order hkcard
      have hDn : ∃ x y : ↥(FP.fixSub β), x * y ≠ y * x := by
        refine AGLEmbedding.nonabelian_of_simple_of_sq_dvd (q := 2) Nat.prime_two ?_
        rw [hcardD]
        refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
        exact pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 2
      have hD : FR.SubfieldGrp β (FP.fixSub β) :=
        ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl, by rw [Subgroup.relIndex_self]; exact odd_one⟩
      exact t263_layer_ne_bot_of_simple_fixed hp hp2 hSp hbN hbp hD hDn (by rw [hcardD]; exact hdesc) hlay

end SzCase

end CFSG.LocalAnalysis.GLTheoremA.T263

end
