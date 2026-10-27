module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec86a
import CFSG.Goldschmidt.Steps.Sec86b
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter Sec8

theorem G86_of (h81 : S_G81) (h83 : S_G83) (h84 : S_G84) : S_G86 := by
  intro G _ _ S A hset h4 hS a ha ha1 H hH
  obtain ⟨p, hp, hp2, hnc⟩ := exists_not_isCyclic h81 h84 hset h4 hS ha ha1 hH
  have : Fact p.Prime := ⟨hp⟩
  have hHa := (h81 G S A hset h4 a ha ha1 H hH).1
  set P := qCoreOf H p with hPdef
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have ha2 : a ^ 2 = 1 := hset.elem.2 a ha
  have hAH : A ≤ H := hset.le.trans (le_of_mem_benderM hset h4 ha hH)
  have hz2 : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  have huniq : ∀ t ∈ H ⊓ Subgroup.centralizer (P : Set G), t ^ 2 = 1 → t = 1 ∨ t = a := by
    intro t ht ht2
    by_contra hne
    simp only [not_or] at hne
    have hta : t ∉ Subgroup.zpowers a := fun hmem =>
      (mem_two hz2 (Subgroup.mem_zpowers a) ha1 hmem).elim hne.1 hne.2
    have := isCyclic_inf_centralizer h81 h84 hset h4 ha ha1 hH hp hp2 ht.1 ht2 hta
    have hle : P ≤ P ⊓ Subgroup.centralizer ({t} : Set G) := fun x hx =>
      ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ht.2 x hx)⟩
    exact hnc (Subgroup.isCyclic_of_le hle)
  have hinvP : ∀ b ∈ A, b ∉ Subgroup.zpowers a → ∀ x ∈ P, b⁻¹ * x * b = x⁻¹ := by
    intro b hb hba
    have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
    rcases (h83 G S A hset h4 a ha ha1 H hH).1 b hb hb1 p hp with hcen | hinv
    · exfalso
      have hbC : b ∈ H ⊓ Subgroup.centralizer (P : Set G) :=
        ⟨hAH hb, Subgroup.mem_centralizer_iff.mpr fun x hx => by
          calc x * b = b * (b⁻¹ * x * b) := by group
            _ = b * x := by rw [hcen x hx]⟩
      rcases huniq b hbC (hset.elem.2 b hb) with h | h
      · exact hb1 h
      · exact hba (h ▸ Subgroup.mem_zpowers a)
    · exact hinv
  refine ⟨p, hp, hp2, hinvP, ?_, huniq⟩
  obtain ⟨n, hn, hnc'⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hca, -⟩ := conj_conj_eq_mul hset h4 hn hnc' ha ha1
  set b := n * a * n⁻¹ with hbdef
  have hbA : b ∈ A := conj_mem hn ha
  have hb2 : b * b = 1 := mul_self_eq_one hset.elem hbA
  have hba : b ∉ Subgroup.zpowers a := fun hmem =>
    (mem_two hz2 (Subgroup.mem_zpowers a) ha1 hmem).elim (conj_ne_one ha1) hca
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    comm_of_inv (hinvP b hbA hba) hx hy
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  refine le_antisymm (CFSG.SectionRank.pRank_le hp.one_lt fun E hEP hE => ?_) ?_
  ·
    obtain ⟨B, hAB, hBel, hB8⟩ := hset.rank
    obtain ⟨t, htB, htA⟩ : ∃ t ∈ B, t ∉ A := by
      by_contra hno
      simp only [not_exists, not_and, not_not] at hno
      have := Subgroup.card_le_of_le (show B ≤ A from hno)
      omega
    have hBH : B ≤ H := fun y hy => hHa ▸ Subgroup.mem_centralizer_singleton_iff.mpr
      (comm hBel hy (hAB ha))
    have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
    have hbt : b * t = t * b := comm hBel (hAB hbA) htB
    have hbtA : b * t ∉ A := fun h => htA (by simpa using A.mul_mem (A.inv_mem hbA) h)
    have hodd : ∀ x ∈ P, x * x = 1 → x = 1 := fun x hx hx2 => by
      obtain ⟨k, hk⟩ := qCoreOf_isPGroup H p ⟨x, hx⟩
      exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left k
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))).mp
        ⟨by simpa using congrArg Subtype.val hk, by rw [sq]; exact hx2⟩
    refine card_le_sq hp hPab hodd (hHP (hBH htB)) (mul_self_eq_one hBel htB)
      (fun x hx => by
        have h := hinvP b hbA hba x hx
        rw [hbi] at h ⊢
        exact h)
      hbt hb2
      (isCyclic_inf_centralizer h81 h84 hset h4 ha ha1 hH hp hp2 (hBH htB) (hBel.2 t htB)
        fun h => htA (hzA h))
      (isCyclic_inf_centralizer h81 h84 hset h4 ha ha1 hH hp hp2 (hBH (B.mul_mem (hAB hbA) htB))
        (hBel.2 _ (B.mul_mem (hAB hbA) htB)) fun h => hbtA (hzA h)) hEP hE.2
  ·
    obtain ⟨E, hEP, hEp, hEcard⟩ := exists_plane hp hp2 (qCoreOf_isPGroup H p) hnc
    refine CFSG.SectionRank.le_pRank hp.one_lt hEP ⟨⟨⟨fun x y => Subtype.ext
      (hPab _ (hEP x.2) _ (hEP y.2))⟩⟩, fun x hx => ?_⟩ hEcard
    simpa using congrArg Subtype.val (hEp ⟨x, hx⟩)

end CFSG.Goldschmidt
