module

public import CFSG.HardMathSupport.Foote.E27.SporE81Sound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.HardMathSupport.Foote.E27
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native
open scoped Pointwise

theorem dvd_card_centralizer_of_e81Check (D : E81Data) (hD : e81Check D = true)
    (hR : D.rOrd = D.qOrd) (h81 : 81 ∣ D.qOrd) {J : Subgroup (Equiv.Perm (Fin D.n))}
    (hJ : ∀ l < D.pg.size, permOfArr D.n D.pg[l]! ∈ J)
    (hord : D.qOrd = 3 ^ (Nat.card J).factorization 3) {s : J} (hs : orderOf s = 3) :
    81 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, R, z, hQJ, -, hQcard, -, -, hzQ, hzc, hRQ, hRcard, -, hgood⟩ :=
    e81_sound_card D hD J hJ
  have hRQeq : R = Q := Subgroup.eq_of_le_of_card_ge hRQ (by rw [hQcard, hRcard, hR])
  subst hRQeq
  have hQ'card : Nat.card (R.subgroupOf J) = 3 ^ (Nat.card J).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv, hQcard, hord]
  let T : Sylow 3 J := Sylow.ofCard (R.subgroupOf J) hQ'card
  have hT : (T : Subgroup J) = R.subgroupOf J := Sylow.coe_ofCard _ _
  have hsp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨P, hP⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P T
  have hsT : g * s * g⁻¹ ∈ (T : Subgroup J) := by
    have h1 : s ∈ (P : Subgroup J) := hP (Subgroup.mem_zpowers s)
    have h2 : MulAut.conj g s ∈ (MulAut.conj g • (P : Set J)) := Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * s * g⁻¹ ∈ T := by simpa [MulAut.conj_apply] using h2
    exact h3
  rw [← card_centralizer_conj g s]
  set s' := g * s * g⁻¹ with hs'def
  have hs'o : orderOf s' = 3 := by
    have := (MulAut.conj g : J ≃* J).orderOf_eq s
    simpa [MulAut.conj_apply, hs] using this
  have hs'R : (s' : Equiv.Perm (Fin D.n)) ∈ R := by
    rw [hT, Subgroup.mem_subgroupOf] at hsT
    exact hsT
  by_cases hsz : (s' : Equiv.Perm (Fin D.n)) ∈ Subgroup.zpowers z
  ·
    have hle : R.subgroupOf J ≤ Subgroup.centralizer ({s'} : Set J) := by
      intro q hq
      rw [Subgroup.mem_subgroupOf] at hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hsz
      apply Subtype.ext
      change (q : Equiv.Perm (Fin D.n)) * s' = s' * q
      rw [← hk]
      exact ((Commute.zpow_left (show Commute z q from (hzc q hq).symm) k)).eq.symm
    exact (h81.trans (by rw [hQ'card, ← hord])).trans (Subgroup.card_dvd_of_le hle)
  ·
    have hs'3 : (s' : Equiv.Perm (Fin D.n)) ^ 3 = 1 := by
      have := pow_orderOf_eq_one s'
      rw [hs'o] at this
      simpa using congrArg Subtype.val this
    obtain ⟨E, hEJ, hEe, hE81, hsE, -⟩ := hgood _ hs'R hs'3 hsz
    have hle : E.subgroupOf J ≤ Subgroup.centralizer ({s'} : Set J) := by
      intro e he
      rw [Subgroup.mem_subgroupOf] at he
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change (e : Equiv.Perm (Fin D.n)) * s' = s' * e
      exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨e, he⟩ ⟨_, hsE⟩)
    have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 x x.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk4 : 4 ≤ k := by
      by_contra hlt
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdvd : 81 ∣ Nat.card (E.subgroupOf J) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, hk]
      exact (show (81 : ℕ) = 3 ^ 4 by norm_num) ▸ pow_dvd_pow 3 hk4
    exact hdvd.trans (Subgroup.card_dvd_of_le hle)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
