module

public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement

public section

namespace CFSG

open scoped Pointwise

theorem dvd_card_quotient_center_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card Q) :
    p ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card (Q ⧸ Subgroup.center Q)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  set Z := Subgroup.center Q with hZ
  let S : Sylow p Q := Sylow.nonempty.some
  have hSmap : ((S : Subgroup Q).map (QuotientGroup.mk' Z)) = ⊥ := by
    have hSp : IsPGroup p ((S : Subgroup Q).map (QuotientGroup.mk' Z)) := S.isPGroup'.map (QuotientGroup.mk' Z)
    have hSdvd : Nat.card ↥((S : Subgroup Q).map (QuotientGroup.mk' Z)) ∣ Nat.card (Q ⧸ Z) :=
      Subgroup.card_subgroup_dvd_card _
    have hnotdvd : ¬ p ∣ Nat.card ↥((S : Subgroup Q).map (QuotientGroup.mk' Z)) := fun h =>
      (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (h.trans hSdvd)
    obtain ⟨n, hn⟩ := hSp.exists_card_eq
    have hn0 : n = 0 := by
      by_contra hn0
      apply hnotdvd
      rw [hn]
      exact dvd_pow_self p hn0
    have hcard1 : Nat.card ↥((S : Subgroup Q).map (QuotientGroup.mk' Z)) = 1 := by
      rw [hn, hn0, pow_zero]
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hSZ : (S : Subgroup Q) ≤ Z := by
    intro x hx
    have hx' : QuotientGroup.mk' Z x ∈ (S : Subgroup Q).map (QuotientGroup.mk' Z) := Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) hx
    rw [hSmap, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).1 (by
      simpa only [QuotientGroup.mk'_apply] using hx')
  have hcenter : (S : Subgroup Q) ≤
      centerIn (G := Q) (Subgroup.normalizer (S : Subgroup Q)) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subgroup.mem_center_iff.1 (hSZ hx) y
  obtain ⟨N, hN, hNcop, hNquot⟩ :=
    exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p S hcenter
  have hperf : Group.IsPerfect Q := hQ.1
  have hsub : Subsingleton (Q ⧸ N) := by
    by_contra hns
    have hnt : Nontrivial (Q ⧸ N) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (G := Q ⧸ N) hNquot.isNilpotent
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  rw [hNtop] at hNcop
  have htop : Nat.card (⊤ : Subgroup Q) = Nat.card Q :=
    Nat.card_congr (Subgroup.topEquiv).toEquiv
  rw [htop] at hNcop
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hNcop hdvd

end CFSG

end
