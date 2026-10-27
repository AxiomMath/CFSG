module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.Open (IsElemAbelian)
open CFSG.LieType.SeitzGeneration (RankLE2)

open scoped Pointwise in
private theorem exists_conj_le_sylow' {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p G) (E : Subgroup G) (hE : IsPGroup p E) :
    ∃ y : G, E.map (MulAut.conj y).toMonoidHom ≤ Q := by
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨g, ?_⟩
  have hgS : (g • S : Sylow p G).toSubgroup = S.toSubgroup.map (MulAut.conj g).toMonoidHom := rfl
  rw [hg] at hgS
  rw [hgS]
  exact Subgroup.map_mono hES

theorem exists_isElemAbelian_card_sq_of_mem {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (hrle : RankLE2 p Y)
    (hE₀ : ∃ E : Subgroup Y, IsElemAbelian p E ∧ Nat.card E = p ^ 2) {d : Y} (hd1 : d ≠ 1)
    (hdp : d ^ p = 1) :
    ∃ E : Subgroup Y, IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ d ∈ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hdord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hzp : ∀ w : Y, w ^ p = 1 → IsElemAbelian p (Subgroup.zpowers w) := by
    intro w hw
    rw [Subgroup.zpowers_eq_closure]
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      subst ha
      subst hb
      rfl
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hw
  have hdPg : IsPGroup p (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdord, pow_one])
  obtain ⟨P, hdP⟩ := hdPg.exists_le_sylow
  have hdP' : d ∈ (P : Subgroup Y) := hdP (Subgroup.mem_zpowers d)
  by_cases hdc : ∀ y ∈ (P : Subgroup Y), y * d = d * y
  ·
    obtain ⟨E₀, hE₀, hE₀c⟩ := hE₀
    have hE₀p : IsPGroup p E₀ := IsPGroup.of_card hE₀c
    obtain ⟨y, hy⟩ := exists_conj_le_sylow' P E₀ hE₀p
    set E₁ : Subgroup Y := E₀.map (MulAut.conj y).toMonoidHom with hE₁
    have hE₁a : IsElemAbelian p E₁ := CFSG.Open.IsElemAbelian.map hE₀ _
    have hE₁c : Nat.card E₁ = p ^ 2 := by
      rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj y).injective, hE₀c]
    have hcomm : ∀ a ∈ E₁, ∀ b ∈ Subgroup.zpowers d, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (hdc a (hy ha)) k).eq
    have hE₂ := CFSG.Open.IsElemAbelian.sup_of_commute hE₁a (hzp d hdp) hcomm
    have hle : Nat.card (E₁ ⊔ Subgroup.zpowers d : Subgroup Y) ≤ Nat.card E₁ := by
      rw [hE₁c]
      exact hrle _ hE₂
    have heq : E₁ = E₁ ⊔ Subgroup.zpowers d := Subgroup.eq_of_le_of_card_ge le_sup_left hle
    refine ⟨E₁, hE₁a, hE₁c, ?_⟩
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  ·
    simp only [not_forall] at hdc
    obtain ⟨y0, hy0, hne⟩ := hdc
    have hPp : IsPGroup p (P : Subgroup Y) := P.isPGroup'
    haveI : Nontrivial (P : Subgroup Y) :=
      ⟨⟨⟨d, hdP'⟩, 1, fun h => hd1 (congrArg Subtype.val h)⟩⟩
    haveI := hPp.center_nontrivial
    have hZp : IsPGroup p (Subgroup.center (P : Subgroup Y)) := hPp.to_subgroup _
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 : Nat.card (Subgroup.center (P : Subgroup Y)) = 1 := by simpa using hn
      have h2 := Finite.one_lt_card_iff_nontrivial.2
        (inferInstance : Nontrivial (Subgroup.center (P : Subgroup Y)))
      omega
    have hpdvd : p ∣ Nat.card (Subgroup.center (P : Subgroup Y)) := by
      rw [hn]
      exact dvd_pow_self p hn0
    obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' p hpdvd
    set z : Y := (((z' : Subgroup.center (P : Subgroup Y)) : (P : Subgroup Y)) : Y) with hz
    have hzord : orderOf z = p := by
      rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz']
    have hzp' : z ^ p = 1 := hzord ▸ pow_orderOf_eq_one z
    have hzc : ∀ y ∈ (P : Subgroup Y), y * z = z * y := by
      intro y hy
      have := Subgroup.mem_center_iff.1 z'.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    have hzP : z ∈ (P : Subgroup Y) := ((z' : Subgroup.center (P : Subgroup Y)) :
      (P : Subgroup Y)).2
    have hzd : z ∉ Subgroup.zpowers d := by
      intro hzmem
      have hzz : Subgroup.zpowers z ≤ Subgroup.zpowers d := (Subgroup.zpowers_le).2 hzmem
      have hcard : Nat.card (Subgroup.zpowers d) ≤ Nat.card (Subgroup.zpowers z) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hdord, hzord]
      have heq := Subgroup.eq_of_le_of_card_ge hzz hcard
      have hdz : d ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers d
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdz
      apply hne
      rw [← hk]
      exact (Commute.zpow_right (hzc y0 hy0) k).eq
    have hcomm : ∀ a ∈ Subgroup.zpowers d, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have hdzc : Commute d z := hzc d hdP'
      exact (hdzc.zpow_zpow i j).eq
    set E : Subgroup Y := Subgroup.zpowers d ⊔ Subgroup.zpowers z with hE
    have hEa : IsElemAbelian p E :=
      CFSG.Open.IsElemAbelian.sup_of_commute (hzp d hdp) (hzp z hzp') hcomm
    have hEle : Nat.card E ≤ p ^ 2 := hrle _ hEa
    have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hEa.2 x x.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hdE : Subgroup.zpowers d ≤ E := le_sup_left
    have hne1 : Nat.card E ≠ Nat.card (Subgroup.zpowers d) := by
      intro h
      have heq : Subgroup.zpowers d = E := Subgroup.eq_of_le_of_card_ge hdE h.le
      apply hzd
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    have hpd : p ∣ Nat.card E := by
      have := Subgroup.card_dvd_of_le hdE
      rwa [Nat.card_zpowers, hdord] at this
    rw [Nat.card_zpowers, hdord] at hne1
    have hk2 : k = 2 := by
      have hk1 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hEle)
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        rw [hk] at hpd
        exact hp.one_lt.ne' (Nat.dvd_one.1 hpd)
      have hk3 : k ≠ 1 := by
        rintro rfl
        exact hne1 (by rw [hk, pow_one])
      omega
    refine ⟨E, hEa, by rw [hk, hk2], ?_⟩
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
