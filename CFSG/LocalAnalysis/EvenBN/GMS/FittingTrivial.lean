module

public import CFSG.LocalAnalysis.EvenBN.GMS.LocalSetup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup

namespace LocalSetting

variable {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}
  (h : LocalSetting A t U V D n)
include h

theorem pPrimeCore_eq_bot : CFSG.pPrimeCore 2 H = ⊥ := by
  have h1 := h.oddCore_eq_bot
  unfold CFSG.Open.standardComponentOddCore at h1
  unfold CFSG.pPrimeCore
  rw [← h1]
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem not_isPGroup_A : ¬ IsPGroup 2 A := by
  intro hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hA.to_le h.D_le_A).exists_card_eq
  have hodd := h.odd_card_D
  rw [hk] at hodd
  rcases k with _ | k
  · rw [pow_zero, Subgroup.card_eq_one] at hk
    exact h.D_ne_bot hk
  · rw [pow_succ] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)

theorem A_inf_eq_bot {Q : Subgroup H} [hQn : Q.Normal] (hQ : IsPGroup 2 Q) : A ⊓ Q = ⊥ := by
  have := h.isSimpleGroup
  have hn : (Q.subgroupOf A).Normal := hQn.subgroupOf A
  rcases hn.eq_bot_or_eq_top with hb | ht
  · rw [inf_comm, ← subgroupOf_map_subtype, hb, Subgroup.map_bot]
  · exfalso
    apply h.not_isPGroup_A
    have hAQ : A ≤ Q := by
      intro a ha
      have : (⟨a, ha⟩ : A) ∈ Q.subgroupOf A := by rw [ht]; exact mem_top _
      exact this
    exact hQ.to_le hAQ

theorem inf_centralizer_le {Q : Subgroup H} [hQn : Q.Normal] (hQ : IsPGroup 2 Q) :
    Q ⊓ centralizer ({t} : Set H) ≤ centralizer (A : Set H) := by
  intro c hc
  obtain ⟨hcQ, hct⟩ := mem_inf.mp hc
  have hcN : c ∈ normalizer (A : Set H) := h.centralizer_le_normalizer hct
  refine mem_centralizer_iff.mpr fun a ha => ?_
  have hkA : a * (c * a⁻¹ * c⁻¹) ∈ A :=
    mul_mem ha ((mem_normalizer_iff.mp hcN a⁻¹).mp (inv_mem ha))
  have hkQ : a * c * a⁻¹ * c⁻¹ ∈ Q := mul_mem (hQn.conj_mem c hcQ a) (inv_mem hcQ)
  have hk : a * c * a⁻¹ * c⁻¹ ∈ A ⊓ Q := mem_inf.mpr ⟨by simpa only [mul_assoc] using hkA, hkQ⟩
  rw [h.A_inf_eq_bot hQ, mem_bot] at hk
  have h1 : a * c * a⁻¹ = c := mul_inv_eq_one.mp hk
  calc a * c = a * c * a⁻¹ * a := by group
    _ = c * a := by rw [h1]

theorem le_centralizer_of_isPGroup {Q : Subgroup H} [hQn : Q.Normal] (hQ : IsPGroup 2 Q) :
    Q ≤ centralizer (A : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isSimpleGroup
  have hNtop : normalizer (Q : Set H) = ⊤ := normalizer_eq_top_iff.mpr hQn
  have hPQ : ⁅zpowers t, D⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    refine zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_)
    exact mem_centralizer_singleton_iff.mp (h.D_le_centralizer hd)
  have hfixed : Q ⊓ centralizer (zpowers t : Set H) ≤ centralizer (D : Set H) := by
    intro x hx
    obtain ⟨hxQ, hxt⟩ := mem_inf.mp hx
    have hxt' : x ∈ centralizer ({t} : Set H) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxt t (mem_zpowers t)).symm
    exact centralizer_le (SetLike.coe_subset_coe.mpr h.D_le_A)
      (h.inf_centralizer_le hQ (mem_inf.mpr ⟨hxQ, hxt'⟩))
  have hQD : ⁅Q, D⁆ = ⊥ :=
    CFSG.GorensteinWalter.ThompsonPQ.thompson_p_times_q (zpowers t) D Q h.isPGroup_zpowers hQ
      (Nat.coprime_two_left.mpr h.odd_card_D) (hNtop ▸ le_top) (hNtop ▸ le_top) hPQ hfixed
  have hDC : D ≤ centralizer (Q : Set H) :=
    le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hQD)
  have hn : ((centralizer (Q : Set H)).subgroupOf A).Normal :=
    (normal_centralizer (H := Q)).subgroupOf A
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply h.D_ne_bot
    rw [eq_bot_iff]
    intro d hd
    have h1 : (⟨d, h.D_le_A hd⟩ : A) ∈ (centralizer (Q : Set H)).subgroupOf A := hDC hd
    rw [hb, mem_bot] at h1
    exact mem_bot.mpr (congrArg Subtype.val h1)
  · refine le_centralizer_iff.mpr fun a ha => ?_
    have : (⟨a, ha⟩ : A) ∈ (centralizer (Q : Set H)).subgroupOf A := by rw [ht]; exact mem_top _
    exact this

theorem eq_bot_of_normal_isPGroup {Q : Subgroup H} [hQn : Q.Normal] (hQ : IsPGroup 2 Q) :
    Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hQ1
  apply h.not_normal
  obtain ⟨-, -, htight, hNN, -⟩ := h.isStandard
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  rw [← hNN]
  by_contra hg
  have hodd := htight g hg
  have hQC : Q ≤ centralizer (A : Set H) := h.le_centralizer_of_isPGroup hQ
  have hle : Q ≤ centralizer (A : Set H) ⊓
      (centralizer (A : Set H)).map (MulAut.conj g).toMonoidHom := by
    refine le_inf hQC fun x hx => ⟨g⁻¹ * x * g, hQC ?_, ?_⟩
    · simpa using hQn.conj_mem x hx g⁻¹
    · simp [mul_assoc]
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hQ1 hk
  have hdvd : 2 ∣ Nat.card (centralizer (A : Set H) ⊓
      (centralizer (A : Set H)).map (MulAut.conj g).toMonoidHom : Subgroup H) :=
    (dvd_pow_self 2 hk0).trans (hk ▸ card_dvd_of_le hle)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem pCore_eq_bot : CFSG.pCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.pCore_normal (p := 2) (G := H)
  exact h.eq_bot_of_normal_isPGroup CFSG.pCore_isPGroup

theorem fittingSubgroup_eq_bot : CFSG.fittingSubgroup H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.Fitting_eq_pcore H 2 h.pPrimeCore_eq_bot, h.pCore_eq_bot]

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS
