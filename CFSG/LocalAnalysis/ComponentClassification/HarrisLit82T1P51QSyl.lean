module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QRed

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup
open scoped MatrixGroups

theorem exists_sylow_of_equiv {R T : Type} [Group R] [Finite R] [Group T] [Finite T]
    (e : R ⧸ pPrimeCore 2 R ≃* T) {m : ℕ} (hm : Odd m) (hT : Nat.card T = 8 * m) {ι : T}
    (hι : ∀ x : T, x * x = 1 → x = 1 ∨ x = ι)
    (hnc : ∀ P : Subgroup T, Nat.card P = 8 → ∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u)
    {z : R} (hzc : z ∈ center R) (hz : orderOf z = 2) :
    ∃ S : Subgroup R, Nat.card S = 8 ∧ z ∈ S ∧ (∃ u ∈ S, ∃ v ∈ S, u * v ≠ v * u) ∧
      ∀ s ∈ S, s * s = 1 → s = 1 ∨ s = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 R) := inferInstance
  set O := pPrimeCore 2 R with hOdef
  have hO : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set ψ : R →* T := e.toMonoidHom.comp (QuotientGroup.mk' O) with hψ
  have hψ1 : ∀ s : R, ψ s = 1 ↔ s ∈ O := by
    intro s
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hSO : (S : Subgroup R) ⊓ O = ⊥ := by
    refine disjoint_iff.mp (disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
  have hinj : ∀ s₁ ∈ (S : Subgroup R), ∀ s₂ ∈ (S : Subgroup R), ψ s₁ = ψ s₂ → s₁ = s₂ := by
    intro s₁ h₁ s₂ h₂ h
    have h3 : s₁ * s₂⁻¹ ∈ (S : Subgroup R) ⊓ O :=
      mem_inf.mpr ⟨mul_mem h₁ (inv_mem h₂), (hψ1 _).mp (by rw [map_mul, map_inv, h,
        mul_inv_cancel])⟩
    rw [hSO, mem_bot] at h3
    exact mul_inv_eq_one.mp h3
  have hS8 : Nat.card S = 8 := by
    have h1 := card_mul_index (S : Subgroup R)
    have h2 : ¬ 2 ∣ (S : Subgroup R).index := S.not_dvd_index
    have h3 := card_eq_card_quotient_mul_card_subgroup O
    rw [Nat.card_congr e.toEquiv, hT] at h3
    have hidx : Odd (S : Subgroup R).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    have hmo : Nat.Coprime (2 ^ k) (m * Nat.card O) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hm.mul hO))
    have hdvd1 : 2 ^ k ∣ 8 := by
      refine hmo.dvd_of_dvd_mul_right ⟨(S : Subgroup R).index, ?_⟩
      rw [← hk, h1, h3]
      ring
    have hdvd2 : 8 ∣ 2 ^ k := by
      have hc : Nat.Coprime 8 (S : Subgroup R).index :=
        Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hidx)
      refine hc.dvd_of_dvd_mul_right ⟨m * Nat.card O, ?_⟩
      rw [← hk, h1, h3]
      ring
    rw [hk]
    exact Nat.dvd_antisymm hdvd1 hdvd2
  have hzS : z ∈ (S : Subgroup R) := by
    have hnorm : (zpowers z).Normal := ⟨fun n hn g => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hn
      have hc : g * z = z * g := ((mem_center_iff.mp hzc) g)
      have : g * z ^ i * g⁻¹ = z ^ i := by
        rw [(Commute.zpow_right hc i).eq, mul_inv_cancel_right]
      rw [this]
      exact zpow_mem (mem_zpowers z) i⟩
    have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hz, pow_one])
    exact hp.le_sylow_of_normal S (mem_zpowers z)
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  set P := (S : Subgroup R).map ψ with hP
  have hPcard : Nat.card P = 8 := by
    rw [← hS8]
    refine (Nat.card_congr (Equiv.ofBijective (fun s : (S : Subgroup R) =>
      (⟨ψ s, mem_map_of_mem ψ s.2⟩ : P)) ⟨fun s₁ s₂ h => ?_, fun y => ?_⟩)).symm
    · exact Subtype.ext (hinj _ s₁.2 _ s₂.2 (congrArg Subtype.val h))
    · obtain ⟨s, hs, hsy⟩ := mem_map.mp y.2
      exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  have hψz : ψ z = ι := by
    rcases hι (ψ z) (by rw [← map_mul, hzz, map_one]) with h | h
    · exact absurd (hinj _ hzS _ (one_mem _) (h.trans (map_one ψ).symm)) hz1
    · exact h
  refine ⟨S, hS8, hzS, ?_, fun s hs hss => ?_⟩
  · obtain ⟨u', hu', v', hv', huv'⟩ := hnc P hPcard
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hu'
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hv'
    exact ⟨u, hu, v, hv, fun h => huv' (by rw [← map_mul, ← map_mul, h])⟩
  · rcases hι (ψ s) (by rw [← map_mul, hss, map_one]) with h | h
    · exact Or.inl (hinj _ hs _ (one_mem _) (h.trans (map_one ψ).symm))
    · exact Or.inr (hinj _ hs _ hzS (h.trans hψz.symm))

theorem exists_sylow_quat {R : Type} [Group R] [Finite R]
    (hRQ : Nonempty (R ⧸ pPrimeCore 2 R ≃* QuaternionGroup 2) ∨
      Nonempty (R ⧸ pPrimeCore 2 R ≃* SL(2, ZMod 3)))
    {z : R} (hzc : z ∈ center R) (hz : orderOf z = 2) :
    ∃ S : Subgroup R, Nat.card S = 8 ∧ z ∈ S ∧ (∃ u ∈ S, ∃ v ∈ S, u * v ≠ v * u) ∧
      ∀ s ∈ S, s * s = 1 → s = 1 ∨ s = z := by
  rcases hRQ with hQ | hS
  · obtain ⟨e⟩ := hQ
    refine exists_sylow_of_equiv e odd_one (by rw [card_quat, mul_one]) quat_mul_self
      (fun P hP => ?_) hzc hz
    have hP' : P = ⊤ := eq_top_of_card_eq P (by rw [hP, card_quat])
    exact ⟨_, hP' ▸ mem_top _, _, hP' ▸ mem_top _, quat_noncomm⟩
  · obtain ⟨e⟩ := hS
    refine exists_sylow_of_equiv e (by decide : Odd 3) (by rw [card_sl23]) sl23_mul_self
      (fun P hP => ?_) hzc hz
    obtain ⟨hi, hj⟩ := mem_of_card_eq_eight hP
    exact ⟨_, hi, _, hj, sl23_noncomm⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
