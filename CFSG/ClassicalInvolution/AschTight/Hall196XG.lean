module

public import CFSG.ClassicalInvolution.AschTight.Hall196Wr
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem le_of_isPGroup_of_odd_index {H : Type*} [Group H] [Finite H] {M : Subgroup H} [M.Normal]
    (hM : Odd M.index) {A : Subgroup H} (hA : IsPGroup 2 A) : A ≤ M := by
  intro a ha
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  have h0 : a ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : (QuotientGroup.mk a : H ⧸ M) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, h0, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk a : H ⧸ M) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk a : H ⧸ M) ∣ M.index := orderOf_dvd_natCard _
  have h4 : Nat.Coprime (2 ^ k) M.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hM)
  have h5 := (Nat.Coprime.coprime_dvd_left h2 h4).eq_one_of_dvd h3
  rw [orderOf_eq_one_iff] at h5
  exact (QuotientGroup.eq_one_iff a).mp h5

theorem isSylow2In_top_of_index_two {H : Type} [Group H] [Finite H] {N P₁ D : Subgroup H}
    [N.Normal] (hN : N.index = 2) (hP₁ : IsSylow2In P₁ N) (hD : IsPGroup 2 D)
    (hcard : 2 * Nat.card P₁ ≤ Nat.card D) : IsSylow2In D ⊤ := by
  obtain ⟨Q, hQ, hDQ⟩ := IsSylow2In.exists_ge hD le_top
  have h1 : Nat.card ↥(N ⊓ Q) ≤ Nat.card P₁ :=
    hP₁.natCard_le (hQ.2.1.to_le inf_le_right) inf_le_left
  have h2 : N.relIndex Q ≤ 2 := by
    rw [← hN]
    exact Nat.le_of_dvd (by rw [hN]; exact two_pos) (Subgroup.relIndex_dvd_index_of_normal N Q)
  have h3 := Subgroup.relIndex_mul_card (H := N) (K := Q)
  have hle : Nat.card Q ≤ Nat.card D := by
    rw [← h3]
    calc N.relIndex Q * Nat.card ↥(N ⊓ Q) ≤ 2 * Nat.card P₁ := Nat.mul_le_mul h2 h1
      _ ≤ Nat.card D := hcard
  have hQD : Q = D := (Subgroup.eq_of_le_of_card_ge hDQ hle).symm
  rw [← hQD]
  exact hQ

theorem hasDihedralSylowTwo_of_isSylow2In {H : Type} [Group H] [Finite H] {D : Subgroup H}
    (hD : IsSylow2In D ⊤) {m : ℕ} (hm : 1 ≤ m) (e : D ≃* DihedralGroup (2 ^ m)) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo H := by
  intro S'
  have hS' : IsSylow2In (S' : Subgroup H) ⊤ :=
    ⟨le_top, S'.isPGroup', fun V' _ hV'2 hle => S'.is_maximal' hV'2 hle⟩
  obtain ⟨g, -, hg⟩ := exists_conjSub_eq_of_isSylow2In hD hS'
  let e₁ : D ≃* conjSub g D :=
    Subgroup.equivMapOfInjective D (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact ⟨m, hm, ⟨((MulEquiv.subgroupCongr hg).symm.trans e₁.symm).trans e⟩⟩

theorem nonempty_mulEquiv_dihedral {H : Type} [Group H] [Finite H] {D : Subgroup H} {ρ σ : H}
    (hgen : D = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) (hσ2 : σ ^ 2 = 1)
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hρ : 3 ≤ orderOf ρ) :
    Nonempty (D ≃* DihedralGroup (orderOf ρ)) := by
  have hρD : ρ ∈ D := hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ)
  have hσD : σ ∈ D := hgen ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  have hord : orderOf (⟨ρ, hρD⟩ : D) = orderOf ρ := Subgroup.orderOf_mk ρ hρD
  rw [← hord]
  refine CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ⟨ρ, hρD⟩ ⟨σ, hσD⟩ ?_
    (Subtype.ext (by simpa using hσ2)) (Subtype.ext (by simpa using hrel)) ?_
  · apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hgen
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : ρ ^ k = σ := by
      have := congrArg Subtype.val hk
      simpa using this
    have hc : σ * ρ * σ⁻¹ = ρ := by rw [← hk']; group
    rw [hrel] at hc
    have h2 : ρ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← hc]
      exact inv_mul_cancel ρ
    have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h2)
    omega

variable {G : Type} [Group G] [Finite G]

theorem oddCoreOf_le_of_le_normalizer {M H : Subgroup G} (hMH : M ≤ H)
    (hHM : H ≤ Subgroup.normalizer (M : Set G)) : oddCoreOf M ≤ oddCoreOf H := by
  have hOH : oddCoreOf M ≤ H := (oddCoreOf_le_self M).trans hMH
  have hn : ((oddCoreOf M).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOH]
    intro h hh
    exact AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (hHM hh)
  have hodd : Odd (Nat.card ↥((oddCoreOf M).subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
    exact oddCoreOf_odd_natCard M
  have h1 := le_classicalInvolutionOddCore hodd
  intro x hx
  exact ⟨⟨x, hOH hx⟩, h1 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
