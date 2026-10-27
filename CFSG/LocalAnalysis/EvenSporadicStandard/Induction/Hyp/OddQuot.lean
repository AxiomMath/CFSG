module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Cover

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

noncomputable def cqEquivOfMulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)

theorem le_oddCore_of_normal_odd {G : Type*} [Group G] {K : Subgroup G} (hK : K.Normal)
    (hodd : Odd (Nat.card K)) : K ≤ CFSG.oddCore G :=
  le_sSup ⟨hK, hodd⟩

theorem oddQuot_equiv_of_surj {A B : Type*} [Group A] [Finite A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) :
    Nonempty ((A ⧸ CFSG.oddCore A) ≃* (B ⧸ CFSG.oddCore B)) := by
  have : Finite B := Finite.of_surjective π hπ
  have hOB : Odd (Nat.card (CFSG.oddCore B)) := odd_card_oddCore' B
  let φ : A →* B ⧸ CFSG.oddCore B := (QuotientGroup.mk' (CFSG.oddCore B)).comp π
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hπ
  have hmem : ∀ x : A, φ x = 1 ↔ π x ∈ CFSG.oddCore B := fun x => by
    simp [φ, QuotientGroup.eq_one_iff]
  have hker : φ.ker = CFSG.oddCore A := by
    apply le_antisymm
    ·
      have hkodd : Odd (Nat.card φ.ker) := by
        by_contra hne
        have h2 : 2 ∣ Nat.card φ.ker := by
          rcases Nat.even_or_odd (Nat.card φ.ker) with he | ho
          · exact even_iff_two_dvd.1 he
          · exact absurd ho hne
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ.ker) 2 h2
        have hx' : orderOf ((x : φ.ker) : A) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
        have hxm : π ((x : φ.ker) : A) ∈ CFSG.oddCore B := (hmem _).1 x.2
        have h1 : orderOf (π ((x : φ.ker) : A)) ∣ 2 := hx' ▸ orderOf_map_dvd π _
        have h3 : orderOf (π ((x : φ.ker) : A)) ∣ Nat.card (CFSG.oddCore B) := by
          have := orderOf_dvd_natCard (⟨π ((x : φ.ker) : A), hxm⟩ : CFSG.oddCore B)
          rwa [Subgroup.orderOf_mk] at this
        have h4 : orderOf (π ((x : φ.ker) : A)) = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
          · exact h
          · rw [h] at h3
            exact absurd (hOB.of_dvd_nat h3) (by decide)
        have h5 : π ((x : φ.ker) : A) = 1 := orderOf_eq_one_iff.1 h4
        have h6 : ((x : φ.ker) : A) ∈ π.ker := h5
        have h7 := orderOf_dvd_natCard (⟨((x : φ.ker) : A), h6⟩ : π.ker)
        rw [Subgroup.orderOf_mk, hx'] at h7
        exact absurd (hodd.of_dvd_nat h7) (by decide)
      exact le_oddCore_of_normal_odd inferInstance hkodd
    · intro x hx
      rw [MonoidHom.mem_ker, hmem]
      have hn : (Subgroup.map π (CFSG.oddCore A)).Normal :=
        Subgroup.Normal.map inferInstance π hπ
      have hodd' : Odd (Nat.card (Subgroup.map π (CFSG.oddCore A))) := by
        have hOA : Odd (Nat.card (CFSG.oddCore A)) := odd_card_oddCore' A
        exact hOA.of_dvd_nat (Subgroup.card_dvd_of_surjective
          (MonoidHom.subgroupMap_surjective π _))
      exact le_oddCore_of_normal_odd hn hodd' ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem oddCore_quotient_eq_bot {A : Type*} [Group A] [Finite A] :
    CFSG.oddCore (A ⧸ CFSG.oddCore A) = ⊥ := by
  obtain ⟨e⟩ := oddQuot_equiv_of_surj (QuotientGroup.mk' (CFSG.oddCore A))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact odd_card_oddCore' A)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore (A ⧸ CFSG.oddCore A))
  have h2 : Nat.card ((A ⧸ CFSG.oddCore A) ⧸ CFSG.oddCore (A ⧸ CFSG.oddCore A)) =
      Nat.card (A ⧸ CFSG.oddCore A) := (Nat.card_congr e.toEquiv).symm
  have hpos : 0 < Nat.card (A ⧸ CFSG.oddCore A) := Nat.card_pos
  have h3 : Nat.card ↥(CFSG.oddCore (A ⧸ CFSG.oddCore A)) = 1 := by
    rw [h2] at h1
    nlinarith
  exact Subgroup.card_eq_one.1 h3

theorem odd_card_center_of_cover {A B : Type*} [Group A] [Finite A] [Group B]
    [Group.IsPerfect A] (π : A →* B) (hπ : Function.Surjective π) (hker : π.ker ≤ center A)
    (h : Odd (Nat.card (center A))) : Odd (Nat.card (center B)) := by
  have : Finite B := Finite.of_surjective π hπ
  let g : ↥(center A) →* ↥(center B) :=
    (π.comp (center A).subtype).codRestrict (center B) (by
      intro z
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hπ w
      show π y * π z = π z * π y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 z.2 y])
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨y, hy⟩ := hπ (w : B)
    have hyc : y ∈ center A := memCenter_of_cover π hker (by rw [hy]; exact w.2)
    exact ⟨⟨y, hyc⟩, Subtype.ext (by exact hy)⟩
  exact h.of_dvd_nat (Subgroup.card_dvd_of_surjective hg)

theorem card_center_eq_of_cover {A B : Type*} [Group A] [Finite A] [Group B]
    [Group.IsPerfect A] (π : A →* B) (hπ : Function.Surjective π) (hker : π.ker ≤ center A) :
    Nat.card (center A) = Nat.card π.ker * Nat.card (center B) := by
  have : Finite B := Finite.of_surjective π hπ
  let g : ↥(center A) →* ↥(center B) :=
    (π.comp (center A).subtype).codRestrict (center B) (by
      intro z
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hπ w
      show π y * π z = π z * π y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 z.2 y])
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨y, hy⟩ := hπ (w : B)
    have hyc : y ∈ center A := memCenter_of_cover π hker (by rw [hy]; exact w.2)
    exact ⟨⟨y, hyc⟩, Subtype.ext (by exact hy)⟩
  have h1 := Subgroup.card_ker_mul_card_range g
  have hr : Nat.card g.range = Nat.card (center B) := by
    rw [MonoidHom.range_eq_top_of_surjective g hg, Subgroup.card_top]
  have hk : g.ker = π.ker.subgroupOf (center A) := by
    ext z
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hk' : Nat.card g.ker = Nat.card π.ker := by
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [← h1, hk', hr]

theorem even_card_center_of_cover {A B : Type*} [Group A] [Finite A] [Group B]
    [Group.IsPerfect A] (π : A →* B) (hπ : Function.Surjective π) (hker : π.ker ≤ center A)
    (h : Even (Nat.card (center B))) : Even (Nat.card (center A)) := by
  by_contra hne
  exact (Nat.not_even_iff_odd.2
    (odd_card_center_of_cover π hπ hker (Nat.not_even_iff_odd.1 hne))) h

theorem oddCover_of_cover {H : Type} [Group H] [Finite H] {s : TauCeti.SporadicName}
    {A B : Subgroup H} (hA : OddCover s A) (π : ↥A →* ↥B) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center ↥A) : OddCover s B := by
  have := hA.1.1
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hker
  obtain ⟨f⟩ := hA.2.2
  exact ⟨isQuasisimple_of_cover hA.1 π hπ hker,
    odd_card_center_of_cover π hπ hker hA.2.1, ⟨e.symm.trans f⟩⟩

theorem oddCover_of_mulEquiv {H H' : Type} [Group H] [Group H'] {s : TauCeti.SporadicName}
    {A : Subgroup H} {B : Subgroup H'} (e : ↥A ≃* ↥B) (h : OddCover s A) : OddCover s B := by
  obtain ⟨f⟩ := h.2.2
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h.1,
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv) ▸ h.2.1,
    ⟨(cqEquivOfMulEquiv e).symm.trans f⟩⟩

end CFSG.EvenSporadicStandard.Induction.Hyp
