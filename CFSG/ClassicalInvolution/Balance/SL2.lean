module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification
open scoped MatrixGroups

section Cover

variable {J : Type*} [Group J] [Finite J]

theorem oddCore_eq_bot_of_isQuasisimple_of_equiv_sl2 (hJ : CFSG.Open.IsQuasisimple J) {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) (h9 : p ^ n ≠ 9)
    (φ : (J ⧸ componentClassificationOddCore J) ≃* SL(2, GaloisField p n)) :
    componentClassificationOddCore J = ⊥ := by
  set O := componentClassificationOddCore J with hO
  have hperf : Group.IsPerfect J := ⟨hJ.1⟩
  have hOc : O ≤ Subgroup.center J := oddCore_le_center_of_isQuasisimple hJ
  have hZ : (Subgroup.center (J ⧸ O)).comap (QuotientGroup.mk' O) = Subgroup.center J :=
    Quasisimple.center_comap_of_central_kernel (QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O) (by rw [QuotientGroup.ker_mk']; exact hOc)
  let ρ : J →* PSL(2, GaloisField p n) :=
    (QuotientGroup.mk' (Subgroup.center SL(2, GaloisField p n))).comp
      (φ.toMonoidHom.comp (QuotientGroup.mk' O))
  have hρsurj : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (φ.surjective.comp (QuotientGroup.mk'_surjective O))
  have hcenter : ∀ x : J ⧸ O, φ x ∈ Subgroup.center SL(2, GaloisField p n) ↔
      x ∈ Subgroup.center (J ⧸ O) := fun x => by
    rw [← Subgroup.map_center_eq φ]
    exact (Subgroup.mem_map_iff_mem φ.injective).trans Iff.rfl
  have hρker : ρ.ker = Subgroup.center J := by
    rw [← hZ]
    ext j
    change (QuotientGroup.mk' (Subgroup.center SL(2, GaloisField p n)))
        (φ (QuotientGroup.mk' O j)) = 1 ↔ QuotientGroup.mk' O j ∈ Subgroup.center (J ⧸ O)
    rw [← hcenter]
    exact QuotientGroup.eq_one_iff _
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.center J)) := inferInstance
  set T : Subgroup J := (P : Subgroup (Subgroup.center J)).map (Subgroup.center J).subtype
    with hT
  have hTc : T ≤ Subgroup.center J := Subgroup.map_subtype_le _
  have : T.Normal := Subgroup.normal_of_le_center hTc
  have hTp : IsPGroup 2 T := P.isPGroup'.map (Subgroup.center J).subtype
  have hTker : T ≤ ρ.ker := hρker ▸ hTc
  let ψ : J ⧸ T →* PSL(2, GaloisField p n) := QuotientGroup.lift T ρ hTker
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨j, hj⟩ := hρsurj y
    exact ⟨(j : J ⧸ T), hj⟩
  have hψker : ψ.ker = (Subgroup.center J).map (QuotientGroup.mk' T) := by
    rw [QuotientGroup.ker_lift, hρker]
  have hψcentral : ψ.ker ≤ Subgroup.center (J ⧸ T) := by
    rw [hψker]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective T q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
  have hψodd : Odd (Nat.card ψ.ker) := by
    let ρ' : Subgroup.center J →* J ⧸ T := (QuotientGroup.mk' T).comp (Subgroup.center J).subtype
    have hker' : ρ'.ker = (P : Subgroup (Subgroup.center J)) := by
      ext x
      change QuotientGroup.mk' T x.1 = 1 ↔ x ∈ (P : Subgroup (Subgroup.center J))
      rw [show QuotientGroup.mk' T x.1 = 1 ↔ x.1 ∈ T from QuotientGroup.eq_one_iff _]
      exact Subgroup.mem_map_iff_mem (Subgroup.center J).subtype_injective
    have hrange : ρ'.range = ψ.ker := by
      rw [hψker]
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.1, z.2, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
    have hcard : Nat.card ψ.ker = (P : Subgroup (Subgroup.center J)).index := by
      rw [← hrange, ← hker', Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ').toEquiv).symm
    rw [hcard]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (fun h => P.not_dvd_index (by simpa using h)) |> fun h => by omega)
  have hKF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn.ne'
  have : Group.IsPerfect (J ⧸ T) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
  have hbot : ψ.ker = ⊥ :=
    (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel hp2 hKF ψ hψsurj hψcentral
      hψodd).1 h9
  have hZT : Subgroup.center J ≤ T := by
    rw [hψker, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  have hOT : O ≤ T := hOc.trans hZT
  have hOp : IsPGroup 2 O := hTp.to_le hOT
  obtain ⟨k, hk⟩ := hOp.exists_card_eq
  have hodd : Odd (Nat.card O) := OddCore.odd_card J
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ Nat.card O := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])

theorem nonempty_mulEquiv_sl2_of_isQuasisimple (hJ : CFSG.Open.IsQuasisimple J) {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) (h9 : p ^ n ≠ 9)
    (φ : (J ⧸ componentClassificationOddCore J) ≃* SL(2, GaloisField p n)) :
    Nonempty (J ≃* SL(2, GaloisField p n)) := by
  have hbot := oddCore_eq_bot_of_isQuasisimple_of_equiv_sl2 hJ hp2 hn h9 φ
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans φ⟩

end Cover

theorem classicalInvolutionOddCore_eq_bot_of_isQuasisimple {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hJ : CFSG.Open.IsQuasisimple J) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 0 < n) (h9 : p ^ n ≠ 9)
    (φ : J ⧸ classicalInvolutionOddCore J ≃* SL(2, GaloisField p n)) :
    classicalInvolutionOddCore J = ⊥ ∧ Nonempty (J ≃* SL(2, GaloisField p n)) :=
  ⟨oddCore_eq_bot_of_isQuasisimple_of_equiv_sl2 hJ hp2 hn h9 φ,
    nonempty_mulEquiv_sl2_of_isQuasisimple hJ hp2 hn h9 φ⟩

end CFSG.ClassicalInvolution.Balance
