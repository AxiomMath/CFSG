module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ExcDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.TwoPartCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.TransferCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.DihedralRank

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.GorensteinWalter

theorem pow_two_eq_one_of_card_le_two {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : Nat.card K ≤ 2) {x : G} (hx : x ∈ K) : x ^ 2 = 1 := by
  have hd : orderOf (⟨x, hx⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h2 : orderOf (⟨x, hx⟩ : K) ∣ 2 := by
    rcases Nat.lt_or_ge (Nat.card K) 2 with h | h
    · have : Nat.card K = 1 := by omega
      rw [this] at hd
      exact hd.trans (one_dvd _)
    · have : Nat.card K = 2 := by omega
      rwa [this] at hd
  have := orderOf_dvd_iff_pow_eq_one.1 h2
  exact congrArg Subtype.val this

theorem pRank_two_le_two_of_excType {A : Type} [Group A] [Finite A] (hA : CFSG.IsQuasisimple A)
    (h : ExcType A) : CFSG.pRank 2 A ≤ 2 := by
  have hperf : Group.IsPerfect A := hA.1
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le one_lt_two fun E _ hE => ?_
  have hE2 : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨S, hES⟩ := hE2.exists_le_sylow
  set π : A →* A ⧸ center A := QuotientGroup.mk' (center A) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨m, hm, ⟨eT⟩⟩ := hasDihedralSylowTwo_of_excType h (Sylow.mapSurjective hπ S)
  let φ₀ : ↥(S : Subgroup A) →* ↥(Sylow.mapSurjective hπ S : Subgroup (A ⧸ center A)) :=
    (π.comp (S : Subgroup A).subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
  let φ : ↥(S : Subgroup A) →* DihedralGroup (2 ^ m) := eT.toMonoidHom.comp φ₀
  have hφ : Function.Surjective φ := by
    refine eT.surjective.comp ?_
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : ↥(S : Subgroup A), x ∈ φ.ker ↔ (x : A) ∈ center A := by
    intro x
    rw [MonoidHom.mem_ker]
    change eT (φ₀ x) = 1 ↔ _
    rw [← map_one eT, eT.injective.eq_iff]
    show φ₀ x = 1 ↔ _
    rw [Subtype.ext_iff]
    exact (QuotientGroup.eq_one_iff _)
  have hcen : φ.ker ≤ center ↥(S : Subgroup A) := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 ((hker x).1 hx) g)
  set Zk : Subgroup A := (φ.ker).map (S : Subgroup A).subtype with hZk
  have hZkc : Zk ≤ center A := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hker x).1 hx
  have hZk2 : IsPGroup 2 Zk := S.isPGroup'.to_le (Subgroup.map_subtype_le _)
  have hcard : Nat.card φ.ker ≤ 2 := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (S : Subgroup A))]
    exact card_le_two_of_two_subgroup_center h hZkc hZk2
  have hker2 : ∀ x ∈ φ.ker, x ^ 2 = 1 := fun x hx =>
    pow_two_eq_one_of_card_le_two φ.ker hcard hx
  have hodd : Odd (S : Subgroup A).index := by
    have := S.not_dvd_index
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 this)
  have hcomm : φ.ker ≤ commutator ↥(S : Subgroup A) := fun x hx =>
    mem_commutator_of_central_perfect hodd ((hker x).1 hx) x.2
      (by simpa using congrArg Subtype.val (hker2 x hx))
  have hE' : CFSG.Open.IsElemAbelian 2 (E.subgroupOf (S : Subgroup A)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have := hE.1
      have hab : ((a : ↥(S : Subgroup A)) : A) * ((b : ↥(S : Subgroup A)) : A) =
          ((b : ↥(S : Subgroup A)) : A) * ((a : ↥(S : Subgroup A)) : A) :=
        congrArg Subtype.val (mul_comm' (⟨((a : ↥(S : Subgroup A)) : A), a.2⟩ : E)
          ⟨((b : ↥(S : Subgroup A)) : A), b.2⟩)
      exact Subtype.ext (Subtype.ext hab)
    · have hx2 := hE.2 (x : A) hx
      apply Subtype.ext
      simpa using hx2
  have := card_le_four_of_dihedral_central hm hφ hcen hker2 hcard hcomm hE'
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv] at this
  simpa using this

end CFSG.EvenSporadicStandard.Induction.Junction
