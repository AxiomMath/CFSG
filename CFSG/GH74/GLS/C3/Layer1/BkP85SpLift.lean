module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Defs

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.TwoThin

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_involution_lift {a : Y} (ha : orderOf a = 2) {b : barQ Y} (hb : orderOf b = 2)
    (hab : b * barMk Y a = barMk Y a * b) :
    ∃ u : Y, orderOf u = 2 ∧ u * a = a * u ∧ barMk Y u = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2 : b ^ 2 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb] at this
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    omega
  have hbmem : b ∈ centralizer ({barMk Y a} : Set (barQ Y)) := mem_centralizer_singleton_iff.2 hab
  obtain ⟨⟨c, hc⟩, hcb⟩ := barMkCentralizer_surjective ha ⟨b, hbmem⟩
  have hcb' : barMk Y c = b := by
    have h := barMkCentralizer_apply ha ⟨c, hc⟩
    rw [hcb] at h
    exact h.symm
  have hc2 : c ^ 2 ∈ pPrimeCore 2 Y := by
    rw [← ker_barMk, MonoidHom.mem_ker, map_pow, hcb']
    exact hb2
  have hk : Odd (orderOf (c ^ 2)) :=
    Odd.of_dvd_nat (odd_card_pPrimeCore Y) (Subgroup.orderOf_dvd_natCard _ hc2)
  have hsq : (c ^ orderOf (c ^ 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_orderOf_eq_one _
  have himg : barMk Y (c ^ orderOf (c ^ 2)) = b := by
    obtain ⟨j, hj⟩ := hk
    rw [map_pow, hcb', hj, pow_succ, pow_mul, hb2, one_pow, one_mul]
  refine ⟨c ^ orderOf (c ^ 2), ?_, ?_, himg⟩
  · refine orderOf_eq_prime hsq ?_
    intro h1
    apply hb1
    rw [← himg, h1, map_one]
  · have hcomm : Commute c a := mem_centralizer_singleton_iff.1 hc
    exact (hcomm.pow_left _).eq

end Lift

section Pre

variable {G : Type} [Group G]

@[expose] def preimgM (M : Subgroup G) (Lb : Subgroup (Mb M)) : Subgroup G :=
  (Lb.comap (barMk ↥M)).map M.subtype

theorem mem_preimgM_iff {M : Subgroup G} {Lb : Subgroup (Mb M)} {g : G} :
    g ∈ preimgM M Lb ↔ ∃ h : g ∈ M, barMk ↥M ⟨g, h⟩ ∈ Lb := by
  unfold preimgM
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem preimgM_le {M : Subgroup G} {Lb : Subgroup (Mb M)} : preimgM M Lb ≤ M := fun _ hg =>
  (mem_preimgM_iff.1 hg).1

theorem preimgM_normal {M : Subgroup G} {Lb : Subgroup (Mb M)}
    (hn : ∀ n : Mb M, ∀ h ∈ Lb, n * h * n⁻¹ ∈ Lb) :
    ∀ m ∈ M, ∀ g ∈ preimgM M Lb, m * g * m⁻¹ ∈ preimgM M Lb := by
  intro m hm g hg
  obtain ⟨hgM, hgb⟩ := mem_preimgM_iff.1 hg
  refine mem_preimgM_iff.2 ⟨M.mul_mem (M.mul_mem hm hgM) (M.inv_mem hm), ?_⟩
  have h1 : (⟨m * g * m⁻¹, M.mul_mem (M.mul_mem hm hgM) (M.inv_mem hm)⟩ : ↥M) =
      ⟨m, hm⟩ * ⟨g, hgM⟩ * ⟨m, hm⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv]
  exact hn _ _ hgb

theorem relIndex_preimgM (M : Subgroup G) (Lb : Subgroup (Mb M)) :
    (preimgM M Lb).relIndex M = Lb.index := by
  have h : (preimgM M Lb).subgroupOf M = Lb.comap (barMk ↥M) := by
    unfold preimgM
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  unfold Subgroup.relIndex
  rw [h]
  exact Subgroup.index_comap_of_surjective Lb barMk_surjective

theorem relIndex_preimgM_eq_two [Finite G] (M : Subgroup G) {Lb : Subgroup (Mb M)}
    (hcard : Nat.card (Mb M) = 2 * Nat.card ↥Lb) : (preimgM M Lb).relIndex M = 2 := by
  rw [relIndex_preimgM]
  have h := Subgroup.card_mul_index Lb
  rw [hcard, mul_comm 2] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

end Pre

end CFSG.GH74.GLS.Th2.P85.Sp
