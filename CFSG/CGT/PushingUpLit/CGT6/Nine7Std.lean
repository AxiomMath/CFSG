module

public import CFSG.Open.StandardDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Five

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open CFSG.Open
open scoped commutatorElement

section Standard

variable {G : Type} [Group G] [Finite G]

theorem conjugate_eq_of_common_involution {A : Subgroup G} (hA : QS A) (hs : Star A)
    (hD : ∀ a : G, orderOf a = 2 → A ≤ Subgroup.centralizer ({a} : Set G) →
      Delta A (Subgroup.centralizer ({a} : Set G)) = A) {h a : G} (ha : orderOf a = 2)
    (haA : a ∈ Subgroup.centralizer (A : Set G))
    (haB : a ∈ Subgroup.centralizer (conjugate A h : Set G)) : conjugate A h = A := by
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [mem_centralizer_single]
    exact (Subgroup.mem_centralizer_iff.1 haA x hx).symm
  have hBa : conjugate A h ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [mem_centralizer_single]
    exact (Subgroup.mem_centralizer_iff.1 haB x hx).symm
  have hBm : conjugate A h ∈ ConjCl A := ⟨h, rfl⟩
  have hBc : IsCompIn (conjugate A h) (Subgroup.centralizer ({a} : Set G)) :=
    isCompIn_centralizer_involution (ConjCl.qs hA hBm) (ConjCl.star hs hBm) ha hBa
  have hle : conjugate A h ≤ Delta A (Subgroup.centralizer ({a} : Set G)) :=
    le_iSup₂_of_le (conjugate A h) ⟨hBm, hBc.1, hBc.2.1⟩ le_rfl
  rw [hD a ha hAa] at hle
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjugate])

omit [Finite G] in
theorem mem_normalizer_centralizer_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
  GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup A hg

theorem isStandard_of_outcome_one {A : Subgroup G} (hA : QS A) (hs : Star A)
    (heven : Even (Nat.card (Subgroup.centralizer (A : Set G))))
    (hD : ∀ a : G, orderOf a = 2 → A ≤ Subgroup.centralizer ({a} : Set G) →
      Delta A (Subgroup.centralizer ({a} : Set G)) = A)
    (hnc : ∀ g : G, ⁅A, conjugate A g⁆ ≠ ⊥) : standardIsStandardSubgroup A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ g : G, (∃ a : G, orderOf a = 2 ∧ a ∈ Subgroup.centralizer (A : Set G) ∧
      a ∈ Subgroup.centralizer (conjugate A g⁻¹ : Set G)) →
        g ∈ Subgroup.normalizer (A : Set G) := by
    rintro g ⟨a, ha, haA, haB⟩
    have := conjugate_eq_of_common_involution hA hs hD ha haA haB
    exact ((Subgroup.normalizer (A : Set G)).inv_mem_iff).1 (mem_normalizer_of_conjugate_eq this)
  refine ⟨hA, heven, ?_, ?_, ?_⟩
  · intro g hg
    by_contra hodd
    have hev : Even (Nat.card ↥(Subgroup.centralizer (A : Set G) ⊓
        (Subgroup.centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom)) :=
      Nat.not_odd_iff_even.1 hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
    have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨a, ha2, haC, haS⟩ : ∃ a : G, orderOf a = 2 ∧ a ∈ Subgroup.centralizer (A : Set G) ∧
        a ∈ (Subgroup.centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom :=
      ⟨(x : G), hx2, x.2.1, x.2.2⟩
    apply hg
    rw [map_conj_eq_conjugate, conjugate_centralizer] at haS
    exact mem_normalizer_centralizer_of_mem_normalizer (key g ⟨a, ha2, haC, haS⟩)
  · refine Subgroup.ext fun g => ⟨fun hg => ?_, mem_normalizer_centralizer_of_mem_normalizer⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 heven)
    have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    refine key g ⟨x, hx2, x.2, ?_⟩
    have h2 : conjugate (Subgroup.centralizer (A : Set G)) g⁻¹ =
        Subgroup.centralizer (A : Set G) :=
      conjugate_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hg)
    rw [conjugate_centralizer] at h2
    rw [h2]
    exact x.2
  · intro g
    rw [← inv_inv g, map_conj_eq_conjugate, inv_inv]
    exact hnc g⁻¹

end Standard

end CFSG.CGT.PushingUpLit.CGT6.Nine7
