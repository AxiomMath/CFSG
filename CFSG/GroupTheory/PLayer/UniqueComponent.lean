module

public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G] [Finite G]

theorem glaPComponent_eq_of_glaPLayer {p : ℕ} {X L : Subgroup G}
    (hL : GLAPComponent p X L) (hX : GLAPLayer p X = L) {K : Subgroup G}
    (hK : GLAPComponent p X K) : K = L := by
  have hKL : K ≤ L := hX ▸ le_sSup hK
  have hbar : barX p X K ≤ barX p X L := barX_mono p hKL
  have hne : barX p X K ≠ ⊥ := by
    rintro hbot
    haveI : IsSimpleGroup (↥(barX p X K) ⧸ Subgroup.center ↥(barX p X K)) := hK.2.2.1.2.2.2
    haveI : Nontrivial ↥(barX p X K) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(barX p X K))).nontrivial
    rw [hbot] at this
    exact not_subsingleton_iff_nontrivial.2 this inferInstance
  let S : Subgroup ↥(barX p X L) := (barX p X K).subgroupOf (barX p X L)
  have hmap : S.map (barX p X L).subtype = barX p X K :=
    Subgroup.map_subgroupOf_eq_of_le hbar
  have hsub : IsSubnormal S ⊤ := by
    have h := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_comap' (barX p X L).subtype
      (isSubnormal_of_le_of_le hK.2.2.1.2.1 hbar le_top)
    rwa [show (barX p X L).comap (barX p X L).subtype = ⊤ from by ext; simp] at h
  haveI : Group.IsPerfect ↥(barX p X K) :=
    Subgroup.isPerfect_iff.mpr (barX_perfect_of_glaPComponent hK)
  have hperf : Group.IsPerfect ↥S :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hbar).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hbar).symm.surjective
  have heq : barX p X K = barX p X L := by
    rcases @CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      _ _ hL.2.2.1.2.2 S hsub hperf with hbot | htop
    · exfalso
      apply hne
      have hle : S ≤ (barX p X L).subtype.ker := by rw [hbot]; exact bot_le
      have hzero : S.map (barX p X L).subtype = ⊥ := (Subgroup.map_eq_bot_iff _).2 hle
      rwa [hmap] at hzero
    · exact le_antisymm hbar fun x hx => by
        have hxS : (⟨x, hx⟩ : ↥(barX p X L)) ∈ S := by rw [htop]; trivial
        exact hxS
  exact glaPComponent_unique hK hL heq

end CFSG

end
