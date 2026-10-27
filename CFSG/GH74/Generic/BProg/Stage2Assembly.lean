module

public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.S1.RZD

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

theorem stage2Allow_of_level2
    (h1 : Stage1Alt) (hPQ : Stage2PQExists) (t1 : Stage2Thm1) (t2 : Stage2Thm2)
    (c2 : Stage2Cor2Stmt) (t3 : Stage2Thm3) (p31 : Stage2Prop31) (t4 : Stage2Thm4) :
    Stage2Allow := by
  intro G _ _ hyp noAlt x K hcirc A hsrc
  by_contra hnot
  have : IsSimpleGroup G := hyp.simple
  have hQK : QShapeNS (↥K ⧸ pPrimeCore 2 ↥K) := by
    obtain ⟨-, -, -, hcase⟩ := hsrc
    rcases hcase with ⟨-, h⟩ | ⟨E, -, -, -, -, -, h | h | h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hreg : IsReg32 A := by
    obtain ⟨a1, a3, a4, a5⟩ := h1
    rcases hQK with h | h | h | h
    · exact (a1 G hyp noAlt x K hcirc h A hsrc).resolve_left hnot
    · exact (a3 G hyp noAlt x K hcirc h A hsrc).resolve_left hnot
    · exact (a4 G hyp noAlt x K hcirc h A hsrc).resolve_left hnot
    · exact (a5 G hyp noAlt x K hcirc h A hsrc).resolve_left hnot
  have hNtop : normalizer (thetaHalf 1 A : Set G) ≠ ⊤ := by
    intro h
    have hnormal : (thetaHalf 1 A).Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (thetaHalf 1 A) with h0 | h0
    · exact hreg.2.1 h0
    · have hodd : Odd (Nat.card G) := by
        have := hreg.2.2
        rwa [h0, Subgroup.card_top] at this
      have hsolv := CFSG.Milestones.odd_order_solvable hodd
      obtain ⟨a, b, hab⟩ := hyp.nonab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  obtain ⟨M, hM, hNM⟩ :=
    (eq_top_or_exists_le_coatom (normalizer (thetaHalf 1 A : Set G))).resolve_left hNtop
  obtain ⟨P, Q, hP, hAP, hQeq, hQ⟩ := hPQ G x K A hcirc hsrc
  have hsetup : Stage2Setup G x K A M P Q :=
    ⟨hyp, noAlt, hcirc, hsrc, hnot, hreg, hM, hNM, hP, hAP, hQeq, hQ⟩
  obtain ⟨H, hc1⟩ := t1 G x K A M P Q hsetup
  have hc2 := t2 G x K A M P Q H hsetup hc1
  have hcor := c2 G x K A M P Q H hsetup hc1 hc2
  obtain ⟨hHs, hCx⟩ := t3 G x K A M P Q H hsetup hc1 hc2 hcor
  have h3A : Stage3A x A M H :=
    ⟨hCx, hcor.d.1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)), hcor.d.2, hHs⟩
  have hLie := p31 G x K A M P Q H hsetup hc1 h3A hQK
  obtain ⟨Z, hZ, hPD⟩ := t4 G x K A M P Q H hsetup hc1 hc2 h3A hLie
  obtain ⟨-, S, hS⟩ := S_CorZD_unconditional G hyp.simple hyp.nonab Z M hZ hPD
  have hsolvM : Group.IsSolvable ↥M := hS ▸ S1.isSolvable_normalizer_sylow S
  have hKM : K ≤ M := hc1.K_le
  have hKsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKM)
  obtain ⟨hKC, K', hK', -, hmap, -⟩ := hcirc.1.1.1.2.2
  have hK₀solv : Group.IsSolvable ↥(K.subgroupOf (centralizer ({x} : Set G))) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hKC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKC).injective
  let φ : ↥(K.subgroupOf (centralizer ({x} : Set G))) →*
      (↥(centralizer ({x} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({x} : Set G))) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))).comp
      (K.subgroupOf (centralizer ({x} : Set G))).subtype
  have hrange : φ.range = K' := by
    rw [← hmap, MonoidHom.range_comp, Subgroup.range_subtype]
  have hrsolv : Group.IsSolvable ↥φ.range :=
    Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  rw [hrange] at hrsolv
  have : Group.IsPerfect ↥K' := hK'.1.1
  have : Nontrivial ↥K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
  exact Group.IsPerfect.not_isSolvable ↥K' hrsolv

end CFSG.GH74.Generic.BProg
