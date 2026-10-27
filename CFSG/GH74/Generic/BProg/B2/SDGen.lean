module

public import CFSG.GH74.Generic.BProg.B2.Lemma83Bar
public import CFSG.GH74.Generic.BProg.B2.Lemma82
public import CFSG.GH74.Generic.BProg.B2.WeakSigGen

import CFSG.GH74.Generic.BProg.B1.Lift0

public section

namespace CFSG.GH74.Generic.BProg.B2.SD2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

open CFSG.GH74.GLS.C3.Layer1.Back (mem_conjugate_iff' pRank_conjugate' isElementaryAbelian_conjugate)

section Statements

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sym8A_inv {M B : Subgroup G} {h : G} (S : Sym8A M B h) : Sym8A M B h⁻¹ := by
  refine ⟨S.maxM, S.O_ne, S.hB, fun hm => S.h_not (inv_mem_iff.1 hm), ?_, ?_⟩
  ·
    intro x hx
    have h1 : h⁻¹ * x * h ∈ B := by
      have := mem_conjugate_iff'.1 hx
      simpa using this
    have h2 := mem_conjugate_iff'.1 (S.B_le h1)
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [e] at h2
  ·
    intro x hx
    rw [mem_conjugate_iff']
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    have h1 : h⁻¹ * x * h ∈ M := S.D_le (mem_conjugate_iff'.2 (by rw [e]; exact hx))
    simpa using h1

namespace SDGen

theorem isRank23_barIn_conjugate {M B : Subgroup G} {h : G} (S : Sym8A M B h) :
    IsRank23 ↥(barIn M (conjugate B h)) := by
  have hDM : conjugate B h ≤ M := S.D_le
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := S.hB.1.2.1
  have hDel : CFSG.IsElementaryAbelian 2 ↥(conjugate B h) := isElementaryAbelian_conjugate hBel h
  have hD2 : IsPGroup 2 ↥(conjugate B h) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hDrank : pRank 2 ↥(barIn M (conjugate B h)) = pRank 2 ↥B := by
    rw [Lemma83Bar.pRank_barIn hDM hD2, pRank_conjugate']
  refine ⟨?_, hDrank ▸ S.hB.2.1⟩
  have hD₀el : CFSG.IsElementaryAbelian 2 ↥((conjugate B h).subgroupOf M) :=
    CFSG.IsElementaryAbelian.subgroupOf hDM
  exact CFSG.IsElementaryAbelian.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))

theorem centralizer_le_barIn_inf_conjugate {M B : Subgroup G} {h : G} (S : Sym8A M B h)
    {E' : Subgroup (Mbar M)} (hE'D : E' ≤ barIn M (conjugate B h))
    (hrk : pRank 2 ↥(barIn M (conjugate B h)) - 1 ≤ pRank 2 ↥E') :
    centralizer (E' : Set (Mbar M)) ≤ barIn M (M ⊓ conjugate M h) := by
  have hDM : conjugate B h ≤ M := S.D_le
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := S.hB.1.2.1
  have hDel : CFSG.IsElementaryAbelian 2 ↥(conjugate B h) := isElementaryAbelian_conjugate hBel h
  have hD2 : IsPGroup 2 ↥(conjugate B h) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  set φ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  set D₀ : Subgroup ↥M := (conjugate B h).subgroupOf M
  have hD₀el : CFSG.IsElementaryAbelian 2 ↥D₀ := CFSG.IsElementaryAbelian.subgroupOf hDM
  have hD₀2 : IsPGroup 2 ↥D₀ := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hDrank : pRank 2 ↥(barIn M (conjugate B h)) = pRank 2 ↥B := by
    rw [Lemma83Bar.pRank_barIn hDM hD2, pRank_conjugate']
  intro c hc
  rw [hDrank] at hrk
  set E₀ : Subgroup ↥M := E'.comap φ ⊓ D₀
  have hE₀D : E₀ ≤ D₀ := inf_le_right
  have hE₀map : E₀.map φ = E' := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hE'D hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hE₀2 : IsPGroup 2 ↥E₀ := hD₀2.to_le hE₀D
  set E : Subgroup G := E₀.map M.subtype
  have hED : E ≤ conjugate B h := by
    rintro _ ⟨x, hx, rfl⟩
    exact hE₀D hx
  have hErk : pRank 2 ↥B - 1 ≤ pRank 2 ↥E := by
    have h1 : pRank 2 ↥E = pRank 2 ↥E₀ :=
      CFSG.RankThree.PartOne.Quotient36.pRank_map_subtype (G := G) (q := 2) one_lt_two (X := M) E₀
    have h2 : pRank 2 ↥E' = pRank 2 ↥E₀ := by
      rw [← hE₀map]
      exact Lemma83Bar.pRank_map_mk hE₀2
    rw [h1, ← h2]
    exact hrk
  have hcomm : ∀ a ∈ E₀, φ a * c = c * φ a := by
    intro a ha
    have : φ a ∈ E' := hE₀map ▸ Subgroup.mem_map_of_mem φ ha
    exact mem_centralizer_iff.1 hc (φ a) this
  obtain ⟨g, rfl, hg⟩ := B1.centralizer_quotient_of_pGroup (pPrimeCore 2 ↥M) hNodd hE₀2 hcomm
  have hgcent : (g : G) ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hg a ha)
  exact Lemma83Bar.mem_barIn_iff.2 ⟨g, ⟨g.2, (lemma82_core S).2.2.2.2.2 E hED hErk hgcent⟩, rfl⟩

theorem centralizer_barIn_eq_barIn {M E : Subgroup G} (hEM : E ≤ M) (hE : IsPGroup 2 ↥E) :
    centralizer ((barIn M E : Subgroup (Mbar M)) : Set (Mbar M)) =
      barIn M (M ⊓ centralizer (E : Set G)) := by
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hE0 : IsPGroup 2 ↥(E.subgroupOf M) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEM).symm
  have key := B1.map_centralizer_eq_centralizer_map_of_isPGroup (pPrimeCore 2 ↥M) hNodd hE0
  have hc : centralizer ((E.subgroupOf M : Subgroup ↥M) : Set ↥M) =
      (M ⊓ centralizer (E : Set G)).subgroupOf M := by
    ext g
    rw [mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_iff]
    constructor
    · intro hg
      refine ⟨g.2, fun e he => ?_⟩
      exact congrArg Subtype.val (hg ⟨e, hEM he⟩ he)
    · rintro ⟨-, hg⟩ e he
      exact Subtype.ext (hg e he)
  unfold barIn
  rw [← key, hc]

end SDGen

theorem gen_of_genProp {M B K : Subgroup G} {h : G} (S : Sym8A M B h)
    (hDK : barIn M (conjugate B h) ≤ normalizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)))
    (hGP : GenProp ↥(barIn M K)) :
    barIn M K ≤ ⨆ (E : Subgroup (Mbar M)) (_ : E ≤ barIn M (conjugate B h))
      (_ : pRank 2 ↥(barIn M (conjugate B h)) - 1 ≤ pRank 2 ↥E), centralizer (E : Set (Mbar M)) := by
  classical
  set D : Subgroup (Mbar M) := barIn M (conjugate B h) with hD
  set L : Subgroup (Mbar M) := barIn M K with hL
  have hrank23 : IsRank23 ↥D := SDGen.isRank23_barIn_conjugate S
  set α : ↥D →* MulAut ↥L :=
    (actOn L (MulEquiv.refl ↥L)).comp (Subgroup.inclusion hDK) with hα
  have hαapply : ∀ (d : ↥D) (x : ↥L), ((α d x : ↥L) : Mbar M) =
      (d : Mbar M) * (x : Mbar M) * (d : Mbar M)⁻¹ := by
    intro d x
    exact coe_symm_actOn L (MulEquiv.refl ↥L) (Subgroup.inclusion hDK d) x
  have hgen : gammaAct α = ⊤ := hGP ↥D α hrank23
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥L) ∈ gammaAct α := by rw [hgen]; trivial
  let T : Subgroup ↥L := (⨆ (E : Subgroup (Mbar M)) (_ : E ≤ D)
      (_ : pRank 2 ↥D - 1 ≤ pRank 2 ↥E), centralizer (E : Set (Mbar M))).comap L.subtype
  have hle : gammaAct α ≤ T := by
    refine iSup_le fun E => iSup_le fun hE => ?_
    intro y hy
    have hE'D : E.map D.subtype ≤ D := Subgroup.map_subtype_le E
    have hcomap : (E.map D.subtype).comap D.subtype = E :=
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective E
    have hrk : pRank 2 ↥D - 1 ≤ pRank 2 ↥(E.map D.subtype) := by
      rw [← WeakSigGen.pRank_comap_subtype hrank23.1 hE'D, hcomap]; exact hE
    have hcent : (y : Mbar M) ∈
        centralizer ((E.map D.subtype : Subgroup (Mbar M)) : Set (Mbar M)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨d, hd, rfl⟩
      have hmemα : α d ∈ E.map α := Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
      have h1 := hαapply d y
      rw [hy _ hmemα] at h1
      show (d : Mbar M) * (y : Mbar M) = (y : Mbar M) * (d : Mbar M)
      exact mul_inv_eq_iff_eq_mul.mp h1.symm
    exact Subgroup.mem_iSup_of_mem (E.map D.subtype)
      (Subgroup.mem_iSup_of_mem hE'D (Subgroup.mem_iSup_of_mem hrk hcent))
  exact hle hmem

theorem le_conjugate_of_gen {M B K : Subgroup G} {h : G} (S : Sym8A M B h) (hKM : K ≤ M)
    (hgen : barIn M K ≤ ⨆ (E : Subgroup (Mbar M)) (_ : E ≤ barIn M (conjugate B h))
      (_ : pRank 2 ↥(barIn M (conjugate B h)) - 1 ≤ pRank 2 ↥E), centralizer (E : Set (Mbar M))) :
    K ≤ conjugate M h := by
  have hNle : pPrimeCoreOf 2 M ≤ conjugate M h := (lemma82_core S).2.1
  have hbar : barIn M K ≤ barIn M (M ⊓ conjugate M h) :=
    hgen.trans (iSup_le fun E' => iSup_le fun hE'D => iSup_le fun hrk =>
      SDGen.centralizer_le_barIn_inf_conjugate S hE'D hrk)
  intro k hk
  have hkM : k ∈ M := hKM hk
  have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨k, hkM⟩ ∈ barIn M K :=
    Lemma83Bar.mem_barIn_iff.2 ⟨⟨k, hkM⟩, hk, rfl⟩
  obtain ⟨m, hm, hmk⟩ := Lemma83Bar.mem_barIn_iff.1 (hbar hmem)
  have hker : m⁻¹ * (⟨k, hkM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hmk
    exact QuotientGroup.eq.1 hmk
  have hmN : (m : G)⁻¹ * k ∈ pPrimeCoreOf 2 M :=
    Subgroup.mem_map.2 ⟨m⁻¹ * ⟨k, hkM⟩, hker, by simp⟩
  have h1 : (m : G)⁻¹ * k ∈ conjugate M h := hNle hmN
  have h2 : (m : G) ∈ conjugate M h := hm.2
  have := (conjugate M h).mul_mem h2 h1
  simpa using this

end Statements

end CFSG.GH74.Generic.BProg.B2.SD2
