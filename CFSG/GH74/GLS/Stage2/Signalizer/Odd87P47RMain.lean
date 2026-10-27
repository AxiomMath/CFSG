module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47RLoc
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cNorm
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Kinds

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

theorem prop47R_of_leaves (h41c : Prop4_1c) (h29 : Lemma29First) : Prop47R := by
  intro G _ _ z k S ctx H X T p sig hTHS hT4 hTX hnot
  classical
  by_cases hone : TypeOneCase G k
  · rcases hT4 with ⟨-, hTS⟩ | ⟨hn, -⟩
    · have hSH : S ≤ H := by rw [← hTS]; exact hTHS.trans inf_le_left
      exact prop47R_of_typeOne ctx sig hSH hnot
    · exact absurd hone hn
  · by_contra hne
    have hcl : IsClassicalKind k := Stage2Ctx.isClassicalKind_of_not_typeOneCase ctx hone
    have hz : z ∈ H := sig.A.z_mem
    have hsig := sig4B_of_sub ctx.orderOf_z sig hnot
    have hpp : Fact p.Prime := ⟨sig.A.prime⟩
    set N : Subgroup ↥H := pCore p ↥H with hNdef
    set R : Subgroup (Sec H N) := pCore 2 (Sec H N) with hR
    set X' : Subgroup (Sec H N) := xBar p H X with hX'
    have hz2 : zSec z H hz N * zSec z H hz N = 1 := by
      have h := orderOf_zSec ctx.orderOf_z hz N hsig.odd
      have h1 := pow_orderOf_eq_one (zSec z H hz N)
      rw [h, pow_two] at h1
      exact h1
    have hRn : R.Normal := inferInstance
    have hRtop : ∀ g : Sec H N, g ∈ normalizer (R : Set (Sec H N)) := fun g =>
      (Subgroup.normalizer_eq_top_iff.mpr hRn).symm ▸ Subgroup.mem_top g
    have hXR : X' ≤ normalizer (R : Set (Sec H N)) := fun g _ => hRtop g
    have hzR : zSec z H hz N ∈ normalizer (R : Set (Sec H N)) := hRtop _
    have hcen : zSec z H hz N ∈ centralizer ({zSec z H hz N} : Set (Sec H N)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hsetup : Setup412 p R X' (zSec z H hz N) :=
      { prime := hsig.A.prime
        odd := hsig.A.odd
        W2 := pCore_isPGroup
        Xp := hsig.A.pgroup
        XW := hXR
        zW := hzR
        z2 := hz2
        zX := hsig.A.inv _ (Subgroup.mem_top _) hcen
        comm := hsig.A.comm
        Cz := fun c _ hc => hsig.A.inv c (Subgroup.mem_top _)
          (Subgroup.mem_centralizer_singleton_iff.mpr hc) }
    obtain ⟨-, hXn, -, hcomm2, -, hsetup'⟩ := reduce412 hsetup
    obtain ⟨-, -, hcase⟩ := h41c G z k S ctx H N hz p X' hsig R pCore_isPGroup hXR hzR hne
    rcases hcase with ⟨hk, -⟩ | ⟨⟨e⟩, -, -⟩
    · rcases hcl with rfl | ⟨ε, rfl⟩ <;> rcases hk with h | h <;> cases h
    obtain ⟨-, hcard⟩ := card_range_actOnK_X hsetup' hcomm2 hne e
    obtain ⟨E, hET, hEab, hE16⟩ := T4CS.exists_elemAbelian_sixteen ctx hone hT4
    obtain ⟨E', hE'T, hE'ab, hE'card⟩ :=
      exists_elemAbelian_xBar hsig.odd hET (hTHS.trans inf_le_left) hEab
    have hE'N : E' ≤ normalizer (X' : Set (Sec H N)) := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := hE'T hg
      exact mk_mem_normalizer_xBar p (hTX ht)
    have hE'V : E' ≤ normalizer ((⁅R, X'⁆ : Subgroup (Sec H N)) : Set (Sec H N)) := fun g hg =>
      CoreA.mem_normalizer_commutator (hRtop g) (hE'N hg)
    have hE2 : ∀ g ∈ E', g * g = 1 := fun g hg => by
      have := hE'ab.2 g hg
      rwa [pow_two] at this
    have hEc : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hE'ab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hE8 : 8 ≤ Nat.card ↥E' := by rw [hE'card, hE16]; norm_num
    obtain ⟨U', V', X'', hU4, hV2', hVq, hX''p, hUV, hXV'', hXU, hcommVX⟩ :=
      exists_q8_config H N hsig.odd hsig.A.prime hsig.A.odd e hsetup'.W2 hsig.A.pgroup hXn hE'V
        hE'N hcard hcomm2 hE2 hEc hE8
    exact false_of_q8_centralized hcl hsig.A.prime hsig.A.odd (h29 G z k S ctx U' hU4) hV2' hVq
      hX''p hUV hXV'' hXU hcommVX

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
