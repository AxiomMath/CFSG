module

public import CFSG.GH74.Generic.BProg.B2.T1Pre
public import CFSG.GH74.Generic.BProg.B2.T1G2Types
public import CFSG.GH74.Generic.BProg.B2.T4ElimAssembly
import CFSG.GH74.Generic.BProg.B2.SDCheap
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyBasic
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC2
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC3
import CFSG.GH74.Generic.BProg.B2.T1Comp
import CFSG.GH74.Generic.BProg.B2.Prop31
import CFSG.GH74.Generic.JMaxCongr
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.OddRankG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs
public import CFSG.Sporadic.Schreier.LyFixedSet
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.Generic.BProg.B2

namespace T1G2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem inCalK2_of_isComponent_Mbar (hG : IsKProperSimple G) (hM : M ≠ ⊤) {L : Subgroup (Mbar M)}
    (hL : IsComponent L) : InCalK2 ↥L := by
  obtain ⟨-, -, hKP⟩ := hG
  refine ⟨hL.1, ?_, ?_⟩
  · have hX : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥M
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, isPGroup_two_center_of_subnormal hX hL.2⟩
    · have hN : (pCore 2 ↥L).Normal := inferInstance
      rcases LocalCores.quasisimple_normal_subgroups hL.1 hN with h | h
      · exfalso
        have hP : IsPGroup 2 ↥L := by
          have := pCore_isPGroup (p := 2) (G := ↥L)
          rw [h] at this
          exact this.of_equiv (Subgroup.topEquiv (G := ↥L))
        have : Group.IsNilpotent ↥L := hP.isNilpotent
        have : Nontrivial ↥L := LocalCores.isQuasisimple_nontrivial hL.1
        have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L
        have : Group.IsPerfect ↥L := hL.1.1
        have h2 : commutator ↥L = ⊤ := Group.IsPerfect.commutator_eq_top
        rw [h2] at h1
        exact lt_irrefl _ h1
      · exact h
  · have hC : IsKGroupNative ↥M := isKGroupNative_of_kProper hKP hM
    let N := pPrimeCore 2 ↥M
    let L' : Subgroup ↥M := L.comap (QuotientGroup.mk' N)
    let φ : L' →* ↥L := ((QuotientGroup.mk' N).comp L'.subtype).codRestrict L fun y => y.2
    have hφ : Function.Surjective φ := fun k => by
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (k : Mbar M)
      exact ⟨⟨y, show QuotientGroup.mk' N y ∈ L by rw [hy]; exact k.2⟩, Subtype.ext hy⟩
    exact isKGroupNative_of_surjective hC L' φ hφ

theorem inG2_barIn_K (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) (hKc : IsComponent (barIn M K)) :
    InG2 ↥(barIn M K) := by
  obtain ⟨e⟩ := SD2.SDCheap.exists_equiv_barIn hKM hKc
  exact inG2_of_mulEquiv e hs.pair.1.1.2

theorem inG2_barIn_K_of_center (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M)
    (hq : IsQuasisimple ↥(barIn M K)) (hZ : center ↥(barIn M K) = ⊥) : InG2 ↥(barIn M K) := by
  obtain ⟨Z, hZc, -, hZn, ⟨e⟩⟩ := T4.T4ElimAssembly.exists_shape_iso hKM hq
  have hZb : Z = ⊥ := le_bot_iff.1 (hZc.trans hZ.le)
  subst hZb
  exact inG2_of_mulEquiv (e.trans QuotientGroup.quotientBot) hs.pair.1.1.2

theorem h_G2_of_pre
    (hL4m : TA7.RefinePuL4) (hG2r : TA7.RefinePuG2) (hB : B_B2_g4) (hPump : PumpupTableU)
    (hs : Stage2Setup G x K A M P Q) {H : Subgroup G} (h1 : Stage2Concl1Pre x K M Q H) :
    ∀ L : Subgroup (Mbar M), IsComponent L → L ≤ barIn M H → InG2 ↥L := by
  intro L hL hLH
  have hG : IsKProperSimple G := ⟨hs.hyp.simple, hs.hyp.nonab, kProper_of_kgh hs.hyp.kgh⟩
  have hCal := inCalK2_of_isComponent_Mbar hG hs.maxM.1 hL
  rcases h1.H_tri with hc1 | ⟨hF, hsimple⟩ | ⟨hF, hx, L₁, L₂, hL₁, hL₂, hne, hs₁, hs₂, hsup, hconj, hall⟩
  ·
    obtain ⟨hKc, -⟩ := components_c1_pre hs h1 hc1
    have hLK : L = barIn M K := T1Comp.eq_of_isComponent_le hL hKc (hc1 ▸ hLH)
    rw [hLK]
    exact inG2_barIn_K hs h1.K_le hKc
  ·
    have hLH' : L = barIn M H := Thm2AssemblyBasic.components_c2 hF hsimple L hL
    have hHt := puTargetG4_of_c2_pre hL4m hG2r hB hPump hs h1 hF hsimple
    have hnab := Thm2AssemblyC2.barIn_nonabelian_of_simple hs h1.K_le hF hsimple
    have hgen : Gen4 ↥(barIn M H) := Gen4.subgroup _ (sectionalTwoRankLE_Mbar hs)
    obtain ⟨hC2, hT2⟩ := not_inC2_not_inT2_of_puTargetG4 hsimple hnab hgen hHt
    rw [hLH'] at hCal ⊢
    exact ⟨hCal, hC2, hT2⟩
  ·
    have := hs₁
    set t : Mbar M := (QuotientGroup.mk (⟨x, hx⟩ : ↥M) : Mbar M) with htdef
    have ht2 : orderOf t = 2 := Prop31.orderOf_mk_involution hx hs.pair.1.1.1.1
    have ht : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2, pow_two] at this
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have h12 : ∀ a ∈ L₁, t * a * t⁻¹ ∈ L₂ := by
      intro a ha
      have := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom ha
      rw [hconj] at this
      simpa using this
    have h21 : ∀ b ∈ L₂, t * b * t⁻¹ ∈ L₁ := by
      intro b hb
      rw [← hconj] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      have e : t * ((MulAut.conj t).toMonoidHom a) * t⁻¹ = a := by
        show t * (t * a * t⁻¹) * t⁻¹ = a
        rw [htinv]
        calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
          _ = a := by rw [ht]; simp
      rw [e]; exact ha
    have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
      intro a ha b hb
      have hle : L₁ ≤ centralizer (L₂ : Set (Mbar M)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1
          ((CFSG.LocalCores.distinct_components_commute hL₁ hL₂).resolve_left hne)
      exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
    have hZ1 : center ↥L₁ = ⊥ := Thm2AssemblyC3.center_eq_bot_of_simple_quasisimple hL₁.1 hs₁
    have hcap : L₁ ⊓ L₂ = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzc : (⟨z, hz.1⟩ : ↥L₁) ∈ center ↥L₁ := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hc g g.2 z hz.2)
      rw [hZ1, Subgroup.mem_bot] at hzc
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hzc)
    obtain ⟨e⟩ := Thm2AssemblyC3.mulEquiv_centralizer_of_swap ht hc hcap h12 h21
    set N : Subgroup (Mbar M) := (L₁ ⊔ L₂) ⊓ centralizer ({t} : Set (Mbar M)) with hN
    have hNsimple : IsSimpleGroup ↥N := e.symm.isSimpleGroup
    have hcomp := barIn_K_isCompIn hB hs h1.K_le hx
    have hKH : K ≤ H := h1.H_min.1
    have hbarKH : barIn M K ≤ L₁ ⊔ L₂ := by
      rw [← hsup]
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hKH hm, rfl⟩
    have hcomp' : IsCompIn N (barIn M K) :=
      Prop31.isCompIn_of_le (le_inf hbarKH hcomp.1) inf_le_right hcomp
    have hKN : barIn M K = N := Thm2AssemblyC3.eq_of_isCompIn_of_simple hNsimple hcomp'
    have hKq : IsQuasisimple ↥(barIn M K) := Prop31.isQuasisimple_of_isCompIn hcomp
    let e' : ↥(barIn M K) ≃* ↥L₁ := (MulEquiv.subgroupCongr hKN).trans e.symm
    have hKsimple : IsSimpleGroup ↥(barIn M K) := e'.isSimpleGroup
    have hKG2 : InG2 ↥(barIn M K) := inG2_barIn_K_of_center hs h1.K_le hKq
      (Thm2AssemblyC3.center_eq_bot_of_simple_quasisimple hKq hKsimple)
    have hG21 : InG2 ↥L₁ := inG2_of_mulEquiv e' hKG2
    rcases hall L hL with rfl | rfl
    · exact hG21
    · have e2 : ↥L₁ ≃* ↥L :=
        ((L₁.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)).trans
          (MulEquiv.subgroupCongr hconj)
      exact inG2_of_mulEquiv e2 hG21

end T1G2

end CFSG.GH74.Generic.BProg.B2
