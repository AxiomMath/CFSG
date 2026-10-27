module

public import CFSG.GH74.Generic.BProg.B1.Stage3aSD
public import CFSG.GH74.Generic.BProg.Stage2QSProof
import CFSG.GH74.Generic.BProg.Stage2QSProofAbs
import CFSG.GH74.Generic.BProg.B1.PilotS3
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement MatrixGroups

theorem stage2QSFor_shape3_of_allow (hAll : Stage2Allow) : Stage2QSFor QShape3 := by
  intro G _ _ hyp noAlt x K hcirc hshape
  obtain ⟨A, hsrc⟩ := PilotS3.exists_source_of_shape3 hcirc.1.1.1.1 hcirc.1.1.1.2.2 hshape
  obtain ⟨y, Lb, hadm⟩ := PilotS3.exists_adm_of_shape3 hcirc.1.1.1.1 hcirc.1.1.1.2.2 hshape hsrc
  have hss : NbhdSemisimple x y Lb := hAll G hyp noAlt x K hcirc A hsrc y Lb hadm
  have hx2 : orderOf x = 2 := hcirc.1.1.1.1
  have hxC : K ≤ centralizer ({x} : Set G) := hcirc.1.1.1.2.2.1
  have hKc : IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set G))) := hcirc.1.1.1.2.2.2
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx2
    omega
  have hcomm : ⁅liftAt x y Lb, pPrimeCoreOf 2 (centralizer ({x} : Set G))⁆ = ⊥ :=
    hss x (Subgroup.subset_closure (Set.mem_insert _ _)) hx1
  have hyC : y ∈ centralizer ({x} : Set G) := hadm.sub.y_mem
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hadm.sub.y_ord, pow_two] at this
  obtain ⟨hLH, a, b, haL, hbL, ⟨ka, ha⟩, ⟨kb, hb⟩, hab⟩ :=
    exists_noncomm_two_elements_of_isQuasi2CompIn
      (H := centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ imgBar x K) (Lb := Lb)
      (hadm.sub.rel.2.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  obtain ⟨g₁, hg₁C, hg₁L, hg₁a, m₁, hm₁⟩ :=
    exists_mem_liftAt_of_two_pow_eq_one hyC hy2 haL
      (Subgroup.mem_centralizer_singleton_iff.1 (hLH haL).1) ha
  obtain ⟨g₂, hg₂C, hg₂L, hg₂b, m₂, hm₂⟩ :=
    exists_mem_liftAt_of_two_pow_eq_one hyC hy2 hbL
      (Subgroup.mem_centralizer_singleton_iff.1 (hLH hbL).1) hb
  have hmemK : ∀ (g : G) (hgC : g ∈ centralizer ({x} : Set G)) (m : ℕ) (c : CentralizerBar x),
      g ^ (2 ^ m) = 1 → proj x ⟨g, hgC⟩ = c → c ∈ imgBar x K → g ∈ K := by
    intro g hgC m c hgm hgc hcK
    have hgm' : (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) ^ (2 ^ m) = 1 :=
      Subtype.ext (by simpa using hgm)
    have := mem_of_two_pow_eq_one_of_map_mem hKc hgm' (by rw [← hgc] at hcK; exact hcK)
    exact Subgroup.mem_subgroupOf.1 this
  have hg₁K : g₁ ∈ K := hmemK g₁ hg₁C m₁ a hm₁ hg₁a (hLH haL).2
  have hg₂K : g₂ ∈ K := hmemK g₂ hg₂C m₂ b hm₂ hg₂b (hLH hbL).2
  have hcent : ∀ w ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)),
      (⟨g₁, hg₁C⟩ : ↥(centralizer ({x} : Set G))) * w = w * ⟨g₁, hg₁C⟩ := by
    intro w hw
    have hwO : (w : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := ⟨w, hw, rfl⟩
    have h1 : ⁅g₁, (w : G)⁆ ∈ ⁅liftAt x y Lb, pPrimeCoreOf 2 (centralizer ({x} : Set G))⁆ :=
      Subgroup.commutator_mem_commutator hg₁L hwO
    rw [hcomm, Subgroup.mem_bot] at h1
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hnc : QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₁, hg₁C⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₂, hg₂C⟩ ≠
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₂, hg₂C⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G))) ⟨g₁, hg₁C⟩ := by
    change proj x ⟨g₁, hg₁C⟩ * proj x ⟨g₂, hg₂C⟩ ≠ proj x ⟨g₂, hg₂C⟩ * proj x ⟨g₁, hg₁C⟩
    rw [hg₁a, hg₂b]
    exact hab
  have hq := (isQuasisimple_of_isPComponent_of_noncomm hKc
    (Subgroup.mem_subgroupOf.2 hg₁K) (Subgroup.mem_subgroupOf.2 hg₂K) hcent hnc).2
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hxC) hq

theorem noJPrimeShape3SD_of_allow
    (hAllow : Stage2Allow) : NoJPrimeShape3SD :=
  noJPrimeShape3SD_of_pumpSS (stage2QSFor_shape3_of_allow hAllow) (stage2PumpSS_of_allow hAllow)

end CFSG.GH74.Generic.BProg.B1
