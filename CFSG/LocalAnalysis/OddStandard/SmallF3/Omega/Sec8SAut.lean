module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SAutQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem autIn_mono_left {H K Y : Subgroup G} (h : H ≤ K) : autIn H Y ≤ autIn K Y :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono (normalizer (Y : Set G)) h)

private theorem sec1011_conjAut_inv {Y : Subgroup G} {m : G}
    (hm : m ∈ normalizer (Y : Set G)) :
    sec1011_conjAut Y m⁻¹ ((normalizer (Y : Set G)).inv_mem hm) =
      (sec1011_conjAut Y m hm)⁻¹ := by
  have h : (⟨m⁻¹, (normalizer (Y : Set G)).inv_mem hm⟩ : ↥(normalizer (Y : Set G))) =
      (⟨m, hm⟩ : ↥(normalizer (Y : Set G)))⁻¹ := rfl
  unfold sec1011_conjAut
  rw [h]
  exact MonoidHom.map_inv Y.normalizerMonoidHom ⟨m, hm⟩

private theorem conjAut_mul_mem_autIn {t : G} {L B : Subgroup G}
    (hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G))
    {h a : MulAut ↥B} (hh : h ∈ autIn (centralizer ({t} : Set G)) B)
    (ha : a ∈ autIn L B) : h * a * h⁻¹ ∈ autIn L B := by
  obtain ⟨m, hmC, hmN, rfl⟩ := sec1011_exists_conjAut hh
  obtain ⟨l, hlL, hlN, rfl⟩ := sec1011_exists_conjAut ha
  have hmL : m ∈ normalizer (L : Set G) := hN m hmC
  have hmlL : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hmL l).mp hlL
  have hmlN : m * l * m⁻¹ ∈ normalizer (B : Set G) :=
    (normalizer (B : Set G)).mul_mem ((normalizer (B : Set G)).mul_mem hmN hlN)
      ((normalizer (B : Set G)).inv_mem hmN)
  have hprod : sec1011_conjAut B m hmN * sec1011_conjAut B l hlN *
      (sec1011_conjAut B m hmN)⁻¹ = sec1011_conjAut B (m * l * m⁻¹) hmlN := by
    rw [← sec1011_conjAut_mul hmN hlN, ← sec1011_conjAut_inv hmN,
        ← sec1011_conjAut_mul ((normalizer (B : Set G)).mul_mem hmN hlN)
          ((normalizer (B : Set G)).inv_mem hmN)]
  rw [hprod]
  exact sec1011_conjAut_mem hmlL hmlN

theorem asc82FinkAut_of (h36 : Asc82Lemma36) (hM : Asc82Tab6M) (h8A : Asc82Lemma8A)
    (hN : Asc82NormA6) : Asc82FinkAut := by
  intro G _ _ t L S z g B E hE
  refine ⟨sec8s_autQ h8A hE, ?_⟩
  have hS : Sec3SettingLB G t L := hE.ctx.toSec3SettingLB
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hNmem : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hS
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hE.ctx.omega6m⟩
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLt hNmem hE.ctx.sylow
  have hBle : B ≤ S ⊓ L := by rw [inf_comm]; exact hE.ctx.B_le
  have hA6 : Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) :=
    (hM.aut_B G L hLM (S ⊓ L) hP B hBle hE.ctx.B_e16).1
  exact hN G B hE.ctx.B_e16 (autIn L B) (autIn (centralizer ({t} : Set G)) B)
    (autIn_mono_left hLt) hA6 (fun h hh a ha => conjAut_mul_mem_autIn hNmem hh ha)

end CFSG.OddStandard.SmallF3.Omega
