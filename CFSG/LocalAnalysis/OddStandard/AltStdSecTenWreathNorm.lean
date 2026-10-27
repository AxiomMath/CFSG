module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarWreath

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

theorem WreathK.map_conj_eq_or (hK : WreathK t A K) (g : X) :
    K.map (MulAut.conj g).toMonoidHom = K ∨ K.map (MulAut.conj g).toMonoidHom = conjSub t K := by
  exact eq_or_eq_of_isComponent_of_layer hK.comp hK.comp_conjSub hK.layer
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK.comp)

theorem WreathK.map_conj_conjSub_eq_or (hK : WreathK t A K) (g : X) :
    (conjSub t K).map (MulAut.conj g).toMonoidHom = K ∨
      (conjSub t K).map (MulAut.conj g).toMonoidHom = conjSub t K := by
  exact eq_or_eq_of_isComponent_of_layer hK.comp hK.comp_conjSub hK.layer
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK.comp_conjSub)

theorem WreathK.t_notMem_normalizer (hK : WreathK t A K) : t ∉ normalizer (K : Set X) := by
  intro ht
  exact hK.ne (by
    rw [conjSub]
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp ht))

theorem WreathK.map_conj_eq_conjSub_of_notMem (hK : WreathK t A K) {u : X}
    (hu : u ∉ normalizer (K : Set X)) : K.map (MulAut.conj u).toMonoidHom = conjSub t K := by
  rcases hK.map_conj_eq_or u with h | h
  · exact absurd (mem_normalizer_of_map_conj_eq h) hu
  · exact h

theorem WreathK.map_conj_conjSub_eq_of_notMem (hK : WreathK t A K) {u : X} (hu2 : u * u = 1)
    (hu : u ∉ normalizer (K : Set X)) : (conjSub t K).map (MulAut.conj u).toMonoidHom = K := by
  have hu' : K.map (MulAut.conj u).toMonoidHom = conjSub t K :=
    hK.map_conj_eq_conjSub_of_notMem hu
  calc (conjSub t K).map (MulAut.conj u).toMonoidHom
      = (K.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u).toMonoidHom := by rw [hu']
    _ = K.map (MulAut.conj (u * u)).toMonoidHom := map_conj_map_conj K u u
    _ = K.map (MulAut.conj (1 : X)).toMonoidHom := by rw [hu2]
    _ = K := by
          rw [show MulAut.conj (1 : X) = 1 from map_one MulAut.conj]
          exact Subgroup.map_id K

theorem WreathK.index_normalizer (hK : WreathK t A K) (ht : t * t = 1) :
    (normalizer (K : Set X)).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨t, fun b => ?_⟩
  rw [xor_iff_iff_not]
  by_cases hb : b ∈ normalizer (K : Set X)
  · exact ⟨fun hbt hb' => hK.t_notMem_normalizer (by
        simpa using (normalizer (K : Set X)).mul_mem (inv_mem hb') hbt),
      fun hnb => absurd hb hnb⟩
  · refine ⟨fun _ => hb, fun _ => ?_⟩
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    have hbmap : K.map (MulAut.conj b).toMonoidHom = conjSub t K :=
      hK.map_conj_eq_conjSub_of_notMem hb
    have hbb : (conjSub t K).map (MulAut.conj b).toMonoidHom = K := by
      rcases hK.map_conj_conjSub_eq_or b with h | h
      · exact h
      · exfalso
        apply hK.ne
        have hinj : Function.Injective (Subgroup.map (MulAut.conj b).toMonoidHom) :=
          Subgroup.map_injective (MulAut.conj b).injective
        apply hinj
        rw [h, ← hbmap]
    calc K.map (MulAut.conj (b * t)).toMonoidHom
        = (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
          rw [map_conj_map_conj K t b]
      _ = (conjSub t K).map (MulAut.conj b).toMonoidHom := by
          rw [show K.map (MulAut.conj t).toMonoidHom = conjSub t K from rfl]
      _ = K := hbb

theorem WreathK.mem_normalizer_conjSub (hK : WreathK t A K) {s : X}
    (hs : s ∈ normalizer (K : Set X)) : s ∈ normalizer (conjSub t K : Set X) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have hsm : K.map (MulAut.conj s).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
  rcases hK.map_conj_conjSub_eq_or s with h | h
  · exfalso
    apply hK.ne
    have hinj : Function.Injective (Subgroup.map (MulAut.conj s).toMonoidHom) :=
      Subgroup.map_injective (MulAut.conj s).injective
    apply hinj
    rw [h, hsm]
  · exact h

end CFSG.OddStandard.AltStdSec.SwapPattern
