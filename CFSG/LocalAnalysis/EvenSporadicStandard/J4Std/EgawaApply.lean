module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.EgawaIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.EgawaQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Wreath

public section

namespace CFSG.EvenSporadicStandard.J4Std.EgawaApply

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}

theorem ebasis_single (e : Fin 11 → G) :
    ebasis e (fun j => if j = 0 then 1 else 0) = e 0 := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [ebasis, List.ofFn_succ, Fin.succ_ne_zero, h1]

theorem not_mem_of_lift {e : Fin 11 → G} {s : G}
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (he : ∀ i, e i ∈ U)
    (hinj : ∀ c d : Fin 11 → ZMod 2, ebasis e c = ebasis e d → c = d)
    (hse : ∀ i, s * e i * s⁻¹ = ebasis e (fun j => Smat i j)) : s ∉ U := by
  intro hsU
  have h1 : s * e 0 * s⁻¹ = e 0 := by
    have := hcomm s hsU (e 0) (he 0)
    calc s * e 0 * s⁻¹ = e 0 * s * s⁻¹ := by rw [this]
      _ = e 0 := by group
  rw [hse 0, ← ebasis_single e] at h1
  have h3 := congrFun (hinj _ _ h1) 3
  revert h3
  decide

theorem exists_index_two [Finite G] (hA : M24Std.Ega81HypAZ2A8K) (hE : Ega81M24Section)
    (hKS : M24Std.KLocalSections G) (hS : Setting L z) (hD : LocalData L U T0)
    (hM : ModData L U) (hY : YStruct L U z Y) (hW : WeakData U z Y)
    (hF : FusionData L U z Y) :
    ∃ E : Subgroup ↥(Mn Y), E.index = 2 ∧ (⟨z, z_mem_M hF⟩ : ↥(Mn Y)) ∉ E := by
  have hzM := z_mem_M hF
  have hH := Hloc_le_M hS hD hF
  have htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u := fun u hu => by
    obtain ⟨w, hw, hwz⟩ := hW.z_conj_W u hu
    exact ⟨w, (mem_Csub.1 hw).1, hwz⟩
  obtain ⟨e, s, -, heU, hinj, hsH, -, hss, -, -, hse, -⟩ := hM.lift
  have hsU : s ∉ U := not_mem_of_lift hD.U_comm heU hinj hse
  obtain ⟨x, hx1, hx2⟩ := exists_conj_ne hS hD hY hF htrans hzM hsH hsU
    (hM.invConj s (Hloc_le_L hsH) hss)
  have hKY : CFSG.SectionRank.IsKGroupCat (Sec Y) := by
    refine hKS Y (fun h => ?_) hW.Y_comm
    have := hW.card_Y
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨E, -, hEidx, hzE⟩ := hE hA (Sec Y) hKY (pi Y ⟨z, hzM⟩) (psi hH).range
    (pi_z_mul_self hS hzM) (pi_z_ne_one hY hzM) (isSporadic_range_psi hD hY hH hM.quot)
    (by rintro k ⟨h, rfl⟩; exact psi_comm_pi hS hH hzM h)
    (fun x hx => cover_of_comm hS hD hY hF hzM x hx) ⟨x, hx1, hx2⟩
  refine ⟨E.comap (pi Y), ?_, hzE⟩
  rw [index_comap_of_surjective _ (pi_surjective Y)]
  exact hEidx

end CFSG.EvenSporadicStandard.J4Std.EgawaApply

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

theorem false_of_fusionData {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hA : M24Std.Ega81HypAZ2A8K) (hE : Ega81M24Section)
    (hKS : M24Std.KLocalSections G) {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}
    (hS : Setting L z) (hD : LocalData L U T0) (hM : ModData L U) (hY : YStruct L U z Y)
    (hW : WeakData U z Y) (hF : FusionData L U z Y) : False := by
  obtain ⟨E, hEidx, hzE⟩ := EgawaApply.exists_index_two hA hE hKS hS hD hM hY hW hF
  obtain ⟨φ, hφ⟩ := exists_hom_of_index_two E hEidx
  have hzM := EgawaApply.z_mem_M hF
  have hφz : φ ⟨z, hzM⟩ = -1 := by
    rcases Int.units_eq_one_or (φ ⟨z, hzM⟩) with h | h
    · exact absurd ((hφ _).1 h) hzE
    · exact h
  exact false_of_fusion_control (hom_units_eq_one_of_simple hnonab) hS.z_mul_self
    (EgawaApply.Mn Y) hzM φ hφz (fun y _ hy => hF.fuse y y.2 hy)
    (EgawaApply.not_two_dvd_relIndex hS hD hF)

end CFSG.EvenSporadicStandard.J4Std
