module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.SylowConj

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem normIn_le_centEl_of_cen {V X : Subgroup Γ} {z : Γ} (hcen : cen X = zpowers z)
    (h1 : z ≠ 1) (h2 : z * z = 1) : normIn V X ≤ centEl V z := by
  intro g hg
  obtain ⟨hgV, hgN⟩ := hg
  refine ⟨hgV, ?_⟩
  change g ∈ Subgroup.centralizer ({z} : Set Γ)
  have hzcen : z ∈ cen X := by rw [hcen]; exact Subgroup.mem_zpowers z
  have hzX : z ∈ X := hzcen.1
  have hzcent : z ∈ centralizer (X : Set Γ) := hzcen.2
  have hgzgX : g * z * g⁻¹ ∈ X := (mem_set_normalizer_iff.mp hgN z).mp hzX
  have hgzgC : g * z * g⁻¹ ∈ centralizer (X : Set Γ) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hgixgX : g⁻¹ * x * g ∈ X := by
      exact (mem_set_normalizer_iff.mp hgN (g⁻¹ * x * g)).mpr (by
        show g * (g⁻¹ * x * g) * g⁻¹ ∈ X
        simpa [mul_assoc] using hx)
    have hzcomm := (mem_centralizer_iff.mp hzcent) (g⁻¹ * x * g) hgixgX
    calc x * (g * z * g⁻¹)
        = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hzcomm]
      _ = (g * z * g⁻¹) * x := by group
  have hmem : g * z * g⁻¹ ∈ zpowers z := by
    rw [← hcen]
    exact ⟨hgzgX, hgzgC⟩
  have hgzg_ne : g * z * g⁻¹ ≠ 1 := by
    intro hzero
    apply h1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hzero]; group
  have hgzg : g * z * g⁻¹ = z := by
    rcases zpowers_eq_one_or_self h1 h2 hmem with h | h
    · exact absurd h hgzg_ne
    · exact h
  rw [mem_centralizer_singleton_iff]
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hgzg]

theorem mem_centralizer_of_comm_mem {z g : Γ} (h1 : z ≠ 1) (h2 : z * z = 1)
    (hg : ⁅z, g⁆ ∈ zpowers z) : g * z * g⁻¹ = z := by
  rcases zpowers_eq_one_or_self h1 h2 hg with hcz | hcz
  · have hcz' : z * g * z⁻¹ * g⁻¹ = 1 := by simpa [commutatorElement_def] using hcz
    have hz : z * g * z⁻¹ = g := by
      have := congrArg (fun x => x * g) hcz'
      simpa [mul_assoc] using this
    have hcomm : z * g = g * z := by
      calc z * g = (z * g * z⁻¹) * z := by group
        _ = g * z := by rw [hz]
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hcomm]
      _ = z := by group
  · exfalso
    have hcz' : z * g * z⁻¹ * g⁻¹ = z := by simpa [commutatorElement_def] using hcz
    have hone : g * z⁻¹ * g⁻¹ = 1 := by
      have := congrArg (fun x => z⁻¹ * x) hcz'
      simpa [mul_assoc] using this
    have hzinv : z⁻¹ = 1 := by
      calc z⁻¹ = g⁻¹ * (g * z⁻¹ * g⁻¹) * g := by group
        _ = 1 := by rw [hone]; group
    exact h1 (by simpa using hzinv)

theorem conjSub_mem_maxElemAbelian {V Y : Subgroup Γ} {c : Γ} (hc : c ∈ V)
    (hY : Y ∈ maxElemAbelian V) : conjSub c Y ∈ maxElemAbelian V := by
  obtain ⟨hYV, hYab, hYmax⟩ := hY
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub.mp hx
    exact V.mul_mem (V.mul_mem hc (hYV hy)) (V.inv_mem hc)
  · exact isElemAbelian_conjSub hYab c
  · intro Y' hYY' hY'V hY'ab
    have hle1 : Y ≤ conjSub c⁻¹ Y' := by
      rw [← conjSub_inv_conjSub c Y]
      change (conjSub c Y).map (MulAut.conj c⁻¹).toMonoidHom ≤
        Y'.map (MulAut.conj c⁻¹).toMonoidHom
      exact Subgroup.map_mono hYY'
    have hle2 : conjSub c⁻¹ Y' ≤ V := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_conjSub.mp hx
      rw [inv_inv]
      exact V.mul_mem (V.mul_mem (V.inv_mem hc) (hY'V hy)) hc
    have hle3 : IsElemAbelian 2 (conjSub c⁻¹ Y') := isElemAbelian_conjSub hY'ab c⁻¹
    have hEq : conjSub c⁻¹ Y' = Y := hYmax _ hle1 hle2 hle3
    have hthis : conjSub c (conjSub c⁻¹ Y') = conjSub c Y := by rw [hEq]
    rwa [conjSub_conjSub_inv c Y'] at hthis

theorem mem_maxElemAbelian_of_le {L S Y : Subgroup Γ} (hSL : S ≤ L) (hYS : Y ≤ S)
    (hY : Y ∈ maxElemAbelian L) : Y ∈ maxElemAbelian S := by
  obtain ⟨hYL, hYab, hYmax⟩ := hY
  exact ⟨hYS, hYab, fun Y' hYY' hY'S hY'ab => hYmax Y' hYY' (hY'S.trans hSL) hY'ab⟩

theorem exists_conj_mem_maxElemAbelian_of_sylow [Finite Γ] {L S Y : Subgroup Γ}
    (hS : IsSylowIn 2 L S) (hY : Y ∈ maxElemAbelian L) :
    ∃ g ∈ L, conjSub g Y ∈ maxElemAbelian S := by
  obtain ⟨hYL, hYab, hYmax⟩ := hY
  have hYsub_ab : IsElemAbelian 2 (Y.subgroupOf L) := by
    rw [← Subgroup.comap_subtype]
    exact IsElemAbelian.comap hYab L.subtype_injective
  obtain ⟨P, hYP⟩ := IsPGroup.exists_le_sylow (IsElemAbelian.isPGroup hYsub_ab)
  let P' : Subgroup Γ := (P : Subgroup ↥L).map L.subtype
  have hYP' : Y ≤ P' := by
    intro y hy
    have hy' : (⟨y, hYL hy⟩ : ↥L) ∈ Y.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact hy
    exact Subgroup.mem_map.mpr ⟨⟨y, hYL hy⟩, hYP hy', rfl⟩
  have hP'syl : IsSylowIn 2 L P' := by
    refine ⟨Subgroup.map_subtype_le (P : Subgroup ↥L), IsPGroup.map P.isPGroup' L.subtype, ?_⟩
    have hidx : P'.relIndex L = P.index := by
      have h1 : P'.relIndex L = (P'.subgroupOf L).index := by
        rw [← Subgroup.relIndex_subgroupOf (H := P') (K := L) (L := L) le_rfl,
          Subgroup.subgroupOf_self, Subgroup.relIndex_top_right]
      have h2 : P'.subgroupOf L = (P : Subgroup ↥L) := by
        change (((P : Subgroup ↥L).map L.subtype).subgroupOf L) = P
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective (P : Subgroup ↥L)
      rw [h1, h2]
    rw [hidx]
    exact P.not_dvd_index
  obtain ⟨g, hgL, hgS⟩ := exists_conj_of_isSylowIn hP'syl hS
  refine ⟨g, hgL, ?_⟩
  have hconjL : conjSub g Y ∈ maxElemAbelian L :=
    conjSub_mem_maxElemAbelian hgL ⟨hYL, hYab, hYmax⟩
  have hleS : conjSub g Y ≤ S := by
    rw [hgS]
    change Y.map (MulAut.conj g).toMonoidHom ≤ P'.map (MulAut.conj g).toMonoidHom
    exact Subgroup.map_mono hYP'
  exact mem_maxElemAbelian_of_le hS.1 hleS hconjL

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
