module

public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Timmesfeld.Bridge.NoPolarConnected

public section

namespace CFSG.GroupTheory

open CFSG.Open

private theorem exists_a6_two_group :
    ∃ x y : alternatingGroup (Fin 6), x * x = 1 ∧ x * y ≠ y * x ∧
      ∃ P : Subgroup (alternatingGroup (Fin 6)), IsPGroup 2 P ∧ x ∈ P ∧ y ∈ P := by
  open CFSG.LieType.SteinbergBR.SmallAlt in
  let x : alternatingGroup (Fin 6) :=
    ⟨a6P 6, Equiv.Perm.mem_alternatingGroup.mpr (a6P_sign 6)⟩
  let y : alternatingGroup (Fin 6) :=
    ⟨a6P 4, Equiv.Perm.mem_alternatingGroup.mpr (a6P_sign 4)⟩
  let P : Subgroup (alternatingGroup (Fin 6)) :=
    finSubgroup a6P a6P_mul a6P_inv a6P_one
  have hPcard : Nat.card P = 8 :=
    card_finSubgroup a6P a6P_mul a6P_inv a6P_one a6P_injective
      fun i => (Equiv.Perm.mem_alternatingGroup).2 (a6P_sign i)
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hPcard]; norm_num)
  exact ⟨x, y, by decide, by decide, P, hP2, ⟨6, rfl⟩, ⟨4, rfl⟩⟩

private theorem exists_alt_two_group {n : ℕ} (hn : 6 ≤ n) :
    ∃ x y : alternatingGroup (Fin n), x * x = 1 ∧ x * y ≠ y * x ∧
      ∃ P : Subgroup (alternatingGroup (Fin n)), IsPGroup 2 P ∧ x ∈ P ∧ y ∈ P := by
  obtain ⟨x0, y0, hx0sq, hxy0, P0, hP02, hx0P, hy0P⟩ := exists_a6_two_group
  obtain ⟨ι⟩ : Nonempty (Fin 6 ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hn)
  set F : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin n) :=
    Equiv.Perm.extendDomainHom ι.toEquivRange with hFdef
  have hF : Function.Injective F := Equiv.Perm.extendDomainHom_injective _
  have hFalt : ∀ σ : alternatingGroup (Fin 6), F σ ∈ alternatingGroup (Fin n) := fun σ => by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.extendDomainHom_apply,
      Equiv.Perm.sign_extendDomain]
    exact Equiv.Perm.mem_alternatingGroup.mp σ.2
  set F' : alternatingGroup (Fin 6) →* alternatingGroup (Fin n) :=
    (F.comp (alternatingGroup (Fin 6)).subtype).codRestrict _ hFalt with hF'def
  have hF' : Function.Injective F' := fun x y h =>
    Subtype.ext (hF (congrArg Subtype.val h))
  refine ⟨F' x0, F' y0, ?_, ?_, P0.map F', hP02.map F',
    Subgroup.mem_map_of_mem F' hx0P, Subgroup.mem_map_of_mem F' hy0P⟩
  · show F' x0 * F' x0 = 1
    rw [← map_mul, hx0sq, map_one]
  · intro h
    exact hxy0 (hF' (by simpa only [map_mul] using h))

theorem not_fusionIsBenderGroup_of_mulEquiv_alternatingGroup {Y : Type*} [Group Y] [Finite Y]
    {n : ℕ} (hn : 6 ≤ n) (e : Y ≃* alternatingGroup (Fin n)) :
    ¬ fusionIsBenderGroup Y := by
  classical
  intro hB
  have hY : fusionIsBenderGroup (alternatingGroup (Fin n)) :=
    CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv e hB
  have hK : CFSG.BenderSuzuki.IsBenderGroup (alternatingGroup (Fin n)) :=
    CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup hY
  obtain ⟨x, y, hxsq, hxy, P, hP2, hxP, hyP⟩ := exists_alt_two_group hn
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  have hxQ : x ∈ (Q : Subgroup (alternatingGroup (Fin n))) := hPQ hxP
  have hyQ : y ∈ (Q : Subgroup (alternatingGroup (Fin n))) := hPQ hyP
  have hcomm := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one
    hK Q hxQ hxsq y hyQ
  exact hxy hcomm.eq
