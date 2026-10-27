module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Completion
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.SUGeneration
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Simple

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.SeitzReduction.UnitaryPilot

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem zero_ne_one_fin_succ {m : ℕ} (hm : 2 ≤ m) :
    (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval

private theorem pair_zero_one_subset_deletionSet {m : ℕ} (hm : 2 ≤ m) :
    ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (m + 1))) ⊆
      Finset.univ.erase (Fin.last m) := by
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
  rcases hx with rfl | rfl
  · intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  · intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega

private theorem normBlock_pair_le_sup {m : ℕ} (hm : 2 ≤ m) {a b : Fin (m + 1)} (hab : a ≠ b) :
    normBlock E (m + 1) ({a, b} : Finset (Fin (m + 1))) ≤
      (normOmegaCast E (Nat.le_succ m)).range ⊔ (normPerm E (by omega : 3 ≤ m + 1)).range := by
  classical
  have hn3 : 3 ≤ m + 1 := by omega
  let L : Subgroup (normOmega E (m + 1)) :=
    (normOmegaCast E (Nat.le_succ m)).range ⊔ (normPerm E hn3).range
  have hsub := pair_zero_one_subset_deletionSet hm
  have hP₀_le : normBlock E (m + 1)
      ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (m + 1))) ≤ L := by
    refine (normBlock_mono E (m + 1) hsub).trans ?_
    intro x hx
    rw [show normBlock E (m + 1) (Finset.univ.erase (Fin.last m)) =
        (normOmegaCast E (Nat.le_succ m)).range from (range_normOmegaCast_succ E m).symm] at hx
    exact Subgroup.mem_sup_left hx
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (m + 1)))
    ({a, b} : Finset (Fin (m + 1)))
    (by rw [Finset.card_pair (zero_ne_one_fin_succ (m := m) hm), Finset.card_pair hab])
  have himage : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (m + 1))).image σ =
      ({a, b} : Finset (Fin (m + 1))) := by
    have h := hσ
    rw [Finset.map_eq_image] at h
    simpa only [Equiv.coe_toEmbedding] using h
  rw [← himage, ← map_normBlock_normPerm E hn3 σ]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hg : normPerm E hn3 σ ∈ L :=
    Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
  have hconj : normPerm E hn3 σ * y * (normPerm E hn3 σ)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem hg (hP₀_le hy)) (L.inv_mem hg)
  simpa [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hconj

theorem range_normOmegaCast_sup_range_normPerm {m : ℕ} (hm : 2 ≤ m) :
    (normOmegaCast E (Nat.le_succ m)).range ⊔ (normPerm E (by omega : 3 ≤ m + 1)).range = ⊤ := by
  have htop : (⊤ : Subgroup (normOmega E (m + 1))) =
      ⨆ P : CFSG.Permutation.ProperSupportMaps.PairBelow
        (Finset.univ : Finset (Fin (m + 1))),
        normBlock E (m + 1) (P : Finset (Fin (m + 1))) := by
    have hcard : 2 ≤ (Finset.univ : Finset (Fin (m + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    rw [← normBlock_univ E (m + 1), normBlock_eq_iSup_pairs E (m + 1) Finset.univ hcard]
  rw [eq_top_iff, htop]
  exact iSup_le fun P => by
    obtain ⟨a, b, hab, hP⟩ := Finset.card_eq_two.mp P.2.2
    rw [hP]
    exact normBlock_pair_le_sup E hm hab

theorem injective_normOmega_hom {m : ℕ} (hm : 1 ≤ m)
    {H : Type} [Group H] (κ : normOmega E m →* H)
    (hκ : Function.Injective κ) (Ψ : normOmega E (m + 1) →* H)
    (hΨcast : ∀ a, Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a) :
    Function.Injective Ψ := by
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : IsSimpleGroup ↥(normOmega E (m + 1)) := isSimpleGroup_normOmega E (by omega)
  have hker : Ψ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top Ψ.ker with h | h
    · exact h
    · exfalso
      have hΨ1 : Ψ = 1 := MonoidHom.ker_eq_top_iff.mp h
      have hκ1 : κ = 1 := by
        ext a
        rw [← hΨcast a, hΨ1]
        exact MonoidHom.one_apply _
      haveI : IsSimpleGroup ↥(normOmega E m) := isSimpleGroup_normOmega E (by omega)
      have hsub : Subsingleton ↥(normOmega E m) := by
        refine ⟨fun a b => ?_⟩
        have ha : κ a = 1 := by rw [hκ1]; rfl
        have hb : κ b = 1 := by rw [hκ1]; rfl
        exact hκ (ha.trans hb.symm)
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial ↥(normOmega E m)).exists_pair_ne
      exact hab (Subsingleton.elim a b)
  exact (MonoidHom.ker_eq_bot_iff Ψ).mp hker

theorem range_normOmega_hom {m : ℕ} (hm : 2 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (Ψ : normOmega E (m + 1) →* H)
    (hΨcast : ∀ a, Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a)
    (hΨperm : ∀ σ, Ψ (normPerm E (by omega : 3 ≤ m + 1) σ) = t σ) :
    Ψ.range = κ.range ⊔ t.range := by
  have hn3 : 3 ≤ m + 1 := by omega
  have hcomp_perm : Ψ.comp (normPerm E hn3) = t := MonoidHom.ext hΨperm
  apply le_antisymm
  · calc Ψ.range = (⊤ : Subgroup ↥(normOmega E (m + 1))).map Ψ :=
          (Subgroup.map_top Ψ).symm
      _ = ((normOmegaCast E (Nat.le_succ m)).range ⊔
            (normPerm E hn3).range).map Ψ := by
            rw [range_normOmegaCast_sup_range_normPerm E hm]
      _ = (normOmegaCast E (Nat.le_succ m)).range.map Ψ ⊔
            (normPerm E hn3).range.map Ψ := Subgroup.map_sup _ _ _
      _ = (Ψ.comp (normOmegaCast E (Nat.le_succ m))).range ⊔
            (Ψ.comp (normPerm E hn3)).range := by
            rw [MonoidHom.range_comp, MonoidHom.range_comp]
      _ = κ.range ⊔ t.range := by
            rw [show Ψ.comp (normOmegaCast E (Nat.le_succ m)) = κ from
              MonoidHom.ext hΨcast, hcomp_perm]
    exact le_rfl
  · refine sup_le ?_ ?_
    · rintro y ⟨a, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨normOmegaCast E (Nat.le_succ m) a, hΨcast a⟩
    · rintro y ⟨σ, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨normPerm E hn3 σ, hΨperm σ⟩

private theorem range_normOmega_hom_of_unitary (h : UnitaryFieldData 2 f K) {m : ℕ}
    {H : Type} [Group H] (π : unitarySU 2 f K (m + 1) →* H) (κ : normOmega E m →* H)
    (Ψ : normOmega E (m + 1) →* H)
    (hΨcast : ∀ a, Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a)
    (hΨrange : Ψ.range = κ.range ⊔ (π.comp (permSUHom h)).range)
    (hpi : Ψ.comp (uniEmb E h (m + 1)) = π) :
    Ψ.range = κ.range ⊔ π.range := by
  have hle : (π.comp (permSUHom h)).range ≤ π.range := by
    rintro y ⟨σ, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨permSUHom h σ, rfl⟩
  apply le_antisymm
  · rw [hΨrange]
    exact sup_le le_sup_left (hle.trans le_sup_right)
  · refine sup_le ?_ ?_
    · rintro y ⟨a, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨normOmegaCast E (Nat.le_succ m) a, hΨcast a⟩
    · rintro y ⟨g, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨uniEmb E h (m + 1) g, DFunLike.congr_fun hpi g⟩

theorem exists_normOmega_hom_of_perm {m : ℕ} (hm : 4 ≤ m) {H : Type} [Group H]
    (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H) (hκ : Function.Injective κ)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ) :
    ∃ Ψ : normOmega E (m + 1) →* H, Function.Injective Ψ ∧
      (∀ a, Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a) ∧
      (∀ σ, Ψ (normPerm E (by omega : 3 ≤ m + 1) σ) = t σ) ∧
      Ψ.range = κ.range ⊔ t.range := by
  obtain ⟨Ψ, hΨcast, hΨperm⟩ := exists_hom_normOmegaCast_normPerm E hm t κ hT1 hT2
  exact ⟨Ψ, injective_normOmega_hom E (by omega) κ hκ Ψ hΨcast, hΨcast, hΨperm,
    range_normOmega_hom E (by omega) t κ Ψ hΨcast hΨperm⟩

private theorem comp_viaEmbeddingHom_of_unitary (h : UnitaryFieldData 2 f K) {m : ℕ}
    (hm : 3 ≤ m) {H : Type} [Group H] (π : unitarySU 2 f K (m + 1) →* H)
    (κ : normOmega E m →* H)
    (hU1 : ∀ g, κ (uniEmb E h m g) = π (uniCast h m g)) :
    (π.comp (permSUHom h)).comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E hm) := by
  refine MonoidHom.ext fun σ' => ?_
  show π (permSUHom h ((Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) σ')) =
    κ (normPerm E hm σ')
  rw [normPerm_eq_uniEmb E h hm σ', hU1,
    uniCast_permSUHom h σ' ((Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) σ')
      (fun i => by
        change (Equiv.Perm.viaEmbedding σ' (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)))
            ((Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i) =
          (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) (σ' i)
        rw [Equiv.Perm.viaEmbedding_apply])]

theorem exists_normOmega_hom_of_unitary (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (π : unitarySU 2 f K (m + 1) →* H) (κ : normOmega E m →* H)
    (hκ : Function.Injective κ)
    (hU1 : ∀ g, κ (uniEmb E h m g) = π (uniCast h m g))
    (hU2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      π (permSUHom h (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m))) * y *
        (π (permSUHom h (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m))))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ) :
    ∃ Ψ : normOmega E (m + 1) →* H, Function.Injective Ψ ∧
      (∀ a, Ψ (normOmegaCast E (Nat.le_succ m) a) = κ a) ∧
      (∀ g, Ψ (uniEmb E h (m + 1) g) = π g) ∧
      Ψ.range = κ.range ⊔ π.range := by
  obtain ⟨Ψ, hΨinj, hΨcast, hΨperm, hΨrange⟩ :=
    exists_normOmega_hom_of_perm E hm (π.comp (permSUHom h)) κ hκ
      (comp_viaEmbeddingHom_of_unitary E h (by omega) π κ hU1) hU2
  have hn3 : 3 ≤ m + 1 := by omega
  have hpi : Ψ.comp (uniEmb E h (m + 1)) = π := by
    refine eq_of_eqOn_uniCast_permSUHom h hm ?_ ?_
    · intro g
      simp only [MonoidHom.comp_apply]
      rw [uniEmb_uniCast E h m g, hΨcast, hU1]
    · intro σ
      simp only [MonoidHom.comp_apply]
      rw [← normPerm_eq_uniEmb E h hn3 σ]
      exact hΨperm σ
  exact ⟨Ψ, hΨinj, hΨcast, fun g => DFunLike.congr_fun hpi g,
    range_normOmega_hom_of_unitary E h π κ Ψ hΨcast hΨrange hpi⟩

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
