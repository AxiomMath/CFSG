module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
public import CFSG.Permutation.BraidCentralizer

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.SeitzReduction.UnitaryPilot CFSG.Permutation.ProperSupportMaps

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

@[expose] noncomputable def deletionChart {H : Type} [Group H] (m : ℕ)
    (κ : normOmega E m →* H) : normBlock E (m + 1) (deletionSet (Fin.last m)) →* H :=
  κ.comp ((MulEquiv.subgroupCongr (range_normOmegaCast_succ E m).symm).trans
    (MonoidHom.ofInjective (normOmegaCast_injective E (Nat.le_succ m))).symm).toMonoidHom

theorem deletionChart_apply {H : Type} [Group H] (m : ℕ) (κ : normOmega E m →* H)
    (a : normOmega E m)
    (ha : normOmegaCast E (Nat.le_succ m) a ∈ normBlock E (m + 1) (deletionSet (Fin.last m))) :
    deletionChart E m κ ⟨normOmegaCast E (Nat.le_succ m) a, ha⟩ = κ a := by
  rw [deletionChart, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  congr 1
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

private theorem deletionChart_apply_mem {H : Type} [Group H] {m : ℕ} (κ : normOmega E m →* H)
    (x : normBlock E (m + 1) (deletionSet (Fin.last m))) {z : normOmega E m}
    (hx : (x : normOmega E (m + 1)) = normOmegaCast E (Nat.le_succ m) z) :
    deletionChart E m κ x = κ z := by
  have hmem : normOmegaCast E (Nat.le_succ m) z ∈
      normBlock E (m + 1) (deletionSet (Fin.last m)) := by
    rw [← hx]
    exact x.2
  have hx' : x = ⟨normOmegaCast E (Nat.le_succ m) z, hmem⟩ := Subtype.ext hx
  rw [hx']
  exact deletionChart_apply E m κ z hmem

private theorem inv_castSucc_of_eq_castSucc {m : ℕ} {σ' : Equiv.Perm (Fin m)}
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i))
    (i : Fin m) : σ⁻¹ (Fin.castSucc i) = Fin.castSucc (σ'⁻¹ i) := by
  show σ.symm (Fin.castSucc i) = Fin.castSucc (σ'.symm i)
  rw [Equiv.symm_apply_eq, hσ (σ'.symm i), Equiv.apply_symm_apply]

private theorem last_of_eq_castSucc {m : ℕ} {σ' : Equiv.Perm (Fin m)}
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i)) :
    σ (Fin.last m) = Fin.last m := by
  obtain ⟨x, hx⟩ := σ.surjective (Fin.last m)
  rcases Fin.eq_castSucc_or_eq_last x with ⟨i, rfl⟩ | rfl
  · rw [hσ i] at hx
    exact absurd hx (Fin.castSucc_ne_last (σ' i))
  · exact hx

theorem normPerm_eq_normOmegaCast_normPerm {m : ℕ} (hm : 3 ≤ m) (σ' : Equiv.Perm (Fin m))
    (σ : Equiv.Perm (Fin (m + 1))) (hσ : ∀ i, σ (Fin.castSucc i) = Fin.castSucc (σ' i)) :
    normPerm E (by omega : 3 ≤ m + 1) σ =
      normOmegaCast E (Nat.le_succ m) (normPerm E hm σ') := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hlin : ∀ w : (F × F) × (Fin m → K),
      (((normPerm E hm σ' : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))).toLinearMap) w =
        (w.1, fun j => w.2 (σ'⁻¹ j)) :=
    fun w => normPerm_apply E hm σ' w
  rw [normPerm_apply, normOmegaCast_apply, castEquiv_apply, castLin_apply, hlin]
  refine Prod.ext rfl (funext fun j => ?_)
  dsimp only
  have hinv_last : σ⁻¹ (Fin.last m) = Fin.last m := by
    show σ.symm (Fin.last m) = Fin.last m
    simpa using (congrArg σ.symm (last_of_eq_castSucc hσ)).symm
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [inv_castSucc_of_eq_castSucc hσ i,
      dif_pos (show (↑i.castSucc : ℕ) < m from i.2)]
    change v.2 (Fin.castSucc (σ'⁻¹ i)) =
      v.2 (Fin.castLE (Nat.le_succ m) (σ'⁻¹ ⟨(↑i.castSucc : ℕ), i.2⟩))
    exact congrArg (fun k : Fin (m + 1) => v.2 k) (Fin.ext rfl)
  · rw [hinv_last, dif_neg (by simp [Fin.val_last])]

theorem deletionChart_common {m : ℕ} (hm : 3 ≤ m) {H : Type} [Group H]
    (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E hm)) :
    ∀ σ : Equiv.Perm (Fin (m + 1)), σ (Fin.last m) = Fin.last m →
      ∃ hmem : (normPerm E (by omega : 3 ≤ m + 1) σ : normOmega E (m + 1)) ∈
          normBlock E (m + 1) (deletionSet (Fin.last m)),
        deletionChart E m κ ⟨normPerm E (by omega : 3 ≤ m + 1) σ, hmem⟩ = t σ := by
  intro σ hσ
  obtain ⟨σ', hσ'⟩ := exists_perm_castSucc σ hσ
  have hcast : normPerm E (by omega : 3 ≤ m + 1) σ =
      normOmegaCast E (Nat.le_succ m) (normPerm E hm σ') :=
    normPerm_eq_normOmegaCast_normPerm E hm σ' σ hσ'
  have hmem : (normPerm E (by omega : 3 ≤ m + 1) σ : normOmega E (m + 1)) ∈
      normBlock E (m + 1) (deletionSet (Fin.last m)) := by
    rw [← range_normOmegaCast_succ E m, hcast]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  refine ⟨hmem, ?_⟩
  have hvia : σ = Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb σ' := by
    have hlast : (Equiv.Perm.viaEmbedding σ'
        (Fin.castSuccEmb : Fin m ↪ Fin (m + 1))) (Fin.last m) = Fin.last m := by
      apply Equiv.Perm.viaEmbedding_apply_of_notMem
      rintro ⟨i, hi⟩
      rw [Fin.castSuccEmb_apply] at hi
      exact Fin.castSucc_ne_last i hi
    refine Equiv.ext fun j => ?_
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [hσ' i, Equiv.Perm.viaEmbeddingHom_apply]
      change (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) (σ' i) =
        (Equiv.Perm.viaEmbedding σ' (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)))
          ((Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i)
      exact (Equiv.Perm.viaEmbedding_apply σ' _ i).symm
    · rw [hσ, Equiv.Perm.viaEmbeddingHom_apply]
      exact hlast.symm
  rw [deletionChart_apply_mem E κ ⟨normPerm E (by omega : 3 ≤ m + 1) σ, hmem⟩ hcast, hvia]
  exact (DFunLike.congr_fun hT1 σ').symm

private theorem normBlock_pair_of_mem_anchorBlock {m : ℕ} (hm : 2 ≤ m) {y : normOmega E m}
    (hy : y ∈ anchorBlock E hm) :
    normOmegaCast E (Nat.le_succ m) y ∈
      normBlock E (m + 1) {⟨0, by omega⟩, ⟨1, by omega⟩} := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hy
  rw [← anchorBlock_eq_normBlock (E := E) (m := m + 1) (by omega), ← hw,
    ← MonoidHom.comp_apply, normOmegaCast_comp]
  exact MonoidHom.mem_range.mpr ⟨w, rfl⟩

private theorem exists_anchorBlock_of_mem_normBlock_pair {m : ℕ} (hm : 2 ≤ m)
    {x : normOmega E (m + 1)}
    (hx : x ∈ normBlock E (m + 1) {⟨0, by omega⟩, ⟨1, by omega⟩}) :
    ∃ z ∈ anchorBlock E hm, x = normOmegaCast E (Nat.le_succ m) z := by
  rw [← anchorBlock_eq_normBlock (E := E) (m := m + 1) (by omega)] at hx
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hx
  refine ⟨normOmegaCast E hm w, MonoidHom.mem_range.mpr ⟨w, rfl⟩, ?_⟩
  rw [← hw, ← MonoidHom.comp_apply, normOmegaCast_comp]

private theorem deletionChart_pair_ne {m : ℕ} (hm : 4 ≤ m) :
    (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ ∧
      (⟨m - 2, by omega⟩ : Fin (m + 1)) ≠ ⟨0, by omega⟩ ∧
      (⟨m - 2, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ ∧
      (Fin.last m : Fin (m + 1)) ≠ ⟨0, by omega⟩ ∧
      (Fin.last m : Fin (m + 1)) ≠ ⟨1, by omega⟩ ∧
      (⟨m - 2, by omega⟩ : Fin (m + 1)) ≠ Fin.last m ∧
      (⟨m - 2, by omega⟩ : Fin (m + 1)) ≠ ⟨m - 1, by omega⟩ ∧
      (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m ∧
      (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨m - 2, by omega⟩ ∧
      (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨m - 1, by omega⟩ ∧
      (⟨1, by omega⟩ : Fin (m + 1)) ≠ ⟨m - 2, by omega⟩ ∧
      (⟨1, by omega⟩ : Fin (m + 1)) ≠ ⟨m - 1, by omega⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk, Fin.val_last] at hv
    omega

private theorem normBlock_pair_normalizes_deletionChart {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ) :
    let Bpair : Subgroup (normOmega E (m + 1)) :=
      normBlock E (m + 1) {⟨0, by omega⟩, ⟨1, by omega⟩}
    let Bdel : Subgroup (normOmega E (m + 1)) :=
      normBlock E (m + 1) (deletionSet (Fin.last m))
    ∀ (hineq : Bpair ≤ Bdel) (x : Bpair),
      ∃ y : Bpair,
        t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) *
            deletionChart E m κ (Subgroup.inclusion hineq x) *
            (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ =
          deletionChart E m κ (Subgroup.inclusion hineq y) := by
  intro Bpair Bdel hineq x
  have hm2 : 2 ≤ m := by omega
  obtain ⟨z, hz, hxz⟩ := exists_anchorBlock_of_mem_normBlock_pair (E := E) hm2 x.2
  have hxval : deletionChart E m κ (Subgroup.inclusion hineq x) = κ z := by
    refine deletionChart_apply_mem E κ _ ?_
    rw [Subgroup.coe_inclusion]
    exact hxz
  obtain ⟨z', hz', hz'eq⟩ :=
    Subgroup.mem_map.mp (hT2 (κ z) (Subgroup.mem_map_of_mem κ hz))
  refine ⟨⟨normOmegaCast E (Nat.le_succ m) z',
    normBlock_pair_of_mem_anchorBlock E hm2 hz'⟩, ?_⟩
  have hyval : deletionChart E m κ (Subgroup.inclusion hineq
      ⟨normOmegaCast E (Nat.le_succ m) z',
        normBlock_pair_of_mem_anchorBlock E hm2 hz'⟩) = κ z' := by
    refine deletionChart_apply_mem E κ _ ?_
    rw [Subgroup.coe_inclusion]
  rw [hxval, hyval, hz'eq]

private theorem deletionChart_cross {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ) :
    let Bpair : Subgroup (normOmega E (m + 1)) :=
      normBlock E (m + 1) {⟨0, by omega⟩, ⟨1, by omega⟩}
    let Bdel : Subgroup (normOmega E (m + 1)) :=
      normBlock E (m + 1) (deletionSet (Fin.last m))
    ∀ (hineq : Bpair ≤ Bdel) (x : Bpair),
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) *
          deletionChart E m κ (Subgroup.inclusion hineq x) =
        deletionChart E m κ (Subgroup.inclusion hineq x) *
          t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) := by
  intro Bpair Bdel hineq x
  obtain ⟨huv, -, -, hdu, hdv, hcd, hce, hed, huc, hue, hvc, hve⟩ :=
    deletionChart_pair_ne (m := m) hm
  have hn : 3 ≤ m + 1 := by omega
  have hbase : ∀ (τ : Equiv.Perm (Fin (m + 1))) (y : Bpair),
      τ ⟨0, by omega⟩ = ⟨0, by omega⟩ → τ ⟨1, by omega⟩ = ⟨1, by omega⟩ →
      normPerm E hn τ * (y : normOmega E (m + 1)) =
        (y : normOmega E (m + 1)) * normPerm E hn τ :=
    fun τ y h0 h1 => normPerm_commute_normBlock_pair E hn huv τ y h0 h1
  exact cross_of_normalizes (d := Fin.last m) (u := ⟨0, by omega⟩)
    (v := ⟨1, by omega⟩) (c := ⟨m - 2, by omega⟩) (e := ⟨m - 1, by omega⟩)
    (B := normBlock E (m + 1)) (hB := normBlock_mono E (m + 1))
    (ρ := normPerm E hn) (t := t) (a := deletionChart E m κ)
    hdu hdv hcd hce hed huc hue hvc hve
    (deletionChart_common E (by omega) t κ hT1) hbase
    (normBlock_pair_normalizes_deletionChart E hm t κ hT2 hineq) x

theorem deletionChart_pairCovariance {m : ℕ} (hm : 4 ≤ m)
    {H : Type} [Group H] (t : Equiv.Perm (Fin (m + 1)) →* H) (κ : normOmega E m →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) =
      κ.comp (normPerm E (by omega : 3 ≤ m)))
    (hT2 : ∀ y ∈ (anchorBlock E (by omega : 2 ≤ m)).map κ,
      t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)) * y *
        (t (Equiv.swap ⟨m - 2, by omega⟩ (Fin.last m)))⁻¹ ∈
        (anchorBlock E (by omega : 2 ≤ m)).map κ) :
    ∀ (P : Finset (Fin (m + 1))) (σ : Equiv.Perm (Fin (m + 1))) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet (Fin.last m)) (hPσD : P.image σ ⊆ deletionSet (Fin.last m))
      (x : normBlock E (m + 1) P),
        deletionChart E m κ (Subgroup.inclusion (normBlock_mono E (m + 1) hPσD)
            (conjMapHom (map_normBlock_normPerm E (by omega : 3 ≤ m + 1)) σ P x)) =
          t σ * deletionChart E m κ (Subgroup.inclusion (normBlock_mono E (m + 1) hPD) x) *
            (t σ)⁻¹ := by
  intro P σ hPcard hPD hPσD x
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨huv, hcu, hcv, hdu, hdv, hcd, -, -, -, -, -, -⟩ :=
    deletionChart_pair_ne (m := m) hm
  let Bpair : Subgroup (normOmega E (m + 1)) :=
    normBlock E (m + 1) {⟨0, by omega⟩, ⟨1, by omega⟩}
  let Bdel : Subgroup (normOmega E (m + 1)) :=
    normBlock E (m + 1) (deletionSet (Fin.last m))
  have hineq : Bpair ≤ Bdel :=
    normBlock_mono E (m + 1) (pair_subset_deletionSet hdu.symm hdv.symm)
  have hbase : ∀ (τ : Equiv.Perm (Fin (m + 1))) (y : Bpair),
      τ ⟨0, by omega⟩ = ⟨0, by omega⟩ → τ ⟨1, by omega⟩ = ⟨1, by omega⟩ →
      normPerm E hn τ * (y : normOmega E (m + 1)) =
        (y : normOmega E (m + 1)) * normPerm E hn τ :=
    fun τ y h0 h1 => normPerm_commute_normBlock_pair E hn huv τ y h0 h1
  exact pairCovariance_of_cross (d := Fin.last m) (u := ⟨0, by omega⟩)
    (v := ⟨1, by omega⟩) (c := ⟨m - 2, by omega⟩)
    (B := normBlock E (m + 1)) (hB := normBlock_mono E (m + 1))
    (ρ := normPerm E hn) (t := t) (a := deletionChart E m κ)
    (hBmap := map_normBlock_normPerm E hn) huv hcu hcv hdu hdv hcd
    (deletionChart_common E (by omega) t κ hT1) hbase
    (deletionChart_cross E hm t κ hT1 hT2 hineq)
    P σ hPcard hPD hPσD x

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
