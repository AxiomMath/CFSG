module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntTodd
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntPlane
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExt

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit CFSG.Monster.B.Classical.Plane
  CFSG.EvenSmallLie.UnitarySix.MathieuExt CFSG.ComponentClassification.WittDesign
  CFSG.Sporadic.Schreier
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {t : G} {L E : Subgroup G}
  {p : L →* Equiv.Perm (Fin 693)}

section Labels

variable
    (H : ToddOrbit.Hyp t L E p)

theorem tvP_uβ_mem
    (i : Fin 21) : tvP (uβ i) ∈ conjClass uK j1 :=
  mem_conjClass_j1_iff.2 ⟨i, rfl⟩

@[expose] noncomputable def iota
    (i : Fin 21) : orb E t :=
  ⟨(H.existsUnique_mem_orb (tvP_uβ_mem i)).exists.choose,
    (H.existsUnique_mem_orb (tvP_uβ_mem i)).exists.choose_spec.1⟩

theorem pe_iota
    (i : Fin 21) : pe p (iota H i : G) = tvP (uβ i) :=
  (H.existsUnique_mem_orb (tvP_uβ_mem i)).exists.choose_spec.2

theorem iota_eq
    {i : Fin 21} {s : G} (hs : s ∈ orb E t) (hps : pe p s = tvP (uβ i)) :
    (iota H i : G) = s :=
  (H.existsUnique_mem_orb (tvP_uβ_mem i)).unique ⟨(iota H i).2, pe_iota H i⟩ ⟨hs, hps⟩

theorem iota_injective
    : Function.Injective (iota H) := fun i j h => by
  have := pe_iota H i
  rw [h, pe_iota] at this
  exact tvP_uβ_injective this.symm

theorem iota_ne
    (i : Fin 21) : iota H i ≠ tPt E t := fun h => by
  have h1 := pe_iota H i
  rw [h, tPt, H.pe_t] at h1
  exact tvP_ne_one _ h1.symm

theorem exists_iota
    {s : orb E t} (hs : s ≠ tPt E t) : ∃ i, iota H i = s := by
  have hst : (s : G) ≠ t := fun h => hs (Subtype.ext h)
  obtain ⟨i, hi⟩ := mem_conjClass_j1_iff.1 (H.mem_conjClass_j1_of_mem_orb s.2 hst)
  exact ⟨i, Subtype.ext (iota_eq H s.2 hi.symm)⟩

end Labels

omit [Finite G] in
theorem tvP_uβ_mem_uA
    (i : Fin 21) : tvP (uβ i) ∈ uA := by
  obtain ⟨c, hc, e⟩ := tvP_uβ_mem i
  rw [e]
  exact (mem_normalizer_iff.1 (uK_le_normalizer hc) j1).1 j1_mem

section Conj

variable
    (H : ToddOrbit.Hyp t L E p)
include H

theorem conj_iota
    {ℓ : G} (hℓL : ℓ ∈ L) (hℓN : ℓ ∈ normalizer (E : Set G))
    {a : Equiv.Perm (Fin 693)} (ha : a ∈ uA) (k : uK) (hp : pe p ℓ = a * k) (i : Fin 21) :
    ℓ * (iota H i : G) * ℓ⁻¹ = iota H (kappa k i) := by
  symm
  refine iota_eq H ((conj_mem_orb_iff' hℓN).2 (iota H i).2) ?_
  rw [pe_conj p hℓL (H.orb_subset_L (iota H i).2), hp, pe_iota]
  have h1 := conj_tvP (uK_le_T46 k.2) (uβ i)
  rw [← uβ_kappa] at h1
  have h2 := uA_comm a ha _ (tvP_uβ_mem_uA (kappa k i))
  calc a * k * tvP (uβ i) * (a * k)⁻¹ = a * (k * tvP (uβ i) * (k : Equiv.Perm (Fin 693))⁻¹) *
        a⁻¹ := by group
    _ = tvP (uβ (kappa k i)) := by rw [h1, h2, mul_inv_cancel_right]

omit [Finite G] in
theorem pe_mem_normalizer
    {ℓ : G} (hℓL : ℓ ∈ L) (hℓN : ℓ ∈ normalizer (E : Set G)) :
    pe p ℓ ∈ normalizer (uA : Set (Equiv.Perm (Fin 693))) := by
  have key : ∀ {ℓ : G}, ℓ ∈ L → ℓ ∈ normalizer (E : Set G) → ∀ x ∈ uA,
      pe p ℓ * x * (pe p ℓ)⁻¹ ∈ uA := by
    intro ℓ hℓL hℓN x hx
    obtain ⟨e, heL, rfl⟩ := H.exists_lift (uA_le_T46 hx)
    have heE : e ∈ E := H.mem_E_iff.2 ⟨heL, hx⟩
    have h := (mem_normalizer_iff.1 hℓN e).1 heE
    rw [← pe_conj p hℓL heL]
    exact (H.mem_E_iff.1 h).2
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key hℓL hℓN x, fun hx => ?_⟩
  have h := key (L.inv_mem hℓL) (inv_mem hℓN) _ hx
  rwa [pe_inv p hℓL, inv_inv, show (pe p ℓ)⁻¹ * (pe p ℓ * x * (pe p ℓ)⁻¹) * pe p ℓ = x by
    group] at h

omit [Finite G] in
theorem exists_decomp
    {ℓ : G} (hℓL : ℓ ∈ L) (hℓN : ℓ ∈ normalizer (E : Set G)) :
    ∃ a ∈ uA, ∃ k : uK, pe p ℓ = a * k := by
  have hP : pe p ℓ ∈ uP := by
    rw [← normalizer_uA]
    exact ⟨H.pe_mem_T46 ℓ, pe_mem_normalizer H hℓL hℓN⟩
  rw [uP_eq] at hP
  have hP' : pe p ℓ ∈ ((uA ⊔ uK : Subgroup (Equiv.Perm (Fin 693))) : Set _) := hP
  rw [coe_mul_of_right_le_normalizer_left uA uK uK_le_normalizer] at hP'
  obtain ⟨a, ha, k, hk, e⟩ := hP'
  exact ⟨a, ha, ⟨k, hk⟩, e.symm⟩

theorem exists_kappa
    {ℓ : G} (hℓL : ℓ ∈ L) (hℓN : ℓ ∈ normalizer (E : Set G)) :
    ∃ k : uK, ∀ i, ℓ * (iota H i : G) * ℓ⁻¹ = iota H (kappa k i) := by
  obtain ⟨a, ha, k, hk⟩ := exists_decomp H hℓL hℓN
  exact ⟨k, conj_iota H hℓL hℓN ha k hk⟩

end Conj

section Extension

variable
    (H : ToddOrbit.Hyp t L E p)
include H

theorem exists_perm
    (π : Equiv.Perm (orb E t)) (hπ : π (tPt E t) = tPt E t) :
    ∃ σ : Equiv.Perm (Fin 21), ∀ i, π (iota H i) = iota H (σ i) := by
  have h : ∀ i, ∃ j, iota H j = π (iota H i) := fun i =>
    exists_iota H fun e => iota_ne H i (π.injective (e.trans hπ.symm))
  choose g hg using h
  have hinj : Function.Injective g := fun i i' e => by
    have := (hg i).symm.trans ((congrArg (iota H) e).trans (hg i'))
    exact iota_injective H (π.injective this)
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hinj), fun i => (hg i).symm⟩

theorem perm_normalizes
    (D : DavisSolomonFacts G t L E) {m : normalizer (E : Set G)}
    (hm : (m : G) ∈ centralizer ({t} : Set G)) {σ : Equiv.Perm (Fin 21)}
    (hσ : ∀ i, actHom m (iota H i) = iota H (σ i)) :
    ∀ τ ∈ pslPerm.range, σ * τ * σ⁻¹ ∈ pslPerm.range := by
  intro τ hτ
  rw [← range_kappa] at hτ ⊢
  obtain ⟨k, rfl⟩ := hτ
  obtain ⟨ℓ, hℓL, hℓ⟩ := H.exists_lift (uK_le_T46 k.2)
  have hℓN := H.lift_mem_normalizer k.2 hℓL hℓ
  have hmL : (m : G) * ℓ * (m : G)⁻¹ ∈ L := (mem_normalizer_iff.1 (D.centralizer_le hm) ℓ).1 hℓL
  have hmN : (m : G) * ℓ * (m : G)⁻¹ ∈ normalizer (E : Set G) :=
    mul_mem (mul_mem m.2 hℓN) (inv_mem m.2)
  obtain ⟨k', hk'⟩ := exists_kappa H hmL hmN
  have hℓι : ∀ i, ℓ * (iota H i : G) * ℓ⁻¹ = iota H (kappa k i) :=
    conj_iota H hℓL hℓN (one_mem _) k (by rw [hℓ, one_mul])
  have hmι : ∀ i, (m : G) * (iota H i : G) * (m : G)⁻¹ = iota H (σ i) := fun i =>
    congrArg Subtype.val (hσ i)
  refine ⟨k', Equiv.ext fun i => ?_⟩
  obtain ⟨j, rfl⟩ := σ.surjective i
  change kappa k' (σ j) = σ (kappa k (σ⁻¹ (σ j)))
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  apply iota_injective H
  apply Subtype.ext
  rw [← hk', ← hmι, ← hmι, ← hℓι]
  group

theorem exists_psl
    (g : PSL(3, F4)) :
    ∃ ℓ ∈ L, ℓ ∈ normalizer (E : Set G) ∧
      ∀ i, ℓ * (iota H i : G) * ℓ⁻¹ = iota H (pslPerm g i) := by
  obtain ⟨k, hk⟩ : pslPerm g ∈ kappa.range := range_kappa ▸ ⟨g, rfl⟩
  obtain ⟨ℓ, hℓL, hℓ⟩ := H.exists_lift (uK_le_T46 k.2)
  refine ⟨ℓ, hℓL, H.lift_mem_normalizer k.2 hℓL hℓ, fun i => ?_⟩
  rw [conj_iota H hℓL (H.lift_mem_normalizer k.2 hℓL hℓ) (one_mem _) k (by rw [hℓ, one_mul]), hk]

end Extension

section Dichotomy

omit [Finite G] in
theorem faithful_actRange : FaithfulSMul (actRange E t) (orb E t) :=
  ⟨fun h => Subtype.ext (Equiv.ext h)⟩

omit [Finite G] in
theorem range_permHom [Fintype (orb E t)] [DecidableEq (orb E t)] (f : orb E t ≃ Fin 22) :
    (permHom (N := actRange E t) f).range = (rhoF f).range := by
  ext x
  constructor
  · rintro ⟨⟨_, m, rfl⟩, rfl⟩
    exact ⟨m, Equiv.ext fun _ => rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨⟨actHom m, m, rfl⟩, Equiv.ext fun _ => rfl⟩

omit [Finite G] in
theorem map_subtype_stabilizer :
    (MulAction.stabilizer (actRange E t) (tPt E t)).map (actRange E t).subtype =
      ((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map actHom := by
  ext x
  constructor
  · rintro ⟨⟨_, m, rfl⟩, hr, rfl⟩
    exact ⟨m, mem_subgroupOf.2 ((actHom_smul_t_iff m).1 hr), rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨actHom m, m, rfl⟩, (actHom_smul_t_iff m).2 (mem_subgroupOf.1 hm), rfl⟩

omit [Finite G] in
@[expose] noncomputable def stabEquiv (f : orb E t ≃ Fin 22) :
    ((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map (rhoF f) ≃*
      MulAction.stabilizer (actRange E t) (tPt E t) :=
  have h : ((((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map
      actHom).map (Equiv.permCongrHom f).toMonoidHom) =
      ((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map (rhoF f) := by
    rw [Subgroup.map_map]
    rfl
  (MulEquiv.subgroupCongr h).symm.trans <|
    (Subgroup.equivMapOfInjective _ _ (Equiv.permCongrHom f).injective).symm.trans <|
      (MulEquiv.subgroupCongr map_subtype_stabilizer.symm).trans
        (Subgroup.equivMapOfInjective _ _ (actRange E t).subtype_injective).symm

theorem Hyp.mathieu_dichotomy
    (H : Hyp t L E p) :
    ∃ f : orb E t ≃ Fin 22,
      ((rhoF f).range = M22 ∧
        Nat.card (((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map
          (rhoF f)) = 20160 ∧
        Nonempty ((((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map
          (rhoF f)) ≃* PSL(3, F4))) ∨
      (rhoF f).range = hexadAut := by
  classical
  have : Fintype (orb E t) := Fintype.ofFinite _
  have := faithful_actRange (E := E) (t := t)
  have := actRange_pretransitive (E := E) (t := t)
  have hΩ : Fintype.card (orb E t) = 22 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, H.todd.ncard_orb]
  have hnorm : ∀ n : actRange E t, n • tPt E t = tPt E t → ∃ σ : Equiv.Perm (Fin 21),
      (∀ q, n • iota H.todd q = iota H.todd (σ q)) ∧
        ∀ τ ∈ pslPerm.range, σ * τ * σ⁻¹ ∈ pslPerm.range := by
    rintro ⟨_, m, rfl⟩ hn
    have hn' : actHom m (tPt E t) = tPt E t := hn
    obtain ⟨σ, hσ⟩ := exists_perm H.todd (actHom m) hn'
    exact ⟨σ, hσ, perm_normalizes H.todd H.ds ((actHom_smul_t_iff m).1 hn') hσ⟩
  have hlow : ∀ g : PSL(3, F4), ∃ n : actRange E t, n • tPt E t = tPt E t ∧
      ∀ q, n • iota H.todd q = iota H.todd (pslPerm g q) := by
    intro g
    obtain ⟨ℓ, hℓL, hℓN, hℓ⟩ := exists_psl H.todd g
    exact ⟨⟨actHom ⟨ℓ, hℓN⟩, ⟨ℓ, hℓN⟩, rfl⟩,
      (actHom_smul_t_iff _).2 (H.todd.le_centralizer hℓL), fun q => Subtype.ext (hℓ q)⟩
  obtain ⟨f, -, hcase⟩ := davis_solomon_transitive_extension_of_normalizes hΩ (tPt E t)
    (iota H.todd) (iota_injective H.todd) (iota_ne H.todd) hnorm hlow
  refine ⟨f, ?_⟩
  rcases hcase with ⟨h1, h2, -, φ, -⟩ | ⟨-, h2, -⟩
  · exact Or.inl ⟨(range_permHom f) ▸ h2, by rw [Nat.card_congr (stabEquiv f).toEquiv, h1],
      ⟨(stabEquiv f).trans φ⟩⟩
  · exact Or.inr ((range_permHom f) ▸ h2)

end Dichotomy

end CFSG.EvenSmallLie.UnitarySix.Hunt
