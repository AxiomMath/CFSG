module

public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Steinberg.BruhatWeyl
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section Blocks

variable {V : Type*} [DecidableEq V] (ρ : V → V)

@[expose] def triBlock (m : V) : List V := if ρ m = m then [m] else [m, ρ m, ρ (ρ m)]

variable {ρ}

theorem mem_triBlock {m x : V} : x ∈ triBlock ρ m ↔ x = m ∨ x = ρ m ∨ x = ρ (ρ m) := by
  unfold triBlock
  split_ifs with h
  · simp only [List.mem_singleton]
    exact ⟨Or.inl, fun h' => by rcases h' with h' | h' | h' <;> rw [h'] <;> simp [h]⟩
  · simp

variable (hρ : ∀ v, ρ (ρ (ρ v)) = v)
include hρ

omit [DecidableEq V] in
theorem orbit_symm {a b : V} (h : b = a ∨ b = ρ a ∨ b = ρ (ρ a)) :
    a = b ∨ a = ρ b ∨ a = ρ (ρ b) := by
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (hρ a).symm)
  · exact Or.inr (Or.inl (hρ a).symm)

omit [DecidableEq V] in
theorem orbit_trans {a b c : V} (h1 : b = a ∨ b = ρ a ∨ b = ρ (ρ a))
    (h2 : c = b ∨ c = ρ b ∨ c = ρ (ρ b)) : c = a ∨ c = ρ a ∨ c = ρ (ρ a) := by
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;> simp [hρ]

theorem nodup_triBlock (m : V) : (triBlock ρ m).Nodup := by
  unfold triBlock
  split_ifs with h
  · exact List.nodup_singleton m
  · have h1 : ρ (ρ m) ≠ m := fun h' => h (by
      have := congrArg ρ h'
      rw [hρ] at this
      exact this.symm)
    have h2 : ρ (ρ m) ≠ ρ m := fun h' => h (by
      have := congrArg ρ h'
      rw [hρ, h'] at this
      exact this.symm)
    simp [Ne.symm h, Ne.symm h1, Ne.symm h2]

theorem prod_map_triBlock_comp {M : Type*} [Monoid M] (F : V → M) {m : V}
    (h : ρ m ≠ m → Commute (F (ρ (ρ m))) (F m) ∧ Commute (F (ρ (ρ m))) (F (ρ m))) :
    ((triBlock ρ m).map (F ∘ ρ ∘ ρ)).prod = ((triBlock ρ m).map F).prod := by
  unfold triBlock
  split_ifs with h'
  · simp [h']
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Function.comp_apply, hρ]
    obtain ⟨h1, h2⟩ := h h'
    rw [← mul_assoc, h1.eq, mul_assoc, h2.eq]

omit [DecidableEq V] in
theorem exists_orbit_rep {β : Type*} [LinearOrder β] (ord : V → β) (v : V) :
    ∃ m, (v = m ∨ v = ρ m ∨ v = ρ (ρ m)) ∧ ord m ≤ ord (ρ m) ∧ ord m ≤ ord (ρ (ρ m)) := by
  by_cases h1 : ord v ≤ ord (ρ v) ∧ ord v ≤ ord (ρ (ρ v))
  · exact ⟨v, Or.inl rfl, h1⟩
  by_cases h2 : ord (ρ v) ≤ ord (ρ (ρ v)) ∧ ord (ρ v) ≤ ord v
  · exact ⟨ρ v, Or.inr (Or.inr (hρ v).symm), h2.1, by rw [hρ]; exact h2.2⟩
  refine ⟨ρ (ρ v), Or.inr (Or.inl (hρ v).symm), ?_, ?_⟩ <;> rw [hρ]
  · rcases le_total (ord v) (ord (ρ v)) with ha | ha
    · exact le_of_lt (lt_of_not_ge fun hc => h1 ⟨ha, hc⟩)
    · rcases le_total (ord (ρ v)) (ord (ρ (ρ v))) with hb | hb
      · exact absurd ⟨hb, ha⟩ h2
      · exact hb.trans ha
  · rcases le_total (ord v) (ord (ρ v)) with ha | ha
    · exact (le_of_lt (lt_of_not_ge fun hc => h1 ⟨ha, hc⟩)).trans ha
    · rcases le_total (ord (ρ v)) (ord (ρ (ρ v))) with hb | hb
      · exact absurd ⟨hb, ha⟩ h2
      · exact hb

theorem exists_list_flatMap_triBlock {β : Type*} [LinearOrder β] {ord : V → β}
    (hord : Function.Injective ord) (key : V → ℤ) (hkey : ∀ v, key (ρ v) = key v) {S : Set V}
    (hS : S.Finite) (hSρ : ∀ v ∈ S, ρ v ∈ S) :
    ∃ M : List V, (∀ m ∈ M, m ∈ S) ∧ (∀ v, v ∈ M.flatMap (triBlock ρ) ↔ v ∈ S) ∧
      (M.flatMap (triBlock ρ)).Nodup ∧
        (M.flatMap (triBlock ρ)).Pairwise (fun a b => key a ≤ key b) := by
  set R : Set V := {v | v ∈ S ∧ ord v ≤ ord (ρ v) ∧ ord v ≤ ord (ρ (ρ v))}
  have hRS : ∀ v ∈ R, v ∈ S := fun v hv => hv.1
  have hR : ∀ m ∈ R, ∀ m' ∈ R, (m' = m ∨ m' = ρ m ∨ m' = ρ (ρ m)) → m' = m := by
    rintro m ⟨-, hm1, hm2⟩ m' ⟨-, hm'1, hm'2⟩ (rfl | rfl | rfl)
    · rfl
    · rw [hρ] at hm'2
      exact hord (le_antisymm hm'2 hm1)
    · rw [hρ] at hm'1
      exact hord (le_antisymm hm'1 hm2)
  have hkey2 : ∀ v, key (ρ (ρ v)) = key v := fun v => by rw [hkey, hkey]
  have hSorb : ∀ v ∈ S, ∀ w, (w = v ∨ w = ρ v ∨ w = ρ (ρ v)) → w ∈ S := by
    rintro v hv w (rfl | rfl | rfl)
    exacts [hv, hSρ _ hv, hSρ _ (hSρ _ hv)]
  obtain ⟨M, hnd, hmem, hsort⟩ := exists_nodup_sorted (hS.subset hRS) key
  refine ⟨M, fun m hm => ((hmem m).1 hm).1, fun v => ?_, ?_, ?_⟩
  · rw [List.mem_flatMap]
    constructor
    · rintro ⟨m, hm, hv⟩
      exact hSorb m ((hmem m).1 hm).1 v (mem_triBlock.1 hv)
    · intro hv
      obtain ⟨m, hvm, hm1, hm2⟩ := exists_orbit_rep hρ ord v
      have hmS : m ∈ S := hSorb v hv m (orbit_symm hρ hvm)
      exact ⟨m, (hmem m).2 ⟨hmS, hm1, hm2⟩, mem_triBlock.2 hvm⟩
  · refine List.nodup_flatMap.2 ⟨fun m _ => nodup_triBlock hρ m, ?_⟩
    refine hnd.imp_of_mem fun {m m'} hm hm' hne => ?_
    refine List.disjoint_left.2 fun {x} hx hx' => hne ?_
    exact (hR m ((hmem m).1 hm) m' ((hmem m').1 hm')
      (orbit_trans hρ (mem_triBlock.1 hx) (orbit_symm hρ (mem_triBlock.1 hx')))).symm
  · refine List.pairwise_flatMap.2 ⟨fun m _ => ?_, hsort.imp fun {m m'} h x hx y hy => ?_⟩
    · unfold triBlock
      split_ifs
      · exact List.pairwise_singleton _ _
      · simp [hkey]
    · rcases mem_triBlock.1 hx with rfl | rfl | rfl <;>
        rcases mem_triBlock.1 hy with rfl | rfl | rfl <;> simpa [hkey, hkey2] using h

end Blocks

section Ambient

variable {K : Type} [Field K]

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

theorem iform_self_eq_two
    {ε : Fin d4.rank → ℤ} (hε : IsRoot d4 ε) : iform ε ε = 2 := by
  obtain ⟨k, hk⟩ := iform_self_of_isRoot hε
  rw [hk, symmetrizer_d4, mul_one]

theorem eq_add_of_mem_openCone
    {γ δ ε : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (hδ : IsRoot d4 δ)
    (hne : γ ≠ δ) (hne' : γ ≠ -δ)
    (hε : ε ∈ openCone (adjDatum (rootOperatorFamily d4) K).roots γ δ) : ε = γ + δ := by
  obtain ⟨hεr, m, n, hm, hn, rfl⟩ := hε
  rw [mem_adjDatum_roots] at hεr
  rcases exponent_pair_cases noG2_D4 hγ hδ hne hne' hm hn hεr with ⟨rfl, rfl⟩ | ⟨-, -, h4, -⟩ |
    ⟨-, -, -, h4, -⟩
  · simp
  · rw [iform_self_eq_two hγ] at h4
    omega
  · rw [iform_self_eq_two hδ] at h4
    omega

theorem commutatorElement_mem_rootGroup_add
    {γ δ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ)
    (hδ : IsRoot d4 δ) (hne : γ + δ ≠ 0) {x y : adjointGroup d4 K} (hx : x ∈ 𝕏 γ)
    (hy : y ∈ 𝕏 δ) : ⁅x, y⁆ ∈ 𝕏 (γ + δ) := by
  by_cases hγδ : γ = δ
  · subst hγδ
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
    obtain ⟨d, rfl⟩ := (mem_rootGroup_iff hγ y).1 hy
    have h1 : ⁅xPar (rootOperatorFamily d4) γ c, xPar (rootOperatorFamily d4) γ d⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      change _ * _ = _ * _
      rw [← xPar_add, ← xPar_add, add_comm]
    rw [h1]
    exact one_mem _
  · have hne' : γ ≠ -δ := fun h => hne (by rw [h, neg_add_cancel])
    have hlin : LinIndepPair γ δ := by
      by_contra h
      rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hγ hδ h with h' | h'
      exacts [hγδ h', hne' h']
    have key := commutator_mem_openCone_of_linIndepPair hγ hδ hlin hx hy
    refine (iSup₂_le fun ε hε => ?_ : (⨆ ε ∈ openCone (adjDatum (rootOperatorFamily d4) K).roots
      γ δ, (adjDatum (rootOperatorFamily d4) K).rootGroup ε) ≤ 𝕏 (γ + δ)) key
    rw [eq_add_of_mem_openCone hγ hδ hγδ hne' hε]

theorem commute_of_mem_rootGroup_rho_rho
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α)
    (hne : rho α ≠ α) {x y : adjointGroup d4 K} (hx : x ∈ 𝕏 α) (hy : y ∈ 𝕏 (rho (rho α))) :
    Commute x y := by
  have h2 := isRoot_rho (isRoot_rho hα)
  have hne2 : rho (rho (rho α)) ≠ rho (rho α) := by
    rw [rho_rho_rho]
    exact (rho_rho_ne hne).symm
  have hx' : x ∈ 𝕏 (rho (rho (rho α))) := by rwa [rho_rho_rho]
  exact (commute_of_mem_rootGroup_rho h2 hne2 hy hx').symm

end Ambient

section Lemma62

variable {K : Type} [Field K] (σ : K →+* K)

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

theorem iSup_rootGroup_inf_twistFixed_le
    {f : (Fin d4.rank → ℤ) →+ ℤ}
    (hf : ∀ v, f (rho v) = f v) {Ψ : Set (Fin d4.rank → ℤ)}
    (hΨ : ∀ α ∈ Ψ, IsRoot d4 α ∧ 0 < f α)
    (hclosed : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot d4 (α + β) → α + β ∈ Ψ)
    (hρ : ∀ α ∈ Ψ, rho α ∈ Ψ) :
    (⨆ α ∈ Ψ, 𝕏 α) ⊓ twistFixed .D4 K σ ≤ ⨆ β ∈ proj '' Ψ, twistedRootSubgroupD4 σ β := by
  intro u hu
  obtain ⟨huΨ, hufix⟩ := Subgroup.mem_inf.1 hu
  have hfix : twistC .D4 K σ u = u := hufix
  have hfin : Ψ.Finite := (finite_setOf_isRoot d4).subset fun α hα => (hΨ α hα).1
  obtain ⟨M, hMΨ, hmem, hnd, hsort⟩ := exists_list_flatMap_triBlock (ρ := rho) rho_rho_rho
    (ord := fun v => List.ofFn v) List.ofFn_injective (fun v => f v) hf hfin hρ
  set L := M.flatMap (triBlock rho) with hL
  have hroot : ∀ γ ∈ L, IsRoot d4 γ := fun γ hγ => (hΨ γ ((hmem γ).1 hγ)).1
  have hpos : ∀ γ ∈ L, 0 < f γ := fun γ hγ => (hΨ γ ((hmem γ).1 hγ)).2
  have hLρ : ∀ γ ∈ L, rho γ ∈ L := fun γ hγ => (hmem _).2 (hρ γ ((hmem γ).1 hγ))
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ 𝕏 a, ∀ y ∈ 𝕏 b,
      ⁅x, y⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (f a) (f b) < f c), 𝕏 c := by
    intro a ha b hb _ x hx y hy
    have hab : 0 < f (a + b) := by rw [map_add]; linarith [hpos a ha, hpos b hb]
    have hne : a + b ≠ 0 := fun h => by rw [h, map_zero] at hab; exact lt_irrefl _ hab
    have hxy := commutatorElement_mem_rootGroup_add (hroot a ha) (hroot b hb) hne hx hy
    by_cases hr : IsRoot d4 (a + b)
    · have hab' : a + b ∈ L := (hmem _).2 (hclosed a ((hmem a).1 ha) b ((hmem b).1 hb) hr)
      refine le_iSup₂_of_le (f := fun c (_ : c ∈ L) =>
        ⨆ (_ : min (f a) (f b) < f c), 𝕏 c) (a + b) hab' (le_iSup_of_le ?_ le_rfl) hxy
      rw [map_add]
      have := hpos a ha
      have := hpos b hb
      omega
    · rw [rootGroup_of_not_isRoot hr, Subgroup.mem_bot] at hxy
      rw [hxy]
      exact one_mem _
  have huL : u ∈ ⨆ v ∈ L, 𝕏 v := by
    have h : ⨆ α ∈ Ψ, 𝕏 α = ⨆ v ∈ L, 𝕏 v :=
      iSup_congr fun α => iSup_congr_Prop (hmem α).symm fun _ => rfl
    rwa [← h]
  obtain ⟨Fu, hF, rfl⟩ := exists_prod_eq_of_commutator_mem 𝕏 (fun γ => f γ) hnd hsort hcomm _ huL
  set F' : (Fin d4.rank → ℤ) → adjointGroup d4 K := fun γ => twistC .D4 K σ (Fu (rho (rho γ)))
  have hF' : ∀ γ ∈ L, F' γ ∈ 𝕏 γ := fun γ hγ => by
    have h := twistC_mem_rootGroup σ (isRoot_rho (isRoot_rho (hroot γ hγ)))
      (hF _ (hLρ _ (hLρ γ hγ)))
    rwa [rho_rho_rho] at h
  have hblock : ∀ m ∈ M, ((triBlock rho m).map (twistC .D4 K σ ∘ Fu)).prod =
      ((triBlock rho m).map F').prod := by
    intro m hm
    have hmL : m ∈ L := (hmem m).2 (hMΨ m hm)
    refine (prod_map_triBlock_comp rho_rho_rho (twistC .D4 K σ ∘ Fu) fun hne => ?_).symm
    have hm0 := twistC_mem_rootGroup σ (hroot m hmL) (hF m hmL)
    have hm1 := twistC_mem_rootGroup σ (hroot _ (hLρ m hmL)) (hF _ (hLρ m hmL))
    have hm2 := twistC_mem_rootGroup σ (hroot _ (hLρ _ (hLρ m hmL)))
      (hF _ (hLρ _ (hLρ m hmL)))
    rw [rho_rho_rho] at hm2
    exact ⟨commute_of_mem_rootGroup_rho (hroot m hmL) hne hm2 hm0,
      commute_of_mem_rootGroup_rho_rho (hroot m hmL) hne hm2 hm1⟩
  have hσu : twistC .D4 K σ (L.map Fu).prod = (L.map F').prod := by
    rw [map_list_prod, List.map_map, hL, prod_map_flatMap, prod_map_flatMap]
    exact congrArg List.prod (List.map_congr_left fun m hm => hblock m hm)
  have hinj := prodInjective (F := rootOperatorFamily d4) (K := K) f L hnd
    (fun γ hγ => ⟨hroot γ hγ, hpos γ hγ⟩) hsort
  have hFF' : ∀ γ ∈ L, Fu γ = F' γ := hinj Fu F' hF hF' (by rw [← hσu, hfix])
  have hP : ∀ m ∈ M, ((triBlock rho m).map Fu).prod ∈ twistedRootSubgroupD4 σ (proj m) := by
    intro m hm
    have hmL : m ∈ L := (hmem m).2 (hMΨ m hm)
    have hsub : ∀ γ ∈ triBlock rho m, γ ∈ L := fun γ hγ => by
      rcases mem_triBlock.1 hγ with rfl | rfl | rfl
      exacts [hmL, hLρ _ hmL, hLρ _ (hLρ _ hmL)]
    refine (mem_twistedRootSubgroupD4_iff σ (hroot m hmL) rfl _).2
      ⟨Subgroup.list_prod_mem _ fun x hx => ?_, ?_⟩
    · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
      rcases mem_triBlock.1 hγ with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hF _ hmL))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hF _ (hLρ _ hmL)))
      · exact Subgroup.mem_sup_right (hF _ (hLρ _ (hLρ _ hmL)))
    · rw [map_list_prod, List.map_map, hblock m hm]
      exact congrArg List.prod (List.map_congr_left fun γ hγ => (hFF' γ (hsub γ hγ)).symm)
  rw [hL, prod_map_flatMap]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
  exact le_iSup₂_of_le (f := fun β (_ : β ∈ proj '' Ψ) => twistedRootSubgroupD4 σ β) (proj m)
    ⟨m, hMΨ m hm, rfl⟩ le_rfl (hP m hm)

end Lemma62

section Commutator

variable {K : Type} [Field K] {σ : K →+* K}

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

private abbrev fibre (γ : Fin (Tag.rank .G2) → ℤ) : Set (Fin d4.rank → ℤ) :=
  {α | IsRoot d4 α ∧ ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • γ}

private theorem mem_iSup_fibre
    {γ : Fin (Tag.rank .G2) → ℤ} {x : adjointGroup d4 K}
    (hx : x ∈ twistedRootSubgroupD4 σ γ) : x ∈ ⨆ α, ⨆ (_ : α ∈ fibre γ), 𝕏 α := by
  have h : x ∈ ⨆ α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • γ), 𝕏 α :=
    (Subgroup.mem_inf.1 hx).1
  have hle : (⨆ α ∈ {α : Fin d4.rank → ℤ | IsRoot d4 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • γ), 𝕏 α) ≤
      ⨆ α, ⨆ (_ : α ∈ fibre γ), 𝕏 α :=
    iSup_le fun α => iSup_le fun hα => iSup_le fun hc =>
      le_iSup₂_of_le (f := fun α (_ : α ∈ fibre γ) => 𝕏 α) α ⟨hα, hc⟩ le_rfl
  exact hle h

theorem commutator_mem_iSup_twistedRootGroup
    {γ δ : Fin (Tag.rank .G2) → ℤ}
    (hlin : LinIndepPair γ δ) {x y : twistedGroup σ} (hx : x ∈ twistedRootGroup σ γ)
    (hy : y ∈ twistedRootGroup σ δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone {β | IsRoot .G2 β} γ δ, twistedRootGroup σ ε := by
  rw [iSup_twistedRootGroup_eq_subgroupOf σ fun β hβ => hβ.1, Subgroup.mem_subgroupOf]
  set Ψ : Set (Fin d4.rank → ℤ) :=
    {α | IsRoot d4 α ∧ proj α ∈ openCone {β | IsRoot .G2 β} γ δ} with hΨ
  set N := ⨆ α ∈ Ψ, 𝕏 α
  have hXN : ∀ α : Fin d4.rank → ℤ, (IsRoot d4 α → α ∈ Ψ) → 𝕏 α ≤ N := fun α h => by
    by_cases hr : IsRoot d4 α
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ Ψ) => 𝕏 α) α (h hr) le_rfl
    · rw [rootGroup_of_not_isRoot hr]
      exact bot_le
  have hcone : ∀ (a b : ℕ), 0 < a → 0 < b → ∀ α : Fin d4.rank → ℤ,
      proj α = a • γ + b • δ → IsRoot d4 α → α ∈ Ψ := fun a b ha hb α hα hr =>
    ⟨hr, isRoot_proj hr, a, b, ha, hb, hα⟩
  have hne : ∀ (a b : ℕ), 0 < b → ∀ α : Fin d4.rank → ℤ, proj α = a • γ + b • δ →
      α ≠ 0 := fun a b hb α hα h0 => by
    rw [h0, map_zero] at hα
    have := (hlin a b (by rw [natCast_zsmul, natCast_zsmul]; exact hα.symm)).2
    omega
  have hnorm : ∀ (η : Fin (Tag.rank .G2) → ℤ), (η = γ ∨ η = δ) → ∀ α ∈ fibre η,
      𝕏 α ≤ Subgroup.normalizer (N : Set _) := by
    rintro η hη α ⟨hα, c, hc, hαc⟩
    refine le_normalizer_iSup₂ fun x hx ε hε y hy => ?_
    obtain ⟨hεr, hεt, a, b, ha, hb, hεab⟩ := hε
    have hsum : proj (α + ε) = (if η = γ then c + a else a) • γ +
        (if η = γ then b else c + b) • δ := by
      rw [map_add, proj_apply, hαc, hεab]
      rcases hη with rfl | rfl
      · simp only [↓reduceIte, add_nsmul]
        abel
      · by_cases h : η = γ
        · subst h
          simp only [↓reduceIte, add_nsmul]
          abel
        · simp only [h, ↓reduceIte, add_nsmul]
          abel
    have hpos : 0 < (if η = γ then b else c + b) := by split_ifs <;> omega
    have hpos' : 0 < (if η = γ then c + a else a) := by split_ifs <;> omega
    have hxy := commutatorElement_mem_rootGroup_add hα hεr (hne _ _ hpos _ hsum) hx hy
    have h1 : ⁅x, y⁆ ∈ N := hXN _ (hcone _ _ hpos' hpos _ hsum) hxy
    have h2 : y ∈ N := hXN ε (fun _ => ⟨hεr, hεt, a, b, ha, hb, hεab⟩) hy
    have := mul_mem h1 h2
    rwa [commutatorElement_def, inv_mul_cancel_right] at this
  have hxN : ⁅(x : adjointGroup d4 K), (y : adjointGroup d4 K)⁆ ∈ N := by
    refine commutatorElement_mem_of_mem_iSup
      (A := fun α => ⨆ (_ : α ∈ fibre γ), 𝕏 α) (B := fun α => ⨆ (_ : α ∈ fibre δ), 𝕏 α)
      (fun α => iSup_le fun hα => hnorm γ (Or.inl rfl) α hα)
      (fun α => iSup_le fun hα => hnorm δ (Or.inr rfl) α hα) (fun α α' a ha b hb => ?_)
      (mem_iSup_fibre hx) (mem_iSup_fibre hy)
    refine commutatorElement_mem_of_mem_iSup
      (A := fun _ : α ∈ fibre γ => 𝕏 α) (B := fun _ : α' ∈ fibre δ => 𝕏 α')
      (fun hα => hnorm γ (Or.inl rfl) α hα) (fun hα' => hnorm δ (Or.inr rfl) α' hα')
      (fun hα hα' a ha b hb => ?_) ha hb
    obtain ⟨hαr, c, hc, hαc⟩ := hα
    obtain ⟨hαr', c', hc', hαc'⟩ := hα'
    have hsum : proj (α + α') = c • γ + c' • δ := by
      rw [map_add, proj_apply, proj_apply, hαc, hαc']
    exact hXN _ (hcone c c' hc hc' _ hsum)
      (commutatorElement_mem_rootGroup_add hαr hαr' (hne c c' hc' _ hsum) ha hb)
  obtain ⟨g, hgγ, hgδ⟩ := exists_addHom_pos_pos hlin
  have hfix : (⁅(x : adjointGroup d4 K), (y : adjointGroup d4 K)⁆ : adjointGroup d4 K) ∈
      twistFixed .D4 K σ := twistedGroup_le_twistFixed σ (⁅x, y⁆ : twistedGroup σ).2
  have hle := iSup_rootGroup_inf_twistFixed_le σ (f := g.comp proj)
    (fun v => by rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, proj_rho]) (Ψ := Ψ)
    (fun α ⟨hα, _, a, b, ha, hb, hab⟩ => ⟨hα, by
      rw [AddMonoidHom.comp_apply, hab]
      exact pos_apply_nsmul_add_nsmul hgγ hgδ (by omega)⟩)
    (fun α ⟨_, _, a, b, ha, hb, hab⟩ α' ⟨_, _, a', b', ha', hb', hab'⟩ hr =>
      hcone (a + a') (b + b') (by omega) (by omega) _
        (by rw [map_add, hab, hab', add_nsmul, add_nsmul]; abel) hr)
    (fun α ⟨hα, hα'⟩ => ⟨isRoot_rho hα, by rwa [proj_rho]⟩) (Subgroup.mem_inf.2 ⟨hxN, hfix⟩)
  have hsub : ⨆ β ∈ proj '' Ψ, twistedRootSubgroupD4 σ β ≤
      ⨆ ε ∈ openCone {β | IsRoot .G2 β} γ δ, twistedRootSubgroupD4 σ ε := by
    refine iSup₂_le fun β hβ => ?_
    obtain ⟨α, ⟨-, hαcone⟩, rfl⟩ := hβ
    exact le_iSup₂_of_le (f := fun ε (_ : ε ∈ openCone {β | IsRoot .G2 β} γ δ) =>
      twistedRootSubgroupD4 σ ε) (proj α) hαcone le_rfl
  exact hsub hle

theorem commutator_mem_twistedDatum :
    ∀ γ ∈ (twistedDatum σ).roots,
    ∀ δ ∈ (twistedDatum σ).roots, LinIndepPair γ δ →
      ∀ x ∈ (twistedDatum σ).rootGroup γ, ∀ y ∈ (twistedDatum σ).rootGroup δ,
        ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (twistedDatum σ).roots γ δ, (twistedDatum σ).rootGroup ε := by
  intro γ _ δ _ hlin x hx y hy
  rw [twistedDatum_roots]
  exact commutator_mem_iSup_twistedRootGroup hlin hx hy

end Commutator

end CFSG.LieType.Steinberg.TwistedD4
