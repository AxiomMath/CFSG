module

public import CFSG.LieType.Steinberg.TwistedE6.Roots
public import CFSG.LieType.Steinberg.BruhatTwistBasic
public import CFSG.LieType.Steinberg.BruhatWeyl
import CFSG.LieType.Steinberg.PartBHalfSpace
import Mathlib.Tactic.Group
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

variable {k : Type*} [Field k] (θ : k →+* k)

section RootGroups

variable {θ}

theorem sigma_mem_rootGroup_rho {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    {x : e6Data_valid.minGroup k} (hx : x ∈ e6Data_valid.rootGroup k γ) :
    sigma k θ x ∈ e6Data_valid.rootGroup k (rho γ) := by
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
  rw [sigma_xm θ hγ c]
  exact e6Data_valid.xm_mem_rootGroup k _ _

theorem commutatorElement_mem_rootGroup_add {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (hne : γ + δ ≠ 0) {x y : e6Data_valid.minGroup k}
    (hx : x ∈ e6Data_valid.rootGroup k γ) (hy : y ∈ e6Data_valid.rootGroup k δ) :
    ⁅x, y⁆ ∈ e6Data_valid.rootGroup k (γ + δ) := by
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
  obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
  obtain ⟨hroot, hcomm⟩ := e6Data_valid.commutator_xm k hγ hδ hne
  by_cases hr : IsRoot .E6 (γ + δ)
  · obtain ⟨σ, -, h⟩ := hroot hr
    rw [h]
    exact e6Data_valid.xm_mem_rootGroup k _ _
  · rw [hcomm hr]
    exact one_mem _

theorem commute_of_mem_rootGroup_rho {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hne : rho α ≠ α) {x y : e6Data_valid.minGroup k} (hx : x ∈ e6Data_valid.rootGroup k α)
    (hy : y ∈ e6Data_valid.rootGroup k (rho α)) : Commute x y := by
  have h := commutatorElement_mem_rootGroup_add hα (isRoot_rho hα) (add_rho_ne_zero hα hne)
    hx hy
  rw [e6Data_valid.rootGroup_eq_bot k (not_isRoot_add_rho hα hne), Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_commute.1 h

theorem twistedDatum_roots : (twistedDatum k θ).roots = {β | IsRoot .F4 β} :=
  roots_eq (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)

end RootGroups

abbrev twistedRootSubgroupE6 (β : Fin (Tag.rank .F4) → ℤ) : Subgroup (e6Data_valid.minGroup k) :=
  twistedRootSubgroup {α | IsRoot .E6 α} orbitMap (e6Data_valid.rootGroup k) (sigma k θ) β

theorem mem_twistedRootSubgroupE6 {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    {g : e6Data_valid.minGroup k}
    (hg : g ∈ e6Data_valid.rootGroup k α ⊔ e6Data_valid.rootGroup k (rho α))
    (hfix : sigma k θ g = g) : g ∈ twistedRootSubgroupE6 θ (proj α) := by
  refine Subgroup.mem_inf.2 ⟨?_, hfix⟩
  have hle : ∀ α' : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 α' → proj α' = proj α →
      e6Data_valid.rootGroup k α' ≤ ⨆ α'' ∈ {α | IsRoot .E6 α},
        ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α'' = c • proj α), e6Data_valid.rootGroup k α'' :=
    fun α' hα' hp => le_iSup₂_of_le α' hα' (le_iSup_of_le ⟨1, one_pos, by
      rw [one_smul, ← proj_apply, hp]⟩ le_rfl)
  exact sup_le (hle α hα rfl) (hle _ (isRoot_rho hα) (proj_rho α)) hg

theorem iSup_rootGroup_inf_fixedGroup_le {f : (Fin (Tag.rank .E6) → ℤ) →+ ℤ}
    (hf : ∀ v, f (rho v) = f v) {Ψ : Set (Fin (Tag.rank .E6) → ℤ)}
    (hΨ : ∀ α ∈ Ψ, IsRoot .E6 α ∧ 0 < f α)
    (hclosed : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot .E6 (α + β) → α + β ∈ Ψ)
    (hρ : ∀ α ∈ Ψ, rho α ∈ Ψ) :
    (⨆ α ∈ Ψ, e6Data_valid.rootGroup k α) ⊓ fixedGroup k θ ≤
      ⨆ β ∈ proj '' Ψ, twistedRootSubgroupE6 θ β := by
  intro u hu
  obtain ⟨huΨ, hufix⟩ := Subgroup.mem_inf.1 hu
  have hfix : sigma k θ u = u := hufix
  have hfin : Ψ.Finite := (finite_setOf_isRoot .E6).subset fun α hα => (hΨ α hα).1
  obtain ⟨M, hMΨ, hmem, hnd, hsort⟩ := exists_list_flatMap_pairBlock (ρ := rho)
    (ord := fun v => List.ofFn v) List.ofFn_injective rho_rho (fun v => f v) hf hfin hρ
  set L := M.flatMap (pairBlock rho) with hL
  have hroot : ∀ γ ∈ L, IsRoot .E6 γ := fun γ hγ => (hΨ γ ((hmem γ).1 hγ)).1
  have hpos : ∀ γ ∈ L, 0 < f γ := fun γ hγ => (hΨ γ ((hmem γ).1 hγ)).2
  have hLρ : ∀ γ ∈ L, rho γ ∈ L := fun γ hγ => (hmem _).2 (hρ γ ((hmem γ).1 hγ))
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ e6Data_valid.rootGroup k a,
      ∀ y ∈ e6Data_valid.rootGroup k b, ⁅x, y⁆ ∈ ⨆ c ∈ L,
        ⨆ (_ : min (f a) (f b) < f c), e6Data_valid.rootGroup k c := by
    intro a ha b hb _ x hx y hy
    have hab : 0 < f (a + b) := by rw [map_add]; linarith [hpos a ha, hpos b hb]
    have hne : a + b ≠ 0 := fun h => by rw [h, map_zero] at hab; exact lt_irrefl _ hab
    have hxy := commutatorElement_mem_rootGroup_add (hroot a ha) (hroot b hb) hne hx hy
    by_cases hr : IsRoot .E6 (a + b)
    · have hab' : a + b ∈ L := (hmem _).2 (hclosed a ((hmem a).1 ha) b ((hmem b).1 hb) hr)
      refine le_iSup₂_of_le (f := fun c (_ : c ∈ L) =>
        ⨆ (_ : min (f a) (f b) < f c), e6Data_valid.rootGroup k c) (a + b) hab'
        (le_iSup_of_le ?_ le_rfl) hxy
      rw [map_add]
      have := hpos a ha
      have := hpos b hb
      omega
    · rw [e6Data_valid.rootGroup_eq_bot k hr, Subgroup.mem_bot] at hxy
      rw [hxy]
      exact one_mem _
  have huL : u ∈ ⨆ v ∈ L, e6Data_valid.rootGroup k v := by
    have h : ⨆ α ∈ Ψ, e6Data_valid.rootGroup k α = ⨆ v ∈ L, e6Data_valid.rootGroup k v :=
      iSup_congr fun α => iSup_congr_Prop (hmem α).symm fun _ => rfl
    rwa [← h]
  obtain ⟨F, hF, rfl⟩ := exists_prod_eq_of_commutator_mem (e6Data_valid.rootGroup k)
    (fun γ => f γ) hnd hsort hcomm _ huL
  set F' : (Fin (Tag.rank .E6) → ℤ) → e6Data_valid.minGroup k := fun γ => sigma k θ (F (rho γ))
  have hF' : ∀ γ ∈ L, F' γ ∈ e6Data_valid.rootGroup k γ := fun γ hγ => by
    have h := sigma_mem_rootGroup_rho (θ := θ) (isRoot_rho (hroot γ hγ)) (hF _ (hLρ γ hγ))
    rwa [rho_rho] at h
  have hblock : ∀ m ∈ M, ((pairBlock rho m).map (sigma k θ ∘ F)).prod =
      ((pairBlock rho m).map F').prod := by
    intro m hm
    have hmL : m ∈ L := (hmem m).2 (hMΨ m hm)
    refine (prod_map_pairBlock_comp (sigma k θ ∘ F) (rho_rho m) fun hne => ?_).symm
    have h1 := sigma_mem_rootGroup_rho (θ := θ) (hroot m hmL) (hF m hmL)
    have h2 := sigma_mem_rootGroup_rho (θ := θ) (hroot _ (hLρ m hmL)) (hF _ (hLρ m hmL))
    refine commute_of_mem_rootGroup_rho (isRoot_rho (hroot m hmL)) ?_ h1 h2
    rwa [rho_rho, ne_comm]
  have hσu : sigma k θ (L.map F).prod = (L.map F').prod := by
    rw [map_list_prod, List.map_map, hL, prod_map_flatMap, prod_map_flatMap]
    exact congrArg List.prod (List.map_congr_left fun m hm => hblock m hm)
  have hinj := e6Data_valid.prodInjective_additive (k := k) posDef_cartan_E6 f L hnd
    (fun γ hγ => ⟨hroot γ hγ, hpos γ hγ⟩) hsort
  have hFF' : ∀ γ ∈ L, F γ = F' γ := hinj F F' hF hF' (by rw [← hσu, hfix])
  have hP : ∀ m ∈ M, ((pairBlock rho m).map F).prod ∈ twistedRootSubgroupE6 θ (proj m) := by
    intro m hm
    have hmL : m ∈ L := (hmem m).2 (hMΨ m hm)
    have hsub : ∀ γ ∈ pairBlock rho m, γ ∈ L := fun γ hγ => by
      rcases mem_pairBlock.1 hγ with rfl | rfl
      exacts [hmL, hLρ _ hmL]
    refine mem_twistedRootSubgroupE6 θ (hroot m hmL) (Subgroup.list_prod_mem _ fun x hx => ?_) ?_
    · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
      rcases mem_pairBlock.1 hγ with rfl | rfl
      · exact Subgroup.mem_sup_left (hF _ hmL)
      · exact Subgroup.mem_sup_right (hF _ (hLρ _ hmL))
    · rw [map_list_prod, List.map_map, hblock m hm]
      exact congrArg List.prod (List.map_congr_left fun γ hγ => (hFF' γ (hsub γ hγ)).symm)
  rw [hL, prod_map_flatMap]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
  exact le_iSup₂_of_le (f := fun β (_ : β ∈ proj '' Ψ) => twistedRootSubgroupE6 θ β) (proj m)
    ⟨m, hMΨ m hm, rfl⟩ le_rfl (hP m hm)

section Commutator

variable {θ}

theorem twistedRootSubgroupE6_le_fixedGroup (β : Fin (Tag.rank .F4) → ℤ) :
    twistedRootSubgroupE6 θ β ≤ fixedGroup k θ :=
  inf_le_right

theorem iSup_twistedRootGroup_eq_subgroupOf (S : Set (Fin (Tag.rank .F4) → ℤ)) :
    ⨆ β ∈ S, twistedRootGroup k θ β = (⨆ β ∈ S, twistedRootSubgroupE6 θ β).subgroupOf
      (fixedGroup k θ) := by
  rw [iSup_subgroupOf fun β => iSup_le fun _ => twistedRootSubgroupE6_le_fixedGroup β]
  exact iSup_congr fun β => (iSup_subgroupOf fun _ => twistedRootSubgroupE6_le_fixedGroup β).symm

private abbrev fibre (γ : Fin (Tag.rank .F4) → ℤ) : Set (Fin (Tag.rank .E6) → ℤ) :=
  {α | IsRoot .E6 α ∧ ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • γ}

private theorem mem_iSup_fibre {γ : Fin (Tag.rank .F4) → ℤ} {x : e6Data_valid.minGroup k}
    (hx : x ∈ twistedRootSubgroupE6 θ γ) :
    x ∈ ⨆ α, ⨆ (_ : α ∈ fibre γ), e6Data_valid.rootGroup k α := by
  have h : x ∈ ⨆ α ∈ {α | IsRoot .E6 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • γ), e6Data_valid.rootGroup k α :=
    (Subgroup.mem_inf.1 hx).1
  have hle : (⨆ α ∈ {α | IsRoot .E6 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • γ), e6Data_valid.rootGroup k α) ≤
      ⨆ α, ⨆ (_ : α ∈ fibre γ), e6Data_valid.rootGroup k α :=
    iSup_le fun α => iSup_le fun hα => iSup_le fun hc =>
      le_iSup₂_of_le (f := fun α (_ : α ∈ fibre γ) => e6Data_valid.rootGroup k α) α ⟨hα, hc⟩
        le_rfl
  exact hle h

theorem mem_iSup_twistedRootGroup_iff {S : Set (Fin (Tag.rank .F4) → ℤ)} {z : fixedGroup k θ} :
    z ∈ ⨆ β ∈ S, twistedRootGroup k θ β ↔
      (z : e6Data_valid.minGroup k) ∈ ⨆ β ∈ S, twistedRootSubgroupE6 θ β := by
  rw [iSup_twistedRootGroup_eq_subgroupOf, Subgroup.mem_subgroupOf]

theorem commutator_mem_iSup_twistedRootGroup {γ δ : Fin (Tag.rank .F4) → ℤ}
    (hlin : LinIndepPair γ δ) {x y : fixedGroup k θ} (hx : x ∈ twistedRootGroup k θ γ)
    (hy : y ∈ twistedRootGroup k θ δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone {β | IsRoot .F4 β} γ δ, twistedRootGroup k θ ε := by
  refine mem_iSup_twistedRootGroup_iff.2 ?_
  set Ψ : Set (Fin (Tag.rank .E6) → ℤ) :=
    {α | IsRoot .E6 α ∧ proj α ∈ openCone {β | IsRoot .F4 β} γ δ} with hΨ
  set N := ⨆ α ∈ Ψ, e6Data_valid.rootGroup k α
  have hXN : ∀ α : Fin (Tag.rank .E6) → ℤ, (IsRoot .E6 α → α ∈ Ψ) →
      e6Data_valid.rootGroup k α ≤ N := fun α h => by
    by_cases hr : IsRoot .E6 α
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ Ψ) => e6Data_valid.rootGroup k α) α (h hr)
        le_rfl
    · rw [e6Data_valid.rootGroup_eq_bot k hr]
      exact bot_le
  have hcone : ∀ (a b : ℕ), 0 < a → 0 < b → ∀ α : Fin (Tag.rank .E6) → ℤ,
      proj α = a • γ + b • δ → IsRoot .E6 α → α ∈ Ψ := fun a b ha hb α hα hr =>
    ⟨hr, isRoot_proj hr, a, b, ha, hb, hα⟩
  have hne : ∀ (a b : ℕ), 0 < b → ∀ α : Fin (Tag.rank .E6) → ℤ, proj α = a • γ + b • δ →
      α ≠ 0 := fun a b hb α hα h0 => by
    rw [h0, map_zero] at hα
    have := (hlin a b (by rw [natCast_zsmul, natCast_zsmul]; exact hα.symm)).2
    omega
  have hnorm : ∀ (η : Fin (Tag.rank .F4) → ℤ), (η = γ ∨ η = δ) → ∀ α ∈ fibre η,
      e6Data_valid.rootGroup k α ≤ Subgroup.normalizer (N : Set _) := by
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
  have hxN : ⁅(x : e6Data_valid.minGroup k), (y : e6Data_valid.minGroup k)⁆ ∈ N := by
    refine commutatorElement_mem_of_mem_iSup
      (A := fun α => ⨆ (_ : α ∈ fibre γ), e6Data_valid.rootGroup k α)
      (B := fun α => ⨆ (_ : α ∈ fibre δ), e6Data_valid.rootGroup k α)
      (fun α => iSup_le fun hα => hnorm γ (Or.inl rfl) α hα)
      (fun α => iSup_le fun hα => hnorm δ (Or.inr rfl) α hα) (fun α α' a ha b hb => ?_)
      (mem_iSup_fibre hx) (mem_iSup_fibre hy)
    refine commutatorElement_mem_of_mem_iSup
      (A := fun _ : α ∈ fibre γ => e6Data_valid.rootGroup k α)
      (B := fun _ : α' ∈ fibre δ => e6Data_valid.rootGroup k α')
      (fun hα => hnorm γ (Or.inl rfl) α hα) (fun hα' => hnorm δ (Or.inr rfl) α' hα')
      (fun hα hα' a ha b hb => ?_) ha hb
    obtain ⟨hαr, c, hc, hαc⟩ := hα
    obtain ⟨hαr', c', hc', hαc'⟩ := hα'
    have hsum : proj (α + α') = c • γ + c' • δ := by rw [map_add, proj_apply, proj_apply, hαc, hαc']
    exact hXN _ (hcone c c' hc hc' _ hsum)
      (commutatorElement_mem_rootGroup_add hαr hαr' (hne c c' hc' _ hsum) ha hb)
  obtain ⟨g, hgγ, hgδ⟩ := exists_addHom_pos_pos hlin
  have hfix : (⁅(x : e6Data_valid.minGroup k), (y : e6Data_valid.minGroup k)⁆ :
      e6Data_valid.minGroup k) ∈ fixedGroup k θ := (⁅x, y⁆ : fixedGroup k θ).2
  have hle := iSup_rootGroup_inf_fixedGroup_le θ (f := g.comp proj)
    (fun v => by rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, proj_rho]) (Ψ := Ψ)
    (fun α ⟨hα, _, a, b, ha, hb, hab⟩ => ⟨hα, by
      rw [AddMonoidHom.comp_apply, hab]
      exact pos_apply_nsmul_add_nsmul hgγ hgδ (by omega)⟩)
    (fun α ⟨_, _, a, b, ha, hb, hab⟩ α' ⟨_, _, a', b', ha', hb', hab'⟩ hr =>
      hcone (a + a') (b + b') (by omega) (by omega) _
        (by rw [map_add, hab, hab', add_nsmul, add_nsmul]; abel) hr)
    (fun α ⟨hα, hα'⟩ => ⟨isRoot_rho hα, by rwa [proj_rho]⟩) (Subgroup.mem_inf.2 ⟨hxN, hfix⟩)
  have hsub : ⨆ β ∈ proj '' Ψ, twistedRootSubgroupE6 θ β ≤
      ⨆ ε ∈ openCone {β | IsRoot .F4 β} γ δ, twistedRootSubgroupE6 θ ε := by
    refine iSup₂_le fun β hβ => ?_
    obtain ⟨α, ⟨-, hαcone⟩, rfl⟩ := hβ
    exact le_iSup₂_of_le (f := fun ε (_ : ε ∈ openCone {β | IsRoot .F4 β} γ δ) =>
      twistedRootSubgroupE6 θ ε) (proj α) hαcone le_rfl
  exact hsub hle

theorem commutator_mem_twistedDatum : ∀ γ ∈ (twistedDatum k θ).roots,
    ∀ δ ∈ (twistedDatum k θ).roots, LinIndepPair γ δ →
      ∀ x ∈ (twistedDatum k θ).rootGroup γ, ∀ y ∈ (twistedDatum k θ).rootGroup δ,
        ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (twistedDatum k θ).roots γ δ, (twistedDatum k θ).rootGroup ε := by
  intro γ _ δ _ hlin x hx y hy
  rw [twistedDatum_roots]
  exact commutator_mem_iSup_twistedRootGroup hlin hx hy

end Commutator

end CFSG.LieType.Steinberg.TwistedE6
