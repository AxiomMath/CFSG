module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6KillBasic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps

@[expose] def twKillPerp (J : Set (Fin TwistTag.E6.tag.rank)) (i : Fin TwistTag.E6.tag.rank) :
    Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  classKillPerp TwistTag.E6.tag J i ∩ classKillPerp TwistTag.E6.tag J (TwistTag.E6.perm i)

structure TwKillAdm (J : Set (Fin TwistTag.E6.tag.rank)) (i : Fin TwistTag.E6.tag.rank)
    (R : Set (Fin TwistTag.E6.tag.rank → ℤ)) : Prop where
  subset : R ⊆ parabolicPosRoots TwistTag.E6.tag J \
    {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}
  ideal : ∀ γ ∈ parabolicPosRoots TwistTag.E6.tag J, ∀ δ ∈ R, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot TwistTag.E6.tag (a • γ + b • δ) → a • γ + b • δ ∈ R
  down : ∀ δ ∈ R, ∀ j, (j = i ∨ j = TwistTag.E6.perm i) →
    IsRoot TwistTag.E6.tag (δ - Pi.single j 1) → δ - Pi.single j 1 ∈ R

structure TwKillMin (i : Fin TwistTag.E6.tag.rank) (R : Set (Fin TwistTag.E6.tag.rank → ℤ))
    (δ : Fin TwistTag.E6.tag.rank → ℤ) : Prop where
  mem : δ ∈ R
  deg_le : ∀ δ' ∈ R, twKillDeg i δ ≤ twKillDeg i δ'
  lev_le : ∀ δ' ∈ R, twKillDeg i δ' = twKillDeg i δ → twKillLev i δ ≤ twKillLev i δ'

theorem twKill_height_perm (v : Fin TwistTag.E6.tag.rank → ℤ) :
    height (permLattice TwistTag.E6.perm v) = height v :=
  Equiv.sum_comp TwistTag.E6.perm.symm v

theorem twKill_perm_single (i : Fin TwistTag.E6.tag.rank) :
    permLattice TwistTag.E6.perm (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      Pi.single (TwistTag.E6.perm i) 1 :=
  permLattice_single _ i

theorem twKill_perm_single_perm (i : Fin TwistTag.E6.tag.rank) :
    permLattice TwistTag.E6.perm (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      Pi.single i 1 := by
  rw [permLattice_single, twistedE6_perm_perm]

theorem TwKillAdm.inter {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank}
    {R₁ R₂ : Set (Fin TwistTag.E6.tag.rank → ℤ)} (h₁ : TwKillAdm J i R₁)
    (h₂ : TwKillAdm J i R₂) : TwKillAdm J i (R₁ ∩ R₂) :=
  ⟨fun _ hx => h₁.subset hx.1, fun γ hγ δ hδ a b ha hb hr =>
    ⟨h₁.ideal γ hγ δ hδ.1 a b ha hb hr, h₂.ideal γ hγ δ hδ.2 a b ha hb hr⟩,
    fun δ hδ j hj hr => ⟨h₁.down δ hδ.1 j hj hr, h₂.down δ hδ.2 j hj hr⟩⟩


theorem twKill_eq_single_of_supp {i : Fin TwistTag.E6.tag.rank}
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ) (hpos : 0 < height δ)
    (hsupp : ∀ l, l ≠ i → l ≠ TwistTag.E6.perm i → δ l = 0) :
    δ = Pi.single i 1 ∨ δ = Pi.single (TwistTag.E6.perm i) 1 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq TwistTag.E6.tag.rootCertificate_check hδ
  rcases twKill_check_supp i k (List.mem_range.2 hk) hpos hsupp with h | h
  · exact Or.inl (List.ofFn_injective h)
  · exact Or.inr (List.ofFn_injective h)

theorem twKillDeg_nonneg {i : Fin TwistTag.E6.tag.rank} {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (hpos : 0 < height δ) : 0 ≤ twKillDeg i δ := by
  have hnn := (IsRoot.height_pos_iff hδ).1 hpos
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact le_rfl
  · exact hnn j

theorem one_le_twKillDeg {i : Fin TwistTag.E6.tag.rank} {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) (hpos : 0 < height δ) (hne : δ ≠ Pi.single i 1)
    (hne' : δ ≠ Pi.single (TwistTag.E6.perm i) 1) : 1 ≤ twKillDeg i δ := by
  have hnn := (IsRoot.height_pos_iff hδ).1 hpos
  by_contra hlt
  have h0 : twKillDeg i δ = 0 := le_antisymm (by omega) (twKillDeg_nonneg hδ hpos)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun l => if l = i ∨ l = TwistTag.E6.perm i then 0 else δ l)
    (fun l _ => by
      split_ifs
      · exact le_rfl
      · exact hnn l)).1 h0
  have hsupp : ∀ l, l ≠ i → l ≠ TwistTag.E6.perm i → δ l = 0 := fun l h1 h2 => by
    have := hz l (Finset.mem_univ l)
    split_ifs at this with h
    · exact absurd h (by tauto)
    · exact this
  rcases twKill_eq_single_of_supp hδ hpos hsupp with h | h
  · exact hne h
  · exact hne' h

theorem twKill_mem_of_agree {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ J) (hi' : TwistTag.E6.perm i ∈ J) {δ v : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : δ ∈ parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1})
    (hv : IsRoot TwistTag.E6.tag v) (hag : ∀ l, l ≠ i → l ≠ TwistTag.E6.perm i → v l = δ l) :
    v ∈ parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1} := by
  obtain ⟨⟨⟨hδr, hδJ⟩, -, hδp⟩, hδne⟩ := hδ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hδne
  have hdeg := one_le_twKillDeg hδr hδp hδne.1 hδne.2
  have hdv : twKillDeg i v = twKillDeg i δ := by
    simp only [twKillDeg]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · rfl
    · exact hag l (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  obtain ⟨l, hl, hlpos⟩ : ∃ l, ¬(l = i ∨ l = TwistTag.E6.perm i) ∧ 0 < δ l := by
    by_contra! h
    have : twKillDeg i δ ≤ 0 := Finset.sum_nonpos fun l _ => by
      split_ifs with hl
      · exact le_rfl
      · exact h l (not_or.1 hl)
    omega
  have hvl : v l = δ l := hag l (fun e => hl (Or.inl e)) (fun e => hl (Or.inr e))
  have hvpos : 0 < height v := by
    rcases hv.nonneg_or_nonpos with h | h
    · exact (IsRoot.height_pos_iff hv).2 h
    · have := h l
      omega
  refine ⟨⟨⟨hv, fun m hm => ?_⟩, hv, hvpos⟩, ?_⟩
  · have hmi : m ≠ i := fun e => hm (e ▸ hi)
    have hmi' : m ≠ TwistTag.E6.perm i := fun e => hm (e ▸ hi')
    rw [hag m hmi hmi', hδJ m hm]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [e, twKillDeg_single (Or.inl rfl)] at hdv
      omega
    · rw [e, twKillDeg_single (Or.inr rfl)] at hdv
      omega

theorem twKill_perm_mem_parabolicPosRoots {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : δ ∈ parabolicPosRoots TwistTag.E6.tag J) :
    permLattice TwistTag.E6.perm δ ∈ parabolicPosRoots TwistTag.E6.tag J := by
  obtain ⟨⟨hδr, hδJ⟩, -, hδp⟩ := hδ
  have hr := hδr.permLattice TwistTag.E6.cartan_perm
  refine ⟨⟨hr, fun l hl => ?_⟩, hr, by rw [twKill_height_perm]; exact hδp⟩
  simp only [permLattice, Function.comp_apply, twistedE6_perm_symm_apply]
  refine hδJ _ fun h => hl ?_
  have := hJ _ h
  rwa [twistedE6_perm_perm] at this

theorem twKill_perm_mem_sdiff {J : Set (Fin TwistTag.E6.tag.rank)}
    (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J) {i : Fin TwistTag.E6.tag.rank}
    {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : δ ∈ parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}) :
    permLattice TwistTag.E6.perm δ ∈ parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1} := by
  refine ⟨twKill_perm_mem_parabolicPosRoots hJ hδ.1, fun h => hδ.2 ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with h | h
  · right
    rw [← permLattice_twistedE6_perm_perm δ, h, twKill_perm_single]
  · left
    rw [← permLattice_twistedE6_perm_perm δ, h, twKill_perm_single_perm]

theorem twKillAdm_top {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ J) :
    TwKillAdm J i (parabolicPosRoots TwistTag.E6.tag J \
      {Pi.single i 1, Pi.single (TwistTag.E6.perm i) 1}) := by
  refine ⟨subset_rfl, fun γ hγ δ hδ a b ha hb hr => ?_, fun δ hδ j hj hr => ?_⟩
  · refine ⟨classKill_parabolicPosRoots_closed hγ hδ.1 ha hb hr, fun h => ?_⟩
    have hd : twKillDeg i (a • γ + b • δ) = 0 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · rw [h, twKillDeg_single (Or.inl rfl)]
      · rw [h, twKillDeg_single (Or.inr rfl)]
    rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul] at hd
    have h1 := twKillDeg_nonneg (i := i) hγ.2.1 hγ.2.2
    obtain ⟨⟨⟨hδr, -⟩, -, hδp⟩, hδne⟩ := hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hδne
    have h2 := one_le_twKillDeg hδr hδp hδne.1 hδne.2
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  · refine twKill_mem_of_agree hi (hJ i hi) hδ hr fun l hl hl' => ?_
    have hlj : l ≠ j := by rcases hj with rfl | rfl <;> assumption
    simp [Pi.single_eq_of_ne hlj]

theorem TwKillAdm.perm {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ j ∈ J, TwistTag.E6.perm j ∈ J)
    {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : TwKillAdm J i R) : TwKillAdm J i {β | permLattice TwistTag.E6.perm β ∈ R} := by
  refine ⟨fun β hβ => ?_, fun γ hγ δ hδ a b ha hb hr => ?_, fun δ hδ j hj hr => ?_⟩
  · have h := twKill_perm_mem_sdiff hJ (hR.subset hβ)
    rwa [permLattice_twistedE6_perm_perm] at h
  · show permLattice TwistTag.E6.perm (a • γ + b • δ) ∈ R
    have e : permLattice TwistTag.E6.perm (a • γ + b • δ) =
        a • permLattice TwistTag.E6.perm γ + b • permLattice TwistTag.E6.perm δ := rfl
    rw [e]
    exact hR.ideal _ (twKill_perm_mem_parabolicPosRoots hJ hγ) _ hδ a b ha hb
      (by rw [← e]; exact hr.permLattice TwistTag.E6.cartan_perm)
  · show permLattice TwistTag.E6.perm (δ - Pi.single j 1) ∈ R
    have e : permLattice TwistTag.E6.perm (δ - Pi.single j 1) =
        permLattice TwistTag.E6.perm δ - Pi.single (TwistTag.E6.perm j) 1 := by
      rw [← permLattice_single]
      rfl
    rw [e]
    refine hR.down _ hδ _ ?_ ?_
    · rcases hj with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (twistedE6_perm_perm _)
    · rw [← e]
      exact hr.permLattice TwistTag.E6.cartan_perm

theorem twKill_inter_perm_stable {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} :
    ∀ β ∈ R ∩ {β | permLattice TwistTag.E6.perm β ∈ R},
      permLattice TwistTag.E6.perm β ∈ R ∩ {β | permLattice TwistTag.E6.perm β ∈ R} :=
  fun β hβ => ⟨hβ.2, by show _ ∈ R; rw [permLattice_twistedE6_perm_perm]; exact hβ.1⟩

theorem twKill_exists_min {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank}
    {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R) (hne : R.Nonempty) :
    ∃ δ, TwKillMin i R δ := by
  have hfin : R.Finite := (finite_setOf_isRoot _).subset fun β hβ => (hR.subset hβ).1.2.1
  obtain ⟨δ, hδR, hmin⟩ := hfin.toFinset.exists_min_image
    (fun δ => toLex (twKillDeg i δ, twKillLev i δ)) ((hfin.toFinset_nonempty).2 hne)
  have hmin' : ∀ δ' ∈ R, twKillDeg i δ < twKillDeg i δ' ∨
      (twKillDeg i δ = twKillDeg i δ' ∧ twKillLev i δ ≤ twKillLev i δ') := fun δ' hδ' =>
    Prod.Lex.toLex_le_toLex.1 (hmin δ' (hfin.mem_toFinset.2 hδ'))
  refine ⟨δ, hfin.mem_toFinset.1 hδR, fun δ' hδ' => ?_, fun δ' hδ' he => ?_⟩
  · rcases hmin' δ' hδ' with h | h
    · exact h.le
    · exact h.1.le
  · rcases hmin' δ' hδ' with h | h
    · omega
    · exact h.2

theorem TwKillMin.perm {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hRρ : ∀ β ∈ R, permLattice TwistTag.E6.perm β ∈ R) {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (h : TwKillMin i R δ) : TwKillMin i R (permLattice TwistTag.E6.perm δ) :=
  ⟨hRρ δ h.mem, fun δ' hδ' => by rw [twKillDeg_permLattice]; exact h.deg_le δ' hδ',
    fun δ' hδ' he => by
      rw [twKillDeg_permLattice] at he
      rw [twKillLev_permLattice]
      exact h.lev_le δ' hδ' he⟩

theorem TwKillMin.mono {i : Fin TwistTag.E6.tag.rank} {R R' : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR' : R' ⊆ R) {δ : Fin TwistTag.E6.tag.rank → ℤ} (h : TwKillMin i R δ) (hδ : δ ∈ R') :
    TwKillMin i R' δ :=
  ⟨hδ, fun δ' hδ' => h.deg_le δ' (hR' hδ'), fun δ' hδ' he => h.lev_le δ' (hR' hδ') he⟩

theorem TwKillMin.not_isRoot_sub {J : Set (Fin TwistTag.E6.tag.rank)}
    {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hR : TwKillAdm J i R) {δ : Fin TwistTag.E6.tag.rank → ℤ} (h : TwKillMin i R δ)
    {j : Fin TwistTag.E6.tag.rank} (hj : j = i ∨ j = TwistTag.E6.perm i) :
    ¬IsRoot TwistTag.E6.tag (δ - Pi.single j 1) := by
  intro hr
  have hmem := hR.down δ h.mem j hj hr
  have hd : twKillDeg i (δ - Pi.single j 1) = twKillDeg i δ := by
    rw [twKillDeg_sub, twKillDeg_single hj, sub_zero]
  have := h.lev_le _ hmem hd
  rw [twKillLev_sub, twKillLev_single hj] at this
  omega

theorem twKill_combo {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank}
    {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    {γ δ' : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∈ parabolicPosRoots TwistTag.E6.tag J)
    (hδ' : δ' ∈ R) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : twKillDeg i (a • γ + b • δ') = twKillDeg i δ) :
    b = 1 ∧ (γ = Pi.single i 1 ∨ γ = Pi.single (TwistTag.E6.perm i) 1) ∧
      twKillLev i δ' + a = twKillLev i (a • γ + b • δ') ∧ twKillLev i δ ≤ twKillLev i δ' := by
  rw [twKillDeg_add, twKillDeg_nsmul, twKillDeg_nsmul] at hw
  have hγ0 := twKillDeg_nonneg (i := i) hγ.2.1 hγ.2.2
  obtain ⟨⟨⟨hδ'r, -⟩, -, hδ'p⟩, hδ'ne⟩ := hR.subset hδ'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hδ'ne
  have hδ'1 := one_le_twKillDeg hδ'r hδ'p hδ'ne.1 hδ'ne.2
  have hle := hmin.deg_le δ' hδ'
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hγdeg : twKillDeg i γ = 0 := by nlinarith
  have hbeq : (b : ℤ) = 1 := by nlinarith
  have hb1 : b = 1 := by exact_mod_cast hbeq
  have hdδ : twKillDeg i δ' = twKillDeg i δ := by nlinarith
  have hγe : γ = Pi.single i 1 ∨ γ = Pi.single (TwistTag.E6.perm i) 1 := by
    by_contra hne
    push Not at hne
    have := one_le_twKillDeg hγ.2.1 hγ.2.2 hne.1 hne.2
    omega
  refine ⟨hb1, hγe, ?_, hmin.lev_le δ' hδ' hdδ⟩
  rw [twKillLev_add, twKillLev_nsmul, twKillLev_nsmul, hb1]
  rcases hγe with rfl | rfl
  · rw [twKillLev_single (Or.inl rfl)]
    push_cast
    ring
  · rw [twKillLev_single (Or.inr rfl)]
    push_cast
    ring

theorem twKill_eq_sub_of_combo {γ δ' w : Fin TwistTag.E6.tag.rank → ℤ} {a : ℕ}
    (h : a • γ + 1 • δ' = w) : δ' = w - a • γ := by
  rw [one_smul] at h
  exact eq_sub_of_add_eq' h

theorem twKillAdm_sdiff_perp {J : Set (Fin TwistTag.E6.tag.rank)} {i : Fin TwistTag.E6.tag.rank}
    {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (h1 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1))
    (h2 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1)) :
    TwKillAdm J i (R \ {δ}) := by
  refine ⟨fun x hx => hR.subset hx.1, fun γ hγ δ' hδ' a b ha hb hr =>
    ⟨hR.ideal γ hγ δ' hδ'.1 a b ha hb hr, fun h => ?_⟩,
    fun δ' hδ' j hj hr => ⟨hR.down δ' hδ'.1 j hj hr, fun h => ?_⟩⟩
  · rw [Set.mem_singleton_iff] at h
    obtain ⟨-, -, hlev, hle⟩ := twKill_combo hR hmin hγ hδ'.1 ha hb (by rw [h])
    rw [h] at hlev
    omega
  · rw [Set.mem_singleton_iff] at h
    have he : δ' = δ + Pi.single j 1 := by rw [← h]; abel
    have hδ'r := (hR.subset hδ'.1).1.2.1
    rcases hj with rfl | rfl
    · exact h1 (he ▸ hδ'r)
    · exact h2 (he ▸ hδ'r)

theorem twKillAdm_sdiff_string {J : Set (Fin TwistTag.E6.tag.rank)}
    {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (hstr : ∀ δ ∈ parabolicPosRoots TwistTag.E6.tag J,
      ¬IsRoot TwistTag.E6.tag (δ + (2 : ℤ) • Pi.single i 1))
    (hb : TwistTag.E6.perm i = i ∨
      (¬IsRoot TwistTag.E6.tag (δ + Pi.single (TwistTag.E6.perm i) 1) ∧
        ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) ∧
        ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1))) :
    TwKillAdm J i (R \ {δ, δ + Pi.single i 1}) := by
  have hδJ := (hR.subset hmin.mem).1
  refine ⟨fun x hx => hR.subset hx.1, fun γ hγ δ' hδ' a b ha hb' hr =>
    ⟨hR.ideal γ hγ δ' hδ'.1 a b ha hb' hr, fun h => ?_⟩,
    fun δ' hδ' j hj hr => ⟨hR.down δ' hδ'.1 j hj hr, fun h => ?_⟩⟩
  · have hδ'r := (hR.subset hδ'.1).1.2.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · obtain ⟨-, -, hlev, hle⟩ := twKill_combo hR hmin hγ hδ'.1 ha hb' (by rw [h])
      rw [h] at hlev
      omega
    · obtain ⟨hb1, hγe, hlev, hle⟩ := twKill_combo hR hmin hγ hδ'.1 ha hb'
        (by rw [h, twKillDeg_add, twKillDeg_single (Or.inl rfl), add_zero])
      rw [h, twKillLev_add, twKillLev_single (Or.inl rfl)] at hlev
      have ha1 : a = 1 := by omega
      subst hb1 ha1
      have hδ'e := twKill_eq_sub_of_combo h
      apply hδ'.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hγe with rfl | rfl
      · left
        rw [hδ'e]
        abel
      · rcases hb with hfix | ⟨-, -, h3⟩
        · left
          rw [hδ'e, hfix]
          abel
        · exact absurd (by rw [hδ'e] at hδ'r; convert hδ'r using 1; abel) h3
  · have hδ'r := (hR.subset hδ'.1).1.2.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · have he : δ' = δ + Pi.single j 1 := by rw [← h]; abel
      rcases hj with rfl | rfl
      · exact hδ'.2 (Or.inr (Set.mem_singleton_iff.2 he))
      · rcases hb with hfix | ⟨h1, -, -⟩
        · exact hδ'.2 (Or.inr (Set.mem_singleton_iff.2 (by rw [he, hfix])))
        · exact h1 (he ▸ hδ'r)
    · have he : δ' = δ + Pi.single i 1 + Pi.single j 1 := by rw [← h]; abel
      rcases hj with rfl | rfl
      · refine hstr δ hδJ ?_
        rw [he] at hδ'r
        convert hδ'r using 1
        rw [two_smul]
        abel
      · rcases hb with hfix | ⟨-, h2, -⟩
        · refine hstr δ hδJ ?_
          rw [he, hfix] at hδ'r
          convert hδ'r using 1
          rw [two_smul]
          abel
        · exact h2 (he ▸ hδ'r)

theorem twKillAdm_sdiff_square {J : Set (Fin TwistTag.E6.tag.rank)}
    {i : Fin TwistTag.E6.tag.rank} {R : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hR : TwKillAdm J i R)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hmin : TwKillMin i R δ)
    (hstr : ∀ δ ∈ parabolicPosRoots TwistTag.E6.tag J,
      ¬IsRoot TwistTag.E6.tag (δ + (2 : ℤ) • Pi.single i 1))
    (hstr' : ∀ δ ∈ parabolicPosRoots TwistTag.E6.tag J,
      ¬IsRoot TwistTag.E6.tag (δ + (2 : ℤ) • Pi.single (TwistTag.E6.perm i) 1))
    (h1 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 - Pi.single (TwistTag.E6.perm i) 1))
    (h2 : ¬IsRoot TwistTag.E6.tag (δ - Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1))
    (h3 : ¬IsRoot TwistTag.E6.tag
      (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 + Pi.single i 1))
    (h4 : ¬IsRoot TwistTag.E6.tag (δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1 +
      Pi.single (TwistTag.E6.perm i) 1)) :
    TwKillAdm J i (R \ {δ, δ + Pi.single i 1, δ + Pi.single (TwistTag.E6.perm i) 1,
      δ + Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1}) := by
  have hδJ := (hR.subset hmin.mem).1
  set α : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i 1 with hα
  set α' : Fin TwistTag.E6.tag.rank → ℤ := Pi.single (TwistTag.E6.perm i) 1 with hα'
  have dα : twKillDeg i α = 0 := twKillDeg_single (Or.inl rfl)
  have dα' : twKillDeg i α' = 0 := twKillDeg_single (Or.inr rfl)
  have lα : twKillLev i α = 1 := twKillLev_single (Or.inl rfl)
  have lα' : twKillLev i α' = 1 := twKillLev_single (Or.inr rfl)
  refine ⟨fun x hx => hR.subset hx.1, fun γ hγ δ' hδ' a b ha hb' hr =>
    ⟨hR.ideal γ hγ δ' hδ'.1 a b ha hb' hr, fun h => ?_⟩,
    fun δ' hδ' j hj hr => ⟨hR.down δ' hδ'.1 j hj hr, fun h => ?_⟩⟩
  · have hδ'r := (hR.subset hδ'.1).1.2.1
    have hδ'n := hδ'.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h hδ'n
    rcases h with h | h | h | h
    · obtain ⟨-, -, hlev, hle⟩ := twKill_combo hR hmin hγ hδ'.1 ha hb' (by rw [h])
      rw [h] at hlev
      omega
    · obtain ⟨hb1, hγe, hlev, hle⟩ := twKill_combo hR hmin hγ hδ'.1 ha hb'
        (by rw [h, twKillDeg_add, dα, add_zero])
      rw [h, twKillLev_add, lα] at hlev
      have ha1 : a = 1 := by omega
      subst hb1 ha1
      have hδ'e := twKill_eq_sub_of_combo h
      rcases hγe with rfl | rfl
      · exact hδ'n.1 (by rw [hδ'e]; abel)
      · exact h1 (by rw [hδ'e] at hδ'r; convert hδ'r using 1; abel)
    · obtain ⟨hb1, hγe, hlev, hle⟩ := twKill_combo hR hmin hγ hδ'.1 ha hb'
        (by rw [h, twKillDeg_add, dα', add_zero])
      rw [h, twKillLev_add, lα'] at hlev
      have ha1 : a = 1 := by omega
      subst hb1 ha1
      have hδ'e := twKill_eq_sub_of_combo h
      rcases hγe with rfl | rfl
      · exact h2 (by rw [hδ'e] at hδ'r; convert hδ'r using 1; abel)
      · exact hδ'n.1 (by rw [hδ'e]; abel)
    · obtain ⟨hb1, hγe, hlev, hle⟩ := twKill_combo hR hmin hγ hδ'.1 ha hb'
        (by rw [h, twKillDeg_add, twKillDeg_add, dα, dα', add_zero, add_zero])
      rw [h, twKillLev_add, twKillLev_add, lα, lα'] at hlev
      have ha12 : a = 1 ∨ a = 2 := by omega
      subst hb1
      have hδ'e := twKill_eq_sub_of_combo h
      rcases ha12 with rfl | rfl <;> rcases hγe with rfl | rfl
      · exact hδ'n.2.2.1 (by rw [hδ'e]; abel)
      · exact hδ'n.2.1 (by rw [hδ'e]; abel)
      · exact h2 (by rw [hδ'e] at hδ'r; convert hδ'r using 1; abel)
      · exact h1 (by rw [hδ'e] at hδ'r; convert hδ'r using 1; abel)
  · have hδ'r := (hR.subset hδ'.1).1.2.1
    have hδ'n := hδ'.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h hδ'n
    have he : δ' = (δ' - Pi.single j 1) + Pi.single j 1 := by abel
    rcases h with h | h | h | h <;> rw [h] at he <;> rcases hj with rfl | rfl
    · exact hδ'n.2.1 he
    · exact hδ'n.2.2.1 he
    · refine hstr δ hδJ ?_
      rw [he] at hδ'r
      convert hδ'r using 1
      rw [two_smul]
      abel
    · exact hδ'n.2.2.2 he
    · exact hδ'n.2.2.2 (by rw [he]; abel)
    · refine hstr' δ hδJ ?_
      rw [he] at hδ'r
      convert hδ'r using 1
      rw [two_smul]
      abel
    · exact h3 (he ▸ hδ'r)
    · exact h4 (he ▸ hδ'r)

end CFSG.SeitzReduction
