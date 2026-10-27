module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpBlocks
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Sp

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.AGLEmbeddingD2.ParabLevi TauCeti.GLSymplecticFin
  CFSG.AGLEmbeddingD2.SquareSymplectic CFSG.AGLEmbeddingD2.SquareLinear CFSG.AGLEmbedding


section Supp

open Classical

variable {n : ℕ} {F : Type} [Field F] {I : Set (Fin n)}

@[expose] noncomputable def suppSet (B : Finset (Fin (n + 1))) : Set (Fin n ⊕ Fin n) :=
  ↑((coordsOf B).disjSum (coordsOf B))

theorem GA_le_supp (B : Finset (Fin (n + 1))) : GA F B ≤ suppGroup (suppSet B) := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  have h1 : (SpecialLinearGroup.toGL (coordHom (F := F) (coordsOf B) A)) ∈
      coordFix (coordsOf B) := by
    intro a b hab
    exact coordHom_apply_of_not_mem (coordsOf B) A hab
  have h2 := leviSp_mem_coordFix h1
  intro r t hrt
  exact h2 r t (by simpa [suppSet] using not_and_or.mp hrt)

theorem GE_le_supp (B : Finset (Fin (n + 1))) : GE F B ≤ suppGroup (suppSet B) := by
  rintro _ ⟨g, rfl⟩
  refine suppGroup_mono ?_ (isSupp_spEmbed (sigmaOf_strictMono B).injective g)
  rintro _ ⟨y, rfl⟩
  rcases y with i | i
  · simpa [suppSet] using sigmaOf_mem B i
  · simpa [suppSet] using sigmaOf_mem B i


@[expose] noncomputable def Gb (F : Type) [Field F] (B : Finset (Fin (n + 1))) : Subgroup (StatedSp n F) :=
  if Fin.last n ∈ B then GE F B else GA F B

theorem Gb_eq {B : Finset (Fin (n + 1))} {p : Fin (n + 1)} (hB : B = blkSet I p) :
    Gb F B = leviM (rootDatum n F) (nodesOf B) := by
  unfold Gb
  split_ifs with h
  · exact GE_eq hB h
  · exact GA_eq hB h

theorem Gb_le_supp (B : Finset (Fin (n + 1))) : Gb F B ≤ suppGroup (suppSet B) := by
  unfold Gb
  split_ifs
  · exact GE_le_supp B
  · exact GA_le_supp B

theorem Gb_commute {p q : Fin (n + 1)} (h : blkSet I p ≠ blkSet I q) :
    Gb F (blkSet I p) ≤ Subgroup.centralizer (Gb F (blkSet I q) : Set (StatedSp n F)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hd := disjoint_blkSet h
  have hsub : suppSet (blkSet I q) ⊆ (suppSet (blkSet I p))ᶜ := by
    intro z hz hz'
    rcases z with i | i
    · have h1 : i ∈ coordsOf (blkSet I q) := by simpa [suppSet] using hz
      have h2 : i ∈ coordsOf (blkSet I p) := by simpa [suppSet] using hz'
      exact Finset.disjoint_left.mp hd (mem_coordsOf.mp h2) (mem_coordsOf.mp h1)
    · have h1 : i ∈ coordsOf (blkSet I q) := by simpa [suppSet] using hz
      have h2 : i ∈ coordsOf (blkSet I p) := by simpa [suppSet] using hz'
      exact Finset.disjoint_left.mp hd (mem_coordsOf.mp h2) (mem_coordsOf.mp h1)
  exact (commute_suppGroup_compl (Gb_le_supp _ hx) (suppGroup_mono hsub (Gb_le_supp _ hy))).eq.symm

end Supp


section Models

variable {n : ℕ} {F : Type} [Field F] {I : Set (Fin n)} {Y : Type} [Group Y]

theorem GA_ns [Finite F] [CharP F 2] (π : StatedSp n F →* Y)
    (hπ : Function.Injective π) (B : Finset (Fin (n + 1)))
    (hk : 3 ≤ (coordsOf B).card ∨ ((coordsOf B).card = 2 ∧ 4 ≤ Nat.card F)) :
    CFSG.IsQuasisimple ↥((GA F B).map π) ∧
      IsClassicalTwoOrG2 (↥((GA F B).map π) ⧸ Subgroup.center ↥((GA F B).map π)) :=
  chev_map_of_equiv π hπ (GA_equiv B).symm (isChevComponent_sl hk)

theorem GA_so [Finite F] (B : Finset (Fin (n + 1))) (hk : (coordsOf B).card = 2)
    (hF : Nat.card F = 2) : Group.IsSolvable ↥(GA F B) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hsolv : Group.IsSolvable (SpecialLinearGroup (Fin (coordsOf B).card) F) := by
    rw [hk]; exact CFSG.Quasithin.R3c21.S0.isSolvable_sl2_of_card_two hcard
  exact Group.isSolvable_of_isSolvable_injective (f := (GA_equiv (F := F) B).toMonoidHom)
    (GA_equiv B).injective

theorem GE_ns [Finite F] [CharP F 2] (π : StatedSp n F →* Y)
    (hπ : Function.Injective π) (B : Finset (Fin (n + 1)))
    (hk : 3 ≤ (coordsOf B).card ∨ ((coordsOf B).card = 2 ∧ 4 ≤ Nat.card F)) :
    CFSG.IsQuasisimple ↥((GE F B).map π) ∧
      IsClassicalTwoOrG2 (↥((GE F B).map π) ⧸ Subgroup.center ↥((GE F B).map π)) :=
  chev_map_of_equiv π hπ (GE_equiv B).symm (isChevComponent_sp hk)

theorem GE_ns_one [Finite F] [CharP F 2] (π : StatedSp n F →* Y)
    (hπ : Function.Injective π) (B : Finset (Fin (n + 1))) (hk : (coordsOf B).card = 1)
    (hF : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple ↥((GE F B).map π) ∧
      IsClassicalTwoOrG2 (↥((GE F B).map π) ⧸ Subgroup.center ↥((GE F B).map π)) := by
  have e := GE_equiv (F := F) B
  generalize (coordsOf B).card = k at e hk
  subst hk
  exact chev_map_of_equiv π hπ e.symm (isChevComponent_sp_one hF)

theorem GE_so [Finite F] (B : Finset (Fin (n + 1))) (hk : (coordsOf B).card = 1)
    (hF : Nat.card F = 2) : Group.IsSolvable ↥(GE F B) := by
  have e := GE_equiv (F := F) B
  generalize (coordsOf B).card = k at e hk
  subst hk
  have : Group.IsSolvable (StatedSp 1 F) :=
    CFSG.AGLEmbedding.LeviBlock.spFlag_isSolvable_Sp (Or.inr ⟨rfl, hF⟩)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

open scoped commutatorElement in
theorem GE_comm_ns [Finite F] [CharP F 2] (π : StatedSp n F →* Y)
    (hπ : Function.Injective π) (B : Finset (Fin (n + 1))) (hk : (coordsOf B).card = 2)
    (hF : Nat.card F = 2) :
    CFSG.IsQuasisimple ↥((⁅GE F B, GE F B⁆ : Subgroup (StatedSp n F)).map π) ∧
      IsClassicalTwoOrG2 (↥((⁅GE F B, GE F B⁆ : Subgroup (StatedSp n F)).map π) ⧸
        Subgroup.center ↥((⁅GE F B, GE F B⁆ : Subgroup (StatedSp n F)).map π)) := by
  have key : ∀ {k : ℕ} (σ : Fin k → Fin n) (hσ : Function.Injective σ), k = 2 →
      CFSG.IsQuasisimple ↥((⁅(spEmbed (K := F) σ hσ).range, (spEmbed (K := F) σ hσ).range⁆ :
          Subgroup (StatedSp n F)).map π) ∧
        IsClassicalTwoOrG2 (↥((⁅(spEmbed (K := F) σ hσ).range, (spEmbed (K := F) σ hσ).range⁆ :
          Subgroup (StatedSp n F)).map π) ⧸ Subgroup.center ↥((⁅(spEmbed (K := F) σ hσ).range,
          (spEmbed (K := F) σ hσ).range⁆ : Subgroup (StatedSp n F)).map π)) := by
    intro k σ hσ hk2
    subst hk2
    set φ := spEmbed (K := F) σ hσ
    have hrange : ⁅φ.range, φ.range⁆ = (commutator (StatedSp 2 F)).map φ := by
      rw [MonoidHom.range_eq_map, commutator_def, Subgroup.map_commutator]
    rw [hrange]
    exact chev_map_of_equiv π hπ ((commutator (StatedSp 2 F)).equivMapOfInjective φ
      (spEmbed_injective hσ)) (isChevComponent_comm_sp_four_two hF)
  exact key (sigmaOf B) (sigmaOf_strictMono B).injective hk

end Models


section RootFacts

variable {n : ℕ} {F : Type} [Field F]

theorem isPGroup_rootGroup_sp [CharP F 2] {γ : Fin n → ℤ}
    (hγ : γ ∈ (rootDatum n F).roots) : IsPGroup 2 ↥((rootDatum n F).rootGroup γ) := by
  have hγ' : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅ := hγ
  rw [roots_eq] at hγ'
  obtain ⟨r, hr⟩ := hγ'
  intro g
  refine ⟨1, ?_⟩
  have hg : (g : StatedSp n F) ∈ rootGroup n F γ := g.2
  obtain ⟨c, hc⟩ := (mem_rootGroup_iff hr).mp hg
  apply Subtype.ext
  show (g : StatedSp n F) ^ 2 ^ 1 = 1
  rw [hc, pow_one, sq, ← elt_add, CharTwo.add_self_eq_zero, elt_zero]

theorem eq_zero_or_eq_of_card_two [Finite F] (hF : Nat.card F = 2) {c c' : F} (hc : c ≠ 0) :
    c' = 0 ∨ c' = c := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra h
  push Not at h
  have h3 : ({0, c, c'} : Finset F).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨0, c, c', hc.symm, h.1.symm, h.2.symm, rfl⟩
  have := Finset.card_le_univ ({0, c, c'} : Finset F)
  rw [h3, ← Nat.card_eq_fintype_card, hF] at this
  omega

theorem rootGroup_cyc_sp [Finite F] (hF : Nat.card F = 2) {γ : Fin n → ℤ}
    (hγ : γ ∈ (rootDatum n F).roots) :
    ∀ y ∈ (rootDatum n F).rootGroup γ, ∀ z ∈ (rootDatum n F).rootGroup γ, y ≠ 1 →
      z = 1 ∨ z = y := by
  have hγ' : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅ := hγ
  rw [roots_eq] at hγ'
  obtain ⟨r, hr⟩ := hγ'
  intro y hy z hz hy1
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).mp hy
  obtain ⟨c', rfl⟩ := (mem_rootGroup_iff hr).mp hz
  have hc : c ≠ 0 := fun h => hy1 (by rw [h, elt_zero])
  rcases eq_zero_or_eq_of_card_two hF hc (c' := c') with h | h
  · left; rw [h, elt_zero]
  · right; rw [h]

end RootFacts


section Decomp

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

variable {n : ℕ} {F : Type} [Field F] {I : Set (Fin n)}

theorem torus_le_normalizer_rootGroup_sp {γ : Fin n → ℤ} (hγ : γ ∈ (rootDatum n F).roots) :
    (⨆ k, torus n F k) ≤ Subgroup.normalizer
      (((rootDatum n F).rootGroup γ : Subgroup (StatedSp n F)) : Set (StatedSp n F)) :=
  @iSup_le_normalizer_rootGroup (StatedSp n F) _ (rootDatum n F) (weylRep n F) (torus n F)
    (isCTGroupDatum n F) γ hγ

theorem single_mem_roots_sp (j : Fin n) : (Pi.single j 1 : Fin n → ℤ) ∈ (rootDatum n F).roots :=
  (RootSystem.ofCartan (rootDatum n F).isFiniteType (rootDatum n F).divisible).single_mem j

theorem neg_single_mem_roots_sp (j : Fin n) :
    -(Pi.single j 1 : Fin n → ℤ) ∈ (rootDatum n F).roots :=
  (RootSystem.ofCartan (rootDatum n F).isFiniteType (rootDatum n F).divisible).neg_mem _
    (single_mem_roots_sp j)

@[expose] noncomputable def Ebd (F : Type) [Field F] (J : Set (Fin n)) : Subgroup (StatedSp n F) :=
  ⨆ j ∈ J, (rootDatum n F).rootGroup (Pi.single j 1)

theorem torus_le_normalizer_Ebd (J : Set (Fin n)) :
    (⨆ k, torus n F k) ≤ Subgroup.normalizer ((Ebd F J : Subgroup (StatedSp n F)) : Set (StatedSp n F)) :=
  le_normalizer_iSup fun j => le_normalizer_iSup fun _ =>
    torus_le_normalizer_rootGroup_sp (single_mem_roots_sp j)

theorem Ebd_le_leviM (J : Set (Fin n)) : Ebd F J ≤ leviM (rootDatum n F) J :=
  iSup₂_le fun j hj => (le_sup_left : _ ≤ rankOne (rootDatum n F).rootGroup j).trans
    (rankOne_le_leviM hj)

theorem isSolvable_Ebd [Finite F] [CharP F 2] (J : Set (Fin n)) : Group.IsSolvable ↥(Ebd F J) :=
  isSolvable_iSup_simple (steinbergExtras n F) (fun _ hγ => isPGroup_rootGroup_sp hγ) J

theorem leviM_le_Ebd_sup [Finite F] [CharP F 2] (hF : Nat.card F = 2) (J : Set (Fin n))
    {G : Subgroup (StatedSp n F)} (hG : leviM (rootDatum n F) J ≤ G) :
    leviM (rootDatum n F) J ≤ Ebd F J ⊔ ⁅G, G⁆ := by
  refine iSup₂_le fun j hj => ?_
  have hLG : rankOne (rootDatum n F).rootGroup j ≤ G := (rankOne_le_leviM hj).trans hG
  have := rankOne_le_sup_commutator (isCTGroupDatum n F) (steinbergExtras n F) hLG
    (rootGroup_cyc_sp hF (neg_single_mem_roots_sp j))
  exact this.trans (sup_le_sup_right (le_iSup₂ (f := fun j (_ : j ∈ J) =>
    (rootDatum n F).rootGroup (Pi.single j 1)) j hj) _)

theorem block_decomp [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (π : StatedSp n F →* Y) (hπ : Function.Injective π) {B : Finset (Fin (n + 1))}
    {p : Fin (n + 1)} (hB : B = blkSet I p) (hne : (nodesOf B).Nonempty) :
    ∃ E C : Subgroup (StatedSp n F), E ≤ Gb F B ∧ C ≤ Gb F B ∧ Gb F B ≤ E ⊔ C ∧
      Group.IsSolvable ↥E ∧ E ≤ Subgroup.normalizer (C : Set (StatedSp n F)) ∧
      (⨆ k, torus n F k) ≤ Subgroup.normalizer (E : Set (StatedSp n F)) ∧
      (⨆ k, torus n F k) ≤ Subgroup.normalizer (C : Set (StatedSp n F)) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
  obtain ⟨i, hi⟩ := hne
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  have hct := isCTGroupDatum n F
  have hext := steinbergExtras n F
  have hT : (⨆ k, torus n F k) ≤ Subgroup.normalizer (Gb F B : Set (StatedSp n F)) := by
    rw [Gb_eq hB]
    exact torus_le_normalizer_leviM (D := rootDatum n F) (H := torus n F) (n := weylRep n F)
      (I := nodesOf B) hct
  have hF2 : Nat.card F = 2 ∨ 4 ≤ Nat.card F := by
    rw [hfcard]
    by_cases hf : f = 1
    · left; rw [hf]; norm_num
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hl : Fin.last n ∈ B
  · have hGb : Gb F B = GE F B := by simp [Gb, hl]
    have hGEeq : GE F B = leviM (rootDatum n F) (nodesOf B) := GE_eq hB hl
    rw [hGb] at hT ⊢
    have hk1 : 1 ≤ (coordsOf B).card := Finset.card_pos.mpr ⟨i, mem_coordsOf.mpr hi.1⟩
    rcases (by omega : (coordsOf B).card = 1 ∨ (coordsOf B).card = 2 ∨ 3 ≤ (coordsOf B).card)
      with h1 | h2 | h3
    · rcases hF2 with hF | hF
      · exact decomp_so π _ _ hT (GE_so B h1 hF)
      · exact decomp_ns π _ _ hT (GE_ns_one π hπ B h1 hF)
    · rcases hF2 with hF | hF
      · refine decomp_bd π _ _ (Ebd F (nodesOf B)) hT (torus_le_normalizer_Ebd _) ?_ ?_
          (isSolvable_Ebd _) (GE_comm_ns π hπ B h2 hF)
        · rw [hGEeq]; exact Ebd_le_leviM _
        · rw [hGEeq]
          exact leviM_le_Ebd_sup hF _ (by rw [← hGEeq])
      · exact decomp_ns π _ _ hT (GE_ns π hπ B (Or.inr ⟨h2, hF⟩))
    · exact decomp_ns π _ _ hT (GE_ns π hπ B (Or.inl h3))
  · have hGb : Gb F B = GA F B := by simp [Gb, hl]
    rw [hGb] at hT ⊢
    have hs : i.val + 1 < n := by
      by_contra h
      apply hl
      have : i.succ = Fin.last n := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      rw [← this]
      exact hi.2
    have hsucc : (⟨i.val + 1, hs⟩ : Fin n) ∈ coordsOf B := by
      have : (⟨i.val + 1, hs⟩ : Fin n).castSucc = i.succ := Fin.ext (by simp)
      rw [mem_coordsOf, this]; exact hi.2
    have hk2 : 2 ≤ (coordsOf B).card := by
      have := Finset.one_lt_card.mpr ⟨i, mem_coordsOf.mpr hi.1, _, hsucc,
        fun h => by have := congrArg Fin.val h; simp at this⟩
      omega
    rcases (by omega : (coordsOf B).card = 2 ∨ 3 ≤ (coordsOf B).card) with h2 | h3
    · rcases hF2 with hF | hF
      · exact decomp_so π _ _ hT (GA_so B h2 hF)
      · exact decomp_ns π _ _ hT (GA_ns π hπ B (Or.inr ⟨h2, hF⟩))
    · exact decomp_ns π _ _ hT (GA_ns π hπ B (Or.inl h3))

end Decomp


section Main

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

variable {n : ℕ} {F : Type} [Field F] {I : Set (Fin n)}

theorem leviM_mono {J J' : Set (Fin n)} (h : J ⊆ J') :
    leviM (rootDatum n F) J ≤ leviM (rootDatum n F) J' :=
  iSup₂_le fun i hi => rankOne_le_leviM (h hi)

theorem leviOb_sp [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (π : StatedSp n F →* Y) (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center (StatedSp n F))
    (I : Set (Fin n)) : LeviOb (rootDatum n F) (torus n F) π I := by
  classical
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have := hker z hz
    rwa [center_sp_eq_bot, Subgroup.mem_bot] at this
  let blocks : Finset (Finset (Fin (n + 1))) :=
    (Finset.univ.image (blkSet I)).filter fun B => (nodesOf B).Nonempty
  have hblocks : ∀ b : ↥blocks, ∃ p, b.1 = blkSet I p ∧ (nodesOf b.1).Nonempty := by
    intro b
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp b.2
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hb1
    exact ⟨p, hp.symm, hb2⟩
  have hdec : ∀ b : ↥blocks, ∃ E C : Subgroup (StatedSp n F), E ≤ Gb F b.1 ∧ C ≤ Gb F b.1 ∧
      Gb F b.1 ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧ E ≤ Subgroup.normalizer (C : Set (StatedSp n F)) ∧
      (⨆ k, torus n F k) ≤ Subgroup.normalizer (E : Set (StatedSp n F)) ∧
      (⨆ k, torus n F k) ≤ Subgroup.normalizer (C : Set (StatedSp n F)) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) := by
    intro b
    obtain ⟨p, hp, hne⟩ := hblocks b
    exact block_decomp π hπ hp hne
  choose E C hEG hCG hGEC hEs hEC hTE hTC hCq using hdec
  have hext := steinbergExtras n F
  refine leviOb_of_blocks (rootDatum n F) (torus n F) π I (fun b : ↥blocks => Gb F b.1) C E
    (Group.isSolvable_of_comm fun a b => (isMulCommutative_torus hext).is_comm.comm a b) ?_ ?_
    hEG hCG hGEC ?_ hEs hEC hTE hTC hCq
  · intro b
    obtain ⟨p, hp, -⟩ := hblocks b
    rw [Gb_eq hp, hp]
    exact leviM_mono (nodesOf_subset p)
  · refine iSup₂_le fun (i : Fin n) hi => ?_
    have hmem : blkSet I i.castSucc ∈ blocks :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
        ⟨i, mem_nodesOf_of_mem hi⟩⟩
    have hG := Gb_eq (F := F) (I := I) (B := blkSet I i.castSucc) rfl
    calc rankOne (rootDatum n F).rootGroup i ≤ leviM (rootDatum n F) (nodesOf (blkSet I i.castSucc)) :=
          rankOne_le_leviM (mem_nodesOf_of_mem hi)
      _ = Gb F (blkSet I i.castSucc) := hG.symm
      _ ≤ _ := le_iSup (fun b : ↥blocks => Gb F b.1) ⟨_, hmem⟩
  · intro b b' hbb'
    obtain ⟨p, hp, -⟩ := hblocks b
    obtain ⟨q, hq, -⟩ := hblocks b'
    have : blkSet I p ≠ blkSet I q := fun h => hbb' (Subtype.ext (by rw [hp, hq, h]))
    rw [hp, hq]
    exact Gb_commute this

theorem spLeviOb : SpLeviOb := by
  intro n f F _ _ _ _ _ Y _ π hker I _
  exact leviOb_sp π hker I

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
