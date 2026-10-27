module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2A

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj dAdj_of_commutes)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent)

section Kneser

variable {m : ℕ}

theorem exists_disjoint (hm : 8 ≤ m) (α : Finset (Fin m)) (hα : α.card = 4) :
    ∃ δ : Finset (Fin m), δ.card = 4 ∧ Disjoint α δ := by
  have hc : 4 ≤ αᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, hα]
    omega
  obtain ⟨δ, hδsub, hδ⟩ := Finset.exists_subset_card_eq hc
  exact ⟨δ, hδ, Finset.disjoint_of_subset_right hδsub disjoint_compl_right⟩

theorem kneser_reflTransGen (hm : 9 ≤ m) : ∀ (k : ℕ) (α β : Finset (Fin m)), α.card = 4 →
    β.card = 4 → (α \ β).card = k →
      Relation.ReflTransGen (fun γ δ : Finset (Fin m) => δ.card = 4 ∧ Disjoint γ δ) α β := by
  intro k
  induction k with
  | zero =>
    intro α β hα hβ hk
    have hsub : α ⊆ β := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hk)
    have hαβ : α = β := Finset.eq_of_subset_of_card_le hsub (by rw [hα, hβ])
    rw [hαβ]
  | succ k ih =>
    intro α β hα hβ hk
    obtain ⟨a, ha⟩ : (α \ β).Nonempty := Finset.card_pos.mp (by rw [hk]; omega)
    have hba : (β \ α).card = k + 1 := by
      have h1 := Finset.card_sdiff_add_card_inter α β
      have h2 := Finset.card_sdiff_add_card_inter β α
      rw [Finset.inter_comm] at h2
      omega
    obtain ⟨b, hb⟩ : (β \ α).Nonempty := Finset.card_pos.mp (by rw [hba]; omega)
    rw [Finset.mem_sdiff] at ha hb
    have hbα' : b ∉ α.erase a := fun h => hb.2 (Finset.mem_of_mem_erase h)
    have hα' : (insert b (α.erase a)).card = 4 := by
      rw [Finset.card_insert_of_notMem hbα', Finset.card_erase_of_mem ha.1, hα]
    have hk' : (insert b (α.erase a) \ β).card = k := by
      have he : insert b (α.erase a) \ β = (α \ β).erase a := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hx | ⟨hxa, hxα⟩, hxβ⟩
          · exact absurd (hx ▸ hb.1) hxβ
          · exact ⟨hxa, hxα, hxβ⟩
        · rintro ⟨hxa, hxα, hxβ⟩
          exact ⟨Or.inr ⟨hxa, hxα⟩, hxβ⟩
      rw [he, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ha), hk]
      omega
    have hU : (α ∪ insert b (α.erase a)).card ≤ 5 := by
      have hsub : α ∪ insert b (α.erase a) ⊆ insert b α := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hx ⊢
        tauto
      calc (α ∪ insert b (α.erase a)).card ≤ (insert b α).card := Finset.card_le_card hsub
        _ ≤ α.card + 1 := Finset.card_insert_le b α
        _ = 5 := by rw [hα]
    have hc : 4 ≤ (α ∪ insert b (α.erase a))ᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨γ, hγsub, hγ⟩ := Finset.exists_subset_card_eq hc
    have hdγ : Disjoint (α ∪ insert b (α.erase a)) γ :=
      Finset.disjoint_of_subset_right hγsub disjoint_compl_right
    have h1 : Disjoint α γ := Finset.disjoint_of_subset_left Finset.subset_union_left hdγ
    have h2 : Disjoint γ (insert b (α.erase a)) :=
      (Finset.disjoint_of_subset_left Finset.subset_union_right hdγ).symm
    exact ((Relation.ReflTransGen.single ⟨hγ, h1⟩).tail ⟨hα', h2⟩).trans
      (ih _ β hα' hβ hk')

end Kneser

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem coe_mem_center (hc : TightCls Y R S t)
    {x : ↥(pSpan (CoreAssembly.conjClass (tightCore R)))}
    (hx : x ∈ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R)))) :
    (x : Y) ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  have hy : y ∈ pSpan (CoreAssembly.conjClass (tightCore R)) := by
    rw [E2D.pSpan_eq_top hc]
    exact Subgroup.mem_top y
  exact congrArg Subtype.val (hx ⟨y, hy⟩)

theorem isPGroup_ker (hc : TightCls Y R S t) {m : ℕ}
    {φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m}
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R)))) :
    IsPGroup 2 ↥φ.ker := by
  intro k
  obtain ⟨j, hj⟩ := isPGroup_center_of_corefree hc.2.2 ⟨_, coe_mem_center hc (hker k.2)⟩
  refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hj
  simpa using this

theorem isPGroup_memBar (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    {m : ℕ} (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {α : Finset (Fin m)}
    {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b) : IsPGroup 2 ↥(AE.memBar α h b) := by
  rw [← hlab]
  exact (E2D.isPGroup_mem hd hc hO2 L hL).comap_subtype.map φ

theorem commutes_of_disjoint_labels (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ}
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    {L M : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) (hne : L ≠ M) {α β : Finset (Fin m)}
    {h : α.card = 4} {h' : β.card = 4} {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar β h' b')
    (hdisj : Disjoint α β) : Commutes L M := by
  have hcomm := AE.comm_memBar_of_disjoint (h := h) (h' := h') hdisj b b'
  have hN : AE.memBar α h b ≤ Subgroup.normalizer (AE.memBar β h' b' : Set (AE.AEQ m)) :=
    fun x hx => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)
  have hsup := (isPGroup_memBar hd hc hO2 φ hL hlab).to_sup_of_normal_right'
    (isPGroup_memBar hd hc hO2 φ hM hlab') hN
  have hQ := (hsup.comap_of_ker_isPGroup φ (isPGroup_ker hc hker)).map
    (pSpan (CoreAssembly.conjClass (tightCore R))).subtype
  refine commutes_of_le hd hc hO2 hL hM hne hQ ?_ ?_
  · intro x hx
    refine ⟨⟨x, le_pSpan hL hx⟩, ?_, rfl⟩
    have hm : φ ⟨x, le_pSpan hL hx⟩ ∈ AE.memBar α h b := by
      rw [← hlab]
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_sup_left hm
  · intro x hx
    refine ⟨⟨x, le_pSpan hM hx⟩, ?_, rfl⟩
    have hm : φ ⟨x, le_pSpan hM hx⟩ ∈ AE.memBar β h' b' := by
      rw [← hlab']
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_sup_right hm

theorem exists_isUniqueInvolution (hd : TightDatum R S t) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) : ∃ u : Y, IsUniqueInvolution L u := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨_, hd.isUniqueInvolution_core.conj g⟩

theorem ne_of_disjoint_labels (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m) {L M : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {α β : Finset (Fin m)} {h : α.card = 4}
    {h' : β.card = 4} {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar β h' b')
    (hdisj : Disjoint α β) : L ≠ M := by
  intro hLM
  rw [← hLM] at hlab'
  obtain ⟨u, hu⟩ := exists_isUniqueInvolution hd hL
  have h8 : Nat.card ↥L = 8 := (E2D.card_mem hd hc hO2 L hL).trans (by norm_num)
  have hab : α = β := AE.eq_of_zBar_eq hm8
    ((TC.Thin.phi_map_eq_zBar φ hm hL h8 hlab hu).symm.trans
      (TC.Thin.phi_map_eq_zBar φ hm hL h8 hlab' hu))
  subst hab
  have he := (Finset.disjoint_self_iff_empty _).mp hdisj
  subst he
  simp at h

theorem dAdj_of_disjoint_labels (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    {L M : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) {α β : Finset (Fin m)} {h : α.card = 4}
    {h' : β.card = 4} {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar β h' b')
    (hdisj : Disjoint α β) : dAdj (CoreAssembly.conjClass (tightCore R)) L M :=
  have hne := ne_of_disjoint_labels hd hc hO2 hm hm8 φ hL hlab hlab' hdisj
  dAdj_of_commutes hM hne (commutes_of_disjoint_labels hd hc hO2 φ hker hL hM hne hlab hlab' hdisj)

theorem dConnected_of_aeIdent (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 9 ≤ m)
    (I : AEIdent (CoreAssembly.conjClass (tightCore R)) m) :
    DConnected (CoreAssembly.conjClass (tightCore R)) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩ
  have hadj : ∀ {L M : Subgroup Y}, L ∈ Ω → M ∈ Ω → ∀ {α β : Finset (Fin m)} {h : α.card = 4}
      {h' : β.card = 4} {b b' : Bool}, (L.subgroupOf (pSpan Ω)).map I.φ = AE.memBar α h b →
      (M.subgroupOf (pSpan Ω)).map I.φ = AE.memBar β h' b' → Disjoint α β →
      Relation.ReflTransGen (fun M N : Subgroup Y => N ∈ Ω ∧ dAdj Ω M N) L M := by
    intro L M hL hM α β h h' b b' hlab hlab' hdisj
    exact Relation.ReflTransGen.single ⟨hM, dAdj_of_disjoint_labels hd hc hO2 (by omega)
      (by omega) I.φ I.ker_le hL hM hlab hlab' hdisj⟩
  intro K hK J hJ
  obtain ⟨α, h, b, hlab⟩ := I.label K hK
  obtain ⟨β, h', b', hlab'⟩ := I.label J hJ
  have hcard : ∀ γ, Relation.ReflTransGen
      (fun γ δ : Finset (Fin m) => δ.card = 4 ∧ Disjoint γ δ) α γ → γ.card = 4 := by
    intro γ hγ
    induction hγ with
    | refl => exact h
    | tail _ hst _ => exact hst.1
  have key : ∀ γ, Relation.ReflTransGen
      (fun γ δ : Finset (Fin m) => δ.card = 4 ∧ Disjoint γ δ) α γ →
      ∀ (hγ : γ.card = 4) (c : Bool) (N : Subgroup Y), N ∈ Ω →
        (N.subgroupOf (pSpan Ω)).map I.φ = AE.memBar γ hγ c →
          Relation.ReflTransGen (fun M N : Subgroup Y => N ∈ Ω ∧ dAdj Ω M N) K N := by
    intro γ hpath
    induction hpath with
    | refl =>
      intro hγ c N hN hlabN
      obtain ⟨δ, hδ, hαδ⟩ := exists_disjoint (by omega) α h
      obtain ⟨N', hN', hlabN'⟩ := I.label_surj δ hδ true
      exact (hadj hK hN' hlab hlabN' hαδ).trans (hadj hN' hN hlabN' hlabN hαδ.symm)
    | tail hαγ hγδ ih =>
      intro hδ c N hN hlabN
      obtain ⟨N', hN', hlabN'⟩ := I.label_surj _ (hcard _ hαγ) true
      exact (ih (hcard _ hαγ) true N' hN' hlabN').trans (hadj hN' hN hlabN' hlabN hγδ.2)
  exact key β (kneser_reflTransGen hm _ α β h h' rfl) h' b' J hJ hlab'

end CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2A
