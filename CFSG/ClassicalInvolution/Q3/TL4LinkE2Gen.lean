module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2K
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lift

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkE2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent AEIdentOn ThmDHyp)

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {r : ℕ}

theorem commutes_of_le (hD : ThmDHyp r Φ) {L M : Subgroup X} (hL : L ∈ Φ) (hM : M ∈ Φ)
    (hne : L ≠ M) {Q : Subgroup X} (hQ : IsPGroup 2 ↥Q) (hLQ : L ≤ Q) (hMQ : M ≤ Q) :
    Commutes L M := by
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  exact Q3CP.l67Gen X _ hD.hyp P L
    (mem_RSet_of_isSylow2In hL (AlphaFr.E2A.isSylow2In_self (hD.two L hL))) M
    (mem_RSet_of_isSylow2In hM (AlphaFr.E2A.isSylow2In_self (hD.two M hM))) (hLQ.trans hP)
    (hMQ.trans hP) hne

omit [Finite X] in
theorem coe_mem_center (hD : ThmDHyp r Φ) {x : ↥(pSpan Φ)}
    (hx : x ∈ Subgroup.center ↥(pSpan Φ)) : (x : X) ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  have hy : y ∈ pSpan Φ := by
    rw [hD.gen]
    exact Subgroup.mem_top y
  exact congrArg Subtype.val (hx ⟨y, hy⟩)

theorem isPGroup_ker (hD : ThmDHyp r Φ) {m : ℕ} {φ : ↥(pSpan Φ) →* AE.AEQ m}
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ)) : IsPGroup 2 ↥φ.ker := by
  intro k
  obtain ⟨j, hj⟩ := isPGroup_center_of_corefree hD.odd ⟨_, coe_mem_center hD (hker k.2)⟩
  refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hj
  simpa using this

omit [Finite X] in
theorem isPGroup_memBar (hD : ThmDHyp r Φ) {m : ℕ} (φ : ↥(pSpan Φ) →* AE.AEQ m)
    {L : Subgroup X} (hL : L ∈ Φ) {α : Finset (Fin m)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b) :
    IsPGroup 2 ↥(AE.memBar α h b) := by
  rw [← hlab]
  exact (hD.two L hL).comap_subtype.map φ

theorem commutes_of_disjoint_labels (hD : ThmDHyp r Φ) {m : ℕ} (φ : ↥(pSpan Φ) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ)) {L M : Subgroup X} (hL : L ∈ Φ) (hM : M ∈ Φ)
    (hne : L ≠ M) {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4} {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan Φ)).map φ = AE.memBar β h' b') (hdisj : Disjoint α β) :
    Commutes L M := by
  have hcomm := AE.comm_memBar_of_disjoint (h := h) (h' := h') hdisj b b'
  have hN : AE.memBar α h b ≤ Subgroup.normalizer (AE.memBar β h' b' : Set (AE.AEQ m)) :=
    fun x hx => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)
  have hsup := (isPGroup_memBar hD φ hL hlab).to_sup_of_normal_right'
    (isPGroup_memBar hD φ hM hlab') hN
  have hQ := (hsup.comap_of_ker_isPGroup φ (isPGroup_ker hD hker)).map (pSpan Φ).subtype
  refine commutes_of_le hD hL hM hne hQ ?_ ?_
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

omit [Finite X] in
theorem ne_of_disjoint_labels {m : ℕ} (φ : ↥(pSpan Φ) →* AE.AEQ m) {L M : Subgroup X}
    {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4} {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan Φ)).map φ = AE.memBar β h' b') (hdisj : Disjoint α β) :
    L ≠ M := by
  intro e
  rw [e] at hlab
  exact AE.memBar_ne_of_disjoint hdisj b b' (hlab.symm.trans hlab')

theorem mem_omegaNbr_of_disjoint_labels (hD : ThmDHyp r Φ) {m : ℕ}
    (φ : ↥(pSpan Φ) →* AE.AEQ m) (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ)) {L M : Subgroup X}
    (hL : L ∈ Φ) (hM : M ∈ Φ) {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4}
    {b b' : Bool} (hlab : (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan Φ)).map φ = AE.memBar β h' b') (hdisj : Disjoint α β) :
    M ∈ omegaNbr Φ L :=
  have hne := ne_of_disjoint_labels φ hlab hlab' hdisj
  mem_omegaNbr_of_commutes hM (Ne.symm hne)
    (commutes_of_disjoint_labels hD φ hker hL hM hne hlab hlab' hdisj)

theorem two_nbrs_of_labels (hD : ThmDHyp r Φ) {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan Φ) →* AE.AEQ m) (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    {A B C : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ Φ) (hC : C ∈ Φ) {α β : Finset (Fin m)}
    {h : α.card = 4} {h' : β.card = 4} {b : Bool} (hdisj : Disjoint α β)
    (hlabA : (A.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hlabB : (B.subgroupOf (pSpan Φ)).map φ = AE.memBar β h' true)
    (hlabC : (C.subgroupOf (pSpan Φ)).map φ = AE.memBar β h' false) :
    B ∈ omegaNbr Φ A ∧ C ∈ omegaNbr Φ A ∧ B ≠ C := by
  refine ⟨mem_omegaNbr_of_disjoint_labels hD φ hker hA hB hlabA hlabB hdisj,
    mem_omegaNbr_of_disjoint_labels hD φ hker hA hC hlabA hlabC hdisj, fun e => ?_⟩
  rw [e] at hlabB
  exact AE.memBar_true_ne_false hm β h' (hlabB.symm.trans hlabC)

theorem exists_two_nbrs_of_aeIdent (hD : ThmDHyp r Φ) {m : ℕ} (hm : 8 ≤ m) (I : AEIdent Φ m) :
    ∃ A ∈ Φ, ∃ B ∈ omegaNbr Φ A, ∃ C ∈ omegaNbr Φ A, B ≠ C := by
  obtain ⟨α, -, hα⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ : Finset (Fin m)).card by
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
  obtain ⟨β, hβ, hdisj⟩ := AlphaFr.E2A.exists_disjoint hm α hα
  obtain ⟨A, hA, hlabA⟩ := I.label_surj α hα true
  obtain ⟨B, hB, hlabB⟩ := I.label_surj β hβ true
  obtain ⟨C, hC, hlabC⟩ := I.label_surj β hβ false
  obtain ⟨h1, h2, h3⟩ :=
    two_nbrs_of_labels hD (by omega) I.φ I.ker_le hA hB hC hdisj hlabA hlabB hlabC
  exact ⟨A, hA, B, h1, C, h2, h3⟩

theorem exists_two_nbrs_of_e29 (hD : ThmDHyp r Φ) (I : AEIdentOn Φ 8 AE.e29Sets AE.e29Sub)
    {L : Subgroup X} (hL : L ∈ Φ) : ∃ A ∈ Φ, ∃ B ∈ omegaNbr Φ A, ∃ C ∈ omegaNbr Φ A, B ≠ C := by
  obtain ⟨α, hα𝒜, hα, b, hlabA⟩ := I.label L hL
  have hc : αᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  have hc𝒜 := AE.e29Sets_compl hα𝒜
  obtain ⟨B, hB, hlabB⟩ := I.label_surj αᶜ hc𝒜 hc true
  obtain ⟨C, hC, hlabC⟩ := I.label_surj αᶜ hc𝒜 hc false
  obtain ⟨h1, h2, h3⟩ := two_nbrs_of_labels hD (by norm_num) I.φ I.ker_le hL hB hC
    disjoint_compl_right hlabA hlabB hlabC
  exact ⟨L, hL, B, h1, C, h2, h3⟩

theorem nonempty_aeIdent_of_restrict {Z : Type} [Group Z] {P : Set (Subgroup Z)}
    {H : Subgroup Z} (hH : pSpan P = H) {n : ℕ} (I : AEIdent (restrictFamily P H) n) :
    Nonempty (AEIdent P n) := by
  have hgen : pSpan (restrictFamily P H) = ⊤ := omegaGen_restrictFamily_eq_top P H hH
  let e : ↥(pSpan P) ≃* ↥(pSpan (restrictFamily P H)) :=
    (MulEquiv.subgroupCongr hH).trans
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgen.symm))
  have he : ∀ x : ↥(pSpan P), (((e x : ↥(pSpan (restrictFamily P H))) : ↥H) : Z) = (x : Z) :=
    fun x => rfl
  have hmap : ∀ L : Subgroup Z, L ≤ H → (L.subgroupOf (pSpan P)).map e.toMonoidHom =
      (L.subgroupOf H).subgroupOf (pSpan (restrictFamily P H)) := by
    intro L _
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show (((e x : ↥(pSpan (restrictFamily P H))) : ↥H) : Z) ∈ L
      rw [he]
      exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have h1 := he (e.symm y)
      rw [e.apply_symm_apply] at h1
      show ((e.symm y : ↥(pSpan P)) : Z) ∈ L
      rw [← h1]
      exact hy
  refine ⟨⟨I.φ.comp e.toMonoidHom, ?_, ?_, ?_, ?_⟩⟩
  · rw [← I.range_eq]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simp⟩
  · intro x hx
    have hz := I.ker_le (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    exact hz (e g)
  · intro L hL
    have hLH : L ≤ H := (le_pSpan hL).trans hH.le
    obtain ⟨α, h, b, hlab⟩ := I.label _ ⟨L, hL, hLH, rfl⟩
    exact ⟨α, h, b, by rw [← Subgroup.map_map, hmap L hLH, hlab]⟩
  · intro α h b
    obtain ⟨L', ⟨L, hL, hLH, rfl⟩, hlab⟩ := I.label_surj α h b
    exact ⟨L, hL, by rw [← Subgroup.map_map, hmap L hLH, hlab]⟩

end CFSG.ClassicalInvolution.Q3.TL4.LinkE2
