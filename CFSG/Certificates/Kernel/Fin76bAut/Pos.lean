module

public import CFSG.Certificates.Kernel.Fin76bAut.Cent
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

universe u

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.E69

theorem eInnK_spec {ET T INN INE : ℕ → ℕ} {cnt ni : ℕ} (h : eInnK ET cnt T ni INN INE = true) :
    ∀ u < ni, INN u < cnt ∧ INE u < 32 ∧ (u + 1 < ni → INN u < INN (u + 1)) ∧
      ∀ x < 32, eMul ET (eG (T (INN u)) x) (INE u) = eMul ET (INE u) x := by
  intro u hu
  have h1 := allN_iff.1 h u hu
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, allN_iff] at h1
  obtain ⟨h1, h2, h3, h4⟩ := h1
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, fun hu1 => ?_,
    fun x hx => beq_t.1 (h4 x hx)⟩
  have hu1' : Nat.blt (Nat.succ u) ni = true := Nat.blt_eq.mpr hu1
  rw [bIf_eq, if_pos hu1'] at h3
  exact Nat.blt_eq.mp h3

theorem eQK_spec {T INN QC : ℕ → ℕ} {cnt ni : ℕ} (h : eQK cnt T ni INN QC = true) :
    ∀ u < ni, ∀ v < ni, QC (ni * u + v) < cnt ∧ (∀ w < ni, QC (ni * u + v) ≠ INN w) ∧
      eInvK (T (QC (ni * u + v))) = true ∧
      eC (T (QC (ni * u + v))) (T (INN u)) = eC (T (INN u)) (T (QC (ni * u + v))) ∧
      eC (T (QC (ni * u + v))) (T (INN v)) = eC (T (INN v)) (T (QC (ni * u + v))) := by
  intro u hu v hv
  have h1 := allN_iff.1 (allN_iff.1 h u hu) v hv
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, allN_iff] at h1
  obtain ⟨h1, h2, h3, h4, h5⟩ := h1
  refine ⟨Nat.le_of_ble_eq_true h1, fun w hw e => ?_, h3, beq_t.1 h4, beq_t.1 h5⟩
  have h6 := h2 w hw
  rw [bIf_eq] at h6
  split_ifs at h6 with hc
  exact hc (beq_t.2 e)

theorem tup_gen {ET : ℕ → ℕ} {GN k f c : ℕ} (htup : eTupK ET GN k f c = true) :
    (∀ j < k, eG GN j < 32) ∧ eGenK ET GN k f = true := by
  simp only [eTupK, bAnd_eq, Bool.and_eq_true, allN_iff, strictB_eq] at htup
  obtain ⟨-, hg, hgen, -⟩ := htup
  exact ⟨fun j hj => Nat.le_of_ble_eq_true (hg j hj).1, hgen⟩

theorem tup_ctr {ET : ℕ → ℕ} {GN k f c : ℕ} (htup : eTupK ET GN k f c = true) : eCtrK ET = true := by
  simp only [eTupK, bAnd_eq, Bool.and_eq_true] at htup
  exact htup.1

theorem ctr_iff {ET : ℕ → ℕ} (h : eCtrK ET = true) {x : ℕ} (hx : x < 32) :
    eZ x = true ↔ ∀ z < 32, eMul ET x z = eMul ET z x := by
  have h1 := eBEq_iff.1 ((allN_iff.1 h) x hx)
  rw [← h1, allN_iff]
  exact forall₂_congr fun z _ => eCm_iff

theorem eq_eId_of_canon {p : ℕ} (hc : canonK 32 6 63 192 p = true) (h : ∀ a < 32, eG p a = a) :
    p = eId := by
  obtain ⟨-, -, hp, -⟩ := CFSG.KS.PF.canon_facts hc
  refine CFSG.KS.PF.eq_of_fields (n := 32) (w := 6) (by norm_num) hp
    (CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)) fun a ha => ?_
  change eG p a = eG eId a
  rw [h a ha, eG_eId ha]

section Acts

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET : ℕ → ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)

@[expose] def Acts (φ : MulAut H) (p : ℕ) : Prop := ∀ a < 32, sg R φ a = eG p a

variable {R}

theorem Acts.lt {φ : MulAut H} {p : ℕ} (h : Acts R φ p) {a : ℕ} (ha : a < 32) : eG p a < 32 :=
  h a ha ▸ sg_lt R φ a

theorem Acts.elt_eq {φ : MulAut H} {p : ℕ} (h : Acts R φ p) {a : ℕ} (ha : a < 32) :
    φ (elt a) = elt (eG p a) := by
  rw [← h a ha, sg_elt R φ a]

theorem Acts.mul {φ ψ : MulAut H} {p q : ℕ} (hφ : Acts R φ p) (hψ : Acts R ψ q) :
    Acts R (φ * ψ) (eC p q) := by
  intro a ha
  rw [sg_mul, hψ a ha, hφ _ (hψ.lt ha), eG_eC p q ha]

variable (R) in
theorem acts_one : Acts R 1 eId := fun a ha => by rw [sg_one R ha, eG_eId ha]

theorem Acts.ext {φ ψ : MulAut H} {p q : ℕ} (hφ : Acts R φ p) (hψ : Acts R ψ q)
    (h : ∀ a < 32, eG p a = eG q a) : φ = ψ :=
  mulAut_ext_sg R fun a ha => (hφ a ha).trans ((h a ha).trans (hψ a ha).symm)

theorem Acts.eq_one_iff {φ : MulAut H} {p : ℕ} (h : Acts R φ p) (hc : canonK 32 6 63 192 p = true) :
    φ = 1 ↔ p = eId := by
  constructor
  · rintro rfl
    exact eq_eId_of_canon hc fun a ha => by rw [← h a ha, sg_one R ha]
  · rintro rfl
    exact h.ext (acts_one R) fun _ _ => rfl

theorem Acts.sq_iff {φ : MulAut H} {p : ℕ} (h : Acts R φ p) :
    φ * φ = 1 ↔ ∀ a < 32, eG p (eG p a) = a := by
  constructor
  · intro e a ha
    rw [← eG_eC p p ha, ← h.mul h a ha, e, sg_one R ha]
  · intro e
    exact (h.mul h).ext (acts_one R) fun a ha => by rw [eG_eC p p ha, e a ha, eG_eId ha]

theorem Acts.eInvK_iff {φ : MulAut H} {p : ℕ} (h : Acts R φ p)
    (hc : canonK 32 6 63 192 p = true) : eInvK p = true ↔ φ * φ = 1 ∧ φ ≠ 1 := by
  rw [h.sq_iff, ne_eq, h.eq_one_iff hc]
  exact ⟨eInvK_spec, fun ⟨h1, h2⟩ => eInvK_of hc h1 h2⟩

include hM

theorem Acts.comm_iff {GN k f c : ℕ} (htup : eTupK ET GN k f c = true) {φ ψ : MulAut H}
    {p q : ℕ} (hφ : Acts R φ p) (hψ : Acts R ψ q) :
    φ * ψ = ψ * φ ↔ eCommG GN k p q = true := by
  obtain ⟨hS, hgen⟩ := tup_gen htup
  unfold eCommG
  rw [allN_iff]
  constructor
  · intro e d hd
    rw [strictB_eq]
    apply beq_t.2
    rw [← eG_eC p q (hS d hd), ← eG_eC q p (hS d hd), ← hφ.mul hψ _ (hS d hd),
      ← hψ.mul hφ _ (hS d hd), e]
  · intro e
    refine mulAut_ext_sg R (sg_eq_of_gen R hM hS hgen _ _ fun d hd => ?_)
    have h1 := e d hd
    rw [strictB_eq] at h1
    rw [hφ.mul hψ _ (hS d hd), hψ.mul hφ _ (hS d hd), eG_eC _ _ (hS d hd), eG_eC _ _ (hS d hd)]
    exact beq_t.1 h1

theorem Acts.eInvG_iff {GN k f c : ℕ} (htup : eTupK ET GN k f c = true) {φ : MulAut H} {p : ℕ}
    (h : Acts R φ p) (hc : canonK 32 6 63 192 p = true) :
    eInvG GN k p = true ↔ φ * φ = 1 ∧ φ ≠ 1 := by
  obtain ⟨hS, hgen⟩ := tup_gen htup
  unfold eInvG
  rw [bAnd_eq, Bool.and_eq_true, allN_iff, bIf_eq, ne_eq, h.eq_one_iff hc]
  have hne : (if Nat.beq p eId = true then false else true) = true ↔ ¬ p = eId := by
    split_ifs with he
    · simpa using beq_t.1 he
    · simpa [beq_t] using he
  rw [hne]
  refine and_congr_left fun _ => ⟨fun e => ?_, fun e d hd => ?_⟩
  · refine mulAut_ext_sg R (sg_eq_of_gen R hM hS hgen _ _ fun d hd => ?_)
    have h1 := e d hd
    rw [strictB_eq] at h1
    rw [(h.mul h) _ (hS d hd), eG_eC _ _ (hS d hd), beq_t.1 h1, sg_one R (hS d hd)]
  · rw [strictB_eq]
    exact beq_t.2 ((h.sq_iff.1 e) _ (hS d hd))

end Acts

section Pos

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)

structure PosData (T : ℕ → ℕ) (cnt : ℕ) (Φ : ℕ → MulAut H) : Prop where
  acts : ∀ i < cnt, Acts R (Φ i) (T i)
  surj : ∀ φ : MulAut H, ∃ i < cnt, Φ i = φ
  inj : ∀ i < cnt, ∀ j < cnt, Φ i = Φ j → i = j

variable {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)

include hM in
theorem exists_posData (hrec : RecOK.{u} ET cnt T) : ∃ Φ : ℕ → MulAut H, PosData R T cnt Φ := by
  classical
  have := finite_mulAut R
  have : Fintype (MulAut H) := Fintype.ofFinite _
  obtain ⟨hall, hex, hcard⟩ := hrec H M elt R hM
  choose! Φ hΦ using hex
  have hsurj : ∀ φ : MulAut H, ∃ i < cnt, Φ i = φ := by
    intro φ
    obtain ⟨i, hi, h⟩ := hall φ
    exact ⟨i, hi, mulAut_ext_sg R fun a ha => (hΦ i hi a ha).trans (h a ha).symm⟩
  have himg : (Finset.range cnt).image Φ = Finset.univ := by
    refine Finset.eq_univ_of_forall fun φ => ?_
    obtain ⟨i, hi, h⟩ := hsurj φ
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, h⟩
  have hinj : Set.InjOn Φ (Finset.range cnt) := Finset.card_image_iff.1 (by
    rw [himg, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, Finset.card_range])
  exact ⟨Φ, ⟨hΦ, hsurj, fun i hi j hj e =>
    hinj (Finset.mem_coe.2 (Finset.mem_range.2 hi)) (Finset.mem_coe.2 (Finset.mem_range.2 hj)) e⟩⟩

include R hM in
theorem card_inn (hc : eCtrK ET = true) :
    Nat.card ↥(MulAut.conj : H →* MulAut H).range = 16 := by
  classical
  have hker : ((MulAut.conj : H →* MulAut H).ker : Set H) = {elt 0, elt 21} := by
    ext g
    obtain ⟨k, hk, rfl⟩ := R.surj g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    have e1 : MulAut.conj (elt k) = 1 ↔ ∀ z < 32, eMul ET k z = eMul ET z k := by
      constructor
      · intro e z hz
        have h1 := congrArg (fun φ : MulAut H => φ (elt z)) e
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        have h2 : elt k * elt z = elt z * elt k := mul_inv_eq_iff_eq_mul.1 h1
        apply R.inj _ _ (tmul_lt R hM hk hz) (tmul_lt R hM hz hk)
        rw [← hM k hk z hz, ← hM z hz k hk, R.mul _ _ hk hz, R.mul _ _ hz hk, h2]
      · intro e
        refine MulEquiv.ext fun x => ?_
        obtain ⟨z, hz, rfl⟩ := R.surj x
        simp only [MulAut.conj_apply, MulAut.one_apply]
        have h2 : elt k * elt z = elt z * elt k := by
          rw [← R.mul _ _ hk hz, ← R.mul _ _ hz hk, hM k hk z hz, hM z hz k hk, e z hz]
        rw [h2, mul_inv_cancel_right]
    rw [e1, ← ctr_iff hc hk]
    constructor
    · intro h
      rcases eZ_spec h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · rw [R.inj _ _ hk (by norm_num) h]
        rfl
      · rw [R.inj _ _ hk (by norm_num) h]
        rfl
  have h01 : elt 0 ≠ elt 21 := fun e => absurd (R.inj _ _ (by norm_num) (by norm_num) e) (by norm_num)
  have hk2 : Nat.card ↥(MulAut.conj : H →* MulAut H).ker = 2 := by
    have e2 : Nat.card ↥(MulAut.conj : H →* MulAut H).ker =
        ((MulAut.conj : H →* MulAut H).ker : Set H).ncard := Nat.card_coe_set_eq _
    rw [e2, hker, Set.ncard_pair h01]
  have hH : Nat.card H = 32 := by
    have hb : Function.Bijective fun i : Fin 32 => elt i :=
      ⟨fun a b e => Fin.ext (R.inj _ _ a.2 b.2 e), fun x => by
        obtain ⟨k, hk, rfl⟩ := R.surj x
        exact ⟨⟨k, hk⟩, rfl⟩⟩
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAut.conj : H →* MulAut H).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAut.conj : H →* MulAut H)).toEquiv,
    hk2, hH] at hq
  omega

variable {Φ : ℕ → MulAut H}

include hM in
theorem inn_iff (pd : PosData R T cnt Φ) (hc : eCtrK ET = true) {INN INE : ℕ → ℕ}
    (hinn : eInnK ET cnt T 16 INN INE = true) (φ : MulAut H) :
    φ ∈ (MulAut.conj : H →* MulAut H).range ↔ ∃ u < 16, Φ (INN u) = φ := by
  classical
  have := finite_mulAut R
  have hs := eInnK_spec hinn
  have hconj : ∀ u < 16, Φ (INN u) = MulAut.conj (elt (INE u)) := by
    intro u hu
    obtain ⟨hi, he, -, hx⟩ := hs u hu
    have hA := pd.acts _ hi
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, hx32, rfl⟩ := R.surj y
    rw [hA.elt_eq hx32, MulAut.conj_apply, eq_mul_inv_iff_mul_eq, ← R.mul _ _ (hA.lt hx32) he,
      ← R.mul _ _ he hx32, hM _ (hA.lt hx32) _ he, hM _ he _ hx32, hx x hx32]
  have hmono : ∀ i j, i < j → j < 16 → INN i < INN j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
      · exact lt_trans (ih h' (by omega)) ((hs j (by omega)).2.2.1 hj)
      · subst h'
        exact (hs i (by omega)).2.2.1 hj
  have hinj : Set.InjOn (fun u => Φ (INN u)) (Finset.range 16) := by
    intro i hi j hj e
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have := pd.inj _ (hs i hi').1 _ (hs j hj').1 e
    rcases Nat.lt_trichotomy i j with h' | h' | h'
    · exact absurd this (Nat.ne_of_lt (hmono i j h' hj'))
    · exact h'
    · exact absurd this.symm (Nat.ne_of_lt (hmono j i h' hi'))
  let F := (Finset.range 16).image fun u => Φ (INN u)
  have hsub : (F : Set (MulAut H)) ⊆ ((MulAut.conj : H →* MulAut H).range : Set (MulAut H)) := by
    intro ψ hψ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hψ
    exact ⟨_, (hconj u (Finset.mem_range.1 hu)).symm⟩
  have e2 : ((MulAut.conj : H →* MulAut H).range : Set (MulAut H)).ncard =
      Nat.card ↥(MulAut.conj : H →* MulAut H).range := (Nat.card_coe_set_eq _).symm
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_range, e2,
      card_inn R hM hc]) (Set.toFinite _)
  constructor
  · intro hφ
    have hφ' : φ ∈ (F : Set (MulAut H)) := by rw [heq]; exact hφ
    obtain ⟨u, hu, e⟩ := Finset.mem_image.1 hφ'
    exact ⟨u, Finset.mem_range.1 hu, e⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, (hconj u hu).symm⟩

end Pos

end CFSG.KS.EAut

end
