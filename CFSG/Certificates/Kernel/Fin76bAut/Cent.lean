module

public import CFSG.Certificates.Kernel.Fin76bAut.Dict
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E614Def
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

universe u

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.E69

theorem eG_eId {a : ℕ} (ha : a < 32) : eG eId a = a :=
  CFSG.KS.PF.pg_pidn (n := 32) (w := 6) (by norm_num) (by norm_num) ha

theorem eC_eq_eId {p : ℕ} (h : ∀ a < 32, eG p (eG p a) = a) : eC p p = eId := by
  refine CFSG.KS.PF.eq_of_fields (n := 32) (w := 6) (by norm_num)
    (CFSG.KS.PF.pcomp_shr p p (by norm_num) (by norm_num))
    (CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)) fun a ha => ?_
  change eG (eC p p) a = eG eId a
  rw [eG_eC p p ha, h a ha, eG_eId ha]

theorem eInvK_spec {p : ℕ} (h : eInvK p = true) : (∀ a < 32, eG p (eG p a) = a) ∧ p ≠ eId := by
  unfold eInvK sqIdK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨⟨-, hsq⟩, hne⟩ := h
  have e1 : eC p p = eId := beq_t.1 hsq
  refine ⟨fun a ha => by rw [← eG_eC p p ha, e1, eG_eId ha], fun e => ?_⟩
  rw [e, bIf_eq, if_pos (beq_t.2 rfl)] at hne
  exact Bool.false_ne_true hne

theorem eInvK_of {p : ℕ} (hc : canonK 32 6 63 192 p = true) (hsq : ∀ a < 32, eG p (eG p a) = a)
    (hne : p ≠ eId) : eInvK p = true := by
  unfold eInvK sqIdK
  simp only [bAnd_eq, Bool.and_eq_true]
  refine ⟨⟨hc, beq_t.2 (eC_eq_eId hsq)⟩, ?_⟩
  rw [bIf_eq, if_neg fun e => hne (beq_t.1 e)]

theorem eClsK_spec {cnt nr nv : ℕ} {T REP IV ICL ICJ : ℕ → ℕ}
    (h : eClsK cnt T nr REP nv IV ICL ICJ = true) :
    eCnt cnt (fun i => eInvK (T i)) = nv ∧
      ∀ q < nv, IV q < cnt ∧ ICL q < nr ∧ ICJ q < cnt ∧ eInvK (T (IV q)) = true ∧
        (q + 1 < nv → IV q < IV (q + 1)) ∧
        eC (T (ICJ q)) (T (REP (ICL q))) = eC (T (IV q)) (T (ICJ q)) := by
  unfold eClsK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨-, hc, hq⟩ := h
  refine ⟨beq_t.1 hc, fun q hq' => ?_⟩
  have h1 := allN_iff.1 hq q hq'
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h1
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3, h4,
    fun hq1 => ?_, beq_t.1 h6⟩
  have hq1' : Nat.blt (Nat.succ q) nv = true := Nat.blt_eq.mpr hq1
  rw [bIf_eq, if_pos hq1'] at h5
  exact Nat.blt_eq.mp h5

theorem e614K_spec {GN k cnt nr : ℕ} {T REP : ℕ → ℕ} (h : e614K GN k cnt T nr REP = true) :
    ∀ r < nr, eCnt cnt (fun i => eCommG GN k (T i) (T (REP r))) % 32 = 0 := by
  intro r hr
  have h1 := allN_iff.1 h r hr
  rw [strictB_eq] at h1
  exact beq_t.1 h1

theorem all_of_sorted {n m : ℕ} {f : ℕ → Bool} {V : ℕ → ℕ} (hcnt : eCnt n f = m)
    (hV : ∀ q < m, V q < n ∧ f (V q) = true ∧ (q + 1 < m → V q < V (q + 1))) :
    ∀ x < n, f x = true → ∃ q < m, V q = x := by
  classical
  have hmono : ∀ i j, i < j → j < m → V i < V j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
      · exact lt_trans (ih h' (by omega)) ((hV j (by omega)).2.2 hj)
      · subst h'
        exact (hV i (by omega)).2.2 hj
  have hinj : Set.InjOn V (Finset.range m) := by
    intro i hi j hj e
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    rcases Nat.lt_trichotomy i j with h' | h' | h'
    · exact absurd e (Nat.ne_of_lt (hmono i j h' hj'))
    · exact h'
    · exact absurd e.symm (Nat.ne_of_lt (hmono j i h' hi'))
  have hsub : (Finset.range m).image V ⊆ (Finset.range n).filter fun i => f i = true := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, h2, -⟩ := hV q (Finset.mem_range.1 hq)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← hcnt, eCnt_eq_card])
  intro x hx hf
  have hmem : x ∈ (Finset.range m).image V := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, hf⟩
  obtain ⟨q, hq, e⟩ := Finset.mem_image.1 hmem
  exact ⟨q, Finset.mem_range.1 hq, e⟩

theorem card_centralizer_conj {Γ : Type*} [Group Γ] {χ ρ ψ : Γ} (h : χ * ρ = ψ * χ) :
    Nat.card ↥(Subgroup.centralizer ({ψ} : Set Γ)) =
      Nat.card ↥(Subgroup.centralizer ({ρ} : Set Γ)) := by
  obtain rfl : ρ = χ⁻¹ * ψ * χ := by rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
  refine Nat.card_congr
    { toFun := fun g => ⟨χ⁻¹ * g * χ, Subgroup.mem_centralizer_iff.2 ?_⟩
      invFun := fun g => ⟨χ * g * χ⁻¹, Subgroup.mem_centralizer_iff.2 ?_⟩
      left_inv := fun g => Subtype.ext (by group)
      right_inv := fun g => Subtype.ext (by group) }
  · rintro _ rfl
    have hg := Subgroup.mem_centralizer_iff.1 g.2 ψ rfl
    calc χ⁻¹ * ψ * χ * (χ⁻¹ * ↑g * χ) = χ⁻¹ * (ψ * ↑g) * χ := by group
      _ = χ⁻¹ * (↑g * ψ) * χ := by rw [hg]
      _ = χ⁻¹ * ↑g * χ * (χ⁻¹ * ψ * χ) := by group
  · intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    have hg := Subgroup.mem_centralizer_iff.1 g.2 (χ⁻¹ * ψ * χ) rfl
    calc ψ * (χ * ↑g * χ⁻¹) = χ * (χ⁻¹ * ψ * χ * ↑g) * χ⁻¹ := by group
      _ = χ * (↑g * (χ⁻¹ * ψ * χ)) * χ⁻¹ := by rw [hg]
      _ = χ * ↑g * χ⁻¹ * ψ := by group

section Cent

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)
  (hrec : RecOK.{u} ET cnt T)

include R hM hrec

theorem cent_dvd_of_checks {GN kg f c nr nv : ℕ} {REP IV ICL ICJ : ℕ → ℕ}
    (hcan : ∀ i < cnt, canonK 32 6 63 192 (T i) = true) (htup : eTupK ET GN kg f c = true)
    (hcls : eClsK cnt T nr REP nv IV ICL ICJ = true) (hcent : e614K GN kg cnt T nr REP = true)
    (hdvd : 32 ∣ cnt) (ψ : MulAut H) (hψ2 : ψ * ψ = 1) :
    32 ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set (MulAut H))) := by
  classical
  have := finite_mulAut R
  have : Fintype (MulAut H) := Fintype.ofFinite _
  obtain ⟨hall, hex, hcard⟩ := hrec H M elt R hM
  choose! Φ hΦ using hex
  have hlt : ∀ i < cnt, ∀ a < 32, eG (T i) a < 32 := fun i hi a ha =>
    (hΦ i hi a ha) ▸ sg_lt R _ _
  have hact : ∀ (φ : MulAut H) (i : ℕ), i < cnt → (∀ a < 32, sg R φ a = eG (T i) a) → φ = Φ i :=
    fun φ i hi h => mulAut_ext_sg R fun a ha => (h a ha).trans (hΦ i hi a ha).symm
  have himg : (Finset.range cnt).image Φ = Finset.univ := by
    refine Finset.eq_univ_of_forall fun φ => ?_
    obtain ⟨i, hi, h⟩ := hall φ
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, (hact φ i hi h).symm⟩
  have hinj : Set.InjOn Φ (Finset.range cnt) := Finset.card_image_iff.1 (by
    rw [himg, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, Finset.card_range])
  simp only [eTupK, bAnd_eq, Bool.and_eq_true, allN_iff, strictB_eq] at htup
  obtain ⟨-, hg, hgen, -⟩ := htup
  have hS : ∀ j < kg, eG GN j < 32 := fun j hj => Nat.le_of_ble_eq_true (hg j hj).1
  have hsgm : ∀ i < cnt, ∀ j < cnt, ∀ a < 32, sg R (Φ i * Φ j) a = eG (T i) (eG (T j) a) :=
    fun i hi j hj a ha => by rw [sg_mul, hΦ j hj a ha, hΦ i hi _ (hlt j hj a ha)]
  have hcomm : ∀ i < cnt, ∀ j < cnt,
      (Φ i * Φ j = Φ j * Φ i ↔ eCommG GN kg (T i) (T j) = true) := by
    intro i hi j hj
    constructor
    · intro h
      unfold eCommG
      rw [allN_iff]
      intro d hd
      rw [strictB_eq]
      apply beq_t.2
      rw [← hsgm i hi j hj _ (hS d hd), ← hsgm j hj i hi _ (hS d hd), h]
    · intro h
      unfold eCommG at h
      rw [allN_iff] at h
      refine mulAut_ext_sg R (sg_eq_of_gen R hM hS hgen _ _ fun d hd => ?_)
      have h1 := h d hd
      rw [strictB_eq] at h1
      rw [hsgm i hi j hj _ (hS d hd), hsgm j hj i hi _ (hS d hd)]
      exact beq_t.1 h1
  have hcnt_cent : ∀ j < cnt, Nat.card ↥(Subgroup.centralizer ({Φ j} : Set (MulAut H))) =
      eCnt cnt (fun i => eCommG GN kg (T i) (T j)) := by
    intro j hj
    let S := (Finset.range cnt).filter fun i => eCommG GN kg (T i) (T j) = true
    have hset : ((Subgroup.centralizer ({Φ j} : Set (MulAut H)) : Set (MulAut H))) =
        ↑(S.image Φ) := by
      ext φ
      simp only [SetLike.mem_coe, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · intro hφ
        obtain ⟨i, hi, h⟩ := hall φ
        obtain rfl := hact φ i hi h
        have hc := Subgroup.mem_centralizer_iff.1 hφ (Φ j) rfl
        exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, (hcomm i hi j hj).1 hc.symm⟩, rfl⟩
      · rintro ⟨i, hiS, rfl⟩
        obtain ⟨hi, hc⟩ := Finset.mem_filter.1 hiS
        refine Subgroup.mem_centralizer_iff.2 ?_
        rintro _ rfl
        exact ((hcomm i (Finset.mem_range.1 hi) j hj).2 hc).symm
    have hcoe : Nat.card ↥(Subgroup.centralizer ({Φ j} : Set (MulAut H))) =
        Nat.card ↥((Subgroup.centralizer ({Φ j} : Set (MulAut H)) : Set (MulAut H))) := rfl
    rw [hcoe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      Finset.card_image_of_injOn (hinj.mono fun i hi => (Finset.mem_filter.1 hi).1),
      eCnt_eq_card]
  obtain ⟨hinv, hq⟩ := eClsK_spec hcls
  have hrep := e614K_spec hcent
  by_cases h1 : ψ = 1
  · subst h1
    have htop : Subgroup.centralizer ({1} : Set (MulAut H)) = ⊤ := by
      ext g
      simp only [Subgroup.mem_top, iff_true]
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ rfl
      rw [one_mul, mul_one]
    rw [htop, Subgroup.card_top, hcard]
    exact hdvd
  · obtain ⟨i, hi, hψ⟩ := hall ψ
    obtain rfl := hact ψ i hi hψ
    have hsq : ∀ a < 32, eG (T i) (eG (T i) a) = a := by
      intro a ha
      rw [← hsgm i hi i hi a ha, hψ2, sg_one R ha]
    have hne : T i ≠ eId := by
      intro e
      refine h1 (mulAut_ext_sg R fun a ha => ?_)
      rw [hΦ i hi a ha, e, eG_eId ha, sg_one R ha]
    obtain ⟨q, hqv, rfl⟩ := all_of_sorted hinv (fun q hq' => ⟨(hq q hq').1, (hq q hq').2.2.2.1,
      (hq q hq').2.2.2.2.1⟩) i hi (eInvK_of (hcan i hi) hsq hne)
    obtain ⟨-, hl, hcj, -, -, hconj⟩ := hq q hqv
    have hrl := ((eClsK_spec hcls).2 q hqv).1
    have hrepl : REP (ICL q) < cnt := by
      unfold eClsK at hcls
      rw [bAnd_eq, Bool.and_eq_true] at hcls
      have h2 := allN_iff.1 hcls.1 (ICL q) hl
      rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h2
      exact Nat.le_of_ble_eq_true h2.1
    have hχ : Φ (ICJ q) * Φ (REP (ICL q)) = Φ (IV q) * Φ (ICJ q) := by
      refine mulAut_ext_sg R fun a ha => ?_
      rw [hsgm _ hcj _ hrepl a ha, hsgm _ hrl _ hcj a ha, ← eG_eC _ _ ha, ← eG_eC _ _ ha, hconj]
    rw [card_centralizer_conj hχ, hcnt_cent _ hrepl]
    exact Nat.dvd_of_mod_eq_zero (hrep _ hl)

end Cent

theorem eFacts614_of_checks {G : Type u} [Group G] {E : Subgroup G} {t : G} {mulE : ℕ → ℕ → ℕ}
    {eltE : ℕ → G} {ET : ℕ → ℕ} (hL : ELabelling E t mulE 21 eltE)
    (hET : ∀ a < 32, ∀ b < 32, mulE a b = eMul ET a b) {T REP IV ICL ICJ : ℕ → ℕ}
    {GN kg f c nr nv : ℕ} (hrec : RecOK.{u} ET 1920 T)
    (hcan : ∀ i < 1920, canonK 32 6 63 192 (T i) = true) (htup : eTupK ET GN kg f c = true)
    (hcls : eClsK 1920 T nr REP nv IV ICL ICJ = true) (hcent : e614K GN kg 1920 T nr REP = true) :
    EFacts614 E t := by
  obtain ⟨elt, R, -⟩ := realizes_of_labelling hL
  have hM : ∀ a < 32, ∀ b < 32, mt (tab2 32 mulE) a b = eMul ET a b := fun a ha b hb =>
    (mt_tab2 mulE ha hb).trans (hET a ha b hb)
  exact ⟨(hrec _ _ _ R hM).2.2,
    cent_dvd_of_checks R hM hrec hcan htup hcls hcent (by norm_num)⟩

end CFSG.KS.EAut

end
