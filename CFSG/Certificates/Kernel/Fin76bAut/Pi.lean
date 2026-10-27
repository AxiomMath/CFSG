module

public import CFSG.Certificates.Kernel.Fin76bAut.Pos
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HPi
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

universe u

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.E69

theorem eInPr_iff {ET : ℕ → ℕ} {r k : ℕ} : eInPr ET r k = true ↔ k = r ∨ k = eMul ET r 21 := by
  unfold eInPr
  rw [bIf_eq]
  split_ifs with h
  · simp [beq_t.1 h]
  · have hne : k ≠ r := fun e => h (beq_t.2 e)
    rw [beq_t]
    exact ⟨Or.inr, fun h' => h'.resolve_left hne⟩

theorem ePrRep_iff {ET : ℕ → ℕ} {r : ℕ} :
    ePrRep ET r = true ↔ eKind ET 0 r = true ∧ r < eMul ET r 21 := by
  unfold ePrRep
  rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq]

theorem ePrK_spec {ET : ℕ → ℕ} {PR : ℕ} (h : ePrK ET PR = true) :
    eMul ET 21 21 = 0 ∧ eCnt 32 (fun r => ePrRep ET r) = 5 ∧
      ∀ j < 5, eG PR j < 32 ∧ ePrRep ET (eG PR j) = true ∧ (j + 1 < 5 → eG PR j < eG PR (j + 1)) := by
  unfold ePrK at h
  simp only [bAnd_eq, Bool.and_eq_true, beq_t, allN_iff] at h
  obtain ⟨h21, h5, hj⟩ := h
  refine ⟨h21, h5, fun j hjl => ?_⟩
  have h1 := hj j hjl
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨h1, h2, h3⟩ := h1
  refine ⟨Nat.le_of_ble_eq_true h1, h2, fun hj1 => ?_⟩
  have hj1' : Nat.blt (Nat.succ j) 5 = true := Nat.blt_eq.mpr hj1
  rw [bIf_eq, if_pos hj1'] at h3
  exact Nat.blt_eq.mp h3

theorem eAnyN_iff {n : ℕ} {f : ℕ → Bool} : eAnyN n f = true ↔ ∃ i < n, f i = true := by
  unfold eAnyN
  rw [bIf_eq]
  split_ifs with h
  · rw [allN_iff] at h
    refine ⟨fun h' => by simp at h', fun ⟨i, hi, hf⟩ => ?_⟩
    have h1 := h i hi
    rw [bIf_eq, if_pos hf] at h1
    exact absurd h1 Bool.false_ne_true
  · rw [allN_iff] at h
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    by_contra hn
    refine h fun i hi => ?_
    have hf : ¬ f i = true := fun e => hn ⟨i, hi, e⟩
    rw [bIf_eq, if_neg hf]

theorem eKerK_spec {ET T INN : ℕ → ℕ} {PR cnt ni : ℕ} (h : eKerK ET PR cnt T ni INN = true) :
    ∀ i < cnt, eG (T i) 21 = 21 ∧ (eTriv ET PR (T i) = true ↔ ∃ u < ni, INN u = i) := by
  intro i hi
  have h1 := allN_iff.1 h i hi
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨h1, h2⟩ := h1
  refine ⟨beq_t.1 h1, ?_⟩
  rw [eBEq_iff.1 h2, eAnyN_iff]
  exact exists_congr fun u => and_congr_right fun _ => beq_t

theorem foldUp_last {n j₀ : ℕ} {g : ℕ → Bool} (hj₀ : j₀ < n) (hg : ∀ j < n, g j = true ↔ j = j₀) :
    foldUp n (fun j acc => Bool.rec (motive := fun _ => ℕ) acc j (g j)) 0 = j₀ := by
  rw [foldUp_eq]
  simp only [nIf_eq]
  suffices H : ∀ m ≤ n, (List.range m).foldl
      (fun s j => if g j = true then j else s) 0 = if j₀ < m then j₀ else 0 by
    rw [H n le_rfl, if_pos hj₀]
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega)]
    by_cases hmj : m = j₀
    · subst hmj
      rw [if_pos ((hg m (by omega)).2 rfl), if_pos (by omega)]
    · have hgm : ¬ g m = true := fun h => hmj ((hg m (by omega)).1 h)
      rw [if_neg hgm]
      by_cases hj : j₀ < m
      · rw [if_pos hj, if_pos (by omega)]
      · rw [if_neg hj, if_neg (by omega)]

@[expose] noncomputable def evenOf (σ : ℕ → ℕ) : Bool :=
  Nat.beq (Nat.land (foldUp 5 (fun i acc => strictN (σ i) (fun si =>
    foldUp i (fun j acc2 => Bool.rec (motive := fun _ => ℕ) acc2 (Nat.succ acc2)
      (Nat.blt si (σ j))) acc)) 0) 1) 0

theorem eEven_eq (ET : ℕ → ℕ) (PR p : ℕ) : eEven ET PR p = evenOf (eSigAt ET PR p) := rfl

theorem foldl_congr' {f g : ℕ → ℕ → ℕ} :
    ∀ (l : List ℕ) (a : ℕ), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | x :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h x (by simp) a]
    exact foldl_congr' l _ fun y hy b => h y (List.mem_cons_of_mem _ hy) b

theorem evenOf_congr {σ σ' : ℕ → ℕ} (h : ∀ j < 5, σ j = σ' j) : evenOf σ = evenOf σ' := by
  unfold evenOf
  congr 2
  rw [foldUp_eq, foldUp_eq]
  refine foldl_congr' _ _ fun i hi acc => ?_
  have hi5 := List.mem_range.1 hi
  simp only [strictN_eq]
  rw [h i hi5, foldUp_eq, foldUp_eq]
  refine foldl_congr' _ _ fun j hj acc2 => ?_
  simp only [h j (lt_trans (List.mem_range.1 hj) hi5)]

theorem evenOf_of_sign : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 →
    evenOf (fun j => if h : j < 5 then ((τ ⟨j, h⟩ : Fin 5) : ℕ) else 0) = true := by
  decide +kernel

section Pairs

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET : ℕ → ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b) (hc : eCtrK ET = true)
  {PR : ℕ} (hpr : ePrK ET PR = true)

include R hM

theorem m21_lt {k : ℕ} (hk : k < 32) : eMul ET k 21 < 32 := tmul_lt R hM hk (by norm_num)

theorem m21_elt {k : ℕ} (hk : k < 32) : elt (eMul ET k 21) = elt k * elt 21 := by
  rw [← hM k hk 21 (by norm_num), R.mul _ _ hk (by norm_num)]

include hpr in
theorem t_sq : elt 21 * elt 21 = 1 := by
  rw [← m21_elt R hM (by norm_num), (ePrK_spec hpr).1, R.one]

include hc in
theorem t_comm {k : ℕ} (hk : k < 32) : elt k * elt 21 = elt 21 * elt k := by
  rw [← R.mul _ _ hk (by norm_num), ← R.mul _ _ (by norm_num) hk, hM _ hk _ (by norm_num),
    hM _ (by norm_num) _ hk, ((ctr_iff hc (by norm_num : (21 : ℕ) < 32)).1 rfl k hk).symm]

include hpr in
theorem m21_m21 {k : ℕ} (hk : k < 32) : eMul ET (eMul ET k 21) 21 = k :=
  R.inj _ _ (m21_lt R hM (m21_lt R hM hk)) hk (by
    rw [m21_elt R hM (m21_lt R hM hk), m21_elt R hM hk, mul_assoc, t_sq R hM hpr, mul_one])

theorem kind_iff {k : ℕ} (hk : k < 32) :
    eKind ET 0 k = true ↔ elt k * elt k = 1 ∧ elt k ≠ 1 ∧ elt k ≠ elt 21 := by
  have e1 : elt k * elt k = 1 ↔ eMul ET k k = 0 := by
    rw [← R.mul _ _ hk hk, hM k hk k hk, ← R.one]
    exact ⟨R.inj _ _ (tmul_lt R hM hk hk) R.pos, fun h => by rw [h]⟩
  have e2 : elt k ≠ 1 ↔ k ≠ 0 := by
    rw [← R.one]
    exact not_congr ⟨R.inj _ _ hk R.pos, fun h => by rw [h]⟩
  have e3 : elt k ≠ elt 21 ↔ k ≠ 21 := not_congr ⟨R.inj _ _ hk (by norm_num), fun h => by rw [h]⟩
  rw [eKind_iff, e1, e2, e3]

include hc hpr in
theorem kind_m21 {k : ℕ} (hk : k < 32) (h : eKind ET 0 k = true) : eKind ET 0 (eMul ET k 21) = true := by
  obtain ⟨h1, h2, h3⟩ := (kind_iff R hM hk).1 h
  refine (kind_iff R hM (m21_lt R hM hk)).2 ⟨?_, fun e => h3 ?_, fun e => h2 ?_⟩
  · rw [m21_elt R hM hk, mul_assoc, ← mul_assoc (elt 21), ← t_comm R hM hc hk, mul_assoc, t_sq R hM hpr,
      mul_one, h1]
  · rw [m21_elt R hM hk] at e
    calc elt k = elt k * elt 21 * elt 21 := by rw [mul_assoc, t_sq R hM hpr, mul_one]
      _ = elt 21 := by rw [e, one_mul]
  · rw [m21_elt R hM hk] at e
    calc elt k = elt k * elt 21 * elt 21 := by rw [mul_assoc, t_sq R hM hpr, mul_one]
      _ = 1 := by rw [e, t_sq R hM hpr]

include hpr in
theorem pr_mono : ∀ i j, i < j → j < 5 → eG PR i < eG PR j := by
  have hs := (ePrK_spec hpr).2.2
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (ih h' (by omega)) ((hs j (by omega)).2.2 hj)
    · subst h'
      exact (hs i (by omega)).2.2 hj

include hc hpr in
theorem pair_cover {k : ℕ} (hk : k < 32) (h : eKind ET 0 k = true) :
    ∃ j < 5, k = eG PR j ∨ k = eMul ET (eG PR j) 21 := by
  obtain ⟨-, h5, hs⟩ := ePrK_spec hpr
  have hall := all_of_sorted h5 fun q hq => ⟨(hs q hq).1, (hs q hq).2.1, (hs q hq).2.2⟩
  have hne : k ≠ eMul ET k 21 := by
    intro e
    have e2 := m21_elt R hM hk
    rw [← e] at e2
    have e3 : elt 21 = 1 := by
      have := congrArg (fun x => (elt k)⁻¹ * x) e2
      simpa using this.symm
    rw [← R.one] at e3
    exact absurd (R.inj _ _ (by norm_num) R.pos e3) (by norm_num)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q, hq, e⟩ := hall k hk (ePrRep_iff.2 ⟨h, hlt⟩)
    exact ⟨q, hq, Or.inl e.symm⟩
  · have hk' := m21_lt R hM hk
    obtain ⟨q, hq, e⟩ := hall _ hk' (ePrRep_iff.2 ⟨kind_m21 R hM hc hpr hk h, by
      rw [m21_m21 R hM hpr hk]; exact hgt⟩)
    exact ⟨q, hq, Or.inr (by rw [e, m21_m21 R hM hpr hk])⟩

include hpr in
theorem pair_unique {j j' k : ℕ} (hj : j < 5) (hj' : j' < 5)
    (h : k = eG PR j ∨ k = eMul ET (eG PR j) 21) (h' : k = eG PR j' ∨ k = eMul ET (eG PR j') 21) :
    j = j' := by
  obtain ⟨-, -, hs⟩ := ePrK_spec hpr
  have hlt : ∀ i < 5, eG PR i < eMul ET (eG PR i) 21 := fun i hi =>
    (ePrRep_iff.1 (hs i hi).2.1).2
  have hpj := (hs j hj).1
  have hpj' := (hs j' hj').1
  have hinj : eG PR j = eG PR j' → j = j' := fun e => by
    rcases Nat.lt_trichotomy j j' with h1 | h1 | h1
    · exact absurd e (Nat.ne_of_lt (pr_mono R hM hpr j j' h1 hj'))
    · exact h1
    · exact absurd e.symm (Nat.ne_of_lt (pr_mono R hM hpr j' j h1 hj))
  rcases h with rfl | rfl <;> rcases h' with e | e
  · exact hinj e
  · have h1 := hlt j' hj'
    have h2 := hlt j hj
    rw [e, m21_m21 R hM hpr hpj'] at h2
    omega
  · have h1 := hlt j hj
    have h2 := hlt j' hj'
    rw [← e, m21_m21 R hM hpr hpj] at h2
    omega
  · refine hinj ?_
    have e2 := congrArg (fun x => eMul ET x 21) e
    rwa [m21_m21 R hM hpr hpj, m21_m21 R hM hpr hpj'] at e2

include hc hpr in
theorem exists_pi : ∃ π : MulAut H →* Equiv.Perm (Fin 5), ∀ (φ : MulAut H) (i j : Fin 5),
    π φ i = j ↔ (φ (elt (eG PR i)) = elt (eG PR j) ∨
      φ (elt (eG PR i)) = elt (eG PR j) * elt 21) := by
  obtain ⟨-, -, hs⟩ := ePrK_spec hpr
  have hlab : ∀ (j : Fin 5) (k : ℕ), k < 32 → ((elt k = elt (eG PR j) ∨
      elt k = elt (eG PR j) * elt 21) ↔ (k = eG PR j ∨ k = eMul ET (eG PR j) 21)) := by
    intro j k hk
    have hp := (hs j j.2).1
    rw [← m21_elt R hM hp]
    exact or_congr ⟨R.inj _ _ hk hp, fun e => by rw [e]⟩
      ⟨R.inj _ _ hk (m21_lt R hM hp), fun e => by rw [e]⟩
  refine exists_perm_hom_of_pairs (elt 21) (fun j => elt (eG PR j)) (fun φ => ?_)
    (t_sq R hM hpr) (fun j => (kind_iff R hM (hs j j.2).1).1 (ePrRep_iff.1 (hs j j.2).2.1).1)
    (fun x hx1 hx2 hx3 => ?_)
  · have e := sg_elt R φ 21
    rw [sg_21 R hM hc φ] at e
    exact e.symm
  · obtain ⟨k, hk, rfl⟩ := R.surj x
    obtain ⟨j, hj, hkj⟩ := pair_cover R hM hc hpr hk ((kind_iff R hM hk).2 ⟨hx1, hx2, hx3⟩)
    refine ⟨⟨j, hj⟩, (hlab ⟨j, hj⟩ k hk).2 hkj, fun y hy => ?_⟩
    exact Fin.ext (pair_unique R hM hpr y.2 hj ((hlab y k hk).1 hy) hkj)

variable {π : MulAut H →* Equiv.Perm (Fin 5)}
  (hπ : ∀ (φ : MulAut H) (i j : Fin 5), π φ i = j ↔ (φ (elt (eG PR i)) = elt (eG PR j) ∨
      φ (elt (eG PR i)) = elt (eG PR j) * elt 21))

include hpr hπ

theorem pi_apply_iff {φ : MulAut H} {p : ℕ} (hφ : Acts R φ p) (i j : Fin 5) :
    π φ i = j ↔ eInPr ET (eG PR j) (eG p (eG PR i)) = true := by
  obtain ⟨-, -, hs⟩ := ePrK_spec hpr
  have hp := (hs j j.2).1
  have hpi := hφ.lt (hs i i.2).1
  rw [hπ, hφ.elt_eq (hs i i.2).1, eInPr_iff, ← m21_elt R hM hp]
  exact or_congr ⟨R.inj _ _ hpi hp, fun e => by rw [e]⟩
    ⟨R.inj _ _ hpi (m21_lt R hM hp), fun e => by rw [e]⟩

theorem pi_eq_one_iff {φ : MulAut H} {p : ℕ} (hφ : Acts R φ p) :
    π φ = 1 ↔ eTriv ET PR p = true := by
  unfold eTriv
  rw [allN_iff]
  constructor
  · intro e j hj
    rw [strictB_eq]
    exact (pi_apply_iff R hM hpr hπ hφ ⟨j, hj⟩ ⟨j, hj⟩).1 (by rw [e]; rfl)
  · intro e
    refine Equiv.ext fun i => ?_
    have h1 := e i i.2
    rw [strictB_eq] at h1
    exact (pi_apply_iff R hM hpr hπ hφ i i).2 h1

theorem ePidx_eq {φ : MulAut H} {p : ℕ} (hφ : Acts R φ p) {i : ℕ} (hi : i < 5) :
    eSigAt ET PR p i = (π φ ⟨i, hi⟩ : ℕ) := by
  unfold eSigAt ePidx
  refine foldUp_last (g := fun j => eInPr ET (eG PR j) (eG p (eG PR i))) (π φ ⟨i, hi⟩).2
    fun j hj => ?_
  exact (pi_apply_iff R hM hpr hπ hφ ⟨i, hi⟩ ⟨j, hj⟩).symm.trans
    ⟨fun e => by rw [e], fun e => Fin.ext e.symm⟩

theorem eEven_of_mem {φ : MulAut H} {p : ℕ} (hφ : Acts R φ p)
    (h : π φ ∈ alternatingGroup (Fin 5)) : eEven ET PR p = true := by
  have hσ : ∀ j < 5, eSigAt ET PR p j =
      (fun j => if h : j < 5 then ((π φ ⟨j, h⟩ : Fin 5) : ℕ) else 0) j := fun j hj => by
    simp only [dif_pos hj]
    exact ePidx_eq R hM hpr hπ hφ hj
  rw [eEven_eq, evenOf_congr hσ]
  exact evenOf_of_sign _ (Equiv.Perm.mem_alternatingGroup.1 h)

end Pairs

section Epi

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b) (hc : eCtrK ET = true)
  {PR : ℕ} (hpr : ePrK ET PR = true) {Φ : ℕ → MulAut H} (pd : PosData R T cnt Φ)
  {π : MulAut H →* Equiv.Perm (Fin 5)}
  (hπ : ∀ (φ : MulAut H) (i j : Fin 5), π φ i = j ↔ (φ (elt (eG PR i)) = elt (eG PR j) ∨
      φ (elt (eG PR i)) = elt (eG PR j) * elt 21))
  {INN INE : ℕ → ℕ} (hker : eKerK ET PR cnt T 16 INN = true) (hinn : eInnK ET cnt T 16 INN INE = true)

include R hM hc hpr pd hπ hker hinn

theorem pi_ker (φ : MulAut H) : π φ = 1 ↔ φ ∈ (MulAut.conj : H →* MulAut H).range := by
  obtain ⟨i, hi, rfl⟩ := pd.surj φ
  rw [pi_eq_one_iff R hM hpr hπ (pd.acts i hi), ((eKerK_spec hker) i hi).2, inn_iff R hM pd hc hinn]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, e⟩
    exact ⟨u, hu, pd.inj _ (eInnK_spec hinn u hu).1 _ hi e⟩

theorem pi_surj (hcard : Nat.card (MulAut H) = 1920) : Function.Surjective π := by
  have hk : π.ker = (MulAut.conj : H →* MulAut H).range :=
    Subgroup.ext fun φ => by rw [MonoidHom.mem_ker]; exact pi_ker R hM hc hpr pd hπ hker hinn φ
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, hk, card_inn R hM hc,
    hcard] at hq
  have h5 : Nat.card (Fin 5) = 5 := by simp
  have hf : (5 : ℕ).factorial = 120 := rfl
  have h120 : Nat.card π.range = Nat.card (Equiv.Perm (Fin 5)) := by
    rw [Nat.card_perm, h5, hf]
    omega
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ h120)

omit hc pd hker hinn in
theorem eBInv_of {φ : MulAut H} {p : ℕ} (hφ : Acts R φ p) (hcan : canonK 32 6 63 192 p = true)
    (h1 : φ * φ = 1) (h2 : π φ ∈ alternatingGroup (Fin 5))
    (h3 : π φ ≠ 1) : eBInv ET PR p = true := by
  unfold eBInv
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, bIf_eq]
  refine ⟨(hφ.eInvK_iff hcan).2 ⟨h1, fun e => h3 (by rw [e, map_one])⟩,
    eEven_of_mem R hM hpr hπ hφ h2, ?_⟩
  rw [if_neg fun e => h3 ((pi_eq_one_iff R hM hpr hπ hφ).2 e)]

end Epi

end CFSG.KS.EAut

end
