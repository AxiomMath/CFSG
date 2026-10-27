module

public import Certificates.Data.Kernel.G24Word
public import CFSG.Certificates.Kernel.G24KeySound

public section

namespace CFSG.KC.G24Word

open CFSG.KC.Enum CFSG.KC.Pack CFSG.KC.G24Key

@[expose] noncomputable def letE (a b : Pm) (c : ℕ) : Pm :=
  if c = 2 then a else if c = 3 then a⁻¹ else if c = 4 then b else b⁻¹

@[expose] noncomputable def wordL (a b : Pm) (w : List ℕ) : Pm := (w.map (letE a b)).prod

theorem wordL_append (a b : Pm) (v w : List ℕ) : wordL a b (v ++ w) = wordL a b v * wordL a b w := by
  simp [wordL]

theorem wordL_mem {G : Type*} [SetLike G Pm] [SubgroupClass G Pm] {H : G} {a b : Pm} (ha : a ∈ H)
    (hb : b ∈ H) (w : List ℕ) : wordL a b w ∈ H := by
  unfold wordL
  induction w with
  | nil => exact one_mem H
  | cons c w ih =>
    rw [List.map_cons, List.prod_cons]
    refine mul_mem ?_ ih
    unfold letE
    split_ifs
    · exact ha
    · exact inv_mem ha
    · exact hb
    · exact inv_mem hb

theorem nif_beq (c k t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t (Nat.beq c k) = if c = k then t else e := by
  cases h : Nat.beq c k
  · rw [if_neg fun e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

theorem letC_eq (A AI B BI c : ℕ) : letC A AI B BI c =
    if c = 2 then A else if c = 3 then AI else if c = 4 then B else BI := by
  unfold letC
  rw [nif_beq, nif_beq, nif_beq]

variable {A AI B BI : ℕ} {a b : Pm}

theorem letC_pt (hA : PtRep A a) (hAI : PtRep AI a⁻¹) (hB : PtRep B b) (hBI : PtRep BI b⁻¹)
    (c : ℕ) : PtRep (letC A AI B BI c) (letE a b c) := by
  rw [letC_eq]
  unfold letE
  split_ifs
  · exact hA
  · exact hAI
  · exact hB
  · exact hBI

theorem letC_pt_inv (hA : PtRep A a) (hAI : PtRep AI a⁻¹) (hB : PtRep B b) (hBI : PtRep BI b⁻¹)
    (c : ℕ) : PtRep (letC AI A BI B c) (letE a b c)⁻¹ := by
  rw [letC_eq]
  unfold letE
  split_ifs
  · exact hAI
  · rw [inv_inv]
    exact hA
  · exact hBI
  · rw [inv_inv]
    exact hB

variable {L LI : ℕ → ℕ} {g : ℕ → Pm}

theorem wF_eq (hL : ∀ c, PtRep (L c) (g c)) :
    ∀ (w : List ℕ) (x : Fin 1365), wF L w x = ((w.map g).prod x : ℕ)
  | [], _ => rfl
  | c :: w, x => by
    change strictN (wF L w x) (fun q => ap (L c) q) = _
    rw [strictN_eq, wF_eq hL w x, hL c]
    simp

theorem wI_eq (hLI : ∀ c, PtRep (LI c) (g c)⁻¹) :
    ∀ (w : List ℕ) (x : Fin 1365), wI LI w x = (((w.map g).prod)⁻¹ x : ℕ)
  | [], _ => rfl
  | c :: w, x => by
    change strictN (ap (LI c) x) (wI LI w) = _
    rw [strictN_eq, hLI c, wI_eq hLI w]
    simp

theorem keyOf_pts {f : ℕ → ℕ} {e : Pm} (h0 : f 0 = e 0) (h1 : f 1 = e 1) (h2 : f 2 = e 2) :
    keyOf f = keyE e := by
  rw [keyOf_eq, h0, h1, h2]
  rfl

theorem lettersK_spec : ∀ {w : List ℕ}, lettersK w = true → ∀ c ∈ w, 2 ≤ c ∧ c ≤ 5
  | [], _ => by simp
  | c :: w, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (lettersK w) (Nat.ble c 5)) (Nat.ble 2 c) = true at h
    obtain ⟨h1, h2⟩ := band_iff.1 h
    obtain ⟨h2, h3⟩ := band_iff.1 h2
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩
    · exact lettersK_spec h3 d hd

theorem normJ_spec (hL : ∀ c, PtRep (L c) (g c)) (hLI : ∀ c, PtRep (LI c) (g c)⁻¹)
    {G KT NI : ℕ → ℕ} {γ : ℕ → Pm} {J n : ℕ} (hG : ∀ i < J, PtRep (G i) (γ i)) {w : List ℕ}
    {j : ℕ} (h : normJ L LI G KT NI J n w j = true) :
    (∀ c ∈ w, 2 ≤ c ∧ c ≤ 5) ∧ ∀ i < J, NI (J * j + i) < n ∧
      KT (NI (J * j + i)) = keyE ((w.map g).prod * γ i * ((w.map g).prod)⁻¹) := by
  unfold normJ at h
  obtain ⟨hw, h⟩ := band_iff.1 h
  refine ⟨lettersK_spec hw, fun i hi => ?_⟩
  simp only [strictB_eq] at h
  obtain ⟨hk, he⟩ := band_iff.1 (allN_spec h i hi)
  have ei : Nat.add (Nat.mul J j) i = J * j + i := rfl
  rw [ei] at hk he
  refine ⟨Nat.le_of_ble_eq_true hk, ?_⟩
  rw [Nat.eq_of_beq_eq_true he]
  have hp : ∀ x : Fin 1365, wF L w (ap (G i) (wI LI w x)) =
      (((w.map g).prod * γ i * ((w.map g).prod)⁻¹) x : ℕ) := fun x => by
    rw [wI_eq hLI w x, hG i hi, wF_eq hL]
    simp
  exact keyOf_pts (hp 0) (hp 1) (hp 2)

theorem fixB_spec (hL : ∀ c, PtRep (L c) (g c)) {w : List ℕ} (h : fixB L w = true) :
    (w.map g).prod 0 = 0 ∧ (w.map g).prod 1 = 1 ∧ (w.map g).prod 2 = 2 := by
  have hp : ∀ x : Fin 1365, (x : ℕ) < 3 → (w.map g).prod x = x := fun x hx => by
    have := Nat.eq_of_beq_eq_true (allN_spec h x hx)
    rw [wF_eq hL] at this
    exact Fin.ext this
  exact ⟨hp 0 (by decide), hp 1 (by decide), hp 2 (by decide)⟩

theorem diffB_spec (hL : ∀ c, PtRep (L c) (g c)) {v w : List ℕ} {p : ℕ} (hp : p < 1365)
    (h : diffB L v w p = true) : (v.map g).prod ≠ (w.map g).prod := fun e => by
  unfold diffB at h
  have hx := wF_eq hL v ⟨p, hp⟩
  rw [e, ← wF_eq hL w ⟨p, hp⟩] at hx
  change Bool.rec (motive := fun _ => Bool) true false (Nat.beq (wF L v p) (wF L w p)) = true at h
  rw [hx, Nat.beq_refl] at h
  exact Bool.noConfusion h

end CFSG.KC.G24Word

end
