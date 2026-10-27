module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import Certificates.Data.GL4Sub
public import CFSG.Certificates.Kernel.Misc.GL4CodeSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.GL4

open Matrix CFSG.KC.LQT.P CFSG.KC.Ord
open CFSG.KC.Misc.Clos (ClosEnc ExactList clos_card sort_distinct treeAt sortAt closedAt)
open Certificates.A5GL42 (Mat4 Vec4 ofCode vecOfCode)
open Certificates.A5A7GL42 (Pset)
open Certificates.GL4 (GL4 sg)

theorem finite_gl4 : Finite GL4 := Finite.of_injective (fun g : GL4 => (g : Mat4)) Units.val_injective

theorem lAt_eq (l : List ℕ) (i : ℕ) : lAt l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem enc4_eq_id4 {g : GL4} : enc4 g = id4 ↔ g = 1 := by
  rw [← gl4_enc.enc_one]
  exact gl4_enc.inj.eq_iff

theorem pow4F_enc (g : GL4) (n : ℕ) : pow4F (enc4 g) n = enc4 (g ^ n) := by
  induction n with
  | zero => exact gl4_enc.enc_one.symm
  | succ n ih =>
    change mul4F (pow4F (enc4 g) n) (enc4 g) = _
    rw [ih, ← gl4_enc.enc_mul, pow_succ]

theorem pow4F_eq_id4 {g : GL4} {n : ℕ} : pow4F (enc4 g) n = id4 ↔ g ^ n = 1 := by
  rw [pow4F_enc, enc4_eq_id4]

theorem ordDiv_iff (g : GL4) (n : ℕ) : ordDiv (enc4 g) n = true ↔ g ≠ 1 ∧ g ^ n = 1 := by
  unfold ordDiv
  rw [andB_iff, notB_iff, beq_iff, beq_iff, enc4_eq_id4, pow4F_eq_id4]

theorem exists_of_invOK {c : ℕ} (h : invOK c = true) : ∃ g : GL4, enc4 g = c := by
  unfold invOK at h
  obtain ⟨hc, hi⟩ := andB_iff.1 h
  have hc' := Nat.blt_eq.mp hc
  have hm : ofCode c * ofCode (inv4F c) = 1 := by
    rw [← mul4F_ofCode, beq_iff.1 hi, ofCode_id4]
  refine ⟨⟨ofCode c, ofCode (inv4F c), hm, mul_eq_one_comm.mp hm⟩, ?_⟩
  exact code4_ofCode hc'

noncomputable def u4 (c : ℕ) : GL4 := if h : ∃ g : GL4, enc4 g = c then h.choose else 1

theorem enc4_u4 {c : ℕ} (h : ∃ g : GL4, enc4 g = c) : enc4 (u4 c) = c := by
  rw [u4, dif_pos h]
  exact h.choose_spec

theorem coe_eq_of_enc4 {g : GL4} {c : ℕ} (h : enc4 g = c) : (g : Mat4) = ofCode c := by
  rw [← h, ofCode_enc4]

theorem mem_pset_iff {l : List ℕ} {g : GL4} (hl : ∀ c ∈ l, c < 65536) :
    (g : Mat4) ∈ Pset l ↔ enc4 g ∈ l := by
  constructor
  · rintro ⟨c, hc, e⟩
    have : enc4 g = c := by rw [enc4, ← e, code4_ofCode (hl c hc)]
    rwa [this]
  · intro h
    exact ⟨_, h, ofCode_enc4 g⟩

theorem sg_eq (l : List ℕ) (hl : ∀ c ∈ l, invOK c = true) :
    sg l = Subgroup.closure {g | g ∈ l.map u4} := by
  unfold sg
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨c, hc, e⟩
    obtain ⟨h, hh⟩ := exists_of_invOK (hl c hc)
    refine ⟨c, hc, ?_⟩
    apply gl4_enc.inj
    rw [enc4_u4 ⟨h, hh⟩, enc4, ← e, code4_ofCode]
    exact Nat.blt_eq.mp (andB_iff.1 (hl c hc)).1
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, (coe_eq_of_enc4 (enc4_u4 (exists_of_invOK (hl c hc)))).symm⟩

theorem enc4_getD_u4 (d : GL4) : ∀ (l : List ℕ), (∀ c ∈ l, invOK c = true) →
    ∀ j < l.length, enc4 ((l.map u4).getD j d) = l.getD j 0
  | [], _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c :: _, hl, 0, _ => by
    rw [List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
    exact enc4_u4 (exists_of_invOK (hl c List.mem_cons_self))
  | _ :: t, hl, j + 1, hj => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
    exact enc4_getD_u4 d t (fun x hx => hl x (List.mem_cons_of_mem _ hx)) j
      (Nat.lt_of_succ_lt_succ hj)

theorem getD_map_u4 (l : List ℕ) (hl : ∀ c ∈ l, invOK c = true) {G : ℕ → ℕ}
    (hG : ∀ j < l.length, G j = l.getD j 0) {d : GL4} :
    ∀ j < (l.map u4).length, G j = enc4 ((l.map u4).getD j d) := by
  intro j hj
  have hj' : j < l.length := lt_of_lt_of_eq hj (List.length_map _)
  rw [hG j hj', enc4_getD_u4 d l hl j hj']

theorem sg_exact (l : List ℕ) (hl : ∀ c ∈ l, invOK c = true) {G E PA SG CT : ℕ → ℕ} {N : ℕ}
    (hG : ∀ j < l.length, G j = l.getD j 0) (hN : 0 < N)
    (ht : ∀ k < N, treeAt mul4F id4 G l.length E PA k = true)
    (hs : ∀ k < N, sortAt N E SG k = true)
    (hc : ∀ k < N, closedAt mul4F G l.length N E CT k = true) :
    Nat.card (sg l) = N ∧ ExactList enc4 (sg l) N E := by
  have hlen : (l.map u4).length = l.length := List.length_map _
  have := finite_gl4
  obtain ⟨h1, -, h3⟩ := clos_card gl4_enc (l.map u4) (getD_map_u4 l hl hG) hN
    (by rw [hlen]; exact ht) hs
  obtain ⟨h4, h5⟩ := h3 (CT := CT) (by rw [hlen]; exact hc)
  rw [sg_eq l hl]
  exact ⟨h4, h1, h5, sort_distinct hs⟩

theorem inL_iff (E : ℕ → ℕ) (N c : ℕ) : inL E N c = true ↔ ∃ k < N, E k = c := by
  unfold inL
  rw [anyN_iff]
  simp only [beq_iff]

theorem sorted_facts {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) :
    (∀ a b, a ≤ b → b < N → E (SG a) ≤ E (SG b)) ∧ ∀ k < N, ∃ a < N, SG a = k := by
  have h1 : ∀ i < N, SG i < N ∧ (i + 1 < N → E (SG i) < E (SG (i + 1))) := by
    intro i hi
    obtain ⟨ha, hb⟩ := andB_iff.1 (hs i hi)
    exact ⟨Nat.blt_eq.mp ha, fun h => Nat.blt_eq.mp (impB_iff.1 hb (Nat.blt_eq.mpr h))⟩
  have hmono : ∀ a b, a < b → b < N → E (SG a) < E (SG b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact (ih h (by omega)).trans ((h1 b (by omega)).2 hb)
      · exact (h1 a (by omega)).2 hb
  refine ⟨fun a b hab hb => ?_, fun k hk => ?_⟩
  · rcases Nat.lt_or_ge a b with h | h
    · exact (hmono a b h hb).le
    · rw [show a = b by omega]
  · let f : Fin N → Fin N := fun a => ⟨SG a, (h1 a a.isLt).1⟩
    have hf : Function.Injective f := by
      intro a b h
      have h' : SG a = SG b := congrArg Fin.val h
      rcases Nat.lt_trichotomy a b with hab | hab | hab
      · exact absurd (congrArg E h') (hmono a b hab b.isLt).ne
      · exact Fin.ext hab
      · exact absurd (congrArg E h') (hmono b a hab a.isLt).ne'
    obtain ⟨a, ha⟩ := Finite.surjective_of_injective hf ⟨k, hk⟩
    exact ⟨a, a.isLt, congrArg Fin.val ha⟩

theorem outK_sound {N c : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true)
    (h : outK E SG N c = true) : ∀ k < N, E k ≠ c := by
  unfold outK brK at h
  rw [letB_eq] at h
  obtain ⟨hq, h⟩ := andB_iff.1 h
  obtain ⟨hlo, hhi⟩ := andB_iff.1 h
  generalize posK E SG N c = q at hq hlo hhi
  have hq' : q ≤ N := Nat.ble_eq.mp hq
  obtain ⟨hmono, hsurj⟩ := sorted_facts hs
  intro k hk e
  obtain ⟨a, ha, rfl⟩ := hsurj k hk
  rcases Nat.lt_or_ge a q with h1 | h1
  · rcases orB_iff.1 hlo with h0 | h0
    · have h0' : q = 0 := beq_iff.1 h0
      omega
    · have h2 : E (SG (q - 1)) < c := Nat.blt_eq.mp h0
      have := hmono a (q - 1) (by omega) (by omega)
      omega
  · rcases orB_iff.1 hhi with h0 | h0
    · have h0' : q = N := beq_iff.1 h0
      omega
    · have := hmono q a h1 ha
      have h2 : c < E (SG q) := Nat.blt_eq.mp h0
      omega

theorem mem_normalizer_of_conj {H : Subgroup GL4} (x : GL4) (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H) :
    x ∈ Subgroup.normalizer (H : Set GL4) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hx h, fun hh => ?_⟩
  have hle : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact hx y hy
  have hcard : Nat.card (H.map (MulAut.conj x).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have heq := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hmem : x * h * x⁻¹ ∈ H.map (MulAut.conj x).toMonoidHom := by rw [heq]; exact hh
  obtain ⟨y, hy, hyy⟩ := hmem
  have : y = h := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy
    exact mul_left_cancel (mul_right_cancel hyy)
  rwa [← this]

theorem memN_iff' (x : ℕ) (l : List ℕ) : CFSG.KC.Misc.memN x l = true ↔ x ∈ l := by
  unfold CFSG.KC.Misc.memN
  rw [letB_eq]
  induction l with
  | nil => simp
  | cons z t ih =>
    change orB (Nat.beq x z) _ = true ↔ _
    rw [orB_iff, beq_iff, ih, List.mem_cons]

def colM (v : Vec4) : Mat4 := Matrix.of fun i j => if j = 0 then v i else 0

theorem mul_colM (A : Mat4) (v : Vec4) : A * colM v = colM (A *ᵥ v) := by
  ext i j
  by_cases hj : j = 0
  · simp [colM, Matrix.mul_apply, Matrix.mulVec, dotProduct, hj]
  · simp [colM, Matrix.mul_apply, hj]

theorem colM_inj {v w : Vec4} (h : colM v = colM w) : v = w := by
  funext i
  have := congrFun (congrFun h i) 0
  simpa [colM] using this

theorem colC_ofCode : ∀ u < 16, ofCode (colC u) = colM (vecOfCode u) := by
  unfold colM
  decide +kernel

theorem colC_lt : ∀ u < 16, colC u < 65536 := by decide +kernel

theorem vec_surj : ∀ v : Vec4, ∃ u < 16, vecOfCode u = v := by decide +kernel

theorem vec_inj : ∀ a < 16, ∀ b < 16, vecOfCode a = vecOfCode b → a = b := by decide +kernel

end CFSG.KC.Misc.GL4

end
