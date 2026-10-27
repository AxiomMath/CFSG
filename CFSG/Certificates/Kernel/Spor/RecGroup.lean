module

public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Sporadic.Th.TableSpec
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.TabWords
public import Mathlib

public section

namespace CFSG.KS.RecGroup

open Subgroup

variable {G : Type*} [Group G] {k cnt : ℕ} {g x : ℕ → G}

theorem mem_closure_iff_of_left_record (h0 : 0 < cnt) (hx0 : x 0 = 1)
    (htree : ∀ i, 0 < i → i < cnt → ∃ p < i, ∃ j < k, x i = g j * x p)
    (hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, x q = g j * x i) (y : G) :
    y ∈ closure (g '' {j | j < k}) ↔ ∃ i < cnt, x i = y := by
  classical
  let R : Finset G := (Finset.range cnt).image x
  have memR : ∀ y, y ∈ R ↔ ∃ i < cnt, x i = y := by
    intro y
    simp [R, Finset.mem_image, Finset.mem_range]
  let K : Subgroup G :=
    { carrier := {h | ∀ y ∈ R, h * y ∈ R}
      mul_mem' := fun {a b} ha hb y hy => by
        rw [mul_assoc]
        exact ha _ (hb y hy)
      one_mem' := fun y hy => by rwa [one_mul]
      inv_mem' := fun {a} ha y hy => by
        have hsub : R.image (a * ·) ⊆ R := by
          intro z hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
          exact ha u hu
        have heq : R.image (a * ·) = R :=
          Finset.eq_of_subset_of_card_le hsub
            (by rw [Finset.card_image_of_injective _ (mul_right_injective a)])
        rw [← heq] at hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
        simpa using hu }
  constructor
  · intro hy
    have hK : closure (g '' {j | j < k}) ≤ K := by
      rw [closure_le]
      rintro _ ⟨j, hj, rfl⟩ z hz
      obtain ⟨i, hi, rfl⟩ := (memR z).1 hz
      obtain ⟨q, hq, e⟩ := hcl i hi j hj
      exact (memR _).2 ⟨q, hq, e⟩
    have h1 := hK hy (x 0) ((memR _).2 ⟨0, h0, rfl⟩)
    rw [hx0, mul_one] at h1
    exact (memR y).1 h1
  · rintro ⟨i, hi, rfl⟩
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hx0]
        exact one_mem _
      · obtain ⟨p, hp, j, hj, e⟩ := htree i hpos hi
        rw [e]
        exact mul_mem (subset_closure ⟨j, hj, rfl⟩) (ih p hp (by omega))

theorem mem_closure_iff_of_right_record (h0 : 0 < cnt) (hx0 : x 0 = 1)
    (htree : ∀ i, 0 < i → i < cnt → ∃ p < i, ∃ j < k, x i = x p * g j)
    (hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, x q = x i * g j) (y : G) :
    y ∈ closure (g '' {j | j < k}) ↔ ∃ i < cnt, x i = y := by
  classical
  let R : Finset G := (Finset.range cnt).image x
  have memR : ∀ y, y ∈ R ↔ ∃ i < cnt, x i = y := by
    intro y
    simp [R, Finset.mem_image, Finset.mem_range]
  let K : Subgroup G :=
    { carrier := {h | ∀ y ∈ R, y * h ∈ R}
      mul_mem' := fun {a b} ha hb y hy => by
        rw [← mul_assoc]
        exact hb _ (ha y hy)
      one_mem' := fun y hy => by rwa [mul_one]
      inv_mem' := fun {a} ha y hy => by
        have hsub : R.image (· * a) ⊆ R := by
          intro z hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
          exact ha u hu
        have heq : R.image (· * a) = R :=
          Finset.eq_of_subset_of_card_le hsub
            (by rw [Finset.card_image_of_injective _ (mul_left_injective a)])
        rw [← heq] at hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
        simpa using hu }
  constructor
  · intro hy
    have hK : closure (g '' {j | j < k}) ≤ K := by
      rw [closure_le]
      rintro _ ⟨j, hj, rfl⟩ z hz
      obtain ⟨i, hi, rfl⟩ := (memR z).1 hz
      obtain ⟨q, hq, e⟩ := hcl i hi j hj
      exact (memR _).2 ⟨q, hq, e⟩
    have h1 := hK hy (x 0) ((memR _).2 ⟨0, h0, rfl⟩)
    rw [hx0, one_mul] at h1
    exact (memR y).1 h1
  · rintro ⟨i, hi, rfl⟩
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hx0]
        exact one_mem _
      · obtain ⟨p, hp, j, hj, e⟩ := htree i hpos hi
        rw [e]
        exact mul_mem (ih p hp (by omega)) (subset_closure ⟨j, hj, rfl⟩)

theorem card_of_mem_iff {H : Subgroup G} (hmem : ∀ y, y ∈ H ↔ ∃ i < cnt, x i = y)
    (hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b) : Nat.card H = cnt := by
  classical
  have e : (H : Set G) = ((Finset.range cnt).image x : Set G) := by
    ext y
    simp [hmem y]
  have hc : Nat.card H = Nat.card ↥((Finset.range cnt).image x : Set G) := by
    rw [← e]
    rfl
  rw [hc, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn,
    Finset.card_range]
  intro a ha b hb hab
  exact hinj a (by simpa using ha) b (by simpa using hb) hab

theorem card_closure_of_left_record (h0 : 0 < cnt) (hx0 : x 0 = 1)
    (htree : ∀ i, 0 < i → i < cnt → ∃ p < i, ∃ j < k, x i = g j * x p)
    (hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, x q = g j * x i)
    (hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b) :
    Nat.card (closure (g '' {j | j < k})) = cnt :=
  card_of_mem_iff (mem_closure_iff_of_left_record h0 hx0 htree hcl) hinj

theorem card_closure_of_right_record (h0 : 0 < cnt) (hx0 : x 0 = 1)
    (htree : ∀ i, 0 < i → i < cnt → ∃ p < i, ∃ j < k, x i = x p * g j)
    (hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, x q = x i * g j)
    (hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b) :
    Nat.card (closure (g '' {j | j < k})) = cnt :=
  card_of_mem_iff (mem_closure_iff_of_right_record h0 hx0 htree hcl) hinj

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem perm_eq_of_rep {n : ℕ} {P : Table} {σ τ : Equiv.Perm (Fin n)} (hσ : Rep n P σ)
    (hτ : Rep n P τ) : σ = τ := by
  ext ⟨i, hi⟩
  have h1 := hσ i hi
  rw [hτ i hi, idx_of_lt σ hi, idx_of_lt τ hi] at h1
  exact h1.symm

theorem eq_of_rep_eq {n w p q : ℕ} {σ : Equiv.Perm (Fin n)}
    (hp : canonK n w (mask w) (n * w) p = true) (hq : canonK n w (mask w) (n * w) q = true)
    (h1 : Rep n (tabT (unpack n w p)) σ) (h2 : Rep n (tabT (unpack n w q)) σ) : p = q := by
  have ht : tblEq n (tabT (unpack n w p)) (tabT (unpack n w q)) = true := by
    unfold tblEq
    rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    rw [h1 i hi, h2 i hi]
    exact beq_self_eq_true _
  rw [tblEq_unpack hp hq] at ht
  exact Nat.eq_of_beq_eq_true ht

theorem rep_pcomp {n w p q : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (hp : canonK n w (mask w) (n * w) p = true) (hq : canonK n w (mask w) (n * w) q = true)
    (h1 : Rep n (tabT (unpack n w p)) σ) (h2 : Rep n (tabT (unpack n w q)) τ) :
    Rep n (tabT (unpack n w (pcomp n w (mask w) p q))) (σ * τ) := by
  have h := Rep.compT h1 h2
  rwa [compT_tabT _ _ fun i _ => unpack_lt hq, CFSG.KC.BfsPin.compA_unpack hp hq] at h

theorem penumLeft_closure {n w k cnt cap : ℕ} {G GI T PL POS SRT SRI : ℕ → ℕ}
    {g : ℕ → Equiv.Perm (Fin n)} (hn : szOK n w = true) (hn32 : n < 2 ^ 32)
    (hg : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true ∧
      Rep n (tabT (unpack n w (G j))) (g j))
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true) :
    ∃ x : ℕ → Equiv.Perm (Fin n), x 0 = 1 ∧
      (∀ i < cnt, Rep n (tabT (unpack n w (T i))) (x i)) ∧
      (∀ a < cnt, ∀ b < cnt, x a = x b → a = b) ∧
      (∀ y, y ∈ closure (g '' {j | j < k}) ↔ ∃ i < cnt, x i = y) ∧
      Nat.card (closure (g '' {j | j < k})) = cnt := by
  classical
  unfold penumHdK at hh
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hh
  obtain ⟨hc0, -, hT0, -⟩ := hh
  have hT0' : T 0 = pidn n w := Nat.eq_of_beq_eq_true hT0
  have sp := fun i (hi : i < cnt) => penumPt_specH (hp i hi)
  have hid : Rep n (tabT (unpack n w (pidn n w))) (1 : Equiv.Perm (Fin n)) := by
    rw [← CFSG.KC.BfsPin.idA_eq hn, ← idT_tabT]
    exact Rep.idT hn32
  have hstep : ∀ i < cnt, ∀ j < k, ∀ σ : Equiv.Perm (Fin n), Rep n (tabT (unpack n w (T i))) σ →
      Rep n (tabT (unpack n w (stepK n w (mask w) false G GI j (T i)))) (g j * σ) :=
    fun i hi j hj σ h => rep_pcomp (hg j hj).1 (sp i hi).1 (hg j hj).2 h
  have hex : ∀ i < cnt, ∃ σ : Equiv.Perm (Fin n), Rep n (tabT (unpack n w (T i))) σ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, by rw [hT0']; exact hid⟩
      · obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
        obtain ⟨σ, hσ⟩ := ih _ h1 (by omega)
        exact ⟨g (labOf PL i) * σ, by rw [h3]; exact hstep _ (by omega) _ h2 σ hσ⟩
  let x : ℕ → Equiv.Perm (Fin n) := fun i => if h : i < cnt then (hex i h).choose else 1
  have hx : ∀ i < cnt, Rep n (tabT (unpack n w (T i))) (x i) := by
    intro i hi
    simp only [x, dif_pos hi]
    exact (hex i hi).choose_spec
  have hx0 : x 0 = 1 := perm_eq_of_rep (hx 0 hc0) (by rw [hT0']; exact hid)
  have htree : ∀ i, 0 < i → i < cnt → ∃ p < i, ∃ j < k, x i = g j * x p := by
    intro i hpos hi
    obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
    refine ⟨_, h1, _, h2, perm_eq_of_rep (hx i hi) ?_⟩
    rw [h3]
    exact hstep _ (by omega) _ h2 _ (hx _ (by omega))
  have hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, x q = g j * x i := by
    intro i hi j hj
    obtain ⟨h1, h2, -⟩ := (sp i hi).2.2.1 j hj
    refine ⟨_, h1, perm_eq_of_rep (hx _ h1) ?_⟩
    rw [h2]
    exact hstep i hi j hj _ (hx i hi)
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortH (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2.2
  have hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b := by
    intro a ha b hb e
    refine hinjT a ha b hb (eq_of_rep_eq (sp a ha).1 (sp b hb).1 (hx a ha) ?_)
    rw [e]
    exact hx b hb
  exact ⟨x, hx0, hx, hinj, mem_closure_iff_of_left_record hc0 hx0 htree hcl,
    card_closure_of_left_record hc0 hx0 htree hcl hinj⟩

end CFSG.KS.RecGroup

end
