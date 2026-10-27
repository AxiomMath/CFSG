module

public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Certificates.Kernel.Spor.RecGroup

public section

namespace CFSG.KC.ThreeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  Subgroup

variable {n w : Nat}

noncomputable def letW {A : Type} [Group A] (ga gb : A) (c : Nat) : A :=
  if Nat.beq c 0 then ga else if Nat.beq c 1 then gb else if Nat.beq c 2 then ga⁻¹ else gb⁻¹

noncomputable def wW {A : Type} [Group A] (ga gb : A) (W : Nat) : Nat → A
  | 0 => 1
  | k + 1 => wW ga gb W k * letW ga gb (wl W k)

theorem lt_letW {a b ai bi : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w a ga)
    (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) (c q : Nat)
    (hq : q < n) :
    CFSG.KC.Enum.lt w (mask w) a b ai bi c q = (letW ga gb c ⟨q, hq⟩ : Nat) := by
  unfold CFSG.KC.Enum.lt letW
  simp only [PK.nIf_eq]
  by_cases h0 : Nat.beq c 0 = true
  · rw [if_pos h0, if_pos h0]
    exact ha ⟨q, hq⟩
  by_cases h1 : Nat.beq c 1 = true
  · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1]
    exact hb ⟨q, hq⟩
  by_cases h2 : Nat.beq c 2 = true
  · rw [if_neg h0, if_neg h1, if_pos h2, if_neg h0, if_neg h1, if_pos h2]
    exact hai ⟨q, hq⟩
  · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h0, if_neg h1, if_neg h2]
    exact hbi ⟨q, hq⟩

theorem foldN_letW {a b ai bi W : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w a ga)
    (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) :
    ∀ k q (hq : q < n), foldN k (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) q =
      (wW ga gb W k ⟨q, hq⟩ : Nat) := by
  intro k
  induction k with
  | zero => exact fun q hq => by rw [PK.foldN_eq]; rfl
  | succ k ih =>
    intro q hq
    have e : ∀ (f : Nat → Nat → Nat) (s : Nat), foldN (k + 1) f s = foldN k f (f k s) :=
      fun f s => by
        rw [PK.foldN_eq, PK.foldN_eq, List.range_succ, List.foldr_append, List.foldr_cons,
          List.foldr_nil]
    rw [e, lt_letW ha hai hb hbi _ q hq, ih _ (letW ga gb (wl W k) ⟨q, hq⟩).2]
    rfl

theorem wpt_eq_foldN_wW (a b ai bi W : Nat) :
    ∀ len q, wpt w (mask w) a b ai bi W len q =
      foldN len (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) q := by
  intro len
  induction len with
  | zero => intro q; rw [PK.foldN_eq]; rfl
  | succ k ih =>
    intro q
    have e : ∀ (f : Nat → Nat → Nat) (s : Nat), foldN (k + 1) f s = foldN k f (f k s) :=
      fun f s => by
        rw [PK.foldN_eq, PK.foldN_eq, List.range_succ, List.foldr_append, List.foldr_cons,
          List.foldr_nil]
    rw [e, ← ih]
    change strictN _ _ = _
    rw [PF.strictN_eqP]
    rfl

theorem wpt_prep_wW {a b ai bi W len : Nat} {ga gb : Equiv.Perm (Fin n)} (ha : PRep n w a ga)
    (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) (q : Nat)
    (hq : q < n) : wpt w (mask w) a b ai bi W len q = (wW ga gb W len ⟨q, hq⟩ : Nat) := by
  rw [wpt_eq_foldN_wW]
  exact foldN_letW ha hai hb hbi len q hq

theorem wperm_prep_wW {a b ai bi W len : Nat} {ga gb : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n ≤ 2 ^ w) (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb)
    (hbi : PRep n w bi gb⁻¹) :
    PRep n w (wperm n w (mask w) a b ai bi W len) (wW ga gb W len) := by
  have hf := foldN_letW (W := W) ha hai hb hbi len
  intro x
  set F : Nat → Nat := fun p =>
    foldN len (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) p
  have hF : ∀ y < n, F y < 2 ^ w := fun y hy => by
    change foldN len _ y < 2 ^ w
    rw [hf y hy]
    exact Nat.lt_of_lt_of_le (wW ga gb W len ⟨y, hy⟩).2 hw
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w F hF (clog n) 0
  have e : wperm n w (mask w) a b ai bi W len = pmkT n w F (clog n) 0 := by
    unfold wperm pmk
    rw [PF.strictN_eqP]
  have hx : (x : Nat) < 2 ^ clog n := Nat.lt_of_lt_of_le x.2 hc
  rw [e, PF.pg_of_fld h (by simp only [hx, ↓reduceIte, Nat.zero_add, x.2]; exact hF x x.2)]
  simp only [hx, ↓reduceIte, Nat.zero_add, x.2]
  exact hf x x.2

theorem wW_mem {A : Type} [Group A] (ga gb : A) (W : Nat) :
    ∀ len, wW ga gb W len ∈ Subgroup.closure ({ga, gb} : Set A) := by
  intro len
  induction len with
  | zero => exact Subgroup.one_mem _
  | succ k ih =>
    refine Subgroup.mul_mem _ ih ?_
    have hga : ga ∈ Subgroup.closure ({ga, gb} : Set A) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hgb : gb ∈ Subgroup.closure ({ga, gb} : Set A) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    unfold letW
    split_ifs
    · exact hga
    · exact hgb
    · exact Subgroup.inv_mem _ hga
    · exact Subgroup.inv_mem _ hgb

theorem code_eq_of_prep {p q : Nat} {σ : Equiv.Perm (Fin n)}
    (hp : canonK n w (mask w) (n * w) p = true) (hq : canonK n w (mask w) (n * w) q = true)
    (h1 : PRep n w p σ) (h2 : PRep n w q σ) : p = q := by
  refine unpack_injH hp hq ?_
  unfold unpack
  congr 1
  funext i
  rw [h1 i, h2 i]

theorem penumRight_group (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {k cnt cap : ℕ}
    {G GI T PL POS SRT SRI : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)}
    (hG : ∀ j < k, G j = pidn n w) (hg : ∀ j < k, PRep n w (GI j) (g j))
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true) :
    ∃ x : ℕ → Equiv.Perm (Fin n), (∀ i < cnt, PRep n w (T i) (x i)) ∧
      (∀ a < cnt, ∀ b < cnt, x a = x b → a = b) ∧
      (∀ y, y ∈ closure (g '' {j | j < k}) ↔ ∃ i < cnt, x i = y) ∧
      Nat.card (closure (g '' {j | j < k})) = cnt := by
  classical
  unfold penumHdK at hh
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hh
  obtain ⟨hc0, -, hT0, -⟩ := hh
  have hT0' : T 0 = pidn n w := Nat.eq_of_beq_eq_true hT0
  have sp := fun i (hi : i < cnt) => penumPt_specH (hp i hi)
  have hn32 : n < 2 ^ 32 := by omega
  have hid : PRep n w (pidn n w) 1 := prep_pidn hn hw
  have hstep : ∀ j < k, ∀ t (σ : Equiv.Perm (Fin n)), PRep n w t σ →
      PRep n w (stepK n w (mask w) true G GI j t) (σ * g j) := by
    intro j hj t σ h
    have e : stepK n w (mask w) true G GI j t =
        pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j) := rfl
    rw [e, hG j hj]
    have h1 := prep_pcomp hn32 (prep_pcomp hn32 hid h) (hg j hj)
    rwa [one_mul] at h1
  have hex : ∀ i < cnt, ∃ σ : Equiv.Perm (Fin n), PRep n w (T i) σ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, by rw [hT0']; exact hid⟩
      · obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
        obtain ⟨σ, hσ⟩ := ih _ h1 (by omega)
        exact ⟨σ * g (labOf PL i), by rw [h3]; exact hstep _ h2 _ σ hσ⟩
  let x : ℕ → Equiv.Perm (Fin n) := fun i => if h : i < cnt then (hex i h).choose else 1
  have hx : ∀ i < cnt, PRep n w (T i) (x i) := by
    intro i hi
    simp only [x, dif_pos hi]
    exact (hex i hi).choose_spec
  have hx0 : x 0 = 1 := CFSG.KC.OrbGroup.prep_eq (hx 0 hc0) (by rw [hT0']; exact hid)
  have htree : ∀ i, 0 < i → i < cnt → ∃ p < i, ∃ j < k, x i = x p * g j := by
    intro i hpos hi
    obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
    exact ⟨_, h1, _, h2, CFSG.KC.OrbGroup.prep_eq (hx i hi)
      (by rw [h3]; exact hstep _ h2 _ _ (hx _ (by omega)))⟩
  have hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, x q = x i * g j := by
    intro i hi j hj
    obtain ⟨h1, h2, -⟩ := (sp i hi).2.2.1 j hj
    exact ⟨_, h1, CFSG.KC.OrbGroup.prep_eq (hx _ h1)
      (by rw [h2]; exact hstep j hj _ _ (hx i hi))⟩
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortH (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2.2
  have hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b := by
    intro a ha b hb e
    have h1 := hx a ha
    rw [e] at h1
    exact hinjT a ha b hb (code_eq_of_prep (sp a ha).1 (sp b hb).1 h1 (hx b hb))
  exact ⟨x, hx, hinj, CFSG.KS.RecGroup.mem_closure_iff_of_right_record hc0 hx0 htree hcl,
    CFSG.KS.RecGroup.card_closure_of_right_record hc0 hx0 htree hcl hinj⟩

end CFSG.KC.ThreeChain

end
