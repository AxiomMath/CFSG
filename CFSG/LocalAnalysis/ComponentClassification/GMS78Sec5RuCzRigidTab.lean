module

public import Certificates.Data.GMS78RuCzRigidCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableSound
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzSign

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b
open CFSG.EvenSporadicStandard.Fin76b.AutETable (tab ix tab_getD ix_tab Realizes)

namespace RigidTab

theorem getElem!_eq_getD (a : Array ℕ) (i : ℕ) : a[i]! = a.getD i 0 := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rfl
  · rw [getElem!_neg a i h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

theorem getElem!_eq_getD' (a : Array (Array ℕ)) (i : ℕ) : a[i]! = a.getD i #[] := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rfl
  · rw [getElem!_neg a i h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

theorem getD_map_range {α : Type} {m k : ℕ} (f : ℕ → α) (d : α) (hk : k < m) :
    ((Array.range m).map f).getD k d = f k := by
  simp [Array.getD_eq_getD_getElem?, hk]

theorem size_compA (n : ℕ) (t u : Array ℕ) : (compA n t u).size = n := by simp [compA]

theorem size_idA (n : ℕ) : (idA n).size = n := by simp [idA]

variable {np : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}

@[expose] noncomputable def ptPerm (np : ℕ) (c : ArrCert) (a : ℕ) : Equiv.Perm (Fin np) :=
  permOfArr np c.pts[a]!

theorem enumOK_arr (h : enumOK np gs ps c = true) :
    arrCertOK (leftA np gs) gs.size (validA np) (keyA np ps) (idA np) c = true := by
  simp only [enumOK, Bool.and_eq_true] at h
  exact h.2

theorem permOfArr_leftA (h : enumOK np gs ps c = true) {k : ℕ} (hk : k < gs.size)
    {a : Array ℕ} (ha : validA np a = true) :
    permOfArr np (leftA np gs k a) = permOfArr np gs[k]! * permOfArr np a :=
  permOfArr_eq_of_rep (rep_compA (rep_of_validA (enumOK_gens_valid h hk)) (rep_of_validA ha))

theorem ptPerm_zero (h : enumOK np gs ps c = true) : ptPerm np c 0 = 1 := by
  rw [ptPerm, arrCertOK_root (enumOK_arr h)]
  exact permOfArr_eq_of_rep rep_idA

theorem ptPerm_tree (h : enumOK np gs ps c = true) {a : ℕ} (ha0 : 0 < a) (ha : a < c.pts.size) :
    c.par[a]! < a ∧ c.lab[a]! < gs.size ∧
      ptPerm np c a = permOfArr np gs[c.lab[a]!]! * ptPerm np c c.par[a]! := by
  obtain ⟨hp, hl, e⟩ := arrCertOK_tree (enumOK_arr h) ha0 ha
  refine ⟨hp, hl, ?_⟩
  rw [ptPerm, e, permOfArr_leftA h hl (arrCertOK_valid (enumOK_arr h) (hp.trans ha))]
  rfl

theorem ptPerm_edge (h : enumOK np gs ps c = true) {i : ℕ} (hi : i < c.pts.size) {k : ℕ}
    (hk : k < gs.size) :
    (c.edges[i]!)[k]! < c.pts.size ∧
      ptPerm np c (c.edges[i]!)[k]! = permOfArr np gs[k]! * ptPerm np c i := by
  obtain ⟨hj, e⟩ := arrCertOK_edge (enumOK_arr h) hi hk
  exact ⟨hj, by rw [ptPerm, e, permOfArr_leftA h hk (arrCertOK_valid (enumOK_arr h) hi)]; rfl⟩

theorem ptPerm_inj (hps : ∀ p ∈ ps, p < np) (h : enumOK np gs ps c = true) {a b : ℕ}
    (ha : a < c.pts.size) (hb : b < c.pts.size) (hab : ptPerm np c a = ptPerm np c b) :
    a = b :=
  arrCertOK_keys_inj (enumOK_arr h) ha hb
    (keyA_eq hps (arrCertOK_valid (enumOK_arr h) ha) (arrCertOK_valid (enumOK_arr h) hb) hab)

theorem leftIdx_get {n : ℕ} {k i : ℕ} (hi : i < n) :
    (leftIdx n c k)[i]! = (c.edges[i]!)[k]! := by
  rw [getElem!_eq_getD, leftIdx, tab_getD _ hi, ix, getElem!_eq_getD, getElem!_eq_getD']

theorem tabRow_spec (hps : ∀ p ∈ ps, p < np) (h : enumOK np gs ps c = true) {n : ℕ}
    (hn : c.pts.size = n) :
    ∀ f a, a < f → a < n → ∀ b < n,
      (tabRow n c ((Array.range gs.size).map (leftIdx n c)) f a)[b]! < n ∧
      ptPerm np c (tabRow n c ((Array.range gs.size).map (leftIdx n c)) f a)[b]! =
        ptPerm np c a * ptPerm np c b
  | 0, a, ha, _, _, _ => absurd ha (Nat.not_lt_zero a)
  | f + 1, a, ha, han, b, hb => by
    by_cases ha0 : a = 0
    · subst ha0
      simp only [tabRow, ↓reduceIte]
      rw [idA_get hb, ptPerm_zero h, one_mul]
      exact ⟨hb, rfl⟩
    · obtain ⟨hp, hl, e⟩ := ptPerm_tree h (Nat.pos_of_ne_zero ha0) (hn ▸ han)
      obtain ⟨ih1, ih2⟩ := tabRow_spec hps h hn f c.par[a]! (by omega) (by omega) b hb
      have e1 : ix c.par a = c.par[a]! := by rw [ix, getElem!_eq_getD]
      have e2 : ix c.lab a = c.lab[a]! := by rw [ix, getElem!_eq_getD]
      simp only [tabRow, ha0, ↓reduceIte, e1, e2]
      rw [compA_get hb, getD_map_range _ _ hl, leftIdx_get ih1]
      obtain ⟨he1, he2⟩ := ptPerm_edge h (by rw [hn]; exact ih1) hl
      exact ⟨hn ▸ he1, by rw [he2, ih2, e, mul_assoc]⟩

theorem tabOf_spec (hps : ∀ p ∈ ps, p < np) (h : enumOK np gs ps c = true) {n : ℕ}
    (hn : c.pts.size = n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    AutETable.mt (tabOf n c gs.size) a b < n ∧
      ptPerm np c (AutETable.mt (tabOf n c gs.size) a b) = ptPerm np c a * ptPerm np c b := by
  have e : AutETable.mt (tabOf n c gs.size) a b =
      (tabRow n c ((Array.range gs.size).map (leftIdx n c)) n a)[b]! := by
    rw [AutETable.mt, tabOf, getD_map_range _ _ ha, getElem!_eq_getD]
  rw [e]
  exact tabRow_spec hps h hn n a ha ha b hb

open Classical in
@[expose] noncomputable def ptElt (np : ℕ) (gs : Array (Array ℕ)) (c : ArrCert) (a : ℕ) :
    ↥(Subgroup.closure (permsA np gs)) :=
  if hm : ptPerm np c a ∈ Subgroup.closure (permsA np gs) then ⟨_, hm⟩ else 1

theorem coe_ptElt (hps : ∀ p ∈ ps, p < np) (h : enumOK np gs ps c = true) {a : ℕ}
    (ha : a < c.pts.size) : (ptElt np gs c a : Equiv.Perm (Fin np)) = ptPerm np c a := by
  have hm : ptPerm np c a ∈ Subgroup.closure (permsA np gs) :=
    ((enumOK_spec hps h).1 _).2 ⟨a, ha, rfl⟩
  simp only [ptElt, hm, ↓reduceDIte]

theorem realizes_tabOf (hps : ∀ p ∈ ps, p < np) (h : enumOK np gs ps c = true) {n : ℕ}
    (hn : c.pts.size = n) :
    Realizes (↥(Subgroup.closure (permsA np gs))) n (tabOf n c gs.size) (ptElt np gs c) where
  pos := hn ▸ arrCertOK_pos (enumOK_arr h)
  lt a b ha hb := (tabOf_spec hps h hn ha hb).1
  mul a b ha hb := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_ptElt hps h (hn ▸ (tabOf_spec hps h hn ha hb).1),
      coe_ptElt hps h (hn ▸ ha), coe_ptElt hps h (hn ▸ hb)]
    exact (tabOf_spec hps h hn ha hb).2
  inj a b ha hb hab := by
    apply ptPerm_inj hps h (hn ▸ ha) (hn ▸ hb)
    rw [← coe_ptElt hps h (hn ▸ ha), ← coe_ptElt hps h (hn ▸ hb), hab]
  surj x := by
    obtain ⟨i, hi, hx⟩ := ((enumOK_spec hps h).1 x).1 x.2
    exact ⟨i, hn ▸ hi, Subtype.ext (by rw [coe_ptElt hps h hi, ← hx]; rfl)⟩
  one := by
    apply Subtype.ext
    rw [coe_ptElt hps h (arrCertOK_pos (enumOK_arr h)), ptPerm_zero h]
    rfl

theorem card_closure_permsA (hps : ∀ p ∈ ps, p < np) (h : enumOK np gs ps c = true) :
    Nat.card (Subgroup.closure (permsA np gs)) = c.pts.size :=
  (enumOK_spec hps h).2.1

theorem ptPerm_gIdx (h : enumOK np gs ps c = true) {k : ℕ} (hk : k < gs.size) :
    gIdx c k < c.pts.size ∧ ptPerm np c (gIdx c k) = permOfArr np gs[k]! := by
  have h0 := arrCertOK_pos (enumOK_arr h)
  have e : gIdx c k = (c.edges[0]!)[k]! := by
    rw [gIdx, ix, getElem!_eq_getD, getElem!_eq_getD']
  rw [e]
  obtain ⟨h1, h2⟩ := ptPerm_edge h h0 hk
  exact ⟨h1, by rw [h2, ptPerm_zero h, mul_one]⟩

section Realize

variable {H H' : Type*} [Group H] [Group H'] {n : ℕ} {M : Array (Array ℕ)} {elt : ℕ → H}

theorem realizes_map (R : Realizes H n M elt) (e : H ≃* H') :
    Realizes H' n M (fun a => e (elt a)) where
  pos := R.pos
  lt := R.lt
  mul a b ha hb := by rw [R.mul a b ha hb, map_mul]
  inj a b ha hb hab := R.inj a b ha hb (e.injective hab)
  surj x := by
    obtain ⟨a, ha, hx⟩ := R.surj (e.symm x)
    exact ⟨a, ha, by rw [hx, MulEquiv.apply_symm_apply]⟩
  one := by rw [R.one, map_one]

@[expose] noncomputable def idx (R : Realizes H n M elt) (x : H) : ℕ := Classical.choose (R.surj x)

theorem idx_spec (R : Realizes H n M elt) (x : H) : idx R x < n ∧ elt (idx R x) = x :=
  Classical.choose_spec (R.surj x)

theorem idx_lt (R : Realizes H n M elt) (x : H) : idx R x < n := (idx_spec R x).1

theorem elt_idx (R : Realizes H n M elt) (x : H) : elt (idx R x) = x := (idx_spec R x).2

theorem idx_elt (R : Realizes H n M elt) {a : ℕ} (ha : a < n) : idx R (elt a) = a :=
  R.inj _ _ (idx_lt R _) ha (elt_idx R _)

theorem idx_mul (R : Realizes H n M elt) (x y : H) :
    idx R (x * y) = AutETable.mt M (idx R x) (idx R y) := by
  apply R.inj _ _ (idx_lt R _) (R.lt _ _ (idx_lt R x) (idx_lt R y))
  rw [elt_idx R, R.mul _ _ (idx_lt R x) (idx_lt R y), elt_idx R, elt_idx R]

theorem idx_one (R : Realizes H n M elt) : idx R 1 = 0 := by
  rw [← R.one, idx_elt R R.pos]

theorem idx_eq_iff (R : Realizes H n M elt) {x : H} {a : ℕ} (ha : a < n) :
    idx R x = a ↔ x = elt a := by
  constructor
  · rintro rfl
    rw [elt_idx R]
  · rintro rfl
    exact idx_elt R ha

@[expose] noncomputable def idxMap (R : Realizes H n M elt) (φ : H → H) (a : ℕ) : ℕ :=
  idx R (φ (elt a))

theorem idxMap_lt (R : Realizes H n M elt) (φ : H → H) (a : ℕ) : idxMap R φ a < n := idx_lt R _

theorem elt_idxMap (R : Realizes H n M elt) (φ : H → H) (a : ℕ) :
    elt (idxMap R φ a) = φ (elt a) := elt_idx R _

theorem idxMap_mt (R : Realizes H n M elt) (φ : H →* H) {a b : ℕ} (ha : a < n) (hb : b < n) :
    idxMap R φ (AutETable.mt M a b) = AutETable.mt M (idxMap R φ a) (idxMap R φ b) := by
  rw [idxMap, R.mul a b ha hb, map_mul, idx_mul]
  rfl

theorem idxMap_zero (R : Realizes H n M elt) (φ : H →* H) : idxMap R φ 0 = 0 := by
  rw [idxMap, R.one, map_one, idx_one]

theorem idxMap_comp (R : Realizes H n M elt) (φ ψ : H → H) (a : ℕ) :
    idxMap R φ (idxMap R ψ a) = idxMap R (φ ∘ ψ) a := by
  rw [idxMap, elt_idxMap R]
  rfl

@[expose] def InvOK (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) : Prop :=
  ∀ a < n, ix inv a < n ∧ AutETable.mt M a (ix inv a) = 0

theorem elt_inv (R : Realizes H n M elt) {inv : Array ℕ} (hinv : InvOK n M inv) {a : ℕ}
    (ha : a < n) : elt (ix inv a) = (elt a)⁻¹ := by
  have h := R.mul a (ix inv a) ha (hinv a ha).1
  rw [(hinv a ha).2, R.one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem letF_lt {inv : Array ℕ} (hinv : InvOK n M inv) {t : List ℕ}
    (ht : ∀ j, t.getD j 0 < n) (l : ℕ) : letF inv t l < n := by
  unfold letF
  split
  · exact ht _
  · exact (hinv _ (ht _)).1

theorem elt_letF (R : Realizes H n M elt) {inv : Array ℕ} (hinv : InvOK n M inv) {t : List ℕ}
    (ht : ∀ j, t.getD j 0 < n) (l : ℕ) :
    elt (letF inv t l) =
      if l % 2 = 0 then elt (t.getD (l / 2) 0) else (elt (t.getD (l / 2) 0))⁻¹ := by
  unfold letF
  split
  · rfl
  · exact elt_inv R hinv (ht _)

theorem foldl_lt (R : Realizes H n M elt) {inv : Array ℕ} (hinv : InvOK n M inv) {t : List ℕ}
    (ht : ∀ j, t.getD j 0 < n) (w : List ℕ) :
    ∀ acc, acc < n → w.foldl (fun acc l => AutETable.mt M acc (letF inv t l)) acc < n := by
  induction w with
  | nil => exact fun acc h => h
  | cons l w ih => exact fun acc h => ih _ (R.lt _ _ h (letF_lt hinv ht l))

theorem elt_foldl (R : Realizes H n M elt) {inv : Array ℕ} (hinv : InvOK n M inv) {t : List ℕ}
    (ht : ∀ j, t.getD j 0 < n) (w : List ℕ) :
    ∀ acc, acc < n → elt (w.foldl (fun acc l => AutETable.mt M acc (letF inv t l)) acc) =
      elt acc * Sign.evalC (fun j => elt (t.getD j 0)) w := by
  induction w with
  | nil => exact fun acc _ => by rw [List.foldl_nil, Sign.evalC_nil, mul_one]
  | cons l w ih =>
    intro acc h
    rw [List.foldl_cons, ih _ (R.lt _ _ h (letF_lt hinv ht l)), R.mul _ _ h (letF_lt hinv ht l),
      elt_letF R hinv ht, Sign.evalC_cons, mul_assoc]

theorem evW_lt (R : Realizes H n M elt) {inv : Array ℕ} (hinv : InvOK n M inv) {t : List ℕ}
    (ht : ∀ j, t.getD j 0 < n) (w : List ℕ) : evW M inv t w < n :=
  foldl_lt R hinv ht w 0 R.pos

theorem elt_evW (R : Realizes H n M elt) {inv : Array ℕ} (hinv : InvOK n M inv) {t : List ℕ}
    (ht : ∀ j, t.getD j 0 < n) (w : List ℕ) :
    elt (evW M inv t w) = Sign.evalC (fun j => elt (t.getD j 0)) w := by
  rw [evW, AutETable.ev, elt_foldl R hinv ht w 0 R.pos, R.one, one_mul]

theorem getD_map_lt {σ : ℕ → ℕ} (hσ : ∀ a, σ a < n) (h0 : 0 < n) (t : List ℕ) (j : ℕ) :
    (t.map σ).getD j 0 < n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases t[j]? with
  | none => exact h0
  | some a => exact hσ a

theorem getD_map_idxMap (R : Realizes H n M elt) (φ : H →* H) (t : List ℕ) (j : ℕ) :
    (t.map (idxMap R φ)).getD j 0 = idxMap R φ (t.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases t[j]? with
  | none => exact (idxMap_zero R φ).symm
  | some a => rfl

theorem evalC_map (φ : H →* H) (g : ℕ → H) (w : List ℕ) :
    φ (Sign.evalC g w) = Sign.evalC (fun j => φ (g j)) w := by
  induction w with
  | nil => rw [Sign.evalC_nil, Sign.evalC_nil, map_one]
  | cons l w ih =>
    rw [Sign.evalC_cons, Sign.evalC_cons, map_mul, ih]
    split <;> simp

theorem idxMap_evW (R : Realizes H n M elt) {inv : Array ℕ} (hinv : InvOK n M inv)
    (φ : H →* H) {t : List ℕ} (ht : ∀ j, t.getD j 0 < n) (w : List ℕ) :
    idxMap R φ (evW M inv t w) = evW M inv (t.map (idxMap R φ)) w := by
  have ht' : ∀ j, (t.map (idxMap R φ)).getD j 0 < n :=
    getD_map_lt (idxMap_lt R φ) R.pos t
  rw [idxMap, idx_eq_iff R (evW_lt R hinv ht' w), elt_evW R hinv ht, elt_evW R hinv ht',
    evalC_map]
  congr 1
  funext j
  rw [getD_map_idxMap, elt_idxMap R]

end Realize

section Hom

variable {H : Type*} [Group H] {n : ℕ} {M : Array (Array ℕ)} {elt : ℕ → H}

theorem homVal_eq {c : ArrCert} {gi t : List ℕ} {σ : ℕ → ℕ}
    (htree : ∀ a, 0 < a → a < n →
      ix c.par a < a ∧ gi.getD (ix c.lab a) 0 < n ∧
        AutETable.mt M (gi.getD (ix c.lab a) 0) (ix c.par a) = a ∧
        t.getD (ix c.lab a) 0 = σ (gi.getD (ix c.lab a) 0))
    (hσ : ∀ a b, a < n → b < n → σ (AutETable.mt M a b) = AutETable.mt M (σ a) (σ b))
    (hσ0 : σ 0 = 0) : ∀ f a, a < f → a < n → homVal M c t f a = σ a
  | 0, a, ha, _ => absurd ha (Nat.not_lt_zero a)
  | f + 1, a, ha, han => by
    by_cases ha0 : a = 0
    · subst ha0
      simp only [homVal, ↓reduceIte, hσ0]
    · obtain ⟨hp, hg, e, et⟩ := htree a (Nat.pos_of_ne_zero ha0) han
      have ih := homVal_eq htree hσ hσ0 f (ix c.par a) (by omega) (by omega)
      simp only [homVal, ha0, ↓reduceIte]
      rw [ih, et, ← hσ _ _ hg (by omega), e]

theorem ix_homTab {c : ArrCert} {t : List ℕ} {a : ℕ} (ha : a < n) :
    ix (homTab n M c t) a = homVal M c t n a := by
  rw [homTab, ix_tab _ ha]

end Hom

end RigidTab

end CFSG.ComponentClassification.GMS78.RuCz
