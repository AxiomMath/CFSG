module

public import Certificates.Data.Kernel.Spor.PRec
public import CFSG.Certificates.Kernel.Spor.RecGroup
public import CFSG.Certificates.Kernel.PermCent.OrbGroup

public section

namespace CFSG.KS.PRec

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Raw.Orb
  Subgroup

variable {n w : ℕ}

theorem wordsEqK_aux {m idn kS : ℕ} {S SI G : ℕ → ℕ} (ws : List (List Int)) :
    ∀ j0, List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun wd _ ih j => bAnd(wordEqK n w m idn S SI kS wd (G j), ih (Nat.succ j))) ws j0 =
        true → ∀ j < ws.length, wordEqK n w m idn S SI kS ws[j]! (G (j0 + j)) = true := by
  induction ws with
  | nil =>
    intro j0 _ j hj
    simp at hj
  | cons wd ws ih =>
    intro j0 h j hj
    have h' : bAnd(wordEqK n w m idn S SI kS wd (G j0),
        List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
          (fun wd _ ih j => bAnd(wordEqK n w m idn S SI kS wd (G j), ih (Nat.succ j))) ws
          (Nat.succ j0)) = true := h
    rw [bAnd_eq, Bool.and_eq_true] at h'
    rcases j with _ | j
    · simpa using h'.1
    · have := ih (Nat.succ j0) h'.2 j (by simpa using hj)
      have e : Nat.succ j0 + j = j0 + (j + 1) := by omega
      rw [e] at this
      simpa using this

theorem prep_wordsEqK (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {kS : ℕ} {S SI G : ℕ → ℕ}
    {gs : ℕ → Equiv.Perm (Fin n)} (hS : ∀ h < kS, PRep n w (S h) (gs h))
    (hSI : ∀ h < kS, PRep n w (SI h) (gs h)⁻¹) {ws : List (List Int)}
    (h : wordsEqK n w (mask w) (pidn n w) S SI kS ws G = true) :
    ∀ j < ws.length, PRep n w (G j)
      (Quiver.SchreierGraph.evalWord (fun h : Fin kS => gs h)
        (CFSG.Monster.B.Co2.toLetters kS ws[j]!)) := by
  intro j hj
  have h1 := wordsEqK_aux (n := n) (w := w) ws 0 h j hj
  rw [Nat.zero_add] at h1
  unfold wordEqK at h1
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨-, hl, he⟩ := h1
  rw [← Nat.eq_of_beq_eq_true he]
  exact (prep_wordK hn hw hS hSI _ hl).1

theorem recHdK_spec {m nw idn root N k : ℕ} {G GI : ℕ → ℕ} {cnt : ℕ} {T PL : ℕ → ℕ} {kS : ℕ}
    {S SI : ℕ → ℕ} {ws : List (List Int)}
    (h : recHdK n w m nw idn root N k G GI cnt T PL kS S SI ws = true) :
    penumHdK root cnt N T PL = true ∧ cnt = N ∧ k = ws.length ∧
      (∀ j < k, permOK n w m nw (G j) (GI j) = true) ∧
      wordsEqK n w m idn S SI kS ws G = true := by
  unfold recHdK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, allN_iff.1 h4, h5⟩

theorem recHdK_gens (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {root N k cnt kS : ℕ}
    {G GI T PL S SI : ℕ → ℕ} {ws : List (List Int)} {gs : ℕ → Equiv.Perm (Fin n)}
    (hS : ∀ h < kS, PRep n w (S h) (gs h)) (hSI : ∀ h < kS, PRep n w (SI h) (gs h)⁻¹)
    (h : recHdK n w (mask w) (n * w) (pidn n w) root N k G GI cnt T PL kS S SI ws = true) :
    penumHdK root cnt N T PL = true ∧ cnt = N ∧ k = ws.length ∧
      (∀ j < k, PRep n w (G j) (Quiver.SchreierGraph.evalWord (fun h : Fin kS => gs h)
        (CFSG.Monster.B.Co2.toLetters kS ws[j]!))) ∧
      (∀ j < k, PRep n w (GI j) (Quiver.SchreierGraph.evalWord (fun h : Fin kS => gs h)
        (CFSG.Monster.B.Co2.toLetters kS ws[j]!))⁻¹) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := recHdK_spec h
  have hG := prep_wordsEqK hn hw hS hSI h5
  refine ⟨h1, h2, h3, fun j hj => hG j (by omega), fun j hj => ?_⟩
  exact CFSG.KC.OrbGroup.prep_inv (hG j (by omega)) (h4 j hj)

theorem penumSlK_pt {m nw : ℕ} {conj : Bool} {G GI T PL POS SRT SRI : ℕ → ℕ} {k cnt lo len : ℕ}
    (h : penumSlK n w m nw conj G GI k cnt T PL POS SRT SRI lo len = true) {i : ℕ} (hlo : lo ≤ i)
    (hlen : i < lo + len) (hi : i < cnt) :
    penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true := by
  unfold penumSlK at h
  have h1 := allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h1
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, bIf_eq, if_pos (Nat.blt_eq.mpr hi)] at h1
  exact h1

theorem penumLeft_group (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {k cnt cap : ℕ}
    {G GI T PL POS SRT SRI : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ j < k, PRep n w (G j) (g j)) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true) :
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
      PRep n w (stepK n w (mask w) false G GI j t) (g j * σ) := by
    intro j hj t σ h
    have e : stepK n w (mask w) false G GI j t = pcomp n w (mask w) (G j) t := rfl
    rw [e]
    exact prep_pcomp hn32 (hg j hj) h
  have hex : ∀ i < cnt, ∃ σ : Equiv.Perm (Fin n), PRep n w (T i) σ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, by rw [hT0']; exact hid⟩
      · obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
        obtain ⟨σ, hσ⟩ := ih _ h1 (by omega)
        exact ⟨g (labOf PL i) * σ, by rw [h3]; exact hstep _ h2 _ σ hσ⟩
  let x : ℕ → Equiv.Perm (Fin n) := fun i => if h : i < cnt then (hex i h).choose else 1
  have hx : ∀ i < cnt, PRep n w (T i) (x i) := by
    intro i hi
    simp only [x, dif_pos hi]
    exact (hex i hi).choose_spec
  have hx0 : x 0 = 1 := CFSG.KC.OrbGroup.prep_eq (hx 0 hc0) (by rw [hT0']; exact hid)
  have htree : ∀ i, 0 < i → i < cnt → ∃ p < i, ∃ j < k, x i = g j * x p := by
    intro i hpos hi
    obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
    exact ⟨_, h1, _, h2, CFSG.KC.OrbGroup.prep_eq (hx i hi)
      (by rw [h3]; exact hstep _ h2 _ _ (hx _ (by omega)))⟩
  have hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, x q = g j * x i := by
    intro i hi j hj
    obtain ⟨h1, h2, -⟩ := (sp i hi).2.2.1 j hj
    exact ⟨_, h1, CFSG.KC.OrbGroup.prep_eq (hx _ h1)
      (by rw [h2]; exact hstep j hj _ _ (hx i hi))⟩
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortH (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2.2
  have hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b := by
    intro a ha b hb e
    refine hinjT a ha b hb (unpack_injH (sp a ha).1 (sp b hb).1 ?_)
    have h1 := hx a ha
    have h2 := hx b hb
    rw [e] at h1
    unfold unpack
    congr 1
    funext i
    rw [h1 i, h2 i]
  exact ⟨x, hx, hinj, CFSG.KS.RecGroup.mem_closure_iff_of_left_record hc0 hx0 htree hcl,
    CFSG.KS.RecGroup.card_closure_of_left_record hc0 hx0 htree hcl hinj⟩

theorem penumConj_class (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {k cnt cap X : ℕ}
    {G GI T PL POS SRT SRI : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)} {r : Equiv.Perm (Fin n)}
    (hg : ∀ j < k, PRep n w (G j) (g j)) (hgi : ∀ j < k, PRep n w (GI j) (g j)⁻¹)
    (hr : PRep n w X r) (hh : penumHdK X cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true) :
    ∃ c : ℕ → Equiv.Perm (Fin n), (∀ i < cnt, PRep n w (T i) (c i)) ∧
      (∀ a < cnt, ∀ b < cnt, c a = c b → a = b) ∧
      ∀ y, (∃ h ∈ closure (g '' {j | j < k}), h * r * h⁻¹ = y) ↔ ∃ i < cnt, c i = y := by
  classical
  unfold penumHdK at hh
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hh
  obtain ⟨hc0, -, hT0, -⟩ := hh
  have hT0' : T 0 = X := Nat.eq_of_beq_eq_true hT0
  have sp := fun i (hi : i < cnt) => penumPt_specH (hp i hi)
  have hn32 : n < 2 ^ 32 := by omega
  have hstep : ∀ j < k, ∀ t (σ : Equiv.Perm (Fin n)), PRep n w t σ →
      PRep n w (stepK n w (mask w) true G GI j t) (g j * σ * (g j)⁻¹) := by
    intro j hj t σ h
    have e : stepK n w (mask w) true G GI j t =
        pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j) := rfl
    rw [e]
    exact prep_pcomp hn32 (prep_pcomp hn32 (hg j hj) h) (hgi j hj)
  have hex : ∀ i < cnt, ∃ σ : Equiv.Perm (Fin n), PRep n w (T i) σ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨r, by rw [hT0']; exact hr⟩
      · obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
        obtain ⟨σ, hσ⟩ := ih _ h1 (by omega)
        exact ⟨g (labOf PL i) * σ * (g (labOf PL i))⁻¹, by rw [h3]; exact hstep _ h2 _ σ hσ⟩
  let c : ℕ → Equiv.Perm (Fin n) := fun i => if h : i < cnt then (hex i h).choose else 1
  have hc : ∀ i < cnt, PRep n w (T i) (c i) := by
    intro i hi
    simp only [c, dif_pos hi]
    exact (hex i hi).choose_spec
  have hc0r : c 0 = r := CFSG.KC.OrbGroup.prep_eq (hc 0 hc0) (by rw [hT0']; exact hr)
  have hgH : ∀ j < k, g j ∈ closure (g '' {j | j < k}) := fun j hj => subset_closure ⟨j, hj, rfl⟩
  have hreach : ∀ i < cnt, ∃ h ∈ closure (g '' {j | j < k}), h * r * h⁻¹ = c i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · refine ⟨1, one_mem _, ?_⟩
        rw [one_mul, inv_one, mul_one, hc0r]
      · obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
        obtain ⟨h, hmem, e⟩ := ih _ h1 (by omega)
        refine ⟨g (labOf PL i) * h, mul_mem (hgH _ h2) hmem, ?_⟩
        refine CFSG.KC.OrbGroup.prep_eq ?_ (hc i hi)
        have hs := hstep _ h2 _ _ (hc (parOf PL i) (by omega))
        rw [← e] at hs
        have eq : g (labOf PL i) * h * r * (g (labOf PL i) * h)⁻¹ =
            g (labOf PL i) * (h * r * h⁻¹) * (g (labOf PL i))⁻¹ := by group
        rw [eq, h3]
        exact hs
  have hcl : ∀ i < cnt, ∀ j < k, ∃ q < cnt, c q = g j * c i * (g j)⁻¹ := by
    intro i hi j hj
    obtain ⟨h1, h2, -⟩ := (sp i hi).2.2.1 j hj
    exact ⟨_, h1, CFSG.KC.OrbGroup.prep_eq (hc _ h1)
      (by rw [h2]; exact hstep j hj _ _ (hc i hi))⟩
  have hall : ∀ h ∈ closure (g '' {j | j < k}), ∀ i < cnt, ∃ q < cnt, c q = h * c i * h⁻¹ := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact fun i hi => hcl i hi j hj
    | one =>
      intro i hi
      exact ⟨i, hi, by group⟩
    | mul a b _ _ ha hb =>
      intro i hi
      obtain ⟨q, hq, e⟩ := hb i hi
      obtain ⟨q', hq', e'⟩ := ha q hq
      exact ⟨q', hq', by rw [e', e]; group⟩
    | inv a _ ha =>
      intro i hi
      obtain ⟨z, ⟨q, hq, rfl⟩, e⟩ := CFSG.KC.OrbGroup.surj_of_mapsTo
        (T := {y | ∃ i < cnt, c i = y}) (fun z => a * z * a⁻¹)
        (fun u v e => by simpa using e)
        (by
          rintro y ⟨i, hi, rfl⟩
          obtain ⟨q, hq, e⟩ := ha i hi
          exact ⟨q, hq, e⟩) (c i) ⟨i, hi, rfl⟩
      refine ⟨q, hq, ?_⟩
      rw [← e]
      group
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortH (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2.2
  have hinj : ∀ a < cnt, ∀ b < cnt, c a = c b → a = b := by
    intro a ha b hb e
    refine hinjT a ha b hb (unpack_injH (sp a ha).1 (sp b hb).1 ?_)
    have h1 := hc a ha
    have h2 := hc b hb
    rw [e] at h1
    unfold unpack
    congr 1
    funext i
    rw [h1 i, h2 i]
  refine ⟨c, hc, hinj, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨q, hq, e⟩ := hall h hh 0 hc0
    exact ⟨q, hq, by rw [e, hc0r]⟩
  · rintro ⟨i, hi, rfl⟩
    exact hreach i hi

theorem card_centralizer_of_class {H : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    (hr : r ∈ H) {cnt : ℕ} {c : ℕ → Equiv.Perm (Fin n)}
    (hcls : ∀ y, (∃ h ∈ H, h * r * h⁻¹ = y) ↔ ∃ i < cnt, c i = y)
    (hinj : ∀ a < cnt, ∀ b < cnt, c a = c b → a = b) :
    cnt * Nat.card (centralizer ({⟨r, hr⟩} : Set H)) = Nat.card H := by
  classical
  have hset : H.subtype '' conjugatesOf (⟨r, hr⟩ : H) = c '' (Finset.range cnt : Set ℕ) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨g, rfl⟩ := isConj_iff.1 hu
      obtain ⟨i, hi, e⟩ := (hcls _).1 ⟨g, g.2, rfl⟩
      refine ⟨i, by simpa using hi, ?_⟩
      rw [e]
      simp
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨h, hh, e⟩ := (hcls (c i)).2 ⟨i, by simpa using hi, rfl⟩
      refine ⟨⟨h, hh⟩ * ⟨r, hr⟩ * ⟨h, hh⟩⁻¹, isConj_iff.2 ⟨⟨h, hh⟩, rfl⟩, ?_⟩
      rw [← e]
      simp
  have hio : Set.InjOn c (Finset.range cnt : Set ℕ) :=
    fun a ha b hb e => hinj a (by simpa using ha) b (by simpa using hb) e
  have hcard : (conjugatesOf (⟨r, hr⟩ : H)).ncard = cnt := by
    rw [← Set.ncard_image_of_injective _ H.subtype_injective, hset, hio.ncard_image,
      Set.ncard_coe_finset, Finset.card_range]
  rw [← hcard, ← Subgroup.index_centralizer_eq_ncard, Subgroup.index_mul_card]

theorem centK_spec {m nw k : ℕ} {G : ℕ → ℕ} {z : ℕ} (h : centK n w m nw k G z = true) :
    ∀ j < k, pcomp n w m (G j) z = pcomp n w m z (G j) := by
  intro j hj
  have h1 := allN_iff.1 h j hj
  unfold commK at h1
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h1
  exact Nat.eq_of_beq_eq_true h1.2.2

theorem comm_of_centK (hn : n < 2 ^ 32) {k Z : ℕ} {G : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin n)}
    {z : Equiv.Perm (Fin n)} (hg : ∀ j < k, PRep n w (G j) (g j)) (hz : PRep n w Z z)
    (h : centK n w (mask w) (n * w) k G Z = true) : ∀ j < k, g j * z = z * g j := by
  intro j hj
  have h1 := prep_pcomp hn (hg j hj) hz
  rw [centK_spec h j hj] at h1
  exact CFSG.KC.OrbGroup.prep_eq h1 (prep_pcomp hn hz (hg j hj))

theorem closure_le_centralizer (hn : n < 2 ^ 32) {k Z : ℕ} {G : ℕ → ℕ}
    {g : ℕ → Equiv.Perm (Fin n)} {z : Equiv.Perm (Fin n)} (hg : ∀ j < k, PRep n w (G j) (g j))
    (hz : PRep n w Z z) (h : centK n w (mask w) (n * w) k G Z = true) :
    closure (g '' {j | j < k}) ≤ centralizer {z} := by
  rw [closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact comm_of_centK hn hg hz h j hj

theorem inPairK_iff {idn z s : ℕ} : inPairK idn z s = true ↔ s = idn ∨ s = z := by
  unfold inPairK
  rw [bIf_eq]
  cases h1 : Nat.beq s idn
  · have h1' : s ≠ idn := Nat.ne_of_beq_eq_false h1
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h
      exact Or.inr (Nat.eq_of_beq_eq_true h)
    · rintro (h | h)
      · exact absurd h h1'
      · subst h
        exact Nat.beq_refl s
  · simp only [↓reduceIte, true_iff]
    exact Or.inl (Nat.eq_of_beq_eq_true h1)

theorem anyHitK_spec {s i : ℕ} : ∀ L : List (ℕ × (ℕ → ℕ) × (ℕ → ℕ)), anyHitK s i L = true →
    ∃ r ∈ L, r32 r.2.2 i < r.1 ∧ r.2.1 (r32 r.2.2 i) = s
  | [], h => by
    have e : anyHitK s i [] = false := rfl
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | r :: L, h => by
    have e : anyHitK s i (r :: L) = bIf(hitK s i r, true, anyHitK s i L) := rfl
    rw [e, bIf_eq] at h
    split_ifs at h with hr
    · refine ⟨r, List.mem_cons_self .., ?_⟩
      unfold hitK at hr
      rw [CFSG.KS.Raw.Orb.strictB_eq, bAnd_eq, Bool.and_eq_true] at hr
      exact ⟨Nat.blt_eq.mp hr.1, Nat.eq_of_beq_eq_true hr.2⟩
    · obtain ⟨r', hr', h'⟩ := anyHitK_spec L h
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem sqCoverK_spec {m idn z : ℕ} {S : ℕ → ℕ} {L : List (ℕ × (ℕ → ℕ) × (ℕ → ℕ))} {cnt : ℕ}
    (h : sqCoverK n w m idn z S L cnt = true) :
    ∀ i < cnt, (pcomp n w m (S i) (S i) = idn ∨ pcomp n w m (S i) (S i) = z) →
      S i ≠ idn → S i ≠ z → ∃ r ∈ L, r32 r.2.2 i < r.1 ∧ r.2.1 (r32 r.2.2 i) = S i := by
  intro i hi hsq h1 h2
  unfold sqCoverK at h
  have hpt := allN_iff.1 h i hi
  unfold sqCoverPtK at hpt
  simp only [CFSG.KS.Raw.Orb.strictB_eq, bIf_eq, bAnd_eq] at hpt
  have hn : inPairK idn z (S i) = false := by
    cases e : inPairK idn z (S i)
    · rfl
    · rcases inPairK_iff.1 e with e | e
      · exact absurd e h1
      · exact absurd e h2
  rw [hn, inPairK_iff.2 hsq] at hpt
  exact anyHitK_spec L (by simpa using hpt)

theorem prep_of_rep_tab {P : ℕ} {t : CFSG.Sporadic.Th.Native.Table} {g : Equiv.Perm (Fin n)}
    (hr : CFSG.Sporadic.Th.Rep n t g)
    (h : allN n (fun i => Nat.beq (pg w (mask w) P i) (CFSG.Sporadic.Th.Native.ap t i)) = true) :
    PRep n w P g := by
  intro x
  rw [Nat.eq_of_beq_eq_true (allN_iff.1 h x x.2), hr x x.2, CFSG.Sporadic.Th.idx_of_lt _ x.2]
  rfl

end CFSG.KS.PRec

end
