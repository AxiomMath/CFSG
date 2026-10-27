module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseEng
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowBlock

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

section FixedPoints

variable {α : Type*}

theorem card_fixedPoints_permCongr {β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) :
    Nat.card (Function.fixedPoints (e.permCongr σ)) = Nat.card (Function.fixedPoints σ) := by
  refine Nat.card_congr (e.symm.subtypeEquiv fun b => ?_)
  simp only [Function.mem_fixedPoints, Function.IsFixedPt, Equiv.permCongr_apply]
  exact e.eq_symm_apply.symm

theorem card_fixedPoints_conj (σ τ : Equiv.Perm α) :
    Nat.card (Function.fixedPoints (σ * τ * σ⁻¹)) = Nat.card (Function.fixedPoints τ) := by
  refine Nat.card_congr ((σ⁻¹).subtypeEquiv fun a => ?_)
  simp only [Function.mem_fixedPoints, Function.IsFixedPt, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def]
  exact σ.eq_symm_apply.symm

theorem card_fixedPoints_prodCongrLeft_mul [Finite α] (f : Z2 → Equiv.Perm α) (r : Z2) :
    Nat.card (Function.fixedPoints (Equiv.prodCongrLeft f *
        Equiv.prodCongr (Equiv.refl α) (Equiv.mulLeft r))) =
      if r = 1 then Nat.card (Function.fixedPoints (f 1)) +
        Nat.card (Function.fixedPoints (f z2)) else 0 := by
  have hfix : ∀ p : α × Z2, p ∈ Function.fixedPoints (Equiv.prodCongrLeft f *
      Equiv.prodCongr (Equiv.refl α) (Equiv.mulLeft r)) ↔
        f (r * p.2) p.1 = p.1 ∧ r * p.2 = p.2 := by
    intro p
    simp [Function.mem_fixedPoints, Function.IsFixedPt, Prod.ext_iff]
  split_ifs with hr
  · subst hr
    have e1 : Nat.card (Function.fixedPoints (Equiv.prodCongrLeft f *
        Equiv.prodCongr (Equiv.refl α) (Equiv.mulLeft (1 : Z2)))) =
        Nat.card {p : α × Z2 // f p.2 p.1 = p.1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun p => by rw [hfix]; simp)
    rw [e1, Nat.card_congr ((Equiv.prodComm α Z2).subtypeEquiv
      (p := fun p : α × Z2 => f p.2 p.1 = p.1) (q := fun p : Z2 × α => f p.1 p.2 = p.2)
      (fun p => Iff.rfl)),
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (q : Z2) (b : α) => f q b = b)),
      Nat.card_sigma]
    have hU : (Finset.univ : Finset Z2) = {1, z2} := by decide
    rw [hU, Finset.sum_pair z2_ne_one.symm]
    rfl
  · have : IsEmpty (Function.fixedPoints (Equiv.prodCongrLeft f *
        Equiv.prodCongr (Equiv.refl α) (Equiv.mulLeft r))) :=
      ⟨fun p => hr (by simpa using ((hfix p.1).1 p.2).2)⟩
    exact Nat.card_of_isEmpty

end FixedPoints

@[expose] noncomputable def fixW (a : ℕ) (x : W a) : ℕ :=
  Nat.card (Function.fixedPoints (repW a x))

theorem card_pts (a : ℕ) : Nat.card (Fin a → Z2) = 2 ^ a := by simp

theorem repW_succ_eq (n : ℕ) (x : W n ≀ᵣ Z2) :
    repW (n + 1) x = (Fin.succFunEquiv Z2 n).symm.permCongr
      (Equiv.prodCongrLeft (fun q : Z2 => repW n (x.left q)) *
        Equiv.prodCongr (Equiv.refl (Fin n → Z2)) (Equiv.mulLeft x.right)) := by
  let _ := MulAction.compHom (Fin n → Z2) (repW n)
  rw [repW_succ]
  congr 1
  ext p
  · simp [RegularWreathProduct.toPerm]
    rfl
  · simp [RegularWreathProduct.toPerm]

theorem fixW_zero (x : W 0) : fixW 0 x = 1 := by
  unfold fixW
  have : Unique (Function.fixedPoints (repW 0 x)) :=
    { default := ⟨default, Subsingleton.elim _ _⟩
      uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
  exact Nat.card_unique

theorem fixW_wr (a : ℕ) (u v : W a) (q : Z2) :
    fixW (a + 1) (wr u v q) = if q = 1 then fixW a u + fixW a v else 0 := by
  unfold fixW
  rw [repW_succ_eq, card_fixedPoints_permCongr, card_fixedPoints_prodCongrLeft_mul]
  simp

theorem fixW_conj (a : ℕ) (g x : W a) : fixW a (g * x * g⁻¹) = fixW a x := by
  unfold fixW
  rw [map_mul, map_mul, map_inv, card_fixedPoints_conj]

theorem fixW_one (a : ℕ) : fixW a 1 = 2 ^ a := by
  unfold fixW
  rw [map_one]
  have : Function.fixedPoints (1 : Equiv.Perm (Fin a → Z2)) = Set.univ := by
    ext x
    simp
  rw [this, Nat.card_univ, card_pts]

theorem fixW_le (a : ℕ) (x : W a) : fixW a x ≤ 2 ^ a := by
  unfold fixW
  rw [← card_pts]
  exact Finite.card_subtype_le _

theorem fixW_even_succ (a : ℕ) : ∀ x : W (a + 1), Even (fixW (a + 1) x) := by
  induction a with
  | zero =>
    intro x
    obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W 0) (q : Z2), x = wr u v q := ⟨_, _, _, (wr_eta x).symm⟩
    rw [fixW_wr]
    split_ifs
    · rw [fixW_zero, fixW_zero]
      exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  | succ a ih =>
    intro x
    obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W (a + 1)) (q : Z2), x = wr u v q :=
      ⟨_, _, _, (wr_eta x).symm⟩
    rw [fixW_wr]
    split_ifs
    · exact (ih u).add (ih v)
    · exact ⟨0, rfl⟩

theorem fixW_even (a : ℕ) (ha : 1 ≤ a) (x : W a) : Even (fixW a x) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  exact fixW_even_succ b x

theorem exists_odd_W (a : ℕ) (ha : 1 ≤ a) : ∃ x : W a, sgW a x = -1 := by
  induction a, ha using Nat.le_induction with
  | base => exact ⟨cc 1, sgW_cc_one⟩
  | succ a _ ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨wr x 1 1, ?_⟩
    rw [sgW_succ]
    simp [hx]

theorem even_sub_fixW (a : ℕ) (x : W a) : (2 ^ a - fixW a x) % 2 = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [fixW_zero]
    simp
  · obtain ⟨k, hk⟩ := fixW_even a ha x
    obtain ⟨m, hm⟩ : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
    have := fixW_le a x
    omega

theorem sgW_invol (a : ℕ) (x : W a) (hx : x * x = 1) :
    sgW a x = (-1) ^ ((2 ^ a - fixW a x) / 2) := by
  induction a with
  | zero =>
    rw [sgW_zero, fixW_zero]
    simp
  | succ a ih =>
    obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W a) (q : Z2), x = wr u v q := ⟨_, _, _, (wr_eta x).symm⟩
    rcases z2_cases q with rfl | rfl
    · have hx' : (wr u v 1 : W a ≀ᵣ Z2) * wr u v 1 = 1 := hx
      rw [wr_mul_one, ← wr_one, wr_inj] at hx'
      obtain ⟨hu, hv, -⟩ := hx'
      rw [sgW_succ, fixW_wr]
      simp only [wr_left_one, wr_left_z2, wr_right, ite_true, mul_one]
      rw [ih u hu, ih v hv, ← pow_add]
      congr 1
      have h1 := even_sub_fixW a u
      have h2 := even_sub_fixW a v
      have h3 := fixW_le a u
      have h4 := fixW_le a v
      rw [pow_succ]
      omega
    · have hx' : (wr u v z2 : W a ≀ᵣ Z2) * wr u v z2 = 1 := hx
      rw [wr_mul_z2, z2_mul_self, ← wr_one, wr_inj] at hx'
      obtain ⟨huv, -, -⟩ := hx'
      have hv : v = u⁻¹ := eq_inv_of_mul_eq_one_right huv
      subst hv
      rw [sgW_succ, fixW_wr]
      simp [z2_ne_one, pow_succ]

@[expose] def Fb (a : ℕ) : Set (W a) := {x | x * x = 1 ∧ fixW a x = 0}

theorem mem_Fb {a : ℕ} {x : W a} : x ∈ Fb a ↔ x * x = 1 ∧ fixW a x = 0 := Iff.rfl

theorem mem_Fb_wr (a : ℕ) (u v : W a) (q : Z2) :
    wr u v q ∈ Fb (a + 1) ↔ (q = 1 ∧ u ∈ Fb a ∧ v ∈ Fb a) ∨ (q = z2 ∧ v = u⁻¹) := by
  show (wr u v q : W a ≀ᵣ Z2) * wr u v q = 1 ∧ fixW (a + 1) (wr u v q) = 0 ↔ _
  rcases z2_cases q with rfl | rfl
  · rw [wr_mul_one, ← wr_one, wr_inj, fixW_wr]
    simp only [mem_Fb]
    simp [z2_ne_one.symm]
    tauto
  · rw [wr_mul_z2, z2_mul_self, ← wr_one, wr_inj, fixW_wr]
    simp [z2_ne_one]
    constructor
    · rintro ⟨h, -⟩
      exact eq_inv_of_mul_eq_one_right h
    · rintro rfl
      simp

theorem Fb_succ_eq (a : ℕ) : Fb (a + 1) = wrY (Fb a) := by
  ext y
  obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W a) (q : Z2), y = wr u v q := ⟨_, _, _, (wr_eta y).symm⟩
  refine (mem_Fb_wr a u v q).trans ?_
  constructor
  · rintro (⟨rfl, hu, hv⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨u, hu, v, hv, rfl⟩
    · exact Or.inr ⟨u, rfl⟩
  · rintro (⟨u', hu', v', hv', h⟩ | ⟨h, h'⟩)
    · obtain ⟨rfl, rfl, rfl⟩ := wr_inj.1 h
      exact Or.inl ⟨rfl, hu', hv'⟩
    · obtain ⟨rfl, rfl, rfl⟩ := wr_inj.1 h'
      exact Or.inr ⟨rfl, rfl⟩

theorem Fb_sq {a : ℕ} {x : W a} (hx : x ∈ Fb a) : x * x = 1 := hx.1

theorem Fb_conj {a : ℕ} (g : W a) {x : W a} (hx : x ∈ Fb a) : g * x * g⁻¹ ∈ Fb a := by
  refine ⟨?_, by rw [fixW_conj]; exact hx.2⟩
  have h : g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  rw [h, hx.1]
  group

theorem card_Fb_succ (a : ℕ) : Nat.card (Fb (a + 1)) = Nat.card (Fb a) ^ 2 + Nat.card (W a) := by
  let f : (Fb a × Fb a) ⊕ W a → Fb (a + 1) :=
    Sum.elim (fun p => ⟨wr p.1.1 p.2.1 1, (mem_Fb_wr a _ _ _).2 (Or.inl ⟨rfl, p.1.2, p.2.2⟩)⟩)
      (fun h => ⟨wr h h⁻¹ z2, (mem_Fb_wr a _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩)
  have hinj : Function.Injective f := by
    rintro (⟨u, v⟩ | h) (⟨u', v'⟩ | h') hh
    · have h1 : (wr u.1 v.1 1 : W a ≀ᵣ Z2) = wr u'.1 v'.1 1 := congrArg Subtype.val hh
      obtain ⟨h2, h3, -⟩ := wr_inj.1 h1
      rw [Subtype.ext h2, Subtype.ext h3]
    · have h1 : (wr u.1 v.1 1 : W a ≀ᵣ Z2) = wr h' h'⁻¹ z2 := congrArg Subtype.val hh
      exact absurd (wr_inj.1 h1).2.2 z2_ne_one.symm
    · have h1 : (wr h h⁻¹ z2 : W a ≀ᵣ Z2) = wr u'.1 v'.1 1 := congrArg Subtype.val hh
      exact absurd (wr_inj.1 h1).2.2 z2_ne_one
    · have h1 : (wr h h⁻¹ z2 : W a ≀ᵣ Z2) = wr h' h'⁻¹ z2 := congrArg Subtype.val hh
      rw [(wr_inj.1 h1).1]
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W a) (q : Z2), y = wr u v q := ⟨_, _, _, (wr_eta y).symm⟩
    rcases (mem_Fb_wr a u v q).1 hy with ⟨rfl, hu, hv⟩ | ⟨rfl, rfl⟩
    · exact ⟨Sum.inl (⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
    · exact ⟨Sum.inr u, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_sum, Nat.card_prod, sq]

theorem cc_one_eq : cc 1 = wr (1 : W 0) 1 z2 := by
  rw [cc_one]
  exact RegularWreathProduct.ext (funext fun _ => Subsingleton.elim _ _) rfl

theorem cc_mem_Fb (a : ℕ) (ha : 1 ≤ a) : cc a ∈ Fb a := by
  induction a, ha using Nat.le_induction with
  | base =>
    rw [cc_one_eq]
    exact (mem_Fb_wr 0 1 1 z2).2 (Or.inr ⟨rfl, inv_one.symm⟩)
  | succ a ha ih =>
    rw [cc_succ a ha, diag_eq_wr]
    exact (mem_Fb_wr a _ _ 1).2 (Or.inl ⟨rfl, ih, ih⟩)

theorem Fb_one : Fb 1 = {cc 1} := by
  ext x
  obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W 0) (q : Z2), x = wr u v q := ⟨_, _, _, (wr_eta x).symm⟩
  obtain rfl : u = 1 := Subsingleton.elim _ _
  obtain rfl : v = 1 := Subsingleton.elim _ _
  constructor
  · intro hx
    rcases (mem_Fb_wr 0 1 1 q).1 hx with ⟨-, hu, -⟩ | ⟨rfl, -⟩
    · have h := hu.2
      rw [fixW_zero] at h
      exact absurd h one_ne_zero
    · exact Set.mem_singleton_iff.2 cc_one_eq.symm
  · intro hx
    have h : (wr (1 : W 0) 1 q : W 0 ≀ᵣ Z2) = wr 1 1 z2 :=
      (Set.mem_singleton_iff.1 hx).trans cc_one_eq
    exact (mem_Fb_wr 0 1 1 q).2 (Or.inr ⟨(wr_inj.1 h).2.2, inv_one.symm⟩)

theorem cc_sq (a : ℕ) (ha : 1 ≤ a) : cc a * cc a = 1 := by
  induction a, ha using Nat.le_induction with
  | base => exact W_one_sq (cc 1)
  | succ a ha ih =>
    rw [cc_succ a ha]
    show (diag (cc a) : W a ≀ᵣ Z2) * diag (cc a) = 1
    rw [diag_mul_self, ih, diag_one]

theorem prodCnt_Fb_succ (a : ℕ) (g : W a) (hg2 : g * g = 1) (hgc : ∀ d : W a, d * g = g * d) :
    prodCnt (Fb (a + 1)) (diag g) =
      prodCnt (Fb a) g ^ 2 + 3 * (Nat.card (W a) * Nat.card (Fb a)) := by
  rw [Fb_succ_eq]
  exact prodCnt_wrY (Fb a) (fun x hx => hx.1) (fun x hx d => Fb_conj d hx) g hg2 hgc

theorem prodCnt_Fb_one_one : prodCnt (Fb 1) 1 = 0 := by
  unfold prodCnt
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨⟨a, b, c⟩, ha, hb, hc, h⟩ => ?_⟩
  rw [Fb_one, Set.mem_singleton_iff] at ha hb hc
  subst ha hb hc
  rw [cc_sq 1 le_rfl, one_mul] at h
  exact cc_ne_one 1 le_rfl h

theorem prodCnt_Fb_one_cc : prodCnt (Fb 1) (cc 1) = 1 := by
  have key : ∀ t : W 1 × W 1 × W 1, (t.1 ∈ Fb 1 ∧ t.2.1 ∈ Fb 1 ∧ t.2.2 ∈ Fb 1 ∧
      t.1 * t.2.1 * t.2.2 = cc 1) ↔ t = (cc 1, cc 1, cc 1) := by
    rintro ⟨a, b, c⟩
    simp only [Fb_one, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl, -⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, by rw [cc_sq 1 le_rfl, one_mul]⟩
  unfold prodCnt
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩,
    ⟨⟨(cc 1, cc 1, cc 1), rfl⟩⟩⟩

end CFSG.OddStandard.AltStdSec.SylowSn
