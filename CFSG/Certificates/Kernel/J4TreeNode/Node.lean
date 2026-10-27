module

public import CFSG.Certificates.Kernel.J4TreeNode.Sound
public import CFSG.Milestones.ASVolI.C31.J4KWP0
public import CFSG.Milestones.ASVolI.C31.J4NP.Forest

public section

namespace CFSG.KC.J4TreeN

open CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc (omegaZ)

section Node


@[expose] noncomputable def Qc : Code := ⟨CFSG.KC.Co1F2.unpackR 12 QK⟩

@[expose] noncomputable def Qic : Code := ⟨CFSG.KC.Co1F2.unpackR 12 QiK⟩

@[expose] noncomputable def phi (x : J) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  burnsideJ4NP_codeMat Qc * burnsideJ4NP_rho x * burnsideJ4NP_codeMat Qic

theorem q_mul (hq : Nat.beq (M QK QiK) oneK = true) :
    burnsideJ4NP_codeMat Qc * burnsideJ4NP_codeMat Qic = 1 := by
  have h1 : RC 1 (M QK QiK) := by rw [Nat.eq_of_beq_eq_true hq]; exact rc_one
  have h := rc_eq (rc_mul (rfl : RC Qc QK) (rfl : RC Qic QiK)) h1
  rw [← burnsideJ4NP_codeMat_mul, h, burnsideJ4NP_codeMat_one]

theorem q_inv (hq : Nat.beq (M QK QiK) oneK = true) :
    burnsideJ4NP_codeMat Qic * burnsideJ4NP_codeMat Qc = 1 :=
  mul_eq_one_comm.mp (q_mul hq)

theorem phi_mul (hq : Nat.beq (M QK QiK) oneK = true) {x y : J} (hy : y ∈ Hj) :
    phi (x * y) = phi x * phi y := by
  unfold phi
  rw [burnsideJ4NP_rho_mul hy]
  calc burnsideJ4NP_codeMat Qc * (burnsideJ4NP_rho x * burnsideJ4NP_rho y) *
        burnsideJ4NP_codeMat Qic
      = burnsideJ4NP_codeMat Qc * burnsideJ4NP_rho x *
          (burnsideJ4NP_codeMat Qic * burnsideJ4NP_codeMat Qc) * burnsideJ4NP_rho y *
          burnsideJ4NP_codeMat Qic := by rw [q_inv hq]; simp [Matrix.mul_assoc]
    _ = _ := by simp [Matrix.mul_assoc]

theorem phi_one (hq : Nat.beq (M QK QiK) oneK = true) : phi 1 = 1 := by
  unfold phi
  rw [burnsideJ4NP_rho_one, Matrix.mul_one, q_mul hq]

theorem pk_lead {x : J} {X : ℕ} (hx : PK x X) (hu : utK (qconj X) = true)
    (hl : leadOf (qconj X) < 66) : UT (phi x) ∧ LeadAt (leadOf (qconj X)) (phi x) := by
  have hrc : RC (Qc * burnsideJ4NP_encJ x * Qic) (qconj X) :=
    rc_mul (rc_mul (rfl : RC Qc QK) hx.2) (rfl : RC Qic QiK)
  have hm : burnsideJ4NP_codeMat (Qc * burnsideJ4NP_encJ x * Qic) = phi x := by
    rw [burnsideJ4NP_codeMat_mul, burnsideJ4NP_codeMat_mul, burnsideJ4NP_encJ_of_mem hx.1,
      burnsideJ4NP_codeMat_enc]
    rfl
  rw [← hm]
  exact ⟨utK_spec hu hrc, leadOf_spec hl hrc⟩

theorem leads_zip (hq : Nat.beq (M QK QiK) oneK = true) :
    ∀ {xs : List J} {Xs : List ℕ}, List.Forall₂ PK xs Xs →
      (∀ X ∈ Xs, utK (qconj X) = true ∧ leadOf (qconj X) < 66) →
      (Xs.map fun X => leadOf (qconj X)).Pairwise (· < ·) →
      let zl := List.zipWith (fun x X => (x, leadOf (qconj X))) xs Xs
      (∀ y ∈ zl, y.1 ∈ Hj ∧ UT (phi y.1) ∧ LeadAt y.2 (phi y.1)) ∧
        zl.Pairwise (fun a b => a.2 < b.2) ∧ zl.map Prod.fst = xs ∧ zl.length = xs.length
  | [], [], .nil, _, _ => by simp
  | x :: xs, X :: Xs, .cons hx hxs, hu, hp => by
    intro zl
    have hu' : ∀ X ∈ Xs, utK (qconj X) = true ∧ leadOf (qconj X) < 66 :=
      fun X' hX' => hu X' (List.mem_cons_of_mem _ hX')
    rw [List.map_cons, List.pairwise_cons] at hp
    obtain ⟨h1, h2, h3, h4⟩ := leads_zip hq hxs hu' hp.2
    have hsnd : ∀ y ∈ List.zipWith (fun x X => (x, leadOf (qconj X))) xs Xs,
        ∃ X' ∈ Xs, y.2 = leadOf (qconj X') := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      refine ⟨Xs[i]'(by simp at hi; omega), List.getElem_mem _, ?_⟩
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · obtain ⟨hU, hL⟩ := pk_lead hx (hu X List.mem_cons_self).1 (hu X List.mem_cons_self).2
        exact ⟨hx.1, hU, hL⟩
      · exact h1 y hy
    · refine List.pairwise_cons.mpr ⟨fun y hy => ?_, h2⟩
      obtain ⟨X', hX', he⟩ := hsnd y hy
      rw [he]
      exact hp.1 _ (List.mem_map_of_mem hX')
    · simp only [zl, List.zipWith_cons_cons, List.map_cons, h3]
    · simp only [zl, List.zipWith_cons_cons, List.length_cons, h4]

theorem leads_inj (hq : Nat.beq (M QK QiK) oneK = true) {xs : List J} {Xs : List ℕ}
    (h2 : List.Forall₂ PK xs Xs) (hL : leadsOK Xs = true) :
    ∀ m m', m < 2 ^ xs.length → m' < 2 ^ xs.length → nwFrom 1 xs m = nwFrom 1 xs m' → m = m' := by
  obtain ⟨hu, hp⟩ := leadsOK_spec hL
  obtain ⟨h1, h2', h3, h4⟩ := leads_zip hq h2 hu hp
  intro m m' hm hm' he
  rw [← h3] at he
  rw [← h4] at hm hm'
  exact nw_injective (K := Hj) phi (fun x _ y hy => phi_mul hq hy) (phi_one hq) _ h1 h2' m m' hm
    hm' he

theorem forall₂_cc {T : Tabs} (hT : tabsOK T = true) :
    ∀ (l : List (ℕ × ℕ)), (∀ ce ∈ l, coordOK ce = true) →
      List.Forall₂ PK (l.map burnsideJ4NP_treeElt) (l.map (ccT T))
  | [], _ => .nil
  | ce :: l, h => .cons (pk_cc hT (h ce List.mem_cons_self))
      (forall₂_cc hT l fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem forall₂_exists {α β : Type*} {R : α → β → Prop} :
    ∀ {xs : List α} {Xs : List β}, List.Forall₂ R xs Xs → ∀ x ∈ xs, ∃ X ∈ Xs, R x X
  | [], [], .nil, _, h => by simp at h
  | y :: xs, Y :: Xs, .cons hy hs, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨Y, List.mem_cons_self, hy⟩
    · obtain ⟨X, hX, hR⟩ := forall₂_exists hs x hx
      exact ⟨X, List.mem_cons_of_mem _ hX, hR⟩

theorem forall₂_getD {α β : Type*} {R : α → β → Prop} {a : α} {b : β} :
    ∀ {xs : List α} {Xs : List β}, List.Forall₂ R xs Xs → ∀ i < xs.length,
      R (xs.getD i a) (Xs.getD i b)
  | [], [], .nil, i, h => by simp at h
  | _ :: _, _ :: _, .cons hy _, 0, _ => by simpa using hy
  | _ :: _, _ :: _, .cons _ hs, i + 1, h => by
    simpa using forall₂_getD hs i (by simpa using h)

theorem forall₂_length {α β : Type*} {R : α → β → Prop} {xs : List α} {Xs : List β}
    (h : List.Forall₂ R xs Xs) : xs.length = Xs.length := h.length_eq

theorem zip_all_getD {α β : Type*} {f : α × β → Bool} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (l₁.zip l₂).all f = true) (hl : l₁.length = l₂.length) :
    ∀ j < l₁.length, f (l₁.getD j a, l₂.getD j b) = true := by
  intro j hj
  refine List.all_eq_true.mp h _ ?_
  have hj2 : j < l₂.length := hl ▸ hj
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj2]
  have hz : j < (l₁.zip l₂).length := by simp [hj, hj2]
  have e : (l₁.zip l₂)[j] = (l₁[j], l₂[j]) := List.getElem_zip
  rw [← e]
  exact List.getElem_mem _

theorem getD_mem {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem _

theorem zip_all_mem {α β : Type*} {f : α × β → Bool} {l₁ : List α} {l₂ : List β} {a : α}
    (h : (l₁.zip l₂).all f = true) (hl : l₁.length = l₂.length) (ha : a ∈ l₁) :
    ∃ b ∈ l₂, f (a, b) = true := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj2 : j < l₂.length := hl ▸ hj
  refine ⟨l₂[j], List.getElem_mem _, List.all_eq_true.mp h _ ?_⟩
  have hz : j < (l₁.zip l₂).length := by simp [hj, hj2]
  have e : (l₁.zip l₂)[j] = (l₁[j], l₂[j]) := List.getElem_zip
  rw [← e]
  exact List.getElem_mem _

theorem forall₂_exists' {α β : Type*} {R : α → β → Prop} :
    ∀ {xs : List α} {Xs : List β}, List.Forall₂ R xs Xs → ∀ X ∈ Xs, ∃ x ∈ xs, R x X
  | [], [], .nil, _, h => by simp at h
  | y :: xs, Y :: Xs, .cons hy hs, X, hX => by
    rcases List.mem_cons.mp hX with rfl | hX
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨x, hx, hR⟩ := forall₂_exists' hs X hX
      exact ⟨x, List.mem_cons_of_mem _ hx, hR⟩

theorem mem_Hj_of {xs : List J} {Xs : List ℕ} (h : List.Forall₂ PK xs Xs) : ∀ x ∈ xs, x ∈ Hj :=
  fun x hx => by
    obtain ⟨X, -, hX⟩ := forall₂_exists h x hx
    exact hX.1

theorem basis_props {xs : List J} {Xs : List ℕ} (h : List.Forall₂ PK xs Xs)
    (hc : Xs.all (fun b => sqOneK b && Xs.all fun b' => commK b b') = true) :
    (∀ x ∈ xs, x * x = 1) ∧ ∀ x ∈ xs, ∀ y ∈ xs, x * y = y * x := by
  rw [List.all_eq_true] at hc
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨X, hX, hxX⟩ := forall₂_exists h x hx
    have := hc X hX
    rw [Bool.and_eq_true] at this
    exact (pk_sq hxX).mpr this.1
  · obtain ⟨X, hX, hxX⟩ := forall₂_exists h x hx
    obtain ⟨Y, hY, hyY⟩ := forall₂_exists h y hy
    have := hc X hX
    rw [Bool.and_eq_true, List.all_eq_true] at this
    exact (pk_comm hxX hyY).mpr (this.2 Y hY)

theorem mem_cent_closure {x : J} {l : List J} (hc : ∀ b ∈ l, x * b = b * x) :
    x ∈ Subgroup.centralizer ((Subgroup.closure {g | g ∈ l} : Subgroup J) : Set J) := by
  have hle : Subgroup.closure {g | g ∈ l} ≤ Subgroup.centralizer {x} :=
    (Subgroup.closure_le _).mpr fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hc b hb).symm
  exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

theorem comm_of_all {xs ys : List J} {Xs Ys : List ℕ} (hx : List.Forall₂ PK xs Xs)
    (hy : List.Forall₂ PK ys Ys) (hc : Xs.all (fun s => Ys.all fun b => commK s b) = true) :
    ∀ x ∈ xs, ∀ y ∈ ys, x * y = y * x := by
  intro x hxm y hym
  obtain ⟨X, hX, hxX⟩ := forall₂_exists hx x hxm
  obtain ⟨Y, hY, hyY⟩ := forall₂_exists hy y hym
  rw [List.all_eq_true] at hc
  exact (pk_comm hxX hyY).mpr (List.all_eq_true.mp (hc X hX) Y hY)

theorem mem_normalizer_of {n : J} {bl : List J}
    (h : ∀ b ∈ bl, n * b * n⁻¹ ∈ Subgroup.closure {g | g ∈ bl}) :
    n ∈ Subgroup.normalizer ((Subgroup.closure {g | g ∈ bl} : Subgroup J) : Set J) := by
  have hle : (Subgroup.closure {g | g ∈ bl}).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.closure {g | g ∈ bl} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [burnsideJ4KW_card_map_conj])
  exact burnsideJ4NP_map_conj_eq_iff.mp heq

theorem cent_sup (A : Subgroup J) (y : J) :
    Hj ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers y : Subgroup J) : Set J) =
      (Hj ⊓ Subgroup.centralizer (A : Set J)) ⊓ Subgroup.centralizer {y} := by
  rw [burnsideJ4NP_centralizer_sup_zpowers, inf_assoc]

theorem orbit_bound {K : Subgroup J} {sl : List J} {S SI : List ℕ} (hS : List.Forall₂ PK sl S)
    (hSI : List.Forall₂ (fun s X => PK s⁻¹ X) sl SI) (hsK : ∀ s ∈ sl, s ∈ K) {y : J} {Y : ℕ}
    (hy : PK y Y) {root : ℕ} {orb : List (ℕ × ℕ × ℕ × ℕ)} (h : orbOK S SI Y root orb = true) :
    orb.length * Nat.card ↥(K ⊓ Subgroup.centralizer {y}) ≤ Nat.card K := by
  classical
  obtain ⟨hroot, hsort, hcanon, hent⟩ := orbOK_spec h
  have hconj : ∀ d, ∀ i < orb.length, (orb.getD i default).2.2.2 = d →
      ∃ p ∈ K, PK (p * y * p⁻¹) (orb.getD i default).1 := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      by_cases hir : i = root
      · refine ⟨1, K.one_mem, ?_⟩
        rw [((hent i hi).1 hir).1]
        simpa using hy
      · have := ((hent i hi).2 hir).2.2.1
        omega
    | succ d ih =>
      intro i hi hd
      by_cases hir : i = root
      · have := ((hent i hi).1 hir).2
        omega
      obtain ⟨hp, hg, hdp, hc⟩ := (hent i hi).2 hir
      obtain ⟨p, hpK, hpp⟩ := ih _ hp (by omega)
      set g := (orb.getD i default).2.2.1
      have hg' : g < sl.length := by rw [forall₂_length hS]; exact hg
      have hs := forall₂_getD (a := 1) (b := 0) hS g hg'
      have hsi := forall₂_getD (a := 1) (b := 0) hSI g hg'
      refine ⟨sl.getD g 1 * p, K.mul_mem (hsK _ (getD_mem hg')) hpK, ?_⟩
      rw [hc]
      have e : sl.getD g 1 * p * y * (sl.getD g 1 * p)⁻¹ =
          sl.getD g 1 * (p * y * p⁻¹) * (sl.getD g 1)⁻¹ := by group
      rw [e]
      exact pk_mul (pk_mul hs hpp) hsi
  choose! q hqK hq using fun i hi => hconj _ i hi rfl
  let z : ℕ → J := fun i => q i * y * (q i)⁻¹
  have hinj : Set.InjOn z (Finset.range orb.length) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hc := pk_canon (hq i hi) (hq j hj) (hcanon _ (getD_mem hi))
      (hcanon _ (getD_mem hj)) hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := List.pairwise_iff_getElem.mp hsort i j (by simpa using hi) (by simpa using hj) hlt
      simp only [List.getElem_map] at this
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hc
      omega
    · have := List.pairwise_iff_getElem.mp hsort j i (by simpa using hj) (by simpa using hi) hlt
      simp only [List.getElem_map] at this
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hc
      omega
  have hcard := Finset.card_image_of_injOn hinj
  have := card_conj_le K y ((Finset.range orb.length).image z) (by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨q i, hqK i (Finset.mem_range.mp hi), rfl⟩)
  rwa [hcard, Finset.card_range] at this

theorem pk_prodMask {xs : List J} {Xs : List ℕ} (h : List.Forall₂ PK xs Xs) (m : ℕ) :
    PK (nwFrom 1 xs m) (prodMask Xs m) := pk_prodFrom h pk_one m

theorem cosetOK_spec {S : List ℕ} {L X u : ℕ} (h : cosetOK S L X u = true)
    (hsq : sqOneK X = true) (hu : u ≠ 0) : L.testBit u = true ∧ ∃ s ∈ S, commK s X = false := by
  unfold cosetOK at h
  have hne : (u != 0) = true := bne_iff_ne.mpr hu
  rw [hsq, hne] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true,
    Bool.not_eq_true'] at h
  exact h

theorem forall₂_inv {xs : List J} {Xs XIs : List ℕ} (h : List.Forall₂ PK xs Xs)
    (hi : (Xs.zip XIs).all (fun p => invK p.1 p.2) = true) (hl : XIs.length = Xs.length) :
    List.Forall₂ (fun s X => PK s⁻¹ X) xs XIs := by
  induction h generalizing XIs with
  | nil => cases XIs with
    | nil => exact .nil
    | cons => simp at hl
  | cons hx _ ih =>
    cases XIs with
    | nil => simp at hl
    | cons XI XIs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hi
      exact .cons (pk_inv hx hi.1) (ih hi.2 (by simpa using hl))

theorem kid_fact {T : Tabs} (hT : tabsOK T = true) (hq : Nat.beq (M QK QiK) oneK = true) {k n : ℕ}
    {B S SI NA : List ℕ} {bJ sJ NAJ : List J} (hB2 : List.Forall₂ PK bJ B)
    (hS2 : List.Forall₂ PK sJ S) (hSI2 : List.Forall₂ (fun s X => PK s⁻¹ X) sJ SI)
    (hNA2 : List.Forall₂ PK NAJ NA) (hbA : burnsideJ4NP_Rep k = Subgroup.closure {g | g ∈ bJ})
    (hsC : ∀ s ∈ sJ, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J))
    (hNAC : ∀ s ∈ NAJ, s ∈ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J))
    (hcard : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = 2 ^ n)
    {kd : KRec} (h : kidOK T B S SI NA n kd = true) :
    (kd.tgt = 0 → burnsideJ4NP_PrunedFact k (nwFrom 1 NAJ kd.u)) ∧
      (kd.tgt ≠ 0 → kd.tgt ∉ treeTopIds ∧ 1 ≤ kd.tgt ∧ kd.tgt ≤ treeN ∧
        burnsideJ4NP_MergeFact k kd.tgt (nwFrom 1 NAJ kd.u)) := by
  set C := Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J) with hC
  set y := nwFrom 1 NAJ kd.u with hy
  have hY : PK y (prodMask NA kd.u) := pk_prodFrom hNA2 pk_one kd.u
  have hyC : y ∈ C := nwFrom_mem hNAC C.one_mem _
  unfold kidOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, horb⟩, hk⟩ := h
  have hob := orbit_bound hS2 hSI2 hsC hY horb
  have hroot := (orbOK_spec horb).1
  have hcy : Hj ⊓ Subgroup.centralizer
      ((burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y : Subgroup J) : Set J) = C ⊓ Subgroup.centralizer {y} :=
    cent_sup _ y
  have hmemKy : ∀ t ∈ Hj, (∀ b ∈ bJ, t * b = b * t) → t * y = y * t →
      t ∈ Hj ⊓ Subgroup.centralizer
        ((burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y : Subgroup J) : Set J) := by
    intro t ht hb hty
    rw [hcy]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨ht, ?_⟩, ?_⟩
    · rw [hbA]
      exact mem_cent_closure hb
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hty
  have horb0 : 0 < kd.orb.length := by omega
  rw [hcard] at hob
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  ·
    rw [if_pos h0] at hk
    unfold prunedOK at hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨⟨⟨⟨⟨⟨⟨hct, hcb⟩, hcomm⟩, hlT⟩, hlZ⟩, hZ⟩, hcnt⟩, hfin⟩ := hk
    set tJ := kd.tC.map burnsideJ4NP_treeElt
    set zJ := kd.bC.map burnsideJ4NP_treeElt
    have hT2 : List.Forall₂ PK tJ (kd.tC.map (ccT T)) := forall₂_cc hT _ (List.all_eq_true.mp hct)
    have hZ2 : List.Forall₂ PK zJ (kd.bC.map (ccT T)) := forall₂_cc hT _ (List.all_eq_true.mp hcb)
    have hTZ2 := List.rel_append hT2 hZ2
    have hYB2 : List.Forall₂ PK (y :: bJ) (prodMask NA kd.u :: B) := .cons hY hB2
    have hc1 := comm_of_all hTZ2 hYB2 hcomm
    set Ky := Hj ⊓ Subgroup.centralizer
      ((burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y : Subgroup J) : Set J) with hKy
    have hinKy : ∀ t ∈ tJ ++ zJ, t ∈ Ky := fun t ht =>
      hmemKy t (mem_Hj_of hTZ2 t ht) (fun b hb => hc1 t ht b (List.mem_cons_of_mem _ hb))
        (hc1 t ht y List.mem_cons_self)
    have htKy : ∀ t ∈ tJ, t ∈ Ky := fun t ht => hinKy t (List.mem_append_left _ ht)
    have hzKy : ∀ z ∈ zJ, z ∈ Ky := fun z hz => hinKy z (List.mem_append_right _ hz)
    have hcardKy : Nat.card Ky ≤ 2 ^ tJ.length := by
      rw [hcy]
      have e : kd.orb.length * 2 ^ tJ.length = 2 ^ n := by simpa [tJ] using hcnt
      have := hob
      rw [← e] at this
      exact Nat.le_of_mul_le_mul_left this horb0
    have hall := eq_nw_of_card htKy (leads_inj hq hT2 hlT) hcardKy
    obtain ⟨hzsq, hzc⟩ : (∀ z ∈ zJ, z * z = 1) ∧ ∀ z ∈ zJ, ∀ t ∈ tJ ++ zJ, z * t = t * z := by
      rw [List.all_eq_true] at hZ
      refine ⟨fun z hz => ?_, fun z hz t ht => ?_⟩
      · obtain ⟨X, hX, hzX⟩ := forall₂_exists hZ2 z hz
        exact (pk_sq hzX).mpr (Bool.and_eq_true _ _ ▸ hZ X hX).1
      · obtain ⟨X, hX, hzX⟩ := forall₂_exists hZ2 z hz
        have := hZ X hX
        rw [Bool.and_eq_true] at this
        exact comm_of_all (.cons hzX .nil) hTZ2 (by simpa using this.2) z List.mem_cons_self t ht
    have hzΩ : ∀ z ∈ zJ, z ∈ omegaZ Ky := by
      intro z hz
      refine CFSG.Quasithin.J4Loc.mem_omegaZ.mpr ⟨hzKy z hz, fun w hw => ?_, hzsq z hz⟩
      obtain ⟨a, -, rfl⟩ := hall w hw
      have hmem : nwFrom 1 tJ a ∈ Subgroup.centralizer ({z} : Set J) := by
        refine nwFrom_mem (fun t ht => ?_) (Subgroup.one_mem _) a
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hzc z hz t (List.mem_append_left _ ht)).symm
      rw [Subgroup.mem_centralizer_singleton_iff] at hmem
      exact hmem.symm
    have hzinj := leads_inj hq hZ2 hlZ
    have hzlen : zJ.length = kd.bC.length := by simp [zJ]
    unfold burnsideJ4NP_PrunedFact
    by_cases he : kd.eflag = 1
    · rw [if_pos he, Bool.and_eq_true] at hfin
      right
      have hzE : ∀ z ∈ zJ, z ∈ omegaZ Ky ⊓ Eg uJ 11 := by
        intro z hz
        refine Subgroup.mem_inf.mpr ⟨hzΩ z hz, ?_⟩
        obtain ⟨X, hX, hzX⟩ := forall₂_exists hZ2 z hz
        rw [burnsideJ4NP_mem_Eg_iff hzX.1, ← burnsideJ4NP_encJ_of_mem hzX.1, inE_eq hzX.2]
        exact List.all_eq_true.mp hfin.1 X hX
      have h7 := card_ge_of_nw hzE hzinj
      have h7' : 7 ≤ zJ.length := by rw [hzlen]; simpa using Nat.le_of_ble_eq_true hfin.2
      calc 2 ^ 6 < 2 ^ 7 := by norm_num
        _ ≤ 2 ^ zJ.length := Nat.pow_le_pow_right (by norm_num) h7'
        _ ≤ _ := h7
    · rw [if_neg he] at hfin
      left
      have h11 := card_ge_of_nw hzΩ hzinj
      have h11' : 11 ≤ zJ.length := by rw [hzlen]; simpa using Nat.le_of_ble_eq_true hfin
      calc 2 ^ 10 < 2 ^ 11 := by norm_num
        _ ≤ 2 ^ zJ.length := Nat.pow_le_pow_right (by norm_num) h11'
        _ ≤ _ := h11
  ·
    rw [if_neg h0] at hk
    unfold mergeOK at hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨⟨⟨⟨⟨⟨htop, h1⟩, hN⟩, hco⟩, hinv⟩, hmsk⟩, hcnt⟩ := hk
    set hW := wordProd xJ (wordC 64 kd.h)
    have hHpk : PK hW (wordT T 64 kd.h) := pk_word hT 64 kd.h
    have hHi : PK hW⁻¹ kd.hI := pk_inv hHpk hinv
    have hTB := forall₂_cc hT _ (List.all_eq_true.mp hco)
    have hBY : List.Forall₂ PK (bJ ++ [y]) (B ++ [prodMask NA kd.u]) :=
      List.rel_append hB2 (.cons hY .nil)
    have hconj : ∀ x ∈ bJ ++ [y], hW⁻¹ * x * hW ∈ burnsideJ4NP_Rep kd.tgt := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hjl : j < B.length + 1 := by
        have := forall₂_length hBY
        simp only [List.length_append, List.length_singleton] at this hj
        omega
      have hm := List.all_eq_true.mp hmsk j (List.mem_range.mpr hjl)
      have hxX := forall₂_getD (a := 1) (b := 0) hBY j hj
      rw [List.getD_eq_getElem _ _ hj] at hxX
      have hl := pk_mul (pk_mul hHi hxX) hHpk
      have hr : PK (nwFrom 1 ((treeBasis kd.tgt).map burnsideJ4NP_treeElt) (kd.msk.getD j 0))
          (prodMask ((treeBasis kd.tgt).map (ccT T)) (kd.msk.getD j 0)) := pk_prodMask hTB _
      have he := pk_beq hl hr hm
      rw [he]
      exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) _
    refine ⟨fun hm => ?_, Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true hN, hW, word_mem 64 kd.h,
      ?_, ?_⟩
    · have := List.elem_eq_true_of_mem hm
      simp_all
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · rw [hbA, Subgroup.closure_le]
        intro b hb
        exact burnsideJ4KW_mem_map_conj.mpr (hconj b (List.mem_append_left _ hb))
      · exact burnsideJ4KW_mem_map_conj.mpr (hconj y (List.mem_append_right _ List.mem_cons_self))
    · rw [hcy]
      have := hob
      rw [← hcnt] at this
      exact Nat.le_of_mul_le_mul_left this horb0

theorem forall₂_word {T : Tabs} (hT : tabsOK T = true) :
    ∀ l : List ℕ, List.Forall₂ PK (l.map fun w => wordProd xJ (wordC 64 w)) (l.map (wordT T 64))
  | [] => .nil
  | w :: l => .cons (pk_word hT 64 w) (forall₂_word hT l)

theorem cover_forest {T : Tabs} (hT : tabsOK T = true) {B NA AI : List ℕ} {bJ NAJ AIJ : List J}
    (hB2 : List.Forall₂ PK bJ B) (hNA2 : List.Forall₂ PK NAJ NA) (hAI2 : List.Forall₂ PK AIJ AI)
    {A : Subgroup J} (hAdef : A = Subgroup.closure {g | g ∈ bJ}) (haw : ∀ v, nwFrom 1 AIJ v ∈ A)
    {D : NRec} (hnorm : normOK B (D.nW.map (wordT T 64)) D.nI D.nD = true)
    (hents : entsOK NA AI (D.nW.map (wordT T 64)) D.nI (D.kids.map KRec.u) [] 0 D.ents = true)
    {e : ℕ × ℕ × ℕ × ℕ × ℕ} (he : e ∈ D.ents) {u v : ℕ} (heu : e.1 = u) :
    ∃ y ∈ D.kids.map (fun kd => nwFrom 1 NAJ kd.u), ∃ n ∈ Hj,
      A ⊔ Subgroup.zpowers (nwFrom 1 NAJ u * nwFrom 1 AIJ v) =
        (A ⊔ Subgroup.zpowers y).map (MulAut.conj n).toMonoidHom := by
  set NJ := D.nW.map fun w => wordProd xJ (wordC 64 w) with hNJ
  set N := D.nW.map (wordT T 64) with hN
  have hN2 : List.Forall₂ PK NJ N := forall₂_word hT D.nW
  have hNH : ∀ n ∈ NJ, n ∈ Hj := mem_Hj_of hN2
  unfold normOK at hnorm
  rw [List.all_eq_true] at hnorm
  have hNinv : ∀ l < NJ.length, PK (NJ.getD l 1)⁻¹ (D.nI.getD l 0) := by
    intro l hl
    have h1 := hnorm l (List.mem_range.mpr (by rwa [← forall₂_length hN2]))
    rw [Bool.and_eq_true] at h1
    exact pk_inv (forall₂_getD hN2 l hl) h1.1
  have hnorml : ∀ l < NJ.length, NJ.getD l 1 ∈ Subgroup.normalizer (A : Set J) := by
    intro l hl
    have h1 := hnorm l (List.mem_range.mpr (by rwa [← forall₂_length hN2]))
    rw [Bool.and_eq_true, List.all_eq_true] at h1
    rw [hAdef]
    refine mem_normalizer_of fun b hb => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    have hjB : j < B.length := by rwa [← forall₂_length hB2]
    have h2 := h1.2 j (List.mem_range.mpr hjB)
    have hbX := forall₂_getD (a := 1) (b := 0) hB2 j hj
    rw [List.getD_eq_getElem _ _ hj] at hbX
    rw [pk_beq (pk_mul (pk_mul (forall₂_getD hN2 l hl) hbX) (hNinv l hl)) (pk_prodMask hB2 _) h2]
    exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) _
  set Ng := Subgroup.closure {n | n ∈ NJ} with hNg
  have hNgN : Ng ≤ Subgroup.normalizer (A : Set J) := by
    rw [hNg, Subgroup.closure_le]
    intro n hn
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hn
    have := hnorml l hl
    rwa [List.getD_eq_getElem _ _ hl] at this
  have hNgH : Ng ≤ Hj := (Subgroup.closure_le Hj).mpr hNH
  have hspec := entsOK_spec hents
  set F : ℕ → J := fun i => nwFrom 1 NAJ (D.ents.getD i default).1 with hF
  set par : ℕ → ℕ := fun i => (D.ents.getD i default).2.2.1
  set lab : ℕ → J := fun i => NJ.getD (D.ents.getD i default).2.2.2.1 1
  have hforest : ∀ i < D.ents.length, F i ∈ {y | y ∈ D.kids.map fun kd => nwFrom 1 NAJ kd.u} ∨
      (par i < i ∧ lab i ∈ Ng ∧ (lab i * F (par i) * (lab i)⁻¹)⁻¹ * F i ∈ A) := by
    intro i hi
    rcases hspec i hi with ⟨hk0, hkl, hku⟩ | ⟨-, hpar, hlab, heq⟩
    · left
      have hkl' : (D.ents.getD i default).2.1 - 1 < D.kids.length := by simpa using hkl
      refine List.mem_map.mpr ⟨D.kids.getD ((D.ents.getD i default).2.1 - 1) default,
        getD_mem hkl', ?_⟩
      simp only [F]
      rw [← hku, List.getD_eq_getElem _ _ hkl, List.getElem_map, List.getD_eq_getElem _ _ hkl']
    · right
      have hlabN : (D.ents.getD i default).2.2.2.1 < NJ.length := by
        rwa [forall₂_length hN2]
      refine ⟨hpar, Subgroup.subset_closure (getD_mem hlabN), ?_⟩
      have hl := pk_mul (pk_mul (forall₂_getD (a := 1) (b := 0) hN2 _ hlabN)
        (pk_prodMask hNA2 (D.ents.getD (D.ents.getD i default).2.2.1 default).1)) (hNinv _ hlabN)
      have hr := pk_mul (pk_prodMask hNA2 (D.ents.getD i default).1)
        (pk_prodMask hAI2 (D.ents.getD i default).2.2.2.2)
      have hJ := pk_eq hl (heq ▸ hr)
      simp only [lab, F, par]
      rw [hJ]
      have e2 : (nwFrom 1 NAJ (D.ents.getD i default).1 *
          nwFrom 1 AIJ (D.ents.getD i default).2.2.2.2)⁻¹ *
          nwFrom 1 NAJ (D.ents.getD i default).1 =
          (nwFrom 1 AIJ (D.ents.getD i default).2.2.2.2)⁻¹ := by group
      rw [e2]
      exact A.inv_mem (haw _)
  obtain ⟨i, hi, hei⟩ := List.getElem_of_mem he
  have hcov : ∀ x ∈ ({nwFrom 1 NAJ u * nwFrom 1 AIJ v} : Set J), ∃ i < D.ents.length,
      (F i)⁻¹ * x ∈ A := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨i, hi, ?_⟩
    simp only [F]
    rw [List.getD_eq_getElem _ _ hi, hei, heu, hx]
    have e2 : (nwFrom 1 NAJ u)⁻¹ * (nwFrom 1 NAJ u * nwFrom 1 AIJ v) = nwFrom 1 AIJ v := by group
    rw [e2]
    exact haw v
  obtain ⟨r, hr, n, hn, hrn⟩ := burnsideJ4NP_forest_cosets hNgN hforest hcov _ rfl
  exact ⟨r, hr, n, hNgH hn, hrn⟩

theorem node_core {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    (hq : Nat.beq (M QK QiK) oneK = true) {k : ℕ} {D : NRec} {bJ sJ NAJ AIJ : List J}
    {B S NA AI : List ℕ} {fl : List Bool} (hB2 : List.Forall₂ PK bJ B) (hS2 : List.Forall₂ PK sJ S)
    (hSI2 : List.Forall₂ (fun s X => PK s⁻¹ X) sJ D.sI)
    (hAdef : burnsideJ4NP_Rep k = Subgroup.closure {g | g ∈ bJ}) (hn : sJ.length = D.n)
    (hord' : treeOrd k = 2 ^ D.n) (hflen : fl.length = sJ.length) (hNAJ : filt fl sJ false = NAJ)
    (hAIJ : filt fl sJ true = AIJ) (hNA2 : List.Forall₂ PK NAJ NA)
    (hAI2 : List.Forall₂ PK AIJ AI)
    (hBc : B.all (fun b => sqOneK b && B.all fun b' => commK b b') = true)
    (hSB : S.all (fun s => B.all fun b => commK s b) = true) (hlead : leadsOK S = true)
    (hblen : (D.beta.length == AI.length) = true)
    (hbeta : (AI.zip D.beta).all (fun p => Nat.beq p.1 (prodMask B p.2)) = true)
    (hglen : (D.gamma.length == B.length) = true)
    (hgamma : (B.zip D.gamma).all
      (fun p => Nat.blt p.2 (2 ^ AI.length) && Nat.beq p.1 (prodMask AI p.2)) = true)
    (hnorm : normOK B (D.nW.map (wordT T 64)) D.nI D.nD = true)
    (hents : entsOK NA AI (D.nW.map (wordT T 64)) D.nI (D.kids.map KRec.u) [] 0 D.ents = true)
    (hnonF : D.nonF.all (nonFOK T.sx NA AI) = true)
    (hkids : D.kids.all (kidOK T B S D.sI NA D.n) = true)
    (hcos : cosetsOK S (coverBits D.ents D.nonF) NA = true) :
    burnsideJ4NP_NodeFacts k ∧ ∀ kd ∈ D.kids, kd.tgt ≠ 0 → burnsideJ4NP_EdgeFact k kd.tgt := by
  set A := burnsideJ4NP_Rep k with hA
  obtain ⟨hbsq, hbcomm⟩ := basis_props hB2 hBc
  have hbH := mem_Hj_of hB2
  have hAab : (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ ∀ x ∈ A, x * x = 1 := by
    rw [hAdef]
    exact burnsideJ4NP_closure_elemAb (s := {g | g ∈ bJ}) hbcomm hbsq
  have hAH : A ≤ Hj := by
    rw [hAdef]
    exact (Subgroup.closure_le Hj).mpr hbH
  set C := Hj ⊓ Subgroup.centralizer (A : Set J) with hC
  have hAC : A ≤ C := fun a ha => Subgroup.mem_inf.mpr ⟨hAH ha,
    Subgroup.mem_centralizer_iff.mpr fun b hb => hAab.1 b hb a ha⟩
  have hcentA : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a := fun a ha c hc =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 a ha)
  have hsC : ∀ s ∈ sJ, s ∈ C := by
    intro s hs
    refine Subgroup.mem_inf.mpr ⟨mem_Hj_of hS2 s hs, ?_⟩
    rw [hAdef]
    exact mem_cent_closure fun b hb => comm_of_all hS2 hB2 hSB s hs b hb
  have hinj := leads_inj hq hS2 hlead
  have hge : 2 ^ sJ.length ≤ Nat.card C := card_ge_of_nw hsC hinj
  rw [hn] at hge
  have hNAC : ∀ s ∈ NAJ, s ∈ C := fun s hs => hsC s (filt_mem (hNAJ ▸ hs))
  have hkid : ∀ kd ∈ D.kids, (kd.tgt = 0 → Nat.card C = 2 ^ D.n →
      burnsideJ4NP_PrunedFact k (nwFrom 1 NAJ kd.u)) ∧ (kd.tgt ≠ 0 → Nat.card C = 2 ^ D.n →
      kd.tgt ∉ treeTopIds ∧ 1 ≤ kd.tgt ∧ kd.tgt ≤ treeN ∧
        burnsideJ4NP_MergeFact k kd.tgt (nwFrom 1 NAJ kd.u)) := by
    intro kd hkd
    have hk := List.all_eq_true.mp hkids kd hkd
    exact ⟨fun h0 hc => (kid_fact hT hq hB2 hS2 hSI2 hNA2 hAdef hsC hNAC hc hk).1 h0,
      fun h0 hc => (kid_fact hT hq hB2 hS2 hSI2 hNA2 hAdef hsC hNAC hc hk).2 h0⟩
  refine ⟨⟨by rw [hord', Nat.log2_two_pow], by rw [hord']; exact hge, fun hcard => ?_⟩,
    fun kd hkd h0 => ⟨nwFrom 1 NAJ kd.u, fun hc => ((hkid kd hkd).2 h0 (hc.trans hord')).2.2.2⟩⟩
  rw [hord'] at hcard
  have hcard' : Nat.card C ≤ 2 ^ sJ.length := by rw [hn, hcard]
  have hall := eq_nw_of_card hsC hinj hcard'
  have hAIA : ∀ a ∈ AIJ, a ∈ A := by
    intro a ha
    obtain ⟨X, hX, haX⟩ := forall₂_exists hAI2 a ha
    obtain ⟨β, -, hβ⟩ := zip_all_mem hbeta (beq_iff_eq.mp hblen).symm hX
    rw [pk_beq haX (pk_prodMask hB2 β) hβ, hAdef]
    exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) β
  have hAIc : ∀ a ∈ filt fl sJ true, ∀ y ∈ C, a * y = y * a :=
    fun a ha y hy => hcentA a (hAIA a (hAIJ ▸ ha)) y hy
  have hdec : ∀ x ∈ C, ∃ u < 2 ^ NAJ.length, ∃ v < 2 ^ AIJ.length,
      x = nwFrom 1 NAJ u * nwFrom 1 AIJ v := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hall x hx
    have := nw_split fl sJ hflen hsC hAIc m hm
    rwa [hNAJ, hAIJ] at this
  have hAIsq : ∀ a ∈ AIJ, a * a = 1 := fun a ha => hAab.2 a (hAIA a ha)
  have hAIcomm : ∀ a ∈ AIJ, ∀ b ∈ AIJ, a * b = b * a :=
    fun a ha b hb => hAab.1 a (hAIA a ha) b (hAIA b hb)
  have haw : ∀ v, nwFrom 1 AIJ v ∈ A := fun v => nwFrom_mem hAIA A.one_mem v
  have hAle : A ≤ Subgroup.closure {g | g ∈ AIJ} := by
    rw [hAdef, Subgroup.closure_le]
    intro b hb
    obtain ⟨X, hX, hbX⟩ := forall₂_exists hB2 b hb
    obtain ⟨γ, -, hγ⟩ := zip_all_mem hgamma (beq_iff_eq.mp hglen).symm hX
    rw [Bool.and_eq_true] at hγ
    rw [pk_beq hbX (pk_prodMask hAI2 γ) hγ.2]
    exact nwFrom_mem (fun a ha => Subgroup.subset_closure ha) (Subgroup.one_mem _) γ
  have hAnw : ∀ a ∈ A, ∃ v < 2 ^ AIJ.length, a = nwFrom 1 AIJ v := by
    intro a ha
    have h1 : a ∈ Subgroup.closure {g | g ∈ AIJ} := hAle ha
    refine mem_closure_nw ?_ ?_ h1
    · intro x hx y hy
      exact hAIcomm x hx y hy
    · intro x hx
      exact hAIsq x hx
  have hR : ∀ u, PK (nwFrom 1 NAJ u) (prodMask NA u) := fun u => pk_prodMask hNA2 u
  have hRC : ∀ u, nwFrom 1 NAJ u ∈ C := fun u => nwFrom_mem hNAC C.one_mem u
  have hNAlen : NAJ.length = NA.length := forall₂_length hNA2
  unfold cosetsOK at hcos
  have hcosu := enumOK_spec hcos
  have hcos' : ∀ u < 2 ^ NAJ.length,
      cosetOK S (coverBits D.ents D.nonF) (prodMask NA u) u = true := by
    intro u hu
    have := hcosu u (hNAlen ▸ hu)
    simpa [prodMask] using this
  have hsqR : ∀ u v, (nwFrom 1 NAJ u * nwFrom 1 AIJ v) * (nwFrom 1 NAJ u * nwFrom 1 AIJ v) = 1 →
      nwFrom 1 NAJ u * nwFrom 1 NAJ u = 1 := by
    intro u v h
    have hc := hcentA _ (haw v) _ (hRC u)
    have hs := hAab.2 _ (haw v)
    have e : nwFrom 1 NAJ u * nwFrom 1 AIJ v * (nwFrom 1 NAJ u * nwFrom 1 AIJ v) =
        nwFrom 1 NAJ u * (nwFrom 1 AIJ v * nwFrom 1 NAJ u) * nwFrom 1 AIJ v := by group
    rw [e, hc] at h
    have e2 : nwFrom 1 NAJ u * (nwFrom 1 NAJ u * nwFrom 1 AIJ v) * nwFrom 1 AIJ v =
        nwFrom 1 NAJ u * nwFrom 1 NAJ u * (nwFrom 1 AIJ v * nwFrom 1 AIJ v) := by group
    rwa [e2, hs, mul_one] at h
  have hnc : ∀ u < 2 ^ NAJ.length, u ≠ 0 → nwFrom 1 NAJ u * nwFrom 1 NAJ u = 1 →
      (coverBits D.ents D.nonF).testBit u = true ∧
        ∃ s ∈ sJ, s * nwFrom 1 NAJ u ≠ nwFrom 1 NAJ u * s := by
    intro u hu hu0 hsq
    obtain ⟨hL, X, hX, hXc⟩ := cosetOK_spec (hcos' u hu) ((pk_sq (hR u)).mp hsq) hu0
    obtain ⟨s, hs, hsX⟩ := forall₂_exists' hS2 X hX
    exact ⟨hL, s, hs, fun he => by rw [(pk_comm hsX (hR u)).mp he] at hXc; exact Bool.noConfusion hXc⟩
  refine ⟨?_, D.kids.map fun kd => nwFrom 1 NAJ kd.u, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro x hx
      obtain ⟨hxC, hxc, hxs⟩ := CFSG.Quasithin.J4Loc.mem_omegaZ.mp hx
      obtain ⟨u, hu, v, hv, rfl⟩ := hdec x hxC
      by_cases hu0 : u = 0
      · rw [hu0, nwFrom_zero, one_mul]
        exact haw v
      · exfalso
        obtain ⟨-, s, hs, hne⟩ := hnc u hu hu0 (hsqR u v hxs)
        apply hne
        have h1 := hxc s (hsC s hs)
        have h2 := hcentA _ (haw v) s (hsC s hs)
        have h3 : nwFrom 1 NAJ u * s * nwFrom 1 AIJ v = s * nwFrom 1 NAJ u * nwFrom 1 AIJ v := by
          calc nwFrom 1 NAJ u * s * nwFrom 1 AIJ v = nwFrom 1 NAJ u * (nwFrom 1 AIJ v * s) := by
                rw [mul_assoc, ← h2]
            _ = nwFrom 1 NAJ u * nwFrom 1 AIJ v * s := by rw [mul_assoc]
            _ = s * (nwFrom 1 NAJ u * nwFrom 1 AIJ v) := h1
            _ = s * nwFrom 1 NAJ u * nwFrom 1 AIJ v := by rw [mul_assoc]
        exact (mul_right_cancel h3).symm
    · intro a ha
      exact CFSG.Quasithin.J4Loc.mem_omegaZ.mpr ⟨hAC ha, fun y hy => hcentA a ha y hy, hAab.2 a ha⟩
  ·
    intro y hy
    obtain ⟨kd, hkd, rfl⟩ := List.mem_map.mp hy
    by_cases h0 : kd.tgt = 0
    · exact Or.inl ((hkid kd hkd).1 h0 hcard)
    · obtain ⟨h1, h2, h3, h4⟩ := (hkid kd hkd).2 h0 hcard
      exact Or.inr ⟨kd.tgt, h2, h3, h1, h4⟩
  ·
    intro x hx hsq hxA ht
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec x hx
    have hu0 : u ≠ 0 := fun h0 => hxA (by rw [h0, nwFrom_zero, one_mul]; exact haw v)
    obtain ⟨hL, -⟩ := hnc u hu hu0 (hsqR u v hsq)
    have hvAI : v < 2 ^ AI.length := by rwa [← forall₂_length hAI2]
    rcases coverBits_spec hL with ⟨e, he, heu⟩ | ⟨c, hc, hcu⟩
    ·
      exact cover_forest hT hB2 hNA2 hAI2 hAdef haw hnorm hents he heu
    ·
      exfalso
      have hcOK := List.all_eq_true.mp hnonF c hc
      unfold nonFOK at hcOK
      have h1 := List.all_eq_true.mp hcOK v (List.mem_range.mpr hvAI)
      have hpk : PK (nwFrom 1 NAJ u * nwFrom 1 AIJ v) (M (prodMask NA c.1) (prodMask AI v)) := by
        rw [hcu]
        exact pk_mul (hR u) (pk_prodMask hAI2 v)
      rw [non2AK_spec h1 hpk.2 hsx] at ht
      exact Bool.noConfusion ht

theorem node_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {k : ℕ}
    {D : NRec} (h : nodeChk T k D = true) :
    burnsideJ4NP_NodeFacts k ∧ ∀ kd ∈ D.kids, kd.tgt ≠ 0 → burnsideJ4NP_EdgeFact k kd.tgt := by
  unfold nodeChk nodeChkWith at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hq, hcB⟩, hcS⟩, hord⟩, hlenS⟩, hlenI⟩, -⟩, -⟩, hBc⟩, hSI⟩,
    hSB⟩, hlead⟩, hblen⟩, hbeta⟩, hglen⟩, hgamma⟩, hnorm⟩, hents⟩, hnonF⟩, hkids⟩, hcos⟩ := h
  have hS2 := forall₂_cc hT _ (List.all_eq_true.mp hcS)
  have hn : (D.sC.map burnsideJ4NP_treeElt).length = D.n := by
    simpa using (beq_iff_eq.mp hlenS)
  exact node_core hT hsx hq (forall₂_cc hT _ (List.all_eq_true.mp hcB)) hS2
    (forall₂_inv hS2 hSI (by rw [← forall₂_length hS2, hn]; exact beq_iff_eq.mp hlenI)) rfl hn
    (beq_iff_eq.mp hord) (by simp [flagsOf, hn]) rfl rfl (filt_forall₂ false _ hS2)
    (filt_forall₂ true _ hS2) hBc hSB hlead hblen hbeta hglen hgamma hnorm hents hnonF hkids hcos

end Node

end CFSG.KC.J4TreeN
