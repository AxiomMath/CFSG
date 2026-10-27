module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Tests
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Certificates.Kernel.RankThree.F2Perm

public section

namespace CFSG.ComponentClassification.RankTwoClassical.J2Std

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.Certificates.ChainArrays
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts okA inCert)

theorem natChain_pairwise : ∀ {L : List ℕ}, natChain L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: L, h => by
    rw [natChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := natChain_pairwise h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem arr_eq_of_rep {t u : Array ℕ} {g : Equiv.Perm (Fin 315)} (hts : t.size = 315)
    (hus : u.size = 315) (ht : Rep 315 t g) (hu : Rep 315 u g) : t = u := by
  refine Array.ext (hts.trans hus.symm) fun i hi _ => ?_
  rw [hts] at hi
  have e1 := ht.apply hi
  have e2 := hu.apply hi
  rw [getElem!_pos t i (by omega)] at e1
  rw [getElem!_pos u i (by omega)] at e2
  rw [e1, e2]

theorem conjW_size (w : ℕ) (x : Array ℕ) : (conjW w x).size = 315 := by
  simp [conjW, conjA, compA]


theorem cperm_mem {a b c : ℕ} (ha : a < 315) (hb : b < 160) (hc : c < 12) :
    cperm a b c ∈ CFSG.ComponentClassification.J2Cover.P := by
  have hm : ∀ i < 3, ∀ k < (lev 315 autStrong jBase i).pts.size,
      levT 315 autStrong jBase i k ∈ CFSG.ComponentClassification.J2Cover.P := fun i hi k hk => by
    rw [← autChain_originalSubgroup]
    exact CFSG.Sporadic.Schreier.levT_mem_original chainArrays_aut chainFacts_aut autChain_valid
      (by rw [baseCount_aut]; exact hi) hk
  obtain ⟨h0, h1, h2⟩ := lev_sizes
  exact mul_mem (mul_mem (hm 0 (by norm_num) a (by rw [h0]; exact ha))
    (hm 1 (by norm_num) b (by rw [h1]; exact hb))) (hm 2 (by norm_num) c (by rw [h2]; exact hc))

@[expose] noncomputable def wElt (w : ℕ) (hw : w < 604800) : GJ :=
  ⟨cperm (w / 1920) (w / 12 % 160) (w % 12), cperm_mem (by omega) (by omega) (by omega)⟩

theorem rep_wElt {w : ℕ} (hw : w < 604800) :
    Rep 315 (prod3 315 autLevels (w / 1920) (w / 12 % 160) (w % 12)) (wElt w hw).1 :=
  rep_prod3 (by omega) (by omega) (by omega)

theorem rep_conjW {w : ℕ} (hw : w < 604800) {t : Array ℕ} {x : GJ} (ht : Rep 315 t x.1) :
    Rep 315 (conjW w t) (wElt w hw * x * (wElt w hw)⁻¹).1 :=
  rep_conj (rep_wElt hw) (CFSG.RankThree.Native.F2.validA_of_rep (rep_wElt hw)) ht

theorem card_cent_le {X : Set GJ} {k : ℕ} (f : Fin k → GJ)
    (hf : ∀ i j, (∀ y ∈ X, f i * y * (f i)⁻¹ = f j * y * (f j)⁻¹) → i = j) :
    Nat.card (centralizer X) * k ≤ 604800 := by
  let φ : Fin k → GJ ⧸ centralizer X := fun i => (f i : GJ ⧸ centralizer X)
  have hφ : Function.Injective φ := by
    intro i j hij
    refine hf i j fun y hy => ?_
    have hc := mem_centralizer_iff.1 (QuotientGroup.eq.1 hij) y hy
    calc f i * y * (f i)⁻¹ = f i * (y * ((f i)⁻¹ * f j)) * (f j)⁻¹ := by group
      _ = f i * ((f i)⁻¹ * f j * y) * (f j)⁻¹ := by rw [hc]
      _ = f j * y * (f j)⁻¹ := by group
  have hk : k ≤ (centralizer X).index := by
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  calc Nat.card (centralizer X) * k ≤ Nat.card (centralizer X) * (centralizer X).index :=
        Nat.mul_le_mul_left _ hk
    _ = Nat.card GJ := card_mul_index _
    _ = 604800 := card_GJ

theorem card_cent_le_orb {X : Set GJ} {k : ℕ} {W : Array ℕ} {ps : List ℕ} {F : ℕ → Array ℕ}
    (hW : orbOK W k ps F = true)
    (hF : ∀ w w' (hw : w < 604800) (hw' : w' < 604800),
      (∀ y ∈ X, wElt w hw * y * (wElt w hw)⁻¹ = wElt w' hw' * y * (wElt w' hw')⁻¹) → F w = F w') :
    Nat.card (centralizer X) * k ≤ 604800 := by
  simp only [orbOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hW
  obtain ⟨⟨hs, hlt⟩, hc⟩ := hW
  have hlt' : ∀ i : Fin k, W[i.val]! < 604800 := fun i => by
    rw [getElem!_pos W i.val (by omega)]
    exact hlt i.val (by omega)
  have hp := List.pairwise_map.1 (natChain_pairwise hc)
  refine card_cent_le (fun i => wElt W[i.val]! (hlt' i)) fun i j h => ?_
  have e := hF _ _ (hlt' i) (hlt' j) h
  by_contra hij
  rw [getElem!_pos W i.val (by omega), getElem!_pos W j.val (by omega)] at e
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hl | hl
  · have := List.pairwise_iff_getElem.1 hp i.val j.val (by simp; omega) (by simp; omega) hl
    simp only [Array.getElem_toList] at this
    rw [e] at this
    exact lt_irrefl _ this
  · have := List.pairwise_iff_getElem.1 hp j.val i.val (by simp; omega) (by simp; omega) hl
    simp only [Array.getElem_toList] at this
    rw [e] at this
    exact lt_irrefl _ this

theorem card_cent_single {x : GJ} {t : Array ℕ} (ht : Rep 315 t x.1) {W : Array ℕ} {k : ℕ}
    {ps : List ℕ} (hW : orbOK W k ps (conjW · t) = true) :
    Nat.card (centralizer ({x} : Set GJ)) * k ≤ 604800 :=
  card_cent_le_orb hW fun w w' hw hw' h =>
    arr_eq_of_rep (conjW_size _ _) (conjW_size _ _) (rep_conjW hw ht)
      (by rw [h x rfl]; exact rep_conjW hw' ht)

theorem card_cent_pair {x y : GJ} {t u : Array ℕ} (ht : Rep 315 t x.1) (hu : Rep 315 u y.1)
    {W : Array ℕ} {k : ℕ} {ps : List ℕ}
    (hW : orbOK W k ps (fun w => conjW w t ++ conjW w u) = true) :
    Nat.card (centralizer ({x, y} : Set GJ)) * k ≤ 604800 :=
  card_cent_le_orb hW fun w w' hw hw' h => by
    rw [arr_eq_of_rep (conjW_size w t) (conjW_size w' t) (rep_conjW hw ht)
        (by rw [h x (Set.mem_insert _ _)]; exact rep_conjW hw' ht),
      arr_eq_of_rep (conjW_size w u) (conjW_size w' u) (rep_conjW hw hu)
        (by rw [h y (Set.mem_insert_of_mem _ rfl)]; exact rep_conjW hw' hu)]

theorem cent_eq_subOf {X : Set GJ} {gs : Array (Array ℕ)} {c : CFSG.Monster.B.Fischer.ArrCert}
    {k : ℕ} (henum : enumOK 315 gs keyPts c = true)
    (hok : ∀ k < gs.size, validA 315 gs[k]! = true ∧ inP gs[k]! = true)
    (hgen : ∀ k (hk : k < gs.size), gElt gs hok k hk ∈ centralizer X)
    (hk : c.pts.size * k = 604800) (hX : Nat.card (centralizer X) * k ≤ 604800) :
    centralizer X = subOf gs := by
  have hle : subOf gs ≤ centralizer X := subOf_le_of gs hok hgen
  have hcard : Nat.card (subOf gs) = c.pts.size := card_subOf (by decide) henum hok
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h] at hk; simp at hk
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hcard]
  exact Nat.le_of_mul_le_mul_right (hX.trans hk.symm.le) hk0

theorem foldl_conj_mem {c : CFSG.Monster.B.Fischer.ArrCert} {k : ℕ} (hk : k < c.pts.size)
    (hval : ∀ i < c.pts.size, validA 315 c.pts[i]! = true) (K : Subgroup (Equiv.Perm (Fin 315)))
    (hK : ∀ j < c.pts.size,
      permOfArr 315 c.pts[j]! * permOfArr 315 c.pts[k]! * (permOfArr 315 c.pts[j]!)⁻¹ ∈ K) :
    ∀ (w : List ℕ) (r : Array ℕ) (R : Equiv.Perm (Fin 315)), (∀ j ∈ w, j < c.pts.size) →
      Rep 315 r R → R ∈ K →
      ∃ X, Rep 315 (w.foldl (fun r j => compA 315 r (conjA 315 c.pts[j]! c.pts[k]!)) r) X ∧ X ∈ K
  | [], _, R, _, hr, hR => ⟨R, hr, hR⟩
  | j :: w, r, R, hw, hr, hR => by
    have hj := hw j List.mem_cons_self
    rw [List.foldl_cons]
    exact foldl_conj_mem hk hval K hK w _ _ (fun j' hj' => hw j' (List.mem_cons_of_mem _ hj'))
      (rep_compA hr (rep_conjA (hval j hj) (rep_of_validA (hval k hk)))) (K.mul_mem hR (hK j hj))

theorem isSimpleGroup_of_conjGenOK {gs : Array (Array ℕ)} {ps : List ℕ}
    {c : CFSG.Monster.B.Fischer.ArrCert} {W : Array (Array (List ℕ))} (hps : ∀ p ∈ ps, p < 315)
    (hc : enumOK 315 gs ps c = true) (hnt : 1 < c.pts.size) (h : conjGenOK c gs W = true) :
    IsSimpleGroup (Subgroup.closure (permsA 315 gs)) := by
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps hc
  set D := Subgroup.closure (permsA 315 gs)
  apply isSimpleGroup_of_conj_closure
  · by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hsub : (D : Set (Equiv.Perm (Fin 315))) ⊆ {1} := fun g hg => hall g hg
    have h1 : Nat.card D ≤ 1 := by
      calc Nat.card D = (D : Set (Equiv.Perm (Fin 315))).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1} : Set (Equiv.Perm (Fin 315))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    omega
  · intro e he he1
    obtain ⟨k, hk, rfl⟩ := (hmem e).1 he
    have hck := allLt_spec h hk
    simp only [Bool.or_eq_true] at hck
    rcases hck with hid | hck
    · exact absurd ((eqA_iff (rep_of_validA (hval k hk)) rep_idA).1 hid) he1
    · set K := Subgroup.closure {y | ∃ g ∈ D, g * permOfArr 315 c.pts[k]! * g⁻¹ = y}
      have hK : ∀ j < c.pts.size,
          permOfArr 315 c.pts[j]! * permOfArr 315 c.pts[k]! * (permOfArr 315 c.pts[j]!)⁻¹ ∈ K :=
        fun j hj => Subgroup.subset_closure ⟨_, (hmem _).2 ⟨j, hj, rfl⟩, rfl⟩
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' := allLt_spec hck hi
      rw [Bool.and_eq_true, List.all_eq_true] at hi'
      obtain ⟨hw, heq⟩ := hi'
      obtain ⟨X, hX, hXK⟩ := foldl_conj_mem hk hval K hK ((W.getD k #[]).getD i []) (idA 315) 1
        (fun j hj => by simpa using hw j hj) rep_idA K.one_mem
      have hgi := rep_of_validA (enumOK_gens_valid hc hi)
      dsimp only
      rw [← (eqA_iff hX hgi).1 heq]
      exact hXK

end CFSG.ComponentClassification.RankTwoClassical.J2Std

end
