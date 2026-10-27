module

public import CFSG.Certificates.Kernel.FixBoundK.Bridge
public import Certificates.Data.Kernel.FixBoundK.PairCp

public section

namespace CFSG.KC.FixBoundK.Pair

open CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.FixBoundK Subgroup

@[expose] noncomputable def srcR (RG s : ℕ) : ℕ := if s = 0 then 0 else fget RG (s - 1) 56

@[expose] noncomputable def srcGen (IV RG s j : ℕ) : Equiv.Perm (Fin 24) :=
  cperm (ivc IV (gI (srcR RG s) j))

@[expose] noncomputable def srcSet (IV RG s : ℕ) : Set (Equiv.Perm (Fin 24)) :=
  srcGen IV RG s '' {j | j < rk (srcR RG s)}

structure CheckFacts (rec : ℕ → ℕ) (IV IR RG CM BP nB : ℕ) (items : ℕ → List Item) : Prop where
  hmem : ∀ x, x ∈ sylowCert.pts ↔ PermArr x = true ∧ ∃ i < 1024, valF 120 (rec i) = keyP x
  hrec : ∀ i < 1024, PermArr (decP (valF 120 (rec i))) = true ∧
    keyP (decP (valF 120 (rec i))) = valF 120 (rec i)
  hlt : ∀ i j, i < j → j < 1024 → valF 120 (rec i) < valF 120 (rec j)
  hbp : ∀ k < nB, bp BP k < 24
  hbase : ∀ j < 1024, baseOK BP nB rec j = true
  hinv : ∀ i < 191, invOK IV IR rec 191 i = true
  hcm : ∀ a < 191, cmOK IV CM BP nB 191 a = true
  hrep : ∀ t < 751, ∃ r gl, repOK IV RG BP nB 191 t r gl = true
  hsrc : ∀ s ≤ 751, srcOK IV RG CM BP nB 1024 751 191 rec s (items s) = true
  hcp : ∀ s ≤ 751, ∀ it ∈ items s, cpItem nB it = true

noncomputable abbrev bpF (BP k : ℕ) (h : bp BP k < 24) : Fin 24 := ⟨bp BP k, h⟩

theorem rk_zero : rk 0 = 0 := rfl

theorem srcR_zero (RG : ℕ) : srcR RG 0 = 0 := rfl

theorem srcR_pos (RG : ℕ) {s : ℕ} (hs : s ≠ 0) : srcR RG s = fget RG (s - 1) 56 := by
  rw [srcR, if_neg hs]

theorem prodM_two_pow_six {G : Type*} [Group G] (h : ℕ → G) : prodM h (2 ^ 6) = 1 :=
  List.prod_eq_one fun b hb => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    have hj' : j < 6 := List.mem_range.1 hj
    have : ¬ 6 = j := by omega
    rw [if_neg (by rw [Nat.testBit_two_pow]; simpa using this)]

theorem testBit_lt {μ r j : ℕ} (hμ : μ < 2 ^ r) (hj : μ.testBit j = true) : j < r := by
  by_contra h
  have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hμ
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt h)))
  rw [this] at hj
  exact absurd hj (by simp)

variable {rec : ℕ → ℕ} {IV IR RG CM BP nB : ℕ} {items : ℕ → List Item}
  (F : CheckFacts rec IV IR RG CM BP nB items)
include F

theorem ivc_perm {i : ℕ} (hi : i < 191) : PermArr (decP (ivc IV i)) = true := by
  rw [(invOK_spec (F.hinv i hi)).1]
  exact (F.hrec _ (fget_IR_lt IR i)).1

theorem rec_mem {j : ℕ} (hj : j < 1024) :
    cperm (valF 120 (rec j)) ∈ sylowSub :=
  (mem_sylowSub_iff F.hmem F.hrec).2 ⟨j, hj, rfl⟩

theorem ivc_mem {i : ℕ} (hi : i < 191) :
    cperm (ivc IV i) ∈ sylowSub := by
  rw [(invOK_spec (F.hinv i hi)).1]
  exact rec_mem F (fget_IR_lt IR i)

theorem ivc_sq {i : ℕ} (hi : i < 191) : cperm (ivc IV i) * cperm (ivc IV i) = 1 := by
  ext p
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, cperm_apply (ivc_perm F hi),
    cperm_apply (ivc_perm F hi), (invOK_spec (F.hinv i hi)).2.1 p p.2]

theorem eq_of_bp {g h : Equiv.Perm (Fin 24)} (hg : g ∈ sylowSub)
    (hh : h ∈ sylowSub) (hgh : ∀ k (hk : k < nB), (g (bpF BP k (F.hbp k hk)) : ℕ) = h (bpF BP k (F.hbp k hk))) :
    g = h := by
  refine eq_of_agree sylowSub {p | ∃ k, ∃ hk : k < nB, p = bpF BP k (F.hbp k hk)} (fun g hg hfix => ?_) hg hh
    (fun b ⟨k, hk, e⟩ => by rw [e]; exact Fin.ext (hgh k hk))
  obtain ⟨j, hj, rfl⟩ := (mem_sylowSub_iff F.hmem F.hrec).1 hg
  have hX := (F.hrec j hj).1
  have hid := baseOK_spec (F.hbase j hj) fun k hk => by
    rw [← cperm_apply hX (bpF BP k (F.hbp k hk)), hfix _ ⟨k, hk, rfl⟩]
  rw [cperm, hid, idc_eq, decP_keyP PermArr_idArr, decode_idArr]

theorem commute_of_bp {A X : ℕ} (hA : PermArr (decP A) = true)
    (hX : PermArr (decP X) = true) (hAE : cperm A ∈ sylowSub) (hXE : cperm X ∈ sylowSub)
    (h : ∀ k < nB, ap A (ap X (bp BP k)) = ap X (ap A (bp BP k))) :
    Commute (cperm A) (cperm X) :=
  eq_of_bp F (mul_mem hAE hXE) (mul_mem hXE hAE) fun k hk => by
    simp only [Equiv.Perm.mul_apply, cperm_apply hA, cperm_apply hX]
    exact h k hk

theorem src_facts {t : ℕ} (ht : t ≤ 751) :
    rk (srcR RG t) ≤ 6 ∧ (∀ j < rk (srcR RG t), gI (srcR RG t) j < 191) ∧
      (∀ i < rk (srcR RG t), ∀ j < i, ∀ k < nB,
        ap (ivc IV (gI (srcR RG t) i)) (ap (ivc IV (gI (srcR RG t) j)) (bp BP k)) =
          ap (ivc IV (gI (srcR RG t) j)) (ap (ivc IV (gI (srcR RG t) i)) (bp BP k))) := by
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · rw [srcR_zero, rk_zero]
    exact ⟨by norm_num, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨r, gl, h⟩ := F.hrep (t - 1) (by omega)
  obtain ⟨hr, -, hgen, hcomm, hmove⟩ := repOK_spec h
  rw [srcR_pos RG (by omega : t ≠ 0), hr]
  refine ⟨?_, fun j hj => (hgen j hj).1, hcomm⟩
  by_contra h6
  obtain ⟨k, hk, hne⟩ := hmove (2 ^ 6) (by norm_num)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))
  apply hne
  have e := pA_apply (IV := IV) (R := fget RG (t - 1) 56) (μ := 2 ^ 6) (fun j hj hb => by
    rw [Nat.testBit_two_pow] at hb
    exact absurd (of_decide_eq_true hb) (by omega)) (bpF BP k (F.hbp k hk))
  rw [prodM_two_pow_six] at e
  exact e

theorem gen_perm {t j : ℕ} (ht : t ≤ 751) (hj : j < rk (srcR RG t)) :
    PermArr (decP (ivc IV (gI (srcR RG t) j))) = true :=
  ivc_perm F ((src_facts F ht).2.1 j hj)

theorem gen_mem {t j : ℕ} (ht : t ≤ 751)
    (hj : j < rk (srcR RG t)) : srcGen IV RG t j ∈ sylowSub :=
  ivc_mem F ((src_facts F ht).2.1 j hj)

theorem gen_sq {t j : ℕ} (ht : t ≤ 751) (hj : j < rk (srcR RG t)) :
    srcGen IV RG t j * srcGen IV RG t j = 1 :=
  ivc_sq F ((src_facts F ht).2.1 j hj)

theorem gen_comm {t i j : ℕ} (ht : t ≤ 751)
    (hi : i < rk (srcR RG t)) (hj : j < rk (srcR RG t)) :
    Commute (srcGen IV RG t i) (srcGen IV RG t j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact (commute_of_bp F (gen_perm F ht hj) (gen_perm F ht hi) (gen_mem F ht hj)
      (gen_mem F ht hi) ((src_facts F ht).2.2 j hj i h)).symm
  · exact Commute.refl _
  · exact commute_of_bp F (gen_perm F ht hi) (gen_perm F ht hj) (gen_mem F ht hi)
      (gen_mem F ht hj) ((src_facts F ht).2.2 i hi j h)

theorem prodM_mem_E {t μ : ℕ} (ht : t ≤ 751)
    (hμ : μ < 2 ^ rk (srcR RG t)) : prodM (srcGen IV RG t) μ ∈ sylowSub :=
  prodL_mem _ _ fun j _ hb => gen_mem F ht (testBit_lt hμ hb)

theorem prodM_mem_src {t μ : ℕ} (hμ : μ < 2 ^ rk (srcR RG t)) :
    prodM (srcGen IV RG t) μ ∈ closure (srcSet IV RG t) :=
  prodL_mem _ _ fun j _ hb => subset_closure ⟨j, testBit_lt hμ hb, rfl⟩

theorem pA_src {t μ : ℕ} (ht : t ≤ 751) (hμ : μ < 2 ^ rk (srcR RG t)) (p : Fin 24) :
    pA IV (srcR RG t) μ p = (prodM (srcGen IV RG t) μ p : ℕ) :=
  pA_apply (fun j _ hb => gen_perm F ht (testBit_lt hμ hb)) p

theorem step :
    ∀ s ∈ {s | s ≤ 751}, ∀ x ∈ sylowSub, x * x = 1 → (∀ y ∈ srcSet IV RG s, x * y = y * x) →
      x ∈ closure (srcSet IV RG s) ∨
        ∃ t ∈ {s | s ≤ 751}, ∃ g ∈ sylowSub,
          conjG g (closure (insert x (srcSet IV RG s))) = closure (srcSet IV RG t) := by
  intro s hs x hxE hxx hcomm
  have hs' : s ≤ 751 := hs
  by_cases hx1 : x = 1
  · exact Or.inl (hx1 ▸ one_mem _)
  obtain ⟨b, hb, rfl⟩ := exists_ivc_eq F.hmem F.hrec F.hlt F.hinv hxE hxx hx1
  have hxP := ivc_perm F hb
  have hbits : ∀ j < rk (srcR RG s), bit (fget CM (gI (srcR RG s) j) 191) b = true := by
    intro j hj
    by_contra hc
    obtain ⟨k, hk, hne⟩ := cmOK_spec (F.hcm _ ((src_facts F hs').2.1 j hj)) hb
      (Bool.eq_false_iff.2 hc)
    apply hne
    have e := congrArg (fun q : Equiv.Perm (Fin 24) => ((q (bpF BP k (F.hbp k hk)) : Fin 24) : ℕ))
      (hcomm _ ⟨j, hj, rfl⟩)
    simp only [Equiv.Perm.mul_apply, srcGen, cperm_apply hxP, cperm_apply (gen_perm F hs' hj)]
      at e
    exact e.symm
  obtain ⟨it, hit, hok⟩ := (srcOK_spec (F.hsrc s hs')).2 b hb hbits
  rcases itemOK_spec hok with ⟨-, hμ, hag⟩ | ⟨hpos, hle, hj, hpair⟩
  · refine Or.inl ?_
    have e : cperm (ivc IV b) = prodM (srcGen IV RG s) it.2.1 :=
      eq_of_bp F (ivc_mem F hb) (prodM_mem_E F hs' hμ) fun k hk => by
        rw [cperm_apply hxP, ← pA_src F hs' hμ]
        exact hag k hk
    rw [e]
    exact prodM_mem_src F hμ
  · refine Or.inr ⟨it.1, hle, cperm (valF 120 (rec it.2.1)), rec_mem F hj, ?_⟩
    set t := it.1 with htdef
    set r := rk (srcR RG s) with hrdef
    have ht0 : t ≠ 0 := by omega
    have hR' : srcR RG t = fget RG (t - 1) 56 := srcR_pos RG ht0
    obtain ⟨hrk, hcp, hmp, hsp⟩ := pairK_spec hpair
    have hrk' : rk (srcR RG t) = r + 1 := by rw [hR']; exact hrk
    have hGP := (F.hrec _ hj).1
    set G := valF 120 (rec it.2.1)
    have hcp24 : ∀ k < nB, fget it.2.2.1 k 5 < 24 := by
      have hc := F.hcp s hs' it hit
      have h0 : Nat.beq it.1 0 = false := by
        cases h : Nat.beq it.1 0
        · rfl
        · exact absurd (beq_iff.1 h) ht0
      unfold cpItem at hc
      rw [h0] at hc
      intro k hk
      exact blt_iff.1 ((allN_iff _ _).1 hc k hk)
    have hginv : ∀ k (hk : k < nB),
        (cperm G)⁻¹ (bpF BP k (F.hbp k hk)) = ⟨fget it.2.2.1 k 5, hcp24 k hk⟩ := by
      intro k hk
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact Fin.ext (by rw [cperm_apply hGP]; exact (hcp k hk).symm)
    have hconj : ∀ i < r + 1, cperm G * cperm (if i < r then ivc IV (gI (srcR RG s) i)
        else ivc IV b) * (cperm G)⁻¹ = prodM (srcGen IV RG t) (fget it.2.2.2.1 i 6) := by
      intro i hi
      have hYP : PermArr (decP (if i < r then ivc IV (gI (srcR RG s) i) else ivc IV b)) = true := by
        split_ifs with h
        · exact gen_perm F hs' h
        · exact hxP
      have hYE : cperm (if i < r then ivc IV (gI (srcR RG s) i) else ivc IV b) ∈ sylowSub := by
        split_ifs with h
        · exact gen_mem F hs' h
        · exact ivc_mem F hb
      have hμ : fget it.2.2.2.1 i 6 < 2 ^ rk (srcR RG t) := by rw [hrk']; exact (hmp i hi).1
      refine eq_of_bp F (mul_mem (mul_mem (rec_mem F hj) hYE) (inv_mem (rec_mem F hj)))
        (prodM_mem_E F (hle.trans le_rfl) hμ) fun k hk => ?_
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hginv k hk, cperm_apply hGP,
        cperm_apply hYP, ← pA_src F hle hμ, hR']
      exact (hmp i hi).2 k hk
    have hr6 : r + 1 ≤ 6 := hrk' ▸ (src_facts F hle).1
    have key := conjG_eq_of_pair (hs := srcGen IV RG s) (ht := srcGen IV RG t) (r := r)
      (x := cperm (ivc IV b)) (g := cperm G) (mp := fun i => fget it.2.2.2.1 i 6) hr6
      (fun i hi j hj => gen_comm F hle (hrk' ▸ hi) (hrk' ▸ hj))
      (fun i hi => gen_sq F hle (hrk' ▸ hi))
      (fun i hi => hrk' ▸ (hmp i hi).1)
      (fun i hi => by have := hconj i (by omega); rwa [if_pos hi] at this)
      (by have := hconj r (by omega); rwa [if_neg (lt_irrefl r)] at this)
      (fun i hi => ⟨fget it.2.2.2.2 i 6, by rw [← xorSel_eq]; exact hsp i hi⟩)
    rw [srcSet, srcSet, hrk']
    exact key

theorem exists_conj_eq_srcSet (P : Subgroup (Equiv.Perm (Fin 24)))
    (hPE : P ≤ sylowSub) (hP : CFSG.Open.IsElemAbelian 2 P) :
    ∃ t ≤ 751, ∃ g ∈ sylowSub, conjG g P = closure (srcSet IV RG t) := by
  have h0 : srcSet IV RG 0 = ∅ := by
    rw [srcSet, srcR_zero, rk_zero]
    simp
  obtain ⟨t, ht, g, hg, e⟩ := exists_conj_eq_closure sylowSub {s | s ≤ 751} (srcSet IV RG)
    (Nat.zero_le _) h0 (step F) P hPE hP
  exact ⟨t, ht, g, hg, e⟩

end CFSG.KC.FixBoundK.Pair

end
