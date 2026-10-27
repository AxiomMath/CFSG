
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvBase
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.U43Mod.LieOdd

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

theorem isInvA_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    isInvA n t (invCand n t) = true :=
  CFSG.KS.Raw.isInvA_of_rep h (CFSG.KS.Raw.rep_invCand h)

theorem treeG_induction_of_depth {root : X₀} {step : X₀ → ℕ → X₀} {par lab : Array ℕ}
    {nl n : ℕ} {dep : ℕ → ℕ} {Q : ℕ → X₀ → Prop} (h0 : Q 0 root)
    (hs : ∀ k < n, k ≠ 0 → par[k]! < n ∧ dep par[k]! < dep k ∧
      ∀ g, Q par[k]! g → Q k (step g (lab[k]! % nl))) :
    ∀ f, ∀ k < n, dep k ≤ f → Q k (treeG root step par lab nl f k) := by
  intro f
  induction f with
  | zero =>
    intro k hk hd
    by_cases hk0 : k = 0
    · rw [hk0]
      exact h0
    · have := (hs k hk hk0).2.1
      omega
  | succ f ih =>
    intro k hk hd
    by_cases hk0 : k = 0
    · rw [hk0]
      exact h0
    · obtain ⟨hp, hdp, hv⟩ := hs k hk hk0
      rw [treeG, if_neg hk0]
      exact hv _ (ih _ hp (by omega))

theorem closedOK_of {T : ℕ → Array ℕ} {tbl : Array ℕ} {n nl : ℕ}
    {step : Array ℕ → ℕ → Array ℕ} {x : ℕ → Equiv.Perm (Fin 820)}
    {sG : Equiv.Perm (Fin 820) → ℕ → Equiv.Perm (Fin 820)}
    (hT : ∀ k < n, Rep 820 (T k) (x k))
    (hs : ∀ k < n, ∀ l < nl, Rep 820 (step (T k) l) (sG (x k) l))
    (h : ∀ k < n, ∀ l < nl, tbl[k * nl + l]! < n ∧ x tbl[k * nl + l]! = sG (x k) l) :
    closedOK T tbl n nl step = true := by
  simp only [closedOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro k hk l hl
  obtain ⟨hlt, he⟩ := h k hk l hl
  exact ⟨hlt, (eqA_iff (hT _ hlt) (hs k hk l hl)).2 he⟩

theorem distinctOK_of {T : ℕ → Array ℕ} {n : ℕ} {x : ℕ → Equiv.Perm (Fin 820)}
    (hT : ∀ k < n, Rep 820 (T k) (x k))
    (hinj : ∀ i < n, ∀ j < n, x i ⟨0, by norm_num⟩ = x j ⟨0, by norm_num⟩ →
      x i ⟨1, by norm_num⟩ = x j ⟨1, by norm_num⟩ → x i ⟨9, by norm_num⟩ = x j ⟨9, by norm_num⟩ →
      i = j) :
    distinctOK T n = true := by
  unfold distinctOK
  refine decide_eq_true ?_
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj e
  have hi : i < n := List.mem_range.1 hi
  have hj : j < n := List.mem_range.1 hj
  simp only [fpKey, List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e9⟩ := e
  rw [(hT i hi).apply (by norm_num), (hT j hj).apply (by norm_num)] at e0 e1 e9
  exact hinj i hi j hj (Fin.ext e0) (Fin.ext e1) (Fin.ext e9)

theorem distinctOK_of_sep {T : ℕ → Array ℕ} {n : ℕ} {x : ℕ → X₀}
    (hsep : ∀ g h : X₀, psi g ⟨0, by norm_num⟩ = psi h ⟨0, by norm_num⟩ →
      psi g ⟨1, by norm_num⟩ = psi h ⟨1, by norm_num⟩ →
      psi g ⟨9, by norm_num⟩ = psi h ⟨9, by norm_num⟩ → g = h)
    (hT : ∀ k < n, Rep 820 (T k) (psi (x k))) (hinj : ∀ i < n, ∀ j < n, x i = x j → i = j) :
    distinctOK T n = true :=
  distinctOK_of hT fun i hi j hj e0 e1 e9 => hinj i hi j hj (hsep _ _ e0 e1 e9)

theorem fuseOK_of {k : ℕ} {g : X₀} (hg : Rep 820 (pTab k) (psi g))
    (h : g * g = 1 → g ≠ 1 → ∃ j < 2835, cElt j = g) : fuseOK k = true := by
  unfold fuseOK
  rw [Bool.or_eq_true]
  by_cases hi : isInvol (pTab k) = true
  · obtain ⟨h2, h1⟩ := (isInvol_iff hg).1 hi
    obtain ⟨j, hj, rfl⟩ := h h2 h1
    right
    rw [List.any_eq_true]
    exact ⟨j, List.mem_range.2 hj, (eqA_iff hg (rep_cTab j)).2 rfl⟩
  · left
    simpa using hi

theorem rep_conjTab' {c b : Array ℕ} {g h : X₀} (hc : Rep 820 c (psi g))
    (hb : Rep 820 b (psi h)) : Rep 820 (conjTab c b) (psi (g * h * g⁻¹)) := by
  unfold conjTab
  rw [map_mul, map_mul, map_inv]
  exact rep_compA (rep_compA hc hb) (CFSG.KS.Raw.rep_invCand hc)

theorem f2OK_of (hH : ∀ j, Rep 820 (hTab j) (psi (hElt j))) {k : ℕ}
    (h : hElt k * hElt k = 1 → hElt k ≠ 1 → hElt k ≠ xElt → f2Wit[k]! < 1152 ∧
      hElt k * (hElt f2Wit[k]! * hElt k * (hElt f2Wit[k]!)⁻¹) ≠
        hElt f2Wit[k]! * hElt k * (hElt f2Wit[k]!)⁻¹ * hElt k) :
    f2OK k = true := by
  unfold f2OK
  rw [Bool.or_eq_true]
  by_cases hi : (isInvol (hTab k) && !(eqA 820 (hTab k) tabA)) = true
  · right
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne,
      eqA_iff (hH k) rep_tabA] at hi
    obtain ⟨hi, hx⟩ := hi
    obtain ⟨h2, h1⟩ := (isInvol_iff (hH k)).1 hi
    have hx' : hElt k ≠ xElt := fun e => hx (by rw [e])
    obtain ⟨hlt, hne⟩ := h h2 h1 hx'
    have hc := rep_conjTab' (hH f2Wit[k]!) (hH k)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff, Ne]
    refine ⟨⟨hlt, isInvA_invCand (hH _)⟩, ?_⟩
    rw [eqA_iff (rep_compA (hH k) hc) (rep_compA hc (hH k)), ← map_mul, ← map_mul]
    exact fun e => hne (psi_injective e)
  · left
    rw [Bool.not_eq_true']
    exact Bool.eq_false_iff.2 hi

theorem g0OK_of (h : 5 < orderOf (xElt * (g0Elt * xElt * g0Elt⁻¹))) : g0OK = true := by
  have hg : Rep 820 (wordTab g0Word) (psi g0Elt) := rep_wordTab _
  have hz : Rep 820 (compA 820 tabA (conjTab (wordTab g0Word) tabA))
      (psi (xElt * (g0Elt * xElt * g0Elt⁻¹))) := by
    rw [map_mul]
    exact rep_compA rep_tabA (rep_conjTab' hg rep_tabA)
  simp only [g0OK, Bool.and_eq_true, List.all_eq_true]
  refine ⟨isInvA_invCand hg, fun k hk => ?_⟩
  have hk : 0 < k ∧ k ≤ 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, eqA_one_iff (rep_powTab hz k)]
  intro e
  have := orderOf_le_of_pow_eq_one hk.1 e
  omega

theorem u43InvCheck_of (hf : CheckFacts) : u43InvCheck () = true := by
  simp only [u43InvCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨isInvA_tabA, isInvA_tabB⟩, hf.gens⟩, hf.hpos⟩, hf.hdist⟩, hf.hclosed⟩, hf.ppos⟩, hf.pinv⟩, hf.pdist⟩,
    hf.pclosed⟩, hf.cdist⟩, hf.fuse⟩, hf.f2⟩, hf.g0⟩

end CFSG.KS.U43Mod.LieOdd

end
