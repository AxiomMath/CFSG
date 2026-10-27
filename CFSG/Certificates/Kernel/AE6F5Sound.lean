module

public import Certificates.Data.Kernel.AE6F5K
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SF

public section

namespace CFSG.KC.AE6F5K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.EnumSound
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

set_option maxRecDepth 100000

abbrev PR (P : Nat) (g : Equiv.Perm (Fin 12)) : Prop := PRep 12 4 P g

theorem mask4 : mask 4 = 15 := by decide

theorem ap_eq {P : Nat} {g : Equiv.Perm (Fin 12)} (h : PR P g) (x : Fin 12) :
    ap P x = (g x).val := by
  unfold ap
  rw [← mask4]
  exact h x

theorem pr_of_ap {P : Nat} {g : Equiv.Perm (Fin 12)} (h : ∀ x : Fin 12, ap P x = (g x).val) :
    PR P g := fun x => by
  rw [mask4]
  exact h x

theorem pr_mulP {P Q : Nat} {g h : Equiv.Perm (Fin 12)} (hP : PR P g) (hQ : PR Q h) :
    PR (mulP P Q) (g * h) := by
  unfold mulP
  rw [← mask4]
  exact prep_pcomp (by norm_num) hP hQ

theorem pr_powP {U : Nat} {u : Equiv.Perm (Fin 12)} (hU : PR U u) :
    ∀ k, PR (powP U k) (u ^ (k + 1))
  | 0 => by
    rw [zero_add, pow_one]
    exact hU
  | k + 1 => by
    change PR (mulP (powP U k) U) _
    rw [pow_succ]
    exact pr_mulP (pr_powP hU k) hU

theorem pr_isProd {r p q : Nat} {g h : Equiv.Perm (Fin 12)} (e : isProd r p q = true)
    (hp : PR p g) (hq : PR q h) : PR r (g * h) := pr_of_ap fun x => by
  unfold isProd at e
  have := PK.allN_iff.1 e x x.2
  rw [beq_iff] at this
  rw [this, ap_eq hq, ap_eq hp]
  rfl

theorem pr_same {p q : Nat} {g : Equiv.Perm (Fin 12)} (e : same p q = true) (hq : PR q g) :
    PR p g := pr_of_ap fun x => by
  unfold same at e
  have := PK.allN_iff.1 e x x.2
  rw [beq_iff] at this
  rw [this, ap_eq hq]

theorem tree_sound {N T P G NG : Nat} {S : Set (Equiv.Perm (Fin 12))}
    (hT : treeOK N T P G NG = true)
    (hG : ∀ l < NG, ∃ g ∈ Subgroup.closure S, PR (el G l) g) :
    ∀ k < N, ∃ g ∈ Subgroup.closure S, PR (el T k) g := by
  unfold treeOK at hT
  rw [PK.bAnd_eq, Bool.and_eq_true, PK.allN_iff, PK.allN_iff] at hT
  obtain ⟨h0, hk⟩ := hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkN
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · refine ⟨1, Subgroup.one_mem _, pr_of_ap fun x => ?_⟩
      have := h0 x x.2
      rw [beq_iff] at this
      exact this
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h := hk j (by change j < N - 1; omega)
      simp only [PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at h
      obtain ⟨hpar, hlab, hprod⟩ := h
      obtain ⟨g, hg, hgr⟩ := ih _ hpar (by omega)
      obtain ⟨l, hl, hlr⟩ := hG _ hlab
      exact ⟨g * l, Subgroup.mul_mem _ hg hl, pr_isProd hprod hgr hlr⟩

theorem allN_false {n : Nat} {f : Nat → Bool} (h : (!allN n f) = true) : ∃ i < n, f i = false := by
  rw [Bool.not_eq_true', Bool.eq_false_iff] at h
  by_contra hc
  push Not at hc
  exact h (PK.allN_iff.2 fun i hi => by simpa using hc i hi)

theorem w1K_spec {T : Nat} {τ : Equiv.Perm (Fin 12)} (hT : PR T τ) (h : w1K T = true) :
    orderOf τ = 3 ∧ (∀ n, ae6Blk (τ n) = ae6Blk n) ∧
      (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1 := by
  unfold w1K at h
  rw [PK.bAnd_eq, PK.bAnd_eq, PK.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, PK.allN_iff, PK.allN_iff] at h
  obtain ⟨hmv, h3, hblk, hone⟩ := h
  have hval : ∀ n : Fin 12, (τ n).val = ap T n.val := fun n => (ap_eq hT n).symm
  have hτ1 : τ ≠ 1 := by
    intro h1
    obtain ⟨i, hi, hf⟩ := allN_false hmv
    have := hval ⟨i, hi⟩
    rw [h1] at this
    simp only [Equiv.Perm.one_apply] at this
    rw [← this] at hf
    simp at hf
  have hτ3 : τ ^ 3 = 1 := by
    ext n
    have := h3 n n.2
    rw [beq_iff] at this
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hval, hval, hval]
    exact this
  have hfix : ∃ b < 4, ∀ i < 12, i / 3 = b ∨ ap T i = i := by
    obtain ⟨b, hb, hf⟩ := allN_false hone
    refine ⟨b, hb, fun i hi => ?_⟩
    rw [Bool.not_eq_false'] at hf
    have := PK.allN_iff.1 hf i hi
    have h' : Nat.div i 3 = b ∨ ap T i = i := by simpa [Bool.or_eq_true, beq_iff_eq] using this
    exact h'
  obtain ⟨b, hb4, hfix⟩ := hfix
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨orderOf_eq_prime hτ3 hτ1, fun n => Fin.ext ?_, ?_⟩
  · change (τ n).val / 3 = n.val / 3
    rw [hval]
    have := hblk n n.2
    rw [beq_iff] at this
    exact this
  · have hmoved : ∃ n : Fin 12, τ n ≠ n := by
      by_contra hno
      push Not at hno
      exact hτ1 (Equiv.ext hno)
    have hb' : (Finset.univ.filter fun b' : Fin 4 => ∃ n, ae6Blk n = b' ∧ τ n ≠ n) =
        {⟨b, hb4⟩} := by
      ext b'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨n, rfl, hn⟩
        apply Fin.ext
        change n.val / 3 = b
        rcases hfix n.val n.isLt with h1 | h1
        · exact h1
        · exact absurd (Fin.ext (by rw [hval]; exact h1)) hn
      · rintro rfl
        obtain ⟨n, hn⟩ := hmoved
        refine ⟨n, Fin.ext ?_, hn⟩
        change n.val / 3 = b
        rcases hfix n.val n.isLt with h1 | h1
        · exact h1
        · exact absurd (Fin.ext (by rw [hval]; exact h1)) hn
    rw [hb', Finset.card_singleton]

theorem fld_pmk {n w : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w) :
    PF.Fld w (pmk n w f) (fun i => if i < n then f i else 0) := by
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w f hf (clog n) 0
  have e : pmk n w f = pmkT n w f (clog n) 0 := by
    unfold pmk
    rw [PF.strictN_eqP]
  rw [e]
  refine PF.fld_congr h fun i => ?_
  by_cases hi : i < n
  · have h2 : i < 2 ^ clog n := by omega
    simp [hi, h2]
  · simp [hi]

theorem pg_pmk {n w i : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w)
    (hi : i < n) : pg w (mask w) (pmk n w f) i = f i := by
  rw [PF.pg_of_fld (fld_pmk hn hf) (by simp only [hi, ↓reduceIte]; exact hf i hi)]
  simp [hi]

theorem fld3_le (X o : Nat) : fld(X, o, 3) ≤ 3 := Nat.and_le_right

theorem exists_blkS {FP FS : Nat}
    (hFP : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → ∃ t < 24,
      fld(FP, 2 * (4 * t + 0), 3) = a.val ∧ fld(FP, 2 * (4 * t + 1), 3) = b.val ∧
        fld(FP, 2 * (4 * t + 2), 3) = c.val ∧ fld(FP, 2 * (4 * t + 3), 3) = d.val)
    (hFS : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → ∃ r < 6,
      fld(FS, 2 * (3 * r + 0), 3) = a.val ∧ fld(FS, 2 * (3 * r + 1), 3) = b.val ∧
        fld(FS, 2 * (3 * r + 2), 3) = c.val)
    {σ : Equiv.Perm (Fin 12)}
    (hσ : ∀ m n : Fin 12, ae6Blk m = ae6Blk n ↔ ae6Blk (σ m) = ae6Blk (σ n)) :
    ∃ t < 24, ∃ j < 1296, PR (blkS FP FS t j) σ := by
  have hblk : ∀ m : Fin 12, (ae6Blk m).val = m.val / 3 := fun m => rfl
  have hb : ∀ i : Fin 12, (σ i).val / 3 = (σ ⟨3 * (i.val / 3), by omega⟩).val / 3 := by
    intro i
    have := (hσ i ⟨3 * (i.val / 3), by omega⟩).mp
      (Fin.ext (by rw [hblk, hblk]; change i.val / 3 = 3 * (i.val / 3) / 3; omega))
    have := congrArg Fin.val this
    simpa [hblk] using this
  have hinj : ∀ i j : Fin 12, (σ i).val = (σ j).val → i = j := fun i j h =>
    σ.injective (Fin.ext h)
  have hπ : ∀ b b' : Fin 4, (σ ⟨3 * b.val, by omega⟩).val / 3 =
      (σ ⟨3 * b'.val, by omega⟩).val / 3 → b = b' := by
    intro b b' h
    have h2 := (hσ ⟨3 * b.val, by omega⟩ ⟨3 * b'.val, by omega⟩).mpr (Fin.ext (by simpa [hblk]))
    have h3 := congrArg Fin.val h2
    simp only [hblk] at h3
    exact Fin.ext (by omega)
  let π : Fin 4 → Fin 4 := fun b => ⟨(σ ⟨3 * b.val, by omega⟩).val / 3, by omega⟩
  have hπne : ∀ b b' : Fin 4, b ≠ b' → π b ≠ π b' := fun b b' h e =>
    h (hπ b b' (congrArg Fin.val e))
  obtain ⟨t, ht, ht0, ht1, ht2, ht3⟩ := hFP (π 0) (π 1) (π 2) (π 3) (hπne _ _ (by decide))
    (hπne _ _ (by decide)) (hπne _ _ (by decide)) (hπne _ _ (by decide)) (hπne _ _ (by decide))
    (hπne _ _ (by decide))
  have htb : ∀ b : Fin 4, fld(FP, 2 * (4 * t + b.val), 3) = (σ ⟨3 * b.val, by omega⟩).val / 3 := by
    intro b
    fin_cases b
    · exact ht0
    · exact ht1
    · exact ht2
    · exact ht3
  let ρ : Fin 4 → Fin 3 → Fin 3 := fun b s => ⟨(σ ⟨3 * b.val + s.val, by omega⟩).val % 3,
    Nat.mod_lt _ (by norm_num)⟩
  have hρne : ∀ b : Fin 4, ∀ s s' : Fin 3, s ≠ s' → ρ b s ≠ ρ b s' := by
    intro b s s' hs e
    have h1 := congrArg Fin.val e
    simp only [ρ] at h1
    have h2 := hb ⟨3 * b.val + s.val, by omega⟩
    have h3 := hb ⟨3 * b.val + s'.val, by omega⟩
    have e2 : (3 * b.val + s.val) / 3 = b.val := by omega
    have e3 : (3 * b.val + s'.val) / 3 = b.val := by omega
    simp only [e2, e3] at h2 h3
    have h4 := hinj _ _ (by omega : (σ ⟨3 * b.val + s.val, by omega⟩).val =
      (σ ⟨3 * b.val + s'.val, by omega⟩).val)
    have h5 := congrArg Fin.val h4
    simp only at h5
    exact hs (Fin.ext (by omega))
  have hr : ∀ b : Fin 4, ∃ r < 6, ∀ s : Fin 3,
      fld(FS, 2 * (3 * r + s.val), 3) = (σ ⟨3 * b.val + s.val, by omega⟩).val % 3 := by
    intro b
    obtain ⟨r, hr, h0, h1, h2⟩ := hFS (ρ b 0) (ρ b 1) (ρ b 2) (hρne b _ _ (by decide))
      (hρne b _ _ (by decide)) (hρne b _ _ (by decide))
    refine ⟨r, hr, fun s => ?_⟩
    fin_cases s
    · exact h0
    · exact h1
    · exact h2
  choose r hr6 hre using hr
  have h60 := hr6 0
  have h61 := hr6 1
  have h62 := hr6 2
  have h63 := hr6 3
  have hJ : ∀ b : Fin 4, (r 0 + 6 * r 1 + 36 * r 2 + 216 * r 3) / 6 ^ b.val % 6 = r b := by
    intro b
    fin_cases b <;> simp <;> omega
  refine ⟨t, ht, r 0 + 6 * r 1 + 36 * r 2 + 216 * r 3, by omega, pr_of_ap fun x => ?_⟩
  have hx := x.isLt
  unfold ap blkS
  rw [← mask4, pg_pmk (by norm_num) (fun i _ => by
    have h1 : fld(FP, Nat.mul 2 (Nat.add (Nat.mul 4 t) (Nat.div i 3)), 3) ≤ 3 := fld3_le _ _
    have h2 : fld(FS, Nat.mul 2 (Nat.add (Nat.mul 3 (Nat.mod (Nat.div
      (r 0 + 6 * r 1 + 36 * r 2 + 216 * r 3) (Nat.pow 6 (Nat.div i 3))) 6)) (Nat.mod i 3)), 3) ≤ 3 :=
      fld3_le _ _
    change 3 * _ + _ < 16
    omega) hx]
  have hb4 : x.val / 3 < 4 := by omega
  have hπx := htb ⟨x.val / 3, hb4⟩
  have hJx : (r 0 + 6 * r 1 + 36 * r 2 + 216 * r 3) / 6 ^ (x.val / 3) % 6 = r ⟨x.val / 3, hb4⟩ :=
    hJ ⟨x.val / 3, hb4⟩
  have hρx := hre ⟨x.val / 3, hb4⟩ ⟨x.val % 3, Nat.mod_lt _ (by norm_num)⟩
  simp only [Fin.val_mk] at hπx hρx
  have ex : σ ⟨3 * (x.val / 3) + x.val % 3, by omega⟩ = σ x :=
    congrArg σ (Fin.ext (by change 3 * (x.val / 3) + x.val % 3 = x.val; omega))
  rw [ex] at hρx
  have hbx := hb x
  have hv := (σ x).isLt
  change 3 * fld(FP, 2 * (4 * t + x.val / 3), 3) +
    fld(FS, 2 * (3 * ((r 0 + 6 * r 1 + 36 * r 2 + 216 * r 3) / 6 ^ (x.val / 3) % 6) +
      x.val % 3), 3) = (σ x).val
  rw [hJx, hρx, hπx]
  omega

@[expose] def genF (l : Nat) : Equiv.Perm (Fin 12) :=
  if h : l < 7 then ae6LetterHatPerm ⟨l, h⟩ else if h' : l - 7 < 2 then ae6GammaHatPerm ⟨l - 7, h'⟩
    else 1

theorem genF_mem_H (l : Nat) (hl : l < 9) : genF l ∈
    Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm) := by
  unfold genF
  by_cases h7 : l < 7
  · rw [dif_pos h7]
    exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · rw [dif_neg h7, dif_pos (by omega)]
    exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)

theorem genF_mem_C (l : Nat) (hl : l < 7) : genF l ∈ Subgroup.closure (Set.range ae6LetterHatPerm) := by
  unfold genF
  rw [dif_pos hl]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem genF_mem_ins (σ : Equiv.Perm (Fin 12)) (l : Nat) (hl : l < 7) :
    genF l ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)) :=
  Subgroup.closure_mono (Set.subset_insert _ _) (genF_mem_C l hl)

theorem tree_case {GN HT HP s h : Nat} {σ : Equiv.Perm (Fin 12)}
    (hH : treeOK 1296 HT HP GN 9 = true) (hG : ∀ l < 9, PR (el GN l) (genF l))
    (hS : PR s σ) (hh : h < 1296) (hsame : same s (el HT h) = true) :
    σ ∈ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm) := by
  obtain ⟨g, hg, hgr⟩ := tree_sound hH (fun l hl => ⟨genF l, genF_mem_H l hl, hG l hl⟩) h hh
  rw [CFSG.KC.EnumSound.prep_unique hS (pr_same hsame hgr)]
  exact hg

theorem wit_case {GN CT CP s si x c k : Nat} {σ : Equiv.Perm (Fin 12)}
    (hC : treeOK 216 CT CP GN 7 = true) (hG : ∀ l < 9, PR (el GN l) (genF l))
    (hS : PR s σ) (hx : x < 7) (hc : c < 216) (hperm : permOK 12 4 15 48 s si = true)
    (hw : w1K (powP (mulP s (mulP (el GN x) (mulP si (el CT c)))) k) = true) :
    ∃ τ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)), orderOf τ = 3 ∧
      (∀ n, ae6Blk (τ n) = ae6Blk n) ∧
      (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1 := by
  rw [← mask4] at hperm
  obtain ⟨g', hg'1, hg'2⟩ := permOK_perm hperm
  have hgσ : g' = σ := CFSG.KC.EnumSound.prep_unique hg'1 hS
  rw [hgσ] at hg'2
  obtain ⟨cc, hccC, hccr⟩ := tree_sound hC (fun l hl => ⟨genF l, genF_mem_C l hl, hG l (by omega)⟩)
    c hc
  have hU := pr_mulP hS (pr_mulP (hG x (by omega)) (pr_mulP hg'2 hccr))
  obtain ⟨h1, h2, h3⟩ := w1K_spec (pr_powP hU k) hw
  refine ⟨_, ?_, h1, h2, h3⟩
  have hσm : σ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hcm : cc ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)) :=
    Subgroup.closure_mono (Set.subset_insert _ _) hccC
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hσm (Subgroup.mul_mem _ (genF_mem_ins σ x hx)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hσm) hcm))) _

theorem entry_sound {GN CT CP HT HP s e : Nat} {σ : Equiv.Perm (Fin 12)}
    (hC : treeOK 216 CT CP GN 7 = true) (hH : treeOK 1296 HT HP GN 9 = true)
    (hG : ∀ l < 9, PR (el GN l) (genF l)) (hS : PR s σ)
    (hnot : σ ∉ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm))
    (he : entryOK GN CT HT s e = true) :
    ∃ τ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)), orderOf τ = 3 ∧
      (∀ n, ae6Blk (τ n) = ae6Blk n) ∧
      (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1 := by
  unfold entryOK at he
  cases hb : Nat.blt e 32768
  · simp only [hb, cond_false, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at he
    exact absurd (tree_case hH hG hS he.1 he.2) hnot
  · simp only [hb, cond_true, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at he
    obtain ⟨hx, hcc, -, hperm, hw⟩ := he
    exact wit_case hC hG hS hx hcc hperm hw

theorem f5_of {GN CT CP HT HP FP FS : Nat} {D : Nat → Nat}
    (hC : treeOK 216 CT CP GN 7 = true) (hH : treeOK 1296 HT HP GN 9 = true)
    (hG : ∀ l < 9, PR (el GN l) (genF l))
    (hFP : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → ∃ t < 24,
      fld(FP, 2 * (4 * t + 0), 3) = a.val ∧ fld(FP, 2 * (4 * t + 1), 3) = b.val ∧
        fld(FP, 2 * (4 * t + 2), 3) = c.val ∧ fld(FP, 2 * (4 * t + 3), 3) = d.val)
    (hFS : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → ∃ r < 6,
      fld(FS, 2 * (3 * r + 0), 3) = a.val ∧ fld(FS, 2 * (3 * r + 1), 3) = b.val ∧
        fld(FS, 2 * (3 * r + 2), 3) = c.val)
    (hD : ∀ t < 24, piOK GN CT HT FP FS t (D t) = true) :
    ∀ σ : Equiv.Perm (Fin 12),
      (∀ m n : Fin 12, ae6Blk m = ae6Blk n ↔ ae6Blk (σ m) = ae6Blk (σ n)) →
      σ ∉ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm) →
      ∃ τ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)), orderOf τ = 3 ∧
        (∀ n, ae6Blk (τ n) = ae6Blk n) ∧
        (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1 := by
  intro σ hσ hnot
  obtain ⟨t, ht, j, hj, hS⟩ := exists_blkS hFP hFS hσ
  exact entry_sound hC hH hG hS hnot ((PK.allN_iff.1 (hD t ht)) j hj)

end CFSG.KC.AE6F5K
