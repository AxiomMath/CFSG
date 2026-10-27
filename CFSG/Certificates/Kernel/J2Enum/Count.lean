module

public import Certificates.Data.Kernel.J2EnumQ
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import CFSG.Certificates.Kernel.J2Enum.Group
import CFSG.Certificates.Kernel.J2CoverSnd.Chain
import CFSG.Certificates.Kernel.Child3Inv
import CFSG.Certificates.Kernel.Spor.PinvSSound

public section

namespace CFSG.KC.J2Enum.CntPf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.KC.J2Enum

private def tri (r0 r1 r2 : ℕ) (φ : ℕ → ℕ → ℕ → ℕ) : ℕ :=
  ((List.range r0).map fun a => ((List.range r1).map fun b =>
    ((List.range r2).map fun c => φ a b c).sum).sum).sum

private theorem tri_congr {r0 r1 r2 : ℕ} {φ ψ : ℕ → ℕ → ℕ → ℕ}
    (h : ∀ a < r0, ∀ b < r1, ∀ c < r2, φ a b c = ψ a b c) :
    tri r0 r1 r2 φ = tri r0 r1 r2 ψ := by
  unfold tri
  congr 1
  refine List.map_congr_left fun a ha => ?_
  congr 1
  refine List.map_congr_left fun b hb => ?_
  congr 1
  exact List.map_congr_left fun c hc =>
    h a (List.mem_range.1 ha) b (List.mem_range.1 hb) c (List.mem_range.1 hc)

private theorem tri_add (r0 r1 r2 : ℕ) (φ ψ : ℕ → ℕ → ℕ → ℕ) :
    tri r0 r1 r2 (fun a b c => φ a b c + ψ a b c) = tri r0 r1 r2 φ + tri r0 r1 r2 ψ := by
  simp only [tri, List.sum_map_add]

private theorem tri_mul (r0 r1 r2 k : ℕ) (φ : ℕ → ℕ → ℕ → ℕ) :
    tri r0 r1 r2 (fun a b c => k * φ a b c) = k * tri r0 r1 r2 φ := by
  simp only [tri, List.sum_map_mul_left]

private theorem sum_map_le {f : ℕ → ℕ} {k : ℕ} (h : ∀ x, f x ≤ k) :
    ∀ l : List ℕ, (l.map f).sum ≤ l.length * k
  | [] => by simp
  | x :: l => by
    have := sum_map_le h l
    have := h x
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem tri_le (r0 r1 r2 : ℕ) (φ : ℕ → ℕ → ℕ → ℕ) (h : ∀ a b c, φ a b c ≤ 1) :
    tri r0 r1 r2 φ ≤ r0 * r1 * r2 := by
  unfold tri
  have h2 : ∀ a b, ((List.range r2).map fun c => φ a b c).sum ≤ r2 := fun a b => by
    have := sum_map_le (h a b) (List.range r2)
    rwa [List.length_range, Nat.mul_one] at this
  have h1 : ∀ a, ((List.range r1).map fun b => ((List.range r2).map fun c => φ a b c).sum).sum ≤
      r1 * r2 := fun a => by
    have := sum_map_le (h2 a) (List.range r1)
    rwa [List.length_range] at this
  have := sum_map_le h1 (List.range r0)
  rwa [List.length_range, ← Nat.mul_assoc] at this

private theorem fld20_val (T k : ℕ) : fld20 T k = T / 2 ^ (20 * k) % 2 ^ 20 := by
  show (T >>> (20 * k)) &&& (2 ^ 20 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem fld20_pack {a b c d : ℕ} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) (hc : c < 2 ^ 20)
    (hd : d < 2 ^ 20) :
    fld20 (a + 2 ^ 20 * (b + 2 ^ 20 * (c + 2 ^ 20 * d))) 0 = a ∧
      fld20 (a + 2 ^ 20 * (b + 2 ^ 20 * (c + 2 ^ 20 * d))) 1 = b ∧
      fld20 (a + 2 ^ 20 * (b + 2 ^ 20 * (c + 2 ^ 20 * d))) 2 = c ∧
      fld20 (a + 2 ^ 20 * (b + 2 ^ 20 * (c + 2 ^ 20 * d))) 3 = d := by
  simp only [Nat.reducePow] at ha hb hc hd
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [fld20_val, Nat.reducePow, Nat.reduceMul] <;> omega

private theorem fld20_pack2 {a b : ℕ} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) :
    fld20 (a + 2 ^ 20 * b) 0 = a ∧ fld20 (a + 2 ^ 20 * b) 1 = b := by
  simp only [Nat.reducePow] at ha hb
  refine ⟨?_, ?_⟩ <;> simp only [fld20_val, Nat.reducePow, Nat.reduceMul] <;> omega

private theorem foldl_add_map' {α : Type} (F : α → ℕ) :
    ∀ (T : List α) (acc : ℕ), T.foldl (fun c t => c + F t) acc = acc + (T.map F).sum
  | [], acc => by simp
  | t :: T, acc => by
    rw [List.foldl_cons, foldl_add_map' F T, List.map_cons, List.sum_cons]
    omega

private theorem countP_filterProducts (n : ℕ) (f p : Table → Bool) (Ts : List (List Table)) :
    ∀ (g : Table) (acc : List Table), (filterProducts n f Ts g acc).countP p =
      acc.countP p + countProducts n (fun t => f t && p t) Ts g := by
  induction Ts with
  | nil =>
    intro g acc
    rw [filterProducts, countProducts]
    by_cases hf : f g = true <;> by_cases hp : p g = true <;> simp [hf, hp, List.countP_cons]
  | cons T Ts ih =>
    intro g acc
    rw [filterProducts, countProducts, foldl_add_map', Nat.zero_add]
    induction T generalizing acc with
    | nil => simp
    | cons t T ihT =>
      simp only [List.foldl_cons]
      rw [ihT, ih, List.map_cons, List.sum_cons]
      omega

private noncomputable def prod3 (n w : ℕ) (LR TR : ℕ → ℕ) (G a b c : ℕ) : ℕ :=
  pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) G (TR (roff n (n * w) (LR 0) + a)))
    (TR (roff n (n * w) (LR 1) + b))) (TR (roff n (n * w) (LR 2) + c))

private theorem countProducts3 {n w : ℕ} {LR TR : ℕ → ℕ} {f : Table → Bool} {G : ℕ}
    (hn : n < 2 ^ 32)
    (hT : ∀ i < 3, ∀ k < rcnt (LR i), ∀ x < n,
      pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x < n) :
    countProducts n f ((List.range 3).map (CFSG.KC.J2Cover.Snd.lvTab n w LR TR)) (tabP n w G) =
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
        if f (tabP n w (prod3 n w LR TR G a b c)) then 1 else 0 := by
  have e3 : (List.range 3).map (CFSG.KC.J2Cover.Snd.lvTab n w LR TR) =
      [CFSG.KC.J2Cover.Snd.lvTab n w LR TR 0, CFSG.KC.J2Cover.Snd.lvTab n w LR TR 1,
        CFSG.KC.J2Cover.Snd.lvTab n w LR TR 2] := rfl
  unfold tri
  rw [e3, countProducts, foldl_add_map', Nat.zero_add]
  unfold CFSG.KC.J2Cover.Snd.lvTab
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  simp only [Function.comp_apply]
  rw [compT_tabP hn (hT 0 (by norm_num) a (List.mem_range.1 ha)), countProducts, foldl_add_map',
    Nat.zero_add, List.map_map]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  simp only [Function.comp_apply]
  rw [compT_tabP hn (hT 1 (by norm_num) b (List.mem_range.1 hb)), countProducts, foldl_add_map',
    Nat.zero_add, List.map_map]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  simp only [Function.comp_apply]
  rw [compT_tabP hn (hT 2 (by norm_num) c (List.mem_range.1 hc)), countProducts]
  rfl

private theorem idT_eq_tabP' {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    idT n = tabP n w (pidn n w) := by
  apply Array.ext
  · simp [idT, tabP_size]
  · intro i h1 h2
    have hi : i < n := by simpa [idT] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, tabP_get hi, PF.pg_pidn hn hw hi, idT,
      getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

private theorem blk_eq (n w : ℕ) (LR TR : ℕ → ℕ) (BP G₀ R₁ R₂ : ℕ) :
    sumF (rcnt (LR 0)) (blkCnt n w LR TR BP G₀ R₁ R₂) =
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
        contrib w (mask w) BP R₁ R₂ fun p => pg w (mask w)
          (pcomp n w (mask w) (pcomp n w (mask w) G₀ (TR (roff n (n * w) (LR 0) + a)))
            (TR (roff n (n * w) (LR 1) + b))) (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p) := by
  rw [sumF_eq]
  unfold tri
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [blkCnt, PF.strictN_eqP, sumF_eq]
  rfl

private theorem blkU_eq (n w : ℕ) (LR TR : ℕ → ℕ) (BP G₀ : ℕ) :
    sumF (rcnt (LR 0)) (blkCntU n w LR TR BP G₀) =
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
        nIf(fix3 w (mask w) BP (fun p => pg w (mask w)
          (pcomp n w (mask w) (pcomp n w (mask w) G₀ (TR (roff n (n * w) (LR 0) + a)))
            (TR (roff n (n * w) (LR 1) + b))) (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p)) 2,
          1, 0) := by
  rw [sumF_eq]
  unfold tri
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [blkCntU, PF.strictN_eqP, sumF_eq]
  rfl

private theorem blkQ_eq (n w : ℕ) (LR TR : ℕ → ℕ) (BP G₀ R₁ R₂ q r s : ℕ) :
    sumF (rcnt (LR 0)) (blkCntQ n w LR TR BP G₀ R₁ R₂ q r s) =
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
        contribQ w (mask w) BP R₁ R₂ q r s fun p => pg w (mask w)
          (pcomp n w (mask w) (pcomp n w (mask w) G₀ (TR (roff n (n * w) (LR 0) + a)))
            (TR (roff n (n * w) (LR 1) + b))) (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p) := by
  rw [sumF_eq]
  unfold tri
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [blkCntQ, PF.strictN_eqP, sumF_eq]
  rfl

private def Acts (n : ℕ) (f : ℕ → ℕ) (γ : Equiv.Perm (Fin n)) : Prop :=
  ∀ p (h : p < n), f p = (γ ⟨p, h⟩ : ℕ)

private theorem acts_comp {n : ℕ} {f g : ℕ → ℕ} {α β : Equiv.Perm (Fin n)} (hf : Acts n f α)
    (hg : Acts n g β) : Acts n (fun p => f (g p)) (α * β) := fun p h => by
  show f (g p) = _
  rw [hg p h, hf _ (Fin.is_lt _), Equiv.Perm.mul_apply]

private theorem acts_pg {n w P : ℕ} {γ : Equiv.Perm (Fin n)} (h : Raw.Orb.PRep n w P γ) :
    Acts n (pg w (mask w) P) γ := fun p hp => h ⟨p, hp⟩

private theorem acts_ap {n w P : ℕ} {γ : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (h : Raw.Orb.PRep n w P γ) : Acts n (ap (tabP n w P)) γ := fun p hp => by
  have e : pg w (mask w) P p = (γ ⟨p, hp⟩ : ℕ) := h ⟨p, hp⟩
  rw [ap_tabP hp (by rw [e]; have := (γ ⟨p, hp⟩).2; omega), e]

private theorem itP_succ' (f : ℕ → ℕ) (k p : ℕ) : itP f (k + 1) p = f (itP f k p) :=
  PF.strictN_eqP _ _

private theorem acts_itP {n : ℕ} {f : ℕ → ℕ} {γ : Equiv.Perm (Fin n)} (hf : Acts n f γ) :
    ∀ k, Acts n (itP f k) (γ ^ k)
  | 0 => fun p h => by simp [itP]
  | k + 1 => fun p h => by
    show itP f (k + 1) p = _
    rw [itP_succ', acts_itP hf k p h, hf _ (Fin.is_lt _), pow_succ', Equiv.Perm.mul_apply]

private theorem acts_apPowW {n : ℕ} {W : List Table} {γ : Equiv.Perm (Fin n)}
    (hW : Acts n (apW W) γ) : ∀ k, Acts n (apPowW W k) (γ ^ k)
  | 0 => fun p h => by simp [apPowW]
  | k + 1 => fun p h => by
    rw [apPowW, acts_apPowW hW k p h, hW _ (Fin.is_lt _), pow_succ', Equiv.Perm.mul_apply]

private theorem acts_single {n : ℕ} {T : Table} {γ : Equiv.Perm (Fin n)} (hT : Acts n (ap T) γ) :
    Acts n (apW [T]) γ := fun p h => hT p h

private theorem acts_cons {n : ℕ} {T : Table} {W : List Table} {α β : Equiv.Perm (Fin n)}
    (hT : Acts n (ap T) α) (hW : Acts n (apW W) β) : Acts n (apW (T :: W)) (α * β) := fun p h => by
  show ap T (apW W p) = _
  rw [hW p h, hT _ (Fin.is_lt _), Equiv.Perm.mul_apply]

private theorem acts_replicate {n : ℕ} {T : Table} {γ : Equiv.Perm (Fin n)} (hT : Acts n (ap T) γ) :
    ∀ k, Acts n (apW (List.replicate k T)) (γ ^ k)
  | 0 => fun p h => by simp [apW]
  | k + 1 => fun p h => by
    show ap T (apW (List.replicate k T) p) = _
    rw [acts_replicate hT k p h, hT _ (Fin.is_lt _), pow_succ', Equiv.Perm.mul_apply]

private theorem powFixW_eq {n : ℕ} {W : List Table} {γ : Equiv.Perm (Fin n)}
    (hW : Acts n (apW W) γ) (k : ℕ) : powFixW n W k = decide (γ ^ k = 1) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, powFixW, CFSG.Sporadic.Th.allIn_eq_true]
  constructor
  · intro H
    refine Equiv.Perm.ext fun x => Fin.ext ?_
    have := H x (Nat.zero_le _) x.2
    rw [beq_iff_eq, acts_apPowW hW k x x.2] at this
    simpa using this
  · intro H i _ hi
    rw [beq_iff_eq, acts_apPowW hW k i hi, H]
    rfl

section Base

variable {n w BP : ℕ} {Γ : Subgroup (Equiv.Perm (Fin n))}
  (hbp : ∀ t < 3, pg w (mask w) BP t < n)
  (hsep : ∀ γ : Equiv.Perm (Fin n), γ ∈ Γ →
    (∀ t < 3, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
include hbp hsep

private theorem fix3_eq {f : ℕ → ℕ} {γ : Equiv.Perm (Fin n)} (hf : Acts n f γ) {k : ℕ}
    (hk : γ ^ k ∈ Γ) : fix3 w (mask w) BP f k = decide (γ ^ k = 1) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold fix3
  rw [bAnd_iff, bAnd_iff]
  have e : ∀ t (ht : t < 3), (Nat.beq (itP f k (pg w (mask w) BP t)) (pg w (mask w) BP t) = true ↔
      (γ ^ k) ⟨_, hbp t ht⟩ = ⟨_, hbp t ht⟩) := fun t ht => by
    rw [Nat.beq_eq, acts_itP hf k _ (hbp t ht), Fin.ext_iff]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine hsep _ hk fun t ht h => ?_
    interval_cases t
    · exact h0
    · exact h1
    · exact h2
  · intro H
    rw [H]
    exact ⟨rfl, rfl, rfl⟩

private theorem fix_eq {f : ℕ → ℕ} {W : List Table} {γ : Equiv.Perm (Fin n)} (hγ : γ ∈ Γ)
    (hf : Acts n f γ) (hW : Acts n (apW W) γ) :
    ∀ e, fix3 w (mask w) BP f e = powFixW n W e := fun e => by
  rw [fix3_eq hbp hsep hf (pow_mem hγ e), powFixW_eq hW]

end Base

private theorem divParts_prime {p : ℕ} (hp : p.Prime) : divParts p = [1] := by
  unfold divParts
  rw [List.range_succ, List.filter_append, List.filter_eq_nil_iff.2 ?_]
  · simp [hp.one_lt, Nat.div_self hp.pos]
  · intro d hd
    simp only [List.mem_range] at hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and]
    intro h1 h2
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h2) with h | h <;> omega

private theorem ordB_eq {n w BP k : ℕ} {f : ℕ → ℕ} {W : List Table}
    (h : ∀ e, fix3 w (mask w) BP f e = powFixW n W e) (hd : divParts k = [1]) :
    ordB w (mask w) BP f k = ordW n W k := by
  unfold ordB ordW
  rw [h, h, hd]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  cases powFixW n W k <;> cases powFixW n W 1 <;> rfl

private theorem ord12B_eq {n w BP : ℕ} {f : ℕ → ℕ} {W : List Table}
    (h : ∀ e, fix3 w (mask w) BP f e = powFixW n W e) :
    ord12B w (mask w) BP f = ordW n W 12 := by
  unfold ord12B ordW
  simp only [h]
  rw [show divParts 12 = [6, 4, 3, 2, 1] by decide]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  cases powFixW n W 12 <;> cases powFixW n W 6 <;> cases powFixW n W 4 <;>
    cases powFixW n W 3 <;> cases powFixW n W 2 <;> cases powFixW n W 1 <;> rfl

section One

variable {n w BP : ℕ} {Γ : Subgroup (Equiv.Perm (Fin n))}
  (hbp : ∀ t < 3, pg w (mask w) BP t < n)
  (hsep : ∀ γ : Equiv.Perm (Fin n), γ ∈ Γ →
    (∀ t < 3, ∀ h : pg w (mask w) BP t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
  (hn : n < 2 ^ 32)
include hbp hsep hn

private theorem pairB_eq {R X : ℕ} {x : ℕ → ℕ} {ρ γ : Equiv.Perm (Fin n)} (hρ : ρ ∈ Γ)
    (hγ : γ ∈ Γ) (hR : Raw.Orb.PRep n w R ρ) (hX : Raw.Orb.PRep n w X γ) (hx : Acts n x γ) :
    pairB w (mask w) BP R x = pairTest n 7 12 2 3 (tabP n w R) (tabP n w X) := by
  have hRa := acts_pg hR
  have hRt := acts_ap hn hR
  have hXt := acts_ap hn hX
  unfold pairB pairTest
  rw [ordB_eq (k := 7) (W := [tabP n w R, tabP n w X])
      (fix_eq hbp hsep (mul_mem hρ hγ) (acts_comp hRa hx) (acts_cons hRt (acts_single hXt))) (by decide),
    ord12B_eq (W := commWord (tabP n w R) (tabP n w X) 2 3)
      (fix_eq hbp hsep (mul_mem hρ (mul_mem hγ (mul_mem hρ (mul_mem hγ hγ))))
        (acts_comp hRa (acts_comp hx (acts_comp hRa (acts_comp hx hx))))
        (acts_cons hRt (acts_cons hXt (acts_cons hRt (acts_cons hXt (acts_single hXt))))))]
  cases ordW n [tabP n w R, tabP n w X] 7 <;> rfl

private theorem pairQ_eq {R X q r s : ℕ} {x : ℕ → ℕ} {ρ γ : Equiv.Perm (Fin n)} (hρ : ρ ∈ Γ)
    (hγ : γ ∈ Γ) (hR : Raw.Orb.PRep n w R ρ) (hX : Raw.Orb.PRep n w X γ) (hx : Acts n x γ)
    (hr : r.Prime) (hs : s.Prime) :
    pairQ w (mask w) BP R q r s x = pairTest n r s 2 q (tabP n w R) (tabP n w X) := by
  have hRa := acts_pg hR
  have hRt := acts_ap hn hR
  have hXt := acts_ap hn hX
  unfold pairQ pairTest
  rw [ordB_eq (k := r) (W := [tabP n w R, tabP n w X])
      (fix_eq hbp hsep (mul_mem hρ hγ) (acts_comp hRa hx) (acts_cons hRt (acts_single hXt))) (divParts_prime hr),
    ordB_eq (k := s) (W := commWord (tabP n w R) (tabP n w X) 2 q)
      (fix_eq hbp hsep (mul_mem hρ (mul_mem hγ (mul_mem hρ (pow_mem hγ (Nat.sub q 1)))))
        (acts_comp hRa (acts_comp hx (acts_comp hRa (acts_itP hx (Nat.sub q 1)))))
        (acts_cons hRt (acts_cons hXt (acts_cons hRt (acts_replicate hXt (Nat.sub q 1))))))
      (divParts_prime hs)]
  cases ordW n [tabP n w R, tabP n w X] r <;> rfl

private theorem contrib_eq {R₁ R₂ X : ℕ} {x : ℕ → ℕ} {ρ₁ ρ₂ γ : Equiv.Perm (Fin n)}
    (hρ₁ : ρ₁ ∈ Γ) (hρ₂ : ρ₂ ∈ Γ) (hγ : γ ∈ Γ) (hR₁ : Raw.Orb.PRep n w R₁ ρ₁)
    (hR₂ : Raw.Orb.PRep n w R₂ ρ₂) (hX : Raw.Orb.PRep n w X γ) (hx : Acts n x γ) :
    contrib w (mask w) BP R₁ R₂ x =
      (if ordTest n 2 (tabP n w X) then 1 else 0) + 2 ^ 20 *
        ((if ordTest n 3 (tabP n w X) then 1 else 0) + 2 ^ 20 *
          ((if (ordTest n 3 (tabP n w X) && pairTest n 7 12 2 3 (tabP n w R₁) (tabP n w X)) then 1
              else 0) + 2 ^ 20 *
            (if (ordTest n 3 (tabP n w X) && pairTest n 7 12 2 3 (tabP n w R₂) (tabP n w X)) then 1
              else 0))) := by
  have hfix := fix_eq hbp hsep (W := [tabP n w X]) hγ hx (acts_single (acts_ap hn hX))
  unfold contrib
  rw [ordB_eq (k := 2) hfix (by decide), ordB_eq (k := 3) hfix (by decide),
    pairB_eq hbp hsep hn hρ₁ hγ hR₁ hX hx, pairB_eq hbp hsep hn hρ₂ hγ hR₂ hX hx]
  unfold ordTest
  generalize ordW n [tabP n w X] 2 = a
  generalize ordW n [tabP n w X] 3 = b
  generalize pairTest n 7 12 2 3 (tabP n w R₁) (tabP n w X) = c
  generalize pairTest n 7 12 2 3 (tabP n w R₂) (tabP n w X) = d
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem contribQ_eq {R₁ R₂ X q r s : ℕ} {x : ℕ → ℕ} {ρ₁ ρ₂ γ : Equiv.Perm (Fin n)}
    (hρ₁ : ρ₁ ∈ Γ) (hρ₂ : ρ₂ ∈ Γ) (hγ : γ ∈ Γ) (hR₁ : Raw.Orb.PRep n w R₁ ρ₁)
    (hR₂ : Raw.Orb.PRep n w R₂ ρ₂) (hX : Raw.Orb.PRep n w X γ) (hx : Acts n x γ)
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) :
    contribQ w (mask w) BP R₁ R₂ q r s x =
      (if (ordTest n q (tabP n w X) && pairTest n r s 2 q (tabP n w R₁) (tabP n w X)) then 1
          else 0) + 2 ^ 20 *
        (if (ordTest n q (tabP n w X) && pairTest n r s 2 q (tabP n w R₂) (tabP n w X)) then 1
          else 0) := by
  have hfix := fix_eq hbp hsep (W := [tabP n w X]) hγ hx (acts_single (acts_ap hn hX))
  unfold contribQ
  rw [ordB_eq (k := q) hfix (divParts_prime hq), pairQ_eq hbp hsep hn hρ₁ hγ hR₁ hX hx hr hs,
    pairQ_eq hbp hsep hn hρ₂ hγ hR₂ hX hx hr hs]
  unfold ordTest
  generalize ordW n [tabP n w X] q = a
  generalize pairTest n r s 2 q (tabP n w R₁) (tabP n w X) = c
  generalize pairTest n r s 2 q (tabP n w R₂) (tabP n w X) = d
  cases a <;> cases c <;> cases d <;> decide

end One

private structure Ch (n w : ℕ) (LR TR BP : ℕ → ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    (bp : ℕ) : Prop where
  hn : n < 16777216
  hw : n + 1 < 2 ^ w
  bp_lt : ∀ t < 3, pg w (mask w) bp t < n
  sep : ∀ γ ∈ G, (∀ t < 3, ∀ h : pg w (mask w) bp t < n, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1
  tr : ∀ j < 3, ∀ k < rcnt (LR j), ∃ γ ∈ G, Raw.Orb.PRep n w (TR (roff n (n * w) (LR j) + k)) γ

private theorem prod3_rep {n w : ℕ} {LR TR BP : ℕ → ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {bp : ℕ} (C : Ch n w LR TR BP G bp) {G₀ : ℕ} {υ : Equiv.Perm (Fin n)}
    (hG₀ : Raw.Orb.PRep n w G₀ υ) {a b c : ℕ} (ha : a < rcnt (LR 0)) (hb : b < rcnt (LR 1))
    (hc : c < rcnt (LR 2)) :
    ∃ g ∈ G, Raw.Orb.PRep n w (prod3 n w LR TR G₀ a b c) (υ * g) ∧
      Acts n (fun p => pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) G₀
        (TR (roff n (n * w) (LR 0) + a))) (TR (roff n (n * w) (LR 1) + b)))
          (pg w (mask w) (TR (roff n (n * w) (LR 2) + c)) p)) (υ * g) := by
  have hn32 : n < 2 ^ 32 := by have := C.hn; omega
  obtain ⟨t0, h0, r0⟩ := C.tr 0 (by norm_num) a ha
  obtain ⟨t1, h1, r1⟩ := C.tr 1 (by norm_num) b hb
  obtain ⟨t2, h2, r2⟩ := C.tr 2 (by norm_num) c hc
  have g2 := Raw.Orb.prep_pcomp hn32 (Raw.Orb.prep_pcomp hn32 hG₀ r0) r1
  have X := Raw.Orb.prep_pcomp hn32 g2 r2
  refine ⟨t0 * t1 * t2, mul_mem (mul_mem h0 h1) h2, ?_, ?_⟩
  · rw [show υ * (t0 * t1 * t2) = υ * t0 * t1 * t2 by simp only [mul_assoc]]
    exact X
  · rw [show υ * (t0 * t1 * t2) = υ * t0 * t1 * t2 by simp only [mul_assoc]]
    exact acts_comp (acts_pg g2) (acts_pg r2)

private theorem ch_of {n w kS kO BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {D : List (List ℤ)}
    {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    Ch n w LR TR (fun _ => BP) (Raw.Orb.Gen n S kO) BP := by
  obtain ⟨hsep, htr, -, hbp⟩ := GrpPf.group3 hb hh hl hNS hs
  exact ⟨by have := hb.2.2.1; omega, hb.2.1, hbp, hsep, fun j hj k hk => (htr j hj k hk).2⟩

theorem enumCnt_sound' {n w kS kO BP NS CH R₁ R₂ : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (h20 : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    (h1 : canonK n w (mask w) (n * w) R₁ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₁ = true)
    (h2 : canonK n w (mask w) (n * w) R₂ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₂ = true) :
    (filterProducts n (ordTest n 2) (chainTables n S base) (idT n) []).length =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 0 ∧
      (filterProducts n (ordTest n 3) (chainTables n S base) (idT n) []).length =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 1 ∧
      (filterProducts n (ordTest n 3) (chainTables n S base) (idT n) []).countP
          (pairTest n 7 12 2 3 (arrTable n (unpack n w R₁))) =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 2 ∧
      (filterProducts n (ordTest n 3) (chainTables n S base) (idT n) []).countP
          (pairTest n 7 12 2 3 (arrTable n (unpack n w R₂))) =
        fld20 (sumF (rcnt (LR 0)) (blkCnt n w LR TR BP (pidn n w) R₁ R₂)) 3 := by
  have C := ch_of hb hh hl hNS hs
  obtain ⟨-, -, hsift, -⟩ := GrpPf.group3 hb hh hl hNS hs
  have hn32 : n < 2 ^ 32 := by have := C.hn; omega
  obtain ⟨hct, hT⟩ := CFSG.KC.J2Cover.Snd.chainTables_eq_lvTab hb hp hl
  obtain ⟨ρ₁, hρ₁, hR₁⟩ := (hsift R₁ h1.1).1 h1.2
  obtain ⟨ρ₂, hρ₂, hR₂⟩ := (hsift R₂ h2.1).1 h2.2
  have hid := Raw.Orb.prep_pidn (w := w) C.hn C.hw
  have hsum := blk_eq n w LR TR BP (pidn n w) R₁ R₂
  rw [tri_congr (ψ := fun a b c =>
      (if ordTest n 2 (tabP n w (prod3 n w LR TR (pidn n w) a b c)) then 1 else 0) + 2 ^ 20 *
        ((if ordTest n 3 (tabP n w (prod3 n w LR TR (pidn n w) a b c)) then 1 else 0) + 2 ^ 20 *
          ((if (ordTest n 3 (tabP n w (prod3 n w LR TR (pidn n w) a b c)) &&
              pairTest n 7 12 2 3 (tabP n w R₁) (tabP n w (prod3 n w LR TR (pidn n w) a b c)))
              then 1 else 0) + 2 ^ 20 *
            (if (ordTest n 3 (tabP n w (prod3 n w LR TR (pidn n w) a b c)) &&
              pairTest n 7 12 2 3 (tabP n w R₂) (tabP n w (prod3 n w LR TR (pidn n w) a b c)))
              then 1 else 0))))
      fun a ha b hb c hc => by
        obtain ⟨g, hg, hX, hx⟩ := prod3_rep C hid ha hb hc
        rw [one_mul] at hX hx
        exact contrib_eq C.bp_lt C.sep hn32 hρ₁ hρ₂ hg hR₁ hR₂ hX hx] at hsum
  simp only [tri_add, tri_mul] at hsum
  have ind : ∀ (P : Prop) [Decidable P], (if P then 1 else 0) ≤ 1 := fun P _ => by
    split <;> omega
  have hcnt : ∀ (f p : Table → Bool),
      (filterProducts n f (chainTables n S base) (idT n) []).countP p =
        tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
          if (f (tabP n w (prod3 n w LR TR (pidn n w) a b c)) &&
            p (tabP n w (prod3 n w LR TR (pidn n w) a b c))) then 1 else 0 := by
    intro f p
    rw [countP_filterProducts, hct, idT_eq_tabP' C.hn C.hw, countProducts3 hn32 hT,
      List.countP_nil, Nat.zero_add]
  have hlen : ∀ f : Table → Bool,
      (filterProducts n f (chainTables n S base) (idT n) []).length =
        tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
          if f (tabP n w (prod3 n w LR TR (pidn n w) a b c)) then 1 else 0 := by
    intro f
    rw [← List.countP_true, hcnt]
    simp only [Bool.and_true]
  have hbd : ∀ φ : ℕ → ℕ → ℕ → ℕ, (∀ a b c, φ a b c ≤ 1) →
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) φ < 2 ^ 20 := fun φ h =>
    lt_of_le_of_lt (tri_le _ _ _ φ h) h20
  rw [hsum]
  refine ⟨(hlen _).trans (fld20_pack ?_ ?_ ?_ ?_).1.symm,
    (hlen _).trans (fld20_pack ?_ ?_ ?_ ?_).2.1.symm,
    (hcnt _ _).trans (fld20_pack ?_ ?_ ?_ ?_).2.2.1.symm,
    (hcnt _ _).trans (fld20_pack ?_ ?_ ?_ ?_).2.2.2.symm⟩
  all_goals exact hbd _ fun _ _ _ => ind _

theorem enumCntQ_sound' {n w kS kO BP NS CH R₁ R₂ q r s : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hsc : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (h20 : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    (h1 : canonK n w (mask w) (n * w) R₁ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₁ = true)
    (h2 : canonK n w (mask w) (n * w) R₂ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₂ = true)
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) :
    (filterProducts n (ordTest n q) (chainTables n S base) (idT n) []).countP
        (pairTest n r s 2 q (arrTable n (unpack n w R₁))) =
      fld20 (sumF (rcnt (LR 0)) (blkCntQ n w LR TR BP (pidn n w) R₁ R₂ q r s)) 0 ∧
    (filterProducts n (ordTest n q) (chainTables n S base) (idT n) []).countP
        (pairTest n r s 2 q (arrTable n (unpack n w R₂))) =
      fld20 (sumF (rcnt (LR 0)) (blkCntQ n w LR TR BP (pidn n w) R₁ R₂ q r s)) 1 := by
  have C := ch_of hb hh hl hNS hsc
  obtain ⟨-, -, hsift, -⟩ := GrpPf.group3 hb hh hl hNS hsc
  have hn32 : n < 2 ^ 32 := by have := C.hn; omega
  obtain ⟨hct, hT⟩ := CFSG.KC.J2Cover.Snd.chainTables_eq_lvTab hb hp hl
  obtain ⟨ρ₁, hρ₁, hR₁⟩ := (hsift R₁ h1.1).1 h1.2
  obtain ⟨ρ₂, hρ₂, hR₂⟩ := (hsift R₂ h2.1).1 h2.2
  have hid := Raw.Orb.prep_pidn (w := w) C.hn C.hw
  have hsum := blkQ_eq n w LR TR BP (pidn n w) R₁ R₂ q r s
  rw [tri_congr (ψ := fun a b c =>
      (if (ordTest n q (tabP n w (prod3 n w LR TR (pidn n w) a b c)) &&
          pairTest n r s 2 q (tabP n w R₁) (tabP n w (prod3 n w LR TR (pidn n w) a b c)))
          then 1 else 0) + 2 ^ 20 *
        (if (ordTest n q (tabP n w (prod3 n w LR TR (pidn n w) a b c)) &&
          pairTest n r s 2 q (tabP n w R₂) (tabP n w (prod3 n w LR TR (pidn n w) a b c)))
          then 1 else 0))
      fun a ha b hb c hc => by
        obtain ⟨g, hg, hX, hx⟩ := prod3_rep C hid ha hb hc
        rw [one_mul] at hX hx
        exact contribQ_eq C.bp_lt C.sep hn32 hρ₁ hρ₂ hg hR₁ hR₂ hX hx hq hr hs] at hsum
  simp only [tri_add, tri_mul] at hsum
  have ind : ∀ (P : Prop) [Decidable P], (if P then 1 else 0) ≤ 1 := fun P _ => by
    split <;> omega
  have hcnt : ∀ (f p : Table → Bool),
      (filterProducts n f (chainTables n S base) (idT n) []).countP p =
        tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
          if (f (tabP n w (prod3 n w LR TR (pidn n w) a b c)) &&
            p (tabP n w (prod3 n w LR TR (pidn n w) a b c))) then 1 else 0 := by
    intro f p
    rw [countP_filterProducts, hct, idT_eq_tabP' C.hn C.hw, countProducts3 hn32 hT,
      List.countP_nil, Nat.zero_add]
  have hbd : ∀ φ : ℕ → ℕ → ℕ → ℕ, (∀ a b c, φ a b c ≤ 1) →
      tri (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) φ < 2 ^ 20 := fun φ h =>
    lt_of_le_of_lt (tri_le _ _ _ φ h) h20
  rw [hsum]
  refine ⟨(hcnt _ _).trans (fld20_pack2 ?_ ?_).1.symm, (hcnt _ _).trans (fld20_pack2 ?_ ?_).2.symm⟩
  all_goals exact hbd _ fun _ _ _ => ind _

private theorem prep_unique {n w P : ℕ} {a b : Equiv.Perm (Fin n)} (ha : Raw.Orb.PRep n w P a)
    (hb : Raw.Orb.PRep n w P b) : a = b :=
  Equiv.ext fun x => Fin.ext ((ha x).symm.trans (hb x))

theorem enumCntU_sound' {n w kS kO BP NS CH U : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hU : canonK n w (mask w) (n * w) U = true)
    (hUn : ∀ j < kS, siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0
      (pcomp n w (mask w) U (pcomp n w (mask w) (PS j) (pinvS n w (mask w) U))) = true)
    (hU2 : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 (pcomp n w (mask w) U U) = true)
    (hUo : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 U = false) :
    (filterProducts n (ordTest n 2) (chainTables n S base) (arrTable n (unpack n w U)) []).length =
      sumF (rcnt (LR 0)) (blkCntU n w LR TR BP U) := by
  have C := ch_of hb hh hl hNS hs
  obtain ⟨-, -, hsift, -⟩ := GrpPf.group3 hb hh hl hNS hs
  set G := Raw.Orb.Gen n S kO with hGdef
  have hn32 : n < 2 ^ 32 := by have := C.hn; omega
  obtain ⟨hct, hT⟩ := CFSG.KC.J2Cover.Snd.chainTables_eq_lvTab hb hp hl
  obtain ⟨-, -, -, hUr⟩ := PF.canon_facts hU
  obtain ⟨δ, hδ, hδP⟩ := (hsift _ (canon_pcomp hU hU)).1 hU2
  have hinj : Function.Injective
      (fun x : Fin n => (⟨pg w (mask w) U x, hUr x x.2⟩ : Fin n)) := by
    intro a b e
    have e' : pg w (mask w) U a = pg w (mask w) U b := congrArg Fin.val e
    apply δ.injective
    apply Fin.ext
    rw [← hδP a, ← hδP b, PF.pg_pcomp hn32 a.2, PF.pg_pcomp hn32 b.2, e']
  let υ : Equiv.Perm (Fin n) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
  have hυ : Raw.Orb.PRep n w U υ := fun x => rfl
  have hυ2 : υ * υ ∈ G := prep_unique hδP (Raw.Orb.prep_pcomp hn32 hυ hυ) ▸ hδ
  have hυG : υ ∉ G := fun h => by
    have := (hsift U hU).2 ⟨υ, h, hυ⟩
    rw [hUo] at this
    exact Bool.false_ne_true this
  have hinjK : CFSG.KS.PinvS.InjK n w U := ⟨hUr, fun a ha b hb e => by
    have := @hinj ⟨a, ha⟩ ⟨b, hb⟩ (Fin.ext e)
    exact congrArg Fin.val this⟩
  have hυi : Raw.Orb.PRep n w (pinvS n w (mask w) U) υ⁻¹ := fun y => by
    have e := hυ (υ⁻¹ y)
    rw [show υ (υ⁻¹ y) = y by simp] at e
    rw [← e, CFSG.KS.PinvS.pg_pinvS (by have := C.hw; omega) hinjK (υ⁻¹ y).2]
  have hk : kO ≤ kS := by
    have := (Raw.Orb.rawHeadOK_of hb hh).1
    rw [hb.2.2.2.1] at this
    exact this
  have hnorm : ∀ g ∈ G, υ * g * υ⁻¹ ∈ G := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => υ * g * υ⁻¹ ∈ G) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨j, rfl⟩
      have hj : j.val < kS := by have := j.2; omega
      obtain ⟨hPS, -⟩ := Raw.Orb.prep_PS hb hp hj
      obtain ⟨hs1, -, hs2⟩ := Raw.Orb.permOK_facts (allN_spec hp j hj)
      have hcPS : canonK n w (mask w) (n * w) (PS j) = true :=
        canonK_of C.hn C.hw hs1 fun i hi => (hs2 i hi).1
      have hcan := canon_pcomp hU (canon_pcomp hcPS (CFSG.KS.PinvS.canonK_pinvS hU hinjK))
      obtain ⟨γ, hγ, hγP⟩ := (hsift _ hcan).1 (hUn j hj)
      have e := prep_unique hγP (Raw.Orb.prep_pcomp hn32 hυ (Raw.Orb.prep_pcomp hn32 hPS hυi))
      rw [← mul_assoc] at e
      exact e ▸ hγ
    · simp
    · intro x y _ _ hx hy
      have := mul_mem hx hy
      simpa [mul_assoc] using this
    · intro x _ hx
      have := inv_mem hx
      simpa [mul_assoc] using this
  have hsum := blkU_eq n w LR TR BP U
  rw [tri_congr (ψ := fun a b c =>
      if ordTest n 2 (tabP n w (prod3 n w LR TR U a b c)) then 1 else 0)
      fun a ha b hb c hc => by
        obtain ⟨g, hg, hX, hx⟩ := prod3_rep C hυ ha hb hc
        have h2 : (υ * g) ^ 2 ∈ G := by
          rw [show (υ * g) ^ 2 = υ * g * υ⁻¹ * (υ * υ) * g by
            rw [sq]; simp only [mul_assoc, inv_mul_cancel_left]]
          exact mul_mem (mul_mem (hnorm g hg) hυ2) hg
        have hne : υ * g ≠ 1 := fun e => hυG (by
          rw [eq_inv_of_mul_eq_one_left e]
          exact inv_mem hg)
        rw [fix3_eq C.bp_lt C.sep hx h2]
        show _ = if ordW n [tabP n w (prod3 n w LR TR U a b c)] 2 then 1 else 0
        rw [ordW, show divParts 2 = [1] by decide]
        simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [powFixW_eq (acts_single (acts_ap hn32 hX)), powFixW_eq (acts_single (acts_ap hn32 hX)),
          pow_one]
        simp only [hne, decide_false, Bool.not_false, Bool.and_true]
        cases decide ((υ * g) ^ 2 = 1) <;> rfl] at hsum
  rw [hsum, ← List.countP_true, countP_filterProducts, hct, countProducts3 hn32 hT,
    List.countP_nil, Nat.zero_add]
  simp only [Bool.and_true]

end CFSG.KC.J2Enum.CntPf

end
