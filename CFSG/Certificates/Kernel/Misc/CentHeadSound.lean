module

public import Certificates.Data.Kernel.Misc.CentHead
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.RankThree.Native.ChainCentralizerD
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Certificates.NativeSchreierCard
public import Mathlib.GroupTheory.Schreier
public import Std.Data.HashMap

public section

namespace CFSG.KC.CentHead

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.KC.CentSrch
open CFSG.Certificates.ChainArrays CFSG.RankThree.Native CFSG.Monster.B.Co2

theorem levDataK {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb) {i : ℕ}
    (hi : i < nb) :
    rcnt (LR i) = (lev n S base i).pts.size ∧
    (∀ k < rcnt (LR i), rpt w (mask w) (LR i) k = (lev n S base i).pts[k]! ∧
      rpt w (mask w) (LR i) k < n ∧
      rpos w (mask w) (n * w) (LR i) (rpt w (mask w) (LR i) k) = k ∧
      Orb.PRep n w (TR (roff n (n * w) (LR i) + k)) (levT n S base i k) ∧
      Orb.PRep n w (TRI (roff n (n * w) (LR i) + k)) (levT n S base i k)⁻¹) ∧
    (∀ z < n, rpos w (mask w) (n * w) (LR i) z < rcnt (LR i) →
      rpt w (mask w) (LR i) (rpos w (mask w) (n * w) (LR i) z) = z) := by
  have hbl := Orb.base_lt_of_levels hb hl
  obtain ⟨A, P⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  obtain ⟨-, -, hR, -, -, -⟩ := Orb.levelK_facts (hl i hi)
  have hiQ : i < Q.baseCount := hnb ▸ hi
  refine ⟨A.cnt, fun k hk => ?_, fun z hz hq => hR.pos z hz hq⟩
  have hk' : k < (lev n S base i).pts.size := A.cnt ▸ hk
  have e : permOfArr n (unpack n w (TR (roff n (n * w) (LR i) + k))) = levT n S base i k :=
    Equiv.ext fun x => Fin.ext (((A.tr k hk').1 x).symm.trans (hA.rep_levT hF hiQ hk' x))
  refine ⟨A.pt k hk', (hR.pt k hk).1, (hR.pt k hk).2, ?_, ?_⟩
  · rw [← e]
    exact (P k hk).1
  · rw [← e]
    exact (P k hk).2

theorem levPosK {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb) {i : ℕ}
    (hi : i < nb) {h : Equiv.Perm (Fin n)} (hh : h ∈ Q.levelSubgroup i) :
    rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩)) < rcnt (LR i) ∧
      rpt w (mask w) (LR i) (rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩))) =
        h (Q.base.get ⟨i, by omega⟩) ∧
      Orb.PRep n w (TR (roff n (n * w) (LR i) +
        rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩))))
        (levT n S base i (rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩)))) ∧
      Orb.PRep n w (TRI (roff n (n * w) (LR i) +
        rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩))))
        (levT n S base i (rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩))))⁻¹ ∧
      (levT n S base i (rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩))))⁻¹ * h ∈
        Q.levelSubgroup (i + 1) := by
  obtain ⟨k, hk, hpt, hk1⟩ := exists_levT_inv_mul_mem hA hF hQ (by omega) hh
  obtain ⟨hc, D, -⟩ := levDataK hA hF hb hp hl hnb hi
  have hkc : k < rcnt (LR i) := hc ▸ hk
  obtain ⟨d1, -, d3, d4, d5⟩ := D k hkc
  have e : rpos w (mask w) (n * w) (LR i) (h (Q.base.get ⟨i, by omega⟩)) = k := by
    rw [← hpt, ← d1, d3]
  rw [e]
  exact ⟨hkc, d1.trans hpt, d4, d5, hk1⟩

theorem wAt_eq (W l : ℕ) : wAt W l = W / 2 ^ (16 * l) % 65536 := by
  have e := Orb.fld_eq W (16 * l) 16
  rw [Orb.mask_eq'] at e
  exact e

theorem lor16_eq {W₁ v : ℕ} (h : W₁ < 65536) :
    Nat.lor W₁ (Nat.shiftLeft v 16) = W₁ + v * 65536 := by
  change W₁ ||| v <<< 16 = _
  rw [Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt (by omega : W₁ < 2 ^ 16), Nat.shiftLeft_eq]
  omega

theorem wAt_zero {W : ℕ} (h : W < 65536) : wAt W 0 = W := by
  rw [wAt_eq, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt h]

theorem wAt_lor16 {W₁ v : ℕ} (h1 : W₁ < 65536) (h2 : v < 65536) :
    wAt (Nat.lor W₁ (Nat.shiftLeft v 16)) 0 = W₁ ∧ wAt (Nat.lor W₁ (Nat.shiftLeft v 16)) 1 = v := by
  have h16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  rw [wAt_eq, wAt_eq, lor16_eq h1, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mul_one, h16]
  omega

theorem invW_one (w m : ℕ) (TRI : ℕ → ℕ) (W y : ℕ) :
    invW w m TRI W 1 y = pg w m (TRI (wAt W 0)) y :=
  Orb.strictN_eq _ _

theorem invW_two (w m : ℕ) (TRI : ℕ → ℕ) (W y : ℕ) :
    invW w m TRI W 2 y = pg w m (TRI (wAt W 1)) (pg w m (TRI (wAt W 0)) y) := by
  have e : invW w m TRI W 2 y = pg w m (TRI (wAt W 1)) (invW w m TRI W 1 y) :=
    Orb.strictN_eq _ _
  rw [e, invW_one]

theorem headPt_true {n w : ℕ} {LR TRI : ℕ → ℕ} {X X2 a k₀ k₁ : ℕ}
    (hr0 : roff n (n * w) (LR 0) + rcnt (LR 0) ≤ 65536)
    (hr1 : roff n (n * w) (LR 1) + rcnt (LR 1) ≤ 65536)
    (h0 : rpos w (mask w) (n * w) (LR 0) a = k₀) (hk0 : k₀ < rcnt (LR 0))
    (h1 : rpos w (mask w) (n * w) (LR 1)
      (pg w (mask w) (TRI (roff n (n * w) (LR 0) + k₀)) (pg w (mask w) X a)) = k₁)
    (hk1 : k₁ < rcnt (LR 1))
    (h2 : rpos w (mask w) (n * w) (LR 2) (pg w (mask w) (TRI (roff n (n * w) (LR 1) + k₁))
      (pg w (mask w) (TRI (roff n (n * w) (LR 0) + k₀)) (pg w (mask w) X2 a))) < rcnt (LR 2)) :
    headPt n w LR TRI X X2 a = true := by
  obtain ⟨e0, e1⟩ := wAt_lor16 (W₁ := roff n (n * w) (LR 0) + k₀)
    (v := roff n (n * w) (LR 1) + k₁) (by omega) (by omega)
  have h1' : rpos w (mask w) (n * w) (LR 1)
      (invW w (mask w) TRI (roff n (n * w) (LR 0) + k₀) 1 (pg w (mask w) X a)) = k₁ := by
    rw [invW_one, wAt_zero (by omega)]
    exact h1
  have h2' : rpos w (mask w) (n * w) (LR 2) (invW w (mask w) TRI
      (Nat.lor (roff n (n * w) (LR 0) + k₀) (Nat.shiftLeft (roff n (n * w) (LR 1) + k₁) 16)) 2
      (pg w (mask w) X2 a)) < rcnt (LR 2) := by
    rw [invW_two, e0, e1]
    exact h2
  clear h1 h2 e0 e1
  subst h0 h1'
  unfold headPt
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq]
  exact ⟨hk0, hk1, h2'⟩

theorem headK_sound {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb) (h3 : 3 ≤ nb)
    (hro : ∀ i < nb, roff n (n * w) (LR i) + rcnt (LR i) ≤ 65536) {X X2 LM : ℕ} {x : Equiv.Perm (Fin n)} (hx : Orb.PRep n w X x) (hx2 : Orb.PRep n w X2 (x ^ 2))
    (hr1 : x (Q.base.get ⟨0, by omega⟩) = Q.base.get ⟨1, by omega⟩)
    (hr2 : (x ^ 2) (Q.base.get ⟨0, by omega⟩) = Q.base.get ⟨2, by omega⟩)
    (h : headK n w LR TRI X X2 LM = true) {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup)
    (hc : g * x = x * g) : Nat.testBit LM (g (Q.base.get ⟨0, by omega⟩)) = true := by
  have hg0 : g ∈ Q.levelSubgroup 0 := by
    rw [Q.levelSubgroup_zero_eq_original hQ]
    exact hg
  obtain ⟨p0, -, -, i0, h1⟩ := levPosK hA hF hQ hb hp hl hnb (i := 0) (by omega) hg0
  obtain ⟨p1, -, -, i1, h2⟩ := levPosK hA hF hQ hb hp hl hnb (i := 1) (by omega) h1
  obtain ⟨p2, -⟩ := levPosK hA hF hQ hb hp hl hnb (i := 2) (by omega) h2
  have hxa : x (g (Q.base.get ⟨0, by omega⟩)) = g (Q.base.get ⟨1, by omega⟩) := by
    have e := congrArg (fun σ : Equiv.Perm (Fin n) => σ (Q.base.get ⟨0, by omega⟩)) hc
    simp only [Equiv.Perm.mul_apply] at e
    rw [← hr1]
    exact e.symm
  have hx2a : (x ^ 2) (g (Q.base.get ⟨0, by omega⟩)) = g (Q.base.get ⟨2, by omega⟩) := by
    have hc2 : g * x ^ 2 = x ^ 2 * g := (Commute.pow_right hc 2).eq
    have e := congrArg (fun σ : Equiv.Perm (Fin n) => σ (Q.base.get ⟨0, by omega⟩)) hc2
    simp only [Equiv.Perm.mul_apply] at e
    rw [← hr2]
    exact e.symm
  have r0 := hro 0 (by omega)
  have r1 := hro 1 (by omega)
  have hpt : headPt n w LR TRI X X2 (g (Q.base.get ⟨0, by omega⟩)) = true := by
    refine headPt_true r0 r1 rfl p0 ?_ p1 ?_
    · rw [hx, hxa, i0]
      rfl
    · rw [hx2, hx2a, i0, i1]
      exact p2
  unfold headK at h
  have hk : (!(headPt n w LR TRI X X2 (g (Q.base.get ⟨0, by omega⟩))) ||
      Nat.beq (Nat.land (Nat.shiftRight LM (g (Q.base.get ⟨0, by omega⟩))) (nat_lit 1))
        (nat_lit 1)) = true :=
    Orb.allN_iff.1 h _ (g (Q.base.get ⟨0, by omega⟩)).2
  rw [hpt, Bool.not_true, Bool.false_or] at hk
  have e : Nat.shiftRight LM (g (Q.base.get ⟨0, by omega⟩)) % 2 = 1 := by
    rw [← Nat.and_one_is_mod]
    exact Nat.eq_of_beq_eq_true hk
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  exact decide_eq_true e

theorem card_centralizer_le_of_head {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
    {chunks : ℕ} (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb) (h3 : 3 ≤ nb)
    (hro : ∀ i < nb, roff n (n * w) (LR i) + rcnt (LR i) ≤ 65536) {X X2 LM : ℕ}
    {x : Equiv.Perm (Fin n)} (hx : Orb.PRep n w X x) (hx2 : Orb.PRep n w X2 (x ^ 2))
    (hr1 : x (Q.base.get ⟨0, by omega⟩) = Q.base.get ⟨1, by omega⟩)
    (hr2 : (x ^ 2) (Q.base.get ⟨0, by omega⟩) = Q.base.get ⟨2, by omega⟩)
    (h : headK n w LR TRI X X2 LM = true) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ Q.originalSubgroup) ≤
      ((List.finRange n).filter fun a : Fin n => Nat.testBit LM a.val).length *
        Nat.card ↥(Q.levelSubgroup 3 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n)))) := by
  set b₀ := Q.base.get ⟨0, by omega⟩
  have hL : ∀ g ∈ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ Q.originalSubgroup,
      g • b₀ ∈ (List.finRange n).filter fun a : Fin n => Nat.testBit LM a.val := by
    intro g hg
    obtain ⟨hgc, hgP⟩ := Subgroup.mem_inf.1 hg
    rw [List.mem_filter]
    refine ⟨List.mem_finRange _, ?_⟩
    have hc : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
    rw [Equiv.Perm.smul_def]
    exact headK_sound hA hF hQ hb hp hl hnb h3 hro hx hx2 hr1 hr2 h hgP hc
  refine (CFSG.RankThree.Native.card_le_of_orbit_subset _ b₀ _ hL).trans
    (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le ?_))
  intro g hg
  obtain ⟨⟨hgc, hgP⟩, hgs⟩ := hg
  have hc : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
  have hg0 : g b₀ = b₀ := hgs
  have hfix : ∀ k : ℕ, g ((x ^ k) b₀) = (x ^ k) b₀ := fun k => by
    have hk : Commute g (x ^ k) := Commute.pow_right (show Commute g x from hc) k
    rw [← Equiv.Perm.mul_apply, hk.eq, Equiv.Perm.mul_apply, hg0]
  have hg1 : g ∈ Q.levelSubgroup 1 := by
    have e := Q.levelSubgroup_succ_eq_stabilizer hQ ⟨0, by omega⟩
    rw [e, ← Q.levelSubgroup_zero_eq_original hQ] at *
    exact ⟨hgP, hg0⟩
  have hg2 : g ∈ Q.levelSubgroup 2 := by
    have e := Q.levelSubgroup_succ_eq_stabilizer hQ ⟨1, by omega⟩
    refine e ▸ ⟨hg1, ?_⟩
    change g (Q.base.get ⟨1, by omega⟩) = Q.base.get ⟨1, by omega⟩
    have := hfix 1
    rwa [pow_one, hr1] at this
  have e := Q.levelSubgroup_succ_eq_stabilizer hQ ⟨2, by omega⟩
  refine ⟨e ▸ ⟨hg2, ?_⟩, hgc⟩
  change g (Q.base.get ⟨2, by omega⟩) = Q.base.get ⟨2, by omega⟩
  have := hfix 2
  rwa [hr2] at this

theorem nrecAnd_iff (P : ℕ → Bool) (N : ℕ) :
    Nat.rec (motive := fun _ => Bool) true (fun r ih => bAnd(P r, ih)) N = true ↔
      ∀ r < N, P r = true := by
  induction N with
  | zero => exact ⟨fun _ r hr => absurd hr (Nat.not_lt_zero r), fun _ => rfl⟩
  | succ N ih =>
    change bAnd(P N, Nat.rec (motive := fun _ => Bool) true (fun r ih => bAnd(P r, ih)) N) =
      true ↔ _
    rw [Orb.bAnd_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ r hr
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h | rfl
      · exact h2 r h
      · exact h1
    · intro h
      exact ⟨h N (Nat.lt_succ_self N), fun r hr => h r (Nat.lt_succ_of_lt hr)⟩

theorem foldN_sumK {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ} (hf : ∀ q s, f q s = s + g q) (c : ℕ) :
    foldN c f 0 = ∑ q ∈ Finset.range c, g q := by
  rw [Orb.foldN_eq]
  suffices h : ∀ c s, (List.range c).foldr f s = s + ∑ q ∈ Finset.range c, g q by
    rw [h, Nat.zero_add]
  intro c
  induction c with
  | zero => intro s; simp
  | succ c ih =>
    intro s
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih, hf,
      Finset.sum_range_succ]
    ring

theorem fld_lor {W v s : ℕ} (h : W < 2 ^ s) :
    Nat.lor W (Nat.shiftLeft v s) = W + v * 2 ^ s := by
  change W ||| v <<< s = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
  ring

theorem fld_low {W v s j l : ℕ} (hW : W < 2 ^ (s * j)) (hl : l < j) :
    (W + v * 2 ^ (s * j)) / 2 ^ (s * l) % 2 ^ s = W / 2 ^ (s * l) % 2 ^ s := by
  have e : 2 ^ (s * j) = 2 ^ (s * l) * (2 ^ s * 2 ^ (s * (j - l - 1))) := by
    rw [← pow_add, ← pow_add]
    congr 1
    have : j = l + 1 + (j - l - 1) := by omega
    conv_lhs => rw [this]
    ring
  have e2 : v * (2 ^ (s * l) * (2 ^ s * 2 ^ (s * (j - l - 1)))) =
      2 ^ (s * l) * (2 ^ s * (v * 2 ^ (s * (j - l - 1)))) := by ring
  rw [e, e2, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem fld_top {W v s j : ℕ} (hW : W < 2 ^ (s * j)) (hv : v < 2 ^ s) :
    (W + v * 2 ^ (s * j)) / 2 ^ (s * j) % 2 ^ s = v := by
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hW, Nat.zero_add,
    Nat.mod_eq_of_lt hv]

theorem fld_lt {W v s j : ℕ} (hW : W < 2 ^ (s * j)) (hv : v < 2 ^ s) :
    W + v * 2 ^ (s * j) < 2 ^ (s * (j + 1)) := by
  rw [Nat.mul_succ, pow_add]
  nlinarith

theorem wAt_eq' (W l : ℕ) : wAt W l = W / 2 ^ (16 * l) % 2 ^ 16 := wAt_eq W l

theorem fwdW_succ (w m : ℕ) (TR : ℕ → ℕ) (W j z : ℕ) :
    fwdW w m TR W (j + 1) z = fwdW w m TR W j (pg w m (TR (wAt W j)) z) :=
  Orb.strictN_eq _ _

theorem invW_succ (w m : ℕ) (TRI : ℕ → ℕ) (W j a : ℕ) :
    invW w m TRI W (j + 1) a = pg w m (TRI (wAt W j)) (invW w m TRI W j a) :=
  Orb.strictN_eq _ _

theorem fwdW_congr (w m : ℕ) (TR : ℕ → ℕ) {W W' : ℕ} :
    ∀ j, (∀ l < j, wAt W l = wAt W' l) → ∀ z, fwdW w m TR W j z = fwdW w m TR W' j z := by
  intro j
  induction j with
  | zero => intro _ z; rfl
  | succ j ih =>
    intro h z
    rw [fwdW_succ, fwdW_succ, h j (Nat.lt_succ_self j)]
    exact ih (fun l hl => h l (Nat.lt_succ_of_lt hl)) _

theorem invW_congr (w m : ℕ) (TRI : ℕ → ℕ) {W W' : ℕ} :
    ∀ j, (∀ l < j, wAt W l = wAt W' l) → ∀ a, invW w m TRI W j a = invW w m TRI W' j a := by
  intro j
  induction j with
  | zero => intro _ a; rfl
  | succ j ih =>
    intro h a
    rw [invW_succ, invW_succ, h j (Nat.lt_succ_self j),
      ih (fun l hl => h l (Nat.lt_succ_of_lt hl)) a]

theorem prep_ppowK {n w P : ℕ} {g : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (hP : Orb.PRep n w P g) :
    ∀ e, Orb.PRep n w (ppow n w (mask w) (pidn n w) P e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact Orb.prep_pidn hn hw
  | e + 1 => by
    have he : ppow n w (mask w) (pidn n w) P (e + 1) =
        pcomp n w (mask w) P (ppow n w (mask w) (pidn n w) P e) := Orb.strictN_eq _ _
    rw [he, pow_succ']
    exact Orb.prep_pcomp (by omega) hP (prep_ppowK hn hw hP e)

theorem levT_base {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks) {i : ℕ}
    (hi : i < Q.baseCount) {k : ℕ} (hk : k < (lev n S base i).pts.size) :
    ((levT n S base i k (Q.base.get ⟨i, hi⟩) : Fin n) : ℕ) = (lev n S base i).pts[k]! := by
  have ht := hA.transversal_of_lt hF hi hk
  have hx : levPts Q S base i k ∈ Q.orbitPoints ⟨i, hi⟩ := by
    change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).isSome = true
    rw [ht]
    rfl
  obtain ⟨-, -, ht'⟩ := hA.orbitPoints_spec hF hi hx
  obtain ⟨-, -, hval⟩ := Q.transversal_getD_spec ⟨i, hi⟩ _ hx
  rw [ht', hA.levPts_val hF hi hk, (hA.levelFacts hF hi).pos_pts k hk] at hval
  rw [hval]
  exact hA.levPts_val hF hi hk

noncomputable def cntXY {n : ℕ} (Q : RawSchreierDatum n) (x y p : Equiv.Perm (Fin n)) (j : ℕ) :
    ℕ :=
  Nat.card {h : Equiv.Perm (Fin n) // h ∈ Q.levelSubgroup j ∧ p * h * x = x * (p * h) ∧
    p * h * y = y * (p * h)}

theorem cntXY_succ {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb)
    (x y p : Equiv.Perm (Fin n)) {j : ℕ} (hj : j < nb) :
    cntXY Q x y p j =
      ∑ k ∈ Finset.range (rcnt (LR j)), cntXY Q x y (p * levT n S base j k) (j + 1) := by
  classical
  have hjQ : j < Q.baseCount := by omega
  have est := Q.levelSubgroup_succ_eq_stabilizer hQ ⟨j, hjQ⟩
  obtain ⟨hc, D, -⟩ := levDataK hA hF hb hp hl hnb hj
  unfold cntXY
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun h => rpos w (mask w) (n * w) (LR j) (h (Q.base.get ⟨j, hjQ⟩)))
    (t := Finset.range (rcnt (LR j))) (by
      intro h hh
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        Finset.coe_range, Set.mem_Iio] at hh ⊢
      exact (levPosK hA hF hQ hb hp hl hnb hj hh.1).1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkc : k < rcnt (LR j) := Finset.mem_range.1 hk
  have hk' : k < (lev n S base j).pts.size := hc ▸ hkc
  obtain ⟨d1, -, d3, -, -⟩ := D k hkc
  have htm : levT n S base j k ∈ Q.levelSubgroup j := hA.levT_mem hF hjQ hk'
  have htb : ((levT n S base j k (Q.base.get ⟨j, hjQ⟩) : Fin n) : ℕ) =
      rpt w (mask w) (LR j) k := by
    rw [levT_base hA hF hjQ hk', d1]
  refine Finset.card_bij' (fun h _ => (levT n S base j k)⁻¹ * h)
    (fun h _ => levT n S base j k * h) ?_ ?_ ?_ ?_
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    obtain ⟨⟨hhj, c1, c2⟩, hpos⟩ := hh
    obtain ⟨-, -, -, -, hmem⟩ := levPosK hA hF hQ hb hp hl hnb hj hhj
    rw [hpos] at hmem
    refine ⟨hmem, ?_, ?_⟩
    · rw [mul_assoc p, mul_inv_cancel_left]
      exact c1
    · rw [mul_assoc p, mul_inv_cancel_left]
      exact c2
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    obtain ⟨hh1, c1, c2⟩ := hh
    rw [est] at hh1
    obtain ⟨hh1j, hfix⟩ := Subgroup.mem_inf.1 hh1
    have hfix' : h (Q.base.get ⟨j, hjQ⟩) = Q.base.get ⟨j, hjQ⟩ := hfix
    refine ⟨⟨(Q.levelSubgroup j).mul_mem htm hh1j, ?_, ?_⟩, ?_⟩
    · rw [← mul_assoc]
      exact c1
    · rw [← mul_assoc]
      exact c2
    · rw [Equiv.Perm.mul_apply, hfix', htb, d3]
  · intro h _
    exact mul_inv_cancel_left _ _
  · intro h _
    exact inv_mul_cancel_left _ _

theorem cntXY_term {n : ℕ} {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    (x y p : Equiv.Perm (Fin n)) :
    cntXY Q x y p Q.baseCount = if p * x = x * p ∧ p * y = y * p then 1 else 0 := by
  unfold cntXY
  simp only [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot]
  split_ifs with hc
  · rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (a.2.1.trans b.2.1.symm)⟩, ⟨⟨1, rfl, ?_, ?_⟩⟩⟩
    · rw [mul_one]
      exact hc.1
    · rw [mul_one]
      exact hc.2
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨h, h1, c1, c2⟩ => hc ?_⟩
    subst h1
    rw [mul_one] at c1 c2
    exact ⟨c1, c2⟩

theorem dAt_eq {n w DP J q : ℕ} (hq : q < n) :
    dAt n w (mask w) DP J q =
      pg w (mask w) (Nat.land (Nat.shiftRight DP (Nat.mul (Nat.mul n w) J)) (mask (Nat.mul n w)))
        q := by
  unfold dAt
  rw [Orb.pg_eq, Orb.pg_eq, Orb.fld_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · have h1 : i + w * q < Nat.mul n w := by
      change i + w * q < n * w
      nlinarith
    simp only [hi, decide_true, Bool.true_and, h1]
    congr 1
    change i + w * (n * J + q) = i + w * q + n * w * J
    ring
  · simp [hi]

theorem dOK_prep {n w X Y DP : ℕ} {x y : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (hx : Orb.PRep n w X x) (hy : Orb.PRep n w Y y)
    (hd : dOK n w X Y DP = true) {J : ℕ} (hJ : J < 8) (q : Fin n) :
    dAt n w (mask w) DP J q = (x ^ ((J + 1) % 3) * y ^ ((J + 1) / 3)) q := by
  unfold dOK at hd
  rw [Orb.bAnd_eq, Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hd
  have e := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hd.2.2 J hJ)
  rw [dAt_eq q.2, e]
  exact Orb.prep_pcomp (by omega) (prep_ppowK hn hw hx _) (prep_ppowK hn hw hy _) q

theorem land7_lt (a : ℕ) : Nat.land a 7 < 8 :=
  Nat.lt_succ_of_le (Nat.and_le_right : a &&& 7 ≤ 7)

section Prune

variable {n w BP DP E i B : ℕ} {bs : ℕ → Fin n} {c : Equiv.Perm (Fin n)}
  {d : ℕ → Equiv.Perm (Fin n)}
  (hd : ∀ J < 8, ∀ q : Fin n, dAt n w (mask w) DP J q = d J q)
  (hcd : ∀ J < 8, c * d J = d J * c) (hbs : ∀ t ≤ i, pg w (mask w) BP t = bs t)
  (hB : ∀ l < i, pg w (mask w) B l = c (bs l))
include hd hcd hbs hB

theorem dAt_c {J l : ℕ} (hJ : J < 8) (hl : l ≤ i)
    (he : dAt n w (mask w) DP J (pg w (mask w) BP l) = pg w (mask w) BP i) :
    dAt n w (mask w) DP J (c (bs l)) = c (bs i) := by
  rw [hbs l hl, hbs i le_rfl, hd J hJ] at he
  have hdl : d J (bs l) = bs i := Fin.ext he
  rw [hd J hJ, ← Equiv.Perm.mul_apply, ← hcd J hJ, Equiv.Perm.mul_apply, hdl]

theorem relOK_of {a : ℕ} (ha : a = c (bs i)) (hr : relsOK n w (mask w) BP DP E i = true) :
    CentSrch.relOK n w (mask w) DP E i B a = true := by
  unfold relsOK at hr
  unfold CentSrch.relOK
  rw [nrecAnd_iff] at hr ⊢
  intro r hr'
  have h := hr r hr'
  rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.ble_dec, decide_eq_true_eq] at h
  obtain ⟨hl, he⟩ := h
  have he' := Nat.eq_of_beq_eq_true he
  have himg : imgAt w (mask w) B i a (Nat.land (eRel E r) 7) = c (bs (Nat.land (eRel E r) 7)) := by
    unfold imgAt
    rw [Orb.nIf_eq, Orb.blt_dec]
    split_ifs with h
    · exact hB _ (of_decide_eq_true h)
    · have : Nat.land (eRel E r) 7 = i := by
        simp only [decide_eq_true_eq] at h
        exact Nat.le_antisymm hl (Nat.not_lt.1 h)
      rw [this, ha]
  rw [himg, dAt_c hd hcd hbs hB (land7_lt _) hl he', ← ha, Orb.beq_dec]
  exact decide_eq_true rfl

theorem fixAll_of {a : ℕ} (ha : a = c (bs i)) (hr : relsOK n w (mask w) BP DP E i = true) :
    fixAll n w (mask w) DP E i a = true := by
  unfold relsOK at hr
  unfold fixAll
  rw [nrecAnd_iff] at hr ⊢
  intro r hr'
  have h := hr r hr'
  rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.ble_dec, decide_eq_true_eq] at h
  obtain ⟨-, he⟩ := h
  have he' := Nat.eq_of_beq_eq_true he
  rw [Bool.or_eq_true, Orb.beq_dec, Orb.beq_dec]
  by_cases hli : Nat.land (eRel E r) 7 = i
  · right
    rw [hli] at he'
    rw [ha, dAt_c hd hcd hbs hB (land7_lt _) le_rfl he']
    exact decide_eq_true rfl
  · left
    rw [decide_eq_false hli]
    rfl

theorem forced_of {a : ℕ} (ha : a = c (bs i)) (hlt : eL E < i)
    (he : dAt n w (mask w) DP (eJ E) (pg w (mask w) BP (eL E)) = pg w (mask w) BP i) :
    dAt n w (mask w) DP (eJ E) (pg w (mask w) B (eL E)) = a := by
  rw [hB _ hlt, dAt_c hd hcd hbs hB (J := eJ E) (land7_lt _) hlt.le he, ha]

end Prune

noncomputable def bsK {n : ℕ} (Q : RawSchreierDatum n) (t : ℕ) : Fin n :=
  if h : t < Q.baseCount then Q.base.get ⟨t, h⟩ else toFin Q 0

theorem bsK_of {n : ℕ} {Q : RawSchreierDatum n} {t : ℕ} (h : t < Q.baseCount) :
    bsK Q t = Q.base.get ⟨t, h⟩ :=
  dif_pos h

theorem levelSubgroup_le_orig {n : ℕ} {Q : RawSchreierDatum n} (hQ : ValidSchreier Q) :
    ∀ j ≤ Q.baseCount, Q.levelSubgroup j ≤ Q.originalSubgroup := by
  intro j
  induction j with
  | zero => intro _; rw [Q.levelSubgroup_zero_eq_original hQ]
  | succ j ih =>
    intro hj
    rw [Q.levelSubgroup_succ_eq_stabilizer hQ ⟨j, by omega⟩]
    exact inf_le_left.trans (ih (by omega))

theorem leafOne {n w nb BP V Bm X : ℕ} {Q : RawSchreierDatum n} {TR : ℕ → ℕ}
    (hQ : ValidSchreier Q) (hnb : Q.baseCount = nb) {x p : Equiv.Perm (Fin n)}
    (hx : Orb.PRep n w X x) (hxQ : x ∈ Q.originalSubgroup) (hpQ : p ∈ Q.originalSubgroup)
    (hf : ∀ z : Fin n, fwdW w (mask w) TR V nb z = p z)
    (hB : ∀ l < nb, pg w (mask w) Bm l = p (bsK Q l))
    (hbs : ∀ t < nb, pg w (mask w) BP t = bsK Q t) :
    allN nb (fun t => Nat.beq (fwdW w (mask w) TR V nb (pg w (mask w) X (pg w (mask w) BP t)))
      (pg w (mask w) X (pg w (mask w) Bm t))) = true ↔ p * x = x * p := by
  rw [Orb.allN_iff]
  constructor
  · intro h
    have e : (x * p)⁻¹ * (p * x) = 1 := by
      apply RawSchreierDatum.eq_one_of_fixes_base Q hQ
      · exact Q.originalSubgroup.mul_mem (Q.originalSubgroup.inv_mem
          (Q.originalSubgroup.mul_mem hxQ hpQ)) (Q.originalSubgroup.mul_mem hpQ hxQ)
      · intro t
        have ht : (t : ℕ) < nb := hnb ▸ t.2
        have e1 := Nat.eq_of_beq_eq_true (h t ht)
        rw [hbs t ht, hx, hf, hB t ht, hx, bsK_of t.2] at e1
        have e2 : (p * x) (Q.base.get t) = (x * p) (Q.base.get t) := Fin.ext e1
        rw [Equiv.Perm.mul_apply, e2, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    exact (inv_mul_eq_one.1 e).symm
  · intro h t ht
    rw [hbs t ht, hx, hf, hB t ht, hx, Orb.beq_dec]
    have e := congrArg (fun σ : Equiv.Perm (Fin n) => σ (bsK Q t)) h
    simp only [Equiv.Perm.mul_apply] at e
    rw [e]
    exact decide_eq_true rfl

theorem leafOK_cons (w m nb : ℕ) (TR : ℕ → ℕ) (BP V Bm X : ℕ) (L : List ℕ) :
    leafOK w m nb TR BP V Bm (X :: L) = bAnd(allN nb fun t => Nat.beq (fwdW w m TR V nb
      (pg w m X (pg w m BP t))) (pg w m X (pg w m Bm t)), leafOK w m nb TR BP V Bm L) := rfl

theorem leaf_count {n w nb BP V Bm X Y : ℕ} {Q : RawSchreierDatum n} {TR : ℕ → ℕ}
    (hQ : ValidSchreier Q) (hnb : Q.baseCount = nb) {x y p : Equiv.Perm (Fin n)}
    (hx : Orb.PRep n w X x) (hy : Orb.PRep n w Y y) (hxQ : x ∈ Q.originalSubgroup)
    (hyQ : y ∈ Q.originalSubgroup) (hpQ : p ∈ Q.originalSubgroup)
    (hf : ∀ z : Fin n, fwdW w (mask w) TR V nb z = p z)
    (hB : ∀ l < nb, pg w (mask w) Bm l = p (bsK Q l))
    (hbs : ∀ t < nb, pg w (mask w) BP t = bsK Q t) :
    Bool.rec (motive := fun _ => ℕ) 0 1 (leafOK w (mask w) nb TR BP V Bm [X, Y]) =
      if p * x = x * p ∧ p * y = y * p then 1 else 0 := by
  have e : leafOK w (mask w) nb TR BP V Bm [X, Y] = decide (p * x = x * p ∧ p * y = y * p) := by
    rw [leafOK_cons, leafOK_cons, Orb.bAnd_eq, Orb.bAnd_eq, Bool.eq_iff_iff, Bool.and_eq_true,
      Bool.and_eq_true, leafOne hQ hnb hx hxQ hpQ hf hB hbs, leafOne hQ hnb hy hyQ hpQ hf hB hbs,
      decide_eq_true_eq]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, rfl⟩⟩
  rw [e]
  by_cases h : p * x = x * p ∧ p * y = y * p <;> simp [h]

theorem cntXY_wit {n : ℕ} {Q : RawSchreierDatum n} {x y p : Equiv.Perm (Fin n)} {j : ℕ}
    (h : cntXY Q x y p j ≠ 0) :
    ∃ h' ∈ Q.levelSubgroup j, p * h' * x = x * (p * h') ∧ p * h' * y = y * (p * h') := by
  unfold cntXY at h
  obtain ⟨⟨h', hh⟩⟩ := (Nat.card_ne_zero.1 h).1
  exact ⟨h', hh.1, hh.2⟩

theorem planOK_le {n w nb BP DP : ℕ} :
    ∀ (pl : List ℕ) (i : ℕ), planOK n w nb BP DP pl i = true → i ≤ nb
  | [], i, h => (Nat.eq_of_beq_eq_true h).le
  | E :: rest, i, h => by
    have h' : bAnd(entryOK n w (mask w) BP DP E i, planOK n w nb BP DP rest (Nat.succ i)) =
      true := h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h'
    have := planOK_le rest (i + 1) h'.2
    omega

theorem lane_child {V v j : ℕ} (hV : V < 2 ^ (16 * j)) (hv : v < 2 ^ 16) :
    Nat.lor V (Nat.shiftLeft v (Nat.mul 16 j)) < 2 ^ (16 * (j + 1)) ∧
    (∀ l < j, wAt (Nat.lor V (Nat.shiftLeft v (Nat.mul 16 j))) l = wAt V l) ∧
    wAt (Nat.lor V (Nat.shiftLeft v (Nat.mul 16 j))) j = v := by
  have e : Nat.lor V (Nat.shiftLeft v (Nat.mul 16 j)) = V + v * 2 ^ (16 * j) := fld_lor hV
  rw [e]
  refine ⟨fld_lt hV hv, fun l hl => ?_, ?_⟩
  · rw [wAt_eq', wAt_eq', fld_low hV hl]
  · rw [wAt_eq', fld_top hV hv]

theorem img_child {w Bm a j : ℕ} (hB : Bm < 2 ^ (w * j)) (ha : a < 2 ^ w) :
    Nat.lor Bm (Nat.shiftLeft a (Nat.mul w j)) < 2 ^ (w * (j + 1)) ∧
    (∀ l < j, pg w (mask w) (Nat.lor Bm (Nat.shiftLeft a (Nat.mul w j))) l =
      pg w (mask w) Bm l) ∧
    pg w (mask w) (Nat.lor Bm (Nat.shiftLeft a (Nat.mul w j))) j = a := by
  have e : Nat.lor Bm (Nat.shiftLeft a (Nat.mul w j)) = Bm + a * 2 ^ (w * j) := fld_lor hB
  rw [e]
  refine ⟨fld_lt hB ha, fun l hl => ?_, ?_⟩
  · rw [Orb.pg_eq, Orb.pg_eq, fld_low hB hl]
  · rw [Orb.pg_eq, fld_top hB ha]

theorem srch_node_count {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
    {chunks : ℕ} (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb)
    (hro : ∀ i < nb, roff n (n * w) (LR i) + rcnt (LR i) ≤ 65536)
    {X Y DP : ℕ} {x y : Equiv.Perm (Fin n)} (hx : Orb.PRep n w X x) (hy : Orb.PRep n w Y y)
    (hxQ : x ∈ Q.originalSubgroup) (hyQ : y ∈ Q.originalSubgroup)
    (hd : dOK n w X Y DP = true) :
    ∀ (pl : List ℕ) (j V Bm : ℕ) (p : Equiv.Perm (Fin n)), planOK n w nb BP DP pl j = true →
      p ∈ Q.originalSubgroup → V < 2 ^ (16 * j) →
      (∀ z : Fin n, fwdW w (mask w) TR V j z = p z) →
      (∀ z : Fin n, invW w (mask w) TRI V j z = p⁻¹ z) → Bm < 2 ^ (w * j) →
      (∀ l < j, pg w (mask w) Bm l = p (bsK Q l)) →
      srch n w nb LR TR TRI BP DP [X, Y] pl j V Bm = cntXY Q x y p j := by
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hw : n + 1 < 2 ^ w := hb.2.1
  have hbs : ∀ t < nb, pg w (mask w) BP t = bsK Q t := fun t ht => by
    rw [bsK_of (by omega), hA.base_val ⟨t, by omega⟩, hb.2.2.2.2.2.2 t ht]
  have hdP : ∀ J < 8, ∀ q : Fin n,
      dAt n w (mask w) DP J q = (x ^ ((J + 1) % 3) * y ^ ((J + 1) / 3)) q :=
    fun J hJ q => dOK_prep hn24 hw hx hy hd hJ q
  have hcd : ∀ c : Equiv.Perm (Fin n), c * x = x * c → c * y = y * c → ∀ J < 8,
      c * (x ^ ((J + 1) % 3) * y ^ ((J + 1) / 3)) = (x ^ ((J + 1) % 3) * y ^ ((J + 1) / 3)) * c :=
    fun c c1 c2 J _ => ((Commute.pow_right c1 _).mul_right (Commute.pow_right c2 _)).eq
  intro pl
  induction pl with
  | nil =>
    intro j V Bm p hpl hpQ _ hf _ _ hB
    have hj : j = nb := Nat.eq_of_beq_eq_true hpl
    subst hj
    change Bool.rec (motive := fun _ => ℕ) 0 1 (leafOK w (mask w) j TR BP V Bm [X, Y]) = _
    rw [leaf_count hQ hnb hx hy hxQ hyQ hpQ hf hB hbs, ← hnb, cntXY_term hQ]
  | cons E rest ih =>
    intro j V Bm p hpl hpQ hV hf hv hBm hB
    have hpl' : bAnd(entryOK n w (mask w) BP DP E j, planOK n w nb BP DP rest (Nat.succ j)) =
      true := hpl
    rw [Orb.bAnd_eq, Bool.and_eq_true] at hpl'
    obtain ⟨hE, hrest⟩ := hpl'
    have hjnb : j < nb := planOK_le rest (j + 1) hrest
    have hjQ : j < Q.baseCount := by omega
    obtain ⟨hc, D, Dpos⟩ := levDataK hA hF hb hp hl hnb hjnb
    have hr := hro j hjnb
    have htm : ∀ k < rcnt (LR j), levT n S base j k ∈ Q.levelSubgroup j :=
      fun k hk => hA.levT_mem hF hjQ (hc ▸ hk)
    have htb : ∀ k < rcnt (LR j),
        ((levT n S base j k (bsK Q j) : Fin n) : ℕ) = rpt w (mask w) (LR j) k := fun k hk => by
      rw [bsK_of hjQ, levT_base hA hF hjQ (hc ▸ hk), (D k hk).1]
    have hBj : ∀ (c : Equiv.Perm (Fin n)), c ∈ Q.levelSubgroup j → ∀ l < j,
        pg w (mask w) Bm l = (p * c) (bsK Q l) := fun c hcj l hlj => by
      rw [hB l hlj, Equiv.Perm.mul_apply, bsK_of (by omega),
        Q.levelSubgroup_fixes_base_index j c hcj ⟨l, by omega⟩ hlj]
    have hE' := hE
    unfold entryOK at hE'
    rw [Orb.bAnd_eq, Bool.and_eq_true] at hE'
    obtain ⟨hrels, hmode⟩ := hE'
    have hsucc := Q.levelSubgroup_succ_eq_stabilizer hQ ⟨j, hjQ⟩
    have hwit : ∀ k < rcnt (LR j), cntXY Q x y (p * levT n S base j k) (j + 1) ≠ 0 →
        ∃ c : Equiv.Perm (Fin n), c * x = x * c ∧ c * y = y * c ∧
          (∀ l < j, pg w (mask w) Bm l = c (bsK Q l)) ∧
          c (bsK Q j) = (p * levT n S base j k) (bsK Q j) := by
      intro k hk hne
      obtain ⟨h', hh', c1, c2⟩ := cntXY_wit hne
      have hh'j : h' ∈ Q.levelSubgroup j := by
        rw [hsucc] at hh'
        exact (Subgroup.mem_inf.1 hh').1
      refine ⟨p * levT n S base j k * h', c1, c2, fun l hl => ?_, ?_⟩
      · rw [mul_assoc]
        exact hBj _ ((Q.levelSubgroup j).mul_mem (htm k hk) hh'j) l hl
      · rw [Equiv.Perm.mul_apply, bsK_of hjQ,
          Q.levelSubgroup_fixes_base_index (j + 1) h' hh' ⟨j, hjQ⟩ (Nat.lt_succ_self j)]
    have hrelW : ∀ k < rcnt (LR j), cntXY Q x y (p * levT n S base j k) (j + 1) ≠ 0 →
        ∀ a : ℕ, a = (((p * levT n S base j k) (bsK Q j) : Fin n) : ℕ) →
        CentSrch.relOK n w (mask w) DP E j Bm a = true := by
      intro k hk hne a ha
      obtain ⟨c, c1, c2, hBc, hcj⟩ := hwit k hk hne
      exact relOK_of hdP (hcd c c1 c2) (fun t ht => hbs t (by omega)) hBc (by rw [ha, hcj])
        hrels
    have hchild : ∀ k < rcnt (LR j), ∀ a : ℕ, a = (((p * levT n S base j k) (bsK Q j) :
        Fin n) : ℕ) →
        child n w (mask w) (Nat.mul n w) DP E j (LR j) V Bm a k
          (srch n w nb LR TR TRI BP DP [X, Y] rest) =
          cntXY Q x y (p * levT n S base j k) (j + 1) := by
      intro k hk a ha
      have han : a < 2 ^ w := by
        rw [ha]
        have := (((p * levT n S base j k) (bsK Q j)) : Fin n).2
        omega
      obtain ⟨L1, L2, L3⟩ := lane_child (v := Nat.add (roff n (Nat.mul n w) (LR j)) k) hV
        (by change roff n (n * w) (LR j) + k < 2 ^ 16; omega)
      obtain ⟨I1, I2, I3⟩ := img_child (j := j) hBm han
      have ihk := ih (j + 1) _ _ (p * levT n S base j k) hrest
        (Q.originalSubgroup.mul_mem hpQ (levelSubgroup_le_orig hQ j (by omega) (htm k hk))) L1
        (fun z => by
          rw [fwdW_succ, L3, fwdW_congr _ _ _ j L2]
          change fwdW w (mask w) TR V j (pg w (mask w) (TR (roff n (n * w) (LR j) + k)) z) = _
          rw [(D k hk).2.2.2.1 z, hf]
          rfl)
        (fun z => by
          rw [invW_succ, L3, invW_congr _ _ _ j L2, hv]
          change pg w (mask w) (TRI (roff n (n * w) (LR j) + k)) _ = _
          rw [(D k hk).2.2.2.2, mul_inv_rev]
          rfl)
        I1
        (fun l hl => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
          · rw [I2 l hl]
            exact hBj _ (htm k hk) l hl
          · rw [I3, ha])
      unfold child
      rw [Orb.nIf_eq, Orb.bAnd_eq, Orb.blt_dec, decide_eq_true hk, Bool.true_and]
      split_ifs with hrel
      · exact ihk
      · symm
        by_contra hne
        exact hrel (hrelW k hk hne a ha)
    have hrptn : ∀ k < rcnt (LR j), rpt w (mask w) (LR j) k < n := fun k hk => (D k hk).2.1
    have hak : ∀ k (hk : k < rcnt (LR j)), (p * levT n S base j k) (bsK Q j) =
        p ⟨rpt w (mask w) (LR j) k, hrptn k hk⟩ := fun k hk => by
      rw [Equiv.Perm.mul_apply]
      congr 1
      exact Fin.ext (htb k hk)
    have hpos : ∀ q : Fin n, rpos w (mask w) (n * w) (LR j) (p⁻¹ q) < rcnt (LR j) →
        (p * levT n S base j (rpos w (mask w) (n * w) (LR j) (p⁻¹ q))) (bsK Q j) = q := by
      intro q hq
      rw [hak _ hq]
      have e := Dpos _ (p⁻¹ q).2 hq
      have e2 : (⟨rpt w (mask w) (LR j) (rpos w (mask w) (n * w) (LR j) (p⁻¹ q)),
          hrptn _ hq⟩ : Fin n) = p⁻¹ q := Fin.ext e
      rw [e2, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have hposk : ∀ k (hk : k < rcnt (LR j)),
        rpos w (mask w) (n * w) (LR j) ((p⁻¹ ((p * levT n S base j k) (bsK Q j)) : Fin n) : ℕ) =
          k := fun k hk => by
      rw [hak k hk, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
      exact (D k hk).2.2.1
    have e : srch n w nb LR TR TRI BP DP [X, Y] (E :: rest) j V Bm =
        level n w (mask w) (Nat.mul n w) TR TRI DP E j (LR j) V Bm
          (srch n w nb LR TR TRI BP DP [X, Y] rest) := by
      change strictN (LR j) (fun R => level n w (mask w) (Nat.mul n w) TR TRI DP E j R V Bm
        (srch n w nb LR TR TRI BP DP [X, Y] rest)) = _
      exact Orb.strictN_eq _ _
    rw [e, cntXY_succ hA hF hQ hb hp hl hnb x y p hjnb]
    unfold level
    generalize hm : emode E = md at hmode ⊢
    rcases md with _ | _ | _ | md
    ·
      refine (?_ : strictN (dAt n w (mask w) DP (eJ E) (pg w (mask w) Bm (eL E)))
        (fun a => tgt n w (mask w) (Nat.mul n w) TRI DP E j (LR j) V Bm a
          (srch n w nb LR TR TRI BP DP [X, Y] rest)) = _)
      change bAnd(Nat.blt (eL E) j, Nat.beq (dAt n w (mask w) DP (eJ E)
        (pg w (mask w) BP (eL E))) (pg w (mask w) BP j)) = true at hmode
      rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.blt_dec, decide_eq_true_eq] at hmode
      obtain ⟨hLj, hJe⟩ := hmode
      have hJe' := Nat.eq_of_beq_eq_true hJe
      rw [Orb.strictN_eq]
      unfold tgt
      rw [Orb.strictN_eq]
      have hJ8 : eJ E < 8 := land7_lt _
      have ha0 : dAt n w (mask w) DP (eJ E) (pg w (mask w) Bm (eL E)) =
          (((x ^ ((eJ E + 1) % 3) * y ^ ((eJ E + 1) / 3)) (p (bsK Q (eL E))) : Fin n) : ℕ) := by
        rw [hB _ hLj, hdP _ hJ8]
      rw [ha0, hv]
      have hforce : ∀ k < rcnt (LR j), cntXY Q x y (p * levT n S base j k) (j + 1) ≠ 0 →
          k = rpos w (mask w) (n * w) (LR j)
            (p⁻¹ ((x ^ ((eJ E + 1) % 3) * y ^ ((eJ E + 1) / 3)) (p (bsK Q (eL E))))) := by
        intro k hk hne
        obtain ⟨c, c1, c2, hBc, hcj⟩ := hwit k hk hne
        have h1 := forced_of hdP (hcd c c1 c2) (fun t ht => hbs t (by omega)) hBc
          (a := ((c (bsK Q j) : Fin n) : ℕ)) rfl hLj hJe'
        rw [ha0, hcj] at h1
        have hq := Fin.ext h1
        rw [hq]
        exact (hposk k hk).symm
      by_cases hk0 : rpos w (mask w) (n * w) (LR j)
          (p⁻¹ ((x ^ ((eJ E + 1) % 3) * y ^ ((eJ E + 1) / 3)) (p (bsK Q (eL E))))) < rcnt (LR j)
      · rw [Finset.sum_eq_single_of_mem _ (Finset.mem_range.2 hk0) (fun k hk hne => by
          by_contra h
          exact hne (hforce k (Finset.mem_range.1 hk) h))]
        exact hchild _ hk0 _ (by rw [hpos _ hk0])
      · rw [Finset.sum_eq_zero (fun k hk => by
          by_contra h
          have := hforce k (Finset.mem_range.1 hk) h
          exact hk0 (this ▸ Finset.mem_range.1 hk))]
        have hk0' : ¬ rpos w (mask w) (Nat.mul n w) (LR j)
            (p⁻¹ ((x ^ ((eJ E + 1) % 3) * y ^ ((eJ E + 1) / 3)) (p (bsK Q (eL E))))) <
              rcnt (LR j) := hk0
        unfold child
        rw [Orb.nIf_eq, Orb.bAnd_eq, Orb.blt_dec, decide_eq_false hk0', Bool.false_and]
        rfl
    ·
      change allN n (fun q => !(fixAll n w (mask w) DP E j q) ||
        Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 q))) = true at hmode
      have htgt : ∀ q (hq : q < n), tgt n w (mask w) (Nat.mul n w) TRI DP E j (LR j) V Bm q
          (srch n w nb LR TR TRI BP DP [X, Y] rest) =
          child n w (mask w) (Nat.mul n w) DP E j (LR j) V Bm q
            (rpos w (mask w) (n * w) (LR j) (p⁻¹ ⟨q, hq⟩))
            (srch n w nb LR TR TRI BP DP [X, Y] rest) := by
        intro q hq
        have e1 : invW w (mask w) TRI V j q = ((p⁻¹ ⟨q, hq⟩ : Fin n) : ℕ) := hv ⟨q, hq⟩
        unfold tgt
        rw [Orb.strictN_eq, e1]
        rfl
      refine (foldN_sumK (f := fun q s => Bool.rec (motive := fun _ => ℕ) s
          (Nat.add s (tgt n w (mask w) (Nat.mul n w) TRI DP E j (LR j) V Bm q
            (srch n w nb LR TR TRI BP DP [X, Y] rest)))
          (Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 q))))
        (g := fun q => Bool.rec (motive := fun _ => ℕ) 0
          (tgt n w (mask w) (Nat.mul n w) TRI DP E j (LR j) V Bm q
            (srch n w nb LR TR TRI BP DP [X, Y] rest))
          (Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 q))))
        (fun q s => by cases Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 q)) <;> rfl) n).trans ?_
      symm
      refine Finset.sum_bij_ne_zero
        (fun k _ _ => (((p * levT n S base j k) (bsK Q j) : Fin n) : ℕ)) ?_ ?_ ?_ ?_
      · intro k _ _
        exact Finset.mem_range.2 (Fin.is_lt _)
      · intro k1 hk1 _ k2 hk2 _ heq
        have hfe : (p * levT n S base j k1) (bsK Q j) = (p * levT n S base j k2) (bsK Q j) :=
          Fin.ext heq
        calc k1 = rpos w (mask w) (n * w) (LR j)
              ((p⁻¹ ((p * levT n S base j k1) (bsK Q j)) : Fin n) : ℕ) :=
              (hposk k1 (Finset.mem_range.1 hk1)).symm
          _ = rpos w (mask w) (n * w) (LR j)
              ((p⁻¹ ((p * levT n S base j k2) (bsK Q j)) : Fin n) : ℕ) := by rw [hfe]
          _ = k2 := hposk k2 (Finset.mem_range.1 hk2)
      · intro q hq hne
        have hqn := Finset.mem_range.1 hq
        beta_reduce at hne
        cases hbit : Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1 q))
        · rw [hbit] at hne
          exact absurd rfl hne
        · rw [hbit, htgt q hqn] at hne
          by_cases hk : rpos w (mask w) (n * w) (LR j) (p⁻¹ ⟨q, hqn⟩) < rcnt (LR j)
          · refine ⟨_, Finset.mem_range.2 hk, ?_, by rw [hpos ⟨q, hqn⟩ hk]⟩
            rw [← hchild _ hk q (by rw [hpos ⟨q, hqn⟩ hk])]
            exact hne
          · exfalso
            apply hne
            unfold child
            rw [Orb.nIf_eq, Orb.bAnd_eq, Orb.blt_dec, decide_eq_false hk, Bool.false_and]
            rfl
      · intro k hk hne
        have hk' := Finset.mem_range.1 hk
        obtain ⟨c, c1, c2, hBc, hcj⟩ := hwit k hk' hne
        have hfix := fixAll_of hdP (hcd c c1 c2) (fun t ht => hbs t (by omega)) hBc
          (a := ((c (bsK Q j) : Fin n) : ℕ)) rfl hrels
        rw [hcj] at hfix
        have hm : (!(fixAll n w (mask w) DP E j (((p * levT n S base j k) (bsK Q j) : Fin n) : ℕ))
            || Nat.blt 0 (Nat.land (eM E) (Nat.shiftLeft 1
              (((p * levT n S base j k) (bsK Q j) : Fin n) : ℕ)))) = true :=
          Orb.allN_iff.1 hmode _ (Fin.is_lt _)
        rw [hfix, Bool.not_true, Bool.false_or] at hm
        beta_reduce
        rw [hm]
        change _ = tgt n w (mask w) (Nat.mul n w) TRI DP E j (LR j) V Bm _
          (srch n w nb LR TR TRI BP DP [X, Y] rest)
        rw [htgt _ (Fin.is_lt _), Fin.eta, hposk k hk']
        exact (hchild k hk' _ rfl).symm
    ·
      refine (?_ : foldN (rcnt (LR j)) (fun k s => s + strictN (fwdW w (mask w) TR V j
        (rpt w (mask w) (LR j) k)) (fun a => child n w (mask w) (Nat.mul n w) DP E j (LR j) V Bm
          a k (srch n w nb LR TR TRI BP DP [X, Y] rest))) 0 = _)
      rw [foldN_sumK (g := fun k => strictN (fwdW w (mask w) TR V j
        (rpt w (mask w) (LR j) k)) (fun a => child n w (mask w) (Nat.mul n w) DP E j (LR j) V Bm
          a k (srch n w nb LR TR TRI BP DP [X, Y] rest))) (fun q s => rfl)]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [Orb.strictN_eq]
      apply hchild k hk'
      rw [hak k hk']
      exact hf ⟨_, hrptn k hk'⟩
    · exact absurd hmode (by simp)

theorem srch_node_sound {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {Q : RawSchreierDatum n}
    {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ}
    (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : Q.baseCount = nb)
    (hro : ∀ i < nb, roff n (n * w) (LR i) + rcnt (LR i) ≤ 65536)
    {X Y DP : ℕ} {x y : Equiv.Perm (Fin n)} (hx : Orb.PRep n w X x) (hy : Orb.PRep n w Y y)
    (hxQ : x ∈ Q.originalSubgroup) (hyQ : y ∈ Q.originalSubgroup)
    {i : ℕ} (hi : i ≤ nb) (hid : idPrefixOK n w LR TR BP i = true)
    {pl : List ℕ} (hpl : planOK n w nb BP DP pl i = true) (hd : dOK n w X Y DP = true) :
    Nat.card ↥(Q.levelSubgroup i ⊓ Subgroup.centralizer ({x, y} : Set (Equiv.Perm (Fin n)))) =
      srch n w nb LR TR TRI BP DP [X, Y] pl i (idWord n w LR BP i) (idImgs w BP i) := by
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hw : n + 1 < 2 ^ w := hb.2.1
  have hbs : ∀ t < nb, pg w (mask w) BP t = bsK Q t := fun t ht => by
    rw [bsK_of (by omega), hA.base_val ⟨t, by omega⟩, hb.2.2.2.2.2.2 t ht]
  have hidl : ∀ l < i, rpos w (mask w) (n * w) (LR l) (pg w (mask w) BP l) < rcnt (LR l) ∧
      TR (roff n (n * w) (LR l) + rpos w (mask w) (n * w) (LR l) (pg w (mask w) BP l)) =
        pidn n w := by
    intro l hli
    have h := Orb.allN_iff.1 hid l hli
    rw [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Orb.blt_dec, decide_eq_true_eq] at h
    exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩
  have hpre : ∀ i' ≤ i, idWord n w LR BP i' < 2 ^ (16 * i') ∧
      (∀ l < i', wAt (idWord n w LR BP i') l =
        roff n (n * w) (LR l) + rpos w (mask w) (n * w) (LR l) (pg w (mask w) BP l)) ∧
      idImgs w BP i' < 2 ^ (w * i') ∧
      ∀ l < i', pg w (mask w) (idImgs w BP i') l = pg w (mask w) BP l := by
    intro i'
    induction i' with
    | zero => intro _; exact ⟨by simp [idWord], fun l hl => absurd hl (Nat.not_lt_zero l),
        by simp [idImgs], fun l hl => absurd hl (Nat.not_lt_zero l)⟩
    | succ i' ih =>
      intro hi'
      obtain ⟨W1, W2, B1, B2⟩ := ih (by omega)
      obtain ⟨hk, -⟩ := hidl i' (by omega)
      have hr := hro i' (by omega)
      obtain ⟨L1, L2, L3⟩ := lane_child (v := Nat.add (roff n (Nat.mul n w) (LR i'))
        (rpos w (mask w) (Nat.mul n w) (LR i') (pg w (mask w) BP i'))) W1
        (by
          change roff n (n * w) (LR i') +
            rpos w (mask w) (n * w) (LR i') (pg w (mask w) BP i') < 2 ^ 16
          omega)
      have hbn : pg w (mask w) BP i' < 2 ^ w := by
        rw [hbs i' (by omega)]
        have := (bsK Q i').2
        omega
      obtain ⟨I1, I2, I3⟩ := img_child (j := i') B1 hbn
      refine ⟨L1, fun l hl => ?_, I1, fun l hl => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
        · exact (L2 l hl).trans (W2 l hl)
        · exact L3
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
        · exact (I2 l hl).trans (B2 l hl)
        · exact I3
  obtain ⟨W1, W2, B1, B2⟩ := hpre i le_rfl
  have hone : ∀ l < i, Orb.PRep n w (TR (wAt (idWord n w LR BP i) l)) 1 ∧
      Orb.PRep n w (TRI (wAt (idWord n w LR BP i) l)) 1 := by
    intro l hli
    obtain ⟨hk, hT⟩ := hidl l hli
    obtain ⟨-, D, -⟩ := levDataK hA hF hb hp hl hnb (i := l) (by omega)
    obtain ⟨-, -, -, d4, d5⟩ := D _ hk
    rw [hT] at d4
    have e := Orb.prep_unique d4 (Orb.prep_pidn hn24 hw)
    rw [e, inv_one] at d5
    rw [W2 l hli, hT]
    exact ⟨Orb.prep_pidn hn24 hw, d5⟩
  have hfw : ∀ j ≤ i, ∀ z : Fin n, fwdW w (mask w) TR (idWord n w LR BP i) j z = z := by
    intro j
    induction j with
    | zero => intro _ z; rfl
    | succ j ih =>
      intro hj z
      rw [fwdW_succ, (hone j (by omega)).1 z, Equiv.Perm.one_apply]
      exact ih (by omega) z
  have hiv : ∀ j ≤ i, ∀ z : Fin n, invW w (mask w) TRI (idWord n w LR BP i) j z = z := by
    intro j
    induction j with
    | zero => intro _ z; rfl
    | succ j ih =>
      intro hj z
      rw [invW_succ, ih (by omega) z, (hone j (by omega)).2 z, Equiv.Perm.one_apply]
  rw [srch_node_count hA hF hQ hb hp hl hnb hro hx hy hxQ hyQ hd pl i _ _ 1 hpl
    (Q.originalSubgroup.one_mem) W1 (fun z => hfw i le_rfl z)
    (fun z => by rw [inv_one, Equiv.Perm.one_apply]; exact hiv i le_rfl z) B1
    (fun l hl => by rw [B2 l hl, hbs l (by omega), Equiv.Perm.one_apply])]
  unfold cntXY
  refine Nat.card_congr (Equiv.subtypeEquivRight fun h => ?_)
  simp only [one_mul, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, b.symm, c.symm⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, b.symm, c.symm⟩

end CFSG.KC.CentHead

end
