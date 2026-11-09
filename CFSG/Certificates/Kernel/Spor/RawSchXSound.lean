module

public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import Certificates.Data.Kernel.Spor.RawX
public import CFSG.Certificates.Kernel.Spor.RawBaseEq
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.Raw

theorem siftKX_zero (n w m nw : Nat) (LR TRI : Nat → Nat) (BP : Nat) (X : Nat → Nat) (nX l : Nat)
    (G : Nat → Nat) :
    siftKX n w m nw LR TRI BP X nX 0 l G =
      allN nX (fun t => strictB (X t) (fun x => Nat.beq (G x) x)) := rfl

theorem siftKX_succ (n w m nw : Nat) (LR TRI : Nat → Nat) (BP : Nat) (X : Nat → Nat)
    (nX d l : Nat) (G : Nat → Nat) :
    siftKX n w m nw LR TRI BP X nX (d + 1) l G =
      strictB (LR l) (fun R => strictB (rpos w m nw R (G (pg w m BP l))) (fun k =>
        bIf(Nat.blt k (rcnt R), strictB (TRI (Nat.add (roff n nw R) k))
          (fun t => siftKX n w m nw LR TRI BP X nX d (Nat.succ l) (fun x => pg w m t (G x))),
          false))) := rfl

section

variable {n w nw idn nb nX BP : Nat} {LR TRI : Nat → Nat} {X : Nat → Nat} (Q : Nat → Prop)
  (hsz : n < 2 ^ 32) (hBP : ∀ l < nb, pg w (mask w) BP l < n) (hX : ∀ t < nX, X t < n)
  (hQ : ∀ l < nb, ∀ k < rcnt (LR l), ∀ g, Q g →
    Q (pcomp n w (mask w) (TRI (roff n nw (LR l) + k)) g))
  (hend : ∀ g, Q g → (∀ t < nX, pg w (mask w) g (X t) = X t) →
    bAnd(szOK n w, Nat.beq g idn) = true)
include hsz hBP hX hQ hend

theorem siftK_of_siftKX : ∀ f l, l + f ≤ nb → ∀ g (G : Nat → Nat), Q g →
    (∀ x < n, G x = pg w (mask w) g x) →
    siftKX n w (mask w) nw LR TRI BP X nX f l G = true →
      siftK n w (mask w) nw idn LR TRI BP f l g = true := by
  intro f
  induction f with
  | zero =>
    intro l _ g G hg hG h
    rw [siftK_zero]
    refine hend g hg fun t ht => ?_
    have h1 := allN_spec h t ht
    simp only [strictB_eq] at h1
    rw [← hG _ (hX t ht)]
    exact Nat.eq_of_beq_eq_true h1
  | succ f ih =>
    intro l hl g G hg hG h
    rw [siftKX_succ] at h
    rw [siftK_succ]
    simp only [strictB_eq] at h ⊢
    rw [← hG _ (hBP l (by omega))]
    cases hb : Nat.blt (rpos w (mask w) nw (LR l) (G (pg w (mask w) BP l))) (rcnt (LR l)) with
    | false =>
      rw [hb] at h
      exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      refine ih (Nat.succ l) (by omega) _ _ (hQ l (by omega) _ (Nat.blt_eq.mp hb) g hg)
        (fun x hx => ?_) h
      rw [PF.pg_pcomp hsz hx, hG x hx]

theorem schK_of_schKX {S SI TR : Nat → Nat} {kS i T h₀ cnt : Nat} (hi : i < nb)
    (hQ0 : ∀ h < rcnt (LR i), ∀ j < stCnt T, ∀ k < rcnt (LR i),
      Q (pcomp n w (mask w) (TRI (roff n nw (LR i) + k))
        (pcomp n w (mask w) (letterK S SI kS (stAt T j)) (TR (roff n nw (LR i) + h)))))
    (hs : schKX n w (mask w) nw S SI LR TR TRI kS BP nb i T h₀ cnt X nX = true) :
    schK n w (mask w) nw idn S SI LR TR TRI kS BP nb i T h₀ cnt = true := by
  unfold schKX at hs
  unfold schK
  simp only [strictB_eq] at hs ⊢
  refine PackFld.allN_of_forall fun dh hdh => ?_
  have h1 := allN_spec hs dh hdh
  cases hb : Nat.blt (Nat.add h₀ dh) (rcnt (LR i)) with
  | false => rfl
  | true =>
    rw [hb] at h1
    refine PackFld.allN_of_forall fun j hj => ?_
    have h2 := allN_spec h1 j hj
    obtain ⟨hk, h3⟩ := (bAnd_iff _ _).1 h2
    refine (bAnd_iff _ _).2 ⟨hk, ?_⟩
    have hf : Nat.succ i + Nat.sub nb (Nat.succ i) ≤ nb := by
      change i + 1 + (nb - (i + 1)) ≤ nb
      omega
    refine siftK_of_siftKX Q hsz hBP hX hQ hend _ _ hf _ _
      (hQ0 _ (Nat.blt_eq.mp hb) j hj _ (Nat.blt_eq.mp hk)) (fun x hx => ?_) h3
    rw [PF.pg_pcomp hsz hx, PF.pg_pcomp hsz hx]

end

@[expose] def DPart (nD w P : Nat) (G : Subgroup (Equiv.Perm (Fin nD))) : Prop :=
  ∃ δ ∈ G, ∀ x : Fin nD, pg w (mask w) P x = δ x

section DPart

variable {n nD w : Nat} {G : Subgroup (Equiv.Perm (Fin nD))}

theorem dp_pcomp {a b : Nat} (hn : n < 2 ^ 32) (hnD : nD ≤ n) (ha : DPart nD w a G)
    (hb : DPart nD w b G) : DPart nD w (pcomp n w (mask w) a b) G := by
  obtain ⟨δa, hδa, ea⟩ := ha
  obtain ⟨δb, hδb, eb⟩ := hb
  refine ⟨δa * δb, G.mul_mem hδa hδb, fun x => ?_⟩
  rw [PF.pg_pcomp hn (Nat.lt_of_lt_of_le x.2 hnD), eb x, ea (δb x), Equiv.Perm.mul_apply]

theorem dp_pidn (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hnD : nD ≤ n) :
    DPart nD w (pidn n w) G :=
  ⟨1, G.one_mem, fun x => by rw [PF.pg_pidn hn hw (Nat.lt_of_lt_of_le x.2 hnD)]; rfl⟩

theorem dp_inv {P Q : Nat} (hnD : nD ≤ n) (h : permOK n w (mask w) (n * w) P Q = true)
    (hP : DPart nD w P G) : DPart nD w Q G := by
  obtain ⟨δ, hδ, e⟩ := hP
  refine ⟨δ⁻¹, G.inv_mem hδ, fun x => ?_⟩
  have e1 := ((permOK_facts h).2.2 (δ⁻¹ x) (Nat.lt_of_lt_of_le (δ⁻¹ x).2 hnD)).2
  have hx : δ (δ⁻¹ x) = x := by simp
  rw [e (δ⁻¹ x), hx] at e1
  exact e1

theorem dp_eq2 {r p q : Nat} (hn : n < 2 ^ 32) (hnD : nD ≤ n)
    (h : eq2 n w (mask w) r p q = true) (hp : DPart nD w p G) (hq : DPart nD w q G) :
    DPart nD w r G := by
  obtain ⟨δ, hδ, e2⟩ := dp_pcomp (b := q) hn hnD hp hq
  refine ⟨δ, hδ, fun x => ?_⟩
  unfold eq2 at h
  have h1 := Nat.eq_of_beq_eq_true (allN_spec h x (Nat.lt_of_lt_of_le x.2 hnD))
  rw [h1, ← PF.pg_pcomp hn (Nat.lt_of_lt_of_le x.2 hnD), e2 x]

theorem dp_tr {pm kS root T R : Nat} {S SI TR TRI : Nat → Nat} (hnD : nD ≤ n)
    (hlv : levelK n w (mask w) (n * w) pm (pidn n w) S SI TR TRI kS root T R = true)
    (hL : ∀ j < stCnt T, DPart nD w (letterK S SI kS (stAt T j)) G) :
    ∀ k < rcnt R, DPart nD w (TR (roff n (n * w) R + k)) G ∧
      DPart nD w (TRI (roff n (n * w) R + k)) G := by
  obtain ⟨hsz, -, hR, h0, hE, hP⟩ := levelK_facts hlv
  obtain ⟨hn, hw⟩ := szOK_facts hsz
  have hn32 : n < 2 ^ 32 := Nat.lt_trans hn (by decide)
  have key : ∀ k < rcnt R, DPart nD w (TR (roff n (n * w) R + k)) G := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases k0 : k = 0
      · subst k0
        rw [Nat.add_zero, h0]
        exact dp_pidn hn hw hnD
      · have hk0 : 0 < k := Nat.pos_of_ne_zero k0
        have hpa := hR.par_lt k hk hk0
        exact dp_eq2 hn32 hnD (hE k hk hk0) (hL _ (hR.lab_lt k hk hk0))
          (ih _ hpa (Nat.lt_trans hpa hk))
  exact fun k hk => ⟨key k hk, dp_inv hnD (hP k hk) (key k hk)⟩

theorem stAt_lt_steps {kS M : Nat} (hk : kS < 128) :
    ∀ j < stCnt (stepTab kS M), stAt (stepTab kS M) j < kS + kS := by
  intro j hj
  have hk2 : kS + kS < 256 := by omega
  rw [stCnt_eq hk2] at hj
  rw [stAt_eq hk2 hj]
  have hm := List.getElem_mem hj
  rw [List.mem_filter, List.mem_range] at hm
  exact hm.1

theorem xPtsK_lt {BP nb t : Nat} (hbD : ∀ t < nb, pg w (mask w) BP t < nD) (hnD : nD ≤ n)
    (hnb : nb ≤ nD) (ht : t < nb + (n - nD)) : xPtsK w (mask w) BP nb nD t < n := by
  unfold xPtsK
  rw [nIf_eq, blt_dec]
  by_cases h : t < nb
  · simp only [h, decide_true, ↓reduceIte]
    exact Nat.lt_of_lt_of_le (hbD t h) hnD
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    change nD - nb + t < n
    omega

theorem idn_of_xPtsK {BP nb g : Nat} (hsz : szOK n w = true) (hnD : nD ≤ n) (hnb : nb ≤ nD)
    (hD : ∀ γ ∈ G, (∀ t < nb, ∀ h : pg w (mask w) BP t < nD, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
    (hg : g >>> (n * w) = 0 ∧ DPart nD w g G)
    (hfix : ∀ t < nb + (n - nD), pg w (mask w) g (xPtsK w (mask w) BP nb nD t) =
      xPtsK w (mask w) BP nb nD t) :
    bAnd(szOK n w, Nat.beq g (pidn n w)) = true := by
  obtain ⟨hn, hw⟩ := szOK_facts hsz
  obtain ⟨hg0, δ, hδ, e⟩ := hg
  have h1 : δ = 1 := hD δ hδ fun t ht hb => by
    apply Fin.ext
    rw [← e ⟨_, hb⟩]
    have hx : xPtsK w (mask w) BP nb nD t = pg w (mask w) BP t := by
      unfold xPtsK
      rw [nIf_eq, blt_dec]
      simp only [ht, decide_true, ↓reduceIte]
    have h2 := hfix t (by omega)
    rw [hx] at h2
    exact h2
  have eg : g = pidn n w := PF.eq_of_fields (PF.w_pos hw) hg0 (PF.pidn_shr hn hw) fun i hi => by
    rw [PF.pg_pidn hn hw hi]
    by_cases hiD : i < nD
    · rw [e ⟨i, hiD⟩, h1]
      rfl
    · have hnot : ¬ (nb + (i - nD) < nb) := by omega
      have hx : xPtsK w (mask w) BP nb nD (nb + (i - nD)) = i := by
        unfold xPtsK
        rw [nIf_eq, blt_dec]
        simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte]
        change nD - nb + (nb + (i - nD)) = i
        omega
      have h2 := hfix (nb + (i - nD)) (by omega)
      rw [hx] at h2
      exact h2
  rw [hsz, eg]
  exact Nat.beq_refl _

theorem dp_letter_of_agree {kS kO nbD BPD : Nat} {PS PSI QS QSI : Nat → Nat}
    {D : List (List Int)} {SD : Array (Array Nat)} {baseD : Array Nat}
    (hb : Binds nD w QS kS nbD BPD SD baseD)
    (hh : headK nD w (mask w) (nD * w) (pidn nD w) QS QSI kS kO D nbD BPD = true)
    (ha : agreeDK nD w (mask w) PS PSI QS QSI kS = true) :
    ∀ l < kS + kS, DPart nD w (letterK PS PSI kS l) (Gen nD SD kO) := by
  have hp := (head_facts hh).1
  obtain ⟨hk, hH⟩ := rawHeadOK_of hb hh
  have hd := hd_of_head hk hH
  have hsz : SD.size = kS := hb.2.2.2.1
  have hag : ∀ j < kS, ∀ x : Fin nD, pg w (mask w) (PS j) x = pg w (mask w) (QS j) x ∧
      pg w (mask w) (PSI j) x = pg w (mask w) (QSI j) x := fun j hj x => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec ha j hj) x x.2)
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  intro l hl
  unfold letterK
  rw [nIf_eq, blt_dec]
  by_cases h : l < kS
  · simp only [h, decide_true, ↓reduceIte]
    obtain ⟨h1, -⟩ := prep_PS hb hp h
    exact ⟨_, S_mem_Gen hd l (by rw [hsz]; exact h), fun x => by rw [(hag l h x).1, h1 x]⟩
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    have h' : l - kS < kS := by omega
    obtain ⟨-, h2⟩ := prep_PS hb hp h'
    exact ⟨_, (Gen nD SD kO).inv_mem (S_mem_Gen hd (l - kS) (by rw [hsz]; exact h')),
      fun x => by rw [Nat.sub_eq, (hag _ h' x).2, h2 x]⟩

theorem schK_of_schKX_D {kS nb BP i T h₀ cnt : Nat} {PS PSI LR TR TRI : Nat → Nat}
    (hnD : nD ≤ n) (hnb : nb ≤ nD) (hi : i < nb)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hD : ∀ γ ∈ G, (∀ t < nb, ∀ h : pg w (mask w) BP t < nD, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1)
    (hbD : ∀ t < nb, pg w (mask w) BP t < nD)
    (hL : ∀ l < kS + kS, DPart nD w (letterK PS PSI kS l) G)
    (hT : ∀ j < stCnt T, stAt T j < kS + kS)
    (hs : schKX n w (mask w) (n * w) PS PSI LR TR TRI kS BP nb i T h₀ cnt
      (xPtsK w (mask w) BP nb nD) (nb + (n - nD)) = true) :
    schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i T h₀ cnt = true := by
  obtain ⟨hsz, -⟩ := levelK_facts (hl i hi)
  obtain ⟨hn, hw⟩ := szOK_facts hsz
  have hn32 : n < 2 ^ 32 := Nat.lt_trans hn (by decide)
  have hw0 : 0 < w := PF.w_pos hw
  have hLv : ∀ l < nb, ∀ k < rcnt (LR l), DPart nD w (TR (roff n (n * w) (LR l) + k)) G ∧
      DPart nD w (TRI (roff n (n * w) (LR l) + k)) G := fun l hl' =>
    dp_tr hnD (hl l hl') fun j hj =>
      hL _ (stAt_lt_steps (levelK_facts (hl l hl')).2.1 j hj)
  refine schK_of_schKX (fun g => g >>> (n * w) = 0 ∧ DPart nD w g G) hn32
    (fun l hl' => Nat.lt_of_lt_of_le (hbD l hl') hnD) (fun t ht => xPtsK_lt hbD hnD hnb ht)
    (fun l hl' k hk g hg => ⟨PF.pcomp_shr _ _ hn32 hw0, dp_pcomp hn32 hnD (hLv l hl' k hk).2 hg.2⟩)
    (fun g hg hfix => idn_of_xPtsK hsz hnD hnb hD hg hfix) hi
    (fun h hh j hj k hk => ⟨PF.pcomp_shr _ _ hn32 hw0, dp_pcomp hn32 hnD (hLv i hi k hk).2
      (dp_pcomp hn32 hnD (hL _ (hT j hj)) (hLv i hi h hh).1)⟩) hs

end DPart

@[expose] def FaithK (n nD w : Nat) (PS PSI : Nat → Nat) (kS nb BP : Nat) : Prop :=
  nD ≤ n ∧ nb ≤ nD ∧ ∃ G : Subgroup (Equiv.Perm (Fin nD)),
    (∀ γ ∈ G, (∀ t < nb, ∀ h : pg w (mask w) BP t < nD, γ ⟨_, h⟩ = ⟨_, h⟩) → γ = 1) ∧
    (∀ t < nb, pg w (mask w) BP t < nD) ∧ ∀ l < kS + kS, DPart nD w (letterK PS PSI kS l) G

theorem faithK_of_chain {n nD w kS kO nb BP NS CH : Nat} {PS PSI QS QSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {SD : Array (Array Nat)} {base : Array Nat}
    (hb : Binds nD w QS kS nb BP SD base)
    (hh : headK nD w (mask w) (nD * w) (pidn nD w) QS QSI kS kO D nb BP = true)
    (hl : LevelsOK nD w QS QSI LR TR TRI kS nb BP) (hNS : nD ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK nD w (mask w) (nD * w) (pidn nD w) QS QSI LR TR TRI kS BP nb i
      (stepsAt nD w QS kS BP i) (s * CH) CH = true)
    (ha : agreeDK nD w (mask w) PS PSI QS QSI kS = true) (hnD : nD ≤ n) (hnb : nb ≤ nD) :
    FaithK n nD w PS PSI kS nb BP := by
  obtain ⟨h1, -, h3⟩ := BaseEq.groupN hb hh hl hNS hs
  exact ⟨hnD, hnb, _, h1, h3, dp_letter_of_agree hb hh ha⟩

theorem binds_ofFn {n w kS nb BP : Nat} {PS : Nat → Nat} (h0 : 0 < n) (hw : n + 1 < 2 ^ w)
    (hn : n < 65536) :
    Binds n w PS kS nb BP (Array.ofFn (n := kS) fun j => unpack n w (PS j))
      (Array.ofFn (n := nb) fun t => pg w (mask w) BP t) :=
  ⟨h0, hw, hn, Array.size_ofFn, fun j hj => by
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn], Array.size_ofFn,
    fun t ht => by rw [getElem!_pos _ t (by simpa using ht), Array.getElem_ofFn]⟩

theorem schK_of_schKX_F {n nD w kS nb BP i T h₀ cnt : Nat} {PS PSI LR TR TRI : Nat → Nat}
    (hF : FaithK n nD w PS PSI kS nb BP) (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hi : i < nb) (hT : ∀ j < stCnt T, stAt T j < kS + kS)
    (hs : schKX n w (mask w) (n * w) PS PSI LR TR TRI kS BP nb i T h₀ cnt
      (xPtsK w (mask w) BP nb nD) (nb + (n - nD)) = true) :
    schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i T h₀ cnt = true := by
  obtain ⟨hnD, hnb, G, hD, hbD, hL⟩ := hF
  exact schK_of_schKX_D hnD hnb hi hl hD hbD hL hT hs

theorem schK_of_schKX_steps {n nD w kS nb BP i h₀ cnt : Nat} {PS PSI LR TR TRI : Nat → Nat}
    (hF : FaithK n nD w PS PSI kS nb BP) (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hi : i < nb)
    (hs : schKX n w (mask w) (n * w) PS PSI LR TR TRI kS BP nb i (stepsAt n w PS kS BP i) h₀ cnt
      (xPtsK w (mask w) BP nb nD) (nb + (n - nD)) = true) :
    schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i (stepsAt n w PS kS BP i)
      h₀ cnt = true :=
  schK_of_schKX_F hF hl hi (stAt_lt_steps (levelK_facts (hl i hi)).2.1) hs

theorem schK_of_schKX_tsb {n nD w kS nb BP i T h₀ cnt : Nat} {PS PSI LR TR TRI : Nat → Nat}
    (hF : FaithK n nD w PS PSI kS nb BP) (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hi : i < nb) (hT : allN (stCnt T) (fun a => Nat.blt (stAt T a) kS) = true)
    (hs : schKX n w (mask w) (n * w) PS PSI LR TR TRI kS BP nb i T h₀ cnt
      (xPtsK w (mask w) BP nb nD) (nb + (n - nD)) = true) :
    schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i T h₀ cnt = true :=
  schK_of_schKX_F hF hl hi (fun j hj => Nat.lt_of_lt_of_le (Nat.blt_eq.mp (allN_spec hT j hj))
    (Nat.le_add_right _ _)) hs

end CFSG.KS.Raw.Orb

end
