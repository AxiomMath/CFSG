module

public import Certificates.Data.Kernel.Spor.CentBound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import CFSG.Certificates.Kernel.Spor.CentBoundPowSound

public section

namespace CFSG.KS.CentBound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

theorem ubProdK_sound {n w kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG : G = Raw.Orb.Gen n S kO)
    {r : Nat} {ρ : Equiv.Perm (Fin n)} (hr : Raw.Orb.PRep n w r ρ) {O : Nat → Nat}
    (h : ubOkK n w (mask w) PS PSI kS BP nb r O = true) :
    Nat.card ↥(G ⊓ Subgroup.centralizer ({ρ} : Set (Equiv.Perm (Fin n)))) ≤
      ubProdK n w (mask w) (n * w) LR TRI nb r O := by
  have h1 : ∀ g : Nat → Bool, allN 1 g = g 0 := fun g => by
    cases e : g 0
    · rw [Bool.eq_false_iff]
      intro ha
      have e' := Orb.allN_iff.1 ha 0 (by omega)
      rw [e] at e'
      exact absurd e' (by decide)
    · exact Orb.allN_iff.2 fun i hi => by
        obtain rfl : i = 0 := by omega
        exact e
  have h' : ubPowOkK n w (mask w) PS PSI kS BP nb 1 (fun _ => r) (fun _ => O) = true := by
    unfold ubPowOkK
    exact Orb.allN_iff.2 fun _ _ => h
  have e := ubPowK_sound (ρ := fun _ => ρ) hb hh hl hNS hs hG (fun _ _ => hr) h'
  have hset : (fun _ : Nat => ρ) '' {l | l < 1} = {ρ} :=
    Set.Nonempty.image_const ⟨0, Nat.zero_lt_one⟩ ρ
  rw [hset] at e
  refine e.trans (le_of_eq ?_)
  unfold ubPowProdK ubProdK ubCntLK ubCntK
  simp only [h1]

theorem cbS_mono (n : Nat) (p : Nat → Nat) : ∀ (l : List Nat) (M b : Nat), M.testBit b = true →
    (l.foldl (fun M k => if M.testBit (p k) = true then M ||| 2 ^ n else M ||| 2 ^ (p k)) M).testBit b
      = true
  | [], _, _, h => h
  | k :: l, M, b, h => by
    rw [List.foldl_cons]
    refine cbS_mono n p l _ b ?_
    split_ifs <;> rw [Nat.testBit_or, h, Bool.true_or]

theorem cbS_distinct (n : Nat) (p : Nat → Nat) : ∀ (l : List Nat) (M : Nat),
    (l.foldl (fun M k => if M.testBit (p k) = true then M ||| 2 ^ n else M ||| 2 ^ (p k)) M).testBit n
      = false → (l.map p).Nodup ∧ ∀ k ∈ l, M.testBit (p k) = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | k :: l, M, h => by
    rw [List.foldl_cons] at h
    have hk : M.testBit (p k) = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rw [if_pos hc] at h
      have e := cbS_mono n p l (M ||| 2 ^ n) n (by rw [Nat.testBit_or, Nat.testBit_two_pow_self,
        Bool.or_true])
      rw [e] at h
      exact absurd h (by decide)
    rw [if_neg (by rw [hk]; decide)] at h
    obtain ⟨hnd, hl⟩ := cbS_distinct n p l _ h
    have key : ∀ k' ∈ l, p k' ≠ p k ∧ M.testBit (p k') = false := by
      intro k' hk'
      have e := hl k' hk'
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.testBit_two_pow] at e
      refine ⟨fun e' => ?_, e.1⟩
      rw [e'] at e
      simp at e
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, fun k' hk' => ?_⟩
    · obtain ⟨k', hk', e⟩ := List.mem_map.1 hm
      exact (key k' hk').1 e
    · rcases List.mem_cons.1 hk' with e | hk'
      · rw [e]
        exact hk
      · exact (key k' hk').2

theorem cbS_level {n w nh nl : Nat} {H L : Nat → Nat} {h : Nat → Equiv.Perm (Fin n)}
    (hH : ∀ l < nh, Raw.Orb.PRep n w (H l) (h l)) {t : Nat}
    (hl : tlevelK n w (mask w) H L nh nl t = true) :
    tst w (mask w) (L t) ≤ tstAt w (mask w) nh nl L (t + 1) ∧
      tcnt w (mask w) (L t) *
          Nat.card ↥(Subgroup.closure (h '' {l | tstAt w (mask w) nh nl L (t + 1) ≤ l ∧ l < nh})) ≤
        Nat.card ↥(Subgroup.closure (h '' {l | tst w (mask w) (L t) ≤ l ∧ l < nh})) := by
  unfold tlevelK at hl
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    Orb.allN_iff] at hl
  obtain ⟨hc0, hss, -, hpts, hmask, hfix⟩ := hl
  set c := tcnt w (mask w) (L t) with hc
  set s := tst w (mask w) (L t) with hs
  set s' := tstAt w (mask w) nh nl L (t + 1) with hs'
  have hx : ∀ k < c, tpt w (mask w) (L t) k < n ∧ (0 < k → tpar w (mask w) (L t) k < k ∧
      s ≤ tlab w (mask w) (L t) k ∧ tlab w (mask w) (L t) k < nh ∧
      pg w (mask w) (H (tlab w (mask w) (L t) k)) (tpt w (mask w) (L t) (tpar w (mask w) (L t) k)) =
        tpt w (mask w) (L t) k) := by
    intro k hk
    have e := hpts k hk
    unfold tptK at e
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨e1, fun hk0 => ?_⟩
    have hb : Nat.beq k 0 = false := by
      cases k with
      | zero => omega
      | succ k => rfl
    rw [hb] at e2
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at e2
    obtain ⟨a1, a2, a3, a4⟩ := e2
    exact ⟨a1, a2, a3, Nat.eq_of_beq_eq_true a4⟩
  set x0 : Fin n := ⟨tpt w (mask w) (L t) 0, (hx 0 hc0).1⟩ with hx0
  have horb : ∀ k < c, ∃ g ∈ Subgroup.closure (h '' {l | s ≤ l ∧ l < nh}),
      (g x0 : Nat) = tpt w (mask w) (L t) k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨1, Subgroup.one_mem _, rfl⟩
      · obtain ⟨hp, hsl, hln, he⟩ := (hx k hk).2 hk0
        obtain ⟨g, hg, hgx⟩ := ih _ hp (by omega)
        refine ⟨h (tlab w (mask w) (L t) k) * g,
          Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, ⟨hsl, hln⟩, rfl⟩) hg, ?_⟩
        rw [Equiv.Perm.mul_apply, ← hH _ hln (g x0), hgx, he]
  have hT : tmaskK n w (mask w) (L t) = (List.range c).foldl (fun M k =>
      if M.testBit (tpt w (mask w) (L t) k) = true then M ||| 2 ^ n
      else M ||| 2 ^ (tpt w (mask w) (L t) k)) 0 := by
    unfold tmaskK
    rw [Orb.foldUp_eq]
    refine congrArg (fun f => List.foldl f 0 (List.range c)) (funext fun M => funext fun k => ?_)
    beta_reduce
    rw [Orb.strictN_eq, Orb.nIf_eq, Orb.hasBit_eq]
    change (if M.testBit _ = true then M ||| 1 <<< n else M ||| 1 <<< _) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  have hm : (tmaskK n w (mask w) (L t)).testBit n = false := by
    rw [← Orb.hasBit_eq]
    cases hb : hasBit (tmaskK n w (mask w) (L t)) n
    · rfl
    · rw [hb] at hmask
      exact absurd hmask (by decide)
  rw [hT] at hm
  obtain ⟨hnd, -⟩ := cbS_distinct n (tpt w (mask w) (L t)) (List.range c) 0 hm
  unfold tfixK at hfix
  rw [Orb.allN_iff] at hfix
  simp only [Nat.sub_eq] at hfix
  have hfx : ∀ l, s' ≤ l → l < nh → h l x0 = x0 := by
    intro l h1 h2
    have e := hfix (l - s') (by omega)
    simp only [Nat.add_eq, Nat.sub_eq] at e
    rw [Nat.add_sub_cancel' h1] at e
    apply Fin.ext
    rw [← hH l h2 x0]
    exact Nat.eq_of_beq_eq_true e
  have hle : Subgroup.closure (h '' {l | s' ≤ l ∧ l < nh}) ≤
      Subgroup.closure (h '' {l | s ≤ l ∧ l < nh}) :=
    Subgroup.closure_mono (Set.image_mono fun l hl => ⟨le_trans hss hl.1, hl.2⟩)
  have hstab : ∀ g ∈ Subgroup.closure (h '' {l | s' ≤ l ∧ l < nh}), g x0 = x0 := by
    intro g hg
    have hS : Subgroup.closure (h '' {l | s' ≤ l ∧ l < nh}) ≤
        MulAction.stabilizer (Equiv.Perm (Fin n)) x0 := by
      rw [Subgroup.closure_le]
      rintro _ ⟨l, ⟨h1, h2⟩, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hfx l h1 h2
    have e := hS hg
    rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at e
  refine ⟨hss, ?_⟩
  have horb' : ∀ k : Fin c, ∃ g ∈ Subgroup.closure (h '' {l | s ≤ l ∧ l < nh}),
      (g x0 : Nat) = tpt w (mask w) (L t) k := fun k => horb k k.isLt
  choose g hgH hgx using horb'
  let f : Fin c × ↥(Subgroup.closure (h '' {l | s' ≤ l ∧ l < nh})) →
      ↥(Subgroup.closure (h '' {l | s ≤ l ∧ l < nh})) :=
    fun p => ⟨g p.1 * p.2, Subgroup.mul_mem _ (hgH p.1) (hle p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ he
    have he' : g i * a = g j * b := congrArg Subtype.val he
    have h1 : (g i * a) x0 = (g j * b) x0 := by rw [he']
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hstab _ a.2, hstab _ b.2] at h1
    have hij : i = j := by
      apply Fin.ext
      refine List.inj_on_of_nodup_map hnd (List.mem_range.2 i.isLt) (List.mem_range.2 j.isLt) ?_
      rw [← hgx i, ← hgx j, h1]
    subst hij
    have hab : a = b := Subtype.ext (mul_left_cancel he')
    rw [hab]
  have e := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_fin] at e

theorem towerProdK_sound {n w nh nl : Nat} {H L : Nat → Nat} {h : Nat → Equiv.Perm (Fin n)}
    (hH : ∀ l < nh, Raw.Orb.PRep n w (H l) (h l)) (hT : towerK n w (mask w) H L nh nl = true) :
    towerProdK w (mask w) L nl ≤ Nat.card ↥(Subgroup.closure (h '' {l | l < nh})) := by
  unfold towerK at hT
  rw [Orb.allN_iff] at hT
  have hat : ∀ t < nl, tstAt w (mask w) nh nl L t = tst w (mask w) (L t) := by
    intro t ht
    unfold tstAt
    rw [Orb.nIf_eq, if_pos (by rw [Nat.blt_eq]; exact ht)]
  have hatn : tstAt w (mask w) nh nl L nl = nh := by
    unfold tstAt
    rw [Orb.nIf_eq, if_neg (by rw [Nat.blt_eq]; omega)]
  have key : ∀ d t, t + d = nl → ∏ u ∈ Finset.Ico t nl, tcnt w (mask w) (L u) ≤
      Nat.card ↥(Subgroup.closure (h '' {l | tstAt w (mask w) nh nl L t ≤ l ∧ l < nh})) := by
    intro d
    induction d with
    | zero =>
      intro t ht
      rw [← ht, Nat.add_zero, Finset.Ico_self, Finset.prod_empty]
      exact Nat.card_pos
    | succ d ih =>
      intro t ht
      have hl := cbS_level hH (hT t (by omega))
      rw [hat t (by omega), Finset.prod_eq_prod_Ico_succ_bot (by omega : t < nl)]
      calc _ ≤ tcnt w (mask w) (L t) * Nat.card ↥(Subgroup.closure
              (h '' {l | tstAt w (mask w) nh nl L (t + 1) ≤ l ∧ l < nh})) :=
            Nat.mul_le_mul_left _ (ih (t + 1) (by omega))
        _ ≤ _ := hl.2
  have e := key nl 0 (Nat.zero_add nl)
  rw [← Finset.range_eq_Ico, ← cbS_foldl_mul] at e
  refine le_trans ?_ (le_trans e (Subgroup.card_le_of_le
    (Subgroup.closure_mono (Set.image_mono fun l hl => hl.2))))
  unfold towerProdK
  rw [Orb.foldUp_eq]
  rfl

end CFSG.KS.CentBound

end
