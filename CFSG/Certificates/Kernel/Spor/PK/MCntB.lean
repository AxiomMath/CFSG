module

public import CFSG.Certificates.Kernel.Spor.PK.MCnt
public import CFSG.Sporadic.Schreier.PairWords
public import Certificates.Data.Kernel.Spor.MCountB

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

@[expose] noncomputable def cfldB (n nb w m ky r : Nat) (Rs : List (Nat × Nat)) (g : Nat → Nat) :
    Nat → Nat :=
  flds (if powId nb g 2 = true ∧ powId nb g 1 = false then 1 else 0)
    (if powId nb g 2 = false ∧ powId nb g ky = true then 1 else 0)
    (fun j => if powId nb g 2 = false ∧ powId nb g ky = true ∧
        partZ nb w m ky r (rAt Rs j).1 (rAt Rs j).2 g = true then 1 else 0)
    (fun j => if powId nb g 2 = true ∧ powId nb g 1 = false ∧
        allFrom (fun i => Nat.beq (g i) (pg w m (rAt Rs j).1 i)) n 0 = true then 1 else 0)

private theorem nIfB_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem cntZB_eq (n nb w m ky r : Nat) (Rs : List (Nat × Nat)) (g : Nat → Nat) (s : Nat) :
    cntZB n nb w m ky r Rs g s = s + dsum (cfldB n nb w m ky r Rs g) (2 + 2 * Rs.length) := by
  rw [dsum_split]
  simp only [cfldB, flds_zero, flds_one, flds_even, flds_odd]
  unfold cntZB
  rw [memsZ_eq, partsZ_eq]
  cases h2 : powId nb g 2 <;> cases h1 : powId nb g 1 <;> cases hk : powId nb g ky <;>
    simp <;> omega

theorem cfldB_le_one (n nb w m ky r : Nat) (Rs : List (Nat × Nat)) (g : Nat → Nat) (f : Nat) :
    cfldB n nb w m ky r Rs g f ≤ 1 := by
  unfold cfldB flds
  dsimp only
  split_ifs <;> omega

theorem lastZB_eq (n nb w m nw pm ky r : Nat) (Rs : List (Nat × Nat)) (L3 L4 h s : Nat) :
    lastZB n nb w m nw pm ky r Rs L3 L4 h s = s + ((List.range (lcnt L3)).map fun k3 =>
      ((List.range (lcnt L4)).map fun k4 =>
        cntZB n nb w m ky r Rs (raw3 w m h (ltr nw pm L3 k3) (ltr nw pm L4 k4)) 0).sum).sum := by
  have h4 : ∀ (g : Nat → Nat) (s : Nat),
      cntZB n nb w m ky r Rs g s = s + cntZB n nb w m ky r Rs g 0 :=
    fun g s => by rw [cntZB_eq, cntZB_eq _ _ _ _ _ _ _ _ 0, Nat.zero_add]
  unfold lastZB
  simp only [strictN_eq]
  rw [foldUp_add]
  · refine congrArg (s + ·) (congrArg List.sum (List.map_congr_left fun k3 _ => ?_))
    rw [foldUp_add, Nat.zero_add]
    · rfl
    · intro k4 s
      exact h4 _ s
  · intro k3 s
    rw [foldUp_add, foldUp_add, Nat.zero_add]
    · intro k4 s
      exact h4 _ s
    · intro k4 s
      exact h4 _ s

theorem sliceZB_eq (n nb w m nw pm ky r : Nat) (Rs : List (Nat × Nat))
    (L0 L1 L2 L3 L4 sub i : Nat) :
    sliceZB n nb w m nw pm ky r Rs L0 L1 L2 L3 L4 sub i =
      ((List.range (lcnt L1 / sub)).map fun j => ((List.range (lcnt L2)).map fun k2 =>
        lastZB n nb w m nw pm ky r Rs L3 L4 (pcomp n w m (pcomp n w m (ltr nw pm L0 (i / sub))
          (ltr nw pm L1 (lcnt L1 / sub * (i % sub) + j))) (ltr nw pm L2 k2)) 0).sum).sum := by
  have hl : ∀ h s, lastZB n nb w m nw pm ky r Rs L3 L4 h s =
      s + lastZB n nb w m nw pm ky r Rs L3 L4 h 0 :=
    fun h s => by rw [lastZB_eq, lastZB_eq _ _ _ _ _ _ _ _ _ _ _ _ 0, Nat.zero_add]
  unfold sliceZB
  simp only [strictN_eq]
  rw [foldUp_add, Nat.zero_add]
  · refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [foldUp_add, Nat.zero_add]
    · rfl
    · intro k2 s
      exact hl _ s
  · intro j s
    rw [foldUp_add, foldUp_add, Nat.zero_add]
    · intro k2 s
      exact hl _ s
    · intro k2 s
      exact hl _ s

section Five

variable {n w : Nat} {F : Nat → Nat → Nat} {s : Nat → BS} {V : Nat → Nat}

theorem sliceZB_five (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hg : ∀ i, GoodBS n F (s i))
    (nb ky r : Nat) (Rs : List (Nat × Nat)) (sub i : Nat) :
    sliceZB n nb w (mask w) (n * w) (mask (n * w)) ky r Rs (recBS n w F (s 0) (V 0))
        (recBS n w F (s 1) (V 1)) (recBS n w F (s 2) (V 2)) (recBS n w F (s 3) (V 3))
        (recBS n w F (s 4) (V 4)) sub i =
      rsum ((s 1).pts.length / sub) fun j => rsum (s 2).pts.length fun k2 =>
        rsum (s 3).pts.length fun k3 => rsum (s 4).pts.length fun k4 =>
          cntZB n nb w (mask w) ky r Rs (raw5 n w F s V (i / sub)
            ((s 1).pts.length / sub * (i % sub) + j) k2 k3 k4) 0 := by
  rw [sliceZB_eq]
  simp only [lastZB_eq, Nat.zero_add, lcnt_recBS hn16 hw (hg _)]
  rfl

theorem cntSum_fiveB (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hg : ∀ i, GoodBS n F (s i))
    (nb ky r : Nat) (Rs : List (Nat × Nat)) {sub : Nat}
    (hsub : 0 < sub ∧ (s 1).pts.length % sub = 0)
    (hsz : (s 1).pts.length * (s 2).pts.length * (s 3).pts.length * (s 4).pts.length < 2 ^ 20)
    {CS : List Nat} (hCS : CS.length = (s 0).pts.length * sub)
    (hc : ∀ i < (s 0).pts.length * sub, sliceZB n nb w (mask w) (n * w) (mask (n * w)) ky r Rs
      (recBS n w F (s 0) (V 0)) (recBS n w F (s 1) (V 1)) (recBS n w F (s 2) (V 2))
      (recBS n w F (s 3) (V 3)) (recBS n w F (s 4) (V 4)) sub i = CS.getD i 0)
    {P : Nat → Prop}
    (hP : ∀ f, P f → ∀ g g' : Nat → Nat, (∀ x < n, g x = g' x) → (∀ x < n, g x < n) →
      cfldB n nb w (mask w) ky r Rs g f = cfldB n nb w (mask w) ky r Rs g' f)
    {f : Nat} (hf : f < 2 + 2 * Rs.length) (hPf : P f) :
    cntSum CS f = ((products ((List.range 5).map fun i =>
      (List.range (s i).pts.length).map (tau n F s i))).map fun σ =>
        cfldB n nb w (mask w) ky r Rs (cfn σ) f).sum := by
  set c : Nat → Nat := fun i => (s i).pts.length with hcdef
  set N := 2 + 2 * Rs.length
  set q := c 1 / sub
  have hq : q * sub = c 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hsub.2)
  have hqle : q ≤ c 1 := Nat.div_le_self _ _
  have hdig : ∀ i < c 0 * sub, (CS.getD i 0 >>> (20 * f)) % 2 ^ 20 =
      rsum q fun j => rsum (c 2) fun k2 => rsum (c 3) fun k3 => rsum (c 4) fun k4 =>
        cfldB n nb w (mask w) ky r Rs (raw5 n w F s V (i / sub) (q * (i % sub) + j) k2 k3 k4)
          f := by
    intro i hi
    rw [← hc i hi, sliceZB_five hn16 hw hg]
    simp only [cntZB_eq, Nat.zero_add, rsum_dsum]
    rw [Nat.shiftRight_eq_div_pow, dsum_digit _ f N, ite_eq_left hf]
    intro f'
    have hb : (rsum q fun j => rsum (c 2) fun k2 => rsum (c 3) fun k3 => rsum (c 4) fun k4 =>
        cfldB n nb w (mask w) ky r Rs (raw5 n w F s V (i / sub) (q * (i % sub) + j) k2 k3 k4)
          f') ≤ q * (c 2 * (c 3 * (c 4 * 1))) :=
      rsum_le fun j _ => rsum_le fun k2 _ => rsum_le fun k3 _ => rsum_le fun k4 _ =>
        cfldB_le_one _ _ _ _ _ _ _ _ _
    have h1 : q * (c 2 * (c 3 * (c 4 * 1))) ≤ c 1 * (c 2 * (c 3 * (c 4 * 1))) :=
      Nat.mul_le_mul_right _ hqle
    have h2 : c 1 * (c 2 * (c 3 * (c 4 * 1))) < 2 ^ 20 := by
      simp only [Nat.mul_one, ← Nat.mul_assoc]
      exact hsz
    exact lt_of_le_of_lt (hb.trans h1) h2
  unfold cntSum
  rw [sum_map_eq_rsum CS _ 0, hCS]
  rw [rsum_congr hdig, rsum_slices (c 0) sub q
    (fun k0 k1 => rsum (c 2) fun k2 => rsum (c 3) fun k3 => rsum (c 4) fun k4 =>
      cfldB n nb w (mask w) ky r Rs (raw5 n w F s V k0 k1 k2 k3 k4) f), hq]
  have hT : (List.range 5).map (fun i => (List.range (s i).pts.length).map (tau n F s i)) =
      [(List.range (c 0)).map (tau n F s 0), (List.range (c 1)).map (tau n F s 1),
        (List.range (c 2)).map (tau n F s 2), (List.range (c 3)).map (tau n F s 3),
        (List.range (c 4)).map (tau n F s 4)] := rfl
  rw [hT]
  simp only [sum_products_cons]
  refine rsum_congr fun k0 h0 => rsum_congr fun k1 h1 => rsum_congr fun k2 h2 =>
    rsum_congr fun k3 h3 => rsum_congr fun k4 h4 => ?_
  rw [hP f hPf _ _ (raw5_eq hn16 hw hg h0 h1 h2 h3 h4) (raw5_lt hn16 hw hg h0 h1 h2 h3 h4)]
  rfl

end Five

theorem powId_le_congr {n nb : Nat} (hnb : nb ≤ n) {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) (k : Nat) : powId nb g k = powId nb g' k := by
  apply Bool.eq_iff_iff.2
  unfold powId
  rw [allFrom_iff, allFrom_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [Nat.zero_add, (itr_congr h hg k (Nat.lt_of_lt_of_le hi hnb)).1]

theorem cfldB_congr_mem {n nb w m ky r : Nat} {Rs : List (Nat × Nat)} {f : Nat} (hnb : nb ≤ n)
    (hf : f = 0 ∨ f = 1 ∨ (3 ≤ f ∧ f % 2 = 1)) {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) : cfldB n nb w m ky r Rs g f = cfldB n nb w m ky r Rs g' f := by
  have hp : ∀ k, powId nb g k = powId nb g' k := powId_le_congr hnb h hg
  have ha : ∀ R, allFrom (fun i => Nat.beq (g i) (pg w m R i)) n 0 =
      allFrom (fun i => Nat.beq (g' i) (pg w m R i)) n 0 := fun R =>
    allFrom_congr fun i hi => by rw [h i hi]
  unfold cfldB flds
  rcases hf with rfl | rfl | hf
  · simp only [ite_true, hp]
  · simp only [ite_true, ite_false, hp, one_ne_zero]
  · have h0 : f ≠ 0 := by omega
    have h1 : f ≠ 1 := by omega
    have h2 : f % 2 ≠ 0 := by omega
    simp only [h0, h1, h2, ite_false, hp, ha]

theorem cfldB_congr {n nb w m ky r : Nat} {Rs : List (Nat × Nat)} (hnb : nb ≤ n)
    (hR : ∀ j, ∀ x < n, pg w m (rAt Rs j).1 x < n ∧ pg w m (rAt Rs j).2 x < n) (f : Nat)
    {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) : cfldB n nb w m ky r Rs g f = cfldB n nb w m ky r Rs g' f := by
  have hp : ∀ k, powId nb g k = powId nb g' k := powId_le_congr hnb h hg
  have ha : ∀ R, allFrom (fun i => Nat.beq (g i) (pg w m R i)) n 0 =
      allFrom (fun i => Nat.beq (g' i) (pg w m R i)) n 0 := fun R =>
    allFrom_congr fun i hi => by rw [h i hi]
  have hz : ∀ j, partZ nb w m ky r (rAt Rs j).1 (rAt Rs j).2 g =
      partZ nb w m ky r (rAt Rs j).1 (rAt Rs j).2 g' := fun j => by
    have hR1 := fun x hx => (hR j x hx).1
    have hR2 := fun x hx => (hR j x hx).2
    have h1 : ∀ x < n, pg w m (rAt Rs j).1 (g x) = pg w m (rAt Rs j).1 (g' x) :=
      fun x hx => by rw [h x hx]
    have h1' : ∀ x < n, pg w m (rAt Rs j).1 (g x) < n := fun x hx => hR1 _ (hg x hx)
    have hi := fun i (hi : i < n) => itr_congr h hg (Nat.sub ky 1) hi
    have h2 : ∀ x < n, pg w m (rAt Rs j).1 (g (pg w m (rAt Rs j).2
        (MEnum.itr g (Nat.sub ky 1) x))) = pg w m (rAt Rs j).1 (g' (pg w m (rAt Rs j).2
        (MEnum.itr g' (Nat.sub ky 1) x))) := fun x hx => by
      rw [← (hi x hx).1, h _ (hR2 _ (hi x hx).2)]
    have h2' : ∀ x < n, pg w m (rAt Rs j).1 (g (pg w m (rAt Rs j).2
        (MEnum.itr g (Nat.sub ky 1) x))) < n :=
      fun x hx => hR1 _ (hg _ (hR2 _ (hi x hx).2))
    unfold partZ ordPZ ord6Z
    rw [powId_le_congr hnb h1 h1', powId_le_congr hnb h1 h1', powId_le_congr hnb h2 h2',
      powId_le_congr hnb h2 h2', powId_le_congr hnb h2 h2', powId_le_congr hnb h2 h2']
  unfold cfldB flds
  simp only [hp, ha, hz]

theorem powId_base {n nb : Nat} {G : Subgroup (Equiv.Perm (Fin n))} (hnb : nb ≤ n)
    (hG : BaseFaithful G (List.range nb)) {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ G) (k : Nat) :
    powId nb (cfn σ) k = powId n (cfn σ) k := by
  apply Bool.eq_iff_iff.2
  rw [powId_cfn]
  unfold powId
  rw [allFrom_iff]
  constructor
  · intro h
    refine hG _ (G.pow_mem hσ k) fun x hx => Fin.ext ?_
    have := h x.val (List.mem_range.1 hx)
    rw [Nat.zero_add, Nat.beq_eq, itr_cfn σ k x] at this
    exact this
  · intro h i hi
    rw [Nat.zero_add, Nat.beq_eq, itr_cfn σ k ⟨i, Nat.lt_of_lt_of_le hi hnb⟩, h]
    rfl

theorem powId_base_of {n nb : Nat} {G : Subgroup (Equiv.Perm (Fin n))} (hnb : nb ≤ n)
    (hG : BaseFaithful G (List.range nb)) {τ : Equiv.Perm (Fin n)} (hτ : τ ∈ G)
    {g : Nat → Nat} (h : ∀ x < n, g x = cfn τ x) (k : Nat) : powId nb g k = powId n g k := by
  have hg : ∀ x < n, g x < n := fun x hx => by rw [h x hx]; exact cfn_lt τ hx
  have hτg : ∀ x < n, cfn τ x = g x := fun x hx => (h x hx).symm
  rw [powId_le_congr hnb h hg, powId_base hnb hG hτ, powId_congr hτg (fun x hx => cfn_lt τ hx)]

theorem partZ_base {n nb w ky r R Ri : Nat} {G : Subgroup (Equiv.Perm (Fin n))} (hnb : nb ≤ n)
    (hG : BaseFaithful G (List.range nb)) {σ ρ : Equiv.Perm (Fin n)} (hσ : σ ∈ G) (hρ : ρ ∈ G)
    (pR : ∀ x : Fin n, pg w (mask w) R x = ρ x) (pRi : ∀ x : Fin n, pg w (mask w) Ri x = ρ⁻¹ x) :
    partZ nb w (mask w) ky r R Ri (cfn σ) = partZ n w (mask w) ky r R Ri (cfn σ) := by
  have h1 : ∀ x < n, pg w (mask w) R (cfn σ x) = cfn (ρ * σ) x := fun x hx => by
    have e1 : cfn σ x = (σ ⟨x, hx⟩ : Nat) := dite_eq_left hx
    have e2 : cfn (ρ * σ) x = ((ρ * σ) ⟨x, hx⟩ : Nat) := dite_eq_left hx
    rw [e1, e2, pR, Equiv.Perm.mul_apply]
  have h2 : ∀ x < n, pg w (mask w) R (cfn σ (pg w (mask w) Ri
      (MEnum.itr (cfn σ) (Nat.sub ky 1) x))) = cfn (ρ * σ * ρ⁻¹ * σ ^ (Nat.sub ky 1)) x :=
    fun x hx => by
      have e0 : MEnum.itr (cfn σ) (Nat.sub ky 1) x = ((σ ^ (Nat.sub ky 1)) ⟨x, hx⟩ : Nat) :=
        itr_cfn σ (Nat.sub ky 1) ⟨x, hx⟩
      have e2 : cfn (ρ * σ * ρ⁻¹ * σ ^ (Nat.sub ky 1)) x =
          ((ρ * σ * ρ⁻¹ * σ ^ (Nat.sub ky 1)) ⟨x, hx⟩ : Nat) := dite_eq_left hx
      rw [e0, pRi, cfn_apply, pR, e2]
      simp only [Equiv.Perm.mul_apply]
  have g1 : ρ * σ ∈ G := G.mul_mem hρ hσ
  have g2 : ρ * σ * ρ⁻¹ * σ ^ (Nat.sub ky 1) ∈ G :=
    G.mul_mem (G.mul_mem g1 (G.inv_mem hρ)) (G.pow_mem hσ _)
  unfold partZ ordPZ ord6Z
  rw [powId_base_of hnb hG g1 h1, powId_base_of hnb hG g1 h1, powId_base_of hnb hG g2 h2,
    powId_base_of hnb hG g2 h2, powId_base_of hnb hG g2 h2, powId_base_of hnb hG g2 h2]

theorem cfldB_eq_cfld {n nb w ky r : Nat} {Rs : List (Nat × Nat)}
    {G : Subgroup (Equiv.Perm (Fin n))} (hnb : nb ≤ n) (hG : BaseFaithful G (List.range nb))
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ G) {f : Nat}
    (hz : ∀ j, f = 2 + 2 * j → partZ nb w (mask w) ky r (rAt Rs j).1 (rAt Rs j).2 (cfn σ) =
      partZ n w (mask w) ky r (rAt Rs j).1 (rAt Rs j).2 (cfn σ)) :
    cfldB n nb w (mask w) ky r Rs (cfn σ) f = cfld n w (mask w) ky r Rs (cfn σ) f := by
  have hp : ∀ k, powId nb (cfn σ) k = powId n (cfn σ) k := powId_base hnb hG hσ
  rcases Nat.lt_or_ge f 2 with hf | hf
  · rcases Nat.lt_or_ge f 1 with hf1 | hf1
    · obtain rfl : f = 0 := by omega
      simp only [cfldB, cfld, flds_zero, hp]
    · obtain rfl : f = 1 := by omega
      simp only [cfldB, cfld, flds_one, hp]
  · rcases Nat.even_or_odd f with ⟨j, hj⟩ | ⟨j, hj⟩
    · obtain ⟨i, rfl⟩ : ∃ i, f = 2 + 2 * i := ⟨j - 1, by omega⟩
      simp only [cfldB, cfld, flds_even, hp, hz i rfl]
    · obtain ⟨i, rfl⟩ : ∃ i, f = 3 + 2 * i := ⟨j - 1, by omega⟩
      simp only [cfldB, cfld, flds_odd, hp]

end CFSG.KS.PK

end
