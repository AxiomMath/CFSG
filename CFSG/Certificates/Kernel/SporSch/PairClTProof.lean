module

public import CFSG.Certificates.Kernel.SporSch.TabChainLv
public import CFSG.Certificates.Kernel.SporSch.PairClProof

public section

namespace CFSG.KS.SporSch.ClTP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Raw.Dec CFSG.KS.NKey
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Certificates
  CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.KS.SporSch

theorem evR_nfWord {n : Nat} {S : Array (Array Nat)} {base : Array Nat}
    (hF : ∀ i < (rawLevels n S base).size, ∀ k < (rawLevels n S base)[i]!.pts.size,
      Rep n (rawLevels n S base)[i]!.tr[k]! (levT n S base i k))
    {nf : Array Nat} (hnf : nfOK (rawLevels n S base) nf = true) (x : Fin n) :
    evR (nfWord (rawLevels n S base) nf) x = (nfElt n S base nf x : Nat) := by
  obtain ⟨hs, hv⟩ := nfOK_spec hnf
  rw [nfWord_eq_hw, nfElt]
  suffices H : ∀ m ≤ nf.size, ∀ x : Fin n, evR (hw (rawLevels n S base) nf m) x =
      (((List.range m).map fun i => levT n S base i nf[i]!).prod x : Nat) from H _ (Nat.le_refl _) x
  intro m
  induction m with
  | zero => intro _ x; rfl
  | succ m ih =>
    intro hm x
    rw [evR_hw_succ, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, Equiv.Perm.mul_apply, (hF m (by omega) _ (hv m (by omega))) x]
    exact ih (by omega) _

section Levels

variable {n w kS nb BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
  (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ)

include hb hp ho hN in
theorem rep_tr : ∀ i < (rawLevels n S base).size, ∀ k < (rawLevels n S base)[i]!.pts.size,
    Rep n (rawLevels n S base)[i]!.tr[k]! (levT n S base i k) := by
  intro i hi k hk
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hsz : (rawLevels n S base).size = nb := by rw [rawLevels, Array.size_ofFn, hbs]
  have F := native_facts hb hp (by omega : i < nb) (Tab.base_lt hb ho hN i (by omega))
  exact (rep_permOfArr (F.tr_inv k hk)).1

omit hb hp ho hN in
include ht in
theorem lptK_eq {l x : Nat} (hl : l < kS + kS) (hx : x < n) :
    lptK w NR LT l x = pg w (mask w) (letterK PS PSI kS l) x := by
  have hj' : l * n + x < (kS + kS) * n := by nlinarith
  have h1 := Tab.blk_of ht.2.2.2.2.2.1 ht.2.2.1 hj'
  unfold ltOKT at h1
  have h2 := Tab.bIf_true (Nat.blt_eq.mpr hj') h1
  have hd : Nat.div (l * n + x) n = l := by
    change (l * n + x) / n = l
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hx, Nat.zero_add]
  have hm : Nat.mod (l * n + x) n = x := by
    change (l * n + x) % n = x
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  rw [Orb.strictB_eq, hd, Orb.strictB_eq, hm] at h2
  exact Nat.eq_of_beq_eq_true h2

omit ho hN in
include hb hp in
theorem letter_lt {l y : Nat} (hl : l < kS + kS) (hy : y < n) :
    pg w (mask w) (letterK PS PSI kS l) y < n := by
  unfold letterK
  rw [nIf_eq, blt_dec]
  by_cases hk : l < kS
  · simp only [hk, decide_true, ↓reduceIte]
    rw [(prep_PS hb hp hk).1 ⟨y, hy⟩]
    exact Fin.isLt _
  · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte]
    have e := (prep_PS hb hp (j := Nat.sub l kS) (by change l - kS < kS; omega)).2 ⟨y, hy⟩
    change pg w (mask w) (PSI (Nat.sub l kS)) (⟨y, hy⟩ : Fin n) < n
    rw [e]
    exact Fin.isLt _

include hb hp ho hN ht in
theorem nfKeyT_eq {F : Nat} (hF : nfValidK nb LR F = true) :
    nfKeyT n w NR NL LT PT nb base.toList F =
      imgKey n (baseImgs base.toList (nfWord (rawLevels n S base) (Tab.nfA nb F))) := by
  obtain ⟨hnf, hpt⟩ := Tab.nfPtT_spec hb hp ho hN ht hF
  unfold nfKeyT baseImgs
  rw [ClP.keyL_eq]
  congr 1
  refine List.map_congr_left fun b hm => ?_
  have hbn := ClR.mem_base_lt hb.2.2.2.2.2.1 (Tab.base_lt hb ho hN) hm
  rw [hpt b hbn, evR_nfWord (rep_tr hb hp ho hN) hnf ⟨b, hbn⟩]

include hb hp ho hN ht in
theorem conjKeyT_eq {F l : Nat} {g gi : Array Nat} (hF : nfValidK nb LR F = true)
    (hl : l < kS + kS) (hg : g = unpack n w (letterK PS PSI kS l))
    (hgi : gi = unpack n w (letterK PS PSI kS (invL kS l))) :
    conjKeyT n w kS NR NL LT PT nb base.toList l F =
      imgKey n (conjImgs base.toList g gi (nfWord (rawLevels n S base) (Tab.nfA nb F))) := by
  obtain ⟨hnf, hpt⟩ := Tab.nfPtT_spec hb hp ho hN ht hF
  have hil := (Tab.letterK_invL (PS := PS) (PSI := PSI) hl).2
  unfold conjKeyT conjImgs
  rw [ClP.keyL_eq]
  congr 1
  refine List.map_congr_left fun b hm => ?_
  have hbn := ClR.mem_base_lt hb.2.2.2.2.2.1 (Tab.base_lt hb ho hN) hm
  have hy := letter_lt hb hp hil hbn
  have hz : (nfElt n S base (Tab.nfA nb F) ⟨_, hy⟩ : Nat) < n := Fin.isLt _
  rw [lptK_eq ht hil hbn, hpt _ hy, lptK_eq ht hl hz, hgi, unpack_get hbn,
    evR_nfWord (rep_tr hb hp ho hN) hnf ⟨_, hy⟩, hg, unpack_get hz]

end Levels

section Step

variable {n w kS NR NL : Nat} {LT PT QT : Nat → Nat} {nb : Nat} {bs : List Nat}
  {GLt X W K : Nat → Nat} {c h l cur : Nat}

theorem stepNFT_spec (hne : stepNFT n w kS NR NL LT PT QT nb bs GLt X W K c h l cur ≠ failC) :
    (h < cur ∧ ClP.posW W h l < cur ∧
        K (ClP.posW W h l) = conjKeyT n w kS NR NL LT PT nb bs (GLt l) (nfX nb (X h)) ∧
        stepNFT n w kS NR NL LT PT QT nb bs GLt X W K c h l cur = cur) ∨
      (h < cur ∧ ClP.posW W h l = cur ∧
        K (ClP.posW W h l) = conjKeyT n w kS NR NL LT PT nb bs (GLt l) (nfX nb (X h)) ∧
        parNF nb (X (ClP.posW W h l)) = h ∧ labNF nb (X (ClP.posW W h l)) = l ∧
        stepNFT n w kS NR NL LT PT QT nb bs GLt X W K c h l cur = cur + 1) ∨
      (cur ≤ h ∧ cur = c ∧ stepNFT n w kS NR NL LT PT QT nb bs GLt X W K c h l cur = cur) := by
  unfold stepNFT at hne ⊢
  simp only [Orb.strictN_eq, Orb.strictB_eq, bAnd_eq, ClP.posW_eq, ClP.brec_ite, Bool.and_eq_true,
    Nat.blt_eq, Nat.beq_eq, Nat.succ_eq_add_one] at hne ⊢
  split_ifs at hne ⊢ with h1 h2 h3 h4
  all_goals first
    | exact absurd rfl hne
    | exact Or.inl ⟨h1, h2.1, h2.2, rfl⟩
    | exact Or.inr (Or.inl ⟨h1, h3.1, h3.1 ▸ h3.2.1, h3.1 ▸ h3.2.2.2.1, h3.1 ▸ h3.2.2.2.2, rfl⟩)
    | exact Or.inr (Or.inl ⟨h1, h3.1, h3.2.1, h3.2.2.2.1, h3.2.2.2.2, rfl⟩)
    | exact Or.inr (Or.inr ⟨Nat.le_of_not_lt h1, h2, rfl⟩)
    | exact Or.inr (Or.inr ⟨Nat.le_of_not_lt h1, h3, rfl⟩)
    | exact Or.inr (Or.inr ⟨Nat.le_of_not_lt h1, h4, rfl⟩)

theorem stepNFT_fail : stepNFT n w kS NR NL LT PT QT nb bs GLt X W K c h l failC = failC := by
  have hj : ClP.posW W h l ≤ 1048575 := Nat.and_le_right
  unfold stepNFT
  simp only [Orb.strictN_eq, Orb.strictB_eq, bAnd_eq, ClP.posW_eq, ClP.brec_ite, Bool.and_eq_true,
    Nat.blt_eq, Nat.beq_eq, Nat.succ_eq_add_one]
  generalize ClP.posW W h l = j at hj ⊢
  have hf := ClP.failC_eq
  split_ifs <;> first | rfl | omega

end Step

theorem closNFT_proved {n w kS nb BP NS CH NR NL NT BT NQ BQ kg c cap nS R H nB B : Nat}
    {PS PSI LR Ts LT PT QT GLt X W K C SO SOI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs RP : List Nat}
    {gens gensInv : Array (Array Nat)} {rep : List (Array Nat)}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
    (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) (hbs : base.toList = bs)
    (hg : gens.size = kg ∧ gensInv.size = kg ∧
      ∀ l < kg, gens[l]! = unpack n w (letterK PS PSI kS (GLt l)) ∧
        gensInv[l]! = unpack n w (letterK PS PSI kS (invL kS (GLt l))))
    (hrep : rep = RP.map (unpack n w))
    (h : ClosNFT n w kS nb NR NL LR LT PT QT bs kg GLt RP c cap nS R H nB B X W K C SO SOI) :
    closureOK (rawLevels n S base) bs gens gensInv rep
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.2 = true ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.size = c ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.toList.map
          (fun nf => imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf))) =
        (List.range c).map K := by
  subst hbs hrep
  obtain ⟨hgs, hgis, hgl⟩ := hg
  subst hgs
  obtain ⟨hc0, hcap, hcS, hcB, hc20, -, -, hGLt, hRP, -, hst, hk0, hrec, hsrt, hC0, hCN, hrun⟩ := h
  have hbl := Tab.base_lt hb ho hN
  have hLv := lvOK_rawLevels hb hp hbl
  have hbn : ∀ b ∈ base.toList, b < n := fun b hm => ClR.mem_base_lt hb.2.2.2.2.2.1 hbl hm
  have hr : ∀ i < c, nfValidK nb LR (nfX nb (X i)) = true ∧
      K i = nfKeyT n w NR NL LT PT nb base.toList (nfX nb (X i)) := by
    intro i hi
    have h1 := all_of_blocks hcB hrec i hi
    unfold recOKT at h1
    rw [Orb.blt_true hi] at h1
    have h2 : strictB (nfX nb (X i)) (fun x => bAnd(allN nb (fun t =>
        Nat.blt (Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 16) t)) (nat_lit 65535))
          (rcnt (LR t))), Nat.beq (K i) (nfKeyT n w NR NL LT PT nb base.toList x))) = true := h1
    rw [Orb.strictB_eq, bAnd_iff] at h2
    exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩
  have srt := keysK_sound (cs := [(c, K)]) (by simp) hcB hsrt
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at srt
  have hD := nodup_of_strictInc_mergeSort srt
  have hgr : ∀ l < gens.size, ∀ y < n, (gens[l]!)[y]! < n ∧ (gensInv[l]!)[y]! < n := by
    intro l hl' y hy
    rw [(hgl l hl').1, (hgl l hl').2, unpack_get hy, unpack_get hy]
    exact ⟨letter_lt hb hp (hGLt l hl') hy,
      letter_lt hb hp (Tab.letterK_invL (PS := PS) (PSI := PSI) (hGLt l hl')).2 hy⟩
  have hrr : ∀ x ∈ baseImgs base.toList (RP.map (unpack n w)), x < n := by
    intro x hx
    obtain ⟨b, hm, rfl⟩ := List.mem_map.1 hx
    have := ClP.evRK_eq (ClP.range_of_canonL hRP) b (hbn b hm)
    rw [← this.1]
    exact this.2
  have hP0 : parNF nb (X 0) = 0 ∧ labNF nb (X 0) = 0 := by
    unfold startNFT at hst
    rw [bAnd_iff, bAnd_iff, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at hst
    exact hst.2
  refine ClR.closure_replay (T := fun i => Tab.nfA nb (nfX nb (X i)))
    (P := fun i => parNF nb (X i)) (Lb := fun i => labNF nb (X i)) (K := K)
    (KS := fun h l => conjKeyT n w kS NR NL LT PT nb base.toList (GLt l) (nfX nb (X h)))
    (pos := ClP.posW W)
    (f := fun h l cur => stepNFT n w kS NR NL LT PT QT nb base.toList GLt X W K c h l cur)
    (fl := failC) (M := nS * R) (H := H) (C := C)
    hLv hbn hgr hrr hc0 hcap hcS (by rw [ClP.failC_eq]; omega) hC0 hCN (slices_of_groups hrun)
    (fun h l _ => stepNFT_fail) (fun i hi => (Tab.nfPtT_spec hb hp ho hN ht (hr i hi).1).1)
    (fun i hi => by rw [(hr i hi).2, nfKeyT_eq hb hp ho hN ht (hr i hi).1])
    (fun h hh l hl' => by
      rw [conjKeyT_eq hb hp ho hN ht (hr h hh).1 (hGLt l hl') (hgl l hl').1 (hgl l hl').2])
    (fun a ha b hb' e => List.inj_on_of_nodup_map hD (List.mem_range.2 ha) (List.mem_range.2 hb') e)
    (by rw [← ClP.wordKey_eq hRP hbn]; exact (Nat.eq_of_beq_eq_true hk0).symm) hP0.1 hP0.2
    (fun h l cur _ hne => stepNFT_spec hne)

end CFSG.KS.SporSch.ClTP

end
