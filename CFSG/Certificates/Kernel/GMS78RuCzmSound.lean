module

public import Certificates.Data.Kernel.GMS78RuCzm
public import CFSG.Certificates.Kernel.GMS78RuGenCzm
public import CFSG.Certificates.Kernel.GMS78RuNMGlue

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuN
  CFSG.ComponentClassification.GMS78.RuCz

theorem czm_packV_linId : packV linId = LINID := by decide +kernel

theorem czm_idx_mem {r : Lin8} (hr : r ∈ glList) :
    glList.idxOf r < 168 ∧ glList.getD (glList.idxOf r) linId = r := by
  have hl := List.idxOf_lt_length_of_mem hr
  rw [NG.glList_length] at hl
  refine ⟨hl, ?_⟩
  rw [NG.getD_of_lt _ _ (by rw [NG.glList_length]; exact hl), List.getElem_idxOf]

theorem invRevK_eq : ∀ (w acc : List (Fin 7 × Bool)), invRevK w acc = FreeGroup.invRev w ++ acc
  | [], acc => rfl
  | (i, s) :: w, acc => by
    change invRevK w ((i, Bool.rec (motive := fun _ => Bool) true false s) :: acc) = _
    rw [invRevK_eq w, FreeGroup.invRev_cons, List.append_assoc]
    cases s <;> rfl

section Pack

variable {nbt ntw : List (List (Fin 8))} {nc nb : List Nat} {GLL TW ADC TAU INV : Nat}

theorem czm_conj_pack (F : NG.Facts nbt ntw nc nb GLL TW ADC TAU INV) (g gi x : NTrip)
    (hg : g.1 < 256) (hgi : gi.1 < 256) (hx : x.1 < 256) :
    conjK ADC TAU (packT g) (packT gi) (packT x) = packT (Gen.czmConjG nbt ntw nc nb g gi x) ∧
      (Gen.czmConjG nbt ntw nc nb g gi x).1 < 256 := by
  obtain ⟨e1, b1⟩ := NG.mulT_pack F g x hg hx
  obtain ⟨e2, b2⟩ := NG.mulT_pack F _ gi b1 hgi
  unfold conjK Gen.czmConjG
  rw [e1, e2]
  exact ⟨rfl, b2⟩

theorem czm_beq_pack {y x : NTrip} (hy : y.1 < 256) (hx : x.1 < 256) :
    Nat.beq (packT y) (packT x) = (y == x) :=
  Bool.eq_iff_iff.2 ⟨fun h => beq_iff_eq.2 (NG.packT_inj hy hx (Nat.eq_of_beq_eq_true h)),
    fun h => by rw [beq_iff_eq.1 h]; exact Nat.beq_refl _⟩

theorem czm_same_pack (F : NG.Facts nbt ntw nc nb GLL TW ADC TAU INV) (y x : NTrip)
    (hy : y.1 < 256) (hx : x.1 < 256) :
    sameK ADC TAU (packT czmZ0) (packT y) (packT x) = Gen.czmSameG nbt ntw nc nb y x := by
  obtain ⟨e, b⟩ := NG.mulT_pack F x czmZ0 hx (by decide)
  unfold sameK Gen.czmSameG
  rw [NG.orB_eq, e, czm_beq_pack hy hx, czm_beq_pack hy b]

end Pack

theorem czm_m207 : ∀ m < 256, Nat.beq (Nat.land m 207) 0 = czmV0.contains m := by decide +kernel

theorem czm_inX0_pack (y : NTrip) (hy : y.1 < 256) : inX0K (packT y) = czmInX0 y := by
  obtain ⟨m, t, r⟩ := y
  obtain ⟨e1, -, e3⟩ := NG.tr_pack m t r hy
  unfold inX0K czmInX0
  dsimp only
  simp only at hy
  rw [e1, e3, NG.andB_eq, czm_m207 m hy]
  congr 1
  rw [← czm_packV_linId]
  exact Bool.eq_iff_iff.2 ⟨fun h => beq_iff_eq.2 (NG.packV_inj (Nat.eq_of_beq_eq_true h)),
    fun h => by rw [beq_iff_eq.1 h]; exact Nat.beq_refl _⟩

theorem imgsListK_eq (ADC TAU NIMG NIMGI XP : Nat) :
    ∀ ws : List (List (Fin 7 × Bool)),
      imgsListK ADC TAU NIMG NIMGI XP ws = ws.map (imgsK ADC TAU NIMG NIMGI XP)
  | [] => rfl
  | w :: ws => by
    change imgsK ADC TAU NIMG NIMGI XP w :: imgsListK ADC TAU NIMG NIMGI XP ws = _
    rw [imgsListK_eq _ _ _ _ _ ws, List.map_cons]

theorem diffAllK_spec {ADC TAU Z0P U : Nat} :
    ∀ {Vs : List Nat}, diffAllK ADC TAU Z0P U Vs = true → ∀ V ∈ Vs, diffK ADC TAU Z0P U V = true
  | [], _, V, hV => by cases hV
  | V' :: Vs, h, V, hV => by
    obtain ⟨h1, h2⟩ := NG.andB_true h
    rcases List.mem_cons.1 hV with rfl | hV
    · exact h1
    · exact diffAllK_spec h2 V hV

theorem pairDiffK_spec {ADC TAU Z0P : Nat} :
    ∀ {Vs : List Nat}, pairDiffK ADC TAU Z0P Vs = true →
      ∀ i j (hi : i < Vs.length) (hj : j < Vs.length), i < j →
        diffK ADC TAU Z0P Vs[i] Vs[j] = true
  | [], _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | U :: Vs, h, i, j, hi, hj, hij => by
    obtain ⟨h1, h2⟩ := NG.andB_true h
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rcases i with _ | i
    · exact diffAllK_spec h1 _ (List.getElem_mem _)
    · exact pairDiffK_spec h2 i j' (by simpa using hi) (by simpa using hj) (by omega)

theorem packT_lt (y : NTrip) (hy : y.1 < 256) : packT y < 2 ^ 20 := by
  obtain ⟨m, t, r⟩ := y
  rw [NG.packT_eq m t r hy]
  have := NG.packV_lt r
  have := t.isLt
  simp only at hy
  omega

theorem imgsK_fget {ADC TAU NIMG NIMGI XP : Nat} {w : List (Fin 7 × Bool)}
    (hc : ∀ k < 32, conjK ADC TAU (evalS ADC TAU NIMG NIMGI w) (evalS ADC TAU NIMG NIMGI (invRevK w []))
      (fget XP k 20) < 2 ^ 20) {k : Nat} (hk : k < 32) :
    fget (imgsK ADC TAU NIMG NIMGI XP w) k 20 =
      conjK ADC TAU (evalS ADC TAU NIMG NIMGI w) (evalS ADC TAU NIMG NIMGI (invRevK w []))
        (fget XP k 20) :=
  NG.fget_orN 20 32 _ hc k hk

theorem incIdx_head : ∀ {a : Lin8} {l : List Lin8}, Gen.incIdx (a :: l) = true →
    ∀ x ∈ l, Gen.linIdx a < Gen.linIdx x
  | _, [], _, x, hx => by cases hx
  | a, b :: l, h, x, hx => by
    simp only [Gen.incIdx, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (incIdx_head h.2 x hx)

theorem incIdx_tail : ∀ {a : Lin8} {l : List Lin8}, Gen.incIdx (a :: l) = true → Gen.incIdx l = true
  | _, [], _ => rfl
  | _, _ :: _, h => by
    simp only [Gen.incIdx, Bool.and_eq_true] at h
    exact h.2

theorem incIdx_nodup : ∀ {l : List Lin8}, Gen.incIdx l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: _, h => List.nodup_cons.2 ⟨fun ha => Nat.lt_irrefl _ (incIdx_head h a ha),
    incIdx_nodup (incIdx_tail h)⟩

theorem czm_glK : glList.all (fun r => glK (packV r)) = true := by decide +kernel

theorem nine_le {GLL INV ws : Nat} {r : Lin8} {gl : List Lin8} (hperm : gl.Perm glList)
    (hGLL : ∀ i < 168, gllAt GLL i = packV (glList.getD i linId)) (hI : invTabOK INV = true)
    (hc : allN 8 (fun k => andB (Nat.blt (fget ws k 8) 168)
      (andB (Nat.blt (fget ws (Nat.succ k) 8) 168)
        (Nat.blt (conjCodeK INV (gllAt GLL (fget ws k 8)) (packV r))
          (conjCodeK INV (gllAt GLL (fget ws (Nat.succ k) 8)) (packV r))))) = true) :
    9 ≤ (gl.map fun c => czmConjCode c r).dedup.length := by
  have hk : ∀ k < 8, fget ws k 8 < 168 ∧ fget ws (k + 1) 8 < 168 ∧
      conjCodeK INV (gllAt GLL (fget ws k 8)) (packV r) <
        conjCodeK INV (gllAt GLL (fget ws (k + 1) 8)) (packV r) := fun k hk => by
    obtain ⟨a1, a⟩ := NG.andB_true (NG.allN_of hc hk)
    obtain ⟨a2, a3⟩ := NG.andB_true a
    exact ⟨Nat.le_of_ble_eq_true a1, Nat.le_of_ble_eq_true a2, Nat.le_of_ble_eq_true a3⟩
  have ha : ∀ k < 9, fget ws k 8 < 168 := fun k hk' => by
    rcases Nat.lt_or_ge k 8 with h | h
    · exact (hk k h).1
    · have : k = 7 + 1 := by omega
      rw [this]
      exact (hk 7 (by decide)).2.1
  have hgk := czm_glK
  rw [List.all_eq_true] at hgk
  have hcc : ∀ a < 168, conjCodeK INV (gllAt GLL a) (packV r) =
      packV (czmConjCode (glList.getD a linId) r) := fun a ha' => by
    have hm : glList.getD a linId ∈ glList := NG.getD_mem _ (by rw [NG.glList_length]; exact ha')
    have hg := hgk _ hm
    unfold conjCodeK
    rw [hGLL a ha', NG.invTab_eq hI hg (NG.packV_lt _), NG.unV_packV, NG.linComp_pack,
      NG.linComp_pack]
    rfl
  let e : Nat → Lin8 := fun k => czmConjCode (glList.getD (fget ws k 8) linId) r
  have hmono := NG.mono_of_step (g := fun k => packV (e k)) (n := 9) (fun k hk' => by
    have := (hk k (by omega)).2.2
    rw [hcc _ (ha k (by omega)), hcc _ (ha (k + 1) hk')] at this
    exact this)
  have hnd : ((List.range 9).map e).Nodup := by
    refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range
    rw [List.mem_range] at hi hj
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hmono j hj i h
      rw [hij] at this
      exact absurd this (Nat.lt_irrefl _)
    · exact h
    · have := hmono i hi j h
      rw [hij] at this
      exact absurd this (Nat.lt_irrefl _)
  have hsub : (List.range 9).map e ⊆ (gl.map fun c => czmConjCode c r).dedup := by
    intro x hx
    obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hk'
    rw [List.mem_dedup]
    exact List.mem_map_of_mem (hperm.mem_iff.2
      (NG.getD_mem _ (by rw [NG.glList_length]; exact ha k hk')))
  have := (List.Nodup.subperm hnd hsub).length_le
  simpa using this

theorem czm_sound (nbt ntw : List (List (Fin 8))) (nc nb sb : List Nat)
    (dct : List (Fin 8 × Fin 8 × Fin 8)) (img imgInv rT : List (Nat × Fin 8 × (Fin 8 × Fin 8 × Fin 8)))
    (z0w : List (Fin 7 × Bool)) (jw rep : ℕ → List (Fin 7 × Bool)) (gl : List CFSG.GMS78RuSim.Lin8)
    {GLL TW ADC TAU INV NIMG NIMGI NRT XP Z0P W : Nat}
    (hN : bindNC sb nbt nc nb dct ntw = true) (hI : invTabOK INV = true) (hG : gllOK GLL = true)
    (hT : bindTW ntw GLL TW = true) (hB : bindImg img imgInv rT NIMG NIMGI NRT = true)
    (hZ : zeroOK ADC TAU = true) (hR : ∀ i < 168, nmR GLL INV TW ADC TAU (gllAt GLL i) = true)
    (_hId : kId GLL INV ADC TAU = true) (_hIm : kImg ADC TAU NIMG NIMGI = true)
    (hX : bindList packT CFSG.ComponentClassification.GMS78.RuCz.czmX0 XP (nat_lit 20) (nat_lit 32) =
      true)
    (hZ0 : Nat.beq (packT CFSG.ComponentClassification.GMS78.RuCz.czmZ0) Z0P = true)
    (h1 : kZ0 z0w ADC TAU NIMG NIMGI Z0P = true) (h2 : kLetter ADC TAU NIMG NIMGI XP Z0P = true)
    (h3 : kJ ((List.range 6).map jw) ADC TAU NIMG NIMGI XP Z0P = true)
    (h4 : kRep ((List.range 24).map rep) ADC TAU NIMG NIMGI XP Z0P = true)
    (h5 : kInvol GLL INV W = true) (hgl : Gen.glOK gl = true) :
    Gen.czmZ0CheckG nbt ntw nc nb img imgInv z0w = true ∧
      Gen.czmLetterCheckG nbt ntw nc nb img imgInv = true ∧
      Gen.czmJCheckG nbt ntw nc nb img imgInv jw = true ∧
      Gen.czmRepCheckG nbt ntw nc nb img imgInv rep = true ∧
      Gen.czmInvolCheckG gl = true := by
  obtain ⟨-, hNBT, hNC, hNB, -, -⟩ := NG.bindNC_facts hN
  have hGLL := NG.gll_eq hG
  have hGr : ∀ r ∈ glList, gllAt GLL (glList.idxOf r) = packV r := fun r hr => by
    rw [hGLL _ (czm_idx_mem hr).1, (czm_idx_mem hr).2]
  obtain ⟨hTl, hTW⟩ := NG.recIdx (P := fun row i => bindFin8 row (fget TW (gllAt GLL i) 24) 8) hT
  have F : NG.Facts nbt ntw nc nb GLL TW ADC TAU INV :=
    { hNBT := hNBT, hNC := hNC, hNB := hNB, hI := hI,
      hTW := fun r hr j hj => by
        have hi := (czm_idx_mem hr).1
        rw [NG.getD_of_lt ntw [] (by rw [hTl]; exact hi)]
        rw [← hGr r hr]
        exact NG.bindFin8_getD (hTW _ (by rw [hTl]; exact hi)) hj
      hR := fun r hr => by rw [← hGr r hr]; exact hR _ (czm_idx_mem hr).1
      hZ := hZ }
  obtain ⟨hI1, hI2, -, -⟩ := NG.bindImg_facts hB
  obtain ⟨hXl, hXv⟩ := NG.bindList_get hX
  have hZ0' : packT czmZ0 = Z0P := Nat.eq_of_beq_eq_true hZ0
  have hz : czmZ0.1 < 256 := by decide
  have hx0 : ∀ x ∈ czmX0, x.1 < 256 := by decide
  have hXk : ∀ k (hk : k < 32), fget XP k 20 = packT (czmX0[k]'(by rw [hXl]; exact hk)) :=
    fun k hk => (hXv k (by rw [hXl]; exact hk)).symm
  have evalP : ∀ w, evalS ADC TAU NIMG NIMGI w = packT (Gen.nEvalW nbt ntw nc nb img imgInv w) ∧
      (Gen.nEvalW nbt ntw nc nb img imgInv w).1 < 256 := fun w => by
    obtain ⟨e, b⟩ := NG.evalS_pack F hI1 hI2 w nOneT (by decide)
    rw [NG.evalS_eq, NG.ONET_eq, e]
    exact ⟨rfl, b⟩
  have conjW : ∀ (w : List (Fin 7 × Bool)) (x : NTrip), x.1 < 256 →
      conjK ADC TAU (evalS ADC TAU NIMG NIMGI w) (evalS ADC TAU NIMG NIMGI (invRevK w []))
        (packT x) = packT (Gen.czmConjWG nbt ntw nc nb img imgInv w x) ∧
      (Gen.czmConjWG nbt ntw nc nb img imgInv w x).1 < 256 := fun w x hx => by
    rw [invRevK_eq, List.append_nil, (evalP w).1, (evalP _).1]
    exact czm_conj_pack F _ _ _ (evalP w).2 (evalP _).2 hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Gen.czmZ0CheckG, beq_iff_eq]
    have e := Nat.eq_of_beq_eq_true h1
    rw [(evalP z0w).1, ← hZ0'] at e
    exact NG.packT_inj (evalP z0w).2 hz e
  · unfold Gen.czmLetterCheckG
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    have hc := NG.allN_of h2 hi
    beta_reduce at hc
    obtain ⟨c1, c2⟩ := NG.andB_true hc
    obtain ⟨p1, p2⟩ := hI1 i (by omega)
    obtain ⟨q1, q2⟩ := hI2 i (by omega)
    rw [← p1, ← hZ0'] at c1
    rw [(NG.mulT_pack F _ _ p2 hz).1, (NG.mulT_pack F _ _ hz p2).1] at c1
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨NG.packT_inj (NG.mulT_pack F _ _ p2 hz).2 (NG.mulT_pack F _ _ hz p2).2
      (Nat.eq_of_beq_eq_true c1), fun x hx => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hk' : k < 32 := by rw [← hXl]; exact hk
    have c3 := NG.allN_of c2 hk'
    beta_reduce at c3
    rw [hXk k hk', ← p1, ← q1] at c3
    obtain ⟨d1, d2⟩ := NG.andB_true c3
    have hb := hx0 _ hx
    rw [(czm_conj_pack F _ _ _ p2 q2 hb).1, czm_inX0_pack _ (czm_conj_pack F _ _ _ p2 q2 hb).2] at d1
    rw [(czm_conj_pack F _ _ _ q2 p2 hb).1, czm_inX0_pack _ (czm_conj_pack F _ _ _ q2 p2 hb).2] at d2
    rw [Bool.and_eq_true]
    exact ⟨d1, d2⟩
  · unfold Gen.czmJCheckG
    rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro x hx
    have hw : jw i ∈ (List.range 6).map jw := List.mem_map_of_mem hi
    have hc := NG.recAll (P := fun w => allN 32 fun k => sameK ADC TAU Z0P
      (conjK ADC TAU (evalS ADC TAU NIMG NIMGI w) (evalS ADC TAU NIMG NIMGI (invRevK w []))
        (fget XP k 20)) (fget XP k 20)) h3 _ hw
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hk' : k < 32 := by rw [← hXl]; exact hk
    have c3 := NG.allN_of hc hk'
    have hb := hx0 _ hx
    rw [hXk k hk', (conjW _ _ hb).1, ← hZ0', czm_same_pack F _ _ (conjW _ _ hb).2 hb] at c3
    exact c3
  · obtain ⟨-, hp⟩ := NG.andB_true h4
    rw [imgsListK_eq] at hp
    have hd := pairDiffK_spec hp
    unfold Gen.czmRepCheckG
    rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hi hj
    rw [Bool.or_eq_true]
    by_cases hij : i < j
    · right
      have h' := hd i j (by simpa using hi) (by simpa using hj) hij
      simp only [List.getElem_map, List.getElem_range] at h'
      unfold diffK at h'
      rw [NG.notB_eq, Bool.not_eq_true', ← Bool.not_eq_true, NG.allN_iff] at h'
      simp only [not_forall] at h'
      obtain ⟨k, hk, hne⟩ := h'
      rw [List.any_eq_true]
      have hk' : k < czmX0.length := by rw [hXl]; exact hk
      refine ⟨czmX0[k], List.getElem_mem hk', ?_⟩
      have hb := hx0 _ (List.getElem_mem hk')
      have hcl : ∀ (w : List (Fin 7 × Bool)), ∀ k < 32, conjK ADC TAU (evalS ADC TAU NIMG NIMGI w)
          (evalS ADC TAU NIMG NIMGI (invRevK w [])) (fget XP k 20) < 2 ^ 20 := fun w k hk => by
        have hb' := hx0 _ (List.getElem_mem (by rw [hXl]; exact hk : k < czmX0.length))
        rw [hXk k hk, (conjW _ _ hb').1]
        exact packT_lt _ (conjW _ _ hb').2
      rw [imgsK_fget (hcl _) hk, imgsK_fget (hcl _) hk, hXk k hk, (conjW _ _ hb).1, (conjW _ _ hb).1,
        ← hZ0', czm_same_pack F _ _ (conjW _ _ hb).2 (conjW _ _ hb).2] at hne
      simpa using hne
    · left
      simpa using hij
  · have hglsub : ∀ r ∈ gl, r ∈ glList := fun r hr => by
      unfold Gen.glOK at hgl
      simp only [Bool.and_eq_true, List.all_eq_true] at hgl
      exact NG.Facts.mem r (by rw [← NG.indep3_eq]; exact hgl.2 r hr)
    have hgllen : gl.length = 168 := by
      unfold Gen.glOK at hgl
      simp only [Bool.and_eq_true, beq_iff_eq] at hgl
      exact hgl.1.1
    have hglnd : gl.Nodup := by
      unfold Gen.glOK at hgl
      simp only [Bool.and_eq_true] at hgl
      exact incIdx_nodup hgl.1.2
    have hperm : gl.Perm glList :=
      (List.Nodup.subperm hglnd hglsub).perm_of_length_le (by rw [hgllen, NG.glList_length])
    unfold Gen.czmInvolCheckG
    rw [List.all_eq_true]
    intro r hr
    rw [Bool.or_eq_true]
    by_cases hinv : (linComp r r == linId && r != linId) = true
    · right
      rw [decide_eq_true_eq]
      have hrl := hglsub r hr
      have hg := (czm_idx_mem hrl).1
      have hc := NG.allN_of h5 hg
      beta_reduce at hc
      rw [hGr r hrl] at hc
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hinv
      have e1 : Nat.beq (linCompK (packV r) (packV r)) LINID = true := by
        rw [NG.linComp_pack, hinv.1, czm_packV_linId]
        exact Nat.beq_refl _
      have e2 : Nat.beq (packV r) LINID = false := by
        cases e : Nat.beq (packV r) LINID
        · rfl
        · rw [← czm_packV_linId] at e
          exact absurd (NG.packV_inj (Nat.eq_of_beq_eq_true e)) hinv.2
      rw [e1, e2, NG.orB_eq] at hc
      change (false || _) = true at hc
      rw [Bool.false_or] at hc
      exact nine_le hperm hGLL hI hc
    · left
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.2 hinv

end CFSG.KC.GMS

end
