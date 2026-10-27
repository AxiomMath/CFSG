module

public import Certificates.Data.Kernel.LocalQT.X1H
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.Certificates.Kernel.LocalQTBfsClosedProved
public import CFSG.Certificates.Kernel.LocalQTEnumFProved

public section

namespace CFSG.KC.LQT.XH.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS CFSG.KC.LQT.XH
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.RF.Pf CFSG.KC.LQT.BS.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

section Codes

variable {n w : Nat}

@[expose] def VC (n w c : Nat) : Prop :=
  (∀ i < n, imgW w c i < n) ∧ ∀ p, w * n ≤ p → c.testBit p = false

theorem imgW_mulW {a b i : Nat} (hi : i < n) : imgW w (mulW n w a b) i = imgW w a (imgW w b i) :=
  imgW_ofFnW (fun _ _ => imgW_lt _ _ _) hi

theorem vc_mul {a b : Nat} (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    VC n w (mulW n w a b) :=
  ⟨fun i hi => by rw [imgW_mulW hi]; exact ha _ (hb i hi),
    fun _ hp => testBit_ofFnW_hi (fun _ _ => imgW_lt _ _ _) hp⟩

theorem vc_one (hw : n ≤ 2 ^ w) : VC n w (oneW n w) :=
  ⟨fun i hi => by rw [oneW, imgW_ofFnW (fun j hj => by omega) hi]; exact hi,
    fun _ hp => testBit_ofFnW_hi (fun j hj => by omega) hp⟩

theorem imgW_one (hw : n ≤ 2 ^ w) {i : Nat} (hi : i < n) : imgW w (oneW n w) i = i := by
  rw [oneW, imgW_ofFnW (fun j hj => by omega) hi]

theorem code_eq {a b : Nat} (ha : VC n w a) (hb : VC n w b)
    (h : ∀ i < n, imgW w a i = imgW w b i) : a = b :=
  code_ext ha.2 hb.2 h

theorem mulW_assoc {a b c : Nat} (hc : ∀ i < n, imgW w c i < n) :
    mulW n w (mulW n w a b) c = mulW n w a (mulW n w b c) := by
  unfold mulW
  apply ofFnW_congr
  intro j hj
  rw [imgW_ofFnW (fun _ _ => imgW_lt _ _ _) (hc j hj), imgW_ofFnW (fun _ _ => imgW_lt _ _ _) hj]

theorem one_mulW (hw : n ≤ 2 ^ w) {a : Nat} (ha : VC n w a) : mulW n w (oneW n w) a = a :=
  code_eq (vc_mul (vc_one hw).1 ha.1) ha fun i hi => by rw [imgW_mulW hi, imgW_one hw (ha.1 i hi)]

@[expose] noncomputable def tabC (n w c : Nat) : Array Nat := ((List.range n).map (imgW w c)).toArray

theorem img_tabC {c i : Nat} (hi : i < n) : img (tabC n w c) i = imgW w c i := by
  rw [img, tabC, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hi]
  rfl

theorem rep_tabC {c : Nat} (hc : ∀ i < n, imgW w c i < n) : Rep n w c (tabC n w c) :=
  ⟨by simp [tabC], fun i hi => by rw [img_tabC hi]; exact ⟨hc i hi, rfl⟩⟩

theorem rep_unique {c : Nat} {s t : Array Nat} (hs : Rep n w c s) (ht : Rep n w c t) : s = t := by
  apply Array.ext (by rw [hs.1, ht.1])
  intro i h1 h2
  have hi : i < n := by rw [← hs.1]; exact h1
  have e1 := (hs.2 i hi).2
  have e2 := (ht.2 i hi).2
  rw [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some] at e1
  rw [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some] at e2
  rw [← e1, ← e2]

theorem tabC_inj {a b : Nat} (ha : VC n w a) (hb : VC n w b) (h : tabC n w a = tabC n w b) :
    a = b :=
  code_eq ha hb fun i hi => by rw [← img_tabC hi, ← img_tabC hi, h]

theorem compArr_tabC {a b : Nat} (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    compArr (tabC n w a) (tabC n w b) = tabC n w (mulW n w a b) :=
  rep_unique (rep_mul (rep_tabC ha) (rep_tabC hb)) (rep_tabC (vc_mul ha hb).1)

theorem rep_fields {c : Nat} {s : Array Nat} (h : Rep n w c s) : ∀ i < n, imgW w c i < n :=
  fun i hi => by rw [(h.2 i hi).2]; exact (h.2 i hi).1

end Codes

theorem find_go (f : Nat → Bool) (d : Nat) : ∀ (m j : Nat),
    Nat.rec (motive := fun _ => Nat → Nat) (fun _ => d)
      (fun _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j)) j (f j)) m j =
    ((List.range' j m).find? f).getD d
  | 0, _ => rfl
  | m + 1, j => by
    change Bool.rec (motive := fun _ => Nat) (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => d)
      (fun _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j)) j (f j)) m (j + 1)) j
        (f j) = _
    rw [List.range'_succ, List.find?_cons]
    cases f j
    · exact find_go f d m (j + 1)
    · rfl

theorem discT_eq (W g : Nat) (CT : Nat → Nat) (p i : Nat) : discT W g CT p i =
    ((List.range g).find? fun t => Nat.beq (fieldT W CT (Nat.add (Nat.mul p (Nat.add g g)) t)) i).getD
      g := by
  rw [discT, List.range_eq_range']
  exact find_go _ g g 0

theorem findW_eq' (g : Nat) (f : Nat → Bool) : findW g f = ((List.range g).find? f).getD 0 := by
  rw [findW, List.range_eq_range']
  exact find_go f 0 g 0

theorem find_some {g d : Nat} {f : Nat → Bool} (hd : g ≤ d)
    (h : ((List.range g).find? f).getD d < g) :
    ∃ t, (List.range g).find? f = some t ∧ t < g ∧ f t = true := by
  cases hf : (List.range g).find? f with
  | none => rw [hf] at h; simp at h; omega
  | some t => exact ⟨t, rfl, List.mem_range.1 (List.mem_of_find?_eq_some hf), List.find?_some hf⟩

section Entries

variable {n w W g N : Nat} {Gc : List Nat} {RC PT CT : Nat → Nat}

theorem par_spec
    (hpar : ∀ i < N, 0 < i → fieldT W PT i < i ∧ discT W g CT (fieldT W PT i) i < g)
    {i : Nat} (hi : i < N) (hi0 : 0 < i) :
    fieldT W PT i < i ∧ genIdxT W g (Nat.add g g) PT CT i < g ∧
      fieldT W CT (fieldT W PT i * (g + g) + genIdxT W g (Nat.add g g) PT CT i) = i := by
  obtain ⟨h1, h2⟩ := hpar i hi hi0
  rw [discT_eq] at h2
  obtain ⟨t, hf, ht, hpt⟩ := find_some (Nat.le_refl g) h2
  have e : genIdxT W g (Nat.add g g) PT CT i = t := by
    rw [genIdxT, findW_eq', hf]
    rfl
  rw [e]
  exact ⟨h1, ht, P.beq_iff.1 hpt⟩

variable (hw : n ≤ 2 ^ w) (hGf : ∀ t < g, ∀ i < n, imgW w (Gc.getD t 0) i < n)
  (hRC0 : RC 0 = oneW n w)
  (hst : ∀ i < N, ∀ t < g, fieldT W CT (i * (g + g) + t) < N ∧
    mulW n w (Gc.getD t 0) (RC i) = RC (fieldT W CT (i * (g + g) + t)))
  (hpar : ∀ i < N, 0 < i → fieldT W PT i < i ∧ discT W g CT (fieldT W PT i) i < g)

include hw hGf hRC0 hst hpar in
theorem rc_vc : ∀ i < N, VC n w (RC i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hRC0]
      exact vc_one hw
    · obtain ⟨h1, h2, h3⟩ := par_spec hpar hi hi0
      have := (hst (fieldT W PT i) (by omega) _ h2).2
      rw [h3] at this
      rw [← this]
      exact vc_mul (hGf _ h2) (ih _ h1 (by omega)).1

include hw hGf hRC0 hst hpar in
theorem mulG_rc : ∀ f i k, i ≤ f → i < N → k < N →
    mulG (fieldT W PT) (fieldT W CT) g (Nat.add g g) f i k < N ∧
      RC (mulG (fieldT W PT) (fieldT W CT) g (Nat.add g g) f i k) = mulW n w (RC i) (RC k) := by
  intro f
  induction f with
  | zero =>
    intro i k hif _ hk
    obtain rfl : i = 0 := by omega
    refine ⟨hk, ?_⟩
    change RC k = _
    rw [hRC0, one_mulW hw (rc_vc hw hGf hRC0 hst hpar k hk)]
  | succ f ih =>
    intro i k hif hi hk
    have hvk := rc_vc hw hGf hRC0 hst hpar k hk
    by_cases hi0 : i = 0
    · subst hi0
      refine ⟨hk, ?_⟩
      change RC k = _
      rw [hRC0, one_mulW hw hvk]
    · obtain ⟨h1, h2, h3⟩ := par_spec hpar hi (Nat.pos_of_ne_zero hi0)
      have e : mulG (fieldT W PT) (fieldT W CT) g (Nat.add g g) (f + 1) i k =
          fieldT W CT (mulG (fieldT W PT) (fieldT W CT) g (Nat.add g g) f (fieldT W PT i) k *
            (g + g) + genIdxT W g (Nat.add g g) PT CT i) := by
        change Bool.rec (motive := fun _ => Nat) _ k (Nat.beq i 0) = _
        rw [beq_false hi0]
        rfl
      obtain ⟨m1, m2⟩ := ih (fieldT W PT i) k (by omega) (by omega) hk
      obtain ⟨s1, s2⟩ := hst _ m1 _ h2
      obtain ⟨-, p2⟩ := hst (fieldT W PT i) (by omega) _ h2
      rw [h3] at p2
      rw [e]
      refine ⟨s1, ?_⟩
      rw [← s2, m2, ← p2, mulW_assoc hvk.1]

include hw hGf hRC0 hst hpar in
theorem x1_bfs {G Gi : List (Array Nat)} (hGl : G.length = g)
    (hGrep : ∀ t < g, Rep n w (Gc.getD t 0) G[t]!) (hGil : Gi.length = G.length)
    (hinv : ∀ j < G.length, ∀ q < n, img Gi[j]! (img G[j]! q) = q)
    (hinj : ∀ a < N, ∀ b < N, RC a = RC b → a = b) (hN : 0 < N) (fuel : Nat) (hfuel : N ≤ fuel) :
    BaseEnumOK n (List.range n) G Gi (bfsEnumB n (List.range n) G Gi fuel).1
      (bfsEnumB n (List.range n) G Gi fuel).2.1 (bfsEnumB n (List.range n) G Gi fuel).2.2 ∧
    (bfsEnumB n (List.range n) G Gi fuel).1.size = N ∧
    ∀ T, T ∈ (bfsEnumB n (List.range n) G Gi fuel).1.toList ↔
      ∃ i < N, T = (ptsOf (List.range n) G).map (imgW w (RC i)) := by
  have hvc := rc_vc hw hGf hRC0 hst hpar
  have hsG : ∀ s ∈ G, ∃ t < g, s = G[t]! := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
    exact ⟨t, by omega, (getElem!_pos G t ht).symm⟩
  have hoN : ∀ p ∈ ptsOf (List.range n) G, p < n := by
    intro x hx
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact List.mem_range.1 hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨t, ht, rfl⟩ := hsG s hs
      exact ((hGrep t ht).2 b (List.mem_range.1 hb)).1
  have hoget : ∀ q < n, (ptsOf (List.range n) G).getD q 0 = q := by
    intro q hq
    rw [ptsOf, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_range hq, Option.getD_some]
  have hUget : ∀ i q, q < n → ((ptsOf (List.range n) G).map (imgW w (RC i))).getD q 0 =
      imgW w (RC i) q := by
    intro i q hq
    have hlen : q < (ptsOf (List.range n) G).length := by
      rw [ptsOf, List.length_append, List.length_range]
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
      Option.map_some, Option.getD_some]
    have := hoget q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at this
    rw [this]
  have hUinj : ∀ a < N, ∀ b < N, (∀ q < n, imgW w (RC a) q = imgW w (RC b) q) → a = b :=
    fun a ha b hb h => hinj a ha b hb (code_eq (hvc a ha) (hvc b hb) h)
  have hstepU : ∀ i < N, ∀ t < g, applyTab G[t]! ((ptsOf (List.range n) G).map (imgW w (RC i))) =
      (ptsOf (List.range n) G).map (imgW w (RC (fieldT W CT (i * (g + g) + t)))) := by
    intro i hi t ht
    rw [applyTab, List.map_map]
    apply List.map_congr_left
    intro p hp
    have hpn := hoN p hp
    rw [← (hst i hi t ht).2, imgW_mulW hpn, Function.comp_apply,
      ((hGrep t ht).2 _ ((hvc i hi).1 p hpn)).2]
  set Ul := (List.range N).map fun i => (ptsOf (List.range n) G).map (imgW w (RC i)) with hUldef
  have hUl : ∀ {T}, T ∈ Ul ↔ ∃ i < N, T = (ptsOf (List.range n) G).map (imgW w (RC i)) := by
    intro T
    rw [hUldef, List.mem_map]
    simp only [List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  have hUv : ∀ T ∈ Ul, Val n (ptsOf (List.range n) G).length T := by
    intro T hT
    obtain ⟨i, hi, rfl⟩ := hUl.1 hT
    refine ⟨by rw [List.length_map], fun x hx => ?_⟩
    rw [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact (hvc i hi).1 p (hoN p hp)
  have hclo : ∀ T ∈ Ul, ∀ s ∈ G, applyTab s T ∈ Ul := by
    intro T hT s hs
    obtain ⟨i, hi, rfl⟩ := hUl.1 hT
    obtain ⟨t, ht, rfl⟩ := hsG s hs
    rw [hstepU i hi t ht]
    exact hUl.2 ⟨_, (hst i hi t ht).1, rfl⟩
  have hkey : ∀ T ∈ Ul, ∀ V ∈ Ul, keyNat n (List.range n).length T =
      keyNat n (List.range n).length V → T = V := by
    intro T hT V hV e
    rw [keyNat_eq_iff (hUv T hT) (hUv V hV)] at e
    obtain ⟨a, ha, rfl⟩ := hUl.1 hT
    obtain ⟨b, hb, rfl⟩ := hUl.1 hV
    rw [hUinj a ha b hb fun q hq => by
      have := congrArg (fun l => l.getD q 0) e
      simp only [List.length_range, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq]
        at this
      rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, hUget a q hq,
        hUget b q hq] at this
      exact this]
  have hU0 : (ptsOf (List.range n) G).map (imgW w (RC 0)) = ptsOf (List.range n) G := by
    conv_rhs => rw [← List.map_id (ptsOf (List.range n) G)]
    apply List.map_congr_left
    intro p hp
    rw [hRC0, imgW_one hw (hoN p hp)]
    rfl
  have hoU : ptsOf (List.range n) G ∈ Ul := hUl.2 ⟨0, hN, hU0.symm⟩
  have hUnd : Ul.Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro a ha b hb e
    exact hUinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) fun q hq => by
      rw [← hUget a q hq, ← hUget b q hq, e]
  have hreach : ∀ A : List (List Nat), ptsOf (List.range n) G ∈ A →
      (∀ T ∈ A, T ∈ Ul → ∀ s ∈ G, applyTab s T ∈ A) → ∀ T ∈ Ul, T ∈ A := by
    intro A hoA hA T hT
    obtain ⟨i, hi, rfl⟩ := hUl.1 hT
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hU0]
        exact hoA
      · obtain ⟨h1, h2, h3⟩ := par_spec hpar hi hi0
        have hp := ih _ h1 (by omega) (hUl.2 ⟨_, by omega, rfl⟩)
        have e := hstepU (fieldT W PT i) (by omega) _ h2
        rw [h3] at e
        rw [← e]
        exact hA _ hp (hUl.2 ⟨_, by omega, rfl⟩) _ (by
          rw [getElem!_pos G _ (by omega)]
          exact List.getElem_mem _)
  have hUlen : Ul.length = N := by rw [hUldef, List.length_map, List.length_range]
  obtain ⟨h1, h2, h3⟩ := BS.Cl.bfs_closed fuel hGil hinv hUv hclo hkey hoU hUnd hreach
    (by rw [hUlen]; exact hfuel)
  exact ⟨h1, by rw [h2, hUlen], fun T => (h3 T).trans hUl⟩

end Entries

section Lists

variable {n w N : Nat} {RC : Nat → Nat} {mul : Nat → Nat → Nat}

@[expose] def Cor (n w N : Nat) (RC : Nat → Nat) (Zt : List (Array Nat)) (Zi : List Nat) : Prop :=
  (∀ z ∈ Zi, z < N) ∧ ∀ y, y ∈ Zt ↔ ∃ z ∈ Zi, y = tabC n w (RC z)

variable (hvc : ∀ i < N, VC n w (RC i)) (hinj : ∀ a < N, ∀ b < N, RC a = RC b → a = b)
  (hmul : ∀ a < N, ∀ b < N, mul a b < N ∧ RC (mul a b) = mulW n w (RC a) (RC b))

include hvc hinj in
theorem tab_eq_iff {a b : Nat} (ha : a < N) (hb : b < N) :
    tabC n w (RC a) = tabC n w (RC b) ↔ a = b :=
  ⟨fun h => hinj a ha b hb (tabC_inj (hvc a ha) (hvc b hb) h), fun h => by rw [h]⟩

include hvc hmul in
theorem compArr_rc {a b : Nat} (ha : a < N) (hb : b < N) :
    compArr (tabC n w (RC a)) (tabC n w (RC b)) = tabC n w (RC (mul a b)) := by
  rw [compArr_tabC (hvc a ha).1 (hvc b hb).1, (hmul a ha b hb).2]

include hvc hinj hmul in
theorem commIn_iff {Zt : List (Array Nat)} {Zi : List Nat} (hc : Cor n w N RC Zt Zi) {x s : Nat}
    (hx : x < N) (hs : s < N) :
    commIn Zt (tabC n w (RC x)) (tabC n w (RC s)) = true ↔
      ∃ z ∈ Zi, mul x s = mul z (mul s x) := by
  rw [commIn, List.any_eq_true]
  constructor
  · rintro ⟨zt, hzt, e⟩
    obtain ⟨z, hz, rfl⟩ := (hc.2 zt).1 hzt
    have hzN := hc.1 z hz
    rw [beq_iff_eq, compArr_rc hvc hmul hx hs, compArr_rc hvc hmul hs hx,
      compArr_rc hvc hmul hzN (hmul s hs x hx).1,
      tab_eq_iff hvc hinj (hmul x hx s hs).1 (hmul z hzN _ (hmul s hs x hx).1).1] at e
    exact ⟨z, hz, e⟩
  · rintro ⟨z, hz, e⟩
    have hzN := hc.1 z hz
    refine ⟨tabC n w (RC z), (hc.2 _).2 ⟨z, hz, rfl⟩, ?_⟩
    rw [beq_iff_eq, compArr_rc hvc hmul hx hs, compArr_rc hvc hmul hs hx,
      compArr_rc hvc hmul hzN (hmul s hs x hx).1, e]

include hvc hinj hmul in
theorem zstep_corr {FT G : List (Array Nat)} (hFT : ∀ y, y ∈ FT ↔ ∃ i < N, y = tabC n w (RC i))
    {gs : List Nat} (hgs : ∀ s ∈ gs, s < N) (hG : G = gs.map fun s => tabC n w (RC s))
    {Zt : List (Array Nat)} {Zi Z' : List Nat} (hc : Cor n w N RC Zt Zi)
    (hZ' : ∀ z ∈ Z', z < N)
    (hpass : ∀ x < N, zPass mul gs Zi x = Z'.contains x) :
    Cor n w N RC (zStep FT G Zt) Z' := by
  refine ⟨hZ', fun y => ?_⟩
  rw [zStep, List.mem_filter, hFT]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hall⟩
    refine ⟨x, ?_, rfl⟩
    rw [← List.contains_iff_mem, ← hpass x hx, zPass, allL_eq, List.all_eq_true]
    intro s hs
    rw [hG, List.all_eq_true] at hall
    have := hall _ (List.mem_map.2 ⟨s, hs, rfl⟩)
    rw [commIn_iff hvc hinj hmul hc hx (hgs s hs)] at this
    obtain ⟨z, hz, e⟩ := this
    rw [anyL_eq, List.any_eq_true]
    exact ⟨z, hz, P.beq_iff.2 e⟩
  · rintro ⟨x, hx, rfl⟩
    have hxN := hZ' x hx
    refine ⟨⟨x, hxN, rfl⟩, ?_⟩
    have hp := hpass x hxN
    rw [List.contains_iff_mem.2 hx, zPass, allL_eq, List.all_eq_true] at hp
    rw [hG, List.all_eq_true]
    intro st hst
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hst
    have := hp s hs
    rw [anyL_eq, List.any_eq_true] at this
    obtain ⟨z, hz, e⟩ := this
    exact (commIn_iff hvc hinj hmul hc hxN (hgs s hs)).2 ⟨z, hz, P.beq_iff.1 e⟩

include hvc hinj hmul in
theorem cen_corr {FT : List (Array Nat)} (hFT : ∀ y, y ∈ FT ↔ ∃ i < N, y = tabC n w (RC i))
    {Zt : List (Array Nat)} {Zi Z' : List Nat} (hc : Cor n w N RC Zt Zi)
    (hZ' : ∀ z ∈ Z', z < N) (hpass : ∀ x < N, cPass mul Zi x = Z'.contains x) :
    Cor n w N RC (cenList FT Zt) Z' := by
  have key : ∀ x < N, (Zt.all fun y => compArr (tabC n w (RC x)) y == compArr y (tabC n w (RC x)))
      = cPass mul Zi x := by
    intro x hx
    rw [cPass, allL_eq]
    apply Bool.eq_iff_iff.2
    rw [List.all_eq_true, List.all_eq_true]
    constructor
    · intro h z hz
      have hzN := hc.1 z hz
      have := h _ ((hc.2 _).2 ⟨z, hz, rfl⟩)
      rw [beq_iff_eq, compArr_rc hvc hmul hx hzN, compArr_rc hvc hmul hzN hx,
        tab_eq_iff hvc hinj (hmul x hx z hzN).1 (hmul z hzN x hx).1] at this
      exact P.beq_iff.2 this
    · intro h yt hyt
      obtain ⟨z, hz, rfl⟩ := (hc.2 yt).1 hyt
      have hzN := hc.1 z hz
      rw [beq_iff_eq, compArr_rc hvc hmul hx hzN, compArr_rc hvc hmul hzN hx,
        P.beq_iff.1 (h z hz)]
  refine ⟨hZ', fun y => ?_⟩
  rw [cenList, List.mem_filter, hFT]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hall⟩
    refine ⟨x, ?_, rfl⟩
    rw [← List.contains_iff_mem, ← hpass x hx, ← key x hx]
    exact hall
  · rintro ⟨x, hx, rfl⟩
    have hxN := hZ' x hx
    refine ⟨⟨x, hxN, rfl⟩, ?_⟩
    rw [key x hxN, hpass x hxN, List.contains_iff_mem]
    exact hx

include hvc in
theorem conj_corr {Zt : List (Array Nat)} {Zi : List Nat} (hc : Cor n w N RC Zt Zi) {a b : Nat}
    (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    (Zt.all fun q => Zt.contains (conjT (tabC n w a) (tabC n w b) q)) =
      allL (mapW RC Zi) (fun q => hasW (mapW RC Zi) (conjK n w a b q)) := by
  have hconj : ∀ z ∈ Zi, conjT (tabC n w a) (tabC n w b) (tabC n w (RC z)) =
      tabC n w (conjK n w a b (RC z)) := by
    intro z hz
    rw [conjT, compArr_tabC (hvc z (hc.1 z hz)).1 hb,
      compArr_tabC ha (vc_mul (hvc z (hc.1 z hz)).1 hb).1]
    rfl
  have hvk : ∀ z ∈ Zi, VC n w (conjK n w a b (RC z)) := fun z hz =>
    vc_mul ha (vc_mul (hvc z (hc.1 z hz)).1 hb).1
  have hmem : ∀ z ∈ Zi, (Zt.contains (tabC n w (conjK n w a b (RC z))) = true ↔
      ∃ z' ∈ Zi, conjK n w a b (RC z) = RC z') := by
    intro z hz
    rw [List.contains_iff_mem, hc.2]
    constructor
    · rintro ⟨z', hz', e⟩
      exact ⟨z', hz', tabC_inj (hvk z hz) (hvc z' (hc.1 z' hz')) e⟩
    · rintro ⟨z', hz', e⟩
      exact ⟨z', hz', by rw [e]⟩
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, allL_eq, List.all_eq_true, mapW_eq]
  constructor
  · intro h c hc'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc'
    have := h _ ((hc.2 _).2 ⟨z, hz, rfl⟩)
    rw [hconj z hz, hmem z hz] at this
    obtain ⟨z', hz', e⟩ := this
    rw [hasW_eq, List.contains_iff_mem, e]
    exact List.mem_map.2 ⟨z', hz', rfl⟩
  · intro h q hq
    obtain ⟨z, hz, rfl⟩ := (hc.2 q).1 hq
    have := h _ (List.mem_map.2 ⟨z, hz, rfl⟩)
    rw [hasW_eq, List.contains_iff_mem, List.mem_map] at this
    obtain ⟨z', hz', e⟩ := this
    rw [hconj z hz, hmem z hz]
    exact ⟨z', hz', e.symm⟩

include hvc in
theorem norm_corr {Zt : List (Array Nat)} {Zi : List Nat} (hc : Cor n w N RC Zt Zi) {a b : Nat}
    (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    normOK Zt (tabC n w a) (tabC n w b) = normK n w (mapW RC Zi) a b := by
  rw [normOK, normK, andB_eq, conj_corr hvc hc ha hb, conj_corr hvc hc hb ha]

include hvc in
theorem notNorm_corr {Zt : List (Array Nat)} {Zi : List Nat} (hc : Cor n w N RC Zt Zi)
    {a b : Nat} (ha : ∀ i < n, imgW w a i < n) (hb : ∀ i < n, imgW w b i < n) :
    notNormOK Zt (tabC n w a) (tabC n w b) = notNormK n w (mapW RC Zi) a b := by
  have h := conj_corr hvc hc ha hb
  rw [notNormOK, notNormK, anyL_eq]
  have e1 : (Zt.any fun q => !(Zt.contains (conjT (tabC n w a) (tabC n w b) q))) =
      !(Zt.all fun q => Zt.contains (conjT (tabC n w a) (tabC n w b) q)) := by
    rw [List.all_eq_not_any_not, Bool.not_not]
  have e2 : ((mapW RC Zi).any fun q => CFSG.KC.Ord.notB (hasW (mapW RC Zi) (conjK n w a b q))) =
      !(allL (mapW RC Zi) fun q => hasW (mapW RC Zi) (conjK n w a b q)) := by
    rw [allL_eq, List.all_eq_not_any_not, Bool.not_not]
    congr 1
  rw [e1, e2, h]

end Lists

theorem bfsCI_spec {n w W g N : Nat} {G : List Nat} {RC SR IS PT CT : Nat → Nat} {i : Nat}
    (h : bfsCI n w W g N G RC SR IS PT CT i = true) :
    SR i < N ∧ IS (SR i) = i ∧ (i + 1 < N → RC (IS i) < RC (IS (i + 1))) ∧
    (i = 0 → RC 0 = oneW n w) ∧
    (∀ t < g, fieldT W CT (i * (g + g) + t) < N ∧
      mulW n w (G.getD t 0) (RC i) = RC (fieldT W CT (i * (g + g) + t))) ∧
    (i = 0 ∨ (fieldT W PT i < i ∧ discT W g CT (fieldT W PT i) i < g)) := by
  rw [bfsCI] at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨P.blt_iff.1 h1, P.beq_iff.1 h2,
    fun hi => P.blt_iff.1 (impB_true h3 (P.blt_iff.2 hi)),
    fun hi => P.beq_iff.1 (impB_true h4 (P.beq_iff.2 hi)), fun t ht => ?_, ?_⟩
  · rw [rangeK_eq', allL_eq, List.all_eq_true] at h5
    have := h5 t (List.mem_range.2 ht)
    simp only [Bool.and_eq_true] at this
    obtain ⟨k1, k2, -⟩ := this
    rw [getK_eq] at k2
    exact ⟨P.blt_iff.1 k1, P.beq_iff.1 k2⟩
  · rw [orB_eq, Bool.or_eq_true] at h6
    rcases h6 with h6 | h6
    · exact Or.inl (P.beq_iff.1 h6)
    · simp only [Bool.and_eq_true] at h6
      exact Or.inr ⟨P.blt_iff.1 h6.1, P.blt_iff.1 h6.2.1⟩

theorem incL_go {N : Nat} : ∀ (l : List Nat) (lo : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun x _ ih lo => CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.ble lo x) (Nat.blt x N)) (ih (Nat.succ x))) l lo = true →
    ∀ z ∈ l, z < N
  | [], _, _, z, hz => by simp at hz
  | x :: l, lo, h, z, hz => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.ble lo x) (Nat.blt x N)) (List.rec (motive := fun _ => Nat → Bool)
      (fun _ => true) (fun x _ ih lo => CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.ble lo x) (Nat.blt x N)) (ih (Nat.succ x)))
        l (x + 1)) = true at h
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hz with rfl | hz
    · exact P.blt_iff.1 h.1.2
    · exact incL_go l _ h.2 z hz

theorem incL_lt {N : Nat} {l : List Nat} (h : incL N l = true) : ∀ z ∈ l, z < N :=
  incL_go l 0 h

theorem eqBH_eq {a b : Bool} (h : eqBH a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem tabC_congr {n w a b : Nat} (h : ∀ i < n, imgW w a i = imgW w b i) :
    tabC n w a = tabC n w b := by
  rw [tabC, tabC]
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

theorem tabC_one {n w : Nat} (hw : n ≤ 2 ^ w) : tabC n w (oneW n w) = Array.range n := by
  rw [tabC, List.map_congr_left (fun i hi => imgW_one hw (List.mem_range.1 hi)), List.map_id']
  rw [← Array.toList_range, Array.toArray_toList]

end CFSG.KC.LQT.XH.Pf

end

public section

namespace CFSG.KC.LQT.XH

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.RB
open CFSG.KC.LQT.FS
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.RF.Pf CFSG.KC.LQT.BS.Pf
open CFSG.KC.LQT.XH.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem x1H_sound_proved {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (ta tb : List Nat)
    (prog qp wprog : List (Nat × Nat)) (gn gin hn hin an bn k fuel N : Nat)
    (Gs Z1L Z2L Z3L QcL : List Nat) (GC GIC HC HIC : Nat) (RC SR IS PT CT : Nat → Nat)
    (KB LB KS LS : Nat)
    (h : x1HH n w ta tb prog qp gn gin hn hin k fuel N Gs Z1L Z2L Z3L QcL GC GIC HC HIC = true)
    (hb : ∀ c < KB, x1HB n w W qp.length N Gs RC SR IS PT CT (c * LB) LB = true)
    (hs : ∀ c < KS, x1HS W qp.length N PT CT Z1L Z2L Z3L QcL (c * LS) LS = true)
    (hcov : N ≤ KB * LB ∧ N ≤ KS * LS)
    (hN : x1HN n w RC Z1L QcL GC GIC HC HIC = true)
    (hW : x1HW n w wprog GC HC an bn ta tb = true) :
    qpOK n (slpTabsA ta.toArray tb.toArray prog) qp ∧
    BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
      (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!)
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 ∧
    (bfsEnumB n (List.range n) (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1.size = 2 ^ k ∧
    (gn < (slpTabsA ta.toArray tb.toArray prog).size ∧
      gin < (slpTabsA ta.toArray tb.toArray prog).size ∧
      hn < (slpTabsA ta.toArray tb.toArray prog).size ∧
      hin < (slpTabsA ta.toArray tb.toArray prog).size ∧
      an < (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog).size ∧
      bn < (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog).size) ∧
    invPairOK (Array.range n) (slpTabsA ta.toArray tb.toArray prog)[gn]!
      (slpTabsA ta.toArray tb.toArray prog)[gin]! = true ∧
    invPairOK (Array.range n) (slpTabsA ta.toArray tb.toArray prog)[hn]!
      (slpTabsA ta.toArray tb.toArray prog)[hin]! = true ∧
    normOK (zSeries (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 1)
      (slpTabsA ta.toArray tb.toArray prog)[gn]! (slpTabsA ta.toArray tb.toArray prog)[gin]! =
        true ∧
    normOK (cenList (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (zSeries (fullTables n (bfsEnumB n (List.range n)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 3))
      (slpTabsA ta.toArray tb.toArray prog)[hn]! (slpTabsA ta.toArray tb.toArray prog)[hin]! =
        true ∧
    notNormOK (cenList (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (zSeries (fullTables n (bfsEnumB n (List.range n)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
          (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 3))
      (slpTabsA ta.toArray tb.toArray prog)[gn]! (slpTabsA ta.toArray tb.toArray prog)[gin]! =
        true ∧
    notNormOK (zSeries (fullTables n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!) (Array.range n) 1)
      (slpTabsA ta.toArray tb.toArray prog)[hn]! (slpTabsA ta.toArray tb.toArray prog)[hin]! =
        true ∧
    (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog)[an]! = ta.toArray ∧
    (slpTabsA (slpTabsA ta.toArray tb.toArray prog)[gn]!
        (slpTabsA ta.toArray tb.toArray prog)[hn]! wprog)[bn]! = tb.toArray := by
  rw [x1HH] at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hta, htb, hso, hR⟩ := h
  obtain ⟨hlen, hrep⟩ := slpW_rep hw hta htb hso
  generalize slpTabsA ta.toArray tb.toArray prog = T at hlen hrep ⊢
  generalize slpW n w (codeK w ta) (codeK w tb) prog = R at hlen hrep hR
  rw [x1HR] at hR
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hR
  obtain ⟨hqp, hGs, hgn, hgin, hhn, hhin, hGC, hGIC, hHC, hHIC, hg1, hg2, hh1, hh2, hNk, hNf,
    hi1, hi2, hi3, hi4⟩ := hR
  rw [P.blt_iff, hlen] at hgn hgin hhn hhin
  rw [P.beq_iff] at hGC hGIC hHC hHIC hg1 hg2 hh1 hh2 hNk
  have hNf' := Nat.le_of_ble_eq_true hNf
  rw [eqLW_iff, fstN_eq] at hGs
  rw [qpW, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, allA_eq, allA_eq,
    List.all_eq_true, List.all_eq_true] at hqp
  obtain ⟨hq1, hq2, -⟩ := hqp
  have hq1' : ∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size := by
    intro p hp
    have := hq1 p hp
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, hlen] at this
    exact this
  have hinvq : ∀ a ∈ qp, ∀ q < n, img T[a.2]! (img T[a.1]! q) = q := fun a ha =>
    rep_inv (hrep a.1 (hq1' a ha).1) (hrep a.2 (hq1' a ha).2) hw
      (Nat.eq_of_beq_eq_true (by simpa using hq2 a ha))
  set G := qp.map fun p => T[p.1]! with hGdef
  set Gi := qp.map fun p => T[p.2]! with hGidef
  have hGl : G.length = qp.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = G.length := by rw [hGidef, hGl, List.length_map]
  have hGj : ∀ j (hj : j < qp.length), G[j]! = T[qp[j].1]! := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < qp.length), Gi[j]! = T[qp[j].2]! := by
    intro j hj
    rw [getElem!_pos Gi j (by omega)]
    simp only [hGidef, List.getElem_map]
  have hGst : ∀ t (ht : t < qp.length), Gs.getD t 0 = nodeK R qp[t].1 := by
    intro t ht
    rw [hGs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]
    rfl
  have hGrep : ∀ t < qp.length, Rep n w (Gs.getD t 0) G[t]! := by
    intro t ht
    rw [hGst t ht, hGj t ht]
    exact hrep _ (hq1' _ (List.getElem_mem ht)).1
  have hGf : ∀ t < qp.length, ∀ i < n, imgW w (Gs.getD t 0) i < n :=
    fun t ht => rep_fields (hGrep t ht)
  have hinv : ∀ j < G.length, ∀ q < n, img Gi[j]! (img G[j]! q) = q := by
    intro j hj q hq
    rw [hGl] at hj
    rw [hGj j hj, hGij j hj]
    exact hinvq _ (List.getElem_mem hj) q hq
  have hN0 : 0 < N := by
    rw [hNk]
    exact Nat.two_pow_pos k
  have hbi : ∀ i < N, bfsCI n w W qp.length N Gs RC SR IS PT CT i = true := by
    intro i hi
    have hLB : 0 < LB := by
      rcases Nat.eq_zero_or_pos LB with h0 | h0
      · have := hcov.1
        rw [h0, Nat.mul_zero] at this
        omega
      · exact h0
    have hc : i / LB < KB := by
      rw [Nat.div_lt_iff_lt_mul hLB]
      exact Nat.lt_of_lt_of_le hi hcov.1
    have := allR_true (hb _ hc) (i % LB) (Nat.mod_lt _ hLB)
    rw [Nat.div_add_mod'] at this
    exact impB_true this (P.blt_iff.2 hi)
  have hRC0 : RC 0 = oneW n w := (bfsCI_spec (hbi 0 hN0)).2.2.2.1 rfl
  have hst : ∀ i < N, ∀ t < qp.length, fieldT W CT (i * (qp.length + qp.length) + t) < N ∧
      mulW n w (Gs.getD t 0) (RC i) = RC (fieldT W CT (i * (qp.length + qp.length) + t)) :=
    fun i hi => (bfsCI_spec (hbi i hi)).2.2.2.2.1
  have hpar : ∀ i < N, 0 < i → fieldT W PT i < i ∧
      discT W qp.length CT (fieldT W PT i) i < qp.length := by
    intro i hi hi0
    rcases (bfsCI_spec (hbi i hi)).2.2.2.2.2 with h0 | h0
    · omega
    · exact h0
  have hmono : ∀ a b, a < b → b < N → RC (IS a) < RC (IS b) := by
    intro a b hab hb'
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact Nat.lt_trans (ih h' (by omega)) ((bfsCI_spec (hbi b (by omega))).2.2.1 hb')
      · exact (bfsCI_spec (hbi a (by omega))).2.2.1 hb'
  have hinj : ∀ a < N, ∀ b < N, RC a = RC b → a = b := by
    intro a ha b hb' e
    obtain ⟨sa, ia⟩ := (bfsCI_spec (hbi a ha))
    obtain ⟨sb, ib⟩ := (bfsCI_spec (hbi b hb'))
    rw [← ia.1, ← ib.1] at e
    rcases Nat.lt_trichotomy (SR a) (SR b) with h' | h' | h'
    · exact absurd e (Nat.ne_of_lt (hmono _ _ h' sb))
    · rw [← ia.1, ← ib.1, h']
    · exact absurd e.symm (Nat.ne_of_lt (hmono _ _ h' sa))
  have hvc := rc_vc hw hGf hRC0 hst hpar
  obtain ⟨hBE, hsz, hmemX⟩ := x1_bfs hw hGf hRC0 hst hpar hGl hGrep hGil hinv hinj hN0 fuel hNf'
  generalize bfsEnumB n (List.range n) G Gi fuel = X at hBE hsz hmemX ⊢
  have hFT : ∀ y, y ∈ fullTables n X.1 ↔ ∃ i < N, y = tabC n w (RC i) := by
    intro y
    have htake : ∀ i, (((ptsOf (List.range n) G).map (imgW w (RC i))).take n).toArray =
        tabC n w (RC i) := by
      intro i
      rw [← List.map_take, ptsOf, List.take_left' (List.length_range)]
      rfl
    rw [fullTables, List.mem_map]
    constructor
    · rintro ⟨T', hT', rfl⟩
      obtain ⟨i, hi, rfl⟩ := (hmemX T').1 hT'
      exact ⟨i, hi, htake i⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, (hmemX _).2 ⟨i, hi, rfl⟩, htake i⟩
  have hmul : ∀ a < N, ∀ b < N, mulT W qp.length N PT CT a b < N ∧
      RC (mulT W qp.length N PT CT a b) = mulW n w (RC a) (RC b) :=
    fun a ha b hb' => mulG_rc hw hGf hRC0 hst hpar N a b (by omega) ha hb'
  have hgs : ∀ s ∈ mapW (fieldT W CT) (rangeK qp.length), s < N := by
    intro s hs
    rw [mapW_eq, rangeK_eq', List.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have := (hst 0 hN0 t (List.mem_range.1 ht)).1
    rwa [Nat.zero_mul, Nat.zero_add] at this
  have hGeq : G = (mapW (fieldT W CT) (rangeK qp.length)).map fun s => tabC n w (RC s) := by
    rw [mapW_eq, rangeK_eq', List.map_map]
    apply List.ext_getElem (by simp [hGl])
    intro t h1 h2
    have ht : t < qp.length := by omega
    rw [← getElem!_pos G t h1]
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    have e := (hst 0 hN0 t ht).2
    rw [Nat.zero_mul, Nat.zero_add, hRC0] at e
    rw [← e, rep_unique (hGrep t ht) (rep_tabC (hGf t ht))]
    exact tabC_congr fun i hi => by rw [imgW_mulW hi, imgW_one hw hi]
  have hsx : ∀ x < N, allBs [eqBH (zPass (mulT W qp.length N PT CT)
      (mapW (fieldT W CT) (rangeK qp.length)) [0] x) (hasW Z1L x),
      eqBH (zPass (mulT W qp.length N PT CT) (mapW (fieldT W CT) (rangeK qp.length)) Z1L x)
        (hasW Z2L x),
      eqBH (zPass (mulT W qp.length N PT CT) (mapW (fieldT W CT) (rangeK qp.length)) Z2L x)
        (hasW Z3L x),
      eqBH (cPass (mulT W qp.length N PT CT) Z3L x) (hasW QcL x)] = true := by
    intro x hx
    have hLS : 0 < LS := by
      rcases Nat.eq_zero_or_pos LS with h0 | h0
      · have := hcov.2
        rw [h0, Nat.mul_zero] at this
        omega
      · exact h0
    have hc : x / LS < KS := by
      rw [Nat.div_lt_iff_lt_mul hLS]
      exact Nat.lt_of_lt_of_le hx hcov.2
    have hsc := hs _ hc
    rw [x1HS] at hsc
    dsimp only at hsc
    have := allR_true hsc (x % LS) (Nat.mod_lt _ hLS)
    rw [Nat.div_add_mod'] at this
    exact impB_true this (P.blt_iff.2 hx)
  have hpass : ∀ x < N,
      zPass (mulT W qp.length N PT CT) (mapW (fieldT W CT) (rangeK qp.length)) [0] x =
        Z1L.contains x ∧
      zPass (mulT W qp.length N PT CT) (mapW (fieldT W CT) (rangeK qp.length)) Z1L x =
        Z2L.contains x ∧
      zPass (mulT W qp.length N PT CT) (mapW (fieldT W CT) (rangeK qp.length)) Z2L x =
        Z3L.contains x ∧
      cPass (mulT W qp.length N PT CT) Z3L x = QcL.contains x := by
    intro x hx
    have := hsx x hx
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at this
    obtain ⟨e1, e2, e3, e4⟩ := this
    rw [← hasW_eq, ← hasW_eq, ← hasW_eq, ← hasW_eq]
    exact ⟨eqBH_eq e1, eqBH_eq e2, eqBH_eq e3, eqBH_eq e4⟩
  have c0 : Cor n w N RC [Array.range n] [0] := by
    refine ⟨fun z hz => by simp at hz; omega, fun y => ?_⟩
    simp only [List.mem_singleton, exists_eq_left]
    rw [hRC0, tabC_one hw]
  have c1 := zstep_corr hvc hinj hmul hFT hgs hGeq c0 (incL_lt hi1) fun x hx => (hpass x hx).1
  have c2 := zstep_corr hvc hinj hmul hFT hgs hGeq c1 (incL_lt hi2) fun x hx => (hpass x hx).2.1
  have c3 := zstep_corr hvc hinj hmul hFT hgs hGeq c2 (incL_lt hi3) fun x hx =>
    (hpass x hx).2.2.1
  have cq := cen_corr hvc hinj hmul hFT c3 (incL_lt hi4) fun x hx => (hpass x hx).2.2.2
  have hz1 : zSeries (fullTables n X.1) G (Array.range n) 1 =
      zStep (fullTables n X.1) G [Array.range n] := rfl
  have hz3 : zSeries (fullTables n X.1) G (Array.range n) 3 =
      zStep (fullTables n X.1) G (zStep (fullTables n X.1) G
        (zStep (fullTables n X.1) G [Array.range n])) := rfl
  have htg : T[gn]! = tabC n w GC := by
    rw [hGC]
    exact rep_unique (hrep gn hgn) (rep_tabC (rep_fields (hrep gn hgn)))
  have htgi : T[gin]! = tabC n w GIC := by
    rw [hGIC]
    exact rep_unique (hrep gin hgin) (rep_tabC (rep_fields (hrep gin hgin)))
  have hth : T[hn]! = tabC n w HC := by
    rw [hHC]
    exact rep_unique (hrep hn hhn) (rep_tabC (rep_fields (hrep hn hhn)))
  have hthi : T[hin]! = tabC n w HIC := by
    rw [hHIC]
    exact rep_unique (hrep hin hhin) (rep_tabC (rep_fields (hrep hin hhin)))
  have fGC : ∀ i < n, imgW w GC i < n := by rw [hGC]; exact rep_fields (hrep gn hgn)
  have fGIC : ∀ i < n, imgW w GIC i < n := by rw [hGIC]; exact rep_fields (hrep gin hgin)
  have fHC : ∀ i < n, imgW w HC i < n := by rw [hHC]; exact rep_fields (hrep hn hhn)
  have fHIC : ∀ i < n, imgW w HIC i < n := by rw [hHIC]; exact rep_fields (hrep hin hhin)
  rw [x1HN] at hN
  dsimp only at hN
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hN
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hN
  rw [x1HW, andB_eq, Bool.and_eq_true] at hW
  obtain ⟨hwso, hW⟩ := hW
  dsimp only at hW
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at hW
  obtain ⟨ha1, hb1, ha2, hb2⟩ := hW
  have hslp := slpGo_rep hw wprog [HC, GC] #[T[gn]!, T[hn]!] rfl (by
      intro j hj
      rcases j with _ | _ | j
      · rw [hGC]
        exact hrep gn hgn
      · rw [hHC]
        exact hrep hn hhn
      · simp at hj) (slpOKK_spec' wprog 2 hwso)
  rw [← slpW_eq] at hslp
  obtain ⟨hsl1, hsl2⟩ := hslp
  rw [lenA_eq, hsl1, P.blt_iff] at ha1 hb1
  rw [P.beq_iff] at ha2 hb2
  have hsa := hsl2 an ha1
  have hsb := hsl2 bn hb1
  rw [ha2] at hsa
  rw [hb2] at hsb
  refine ⟨fun p hp => ⟨(hq1' p hp).1, (hq1' p hp).2, hinvq p hp⟩, hBE, by rw [hsz]; exact hNk,
    ⟨hgn, hgin, hhn, hhin, ha1, hb1⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    rep_unique hsa (rep_codeK hw hta), rep_unique hsb (rep_codeK hw htb)⟩
  · rw [invPairOK, htg, htgi, compArr_tabC fGC fGIC, compArr_tabC fGIC fGC, hg1, hg2,
      tabC_one hw]
    simp
  · rw [invPairOK, hth, hthi, compArr_tabC fHC fHIC, compArr_tabC fHIC fHC, hh1, hh2,
      tabC_one hw]
    simp
  · rw [hz1, htg, htgi, norm_corr hvc c1 fGC fGIC]
    exact hn1
  · rw [hz3, hth, hthi, norm_corr hvc cq fHC fHIC]
    exact hn2
  · rw [hz3, htg, htgi, notNorm_corr hvc cq fGC fGIC]
    exact hn3
  · rw [hz1, hth, hthi, notNorm_corr hvc c1 fHC fHIC]
    exact hn4

end CFSG.KC.LQT.XH

end
