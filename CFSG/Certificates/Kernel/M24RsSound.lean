module

public import Certificates.Data.Kernel.M24Rs
public import Mathlib.GroupTheory.Index
import CFSG.Certificates.Kernel.M24RsGroup

public section

namespace CFSG.KM24

@[expose] def letP {G : Type*} [Group G] (gen : ℕ → G) (l : ℕ) : G :=
  if l % 2 = 0 then gen (l / 2) else (gen (l / 2))⁻¹

@[expose] noncomputable def pval {G : Type*} [Group G] (gen : ℕ → G) (x : ℕ) : G :=
  ((List.range (pn x)).map fun i => letP gen (lt (pw x) i)).prod

theorem lettersLt_spec {R : List ℕ} {k2 : ℕ} (h : lettersLt R k2 = true) :
    ∀ x ∈ R, ∀ i < pn x, lt (pw x) i < k2 := by
  induction R with
  | nil => intro x hx; simp at hx
  | cons y R ih =>
    intro x hx
    change mAnd _ (lettersLt R k2) = true at h
    rw [RS.mAnd_iff] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · intro i hi
      exact (RS.blt_iff _ _).1 ((RS.natRec_and_iff _).1 h.1 i hi)
    · exact ih h.2 x hx

theorem rsOk_sound {T P k2 nc : ℕ} {R0 A0 : List ℕ} {G0 : ℕ}
    {steps : List (ℕ × (ℕ × (List ℕ × ℕ)))} {N : ℕ} {Rn : List ℕ} {ng kq : ℕ}
    (hok : rsOk T P k2 nc R0 A0 G0 steps N Rn ng kq = true)
    {G : Type*} [Group G] (gen : ℕ → G) (hrels : ∀ r ∈ R0, pval gen r = 1) :
    ∃ h : ℕ → G, (∀ r ∈ Rn, pval h r = 1) ∧
      Subgroup.closure (h '' {i | i < kq}) ≤ Subgroup.closure (gen '' {g | 2 * g < k2}) ∧
      (Subgroup.closure (h '' {i | i < kq})).relIndex
          (Subgroup.closure (gen '' {g | 2 * g < k2})) ≠ 0 ∧
      (Subgroup.closure (h '' {i | i < kq})).relIndex
          (Subgroup.closure (gen '' {g | 2 * g < k2})) ≤ nc := by
  open CFSG.KM24.RS in
  have pval_eq : ∀ (f : ℕ → G) (x : ℕ), pval f x = lv f (wl (pw x) (pn x)) := by
    intro f x
    simp only [pval, lv, wl, List.map_map]
    rfl
  classical
  unfold rsOk at hok
  simp only [RS.mAnd_iff, RS.beq_iff, RS.blt_iff] at hok
  obtain ⟨hk2, hnc, hb, hlet, hinit, hchain⟩ := hok
  change k2 % 2 = 0 at hk2
  change nc * k2 < 32768 at hb
  unfold chkInit at hinit
  rw [RS.mAnd_iff, RS.mAnd_iff, RS.beq_iff] at hinit
  obtain ⟨ht, hG0, htr⟩ := hinit
  set sv := RS.sch T P k2 gen
  have hB15 : nc * k2 ≤ 32768 := by omega
  have hR0 := lettersLt_spec hlet
  have hinv0 : RS.Inv sv (nc * k2) (RS.K0 T P k2 nc gen) A0 G0 := by
    generalize hat : allTraces T P k2 nc R0 = atr at htr
    obtain ⟨ok, L⟩ := atr
    dsimp only at htr
    rw [RS.mAnd_iff] at htr
    obtain ⟨hok, hL⟩ := htr
    have hmem := RS.allTraces_mem (T := T) (P := P) (k2 := k2) (nc := nc) (R := R0)
    rw [hat] at hmem
    rw [← RS.eqRL_eq hL]
    refine ⟨fun y hy => ?_, fun j hj => ?_, ?_⟩
    · obtain ⟨x, hx, hc⟩ := hmem hok y hy
      rw [← hG0]
      rcases List.mem_append.1 hx with hx | hx
      · exact RS.closes_relOK ht hb gen (hR0 x hx) (by rw [← pval_eq]; exact hrels x hx) hc
      · obtain ⟨l, hl, rfl⟩ := RS.invWords_mem k2 x hx
        have hl16 : l < 2 ^ 16 := by
          have : k2 ≤ nc * k2 := Nat.le_mul_of_pos_left _ hnc
          omega
        have e : Nat.lor l (Nat.shiftLeft (Nat.xor l 1) 16) = RS.enc [l, l ^^^ 1] := by
          change l ||| ((l ^^^ 1) <<< 16) = _
          rw [RS.or_shift hl16]
          simp [RS.enc]
        have hok2 : RS.Ok16 [l, l ^^^ 1] := by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact hl16
          · exact RS.xor1_lt_pow hl16
        have hpw : pw (pk (Nat.lor l (Nat.shiftLeft (Nat.xor l 1) 16)) 2) = RS.enc [l, l ^^^ 1] := by
          rw [RS.pw_pk (by decide), e]
        have hpn : pn (pk (Nat.lor l (Nat.shiftLeft (Nat.xor l 1) 16)) 2) = 2 := RS.pn_pk (by decide)
        have hwl : RS.wl (RS.enc [l, l ^^^ 1]) 2 = [l, l ^^^ 1] := RS.wl_enc hok2
        refine RS.closes_relOK ht hb gen ?_ ?_ hc
        · rw [hpw, hpn]
          intro i hi
          rw [RS.lt_enc hok2]
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · exact hl
          · exact RS.xor1_lt hk2 hl
        · rw [hpw, hpn, hwl, RS.lv_cons, RS.lv_singleton, RS.ltv_xor, mul_inv_cancel]
    · rw [← hG0, RS.gens_testBit] at hj
      exact hj.1
    · unfold RS.K0
      rw [Subgroup.closure_le]
      rintro _ ⟨id, hid, rfl⟩
      have hid' : id < nc * k2 := hid
      have hk0 : 0 < k2 := by
        rcases Nat.eq_zero_or_pos k2 with h0 | h0
        · rw [h0, Nat.mul_zero] at hid'
          omega
        · exact h0
      have hc : id / k2 < nc := (Nat.div_lt_iff_lt_mul hk0).2 hid'
      have hl : id % k2 < k2 := Nat.mod_lt _ hk0
      have e : id / k2 * k2 + id % k2 = id := by rw [Nat.mul_comm]; exact Nat.div_add_mod id k2
      cases htree : isTree P (id / k2) (id % k2) (t8 T id)
      · apply Subgroup.subset_closure
        refine ⟨id, ?_, rfl⟩
        change G0.testBit id = true
        rw [← hG0, RS.gens_testBit]
        exact ⟨hid', htree⟩
      · have h1 : RS.sch T P k2 gen id = 1 := by
          have := RS.sch_tree ht gen hc hl (by rw [e]; exact htree)
          rwa [e] at this
        rw [h1]
        exact Subgroup.one_mem _
  obtain ⟨L, Gf, ⟨hA, hBd, hK⟩, hnext⟩ := RS.rsChain_inv hB15 steps hinv0 hchain
  rw [RS.chkNext_eq, RS.mAnd_iff, RS.chkRen_eq] at hnext
  obtain ⟨hren, hnx⟩ := hnext
  generalize hcr : RS.crRec N Gf kq ng = cr at hren
  obtain ⟨ok, im⟩ := cr
  dsimp only at hren
  rw [RS.mAnd_iff, RS.mAnd_iff, RS.blt_iff, RS.beq_iff] at hren
  obtain ⟨hok, hGf, him⟩ := hren
  obtain ⟨c1, c2, c3⟩ := RS.crRec_spec N Gf kq ng (by rw [hcr]; exact hok)
  rw [hcr] at c3
  dsimp only at c3
  have hGf' : Gf < 2 ^ ng := by
    have : Nat.shiftLeft 1 ng = 2 ^ ng := by
      change 1 <<< ng = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rwa [this] at hGf
  have him' : im = 2 ^ kq - 1 := by
    rw [him]
    change (1 <<< kq) - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hlive_ng : ∀ g, Gf.testBit g = true → g < ng := by
    intro g hg
    by_contra hng
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hGf' (Nat.pow_le_pow_right (by decide)
      (by omega)))] at hg
    exact absurd hg (by decide)
  have hsurj : ∀ t < kq, ∃ g, Gf.testBit g = true ∧ lt N g - 1 = t ∧ 0 < lt N g := by
    intro t ht
    have : im.testBit t = true := by rw [him', Nat.testBit_two_pow_sub_one]; simpa using ht
    obtain ⟨g, hg, hl, he⟩ := (c3 t).1 this
    exact ⟨g, hl, he, (c1 g hg hl).1⟩
  let hv : ℕ → G := fun t =>
    if hx : ∃ g, Gf.testBit g = true ∧ lt N g - 1 = t ∧ 0 < lt N g then sv (Classical.choose hx) else 1
  have hv_eq : ∀ g, Gf.testBit g = true → hv (lt N g - 1) = sv g := by
    intro g hg
    have hng := hlive_ng g hg
    have hx : ∃ g', Gf.testBit g' = true ∧ lt N g' - 1 = lt N g - 1 ∧ 0 < lt N g' :=
      ⟨g, hg, rfl, (c1 g hng hg).1⟩
    simp only [hv, dite_eq_left hx]
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hx
    congr 1
    have h4 := (c1 g hng hg).1
    exact c2 _ (hlive_ng _ h1) g hng h1 hg (by omega)
  have hkq : kq ≤ nc * k2 := by
    classical
    have hinj : Set.InjOn (fun t => if hx : ∃ g, Gf.testBit g = true ∧ lt N g - 1 = t ∧ 0 < lt N g
        then Classical.choose hx else 0) (Finset.range kq : Set ℕ) := by
      intro t1 ht1 t2 ht2 he
      have ht1' : t1 < kq := Finset.mem_range.1 ht1
      have ht2' : t2 < kq := Finset.mem_range.1 ht2
      have hx1 := hsurj t1 ht1'
      have hx2 := hsurj t2 ht2'
      simp only [dite_eq_left hx1, dite_eq_left hx2] at he
      have s1 := Classical.choose_spec hx1
      have s2 := Classical.choose_spec hx2
      rw [← s1.2.1, ← s2.2.1, he]
    have hmaps : Set.MapsTo (fun t => if hx : ∃ g, Gf.testBit g = true ∧ lt N g - 1 = t ∧ 0 < lt N g
        then Classical.choose hx else 0) (Finset.range kq : Set ℕ) (Finset.range (nc * k2) : Set ℕ) := by
      intro t ht
      have hx := hsurj t (Finset.mem_range.1 ht)
      simp only [dite_eq_left hx, Finset.coe_range, Set.mem_Iio]
      exact hBd _ (Classical.choose_spec hx).1
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa using this
  refine ⟨hv, ?_, ?_, ?_⟩
  ·
    intro r hr
    obtain ⟨ha, hha, hrok, rfl⟩ := RS.nxF_spec N Gf L Rn hnx r hr
    obtain ⟨acc, hacc, hal, haok, hav, halet⟩ := hA ha hha
    have hpw : pw ha = RS.enc acc := by rw [hacc, RS.pw_pk hal]
    have hpn : pn ha = acc.length := by rw [hacc, RS.pn_pk hal]
    rw [hpw, hpn] at hrok ⊢
    have hbound : ∀ l, Gf.testBit (l / 2) = true → 0 < lt N (l / 2) → RS.renL N l < 2 ^ 16 := by
      intro l hl hN
      have := (c1 _ (hlive_ng _ hl) hl).2
      unfold RS.renL
      have := Nat.mod_lt l (by decide : 0 < 2)
      omega
    rw [RS.rename_eq] at hrok ⊢
    obtain ⟨hr1, hr2⟩ := RS.rnRec_spec N Gf (RS.enc acc) hbound acc.length hrok
    rw [hr2, RS.wl_enc haok]
    have hMok : RS.Ok16 (acc.map (RS.renL N)) := by
      intro d hd
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hd
      obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.1 hl
      have := hr1 i hi
      rw [RS.lt_enc haok, RS.getD_of_lt hi, hli] at this
      exact hbound l this.1 this.2
    have hlen : (acc.map (RS.renL N)).length = acc.length := List.length_map _
    rw [← hlen, pval_eq, RS.pw_pk (by rw [hlen]; exact hal), RS.pn_pk (by rw [hlen]; exact hal),
      RS.wl_enc hMok]
    rw [← hav]
    unfold RS.lv
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro l hl
    obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.1 hl
    have hli' := hr1 i hi
    rw [RS.lt_enc haok, RS.getD_of_lt hi, hli] at hli'
    obtain ⟨hlg, hlN⟩ := hli'
    simp only [Function.comp]
    unfold RS.renL RS.ltv
    have e1 : (2 * (lt N (l / 2) - 1) + l % 2) / 2 = lt N (l / 2) - 1 := by omega
    have e2 : (2 * (lt N (l / 2) - 1) + l % 2) % 2 = l % 2 := by omega
    rw [e1, e2, hv_eq _ hlg]
  ·
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨t, htk, rfl⟩
    have ht' : t < kq := htk
    obtain ⟨g, hg, he, hN⟩ := hsurj t ht'
    rw [← he, hv_eq g hg]
    exact RS.sch_mem ht hk2 (fun g hg => Subgroup.subset_closure (Set.mem_image_of_mem gen hg))
      (hBd g hg)
  · have hle : RS.K0 T P k2 nc gen ≤ Subgroup.closure (hv '' {i | i < kq}) := by
      refine hK.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨g, hg, rfl⟩
      have hg' : Gf.testBit g = true := hg
      apply Subgroup.subset_closure
      refine ⟨lt N g - 1, ?_, hv_eq g hg'⟩
      have := c1 g (hlive_ng g hg') hg'
      change lt N g - 1 < kq
      omega
    obtain ⟨hne, hle'⟩ := RS.cover_K0 ht hnc hk2 gen
    refine ⟨?_, ?_⟩
    · intro h0
      apply hne
      obtain ⟨c, hc⟩ := Subgroup.relIndex_dvd_of_le_left _ hle
      rw [hc, h0, Nat.zero_mul]
    · exact (Subgroup.relIndex_le_of_le_left hle hne).trans hle'

end CFSG.KM24

end
