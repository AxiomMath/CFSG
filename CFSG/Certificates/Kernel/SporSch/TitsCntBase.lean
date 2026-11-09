module

public import Certificates.Data.Kernel.SporSch.TitsCnt
public import CFSG.Certificates.Kernel.SporSch.TitsInvSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.BaseSep
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def IsTr5 (LR TR : Nat → Nat) (t0 t1 t2 t3 t4 : Nat) : Prop :=
  (∃ a < rcnt (LR 0), t0 = trAt 1755 (1755 * 11) LR TR 0 a) ∧
  (∃ a < rcnt (LR 1), t1 = trAt 1755 (1755 * 11) LR TR 1 a) ∧
  (∃ a < rcnt (LR 2), t2 = trAt 1755 (1755 * 11) LR TR 2 a) ∧
  (∃ a < rcnt (LR 3), t3 = trAt 1755 (1755 * 11) LR TR 3 a) ∧
  (∃ a < rcnt (LR 4), t4 = trAt 1755 (1755 * 11) LR TR 4 a)

@[expose] def Agrees (LR TR : Nat → Nat) (P : Nat → Nat → Nat → Nat → Nat → Bool)
    (p : Array Nat → Bool) : Prop :=
  ∀ t0 t1 t2 t3 t4, IsTr5 LR TR t0 t1 t2 t3 t4 →
    P t0 t1 t2 t3 t4 = p (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))

section Mask

variable {kS BP M : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}

private theorem isTr5_code {k : Nat} (hk : k < tot5 LR) :
    IsTr5 LR TR
      (trAt 1755 (1755 * 11) LR TR 0 (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1)))
      (trAt 1755 (1755 * 11) LR TR 1 (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1)))
      (trAt 1755 (1755 * 11) LR TR 2 (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)))
      (trAt 1755 (1755 * 11) LR TR 3 (k / rcnt (LR 4) % rcnt (LR 3)))
      (trAt 1755 (1755 * 11) LR TR 4 (k % rcnt (LR 4))) := by
  obtain ⟨d0, d1, d2, d3, d4, -⟩ := code_facts hk
  exact ⟨⟨_, d0, rfl⟩, ⟨_, d1, rfl⟩, ⟨_, d2, rfl⟩, ⟨_, d3, rfl⟩, ⟨_, d4, rfl⟩⟩

theorem survivors5_mask (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (h : all5K 1755 (1755 * 11) LR TR (survQ P M) = true) :
    survivors5 1755 (rawLevels 1755 S base) p =
      ((List.range (tot5 LR)).filter (hasBit M)).map
        (fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  have hF : ∀ k < tot5 LR, prod5 1755 (rawLevels 1755 S base)
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) (k / rcnt (LR 4) % rcnt (LR 3))
      (k % rcnt (LR 4)) = unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k) ∧
      p (unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) = hasBit M k := by
    intro k hk
    obtain ⟨d0, d1, d2, d3, d4, dk⟩ := code_facts hk
    obtain ⟨-, e, -⟩ := prod5_facts hb hp hl d0 d1 d2 d3 d4
    rw [prodCode_eq]
    refine ⟨e, ?_⟩
    have hq := all5K_at h d0 d1 d2 d3 d4
    rw [dk] at hq
    unfold survQ at hq
    rw [hP _ _ _ _ _ (isTr5_code hk)] at hq
    cases hp' : p (unpack 1755 11 (prod5K 1755 11 (mask 11) _ _ _ _ _)) <;>
      cases hd : hasBit M k <;> simp_all
  unfold survivors5
  rw [c0, c1, c2, c3, c4]
  simp only [filter_map_flatMap]
  rw [flatMap_range_mul, flatMap_range_mul, flatMap_range_mul, flatMap_range_mul, flatMap_ite]
  have hT : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) * rcnt (LR 3) * rcnt (LR 4) = tot5 LR := rfl
  rw [hT]
  have hfil : (List.range (tot5 LR)).filter (fun k => p (prod5 1755 (rawLevels 1755 S base)
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) / rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) / rcnt (LR 2) % rcnt (LR 1))
      (k / rcnt (LR 4) / rcnt (LR 3) % rcnt (LR 2)) (k / rcnt (LR 4) % rcnt (LR 3))
      (k % rcnt (LR 4)))) = (List.range (tot5 LR)).filter (hasBit M) := by
    apply List.filter_congr
    intro k hk
    have hk := List.mem_range.1 hk
    rw [(hF k hk).1, (hF k hk).2]
  rw [hfil]
  exact List.map_congr_left fun k hk => (hF k (List.mem_range.1 (List.mem_filter.1 hk).1)).1

end Mask

theorem surv5K_soundCT {kS BP M : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}
    {C : List Nat}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (hM : Nat.beq (maskOf C) M = true) (hA : ascK (tot5 LR) C 0 = true)
    (h : all5K 1755 (1755 * 11) LR TR (survQ P M) = true) :
    survivors5 1755 (rawLevels 1755 S base) p =
      C.map (fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k)) := by
  rw [survivors5_mask hb hp hl hP h]
  congr 1
  obtain ⟨hC1, hC2⟩ := ascK_spec hA
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (List.pairwise_lt_range.filter _) hC1
    fun k => ?_
  rw [List.mem_filter, List.mem_range, ← Nat.eq_of_beq_eq_true hM, hasBit_maskOf]
  constructor
  · rintro ⟨-, h⟩
    exact of_decide_eq_true h
  · intro hk
    exact ⟨(hC2 k hk).2, decide_eq_true hk⟩

theorem all5K_soundA {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (h : all5K 1755 (1755 * 11) LR TR (fun _ => P) = true) :
    all5 1755 (rawLevels 1755 S base) p = true := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  unfold all5
  rw [c0, c1, c2, c3, c4]
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb' =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => CFSG.Monster.B.Co2.allLt_iff.2 fun d hd =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun e he => ?_
  obtain ⟨-, eg, -⟩ := prod5_facts hb hp hl ha hb' hc hd he
  rw [eg, ← hP _ _ _ _ _ ⟨⟨a, ha, rfl⟩, ⟨b, hb', rfl⟩, ⟨c, hc, rfl⟩, ⟨d, hd, rfl⟩, ⟨e, he, rfl⟩⟩]
  exact all5K_at h ha hb' hc hd he

section Group

open CFSG.Certificates CFSG.Monster.B.Co2

variable {kS kO BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}

theorem chain_group (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup) :
    ∃ G : Subgroup (Equiv.Perm (Fin 1755)),
      (∀ (g : Array Nat) (γ : Equiv.Perm (Fin 1755)), Rep 1755 g γ →
        (siftA 1755 (rawLevels 1755 S base) base 0 g = true ↔ γ ∈ G)) ∧
      ∀ γ ∈ G, (∀ t < 5, ∀ h : base[t]! < 1755, γ ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → γ = 1 := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  have hc := Raw.Orb.rawChainOK_of_K (chunks := 1) hb hh hl hNS hs
  obtain ⟨hk, -⟩ := Raw.Orb.rawHeadOK_of hb hh
  have hmem : ∀ x ∈ base.toList, x < 1755 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    have ht' : t < 5 := by simpa [hbs] using ht
    have := hbl t ht'
    rwa [getElem!_pos base t (by omega), ← Array.getElem_toList] at this
  let bL : List (Fin 1755) := base.toList.map fun x => ⟨x % 1755, Nat.mod_lt _ (by norm_num)⟩
  have hbnd : bL.Nodup := List.Nodup.map_on (fun x hx y hy e => by
      have e' := congrArg Fin.val e
      simp only at e'
      rwa [Nat.mod_eq_of_lt (hmem x hx), Nat.mod_eq_of_lt (hmem y hy)] at e') hnd
  have hBA : (bL.map Fin.val).toArray = base := by
    apply Array.ext'
    simp only [List.map_map, bL]
    conv_rhs => rw [← List.map_id base.toList]
    apply List.map_congr_left
    intro x hx
    exact Nat.mod_eq_of_lt (hmem x hx)
  have hF := chainCheckFacts hc
  have hA := chainArrays_ofArrays (n := 1755) (hn := by norm_num) (k := kO) (hk := hk) (base := bL)
    (hb := hbnd) (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) hF.strong_inv
  rw [hBA] at hA
  have hv := validSchreier_of_chainOK hA (by norm_num) hc
  refine ⟨_, fun g γ hg => siftA_iff_mem_originalSubgroup hA (by norm_num) hc hg,
    fun γ hγ hfix => RawSchreierDatum.eq_one_of_fixes_base _ hv.1 hγ fun i => ?_⟩
  have hi : (i : Nat) < 5 := by
    have h1 := i.2
    have h2 := hA.base_size
    omega
  have hq : (RawSchreierDatum.ofArrays 1755 (by norm_num) S kO hk bL hbnd
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)).base.get i =
        ⟨base[(i : Nat)]!, hbl i hi⟩ := Fin.ext (hA.base_val i)
  rw [hq]
  exact hfix i hi (hbl i hi)

theorem tr5_rep (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) {a b c d e : Nat} (ha : a < rcnt (LR 0))
    (hb1 : b < rcnt (LR 1)) (hc : c < rcnt (LR 2)) (hd : d < rcnt (LR 3)) (he : e < rcnt (LR 4)) :
    Rep 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) (trAt 1755 (1755 * 11) LR TR 0 a)
      (trAt 1755 (1755 * 11) LR TR 1 b) (trAt 1755 (1755 * 11) LR TR 2 c)
      (trAt 1755 (1755 * 11) LR TR 3 d) (trAt 1755 (1755 * 11) LR TR 4 e)))
      (Raw.Orb.trP 1755 S base 0 a * Raw.Orb.trP 1755 S base 1 b * Raw.Orb.trP 1755 S base 2 c *
        Raw.Orb.trP 1755 S base 3 d * Raw.Orb.trP 1755 S base 4 e) ∧
    siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 (prod5K 1755 11 (mask 11)
      (trAt 1755 (1755 * 11) LR TR 0 a) (trAt 1755 (1755 * 11) LR TR 1 b)
      (trAt 1755 (1755 * 11) LR TR 2 c) (trAt 1755 (1755 * 11) LR TR 3 d)
      (trAt 1755 (1755 * 11) LR TR 4 e))) = true := by
  have hd' := hd_of_binds hb hp hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  obtain ⟨-, e5, -⟩ := prod5_facts hb hp hl ha hb1 hc hd he
  have hr : Rep 1755 (prod5 1755 (rawLevels 1755 S base) a b c d e)
      (Raw.Orb.trP 1755 S base 0 a * Raw.Orb.trP 1755 S base 1 b * Raw.Orb.trP 1755 S base 2 c *
        Raw.Orb.trP 1755 S base 3 d * Raw.Orb.trP 1755 S base 4 e) :=
    rep_compA (rep_compA (rep_compA (rep_compA
      (Raw.Orb.rep_tr hd' (by omega) (c0 ▸ ha)) (Raw.Orb.rep_tr hd' (by omega) (c1 ▸ hb1)))
      (Raw.Orb.rep_tr hd' (by omega) (c2 ▸ hc))) (Raw.Orb.rep_tr hd' (by omega) (c3 ▸ hd)))
      (Raw.Orb.rep_tr hd' (by omega) (c4 ▸ he))
  rw [← e5]
  exact ⟨hr, sift5 hd' hbs (c0 ▸ ha) (c1 ▸ hb1) (c2 ▸ hc) (c3 ▸ hd) (c4 ▸ he) hr⟩

theorem baseCommE_of_sep {G : Subgroup (Equiv.Perm (Fin 1755))}
    (hsep : ∀ γ ∈ G, (∀ t < 5, ∀ h : base[t]! < 1755, γ ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → γ = 1)
    (hbl : ∀ t < 5, base[t]! < 1755) (hBP : ∀ t < 5, base[t]! = pg 11 (mask 11) BP t)
    {X Y : Array Nat} {σ τ : Equiv.Perm (Fin 1755)} (hX : Rep 1755 X σ) (hY : Rep 1755 Y τ)
    (hσ : σ ∈ G) (hτ : τ ∈ G) {gx gy : Nat → Nat} (hgx : ∀ i < 1755, gx i = X[i]!)
    (hgy : ∀ i < 1755, gy i = Y[i]!) :
    baseComm BP 5 gx gy = eqA 1755 (compA 1755 X Y) (compA 1755 Y X) := by
  rw [Bool.eq_iff_iff, eqA_iff (rep_compA hX hY) (rep_compA hY hX)]
  have hpt : ∀ t (ht : t < 5), gx (gy base[t]!) = ((σ * τ) ⟨base[t]!, hbl t ht⟩ : Nat) ∧
      gy (gx base[t]!) = ((τ * σ) ⟨base[t]!, hbl t ht⟩ : Nat) := by
    intro t ht
    have hb := hbl t ht
    rw [hgy _ hb, hY.apply hb, hgx _ (τ _).2, hX.apply (τ _).2, hgx _ hb, hX.apply hb,
      hgy _ (σ _).2, hY.apply (σ _).2]
    exact ⟨rfl, rfl⟩
  constructor
  · intro h
    have hfix : ∀ t < 5, ∀ hb : base[t]! < 1755,
        ((τ * σ)⁻¹ * (σ * τ)) ⟨base[t]!, hb⟩ = ⟨base[t]!, hb⟩ := by
      intro t ht hb
      have := allN_spec h t ht
      rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2] at this
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      exact Fin.ext this
    have h1 := hsep _ (G.mul_mem (G.inv_mem (G.mul_mem hτ hσ)) (G.mul_mem hσ hτ)) hfix
    exact inv_mul_eq_one.1 h1 |>.symm
  · intro h
    unfold baseComm
    refine allN_of_forall fun t ht => ?_
    rw [strictB_eq, ← hBP t ht, Nat.beq_eq, (hpt t ht).1, (hpt t ht).2, h]

theorem rep_of_siftA (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) :
    ∀ d l, l + d = 5 → ∀ g : Array Nat, (∀ i < 1755, g[i]! < 1755) →
      siftA 1755 (rawLevels 1755 S base) base l g = true → ∃ γ, Rep 1755 g γ := by
  have hd' := hd_of_binds hb hp hl
  have hbs : base.size = 5 := hb.2.2.2.2.2.1
  intro d
  induction d with
  | zero =>
    intro l hl' g _ h
    rw [siftA, dite_eq_right (by rw [ChainArrays.chainLevels_size]; omega)] at h
    refine ⟨1, fun x => ?_⟩
    have := allLt_spec h x.2
    rw [beq_iff_eq, idA_get x.2] at this
    exact this
  | succ d ih =>
    intro l hl' g hg h
    have hls : l < (rawLevels 1755 S base).size := by
      rw [ChainArrays.chainLevels_size]
      omega
    rw [siftA, dite_eq_left hls, ChainArrays.chainLevels_getElem hls] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, h⟩ := h
    have hlb : l < base.size := by omega
    have rI := Raw.Orb.rep_trInv hd' hlb hk
    have rT := Raw.Orb.rep_tr hd' hlb hk
    obtain ⟨γ', hγ'⟩ := ih (l + 1) (by omega) _ (fun i hi => by
      rw [compA_get hi]
      exact rI.lt (hg i hi)) h
    refine ⟨Raw.Orb.trP 1755 S base l
      ((ChainArrays.lev 1755 S base l).pos[g[base[l]!]!]!) * γ', fun x => ?_⟩
    have e1 := hγ' x
    rw [compA_get x.2] at e1
    have e2 : γ' x = (Raw.Orb.trP 1755 S base l
        ((ChainArrays.lev 1755 S base l).pos[g[base[l]!]!]!))⁻¹ ⟨g[(x : Nat)]!, hg x x.2⟩ :=
      Fin.ext (by rw [← e1, rI.apply (hg x x.2)])
    rw [Equiv.Perm.mul_apply, e2]
    simp

end Group

open CFSG.Certificates CFSG.Monster.B.Co2 in
theorem baseCommGE_eq {kS kO BP NS CH Y t0 t1 t2 t3 t4 : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hh : headK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI kS kO D 5 BP = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hNS : 1755 ≤ NS * CH)
    (hs : ∀ i < 5, ∀ s < NS, schK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) PS PSI LR TR TRI
      kS BP 5 i (stepsAt 1755 11 PS kS BP i) (s * CH) CH = true)
    (hnd : base.toList.Nodup)
    (htr : IsTr5 LR TR t0 t1 t2 t3 t4)
    (hYc : canonK 1755 11 (mask 11) (1755 * 11) Y = true)
    (hY : siftA 1755 (rawLevels 1755 S base) base 0 (unpack 1755 11 Y) = true) :
    baseComm BP 5 (gptR t0 t1 t2 t3 t4) (pgR Y) =
      eqA 1755 (compA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
          (unpack 1755 11 Y))
        (compA 1755 (unpack 1755 11 Y) (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) := by
  have hp := (Raw.Orb.head_facts hh).1
  obtain ⟨G, hmem, hsep⟩ := chain_group hb hh hl hNS hs hnd
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  obtain ⟨⟨a0, h0, rfl⟩, ⟨a1, h1, rfl⟩, ⟨a2, h2, rfl⟩, ⟨a3, h3, rfl⟩, ⟨a4, h4, rfl⟩⟩ := htr
  obtain ⟨rX, sX⟩ := tr5_rep hb hp hl h0 h1 h2 h3 h4
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, -, -⟩ := prod5_facts hb hp hl h0 h1 h2 h3 h4
  obtain ⟨-, hgX⟩ := gpt_facts k0 k1 k2 k3 k4
  obtain ⟨-, -, -, rYc⟩ := canonK_facts hYc
  obtain ⟨τ, rY⟩ := rep_of_siftA hb hp hl 5 0 rfl _ (fun i hi => by
    rw [unpack_getT hi]
    exact rYc i hi) hY
  exact baseCommE_of_sep hsep hbl (fun t ht => hb.2.2.2.2.2.2 t ht) rX rY ((hmem _ _ rX).1 sX)
    ((hmem _ _ rY).1 hY) (fun i hi => by rw [gptR_eq]; exact ((hgX i hi).1).symm)
    (fun i hi => by rw [pgR_eq, unpack_getT hi])

end CFSG.KS.SporSch

end
