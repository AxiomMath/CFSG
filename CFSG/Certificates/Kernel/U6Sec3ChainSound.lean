module

public import CFSG.Certificates.Kernel.U6Sec3ElemSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.NativeSchreierEnum
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.U6Sec3.SEq

public section

namespace CFSG.KC.U6Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.Enum

theorem chain_of_kernel' (c : ChainData) {kS nb BP NS : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    (hk : kS = c.gens.length + c.words.length) (hnb : c.B.size = nb)
    (hBP : ∀ t < nb, c.B[t]! = pg 10 (mask 10) BP t)
    (hh : headK 693 10 (mask 10) (693 * 10) (pidn 693 10) PS PSI kS c.gens.length c.words nb BP =
      true)
    (hl : LevelsOK 693 10 PS PSI LR TR TRI kS nb BP) (hNS : 693 ≤ NS * 64)
    (hs : ∀ i < nb, ∀ s < NS, schK 693 10 (mask 10) (693 * 10) (pidn 693 10) PS PSI LR TR TRI kS
      BP nb i (stepsAt 693 10 PS kS BP i) (s * 64) 64 = true)
    (hp : allN kS (fun j => permOK 693 10 (mask 10) (693 * 10) (PS j) (PSI j)) = true)
    (hO : ∀ j < c.gens.length, unpack 693 10 (PS j) = c.O[j]!) :
    c.ok = true ∧ c.order = ((List.range nb).map fun i => rcnt (LR i)).prod ∧
      c.S = unpackAll kS PS := by
  have hb : Binds 693 10 PS kS nb BP (unpackAll kS PS) c.B :=
    ⟨by norm_num, by norm_num, by norm_num, by simp [unpackAll], fun j hj => unpackAll_get hj,
      hnb, hBP⟩
  have hraw := rawChainK_sound (chunks := 1) (NS := NS) (CH := 64) hb hh hl hNS hs
  have hsz : (unpackAll kS PS).size = c.gens.length + c.words.length := by simp [unpackAll, hk]
  have hraw' : rawChainOK 693 ((unpackAll kS PS).extract 0 c.gens.length) (unpackAll kS PS) c.B
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr c.gens.length (unpackAll kS PS).size c.words)
      1 = true := by
    rw [show (unpackAll kS PS).size = kS by simp [unpackAll]]
    exact hraw
  have hS := S_eq_of_rawChainOK' c hraw' hsz
    (fun j hj => by rw [unpackAll_get (by omega), hO j hj])
    (fun j hj => by
      rw [unpackAll_get (by simpa [unpackAll] using hj)]
      simp [unpack])
  refine ⟨ok_of_rawChainOK c hS hraw' hsz, ?_, hS⟩
  rw [order_of_rawChainOK c hS, rawOrbitSizesK_sound hb hp hl]

theorem prodLazyK_spec {n nw : ℕ} {LR TR : ℕ → ℕ} {f : List ℕ → Bool} (κ : ℕ → ℕ) :
    ∀ d i L, prodLazyK n nw LR TR f d i L = true →
      (∀ j < d, κ (i + j) < rcnt (LR (i + j))) →
      f (((List.range d).map fun j => TR (roff n nw (LR (i + j)) + κ (i + j))).reverse ++ L) =
        true
  | 0, i, L, h, _ => by simpa [prodLazyK_zero] using h
  | d + 1, i, L, h, hκ => by
    rw [prodLazyK_succ] at h
    have h1 := prodLazyK_spec κ d (i + 1) _ (allN_spec h (κ i) (by simpa using hκ 0 (by omega)))
      (fun j hj => by
        have := hκ (j + 1) (by omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this)
    have e : (fun j => TR (roff n nw (LR (i + (j + 1))) + κ (i + (j + 1)))) =
        fun j => TR (roff n nw (LR (i + 1 + j)) + κ (i + 1 + j)) :=
      funext fun j => by rw [Nat.add_assoc, Nat.add_comm 1 j]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons,
      List.append_assoc, List.singleton_append, Nat.add_zero]
    simpa only [Function.comp_def, Nat.succ_eq_add_one, e] using h1

theorem pg_foldl {n w : ℕ} (hn : n < 2 ^ 32) :
    ∀ (L : List ℕ) (acc i : ℕ), i < n →
      pg w (mask w) (List.foldl (fun acc t => strictN acc fun acc => pcomp n w (mask w) t acc)
        acc L) i = ptL w (mask w) L (pg w (mask w) acc i)
  | [], _, _, _ => rfl
  | t :: L, acc, i, hi => by
    have e : ∀ (y : ℕ) (k : ℕ → ℕ), strictN y k = k y := fun y k => by cases y <;> rfl
    rw [List.foldl_cons, e, pg_foldl hn L _ i hi, CFSG.KS.PF.pg_pcomp hn hi]
    rfl

theorem ptL_reverse {n w : ℕ} :
    ∀ {Ts : List ℕ} {Gs : List (Equiv.Perm (Fin n))},
      List.Forall₂ (fun t (g : Equiv.Perm (Fin n)) => ∀ z : Fin n, pg w (mask w) t z = g z) Ts Gs →
      ∀ z : Fin n, ptL w (mask w) Ts.reverse z = (Gs.prod z : ℕ)
  | [], [], .nil, _ => rfl
  | t :: Ts, g :: Gs, .cons ht h, z => by
    have e : ptL w (mask w) (Ts.reverse ++ [t]) z =
        pg w (mask w) t (ptL w (mask w) Ts.reverse z) := by
      simp only [ptL, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.reverse_cons, e, ptL_reverse h z, List.prod_cons, Equiv.Perm.mul_apply]
    exact ht _

theorem canonK_of_permOK {n w p q : ℕ} (hs : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p q = true) : canonK n w (mask w) (n * w) p = true := by
  refine (bAnd_iff _ _).2 ⟨hs, (bAnd_iff _ _).2 ⟨?_, range_of_permOK h⟩⟩
  unfold permOK at h
  exact ((bAnd_iff _ _).1 h).1

theorem forall_of_prodLazyK' {n w kS kO nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {SA : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {f : List ℕ → Bool}
    (hb : Binds n w PS kS nb BP SA base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hraw : rawChainOK n (SA.extract 0 kO) SA base W 1 = true) (hnd : base.toList.Nodup)
    (hf : prodLazyK n (n * w) LR TR f nb 0 [] = true) :
    ∀ x ∈ Subgroup.closure (permsA n (SA.extract 0 kO)), ∃ L : List ℕ,
      (∀ t ∈ L, canonK n w (mask w) (n * w) t = true) ∧
      Rep n (unpack n w (prodL n w (mask w) L)) x ∧ f L = true := by
  intro x hx
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hn32 : n < 2 ^ 32 := by omega
  have hw' : n + 1 < 2 ^ w := hb.2.1
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hF := CFSG.Certificates.chainCheckFacts hraw
  have hk : (SA.extract 0 kO).size ≤ SA.size := by simp
  have hext : SA.extract 0 (SA.extract 0 kO).size = SA.extract 0 kO := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_extract]
  have hmem : ∀ y ∈ base.toList, y < n := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    have ht' : t < nb := by simpa [hbs] using ht
    have := hbl t ht'
    rwa [getElem!_pos base t (by omega), ← Array.getElem_toList] at this
  let bL : List (Fin n) := base.toList.map fun y => ⟨y % n, Nat.mod_lt _ hb.1⟩
  have hbnd : bL.Nodup := List.Nodup.map_on (fun y hy z hz e => by
      have e' := congrArg Fin.val e
      simp only at e'
      rwa [Nat.mod_eq_of_lt (hmem y hy), Nat.mod_eq_of_lt (hmem z hz)] at e') hnd
  have hBA : (bL.map Fin.val).toArray = base := by
    apply Array.ext'
    simp only [List.map_map, bL]
    conv_rhs => rw [← List.map_id base.toList]
    apply List.map_congr_left
    intro y hy
    exact Nat.mod_eq_of_lt (hmem y hy)
  let Q := CFSG.Certificates.RawSchreierDatum.ofArrays n hb.1 SA (SA.extract 0 kO).size hk bL
    hbnd W
  have hA := CFSG.Certificates.chainArrays_ofArrays (n := n) (hn := hb.1)
    (k := (SA.extract 0 kO).size) (hk := hk) (base := bL) (hb := hbnd) (W := W) hF.strong_inv
  rw [hBA, hext] at hA
  have hQ := (CFSG.Certificates.validSchreier_of_chainOK hA (by norm_num) hraw).1
  have hcount : Q.baseCount = nb := by rw [← hA.base_size, hbs]
  have hxQ : x ∈ Q.originalSubgroup := by
    refine Subgroup.closure_mono ?_ hx
    rintro _ ⟨j, hj, rfl⟩
    have hj0 : j < (SA.extract 0 kO).size := hj
    rw [Set.mem_ofPred_eq, CFSG.Certificates.RawSchreierDatum.mem_ofArrays_original]
    refine ⟨j, hj0, ?_⟩
    have hj' : j < SA.size := by simp at hj0; omega
    change permOfArr n SA[j]! = permOfArr n (SA.extract 0 kO)[j]!
    rw [getElem!_pos (SA.extract 0 kO) j hj0, Array.getElem_extract, getElem!_pos SA j hj']
    simp
  obtain ⟨-, Φ, hΦ, hbij, -⟩ := Q.schreier_transversal_product_bijection hQ
  obtain ⟨y, hy⟩ := hbij.2 ⟨x, hxQ⟩
  have hx' : x = (List.ofFn fun i => Q.orbitTransversal i (y i)).prod := by
    rw [← hΦ y, hy]
  let κ : ℕ → ℕ := fun j => if h : j < Q.baseCount then
    (CFSG.Certificates.ChainArrays.lev n SA base j).pos[((y ⟨j, h⟩ : Fin n) : ℕ)]! else 0
  have hT : ∀ i : Fin Q.baseCount, Q.orbitTransversal i (y i) =
      CFSG.Certificates.ChainArrays.levT n SA base i (κ i) := fun i => by
    refine Eq.trans (hA.orbitPoints_spec hF i.2 (y i).2).2.2 ?_
    simp only [κ, dite_eq_left i.2]
  have hK : ∀ j < nb, κ j < (CFSG.Certificates.ChainArrays.lev n SA base j).pts.size :=
    fun j hj => by
      have hj' : j < Q.baseCount := hcount ▸ hj
      simp only [κ, dite_eq_left hj']
      exact (hA.orbitPoints_spec hF hj' (y ⟨j, hj'⟩).2).1
  let T : ℕ → ℕ := fun j => TR (roff n (n * w) (LR j) + κ j)
  have hTj : ∀ j < nb, κ j < rcnt (LR j) ∧ canonK n w (mask w) (n * w) (T j) = true ∧
      ∀ z : Fin n, pg w (mask w) (T j) z =
        (CFSG.Certificates.ChainArrays.levT n SA base j (κ j) z : ℕ) := by
    intro j hj
    obtain ⟨A, P⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hj (hl j hj)
    have hkc : κ j < rcnt (LR j) := A.cnt ▸ hK j hj
    obtain ⟨hsz, -, -, -, -, hperm⟩ := Raw.Orb.levelK_facts (hl j hj)
    refine ⟨hkc, canonK_of_permOK hsz (hperm _ hkc), fun z => ?_⟩
    have hjQ : j < Q.baseCount := by rw [hcount]; exact hj
    have r1 := (P _ hkc).1 z
    have r2 := (A.tr _ (hK j hj)).1 z
    have r3 := hA.rep_levT hF hjQ (hK j hj) z
    exact r1.trans (r2.symm.trans r3)
  refine ⟨((List.range nb).map T).reverse, fun t ht => ?_, fun z => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 ht)
    exact (hTj j (List.mem_range.1 hj)).2.1
  · rw [Raw.Orb.unpack_get z.2, prodL, pg_foldl hn32 _ _ _ z.2, CFSG.KS.PF.pg_pidn hn24 hw' z.2]
    have e : x = ((List.range nb).map fun j =>
        CFSG.Certificates.ChainArrays.levT n SA base j (κ j)).prod := by
      rw [hx']
      congr 1
      apply List.ext_getElem
      · simp [hcount]
      · intro j h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact hT ⟨j, by simpa using h1⟩
    rw [e]
    refine ptL_reverse ?_ z
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun j hj => (hTj j (List.mem_range.1 hj)).2.2
  · have := prodLazyK_spec κ nb 0 [] hf fun j hj => by
      simpa using (hTj j hj).1
    simpa using this

namespace ChainK

variable {c : ChainData} {kS nb BP NS : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}

theorem facts' (h : ChainK c kS nb BP NS PS PSI LR TR TRI) :
    c.ok = true ∧ c.order = ((List.range nb).map fun i => rcnt (LR i)).prod ∧
      c.S = unpackAll kS PS :=
  chain_of_kernel' c h.hk h.hnb h.hBP h.hh h.hl h.hNS h.hs h.hp h.hO

theorem S_eq' (h : ChainK c kS nb BP NS PS PSI LR TR TRI) : c.S = unpackAll kS PS :=
  h.facts'.2.2

theorem sift' (h : ChainK c kS nb BP NS PS PSI LR TR TRI) {G : ℕ}
    (hG : canonK 693 10 (mask 10) (693 * 10) G = true) :
    siftA 693 c.levels c.B 0 (unpack 693 10 G) =
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR TRI BP nb 0 G := by
  have hz : Nat.shiftRight G (693 * 10) = 0 := by
    unfold canonK at hG
    simp only [bAnd_iff] at hG
    exact Nat.eq_of_beq_eq_true hG.2.1
  unfold ChainData.levels
  rw [h.S_eq']
  exact siftK_eq h.binds h.hp h.hl rfl hz (range_of_canonK hG)

theorem permsA_eq' (h : ChainK c kS nb BP NS PS PSI LR TR TRI) :
    permsA 693 ((unpackAll kS PS).extract 0 c.gens.length) = permsA 693 c.O := by
  have hsz : ((unpackAll kS PS).extract 0 c.gens.length).size = c.O.size := by
    simp only [Array.size_extract, unpackAll, Array.size_ofFn, ChainData.O_size, h.hk]
    omega
  ext x
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, hsz]
  refine exists_congr fun k => and_congr_right fun hk => ?_
  rw [ChainData.O_size] at hk
  have hlt : k < (unpackAll kS PS).size := by
    simp only [unpackAll, Array.size_ofFn, h.hk]
    omega
  have e : ((unpackAll kS PS).extract 0 c.gens.length)[k]! = c.O[k]! := by
    rw [getElem!_pos _ k (by rw [hsz, ChainData.O_size]; exact hk), Array.getElem_extract,
      ← ChainData.S_getElem_of_lt c hk, h.S_eq', getElem!_pos _ k hlt]
    simp
  rw [e]

theorem forall_lazy' (h : ChainK c kS nb BP NS PS PSI LR TR TRI) (htabs : tabsCheck = true)
    (hg : c.GensOK) (hnd : c.base.Nodup) {f : List ℕ → Bool}
    (hf : prodLazyK 693 (693 * 10) LR TR f nb 0 [] = true) :
    ∀ x ∈ c.grp, ∃ L : List ℕ, (∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) ∧
      Rep 693 (unpack 693 10 (prodL 693 10 (mask 10) L)) x ∧ f L = true := by
  intro x hx
  rw [← ChainData.closure_permsA htabs hg, ← h.permsA_eq'] at hx
  exact forall_of_prodLazyK' h.binds h.hp h.hl h.raw (by simpa [ChainData.B] using hnd) hf x hx

end ChainK

end CFSG.KC.U6Sec3

end
