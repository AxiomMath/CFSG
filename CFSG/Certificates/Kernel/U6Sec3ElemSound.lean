module

public import CFSG.Certificates.Kernel.U6Sec3Sound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

namespace CFSG.KC.U6Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.Enum

structure ChainK (c : ChainData) (kS nb BP NS : ℕ) (PS PSI LR TR TRI : ℕ → ℕ) : Prop where
  hk : kS = c.gens.length + c.words.length
  hnb : c.B.size = nb
  hBP : ∀ t < nb, c.B[t]! = pg 10 (mask 10) BP t
  hh : headK 693 10 (mask 10) (693 * 10) (pidn 693 10) PS PSI kS c.gens.length c.words nb BP = true
  hl : LevelsOK 693 10 PS PSI LR TR TRI kS nb BP
  hNS : 693 ≤ NS * 64
  hs : ∀ i < nb, ∀ s < NS, schK 693 10 (mask 10) (693 * 10) (pidn 693 10) PS PSI LR TR TRI kS BP nb
    i (stepsAt 693 10 PS kS BP i) (s * 64) 64 = true
  hp : allN kS (fun j => permOK 693 10 (mask 10) (693 * 10) (PS j) (PSI j)) = true
  hO : ∀ j < c.gens.length, unpack 693 10 (PS j) = c.O[j]!

namespace ChainK

variable {c : ChainData} {kS nb BP NS : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}

theorem binds (h : ChainK c kS nb BP NS PS PSI LR TR TRI) :
    Binds 693 10 PS kS nb BP (unpackAll kS PS) c.B :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [unpackAll], fun j hj => unpackAll_get hj,
    h.hnb, h.hBP⟩

theorem raw (h : ChainK c kS nb BP NS PS PSI LR TR TRI) :
    rawChainOK 693 ((unpackAll kS PS).extract 0 c.gens.length) (unpackAll kS PS) c.B
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr c.gens.length kS c.words) 1 = true :=
  rawChainK_sound (chunks := 1) (NS := NS) (CH := 64) h.binds h.hh h.hl h.hNS h.hs

theorem O_all (h : ChainK c kS nb BP NS PS PSI LR TR TRI) (p : Array ℕ → Bool) :
    c.O.all p = (List.range c.gens.length).all fun j => p (unpack 693 10 (PS j)) := by
  apply Bool.eq_iff_iff.2
  rw [Array.all_eq_true, List.all_eq_true]
  simp only [List.mem_range, ChainData.O_size]
  refine forall_congr' fun j => forall_congr' fun hlt => ?_
  rw [h.hO j hlt, getElem!_pos c.O j (by rw [ChainData.O_size]; exact hlt)]

theorem O_any (h : ChainK c kS nb BP NS PS PSI LR TR TRI) (p : Array ℕ → Bool) :
    c.O.any p = (List.range c.gens.length).any fun j => p (unpack 693 10 (PS j)) := by
  apply Bool.eq_iff_iff.2
  rw [Array.any_eq_true, List.any_eq_true]
  simp only [List.mem_range, ChainData.O_size]
  refine exists_congr fun j => ⟨fun ⟨hlt, hp⟩ => ⟨hlt, ?_⟩, fun ⟨hlt, hp⟩ => ⟨hlt, ?_⟩⟩
  · rw [h.hO j hlt, getElem!_pos c.O j (by rw [ChainData.O_size]; exact hlt)]
    exact hp
  · rw [h.hO j hlt, getElem!_pos c.O j (by rw [ChainData.O_size]; exact hlt)] at hp
    exact hp

end ChainK

theorem PermK.canon {p q : ℕ} (h : PermK p q = true) : canonK 693 10 (mask 10) (693 * 10) p = true := by
  unfold PermK at h
  simp only [bAnd_iff] at h
  exact h.1

theorem PermK.canon_inv {p q : ℕ} (h : PermK p q = true) :
    canonK 693 10 (mask 10) (693 * 10) q = true := by
  unfold PermK at h
  simp only [bAnd_iff] at h
  exact h.2.1

theorem PermK.inv {p q : ℕ} (h : PermK p q = true) :
    invCand 693 (unpack 693 10 p) = unpack 693 10 q := by
  unfold PermK at h
  simp only [bAnd_iff] at h
  exact (invEqK_sound h.2.2).1

theorem PermK.valid {p q : ℕ} (h : PermK p q = true) : validA 693 (unpack 693 10 p) = true := by
  unfold PermK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := invEqK_sound h.2.2
  rw [validA, h1]
  exact h2

theorem comp_unpack {p q : ℕ} (hp : canonK 693 10 (mask 10) (693 * 10) p = true)
    (hq : canonK 693 10 (mask 10) (693 * 10) q = true) :
    compA 693 (unpack 693 10 p) (unpack 693 10 q) = unpack 693 10 (pcomp 693 10 (mask 10) p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem canon_comp {p q : ℕ} (hp : canonK 693 10 (mask 10) (693 * 10) p = true)
    (hq : canonK 693 10 (mask 10) (693 * 10) q = true) :
    canonK 693 10 (mask 10) (693 * 10) (pcomp 693 10 (mask 10) p q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem conj_unpack {g gi y : ℕ} (hg : PermK g gi = true)
    (hy : canonK 693 10 (mask 10) (693 * 10) y = true) :
    conjA 693 (unpack 693 10 g) (unpack 693 10 y) =
      unpack 693 10 (pcomp 693 10 (mask 10) g (pcomp 693 10 (mask 10) y gi)) := by
  rw [conjA, PermK.inv hg, comp_unpack hy (PermK.canon_inv hg),
    comp_unpack (PermK.canon hg) (canon_comp hy (PermK.canon_inv hg))]

theorem conjInv_unpack {g gi y : ℕ} (hg : PermK g gi = true)
    (hy : canonK 693 10 (mask 10) (693 * 10) y = true) :
    conjInvA 693 (unpack 693 10 g) (unpack 693 10 y) =
      unpack 693 10 (pcomp 693 10 (mask 10) gi (pcomp 693 10 (mask 10) y g)) := by
  rw [conjInvA, PermK.inv hg, comp_unpack hy (PermK.canon hg),
    comp_unpack (PermK.canon_inv hg) (canon_comp hy (PermK.canon hg))]

theorem commutator_unpack {g gi h hi : ℕ} (hg : PermK g gi = true) (hh : PermK h hi = true) :
    commutatorA 693 (unpack 693 10 g) (unpack 693 10 h) =
      unpack 693 10 (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) g h)
        (pcomp 693 10 (mask 10) gi hi)) := by
  rw [commutatorA, PermK.inv hg, PermK.inv hh, comp_unpack (PermK.canon hg) (PermK.canon hh),
    comp_unpack (PermK.canon_inv hg) (PermK.canon_inv hh),
    comp_unpack (canon_comp (PermK.canon hg) (PermK.canon hh))
      (canon_comp (PermK.canon_inv hg) (PermK.canon_inv hh))]

theorem eq_unpack {p q : ℕ} (hp : canonK 693 10 (mask 10) (693 * 10) p = true)
    (hq : canonK 693 10 (mask 10) (693 * 10) q = true) :
    eqA 693 (unpack 693 10 p) (unpack 693 10 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

theorem unpack_get {p i : ℕ} (hi : i < 693) : (unpack 693 10 p)[i]! = pg 10 (mask 10) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem strictN_val (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem canon_pidn : canonK 693 10 (mask 10) (693 * 10) (pidn 693 10) = true := by decide +kernel

theorem idA_eq_pidn : idA 693 = unpack 693 10 (pidn 693 10) :=
  unpack_eq_of_all (by simp [idA]) (by decide +kernel)

theorem canon_lt {p i : ℕ} (hp : canonK 693 10 (mask 10) (693 * 10) p = true) (hi : i < 693) :
    pg 10 (mask 10) p i < 693 := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  simpa [Nat.blt_eq] using allN_spec hp.2.2 i hi

theorem comp_get {p q i : ℕ} (hp : canonK 693 10 (mask 10) (693 * 10) p = true)
    (hq : canonK 693 10 (mask 10) (693 * 10) q = true) (hi : i < 693) :
    pg 10 (mask 10) (pcomp 693 10 (mask 10) p q) i = pg 10 (mask 10) p (pg 10 (mask 10) q i) := by
  rw [← unpack_get hi, ← comp_unpack hp hq, compA, getElem!_pos _ i (by simpa using hi),
    Array.getElem_ofFn, unpack_get hi, unpack_get (canon_lt hq hi)]

theorem foldl_canon {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    ∀ {acc : ℕ}, canonK 693 10 (mask 10) (693 * 10) acc = true →
      canonK 693 10 (mask 10) (693 * 10)
        (List.foldl (fun acc t => strictN acc fun acc => pcomp 693 10 (mask 10) t acc) acc L) =
        true := by
  induction L with
  | nil => exact fun h => h
  | cons t L ih =>
    intro acc hacc
    rw [List.foldl_cons, strictN_val]
    exact ih (fun t' ht' => hL t' (List.mem_cons_of_mem t ht'))
      (canon_comp (hL t List.mem_cons_self) hacc)

theorem prodL_canon {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    canonK 693 10 (mask 10) (693 * 10) (prodL 693 10 (mask 10) L) = true :=
  foldl_canon hL canon_pidn

theorem foldl_get {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    ∀ {acc i : ℕ}, canonK 693 10 (mask 10) (693 * 10) acc = true → i < 693 →
      pg 10 (mask 10)
        (List.foldl (fun acc t => strictN acc fun acc => pcomp 693 10 (mask 10) t acc) acc L) i =
        ptL 10 (mask 10) L (pg 10 (mask 10) acc i) := by
  induction L with
  | nil => intro acc i _ _; rfl
  | cons t L ih =>
    intro acc i hacc hi
    have ht := hL t List.mem_cons_self
    rw [List.foldl_cons, strictN_val, ih (fun t' ht' => hL t' (List.mem_cons_of_mem t ht'))
      (canon_comp ht hacc) hi, comp_get ht hacc hi]
    rfl

theorem prodL_get {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
    {i : ℕ} (hi : i < 693) : (unpack 693 10 (prodL 693 10 (mask 10) L))[i]! = ptL 10 (mask 10) L i := by
  rw [unpack_get hi, prodL, foldl_get hL canon_pidn hi, ← unpack_get hi, ← idA_eq_pidn, idA,
    getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

end CFSG.KC.U6Sec3

end
