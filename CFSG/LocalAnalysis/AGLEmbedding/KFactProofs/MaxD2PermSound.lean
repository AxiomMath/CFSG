module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
import CFSG.CharacterTheory.Burnside
public import Certificates.Data.MaxD2Perm

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm
open Certificates.FusD2Perm (powT wordT)

section DoubleCosets

variable {Q : Type*} [Group Q]

@[expose] def dcoset (N : Subgroup Q) (g : Q) : Set Q := {x | ∃ a ∈ N, ∃ b ∈ N, x = a * g * b}

@[expose] def conjStab (N : Subgroup Q) (g : Q) : Subgroup Q :=
  N ⊓ N.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjStab {N : Subgroup Q} {g a : Q} : a ∈ conjStab N g ↔ a ∈ N ∧ g⁻¹ * a * g ∈ N := by
  simp [conjStab]

@[instance_reducible] def prodAct (N : Subgroup Q) : MulAction (N × N) Q where
  smul ab x := (ab.1 : Q) * x * (ab.2 : Q)⁻¹
  one_smul x := by
    show ((1 : N × N).1 : Q) * x * ((1 : N × N).2 : Q)⁻¹ = x
    simp
  mul_smul ab cd x := by
    show ((ab * cd).1 : Q) * x * ((ab * cd).2 : Q)⁻¹ =
      (ab.1 : Q) * ((cd.1 : Q) * x * (cd.2 : Q)⁻¹) * (ab.2 : Q)⁻¹
    simp [mul_assoc]

theorem card_dcoset_mul (N : Subgroup Q) (g : Q) :
    Nat.card (dcoset N g) * Nat.card (conjStab N g) = Nat.card N * Nat.card N := by
  let _ := prodAct N
  have h1 : MulAction.orbit (N × N) g = dcoset N g := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, a.2, b⁻¹, (b⁻¹).2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b⁻¹, N.inv_mem hb⟩), by
        show a * g * (b⁻¹)⁻¹ = a * g * b
        simp⟩
  have h2 : Nat.card (MulAction.stabilizer (N × N) g) = Nat.card (conjStab N g) := by
    refine Nat.card_congr ⟨fun ab => ⟨(ab.1.1 : Q), ?_⟩,
      fun s => ⟨(⟨s, (mem_conjStab.1 s.2).1⟩, ⟨g⁻¹ * s * g, (mem_conjStab.1 s.2).2⟩), ?_⟩, ?_, ?_⟩
    · obtain ⟨⟨a, b⟩, hab⟩ := ab
      have : (a : Q) * g * (b : Q)⁻¹ = g := hab
      refine mem_conjStab.2 ⟨a.2, ?_⟩
      have hb : g⁻¹ * a * g = b := by
        calc g⁻¹ * a * g = g⁻¹ * (a * g * (b : Q)⁻¹) * b := by group
          _ = b := by rw [this]; group
      rw [hb]; exact b.2
    · show (s : Q) * g * (g⁻¹ * s * g)⁻¹ = g
      group
    · rintro ⟨⟨a, b⟩, hab⟩
      have : (a : Q) * g * (b : Q)⁻¹ = g := hab
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        show g⁻¹ * (a : Q) * g = b
        calc g⁻¹ * a * g = g⁻¹ * (a * g * (b : Q)⁻¹) * b := by group
          _ = b := by rw [this]; group
    · rintro s
      rfl
  have h3 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (N × N) g)
  rw [Nat.card_prod, Nat.card_prod, h1, h2] at h3
  rw [h3]

theorem disjoint_dcoset {N : Subgroup Q} {g₁ g₂ : Q}
    (h : ∀ a ∈ N, g₁⁻¹ * a * g₂ ∉ N) : Disjoint (dcoset N g₁) (dcoset N g₂) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', hx⟩
  refine h (a⁻¹ * a') (N.mul_mem (N.inv_mem ha) ha') ?_
  have : g₁⁻¹ * (a⁻¹ * a') * g₂ = b * b'⁻¹ := by
    have h1 : a⁻¹ * a' = g₁ * (b * b'⁻¹) * g₂⁻¹ := by
      calc a⁻¹ * a' = a⁻¹ * (a' * g₂ * b') * b'⁻¹ * g₂⁻¹ := by group
        _ = a⁻¹ * (a * g₁ * b) * b'⁻¹ * g₂⁻¹ := by rw [← hx]
        _ = g₁ * (b * b'⁻¹) * g₂⁻¹ := by group
    rw [h1]; group
  rw [this]
  exact N.mul_mem hb (N.inv_mem hb')

theorem dcoset_subset {G N : Subgroup Q} (hNG : N ≤ G) {g : Q} (hg : g ∈ G) :
    dcoset N g ⊆ G := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact G.mul_mem (G.mul_mem (hNG ha) hg) (hNG hb)

theorem exists_dcoset_of_sum [Finite Q] {G N : Subgroup Q} (hNG : N ≤ G)
    (g : ℕ → Q) (r : ℕ) (hgG : ∀ i ≤ r, g i ∈ G)
    (hsum : ∑ i ∈ Finset.range (r + 1),
      Nat.card N * Nat.card N / Nat.card (conjStab N (g i)) = Nat.card G)
    (hdisj : ∀ i ≤ r, ∀ j ≤ r, i < j → ∀ a ∈ N, (g i)⁻¹ * a * g j ∉ N) :
    ∀ y ∈ G, ∃ i ≤ r, y ∈ dcoset N (g i) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  let Df : ℕ → Finset Q := fun i => (dcoset N (g i)).toFinset
  have hcard : ∀ i, (Df i).card =
      Nat.card N * Nat.card N / Nat.card (conjStab N (g i)) := by
    intro i
    have h1 := card_dcoset_mul N (g i)
    have hc : 0 < Nat.card (conjStab N (g i)) := Nat.card_pos
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact (Nat.div_eq_of_eq_mul_left hc h1.symm).symm
  have hdisjf : ∀ i ∈ Finset.range (r + 1), ∀ j ∈ Finset.range (r + 1), i ≠ j →
      Disjoint (Df i) (Df j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    simp only [Df, Set.disjoint_toFinset]
    rcases lt_or_gt_of_ne hij with h | h
    · exact disjoint_dcoset (hdisj i (by omega) j (by omega) h)
    · exact (disjoint_dcoset (hdisj j (by omega) i (by omega) h)).symm
  let Gf : Finset Q := (G : Set Q).toFinset
  have hGf : Gf.card = Nat.card G := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  have hsub : (Finset.range (r + 1)).biUnion Df ⊆ Gf := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    rw [Finset.mem_range] at hi
    simp only [Df, Set.mem_toFinset] at hxi
    simpa [Gf] using dcoset_subset hNG (hgG i (by omega)) hxi
  have hcardU : ((Finset.range (r + 1)).biUnion Df).card = Gf.card := by
    rw [Finset.card_biUnion hdisjf, hGf, ← hsum]
    exact Finset.sum_congr rfl fun i _ => hcard i
  have heq := Finset.eq_of_subset_of_card_le hsub hcardU.ge
  intro y hy
  have : y ∈ Gf := by simpa [Gf] using hy
  rw [← heq, Finset.mem_biUnion] at this
  obtain ⟨i, hi, hyi⟩ := this
  rw [Finset.mem_range] at hi
  exact ⟨i, by omega, by simpa [Df] using hyi⟩

theorem maximal_of_doubleCosets [Finite Q] {G N : Subgroup Q} (hNG : N ≤ G)
    (g : ℕ → Q) (r : ℕ) (hg0 : g 0 = 1) (hgG : ∀ i ≤ r, g i ∈ G)
    (hsum : ∑ i ∈ Finset.range (r + 1),
      Nat.card N * Nat.card N / Nat.card (conjStab N (g i)) = Nat.card G)
    (hdisj : ∀ i ≤ r, ∀ j ≤ r, i < j → ∀ a ∈ N, (g i)⁻¹ * a * g j ∉ N)
    (hgen : ∀ i, 1 ≤ i → i ≤ r → G ≤ Subgroup.closure ((N : Set Q) ∪ {g i})) :
    ∀ Y : Subgroup Q, N ≤ Y → Y ≤ G → Y = N ∨ Y = G := by
  intro Y hNY hYG
  by_cases hYN : Y ≤ N
  · exact Or.inl (le_antisymm hYN hNY)
  · refine Or.inr (le_antisymm hYG ?_)
    obtain ⟨y, hyY, hyN⟩ := Set.not_subset.1 hYN
    obtain ⟨i, hi, a, ha, b, hb, rfl⟩ := exists_dcoset_of_sum hNG g r hgG hsum hdisj y (hYG hyY)
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hyN
      rw [hg0, mul_one]
      exact N.mul_mem ha hb
    have hgY : g i ∈ Y := by
      have : g i = a⁻¹ * (a * g i * b) * b⁻¹ := by group
      rw [this]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem (hNY ha)) hyY) (Y.inv_mem (hNY hb))
    refine (hgen i (Nat.pos_of_ne_zero hi0) hi).trans ?_
    rw [Subgroup.closure_le]
    rintro z (hz | rfl)
    · exact hNY hz
    · exact hgY

end DoubleCosets

section Generic

theorem zpowers_eq_of_card_prime {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {Y : Subgroup X} (hY : Nat.card Y = p) {y : X} (hy : y ∈ Y) (hy1 : y ≠ 1) :
    Subgroup.zpowers y = Y ∧ orderOf y = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hyp : y ^ p = 1 := by
    have := pow_card_eq_one' (G := Y) (x := ⟨y, hy⟩)
    rw [hY] at this
    exact congrArg Subtype.val this
  have hord : orderOf y = p := orderOf_eq_prime hyp hy1
  refine ⟨Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hy) ?_, hord⟩
  rw [hY, Nat.card_zpowers, hord]

theorem exists_pow_lt_of_mem_zpowers {X : Type*} [Group X] [Finite X] {y z : X}
    (hz : z ∈ Subgroup.zpowers y) (hpos : 0 < orderOf y) : ∃ j < orderOf y, y ^ j = z := by
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hz
  obtain ⟨m, hm⟩ := hz
  exact ⟨m % orderOf y, Nat.mod_lt m hpos, by rw [pow_mod_orderOf, hm]⟩

theorem mem_normalizer_of_conj_gens {Q : Type*} [Group Q] [Finite Q] {A : Set Q} {a : Q}
    (h : ∀ s ∈ A, a * s * a⁻¹ ∈ Subgroup.closure A) :
    a ∈ Subgroup.normalizer (Subgroup.closure A : Set Q) := by
  have hle : Subgroup.closure A ≤ (Subgroup.closure A).comap (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.closure_le]
    exact fun s hs => h s hs
  exact Subgroup.mem_normalizer_fintype fun m hm => hle hm

theorem foldl_range_add (f : ℕ → ℕ) (m : ℕ) :
    (List.range m).foldl (fun s i => s + f i) 0 = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

end Generic

section Tables

theorem countBelow_getElem! (T : Array Tab) (p : Tab → Bool) :
    countBelow T.size (fun k => p T[k]!) = (T.toList.filter p).length := by
  have h : (List.range T.size).map (fun k => T[k]!) = T.toList := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [getElem!_pos T i (by simpa using h1)]
      simp
  rw [← h, List.filter_map, List.length_map]
  rfl

theorem found_of_mem_treeOK {step : ℕ → Tab → Tab} {k : ℕ} {root : Tab} {E : Enum}
    (h : treeOK step k root E = true) {x : Tab} (hx : x ∈ E.tabs.toList) :
    found (indexOf E.tabs) E.tabs x = true := by
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem hx
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨⟨hpos, h0⟩, hall⟩ := h
  have := (hall i hi).1.1
  simp only [found, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [this]
  exact ⟨hi, rfl⟩

theorem found_iff_of_enumOK {n : ℕ} {gens : Array Tab} {E : Enum} (h : enumOK n gens E = true)
    (x : Tab) : found (indexOf E.tabs) E.tabs x = true ↔ x ∈ E.tabs.toList :=
  ⟨mem_of_found, found_of_mem_treeOK h⟩

theorem memFp_iff {pts : List ℕ} {T : Array Tab} (h : fpOK pts T = true) (y : Tab) :
    memFp pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T y = true ↔
      y ∈ T.toList := by
  simp only [fpOK, allBelow_eq_true, beq_iff_eq] at h
  constructor
  · intro hy
    simp only [memFp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hy
    obtain ⟨hlt, heq⟩ := hy
    rw [← heq]
    exact getElem!_mem hlt
  · intro hy
    obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem hy
    have hk' : k < (T.map (fpTab pts)).size := by simpa using hk
    have hfp : (T.map (fpTab pts))[k]! = fpTab pts T[k]! := by
      rw [getElem!_pos (T.map (fpTab pts)) k hk', Array.getElem_map, getElem!_pos T k hk]
    have := h k hk'
    rw [hfp] at this
    simp only [memFp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [this]
    exact ⟨hk, rfl⟩

variable {n : ℕ}

theorem rep_map_words (S : List (Equiv.Perm (Fin n))) (gs gi : Array Tab)
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹) (ws : List (List ℤ)) (j : ℕ) :
    TabRep ((ws.map (wordT n gs gi)).toArray.getD j (idTab n)) ((ws.map (wordVal S)).getD j 1) := by
  by_cases hj : j < ws.length
  · rw [show (ws.map (wordT n gs gi)).toArray.getD j (idTab n) = wordT n gs gi ws[j] by simp [hj],
      show (ws.map (wordVal S)).getD j 1 = wordVal S ws[j] by simp [hj]]
    exact wordT_rep S gs gi hgs hgi _
  · have hn : ws[j]? = none := List.getElem?_eq_none (by omega)
    rw [show (ws.map (wordT n gs gi)).toArray.getD j (idTab n) = idTab n by simp [hn],
      show (ws.map (wordVal S)).getD j 1 = 1 by simp [hn]]
    exact TabRep.idTab

theorem enumerates_of_words (S : List (Equiv.Perm (Fin n))) (gs gi : Array Tab)
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹) (ws : List (List ℤ)) {E : Enum}
    (h : enumOK n (ws.map (wordT n gs gi)).toArray E = true) :
    Enumerates (Subgroup.closure {g | g ∈ ws.map (wordVal S)}) E.tabs.toList := by
  set L : List (Equiv.Perm (Fin n)) := ws.map (wordVal S) with hLdef
  have heG := rep_map_words S gs gi hgs hgi ws
  have hEsz : (ws.map (wordT n gs gi)).toArray.size = ws.length := by simp
  have hLlen : L.length = ws.length := by simp [hLdef]
  have heG' : ∀ j (hj : j < ws.length),
      TabRep (ws.map (wordT n gs gi)).toArray[j]! (L.getD j 1) := by
    intro j hj
    have := heG j
    rwa [show (ws.map (wordT n gs gi)).toArray.getD j (idTab n) =
      (ws.map (wordT n gs gi)).toArray[j]! by simp [hj]] at this
  have hLmem : ∀ j, j < ws.length → L.getD j 1 ∈ L := by
    intro j hj
    rw [show L.getD j 1 = L[j]'(by omega) by simp [List.getD_eq_getElem?_getD, hLlen, hj]]
    exact List.getElem_mem _
  have hA : ∀ g ∈ {g | g ∈ L}, ∃ j < (ws.map (wordT n gs gi)).toArray.size,
      TabRep (ws.map (wordT n gs gi)).toArray[j]! g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < ws.length := by omega
    refine ⟨j, by rw [hEsz]; exact hj', ?_⟩
    have := heG' j hj'
    rwa [show L.getD j 1 = L[j] by simp [hj]] at this
  have hgensE : ∀ j < (ws.map (wordT n gs gi)).toArray.size,
      ∃ g ∈ {g | g ∈ L}, TabRep (ws.map (wordT n gs gi)).toArray[j]! g := by
    intro j hj
    have hj' : j < ws.length := by rwa [hEsz] at hj
    exact ⟨L.getD j 1, hLmem j hj', heG' j hj'⟩
  exact enumerates_closure (A := {g | g ∈ L}) hA hgensE h

theorem rep_getElem!_of_words (S : List (Equiv.Perm (Fin n))) (gs gi : Array Tab)
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹) (ws : List (List ℤ)) {j : ℕ}
    (hj : j < ws.length) :
    TabRep (ws.map (wordT n gs gi)).toArray[j]! ((ws.map (wordVal S))[j]'(by simpa using hj)) := by
  have := rep_map_words S gs gi hgs hgi ws j
  rwa [show (ws.map (wordT n gs gi)).toArray.getD j (idTab n) =
      (ws.map (wordT n gs gi)).toArray[j]! by simp [hj],
    show (ws.map (wordVal S)).getD j 1 = (ws.map (wordVal S))[j]'(by simpa using hj) by
      simp [hj]] at this


theorem mem_enum_iff {H : Subgroup (Equiv.Perm (Fin n))} {T : List Tab} (hH : Enumerates H T)
    {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) : t ∈ T ↔ g ∈ H :=
  ⟨fun h => by
    obtain ⟨g', hg', hr⟩ := hH.sound t h
    rwa [ht.perm_eq hr],
  fun h => by
    obtain ⟨t', ht', hr⟩ := hH.complete g h
    rwa [ht.tab_eq hr]⟩

theorem found_iff_mem {H : Subgroup (Equiv.Perm (Fin n))} {gens : Array Tab} {E : Enum}
    (hE : enumOK n gens E = true) (hH : Enumerates H E.tabs.toList) {t : Tab}
    {g : Equiv.Perm (Fin n)} (ht : TabRep t g) :
    found (indexOf E.tabs) E.tabs t = true ↔ g ∈ H :=
  (found_iff_of_enumOK hE t).trans (mem_enum_iff hH ht)

theorem inv_rep_of_check {gs gi : Array Tab} {S : List (Equiv.Perm (Fin n))}
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1)) (hsz : gi.size = gs.size)
    (hinv : ∀ k < gs.size, (gi[k]!).size = n ∧ comp n gi[k]! gs[k]! = idTab n) :
    ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹ := by
  intro j
  by_cases hj : j < gs.size
  · obtain ⟨h1, h2⟩ := hinv j hj
    rw [show gi.getD j (idTab n) = gi[j]! by simp [hsz, hj]]
    have := hgs j
    rw [show gs.getD j (idTab n) = gs[j]! by simp [hj]] at this
    exact this.inv h1 h2
  · have h0 : gs.getD j (idTab n) = idTab n := by simp [hj]
    have h0' : gi.getD j (idTab n) = idTab n := by simp [hsz, hj]
    rw [h0']
    have h1 := hgs j
    rw [h0] at h1
    have : S.getD j 1 = 1 := (TabRep.perm_eq TabRep.idTab h1).symm
    rw [this, inv_one]
    exact TabRep.idTab


theorem getD_cons_array_succ (x d : Tab) (arr : Array Tab) (i : ℕ) :
    (#[x] ++ arr).getD (i + 1) d = arr.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append]
  simp

theorem getD_append_singleton_lt (A : Array Tab) (x d : Tab) {i : ℕ} (hi : i < A.size) :
    (A ++ #[x]).getD i d = A.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append]
  simp [hi]

theorem getD_append_singleton_self (A : Array Tab) (x d : Tab) :
    (A ++ #[x]).getD A.size d = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  simp

theorem getD_append_singleton_gt (A : Array Tab) (x d : Tab) {i : ℕ} (hi : A.size < i) :
    (A ++ #[x]).getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  have h1 : ¬ i < A.size := by omega
  have h2 : (#[x] : Array Tab)[i - A.size]? = none := by
    rw [Array.getElem?_eq_none]; simp; omega
  simp [h1, h2]

theorem rep_append_singleton {A : Array Tab} {L : List (Equiv.Perm (Fin n))}
    (φ : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (hφ : φ 1 = 1)
    (hA : ∀ j, TabRep (A.getD j (idTab n)) (φ (L.getD j 1))) (hsz : A.size = L.length)
    {x : Tab} {g : Equiv.Perm (Fin n)} (hx : TabRep x (φ g)) :
    ∀ j, TabRep ((A ++ #[x]).getD j (idTab n)) (φ ((L ++ [g]).getD j 1)) := by
  intro j
  rcases lt_trichotomy j A.size with h | h | h
  · rw [getD_append_singleton_lt A x _ h, List.getD_append L [g] 1 j (by omega)]
    exact hA j
  · subst h
    rw [getD_append_singleton_self, hsz, List.getD_append_right L [g] 1 L.length le_rfl]
    simpa using hx
  · rw [getD_append_singleton_gt A x _ h]
    have h1 : (L ++ [g]).getD j 1 = 1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [h1, hφ]
    exact TabRep.idTab

theorem rep_cons_array {A : Array Tab} {L : List (Equiv.Perm (Fin n))}
    (hA : ∀ j, TabRep (A.getD j (idTab n)) (L.getD j 1)) :
    ∀ j, TabRep ((#[idTab n] ++ A).getD j (idTab n)) ((1 :: L).getD j 1) := by
  intro j
  rcases j with _ | j
  · simpa using TabRep.idTab (n := n)
  · rw [getD_cons_array_succ, List.getD_cons_succ]
    exact hA j

end Tables

theorem isSolvable_of_normal_sq {X : Type*} [Group X] [Finite X] {p a b : ℕ} (hp : p.Prime)
    {N R : Subgroup X} (hRN : R ≤ N) (hnorm : N ≤ Subgroup.normalizer (R : Set X))
    (hR : Nat.card R = p ^ 2) (hN : Nat.card N = p ^ 2 * (2 ^ a * 3 ^ b)) :
    Group.IsSolvable N := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).2 hnorm
  have hR' : Nat.card (R.subgroupOf N) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv, hR]
  have hRp : IsPGroup p (R.subgroupOf N) := IsPGroup.of_card hR'
  have : Group.IsNilpotent (R.subgroupOf N) := hRp.isNilpotent
  have hsolvR : Group.IsSolvable (R.subgroupOf N) := inferInstance
  have hq : Nat.card (N ⧸ R.subgroupOf N) = 2 ^ a * 3 ^ b := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf N)
    rw [hN, hR'] at h
    have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [h, mul_comm])).symm
  have hsolvQ : Group.IsSolvable (N ⧸ R.subgroupOf N) := by
    have := Fintype.ofFinite (N ⧸ R.subgroupOf N)
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, hq])
  exact Group.isSolvable_of_ker_le_range (R.subgroupOf N).subtype
    (QuotientGroup.mk' (R.subgroupOf N)) (by simp [QuotientGroup.ker_mk'])

@[expose] def LocalData (p m lam e : ℕ) {Q : Type*} [Group Q] (G R : Subgroup Q) : Prop :=
  R ≤ G ∧ Nat.card R = p ^ 2 ∧
  (∀ Y : Subgroup Q, Subgroup.normalizer (R : Set Q) ⊓ G ≤ Y → Y ≤ G →
    Y = Subgroup.normalizer (R : Set Q) ⊓ G ∨ Y = G) ∧
  (∀ g ∈ G, (∀ r ∈ R, g * r = r * g) → g ∈ R) ∧
  Group.IsSolvable ↥(Subgroup.normalizer (R : Set Q) ⊓ G) ∧
  ∃ t ∈ Subgroup.normalizer (R : Set Q) ⊓ G,
    (∀ x ∈ R, t ^ m * x * (t ^ m)⁻¹ = x ^ lam) ∧ (∀ x ∈ R, t ^ e * x * (t ^ e)⁻¹ = x⁻¹) ∧
    ∀ k : ℕ, 0 < k → k < m → ∀ Y₀ : Subgroup Q, Y₀ ≤ R → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set Q)

section Perm

variable {D : Data}

@[expose] def Gsub (S : List (Equiv.Perm (Fin D.n))) : Subgroup (Equiv.Perm (Fin D.n)) :=
  Subgroup.closure {g | g ∈ S}

@[expose] def Rsub (D : Data) (S : List (Equiv.Perm (Fin D.n))) :
    Subgroup (Equiv.Perm (Fin D.n)) :=
  Subgroup.closure {g | g ∈ (rWs D).map (wordVal S)}

@[expose] def Nsub (D : Data) (S : List (Equiv.Perm (Fin D.n))) :
    Subgroup (Equiv.Perm (Fin D.n)) :=
  Subgroup.closure {g | g ∈ D.nW.map (wordVal S)}

@[expose] def repElts (D : Data) (S : List (Equiv.Perm (Fin D.n))) : List (Equiv.Perm (Fin D.n)) :=
  1 :: D.repW.map (wordVal S)

variable {S : List (Equiv.Perm (Fin D.n))}

theorem Gsub_mem_of_mem {g : Equiv.Perm (Fin D.n)} (hg : g ∈ S) : g ∈ Gsub S :=
  Subgroup.subset_closure hg

theorem wordVal_mem_Gsub (w : List ℤ) : wordVal S w ∈ Gsub S :=
  wordVal_mem S (Gsub S) (fun _ hg => Gsub_mem_of_mem hg) w

theorem Rsub_le_Gsub : Rsub D S ≤ Gsub S := by
  unfold Rsub
  rw [Subgroup.closure_le]
  rintro _ hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordVal_mem_Gsub w

theorem Nsub_le_Gsub : Nsub D S ≤ Gsub S := by
  unfold Nsub
  rw [Subgroup.closure_le]
  rintro _ hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordVal_mem_Gsub w

theorem wT_rep (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹) (w : List ℤ) :
    TabRep (wT D w) (wordVal S w) :=
  wordT_rep S D.gT (giT D) hgs hgi w

theorem giT_rep (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (h : checkInv D = true) : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹ := by
  refine inv_rep_of_check hgs (by simp [giT]) ?_
  simp only [checkInv, allBelow_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem getD_mem_of_lt {α : Type*} {L : List α} {i : ℕ} (h : i < L.length) (d : α) :
    L.getD i d ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem repElts_mem {g : Equiv.Perm (Fin D.n)} (hg : g ∈ repElts D S) : g ∈ Gsub S := by
  unfold repElts at hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact one_mem _
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem_Gsub w

theorem invsOK_of_checkNormal (h : checkNormal D = true) :
    invsOK D.n (nGens D) (nGensI D) = true := by
  simp only [checkNormal, normalOK, Bool.and_eq_true] at h
  exact h.1

variable (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
  (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)

include hgs hgi

theorem enum_R (h : checkR D = true) : Enumerates (Rsub D S) (rEnum D).tabs.toList := by
  simp only [checkR, Bool.and_eq_true] at h
  exact enumerates_of_words S D.gT (giT D) hgs hgi (rWs D) h.1

theorem card_R (h : checkR D = true) : Nat.card (Rsub D S) = D.p ^ 2 := by
  have h' := h
  simp only [checkR, Bool.and_eq_true, beq_iff_eq] at h'
  rw [(enum_R hgs hgi h).card, Array.length_toList, h'.2]

theorem enum_N (h : checkN D = true) : Enumerates (Nsub D S) (nEnum D).tabs.toList := by
  simp only [checkN, Bool.and_eq_true] at h
  exact enumerates_of_words S D.gT (giT D) hgs hgi D.nW h.1

theorem card_N (h : checkN D = true) : Nat.card (Nsub D S) = D.nOrder := by
  have h' := h
  simp only [checkN, Bool.and_eq_true, beq_iff_eq] at h'
  rw [(enum_N hgs hgi h).card, Array.length_toList, h'.2]

theorem N_le_normalizer (hR : checkR D = true) (hNorm : checkNormal D = true) :
    Nsub D S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
  unfold Nsub
  rw [Subgroup.closure_le]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj' : j < D.nW.length := by simpa using hj
  refine mem_normalizer_of_conj_gens (A := {g | g ∈ (rWs D).map (wordVal S)}) ?_
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  have hi' : i < (rWs D).length := by simpa using hi
  have hja : j < (nGens D).size := by simp [nGens, hj']
  have hia : i < (rGens D).size := by simp [rGens, hi']
  exact (conj_mem_of_normalOK (enum_R hgs hgi hR) hNorm hja hia
    (rep_getElem!_of_words S D.gT (giT D) hgs hgi D.nW hj')
    (rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) hi')).1

theorem not_le_normalizer (hlen : S.length = D.gT.size) (hR : checkR D = true)
    (hMoves : checkMoves D = true) :
    ¬ Gsub S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
  intro hle
  have hRok : enumOK D.n (rGens D) (rEnum D) = true := by
    simp only [checkR, Bool.and_eq_true] at hR
    exact hR.1
  have hR' := enum_R hgs hgi hR
  simp only [checkMoves, anyBelow_eq_true, Bool.not_eq_true'] at hMoves
  obtain ⟨j, hj, hnot⟩ := hMoves
  have hjS : j < S.length := by omega
  have hsG : S[j] ∈ Gsub S := Gsub_mem_of_mem (List.getElem_mem hjS)
  have hsN := hle hsG
  have hs := hgs j
  rw [show D.gT.getD j (idTab D.n) = D.gT[j]! by simp [hj]] at hs
  rw [show S.getD j 1 = S[j] by simp [hjS]] at hs
  have hsi := hgi j
  rw [show (giT D).getD j (idTab D.n) = (giT D)[j]! by simp [giT, hj]] at hsi
  rw [show S.getD j 1 = S[j] by simp [hjS]] at hsi
  have hall : (allBelow (rGens D).size fun i =>
      found (indexOf (rEnum D).tabs) (rEnum D).tabs
        (conjTab D.n D.gT[j]! (giT D)[j]! (rGens D)[i]!)) = true := by
    rw [allBelow_eq_true]
    intro i hi
    have hi' : i < (rWs D).length := by simpa [rGens] using hi
    have hr : TabRep (rGens D)[i]! (((rWs D).map (wordVal S))[i]'(by simpa using hi')) :=
      rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) hi'
    rw [found_iff_mem hRok hR' (hs.conjTab hr hsi)]
    have hmem : ((rWs D).map (wordVal S))[i]'(by simpa using hi') ∈ Rsub D S :=
      Subgroup.subset_closure (List.getElem_mem _)
    exact ((Subgroup.mem_normalizer_iff.1 hsN _).1 hmem)
  rw [hall] at hnot
  exact Bool.noConfusion hnot

theorem torus_data (hp : D.p.Prime) (hR : checkR D = true) (hN : checkN D = true)
    (hT : checkTorus D = true) :
    ∃ t ∈ Nsub D S, (∀ x ∈ Rsub D S, t ^ D.tm * x * (t ^ D.tm)⁻¹ = x ^ D.tlam) ∧
      (∀ x ∈ Rsub D S, t ^ D.te * x * (t ^ D.te)⁻¹ = x⁻¹) ∧
      ∀ k : ℕ, 0 < k → k < D.tm → ∀ Y₀ : Subgroup (Equiv.Perm (Fin D.n)), Y₀ ≤ Rsub D S →
        Nat.card Y₀ = D.p → t ^ k ∉ Subgroup.normalizer (Y₀ : Set (Equiv.Perm (Fin D.n))) := by
  have htrep := wT_rep hgs hgi D.tW
  have hR' := enum_R hgs hgi hR
  have hN' := enum_N hgs hgi hN
  have hNok : enumOK D.n (nGens D) (nEnum D) = true := by
    simp only [checkN, Bool.and_eq_true] at hN
    exact hN.1
  simp only [checkTorus, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨hsz, hinv⟩, hfound⟩, hm⟩, he⟩, hk⟩ := hT
  have hti := htrep.inv hsz hinv
  refine ⟨wordVal S D.tW, (found_iff_mem hNok hN' htrep).1 hfound, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := hR'.exists_pos hx
    have hA := ((powT_rep htrep D.tm).comp hkx).comp (powT_rep hti D.tm)
    have := (hA.eq_iff (powT_rep hkx D.tlam)).1 (hm k hk)
    rwa [inv_pow] at this
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := hR'.exists_pos hx
    have hA := (((powT_rep htrep D.te).comp hkx).comp (powT_rep hti D.te)).comp hkx
    have := (hA.eq_iff TabRep.idTab).1 (he k hk)
    rw [inv_pow] at this
    exact mul_eq_one_iff_eq_inv.1 this
  · intro k hk0 hkm Y₀ hY₀R hY₀ hnorm
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hY₀ne : Y₀ ≠ ⊥ := by
      rintro rfl
      have : Nat.card (⊥ : Subgroup (Equiv.Perm (Fin D.n))) = 1 := Subgroup.card_bot
      rw [this] at hY₀
      exact hp.one_lt.ne hY₀
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hY₀ne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨hzp, hord⟩ := zpowers_eq_of_card_prime hp hY₀ hy hy1'
    obtain ⟨i, hi, hiy⟩ := hR'.exists_pos (hY₀R hy)
    have hnid : (rEnum D).tabs[i]! ≠ idTab D.n := fun h =>
      hy1' ((hiy.eq_iff TabRep.idTab).1 h)
    rcases hk k' (by omega) i hi with h1 | h1
    · exact hnid h1
    · have hmem : wordVal S D.tW ^ (k' + 1) * y * (wordVal S D.tW ^ (k' + 1))⁻¹ ∈ Y₀ :=
        (Subgroup.mem_normalizer_iff.1 hnorm y).1 hy
      rw [← hzp] at hmem
      obtain ⟨j, hj, hjy⟩ := exists_pow_lt_of_mem_zpowers hmem (by rw [hord]; exact hp.pos)
      rw [hord] at hj
      have hA := (((powT_rep htrep (k' + 1)).comp hiy).comp (powT_rep hti (k' + 1)))
      rw [inv_pow] at hA
      have := (hA.eq_iff (powT_rep hiy j)).2 hjy.symm
      have := h1 j hj
      simp_all


theorem nGensI_rep (hinvN : invsOK D.n (nGens D) (nGensI D) = true) :
    ∀ j, TabRep ((nGensI D).getD j (idTab D.n)) ((D.nW.map (wordVal S)).getD j 1)⁻¹ := by
  simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hinvN
  obtain ⟨hsz, hinv⟩ := hinvN
  exact inv_rep_of_check (gs := nGens D) (gi := nGensI D)
    (rep_map_words S D.gT (giT D) hgs hgi D.nW) hsz hinv

theorem repT_rep : ∀ i, TabRep ((repT D).getD i (idTab D.n)) ((repElts D S).getD i 1) :=
  rep_cons_array (rep_map_words S D.gT (giT D) hgs hgi D.repW)

theorem repI_rep (hinvs : invsOK D.n (repT D) (repI D) = true) :
    ∀ j, TabRep ((repI D).getD j (idTab D.n)) ((repElts D S).getD j 1)⁻¹ := by
  simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hinvs
  exact inv_rep_of_check (gs := repT D) (gi := repI D) (repT_rep hgs hgi) hinvs.1 hinvs.2

theorem conjCount_eq (hN : checkN D = true) (hfp : fpOK D.fpPts (nEnum D).tabs = true) {i : ℕ}
    (hi : i < (repT D).size) (hinvs : invsOK D.n (repT D) (repI D) = true) :
    conjCount D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repI D)[i]! (repT D)[i]! =
      Nat.card (conjStab (Nsub D S) ((repElts D S).getD i 1)) := by
  have hN' := enum_N hgs hgi hN
  have hx : TabRep (repT D)[i]! ((repElts D S).getD i 1) := by
    have := repT_rep hgs hgi i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hi]] at this
  have hxi : TabRep (repI D)[i]! ((repElts D S).getD i 1)⁻¹ := by
    have := repI_rep hgs hgi hinvs i
    have hi' : i < (repI D).size := by simpa [repI] using hi
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hi']] at this
  set g := (repElts D S).getD i 1 with hg
  unfold conjCount
  rw [countBelow_getElem! (nEnum D).tabs (fun t => memFp D.fpPts
    (indexOf ((nEnum D).tabs.map (fpTab D.fpPts))) ((nEnum D).tabs.map (fpTab D.fpPts))
    (nEnum D).tabs (comp D.n (comp D.n (repI D)[i]! t) (repT D)[i]!))]
  have hfilter := hN'.filter (K := (Nsub D S).comap (MulAut.conj g⁻¹).toMonoidHom)
    (fun t => memFp D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs
      (comp D.n (comp D.n (repI D)[i]! t) (repT D)[i]!)) (by
    intro t a ht
    rw [memFp_iff hfp, mem_enum_iff hN' ((hxi.comp ht).comp hx)]
    simp [Subgroup.mem_comap])
  rw [← Enumerates.card hfilter, conjStab, inf_comm]

theorem sum_eq (hN : checkN D = true) (hfp : fpOK D.fpPts (nEnum D).tabs = true)
    (hinvs : invsOK D.n (repT D) (repI D) = true)
    (hsum : dcSum D.n D.nOrder D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = D.gOrder) :
    ∑ i ∈ Finset.range (D.repW.length + 1), Nat.card (Nsub D S) * Nat.card (Nsub D S) /
      Nat.card (conjStab (Nsub D S) ((repElts D S).getD i 1)) = D.gOrder := by
  rw [← hsum, dcSum, foldl_range_add]
  have hsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  rw [hsz, card_N hgs hgi hN]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [conjCount_eq hgs hgi hN hfp (by omega) hinvs]

theorem maximal_N (hlen : S.length = D.gT.size) (hcard : Nat.card (Gsub S) = D.gOrder)
    (hN : checkN D = true) (hinvN : invsOK D.n (nGens D) (nGensI D) = true)
    (hMax : checkMax D = true) :
    ∀ Y : Subgroup (Equiv.Perm (Fin D.n)), Nsub D S ≤ Y → Y ≤ Gsub S →
      Y = Nsub D S ∨ Y = Gsub S := by
  have hN' := enum_N hgs hgi hN
  simp only [checkMax, Bool.and_eq_true, beq_iff_eq] at hMax
  obtain ⟨⟨⟨⟨hfp, hinvs⟩, hsum⟩, hdisj⟩, hgen⟩ := hMax
  simp only [dcDisjoint, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hdisj
  simp only [dcGenerate, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hgen
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hrisz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
  have hrepT := repT_rep hgs hgi
  have hrepI := repI_rep hgs hgi hinvs
  have hlenE : (repElts D S).length = D.repW.length + 1 := by simp [repElts]
  have hxT : ∀ i, i < D.repW.length + 1 → TabRep (repT D)[i]! ((repElts D S).getD i 1) := by
    intro i hi
    have := hrepT i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hrsz, hi]] at this
  have hxI : ∀ i, i < D.repW.length + 1 → TabRep (repI D)[i]! ((repElts D S).getD i 1)⁻¹ := by
    intro i hi
    have := hrepI i
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hrisz, hi]] at this
  refine maximal_of_doubleCosets Nsub_le_Gsub (fun i => (repElts D S).getD i 1) D.repW.length
    (by simp [repElts]) (fun i hi => repElts_mem (getD_mem_of_lt (by omega) 1))
    (by rw [sum_eq hgs hgi hN hfp hinvs hsum, hcard]) ?_ ?_
  · intro i hi j hj hij a ha hmem
    obtain ⟨k, hk, hka⟩ := hN'.exists_pos ha
    rcases hdisj i (by omega) j (by omega) with h | h
    · exact h hij
    · have hy := ((hxI i (by omega)).comp hka).comp (hxT j (by omega))
      have hmemT := (mem_enum_iff hN' hy).2 hmem
      have := (memFp_iff hfp _).2 hmemT
      rw [h k hk] at this
      exact Bool.noConfusion this
  · intro i hi1 hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi' : i' < D.repW.length := by omega
    obtain ⟨-, hgw⟩ := hgen
    obtain ⟨-, hwords⟩ := hgw i' hi'
    set Ln := D.nW.map (wordVal S) with hLn
    set Alph : List (Equiv.Perm (Fin D.n)) := Ln ++ [(repElts D S).getD (i' + 1) 1] with hAlph
    have hszN : (nGens D).size = Ln.length := by simp [nGens, hLn]
    have hszNI : (nGensI D).size = Ln.length := by simp [nGensI, nGens, hLn]
    have hAs : ∀ j, TabRep ((nGens D ++ #[(repT D)[i' + 1]!]).getD j (idTab D.n)) (Alph.getD j 1) :=
      rep_append_singleton (fun x => x) rfl (rep_map_words S D.gT (giT D) hgs hgi D.nW) hszN
        (hxT (i' + 1) (by omega))
    have hAi : ∀ j, TabRep ((nGensI D ++ #[(repI D)[i' + 1]!]).getD j (idTab D.n))
        ((Alph.getD j 1)⁻¹) :=
      rep_append_singleton (fun x => x⁻¹) inv_one (nGensI_rep hgs hgi hinvN) hszNI
        (hxI (i' + 1) (by omega))
    unfold Gsub
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hjg : j < D.gT.size := by omega
    have hword := hwords j hjg
    have hrw := wordT_rep Alph _ _ hAs hAi ((D.genW[i']!)[j]!)
    have hgj : TabRep D.gT[j]! S[j] := by
      have := hgs j
      rwa [show D.gT.getD j (idTab D.n) = D.gT[j]! by simp [hjg],
        show S.getD j 1 = S[j] by simp [hj]] at this
    have heq : wordVal Alph ((D.genW[i']!)[j]!) = S[j] := by
      rw [hword] at hrw
      exact hrw.perm_eq hgj
    rw [← heq]
    refine wordVal_mem Alph _ ?_ _
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact Subgroup.subset_closure (Set.mem_union_left _ (Subgroup.subset_closure hg))
    · rw [List.mem_singleton] at hg
      subst hg
      exact Subgroup.subset_closure (Set.mem_union_right _ rfl)

theorem normalizer_inf_eq (hlen : S.length = D.gT.size) (hcard : Nat.card (Gsub S) = D.gOrder)
    (hR : checkR D = true) (hN : checkN D = true) (hNorm : checkNormal D = true)
    (hMoves : checkMoves D = true) (hMax : checkMax D = true) :
    Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S = Nsub D S := by
  have hle : Nsub D S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S :=
    le_inf (N_le_normalizer hgs hgi hR hNorm) Nsub_le_Gsub
  rcases maximal_N hgs hgi hlen hcard hN (invsOK_of_checkNormal hNorm) hMax _ hle
    inf_le_right with h | h
  · exact h
  · exact absurd (inf_eq_right.1 h) (not_le_normalizer hgs hgi hlen hR hMoves)

theorem centralizer_le (hlen : S.length = D.gT.size) (hcard : Nat.card (Gsub S) = D.gOrder)
    (hR : checkR D = true) (hN : checkN D = true) (hNorm : checkNormal D = true)
    (hMoves : checkMoves D = true) (hMax : checkMax D = true) (hCent : checkCent D = true) :
    ∀ g ∈ Gsub S, (∀ r ∈ Rsub D S, g * r = r * g) → g ∈ Rsub D S := by
  intro g hgG hgc
  have hR' := enum_R hgs hgi hR
  have hN' := enum_N hgs hgi hN
  have hRok : enumOK D.n (rGens D) (rEnum D) = true := by
    simp only [checkR, Bool.and_eq_true] at hR
    exact hR.1
  have hNeq := normalizer_inf_eq hgs hgi hlen hcard hR hN hNorm hMoves hMax
  have hgN : g ∈ Nsub D S := by
    rw [← hNeq]
    refine ⟨Subgroup.mem_normalizer_fintype (S := (Rsub D S : Set (Equiv.Perm (Fin D.n))))
      (fun r hr => ?_), hgG⟩
    rw [hgc r hr, mul_inv_cancel_right]
    exact hr
  obtain ⟨k, hk, hgk⟩ := hN'.exists_pos hgN
  have hu : TabRep (rGens D)[0]! (wordVal S D.uW) :=
    rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) (j := 0) (by simp [rWs])
  have hv : TabRep (rGens D)[1]! (wordVal S D.vW) :=
    rep_getElem!_of_words S D.gT (giT D) hgs hgi (rWs D) (j := 1) (by simp [rWs])
  have huR : wordVal S D.uW ∈ Rsub D S := Subgroup.subset_closure (by simp [rWs])
  have hvR : wordVal S D.vW ∈ Rsub D S := Subgroup.subset_closure (by simp [rWs])
  simp only [checkCent, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hCent
  rcases hCent k hk with h | h
  · exfalso
    have hA : (comp D.n (nEnum D).tabs[k]! (rGens D)[0]! ==
        comp D.n (rGens D)[0]! (nEnum D).tabs[k]!) = true :=
      (((hgk.comp hu).beq_iff (hu.comp hgk)).2 (hgc _ huR))
    have hB : (comp D.n (nEnum D).tabs[k]! (rGens D)[1]! ==
        comp D.n (rGens D)[1]! (nEnum D).tabs[k]!) = true :=
      (((hgk.comp hv).beq_iff (hv.comp hgk)).2 (hgc _ hvR))
    rw [hA, hB] at h
    exact absurd h (by decide)
  · exact (found_iff_mem hRok hR' hgk).1 h

end Perm

theorem localData_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data} (hn : D.n = n)
    (hp : D.p.Prime) (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (hsolv : ∃ a b : ℕ, D.nOrder = D.p ^ 2 * (2 ^ a * 3 ^ b)) (h : check D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)),
      LocalData D.p D.tm D.tlam D.te (Subgroup.closure {g | g ∈ S}) R := by
  subst hn
  show ∃ R : Subgroup (Equiv.Perm (Fin D.n)), LocalData D.p D.tm D.tlam D.te (Gsub S) R
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hcardG : Nat.card (Gsub S) = D.gOrder := hcard
  have hNeq := normalizer_inf_eq hS hgi hlen hcardG hR hN hNorm hMoves hMax
  refine ⟨Rsub D S, Rsub_le_Gsub, card_R hS hgi hR, ?_, centralizer_le hS hgi hlen hcardG hR hN
    hNorm hMoves hMax hCent, ?_, ?_⟩
  · intro Y hY hYG
    rw [hNeq] at hY ⊢
    exact maximal_N hS hgi hlen hcardG hN (invsOK_of_checkNormal hNorm) hMax Y hY hYG
  · rw [hNeq]
    obtain ⟨a, b, hab⟩ := hsolv
    refine isSolvable_of_normal_sq (a := a) (b := b) hp ?_ (N_le_normalizer hS hgi hR hNorm)
      (card_R hS hgi hR) (by rw [card_N hS hgi hN, hab])
    rw [← hNeq]
    exact le_inf Subgroup.le_normalizer Rsub_le_Gsub
  · obtain ⟨t, htN, h1, h2, h3⟩ := torus_data hS hgi hp hR hN hTorus
    exact ⟨t, by rw [hNeq]; exact htN, h1, h2, h3⟩


end CFSG.AGLEmbedding.MaxD2
