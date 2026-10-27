module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Certificates

@[noinline, expose] def witnessCore (n : Nat) (gens gensInv : Array Table) (S : Array Table)
    (y : Table) : Bool :=
  S.toList.all (fun s => (List.range gens.size).all fun l =>
      S.toList.any (fun s' => tblEq n s' (conjT n gens[l]! gensInv[l]! s)) &&
        S.toList.any (fun s' => tblEq n s' (conjT n gensInv[l]! gens[l]! s))) &&
    S.toList.all (fun s => S.toList.all fun s' => commT n s s') &&
    S.toList.any (fun s => !commT n y s) && ordTest n 3 y

@[expose] def threeWitnessOK (n : Nat) (gens gensInv : Array Table) (q y : Table) (cap : Nat) :
    Bool :=
  let c := conjClosure n gens gensInv q cap
  conjTreeOK n gens gensInv q c.1 c.2.1 c.2.2 && witnessCore n gens gensInv c.1 y

variable {n : ℕ}

@[expose] def listTables (L : List (Equiv.Perm (Fin n))) : Array Table := (L.map toTable).toArray

@[expose] def listInvTables (L : List (Equiv.Perm (Fin n))) : Array Table :=
  (L.map fun g => toTable g⁻¹).toArray

theorem listTables_spec (hn : n < 2 ^ 32) {H : Subgroup (Equiv.Perm (Fin n))}
    {L : List (Equiv.Perm (Fin n))} (hL : ∀ g ∈ L, g ∈ H) :
    ∀ l < (listTables L).size, Rep n (listTables L)[l]! (L.getD l 1) ∧
      Rep n (listInvTables L)[l]! (L.getD l 1)⁻¹ ∧ L.getD l 1 ∈ H := by
  intro l hl
  have hlL : l < L.length := by simpa [listTables] using hl
  have hl' : l < (listInvTables L).size := by simpa [listInvTables] using hlL
  rw [getElem!_pos _ l hl, getElem!_pos _ l hl', List.getD_eq_getElem _ _ hlL]
  simp only [listTables, listInvTables, List.getElem_toArray, List.getElem_map]
  exact ⟨rep_toTable hn _, rep_toTable hn _, hL _ (List.getElem_mem hlL)⟩

theorem closure_listTables (L : List (Equiv.Perm (Fin n))) :
    closure {g | g ∈ L} ≤ closure {g | ∃ l < (listTables L).size, g = L.getD l 1} := by
  rw [closure_le]
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
  exact subset_closure ⟨l, by simpa [listTables] using hl, (List.getD_eq_getElem _ _ hl).symm⟩

theorem exists_getElem!_of_mem {S : Array Table} {s : Table} (h : s ∈ S.toList) :
    ∃ k < S.size, S[k]! = s := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  rw [Array.length_toList] at hk
  exact ⟨k, hk, by rw [getElem!_pos S k hk, Array.getElem_toList]⟩

theorem getElem!_mem {S : Array Table} {k : ℕ} (hk : k < S.size) : S[k]! ∈ S.toList := by
  rw [getElem!_pos S k hk, ← Array.getElem_toList]
  exact List.getElem_mem _

theorem compsSatisfy_of_threeWitnessOK_of_rep (H : Subgroup (Equiv.Perm (Fin n)))
    [Finite H] {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    (hgen : H ≤ closure {g | ∃ l < gens.size, g = gg l})
    {q y : Equiv.Perm (Fin n)} (hq : q ∈ H) (hy : y ∈ H) {Tq Ty : Table} (hTq : Rep n Tq q)
    (hTy : Rep n Ty y) {cap : ℕ} (h : threeWitnessOK n gens gensInv Tq Ty cap = true)
    (h9 : ¬ 9 ∣ Nat.card H) :
    CompsSatisfy H fun Y _ => ¬ 3 ∣ Nat.card Y := by
  simp only [threeWitnessOK, Bool.and_eq_true] at h
  obtain ⟨htree, hcore⟩ := h
  set c := conjClosure n gens gensInv Tq cap
  simp only [witnessCore, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Bool.not_eq_true'] at hcore
  obtain ⟨⟨⟨hclosed, hcommT⟩, ⟨s₀, hs₀, hy₀⟩⟩, hy3⟩ := hcore
  have hentry := conjTreeOK_spec H hg hTq htree
  set T : Set (Equiv.Perm (Fin n)) := {g | ∃ k < c.1.size, Rep n c.1[k]! g} with hT
  have hTH : T ⊆ H := by
    rintro g ⟨k, hk, hrep⟩
    obtain ⟨d, hd, hrepd⟩ := hentry k hk
    rw [rep_unique hrep hrepd]
    exact H.mul_mem (H.mul_mem hd hq) (H.inv_mem hd)
  have hstep : ∀ l < gens.size, ∀ g ∈ T, gg l * g * (gg l)⁻¹ ∈ T ∧ (gg l)⁻¹ * g * gg l ∈ T := by
    rintro l hl g ⟨k, hk, hrep⟩
    obtain ⟨hgl, hgil, -⟩ := hg l hl
    obtain ⟨⟨s', hs', heq⟩, ⟨s'', hs'', heq'⟩⟩ :=
      hclosed _ (getElem!_mem hk) l (List.mem_range.2 hl)
    obtain ⟨k', hk', rfl⟩ := exists_getElem!_of_mem hs'
    obtain ⟨k'', hk'', rfl⟩ := exists_getElem!_of_mem hs''
    refine ⟨⟨k', hk', rep_of_tblEq (rep_conjT hgl hgil hrep) heq⟩, ⟨k'', hk'', ?_⟩⟩
    have h1 := rep_conjT hgil (by simpa using hgl) hrep
    simpa only [inv_inv] using rep_of_tblEq h1 heq'
  have hkey : ∀ x ∈ closure {g | ∃ l < gens.size, g = gg l}, ∀ g ∈ T, x * g * x⁻¹ ∈ T := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => intro g hg; simpa using hg
    | mul_left a ha b _ ih =>
      obtain ⟨l, hl, rfl⟩ := ha
      intro g hgT
      have := (hstep l hl _ (ih g hgT)).1
      simpa only [mul_inv_rev, mul_assoc] using this
    | inv_mul_cancel a ha b _ ih =>
      obtain ⟨l, hl, rfl⟩ := ha
      intro g hgT
      have := (hstep l hl _ (ih g hgT)).2
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  have hconj : ∀ x ∈ H, ∀ g ∈ T, x * g * x⁻¹ ∈ T := fun x hx => hkey x (hgen hx)
  set S : Set H := {h | (h : Equiv.Perm (Fin n)) ∈ T}
  have hy3' : orderOf (⟨y, hy⟩ : H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact (ordTest_iff perm_faithful hTy (by norm_num)).1 hy3
  refine not_three_dvd_card_of_witness S (fun k s hs => ?_) (fun s hs s' hs' => ?_) hy3' h9 ?_
  · exact hconj k k.2 s hs
  · obtain ⟨k, hk, hrep⟩ := hs
    obtain ⟨k', hk', hrep'⟩ := hs'
    apply Subtype.ext
    exact (commT_iff hrep hrep').1 (hcommT _ (getElem!_mem hk) _ (getElem!_mem hk'))
  · obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem hs₀
    obtain ⟨d, hd, hrepd⟩ := hentry k hk
    have hmem : d * q * d⁻¹ ∈ H := H.mul_mem (H.mul_mem hd hq) (H.inv_mem hd)
    refine ⟨⟨d * q * d⁻¹, hmem⟩, ⟨k, hk, hrepd⟩, fun hc => ?_⟩
    have hc' : y * (d * q * d⁻¹) = d * q * d⁻¹ * y := congrArg Subtype.val hc
    have := (commT_iff hTy hrepd).2 hc'
    rw [hy₀] at this
    exact Bool.false_ne_true this

theorem compsSatisfy_of_threeWitnessOK (hn : n < 2 ^ 32) (H : Subgroup (Equiv.Perm (Fin n)))
    [Finite H] {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    (hgen : H ≤ closure {g | ∃ l < gens.size, g = gg l})
    {q y : Equiv.Perm (Fin n)} (hq : q ∈ H) (hy : y ∈ H) {cap : ℕ}
    (h : threeWitnessOK n gens gensInv (toTable q) (toTable y) cap = true)
    (h9 : ¬ 9 ∣ Nat.card H) :
    CompsSatisfy H fun Y _ => ¬ 3 ∣ Nat.card Y :=
  compsSatisfy_of_threeWitnessOK_of_rep H hg hgen hq hy (rep_toTable hn q) (rep_toTable hn y) h h9

theorem compsSatisfy_centralizerIn_of_reps (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    {P : (Y : Type) → [Group Y] → Prop} (hP : IsoInvariant P)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n))))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2 =
        Nat.card Q.originalSubgroup ∧ CompsSatisfy d.2 P) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      CompsSatisfy (centralizerIn Q.originalSubgroup u) P := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) ((data.map Prod.fst).map toTable)
      cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard, hKP⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  rw [centralizerIn_conj _ hc, hcent]
  exact CompsSatisfy.of_mulEquiv hP (conjEquiv d.2 c).symm hKP

theorem compsSatisfy_centralizer_of_mulEquiv {M : Type} [Group M] (H : Subgroup M)
    {P : (Y : Type) → [Group Y] → Prop} (hP : IsoInvariant P)
    (h : ∀ u ∈ H, orderOf u = 2 → CompsSatisfy (centralizerIn H u) P) {G : Type} [Group G]
    (e : G ≃* H) (t : G) (ht : orderOf t = 2) : CompsSatisfy (centralizer ({t} : Set G)) P := by
  have hu : orderOf ((e t : H) : M) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  exact CompsSatisfy.of_mulEquiv hP ((centralizerEquiv e t).trans
    (centralizerSubtypeEquiv H (e t))) (h _ (e t).2 hu)

end CFSG.ComponentClassification.RestrictedStd.Spor
