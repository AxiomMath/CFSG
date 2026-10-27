module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoSylowCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42Enum

public section

namespace CFSG.AGLEmbedding.E6Two

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec4.Item434F42 (wordElt wordElt_nil wordElt_cons wordElt_append
  wordElt_mem enum_spec)

theorem getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β)
    {k : ℕ} (hk : k < A.size) : (A.map f)[k]! = f A[k]! := by
  rw [getElem!_pos (A.map f) k (by simpa using hk), getElem!_pos A k hk]
  simp

theorem distinctE_spec : ∀ l : List ℕ, distinctE l = true →
    l.Pairwise fun a b => eqE a b = false
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    simp only [distinctE, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    exact List.Pairwise.cons h.1 (distinctE_spec l (by simpa [distinctE] using h.2))

theorem enumOKE_letters {gb : Array ℕ} {L : List (List ℕ)} {vals : List ℕ}
    (h : enumOKE gb L vals = true) : ∀ w ∈ L, ∀ l ∈ w, l < gb.size := by
  simp only [enumOKE, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem hasDistinctAux_spec {α : Type} (f : α → ℕ) :
    ∀ (fuel k : ℕ) (l : List α), hasDistinctAux f fuel k l = true →
      ∃ l' : List α, l'.Sublist l ∧ l'.length = k ∧
        (l'.map f).Pairwise fun a b => eqE a b = false
  | _, 0, l, _ => ⟨[], List.nil_sublist _, rfl, List.Pairwise.nil⟩
  | 0, k + 1, l, h => by simp [hasDistinctAux] at h
  | fuel + 1, k + 1, [], h => by simp [hasDistinctAux] at h
  | fuel + 1, k + 1, a :: l, h => by
    simp only [hasDistinctAux, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨l', hsub, hlen, hpw⟩ := hasDistinctAux_spec f fuel k _ h
      refine ⟨a :: l', (hsub.trans (List.filter_sublist)).cons_cons a, by simp [hlen], ?_⟩
      rw [List.map_cons]
      refine List.Pairwise.cons ?_ hpw
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      have := (List.mem_filter.1 (hsub.subset hc)).2
      simpa using this
    · obtain ⟨l', hsub, hlen, hpw⟩ := hasDistinctAux_spec f fuel (k + 1) l h
      exact ⟨l', hsub.cons a, hlen, hpw⟩

theorem card_centralizer_mul_le {X : Type*} [Group X] [Finite X] {S : Subgroup X} {x : X}
    (us : List X) (hus : ∀ u ∈ us, u ∈ S)
    (hnd : (us.map fun u => u * x * u⁻¹).Nodup) :
    us.length * Nat.card (Subgroup.centralizer ({x} : Set X) ⊓ S : Subgroup X) ≤ Nat.card S := by
  classical
  set H := Subgroup.centralizer ({x} : Set X) with hH
  have hmul := Subgroup.relIndex_mul_card (H := H) (K := S)
  have hnd' : us.Nodup := List.Nodup.of_map _ hnd
  have hinj : ∀ a ∈ us, ∀ b ∈ us, a * x * a⁻¹ = b * x * b⁻¹ → a = b :=
    List.inj_on_of_nodup_map hnd
  have hlen : us.length ≤ H.relIndex S := by
    let φ : us.toFinset → S ⧸ H.subgroupOf S := fun u =>
      QuotientGroup.mk ⟨u, hus u (List.mem_toFinset.1 u.2)⟩
    have hφ : Function.Injective φ := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have ha' := List.mem_toFinset.1 ha
      have hb' := List.mem_toFinset.1 hb
      have h1 := QuotientGroup.eq.1 hab
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
      have h2 : x * (a⁻¹ * b) = (a⁻¹ * b) * x := h1 x (Set.mem_singleton x)
      refine Subtype.ext (hinj a ha' b hb' ?_)
      calc a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
        _ = a * ((a⁻¹ * b) * x) * b⁻¹ := by rw [h2]
        _ = b * x * b⁻¹ := by group
    have := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd'] at this
    exact this
  calc us.length * Nat.card (H ⊓ S : Subgroup X) ≤ H.relIndex S * Nat.card (H ⊓ S : Subgroup X) :=
        Nat.mul_le_mul_right _ hlen
    _ = Nat.card S := hmul

section Bits

variable {K : Type} [Field K]

theorem hasBitsE_wordElt [CharP K 2]
    {g : ℕ → adjointGroup Tag.E6 K} {gb : Array ℕ}
    (hg : ∀ l < gb.size, HasBitsE (g l) gb[l]!) (w : List ℕ) (hw : ∀ l ∈ w, l < gb.size) :
    HasBitsE (wordElt g w) (wordE gb w) := by
  have key : ∀ (w : List ℕ), (∀ l ∈ w, l < gb.size) → ∀ (acc : ℕ)
      (a : adjointGroup Tag.E6 K), HasBitsE a acc →
      HasBitsE (a * wordElt g w) (w.foldl (fun acc l => mulE acc gb[l]!) acc) := by
    intro w
    induction w with
    | nil => intro _ acc a h; simpa using h
    | cons l w ih =>
      intro hw acc a h
      rw [List.foldl_cons, wordElt_cons, ← mul_assoc]
      exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ _
        (h.mul (hg l (hw l (List.mem_cons_self ..))))
  have := key w hw oneE 1 hasBitsE_one
  rwa [one_mul] at this

theorem eqE_iff [CharP K 2] {g h : adjointGroup Tag.E6 K}
    {A B : ℕ} (hg : HasBitsE g A) (hh : HasBitsE h B) : eqE A B = true ↔ g = h := by
  rw [eqE, beq_iff_eq]
  exact (hg.eq_iff hh).symm

theorem enumE_sound [CharP K 2]
    [Finite (adjointGroup Tag.E6 K)] {g : ℕ → adjointGroup Tag.E6 K}
    {gb : Array ℕ} (hg : ∀ l < gb.size, HasBitsE (g l) gb[l]!) {L : List (List ℕ)}
    (h : enumOKE gb L (L.map (wordE gb)) = true) :
    (∀ x, x ∈ Subgroup.closure (g '' {k | k < gb.size}) ↔ ∃ w ∈ L, wordElt g w = x) ∧
      Nat.card (Subgroup.closure (g '' {k | k < gb.size})) = L.length := by
  have hL' := enumOKE_letters h
  simp only [enumOKE, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.any_eq_true, and_assoc] at h
  obtain ⟨-, h1, hcl, hnd⟩ := h
  have hbits : ∀ w ∈ L, HasBitsE (wordElt g w) (wordE gb w) := fun w hw =>
    hasBitsE_wordElt hg w (hL' w hw)
  refine enum_spec hL' h1 ?_ ?_
  · intro w hw k hk
    obtain ⟨x, hx, hxe⟩ := hcl _ (List.mem_map_of_mem hw) k hk
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hx
    refine ⟨w', hw', ?_⟩
    exact ((eqE_iff ((hbits w hw).mul (hg k hk)) (hbits w' hw')).1 hxe).symm
  · have hp := distinctE_spec _ hnd
    rw [List.pairwise_map] at hp
    rw [List.Nodup, List.pairwise_map]
    refine hp.imp_of_mem fun {a b} ha hb hab hE => ?_
    have := (eqE_iff (hbits a ha) (hbits b hb)).2 hE
    rw [hab] at this
    exact Bool.false_ne_true this

end Bits

section Gens

variable (K : Type) [Field K]

noncomputable def sGen (X : E6SylowData) (k : ℕ) : adjointGroup Tag.E6 K :=
  evalG K X.sW[k]!

end Gens

section Main

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem evalG_cLetters (X : E6SylowData) (c : List ℕ) :
    evalG K (cLetters X c) = wordElt (sGen K X) c := by
  induction c with
  | nil => simp [cLetters, evalG_nil, wordElt]
  | cons i c ih =>
    unfold cLetters at ih ⊢
    rw [List.map_cons, List.flatten_cons, evalG_append, ih, wordElt_cons]
    rfl

theorem sylow_facts [Finite (adjointGroup Tag.E6 K)] (X : E6SylowData)
    (h : e6SylowCheck X = true) :
    ∃ S : Subgroup (adjointGroup Tag.E6 K), Nat.card S = 729 ∧
      ∀ E : Subgroup (adjointGroup Tag.E6 K), E ≤ S → IsElemAbelian 3 E → Nat.card E < 243 := by
  have h' : e6SylowCheck' X (sgB X) (bfsE (sgB X) X.sFuel)
      ((bfsE (sgB X) X.sFuel).map (wordE (sgB X))) (cpsB X) = true := h
  unfold e6SylowCheck' at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨hcW, hEnum⟩, hOrd⟩, hBad⟩ := h'
  set gb := sgB X with hgb
  set L := bfsE gb X.sFuel with hL
  set cp := cpsB X with hcp
  have hgbits : ∀ l < gb.size, HasBitsE (sGen K X l) gb[l]! := by
    intro l hl
    have hl' : l < X.sW.size := by simpa [hgb, sgB] using hl
    rw [hgb, sgB, getElem!_map' X.sW evalE hl']
    exact hasBitsE_evalG X.sW[l]!
  obtain ⟨hmem, hcard⟩ := enumE_sound hgbits hEnum
  have hLl := enumOKE_letters hEnum
  refine ⟨Subgroup.closure (sGen K X '' {k | k < gb.size}), by rw [hcard]; exact hOrd, ?_⟩
  set S := Subgroup.closure (sGen K X '' {k | k < gb.size}) with hS
  have hgbS : ∀ l < gb.size, sGen K X l ∈ S := fun l hl => Subgroup.subset_closure ⟨l, hl, rfl⟩
  intro E hES hE
  by_contra hlt
  have hlt' : 243 ≤ Nat.card E := not_lt.1 hlt
  have hbad : ∀ x ∈ E, ∃ w ∈ badWords gb L cp, wordElt (sGen K X) w = x := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := (hmem x).1 (hES hx)
    refine ⟨w, ?_, hwx⟩
    unfold badWords
    rw [List.mem_filter]
    refine ⟨hw, ?_⟩
    by_contra hgood
    have hgood' : goodB cp (wordE gb w) = true := by simpa using hgood
    obtain ⟨l', hsub, hlen, hpw⟩ :=
      hasDistinctAux_spec (conjP (wordE gb w)) cp.length 4 cp hgood'
    have hcpmem : ∀ p ∈ l', ∃ c ∈ X.cW.toList, p = (cLetters X c, evalE (cLetters X c),
        evalE (cLetters X c).reverse) := by
      intro p hp
      obtain ⟨lw, hlw, rfl⟩ := List.mem_map.1 (hsub.subset hp)
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hlw
      exact ⟨c, hc, rfl⟩
    have hbx : HasBitsE (wordElt (sGen K X) w) (wordE gb w) :=
      hasBitsE_wordElt hgbits w (hLl w hw)
    rw [hwx] at hbx
    have hu : ∀ p ∈ l', evalG K p.1 ∈ S ∧ HasBitsE (evalG K p.1) p.2.1 ∧
        HasBitsE (evalG K p.1)⁻¹ p.2.2 := by
      intro p hp
      obtain ⟨c, hc, rfl⟩ := hcpmem p hp
      have hcl : ∀ i ∈ c, i < gb.size := by
        intro i hi
        have := List.all_eq_true.1 (List.all_eq_true.1 hcW c hc) i hi
        simpa [hgb, sgB] using this
      refine ⟨?_, hasBitsE_evalG _, ?_⟩
      · rw [evalG_cLetters]
        exact wordElt_mem hgbS hcl
      · rw [evalG_inv]
        exact hasBitsE_evalG _
    have hconj : ∀ p ∈ l', HasBitsE (evalG K p.1 * x * (evalG K p.1)⁻¹) (conjP (wordE gb w) p) := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := hu p hp
      exact (h1.mul hbx).mul h2
    have hnd : ((l'.map fun p => evalG K p.1).map fun u => u * x * u⁻¹).Nodup := by
      rw [List.map_map, List.Nodup, List.pairwise_map]
      rw [List.pairwise_map] at hpw
      refine hpw.imp_of_mem fun {a b} ha hb hab hE' => ?_
      have := (eqE_iff (hconj a ha) (hconj b hb)).2 hE'
      rw [hab] at this
      exact Bool.false_ne_true this
    have h4 := card_centralizer_mul_le (S := S) (x := x) (l'.map fun p => evalG K p.1)
      (fun u hu' => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu'
        exact (hu p hp).1) hnd
    rw [List.length_map, hlen, hcard] at h4
    have hEC : E ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)) ⊓ S := by
      intro e he
      refine Subgroup.mem_inf.2 ⟨?_, hES he⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hx⟩ ⟨e, he⟩)
    have := Subgroup.card_le_of_le hEC
    omega
  classical
  have hsub : (E : Set (adjointGroup Tag.E6 K)) ⊆
      ↑((badWords gb L cp).map (wordElt (sGen K X))).toFinset := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hbad x hx
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact List.mem_map_of_mem hw
  have h1 : Nat.card E ≤ ((badWords gb L cp).map (wordElt (sGen K X))).toFinset.card := by
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
  have h2 := List.toFinset_card_le ((badWords gb L cp).map (wordElt (sGen K X)))
  rw [List.length_map] at h2
  omega

end Main

end CFSG.AGLEmbedding.E6Two
