module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8Core
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.ClassSpec
public import Certificates.Data.S7TwinCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf18CaseIB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf21M20
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf23AViolA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3OddStand
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
public import CFSG.ClassicalInvolution.Q3.TL4Res2FXDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native Certificates.S7Twin Certificates.S5Rows
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

variable {n : ℕ}

theorem exists_of_forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons hab h, _, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h'⟩ := exists_of_forall₂_right h hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

theorem exists_of_forall₂_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, ha => absurd ha List.not_mem_nil
  | _, _, .cons hab h, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h'⟩ := exists_of_forall₂_left h ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h'⟩

theorem forall₂_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ (k : ℕ) (h₁ : k < l₁.length) (h₂ : k < l₂.length), R l₁[k] l₂[k]
  | _, _, .nil, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _, _, .cons hab _, 0, _, _ => hab
  | _, _, .cons _ h, k + 1, h₁, h₂ =>
    forall₂_getElem h k (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

theorem tblEq_iff_eq {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h) :
    tblEq n S T = true ↔ g = h := by
  constructor
  · intro e
    exact rep_unique hS (rep_of_tblEq hT e)
  · rintro rfl
    rw [tblEq_iff]
    intro i hi
    rw [hS i hi, hT i hi]

theorem commT_iff_commute {x y : Table} {xg yg : Equiv.Perm (Fin n)} (hx : Rep n x xg)
    (hy : Rep n y yg) : commT n x y = true ↔ xg * yg = yg * xg :=
  tblEq_iff_eq (Rep.compT hx hy) (Rep.compT hy hx)

theorem memT_iff {L : List Table} {l : List (Equiv.Perm (Fin n))} (hL : List.Forall₂ (Rep n) L l)
    {X : Table} {x : Equiv.Perm (Fin n)} (hX : Rep n X x) : memT n L X = true ↔ x ∈ l := by
  unfold memT
  induction hL with
  | nil => simp
  | cons hT _ ih =>
    rw [List.any_cons, Bool.or_eq_true, ih, tblEq_iff_eq hX hT, List.mem_cons]

theorem sqOneT_iff (hn : n < 2 ^ 32) {A : Table} {a : Equiv.Perm (Fin n)} (hA : Rep n A a) :
    sqOneT n A = true ↔ a * a = 1 :=
  tblEq_iff_eq (Rep.compT hA hA) (Rep.idT hn)

theorem forall₂_spanT (hn : n < 2 ^ 32) {R Ri Y Yi : Table} {r y : Equiv.Perm (Fin n)}
    (hR : Rep n R r) (hRi : Rep n Ri r⁻¹) (hY : Rep n Y y) (hYi : Rep n Yi y⁻¹) :
    List.Forall₂ (Rep n) (spanT n R Ri Y Yi) (q8Span r y) := by
  unfold spanT q8Span
  refine .cons (Rep.idT hn) (.cons ?_ (.cons hR (.cons hRi (.cons hY (.cons hYi
    (.cons (Rep.compT hR hY) (.cons (Rep.compT hY hR) .nil)))))))
  rw [sq]
  exact Rep.compT hR hR

theorem forall₂_conj {sp : List Table} {l : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) sp l) {C Ci : Table} {c : Equiv.Perm (Fin n)} (hC : Rep n C c)
    (hCi : Rep n Ci c⁻¹) :
    List.Forall₂ (Rep n) (sp.map (conjT n C Ci)) (l.map fun t => c * t * c⁻¹) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ hT => rep_conjT hC hCi hT

theorem q8PairT_of_q8Rel {R Ri Y : Table} {r y : Equiv.Perm (Fin n)} (hR : Rep n R r)
    (hRi : Rep n Ri r⁻¹) (hY : Rep n Y y) (h : Q8Rel r y) : q8PairT n R Ri Y = true := by
  unfold q8PairT
  rw [Bool.and_eq_true, tblEq_iff_eq (Rep.compT hR hR) (Rep.compT hY hY),
    tblEq_iff_eq (Rep.compT hR hY) (Rep.compT hY hRi), ← sq, ← sq]
  exact ⟨h.2.2.1, CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert.q8Rel_mul_j h⟩

theorem q8RelT_spec (hn : n < 2 ^ 32) {X Xi Y Yi : Table} {x y : Equiv.Perm (Fin n)}
    (hX : Rep n X x) (hXi : Rep n Xi x⁻¹) (hY : Rep n Y y) (hYi : Rep n Yi y⁻¹)
    (h : q8RelT n X Xi Y Yi = true) : Q8Rel x y := by
  unfold q8RelT at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hX2 := Rep.compT hX hX
  rw [tblEq_iff_eq (Rep.compT hX2 hX2) (Rep.idT hn)] at h1
  rw [tblEq_iff_eq hX2 (Rep.compT hY hY)] at h3
  rw [tblEq_iff_eq (Rep.compT (Rep.compT hYi hX) hY) hXi] at h4
  refine ⟨?_, fun hx => ?_, by rw [sq, sq]; exact h3, h4⟩
  · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    exact h1
  · rw [sq] at hx
    have : tblEq n (compT n X X) (idT n) = true := (tblEq_iff_eq hX2 (Rep.idT hn)).mpr hx
    rw [this] at h2
    exact absurd h2 (by decide)

theorem getD_mem_or_eq {α : Type*} (T : Array α) (i : ℕ) (d : α) :
    T.getD i d ∈ T.toList ∨ T.getD i d = d := by
  rw [Array.getD]
  split_ifs with hi
  · exact Or.inl (Array.getElem_mem_toList hi)
  · exact Or.inr rfl

theorem cands_spec (hn : n < 2 ^ 32) {H : Subgroup (Equiv.Perm (Fin n))}
    (L : List (Equiv.Perm (Fin n))) (hL : ∀ g ∈ L, g ∈ H) (perRep : List (List ℕ)) :
    ∀ cs ∈ perRep.map (fun l => l.map fun i =>
      ((L.map fun g => (toTable g, toTable g⁻¹)).toArray).getD i
        (toTable (1 : Equiv.Perm (Fin n)), toTable (1 : Equiv.Perm (Fin n)))),
      ∀ c ∈ cs, ∃ g ∈ H, Rep n c.1 g ∧ Rep n c.2 g⁻¹ := by
  intro cs hcs c hc
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hcs
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  rcases getD_mem_or_eq ((L.map fun g => (toTable g, toTable g⁻¹)).toArray) i
      (toTable (1 : Equiv.Perm (Fin n)), toTable (1 : Equiv.Perm (Fin n))) with h | h
  · rw [List.toList_toArray] at h
    obtain ⟨g, hg, hgc⟩ := List.mem_map.mp h
    rw [← hgc]
    exact ⟨g, hL g hg, rep_toTable hn g, rep_toTable hn g⁻¹⟩
  · rw [h]
    exact ⟨1, H.one_mem, rep_toTable hn 1, by rw [inv_one]; exact rep_toTable hn 1⟩

theorem pairWitT_spec (hn : n < 2 ^ 32) {sp0 sp : List Table} {x₀ y₀ r y : Equiv.Perm (Fin n)}
    (h0 : List.Forall₂ (Rep n) sp0 (q8Span x₀ y₀)) (hsp : List.Forall₂ (Rep n) sp (q8Span r y))
    {R C Ci : Table} {c : Equiv.Perm (Fin n)} (hR : Rep n R r) (hC : Rep n C c)
    (hCi : Rep n Ci c⁻¹) (h : pairWitT n sp0 sp R C Ci = true) : PairWit x₀ y₀ r y c := by
  have hJ := forall₂_conj hsp hC hCi
  set J := sp.map (conjT n C Ci) with hJdef
  have hmemJ : ∀ {a : Equiv.Perm (Fin n)},
      a ∈ (q8Span r y).map (fun t => c * t * c⁻¹) ↔ ∃ t ∈ q8Span r y, c * t * c⁻¹ = a := by
    intro a
    rw [List.mem_map]
  unfold pairWitT at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Bool.not_eq_true'] at h
  rcases h with (hg | ⟨⟨X, hX, hXn⟩, A, hA, hA2, hAJ⟩) | ⟨⟨hz, hno⟩, K, hK, W, hW, hKW⟩
  · refine Or.inl fun t ht => ?_
    obtain ⟨T, hT, hTt⟩ := exists_of_forall₂_right hsp ht
    have hrep := rep_conjT hC hCi hTt
    exact (memT_iff h0 hrep).mp (hg _ (List.mem_map_of_mem hT))
  · obtain ⟨x, hx, hXx⟩ := exists_of_forall₂_left hJ hX
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, ha, hAa⟩ := exists_of_forall₂_left hsp hA
    refine Or.inr (Or.inl ⟨⟨t, ht, fun hm => ?_⟩, a, ha, fun h1 => ?_, ?_⟩)
    · rw [← memT_iff hsp hXx] at hm
      rw [hm] at hXn
      exact absurd hXn (by decide)
    · rw [← sqOneT_iff hn hAa] at h1
      rw [h1] at hA2
      exact absurd hA2 (by decide)
    · exact hmemJ.mp ((memT_iff hJ hAa).mp hAJ)
  · refine Or.inr (Or.inr ⟨?_, fun a ha ha2 t ht he => ?_, ?_⟩)
    · exact hmemJ.mp ((memT_iff hJ (Rep.compT hR hR)).mp hz)
    · obtain ⟨A, hA, hAa⟩ := exists_of_forall₂_right hsp ha
      have h1 := hno A hA
      rcases h1 with h1 | h1
      · exact ha2 ((sqOneT_iff hn hAa).mp h1)
      · have : memT n J A = true := (memT_iff hJ hAa).mpr (hmemJ.mpr ⟨t, ht, he⟩)
        rw [this] at h1
        exact absurd h1 (by decide)
    · obtain ⟨k, hk, hKk⟩ := exists_of_forall₂_left hsp hK
      obtain ⟨w, hw, hWw⟩ := exists_of_forall₂_left hJ hW
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
      refine ⟨k, hk, t, ht, fun he => ?_⟩
      rw [← commT_iff_commute hKk hWw] at he
      rw [he] at hKW
      exact absurd hKW (by decide)

theorem orderOf_eq_four_of_q8Rel_right {r y : Equiv.Perm (Fin n)} (h : Q8Rel r y) :
    orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : y ^ 2 ≠ 1 := by rw [← h.2.2.1]; exact h.2.1
  have hy4 : y ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← h.2.2.1, ← pow_mul]
    exact h.1
  exact orderOf_eq_prime_pow (n := 1) (by simpa using hy2) (by simpa using hy4)

theorem repPairsT_spec (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {H : Subgroup (Equiv.Perm (Fin n))} {sp0 : List Table} {x₀ y₀ : Equiv.Perm (Fin n)}
    (h0 : List.Forall₂ (Rep n) sp0 (q8Span x₀ y₀)) {R : Table} {r : Equiv.Perm (Fin n)}
    (hR : Rep n R r) {cands : List (Table × Table)}
    (hc : ∀ c ∈ cands, ∃ g ∈ H, Rep n c.1 g ∧ Rep n c.2 g⁻¹)
    (h : repPairsT n sp0 (cosetOrderTables Q 1 4) R cands = true) :
    ∀ y ∈ Q.originalSubgroup, Q8Rel r y → ∃ c ∈ H, PairWit x₀ y₀ r y c := by
  intro y hy hry
  unfold repPairsT at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true] at h
  obtain ⟨hRi, hall⟩ := h
  have hRi' : Rep n (invT n R) r⁻¹ := Rep.inv_of_invOK hR hRi
  have hL := forall₂_cosetOrderTables hn Q 1 (m := 4) (by norm_num)
  have hyL : y ∈ (((enumeration Q).map (1 * ·)).filter
      fun h => decide (orderOf h = 4)).reverse := by
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_iff]
    exact ⟨List.mem_map.mpr ⟨y, (mem_enumeration_iff Q hQ y).mpr hy, one_mul y⟩,
      orderOf_eq_four_of_q8Rel_right hry⟩
  obtain ⟨Y, hY, hYy⟩ := exists_of_forall₂_right hL hyL
  rcases hall Y hY with h1 | ⟨hYi, c, hcm, hw⟩
  · rw [q8PairT_of_q8Rel hR hRi' hYy hry] at h1
    exact absurd h1 (by decide)
  · obtain ⟨g, hg, hc1, hc2⟩ := hc c hcm
    have hYi' : Rep n (invT n Y) y⁻¹ := Rep.inv_of_invOK hYy hYi
    exact ⟨g, hg, pairWitT_spec hn h0 (forall₂_spanT hn hR hRi' hYy hYi') hR hc1 hc2 hw⟩

theorem pairsOK_spec (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {H : Subgroup (Equiv.Perm (Fin n))} {sp0 : List Table} {x₀ y₀ : Equiv.Perm (Fin n)}
    (h0 : List.Forall₂ (Rep n) sp0 (q8Span x₀ y₀)) {repT : List Table}
    {reps : List (Equiv.Perm (Fin n))} (hreps : List.Forall₂ (Rep n) repT reps)
    {cands : List (List (Table × Table))}
    (hc : ∀ cs ∈ cands, ∀ c ∈ cs, ∃ g ∈ H, Rep n c.1 g ∧ Rep n c.2 g⁻¹)
    {L4 : List Table} (hL4 : L4 = cosetOrderTables Q 1 4)
    (h : pairsOK n sp0 L4 repT cands = true) :
    ∀ r ∈ reps, ∀ y ∈ Q.originalSubgroup, Q8Rel r y → ∃ c ∈ H, PairWit x₀ y₀ r y c := by
  subst hL4
  have h' : repT.length = cands.length ∧
      ∀ p ∈ repT.zip cands, repPairsT n sp0 (cosetOrderTables Q 1 4) p.1 p.2 = true := by
    unfold pairsOK at h
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    exact h
  obtain ⟨hlen, hall⟩ := h'
  intro r hr
  obtain ⟨k, hk, hkr⟩ := List.getElem_of_mem hr
  have hk' : k < repT.length := hreps.length_eq ▸ hk
  have hkc : k < cands.length := hlen ▸ hk'
  have hmem : (repT[k], cands[k]) ∈ repT.zip cands := by
    have hlt : k < (repT.zip cands).length := by rw [List.length_zip]; omega
    rw [← List.getElem_zip (h := hlt)]
    exact List.getElem_mem hlt
  have hRk : Rep n repT[k] r := by
    rw [← hkr]
    exact forall₂_getElem hreps k hk' hk
  have hpk := hall _ hmem
  have hck := hc _ (List.getElem_mem hkc)
  exact repPairsT_spec hn Q hQ h0 hRk hck hpk

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin
