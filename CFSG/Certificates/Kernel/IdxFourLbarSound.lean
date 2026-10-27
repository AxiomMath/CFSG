
module

public import Certificates.Data.Kernel.IdxFourLbarK
public import CFSG.Certificates.Kernel.IdxFourChainSound
public import Mathlib.Tactic.Group

public section

namespace CFSG.KC.IF4L

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.GF2Type.Smith1979.GammaU

theorem testBit_xor_zero (m n : ℕ) : (m ^^^ n).testBit 0 = (m.testBit 0 ^^ n.testBit 0) :=
  Nat.testBit_xor m n 0

theorem xor_div_two' (m n : ℕ) : (m ^^^ n) / 2 = m / 2 ^^^ n / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, ← Nat.testBit_succ, ← Nat.testBit_succ]

theorem beq_mod_two (x : ℕ) : Nat.beq (x % 2) 1 = x.testBit 0 := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> rfl

section Group

variable {G : Type*} [Group G]

@[expose] def subG : List G → ℕ → G
  | [], _ => 1
  | g :: gs, m => (if m.testBit 0 then g else 1) * subG gs (m / 2)

theorem subG_nil (m : ℕ) : subG ([] : List G) m = 1 := rfl

theorem subG_cons (g : G) (gs : List G) (m : ℕ) :
    subG (g :: gs) m = (if m.testBit 0 then g else 1) * subG gs (m / 2) := rfl

theorem subG_zero : ∀ gs : List G, subG gs 0 = 1
  | [] => rfl
  | g :: gs => by rw [subG_cons, Nat.zero_div, subG_zero gs]; simp

@[expose] def CommInv (gs : List G) : Prop := ∀ g ∈ gs, g * g = 1 ∧ ∀ h ∈ gs, g * h = h * g

theorem CommInv.tail {g : G} {gs : List G} (h : CommInv (g :: gs)) : CommInv gs := fun a ha =>
  ⟨(h a (List.mem_cons_of_mem _ ha)).1, fun b hb =>
    (h a (List.mem_cons_of_mem _ ha)).2 b (List.mem_cons_of_mem _ hb)⟩

theorem comm_subG {a : G} : ∀ {gs : List G}, (∀ g ∈ gs, a * g = g * a) →
    ∀ m, a * subG gs m = subG gs m * a
  | [], _, m => by simp [subG_nil]
  | g :: gs, h, m => by
    have ih := comm_subG (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) (m / 2)
    have hg := h g List.mem_cons_self
    rw [subG_cons]
    split_ifs
    · rw [← mul_assoc, hg, mul_assoc, ih, mul_assoc]
    · rw [one_mul, ih]

theorem subG_xor : ∀ {gs : List G}, CommInv gs → ∀ m n,
    subG gs (m ^^^ n) = subG gs m * subG gs n
  | [], _, _, _ => by simp [subG_nil]
  | g :: gs, h, m, n => by
    have hgg := (h g List.mem_cons_self).1
    have hc : ∀ x, g * subG gs x = subG gs x * g :=
      comm_subG (fun b hb => (h g List.mem_cons_self).2 b (List.mem_cons_of_mem _ hb))
    rw [subG_cons, subG_cons, subG_cons, xor_div_two', subG_xor h.tail, testBit_xor_zero]
    cases m.testBit 0 <;> cases n.testBit 0 <;> simp only [Bool.xor_false, Bool.xor_true,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false, one_mul, mul_one]
    · rw [← mul_assoc, hc, mul_assoc]
    · rw [mul_assoc]
    · rw [hc, mul_assoc, ← mul_assoc g g, hgg, one_mul]

theorem subG_mul_self {gs : List G} (h : CommInv gs) (m : ℕ) : subG gs m * subG gs m = 1 := by
  rw [← subG_xor h, Nat.xor_self, subG_zero]

theorem subG_two_pow : ∀ (gs : List G) (i : ℕ) (h : i < gs.length), subG gs (2 ^ i) = gs[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | g :: gs, 0, _ => by
    rw [subG_cons]
    simp [subG_zero]
  | g :: gs, i + 1, h => by
    rw [subG_cons, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2),
      subG_two_pow gs i (by simpa using h)]
    simp [Nat.testBit_zero]

theorem subG_mem {K : Subgroup G} : ∀ {gs : List G}, (∀ g ∈ gs, g ∈ K) → ∀ m, subG gs m ∈ K
  | [], _, _ => K.one_mem
  | g :: gs, h, m => by
    rw [subG_cons]
    refine K.mul_mem ?_ (subG_mem (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) _)
    split_ifs
    · exact h g List.mem_cons_self
    · exact K.one_mem

theorem mem_closure_iff [Finite G] {gs : List G} (h : CommInv gs) {U : G} :
    U ∈ Subgroup.closure {g | g ∈ gs} ↔ ∃ m < 2 ^ gs.length, subG gs m = U := by
  constructor
  · intro hU
    refine mem_of_closure (K := {U | ∃ m < 2 ^ gs.length, subG gs m = U})
      ⟨0, Nat.two_pow_pos _, subG_zero gs⟩ ?_ hU
    rintro s hs _ ⟨m, hm, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    refine ⟨2 ^ i ^^^ m, Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) hi) hm, ?_⟩
    rw [subG_xor h, subG_two_pow gs i hi]
  · rintro ⟨m, -, rfl⟩
    exact subG_mem (fun g hg => Subgroup.subset_closure hg) m

theorem subG_inj {gs : List G} (h : CommInv gs)
    (hne : ∀ m, 0 < m → m < 2 ^ gs.length → subG gs m ≠ 1) {m n : ℕ} (hm : m < 2 ^ gs.length)
    (hn : n < 2 ^ gs.length) (e : subG gs m = subG gs n) : m = n := by
  by_contra hmn
  have hx : 0 < m ^^^ n := Nat.pos_of_ne_zero fun h0 => hmn (Nat.eq_of_testBit_eq fun i => by
    have := congrArg (fun x => x.testBit i) h0
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    revert this
    cases m.testBit i <;> cases n.testBit i <;> simp)
  refine hne _ hx (Nat.xor_lt_two_pow hm hn) ?_
  rw [subG_xor h, e, subG_mul_self h]

theorem card_closure [Finite G] {gs : List G} (h : CommInv gs)
    (hne : ∀ m, 0 < m → m < 2 ^ gs.length → subG gs m ≠ 1) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = 2 ^ gs.length := by
  let f : Fin (2 ^ gs.length) → Subgroup.closure {g | g ∈ gs} := fun m =>
    ⟨subG gs m, (mem_closure_iff h).2 ⟨m, m.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b e => Fin.ext (subG_inj h hne a.2 b.2 (congrArg Subtype.val e)), ?_⟩
    rintro ⟨U, hU⟩
    obtain ⟨m, hm, rfl⟩ := (mem_closure_iff h).1 hU
    exact ⟨⟨m, hm⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem subG_bif {gs : List G} (h : CommInv gs) (b : Bool) (c : ℕ) :
    subG gs (bif b then c else 0) = if b then subG gs c else 1 := by
  cases b
  · exact subG_zero gs
  · rfl

theorem map_subG {gs : List G} (h : CommInv gs) (φ : G →* G) :
    ∀ {ls : List G} {cs : List ℕ}, List.Forall₂ (fun a c => φ a = subG gs c) ls cs →
      ∀ m, φ (subG ls m) = subG gs (xsel cs m)
  | [], [], .nil, m => by rw [subG_nil, map_one]; exact (subG_zero gs).symm
  | a :: ls, c :: cs, .cons hac hrest, m => by
    change φ (subG (a :: ls) m) =
      subG gs (Nat.xor (bif Nat.beq (Nat.mod m 2) 1 then c else 0) (xsel cs (Nat.div m 2)))
    rw [subG_cons, map_mul, map_subG h φ hrest (m / 2)]
    change _ = subG gs ((bif Nat.beq (m % 2) 1 then c else 0) ^^^ xsel cs (m / 2))
    rw [subG_xor h, beq_mod_two, subG_bif h]
    split_ifs
    · rw [hac]
    · rw [map_one]

@[expose] def wordG (S : ℕ → G) : List ℕ → G
  | [] => 1
  | s :: w => S s * wordG S w

theorem wordG_mem {K : Subgroup G} {S : ℕ → G} (hS : ∀ s, S s ∈ K) :
    ∀ w : List ℕ, wordG S w ∈ K
  | [] => K.one_mem
  | s :: w => K.mul_mem (hS s) (wordG_mem hS w)

theorem lettersOK_spec {n : ℕ} : ∀ {w : List ℕ}, lettersOK n w = true → ∀ s ∈ w, s < n
  | [], _, s, hs => absurd hs List.not_mem_nil
  | a :: w, h, s, hs => by
    change (Nat.blt a n && lettersOK n w) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h.1
    · exact lettersOK_spec h.2 s hs

theorem conj_wordG {gs : List G} {S : ℕ → G} {CM : List (List ℕ)}
    (hS : ∀ s < CM.length, ∀ m, S s * subG gs m * (S s)⁻¹ = subG gs (xsel (CM.getD s []) m)) :
    ∀ {w : List ℕ}, (∀ s ∈ w, s < CM.length) →
      ∀ m, wordG S w * subG gs m * (wordG S w)⁻¹ = subG gs (wact CM w m)
  | [], _, m => by simp [wordG]; rfl
  | s :: w, hw, m => by
    change _ = subG gs (xsel (nthD [] CM s) (wact CM w m))
    rw [nthD_eq, ← hS s (hw s List.mem_cons_self), ← conj_wordG hS
      (fun s' hs' => hw s' (List.mem_cons_of_mem _ hs')) m, wordG]
    group

theorem xsel_lt {n : ℕ} : ∀ {cs : List ℕ}, (∀ c ∈ cs, c < 2 ^ n) → ∀ m, xsel cs m < 2 ^ n
  | [], _, _ => Nat.two_pow_pos n
  | c :: cs, h, m => by
    change Nat.xor (bif Nat.beq (Nat.mod m 2) 1 then c else 0) (xsel cs (Nat.div m 2)) < 2 ^ n
    refine Nat.xor_lt_two_pow ?_ (xsel_lt (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) _)
    cases Nat.beq (Nat.mod m 2) 1
    · exact Nat.two_pow_pos n
    · exact h c List.mem_cons_self

theorem wact_lt {n : ℕ} {CM : List (List ℕ)} (hCM : ∀ s < CM.length, ∀ c ∈ CM.getD s [], c < 2 ^ n) :
    ∀ {w : List ℕ}, (∀ s ∈ w, s < CM.length) → ∀ m, m < 2 ^ n → wact CM w m < 2 ^ n
  | [], _, _, hm => hm
  | s :: w, hw, m, _ => by
    change xsel (nthD [] CM s) (wact CM w m) < 2 ^ n
    rw [nthD_eq]
    exact xsel_lt (hCM s (hw s List.mem_cons_self)) _

@[expose] def ChainG : List (List G) → List G → Prop
  | [], [] => True
  | X :: Ls, t :: ts =>
    (X.map fun x => x * t * x⁻¹).Nodup ∧ (∀ Y ∈ Ls, ∀ y ∈ Y, y * t = t * y) ∧ ChainG Ls ts
  | _, _ => False

@[expose] def prodsG : List (List G) → List G
  | [] => [1]
  | X :: Ls => X.flatMap fun x => (prodsG Ls).map (x * ·)

theorem length_prodsG : ∀ Ls : List (List G), (prodsG Ls).length = (Ls.map List.length).prod
  | [] => rfl
  | X :: Ls => by
    simp only [prodsG, List.length_flatMap, List.length_map, length_prodsG Ls, List.map_cons,
      List.prod_cons, List.map_const', List.sum_replicate, smul_eq_mul]

theorem mem_prodsG {K : Subgroup G} : ∀ {Ls : List (List G)}, (∀ Y ∈ Ls, ∀ y ∈ Y, y ∈ K) →
    ∀ p ∈ prodsG Ls, p ∈ K
  | [], _, p, hp => by
    rw [prodsG, List.mem_singleton] at hp
    rw [hp]
    exact K.one_mem
  | X :: Ls, h, p, hp => by
    rw [prodsG, List.mem_flatMap] at hp
    obtain ⟨x, hx, hp⟩ := hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact K.mul_mem (h X List.mem_cons_self x hx)
      (mem_prodsG (fun Y hY => h Y (List.mem_cons_of_mem _ hY)) q hq)

theorem conj_eq_of_comm {A B t : G} (h : (A⁻¹ * B) * t = t * (A⁻¹ * B)) :
    B * t * B⁻¹ = A * t * A⁻¹ :=
  calc B * t * B⁻¹ = A * ((A⁻¹ * B) * t) * B⁻¹ := by group
    _ = A * (t * (A⁻¹ * B)) * B⁻¹ := by rw [h]
    _ = A * t * A⁻¹ := by group

@[expose] def Sep (ts : List G) (a b : G) : Prop := ¬ ∀ t ∈ ts, (a⁻¹ * b) * t = t * (a⁻¹ * b)

theorem pairwise_prodsG : ∀ {Ls : List (List G)} {ts : List G}, ChainG Ls ts →
    (prodsG Ls).Pairwise (Sep ts)
  | [], [], _ => List.pairwise_singleton _ _
  | X :: Ls, t :: ts, ⟨hX, hc, hL⟩ => by
    have hcent : ∀ p ∈ prodsG Ls, p * t = t * p := by
      have := mem_prodsG (K := Subgroup.centralizer {t}) (Ls := Ls) (fun Y hY y hy =>
        Subgroup.mem_centralizer_iff.2 fun t' ht' => by
          rw [Set.mem_singleton_iff.1 ht']
          exact (hc Y hY y hy).symm)
      exact fun p hp => ((Subgroup.mem_centralizer_iff.1 (this p hp)) t rfl).symm
    rw [prodsG, List.pairwise_flatMap]
    refine ⟨fun x _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (pairwise_prodsG hL).imp fun {a b} hab h => hab fun t' ht' => ?_
      have := h t' (List.mem_cons_of_mem _ ht')
      have e : (x * a)⁻¹ * (x * b) = a⁻¹ * b := by group
      rwa [e] at this
    · rw [List.Nodup, List.pairwise_map] at hX
      refine hX.imp fun {x x'} hne => ?_
      intro y hy y' hy' h
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy'
      apply hne
      have e := conj_eq_of_comm (h t List.mem_cons_self)
      have ea : x * a * t * (x * a)⁻¹ = x * t * x⁻¹ := by
        calc x * a * t * (x * a)⁻¹ = x * (a * t) * a⁻¹ * x⁻¹ := by group
          _ = x * t * x⁻¹ := by rw [hcent a ha]; group
      have eb : x' * b * t * (x' * b)⁻¹ = x' * t * x'⁻¹ := by
        calc x' * b * t * (x' * b)⁻¹ = x' * (b * t) * b⁻¹ * x'⁻¹ := by group
          _ = x' * t * x'⁻¹ := by rw [hcent b hb]; group
      rw [← ea, ← eb, e]

theorem sep_symm (ts : List G) : Symmetric (Sep ts) := fun a b h h' => h fun t ht => by
  have := h' t ht
  have e : a⁻¹ * b = (b⁻¹ * a)⁻¹ := by group
  rw [e]
  calc (b⁻¹ * a)⁻¹ * t = (b⁻¹ * a)⁻¹ * (t * (b⁻¹ * a)) * (b⁻¹ * a)⁻¹ := by group
    _ = (b⁻¹ * a)⁻¹ * ((b⁻¹ * a) * t) * (b⁻¹ * a)⁻¹ := by rw [this]
    _ = t * (b⁻¹ * a)⁻¹ := by group

theorem prod_le_relIndex [Finite G] {Ls : List (List G)} {ts : List G} (hch : ChainG Ls ts)
    {H C : Subgroup G} (hH : ∀ Y ∈ Ls, ∀ y ∈ Y, y ∈ H) (hC : ∀ c ∈ C, ∀ t ∈ ts, c * t = t * c) :
    (Ls.map List.length).prod ≤ C.relIndex H := by
  classical
  have hP := pairwise_prodsG hch
  have hnd : (prodsG Ls).Nodup := hP.imp fun {a b} hab e => hab fun t _ => by
    rw [e, inv_mul_cancel, one_mul, mul_one]
  set S := (prodsG Ls).toFinset with hS
  have hmem : ∀ p ∈ S, p ∈ H := fun p hp => mem_prodsG hH p (List.mem_toFinset.1 hp)
  let f : S → H ⧸ C.subgroupOf H := fun p => QuotientGroup.mk ⟨p.1, hmem p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at e
    by_contra hab
    have hab' : a ≠ b := fun h => hab (Subtype.ext h)
    have : Std.Symm (Sep ts) := ⟨fun a b h => sep_symm ts h⟩
    refine (hP.forall (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb) hab')
      fun t ht => ?_
    exact hC _ e t ht
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS, List.toFinset_card_of_nodup hnd,
    length_prodsG] at this
  exact this

end Group

theorem isP_subG : ∀ {Us : List (V12 ≃ₗ[ZMod 2] V12)} {LP : List ℕ}, List.Forall₂ IsP Us LP →
    ∀ m, IsP (subG Us m) (subP LP m)
  | [], [], .nil, _ => IsP.one
  | U :: Us, g :: LP, .cons hU hrest, m => by
    change IsP _ (mulP (bif Nat.beq (Nat.mod m 2) 1 then g else idP) (subP LP (Nat.div m 2)))
    rw [subG_cons]
    refine IsP.mul ?_ (isP_subG hrest _)
    change IsP _ (bif Nat.beq (m % 2) 1 then g else idP)
    rw [beq_mod_two]
    cases m.testBit 0
    · exact IsP.one
    · exact hU

theorem commOK_spec {LP : List ℕ} (h : commOK LP = true) :
    ∀ i < LP.length, mulP (LP.getD i 0) (LP.getD i 0) = idP ∧
      ∀ j < i, mulP (LP.getD i 0) (LP.getD j 0) = mulP (LP.getD j 0) (LP.getD i 0) := by
  unfold commOK at h
  rw [allBelow_iff, lenN_eq] at h
  intro i hi
  have hi' := h i hi
  rw [Bool.and_eq_true, allBelow_iff] at hi'
  simp only [Nat.beq_eq, nthD_eq] at hi'
  exact ⟨hi'.1, hi'.2⟩

theorem subOK_spec {LP : List ℕ} (h : subOK LP = true) :
    ∀ m, 0 < m → m < 2 ^ LP.length → subP LP m ≠ idP := by
  unfold subOK at h
  rw [allBelow_iff, lenN_eq] at h
  intro m hm0 hm e
  have := h (m - 1) (by change m - 1 < 2 ^ LP.length - 1; omega)
  rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hm0, e] at this
  simp at this

theorem conjOK_spec {SG LP : List ℕ} {CM : List (List ℕ)} (h : conjOK SG LP CM = true) :
    CM.length = SG.length ∧ ∀ s < SG.length, (CM.getD s []).length = LP.length ∧
      ∀ i < LP.length, (CM.getD s []).getD i 0 < 2 ^ LP.length ∧
        mulP (SG.getD s 0) (LP.getD i 0) =
          mulP (subP LP ((CM.getD s []).getD i 0)) (SG.getD s 0) := by
  unfold conjOK at h
  rw [Bool.and_eq_true, Nat.beq_eq, allBelow_iff, lenN_eq, lenN_eq] at h
  refine ⟨h.1, fun s hs => ?_⟩
  have hs' := h.2 s hs
  rw [Bool.and_eq_true, Nat.beq_eq, allBelow_iff, lenN_eq, lenN_eq] at hs'
  refine ⟨by simpa [nthD_eq] using hs'.1, fun i hi => ?_⟩
  have hi' := hs'.2 i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nthD_eq, lenN_eq] at hi'
  exact hi'

theorem orbOK_spec {CM : List (List ℕ)} {r : ℕ} {ws : List (List ℕ)} {ms : List ℕ}
    (h : orbOK CM r ws ms = true) : ws.length = ms.length ∧ ∀ k < ms.length,
      (∀ s ∈ ws.getD k [], s < CM.length) ∧ wact CM (ws.getD k []) r = ms.getD k 0 := by
  unfold orbOK at h
  rw [Bool.and_eq_true, Nat.beq_eq, allBelow_iff, lenN_eq, lenN_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have hk' := h.2 k hk
  rw [Bool.and_eq_true, Nat.beq_eq, nthD_eq, nthD_eq, lenN_eq] at hk'
  exact ⟨lettersOK_spec hk'.1, hk'.2⟩

theorem nodupN_spec : ∀ {l : List ℕ}, nodupN l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    change (!memN a t && nodupN t) = true at h
    rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, memN_iff] at h
    exact List.nodup_cons.2 ⟨h.1, nodupN_spec h.2⟩

theorem levelOK_spec {CM : List (List ℕ)} {τ : List ℕ} {k : ℕ} {ws : List (List ℕ)}
    (h : levelOK CM τ k ws = true) :
    (∀ w ∈ ws, (∀ s ∈ w, s < CM.length) ∧ ∀ j < k, wact CM w (τ.getD j 0) = τ.getD j 0) ∧
      (ws.map fun w => wact CM w (τ.getD k 0)).Nodup := by
  unfold levelOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun w hw => ?_, ?_⟩
  · have hw' := h.1 w hw
    rw [Bool.and_eq_true, allBelow_iff, lenN_eq] at hw'
    refine ⟨lettersOK_spec hw'.1, fun j hj => ?_⟩
    have := hw'.2 j hj
    rwa [Nat.beq_eq, nthD_eq] at this
  · have := nodupN_spec h.2
    simpa only [nthD_eq] using this

theorem prodLen_eq : ∀ TT : List (List (List ℕ)), prodLen TT = (TT.map List.length).prod
  | [] => rfl
  | ws :: TT => by
    change Nat.mul (lenN ws) (prodLen TT) = _
    rw [lenN_eq, prodLen_eq TT, List.map_cons, List.prod_cons]
    rfl

theorem chainOK_spec {CM : List (List ℕ)} {ms τ : List ℕ} {TT : List (List (List ℕ))} {n : ℕ}
    (h : chainOK CM ms τ TT n = true) :
    (∀ t ∈ τ, t ∈ ms) ∧ TT.length = τ.length ∧
      (∀ k < τ.length, levelOK CM τ k (TT.getD k []) = true) ∧ n ≤ (TT.map List.length).prod := by
  unfold chainOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, memN_iff, Nat.beq_eq, lenN_eq, allBelow_iff,
    nthD_eq, Nat.ble_eq, prodLen_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end CFSG.KC.IF4L

end
