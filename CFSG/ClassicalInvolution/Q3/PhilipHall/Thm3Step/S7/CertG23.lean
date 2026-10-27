module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowG23
public import Certificates.Certificate517003

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5 CFSG.Blueprint
  CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U
  Certificates.S5Rows Certificates.S5RowsG23 Certificates.S7Q8 Certificates.S7G23

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)
local notation "GL14" => GL (Fin 14) (ZMod 3)

namespace G23S7

@[expose] def Rep (c : List ℕ) (g : H3) : Prop :=
  canon14 c = true ∧ (((g : GL14) : M14)) = dec14 c

theorem rep_mul {a b : List ℕ} {g h : H3} (ha : Rep a g) (hb : Rep b h) :
    Rep (mul14 a b) (g * h) :=
  ⟨canon14_mul14 a b, by rw [Subgroup.coe_mul, Units.val_mul, ha.2, hb.2, dec14_mul14]⟩

theorem rep_one : Rep one14 1 :=
  ⟨canon14_one14, by rw [dec14_one14]; rfl⟩

theorem rep_beq {a b : List ℕ} {g h : H3} (ha : Rep a g) (hb : Rep b h) :
    (a == b) = true ↔ g = h := by
  rw [beq_iff_eq]
  constructor
  · rintro rfl
    exact Subtype.ext (Units.ext (ha.2.trans hb.2.symm))
  · rintro rfl
    exact dec14_injective ha.1 hb.1 (ha.2.symm.trans hb.2)

theorem rep_sq {a : List ℕ} {g : H3} (ha : Rep a g) : Rep (sq14 a) (g * g) := rep_mul ha ha

theorem rep_foldl {f : ℕ → List ℕ} {F : ℕ → H3} (hf : ∀ k, Rep (f k) (F k)) :
    ∀ (l : List ℕ) (acc : List ℕ) (g : H3), Rep acc g →
      Rep (l.foldl (fun acc k => mul14 acc (f k)) acc) (g * (l.map F).prod)
  | [], acc, g, h => by simpa using h
  | k :: l, acc, g, h => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact rep_foldl hf l _ _ (rep_mul h (hf k))

theorem conj_eq_iff {g x q : H3} : g * x * g⁻¹ = q ↔ g * x = q * g := by
  constructor
  · rintro rfl
    group
  · intro h
    rw [h]
    group

theorem any_iff_of_forall₂ {L : List (List ℕ)} {G : List H3} (h : List.Forall₂ Rep L G)
    {p : List ℕ → Bool} {q : H3 → Prop} (hpq : ∀ c g, Rep c g → (p c = true ↔ q g)) :
    L.any p = true ↔ ∃ g ∈ G, q g := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    rw [List.any_cons, Bool.or_eq_true, hpq _ _ hab, ih]
    simp

theorem contains_iff_of_forall₂ {L : List (List ℕ)} {G : List H3} (h : List.Forall₂ Rep L G)
    {c : List ℕ} {g : H3} (hc : Rep c g) : L.contains c = true ↔ g ∈ G := by
  rw [List.contains_eq_any_beq, any_iff_of_forall₂ h (q := fun x => g = x)
    fun c' g' hc' => (rep_beq hc hc')]
  exact ⟨fun ⟨x, hx, hgx⟩ => hgx ▸ hx, fun hg => ⟨g, hg, rfl⟩⟩


noncomputable def gH (k : ℕ) : H3 :=
  if k = 0 then ⟨gX 0, gX_mem 0⟩ else if k = 1 then ⟨gX 1, gX_mem 1⟩
  else if k = 2 then ⟨gY 0, gY_mem 0⟩ else if k = 3 then ⟨gY 1, gY_mem 1⟩ else 1

theorem rep_gens (k : ℕ) : Rep (gensC.getD k one14) (gH k) := by
  unfold gH
  rcases k with _ | _ | _ | _ | k
  · exact ⟨by decide +kernel, coe_gX0⟩
  · exact ⟨by decide +kernel, coe_gX1⟩
  · exact ⟨by decide +kernel, coe_gY0⟩
  · exact ⟨by decide +kernel, coe_gY1⟩
  · simp only [gensC, List.getD_cons_succ, List.getD_nil]
    exact rep_one

noncomputable def wordH (w : List ℕ) : H3 := (w.map gH).prod

theorem rep_wordC (w : List ℕ) : Rep (wordC w) (wordH w) := by
  have := rep_foldl rep_gens w one14 1 rep_one
  rwa [one_mul] at this


theorem gH_mul_self (k : ℕ) : gH k * gH k = (gH k)⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := gens_pow_three
  have key : ∀ g : H3, g ^ 3 = 1 → g * g = g⁻¹ := fun g hg => by
    rw [eq_inv_iff_mul_eq_one, ← pow_two, ← pow_succ, hg]
  unfold gH
  rcases k with _ | _ | _ | _ | k
  · exact key _ (Subtype.ext h0)
  · exact key _ (Subtype.ext h1)
  · exact key _ (Subtype.ext h2)
  · exact key _ (Subtype.ext h3)
  · simp

theorem rep_wordInvC (w : List ℕ) : Rep (wordInvC w) (wordH w)⁻¹ := by
  have hf : ∀ k, Rep (sq14 (gensC.getD k one14)) (gH k)⁻¹ := fun k => by
    rw [← gH_mul_self]
    exact rep_sq (rep_gens k)
  have h1 := rep_foldl hf w.reverse one14 1 rep_one
  have h2 : (wordH w)⁻¹ = 1 * (w.reverse.map fun k => (gH k)⁻¹).prod := by
    rw [one_mul, wordH, List.prod_inv_reverse, List.map_map, ← List.map_reverse]
    rfl
  rw [h2]
  exact h1

section Span

variable {ci cj : List ℕ} {i j : H3}

theorem forall₂_spanC (hi : Rep ci i) (hj : Rep cj j) (h : Q8Rel i j) :
    List.Forall₂ Rep (spanC ci cj) (q8Span i j) := by
  have h4 : i ^ 4 = 1 := h.1
  have hinv : i * i * i = i⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc i * i * i * i = i ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := h4
  have hjinv : j * j * j = j⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    have hj2 : j * j = i * i := by rw [← sq, ← sq, h.2.2.1]
    calc j * j * j * j = (j * j) * (j * j) := by group
      _ = i ^ 4 := by rw [hj2]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  simp only [spanC, q8Span]
  refine .cons rep_one (.cons ?_ (.cons hi (.cons ?_ (.cons hj (.cons ?_
    (.cons (rep_mul hi hj) (.cons (rep_mul hj hi) .nil)))))))
  · rw [sq]; exact rep_sq hi
  · rw [← hinv]; exact rep_mul (rep_sq hi) hi
  · rw [← hjinv]; exact rep_mul (rep_sq hj) hj

theorem inSpanC_iff (hi : Rep ci i) (hj : Rep cj j) (h : Q8Rel i j) {cx : List ℕ} {x : H3}
    (hx : Rep cx x) : inSpanC ci cj cx = true ↔ x ∈ Subgroup.closure ({i, j} : Set H3) := by
  rw [inSpanC, contains_iff_of_forall₂ (forall₂_spanC hi hj h) hx, mem_closure_pair_iff h]

theorem conjInC_iff {sp : List (List ℕ)} {G : List H3} (hsp : List.Forall₂ Rep sp G)
    {cg cx : List ℕ} {g x : H3} (hg : Rep cg g) (hx : Rep cx x) :
    conjInC sp cg cx = true ↔ g * x * g⁻¹ ∈ G := by
  rw [conjInC, any_iff_of_forall₂ hsp (q := fun q => g * x = q * g)
    fun c q hc => rep_beq (rep_mul hg hx) (rep_mul hc hg)]
  constructor
  · rintro ⟨q, hq, hgq⟩
    rwa [conj_eq_iff.mpr hgq]
  · intro hmem
    exact ⟨_, hmem, conj_eq_iff.mp rfl⟩

theorem normC_iff (hi : Rep ci i) (hj : Rep cj j) (h : Q8Rel i j) {cg : List ℕ} {g : H3}
    (hg : Rep cg g) :
    normC ci cj cg = true ↔ g ∈ Subgroup.normalizer
      ((Subgroup.closure ({i, j} : Set H3) : Subgroup H3) : Set H3) := by
  classical
  rw [← normB_iff h]
  have e1 := conjInC_iff (forall₂_spanC hi hj h) hg hi
  have e2 := conjInC_iff (forall₂_spanC hi hj h) hg hj
  simp only [normC, normB, inSpanB, Bool.and_eq_true, decide_eq_true_eq]
  rw [e1, e2]

end Span

theorem ord4C_iff {cu : List ℕ} {u : H3} (hu : Rep cu u) : ord4C cu = true ↔ orderOf u = 4 := by
  classical
  rw [← ord4B_iff, ord4C, ord4B, Bool.and_eq_true, Bool.and_eq_true,
    rep_beq (rep_sq (rep_sq hu)) rep_one, Bool.not_eq_true', Bool.not_eq_true',
    Bool.eq_false_iff, Bool.eq_false_iff, Ne, Ne, rep_beq (rep_sq hu) rep_one, decide_eq_true_iff,
    decide_eq_true_iff]

theorem q8RelC_iff {ci cj : List ℕ} {i j : H3} (hi : Rep ci i) (hj : Rep cj j) :
    q8RelC ci cj = true ↔ Q8Rel i j := by
  have hrel : i * j * i = j ↔ j⁻¹ * i * j = i⁻¹ := by
    constructor
    · intro h
      rw [eq_inv_iff_mul_eq_one]
      calc j⁻¹ * i * j * i = j⁻¹ * (i * j * i) := by group
        _ = 1 := by rw [h]; group
    · intro h
      calc i * j * i = j * (j⁻¹ * i * j) * i := by group
        _ = j := by rw [h]; group
  have hne : (sq14 ci != one14) = true ↔ i * i ≠ 1 := by
    rw [bne, Bool.not_eq_true', Bool.eq_false_iff, Ne, Ne, rep_beq (rep_sq hi) rep_one]
  simp only [q8RelC, Bool.and_eq_true]
  rw [rep_beq (rep_mul (rep_sq hi) (rep_sq hi)) rep_one, hne,
    rep_beq (rep_sq hi) (rep_sq hj), rep_beq (rep_mul (rep_mul hi hj) hi) hj, hrel]
  simp only [Q8Rel, sq, pow_succ, pow_zero, one_mul, mul_assoc, and_assoc]

theorem mem_normalizer_of_normVC {cz cw ca : List ℕ} {z w a : H3} (hz : Rep cz z)
    (hw : Rep cw w) (ha : Rep ca a) (h : normVC cz cw ca = true) :
    a ∈ Subgroup.normalizer ((Subgroup.closure ({z, w} : Set H3) : Subgroup H3) : Set H3) := by
  classical
  have hV : List.Forall₂ Rep [one14, cz, cw, mul14 cz cw] [1, z, w, z * w] :=
    .cons rep_one (.cons hz (.cons hw (.cons (rep_mul hz hw) .nil)))
  simp only [normVC, Bool.and_eq_true] at h
  rw [conjInC_iff hV ha hz, conjInC_iff hV ha hw] at h
  refine mem_normalizer_of_normVB (z := z) (w := w) ?_
  simp only [normVB, Bool.and_eq_true, decide_eq_true_eq]
  exact h

theorem exists_rep_S2 {s : H3} (hs : s ∈ S2H) : ∃ c ∈ elemsS.toList, Rep c s := by
  obtain ⟨k, hk, hcode⟩ := exists_code_S2 (Subgroup.mem_subgroupOf.mp hs)
  exact ⟨_, Array.mem_toList_iff.mpr (getD_mem_of_lt hk),
    allCheck_spec certS.2.2.2 hk, hcode.symm⟩

theorem exists_rep_X0 {s : H3} (hs : s ∈ X0H) : ∃ c ∈ elemsX.toList, Rep c s := by
  obtain ⟨k, hk, hcode⟩ := exists_code_X0 (Subgroup.mem_subgroupOf.mp hs)
  exact ⟨_, Array.mem_toList_iff.mpr (getD_mem_of_lt hk),
    allCheck_spec certX.2.2.2.1 hk, hcode.symm⟩

theorem exists_of_mem_forall₂ {L : List (List ℕ)} {G : List H3} (h : List.Forall₂ Rep L G)
    {c : List ℕ} (hc : c ∈ L) : ∃ g ∈ G, Rep c g := by
  induction h with
  | nil => exact absurd hc (List.not_mem_nil)
  | cons hab _ ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨g, hg, hr⟩ := ih hc
      exact ⟨g, List.mem_cons_of_mem _ hg, hr⟩

theorem classCheckC_sound {ci cj : List ℕ} {i j : H3} (hi : Rep ci i) (hj : Rep cj j)
    (h : Q8Rel i j) {S X : List (List ℕ)} (hc : classCheckC ci cj S X = true) {cu : List ℕ}
    {u : H3} (hcu : cu ∈ S) (hu : Rep cu u) (hu4 : orderOf u = 4) :
    ∃ x : H3, x * (i * i) * x⁻¹ = u * u ∧
      (u ∈ conjSub x (Subgroup.closure ({i, j} : Set H3)) →
        conjSub x (Subgroup.closure ({i, j} : Set H3)) ≠ Subgroup.closure ({i, j} : Set H3) →
        ¬ conjSub x (Subgroup.closure ({i, j} : Set H3)) ≤
          Subgroup.normalizer ((Subgroup.closure ({i, j} : Set H3)) : Set H3) →
        ∃ g ∈ pairNormalizers (Subgroup.closure ({i, j} : Set H3))
            (conjSub x (Subgroup.closure ({i, j} : Set H3))) (i * i) (u * u),
          conjSub g (Subgroup.closure ({i, j} : Set H3)) =
            conjSub x (Subgroup.closure ({i, j} : Set H3))) := by
  simp only [classCheckC, List.all_eq_true] at hc
  have h1 := hc cu hcu
  rw [Bool.or_eq_true, Bool.not_eq_true', (ord4C_iff hu).mpr hu4, List.any_eq_true] at h1
  obtain ⟨xw, -, hx⟩ := h1.resolve_left (by decide)
  have hxr := rep_wordC xw
  have hxir := rep_wordInvC xw
  set x := wordH xw
  set ci' := mul14 (mul14 (wordC xw) ci) (wordInvC xw) with hci'
  set cj' := mul14 (mul14 (wordC xw) cj) (wordInvC xw) with hcj'
  simp only [classStepC, Bool.and_eq_true] at hx
  rw [← hci', ← hcj'] at hx
  obtain ⟨⟨-, hxz⟩, hx⟩ := hx
  have hxz' : x * (i * i) * x⁻¹ = u * u :=
    conj_eq_iff.mpr ((rep_beq (rep_mul hxr (rep_sq hi)) (rep_mul (rep_sq hu) hxr)).mp hxz)
  refine ⟨x, hxz', fun huJ hne hnN => ?_⟩
  have hi' : Rep ci' (x * i * x⁻¹) := rep_mul (rep_mul hxr hi) hxir
  have hj' : Rep cj' (x * j * x⁻¹) := rep_mul (rep_mul hxr hj) hxir
  have h' : Q8Rel (x * i * x⁻¹) (x * j * x⁻¹) := q8Rel_conj h x
  rw [conjSub_closure_pair] at huJ hne hnN ⊢
  have hb1 : inSpanC ci' cj' cu = true := (inSpanC_iff hi' hj' h' hu).mpr huJ
  have hb2 : (inSpanC ci cj ci' && inSpanC ci cj cj') = false := by
    rw [Bool.eq_false_iff]
    intro hb
    rw [Bool.and_eq_true, inSpanC_iff hi hj h hi', inSpanC_iff hi hj h hj'] at hb
    exact hne (closure_pair_eq_of_mem h' h hb.1 hb.2)
  have hb3 : (normC ci cj ci' && normC ci cj cj') = false := by
    rw [Bool.eq_false_iff]
    intro hb
    rw [Bool.and_eq_true, normC_iff hi hj h hi', normC_iff hi hj h hj'] at hb
    exact hnN (closure_pair_le hb.1 hb.2)
  rw [hb1, hb2, hb3] at hx
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    Bool.and_eq_true] at hx
  obtain ⟨a', ha', b', hb', ⟨⟨hza, hzb⟩, hgi⟩, hgj⟩ := hx
  obtain ⟨a, haS, hra⟩ := exists_of_mem_forall₂ (forall₂_spanC hi hj h) ha'
  obtain ⟨b, hbS, hrb⟩ := exists_of_mem_forall₂ (forall₂_spanC hi' hj' h') hb'
  have hsp' := forall₂_spanC hi' hj' h'
  rw [conjInC_iff hsp' (rep_mul hra hrb) hi] at hgi
  rw [conjInC_iff hsp' (rep_mul hra hrb) hj] at hgj
  refine ⟨a * b, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨(mem_closure_pair_iff h).mpr haS,
      mem_normalizer_of_normVC (rep_sq hi) (rep_sq hu) hra hza⟩)
      (Subgroup.mem_sup_right ⟨(mem_closure_pair_iff h').mpr hbS,
        mem_normalizer_of_normVC (rep_sq hi) (rep_sq hu) hrb hzb⟩)
  · rw [conjSub_closure_pair]
    exact closure_pair_eq_of_mem (q8Rel_conj h (a * b)) h' ((mem_closure_pair_iff h').mpr hgi)
      ((mem_closure_pair_iff h').mpr hgj)

theorem normAllC_sound {ci cj : List ℕ} {i j : H3} (hi : Rep ci i) (hj : Rep cj j)
    (h : Q8Rel i j) {C : List (List ℕ)} (hc : normAllC ci cj C = true) {cg : List ℕ} {g : H3}
    (hcg : cg ∈ C) (hg : Rep cg g) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({i, j} : Set H3)) : Set H3) := by
  simp only [normAllC, List.all_eq_true] at hc
  exact (normC_iff hi hj h hg).mp (hc cg hcg)

theorem q8InCheckC_sound {ci₁ cj₁ ci₂ cj₂ : List ℕ} {i₁ j₁ i₂ j₂ : H3} (hi₁ : Rep ci₁ i₁)
    (hj₁ : Rep cj₁ j₁) (hi₂ : Rep ci₂ i₂) (hj₂ : Rep cj₂ j₂) (h₁ : Q8Rel i₁ j₁)
    (h₂ : Q8Rel i₂ j₂) {L : List (List ℕ)} (hc : q8InCheckC L ci₁ cj₁ ci₂ cj₂ = true)
    {T : Subgroup H3} (hT : Nonempty (↥T ≃* QuaternionGroup 2))
    (hTL : ∀ t ∈ T, ∃ c ∈ L, Rep c t) :
    T = Subgroup.closure ({i₁, j₁} : Set H3) ∨ T = Subgroup.closure ({i₂, j₂} : Set H3) := by
  obtain ⟨e⟩ := hT
  obtain ⟨a, haT, b, hbT, hab, hspan⟩ := exists_q8Pair e
  have hTab : T = Subgroup.closure ({a, b} : Set H3) := by
    apply le_antisymm
    · intro t ht
      exact (mem_closure_pair_iff hab).mpr (hspan t ht)
    · exact closure_pair_le haT hbT
  obtain ⟨ca, hca, hra⟩ := hTL a haT
  obtain ⟨cb, hcb, hrb⟩ := hTL b hbT
  have ha4 := orderOf_eq_four_of_q8Rel hab
  have hb2 : b ^ 2 = a ^ 2 := hab.2.2.1.symm
  have hb4 : orderOf b = 4 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, hb2]; exact hab.2.1) ?_
    rw [show 2 ^ (1 + 1) = 2 * 2 by rfl, pow_mul, hb2, ← pow_mul]
    exact hab.1
  have haba : a * b * a = b := by
    calc a * b * a = b * (b⁻¹ * a * b) * a := by group
      _ = b := by rw [hab.2.2.2]; group
  have hmem : ∀ {c : List ℕ} {g : H3}, c ∈ L → Rep c g → orderOf g = 4 →
      (c, sq14 c) ∈ (L.filter ord4C).map fun a => (a, sq14 a) := by
    intro c g hc hr hg
    exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, (ord4C_iff hr).mpr hg⟩, rfl⟩
  simp only [q8InCheckC, List.all_eq_true] at hc
  have h1 := hc _ (hmem hca hra ha4) _ (hmem hcb hrb hb4)
  have hcond : ((sq14 ca == sq14 cb) && (mul14 (mul14 ca cb) ca == cb)) = true := by
    rw [Bool.and_eq_true, rep_beq (rep_sq hra) (rep_sq hrb),
      rep_beq (rep_mul (rep_mul hra hrb) hra) hrb]
    exact ⟨by rw [← sq, ← sq, hb2], haba⟩
  rw [hcond] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at h1
  rw [hTab]
  rcases h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl (closure_pair_eq_of_mem hab h₁ ((inSpanC_iff hi₁ hj₁ h₁ hra).mp ha)
      ((inSpanC_iff hi₁ hj₁ h₁ hrb).mp hb))
  · exact Or.inr (closure_pair_eq_of_mem hab h₂ ((inSpanC_iff hi₂ hj₂ h₂ hra).mp ha)
      ((inSpanC_iff hi₂ hj₂ h₂ hrb).mp hb))

section Model


theorem centralizer_tH : Subgroup.centralizer ({tH} : Set H3) = X0H := by
  haveI : Finite H3 := Nat.finite_of_card_ne_zero (by rw [card_R3]; norm_num)
  refine (Subgroup.eq_of_le_of_card_ge X0H_le_centralizer ?_).symm
  have h := card_centralizer_mul_le (H := H3) (t := tH) orbitElt orbitElt_injective
    orbitElt_conj
  rw [show Nat.card H3 = 4245696 from card_R3] at h
  rw [card_X0H]
  by_contra hlt
  push Not at hlt
  have : 577 * 7371 ≤ Nat.card (Subgroup.centralizer ({tH} : Set H3)) * 7371 :=
    Nat.mul_le_mul_right _ hlt
  omega

theorem rep_tc : Rep tc tH := by
  refine ⟨?_, by rw [coe_tH, coe_tU]⟩
  rw [tc]
  exact canon14_mul14 _ _

theorem S2H_isPGroup : IsPGroup 2 S2H :=
  IsPGroup.of_card (n := 6) (by rw [card_S2H]; norm_num)

theorem S2H_not_dvd_index : ¬ 2 ∣ S2H.index := by
  have h := Subgroup.card_mul_index S2H
  rw [card_S2H, card_R3] at h
  have h1 : S2H.index = 66339 := by omega
  rw [h1]
  decide


noncomputable abbrev i1H : H3 := wordH i1W
noncomputable abbrev j1H : H3 := wordH j1W
noncomputable abbrev i2H : H3 := wordH i2W
noncomputable abbrev j2H : H3 := wordH j2W

noncomputable abbrev Q1 : Subgroup H3 := Subgroup.closure {i1H, j1H}
noncomputable abbrev Q2 : Subgroup H3 := Subgroup.closure {i2H, j2H}

theorem basic_spec : Q8Rel i1H j1H ∧ Q8Rel i2H j2H ∧ i1H * i1H = tH ∧ i2H * i2H = tH := by
  have h := (Certificates.certificate517003).1
  simp only [g23S7Basic, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
  exact ⟨(q8RelC_iff (rep_wordC _) (rep_wordC _)).mp h1,
    (q8RelC_iff (rep_wordC _) (rep_wordC _)).mp h2,
    (rep_beq (rep_sq (rep_wordC _)) rep_tc).mp h3, (rep_beq (rep_sq (rep_wordC _)) rep_tc).mp h4⟩

theorem aEmpty_of_checks {ci cj : List ℕ} {i j : H3} (hi : Rep ci i) (hj : Rep cj j)
    (h : Q8Rel i j) (hz : i * i = tH) (hc : classCheckC ci cj elemsS.toList conjW = true)
    (hnX : normAllC ci cj elemsX.toList = true) (hnS : normAllC ci cj elemsS.toList = true) :
    AEmpty (CoreAssembly.conjClass (Subgroup.closure ({i, j} : Set H3)))
      (Subgroup.closure ({i, j} : Set H3)) := by
  haveI : Finite H3 := Nat.finite_of_card_ne_zero (by rw [card_R3]; norm_num)
  refine aEmpty_conjClass_of_sylow (S := S2H) (nonempty_closure_pair_mulEquiv h)
    (isUniqueInvolution_closure_pair h) (fun u hu hu4 => ?_) (fun c hc' => ?_)
    (fun u hu hu4 => ?_)
  · refine exists_conj_mem_of_le_normalizer (fun s hs => ?_) S2H_isPGroup S2H_not_dvd_index hu
      (k := 2) (by rw [hu4]; norm_num)
    obtain ⟨c, hc, hr⟩ := exists_rep_S2 hs
    exact normAllC_sound hi hj h hnS hc hr
  · rw [hz] at hc'
    have hcX : c ∈ X0H := by
      rw [← centralizer_tH, Subgroup.mem_centralizer_singleton_iff]
      exact hc'
    obtain ⟨cc, hcc, hr⟩ := exists_rep_X0 hcX
    exact normAllC_sound hi hj h hnX hcc hr
  · obtain ⟨cu, hcu, hr⟩ := exists_rep_S2 hu
    exact classCheckC_sound hi hj h hc hcu hr hu4

theorem classes : ∀ T ∈ q8Fam H3, ∃ g : H3, T = conjSub g Q1 ∨ T = conjSub g Q2 := by
  haveI : Finite H3 := Nat.finite_of_card_ne_zero (by rw [card_R3]; norm_num)
  intro T hT
  obtain ⟨h1, h2, -, -⟩ := basic_spec
  have hq := (Certificates.certificate517003).2.2.2.2
  rw [g23S7Q8] at hq
  obtain ⟨g, hg⟩ := g23_conj_mem_S2H T (isPGroup_of_q8 hT)
  have hT' : conjSub g⁻¹ T ∈ q8Fam H3 := nonempty_conjSub_mulEquiv hT g⁻¹
  have hL : ∀ t ∈ conjSub g⁻¹ T, ∃ c ∈ elemsS.toList, Rep c t := by
    intro t ht
    rw [mem_conjSub_iff, inv_inv] at ht
    apply exists_rep_S2
    have := hg _ ht
    rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at this
  have hT'' : T = conjSub g (conjSub g⁻¹ T) := (conjSub_conjSub_inv g T).symm
  refine ⟨g, ?_⟩
  rcases q8InCheckC_sound (rep_wordC _) (rep_wordC _) (rep_wordC _) (rep_wordC _) h1 h2 hq hT'
    hL with h | h
  · left
    rw [hT'', h]
  · right
    rw [hT'', h]

theorem aEmpty_q8 : ∀ T ∈ q8Fam H3, AEmpty (CoreAssembly.conjClass T) T := by
  haveI : Finite H3 := Nat.finite_of_card_ne_zero (by rw [card_R3]; norm_num)
  obtain ⟨h1, h2, hz1, hz2⟩ := basic_spec
  have hc1 := (Certificates.certificate517003).2.1
  have hc2 := (Certificates.certificate517003).2.2.1
  have hn := (Certificates.certificate517003).2.2.2.1
  rw [g23S7Class1] at hc1
  rw [g23S7Class2] at hc2
  simp only [g23S7Norm, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨hn1, hn2⟩, hs1⟩, hs2⟩ := hn
  exact aEmpty_q8Fam_of_classes classes
    (aEmpty_of_checks (rep_wordC _) (rep_wordC _) h1 hz1 hc1 hn1 hs1)
    (aEmpty_of_checks (rep_wordC _) (rep_wordC _) h2 hz2 hc2 hn2 hs2)

end Model

end G23S7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
