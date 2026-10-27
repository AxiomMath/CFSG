module

public import Certificates.Data.Kernel.E6Syl3P
public import CFSG.Certificates.Kernel.E6Syl3Glue

public section

namespace CFSG.KC.E6Syl3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_conj_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Subgroup G) (hS : Nat.card S = p ^ (Nat.card G).factorization p) {H : Subgroup G}
    (hH : IsPGroup p H) : ∃ g : G, ∀ h ∈ H, g⁻¹ * h * g ∈ S := by
  let S0 : Sylow p G := Sylow.ofCard S hS
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 P
  refine ⟨g, fun h hh => ?_⟩
  have hhP : h ∈ (P : Subgroup G) := hP hh
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hhP
  obtain ⟨y, hy, hyx⟩ := hhP
  have hyS : y ∈ S := by
    have e : (S0 : Subgroup G) = S := Sylow.coe_ofCard _ _
    rwa [← e]
  rw [← hyx, MulAut.smul_def, MulAut.conj_apply]
  convert hyS using 1
  group

theorem isPGroup_closure {G : Type*} [Group G] {s : Set G}
    (hs : ∀ a ∈ s, ∀ b ∈ s, Commute a b) (h3 : ∀ a ∈ s, a ^ 3 = 1) :
    IsPGroup 3 (Subgroup.closure s) := by
  have c1 : ∀ x ∈ Subgroup.closure s, ∀ a ∈ s, Commute a x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem b hb => exact fun a ha => hs a ha b hb
    | one => exact fun a _ => Commute.one_right a
    | mul x y _ _ ihx ihy => exact fun a ha => (ihx a ha).mul_right (ihy a ha)
    | inv x _ ih => exact fun a ha => (ih a ha).inv_right
  have c2 : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, Commute x y := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem b hb => exact fun y hy => c1 y hy b hb
    | one => exact fun y _ => Commute.one_left y
    | mul x z _ _ ihx ihz => exact fun y hy => (ihx y hy).mul_left (ihz y hy)
    | inv x _ ih => exact fun y hy => (ih y hy).inv_left
  have hc : ∀ x ∈ Subgroup.closure s, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem b hb => exact h3 b hb
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy => rw [(c2 x hx y hy).mul_pow, ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa using hc g g.2)⟩

theorem conj_eq (g w : WeylGroup Tag.E6) : w = g * (g⁻¹ * w * g) * g⁻¹ := by group

theorem conj_pow' (g w : WeylGroup Tag.E6) (n : ℕ) :
    w ^ n = g * (g⁻¹ * w * g) ^ n * g⁻¹ := by
  have e := conj_pow (a := g) (b := g⁻¹ * w * g) (i := n)
  rwa [← conj_eq] at e


noncomputable def yI (gw wd : List (List ℕ)) (i : ℕ) : WeylGroup Tag.E6 :=
  ((wd.getD i []).map fun k => wordW (gw.getD k [])).prod

theorem rep_wordG {gw : List (List ℕ)} (hl : ∀ w ∈ gw, ∀ i ∈ w, i < 6) :
    ∀ ks : List ℕ, e6Certificate.Represents (wordG gw ks)
      ((ks.map fun k => wordW (gw.getD k [])).prod)
  | [] => by
    simp only [wordG, List.foldr_nil, List.map_nil, List.prod_nil]
    exact RootCertificate.represents_one e6Certificate_check
  | k :: ks => by
    have h := rep_wordT (rep_wordG hl ks) (gw.getD k []) (letters_getD hl k)
    simpa [wordG, List.foldr_cons] using h

structure QFacts (gw wd lt : List (List ℕ)) : Prop where
  letters : ∀ w ∈ gw, ∀ i ∈ w, i < 6
  len : (qTups gw).length = 81
  nodup : (qTups gw).Nodup
  cover : ∀ y ∈ qSub gw, ∃ t ∈ qTups gw, e6Certificate.Represents t y
  zero : (qTups gw).getD 0 [] = List.range 6
  wdl : ∀ ks ∈ wd, ∀ k ∈ ks, k < 4
  wdt : ∀ i < 81, wordG gw (wd.getD i []) = (qTups gw).getD i []
  ltl : ∀ k < 4, ∀ i < 81, ltAt lt k i < 81
  ltt : ∀ k < 4, ∀ i < 81, wordT (gw.getD k []) ((qTups gw).getD i []) =
    (qTups gw).getD (ltAt lt k i) []

theorem qFacts_of_checks {gw wd lt : List (List ℕ)} (hq : qCheckWith gw (qTups gw) = true)
    (hwd : wdOK gw (qTups gw) wd = true) (hlt : ltOK gw (qTups gw) lt = true) :
    QFacts gw wd lt := by
  have hc := (exists_subgroup_of_qCheck hq).2
  simp only [qCheckWith, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hq
  simp only [wdOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range] at hwd
  simp only [ltOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range] at hlt
  exact ⟨hq.1.1.1.1, hq.1.1.1.2, nodup_of_nodupB _ hq.1.1.2, hc, hwd.1.1, hwd.1.2,
    hwd.2, fun k hk i hi => (hlt k hk i hi).1, fun k hk i hi => (hlt k hk i hi).2⟩

variable {gw wd lt : List (List ℕ)}

theorem rep_yI (hF : QFacts gw wd lt) {i : ℕ} (hi : i < 81) :
    e6Certificate.Represents ((qTups gw).getD i []) (yI gw wd i) := by
  rw [← hF.wdt i hi]
  exact rep_wordG hF.letters _

theorem yI_inj (hF : QFacts gw wd lt) {a b : ℕ} (ha : a < 81) (hb : b < 81)
    (h : yI gw wd a = yI gw wd b) : a = b := by
  have e := tuple_unique (rep_yI hF ha) (h ▸ rep_yI hF hb)
  rw [List.getD_eq_getElem _ _ (by rw [hF.len]; exact ha),
    List.getD_eq_getElem _ _ (by rw [hF.len]; exact hb)] at e
  exact (List.Nodup.getElem_inj_iff hF.nodup).1 e

theorem yI_zero (hF : QFacts gw wd lt) : yI gw wd 0 = 1 := by
  have h := rep_yI hF (show 0 < 81 by norm_num)
  rw [hF.zero] at h
  exact RootCertificate.represents_unique h (RootCertificate.represents_one e6Certificate_check)

theorem yI_mem (gw wd : List (List ℕ)) (i : ℕ) : yI gw wd i ∈ qSub gw := by
  unfold yI
  refine list_prod_mem fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact wordW_getD_mem gw k

theorem exists_yI (hF : QFacts gw wd lt) {y : WeylGroup Tag.E6} (hy : y ∈ qSub gw) :
    ∃ i < 81, yI gw wd i = y := by
  obtain ⟨t, ht, hrep⟩ := hF.cover y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  rw [hF.len] at hi
  refine ⟨i, hi, RootCertificate.represents_unique (rep_yI hF hi) ?_⟩
  rwa [List.getD_eq_getElem _ _ (by rw [hF.len]; exact hi)]

theorem yI_ltAt (hF : QFacts gw wd lt) {k i : ℕ} (hk : k < 4) (hi : i < 81) :
    yI gw wd (ltAt lt k i) = wordW (gw.getD k []) * yI gw wd i := by
  have h1 := rep_yI hF (hF.ltl k hk i hi)
  rw [← hF.ltt k hk i hi] at h1
  exact RootCertificate.represents_unique h1 (rep_wordT (rep_yI hF hi) _ (letters_getD hF.letters k))

theorem mulI_spec (hF : QFacts gw wd lt) {i j : ℕ} (hi : i < 81) (hj : j < 81) :
    mulI lt wd i j < 81 ∧ yI gw wd (mulI lt wd i j) = yI gw wd i * yI gw wd j := by
  have hks : ∀ ks : List ℕ, (∀ k ∈ ks, k < 4) →
      ks.foldr (fun k x => ltAt lt k x) j < 81 ∧
        yI gw wd (ks.foldr (fun k x => ltAt lt k x) j) =
          (ks.map fun k => wordW (gw.getD k [])).prod * yI gw wd j := by
    intro ks
    induction ks with
    | nil => intro _; simpa using hj
    | cons k ks ih =>
      intro hl
      obtain ⟨h1, h2⟩ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
      have hk := hl k List.mem_cons_self
      refine ⟨hF.ltl k hk _ h1, ?_⟩
      rw [List.foldr_cons, yI_ltAt hF hk h1, h2, List.map_cons, List.prod_cons, mul_assoc]
  have hl : ∀ k ∈ wd.getD i [], k < 4 := by
    by_cases h : i < wd.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hF.wdl _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp
  exact hks _ hl

theorem powI_spec (hF : QFacts gw wd lt) {i : ℕ} (hi : i < 81) :
    ∀ n, powI lt wd i n < 81 ∧ yI gw wd (powI lt wd i n) = yI gw wd i ^ n
  | 0 => ⟨by norm_num [powI], by rw [powI, yI_zero hF, pow_zero]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := powI_spec hF hi n
    obtain ⟨h3, h4⟩ := mulI_spec hF h1 hi
    exact ⟨h3, by rw [powI, h4, h2, pow_succ]⟩

theorem gEl_spec (hF : QFacts gw wd lt) {i j : ℕ} (hi : i < 81) (hj : j < 81) (a b : ℕ) :
    gEl lt wd i j a b < 81 ∧
      yI gw wd (gEl lt wd i j a b) = yI gw wd i ^ a * yI gw wd j ^ b := by
  obtain ⟨h1, h2⟩ := powI_spec hF hi a
  obtain ⟨h3, h4⟩ := powI_spec hF hj b
  obtain ⟨h5, h6⟩ := mulI_spec hF h1 h3
  exact ⟨h5, by rw [gEl, h6, h2, h4]⟩

theorem kindOK_getD {Q W : List (List ℕ)} (h : kindsCheck Q W = true) {x : ℕ}
    (hx : x < Q.length) : kindOK (Q.getD x []) (W.getD x []) = true := by
  simp only [kindsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  have hxW : x < W.length := h.1 ▸ hx
  rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hxW]
  refine h.2 (Q[x], W[x]) ?_
  rw [List.mem_iff_getElem]
  exact ⟨x, by rw [List.length_zip, ← h.1, Nat.min_self]; exact hx, by rw [List.getElem_zip]⟩

theorem is3A2_sound (hF : QFacts gw wd lt) {kw : List (List ℕ)}
    (hk : kindsCheck (qTups gw) kw = true) {x : ℕ} (hx : x < 81) (h : is3A2 kw x = true) :
    E6Kind3A2 (yI gw wd x) := by
  have hc := kindOK_getD hk (x := x) (by rw [hF.len]; exact hx)
  simp only [is3A2, beq_iff_eq] at h
  rw [h] at hc
  exact k3B_sound (rep_yI hF hx) hc

theorem is2A2_sound (hF : QFacts gw wd lt) {kw : List (List ℕ)}
    (hk : kindsCheck (qTups gw) kw = true) {x : ℕ} (hx : x < 81) (h : is2A2 kw x = true) :
    ∃ γ₁ γ₂, E6Kind2A2 (yI gw wd x) γ₁ γ₂ := by
  have hc := kindOK_getD hk (x := x) (by rw [hF.len]; exact hx)
  unfold is2A2 at h
  split at h
  · rename_i a b d m e
    rw [e] at hc
    exact ⟨_, _, k2B_sound (rep_yI hF hx) hc⟩
  · exact absurd h (by simp)

theorem mem_o3 {o3 : List ℕ} (hF : QFacts gw wd lt) (ho : o3OK lt wd o3 = true) {i : ℕ}
    (hi : i < 81) (h1 : yI gw wd i ≠ 1) (h3 : yI gw wd i ^ 3 = 1) : i ∈ o3 := by
  simp only [o3OK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at ho
  have e := ho.1 i hi
  have hi0 : i ≠ 0 := fun h => h1 (h ▸ yI_zero hF)
  have hp : powI lt wd i 3 = 0 := by
    obtain ⟨hlt, hy⟩ := powI_spec hF hi 3
    exact yI_inj hF hlt (by norm_num) (by rw [hy, h3, yI_zero hF])
  have : ord3 lt wd i = true := by simp [ord3, hi0, hp]
  rw [this] at e
  exact List.contains_iff_mem.1 e

theorem lt_of_mem_o3 {o3 : List ℕ} (ho : o3OK lt wd o3 = true) {i : ℕ} (hi : i ∈ o3) : i < 81 := by
  simp only [o3OK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ho
  exact ho.2 i hi

theorem pairFact_of_check (hF : QFacts gw wd lt) {kw bw : List (List ℕ)} {o3 : List ℕ}
    (hk : kindsCheck (qTups gw) kw = true) (ho : o3OK lt wd o3 = true)
    (hp : pairsCheck (qTups gw) kw lt wd o3 bw = true) {i j : ℕ} (hi : i ∈ o3) (hj : j ∈ o3)
    (hc : Commute (yI gw wd i) (yI gw wd j)) (hji : j ≠ i) (hj2 : j ≠ powI lt wd i 2) :
    (∃ a b : ℕ, E6Kind3A2 (yI gw wd i ^ a * yI gw wd j ^ b)) ∨
    ((∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ yI gw wd i • γ = γ ∧ yI gw wd j • γ = γ) ∧
      (∃ a b c d : ℕ, ¬ (3 : ℤ) ∣ ((a * d : ℕ) : ℤ) - ((b * c : ℕ) : ℤ) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (yI gw wd i ^ a * yI gw wd j ^ b) γ₁ γ₂) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (yI gw wd i ^ c * yI gw wd j ^ d) γ₁ γ₂)) ∧
      ∀ k ∈ o3, Commute (yI gw wd i) (yI gw wd k) → Commute (yI gw wd j) (yI gw wd k) →
        (∀ a b : ℕ, a < 3 → b < 3 → yI gw wd i ^ a * yI gw wd j ^ b ≠ yI gw wd k) →
          ∃ a b c : ℕ, E6Kind3A2 (yI gw wd i ^ a * yI gw wd j ^ b * yI gw wd k ^ c)) := by
  have hi81 := lt_of_mem_o3 ho hi
  have hj81 := lt_of_mem_o3 ho hj
  have hcomm : ∀ {x y : ℕ}, x < 81 → y < 81 → Commute (yI gw wd x) (yI gw wd y) →
      commI lt wd x y = true := by
    intro x y hx hy hxy
    obtain ⟨h1, h2⟩ := mulI_spec hF hx hy
    obtain ⟨h3, h4⟩ := mulI_spec hF hy hx
    simp only [commI, beq_iff_eq]
    exact yI_inj hF h1 h3 (by rw [h2, h4, hxy.eq])
  simp only [pairsCheck, List.all_eq_true] at hp
  have h := hp i hi j hj
  have hA : commI lt wd i j = true := hcomm hi81 hj81 hc
  have hB : (j != i) = true := by simpa using hji
  have hC : (j != powI lt wd i 2) = true := by simpa using hj2
  simp only [pairOK, hA, hB, hC, Bool.true_and, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    List.any_eq_true] at h
  rcases h with h | ⟨e, -, he⟩
  · left
    simp only [has3, List.any_eq_true, List.mem_range] at h
    obtain ⟨a, -, b, -, hab⟩ := h
    obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 a b
    exact ⟨a, b, hy ▸ is3A2_sound hF hk hx hab⟩
  · right
    unfold badOK at he
    split at he
    · rename_i i' j' r a b c d
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq,
        List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at he
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hr⟩, hfi⟩, hfj⟩, hdet⟩, h2a⟩, h2b⟩, hks⟩ := he
      rw [actV_rvL (rep_yI hF hi81), rvL_eq] at hfi
      rw [actV_rvL (rep_yI hF hj81), rvL_eq] at hfj
      refine ⟨⟨_, isRoot_root72 hr, ofFn_inj' hfi, ofFn_inj' hfj⟩, ⟨a, b, c, d, ?_, ?_, ?_⟩, ?_⟩
      · generalize a * d = X at hdet ⊢
        generalize b * c = Y at hdet ⊢
        omega
      · obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 a b
        exact hy ▸ is2A2_sound hF hk hx h2a
      · obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 c d
        exact hy ▸ is2A2_sound hF hk hx h2b
      · intro k hk3 hik hjk hout
        have hk81 := lt_of_mem_o3 ho hk3
        rcases hks k hk3 with ((h | h) | h) | h
        · rw [hcomm hi81 hk81 hik] at h
          exact absurd h (by simp)
        · rw [hcomm hj81 hk81 hjk] at h
          exact absurd h (by simp)
        · have h' : ¬ outG lt wd i j k = true := by
            rw [h]
            simp
          refine absurd ?_ h'
          simp only [outG, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
          intro a ha b hb e
          obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 a b
          exact hout a b ha hb (by rw [← hy, e])
        · simp only [has3k, List.any_eq_true, List.mem_range] at h
          obtain ⟨a, -, b, -, c, -, habc⟩ := h
          obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 a b
          obtain ⟨hz, hw⟩ := powI_spec hF hk81 c
          obtain ⟨hm, hmy⟩ := mulI_spec hF hx hz
          refine ⟨a, b, c, ?_⟩
          have := is3A2_sound hF hk hm habc
          rwa [hmy, hy, hw] at this
    · exact absurd he (by simp)

theorem exists_conj_yI (hF : QFacts gw wd lt)
    (hS : Nat.card (qSub gw) = 3 ^ (Nat.card (WeylGroup Tag.E6)).factorization 3)
    {s : Set (WeylGroup Tag.E6)} (hs : ∀ a ∈ s, ∀ b ∈ s, Commute a b) (h3 : ∀ a ∈ s, a ^ 3 = 1) :
    ∃ g : WeylGroup Tag.E6, ∀ x ∈ s, ∃ i < 81, MulAut.conj g (yI gw wd i) = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_le (qSub gw) hS (isPGroup_closure hs h3)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨i, hi, hyi⟩ := exists_yI hF (hg x (Subgroup.subset_closure hx))
  exact ⟨i, hi, by rw [MulAut.conj_apply, hyi]; group⟩

theorem mem_o3_conj {o3 : List ℕ} (hF : QFacts gw wd lt) (ho : o3OK lt wd o3 = true)
    {g w : WeylGroup Tag.E6} {i : ℕ} (hi : i < 81) (hw : MulAut.conj g (yI gw wd i) = w)
    (h3 : w ^ 3 = 1) (h1 : w ≠ 1) : i ∈ o3 := by
  refine mem_o3 hF ho hi (fun h => h1 ?_) ((MulAut.conj g).injective ?_)
  · rw [← hw, h, map_one]
  · rw [map_pow, hw, h3, map_one]

theorem commute_conj {g w w' : WeylGroup Tag.E6} {y y' : WeylGroup Tag.E6}
    (hw : MulAut.conj g y = w) (hw' : MulAut.conj g y' = w') (h : Commute w w') : Commute y y' := by
  have e := h.map (MulAut.conj g).symm
  rwa [← hw, ← hw', MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at e

theorem ne_of_not_mem_zpowers (hF : QFacts gw wd lt) {g w₁ w₂ : WeylGroup Tag.E6} {i j : ℕ}
    (hi : i < 81) (h1 : MulAut.conj g (yI gw wd i) = w₁) (h2 : MulAut.conj g (yI gw wd j) = w₂)
    (hn : w₂ ∉ Subgroup.zpowers w₁) : j ≠ i ∧ j ≠ powI lt wd i 2 := by
  refine ⟨fun e => hn ?_, fun e => hn ?_⟩
  · rw [← h2, e, h1]
    exact Subgroup.mem_zpowers _
  · rw [← h2, e, (powI_spec hF hi 2).2, map_pow, h1]
    exact Subgroup.npow_mem_zpowers _ _

theorem e6Order3Pairs_of_checks {kw bw : List (List ℕ)} {o3 : List ℕ}
    (hq : qCheckWith gw (qTups gw) = true) (hwd : wdOK gw (qTups gw) wd = true)
    (hlt : ltOK gw (qTups gw) lt = true) (hk : kindsCheck (qTups gw) kw = true)
    (ho : o3OK lt wd o3 = true) (hp : pairsCheck (qTups gw) kw lt wd o3 bw = true) :
    E6Order3Pairs := by
  have hF := qFacts_of_checks hq hwd hlt
  have hS : Nat.card (qSub gw) = 3 ^ (Nat.card (WeylGroup Tag.E6)).factorization 3 := by
    rw [(exists_subgroup_of_qCheck hq).1,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6, factorization_E6]
    norm_num
  intro w₁ w₂ h13 h11 h23 hc12 hn
  have h21 : w₂ ≠ 1 := fun h => hn (h ▸ Subgroup.one_mem _)
  have pair_s : ∀ a ∈ ({w₁, w₂} : Set (WeylGroup Tag.E6)),
      ∀ b ∈ ({w₁, w₂} : Set (WeylGroup Tag.E6)), Commute a b := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [Commute.refl _, hc12, hc12.symm, Commute.refl _]
  have pair_3 : ∀ a ∈ ({w₁, w₂} : Set (WeylGroup Tag.E6)), a ^ 3 = 1 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    exacts [h13, h23]
  obtain ⟨g, hg⟩ := exists_conj_yI hF hS pair_s pair_3
  obtain ⟨i, hi, hw1⟩ := hg w₁ (by simp)
  obtain ⟨j, hj, hw2⟩ := hg w₂ (by simp)
  obtain ⟨hji, hj2⟩ := ne_of_not_mem_zpowers hF hi hw1 hw2 hn
  have key := pairFact_of_check hF hk ho hp (mem_o3_conj hF ho hi hw1 h13 h11)
    (mem_o3_conj hF ho hj hw2 h23 h21) (commute_conj hw1 hw2 hc12) hji hj2
  have prod_eq : ∀ a b : ℕ, MulAut.conj g (yI gw wd i ^ a * yI gw wd j ^ b) = w₁ ^ a * w₂ ^ b :=
    fun a b => by rw [map_mul, map_pow, map_pow, hw1, hw2]
  rcases key with ⟨a, b, h⟩ | ⟨⟨γ, hγ, f1, f2⟩, ⟨a, b, c, d, hdet, ⟨γ₁, γ₂, h2a⟩, ⟨δ₁, δ₂, h2b⟩⟩, -⟩
  · left
    refine ⟨a, b, ?_⟩
    have e := kind3_conj h g
    rwa [← MulAut.conj_apply, prod_eq] at e
  · right
    refine ⟨⟨g • γ, IsRoot.smul hγ g, ?_, ?_⟩, ⟨a, b, c, d, hdet, ?_, ?_⟩, ?_⟩
    · rw [← hw1, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul, f1]
    · rw [← hw2, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul, f2]
    · have e := kind2_conj h2a g
      rw [← MulAut.conj_apply, prod_eq] at e
      exact ⟨_, _, e⟩
    · have e := kind2_conj h2b g
      rw [← MulAut.conj_apply, prod_eq] at e
      exact ⟨_, _, e⟩
    · intro w₃ h33 hc13 hc23 hout
      have h31 : w₃ ≠ 1 := by simpa using hout 0 0
      have tri_s : ∀ a ∈ ({w₁, w₂, w₃} : Set (WeylGroup Tag.E6)),
          ∀ b ∈ ({w₁, w₂, w₃} : Set (WeylGroup Tag.E6)), Commute a b := by
        intro a ha b hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        exacts [Commute.refl _, hc12, hc13, hc12.symm, Commute.refl _, hc23, hc13.symm,
          hc23.symm, Commute.refl _]
      have tri_3 : ∀ a ∈ ({w₁, w₂, w₃} : Set (WeylGroup Tag.E6)), a ^ 3 = 1 := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        exacts [h13, h23, h33]
      obtain ⟨g', hg'⟩ := exists_conj_yI hF hS tri_s tri_3
      obtain ⟨i', hi', hv1⟩ := hg' w₁ (by simp)
      obtain ⟨j', hj', hv2⟩ := hg' w₂ (by simp)
      obtain ⟨k', hk', hv3⟩ := hg' w₃ (by simp)
      obtain ⟨hji', hj2'⟩ := ne_of_not_mem_zpowers hF hi' hv1 hv2 hn
      have key' := pairFact_of_check hF hk ho hp (mem_o3_conj hF ho hi' hv1 h13 h11)
        (mem_o3_conj hF ho hj' hv2 h23 h21) (commute_conj hv1 hv2 hc12) hji' hj2'
      have prod3 : ∀ a b c : ℕ, MulAut.conj g'
          (yI gw wd i' ^ a * yI gw wd j' ^ b * yI gw wd k' ^ c) = w₁ ^ a * w₂ ^ b * w₃ ^ c :=
        fun a b c => by rw [map_mul, map_mul, map_pow, map_pow, map_pow, hv1, hv2, hv3]
      rcases key' with ⟨a, b, h⟩ | ⟨-, -, hk3⟩
      · refine ⟨a, b, 0, ?_⟩
        have e := kind3_conj (show E6Kind3A2 (yI gw wd i' ^ a * yI gw wd j' ^ b * yI gw wd k' ^ 0)
          by rwa [pow_zero, mul_one]) g'
        rwa [← MulAut.conj_apply, prod3] at e
      · obtain ⟨a, b, c, h⟩ := hk3 k' (mem_o3_conj hF ho hk' hv3 h33 h31)
          (commute_conj hv1 hv3 hc13) (commute_conj hv2 hv3 hc23) (fun a b _ _ e => hout a b (by
            rw [← hv1, ← hv2, ← hv3, ← e, map_mul, map_pow, map_pow]))
        refine ⟨a, b, c, ?_⟩
        have e := kind3_conj h g'
        rwa [← MulAut.conj_apply, prod3] at e

end CFSG.KC.E6Syl3
