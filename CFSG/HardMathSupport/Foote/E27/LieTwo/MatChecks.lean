module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatTable
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Sporadic.He.Native

@[expose] def FpfM {d : ℕ} (M : M2 d) : Prop := ∀ v : Fin d → ZMod 2, M *ᵥ v = v → v = 0

instance {d : ℕ} (M : M2 d) : Decidable (FpfM M) := by
  unfold FpfM; infer_instance

@[expose] def fpfB {d : ℕ} (M : M2 d) : Bool := decide (FpfM M)

@[expose] def tabPw (par : Array (ℕ × ℕ)) (L : Array (Array ℕ)) (x i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then x else tabMul par L x x

@[expose] def fpfA (d : ℕ) (X : AM) : Bool := fpfB (toMat 2 d X)

@[expose] def centralTOK (d : ℕ) (T : RawTab) : Bool :=
  let n := T.elts.size
  let fp := T.elts.map (fpfA d)
  (List.range n).all (fun a => (a == 0) ||
    !((List.range n).all fun b => tabMul T.par T.L a b == tabMul T.par T.L b a) ||
    fp[a]!) &&
  (List.range n).all (fun α =>
    (α == 0) || !(tabMul T.par T.L α (tabMul T.par T.L α α) == 0) ||
    (List.range n).all fun β =>
      (β == 0) || (β == α) || (β == tabMul T.par T.L α α) ||
      !(tabMul T.par T.L β (tabMul T.par T.L β β) == 0) ||
      !(tabMul T.par T.L α β == tabMul T.par T.L β α) ||
      (List.range 3).any fun i => (List.range 3).any fun j =>
        let γ := tabMul T.par T.L (tabPw T.par T.L α i) (tabPw T.par T.L β j)
        (γ != 0) && !(fp[γ]!))

@[expose] def tabAbelianOK (B : RawTab) : Bool :=
  (List.range B.elts.size).all fun a => (List.range B.elts.size).all fun b =>
    tabMul B.par B.L a b == tabMul B.par B.L b a

@[expose] def coverOK (d : ℕ) (adm : AM → Bool) (S B : RawTab) (wits : Array (AM × AM)) :
    Bool :=
  (List.range S.elts.size).all fun a =>
    (a == 0) || !(tabMul S.par S.L a (tabMul S.par S.L a a) == 0) ||
    wits.any fun w => matEqB 2 d w.1 S.elts[a]! && adm w.2 &&
      (List.range B.elts.size).any fun b =>
        matEqB 2 d (mulM 2 d w.2 S.elts[a]!) (mulM 2 d B.elts[b]! w.2)

@[expose] def coverOK3 (d : ℕ) (adm : AM → AM → Bool) (S B : RawTab)
    (wits : Array (AM × AM × AM)) : Bool :=
  (List.range S.elts.size).all fun a =>
    (a == 0) || !(tabMul S.par S.L a (tabMul S.par S.L a a) == 0) ||
    wits.any fun w => matEqB 2 d w.1 S.elts[a]! && adm w.2.1 w.2.2 &&
      (List.range B.elts.size).any fun b =>
        matEqB 2 d (mulM 2 d w.2.1 S.elts[a]!) (mulM 2 d B.elts[b]! w.2.1)

@[expose] def commOK (T : RawTab) : Bool :=
  (List.range T.elts.size).all fun a =>
    (a == 0) || !(tabMul T.par T.L a (tabMul T.par T.L a a) == 0) ||
    decide (81 ≤ tabComm T.par T.L T.elts.size a)

theorem factorization_three_of_eq {n k m : ℕ} (h : n = 3 ^ k * m) (hm : ¬ 3 ∣ m) :
    n.factorization 3 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [h, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem fpfM_conj_mp {d : ℕ} {G : Type*} [Group G] (mat : G →* M2 d) (g x : G)
    (h : FpfM (mat x)) : FpfM (mat (g * x * g⁻¹)) := by
  intro w hw
  have hinv : mat g⁻¹ * mat g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : mat g * mat g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have this' : (mat g * mat x * mat g⁻¹) *ᵥ w = w := by
    have := hw
    rwa [map_mul, map_mul] at this
  have h1 : mat x *ᵥ (mat g⁻¹ *ᵥ w) = mat g⁻¹ *ᵥ w := by
    calc mat x *ᵥ (mat g⁻¹ *ᵥ w)
        = (mat g⁻¹ * mat g) *ᵥ (mat x *ᵥ (mat g⁻¹ *ᵥ w)) := by rw [hinv, Matrix.one_mulVec]
      _ = mat g⁻¹ *ᵥ ((mat g * mat x * mat g⁻¹) *ᵥ w) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = mat g⁻¹ *ᵥ w := by rw [this']
  have h3 := h _ h1
  have : w = mat g *ᵥ (mat g⁻¹ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  rw [this, h3, Matrix.mulVec_zero]

theorem fpfM_conj {d : ℕ} {G : Type*} [Group G] (mat : G →* M2 d) (g x : G) :
    FpfM (mat (g * x * g⁻¹)) = FpfM (mat x) := by
  apply propext
  refine ⟨fun h => ?_, fpfM_conj_mp mat g x⟩
  have := fpfM_conj_mp mat g⁻¹ _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

section Spec

variable {d : ℕ} {G : Type*} [Group G] {g : ℕ → G} {par : Array (ℕ × ℕ)} {L : Array (Array ℕ)}
  {n m : ℕ}

theorem tab_comm_iff (h : TabData g par L n m) {a b : ℕ} (ha : a < n) (hb : b < n) :
    tabElt g par a * tabElt g par b = tabElt g par b * tabElt g par a ↔
      tabMul par L a b = tabMul par L b a := by
  obtain ⟨hl1, e1⟩ := h.mul a ha b hb
  obtain ⟨hl2, e2⟩ := h.mul b hb a ha
  rw [e1, e2]
  exact ⟨fun e => h.inj _ hl1 _ hl2 e, fun e => by rw [e]⟩

theorem tab_cube_iff (h : TabData g par L n m) {a : ℕ} (ha : a < n) :
    tabElt g par a ^ 3 = 1 ↔ tabMul par L a (tabMul par L a a) = 0 := by
  obtain ⟨hl1, e1⟩ := h.mul a ha a ha
  obtain ⟨hl2, e2⟩ := h.mul a ha _ hl1
  have h0 : 0 < n := by omega
  constructor
  · intro hpow
    have : tabElt g par (tabMul par L a (tabMul par L a a)) = tabElt g par 0 := by
      rw [tabElt_zero, ← e2, ← e1, ← hpow, pow_three', mul_assoc]
    exact h.inj _ hl2 0 h0 this
  · intro h3
    rw [h3, tabElt_zero] at e2
    rw [pow_three, e1, e2]

theorem tab_pw (h : TabData g par L n m) {a : ℕ} (ha : a < n) {i : ℕ} (hi : i < 3) :
    tabPw par L a i < n ∧ tabElt g par (tabPw par L a i) = tabElt g par a ^ i := by
  have h0 : 0 < n := by omega
  interval_cases i
  · refine ⟨h0, ?_⟩
    simp [tabPw, tabElt_zero]
  · refine ⟨ha, ?_⟩
    simp [tabPw]
  · obtain ⟨hl, e⟩ := h.mul a ha a ha
    refine ⟨?_, ?_⟩
    · simpa [tabPw] using hl
    · simp only [tabPw]
      simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false]
      rw [← e, pow_two]

theorem centralT_hyps (mat : G →* M2 d) (T : RawTab)
    (hT : TabData g T.par T.L T.elts.size m)
    (heq : ∀ i < T.elts.size, mat (tabElt g T.par i) = toMat 2 d T.elts[i]!)
    (hc : centralTOK d T = true) {S₀ : Subgroup G}
    (hS₀ : ∀ x, x ∈ S₀ ↔ ∃ i < T.elts.size, tabElt g T.par i = x) :
    (∀ c ∈ S₀, c ≠ 1 → (∀ s ∈ S₀, s * c = c * s) → FpfM (mat c)) ∧
    (∀ a ∈ S₀, ∀ b ∈ S₀, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
      ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧ ¬ FpfM (mat (a ^ i * b ^ j))) := by
  have hfpIdx : ∀ i < T.elts.size, (T.elts.map (fpfA d))[i]! = fpfB (toMat 2 d T.elts[i]!) := by
    intro i hi
    rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i hi, Array.getElem_map]
    rfl
  unfold centralTOK at hc
  dsimp only at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hc1, hc2⟩ := hc
  rw [List.all_eq_true] at hc1 hc2
  constructor
  · intro c hcS hc1' hcen
    obtain ⟨a, ha, rfl⟩ := (hS₀ c).1 hcS
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hc1' (tabElt_zero g T.par)
    have hall : (List.range T.elts.size).all (fun b =>
        tabMul T.par T.L a b == tabMul T.par T.L b a) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      intro b hb
      exact (tab_comm_iff hT ha hb).1 (hcen _ ((hS₀ _).2 ⟨b, hb, rfl⟩)).symm
    have h1 := hc1 a (List.mem_range.2 ha)
    have h2 : (T.elts.map (fpfA d))[a]! = true := by
      simpa [hall, ha0] using h1
    rw [hfpIdx a ha] at h2
    have h3 : FpfM (toMat 2 d T.elts[a]!) := of_decide_eq_true h2
    rw [heq a ha]
    exact h3
  · intro a haS b hbS ha3 hb3 hab ha1 hbz
    obtain ⟨α, hα, rfl⟩ := (hS₀ a).1 haS
    obtain ⟨β, hβ, rfl⟩ := (hS₀ b).1 hbS
    have hα0 : α ≠ 0 := by
      rintro rfl
      exact ha1 (tabElt_zero g T.par)
    have hβ0 : β ≠ 0 := by
      rintro rfl
      exact hbz (by rw [tabElt_zero]; exact one_mem _)
    have hβα : β ≠ α := by
      rintro rfl
      exact hbz (mem_zpowers _)
    have hβα2 : β ≠ tabMul T.par T.L α α := by
      intro e
      apply hbz
      obtain ⟨hl, e1⟩ := hT.mul α hα α hα
      rw [e, ← e1, ← pow_two]
      exact pow_mem (mem_zpowers _) 2
    have hc3 := (tab_cube_iff hT hα).1 ha3
    have hc4 := (tab_cube_iff hT hβ).1 hb3
    have hc5 := (tab_comm_iff hT hα hβ).1 hab
    have h1 := hc2 α (List.mem_range.2 hα)
    have h1' : (List.range T.elts.size).all (fun β' =>
        β' == 0 || β' == α || β' == tabMul T.par T.L α α ||
        !(tabMul T.par T.L β' (tabMul T.par T.L β' β') == 0) ||
        !(tabMul T.par T.L α β' == tabMul T.par T.L β' α) ||
        (List.range 3).any fun i => (List.range 3).any fun j =>
          let γ := tabMul T.par T.L (tabPw T.par T.L α i) (tabPw T.par T.L β' j)
          (γ != 0) && !((T.elts.map (fpfA d))[γ]!)) = true := by
      simp only [Bool.or_eq_true] at h1
      rcases h1 with (h | h) | h
      · exact absurd (beq_iff_eq.1 h) hα0
      · exfalso
        rw [hc3] at h
        simp at h
      · exact h
    rw [List.all_eq_true] at h1'
    have h2 := h1' β (List.mem_range.2 hβ)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', hβ0, hβα, hβα2, hc4, hc5,
      List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq, false_or,
      beq_self_eq_true, Bool.not_true, Bool.false_eq_true, or_false,
      Bool.not_eq_true] at h2
    obtain ⟨i, hi, j, hj, hγ0, hγf⟩ := h2
    obtain ⟨hli, ei⟩ := tab_pw hT hα hi
    obtain ⟨hlj, ej⟩ := tab_pw hT hβ hj
    obtain ⟨hlγ, eγ⟩ := hT.mul _ hli _ hlj
    refine ⟨i, j, ?_, ?_⟩
    · rw [← ei, ← ej, eγ]
      intro e
      apply hγ0
      exact hT.inj _ hlγ 0 (by omega) (by rw [e, tabElt_zero])
    · rw [← ei, ← ej, eγ, heq _ hlγ]
      intro hf
      have : (T.elts.map (fpfA d))[tabMul T.par T.L (tabPw T.par T.L α i)
          (tabPw T.par T.L β j)]! = true := by
        rw [hfpIdx _ hlγ]; exact decide_eq_true hf
      rw [this] at hγf
      exact absurd hγf (by simp)

theorem tabAbelian_spec {T : RawTab} (hB : TabData g T.par T.L T.elts.size m)
    (hc : tabAbelianOK T = true) {B₀ : Subgroup G}
    (hB₀ : ∀ x, x ∈ B₀ ↔ ∃ i < T.elts.size, tabElt g T.par i = x) :
    ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := by
  unfold tabAbelianOK at hc
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := (hB₀ x).1 hx
  obtain ⟨b, hb, rfl⟩ := (hB₀ y).1 hy
  rw [tab_comm_iff hB ha hb]
  exact hc a ha b hb

theorem cover_hyps (mat : G →* M2 d) (hinj : Function.Injective mat) (adm : AM → Bool)
    (hadm : ∀ X, adm X = true → ∃ x : G, mat x = toMat 2 d X)
    (S B : RawTab) (wits : Array (AM × AM)) {gS gB : ℕ → G} {mS mB : ℕ}
    (hS : TabData gS S.par S.L S.elts.size mS)
    (heqS : ∀ i < S.elts.size, mat (tabElt gS S.par i) = toMat 2 d S.elts[i]!)
    (hB : TabData gB B.par B.L B.elts.size mB)
    (heqB : ∀ i < B.elts.size, mat (tabElt gB B.par i) = toMat 2 d B.elts[i]!)
    (hc : coverOK d adm S B wits = true) {S₀ B₀ : Subgroup G}
    (hS₀ : ∀ x, x ∈ S₀ ↔ ∃ i < S.elts.size, tabElt gS S.par i = x)
    (hB₀ : ∀ x, x ∈ B₀ ↔ ∃ i < B.elts.size, tabElt gB B.par i = x) :
    ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ x : G, x * s * x⁻¹ ∈ B₀ := by
  intro s hs hs3 hs1
  obtain ⟨a, ha, rfl⟩ := (hS₀ s).1 hs
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hs1 (tabElt_zero gS S.par)
  have hcube := (tab_cube_iff hS ha).1 hs3
  unfold coverOK at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have h1 := hc a ha
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', hcube, ha0, List.any_eq_true,
    Bool.and_eq_true, false_or, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
    or_false] at h1
  obtain ⟨w, -, hw⟩ := Array.any_eq_true'.mp h1
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range] at hw
  obtain ⟨⟨hw1, hw2⟩, b, hb, hw3⟩ := hw
  obtain ⟨x, hx⟩ := hadm w.2 hw2
  have key : x * tabElt gS S.par a = tabElt gB B.par b * x := by
    apply hinj
    rw [map_mul, map_mul, hx, heqS a ha, heqB b hb]
    have := matEqB_true hw3
    rw [toMat_mulM, toMat_mulM] at this
    exact this
  refine ⟨x, ?_⟩
  have e : x * tabElt gS S.par a * x⁻¹ = tabElt gB B.par b := by
    rw [key]; group
  rw [e]
  exact (hB₀ _).2 ⟨b, hb, rfl⟩


theorem cover_hyps3 (mat : G →* M2 d) (hinj : Function.Injective mat) (adm : AM → AM → Bool)
    (hadm : ∀ X Xi, adm X Xi = true → ∃ x : G, mat x = toMat 2 d X)
    (S B : RawTab) (wits : Array (AM × AM × AM)) {gS gB : ℕ → G} {mS mB : ℕ}
    (hS : TabData gS S.par S.L S.elts.size mS)
    (heqS : ∀ i < S.elts.size, mat (tabElt gS S.par i) = toMat 2 d S.elts[i]!)
    (hB : TabData gB B.par B.L B.elts.size mB)
    (heqB : ∀ i < B.elts.size, mat (tabElt gB B.par i) = toMat 2 d B.elts[i]!)
    (hc : coverOK3 d adm S B wits = true) {S₀ B₀ : Subgroup G}
    (hS₀ : ∀ x, x ∈ S₀ ↔ ∃ i < S.elts.size, tabElt gS S.par i = x)
    (hB₀ : ∀ x, x ∈ B₀ ↔ ∃ i < B.elts.size, tabElt gB B.par i = x) :
    ∀ s ∈ S₀, s ^ 3 = 1 → s ≠ 1 → ∃ x : G, x * s * x⁻¹ ∈ B₀ := by
  intro s hs hs3 hs1
  obtain ⟨a, ha, rfl⟩ := (hS₀ s).1 hs
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hs1 (tabElt_zero gS S.par)
  have hcube := (tab_cube_iff hS ha).1 hs3
  unfold coverOK3 at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have h1 := hc a ha
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', hcube, ha0, List.any_eq_true,
    Bool.and_eq_true, false_or, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
    or_false] at h1
  obtain ⟨w, -, hw⟩ := Array.any_eq_true'.mp h1
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range] at hw
  obtain ⟨⟨hw1, hw2⟩, b, hb, hw3⟩ := hw
  obtain ⟨x, hx⟩ := hadm w.2.1 w.2.2 hw2
  have key : x * tabElt gS S.par a = tabElt gB B.par b * x := by
    apply hinj
    rw [map_mul, map_mul, hx, heqS a ha, heqB b hb]
    have := matEqB_true hw3
    rw [toMat_mulM, toMat_mulM] at this
    exact this
  refine ⟨x, ?_⟩
  have e : x * tabElt gS S.par a * x⁻¹ = tabElt gB B.par b := by
    rw [key]; group
  rw [e]
  exact (hB₀ _).2 ⟨b, hb, rfl⟩

theorem commOK_hyps [Finite G] (T : RawTab) (hT : TabData g T.par T.L T.elts.size m)
    (hc : commOK T = true) {S₀ : Subgroup G}
    (hS₀ : ∀ x, x ∈ S₀ ↔ ∃ i < T.elts.size, tabElt g T.par i = x)
    (hn : T.elts.size = 3 ^ (Nat.card G).factorization 3) :
    Nat.card S₀ = 3 ^ (Nat.card G).factorization 3 ∧
      ∀ s ∈ S₀, orderOf s = 3 → 81 ∣ Nat.card ↥(S₀ ⊓ centralizer ({s} : Set G)) := by
  refine TabData.sylow_kill hT hS₀ hn ?_
  unfold commOK at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq] at hc
  intro a ha ha0 hcube
  rcases hc a ha with (h0 | h1) | h2
  · exact absurd h0 ha0
  · rw [hcube] at h1; simp at h1
  · exact h2


end Spec

end CFSG.HardMathSupport.Foote.E27
