module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.Monster.Existence.Defs
public import CFSG.Sporadic.Fi23.Simple
public import CFSG.Sporadic.HN
public import CFSG.Milestones.FAM_Th_simplicity
public import CFSG.RankThree.OddKernel.SporadicKernelTh

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator Subgroup

section Generic

variable {G : Type*} [Group G]

theorem orderOf_eq_of_isConj' {u v : G} (h : IsConj u v) : orderOf u = orderOf v := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact SemiconjBy.orderOf_eq c (show c * u = v * c by rw [← hc]; group)

theorem gLAPPrimeCoreOf_eq_bot_of_isSimpleGroup {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : IsSimpleGroup ↥H) (hpH : p ∣ Nat.card H) : GLAPPrimeCoreOf p H = ⊥ := by
  have h : GLAPPrimeCore p ↥H = ⊥ := by
    refine le_bot_iff.1 (sSup_le ?_)
    rintro N ⟨hN, hcop⟩
    have := hN
    rcases hH.eq_bot_or_eq_top_of_normal N with h | h
    · exact le_of_eq h
    · exfalso
      rw [h, Subgroup.card_top] at hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpH)
  unfold GLAPPrimeCoreOf
  rw [h, Subgroup.map_bot]

theorem centralizer_inf_centralizer_mul_eq (α β : G) :
    Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({β} : Set G) =
      Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({α * β} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ((Commute.mul_right (show Commute x α from h1) (show Commute x β from h2))).eq⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := Commute.mul_right (Commute.inv_right (show Commute x α from h1))
      (show Commute x (α * β) from h2)
    simpa using this.eq

end Generic

section Monster

variable {G : Type} [Group G]

@[expose] def InvertedByTwoA (s : G) : Prop :=
  ∃ α : G, orderOf α = 2 ∧ Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder ∧
    α * s * α⁻¹ = s⁻¹

@[expose] def UninvertedOPrimeTrivial (p : ℕ) (G : Type) [Group G] : Prop :=
  ∀ s : G, orderOf s = p → ¬ InvertedByTwoA s →
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥

theorem twoA_data_of_existence (hE : MonsterExistenceStatement G) :
    Finite G ∧ ∃ a : G, (∀ α : G, orderOf α = 2 →
      Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder → IsConj a α) ∧
      (∀ x y : G, IsConj a x → IsConj a y → orderOf (x * y) ≤ 6) ∧
      (∀ α β : G, IsConj a α → IsConj a β →
        ∃ i : Fin 9, suborbitClassOrder i = orderOf (α * β) ∧ TwoPointShape (cent2 α β) i) := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, -, -, -, hcls, -, hB, hgraph⟩ := hE
  obtain ⟨-, c, -, -, -, -, hord, hcov, -, hshape, -⟩ := hgraph
  refine ⟨hfin, a, ?_, ?_, ?_⟩
  · intro α hα hαc
    rcases hcls α hα with h | h
    · exact h
    · exfalso
      have h2 := (hB α h).2.2.2.2.1
      rw [hαc] at h2
      norm_num [twoBCentralizerOrder, monsterBabyOrder] at h2
  · intro x y hx hy
    obtain ⟨i, hi⟩ := hcov x y hx hy
    rw [orderOf_eq_of_isConj' hi, hord i]
    fin_cases i <;> simp [suborbitClassOrder]
  · intro α β hα hβ
    obtain ⟨i, hi⟩ := hcov α β hα hβ
    refine ⟨i, ?_, hshape α β i hα hβ hi⟩
    rw [← hord i, orderOf_eq_of_isConj' hi]

theorem gLAPPrimeCoreOf_eq_bot_of_twoPointShape
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    {i : Fin 9} (hi : suborbitClassOrder i = p) (h : TwoPointShape H i) :
    GLAPPrimeCoreOf p H = ⊥ := by
  fin_cases i
  · simp [suborbitClassOrder] at hi
    exact absurd hi hp.one_lt.ne
  · simp [suborbitClassOrder] at hi
    exact absurd hi.symm hp2
  · simp [suborbitClassOrder] at hi
    exact absurd hi.symm hp2
  · simp [suborbitClassOrder] at hi
    subst hi
    obtain ⟨e⟩ : Nonempty (↥H ≃* CFSG.Blueprint.NativeSporadic.Fi23) := h
    have hs : IsSimpleGroup ↥H := @MulEquiv.isSimpleGroup ↥H _ CFSG.Blueprint.NativeSporadic.Fi23
      Units.instGroup CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 e
    refine gLAPPrimeCoreOf_eq_bot_of_isSimpleGroup hp hs ?_
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    norm_num
  · simp [suborbitClassOrder] at hi
    subst hi
    obtain ⟨e⟩ : Nonempty (↥H ≃* CFSG.Blueprint.NativeSporadic.Th) := h
    have hs : IsSimpleGroup ↥H := @MulEquiv.isSimpleGroup ↥H _ CFSG.Blueprint.NativeSporadic.Th
      Units.instGroup CFSG.Milestones.fam_th_simplicity e
    refine gLAPPrimeCoreOf_eq_bot_of_isSimpleGroup hp hs ?_
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.OddKernel.card_Th_eq]
    norm_num
  · simp [suborbitClassOrder] at hi
    exact absurd (hi ▸ hp) (by norm_num)
  · simp [suborbitClassOrder] at hi
    exact absurd (hi ▸ hp) (by norm_num)
  · simp [suborbitClassOrder] at hi
    subst hi
    obtain ⟨e⟩ : Nonempty (↥H ≃* CFSG.Blueprint.NativeSporadic.HN) := h
    have hs : IsSimpleGroup ↥H := @MulEquiv.isSimpleGroup ↥H _ CFSG.Blueprint.NativeSporadic.HN
      Units.instGroup CFSG.Sporadic.HN.isSimpleGroup_HN e
    refine gLAPPrimeCoreOf_eq_bot_of_isSimpleGroup hp hs ?_
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HN.card_HN]
    norm_num
  · simp [suborbitClassOrder] at hi
    exact absurd (hi ▸ hp) (by norm_num)

theorem invertedByTwoA_data (hE : MonsterExistenceStatement G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : G} (hs : orderOf s = p) (hinv : InvertedByTwoA s) :
    Finite G ∧ ∃ α : G, α * α = 1 ∧ α * s * α⁻¹ = s⁻¹ ∧
      (∀ x y : G, IsConj α x → IsConj α y → orderOf (x * y) ≤ 6) ∧
      ∃ i : Fin 9, suborbitClassOrder i = p ∧
        TwoPointShape
          (Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) i := by
  obtain ⟨hfin, a, hcls, hbd, hshape⟩ := twoA_data_of_existence hE
  obtain ⟨α, hα2, hαc, hαs⟩ := hinv
  have hαA : IsConj a α := hcls α hα2 hαc
  have hαα : α * α = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα2, sq] at this
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hsodd : Odd (orderOf s⁻¹) := by rw [orderOf_inv, hs]; exact hpodd
  have hinv' : α * s⁻¹ * α⁻¹ = (s⁻¹)⁻¹ := by
    have := conj_inv (a := s) (b := α)
    rw [hαs, inv_inv] at this
    rw [inv_inv]
    exact this.symm
  have hβ : IsConj a (s⁻¹ * α) := hαA.trans (isConj_mul_of_inverts_odd hinv' hsodd)
  have hαβ : α * (s⁻¹ * α) = s := by
    calc α * (s⁻¹ * α) = α * s⁻¹ * α⁻¹ := by rw [hαi]; group
      _ = s := by rw [hinv', inv_inv]
  refine ⟨hfin, α, hαα, hαs, fun x y hx hy => hbd x y (hαA.trans hx) (hαA.trans hy), ?_⟩
  obtain ⟨i, hi, hsh⟩ := hshape α (s⁻¹ * α) hαA hβ
  rw [hαβ, hs] at hi
  refine ⟨i, hi, ?_⟩
  have := centralizer_inf_centralizer_mul_eq α (s⁻¹ * α)
  rw [hαβ] at this
  rw [← this]
  exact hsh

theorem orderOf_eq_three_or_five_of_invertedByTwoA (hE : MonsterExistenceStatement G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {s : G} (hs : orderOf s = p) (hinv : InvertedByTwoA s) :
    p = 3 ∨ p = 5 := by
  obtain ⟨-, α, -, -, -, i, hi, -⟩ := invertedByTwoA_data hE hp hp2 hs hinv
  fin_cases i <;> simp [suborbitClassOrder] at hi
  · exact absurd hi hp.one_lt.ne
  · exact absurd hi.symm hp2
  · exact absurd hi.symm hp2
  · exact Or.inl hi.symm
  · exact Or.inl hi.symm
  · exact absurd (hi ▸ hp) (by norm_num)
  · exact absurd (hi ▸ hp) (by norm_num)
  · exact Or.inr hi.symm
  · exact absurd (hi ▸ hp) (by norm_num)

theorem gLAPPrimeCoreOf_eq_bot_of_invertedByTwoA
    (hE : MonsterExistenceStatement G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : G} (hs : orderOf s = p) (hinv : InvertedByTwoA s) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  obtain ⟨hfin, α, hαα, hαs, hbd, i, hi, hsh⟩ := invertedByTwoA_data hE hp hp2 hs hinv
  have := hfin
  exact gLAPPrimeCoreOf_centralizer_eq_bot_of_inverting_involution hp hp2 hαα hs
    (by simpa using hαs) (gLAPPrimeCoreOf_eq_bot_of_twoPointShape hp hp2 hi hsh) hbd

theorem not_invertedByTwoA_of_ne (hE : MonsterExistenceStatement G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) {s : G} (hs : orderOf s = p) :
    ¬ InvertedByTwoA s := by
  intro hinv
  rcases orderOf_eq_three_or_five_of_invertedByTwoA hE hp hp2 hs hinv with h | h
  · exact hp3 h
  · exact hp5 h

theorem oPrimeCoreTrivialAt_of_uninverted
    (hE : MonsterExistenceStatement G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : UninvertedOPrimeTrivial p G) : OPrimeCoreTrivialAt p G := by
  intro s hs
  by_cases hinv : InvertedByTwoA s
  · exact gLAPPrimeCoreOf_eq_bot_of_invertedByTwoA hE hp hp2 hs hinv
  · exact h s hs hinv

theorem natCard_centralizer_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (a : K) :
    Nat.card ↥(Subgroup.centralizer ({e a} : Set K')) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set K)) := by
  have hc := map_inf_centralizer_of_injective e.toMonoidHom e.injective ⊤ a
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at hc
  rw [show e.toMonoidHom a = e a from rfl] at hc
  rw [← hc]
  exact Subgroup.card_map_of_injective e.injective

theorem InvertedByTwoA.map {G' : Type} [Group G'] (e : G ≃* G') {s : G} (h : InvertedByTwoA s) :
    InvertedByTwoA (e s) := by
  obtain ⟨α, hα, hc, hi⟩ := h
  refine ⟨e α, by rw [MulEquiv.orderOf_eq]; exact hα, ?_, ?_⟩
  · rw [natCard_centralizer_mulEquiv]
    exact hc
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, hi]

theorem gLAPPrimeCoreOf_centralizer_eq_bot_of_mulEquiv {K K' : Type*} [Group K] [Group K']
    (e : K ≃* K') {p : ℕ} {s : K}
    (h : GLAPPrimeCoreOf p (Subgroup.centralizer ({e s} : Set K')) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K)) = ⊥ := by
  have hmap := map_glaPPrimeCoreOf_of_injective p e.toMonoidHom e.injective
    (Subgroup.centralizer ({s} : Set K))
  have hc := map_inf_centralizer_of_injective e.toMonoidHom e.injective ⊤ s
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at hc
  rw [hc] at hmap
  have h'' : (GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K))).map e.toMonoidHom = ⊥ := by
    rw [hmap]
    exact h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h''

theorem UninvertedOPrimeTrivial.of_mulEquiv {G' : Type} [Group G'] (e : G ≃* G') {p : ℕ}
    (h : UninvertedOPrimeTrivial p G') : UninvertedOPrimeTrivial p G := by
  intro s hs hn
  refine gLAPPrimeCoreOf_centralizer_eq_bot_of_mulEquiv e
    (h (e s) (by rw [MulEquiv.orderOf_eq]; exact hs) fun hi => hn ?_)
  have := hi.map e.symm
  rwa [MulEquiv.symm_apply_apply] at this

theorem oPrimeCoreTrivialAt_of_uninverted_mulEquiv
    {K : Type} [Group K] (hE : MonsterExistenceStatement K)
    (e : G ≃* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : UninvertedOPrimeTrivial p G) :
    OPrimeCoreTrivialAt p G :=
  OPrimeCoreTrivialAt.of_mulEquiv e
    (oPrimeCoreTrivialAt_of_uninverted hE hp hp2 (h.of_mulEquiv e.symm))


end Monster

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
