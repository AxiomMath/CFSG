module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Repeat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24OneCIT
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Prop13Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.OddStandard.Children

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

@[expose] def seq2 {α : Type*} (a b : α) : ℕ → α := fun i => if i = 0 then a else b

@[expose] def seq3 {α : Type*} (a b c : α) : ℕ → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem seq2_zero {α : Type*} (a b : α) : seq2 a b 0 = a := by simp [seq2]

@[simp] theorem seq2_succ {α : Type*} (a b : α) (i : ℕ) : seq2 a b (i + 1) = b := by
  simp [seq2]

@[simp] theorem seq3_zero {α : Type*} (a b c : α) : seq3 a b c 0 = a := by simp [seq3]

@[simp] theorem seq3_one {α : Type*} (a b c : α) : seq3 a b c 1 = b := by simp [seq3]

@[simp] theorem seq3_add_two {α : Type*} (a b c : α) (i : ℕ) : seq3 a b c (i + 2) = c := by
  simp [seq3]

structure TLinks (H : Type) [Group H] (a : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H) : Prop where
  comp : ∀ i ≤ a, IsPGroup 2 (T i) ∧ IsCompIn (L i) (centralizer (T i : Set H))
  elem : ∀ i, 1 ≤ i → i ≤ a → IsPGroup 2 (zpowers (s i)) ∧ s i ∈ normalizer (T i : Set H) ∧
    s i ^ 2 ∈ T i ∧ IsCompIn (L (i - 1)) (centralizer ((T i ⊔ zpowers (s i) : Subgroup H) : Set H))
  incl : ∀ i, 1 ≤ i → i ≤ a →
    L (i - 1) ≤ L i ⊔ (L i).map (MulAut.conj (s i)).toMonoidHom ∧
      L i ⊔ (L i).map (MulAut.conj (s i)).toMonoidHom =
        conjClosure (L (i - 1)) (layerIn (centralizer (T i : Set H)))
  link : ∀ i, 1 ≤ i → i ≤ a →
    Sol78Link5a (L i) (L (i - 1)) (s i) ∨ L i = (L i).map (MulAut.conj (s i)).toMonoidHom

section TLinksLemmas

variable {H : Type} [Group H] {a b : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}

theorem TLinks.mono (h : TLinks H a L T s) (hba : b ≤ a) : TLinks H b L T s :=
  ⟨fun i hi => h.comp i (hi.trans hba), fun i h1 hi => h.elem i h1 (hi.trans hba),
    fun i h1 hi => h.incl i h1 (hi.trans hba), fun i h1 hi => h.link i h1 (hi.trans hba)⟩

theorem TLinks.shift (h : TLinks H a L T s) (j : ℕ) (hj : j ≤ a) :
    TLinks H (a - j) (fun i => L (i + j)) (fun i => T (i + j)) (fun i => s (i + j)) := by
  refine ⟨fun i hi => h.comp (i + j) (by omega), ?_, ?_, ?_⟩
  · intro i hi1 hi
    have h1 : i + j - 1 = (i - 1) + j := by omega
    have := h.elem (i + j) (by omega) (by omega)
    rw [h1] at this
    exact this
  · intro i hi1 hi
    have h1 : i + j - 1 = (i - 1) + j := by omega
    have := h.incl (i + j) (by omega) (by omega)
    rw [h1] at this
    exact this
  · intro i hi1 hi
    have h1 : i + j - 1 = (i - 1) + j := by omega
    have := h.link (i + j) (by omega) (by omega)
    rw [h1] at this
    exact this

theorem TLinks.le_of_inv (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hinv : L i = (L i).map (MulAut.conj (s i)).toMonoidHom) : L (i - 1) ≤ L i := by
  have h1 := (h.incl i hi hia).1
  rw [← hinv, sup_idem] at h1
  exact h1

theorem TLinks.cqOrd_eq_of_swap [Finite H] (_h : TLinks H a L T s) {i : ℕ} (_hi : 1 ≤ i)
    (_hia : i ≤ a) (h5a : Sol78Link5a (L i) (L (i - 1)) (s i)) :
    cqOrd (L (i - 1)) = cqOrd (L i) := by
  obtain ⟨e⟩ := h5a.2
  exact (Nat.card_congr e.toEquiv).symm

theorem TLinks.fiveALink (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hT : T i ≠ ⊥) (h5a : Sol78Link5a (L i) (L (i - 1)) (s i)) : FiveALink (L i) (L (i - 1)) := by
  obtain ⟨hTp, hLc⟩ := h.comp i hia
  obtain ⟨hsp, hsN, hs2, hLp⟩ := h.elem i hi hia
  obtain ⟨hincl, heq⟩ := h.incl i hi hia
  exact ⟨T i, s i, hT, hTp, hLc, hsp, hsN, hs2, hLp, hincl, heq, h5a.1, h5a.2⟩

section Order

variable [Finite H]

theorem TLinks.cqOrd_le_succ (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a) :
    cqOrd (L (i - 1)) ≤ cqOrd (L i) := by
  rcases h.link i hi hia with h5a | hinv
  · exact (h.cqOrd_eq_of_swap hi hia h5a).le
  · exact cqOrd_le_of_le (h.le_of_inv hi hia hinv)

theorem TLinks.cqOrd_mono (h : TLinks H a L T s) {c d : ℕ} (hcd : c ≤ d) (hd : d ≤ a) :
    cqOrd (L c) ≤ cqOrd (L d) := by
  induction d, hcd using Nat.le_induction with
  | base => exact le_rfl
  | succ d hcd ih =>
    have := h.cqOrd_le_succ (i := d + 1) (by omega) hd
    simp only [Nat.add_sub_cancel] at this
    exact (ih (by omega)).trans this

theorem TLinks.cqOrd_lt_succ_of_inv (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hinv : L i = (L i).map (MulAut.conj (s i)).toMonoidHom) (hne : L (i - 1) ≠ L i) :
    cqOrd (L (i - 1)) < cqOrd (L i) := by
  have hle := h.le_of_inv hi hia hinv
  refine lt_of_le_of_ne (cqOrd_le_of_le hle) fun heq => hne ?_
  exact eq_of_le_of_cqOrd_eq hle (h.comp (i - 1) (by omega)).2.isQuasisimple
    (h.comp i hia).2.isQuasisimple heq

theorem TLinks.link5a_of_cqOrd_eq (h : TLinks H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (heq : cqOrd (L (i - 1)) = cqOrd (L i)) (hne : L (i - 1) ≠ L i) :
    Sol78Link5a (L i) (L (i - 1)) (s i) := by
  rcases h.link i hi hia with h5a | hinv
  · exact h5a
  · exact absurd (eq_of_le_of_cqOrd_eq (h.le_of_inv hi hia hinv)
      (h.comp (i - 1) (by omega)).2.isQuasisimple (h.comp i hia).2.isQuasisimple heq) hne

end Order

end TLinksLemmas

structure InCG (G : Type) [Group G] (n : ℕ) (L T : ℕ → Subgroup G) (s : ℕ → G) : Prop where
  one_le : 1 ≤ n
  last : L n = ⊤
  inj : ∀ i ≤ n, ∀ j ≤ n, L i = L j → i = j
  links : TLinks G n L T s
  top : StdBare (L (n - 1))

section InCGLemmas

variable {G : Type} [Group G] {n : ℕ} {L T : ℕ → Subgroup G} {s : ℕ → G}

theorem center_eq_bot_of_isSimpleGroup (hG : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact absurd (mem_center_iff.mp (h ▸ mem_top a : a ∈ center G) b).symm hab

theorem eq_top_of_isCompIn_top (hG : IsSimpleGroup G) {M : Subgroup G}
    (h : IsCompIn M ⊤) : M = ⊤ := by
  have hs : M.IsSubnormal := (HSStd.Prop13.isCompIn_top_iff.1 h).2
  rcases hs.eq_bot_or_top_of_isSimpleGroup hG with hbot | htop
  · exfalso
    have hq := h.isQuasisimple
    subst hbot
    obtain ⟨-, -, a, b, hab⟩ := hq
    exact hab (Subsingleton.elim _ _)
  · exact htop

theorem InCG.T_eq_bot_last (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    (h : InCG G n L T s) : T n = ⊥ := by
  have hc := (h.links.comp n le_rfl).2
  rw [h.last] at hc
  have h1 : centralizer (T n : Set G) = ⊤ := top_le_iff.1 hc.1
  have h2 := Subgroup.centralizer_eq_top_iff_subset.1 h1
  rw [eq_bot_iff]
  intro x hx
  have := h2 hx
  rwa [center_eq_bot_of_isSimpleGroup hG hna] at this

theorem InCG.T_ne_bot (hG : IsSimpleGroup G) (_hna : ∃ a b : G, a * b ≠ b * a)
    (h : InCG G n L T s) {i : ℕ} (hi : i < n) : T i ≠ ⊥ := by
  intro hT
  have hc := (h.links.comp i hi.le).2
  rw [hT] at hc
  have h1 : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset]
    simp
  rw [h1] at hc
  have h2 := eq_top_of_isCompIn_top hG hc
  have := h.inj i hi.le n le_rfl (h2.trans h.last.symm)
  omega

theorem InCG.top_ne_top (h : InCG G n L T s) : L (n - 1) ≠ ⊤ := by
  intro hL
  have := h.inj (n - 1) (by omega) n le_rfl (hL.trans h.last.symm)
  have h1 := h.one_le
  omega

theorem InCG.top_isCompIn (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    (h : InCG G n L T s) :
    orderOf (s n) = 2 ∧ IsCompIn (L (n - 1)) (centralizer ({s n} : Set G)) := by
  obtain ⟨-, -, hs2, hc⟩ := h.links.elem n h.one_le le_rfl
  have hT := h.T_eq_bot_last hG hna
  rw [hT] at hs2 hc
  have hcen : centralizer ((((⊥ : Subgroup G) ⊔ zpowers (s n) : Subgroup G)) : Set G) =
      centralizer ({s n} : Set G) := by
    rw [bot_sup_eq]
    refine le_antisymm (Subgroup.centralizer_le (by simp)) fun x hx => ?_
    rw [mem_centralizer_iff] at hx ⊢
    rintro _ ⟨k, rfl⟩
    exact ((Commute.symm (hx (s n) rfl)).zpow_right k).symm
  rw [hcen] at hc
  have hsq : s n ^ 2 = 1 := Subgroup.mem_bot.1 hs2
  have hne : s n ≠ 1 := by
    intro h1
    rw [h1] at hc
    have h2 : centralizer (({1} : Set G)) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      simp
    rw [h2] at hc
    exact h.top_ne_top (eq_top_of_isCompIn_top hG hc)
  exact ⟨orderOf_eq_prime hsq hne, hc⟩

end InCGLemmas

@[expose] def CharThreeLie (Q : Type) [Group Q] : Prop :=
  ∃ (τ : StatedLieTag) (n f : ℕ), LieModel Q τ n 3 f

theorem charThreeLie_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    CharThreeLie Q ↔ CharThreeLie Q' :=
  ⟨fun ⟨τ, n, f, h⟩ => ⟨τ, n, f, h.of_mulEquiv e⟩,
    fun ⟨τ, n, f, h⟩ => ⟨τ, n, f, h.of_mulEquiv e.symm⟩⟩

@[expose] def NotF3Five {H : Type} [Group H] [Finite H] (X : Subgroup H) : Prop :=
  ¬ CharThreeLie (↥X ⧸ center ↥X) ∧ 5 ∣ cqOrd X

@[expose] def InCGb (G : Type) [Group G] [Finite G] (n : ℕ) (L T : ℕ → Subgroup G)
    (s : ℕ → G) : Prop :=
  InCG G n L T s ∧ NotF3Five (L 0)

section Maximal

variable {G : Type} [Group G] [Finite G]

theorem exists_inCGb_maximal {K : Subgroup G}
    (h₀ : ∃ n L T s, InCGb G n L T s ∧ L 0 = K) :
    ∃ n L T s, InCGb G n L T s ∧ L 0 = K ∧
      ∀ m L' T' s', InCGb G m L' T' s' → L' 0 = K → m ≤ n := by
  classical
  have hbound : ∀ m L' T' s', InCGb G m L' T' s' → m ≤ Nat.card (Subgroup G) := by
    intro m L' T' s' h
    have hinj : Function.Injective (fun i : Fin (m + 1) => L' i) := fun i j hij =>
      Fin.ext (h.1.inj i (by omega) j (by omega) hij)
    have := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  obtain ⟨n₀, L₀, T₀, s₀, h₀', h₀''⟩ := h₀
  let P : ℕ → Prop := fun m => ∃ L T s, InCGb G m L T s ∧ L 0 = K
  have hP₀ : P n₀ := ⟨L₀, T₀, s₀, h₀', h₀''⟩
  have hn₀ : n₀ ≤ Nat.card (Subgroup G) := hbound _ _ _ _ h₀'
  obtain ⟨L, T, s, h1, h2⟩ := Nat.findGreatest_spec (P := P) hn₀ hP₀
  exact ⟨Nat.findGreatest P (Nat.card (Subgroup G)), L, T, s, h1, h2,
    fun m L' T' s' h h0 => Nat.le_findGreatest (hbound _ _ _ _ h) ⟨L', T', s', h, h0⟩⟩

end Maximal

structure Out (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) : Prop where
  std : StdHyp G L
  m12 : IsSporadic L .M12
  mem : t ∈ centralizer (L : Set G)
  inv : orderOf t = 2
  outer : ¬ centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)

section OutLemmas

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem Out.isCompIn (hO : Out G L t) : IsCompIn L (centralizer ({t} : Set G)) :=
  HSStd.Prop13.isCompIn_centralizer_singleton hO.std.standard hO.inv hO.mem

end OutLemmas

@[expose] def TopIsM12 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ X : Subgroup G, StdHyp G X → NotF3Five X → IsSporadic X .M12

theorem stdSetting_of_stdHyp {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) : CFSG.OddStandard.StandardSetting G L :=
  ⟨h.simple, h.nonabelian, h.kProper, h.standard⟩

theorem citPart2_of_cit
    (h : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels) :
    CITPart2 :=
  fun G _ _ _ hF z hz J hzJ hJ S hS => (h G hF z hz J hzJ hJ S hS).2

theorem ci_of_cit
    (h : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels) :
    CFSG.ComponentClassification.GSLit.ClassicalInvolutionInput := h

end CFSG.EvenSporadicStandard.M12Std.Rbc
