module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma44

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

@[expose] def cBarB (p : ℕ) (B L : Subgroup G) : Subgroup G :=
  B ⊓ centralizerQuot L (GLAPPrimeCoreOf p L)

theorem card_sup_eq_mul_of_commute {A F : Subgroup G} (hc : ∀ a ∈ A, ∀ f ∈ F, a * f = f * a)
    (hd : A ⊓ F = ⊥) : Nat.card ↥(A ⊔ F) = Nat.card A * Nat.card F := by
  have hcomm : ∀ (m : A) (n : F), Commute (A.subtype m) (F.subtype n) := fun m n => hc m m.2 n n.2
  have hdisj : Disjoint A F := disjoint_iff.2 hd
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype F.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨A.subtype_injective, F.subtype_injective, by simpa using hdisj⟩
  have hrange : (MonoidHom.noncommCoprod A.subtype F.subtype hcomm).range = A ⊔ F := by
    rw [MonoidHom.noncommCoprod_range]; simp
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

variable [Finite G]

@[expose] def Lemma43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p → p = 5 →
    ∀ B : Subgroup G, IsBOneMax p B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer ({b} : Set G)) L → IsFiTwentyTwo (barOf 5 L) →
      (cBarB 5 B L ⊔ B ⊓ L = B ∧ cBarB 5 B L ⊓ (B ⊓ L) = ⊥ ∧ IsPPlane 5 (B ⊓ L) ∧
        Nat.card ↥(B ⊓ L) = 5 ^ (Nat.card L).factorization 5) ∧
      (∀ a ∈ cBarB 5 B L, a ≠ 1 →
        GLAPComponent 5 (Subgroup.centralizer ({a} : Set G))
          (⨆ g ∈ GLAPLayer 5 (Subgroup.centralizer ({a} : Set G)),
            GLBConj g (GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)))) ∧
        (⨆ g ∈ GLAPLayer 5 (Subgroup.centralizer ({a} : Set G)),
          GLBConj g (GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)))) ≤
          GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)) ⊔
            GLAPPrimeCoreOf 5 (⨆ g ∈ GLAPLayer 5 (Subgroup.centralizer ({a} : Set G)),
              GLBConj g (GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G))))) ∧
      (∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧
        GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)) ≤
          N ⊓ GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)) ⊔
            GLAPPrimeCoreOf 5 (GLAPLayer 5 (L ⊓ Subgroup.centralizer (cBarB 5 B L : Set G)))) ∧
      (∃ D : Subgroup G, D ≤ cBarB 5 B L ∧ (D.subgroupOf (cBarB 5 B L)).index = 5 ∧
        Even (Nat.card (⁅B, GLADelta 5 D⁆ : Subgroup G)))

@[expose] def CaseTwoFiveEvenGe5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p → p = 5 → 5 ≤ m →
    ¬ GLCaseOne G p → ∀ B : Subgroup G, IsBOneMax p B →
      ∃ D : Subgroup G, IsEkIn p 2 B D ∧ Even (Nat.card (⁅GLADelta p D, B⁆ : Subgroup G))

omit [Finite G] in
theorem glaDelta_le_glaDelta_of_le {p : ℕ} {D D' : Subgroup G} (h : D' ≤ D) :
    GLADelta p D ≤ GLADelta p D' := by
  intro y hy
  simp only [GLADelta, Subgroup.mem_iInf] at hy ⊢
  intro d hd hd1
  exact hy d (h hd) hd1

theorem caseTwoFiveEvenGe5_of_lemmas (h43 : Lemma43) (h44 : Lemma44) : CaseTwoFiveEvenGe5 := by
  intro G _ _ m p hS hp5 hm5 hnc B hB1
  subst hp5
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨b, hb, hb1, L, hL, hM⟩ := h44 G m 5 hS rfl hnc B hB1
  obtain ⟨⟨hsup, hinf, hFpl, -⟩, -, -, D, hDA, hDidx, hDev⟩ := h43 G m 5 hS rfl B hB1 b hb hb1 L hL hM
  have hBel : IsElemAbelian 5 B := hB1.1.1
  have hAB : cBarB 5 B L ≤ B := inf_le_left
  have hcardB : Nat.card B = 5 ^ m := hS.card_eq hB1
  have hAcard : Nat.card (cBarB 5 B L) = 5 ^ (m - 2) := by
    have h1 := card_sup_eq_mul_of_commute (A := cBarB 5 B L) (F := B ⊓ L)
      (fun a ha f hf => elemAbelian_comm hBel (hAB ha) ((inf_le_left : B ⊓ L ≤ B) hf)) hinf
    rw [hsup, hcardB, hFpl.2] at h1
    have h3 : (5 : ℕ) ^ m = 5 ^ (m - 2) * 5 ^ 2 := by rw [← pow_add]; congr 1; omega
    rw [h3] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  have hDcard : Nat.card D = 5 ^ (m - 3) :=
    card_eq_of_index_eq hp hDA hDidx (by rw [show m - 3 + 1 = m - 2 by omega]; exact hAcard)
  have hDel : IsElemAbelian 5 D := isElemAbelian_mono (isElemAbelian_mono hBel hAB) hDA
  obtain ⟨D', hD'D, hD'el, hD'card⟩ := exists_le_isElemAbelian_card (p := 5) hDel (n := 2)
    (by rw [hDcard]; exact pow_dvd_pow 5 (by omega))
  refine ⟨D', ⟨hD'D.trans (hDA.trans hAB), hD'el, hD'card⟩, ?_⟩
  have hle : ⁅GLADelta 5 D, B⁆ ≤ ⁅GLADelta 5 D', B⁆ :=
    Subgroup.commutator_mono (glaDelta_le_glaDelta_of_le hD'D) le_rfl
  rw [Subgroup.commutator_comm] at hDev
  exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 hDev).trans (Subgroup.card_dvd_of_le hle))

end CFSG.HardMathSupport.Solomon.LocalBalance
