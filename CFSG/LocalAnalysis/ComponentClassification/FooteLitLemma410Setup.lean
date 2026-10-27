module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410A
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Tools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_isSylowOf_ge_le_normalizer {p : ℕ} [Fact p.Prime] {X A B : Subgroup G}
    (hAX : A ≤ normalizer (X : Set G)) (hBX : B ≤ X) (hAB : IsPGroup p ↥(A ⊔ B)) :
    ∃ T : Subgroup G, IsSylowOf p T X ∧ B ≤ T ∧ A ≤ normalizer (T : Set G) := by
  have hYN : X ⊔ A ≤ normalizer (X : Set G) := sup_le le_normalizer hAX
  obtain ⟨S, hS, hABS⟩ := exists_isSylowOf_ge_of_le
    (sup_le (le_sup_right : A ≤ X ⊔ A) (hBX.trans le_sup_left)) hAB
  refine ⟨S ⊓ X, hS.inf_of_le_normalizer le_sup_left hYN,
    le_inf (le_sup_right.trans hABS) hBX, fun a ha => ?_⟩
  exact mem_normalizer_inf' (le_normalizer (hABS (mem_sup_left ha))) (hAX ha)

structure Foote410Config (M : Subgroup G) (g : G) (E Q : Subgroup G) (t : G) : Prop where
  hinv : ¬ ∃ x ∈ coreActionKernel M ⊓ coreActionKernel (conjugate M g), orderOf x = 2
  hMN : ¬ M ≤ normalizer (conjugate M g : Set G)
  hMN' : ¬ conjugate M g ≤ normalizer (M : Set G)
  hEC : E ≤ coreActionKernel (conjugate M g)
  hEN : E ≤ normalizer (M : Set G)
  hE2 : ∀ x ∈ E, x ^ 2 = 1
  hE8 : Nat.card E = 8
  hESyl : IsSylowOf 2 E (coreActionKernel (conjugate M g) ⊓ normalizer (M : Set G))
  hQC : Q ≤ coreActionKernel M
  hQN : Q ≤ normalizer (conjugate M g : Set G)
  hQ2 : ∀ x ∈ Q, x ^ 2 = 1
  hQ8 : Nat.card Q = 8
  hQSyl : IsSylowOf 2 Q (coreActionKernel M ⊓ normalizer (conjugate M g : Set G))
  hEQ : ∀ e ∈ E, ∀ q ∈ Q, e * q = q * e
  htQ : t ∈ Q
  ht : FooteInCC M t

theorem Foote410Config.eq_bot {M : Subgroup G} {g : G} {E Q : Subgroup G} {t : G}
    (hc : Foote410Config M g E Q t) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ coreActionKernel M ⊓ coreActionKernel (conjugate M g)) : P = ⊥ := by
  by_contra hne
  obtain ⟨x, hxP, hx, -⟩ := exists_involution_central hP hne
  exact hc.hinv ⟨x, hPC hxP, hx⟩

theorem Foote410Config.eq_one {M : Subgroup G} {g : G} {E Q : Subgroup G} {t : G}
    (hc : Foote410Config M g E Q t) {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hxP : x ∈ P)
    (hxC : x ∈ coreActionKernel M) (hxC' : x ∈ coreActionKernel (conjugate M g)) : x = 1 := by
  have h := hc.eq_bot (hP.to_le (inf_le_left : P ⊓ (coreActionKernel M ⊓
    coreActionKernel (conjugate M g)) ≤ P)) inf_le_right
  have hx : x ∈ P ⊓ (coreActionKernel M ⊓ coreActionKernel (conjugate M g)) :=
    mem_inf.mpr ⟨hxP, mem_inf.mpr ⟨hxC, hxC'⟩⟩
  rw [h] at hx
  exact (mem_bot).mp hx

theorem exists_foote410Config
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hA5 : GSThmB.AschbacherTheorem5Input) (hE8' : FooteL2FourgroupE8)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hFI : FooteFourgroupInner)
    (htype : Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ^ f = 9 ∧ Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p f)
    {M : Subgroup G} (hM : IsFooteM L M) {g : G} {E : Subgroup G}
    (hE : E ≤ coreActionKernel (conjugate M g) ⊓ normalizer (M : Set G))
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8)
    (hinv : ¬ ∃ x ∈ coreActionKernel M ⊓ coreActionKernel (conjugate M g), orderOf x = 2)
    (hMN : ¬ M ≤ normalizer (conjugate M g : Set G)) :
    ∃ Q : Subgroup G, ∃ t : G, Foote410Config M g E Q t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M' := conjugate M g with hM'def
  set C := coreActionKernel M with hCdef
  set C' := coreActionKernel M' with hC'def
  set N := normalizer (M : Set G) with hNdef
  set N' := normalizer (M' : Set G) with hN'def
  have hM' : IsFooteM L M' := isFooteM_conjugate h hM g
  have hinv' : conjugate M' g⁻¹ = M := conjugate_conjugate_inv M g
  have hEC' : E ≤ C' := hE.trans inf_le_left
  have hEN : E ≤ N := hE.trans inf_le_right
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE8]; norm_num)
  have h2 : ∀ P : Subgroup G, IsPGroup 2 P → ∀ x ∈ P, x ∈ C → x ∈ C' → x = 1 := by
    intro P hP x hxP hxC hxC'
    have hbot : P ⊓ (C ⊓ C') = ⊥ := by
      by_contra hne
      obtain ⟨y, hyP, hy, -⟩ := exists_involution_central (hP.to_le inf_le_left) hne
      exact hinv ⟨y, (mem_inf.mp hyP).2, hy⟩
    have hx : x ∈ P ⊓ (C ⊓ C') := mem_inf.mpr ⟨hxP, mem_inf.mpr ⟨hxC, hxC'⟩⟩
    rw [hbot] at hx
    exact (mem_bot).mp hx
  have hEC : ∀ x ∈ E, x ∈ C → x = 1 := fun x hx hxC => h2 E hEp x hx hxC (hEC' hx)
  obtain ⟨P, hP, hEP⟩ := exists_isSylowOf_ge_of_le hE hEp
  have hPE : P = E := by
    rcases le_normalizer_conjugate_or_eq h h47 hST hFI htype hM (hP.le.trans inf_le_left)
      (hP.le.trans inf_le_right) hP.isPGroup
      (fun x hx hxC => h2 P hP.isPGroup x hx hxC ((hP.le.trans inf_le_left) hx)) hEP hE2 hE8
      with h1 | h1
    · exact absurd h1 hMN
    · exact h1
  have hESyl : IsSylowOf 2 E (C' ⊓ N) := hPE ▸ hP
  set D := C ⊓ N' with hD
  have hED : E ≤ normalizer (D : Set G) := fun e he =>
    mem_normalizer_inf' (normalizer_le_normalizer_coreActionKernel M (hEN he))
      (le_normalizer ((hEC'.trans (fun c hc => (mem_coreActionKernel.mp hc).1)) he))
  obtain ⟨Q₁, hQ₁, -, hEQ₁⟩ := exists_isSylowOf_ge_le_normalizer hED (bot_le : ⊥ ≤ D)
    (by rw [sup_bot_eq]; exact hEp)
  have hQ₁C : Q₁ ≤ C := hQ₁.le.trans inf_le_left
  have hQ₁N' : Q₁ ≤ N' := hQ₁.le.trans inf_le_right
  have hQ₁p : IsPGroup 2 Q₁ := hQ₁.isPGroup
  have hEQ : ∀ e ∈ E, ∀ q ∈ Q₁, e * q = q * e := by
    intro e he q hq
    have hc1 : e * q * e⁻¹ * q⁻¹ ∈ Q₁ :=
      mul_mem ((mem_normalizer_iff.mp (hEQ₁ he) q).mp hq) (inv_mem hq)
    have hc2 : e * q * e⁻¹ * q⁻¹ ∈ C := by
      have : e * q * e⁻¹ ∈ C :=
        (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M (hEN he)) q).mp
          (hQ₁C hq)
      exact mul_mem this (inv_mem (hQ₁C hq))
    have hc3 : e * q * e⁻¹ * q⁻¹ ∈ C' := by
      have : q * e⁻¹ * q⁻¹ ∈ C' :=
        (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M' (hQ₁N' hq)) _).mp
          (inv_mem (hEC' he))
      rw [show e * q * e⁻¹ * q⁻¹ = e * (q * e⁻¹ * q⁻¹) by group]
      exact mul_mem (hEC' he) this
    have h1 := h2 Q₁ hQ₁p _ hc1 hc2 hc3
    calc e * q = e * q * e⁻¹ * q⁻¹ * (q * e) := by group
      _ = q * e := by rw [h1, one_mul]
  obtain ⟨E₀, hE₀, hE₀E, hE₀MC⟩ := exists_isKleinFour_le_inf_sup h hFI hM hEN hE2 hE8 hEC
  obtain ⟨F, hFC, hF2, hF8⟩ :=
    exists_card_eight_le_inf_centralizer_of_isKleinFour h h47 hST hM hE₀ hE₀MC
  have hFD : F ≤ D := fun f hf => mem_inf.mpr ⟨(mem_inf.mp (hFC hf)).1,
    foote_cor_4_8_iv h h47 hST hM' (hE₀E.trans hEC') hE₀ le_rfl
      (centralizer_le_normalizer _ (mem_inf.mp (hFC hf)).2)⟩
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hQ₁ hFD hFp
  have hF'Q : conjugate F k ≤ Q₁ := conjugate_le_of_forall hk
  have hF'2 := sq_eq_one_of_mem_conjugate hF2 k
  have hF'8 : Nat.card (conjugate F k) = 8 := by rw [card_conjugate_eq_card, hF8]
  have hM'N : ¬ M' ≤ N := by
    intro hle
    obtain ⟨w, hwE, hw1, -⟩ := exists_ne_of_isKleinFour hE₀ 1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (hE2 w (hE₀E hwE)) hw1
    have heq := eq_conjugate_of_le_normalizer h h47 hST hA5 hE8' hK hcalc hM' (g := g⁻¹)
      (by rw [hinv']; exact hle) hw2 (hEC' (hE₀E hwE)) (by rw [hinv']; exact hEN (hE₀E hwE))
    rw [hinv'] at heq
    have hwC : w ∈ C := by
      rw [hCdef, ← heq]
      exact hEC' (hE₀E hwE)
    exact hw1 (hEC w (hE₀E hwE) hwC)
  have hQ₁F : Q₁ = conjugate F k := by
    rcases le_normalizer_conjugate_or_eq h h47 hST hFI htype hM' (g := g⁻¹) (P := Q₁)
      (by rw [hinv']; exact hQ₁C) hQ₁N' hQ₁p
      (fun x hx hxC' => h2 Q₁ hQ₁p x hx (hQ₁C hx) hxC') hF'Q hF'2 hF'8 with h1 | h1
    · rw [hinv'] at h1
      exact absurd h1 hM'N
    · exact h1
  have hQ₁2 : ∀ x ∈ Q₁, x ^ 2 = 1 := fun x hx => hF'2 x (hQ₁F ▸ hx)
  have hQ₁8 : Nat.card Q₁ = 8 := by rw [hQ₁F, hF'8]
  obtain ⟨t, htQ, ht2, htN⟩ : ∃ t ∈ Q₁, orderOf t = 2 ∧
      ¬ centralizer ({t} : Set G) ≤ N := by
    by_contra hno
    push Not at hno
    exact hM'N (le_of_forall_centralizer_le_e8 h hK hM' hQ₁N' hQ₁2 hQ₁8 hno)
  exact ⟨Q₁, t, ⟨hinv, hMN, hM'N, hEC', hEN, hE2, hE8, hESyl, hQ₁C, hQ₁N', hQ₁2, hQ₁8, hQ₁,
    hEQ, htQ, ⟨ht2, hQ₁C htQ, htN⟩⟩⟩

end CFSG.ComponentClassification.FooteLit
