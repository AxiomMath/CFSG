module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16FourPlane
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Kernel
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Outer
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Four

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Commutator

variable {A : Type} [Group A] [Finite A]

theorem inf_center_le_commutator (c : L34Cover A) (hA : commutator A = ⊤) (T : Sylow 2 A)
    {M : Subgroup A} (hMT : M ≤ T) (hM : IsElemAbelian 2 M)
    (hcard : Nat.card M = 16 * Nat.card c.π.ker) :
    (T : Subgroup A) ⊓ center A ≤ ⁅(T : Subgroup A), M⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set p := QuotientGroup.mk' N with hpdef
  obtain ⟨π', hsurj', hker', hTb⟩ := exists_std_cover c T
  have hCZ' : π'.ker ≤ center (A ⧸ N) := hker' ▸ c.ker_le_center
  have helem' : CFSG.IsElementaryAbelian 2 π'.ker := hker' ▸ c.elem
  obtain ⟨hH, -, -, -, -, hcenter, -, hlevi⟩ :=
    field_four_central_two_cover_parabolic_normalizers c.card_k π' hsurj' hCZ' helem'
  obtain ⟨⟨σ₀, -, -, hσ₀, -⟩, -⟩ := hlevi 0
  obtain ⟨⟨-, -, -, -, -, -, hEA, -, -, -, -⟩, -, hperf⟩ :=
    field_four_central_cover_exact_Sylow_geometry c.card_k π' hsurj' hCZ' helem' σ₀ hσ₀
  have : Group.IsPerfect A := (Group.isPerfect_def).2 hA
  obtain ⟨h0, h1, h2, h3, -⟩ := hperf inferInstance
  set TX := (projUnip c.k).comap π' with hTX
  have hpM : IsElemAbelian 2 (M.map p) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      exact congrArg p (congrArg Subtype.val (hM.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hM.2 x hx, map_one]
  have hpM' : CFSG.IsElementaryAbelian 2 ↥(M.map p) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr hpM
  have hpMT : M.map p ≤ TX := hTb ▸ map_mono hMT
  have hcardM : Nat.card (M.map p) = Nat.card M := card_map_mk'_of_le T.2 hN hMT
  have hcomm : ⁅TX, M.map p⁆ = ⁅TX, TX⁆ := by
    have key : ∀ j : Fin 2, M.map p ≤ (projRad c.k j).comap π' →
        M.map p = (projRad c.k j).comap π' := fun j hj =>
      Subgroup.eq_of_le_of_card_ge hj (by rw [hcardM, hcard, (hH j).2, hker'])
    rcases hEA _ hpMT hpM' with h | h
    · rw [key 0 h, h0]
    · rw [key 1 h, h1]
  have hkerC : π'.ker ≤ ⁅TX, TX⁆ := by
    rw [h2, h3, hcenter]
    exact fun x hx => show π' x ∈ projCenterW c.k by rw [hx]; exact one_mem _
  rintro z ⟨hzT, hzZ⟩
  have hpz : p z ∈ ⁅TX, M.map p⁆ := by
    rw [hcomm]
    refine hkerC ?_
    rw [hker', c.ker_eq]
    exact ⟨z, hzZ, rfl⟩
  rw [hTb, ← map_commutator] at hpz
  obtain ⟨w, hw, hwz⟩ := hpz
  have hwT : w ∈ (T : Subgroup A) :=
    Subgroup.commutator_le.mpr (fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha (hMT hb)) (inv_mem ha)) (inv_mem (hMT hb))) hw
  rw [← mk'_injOn T.2 hN hwT hzT hwz]
  exact hw

end Commutator

section Closure

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {Pts : Set (Subgroup G)}

theorem exists_subgroup_offPoints (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE64 : Nat.card E = 64) (hle : ∀ Q ∈ Pts, Q ≤ E) (hcard : ∀ Q ∈ Pts, Nat.card Q = 4)
    (hdisj : ∀ Q₁ ∈ Pts, ∀ Q₂ ∈ Pts, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥) (h16 : Pts.ncard = 16)
    (hline : ∀ a ∈ Pts, ∀ b ∈ Pts, a ≠ b → {Q | Q ∈ Pts ∧ Q ≤ a ⊔ b}.ncard = 4)
    (hmeet : ∀ a ∈ Pts, ∀ b ∈ Pts, a ≠ b → ∀ P ∈ Pts, P ⊓ (a ⊔ b) ≠ ⊥ → P ≤ a ⊔ b)
    (hpar : ∀ a ∈ Pts, ∀ b ∈ Pts, a ≠ b → ∀ Q ∈ Pts, ¬ Q ≤ a ⊔ b →
      ∃ c ∈ Pts, ∃ d ∈ Pts, c ≠ d ∧ Q ≤ c ⊔ d ∧ ∀ P ∈ Pts, P ≤ a ⊔ b → ¬ P ≤ c ⊔ d) :
    ∃ K : Subgroup G, Nat.card K = 16 ∧ ∀ e : G, e ∈ K ↔ e ∈ E ∧ ∀ Q ∈ Pts, e ∈ Q → e = 1 := by
  classical
  set K : Set G := {e | e ∈ E ∧ ∀ Q ∈ Pts, e ∈ Q → e = 1} with hKdef
  have hKE : K ⊆ E := fun e he => he.1
  have hQK : ∀ Q ∈ Pts, ∀ e ∈ K, e ∈ Q → e = 1 := fun Q hQ e he heQ => he.2 Q hQ heQ
  have hQ3 : ∀ Q ∈ Pts, ((Q : Set G) \ {1}).ncard = 3 := fun Q hQ => by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem Q), ← Nat.card_coe_set_eq]
    change Nat.card Q - 1 = 3
    rw [hcard Q hQ]
  have hsupE : ∀ a ∈ Pts, ∀ b ∈ Pts, a ⊔ b ≤ E := fun a ha b hb => sup_le (hle a ha) (hle b hb)
  have hsup16 : ∀ a ∈ Pts, ∀ b ∈ Pts, a ≠ b → Nat.card ↥(a ⊔ b) = 16 := fun a ha b hb hab => by
    rw [card_sup_of_inf_eq_bot hE (hle a ha) (hle b hb) (hdisj a ha b hb hab), hcard a ha,
      hcard b hb]
  have hK16 : K.ncard = 16 := by
    have h := ncard_eq_ncard_mul_of_partition (X := (E : Set G) \ K) (I := Pts)
      (B := fun Q => (Q : Set G) \ {1}) (m := 3)
      (fun Q hQ x hx => ⟨hle Q hQ hx.1, fun hxK => hx.2 (hQK Q hQ x hxK hx.1)⟩)
      (fun x hx => by
        have h1 : ¬ ∀ Q ∈ Pts, x ∈ Q → x = 1 := fun h => hx.2 ⟨hx.1, h⟩
        push Not at h1
        obtain ⟨Q, hQ, hxQ, hx1⟩ := h1
        exact ⟨Q, hQ, hxQ, hx1⟩)
      (fun Q₁ hQ₁ Q₂ hQ₂ hne => Set.disjoint_left.mpr fun x hx₁ hx₂ => by
        have h1 : x ∈ Q₁ ⊓ Q₂ := ⟨hx₁.1, hx₂.1⟩
        rw [hdisj Q₁ hQ₁ Q₂ hQ₂ hne, mem_bot] at h1
        exact hx₁.2 h1)
      hQ3
    rw [Set.ncard_sdiff hKE, h16, ← Nat.card_coe_set_eq (E : Set G)] at h
    change Nat.card E - K.ncard = _ at h
    rw [hE64] at h
    have hle64 : K.ncard ≤ 64 := by
      have := Set.ncard_le_ncard hKE
      rw [← Nat.card_coe_set_eq (E : Set G)] at this
      exact le_trans this hE64.le
    omega
  have hKline : ∀ a ∈ Pts, ∀ b ∈ Pts, a ≠ b → ((↑(a ⊔ b) : Set G) ∩ K).ncard = 4 := by
    intro a ha b hb hab
    have h := ncard_eq_ncard_mul_of_partition (X := (↑(a ⊔ b) : Set G) \ K)
      (I := {Q | Q ∈ Pts ∧ Q ≤ a ⊔ b}) (B := fun Q => (Q : Set G) \ {1}) (m := 3)
      (fun Q hQ x hx => ⟨hQ.2 hx.1, fun hxK => hx.2 (hQK Q hQ.1 x hxK hx.1)⟩)
      (fun x hx => by
        have h1 : ¬ ∀ Q ∈ Pts, x ∈ Q → x = 1 := fun h => hx.2 ⟨hsupE a ha b hb hx.1, h⟩
        push Not at h1
        obtain ⟨Q, hQ, hxQ, hx1⟩ := h1
        refine ⟨Q, ⟨hQ, hmeet a ha b hb hab Q hQ fun h0 => hx1 ?_⟩, hxQ, hx1⟩
        have : x ∈ Q ⊓ (a ⊔ b) := ⟨hxQ, hx.1⟩
        rwa [h0, mem_bot] at this)
      (fun Q₁ hQ₁ Q₂ hQ₂ hne => Set.disjoint_left.mpr fun x hx₁ hx₂ => by
        have h1 : x ∈ Q₁ ⊓ Q₂ := ⟨hx₁.1, hx₂.1⟩
        rw [hdisj Q₁ hQ₁.1 Q₂ hQ₂.1 hne, mem_bot] at h1
        exact hx₁.2 h1)
      (fun Q hQ => hQ3 Q hQ.1)
    rw [hline a ha b hb hab] at h
    have h2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (↑(a ⊔ b) : Set G) K
    rw [h, ← Nat.card_coe_set_eq (↑(a ⊔ b) : Set G)] at h2
    change _ + 4 * 3 = Nat.card ↥(a ⊔ b) at h2
    rw [hsup16 a ha b hb hab] at h2
    omega
  have hparK : ∀ a ∈ Pts, ∀ b ∈ Pts, ∀ c ∈ Pts, ∀ d ∈ Pts, a ≠ b → c ≠ d →
      (∀ P ∈ Pts, P ≤ a ⊔ b → ¬ P ≤ c ⊔ d) →
      ((↑((a ⊔ b) ⊓ (c ⊔ d)) : Set G) = ↑(a ⊔ b) ∩ K) ∧
        ((↑((a ⊔ b) ⊓ (c ⊔ d)) : Set G) = ↑(c ⊔ d) ∩ K) := by
    intro a ha b hb c hc d hd hab hcd hdis
    have hsubK : ∀ x ∈ (a ⊔ b) ⊓ (c ⊔ d), x ∈ K := by
      intro x hx
      refine ⟨hsupE a ha b hb hx.1, fun Q hQ hxQ => ?_⟩
      by_contra hx1
      have hne : ∀ {W : Subgroup G}, x ∈ W → Q ⊓ W ≠ ⊥ := fun hxW h0 => by
        have : x ∈ Q ⊓ _ := ⟨hxQ, hxW⟩
        rw [h0, mem_bot] at this
        exact hx1 this
      exact hdis Q hQ (hmeet a ha b hb hab Q hQ (hne hx.1)) (hmeet c hc d hd hcd Q hQ (hne hx.2))
    have hN : c ⊔ d ≤ normalizer ((a ⊔ b : Subgroup G) : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
        hE z (hsupE a ha b hb hz) y (hsupE c hc d hd hy))
    have hcard4 : 4 ≤ Nat.card ↥((a ⊔ b) ⊓ (c ⊔ d)) := by
      have h := card_sup_mul_card_inf hN
      rw [hsup16 a ha b hb hab, hsup16 c hc d hd hcd] at h
      have h1 : Nat.card ↥(a ⊔ b ⊔ (c ⊔ d)) ≤ 64 :=
        hE64 ▸ Subgroup.card_le_of_le (sup_le (hsupE a ha b hb) (hsupE c hc d hd))
      by_contra h2
      push Not at h2
      have : Nat.card ↥(a ⊔ b ⊔ (c ⊔ d)) * Nat.card ↥((a ⊔ b) ⊓ (c ⊔ d)) < 256 :=
        calc _ < 64 * 4 := Nat.mul_lt_mul_of_le_of_lt h1 h2 (by norm_num)
          _ = 256 := by norm_num
      omega
    have key : ∀ {W : Subgroup G}, (a ⊔ b) ⊓ (c ⊔ d) ≤ W → (↑W ∩ K).ncard = 4 →
        (↑((a ⊔ b) ⊓ (c ⊔ d)) : Set G) = ↑W ∩ K := by
      intro W hW hW4
      refine Set.eq_of_subset_of_ncard_le (fun x hx => ⟨hW hx, hsubK x hx⟩) ?_ (Set.toFinite _)
      rw [hW4, ← Nat.card_coe_set_eq]
      exact hcard4
    exact ⟨key inf_le_left (hKline a ha b hb hab), key inf_le_right (hKline c hc d hd hcd)⟩
  have hmeetQ : ∀ a ∈ Pts, ∀ b ∈ Pts, ∀ c ∈ Pts, ∀ d ∈ Pts, a ≠ b → c ≠ d →
      ∀ Q ∈ Pts, Q ≤ a ⊔ b → Q ≤ c ⊔ d → a ⊔ b ≠ c ⊔ d → (a ⊔ b) ⊓ (c ⊔ d) = Q := by
    intro a ha b hb c hc d hd hab hcd Q hQ hQ₁ hQ₂ hne
    have hsub : (↑((a ⊔ b) ⊓ (c ⊔ d)) : Set G) ⊆ ↑Q ∪ (↑(a ⊔ b) ∩ K) := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inr ⟨hx.1, hxK⟩
      · left
        have h1 : ¬ ∀ P ∈ Pts, x ∈ P → x = 1 := fun h => hxK ⟨hsupE a ha b hb hx.1, h⟩
        push Not at h1
        obtain ⟨P, hP, hxP, hx1⟩ := h1
        have hne' : ∀ {W : Subgroup G}, x ∈ W → P ⊓ W ≠ ⊥ := fun hxW h0 => by
          have : x ∈ P ⊓ _ := ⟨hxP, hxW⟩
          rw [h0, mem_bot] at this
          exact hx1 this
        have hP₁ := hmeet a ha b hb hab P hP (hne' hx.1)
        have hP₂ := hmeet c hc d hd hcd P hP (hne' hx.2)
        by_cases hPQ : P = Q
        · exact hPQ ▸ hxP
        · exfalso
          apply hne
          have hle₁ : P ⊔ Q ≤ a ⊔ b := sup_le hP₁ hQ₁
          have hle₂ : P ⊔ Q ≤ c ⊔ d := sup_le hP₂ hQ₂
          have e₁ := Subgroup.eq_of_le_of_card_ge hle₁
            (by rw [hsup16 a ha b hb hab, hsup16 P hP Q hQ hPQ])
          have e₂ := Subgroup.eq_of_le_of_card_ge hle₂
            (by rw [hsup16 c hc d hd hcd, hsup16 P hP Q hQ hPQ])
          rw [← e₁, e₂]
    have hQK : (↑Q : Set G) ∩ (↑(a ⊔ b) ∩ K) = {1} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, SetLike.mem_coe]
      constructor
      · rintro ⟨hxQ, -, hxK⟩
        exact hQK Q hQ x hxK hxQ
      · rintro rfl
        exact ⟨one_mem _, one_mem _, one_mem _, fun _ _ _ => rfl⟩
    have hcardU : ((↑Q : Set G) ∪ (↑(a ⊔ b) ∩ K)).ncard ≤ 7 := by
      have h := Set.ncard_union_add_ncard_inter (↑Q : Set G) (↑(a ⊔ b) ∩ K)
      rw [hQK, Set.ncard_singleton, hKline a ha b hb hab, ← Nat.card_coe_set_eq (↑Q : Set G)] at h
      change _ + 1 = Nat.card Q + 4 at h
      rw [hcard Q hQ] at h
      omega
    have hle8 : Nat.card ↥((a ⊔ b) ⊓ (c ⊔ d)) ≤ 7 := by
      change Nat.card ↑((↑((a ⊔ b) ⊓ (c ⊔ d)) : Set G)) ≤ 7
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hcardU
    have hdvd : Nat.card ↥((a ⊔ b) ⊓ (c ⊔ d)) ∣ 16 := by
      rw [← hsup16 a ha b hb hab]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hQle : Q ≤ (a ⊔ b) ⊓ (c ⊔ d) := le_inf hQ₁ hQ₂
    have h4 : 4 ≤ Nat.card ↥((a ⊔ b) ⊓ (c ⊔ d)) := hcard Q hQ ▸ Subgroup.card_le_of_le hQle
    have hc4 : Nat.card ↥((a ⊔ b) ⊓ (c ⊔ d)) = 4 := by
      have : Nat.card ↥((a ⊔ b) ⊓ (c ⊔ d)) ∈ Nat.divisors 16 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    exact (Subgroup.eq_of_le_of_card_ge hQle (by rw [hc4, hcard Q hQ])).symm
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ ∈ Pts := Set.nonempty_of_ncard_ne_zero (by omega)
  have hexoff : ∀ a ∈ Pts, ∀ b ∈ Pts, a ≠ b → ∃ Q ∈ Pts, ¬ Q ≤ a ⊔ b := by
    intro a ha b hb hab
    by_contra h
    push Not at h
    have hsub : Pts ⊆ {Q | Q ∈ Pts ∧ Q ≤ a ⊔ b} := fun Q hQ => ⟨hQ, h Q hQ⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h16, hline a ha b hb hab] at this
    omega
  obtain ⟨p₁, hp₁, hp₁R⟩ : ∃ p₁ ∈ Pts, p₁ ≠ R₀ := by
    by_contra h
    push Not at h
    have hsub : Pts ⊆ {R₀} := fun Q hQ => h Q hQ
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h16, Set.ncard_singleton] at this
    omega
  obtain ⟨p₂, hp₂, hp₂W⟩ := hexoff R₀ hR₀ p₁ hp₁ hp₁R.symm
  have hp₂R : p₂ ≠ R₀ := fun h => hp₂W (h ▸ le_sup_left)
  have hW₁₂ : R₀ ⊔ p₁ ≠ R₀ ⊔ p₂ := fun h => hp₂W (h ▸ le_sup_right)
  have hZ : ∀ p ∈ Pts, p ≠ R₀ → ∃ Z : Subgroup G, (↑Z : Set G) = ↑(R₀ ⊔ p) ∩ K := by
    intro p hp hpR
    obtain ⟨Q, hQ, hQW⟩ := hexoff R₀ hR₀ p hp hpR.symm
    obtain ⟨c, hc, d, hd, hcd, -, hdis⟩ := hpar R₀ hR₀ p hp hpR.symm Q hQ hQW
    exact ⟨(R₀ ⊔ p) ⊓ (c ⊔ d), (hparK R₀ hR₀ p hp c hc d hd hpR.symm hcd hdis).1⟩
  obtain ⟨Z₁, hZ₁⟩ := hZ p₁ hp₁ hp₁R
  obtain ⟨Z₂, hZ₂⟩ := hZ p₂ hp₂ hp₂R
  have hZ₁K : ∀ x ∈ Z₁, x ∈ K := fun x hx => (hZ₁ ▸ hx : x ∈ (↑(R₀ ⊔ p₁) : Set G) ∩ K).2
  have hZ₂K : ∀ x ∈ Z₂, x ∈ K := fun x hx => (hZ₂ ▸ hx : x ∈ (↑(R₀ ⊔ p₂) : Set G) ∩ K).2
  have hZ₁E : Z₁ ≤ E := fun x hx => (hZ₁K x hx).1
  have hZ₂E : Z₂ ≤ E := fun x hx => (hZ₂K x hx).1
  have hZcard : ∀ {Z : Subgroup G} {p : Subgroup G}, p ∈ Pts → p ≠ R₀ →
      (↑Z : Set G) = ↑(R₀ ⊔ p) ∩ K → Nat.card Z = 4 := by
    intro Z p hp hpR hZ'
    change Nat.card ↑((↑Z : Set G)) = 4
    rw [Nat.card_coe_set_eq, hZ', hKline R₀ hR₀ _ hp hpR.symm]
  have hZ₁4 := hZcard hp₁ hp₁R hZ₁
  have hZ₂4 := hZcard hp₂ hp₂R hZ₂
  have hZ₁₂ : Z₁ ⊓ Z₂ = ⊥ := by
    have hmeet₀ := hmeetQ R₀ hR₀ p₁ hp₁ R₀ hR₀ p₂ hp₂ hp₁R.symm hp₂R.symm R₀ hR₀ le_sup_left
      le_sup_left hW₁₂
    rw [eq_bot_iff]
    intro x hx
    have hx₁ : x ∈ (↑(R₀ ⊔ p₁) : Set G) ∩ K := hZ₁ ▸ hx.1
    have hx₂ : x ∈ (↑(R₀ ⊔ p₂) : Set G) ∩ K := hZ₂ ▸ hx.2
    have hxR : x ∈ R₀ := hmeet₀ ▸ (⟨hx₁.1, hx₂.1⟩ : x ∈ (R₀ ⊔ p₁) ⊓ (R₀ ⊔ p₂))
    exact hQK R₀ hR₀ x hx₁.2 hxR
  have hZ16 : Nat.card ↥(Z₁ ⊔ Z₂) = 16 := by
    rw [card_sup_of_inf_eq_bot hE hZ₁E hZ₂E hZ₁₂, hZ₁4, hZ₂4]
  have hthrough : ∀ {p : Subgroup G} {Z : Subgroup G}, p ∈ Pts → p ≠ R₀ →
      (↑Z : Set G) = ↑(R₀ ⊔ p) ∩ K → ∀ Q ∈ Pts, ∃ c ∈ Pts, ∃ d ∈ Pts, c ≠ d ∧ Q ≤ c ⊔ d ∧
        (↑(c ⊔ d) : Set G) ∩ K = ↑Z := by
    intro p Z hp hpR hZ' Q hQ
    by_cases hQW : Q ≤ R₀ ⊔ p
    · exact ⟨R₀, hR₀, p, hp, hpR.symm, hQW, hZ'.symm⟩
    · obtain ⟨c, hc, d, hd, hcd, hQcd, hdis⟩ := hpar R₀ hR₀ p hp hpR.symm Q hQ hQW
      have h := hparK R₀ hR₀ p hp c hc d hd hpR.symm hcd hdis
      exact ⟨c, hc, d, hd, hcd, hQcd, by rw [← h.2, h.1, hZ']⟩
  have hQZ : ∀ Q ∈ Pts, Q ⊓ (Z₁ ⊔ Z₂) = ⊥ := by
    intro Q hQ
    obtain ⟨c₁, hc₁, d₁, hd₁, hcd₁, hQ₁, hK₁⟩ := hthrough hp₁ hp₁R hZ₁ Q hQ
    obtain ⟨c₂, hc₂, d₂, hd₂, hcd₂, hQ₂, hK₂⟩ := hthrough hp₂ hp₂R hZ₂ Q hQ
    have hQZi : ∀ {Z : Subgroup G}, (∀ x ∈ Z, x ∈ K) → Q ⊓ Z = ⊥ := fun hZK => by
      rw [eq_bot_iff]
      intro x hx
      exact hQK Q hQ x (hZK x hx.2) hx.1
    have hline_eq : ∀ {c d Z : Subgroup G}, c ∈ Pts → d ∈ Pts → c ≠ d → Q ≤ c ⊔ d →
        (↑(c ⊔ d) : Set G) ∩ K = ↑Z → Z ≤ E → (∀ x ∈ Z, x ∈ K) → Nat.card Z = 4 →
        Q ⊔ Z = c ⊔ d := by
      intro c d Z hc hd hcd hQcd hK' hZE hZK hZ4
      have hZle : Z ≤ c ⊔ d := fun x hx => by
        have : x ∈ (↑(c ⊔ d) : Set G) ∩ K := hK' ▸ hx
        exact this.1
      refine Subgroup.eq_of_le_of_card_ge (sup_le hQcd hZle) ?_
      rw [hsup16 c hc d hd hcd, card_sup_of_inf_eq_bot hE (hle Q hQ) hZE (hQZi hZK), hcard Q hQ,
        hZ4]
    have e₁ := hline_eq hc₁ hd₁ hcd₁ hQ₁ hK₁ hZ₁E hZ₁K hZ₁4
    have e₂ := hline_eq hc₂ hd₂ hcd₂ hQ₂ hK₂ hZ₂E hZ₂K hZ₂4
    have hne : c₁ ⊔ d₁ ≠ c₂ ⊔ d₂ := by
      intro h
      have hZeq : (↑Z₁ : Set G) = ↑Z₂ := by rw [← hK₁, ← hK₂, h]
      have h1 : Z₁ = Z₂ := SetLike.coe_injective hZeq
      rw [h1, inf_idem] at hZ₁₂
      rw [hZ₁₂, Subgroup.card_bot] at hZ₂4
      omega
    have hint := hmeetQ c₁ hc₁ d₁ hd₁ c₂ hc₂ d₂ hd₂ hcd₁ hcd₂ Q hQ hQ₁ hQ₂ hne
    have hN : c₂ ⊔ d₂ ≤ normalizer ((c₁ ⊔ d₁ : Subgroup G) : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
        hE z (hsupE c₁ hc₁ d₁ hd₁ hz) y (hsupE c₂ hc₂ d₂ hd₂ hy))
    have h64 : Nat.card ↥((c₁ ⊔ d₁) ⊔ (c₂ ⊔ d₂)) = 64 := by
      have h := card_sup_mul_card_inf hN
      rw [hint, hsup16 c₁ hc₁ d₁ hd₁ hcd₁, hsup16 c₂ hc₂ d₂ hd₂ hcd₂, hcard Q hQ] at h
      omega
    have hsup : Q ⊔ (Z₁ ⊔ Z₂) = (c₁ ⊔ d₁) ⊔ (c₂ ⊔ d₂) := by
      rw [← e₁, ← e₂]
      apply le_antisymm
      · exact sup_le (le_sup_left.trans le_sup_left)
          (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))
      · exact sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
          (sup_le le_sup_left (le_sup_right.trans le_sup_right))
    have hN' : Z₁ ⊔ Z₂ ≤ normalizer (Q : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
        hE z (hle Q hQ hz) y (sup_le hZ₁E hZ₂E hy))
    have h := card_sup_mul_card_inf hN'
    rw [hsup, h64, hcard Q hQ, hZ16] at h
    have h1 : Nat.card ↥(Q ⊓ (Z₁ ⊔ Z₂)) = 1 := by omega
    exact Subgroup.card_eq_one.mp h1
  refine ⟨Z₁ ⊔ Z₂, hZ16, fun e => ⟨fun he => ⟨sup_le hZ₁E hZ₂E he, fun Q hQ heQ => ?_⟩,
    fun he => ?_⟩⟩
  · have : e ∈ Q ⊓ (Z₁ ⊔ Z₂) := ⟨heQ, he⟩
    rwa [hQZ Q hQ, mem_bot] at this
  · have hsub : (↑(Z₁ ⊔ Z₂) : Set G) ⊆ K := fun x hx =>
      ⟨sup_le hZ₁E hZ₂E hx, fun Q hQ hxQ => by
        have : x ∈ Q ⊓ (Z₁ ⊔ Z₂) := ⟨hxQ, hx⟩
        rwa [hQZ Q hQ, mem_bot] at this⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [hK16, ← Nat.card_coe_set_eq]
      change 16 ≤ Nat.card ↥(Z₁ ⊔ Z₂)
      rw [hZ16]) (Set.toFinite _)
    have : e ∈ K := he
    rw [← heq] at this
    exact this

end Closure

section Frame

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem le_sup_of_inf_ne_bot {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) {P Q : Subgroup G}
    (hP : P ∈ pointsIn R E) (hQ : Q ∈ pointsIn R E) (hQR : Q ≠ R) (hPQ : P ⊓ (R ⊔ Q) ≠ ⊥) :
    P ≤ R ⊔ Q := by
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hPR : P = R
  · rw [hPR]
    exact le_sup_left
  obtain ⟨a, ha, haQ⟩ := exists_line_of_mem_pointsIn hE16 h11 hF hL hQ hQR
  obtain ⟨b, hb, hbP⟩ := exists_line_of_mem_pointsIn hE16 h11 hF hL hP hPR
  by_cases hab : rightConjugate (E ⊓ F) a = rightConjugate (E ⊓ F) b
  · rw [← haQ, hab, hbP]
    exact le_sup_right
  · exfalso
    apply hPQ
    have hle := inf_rightConjugate_le h11 hF hL ha hb hab
    rw [haQ, hbP] at hle
    have h1 : P ⊓ (R ⊔ Q) ≤ R ⊓ P := fun x hx => ⟨hle ⟨hx.2, mem_sup_right hx.1⟩, hx.1⟩
    rw [inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hcommE (self_mem_pointsIn hF.R_le_E) hP
      (Ne.symm hPR)] at h1
    exact le_bot_iff.mp h1

theorem exists_offPoints_of_card_four {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h4 : Nat.card (pointsIn R (E ⊓ F)) = 4) :
    ∃ K : Subgroup G, Nat.card K = 16 ∧
      ∀ e : G, e ∈ K ↔ e ∈ E ∧ ∀ Q ∈ pointsIn R E, e ∈ Q → e = 1 := by
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hplane := isAffinePlane_points_of_card_four hE16 h11 hF hL h4
  have hRgE : rightConjugate R g ≤ E := (hF.inf_eq ▸ le_sup_right).trans inf_le_left
  have hRgR := rightConjugate_ne_of_frame hF
  have hRg : rightConjugate R g ∈ pointsIn R E := ⟨hRgE, g, rfl⟩
  have hR : R ∈ pointsIn R E := self_mem_pointsIn hF.R_le_E
  have hlineset : ∀ a (ha : a ∈ pointsIn R E) b (hb : b ∈ pointsIn R E),
      Subtype.val '' pointLine R E ⟨a, ha⟩ ⟨b, hb⟩ =
        {Q | Q ∈ pointsIn R E ∧ Q ≤ a ⊔ b} := by
    intro a ha b hb
    ext X
    simp only [Set.mem_image, pointLine, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.2, hQ⟩
    · rintro ⟨hX, hXab⟩
      exact ⟨⟨X, hX⟩, hXab, rfl⟩
  refine exists_subgroup_offPoints hcommE hF.cardE (fun Q hQ => hQ.1) ?_
    (fun Q₁ h₁ Q₂ h₂ hne => inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hcommE h₁ h₂ hne) ?_ ?_ ?_ ?_
  · rintro Q ⟨-, x, rfl⟩
    rw [rightConjugate_card, hF.cardR]
  · rw [← Nat.card_coe_set_eq, card_pointsIn_eq hE16 h11 hF hL, h4]
  · intro a ha b hb hab
    rw [← hlineset a ha b hb, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact ncard_pointLine_of_card_four hE16 h11 hF hL h4 (fun h => hab (congrArg Subtype.val h))
  ·
    intro a ha b hb hab P hP hPab
    obtain ⟨n, hna, hnb⟩ := exists_pointsAction_eq_pair_of_card_four hE16 h11 hF hL h4
      (p₁ := ⟨a, ha⟩) (p₂ := ⟨b, hb⟩) (q₁ := ⟨R, hR⟩) (q₂ := ⟨rightConjugate R g, hRg⟩)
      (fun h => hab (congrArg Subtype.val h)) (fun h => hRgR (congrArg Subtype.val h).symm)
    have hna' : rightConjugate a (n : G)⁻¹ = R := by
      have := congrArg Subtype.val hna
      rwa [coe_pointsAction_apply] at this
    have hnb' : rightConjugate b (n : G)⁻¹ = rightConjugate R g := by
      have := congrArg Subtype.val hnb
      rwa [coe_pointsAction_apply] at this
    have hP' : rightConjugate P (n : G)⁻¹ ∈ pointsIn R E :=
      rightConjugate_mem_pointsIn hP ((normalizer (E : Set G)).inv_mem n.2)
    have hsup : rightConjugate (a ⊔ b) (n : G)⁻¹ = R ⊔ rightConjugate R g := by
      rw [rightConjugate_sup', hna', hnb']
    have hne : rightConjugate P (n : G)⁻¹ ⊓ (R ⊔ rightConjugate R g) ≠ ⊥ := by
      rw [← hsup, ← AschbacherTheorem3.rightConjugate_inf]
      intro h
      apply hPab
      have h1 := congrArg (fun Z => rightConjugate Z (n : G)) h
      simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one,
        AschbacherTheorem3.rightConjugate_bot] at h1
      exact h1
    have h1 := le_sup_of_inf_ne_bot hE16 h11 hF hL hP' hRg hRgR hne
    rw [← hsup, rightConjugate_le_iff] at h1
    exact h1
  ·
    intro a ha b hb hab Q hQ hQab
    have hℓ : pointLine R E ⟨a, ha⟩ ⟨b, hb⟩ ∈ linesOf (pointLine R E) :=
      ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h), rfl⟩
    obtain ⟨m, ⟨hm, hQm, hdis⟩, -⟩ := hplane.parallel _ hℓ ⟨Q, hQ⟩ hQab
    obtain ⟨c, d, hcd, rfl⟩ := hm
    refine ⟨c, c.2, d, d.2, fun h => hcd (Subtype.ext h), hQm, fun P hP hPab hPcd => ?_⟩
    exact Set.disjoint_left.mp hdis (show (⟨P, hP⟩ : ↥(pointsIn R E)) ∈ pointLine R E ⟨a, ha⟩
      ⟨b, hb⟩ from hPab) hPcd

theorem card_pointsIn_inf_ne_four {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (heven : Even (Nat.card (center ↥A))) : Nat.card (pointsIn R (E ⊓ F)) ≠ 4 := by
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  obtain ⟨c⟩ := l34Cover_of_base h11 hF.base hL
  have hNZ := oddCore_le_center hstd.1.1 hstd.1.2
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨K, hK16, hK⟩ := exists_offPoints_of_card_four hE16 h11 hF hL h4
  obtain ⟨hT, -⟩ := isSylowOf_inf_and_inf_eq hF
  set T := (E ⊔ F) ⊓ A with hTdef
  have hEAe : IsElemAbelian 2 (E ⊓ A) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE a a.2.1 b b.2.1)⟩⟩, fun x hx => hF.elemE.2 x hx.1⟩
  have hcardEA := card_inf_eq_of_le_sup c hF.sylowR hF.R_le_E hF.E_le hF.cardE hF.cardR
  have hEAT : E ⊓ A ≤ T := inf_le_inf_right A le_sup_left
  have hTN : T ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    (radical_of_le c hNZ hT hEAT hEAe hcardEA).1
  have hTE : ∀ t ∈ T, t ∈ normalizer (E : Set G) := fun t ht =>
    mem_normalizer_of_mem_inf hF ⟨hT.le ht, hTN ht⟩
  have hTK : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K := by
    intro t ht k hk
    rw [hK] at hk ⊢
    refine ⟨(mem_normalizer_iff.mp (hTE t ht) k).mp hk.1, fun Q hQ hkQ => ?_⟩
    have hk' : k ∈ rightConjugate Q t := (mem_rightConjugate_iff Q t k).mpr hkQ
    rw [hk.2 _ (rightConjugate_mem_pointsIn hQ (hTE t ht)) hk', mul_one, mul_inv_cancel]
  have hR : R ∈ pointsIn R E := self_mem_pointsIn hF.R_le_E
  have hKR : K ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact ((hK x).mp hx.1).2 R hR hx.2
  have hKE : K ≤ E := fun x hx => ((hK x).mp hx).1
  have hKRE : K ⊔ R = E :=
    sup_eq_of_inf_eq_bot hcommE hKE hF.R_le_E hKR (by rw [hF.cardE, hK16, hF.cardR])
  have hcomm : ⁅T, E ⊓ A⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro t ht e he
    have he' : e ∈ K ⊔ R := hKRE ▸ he.1
    obtain ⟨k, hk, r, hr, rfl⟩ := exists_mul_of_mem_sup hcommE hKE hF.R_le_E he'
    have htr : t * r = r * t := (mem_centralizer_iff.mp (hRA hr) t (hT.le ht))
    rw [commutatorElement_def]
    have hrt : r * t⁻¹ = t⁻¹ * r := by
      calc r * t⁻¹ = t⁻¹ * (t * r) * t⁻¹ := by group
        _ = t⁻¹ * (r * t) * t⁻¹ := by rw [htr]
        _ = t⁻¹ * r := by group
    have e : t * (k * r) * t⁻¹ * (k * r)⁻¹ = (t * k * t⁻¹) * k⁻¹ := by
      calc t * (k * r) * t⁻¹ * (k * r)⁻¹ = t * k * (r * t⁻¹) * r⁻¹ * k⁻¹ := by group
        _ = t * k * (t⁻¹ * r) * r⁻¹ * k⁻¹ := by rw [hrt]
        _ = (t * k * t⁻¹) * k⁻¹ := by group
    rw [e]
    exact mul_mem (hTK t ht k hk) (inv_mem hk)
  obtain ⟨z, ⟨hzR, hzA⟩, hz1⟩ := exists_mem_inf_of_even hF heven
  have hzK : z ∈ centralizer (A : Set G) := hRA hzR
  have hzT : z ∈ T := by
    have hle := le_of_le_sup_centralizer hT inf_le_right
      (hF.sylowR.isPGroup.to_le inf_le_left) (inf_le_left.trans (hRA.trans le_sup_right))
    exact hle ⟨hzR, hzA⟩
  obtain ⟨T', hT'⟩ := hT
  have hzT' : (⟨z, hzA⟩ : ↥A) ∈ (T' : Subgroup ↥A) ⊓ center ↥A := by
    refine ⟨?_, mem_center_iff.mpr fun b => Subtype.ext (mem_centralizer_iff.mp hzK b b.2)⟩
    rw [← hT'] at hzT
    obtain ⟨y, hy, hyz⟩ := hzT
    rwa [show y = ⟨z, hzA⟩ from Subtype.ext hyz] at hy
  have hMT : (E ⊓ A).subgroupOf A ≤ T' := fun x hx => by
    have : (x : G) ∈ T := ⟨mem_sup_left (mem_subgroupOf.mp hx).1, x.2⟩
    rw [← hT'] at this
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x from Subtype.ext hyx] at hy
  have hcardM : Nat.card ((E ⊓ A).subgroupOf A) = 16 * Nat.card c.π.ker := by
    rw [← hcardEA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hzc := inf_center_le_commutator c hstd.1.1 T' hMT (isElemAbelian_subgroupOf hEAe A) hcardM
    hzT'
  have hzc' : z ∈ ⁅T, E ⊓ A⁆ := by
    have h1 : A.subtype ⟨z, hzA⟩ ∈ ⁅(T' : Subgroup ↥A), (E ⊓ A).subgroupOf A⁆.map A.subtype :=
      ⟨_, hzc, rfl⟩
    rwa [map_commutator, hT', subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at h1
  exact hz1 (((hK z).mp (hcomm hzc')).2 R hR hzR)

end Frame

theorem step16NotFourPoints {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) :
    Step16NotFourPoints := fun _ _ _ _ _ _ _ _ hF heven =>
  card_pointsIn_inf_ne_four hE16 h11 hF hF.typeA₁ heven

end CFSG.ComponentClassification.AS81
