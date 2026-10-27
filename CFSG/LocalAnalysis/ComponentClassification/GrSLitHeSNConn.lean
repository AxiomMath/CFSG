module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNMove
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectSubgroupLeTwoResidual

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem mem_twoResidualOf_top' [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (a : X) :
    a ∈ GorensteinWalter.twoResidualOf (⊤ : Subgroup X) := by
  have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup X) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      apply hxy
      have h1 : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
        Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  have hperf : Group.IsPerfect ↥(⊤ : Subgroup X) := Subgroup.isPerfect_iff.mpr hcomm
  exact GorensteinWalter.perfect_subgroup_le_twoResidualOf ⊤ ⊤ le_rfl hperf (mem_top a)

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

theorem card_inf_eq_of_isSylow
    (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    {T : Subgroup X} (hT₁ : IsSylowTwoIn (T ⊓ normalizer (K : Set X))
      (normalizer (W : Set X) ⊓ normalizer (K : Set X))) :
    Nat.card ↥(T ⊓ K) = 1024 := by
  have h1 := HeNormal.card_inf_eq_of_normal e₁ (le_inf h.le_normalizer le_normalizer)
    inf_le_right hT₁
  rwa [HeDiag.inf_normalizer_inf] at h1

section Conn


theorem exists_conn_of_not_le (hMax : MaximalTwoComponentInputHe)
    (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) {T : Subgroup X}
    (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set X)) (h1024 : Nat.card ↥(T ⊓ K) = 1024)
    (haT : a ∈ T) {F : Subgroup X} (hFT : F ≤ T) (hFe : IsElemTwo F) (hF8 : Nat.card F = 8)
    (hFK : ¬ F ≤ normalizer (K : Set X)) :
    ∃ B : Subgroup X, B ≤ T ⊓ normalizer (K : Set X) ∧ IsAbelianTwoOfRank 3 B ∧
      AbelianConnectedIn T 3 F B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcases : ∀ {F' : Subgroup X}, F' ≤ T → IsElemTwo F' → Nat.card F' = 8 →
      (Nat.card ↥(F' ⊓ normalizer (K : Set X)) = 4 ∨
        Nat.card ↥(F' ⊓ normalizer (K : Set X)) = 2) →
      ∃ B : Subgroup X, B ≤ T ⊓ normalizer (K : Set X) ∧ IsAbelianTwoOfRank 3 B ∧
        AbelianConnectedIn T 3 F' B := by
    intro F' hF'T hF'e hF'8 h42
    obtain ⟨B, hBT, hBe, hB8, hc⟩ : ∃ B : Subgroup X, B ≤ T ⊓ normalizer (K : Set X) ∧
        IsElemTwo B ∧ Nat.card B = 8 ∧ ∀ x ∈ F', ∀ y ∈ B, x * y = y * x := by
      rcases h42 with h4 | h2
      · exact h.exists_comm_of_card_four e₁ h64 hOut hT2 hTM h1024 hF'T hF'e hF'8 h4
      · exact h.exists_comm_of_card_two e₁ h64 hOut hT2 hTM h1024 hF'T hF'e hF'8 h2
    have hBr := hBe.isAbelianTwoOfRank (by omega)
    exact ⟨B, hBT, hBr, hF'T, hF'e.isAbelianTwoOfRank (by omega),
      Relation.ReflTransGen.single ⟨hBT.trans inf_le_left, hBr, hc⟩⟩
  have hdvd : Nat.card ↥(F ⊓ normalizer (K : Set X)) ∣ 8 := hF8 ▸ card_dvd_of_le inf_le_left
  have hne8 : Nat.card ↥(F ⊓ normalizer (K : Set X)) ≠ 8 := fun h8 => hFK (by
    have h1 := eq_of_le_of_card_ge (inf_le_left : F ⊓ normalizer (K : Set X) ≤ F)
      (by rw [h8, hF8])
    rw [← h1]
    exact inf_le_right)
  have hle8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ↥(F ⊓ normalizer (K : Set X)) := Nat.card_pos
  interval_cases hn : Nat.card ↥(F ⊓ normalizer (K : Set X))
  ·
    have hF₀ : F ⊓ normalizer (K : Set X) = ⊥ := card_eq_one.mp hn
    have hTne : T ≠ ⊥ := fun hb => by
      have h1 := card_le_of_le hFT
      rw [hb, card_bot, hF8] at h1
      omega
    obtain ⟨z, hzT, hz2, hzc⟩ := exists_central_involution hT2 le_rfl le_normalizer hTne
    have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
    have hzK : z ∈ normalizer (K : Set X) :=
      ((h.centralizer_le_normalizer hMax).trans h.normalizer_L_le)
        (mem_centralizer_singleton_iff.mpr (hzc a haT).symm)
    have hnK : ∀ x ∈ F, x ∈ normalizer (K : Set X) → x = 1 := fun x hx hxK => by
      have h1 : x ∈ F ⊓ normalizer (K : Set X) := mem_inf.mpr ⟨hx, hxK⟩
      rwa [hF₀, mem_bot] at h1
    have hzF : z ∉ F := fun hz => by
      rw [hnK z hz hzK, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    obtain ⟨c, hcF, hc1⟩ : ∃ c ∈ F, c ≠ 1 := by
      by_contra hall
      push Not at hall
      have h1 : F = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hall x hx)
      rw [h1, card_bot] at hF8
      omega
    have hc2 : orderOf c = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hFe.2 c hcF) hc1
    have hcK : c ∉ normalizer (K : Set X) := fun hc => hc1 (hnK c hcF hc)
    obtain ⟨d, hdF, hdc⟩ : ∃ d ∈ F, d ∉ zpowers c := by
      by_contra hall
      push Not at hall
      have h1 := card_le_of_le (fun x hx => hall x hx : F ≤ zpowers c)
      rw [Nat.card_zpowers, hc2, hF8] at h1
      omega
    have hd2 : orderOf d = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hFe.2 d hdF) fun h1 => hdc (h1 ▸ one_mem _)
    have hF₂F : zpowers c ⊔ zpowers d ≤ F := sup_le (zpowers_le.mpr hcF) (zpowers_le.mpr hdF)
    have hF₂4 : Nat.card ↥(zpowers c ⊔ zpowers d) = 4 := by
      rw [card_sup_zpowers hd2 hdc (GrSLit.mem_normalizer_of_commute fun x hx =>
        hFe.1 d hdF x (zpowers_le.mpr hcF hx)), Nat.card_zpowers, hc2]
    have hzF₂ : z ∉ zpowers c ⊔ zpowers d := fun hz => hzF (hF₂F hz)
    have hF''8 : Nat.card ↥(zpowers c ⊔ zpowers d ⊔ zpowers z) = 8 := by
      rw [card_sup_zpowers hz2 hzF₂ (GrSLit.mem_normalizer_of_commute fun x hx =>
        (hzc x (hFT (hF₂F hx))).symm), hF₂4]
    have hF''e : IsElemTwo (zpowers c ⊔ zpowers d ⊔ zpowers z) :=
      (hFe.mono hF₂F).sup (isElemTwo_zpowers hzz) fun x hx y hy => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_right (show Commute x z from hzc x (hFT (hF₂F hx))) k).eq
    have hF''T : zpowers c ⊔ zpowers d ⊔ zpowers z ≤ T :=
      sup_le (hF₂F.trans hFT) (zpowers_le.mpr hzT)
    have hF''K : ¬ zpowers c ⊔ zpowers d ⊔ zpowers z ≤ normalizer (K : Set X) := fun hle =>
      hcK (hle (mem_sup_left (mem_sup_left (mem_zpowers c))))
    have hz₀ : z ∈ (zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓ normalizer (K : Set X) :=
      mem_inf.mpr ⟨mem_sup_right (mem_zpowers z), hzK⟩
    have hdvd'' : Nat.card ↥((zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓ normalizer (K : Set X)) ∣
        8 := hF''8 ▸ card_dvd_of_le inf_le_left
    have hne8'' :
        Nat.card ↥((zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓ normalizer (K : Set X)) ≠ 8 :=
      fun h8 => hF''K (by
        have h1 := eq_of_le_of_card_ge (inf_le_left : (zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓
          normalizer (K : Set X) ≤ _) (by rw [h8, hF''8])
        rw [← h1]
        exact inf_le_right)
    have hne1'' :
        Nat.card ↥((zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓ normalizer (K : Set X)) ≠ 1 :=
      fun h1 => by
        have h2 := (card_eq_one.mp h1) ▸ hz₀
        rw [mem_bot] at h2
        rw [h2, orderOf_one] at hz2
        exact absurd hz2 (by norm_num)
    have hle8'' := Nat.le_of_dvd (by norm_num) hdvd''
    have h42 : Nat.card ↥((zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓ normalizer (K : Set X)) = 4 ∨
        Nat.card ↥((zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓ normalizer (K : Set X)) = 2 := by
      interval_cases hm : Nat.card ↥((zpowers c ⊔ zpowers d ⊔ zpowers z) ⊓
        normalizer (K : Set X)) <;> simp_all
    obtain ⟨B, hBT, hBr, hconnB⟩ := hcases hF''T hF''e hF''8 h42
    have hFF'' : AbelianConnectedIn T 3 F (zpowers c ⊔ zpowers d ⊔ zpowers z) :=
      ⟨hFT, hFe.isAbelianTwoOfRank (by omega), Relation.ReflTransGen.single
        ⟨hF''T, hF''e.isAbelianTwoOfRank (by omega), commute_sup_right
          (fun x hx y hy => hFe.1 x hx y (hF₂F hy)) fun x hx y hy => by
            obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
            exact (Commute.zpow_right (show Commute x z from hzc x (hFT hx)) k).eq⟩⟩
    exact ⟨B, hBT, hBr, hFF''.trans hconnB⟩
  · exact hcases hFT hFe hF8 (Or.inr hn)
  · exact absurd hdvd (by norm_num)
  · exact hcases hFT hFe hF8 (Or.inl hn)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd rfl hne8

theorem isThreeConnected (hMax : MaximalTwoComponentInputHe) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) {T : Subgroup X} (hT2 : IsPGroup 2 T)
    (hTM : T ≤ normalizer (W : Set X)) (haT : a ∈ T)
    (hT₁ : IsSylowTwoIn (T ⊓ normalizer (K : Set X))
      (normalizer (W : Set X) ⊓ normalizer (K : Set X))) : IsThreeConnected T := by
  obtain ⟨e₁⟩ := h.heldK
  have h1024 := h.card_inf_eq_of_isSylow e₁ hT₁
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [HeDiag.inf_normalizer_inf]; exact h1024
  have h3₁ := HeNormal.isThreeConnected_of_normal e₁ h64 hOut (hT2.to_le inf_le_left)
    inf_le_right h1024'
  obtain ⟨E, hET, -, hEe, hE64⟩ :=
    exists_elem_sixtyFour e₁ h64 inf_le_right (hT2.to_le inf_le_left) h1024
  have hEr : IsAbelianTwoOfRank 3 E := hEe.isAbelianTwoOfRank (by omega)
  have hET₁ : E ≤ T ⊓ normalizer (K : Set X) := hET.trans (inf_le_inf_left T le_normalizer)
  have key : ∀ A : Subgroup X, A ≤ T → IsAbelianTwoOfRank 3 A → AbelianConnectedIn T 3 A E := by
    intro A hAT hA
    obtain ⟨F, hFA, hFe, hF8⟩ := exists_isElemTwo_eight hA
    have hFT := hFA.trans hAT
    have hFr := hFe.isAbelianTwoOfRank (by omega)
    have hAF : AbelianConnectedIn T 3 A F :=
      ⟨hAT, hA, Relation.ReflTransGen.single ⟨hFT, hFr, fun x hx y hy => hA.2.1 x hx y (hFA hy)⟩⟩
    by_cases hFK : F ≤ normalizer (K : Set X)
    · exact hAF.trans ((h3₁ F E (le_inf hFT hFK) hET₁ hFr hEr).mono inf_le_left)
    · obtain ⟨B, hBT, hBr, hFB⟩ :=
        h.exists_conn_of_not_le hMax e₁ h64 hOut hT2 hTM h1024 haT hFT hFe hF8 hFK
      exact hAF.trans (hFB.trans ((h3₁ B E hBT hET₁ hBr hEr).mono inf_le_left))
  intro A B hAT hBT hA hB
  exact (key A hAT hA).trans (key B hBT hB).symm

theorem three_le_pRank_centralizer (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) {T : Subgroup X}
    (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set X)) (h1024 : Nat.card ↥(T ⊓ K) = 1024)
    {t : X} (htT : t ∈ T) (htt : t * t = 1) :
    3 ≤ pRank 2 ↥(T ⊓ centralizer ({t} : Set X)) := by
  have hT₁2 : IsPGroup 2 ↥(T ⊓ normalizer (K : Set X)) := hT2.to_le inf_le_left
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [HeDiag.inf_normalizer_inf]; exact h1024
  by_cases htK : t ∈ normalizer (K : Set X)
  · obtain ⟨F, hFS, hFC, hFe, hF8⟩ := HeDiag.exists_eight_fixed e₁ h64 hOut
      (inf_le_right : T ⊓ normalizer (K : Set X) ≤ _) hT₁2 h1024' (mem_inf.mpr ⟨htT, htK⟩) htt
    exact three_le_pRank_of_le hFe (by omega)
      (le_inf (hFS.trans (inf_le_left.trans inf_le_left)) hFC)
  · have hKt : conjugate K t ≠ K := fun e => htK (mem_normalizer_of_conjugate_eq e)
    obtain ⟨hY, hinj, hψT⟩ := h.doubleHom_facts e₁ hT2 hTM htT hKt
    obtain ⟨E, hET, -, hEe, hE64⟩ :=
      exists_elem_sixtyFour e₁ h64 inf_le_right (hT2.to_le inf_le_left) h1024
    let φ : ↥E →* X := (doubleHom hY).comp (inclusion hET)
    have hφinj : Function.Injective φ := hinj.comp (inclusion_injective hET)
    refine three_le_pRank_of_le (isElemTwo_range hEe φ)
      (by rw [card_range_of_injective hφinj, hE64]; norm_num) ?_
    rintro _ ⟨y, rfl⟩
    exact mem_inf.mpr ⟨(mem_inf.mp (hψT _)).1, mem_centralizer_singleton_iff.mpr
      (commute_doubleHom_self hY htt (inclusion hET y)).symm.eq⟩

end Conn

end Setting

end CFSG.ComponentClassification.GrSLit.HeSN
