module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5ExclComp
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.Goldschmidt.Steps.Red2Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N.P5
  CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Comp

theorem eq_bot_or_eq_of_invariant16 {Q : Type*} [Group Q] [Finite Q] {Ab B : Subgroup Q}
    {φ : MulAut Q} (hcard : Nat.card Ab = 16) (hφ : φ ^ 5 = 1)
    (hfpf : ∀ a ∈ Ab, φ a = a → a = 1) (hBA : B ≤ Ab) (hφB : ∀ b ∈ B, φ b ∈ B) :
    B = ⊥ ∨ B = Ab := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod : Nat.card B ≡ 1 [MOD 5] :=
    card_modEq_one_of_fpf hφ hφB fun c hc h => hfpf c (hBA hc) h
  have hdvd : Nat.card B ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le hBA
    rwa [hcard] at this
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hkc] at hmod
  interval_cases k
  · left
    exact Subgroup.card_eq_one.1 (by simpa using hkc)
  · simp [Nat.ModEq] at hmod
  · simp [Nat.ModEq] at hmod
  · simp [Nat.ModEq] at hmod
  · right
    exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hcard, hkc]; norm_num)

section


theorem comp_odd_transitive16 {Q : Type} [Group Q] [Finite Q] (hO : goldschmidtOddCore Q = ⊥)
    (hR : pCore 2 Q = ⊥) (hL : pCore 2 Q ⊔ goldschmidtLayer Q = ⊤)
    (hgold : ∀ K : Subgroup Q, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ center K))
    (Sb : Sylow 2 Q) {Ab : Subgroup Q}
    (hAb : Ab = pCore 2 Q ⊔ closure {t | t ∈ (Sb : Subgroup Q) ⊓ goldschmidtLayer Q ∧ t ^ 2 = 1})
    (hEA : IsElemAbelian 2 Ab) (hcard : Nat.card Ab = 16)
    {φ : MulAut Q} (hφ : φ ^ 5 = 1) (hφA : ∀ a ∈ Ab, φ a ∈ Ab) (hfpf : ∀ a ∈ Ab, φ a = a → a = 1)
    (hlay : goldschmidtLayer Q ≠ ⊥) :
    (∀ a ∈ Ab, ∀ b ∈ Ab, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (Ab : Set Q), n⁻¹ * a * n = b) ∧
      Odd ((centralizer (Ab : Set Q)).relIndex (normalizer (Ab : Set Q))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hlay' : goldschmidtLayer Q = ⊤ := by rwa [hR, bot_sup_eq] at hL
  have hinv0 : ∀ t ∈ (Sb : Subgroup Q), t ^ 2 = 1 → t ∈ Ab := by
    intro t ht ht2
    rw [hAb]
    refine Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨ht, ?_⟩, ht2⟩)
    rw [hlay']
    exact mem_top t
  obtain ⟨K, hK⟩ : ∃ K : Subgroup Q, IsComponentOf K ⊤ := by
    by_contra hnone
    push Not at hnone
    apply hlay
    rw [goldschmidtLayer.eq_sSup]
    have : {K : Subgroup Q | IsComponentOf K ⊤} = ∅ := Set.eq_empty_of_forall_notMem hnone
    rw [this, sSup_empty]
  have hZK := eq_one_of_central_component hO hR hlay' hK
  obtain ⟨s, hsK, hsP, hs1, hs2⟩ := exists_involution_of_component Sb hK
  have hsAb : s ∈ Ab := hinv0 s hsP hs2
  have hsnc : ∃ k ∈ K, s * k ≠ k * s := by
    by_contra hcon
    push Not at hcon
    exact hs1 (hZK s hsK hcon)
  have hφK : K.map φ.toMonoidHom = K :=
    map_eq_of_fpf hφ (fun a ha b hb => congrArg Subtype.val (hEA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      hφA hfpf hK hsAb hsK hsnc
  have hBne : Ab ⊓ K ≠ ⊥ := by
    intro h
    have : s ∈ Ab ⊓ K := mem_inf.2 ⟨hsAb, hsK⟩
    rw [h] at this
    exact hs1 (Subgroup.mem_bot.1 this)
  have hBeq : Ab ⊓ K = Ab :=
    (eq_bot_or_eq_of_invariant16 hcard hφ hfpf inf_le_left fun b hb => by
      rw [mem_inf] at hb ⊢
      exact ⟨hφA b hb.1, map_mem_of_map_eq hφK hb.2⟩).resolve_left hBne
  have hAbK : Ab ≤ K := hBeq ▸ inf_le_right
  have hfaith : ∀ b ∈ Ab, b ∈ centralizer (K : Set Q) → b = 1 := by
    intro b hbA hbC
    by_contra hb1
    have hCne : Ab ⊓ centralizer (K : Set Q) ≠ ⊥ := by
      intro h
      have : b ∈ Ab ⊓ centralizer (K : Set Q) := mem_inf.2 ⟨hbA, hbC⟩
      rw [h] at this
      exact hb1 (Subgroup.mem_bot.1 this)
    have hCeq : Ab ⊓ centralizer (K : Set Q) = Ab :=
      (eq_bot_or_eq_of_invariant16 hcard hφ hfpf inf_le_left fun c hc => by
        rw [mem_inf] at hc ⊢
        exact ⟨hφA c hc.1, map_mem_centralizer_of_map_eq hφK hc.2⟩).resolve_left hCne
    have hAbC : Ab ≤ centralizer (K : Set Q) := hCeq ▸ inf_le_right
    have hAb1 : Ab = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      exact Subgroup.mem_bot.2
        (hZK u (hAbK hu) fun k hk => (Subgroup.mem_centralizer_iff.1 (hAbC hu) k hk).symm)
    rw [hAb1, Subgroup.card_bot] at hcard
    omega
  obtain ⟨hKtop, hZ, hinv⟩ :=
    LemmaX.layer_structure hO Sb hL hAb (by rw [hR]; exact bot_le) K hK hfaith
  subst hKtop
  have hcen : center ↥(⊤ : Subgroup Q) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : (z : Q) ∈ center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, mem_top y⟩)
    rw [hZ] at hzc
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hzc))
  let e : ↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q) ≃* Q :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv
  haveI hsimple : IsSimpleGroup Q := by
    haveI := hK.2.2.2
    exact e.symm.isSimpleGroup
  have hGT : goldschmidtSimpleType Q :=
    Red2.goldschmidtSimpleType_of_mulEquiv e.symm (hgold _ hK)
  have hAbS : Ab ≤ (Sb : Subgroup Q) := by
    rw [hAb]
    exact sup_le (by rw [hR]; exact bot_le) ((closure_le _).2 fun t ht => ht.1.1)
  have hΩ : Goldschmidt.Omega1 (Sb : Subgroup Q) = Ab := by
    apply le_antisymm
    · exact (closure_le _).2 fun t ht => hinv t ht.1 ht.2
    · intro a ha
      exact Subgroup.subset_closure ⟨hAbS ha, hEA.2 a ha⟩
  have hΩab : IsMulCommutative (Goldschmidt.Omega1 (Sb : Subgroup Q)) := by
    rw [hΩ]
    exact hEA.1
  refine ⟨fun a ha b hb ha1 hb1 => ?_, ?_⟩
  · have h := N.P4.goldExcl_transitive hGT Sb hΩab a (hΩ ▸ ha) b (hΩ ▸ hb) ha1 hb1
    rw [hΩ] at h
    exact h
  · have h := N.P4.goldExcl_odd hGT Sb hΩab
    rw [hΩ] at h
    exact h

end

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
