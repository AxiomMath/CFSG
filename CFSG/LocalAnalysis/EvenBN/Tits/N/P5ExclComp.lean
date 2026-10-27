module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5CompFix
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4GoldExcl
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.Goldschmidt.Steps.Red2Basic
import CFSG.Goldschmidt.Steps.PropHSetup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N.P5
  CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Comp

theorem eq_one_of_central_component {Q : Type} [Group Q] [Finite Q] (hO : goldschmidtOddCore Q = ⊥)
    (hR : pCore 2 Q = ⊥) (hL : goldschmidtLayer Q = ⊤) {K : Subgroup Q} (hK : IsComponentOf K ⊤) :
    ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z = 1 := by
  intro z hzK hz
  have hle : goldschmidtLayer Q ≤ centralizer ({z} : Set Q) := by
    rw [goldschmidtLayer.eq_sSup]
    refine sSup_le fun L hL' => ?_
    by_cases hLK : L = K
    · subst hLK
      intro l hl
      rw [mem_centralizer_singleton_iff]
      exact (hz l hl).symm
    · intro l hl
      rw [mem_centralizer_singleton_iff]
      exact comm_of_components hK hL' (Ne.symm hLK) l hl z hzK
  have hzc : z ∈ center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ goldschmidtLayer Q := by rw [hL]; exact mem_top y
    exact mem_centralizer_singleton_iff.1 (hle hy)
  obtain ⟨-, hZE, -⟩ := N8d Q hO
  have hzL : z ∈ goldschmidtLayer Q := by rw [hL]; exact mem_top z
  have hzp : z ∈ pCore 2 Q :=
    hZE ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (Subgroup.mem_center_iff.1 hzc y), rfl⟩
  rw [hR] at hzp
  exact Subgroup.mem_bot.1 hzp

theorem map_mem_of_map_eq {Q : Type*} [Group Q] {e : MulAut Q} {K : Subgroup Q}
    (h : K.map e.toMonoidHom = K) {k : Q} (hk : k ∈ K) : e k ∈ K := by
  have : e k ∈ K.map e.toMonoidHom := ⟨k, hk, rfl⟩
  rwa [h] at this

theorem exists_preimage_of_map_eq {Q : Type*} [Group Q] {e : MulAut Q} {K : Subgroup Q}
    (h : K.map e.toMonoidHom = K) {k : Q} (hk : k ∈ K) : ∃ k' ∈ K, e k' = k := by
  rw [← h] at hk
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨k', hk', rfl⟩

theorem map_mem_centralizer_of_map_eq {Q : Type*} [Group Q] {e : MulAut Q} {K : Subgroup Q}
    (h : K.map e.toMonoidHom = K) {c : Q} (hc : c ∈ centralizer (K : Set Q)) :
    e c ∈ centralizer (K : Set Q) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨k', hk', rfl⟩ := exists_preimage_of_map_eq h hk
  have := Subgroup.mem_centralizer_iff.1 hc k' hk'
  rw [← map_mul, ← map_mul, this]

theorem exists_involution_of_component {Q : Type} [Group Q] [Finite Q] (P : Sylow 2 Q) {K : Subgroup Q}
    (hK : IsComponentOf K ⊤) : ∃ s ∈ K, s ∈ (P : Subgroup Q) ∧ s ≠ 1 ∧ s ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : K.IsSubnormal := G310.isSubnormal_of_isComponentOf hK
  obtain ⟨R, hR⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hsub
  obtain ⟨s, hsR, hs2⟩ := PropHSetup.exists_orderOf_eq_two R.isPGroup'
    (R.ne_bot_of_dvd_card (LemmaX.two_dvd_card_of_isQuasisimple hK.2.2))
  have hs2' : orderOf (s : Q) = 2 := (Subgroup.orderOf_coe s).trans hs2
  have h1 : (s : Q) ∈ (R : Subgroup K).map K.subtype := ⟨s, hsR, rfl⟩
  rw [hR] at h1
  refine ⟨(s : Q), s.2, h1.1, ?_, hs2' ▸ pow_orderOf_eq_one (s : Q)⟩
  intro h
  rw [h, orderOf_one] at hs2'
  exact absurd hs2' (by norm_num)

section


theorem comp_transitive {Q : Type} [Group Q] [Finite Q] (hO : goldschmidtOddCore Q = ⊥)
    (hR : pCore 2 Q = ⊥) (hL : pCore 2 Q ⊔ goldschmidtLayer Q = ⊤)
    (hgold : ∀ K : Subgroup Q, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ center K))
    (Sb : Sylow 2 Q) {Ab U : Subgroup Q}
    (hAb : Ab = pCore 2 Q ⊔ closure {t | t ∈ (Sb : Subgroup Q) ⊓ goldschmidtLayer Q ∧ t ^ 2 = 1})
    (hEA : IsElemAbelian 2 Ab) (hcard : Nat.card Ab = 256)
    {φ ψ : MulAut Q} (hφ : φ ^ 5 = 1) (hψ : ψ ^ 2 = 1) (hcomm : φ * ψ = ψ * φ)
    (hφA : ∀ a ∈ Ab, φ a ∈ Ab) (hψA : ∀ a ∈ Ab, ψ a ∈ Ab) (hfpf : ∀ a ∈ Ab, φ a = a → a = 1)
    (hUA : U ≤ Ab) (hU : ∀ a ∈ Ab, ψ a = a ↔ a ∈ U) (hU16 : Nat.card U = 16)
    (hsolv : Group.IsSolvable ↥(fixSub ψ)) :
    ∀ a ∈ Ab, ∀ b ∈ Ab, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (Ab : Set Q), n⁻¹ * a * n = b := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlay : goldschmidtLayer Q = ⊤ := by rwa [hR, bot_sup_eq] at hL
  have hinv0 : ∀ t ∈ (Sb : Subgroup Q), t ^ 2 = 1 → t ∈ Ab := by
    intro t ht ht2
    rw [hAb]
    refine Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨ht, ?_⟩, ht2⟩)
    rw [hlay]
    exact mem_top t
  obtain ⟨K, hK⟩ : ∃ K : Subgroup Q, IsComponentOf K ⊤ := by
    by_contra hnone
    push Not at hnone
    have h1 : goldschmidtLayer Q = ⊥ := by
      rw [goldschmidtLayer.eq_sSup]
      have : {K : Subgroup Q | IsComponentOf K ⊤} = ∅ := Set.eq_empty_of_forall_notMem hnone
      rw [this, sSup_empty]
    rw [hlay] at h1
    have h2 : Nat.card Ab ∣ Nat.card (⊥ : Subgroup Q) := by
      have := Subgroup.card_dvd_of_le (le_top : Ab ≤ ⊤)
      rwa [h1] at this
    rw [Subgroup.card_bot, hcard] at h2
    exact absurd (Nat.dvd_one.1 h2) (by norm_num)
  have hZK := eq_one_of_central_component hO hR hlay hK
  obtain ⟨s, hsK, hsP, hs1, hs2⟩ := exists_involution_of_component Sb hK
  have hsAb : s ∈ Ab := hinv0 s hsP hs2
  have hsnc : ∃ k ∈ K, s * k ≠ k * s := by
    by_contra hcon
    push Not at hcon
    exact hs1 (hZK s hsK hcon)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hφK : K.map φ.toMonoidHom = K :=
    map_eq_of_fpf hφ (fun a ha b hb => congrArg Subtype.val (hEA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      hφA hfpf hK hsAb hsK hsnc
  have hψK : K.map ψ.toMonoidHom = K := map_eq_of_involution hψ hK hZK hsolv
  have hinvB : ∀ e : MulAut Q, (∀ a ∈ Ab, e a ∈ Ab) → K.map e.toMonoidHom = K →
      ∀ b ∈ Ab ⊓ K, e b ∈ Ab ⊓ K := by
    intro e heA heK b hb
    rw [mem_inf] at hb ⊢
    exact ⟨heA b hb.1, map_mem_of_map_eq heK hb.2⟩
  have hinvC : ∀ e : MulAut Q, (∀ a ∈ Ab, e a ∈ Ab) → K.map e.toMonoidHom = K →
      ∀ c ∈ Ab ⊓ centralizer (K : Set Q), e c ∈ Ab ⊓ centralizer (K : Set Q) := by
    intro e heA heK c hc
    rw [mem_inf] at hc ⊢
    exact ⟨heA c hc.1, map_mem_centralizer_of_map_eq heK hc.2⟩
  have hBne : Ab ⊓ K ≠ ⊥ := by
    intro h
    have : s ∈ Ab ⊓ K := mem_inf.2 ⟨hsAb, hsK⟩
    rw [h] at this
    exact hs1 (Subgroup.mem_bot.1 this)
  have hUB : U ≤ Ab ⊓ K :=
    le_of_invariant hcard hφ hψ hcomm hφA hψA hfpf hUA hU hU16 inf_le_left
      (hinvB φ hφA hφK) (hinvB ψ hψA hψK) hBne
  have hfaith : ∀ b ∈ Ab, b ∈ centralizer (K : Set Q) → b = 1 := by
    intro b hbA hbC
    by_contra hb1
    have hCne : Ab ⊓ centralizer (K : Set Q) ≠ ⊥ := by
      intro h
      have : b ∈ Ab ⊓ centralizer (K : Set Q) := mem_inf.2 ⟨hbA, hbC⟩
      rw [h] at this
      exact hb1 (Subgroup.mem_bot.1 this)
    have hUC : U ≤ Ab ⊓ centralizer (K : Set Q) :=
      le_of_invariant hcard hφ hψ hcomm hφA hψA hfpf hUA hU hU16 inf_le_left
        (hinvC φ hφA hφK) (hinvC ψ hψA hψK) hCne
    have hUbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu1 := (mem_inf.1 (hUB hu)).2
      have hu2 := (mem_inf.1 (hUC hu)).2
      exact Subgroup.mem_bot.2
        (hZK u hu1 fun k hk => (Subgroup.mem_centralizer_iff.1 hu2 k hk).symm)
    rw [hUbot, Subgroup.card_bot] at hU16
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
  intro a ha b hb ha1 hb1
  have h := N.P4.goldExcl_transitive hGT Sb hΩab a (hΩ ▸ ha) b (hΩ ▸ hb) ha1 hb1
  rw [hΩ] at h
  exact h

end

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
