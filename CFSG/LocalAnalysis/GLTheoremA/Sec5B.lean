module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
public import CFSG.Walter.Bender1970.S3.CoreExchangeTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace Prop53

section Finite

variable {G : Type} [Group G] [Finite G]

theorem exists_typePP_subgroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q B : Subgroup G} {x : G}
    (hQp : IsPGroup p Q) (hQnc : ¬ IsCyclic Q) (hB : IsElemAbelian p B)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hxQ : x ∈ Q) (hxB : x ∈ B) :
    ∃ D : Subgroup G, D ≤ Q ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ x ∈ D ∧
      B ≤ Subgroup.normalizer (D : Set G) ∧
      Nat.card B ≤ p * Nat.card (B ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) := by
  classical
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  have hxp : x ^ p = 1 := hB.2 x hxB
  set 𝔓 := Q ⊔ B with h𝔓
  have h𝔓p : IsPGroup p 𝔓 := hQp.to_sup_of_normal_left' hBp hBQ
  have hB𝔓 : B ≤ 𝔓 := le_sup_right
  have hQ𝔓 : Q ≤ 𝔓 := le_sup_left
  have h𝔓N : 𝔓 ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hBQ
  obtain ⟨X, hXQ, hXc, hXexp, hXN⟩ := CFSG.Walter.exists_noncyclic_exponent_le hp hp2 hQp hQnc
  have hX𝔓 : X ≤ 𝔓 := hXQ.trans hQ𝔓
  have h𝔓X : 𝔓 ≤ Subgroup.normalizer (X : Set G) := h𝔓N.trans hXN
  obtain ⟨z, hzX, y, hyX, hz1, hz𝔓, hynz, hyc, -, -⟩ :=
    CFSG.Walter.exists_typePP hp hp2 h𝔓p hX𝔓 h𝔓X hXexp hXc (t := 1) (mul_one 1)
      (Subgroup.one_mem _) (Subgroup.one_mem _)
  have hzp : z ^ p = 1 := hXexp z hzX
  have hyp : y ^ p = 1 := hXexp y hyX
  have hzQ : z ∈ Q := hXQ hzX
  have hyQ : y ∈ Q := hXQ hyX
  have hzcomm : ∀ g ∈ 𝔓, g * z = z * g := fun g hg => Subgroup.mem_centralizer_iff.1 hz𝔓 g hg
  have hyz : y * z = z * y := hzcomm y (hQ𝔓 hyQ)
  obtain ⟨hVe, hVc⟩ := isElemAbelian_card_sup_zpowers hp hyz hyp hzp hz1 hynz
  have hzcard : Nat.card (Subgroup.zpowers z) = p := card_zpowers_eq_of_pow hp hzp hz1
  by_cases hxV : x ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers z
  · refine ⟨Subgroup.zpowers y ⊔ Subgroup.zpowers z,
      sup_le (Subgroup.zpowers_le.2 hyQ) (Subgroup.zpowers_le.2 hzQ), hVe, hVc, hxV, ?_, ?_⟩
    · intro g hg
      have hg𝔓 : g ∈ 𝔓 := hB𝔓 hg
      apply mem_normalizer_zpowers_sup
      · have h1 := hyc g hg𝔓
        have h2 : g * y * g⁻¹ = ⁅y, g⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
      · have h2 : g * z * g⁻¹ = z := by
          rw [hzcomm g hg𝔓]
          group
        rw [h2]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    · have hcard := (CFSG.Walter.card_le_and_commutator_le_of_commutator_mem hz𝔓 hyc hB𝔓).1
      rw [hzcard] at hcard
      refine hcard.trans (Nat.mul_le_mul_left p (Subgroup.card_le_of_le ?_))
      intro b hb
      refine ⟨hb.1, mem_centralizer_of_le_centralizer ?_⟩
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hb.2).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hzcomm b (hB𝔓 hb.1)).symm
  · have hxz : x * z = z * x := hzcomm x (hB𝔓 hxB)
    have hxnz : x ∉ Subgroup.zpowers z := fun h => hxV (Subgroup.mem_sup_right h)
    obtain ⟨hDe, hDc⟩ := isElemAbelian_card_sup_zpowers hp hxz hxp hzp hz1 hxnz
    have hBcD : ∀ b ∈ B, b ∈ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) : Set G) := by
      intro b hb
      refine mem_centralizer_of_le_centralizer (sup_le (Subgroup.zpowers_le.2 ?_)
        (Subgroup.zpowers_le.2 ?_))
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact isElemAbelian_commute hB hxB hb
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hzcomm b (hB𝔓 hb)).symm
    refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers z,
      sup_le (Subgroup.zpowers_le.2 hxQ) (Subgroup.zpowers_le.2 hzQ), hDe, hDc,
      Subgroup.mem_sup_left (Subgroup.mem_zpowers x), ?_, ?_⟩
    · intro g hg
      exact Subgroup.centralizer_le_normalizer _ (hBcD g hg)
    · have : (B ⊓ Subgroup.centralizer
          ((Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) : Set G)) = B :=
        inf_eq_left.2 hBcD
      rw [this]
      exact Nat.le_mul_of_pos_left _ hp.pos

theorem card_le_card_sup_inf_centralizer {p : ℕ} (hp : p.Prime) {B D : Subgroup G}
    (hB : IsElemAbelian p B) (hD : Nat.card D = p ^ 2)
    (hcount : Nat.card B ≤
      p * Nat.card (B ⊓ Subgroup.centralizer (D : Set G) : Subgroup G)) :
    Nat.card B ≤ Nat.card (D ⊔ (B ⊓ Subgroup.centralizer (D : Set G)) : Subgroup G) := by
  set C := B ⊓ Subgroup.centralizer (D : Set G) with hC
  have hCle : C ≤ Subgroup.normalizer (D : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hCle
  by_cases hDB : D ≤ B
  · have hBC : B ≤ Subgroup.centralizer (D : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact isElemAbelian_commute hB (hDB hd) hb
    have hCB : C = B := inf_eq_left.2 hBC
    calc Nat.card B = Nat.card C := by rw [hCB]
      _ ≤ _ := Subgroup.card_le_of_le le_sup_right
  · have h1 : Nat.card (D ⊓ B : Subgroup G) ≤ p := by
      have hd : Nat.card (D ⊓ B : Subgroup G) ∣ p ^ 2 :=
        hD ▸ Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).1 hd
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · rw [hkeq, pow_zero]
        exact hp.one_lt.le
      · rw [hkeq, pow_one]
      · exfalso
        apply hDB
        have : D ⊓ B = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hD, hkeq])
        exact this ▸ inf_le_right
    have h2 : Nat.card (D ⊓ C : Subgroup G) ≤ p :=
      (Subgroup.card_le_of_le (inf_le_inf_left D inf_le_left)).trans h1
    have h3 : p ^ 2 * Nat.card C ≤ Nat.card (D ⊔ C : Subgroup G) * p := by
      calc p ^ 2 * Nat.card C
          = Nat.card (D ⊔ C : Subgroup G) * Nat.card (D ⊓ C : Subgroup G) := by
            rw [hprod, hD]
        _ ≤ Nat.card (D ⊔ C : Subgroup G) * p := Nat.mul_le_mul_left _ h2
    have h4 : p * Nat.card C ≤ Nat.card (D ⊔ C : Subgroup G) := by
      have : p * (p * Nat.card C) ≤ p * Nat.card (D ⊔ C : Subgroup G) := by
        calc p * (p * Nat.card C) = p ^ 2 * Nat.card C := by ring
          _ ≤ Nat.card (D ⊔ C : Subgroup G) * p := h3
          _ = p * Nat.card (D ⊔ C : Subgroup G) := by ring
      exact Nat.le_of_mul_le_mul_left this hp.pos
    exact hcount.trans h4

theorem exists_normalized_two_subgroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B D L C T : Subgroup G} (hOL : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p C) (hLC : L ≤ C)
    (hBC : B ≤ C) (hDC : D ≤ C) (hDZ : D ≤ centModSubgroup p L) (hBp : IsPGroup p B)
    (hDp : IsPGroup p D) (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hT : T ≤ L ⊔ GLAPPrimeCoreOf p C) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ⊔ D ≤ Subgroup.normalizer (U : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := GLAPPrimeCoreOf p C with hO
  have hCN : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p C
  have hLN : L ≤ Subgroup.normalizer (O : Set G) := hLC.trans hCN
  have hTN : T ≤ Subgroup.normalizer (O : Set G) :=
    hT.trans (sup_le hLN Subgroup.le_normalizer)
  have hTp : ¬ p ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  set H := O ⊔ T with hH
  have hHp : ¬ p ∣ Nat.card H :=
    not_dvd_card_sup_of_le_normalizer hp hTN (not_dvd_card_glaPPrimeCoreOf hp C) hTp
  have hBH : B ≤ Subgroup.normalizer (H : Set G) := fun b hb =>
    mem_normalizer_sup (hCN (hBC hb)) (hBT hb)
  have hDH : D ≤ Subgroup.normalizer (H : Set G) := by
    intro d hd
    apply mem_normalizer_of_conj_mem
    set K' := H.comap (MulAut.conj d).toMonoidHom with hK'
    have hmem : ∀ y, y ∈ K' ↔ d * y * d⁻¹ ∈ H := fun y => by
      simp [hK', MulAut.conj_apply]
    have hdO : ∀ o ∈ O, d * o * d⁻¹ ∈ O := fun o ho =>
      (Subgroup.mem_normalizer_iff.1 (hCN (hDC hd)) o).1 ho
    have hOK : O ≤ K' := fun y hy => (hmem y).2 (Subgroup.mem_sup_left (hdO y hy))
    have hTK : T ≤ K' := by
      intro t ht
      rw [hmem]
      have htLO : t ∈ L ⊔ O := hT ht
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L O hLN] at htLO
      obtain ⟨l, hl, o, ho, rfl⟩ := Set.mem_mul.mp htLO
      have h1 : ⁅l⁻¹, d⁆ ∈ O := hOL ((hDZ hd).2 l⁻¹ (Subgroup.inv_mem _ hl))
      have h2 : d * (l * o) * d⁻¹ = (l * o) * (o⁻¹ * ⁅l⁻¹, d⁆ * (d * o * d⁻¹)) := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ho) h1) (hdO o ho)))
    intro y hy
    exact (hmem y).1 (sup_le hOK hTK hy)
  have hEH : B ⊔ D ≤ Subgroup.normalizer (H : Set G) := sup_le hBH hDH
  have hEp : IsPGroup p (B ⊔ D : Subgroup G) := hBp.to_sup_of_normal_right' hDp hBD
  obtain ⟨S2, hS2⟩ := exists_sylow_normalized (r := 2) hEH hEp hHp
  set U := (S2 : Subgroup H).map H.subtype with hU
  have hUp : IsPGroup 2 U := S2.isPGroup'.map H.subtype
  have h2H : 2 ∣ Nat.card H := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hT1 (Subgroup.card_eq_one.1 hn)
    have h1 : 2 ∣ Nat.card T := hn ▸ dvd_pow_self 2 hn0
    exact h1.trans (Subgroup.card_dvd_of_le le_sup_right)
  have hUne : U ≠ ⊥ := by
    intro h
    apply S2.ne_bot_of_dvd_card h2H
    rw [hU] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 h
  exact ⟨U, hUne, hUp, hS2⟩

end Finite

end Prop53

section Main

open Prop53

variable {G : Type} [Group G] [Finite G]

theorem prop53 {p : ℕ} (hc : Sec5Ctx G p) (h51 : Prop51At G p) {B L : Subgroup G} {x : G}
    (hBxL : IsS0Max p B x L)
    (hT : ∃ T : Subgroup G, T ≤ L ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) ∧
      T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)) :
    CycModSylow p L := by
  classical
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨hBmax, hE, hLc⟩ := hBxL.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBxL.2.2
  have hxB : x ∈ B := hE.1
  have hx1 : x ≠ 1 := hE.2.1
  have hB : IsElemAbelian p B := hBmax.1
  have hBpg : IsPGroup p B := isPGroup_of_isElemAbelian hB
  have hxp : x ^ p = 1 := hB.2 x hxB
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  set Z := centModSubgroup p L with hZ
  have hBCx : B ≤ Cx := isElemAbelian_le_centralizer hB hxB
  have hLCx : L ≤ Cx := hLc.1
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := IsSTriple.mem_centralizer hBxL.1.1
  have hxZ : x ∈ Z := centMod_iff.1 (centMod_of_mem_centralizer hxCL)
  have key : ∀ S : Subgroup G, S ≤ Cx ⊓ Z → IsPGroup p S → IsCyclic S := by
    intro S₀ hS₀ hS₀p
    by_contra hS₀nc
    set C₀ := Cx ⊓ Z with hC₀
    have hBZ : B ≤ Subgroup.normalizer (Z : Set G) :=
      hBN.trans (normalizer_le_normalizer_centModSubgroup p L)
    have hBC₀ : B ≤ Subgroup.normalizer (C₀ : Set G) := fun b hb =>
      mem_normalizer_inf_of_mem (Subgroup.le_normalizer (hBCx hb)) (hBZ hb)
    obtain ⟨Q, hQC₀, hQp, hQi, hBQ⟩ := exists_sylow_self_normalized hp hBpg hBC₀
    have hQnc : ¬ IsCyclic Q := by
      intro hQc
      obtain ⟨w, -, hw⟩ := exists_conj_mem_of_sylow hp hS₀ hS₀p hQp hQi
      exact hS₀nc (isCyclic_of_forall_conj_mem hQc w hw)
    have hxC₀ : x ∈ C₀ := ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hxZ⟩
    have hxQ : x ∈ Q := mem_of_commute_of_sylow hp hQC₀ hQp hQi hxC₀ hxp (fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.1 (hQC₀ hq).1)
    obtain ⟨D, hDQ, hDe, hDcard, hxD, hBD, hcount⟩ :=
      exists_typePP_subgroup hp hp2 hQp hQnc hB hBQ hxQ hxB
    have hDC₀ : D ≤ C₀ := hDQ.trans hQC₀
    have hDCx : D ≤ Cx := hDC₀.trans inf_le_left
    have hDZ : D ≤ Z := hDC₀.trans inf_le_right
    have hDp : IsPGroup p D := isPGroup_of_isElemAbelian hDe
    obtain ⟨T, hTLO, hT1, hT2, hBT⟩ := hT
    obtain ⟨U, hU1, hU2, hUE⟩ := exists_normalized_two_subgroup hp hp2
      (glaPPrimeCoreOf_le_of_isSubnormal hp hLc.2.1) hLCx hBCx hDCx hDZ hBpg hDp hBD hTLO hT1 hT2
      hBT
    set Cd := B ⊓ Subgroup.centralizer (D : Set G) with hCd
    set A := D ⊔ Cd with hA
    have hAe : IsElemAbelian p A :=
      isElemAbelian_sup_of_commute hDe (isElemAbelian_mono hB inf_le_left)
        (fun d hd c hc' => Subgroup.mem_centralizer_iff.1 hc'.2 d hd)
    have hAle : A ≤ B ⊔ D := sup_le le_sup_right (inf_le_left.trans le_sup_left)
    have hAU : A ≤ Subgroup.normalizer (U : Set G) := hAle.trans hUE
    have hcardA : Nat.card B ≤ Nat.card A :=
      card_le_card_sup_inf_centralizer hp hB hDcard hcount
    have hcardA' : Nat.card A ≤ p ^ GLATwoLocalRank p G :=
      card_le_pow_glaTwoLocalRank hp hAe hU1 hU2 hAU
    have hAmax : GLAIsBmax p A := by
      refine ⟨hAe, le_antisymm hcardA' ?_, U, hU1, hU2, hAU⟩
      rw [← hBmax.2.1]
      exact hcardA
    have hxA : x ∈ A := Subgroup.mem_sup_left hxD
    have hdec : ∀ a ∈ A, ∃ u ∈ B ⊓ A, ∃ v ∈ A, CentMod p L v ∧ a = u * v := by
      intro a ha
      have hCn : Cd ≤ Subgroup.normalizer (D : Set G) :=
        inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
      rw [hA, sup_comm, ← SetLike.mem_coe,
        Subgroup.coe_mul_of_left_le_normalizer_right Cd D hCn] at ha
      obtain ⟨c', hc', d, hd, rfl⟩ := Set.mem_mul.mp ha
      exact ⟨c', ⟨hc'.1, Subgroup.mem_sup_right hc'⟩, d, Subgroup.mem_sup_left hd,
        centMod_iff.2 (hDZ hd), rfl⟩
    have h52 := lemma52 hc h51 hBxL hAmax hxA hdec
    have hDx : D ≤ Subgroup.zpowers x := fun d hd =>
      (h52 d (Subgroup.mem_sup_left hd)).1 (centMod_iff.2 (hDZ hd))
    have hcard := Subgroup.card_le_of_le hDx
    rw [hDcard, card_zpowers_eq_of_pow hp hxp hx1] at hcard
    have h2 := hp.two_le
    nlinarith
  intro S hS hSp
  exact isCyclic_of_forall_isCyclic_inf_centralizer hp hxZ hx1 hxp key
    (fun g hg => centMod_iff.1 (hS g hg)) hSp

end Main

end CFSG.LocalAnalysis.GLTheoremA
