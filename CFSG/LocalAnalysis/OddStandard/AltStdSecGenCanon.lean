module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenCase
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenAbsorb

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Canon

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G}

structure CanonLift (e : L ≃* alternatingGroup (Fin n)) (z : G) (S : Finset (Fin n))
    (Q : Subgroup G) : Prop where
  le_cent : Q ≤ centralizer (corr (X := G) e (altSub S) : Set G)
  comm : ∀ a ∈ Q, ∀ b ∈ Q, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a
  inf : ∀ x ∈ Q, x ∈ Q.map (MulAut.conj z).toMonoidHom → x = 1
  cover : ∀ b ∈ corr (X := G) e (altSub Sᶜ), ∃ q ∈ Q, q * (z * q * z⁻¹) = b
  absorb : ∀ (k : ℕ) (P : Subgroup G), 5 ≤ k → k ≤ n - 3 → n - 3 ≤ k + 3 →
    P ≤ centralizer (corr (X := G) e (altSub S) : Set G) →
    Nonempty (↥P ≃* alternatingGroup (Fin k)) →
    (∀ a ∈ P, ∀ b ∈ P, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) →
    P ≤ Q ∨ P ≤ Q.map (MulAut.conj z).toMonoidHom

theorem exists_canon [Finite G] (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) {S : Finset (Fin n)} (hS : S.card = 3) (hIII : CaseIIIAt e z S) :
    ∃ Q : Subgroup G, CanonLift e z S Q := by
  obtain ⟨ht, K, hKc, hKne, hlayer, ⟨eK⟩, hdiag⟩ := hIII
  set R : Subgroup G := corr (X := G) e (altSub S) with hR
  set C : Subgroup G := centralizer (R : Set G) with hC
  set B : Subgroup G := corr (X := G) e (altSub Sᶜ) with hB
  have hSc : 5 ≤ Sᶜ.card := by rw [card_compl_fin, hS]; omega
  have hBA : B ≤ L ⊓ C := corr_le_centralizer_corr (X := G) e
    (fun g hg g' hg' => comm_of_altSub_disjoint disjoint_compl_right hg hg')
  have hBC : B ≤ C := fun b hb => (hBA hb).2
  have hBL : B ≤ L := fun b hb => (hBA hb).1
  have hOodd : Odd (Nat.card (CFSG.oddCore ↥C)) :=
    ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore ↥C
  have ht2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.order, pow_two] at this
  have hRO : R.subgroupOf C ≤ CFSG.oddCore ↥C := by
    intro x hx
    have hxR : (x : G) ∈ R := hx
    obtain ⟨y, hy, hyx⟩ := corr_altSub_le_oddCoreOf (X := G) e hS hxR
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hRc : R.subgroupOf C ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (mem_centralizer_iff.1 g.2 (x : G) hx).symm
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  let eB' : B.subgroupOf C ≃* alternatingGroup (Fin Sᶜ.card) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans eB
  have hBperf : ⁅B.subgroupOf C, B.subgroupOf C⁆ = B.subgroupOf C :=
    Subgroup.isPerfect_iff.1 ⟨(isQuasisimple_of_alt hSc eB').1⟩
  have hBz : ∀ b ∈ B.subgroupOf C, (⟨z, ht⟩ : ↥C) * b * (⟨z, ht⟩ : ↥C)⁻¹ = b := by
    intro b hb
    have hbL : (b : G) ∈ L := hBL hb
    have h1 : (b : G) * z = z * b :=
      mem_centralizer_singleton_iff.1 (h.le_cent hbL)
    have : (⟨z, ht⟩ : ↥C) * b = b * (⟨z, ht⟩ : ↥C) := Subtype.ext h1.symm
    rw [this]; group
  set zq : Sec G R := QuotientGroup.mk (⟨z, ht⟩ : ↥C) with hzq
  have hKK : ∀ a ∈ K, ∀ b ∈ K, a * (zq * b * zq⁻¹) = (zq * b * zq⁻¹) * a := by
    have hK'c : CFSG.IsComponent (K.map (MulAut.conj zq).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj zq) hKc
    rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with h1 | h1
    · exact absurd h1.symm hKne
    · intro a ha b hb
      have h2 : a * (zq * b * zq⁻¹) * a⁻¹ * (zq * b * zq⁻¹)⁻¹ ∈
          ⁅K, K.map (MulAut.conj zq).toMonoidHom⁆ := by
        have := Subgroup.commutator_mem_commutator ha
          (show zq * b * zq⁻¹ ∈ K.map (MulAut.conj zq).toMonoidHom from ⟨b, hb, by simp⟩)
        simpa [commutatorElement_def] using this
      rw [h1] at h2
      have h3 : a * (zq * b * zq⁻¹) * a⁻¹ * (zq * b * zq⁻¹)⁻¹ = 1 := h2
      calc a * (zq * b * zq⁻¹) = (a * (zq * b * zq⁻¹) * a⁻¹ * (zq * b * zq⁻¹)⁻¹) *
            ((zq * b * zq⁻¹) * a) := by group
        _ = (zq * b * zq⁻¹) * a := by rw [h3, one_mul]
  have hB' : ∀ g : Sec G R, g ∈ (B.subgroupOf C).map (QuotientGroup.mk' (CFSG.oddCore ↥C)) ↔
      ∃ k ∈ K, g = k * (zq * k * zq⁻¹) := by
    intro g
    have := Set.ext_iff.1 hdiag g
    simpa [secComp] using this
  obtain ⟨Q, ψN, hQmap, hQperf, hQbot, hQO, hQQz, hQQzbot, hψQ, hinj, hdN⟩ :=
    exists_wreath_lift (O := CFSG.oddCore ↥C) (R := R.subgroupOf C) (B := B.subgroupOf C)
      hOodd hRO hRc (z := (⟨z, ht⟩ : ↥C)) (Subtype.ext ht2) (fun u hu hzu =>
        centralizer_oddCore_le_root h e hS hSc ht u hu hzu)
      (m := n - S.card) (by omega) eK hKK hBperf hBz hB'
  have hex := exactShape_section_three h e hS (by omega : 5 ≤ n - S.card) ht
  have hA' : secComp e S ≤ K ⊔ K.map (MulAut.conj zq).toMonoidHom := by
    intro x hx
    have hx' : x ∈ (secComp e S : Set (Sec G R)) := hx
    rw [hdiag] at hx'
    obtain ⟨k, hk, rfl⟩ := hx'
    exact mul_mem (mem_sup_left hk) (mem_sup_right ⟨k, hk, by simp⟩)
  refine ⟨Q.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨q, _, rfl⟩
    exact q.2
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hmemx : (⟨z, ht⟩ : ↥C) * b * (⟨z, ht⟩ : ↥C)⁻¹ ∈ zConjSub (⟨z, ht⟩ : ↥C) Q :=
      mem_zConjSub.2 ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hQQz a ha _ hmemx)
  · rintro _ ⟨q, hq, rfl⟩ ⟨_, ⟨q', hq', rfl⟩, hqq⟩
    have hqq' : (z * (q' : G) * z⁻¹ : G) = (q : G) := hqq
    have hmem : q ∈ Q ⊓ zConjSub (⟨z, ht⟩ : ↥C) Q :=
      ⟨hq, mem_zConjSub.2 ⟨q', hq', Subtype.ext hqq'⟩⟩
    rw [hQQzbot] at hmem
    have : q = 1 := hmem
    simp [this]
  · intro b hb
    have hbb : (⟨⟨b, hBC hb⟩, hb⟩ : ↥(B.subgroupOf C)) = (⟨⟨b, hBC hb⟩, hb⟩ : ↥(B.subgroupOf C)) :=
      rfl
    refine ⟨((ψN ⟨⟨b, hBC hb⟩, hb⟩ : ↥C) : G), ⟨_, hψQ _, rfl⟩, ?_⟩
    have := congrArg Subtype.val (hdN ⟨⟨b, hBC hb⟩, hb⟩)
    simpa using this
  · intro k P hk6 hkn hnk hPC ⟨eP⟩ hPP
    have hm : n - S.card = n - 3 := by rw [hS]
    have eP' : ↥(P.subgroupOf C) ≃* alternatingGroup (Fin k) :=
      (Subgroup.subgroupOfEquivOfLe hPC).trans eP
    have hPP' : ∀ a ∈ P.subgroupOf C, ∀ b ∈ P.subgroupOf C,
        a * ((⟨z, ht⟩ : ↥C) * b * (⟨z, ht⟩ : ↥C)⁻¹) =
          ((⟨z, ht⟩ : ↥C) * b * (⟨z, ht⟩ : ↥C)⁻¹) * a := fun a ha b hb =>
      Subtype.ext (hPP (a : G) ha (b : G) hb)
    have hab := absorb_abstract hOodd (z := (⟨z, ht⟩ : ↥C)) (Subtype.ext ht2) hKc hKne hlayer hA'
      hex eK (by omega) hQmap hQO hQbot hk6 (by omega) (by omega) eP' hPP'
    rcases hab with hl | hr
    · left
      intro x hx
      exact ⟨⟨x, hPC hx⟩, hl hx, rfl⟩
    · right
      intro x hx
      obtain ⟨q, hq, hqx⟩ := hr (show (⟨x, hPC hx⟩ : ↥C) ∈ P.subgroupOf C from hx)
      refine ⟨(q : G), ⟨q, hq, rfl⟩, ?_⟩
      have := congrArg Subtype.val hqx
      simpa using this

end Canon

end CFSG.OddStandard.AltStdSec
