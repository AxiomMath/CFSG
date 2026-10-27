module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageMLift
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenCanon
public import CFSG.LocalAnalysis.OddStandard.AltStdWeakSec
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootSec
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseOpen

public section

namespace CFSG.OddStandard.AltStdCycTwo.StageM

open Subgroup AltStdSec

section Norm

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G}

theorem hnorm_three_w (h : WeakShape z L n) (e : L ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 5 ≤ Sᶜ.card) :
    centralizer ({z} : Set G) ⊓ centralizer (corr (X := G) e (altSub S) : Set G) ≤
      normalizer (corr (X := G) e (altSub Sᶜ) : Set G) :=
  hnorm_of_perm_of_weakShape e (eight_le_of_cards (le_of_eq hS.symm) hSc (by omega)) h
    (altSub_le_alternatingGroup S)
    (fun σ hσ => mem_normalizer_altSub (T := Sᶜ) (fun i => by
      simpa using (mem_iff_of_centralizer_altSub_card_three hS hσ i).not))

theorem mem_centralizer_corr_of_weakShape (h : WeakShape z L n)
    (e : L ≃* alternatingGroup (Fin n)) (T : Subgroup (Equiv.Perm (Fin n))) :
    z ∈ centralizer (corr (X := G) e T : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  exact mem_centralizer_singleton_iff.1 (h.le_cent (corr_le e T hr))

end Norm

section Root

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem comm_of_mem_oddCore_root (h : WeakShape z L n) (e : L ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 5 ≤ Sᶜ.card)
    (ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G)) :
    ∀ u ∈ CFSG.oddCore ↥(centralizer (corr (X := G) e (altSub S) : Set G)),
      (⟨z, ht⟩ : ↥(centralizer (corr (X := G) e (altSub S) : Set G))) * u * ⟨z, ht⟩⁻¹ = u →
      ∀ b ∈ (corr (X := G) e (altSub Sᶜ)).subgroupOf
        (centralizer (corr (X := G) e (altSub S) : Set G)), u * b = b * u := by
  set R : Subgroup G := corr (X := G) e (altSub S) with hR
  set C : Subgroup G := centralizer (R : Set G) with hC
  set B : Subgroup G := corr (X := G) e (altSub Sᶜ) with hB
  intro u hu hzu b hb
  have hBA : B ≤ L ⊓ C := corr_le_centralizer_corr (X := G) e
    (fun g hg g' hg' => comm_of_altSub_disjoint disjoint_compl_right hg hg')
  have hBC : B ≤ C := fun b hb => (hBA hb).2
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  let eB' : B.subgroupOf C ≃* alternatingGroup (Fin Sᶜ.card) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans eB
  have hbot : B.subgroupOf C ⊓ CFSG.oddCore ↥C = ⊥ :=
    inf_oddCore_eq_bot_of_alt (by omega) eB'
  have hzu' : (⟨z, ht⟩ : ↥C) * u = u * (⟨z, ht⟩ : ↥C) := mul_inv_eq_iff_eq_mul.1 hzu
  have hut : (u : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val hzu').symm
  have hnormB : (u : G) ∈ normalizer (B : Set G) :=
    hnorm_three_w h e hS hSc (Subgroup.mem_inf.2 ⟨hut, u.2⟩)
  have hcO : u * b * u⁻¹ * b⁻¹ ∈ CFSG.oddCore ↥C := by
    have h1 : b * u⁻¹ * b⁻¹ ∈ CFSG.oddCore ↥C :=
      (inferInstance : (CFSG.oddCore ↥C).Normal).conj_mem _ (inv_mem hu) b
    have : u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) := by group
    rw [this]
    exact mul_mem hu h1
  have hcB : u * b * u⁻¹ * b⁻¹ ∈ B.subgroupOf C := by
    rw [Subgroup.mem_subgroupOf]
    have hbB : (b : G) ∈ B := hb
    have h1 : (u : G) * b * (u : G)⁻¹ ∈ B := by
      have := (mem_normalizer_iff.1 hnormB b).1 hbB
      simpa using this
    have h2 : (u : G) * b * (u : G)⁻¹ * (b : G)⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem hbB)
    simpa using h2
  have hc1 : u * b * u⁻¹ * b⁻¹ ∈ B.subgroupOf C ⊓ CFSG.oddCore ↥C := ⟨hcB, hcO⟩
  rw [hbot] at hc1
  have hc2 : u * b * u⁻¹ * b⁻¹ = 1 := hc1
  have h5 : u * b * u⁻¹ = b := mul_inv_eq_one.1 hc2
  calc u * b = (u * b * u⁻¹) * u := by group
    _ = b * u := by rw [h5]

theorem exists_canon_rootLift_w (h : WeakShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) {S : Finset (Fin n)} (hS : S.card = 3) (hIII : CaseIIIAt e z S) :
    (RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card) →
      ∃ Q : Subgroup G, CanonLift e z S Q) ∧
      ∃ ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G, IsRootLift e z S ψ := by
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
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  let eB' : B.subgroupOf C ≃* alternatingGroup (Fin Sᶜ.card) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans eB
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
  obtain ⟨Q, ψN, hQmap, -, hQbot, hQO, hQQz, hQQzbot, hψQ, hinj, hdN⟩ :=
    exists_wreath_lift_weak (O := CFSG.oddCore ↥C) (B := B.subgroupOf C) hOodd
      (z := (⟨z, ht⟩ : ↥C)) (Subtype.ext ht2) (comm_of_mem_oddCore_root h e hS hSc ht)
      (m := n - S.card) (by omega) eK hKK hSc eB' hBz hB'
  refine ⟨fun hRD => ?_, ?_⟩
  ·
    have hex : ExactShape zq (secComp e S) (n - S.card) := hRD.shape
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
      refine ⟨((ψN ⟨⟨b, hBC hb⟩, hb⟩ : ↥C) : G), ⟨_, hψQ _, rfl⟩, ?_⟩
      have := congrArg Subtype.val (hdN ⟨⟨b, hBC hb⟩, hb⟩)
      simpa using this
    · intro k P hk6 hkn hnk hPC ⟨eP⟩ hPP
      have eP' : ↥(P.subgroupOf C) ≃* alternatingGroup (Fin k) :=
        (Subgroup.subgroupOfEquivOfLe hPC).trans eP
      have hPP' : ∀ a ∈ P.subgroupOf C, ∀ b ∈ P.subgroupOf C,
          a * ((⟨z, ht⟩ : ↥C) * b * (⟨z, ht⟩ : ↥C)⁻¹) =
            ((⟨z, ht⟩ : ↥C) * b * (⟨z, ht⟩ : ↥C)⁻¹) * a := fun a ha b hb =>
        Subtype.ext (hPP (a : G) ha (b : G) hb)
      have hab := absorb_abstract hOodd (z := (⟨z, ht⟩ : ↥C)) (Subtype.ext ht2) hKc hKne hlayer
        hA' hex eK (by omega) hQmap hQO hQbot hk6 (by omega) (by omega) eP' hPP'
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
  ·
    let eBN : ↥B ≃* ↥(B.subgroupOf C) := (Subgroup.subgroupOfEquivOfLe hBC).symm
    have hcoe : ∀ b : ↥B, (((eBN b : ↥(B.subgroupOf C)) : ↥C) : G) = (b : G) := fun b => rfl
    let ψ : ↥B →* G := C.subtype.comp (ψN.comp eBN.toMonoidHom)
    have hψ : ∀ b : ↥B, ψ b = ((ψN (eBN b) : ↥C) : G) := fun b => rfl
    refine ⟨ψ, ⟨Subtype.val_injective.comp (hinj.comp eBN.injective), ?_, ?_, ?_, ?_⟩⟩
    · intro b
      have h2 := congrArg Subtype.val (hdN (eBN b))
      simpa [hψ, hcoe] using h2
    · intro a b
      have hmemx : (⟨z, ht⟩ : ↥C) * ψN (eBN b) * (⟨z, ht⟩ : ↥C)⁻¹ ∈
          zConjSub (⟨z, ht⟩ : ↥C) Q := mem_zConjSub.2 ⟨ψN (eBN b), hψQ _, rfl⟩
      have h2 := congrArg Subtype.val (hQQz (ψN (eBN a)) (hψQ _) _ hmemx)
      simpa [hψ] using h2
    · intro x hx
      have h1 : ψN (eBN x) = (⟨z, ht⟩ : ↥C) * ψN (eBN x) * (⟨z, ht⟩ : ↥C)⁻¹ := by
        apply Subtype.ext
        simpa [hψ] using hx
      have h2 : ψN (eBN x) ∈ Q ⊓ zConjSub (⟨z, ht⟩ : ↥C) Q :=
        ⟨hψQ _, mem_zConjSub.2 ⟨ψN (eBN x), hψQ _, h1.symm⟩⟩
      rw [hQQzbot] at h2
      have h3 : ψN (eBN x) = 1 := Subgroup.mem_bot.1 h2
      have h4 : eBN x = 1 := hinj (h3.trans (map_one ψN).symm)
      exact eBN.injective (h4.trans (map_one eBN).symm)
    · intro b
      exact (ψN (eBN b)).2

theorem exists_canon_w (h : WeakShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) {S : Finset (Fin n)} (hS : S.card = 3)
    (hRD : RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card))
    (hIII : CaseIIIAt e z S) : ∃ Q : Subgroup G, CanonLift e z S Q :=
  (exists_canon_rootLift_w h e hn hS hIII).1 hRD

theorem exists_rootLift_w (h : WeakShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) {S : Finset (Fin n)} (hS : S.card = 3) (hIII : CaseIIIAt e z S) :
    ∃ ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G, IsRootLift e z S ψ :=
  (exists_canon_rootLift_w h e hn hS hIII).2

end Root

end CFSG.OddStandard.AltStdCycTwo.StageM
