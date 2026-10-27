module

public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Conj

variable {G : Type*} [Group G] [Finite G]

theorem inf_glaPPrimeCoreOf_le {p : ℕ} (hp : p.Prime) {H A : Subgroup G} (hHA : H ≤ A) :
    H ⊓ GLAPPrimeCoreOf p A ≤ GLAPPrimeCoreOf p H := by
  set O := GLAPPrimeCoreOf p A with hO
  set N0 : Subgroup ↥H := O.subgroupOf H with hN0
  have hnorm : N0.Normal := by
    refine ⟨fun n hn h' => ?_⟩
    show ((h' * n * h'⁻¹ : ↥H) : G) ∈ O
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p A (hHA h'.2)) (n : G)).1 hn
    simpa using this
  have hdvd : Nat.card N0 ∣ Nat.card O := by
    have h1 : N0.map H.subtype = H ⊓ O := by
      rw [hN0, ← Subgroup.inf_subgroupOf_right O H]
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : O ⊓ H ≤ H)]
      exact inf_comm _ _
    have h2 : Nat.card (N0.map H.subtype) = Nat.card N0 :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h2, h1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime p (Nat.card N0) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf hp A (hd.trans hdvd)
  have hle : N0 ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx.2), rfl⟩

omit [Finite G] in
theorem barX_gLBConj_eq (p : ℕ) {M : Subgroup G} {g : G} (hg : g ∈ M) (K : Subgroup G) :
    barX p M (GLBConj g K) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) (barX p M K) := by
  refine le_antisymm (barX_le_gLBConj p hg K) ?_
  have h := barX_le_gLBConj p (M.inv_mem hg) (GLBConj g K)
  rw [gLBConj_inv_gLBConj] at h
  have h2 := gLBConj_mono (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩) h
  have e : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨g⁻¹, M.inv_mem hg⟩ : ↥M) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, gLBConj_gLBConj_inv] at h2
  exact h2

theorem barX_eq_of_barX_eq {p : ℕ} (hp : p.Prime) {M A K₁ K₂ : Subgroup G} (hAM : A ≤ M)
    (h₁ : K₁ ≤ A) (h₂ : K₂ ≤ A) (h : barX p M K₁ = barX p M K₂) :
    barX p A K₁ = barX p A K₂ := by
  have key : ∀ {J K : Subgroup G}, J ≤ A → K ≤ A → barX p M K ≤ barX p M J →
      barX p A K ≤ barX p A J := by
    intro J K hJ hK hle
    refine barX_le_of_forall hJ fun k hk => ?_
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) hle hk (hAM (hK hk))
    exact ⟨j, hj, inf_glaPPrimeCoreOf_le hp hAM
      ⟨A.mul_mem (A.inv_mem (hJ hj)) (hK hk), hjk⟩⟩
  exact le_antisymm (key h₂ h₁ h.le) (key h₁ h₂ h.ge)

theorem gLBConj_eq_of_barX_eq {p : ℕ} (hp : p.Prime) {M A K : Subgroup G} (hAM : A ≤ M)
    (hK : GLAPComponent p A K) {g : G} (hgM : g ∈ M) (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (h : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩) (barX p M K) =
      barX p M K) : GLBConj g K = K := by
  have hK' : GLAPComponent p A (GLBConj g K) := by
    have := glaPComponent_gLBConj hK g
    rwa [mem_normalizer_iff_gLBConj_eq.1 hgA] at this
  have hbar : barX p M (GLBConj g K) = barX p M K := by
    rw [barX_gLBConj_eq p hgM K]
    exact h
  exact glaPComponent_unique hK' hK (barX_eq_of_barX_eq hp hAM hK'.1 hK.1 hbar)

theorem mem_normalizer_of_barX_normalizes {p : ℕ} (hp : p.Prime) {M A K : Subgroup G}
    (hAM : A ≤ M) (hK : GLAPComponent p A K) {g : G} (hgM : g ∈ M)
    (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer ((barX p M K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    g ∈ Subgroup.normalizer (K : Set G) :=
  mem_normalizer_iff_gLBConj_eq.2
    (gLBConj_eq_of_barX_eq hp hAM hK hgM hgA (mem_normalizer_iff_gLBConj_eq.1 h))

end Conj

section Setting

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem isTwoLocal_ne_top (hSt : GLStanding G m p) {M : Subgroup G} (hM : IsTwoLocal M) :
    M ≠ ⊤ := by
  obtain ⟨P, hP, hP2, rfl⟩ := hM
  intro htop
  have := hSt.simple
  have hn : P.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact hP h
  · rw [h] at hP2
    have hG2 : IsPGroup 2 G := hP2.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hSt.nonabelian
    have : Nontrivial G := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc := hG2.center_nontrivial
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h0 | h0
    · obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center G))
      rw [h0, Subgroup.mem_bot] at hz
      exact hz1 (Subtype.ext hz)
    · exact hab (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b : b ∈ Subgroup.center G) a)

theorem pRank_le_glaTwoLocalRank {X : Type*} [Group X] [Finite X] {q : ℕ} (hq : 1 < q)
    {H : Subgroup X} (hH : IsTwoLocal H) : CFSG.Open.pRank q H ≤ GLATwoLocalRank q X := by
  have hbdd : BddAbove {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank q H = k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank hq H
    have h1 : CFSG.Open.pRank q H < q ^ CFSG.Open.pRank q H := Nat.lt_pow_self hq
    have h2 : q ^ CFSG.Open.pRank q H ≤ Nat.card X := hE ▸ Subgroup.card_le_card_group E
    change CFSG.Open.pRank q H ≤ Nat.card X
    omega
  exact le_csSup hbdd ⟨H, hH, rfl⟩

theorem glaIsBmax_subgroupOf (hSt : GLStanding G m p) {B M : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsTwoLocal M) (hBM : B ≤ M) : GLAIsBmax p (B.subgroupOf M) := by
  have hp := hSt.prime
  have hBel : IsElemAbelian p (B.subgroupOf M) := isElemAbelian_subgroupOf hB.1.1 M
  obtain ⟨P, hP, hP2, hPle⟩ := exists_ne_bot_le_pCoreOf hM
  set U : Subgroup ↥M := (pCoreOf 2 M).subgroupOf M with hU
  have hOM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hUne : U ≠ ⊥ := by
    intro h0
    apply hP
    have h1 : (pCoreOf 2 M).subgroupOf M = ⊥ := h0
    have h2 : (pCoreOf 2 M) = ⊥ := by
      have := congrArg (Subgroup.map M.subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le hOM, Subgroup.map_bot] at this
    exact eq_bot_iff.2 (hPle.trans h2.le)
  have hU2 : IsPGroup 2 U :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_equiv (Subgroup.subgroupOfEquivOfLe hOM).symm
  have hBU : B.subgroupOf M ≤ Subgroup.normalizer (U : Set ↥M) := by
    rw [hU, normalizer_subgroupOf_eq hOM]
    intro b _
    exact (Subgroup.mem_subgroupOf).2 (le_normalizer_pCoreOf 2 M b.2)
  have hcard : Nat.card (B.subgroupOf M) = p ^ m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv]
    exact hSt.card_eq hB
  have hrank : GLATwoLocalRank p ↥M = m := by
    refine le_antisymm ?_ ?_
    · exact (glaTwoLocalRank_subgroup_le hp.one_lt M).trans hSt.rank_eq.le
    · calc m ≤ CFSG.Open.pRank p (B.subgroupOf M) :=
            CFSG.SectionRank.le_pRank hp.one_lt le_rfl hBel hcard
        _ ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set ↥M)) :=
            CFSG.SectionRank.pRank_mono hp.one_lt hBU
        _ ≤ GLATwoLocalRank p ↥M :=
            pRank_le_glaTwoLocalRank hp.one_lt ⟨U, hUne, hU2, rfl⟩
  exact ⟨hBel, by rw [hcard, hrank], ⟨U, hUne, hU2, hBU⟩⟩

end Setting

section Block

variable {G : Type*} [Group G] [Finite G]

theorem glaPPrimeCore_eq_pCore_two_of_block {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) :
    GLAPPrimeCore p ↥L = CFSG.pCore 2 ↥L := by
  set Q := ↥L ⧸ GLAPPrimeCore p ↥L with hQ
  have hQq : CFSG.Open.IsQuasisimple Q :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp hL.1 hL.2.1).symm hL.2.2.1.2.2
  have hnt : Nontrivial Q := by
    have h1 : Nontrivial (Q ⧸ Subgroup.center Q) := hQq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have hle : CFSG.pCore 2 ↥L ≤ GLAPPrimeCore p ↥L := by
    have h := pCoreOf_two_le_glaPPrimeCoreOf hp hp2 L
    unfold pCoreOf GLAPPrimeCoreOf at h
    exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 h
  let f : (↥L ⧸ CFSG.pCore 2 ↥L) →* Q :=
    QuotientGroup.map (CFSG.pCore 2 ↥L) (GLAPPrimeCore p ↥L) (MonoidHom.id _) hle
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := hbl.simple
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton Q := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hf a
        obtain ⟨y, rfl⟩ := hf b
        have hx : x ∈ f.ker := h ▸ Subgroup.mem_top x
        have hy : y ∈ f.ker := h ▸ Subgroup.mem_top y
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]⟩
      exact not_subsingleton Q hsub
  refine le_antisymm (fun x hx => ?_) hle
  have h1 : f (QuotientGroup.mk x) = 1 := (QuotientGroup.eq_one_iff x).2 hx
  exact (QuotientGroup.eq_one_iff x).1 (hinj (h1.trans (map_one f).symm))

theorem isPGroup_two_inf_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) : IsPGroup 2 ↥(L ⊓ GLAPPrimeCoreOf p M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le ?_
  refine (inf_glaPPrimeCoreOf_le hp hL.1).trans ?_
  unfold GLAPPrimeCoreOf pCoreOf
  rw [glaPPrimeCore_eq_pCore_two_of_block hp hp2 hL hbl]

theorem center_quotient_eq_bot_of_block {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) :
    Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) = ⊥ := by
  set Q := ↥L ⧸ GLAPPrimeCore p ↥L with hQ
  have hQq : CFSG.Open.IsQuasisimple Q :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp hL.1 hL.2.1).symm hL.2.2.1.2.2
  have e : Q ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two_of_block hp hp2 hL hbl)
  have hQs : IsSimpleGroup Q := e.isSimpleGroup_congr.2 hbl.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative Q := Subgroup.center_eq_top_iff.1 h
    have hperf : Group.IsPerfect Q := ⟨hQq.1⟩
    have : Subsingleton Q := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact not_subsingleton Q this

end Block

end CFSG.LocalAnalysis.GLTheoremB
