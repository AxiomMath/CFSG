module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264Aux
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I264
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open scoped Pointwise

@[expose] def KD264K (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K →
    CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) →
    GLAPPrimeCore p ↥K = ⊥ → fullCoverLevel p ↥K = 4 →
    IsElemAbelian p B → K ⊔ B = ⊤ → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    (∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) ∨
      (p = 3 ∧ Nat.card B = 3 ^ 4 ∧ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 ∧
        catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie isTrialityD4Big) ∧
        ∃ b ∈ B, ¬ InducesInnerMod 3 K b)

theorem i264At_of_K {G : Type} [Group G] [Finite G] {p : ℕ} (h : KD264K p) : I264At G p := by
  unfold I264At
  intro hp _hp2 B x L hBab hxB hx1 hL hKG hBN hpB hmax hlev
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hBab
  set M : Subgroup G := L ⊔ B with hM
  have hLM : L ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  haveI hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hMN
  have hsn : IsSubnormal L M := IsSubnormal.step hLM hLn (IsSubnormal.refl M)
  have hOL : GLAPPrimeCoreOf p M ≤ L := ys03_glaPPrimeCoreOf_sup_le hp hBp hBN
  have hLC : ∀ l ∈ L, x * l = l * x := fun l hl =>
    Subgroup.mem_centralizer_iff.1 (hL.1 hl) x (Set.mem_singleton x)
  have hxM : x ∈ M := hBM hxB
  have hxB' : x ∈ B := hxB
  have eK : ↥(barX p M L) ≃* (↥L ⧸ GLAPPrimeCore p ↥L) := (quotEquivBarX hp hLM hsn).symm
  have hKq : CFSG.Open.IsQuasisimple ↥(barX p M L) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm
      (isQuasisimple_pQuot_of_glaPComponent hp hL)
  have hKcore : GLAPPrimeCore p ↥(barX p M L) = ⊥ := by
    have h1 := glaPPrimeCore_map_iso p eK
    rw [ys03_glaPPrimeCore_quot_eq_bot hp ↥L] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).1 h1
  have hKlev : fullCoverLevel p ↥(barX p M L) = 4 := by
    rw [fullCoverLevel_congr eK]
    exact hlev
  have hKn : (barX p M L).Normal := by
    show ((L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).Normal
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hBab' : IsElemAbelian p (barX p M B) := isElemAbelian_barX hBab
  have hsup : barX p M L ⊔ barX p M B = ⊤ := by
    show (L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) ⊔
      (B.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) = ⊤
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLM hBM]
    have htop : (L ⊔ B).subgroupOf M = ⊤ := by
      rw [← hM, Subgroup.subgroupOf_self]
    rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hpow : p ^ 4 ≤ Nat.card (barX p M B) := by
    rw [ys03_card_barX_of_isPGroup hp hBp hBM]
    exact hpB
  have hcop : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hmaxY : IsMaxRankIn p (barX p M B) ⊤ := by
    intro E _ hE
    obtain ⟨S, hS, hSE, hSc⟩ := exists_elemAbelian_lift (GLAPPrimeCore p ↥M) hcop hE
    have hS0 : IsElemAbelian p (S.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hS _
    have hle := hmax (S.map M.subtype) (Subgroup.map_subtype_le S) hS0
    have hc1 : Nat.card (S.map M.subtype) = Nat.card S :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [ys03_card_barX_of_isPGroup hp hBp hBM]
    have : Nat.card E = Nat.card S := hSc.symm
    omega
  have hxbar_ne : ys03_qMap p M ⟨x, hxM⟩ ≠ 1 := by
    intro h1
    have hinj := injective_barX_comp hp hBp hBM
    have h2 : ((QuotientGroup.mk' (GLAPPrimeCore p ↥M)).comp (B.subgroupOf M).subtype)
        ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hxB'⟩ =
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥M)).comp (B.subgroupOf M).subtype) 1 := by
      show ys03_qMap p M ⟨x, hxM⟩ = ys03_qMap p M 1
      rw [h1, map_one]
    have h3 : (⟨x, hxM⟩ : ↥M) = 1 := congrArg Subtype.val (hinj h2)
    exact hx1 (congrArg Subtype.val h3)
  have hxC : ys03_qMap p M ⟨x, hxM⟩ ∈ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) :=
    Subgroup.mem_centralizer_iff.2 (by
      rintro w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
      have hlx : (u : G) * x = x * (u : G) := (hLC (u : G) (Subgroup.mem_subgroupOf.1 hu)).symm
      rw [← map_mul, ← map_mul]
      exact congrArg (ys03_qMap p M) (Subtype.ext hlx))
  have hxbar_mem : ys03_qMap p M ⟨x, hxM⟩ ∈ barX p M B ⊓ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) :=
    ⟨Subgroup.mem_map.2 ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hxB', rfl⟩, hxC⟩
  have hcent : barX p M B ⊓ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) ≠ ⊥ := by
    intro hbot
    apply hxbar_ne
    have hmem := hxbar_mem
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  let φ : ↥L →* ↥(barX p M L) :=
    eK.symm.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))
  have hφ : Function.Surjective φ :=
    eK.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hKGroup : CFSG.Open.IsKGroup ↥(barX p M L) := hKG.of_surjective φ hφ
  have hKhat : CFSG.Open.IsCatalogGroup (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) := by
    haveI : IsSimpleGroup (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) := hKq.2
    let ψ : ↥L →* ↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L) :=
      (QuotientGroup.mk' (Subgroup.center ↥(barX p M L))).comp φ
    have hψ : Function.Surjective ψ :=
      (QuotientGroup.mk'_surjective _).comp hφ
    exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isCatalogGroup_of_isKGroup_of_surjective hKG ⊤
      (exists_noncomm_of_isQuasisimple hKq) (ψ.comp (Subgroup.subtype ⊤))
      (hψ.comp (fun l => ⟨⟨l, Subgroup.mem_top l⟩, rfl⟩))
  rcases h (PQuot p M) (barX p M L) (barX p M B) hKn hKq hKGroup hKhat hKcore hKlev hBab' hsup hpow hmaxY
    hcent with
    ⟨E'', hE''B, _hE''ab, hE''card, hE''layer⟩ | ⟨h3, hBcard, hcentcard, hcat, bb, hbbB, hbb⟩
  ·
    left
    obtain ⟨E, hEB, hEq, -⟩ := exists_le_barX_eq hp hBp hBM hE''B
    have hEM : E ≤ M := hEB.trans hBM
    have hEp : IsPGroup p E := hBp.to_le hEB
    have hEcard : Nat.card E = p ^ 3 := by
      rw [← ys03_card_barX_of_isPGroup hp hEp hEM, hEq]
      exact hE''card
    have hcE := ys03_barX_inf_centralizer_eq hp hLM hEM hEp hOL
    rw [hEq] at hcE
    obtain ⟨J', hJ', hJ'ne⟩ := ys03_exists_component_ne_bot hE''layer
    rw [← hcE] at hJ'
    obtain ⟨K₂, hK₂, hK₂J⟩ := exists_glaPComponent_map_eq hp (ys03_qMap p M)
      (ys03_coprime_inf_ker_qMap hp ((L ⊓ Subgroup.centralizer (E : Set G)).subgroupOf M)) hJ'
    have hkerM : Nat.Coprime p (Nat.card ↥((L ⊓ Subgroup.centralizer (E : Set G)).subgroupOf M ⊓
        M.subtype.ker)) := by
      rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have hK₂G := glaPComponent_map hp M.subtype hkerM hK₂
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (inf_le_left.trans hLM)] at hK₂G
    have hK₂ne : K₂ ≠ ⊥ := by
      rintro rfl
      apply hJ'ne
      rw [← hK₂J, Subgroup.map_bot]
    have hK₂G_ne : K₂.map M.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
      exact hK₂ne
    unfold IsGB
    refine ⟨E, hEB, isElemAbelian_mono hBab hEB, hEcard, hEB.trans hBN, ?_⟩
    intro hbot
    have hle : K₂.map M.subtype ≤ GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) :=
      le_sSup hK₂G
    rw [hbot] at hle
    exact hK₂G_ne (le_bot_iff.1 hle)
  ·
    right
    subst h3
    have hx3 : x ^ 3 = 1 := hBab.2 x hxB
    have hZ : Subgroup.zpowers (ys03_qMap 3 M ⟨x, hxM⟩) =
        barX 3 M B ⊓ Subgroup.centralizer ((barX 3 M L : Subgroup (PQuot 3 M)) :
          Set (PQuot 3 M)) := by
      have hord : orderOf (ys03_qMap 3 M ⟨x, hxM⟩) = 3 := by
        apply orderOf_eq_prime
        · rw [← map_pow]
          have h1 : (⟨x, hxM⟩ : ↥M) ^ 3 = 1 := Subtype.ext hx3
          rw [h1, map_one]
        · exact hxbar_ne
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.2 hxbar_mem
      · rw [hcentcard, Nat.card_zpowers, hord]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [← ys03_card_barX_of_isPGroup hp hBp hBM]
      exact hBcard
    · intro b hb
      have hbM : b ∈ M := hBM hb
      rw [ys03_centMod_iff_qMap hp hLM hMN hsn hbM]
      constructor
      · intro hC
        have hmem : ys03_qMap 3 M ⟨b, hbM⟩ ∈ barX 3 M B ⊓ Subgroup.centralizer
            ((barX 3 M L : Subgroup (PQuot 3 M)) : Set (PQuot 3 M)) :=
          ⟨Subgroup.mem_map.2 ⟨⟨b, hbM⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩, hC⟩
        rw [← hZ] at hmem
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
        have hxn : x ^ n ∈ B := B.zpow_mem hxB n
        have hxnM : x ^ n ∈ M := M.zpow_mem hxM n
        have hinj := injective_barX_comp hp hBp hBM
        have h2 : ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (B.subgroupOf M).subtype)
            ⟨⟨x ^ n, hxnM⟩, Subgroup.mem_subgroupOf.2 hxn⟩ =
            ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (B.subgroupOf M).subtype)
              ⟨⟨b, hbM⟩, Subgroup.mem_subgroupOf.2 hb⟩ := by
          show ys03_qMap 3 M ⟨x ^ n, hxnM⟩ = ys03_qMap 3 M ⟨b, hbM⟩
          rw [← hn, ← map_zpow]
          congr 1
        have h3 : (⟨x ^ n, hxnM⟩ : ↥M) = ⟨b, hbM⟩ := congrArg Subtype.val (hinj h2)
        exact Subgroup.mem_zpowers_iff.2 ⟨n, congrArg Subtype.val h3⟩
      · intro hb'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
        have hxnM : x ^ n ∈ M := M.zpow_mem hxM n
        have heq : ys03_qMap 3 M ⟨x ^ n, hxnM⟩ = (ys03_qMap 3 M ⟨x, hxM⟩) ^ n := by
          rw [← map_zpow]
          congr 1
        rw [heq]
        exact (Subgroup.centralizer _).zpow_mem hxC n
    · exact ys03_catalogIs_of_mulEquiv (QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)) hcat
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hbbB
      refine ⟨(u : G), Subgroup.mem_subgroupOf.1 hu, ?_⟩
      intro hind
      apply hbb
      obtain ⟨l, hl, hlall⟩ := hind
      refine ⟨ys03_qMap 3 M ⟨l, hLM hl⟩,
        Subgroup.mem_map.2 ⟨⟨l, hLM hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩, ?_⟩
      intro y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
      have hy'L : (y' : G) ∈ L := Subgroup.mem_subgroupOf.1 hy'
      have hw := hlall (y' : G) hy'L
      obtain ⟨W, hWdef⟩ : ∃ W : ↥M, W = ((⟨l, hLM hl⟩ : ↥M)⁻¹ * y' * (⟨l, hLM hl⟩ : ↥M))⁻¹ *
          (u⁻¹ * y' * u) := ⟨_, rfl⟩
      have hWval : (W : G) = ((l : G)⁻¹ * (y' : G) * (l : G))⁻¹ *
          ((u : G)⁻¹ * (y' : G) * (u : G)) := by
        rw [hWdef]
        simp
      have hWO : (W : G) ∈ GLAPPrimeCoreOf 3 M := by
        rw [hWval]
        exact glaPPrimeCoreOf_le_of_isSubnormal hp hsn hw
      have hqW : ys03_qMap 3 M W = 1 := (ys03_mem_primeCoreOf_iff_qMap W.2).1 hWO
      have heq : ((ys03_qMap 3 M ⟨l, hLM hl⟩)⁻¹ * ys03_qMap 3 M y' * ys03_qMap 3 M ⟨l, hLM hl⟩)⁻¹ *
          ((ys03_qMap 3 M u)⁻¹ * ys03_qMap 3 M y' * ys03_qMap 3 M u) = ys03_qMap 3 M W := by
        rw [hWdef]
        simp only [map_mul, map_inv]
      rw [heq, hqW]
      exact one_mem _

end CFSG.LocalAnalysis.GLTheoremA
