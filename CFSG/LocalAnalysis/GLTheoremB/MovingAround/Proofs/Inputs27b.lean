module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs27
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvCore
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6GInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs27b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs27
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

section I275Deep

variable {X : Type} [Group X] [Finite X]

theorem glaPPrimeCoreOf_eq_bot_of_comp (hO : GLAPPrimeCore 3 X = ⊥) {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) : GLAPPrimeCoreOf 3 K = ⊥ := by
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  show (GLAPPrimeCore 3 ↥K).map K.subtype = ⊥
  rw [hOK, Subgroup.map_bot]

theorem mem_centralizer_of_barAut_eq_one {K : Subgroup X} (hOK : GLAPPrimeCoreOf 3 K = ⊥)
    (g : ↥(Subgroup.normalizer (K : Set X))) (hg : barAut 3 K g = 1) :
    (g : X) ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := Lemma1315b.mem_primeCoreOf_of_barAut_eq_one g hg hx
  rw [hOK, Subgroup.mem_bot] at h
  have h2 : (g : X) * x * (g : X)⁻¹ = x := by
    have := inv_mul_eq_one.1 h
    exact this.symm
  calc x * (g : X) = (g : X) * x * (g : X)⁻¹ * (g : X) := by rw [h2]
    _ = (g : X) * x := by group

theorem isElemAbelian_zpowers_of_mem {p : ℕ} {B : Subgroup X} (hB : IsElemAbelian p B) {b : X}
    (hb : b ∈ B) : IsElemAbelian p (Subgroup.zpowers b) :=
  CFSG.Open.IsElemAbelian.mono hB (Subgroup.zpowers_le.2 hb)

theorem isElemAbelian_autBar {B : Subgroup X} (hB : IsElemAbelian 3 B) (K : Subgroup X) :
    IsElemAbelian 3 (autBar 3 B K) :=
  CFSG.SectionRank.isElemAbelian_map (Inputs27.isElemAbelian_subgroupOf
    (CFSG.Open.IsElemAbelian.mono hB inf_le_left) _) _

theorem card_autBar_of_faithful (hO : GLAPPrimeCore 3 X = ⊥) {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) :
    Nat.card (autBar 3 B K) = Nat.card B := by
  have hOK := glaPPrimeCoreOf_eq_bot_of_comp hO hK
  have hkerB : CFSG.HardMathSupport.Solomon.LocalBalance.kerB 3 B K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxB, hxc⟩ := Subgroup.mem_inf.1 hx
    have h1 := (CFSG.HardMathSupport.Solomon.Coordinator.mem_centralizerQuot_iff_barAut_eq_one 3
      (⟨x, hN hxB⟩ : ↥(Subgroup.normalizer (K : Set X)))).1 hxc
    exact hC x hxB (mem_centralizer_of_barAut_eq_one hOK _ h1)
  have hBeq : autBar 3 B K = (B.subgroupOf (Subgroup.normalizer (K : Set X))).map (barAut 3 K) := by
    unfold autBar
    rw [inf_eq_left.2 hN]
  rw [hBeq, CFSG.HardMathSupport.Solomon.Coordinator.card_map_barAut hN hkerB]

theorem deltaImage_facts (hO : GLAPPrimeCore 3 X = ⊥) {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) {b : X} (hbB : b ∈ B) (hb1 : b ≠ 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn 3 1 (autBar 3 B K)
        (autBar 3 (Subgroup.zpowers b) K) ∧
      autBar 3 B K ≤ Subgroup.normalizer ((innerAut (barOf 3 K) ⊔
        Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers b) K : Subgroup (MulAut (barOf 3 K))) :
          Set (MulAut (barOf 3 K))) ∧
      Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers b) K ≤
        localDeltaTwoIn (innerAut (barOf 3 K) ⊔ Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers b) K)
          (autBar 3 (Subgroup.zpowers b) K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup X := Subgroup.zpowers b with hDdef
  have hDB : D ≤ B := Subgroup.zpowers_le.2 hbB
  have hDel : IsElemAbelian 3 D := isElemAbelian_zpowers_of_mem hB hbB
  have hDN : D ≤ Subgroup.normalizer (K : Set X) := hDB.trans hN
  set W : Subgroup (MulAut (barOf 3 K)) := Lemma123.DeltaImage 3 ⊤ D K with hWdef
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hDc : Nat.card D = 3 := by
    rw [hDdef, Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hE1 : CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn 3 1 (autBar 3 B K) (autBar 3 D K) := by
    refine ⟨?_, isElemAbelian_autBar hDel K, ?_⟩
    · unfold autBar
      refine Subgroup.map_mono fun x hx => ?_
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hDB hx.1, hx.2⟩
    · rw [card_autBar_of_faithful hO hK hDN (fun x hx => hC x (hDB hx)), hDc, pow_one]
  have hBΔ : B ≤ Subgroup.normalizer ((localDeltaTwoIn ⊤ D : Subgroup X) : Set X) := fun g hg =>
    Lemma123.mem_normalizer_localDeltaTwoIn (Subgroup.le_normalizer (Subgroup.mem_top g))
      (fun d hd => Inputs27.elem_mul_comm hB hg (hDB hd))
  have hnormW : autBar 3 B K ≤ Subgroup.normalizer ((W : Subgroup (MulAut (barOf 3 K))) :
      Set (MulAut (barOf 3 K))) := by
    rw [hWdef]
    unfold autBar Lemma123.DeltaImage
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map (barAut 3 K))
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hd' : (d : X) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hd)).1
    have h1 := Subgroup.mem_normalizer_iff.1 (hBΔ hd') (w : X)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv]
    exact h1
  have hnorm : autBar 3 B K ≤ Subgroup.normalizer
      ((innerAut (barOf 3 K) ⊔ W : Subgroup (MulAut (barOf 3 K))) : Set (MulAut (barOf 3 K))) := by
    intro δ hδ
    have hI : ∀ ε : MulAut (barOf 3 K), ε ∈ Subgroup.normalizer
        ((innerAut (barOf 3 K) : Subgroup (MulAut (barOf 3 K))) : Set (MulAut (barOf 3 K))) := by
      intro ε
      rw [(Subgroup.normalizer_eq_top_iff).2 (Lemma123.innerAut_normal _)]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact CFSG.HardMathSupport.Solomon.Coordinator.conj_mem_sup_of_mem_normalizer (hI δ)
        (hnormW hδ) ht
    · intro ht
      have h1 := CFSG.HardMathSupport.Solomon.Coordinator.conj_mem_sup_of_mem_normalizer (hI δ⁻¹)
        (hnormW (Subgroup.inv_mem _ hδ)) ht
      simpa [mul_assoc] using h1
  exact ⟨hE1, hnorm, Inputs123a.deltaImage_le Nat.prime_three (by norm_num) le_top hDel⟩

theorem not_isLocallyOTwoBalanced_of_S (hO : GLAPPrimeCore 3 X = ⊥) {K B S : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) (hS : IsPGroup 2 ↥S)
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hnc : ¬ K ≤ Subgroup.centralizer (S : Set X))
    (hcond : ∀ b ∈ B, b ≠ 1 →
      S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X))) :
    ¬ IsLocallyOTwoBalanced 3 1 (autBar 3 B K) := by
  intro hbal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK := glaPPrimeCoreOf_eq_bot_of_comp hO hK
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three B S (fun f => Subtype.ext (by simpa using hB.2 f.1 f.2)) (by rw [hB9]; norm_num)
    (by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS
      rw [hn]
      intro hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num))
    hBS
  obtain ⟨b, hbB, hb1, s, hsS, hsb, hsK⟩ : ∃ b ∈ B, b ≠ 1 ∧ ∃ s ∈ S,
      s ∈ Subgroup.centralizer ({b} : Set X) ∧ s ∉ Subgroup.centralizer (K : Set X) := by
    by_contra hcon
    push Not at hcon
    apply hnc
    rw [Subgroup.le_centralizer_iff, hgen]
    refine iSup₂_le fun f hf1 => ?_
    intro t ht
    exact hcon f f.2 (fun h => hf1 (Subtype.ext h)) t (Subgroup.mem_inf.1 ht).1
      (Subgroup.mem_inf.1 ht).2
  have hΔ : S ⊓ Subgroup.centralizer ({b} : Set X) ≤ localDeltaTwoIn ⊤ (Subgroup.zpowers b) := by
    unfold localDeltaTwoIn
    refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.centralizer_eq_of_mem_zpowers hB hbB hb1
      hd hd1, top_inf_eq]
    exact hcond b hbB hb1
  set W : Subgroup (MulAut (barOf 3 K)) := Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers b) K with hWdef
  have hsN : s ∈ Subgroup.normalizer (K : Set X) := hSN hsS
  have hWs : barAut 3 K ⟨s, hsN⟩ ∈ W :=
    ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.2 (hΔ ⟨hsS, hsb⟩), rfl⟩
  have hWne : W ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.mem_bot] at hWs
    exact hsK (mem_centralizer_of_barAut_eq_one hOK ⟨s, hsN⟩ hWs)
  obtain ⟨hE1, hnorm, hle⟩ := deltaImage_facts hO hK hB hN hC hbB hb1
  have h0 := hbal _ hE1 _ le_sup_left (hE1.1.trans hnorm)
  rw [h0] at hle
  exact hWne (le_bot_iff.1 hle)

theorem glaPPrimeCore_top_eq_bot {p : ℕ} (hO : GLAPPrimeCore p X = ⊥) :
    GLAPPrimeCore p ↥(⊤ : Subgroup X) = ⊥ := by
  have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)
  rw [hO] at h
  exact Subgroup.map_injective (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).injective
    (by simpa using h)

theorem mk'_top_injective {p : ℕ} (hO : GLAPPrimeCore p X = ⊥) :
    Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', glaPPrimeCore_top_eq_bot hO]

theorem le_of_barX_top_le {p : ℕ} (hO : GLAPPrimeCore p X = ⊥) {H₁ H₂ : Subgroup X}
    (h : barX p ⊤ H₁ ≤ barX p ⊤ H₂) : H₁ ≤ H₂ := by
  intro x hx
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X)) ⟨x, trivial⟩ ∈ barX p ⊤ H₁ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (h hmem)
  rw [mk'_top_injective hO hyx] at hy
  exact Subgroup.mem_subgroupOf.1 hy

theorem glaPComponent_top_of_comp (hO : GLAPPrimeCore 3 X = ⊥) {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) : GLAPComponent 3 ⊤ K := by
  refine CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_of_isComponentOf_of_core_eq_bot ?_ hK
  show (GLAPPrimeCore 3 ↥(⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype = ⊥
  rw [glaPPrimeCore_top_eq_bot hO, Subgroup.map_bot]

noncomputable def barOfEquivSelf {K : Subgroup X} (hOK : GLAPPrimeCore 3 ↥K = ⊥) : barOf 3 K ≃* ↥K :=
  (QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot

theorem pRank_eq_two_of_card_nine {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9) :
    CFSG.Open.pRank 3 B = 2 := by
  have h := Inputs27.card_eq_pow_pRank Nat.prime_three hB
  rw [hB9, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm

theorem le_iSup_centralizer_of_chev3 (hI196 : Lemma123.Input19_6_4) (hI2317 : Lemma123.Input23_17)
    (hO : GLAPPrimeCore 3 X = ⊥)
    {K B : Subgroup X} (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1)
    (hnb : ¬ IsLocallyOTwoBalanced 3 1 (autBar 3 B K))
    (hch : IsChevSimple 3 (↥K ⧸ Subgroup.center ↥K)) :
    K ≤ ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X) := by
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  have hOK' := glaPPrimeCoreOf_eq_bot_of_comp hO hK
  set e := barOfEquivSelf hOK
  have hYq : CFSG.Open.IsQuasisimple (barOf 3 K) := CFSG.Open.IsQuasisimple.of_mulEquiv e hK.2.2
  have hYO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hYch : IsChevSimple 3 (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    Lemma1315b.isChevSimple_center_of_equiv e hch
  obtain ⟨-, hL27, hout⟩ := hI196 3 Nat.prime_three (by norm_num) (barOf 3 K) hYq hYO hYch
    (autBar 3 B K) (isElemAbelian_autBar hB K) hnb
  have hcent : ∀ x ∈ B, x ∈ centBar 3 ⊤ K → x = 1 := by
    intro x hxB hx
    obtain ⟨⟨g, hg, rfl⟩, -⟩ := hx
    exact hC _ hxB (mem_centralizer_of_barAut_eq_one hOK' g hg)
  have hgen := hI2317 X ⊤ K B (glaPComponent_top_of_comp hO hK) le_top hB hN
    hcent (by rw [pRank_eq_two_of_card_nine hB hB9]) hL27 hout
  refine (le_of_barX_top_le hO hgen).trans (iSup_mono fun b => iSup_mono fun _ => iSup_mono fun _ => ?_)
  exact (sec11_glaPPrimeCoreOf_le _).trans inf_le_right

theorem le_iSup_centralizer_of_chevq (h2310 : Claims1116.Input23_10) (hO : GLAPPrimeCore 3 X = ⊥)
    {K B : Subgroup X} (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (hN : B ≤ Subgroup.normalizer (K : Set X)) {q : ℕ} (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) (hch : IsChevSimple q (↥K ⧸ Subgroup.center ↥K)) :
    K ≤ ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X) := by
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  have hch' : IsChevSimple q (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    Lemma1315b.isChevSimple_center_of_equiv (barOfEquivSelf hOK) hch
  have h := h2310 (G := X) (p := 3) (r := q) Nat.prime_three (by norm_num) hq3
    (X := ⊤) (J := K) (E := B) (glaPComponent_top_of_comp hO hK) le_top hB (by rw [hB9]; norm_num) hch'
    (fun h => hq2 h.1)
  have hinj := mk'_top_injective (p := 3) hO
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(⊤ : Subgroup X)) with hπ
  have hBN : barX 3 ⊤ B ≤ Subgroup.normalizer (barX 3 ⊤ K : Set (↥(⊤ : Subgroup X) ⧸
      GLAPPrimeCore 3 ↥(⊤ : Subgroup X))) := barX_le_normalizer hN
  have hBc : Nat.card (barX 3 ⊤ B) = 9 := by
    rw [barX, Subgroup.card_map_of_injective hinj, ← hB9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
  refine le_of_barX_top_le hO (h.trans (iSup₂_le fun F hF => ?_))
  obtain ⟨hFB, hFc⟩ := hF
  rw [inf_eq_left.2 hBN, hBc] at hFc
  have hF1 : F ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hFc
    omega
  obtain ⟨⟨f, hfF⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  obtain ⟨y, hyB, rfl⟩ := Subgroup.mem_map.1 ((hFB.trans inf_le_left) hfF)
  have hy1 : (y : X) ≠ 1 := fun h => hf1' (by rw [show y = 1 from Subtype.ext h, map_one])
  rintro _ ⟨⟨w, hwK, rfl⟩, hwc⟩
  have hc := Subgroup.mem_centralizer_iff.1 hwc (π y) hfF
  rw [← map_mul, ← map_mul] at hc
  have hwy : (w : X) ∈ Subgroup.centralizer ({(y : X)} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hinj hc)).symm
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
  exact Subgroup.mem_iSup_of_mem (y : X) (Subgroup.mem_iSup_of_mem
    (Subgroup.mem_subgroupOf.1 hyB) (Subgroup.mem_iSup_of_mem hy1 hwy))

end I275Deep

section Chev2

variable {X : Type} [Group X] [Finite X]

theorem exists_centralizing_lift {K S : Subgroup X} {b : X} (hS : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (K : Set X)) (hbS : b ∈ Subgroup.normalizer (S : Set X))
    (hbK : b ∈ Subgroup.normalizer (K : Set X)) (hb3 : b ^ 3 = 1) {s : X} (hs : s ∈ S)
    (hcomm : barAut 3 K ⟨s, hSN hs⟩ * barAut 3 K ⟨b, hbK⟩ =
      barAut 3 K ⟨b, hbK⟩ * barAut 3 K ⟨s, hSN hs⟩) :
    ∃ c ∈ S ⊓ Subgroup.centralizer ({b} : Set X), ∃ hc : c ∈ Subgroup.normalizer (K : Set X),
      barAut 3 K ⟨c, hc⟩ = barAut 3 K ⟨s, hSN hs⟩ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup X := Subgroup.zpowers b with hA
  have hAp : IsPGroup 3 ↥A := l119_isPGroup_zpowers hb3
  have hAS : A ≤ Subgroup.normalizer (S : Set X) := Subgroup.zpowers_le.2 hbS
  have hAK : A ≤ Subgroup.normalizer (K : Set X) := Subgroup.zpowers_le.2 hbK
  set φ₀ : ↥S →* MulAut (barOf 3 K) := (barAut 3 K).comp (Subgroup.inclusion hSN) with hφ₀
  set β : ↥A →* MulAut (barOf 3 K) := (barAut 3 K).comp (Subgroup.inclusion hAK) with hβ
  have hconj : ∀ (g : ↥A) (t : ↥S), φ₀ ⟨(g : X) * t * (g : X)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (hAS g.2) t).1 t.2⟩ = β g * φ₀ t * (β g)⁻¹ := by
    intro g t
    simp only [hφ₀, hβ, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hAR : ∀ g : ↥A, β g ∈ Subgroup.normalizer ((φ₀.range : Subgroup (MulAut (barOf 3 K))) :
      Set (MulAut (barOf 3 K))) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, hconj g t⟩
    · rintro ⟨t, ht⟩
      refine ⟨⟨((g⁻¹ : ↥A) : X) * t * ((g⁻¹ : ↥A) : X)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (hAS (g⁻¹).2) t).1 t.2⟩, ?_⟩
      rw [hconj g⁻¹ t, map_inv, inv_inv, ht]
      group
  set ψ : ↥A →* ↥(Subgroup.normalizer ((φ₀.range : Subgroup (MulAut (barOf 3 K))) :
      Set (MulAut (barOf 3 K)))) := β.codRestrict _ hAR with hψ
  set sa : ↥A →* MulAut ↥S := S.normalizerMonoidHom.comp (Subgroup.inclusion hAS) with hsa
  set ta : ↥A →* MulAut ↥φ₀.range := φ₀.range.normalizerMonoidHom.comp ψ with hta
  have hequiv : ∀ (g : ↥A) (t : ↥S), φ₀.rangeRestrict (sa g t) = ta g (φ₀.rangeRestrict t) := by
    intro g t
    apply Subtype.ext
    exact hconj g t
  have hker : ¬ 3 ∣ Nat.card φ₀.rangeRestrict.ker := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS
    intro hd
    have h1 := hd.trans (Subgroup.card_subgroup_dvd_card φ₀.rangeRestrict.ker)
    rw [hn] at h1
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h1)) (by norm_num)
  have hfix : ∀ g : ↥A, ta g (φ₀.rangeRestrict ⟨s, hs⟩) = φ₀.rangeRestrict ⟨s, hs⟩ := by
    intro g
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    have hg : g = (⟨b, Subgroup.mem_zpowers b⟩ : ↥A) ^ k := Subtype.ext (by simp [hk])
    show β g * φ₀ ⟨s, hs⟩ * (β g)⁻¹ = φ₀ ⟨s, hs⟩
    have hc : Commute (β g) (φ₀ ⟨s, hs⟩) := by
      rw [hg, map_zpow]
      exact Commute.zpow_left hcomm.symm k
    rw [hc.eq, mul_inv_cancel_right]
  obtain ⟨c, hc1, hc2⟩ := CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_coprime_kernel 3
    hAp sa ta φ₀.rangeRestrict φ₀.rangeRestrict_surjective hker hequiv _ hfix
  have hcb : (c : X) ∈ Subgroup.centralizer ({b} : Set X) := by
    have h := congrArg Subtype.val (hc2 ⟨b, Subgroup.mem_zpowers b⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : b * (c : X) * b⁻¹ = c := h
    calc (c : X) * b = b * (c : X) * b⁻¹ * b := by rw [h']
      _ = b * c := by group
  refine ⟨c, ⟨c.2, hcb⟩, hSN c.2, ?_⟩
  exact congrArg Subtype.val hc1

theorem not_isLocallyOTwoBalanced_two_of_weak (hO : GLAPPrimeCore 3 X = ⊥) {K B S : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) (hS : IsPGroup 2 ↥S)
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hnc : ¬ K ≤ Subgroup.centralizer (S : Set X))
    (hcond : ∀ b ∈ B, b ≠ 1 →
      S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
    (hweak : IsWeaklyLocallyOTwoBalanced 3 1 (autBar 3 B K)) :
    ¬ IsLocallyOTwoBalanced 3 2 (autBar 3 B K) := by
  intro hbal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK := glaPPrimeCoreOf_eq_bot_of_comp hO hK
  have hBel : IsElemAbelian 3 (autBar 3 B K) := isElemAbelian_autBar hB K
  have hΔ : ∀ b ∈ B, b ≠ 1 → ∀ (t : X) (ht : t ∈ S), t ∈ Subgroup.centralizer ({b} : Set X) →
      barAut 3 K ⟨t, hSN ht⟩ ∈ Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers b) K := by
    intro b hbB hb1 t ht htb
    have hmem : t ∈ localDeltaTwoIn ⊤ (Subgroup.zpowers b) := by
      unfold localDeltaTwoIn
      refine Subgroup.mem_iInf.2 fun d => Subgroup.mem_iInf.2 fun hd => Subgroup.mem_iInf.2 fun hd1 => ?_
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.centralizer_eq_of_mem_zpowers hB hbB hb1
        hd hd1, top_inf_eq]
      exact hcond b hbB hb1 ⟨ht, htb⟩
    exact ⟨⟨t, hSN ht⟩, Subgroup.mem_subgroupOf.2 hmem, rfl⟩
  have hW : ∀ b ∈ B, b ≠ 1 → Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers b) K ≤
      Subgroup.centralizer ((autBar 3 B K : Subgroup (MulAut (barOf 3 K))) : Set (MulAut (barOf 3 K))) := by
    intro b hbB hb1
    obtain ⟨hE1, hnorm, hle⟩ := deltaImage_facts hO hK hB hN hC hbB hb1
    have h0 := hweak _ hE1 _ le_sup_left hnorm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (le_bot_iff.1 (h0 ▸ Subgroup.commutator_mono hle le_rfl))
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three B S (fun f => Subtype.ext (by simpa using hB.2 f.1 f.2)) (by rw [hB9]; norm_num)
    (by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS
      rw [hn]
      intro hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num))
    hBS
  have hSC : ∀ (t : X) (ht : t ∈ S), barAut 3 K ⟨t, hSN ht⟩ ∈
      Subgroup.centralizer ((autBar 3 B K : Subgroup (MulAut (barOf 3 K))) : Set (MulAut (barOf 3 K))) := by
    set T : Subgroup X := ((Subgroup.centralizer ((autBar 3 B K : Subgroup (MulAut (barOf 3 K))) :
      Set (MulAut (barOf 3 K)))).comap (barAut 3 K)).map (Subgroup.normalizer (K : Set X)).subtype with hT
    have hST : S ≤ T := by
      rw [hgen]
      refine iSup₂_le fun f hf1 => ?_
      intro t ht
      have hf1' : (f : X) ≠ 1 := fun h => hf1 (Subtype.ext h)
      exact ⟨⟨t, hSN (Subgroup.mem_inf.1 ht).1⟩, hW f f.2 hf1' (hΔ f f.2 hf1' t
        (Subgroup.mem_inf.1 ht).1 (Subgroup.mem_inf.1 ht).2), rfl⟩
    intro t ht
    obtain ⟨g, hg, hgt⟩ := hST ht
    have hgeq : g = ⟨t, hSN ht⟩ := Subtype.ext hgt
    rw [← hgeq]
    exact hg
  have hSW : ∀ b ∈ B, b ≠ 1 → ∀ (t : X) (ht : t ∈ S),
      barAut 3 K ⟨t, hSN ht⟩ ∈ Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers b) K := by
    intro b hbB hb1 t ht
    have hbA : barAut 3 K ⟨b, hN hbB⟩ ∈ autBar 3 B K :=
      ⟨⟨b, hN hbB⟩, Subgroup.mem_subgroupOf.2 ⟨hbB, hN hbB⟩, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (hSC t ht) _ hbA
    obtain ⟨c, hc, hcN, hceq⟩ := exists_centralizing_lift hS hSN (hBS hbB) (hN hbB) (hB.2 b hbB) ht
      hcomm.symm
    rw [← hceq]
    exact hΔ b hbB hb1 c (Subgroup.mem_inf.1 hc).1 (Subgroup.mem_inf.1 hc).2
  set H : Subgroup (MulAut (barOf 3 K)) := innerAut (barOf 3 K) ⊔ autBar 3 S K with hH
  have hI : ∀ ε : MulAut (barOf 3 K), ε ∈ Subgroup.normalizer
      ((innerAut (barOf 3 K) : Subgroup (MulAut (barOf 3 K))) : Set (MulAut (barOf 3 K))) := by
    intro ε
    rw [(Subgroup.normalizer_eq_top_iff).2 (Lemma123.innerAut_normal _)]
    exact Subgroup.mem_top _
  have hBSt : autBar 3 B K ≤ Subgroup.normalizer ((autBar 3 S K : Subgroup (MulAut (barOf 3 K))) :
      Set (MulAut (barOf 3 K))) := by
    unfold autBar
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map (barAut 3 K))
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hd' : (d : X) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hd)).1
    have h1 := Subgroup.mem_normalizer_iff.1 (hBS hd') (w : X)
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul, InvMemClass.coe_inv]
    constructor
    · rintro ⟨hw, -⟩
      exact ⟨h1.1 hw, Subgroup.mul_mem _ (Subgroup.mul_mem _ d.2 w.2) (Subgroup.inv_mem _ d.2)⟩
    · rintro ⟨hw, -⟩
      exact ⟨h1.2 hw, w.2⟩
  have hBH : autBar 3 B K ≤ Subgroup.normalizer ((H : Subgroup (MulAut (barOf 3 K))) :
      Set (MulAut (barOf 3 K))) := by
    intro δ hδ
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact CFSG.HardMathSupport.Solomon.Coordinator.conj_mem_sup_of_mem_normalizer (hI δ)
        (hBSt hδ) ht
    · intro ht
      have h1 := CFSG.HardMathSupport.Solomon.Coordinator.conj_mem_sup_of_mem_normalizer (hI δ⁻¹)
        (hBSt (Subgroup.inv_mem _ hδ)) ht
      simpa [mul_assoc] using h1
  have hSΔ : autBar 3 S K ≤ localDeltaTwoIn H (autBar 3 B K) := by
    unfold localDeltaTwoIn
    refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
    obtain ⟨g, hg, rfl⟩ := hd
    have hgB : (g : X) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1
    have hg1 : (g : X) ≠ 1 := fun h => hd1 (by rw [show g = 1 from Subtype.ext h, map_one])
    obtain ⟨-, -, hle⟩ := deltaImage_facts hO hK hB hN hC hgB hg1
    set W := Lemma123.DeltaImage 3 ⊤ (Subgroup.zpowers (g : X)) K with hWdef
    have hdD : barAut 3 K g ∈ autBar 3 (Subgroup.zpowers (g : X)) K :=
      ⟨g, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_zpowers _, g.2⟩, rfl⟩
    have hWP : W ≤ pCoreOf 2 ((innerAut (barOf 3 K) ⊔ W) ⊓
        Subgroup.centralizer ({barAut 3 K g} : Set (MulAut (barOf 3 K)))) :=
      hle.trans ((iInf_le _ _).trans ((iInf_le _ hdD).trans (iInf_le _ hd1)))
    have hSW' : autBar 3 S K ≤ W := by
      rintro _ ⟨t, ht, rfl⟩
      have htS : (t : X) ∈ S := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ht)).1
      have := hSW (g : X) hgB hg1 (t : X) htS
      have htt : t = ⟨(t : X), hSN htS⟩ := Subtype.ext rfl
      rw [htt]
      exact this
    have hHW : H ≤ innerAut (barOf 3 K) ⊔ W := sup_le le_sup_left (hSW'.trans le_sup_right)
    have hSH : autBar 3 S K ≤ H ⊓ Subgroup.centralizer ({barAut 3 K g} : Set (MulAut (barOf 3 K))) := by
      refine le_inf le_sup_right fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨t, ht, rfl⟩ := hx
      have htS : (t : X) ∈ S := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ht)).1
      have htt : t = ⟨(t : X), hSN htS⟩ := Subtype.ext rfl
      have hgA : barAut 3 K g ∈ autBar 3 B K :=
        ⟨g, hg, rfl⟩
      rw [htt]
      exact (Subgroup.mem_centralizer_iff.1 (hSC (t : X) htS) _ hgA).symm
    set T := pCoreOf 2 ((innerAut (barOf 3 K) ⊔ W) ⊓
      Subgroup.centralizer ({barAut 3 K g} : Set (MulAut (barOf 3 K)))) ⊓
        (H ⊓ Subgroup.centralizer ({barAut 3 K g} : Set (MulAut (barOf 3 K)))) with hTdef
    have hST : autBar 3 S K ≤ T := le_inf (hSW'.trans hWP) hSH
    refine hST.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left))
    intro x hx
    have hx' : x ∈ (innerAut (barOf 3 K) ⊔ W) ⊓
        Subgroup.centralizer ({barAut 3 K g} : Set (MulAut (barOf 3 K))) :=
      ⟨hHW (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    exact Lemma123.mem_normalizer_inf' (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx')
      (Subgroup.le_normalizer hx)
  have hS1 : autBar 3 S K ≠ ⊥ := by
    intro h0
    apply hnc
    rw [Subgroup.le_centralizer_iff]
    intro s hs
    have hb : barAut 3 K ⟨s, hSN hs⟩ ∈ autBar 3 S K :=
      ⟨⟨s, hSN hs⟩, Subgroup.mem_subgroupOf.2 ⟨hs, hSN hs⟩, rfl⟩
    rw [h0, Subgroup.mem_bot] at hb
    exact mem_centralizer_of_barAut_eq_one hOK _ hb
  have hBc : Nat.card (autBar 3 B K) = 3 ^ 2 := by
    rw [card_autBar_of_faithful hO hK hN hC, hB9]
    norm_num
  have h0 := hbal (autBar 3 B K) ⟨le_rfl, hBel, hBc⟩ H le_sup_left hBH
  rw [h0] at hSΔ
  exact hS1 (le_bot_iff.1 hSΔ)

theorem not_isLocallyOTwoBalanced_two_or_weak (hO : GLAPPrimeCore 3 X = ⊥) {K B S : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) (hS : IsPGroup 2 ↥S)
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hnc : ¬ K ≤ Subgroup.centralizer (S : Set X))
    (hcond : ∀ b ∈ B, b ≠ 1 →
      S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X))) :
    ¬ IsLocallyOTwoBalanced 3 2 (autBar 3 B K) ∨ ¬ IsWeaklyLocallyOTwoBalanced 3 1 (autBar 3 B K) := by
  by_cases hw : IsWeaklyLocallyOTwoBalanced 3 1 (autBar 3 B K)
  · exact Or.inl (not_isLocallyOTwoBalanced_two_of_weak hO hK hB hB9 hN hC hS hBS hSN hnc hcond hw)
  · exact Or.inr hw

theorem not_isLocallyOTwoBalanced_two_of_chev2 (hI1920 : Lemma123.Input19_20_1)
    (hI712 : Lemma123.Input7_12_2) (hO : GLAPPrimeCore 3 X = ⊥) {K B S : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) (hS : IsPGroup 2 ↥S)
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hnc : ¬ K ≤ Subgroup.centralizer (S : Set X))
    (hcond : ∀ b ∈ B, b ≠ 1 →
      S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
    (hch : IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)) :
    ¬ IsLocallyOTwoBalanced 3 2 (autBar 3 B K) := by
  have hOK0 : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  set e := barOfEquivSelf hOK0
  have hYq : CFSG.Open.IsQuasisimple (barOf 3 K) := CFSG.Open.IsQuasisimple.of_mulEquiv e hK.2.2
  have hYch : IsChevSimple 2 (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    Lemma1315b.isChevSimple_center_of_equiv e hch
  exact not_isLocallyOTwoBalanced_two_of_weak hO hK hB hB9 hN hC hS hBS hSN hnc hcond
    (Lemma123.chev2_weak hI1920 hI712 Nat.prime_three (by norm_num) hYq hYch _ (isElemAbelian_autBar hB K))

theorem isPGroup_center_of_core_eq_bot {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (hO : GLAPPrimeCore p Y = ⊥) : IsPGroup p ↥(Subgroup.center Y) := by
  intro z
  have hn0 : orderOf (z : Y) ≠ 0 := (orderOf_pos (z : Y)).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.ne_one
  set y : Y := (z : Y) ^ (p ^ a) with hy
  have hyo : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero a hp.out.ne_zero) ⟨m, hnm⟩, hnm,
      Nat.mul_div_cancel_left _ (pow_pos hp.out.pos a)]
  have hyZ : y ∈ Subgroup.center Y := Subgroup.pow_mem _ z.2 _
  haveI hN : (Subgroup.zpowers y).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hyZ)
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hyo]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hm
  have h0 := GL83.CompFam.eq_bot_of_isSubnormal_of_coprime hp.out hO
    (CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_normal hN) hcop
  have hy1 : y = 1 := by
    have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
    rw [h0, Subgroup.mem_bot] at this
    exact this
  refine ⟨a, Subtype.ext ?_⟩
  simpa [hy] using hy1

theorem concl_c_of_lThreeFour (hI7L : Input7_L34)
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover)
    (hSL : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    {Y : Type} [Group Y] [Finite Y] (hYq : CFSG.Open.IsQuasisimple Y) (hYO : GLAPPrimeCore 3 Y = ⊥)
    (hL : IsLThreeFour (Y ⧸ Subgroup.center Y))
    (hA2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y))) :
    CFSG.Open.pRank 3 (⊤ : Subgroup Y) = 2 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) = 2 ∧
      9 ∣ Nat.card Y ∧ ¬ 81 ∣ Nat.card Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 ↥(Subgroup.center Y) := isPGroup_center_of_core_eq_bot hYO
  have hZc : CFSG.pCore 3 Y = Subgroup.center Y :=
    le_antisymm (CFSG.HardMathSupport.Solomon.Proving.pCore_three_le_center_of_quasisimple hYq)
      (le_sSup ⟨inferInstance, hZp⟩)
  have hL' : IsLThreeFour (Y ⧸ CFSG.pCore 3 Y) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hZc.symm) hL
  have hAut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) = 2 := by
    refine le_antisymm (CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_) hA2
    have h1 := hI7L Y hYq hL hYO E hE
    rw [Inputs27.card_eq_pow_pRank Nat.prime_three hE]
    exact Nat.pow_le_pow_right (by norm_num) h1
  have hQc : Nat.card (Y ⧸ Subgroup.center Y) = 20160 :=
    CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour hL
  have hYc : Nat.card Y = Nat.card (Subgroup.center Y) * 20160 := by
    rw [← hQc, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rcases hcov Y hYq hL' with hY | hY
  ·
    have hYc' : Nat.card Y = 20160 := CFSG.HardMathSupport.Solomon.Coordinator.card_of_isLThreeFour hY
    refine ⟨le_antisymm (CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_) ?_, hAut,
      by rw [hYc']; norm_num, by rw [hYc']; norm_num⟩
    · have hd : Nat.card E ∣ 20160 := hYc' ▸ Subgroup.card_subgroup_dvd_card E
      rw [Inputs27.card_eq_pow_pRank Nat.prime_three hE] at hd ⊢
      apply Nat.pow_le_pow_right (by norm_num)
      by_contra hlt
      push Not at hlt
      have h3 : 3 ^ 3 ∣ 20160 := (Nat.pow_dvd_pow 3 hlt).trans hd
      norm_num at h3
    · obtain ⟨P⟩ : Nonempty (Sylow 3 Y) := inferInstance
      have hP9 : Nat.card (P : Subgroup Y) = 9 :=
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_sylow_three_lThreeFour hY P
      have hPel := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C.isElemAbelian_of_card_nine hY
        (P : Subgroup Y) hP9
      exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hPel (k := 2) (by rw [hP9]; norm_num)
  ·
    obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hY
    have hZ3 : Nat.card (Subgroup.center Y) = 3 := by
      rw [← CFSG.HardMathSupport.Solomon.Proving.card_center_statedSL_three_four hF]
      exact Nat.card_congr (Subgroup.centerCongr f).toEquiv
    have hYc' : Nat.card Y = 60480 := by rw [hYc, hZ3]
    have hZne : Subgroup.center Y ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hZ3
      omega
    refine ⟨le_antisymm (CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_) ?_, hAut,
      by rw [hYc']; norm_num, by rw [hYc']; norm_num⟩
    ·
      have hd : Nat.card E ∣ 60480 := hYc' ▸ Subgroup.card_subgroup_dvd_card E
      rw [Inputs27.card_eq_pow_pRank Nat.prime_three hE] at hd ⊢
      apply Nat.pow_le_pow_right (by norm_num)
      by_contra hlt
      push Not at hlt
      have hr3 : CFSG.Open.pRank 3 E = 3 := by
        refine le_antisymm ?_ hlt
        by_contra h4
        push Not at h4
        have h3 : 3 ^ 4 ∣ 60480 := (Nat.pow_dvd_pow 3 h4).trans hd
        norm_num at h3
      have hEc : Nat.card E = 27 := by rw [Inputs27.card_eq_pow_pRank Nat.prime_three hE, hr3]; norm_num
      have hEp : IsPGroup 3 ↥E := CFSG.Open.IsElemAbelian.isPGroup hE
      have hEi : ¬ 3 ∣ E.index := by
        have h1 := Subgroup.card_mul_index E
        rw [hEc, hYc'] at h1
        have h2 : E.index = 2240 := by omega
        rw [h2]
        norm_num
      have hZE : Subgroup.center Y ≤ E := by
        have := hZp.le_sylow_of_normal (hEp.toSylow hEi)
        simpa using this
      obtain ⟨⟨x, hx, y, hy, hxy⟩, -⟩ := hSL Y hYq hZp hZne hL E hEp hZE (by rw [hEc, hZ3])
      exact hxy (Inputs27.elem_mul_comm hE hx hy)
    ·
      obtain ⟨P⟩ : Nonempty (Sylow 3 Y) := inferInstance
      have hPc : Nat.card (P : Subgroup Y) = 27 := by
        rw [Sylow.card_eq_multiplicity, hYc']
        have : (60480 : ℕ) = 3 ^ 3 * 2240 := by norm_num
        rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
        simp only [Finsupp.add_apply]
        rw [Nat.Prime.factorization_pow Nat.prime_three]
        have : (2240 : ℕ).factorization 3 = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)
        simp [this]
      have hZP : Subgroup.center Y ≤ (P : Subgroup Y) := hZp.le_sylow_of_normal P
      obtain ⟨⟨x, hx, y, hy, hxy⟩, hexp⟩ := hSL Y hYq hZp hZne hL P P.isPGroup' hZP (by rw [hPc, hZ3])
      have hxZ : x ∉ Subgroup.center Y ∨ y ∉ Subgroup.center Y := by
        by_contra h
        push Not at h
        exact hxy (Subgroup.mem_center_iff.1 h.1 y).symm
      obtain ⟨w, hwP, hwZ⟩ : ∃ w ∈ (P : Subgroup Y), w ∉ Subgroup.center Y := by
        rcases hxZ with h | h
        · exact ⟨x, hx, h⟩
        · exact ⟨y, hy, h⟩
      have hw3 : w ^ 3 = 1 := hexp w hwP
      have hw1 : w ≠ 1 := fun h => hwZ (h ▸ (Subgroup.center Y).one_mem)
      have hZel : IsElemAbelian 3 (Subgroup.center Y) := by
        refine ⟨inferInstance, fun z hz => ?_⟩
        have := pow_card_eq_one' (G := ↥(Subgroup.center Y)) (x := ⟨z, hz⟩)
        rw [hZ3] at this
        exact congrArg Subtype.val this
      have hcomm : ∀ a ∈ Subgroup.center Y, ∀ b ∈ Subgroup.zpowers w, a * b = b * a :=
        fun a ha b _ => (Subgroup.mem_center_iff.1 ha b).symm
      have hel : IsElemAbelian 3 (Subgroup.center Y ⊔ Subgroup.zpowers w) :=
        Inputs27.isElemAbelian_sup_of_commute hZel (Inputs27.isElemAbelian_zpowers' hw3) hcomm
      have hinf : Subgroup.center Y ⊓ Subgroup.zpowers w = ⊥ := by
        have hwc : Nat.card (Subgroup.zpowers w) = 3 := by
          rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
        have hle : Subgroup.center Y ⊓ Subgroup.zpowers w ≤ Subgroup.zpowers w := inf_le_right
        have hd := Subgroup.card_dvd_of_le hle
        rw [hwc] at hd
        rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hwc])
          have hw : w ∈ Subgroup.center Y ⊓ Subgroup.zpowers w := by
            rw [heq]
            exact Subgroup.mem_zpowers w
          exact hwZ (Subgroup.mem_inf.1 hw).1
      have hcard : Nat.card (Subgroup.center Y ⊔ Subgroup.zpowers w : Subgroup Y) = 3 ^ 2 := by
        rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm hinf, hZ3, Nat.card_zpowers,
          orderOf_eq_prime hw3 hw1]
        norm_num
      exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hel hcard

theorem two_le_pRank_aut (hO : GLAPPrimeCore 3 X = ⊥) {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) := by
  have hOK0 : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  set e := barOfEquivSelf hOK0
  have hc : Nat.card ((autBar 3 B K).map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective,
      card_autBar_of_faithful hO hK hN hC, hB9]
    norm_num
  exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top
    (CFSG.SectionRank.isElemAbelian_map (isElemAbelian_autBar hB K) _) hc

theorem concl_of_chev2 (hI1916 : Lemma123.Input19_16_two) (hI1920 : Lemma123.Input19_20_1)
    (hI712 : Lemma123.Input7_12_2) (hI7L : Input7_L34)
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover)
    (hSL : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hO : GLAPPrimeCore 3 X = ⊥) {K B S : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) (hS : IsPGroup 2 ↥S)
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hnc : ¬ K ≤ Subgroup.centralizer (S : Set X))
    (hcond : ∀ b ∈ B, b ≠ 1 →
      S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
    (hch : IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 2 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) = 2 ∧
      9 ∣ Nat.card ↥K ∧ ¬ 81 ∣ Nat.card ↥K := by
  have hnb2 := not_isLocallyOTwoBalanced_two_of_chev2 hI1920 hI712 hO hK hB hB9 hN hC hS hBS hSN hnc
    hcond hch
  have hOK0 : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  set e := barOfEquivSelf hOK0
  have hYq : CFSG.Open.IsQuasisimple (barOf 3 K) := CFSG.Open.IsQuasisimple.of_mulEquiv e hK.2.2
  have hYO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hYch : IsChevSimple 2 (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    Lemma1315b.isChevSimple_center_of_equiv e hch
  have hBc : Nat.card (autBar 3 B K) = 3 ^ 2 := by
    rw [card_autBar_of_faithful hO hK hN hC, hB9]
    norm_num
  obtain ⟨-, hL, -⟩ := hI1916 3 Nat.prime_three (by norm_num) (barOf 3 K) hYq hYO hYch 2
    (autBar 3 B K) le_rfl (isElemAbelian_autBar hB K) hBc hnb2
  have hLK : IsLThreeFour (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
      (Lemma1315b.centerQuotEquiv e) hL
  exact concl_c_of_lThreeFour hI7L hcov hSL hK.2.2 hOK0 hLK
    (two_le_pRank_aut hO hK hB hB9 hN hC)

end Chev2

section AltCover

variable {X : Type} [Group X] [Finite X]

theorem card_mulAut_alt7 : Nat.card (MulAut ↥(alternatingGroup (Fin 7))) = 5040 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num))),
    Nat.card_perm, Nat.card_fin]
  rfl

theorem concl_of_alt (hSchur : Lemma123.InputSchurAlt')
    (h67 : CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.AltSixSevenCentre)
    (hO : GLAPPrimeCore 3 X = ⊥) {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) {n : ℕ}
    (hn : IsAltType n (↥K ⧸ Subgroup.center ↥K)) :
    (∃ m : ℕ, IsAltType m ↥K) ∨
      (CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 2 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) = 2 ∧
        9 ∣ Nat.card ↥K ∧ ¬ 81 ∣ Nat.card ↥K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOK0 : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  obtain ⟨e⟩ := hn
  by_cases hZ : Subgroup.center ↥K = ⊥
  · exact Or.inl ⟨n, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.trans e⟩⟩
  right
  have hn67 : n = 6 ∨ n = 7 := by
    rcases hSchur 3 n Nat.prime_three (by norm_num) ↥K hK.2.2 hOK0 ⟨e⟩ with h | ⟨-, h⟩
    · exact absurd h hZ
    · exact h
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥K) := isPGroup_center_of_core_eq_bot hOK0
  have hZ3 : Nat.card (Subgroup.center ↥K) = 3 := by
    have hZd : Nat.card (Subgroup.center ↥K) ∣ 6 := h67 n hn67 ↥K hperf ⟨e⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZp
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZ (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    have hk1 : k ≤ 1 := by
      by_contra h
      push Not at h
      have h9 : 3 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 3 h).trans (hk ▸ hZd)
      norm_num at h9
    rw [hk, show k = 1 by omega, pow_one]
  have hcardK : Nat.card ↥K = 1080 ∨ Nat.card ↥K = 7560 := by
    have hKc : Nat.card ↥K = Nat.card (Subgroup.center ↥K) * Nat.card (↥K ⧸ Subgroup.center ↥K) := by
      rw [mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hKc, hZ3, Nat.card_congr e.toEquiv]
    rcases hn67 with rfl | rfl
    · left
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
    · right
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
  have hAutd : Nat.card (MulAut ↥(alternatingGroup (Fin n))) ∣ 10080 := by
    rcases hn67 with rfl | rfl
    · rw [CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6]
      norm_num
    · rw [card_mulAut_alt7]
      norm_num
  have h9 : 9 ∣ Nat.card ↥K := by rcases hcardK with h | h <;> rw [h] <;> norm_num
  have h81 : ¬ 81 ∣ Nat.card ↥K := by rcases hcardK with h | h <;> rw [h] <;> norm_num
  have hnab : ∀ P : Sylow 3 ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K) :=
    GL83.not_isMulCommutative_sylow_of_perfect hperf (by rw [hZ3])
  refine ⟨le_antisymm (CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_) ?_,
    le_antisymm (CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_)
      (two_le_pRank_aut hO hK hB hB9 hN hC), h9, h81⟩
  ·
    have hd : Nat.card E ∣ Nat.card ↥K := Subgroup.card_subgroup_dvd_card E
    rw [Inputs27.card_eq_pow_pRank Nat.prime_three hE] at hd ⊢
    apply Nat.pow_le_pow_right (by norm_num)
    by_contra hlt
    push Not at hlt
    have hr3 : CFSG.Open.pRank 3 E = 3 := by
      refine le_antisymm ?_ hlt
      by_contra h4
      push Not at h4
      have h81' : 3 ^ 4 ∣ Nat.card ↥K := (Nat.pow_dvd_pow 3 h4).trans hd
      exact h81 (by simpa using h81')
    have hEc : Nat.card E = 27 := by
      rw [Inputs27.card_eq_pow_pRank Nat.prime_three hE, hr3]
      norm_num
    have hEp : IsPGroup 3 ↥E := CFSG.Open.IsElemAbelian.isPGroup hE
    have hEi : ¬ 3 ∣ E.index := by
      rintro ⟨c, hc⟩
      apply h81
      rw [← Subgroup.card_mul_index E, hEc, hc]
      exact ⟨c, by ring⟩
    exact hnab (hEp.toSylow hEi) hE.1
  ·
    obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
    haveI : Fact (IsPGroup 3 ↥(P : Subgroup ↥K)) := ⟨P.isPGroup'⟩
    have hnc : ¬ IsCyclic ↥(P : Subgroup ↥K) := fun hc => hnab P inferInstance
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
    have hSE : IsElemAbelian 3 (S.map (P : Subgroup ↥K).subtype) :=
      CFSG.SectionRank.isElemAbelian_map
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).mp hSel) _
    exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hSE
      (by rw [Subgroup.card_map_of_injective (P : Subgroup ↥K).subtype_injective, hScard])
  ·
    have hφ : Function.Injective ((MulAut.congr e).toMonoidHom.comp (Lemma123.autQ ↥K)) :=
      (MulAut.congr e).injective.comp (Lemma123.autQ_injective hperf)
    have hd : Nat.card E ∣ 10080 := by
      have h1 := Subgroup.card_subgroup_dvd_card
        (E.map ((MulAut.congr e).toMonoidHom.comp (Lemma123.autQ ↥K)))
      rw [Subgroup.card_map_of_injective hφ] at h1
      exact h1.trans hAutd
    rw [Inputs27.card_eq_pow_pRank Nat.prime_three hE] at hd ⊢
    apply Nat.pow_le_pow_right (by norm_num)
    by_contra hlt
    push Not at hlt
    have h3 : 3 ^ 3 ∣ 10080 := (Nat.pow_dvd_pow 3 hlt).trans hd
    norm_num at h3

end AltCover

section Spor

variable {X : Type} [Group X] [Finite X]

theorem le_iSup_centralizer_of_spor (hI1917 : Lemma123.Input19_17_2) (hI2324 : Lemma123.Input23_24)
    (hO : GLAPPrimeCore 3 X = ⊥) {K B S : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hB : IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) (hS : IsPGroup 2 ↥S)
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (hSN : S ≤ Subgroup.normalizer (K : Set X))
    (hnc : ¬ K ≤ Subgroup.centralizer (S : Set X))
    (hcond : ∀ b ∈ B, b ≠ 1 →
      S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
    {s : TauCeti.SporadicName} (hsp : IsSporType s (↥K ⧸ Subgroup.center ↥K)) :
    K ≤ ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X) := by
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPPrimeCore_eq_bot_of_isSubnormal hO hK.2.1
  have hOK' := glaPPrimeCoreOf_eq_bot_of_comp hO hK
  set e := barOfEquivSelf hOK
  have hYq : CFSG.Open.IsQuasisimple (barOf 3 K) := CFSG.Open.IsQuasisimple.of_mulEquiv e hK.2.2
  have hYO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hYs : IsSporType s (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    ⟨(Lemma1315b.centerQuotEquiv e).trans hsp.some⟩
  have hnb := not_isLocallyOTwoBalanced_two_or_weak hO hK hB hB9 hN hC hS hBS hSN hnc hcond
  have hexc : s = TauCeti.SporadicName.M12 ∨ s = TauCeti.SporadicName.M22 ∨
      s = TauCeti.SporadicName.J2 := by
    have hnb' : ¬ IsLocallyOTwoBalancedWrtP 3 2 (barOf 3 K) ∨
        ¬ IsWeaklyLocallyOTwoBalancedWrtP 3 1 (barOf 3 K) := by
      rcases hnb with h | h
      · exact Or.inl fun hb => h (hb _ (isElemAbelian_autBar hB K))
      · exact Or.inr fun hb => h (hb _ (isElemAbelian_autBar hB K))
    rcases hI1917 3 Nat.prime_three (by norm_num) s (barOf 3 K) hYq hYO hYs hnb' with ⟨h5, -⟩ | ⟨-, h⟩
    · norm_num at h5
    · exact h
  have hcent : ∀ x ∈ B, x ∈ centBar 3 ⊤ K → x = 1 := by
    intro x hxB hx
    obtain ⟨⟨g, hg, rfl⟩, -⟩ := hx
    exact hC _ hxB (mem_centralizer_of_barAut_eq_one hOK' g hg)
  have hgen := hI2324 X ⊤ K B s (glaPComponent_top_of_comp hO hK) le_top hB hN hcent
    (by rw [pRank_eq_two_of_card_nine hB hB9]) hexc hYs hnb
  refine (le_of_barX_top_le hO hgen).trans (iSup_mono fun b => iSup_mono fun _ => iSup_mono fun _ => ?_)
  exact (sec11_glaPPrimeCoreOf_le _).trans inf_le_right

end Spor

section Assembly

theorem isChevSimple_of_lie {S : Type} [Group S] {idx : TauCeti.ValidLieTypeIndex}
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) : IsChevSimple idx.1.characteristic S :=
  Or.inl ⟨.lie idx, rfl, ⟨e⟩⟩

theorem type_cases {X : Type} [Group X] [Finite X] (hXK : CFSG.Open.IsKGroup X) {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) :
    (∃ n : ℕ, IsAltType n (↥K ⧸ Subgroup.center ↥K)) ∨
      (∃ r : ℕ, IsChevSimple r (↥K ⧸ Subgroup.center ↥K)) ∨
      (∃ s : TauCeti.SporadicName, IsSporType s (↥K ⧸ Subgroup.center ↥K)) := by
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  have hnab := Prop1116Design.not_isCommutative_barQuot ↥K hK.2.2
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.KCore.KGroupNonab.catalogue_of_surjective isoInvariant_isCatalogGroup hXK K hnab
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rcases Lemma1315b.catalog_cases hnab hcat with h | ⟨idx, ⟨e⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨_, isChevSimple_of_lie e⟩)
  · exact Or.inr (Or.inr h)

theorem input27_5Core_of_inputs (hI196 : Lemma123.Input19_6_4) (hI2317 : Lemma123.Input23_17)
    (h2310 : Claims1116.Input23_10) (hI1916 : Lemma123.Input19_16_two)
    (hI1920 : Lemma123.Input19_20_1) (hI712 : Lemma123.Input7_12_2) (hI7L : Input7_L34)
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover)
    (hSL : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hSchur : Lemma123.InputSchurAlt') (h67 : CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.AltSixSevenCentre)
    (hI1917 : Lemma123.Input19_17_2) (hI2324 : Lemma123.Input23_24) : Input27_5Core := by
  intro X _ _ hXK hO K hK B hB hB9 hN hC S hS hBS hSN hnc hcond
  rcases type_cases hXK hK with ⟨n, hn⟩ | ⟨r, hr⟩ | ⟨s, hsp⟩
  · exact Or.inr (concl_of_alt hSchur h67 hO hK hB hB9 hN hC hn)
  · rcases eq_or_ne r 2 with rfl | hr2
    · exact Or.inr (Or.inr (concl_of_chev2 hI1916 hI1920 hI712 hI7L hcov hSL hO hK hB hB9 hN hC hS hBS hSN
        hnc hcond hr))
    rcases eq_or_ne r 3 with rfl | hr3
    · exact Or.inl (le_iSup_centralizer_of_chev3 hI196 hI2317 hO hK hB hB9 hN hC
        (not_isLocallyOTwoBalanced_of_S hO hK hB hB9 hN hC hS hBS hSN hnc hcond) hr)
    · exact Or.inl (le_iSup_centralizer_of_chevq h2310 hO hK hB hB9 hN hr2 hr3 hr)
  · exact Or.inl (le_iSup_centralizer_of_spor hI1917 hI2324 hO hK hB hB9 hN hC hS hBS hSN hnc hcond hsp)

theorem input27_5_of_inputs (hI196 : Lemma123.Input19_6_4) (hI2317 : Lemma123.Input23_17)
    (h2310 : Claims1116.Input23_10) (hI1916 : Lemma123.Input19_16_two)
    (hI1920 : Lemma123.Input19_20_1) (hI712 : Lemma123.Input7_12_2) (hI7L : Input7_L34)
    (hcov : CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover)
    (hSL : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510iiNs.InputSL34Sylow)
    (hSchur : Lemma123.InputSchurAlt') (h67 : CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.AltSixSevenCentre)
    (hI1917 : Lemma123.Input19_17_2) (hI2324 : Lemma123.Input23_24) : Claims1245b.Input27_5 :=
  input27_5_of_core (input27_5Core_of_inputs hI196 hI2317 h2310 hI1916 hI1920 hI712 hI7L hcov hSL hSchur h67
    hI1917 hI2324)

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs27b
