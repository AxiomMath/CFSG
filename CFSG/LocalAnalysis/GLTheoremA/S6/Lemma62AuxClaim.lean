module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs62
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsShared
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

namespace L62

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem inf_glaPPrimeCoreOf_le (hp : p.Prime) {A I : Subgroup G}
    (hAI : A ≤ Subgroup.normalizer (GLAPPrimeCoreOf p I : Set G)) :
    A ⊓ GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p A := by
  set O := GLAPPrimeCoreOf p I with hO
  set N0 : Subgroup ↥A := O.subgroupOf A with hN0
  have hnorm : N0.Normal := by
    refine ⟨fun n hn h' => ?_⟩
    show ((h' * n * h'⁻¹ : ↥A) : G) ∈ O
    have := (Subgroup.mem_normalizer_iff.1 (hAI h'.2) (n : G)).1 hn
    simpa using this
  have hdvd : Nat.card N0 ∣ Nat.card O := by
    have h1 : N0.map A.subtype = A ⊓ O := by
      rw [hN0, ← Subgroup.inf_subgroupOf_right O A]
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : O ⊓ A ≤ A)]
      exact inf_comm _ _
    have h2 : Nat.card (N0.map A.subtype) = Nat.card N0 :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [← h2, h1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime p (Nat.card N0) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf hp I (hd.trans hdvd)
  have hle : N0 ≤ GLAPPrimeCore p ↥A := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx.2), rfl⟩

theorem glaPPrimeCoreOf_le_centModSubgroup (p : ℕ) (K : Subgroup G) :
    GLAPPrimeCoreOf p K ≤ centModSubgroup p K := by
  intro o ho
  have hoK : o ∈ K := Subgroup.map_subtype_le _ ho
  refine ⟨Subgroup.le_normalizer hoK, fun l hl => ?_⟩
  rw [commutatorElement_def]
  have : l * o * l⁻¹ ∈ GLAPPrimeCoreOf p K :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p K hl) o).1 ho
  exact (GLAPPrimeCoreOf p K).mul_mem this ((GLAPPrimeCoreOf p K).inv_mem ho)

theorem eq_sup_zpowers_of_index_prime (hp : p.Prime) {A D : Subgroup G} (hAD : A ≤ D)
    (hidx : (A.subgroupOf D).index = p) {d : G} (hdD : d ∈ D) (hdA : d ∉ A) :
    A ⊔ Subgroup.zpowers d = D := by
  have hMD : A ⊔ Subgroup.zpowers d ≤ D := sup_le hAD (Subgroup.zpowers_le.2 hdD)
  have hAM : A ≤ A ⊔ Subgroup.zpowers d := le_sup_left
  have hmul := Subgroup.relIndex_mul_relIndex A (A ⊔ Subgroup.zpowers d) D hAM hMD
  have hAD' : A.relIndex D = p := hidx
  rw [hAD'] at hmul
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ hmul) with h1 | h1
  · exfalso
    have : A ⊔ Subgroup.zpowers d ≤ A := (Subgroup.relIndex_eq_one.1 h1)
    exact hdA (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  · rw [h1] at hmul
    have h2 : (A ⊔ Subgroup.zpowers d).relIndex D = 1 :=
      Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one p).symm)
    exact le_antisymm hMD (Subgroup.relIndex_eq_one.1 h2)

theorem centB_eq (hp : p.Prime) {B D A J K : Subgroup G} (hDB : D ≤ B) (hAD : A ≤ D)
    (hidx : (A.subgroupOf D).index = p) (hKA : K ≤ Subgroup.centralizer (A : Set G)) (hJK : J ≤ K)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hker : ∀ b ∈ B, CentMod p J b ↔ b ∈ D)
    (hnontriv : ∃ d ∈ D, ¬ CentMod p K d) : B ⊓ centModSubgroup p K = A := by
  have hAcm : A ≤ centModSubgroup p K := fun a ha => by
    apply centMod_iff.1
    apply centMod_of_mem_centralizer
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.1 (hKA hk) a ha).symm
  apply le_antisymm
  · rintro b ⟨hbB, hbcm⟩
    have hbJ : b ∈ Subgroup.normalizer (J : Set G) := hBJ hbB
    have hJcm : CentMod p J b := by
      rw [centMod_iff]
      refine ⟨hbJ, fun l hl => ?_⟩
      have h1 : ⁅l, b⁆ ∈ GLAPPrimeCoreOf p K := hbcm.2 l (hJK hl)
      have h2 : ⁅l, b⁆ ∈ J := by
        have h3 : b * l⁻¹ * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hbJ _).1 (J.inv_mem hl)
        have e : ⁅l, b⁆ = l * (b * l⁻¹ * b⁻¹) := by
          simp only [commutatorElement_def, mul_assoc]
        rw [e]
        exact J.mul_mem hl h3
      exact inf_glaPPrimeCoreOf_le hp (hJK.trans (le_normalizer_glaPPrimeCoreOf p K)) ⟨h2, h1⟩
    have hbD : b ∈ D := (hker b hbB).1 hJcm
    by_contra hbA
    have hDeq := eq_sup_zpowers_of_index_prime hp hAD hidx hbD hbA
    obtain ⟨d, hdD, hd⟩ := hnontriv
    apply hd
    have hDle : D ≤ centModSubgroup p K :=
      hDeq ▸ sup_le hAcm (Subgroup.zpowers_le.2 hbcm)
    exact centMod_iff.2 (hDle hdD)
  · intro a ha
    exact ⟨hDB (hAD ha), hAcm ha⟩

theorem aut_rank (hp : p.Prime) {X B D J : Subgroup G} (hJ : GLAPComponent p X J)
    (hBel : IsElemAbelian p B) (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hDB : D ≤ B)
    (hker : ∀ b ∈ B, CentMod p J b ↔ b ∈ D) (hcard : p ^ 2 * Nat.card D ≤ Nat.card B) :
    ∃ A' : Subgroup (MulAut (PSimple p J)), IsElemAbelian p A' ∧ p ^ 2 ≤ Nat.card A' := by
  let f : ↥B →* MulAut (PSimple p J) := (phiC p J).comp (Subgroup.inclusion hBJ)
  have hfker : f.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (phiC p J) ⟨b, hBJ b.2⟩ = 1 ↔ (b : G) ∈ D
    rw [phiC_eq_one_iff hp hJ (hBJ b.2)]
    exact hker b b.2
  refine ⟨f.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    show (a : MulAut (PSimple p J)) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hBel x.2 y.2)
  · obtain ⟨x, hx⟩ := ha
    rw [← hx, ← map_pow]
    have : x ^ p = 1 := Subtype.ext (by simpa using hBel.2 (x : G) x.2)
    rw [this, map_one]
  · have h1 : Nat.card ↥B = Nat.card (↥B ⧸ f.ker) * Nat.card f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥B ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.ker = Nat.card D := by
      rw [hfker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
    have hDpos : 0 < Nat.card D := Nat.card_pos
    rw [h1, h2, h3] at hcard
    exact le_of_mul_le_mul_right hcard hDpos

theorem claim_beta (hp : p.Prime) (hp2 : p ≠ 2) (hcc : ChevClosureQAt G p) (h1416 : I1416At G p)
    (h2019 : I2019At G p) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    {B D A J K L S : Subgroup G} {x : G} (hBmax : GLAIsBmax p B)
    (hLX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)))
    (hLcomp : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hLchev : IsChevSimple q (PSimple p L))
    (hDB : D ≤ B) (hDcard : p ^ 2 * Nat.card D ≤ Nat.card B)
    (hJL : GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) J)
    (hJC : GLAPComponent p (Subgroup.centralizer (D : Set G)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hker : ∀ b ∈ B, CentMod p J b ↔ b ∈ D)
    (hAD : A ≤ D) (hidx : (A.subgroupOf D).index = p) (hAne : A ≠ ⊥)
    (hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G)))
    (hKcomp : GLAPComponent p (Subgroup.centralizer (A : Set G)) K) (hJK : J ≤ K)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hnontriv : ∃ d ∈ D, ¬ CentMod p K d)
    (hS2 : IsPGroup 2 S) (hSK : S ≤ K)
    (hJS : J ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G)) :
    ⁅S, J⁆ ≤ GLAPPrimeCoreOf p K := by
  have hBel : IsElemAbelian p B := hBmax.1
  have hDel : IsElemAbelian p D := isElemAbelian_mono hBel hDB
  have hKA : K ≤ Subgroup.centralizer (A : Set G) := hKcomp.1
  have hcentB := centB_eq hp hDB hAD hidx hKA hJK hBJ hker hnontriv
  obtain ⟨d, hdD, hd⟩ := hnontriv
  have hAcm : A ≤ centModSubgroup p K := hcentB ▸ inf_le_right
  have hdA : d ∉ A := fun h => hd (centMod_iff.2 (hAcm h))
  have hDeq := eq_sup_zpowers_of_index_prime hp hAD hidx hdD hdA
  have hKd : K ⊓ Subgroup.centralizer ({d} : Set G) = K ⊓ Subgroup.centralizer (D : Set G) := by
    apply le_antisymm
    · refine le_inf inf_le_left fun k hk => ?_
      have hkK : k ∈ K := hk.1
      have hkd : k ∈ Subgroup.centralizer ({d} : Set G) := hk.2
      have hDle : D ≤ Subgroup.centralizer ({k} : Set G) := by
        rw [← hDeq]
        refine sup_le (fun a ha => ?_) ?_
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.1 (hKA hkK) a ha
        · rw [Subgroup.zpowers_le]
          rw [Subgroup.mem_centralizer_singleton_iff] at hkd ⊢
          exact hkd.symm
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.1 (hDle hy)
    · exact le_inf inf_le_left
        (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD)))
  have hJKD : GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set G)) J :=
    glaPComponent_of_le hp hJC (le_inf hJK hJC.1) inf_le_right
  have hJKd : GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set G)) J := hKd ▸ hJKD
  have hJchev : IsChevSimple q (PSimple p J) :=
    hcc hp hp2 q hq _ L D hLX hLcomp hLchev hDel (hDB.trans hBL) J hJL
  have hrank := aut_rank hp hJC hBel hBJ hDB hker hDcard
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := hBK (hDB hdD)
  have hd1 : d ^ p = 1 := hDel.2 d hdD
  have hKchev : IsChevSimple q (PSimple p K) :=
    h1416 hp hp2 q hq hq2 hqp _ K J d hX hKcomp hdN hd1 hd hJKd hJchev hrank
  have hKq := isQuasisimple_pQuot_of_glaPComponent hp hKcomp
  exact h2019 hp hp2 q hq hq2 hqp B D K J hBmax hBK hKq hKchev (hcentB ▸ hAne) hDB
    (hcentB ▸ hAD) (le_of_eq (by rw [hcentB]; exact hidx)) hDcard hJKD hBJ hker S hSK hS2 hJS

theorem le_sup_core_of_centMod (hp : p.Prime) {X K D J : Subgroup G} (hK : GLAPComponent p X K)
    (hD : IsPGroup p D) (hDK : ∀ d ∈ D, CentMod p K d)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set G)) J) :
    K ≤ J ⊔ GLAPPrimeCoreOf p K := by
  obtain ⟨-, hall, -, hsup, -⟩ := glaPLayer_inf_centralizer_of_isPGroup hp hK hD
    (fun d hd => centMod_iff.1 (hDK d hd))
  rw [hall J hJ]
  exact hsup.ge

theorem gLBConj_closureIn_le {J H : Subgroup G} {b : G} (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hbH : b ∈ Subgroup.normalizer (H : Set G)) :
    GLBConj b (closureIn J H) ≤ closureIn J H := by
  rw [closureIn_eq_iSup_gLBConj]
  refine i183_gLBConj_iSup_le fun g hg => ?_
  rw [gLBConj_gLBConj]
  have e : g * b = b * (b⁻¹ * g * b) := by group
  rw [e, ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer hbJ]
  exact le_biSup (fun g => GLBConj g J) ((Subgroup.mem_normalizer_iff''.1 hbH g).1 hg)

theorem le_normalizer_closureIn_of_le {B J H : Subgroup G} (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hBH : B ≤ Subgroup.normalizer (H : Set G)) :
    B ≤ Subgroup.normalizer (closureIn J H : Set G) := fun b hb =>
  i183_mem_normalizer_of_gLBConj_le (gLBConj_closureIn_le (hBJ hb) (hBH hb))
    (gLBConj_closureIn_le (Subgroup.inv_mem _ (hBJ hb)) (Subgroup.inv_mem _ (hBH hb)))

theorem exists_ne_one_mem (hp : p.Prime) {D A : Subgroup G} (hD2 : p ^ 2 ≤ Nat.card D) (hAD : A ≤ D)
    (hidx : (A.subgroupOf D).index = p) : ∃ a ∈ A, a ≠ 1 := by
  have hAne : A ≠ ⊥ := by
    intro h
    have h1 : Nat.card (A.subgroupOf D) * (A.subgroupOf D).index = Nat.card D :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (A.subgroupOf D) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv
    rw [h2, hidx, h, Subgroup.card_bot, one_mul] at h1
    rw [← h1] at hD2
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem centralizer_isKGroup (hc : S6Ctx G p) {A : Subgroup G} {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) :
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G)) :=
  CFSG.Open.IsKGroup.of_le (kGroup_centralizer hc ha1)
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA))

theorem partB (hc : S6Ctx G p) (h183 : Input18_3_4) (hdiag : I183DiagAt G p)
    (hcc : ChevClosureQAt G p) (h1416 : I1416At G p) (h2019 : I2019At G p)
    (h145 : I145UsedAt G p) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    {B : Subgroup G} {x : G} {L D J A J₀ S : Subgroup G}
    (hT : InTq q p B x L) (hD : InD p B x L D J)
    (hAD : A ≤ D) (hidx : (A.subgroupOf D).index = p) (hJ₀J : J₀ ≤ J)
    (hJ₀cov : J₀ ⊔ GLAPPrimeCoreOf p J = J) (hS2 : IsPGroup 2 S)
    (hSA : S ≤ Subgroup.centralizer (A : Set G)) (hJ₀S : J₀ ≤ Subgroup.normalizer (S : Set G))
    (hSJ₀ : S ≤ ⁅S, J₀⁆) :
    S ≤ GLAPPrimeCoreOf p (layerClosure p A J) := by
  have hp := hc.prime
  have hp2 := hc.odd
  obtain ⟨hT0, hLchev⟩ := hT
  have hT1 := hT0
  obtain ⟨hBmax, hxB, hx1, hLcomp, hBL, hCM⟩ := hT0
  have hBel : IsElemAbelian p B := hBmax.1
  have hDB : D ≤ B := hD.1.1
  have hDel : IsElemAbelian p D := isElemAbelian_mono hBel hDB
  have hDp : IsPGroup p D := isPGroup_of_isElemAbelian hDel
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hD.2.1.2.1
  have hker : ∀ b ∈ B, CentMod p J b ↔ b ∈ D := hD.2.1.2.2
  have hJC : GLAPComponent p (Subgroup.centralizer (D : Set G)) J := J_comp_centralizer hp hT1 hD
  obtain ⟨a, haA, ha1⟩ := exists_ne_one_mem hp hD.1.2.1 hAD hidx
  have hAne : A ≠ ⊥ := fun h => ha1 (by simpa [h] using haA)
  have hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G)) := centralizer_isKGroup hc haA ha1
  have hLX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) := kGroup_centralizer hc hx1
  obtain ⟨𝒞, hcomp, hsup, hcl, htr, hJK, hne⟩ := exists_family hp h183 hX hAD hDel hJC
  have hKsub := layerClosure_isSubnormal hp hcomp hsup
  have hBA : B ≤ Subgroup.centralizer (A : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact isElemAbelian_commute hBel (hDB (hAD he)) hb
  have hBK : B ≤ Subgroup.normalizer (layerClosure p A J : Set G) := by
    have hKeq : layerClosure p A J = closureIn J (GLAPLayer p (Subgroup.centralizer (A : Set G))) :=
      (closureIn_eq_iSup_gLBConj J _).symm
    rw [hKeq]
    exact le_normalizer_closureIn_of_le hBJ (hBA.trans (le_normalizer_glaPLayer p _))
  have hsup0 := hsup
  generalize layerClosure p A J = K at hsup hJK hKsub hBK ⊢
  have hSK : S ≤ K := le_of_subnormal_comm_eq hKsub (hJ₀J.trans hJK) hSA hSJ₀
  have hDX : D ≤ Subgroup.centralizer (A : Set G) := fun d hd => by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact isElemAbelian_commute hDel (hAD he) hd
  have hI := h145 hp hp2 _ D hX hDX hDp
  have hCAD : Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer (D : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAD))
  rw [hCAD] at hI
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJC
  have hJL' : J ≤ GLAPLayer p (Subgroup.centralizer (D : Set G)) := le_sSup hJC
  have hOJ : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (D : Set G)) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hJC.2.1
  have hOJle : GLAPPrimeCoreOf p J ≤ J := Subgroup.map_subtype_le _
  have hcomm1 : ⁅J, GLAPPrimeCoreOf p J⁆ ≤ GLAPPrimeCoreOf p K := by
    have h1 : ⁅J, GLAPPrimeCoreOf p J⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) :=
      (Subgroup.commutator_mono hJL' hOJ).trans hI
    have h2 : ⁅J, GLAPPrimeCoreOf p J⁆ ≤ K :=
      ((Subgroup.commutator_mono le_rfl hOJle).trans hJperf.le).trans hJK
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hKsub]
    exact le_inf h2 h1
  have hKO : K ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    le_normalizer_glaPPrimeCoreOf p K
  have hJleJ0 : J ≤ J₀ ⊔ GLAPPrimeCoreOf p K :=
    le_sup_of_perfect_cover hJperf hJ₀J hJ₀cov hOJle (le_normalizer_glaPPrimeCoreOf p J)
      (hJK.trans hKO) hcomm1
  have hJS : J ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p K : Subgroup G) : Set G) := by
    refine hJleJ0.trans (sup_le (fun j hj => ?_) (fun o ho => ?_))
    · exact i183_mem_normalizer_sup (hJ₀S hj) (hKO (hJK (hJ₀J hj)))
    · exact Subgroup.le_normalizer (Subgroup.mem_sup_right ho)
  have hmain : ⁅S, J⁆ ≤ GLAPPrimeCoreOf p K := by
    by_cases h2 : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂
    ·
      have hproj := hdiag hp hp2 A D J 𝒞 hDel hAD hidx hX hJC hcomp hsup0 hcl htr h2
      exact claim_of_projection hp hcomp hsup hKsub hJK hS2 hSK hJS hproj
    · push Not at h2
      obtain ⟨K₁, hK₁⟩ := hne
      have hKK₁ : K = K₁ := by
        rw [← hsup]
        exact le_antisymm (iSup₂_le fun C hC => (h2 C hC K₁ hK₁).le)
          (le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) K₁ hK₁)
      have hKcomp : GLAPComponent p (Subgroup.centralizer (A : Set G)) K := hKK₁ ▸ hcomp K₁ hK₁
      have hJKD : GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set G)) J :=
        glaPComponent_of_le hp hJC (le_inf hJK hJC.1) inf_le_right
      by_cases hcen : ∀ d ∈ D, CentMod p K d
      ·
        have hcov : K ≤ J ⊔ GLAPPrimeCoreOf p K := le_sup_core_of_centMod hp hKcomp hDp hcen hJKD
        have hproj : ∀ C ∈ 𝒞, C ≤ J ⊔ centModSubgroup p C := by
          intro C hC
          have hCK : C = K := (h2 C hC K₁ hK₁).trans hKK₁.symm
          rw [hCK]
          exact hcov.trans (sup_le_sup_left (glaPPrimeCoreOf_le_centModSubgroup p K) J)
        exact claim_of_projection hp hcomp hsup hKsub hJK hS2 hSK hJS hproj
      · push Not at hcen
        exact claim_beta hp hp2 hcc h1416 h2019 hq hq2 hqp hBmax hLX hLcomp hBL hLchev hDB hD.1.2.2
          hD.2.1.1 hJC hBJ hker hAD hidx hAne hX hKcomp hJK hBK hcen hS2 hSK hJS
  exact hSJ₀.trans ((Subgroup.commutator_mono le_rfl hJ₀J).trans hmain)

end L62

end CFSG.LocalAnalysis.GLTheoremA
