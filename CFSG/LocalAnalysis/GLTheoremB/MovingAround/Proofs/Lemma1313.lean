module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1311

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf barAut_mk)

section Basic

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_glaPPrimeCoreOf (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p H)) := by
  have h1 : Nat.card ↥(GLAPPrimeCoreOf p H) = Nat.card ↥(GLAPPrimeCore p ↥H) := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.card_map_of_injective (f := H.subtype) Subtype.val_injective
  rw [h1]
  exact CFSG.pPrimeCore_coprime_card

theorem le_glaPPrimeCore_of_normal {p : ℕ} (H : Type) [Group H] [Finite H] {K : Subgroup H}
    (hK : K.Normal) (hcop : Nat.Coprime p (Nat.card K)) : K ≤ GLAPPrimeCore p H := by
  unfold GLAPPrimeCore CFSG.pPrimeCore
  exact le_sSup ⟨hK, hcop⟩

theorem eq_top_of_isComponentOf_quasisimple {X : Type} [Group X] {K : Subgroup X}
    (hX : CFSG.Open.IsQuasisimple X) (hK : CFSG.Open.IsComponentOf K ⊤) : K = ⊤ := by
  obtain ⟨-, hsn, hq⟩ := hK
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hX K hsn with
    h | h
  · exfalso
    have hnt := hq.2.1
    rw [h] at hnt
    exact not_nontrivial_iff_subsingleton.2 (by
      infer_instance) hnt
  · exact h

end Basic

section Core

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCoreOf_gLBConj_eq {p : ℕ} {L0 : Subgroup G} {b : G} (hnorm : GLBConj b L0 = L0) :
    GLBConj b (GLAPPrimeCoreOf p L0) = GLAPPrimeCoreOf p L0 := by
  rw [← glaPPrimeCoreOf_gLBConj, hnorm]

theorem mem_normalizer_glaPPrimeCoreOf {p : ℕ} {L0 : Subgroup G} {x : G} (hx : x ∈ L0) :
    x ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p L0 : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hN : GLBConj x L0 = L0 := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)
  have h2 : GLBConj x (GLAPPrimeCoreOf p L0) = GLAPPrimeCoreOf p L0 := by
    rw [← glaPPrimeCoreOf_gLBConj, hN]
  rw [← mem_gLBConj, h2]

theorem glaPPrimeCoreOf_le_self {p : ℕ} (H : Subgroup G) : GLAPPrimeCoreOf p H ≤ H := by
  unfold GLAPPrimeCoreOf
  rintro _ ⟨k, -, rfl⟩
  exact k.2

theorem cover_centralizer {p : ℕ} [Fact p.Prime] {L0 : Subgroup G} {b : G}
    (hbord : orderOf b = p) (hnorm : GLBConj b L0 = L0)
    (hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0) :
    ∀ x ∈ L0, ∃ y ∈ L0 ⊓ Subgroup.centralizer ({b} : Set G), ∃ n ∈ GLAPPrimeCoreOf p L0,
      x = y * n := by
  intro x hx
  have hd : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbord, pow_one])
  have hVp : ¬ p ∣ Nat.card ↥(GLAPPrimeCoreOf p L0) :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out)).1 (coprime_card_glaPPrimeCoreOf p L0)
  have hdV : b ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p L0 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    rw [← mem_gLBConj, glaPPrimeCoreOf_gLBConj_eq hnorm]
  have hxV := mem_normalizer_glaPPrimeCoreOf (p := p) hx
  obtain ⟨v, hv, hxv⟩ := exists_mul_mem_centralizer hd hVp hdV hxV (hcomm x hx)
  have hvL : v ∈ L0 := glaPPrimeCoreOf_le_self L0 hv
  refine ⟨x * v, ⟨L0.mul_mem hx hvL, hxv⟩, v⁻¹, (GLAPPrimeCoreOf p L0).inv_mem hv, ?_⟩
  simp

theorem barOf_glaPLayer_inf_cent_iso {p : ℕ} [Fact p.Prime] {L0 : Subgroup G} {b : G}
    (hbord : orderOf b = p) (hnorm : GLBConj b L0 = L0)
    (hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0)
    (hquasi : CFSG.Open.IsQuasisimple (barOf p L0)) :
    Nonempty (barOf p (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) ≃* barOf p L0) := by
  classical
  set Y : Subgroup G := L0 ⊓ Subgroup.centralizer ({b} : Set G) with hYdef
  have hYL0 : Y ≤ L0 := inf_le_left
  let f : ↥Y →* (↥L0 ⧸ GLAPPrimeCore p ↥L0) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L0)).comp (Subgroup.inclusion hYL0)
  have hcov := cover_centralizer hbord hnorm hcomm
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hyY, n, hn, hxyn⟩ := hcov (x : G) x.2
    refine ⟨⟨y, hyY⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hYL0 ⟨y, hyY⟩) : ↥L0 ⧸ GLAPPrimeCore p ↥L0) =
      QuotientGroup.mk x
    rw [QuotientGroup.eq]
    have hn' : n ∈ (GLAPPrimeCore p ↥L0).map L0.subtype := hn
    obtain ⟨n', hn'mem, hn'eq⟩ := Subgroup.mem_map.1 hn'
    have key : (Subgroup.inclusion hYL0 ⟨y, hyY⟩ : ↥L0)⁻¹ * x = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, Subtype.coe_mk]
      have hn'val : (n' : G) = n := hn'eq
      rw [hxyn, hn'val]
      group
    rw [key]
    exact hn'mem
  have hkerle : f.ker ≤ GLAPPrimeCore p ↥Y := by
    have hcop : Nat.Coprime p (Nat.card ↥f.ker) := by
      have hmap : f.ker.map (Subgroup.inclusion hYL0) ≤ GLAPPrimeCore p ↥L0 := by
        rintro _ ⟨k, hk, rfl⟩
        have hk1 : f k = 1 := hk
        have hk2 : QuotientGroup.mk (Subgroup.inclusion hYL0 k) = (1 : ↥L0 ⧸ GLAPPrimeCore p ↥L0) := hk1
        exact (QuotientGroup.eq_one_iff _).1 hk2
      have hcard : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL0)) = Nat.card ↥f.ker :=
        Subgroup.card_map_of_injective (f := Subgroup.inclusion hYL0)
          (Subgroup.inclusion_injective hYL0)
      have hdvd : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL0)) ∣
          Nat.card ↥(GLAPPrimeCore p ↥L0) := Subgroup.card_dvd_of_le hmap
      have h2 := Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L0))
      rw [hcard] at h2
      exact h2
    exact le_glaPPrimeCore_of_normal (p := p) ↥Y (K := f.ker) inferInstance hcop
  have hkerge : GLAPPrimeCore p ↥Y ≤ f.ker := by
    intro t ht
    have hTn : (GLAPPrimeCore p ↥Y).Normal := inferInstance
    have hmapN : ((GLAPPrimeCore p ↥Y).map f).Normal := hTn.map f hsurj
    have hcop : Nat.Coprime p (Nat.card ↥((GLAPPrimeCore p ↥Y).map f)) := by
      have hdvd := Subgroup.card_map_dvd (GLAPPrimeCore p ↥Y) f
      exact Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥Y))
    have hle := le_glaPPrimeCore_of_normal (p := p) (↥L0 ⧸ GLAPPrimeCore p ↥L0) hmapN hcop
    rw [Lemma1311.glaPPrimeCore_quot_eq_bot p ↥L0] at hle
    have hft : f t ∈ (GLAPPrimeCore p ↥Y).map f := Subgroup.mem_map_of_mem f ht
    have h1 : f t = 1 := (Subgroup.mem_bot).1 (hle hft)
    exact h1
  have hker : GLAPPrimeCore p ↥Y = f.ker := le_antisymm hkerge hkerle
  let e1 : (↥Y ⧸ GLAPPrimeCore p ↥Y) ≃* (↥L0 ⧸ GLAPPrimeCore p ↥L0) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  have hYq : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore p ↥Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1.symm hquasi
  have hYqTop : CFSG.Open.IsQuasisimple (↥(⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y))) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)) ≃* (↥Y ⧸ GLAPPrimeCore p ↥Y)).symm
      hYq
  obtain ⟨K, hKc, hKtop⟩ := exists_glaPComponent_barX_eq (p := p) Y
    (K := (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)))
    ⟨le_top, CFSG.Open.IsSubnormal.refl ⊤, hYqTop⟩
  have huniq : ∀ J : Subgroup G, GLAPComponent p Y J → J = K := by
    intro J hJ
    have hc : CFSG.Open.IsComponentOf (barX p Y J) ⊤ := hJ.2.2.1
    have htop : barX p Y J = ⊤ := eq_top_of_isComponentOf_quasisimple hYq hc
    exact glaPComponent_unique hJ hKc (htop.trans hKtop.symm)
  have hlayer : GLAPLayer p Y = K := by
    have hset : {L : Subgroup G | GLAPComponent p Y L} = {K} := by
      ext L
      constructor
      · intro hL
        exact huniq L hL
      · intro hL
        rw [Set.mem_singleton_iff] at hL
        rw [hL]
        exact hKc
    unfold GLAPLayer
    show sSup {L : Subgroup G | GLAPComponent p Y L} = K
    rw [hset, sSup_singleton]
  rw [hlayer]
  have e2 : barOf p K ≃* ↥(barX p Y K) := quotEquivBarX (Fact.out : Nat.Prime p) hKc.1 hKc.2.1
  have e3 : ↥(barX p Y K) ≃* (↥Y ⧸ GLAPPrimeCore p ↥Y) :=
    (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
  exact ⟨e2.trans (e3.trans e1)⟩

end Core

section Setting

variable {G : Type} [Group G] [Finite G]

theorem inv_mul_mem_glaPPrimeCoreOf_of_centBar {p : ℕ} [Fact p.Prime] {X L : Subgroup G} {c : G}
    (hc : c ∈ centBar p X L) {x : G} (hx : x ∈ L) :
    (c * x * c⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨hmem, -⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨γ, hγ, hγc⟩ := Subgroup.mem_map.1 hmem
  have h1 : barAut p L γ = 1 := MonoidHom.mem_ker.1 hγ
  have h2 := congrArg (fun φ : MulAut (↥L ⧸ GLAPPrimeCore p ↥L) => φ (QuotientGroup.mk ⟨x, hx⟩)) h1
  simp only [MulAut.one_apply] at h2
  rw [barAut_mk] at h2
  have h3 := (QuotientGroup.eq).1 h2
  unfold GLAPPrimeCoreOf
  refine ⟨_, h3, ?_⟩
  rw [← hγc]
  rfl

theorem mem_glaPPrimeCoreOf_of_mem_of_normalized {p : ℕ} [Fact p.Prime] {I P N : Subgroup G}
    (hPI : P ≤ I) (hN : ∀ q ∈ I, GLBConj q N = N) (hcop : Nat.Coprime p (Nat.card ↥N))
    {z : G} (hzN : z ∈ N) (hzP : z ∈ P) : z ∈ GLAPPrimeCoreOf p P := by
  have hKn : ((N ⊓ P).subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnN, hnP⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hmem : (n : G) ∈ GLBConj (g : G) N := by
        rw [hN _ (hPI g.2)]
        exact hnN
      have := mem_gLBConj.1 hmem
      simpa [mul_assoc] using this
    · exact P.mul_mem (P.mul_mem g.2 hnP) (P.inv_mem g.2)
  have hcard : Nat.card ↥(((N ⊓ P).subgroupOf P).map P.subtype) = Nat.card ↥((N ⊓ P).subgroupOf P) :=
    Subgroup.card_map_of_injective (f := P.subtype) Subtype.val_injective
  have hle : ((N ⊓ P).subgroupOf P).map P.subtype ≤ N := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 hk)).1
  have hdvd := Subgroup.card_dvd_of_le hle
  have hcop' : Nat.Coprime p (Nat.card ↥((N ⊓ P).subgroupOf P)) := by
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd hcop
  have hK := le_glaPPrimeCore_of_normal (p := p) ↥P hKn hcop'
  have hmemK : (⟨z, hzP⟩ : ↥P) ∈ (N ⊓ P).subgroupOf P :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hzN, hzP⟩)
  exact ⟨⟨z, hzP⟩, hK hmemK, rfl⟩

theorem gLBConj_gLBConj_mul' (q g : G) (H : Subgroup G) :
    GLBConj q (GLBConj g H) = GLBConj (g * q) H := by
  ext y
  rw [mem_gLBConj, mem_gLBConj, mem_gLBConj]
  have e : g * q * y * (g * q)⁻¹ = g * (q * y * q⁻¹) * g⁻¹ := by group
  rw [e]

theorem L1of_gLBConj_eq_of_mem_istar {p : ℕ} {M D L0 : Subgroup G} {q : G}
    (hq : q ∈ Istar p M D) :
    GLBConj q (L1of p M D L0) = L1of p M D L0 := by
  apply le_antisymm
  · unfold L1of
    rw [gLBConj_iSup_eq]
    refine iSup_le fun g => ?_
    by_cases hg : g ∈ Istar p M D
    · rw [iSup_pos hg, gLBConj_gLBConj_mul']
      exact le_iSup₂_of_le (g * q) ((Istar p M D).mul_mem hg hq) le_rfl
    · rw [iSup_neg hg]
      unfold GLBConj
      rw [Subgroup.map_bot]
      exact bot_le
  · unfold L1of
    refine iSup₂_le fun g hg => ?_
    have e : GLBConj g L0 = GLBConj q (GLBConj (g * q⁻¹) L0) := by
      rw [gLBConj_gLBConj_mul', mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact gLBConj_mono q (le_iSup₂_of_le (g * q⁻¹) ((Istar p M D).mul_mem hg ((Istar p M D).inv_mem hq))
      le_rfl)

theorem glbConj_eq_of_pComp {p : ℕ} [Fact p.Prime] {I P L0 L1 : Subgroup G} {b : G}
    (hL0P : GLAPComponent p P L0) (hPI : P ≤ I)
    (hPb : GLBConj b P = P) (hL0L1 : L0 ≤ L1) (hbL1 : GLBConj b L1 = L1)
    (hN : ∀ q ∈ I, GLBConj q (GLAPPrimeCoreOf p L1) = GLAPPrimeCoreOf p L1)
    (hcb : ∀ x ∈ L1, (b * x * b⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p L1)
    (hcb' : ∀ x ∈ L1, (b⁻¹ * x * b)⁻¹ * x ∈ GLAPPrimeCoreOf p L1) :
    GLBConj b L0 = L0 := by
  have hcomp' : GLAPComponent p P (GLBConj b L0) := by
    have := glaPComponent_gLBConj hL0P b
    rwa [hPb] at this
  have hL0P_le : L0 ≤ P := hL0P.1
  have hcopL1 : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p L1)) := coprime_card_glaPPrimeCoreOf p L1
  have hconjL1 : ∀ k ∈ GLBConj b L0, k ∈ L1 := by
    intro k hk
    have h := gLBConj_mono b hL0L1 hk
    rwa [hbL1] at h
  have hconjP : GLBConj b L0 ≤ P := hcomp'.1
  apply glaPComponent_unique hcomp' hL0P
  apply le_antisymm
  · apply barX_le_of_forall hL0P_le
    intro k hk
    refine ⟨b * k * b⁻¹, mem_gLBConj.1 hk, ?_⟩
    apply mem_glaPPrimeCoreOf_of_mem_of_normalized hPI hN hcopL1
    · exact hcb k (hconjL1 k hk)
    · exact P.mul_mem (P.inv_mem (hL0P_le (mem_gLBConj.1 hk))) (hconjP hk)
  · apply barX_le_of_forall hconjP
    intro x hx
    have hj : b⁻¹ * x * b ∈ GLBConj b L0 := by
      rw [mem_gLBConj]
      have e : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
      rw [e]
      exact hx
    refine ⟨b⁻¹ * x * b, hj, ?_⟩
    apply mem_glaPPrimeCoreOf_of_mem_of_normalized hPI hN hcopL1
    · exact hcb' x (hL0L1 hx)
    · exact P.mul_mem (P.inv_mem (hconjP hj)) (hL0P_le hx)

theorem comm_mem_glaPPrimeCoreOf {p : ℕ} [Fact p.Prime] {L0 L1 : Subgroup G} {b : G}
    (hL0L1 : L0 ≤ L1) (hnorm : GLBConj b L0 = L0)
    (hcb : ∀ x ∈ L1, (b * x * b⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p L1) :
    ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0 := by
  intro x hx
  have hbx : b * x * b⁻¹ ∈ L0 := by
    rw [← mem_gLBConj, hnorm]
    exact hx
  have hw := hcb x (hL0L1 hx)
  have hcomm_eq : b * x * b⁻¹ * x⁻¹ = x * ((b * x * b⁻¹)⁻¹ * x)⁻¹ * x⁻¹ := by group
  have hxn := mem_normalizer_glaPPrimeCoreOf (p := p) (hL0L1 hx)
  rw [Subgroup.mem_normalizer_iff] at hxn
  have hO1 : b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L1 := by
    rw [hcomm_eq]
    exact (hxn (((b * x * b⁻¹)⁻¹ * x)⁻¹)).1 ((GLAPPrimeCoreOf p L1).inv_mem hw)
  have hz : b * x * b⁻¹ * x⁻¹ ∈ L0 := L0.mul_mem hbx (L0.inv_mem hx)
  exact mem_glaPPrimeCoreOf_of_mem_of_normalized (I := L1) (P := L0) (N := GLAPPrimeCoreOf p L1)
    hL0L1 (fun q hq => gLBConj_eq_of_mem_normalizer (mem_normalizer_glaPPrimeCoreOf (p := p) hq))
    (coprime_card_glaPPrimeCoreOf p L1) hO1 hz

theorem covering_data {p : ℕ} [Fact p.Prime] {L0 : Subgroup G} {b : G}
    (hbord : orderOf b = p) (hnorm : GLBConj b L0 = L0)
    (hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0)
    (hquasi : CFSG.Open.IsQuasisimple (barOf p L0)) :
    GLAPPrimeCoreOf p (L0 ⊓ Subgroup.centralizer ({b} : Set G)) ≤ GLAPPrimeCoreOf p L0 ∧
      barX p (L0 ⊓ Subgroup.centralizer ({b} : Set G))
        (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) = ⊤ := by
  classical
  set Y : Subgroup G := L0 ⊓ Subgroup.centralizer ({b} : Set G) with hYdef
  have hYL0 : Y ≤ L0 := inf_le_left
  let f : ↥Y →* (↥L0 ⧸ GLAPPrimeCore p ↥L0) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L0)).comp (Subgroup.inclusion hYL0)
  have hcov := cover_centralizer hbord hnorm hcomm
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hyY, n, hn, hxyn⟩ := hcov (x : G) x.2
    refine ⟨⟨y, hyY⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hYL0 ⟨y, hyY⟩) : ↥L0 ⧸ GLAPPrimeCore p ↥L0) =
      QuotientGroup.mk x
    rw [QuotientGroup.eq]
    have hn' : n ∈ (GLAPPrimeCore p ↥L0).map L0.subtype := hn
    obtain ⟨n', hn'mem, hn'eq⟩ := Subgroup.mem_map.1 hn'
    have key : (Subgroup.inclusion hYL0 ⟨y, hyY⟩ : ↥L0)⁻¹ * x = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, Subtype.coe_mk]
      have hn'val : (n' : G) = n := hn'eq
      rw [hxyn, hn'val]
      group
    rw [key]
    exact hn'mem
  have hkerle : f.ker ≤ GLAPPrimeCore p ↥Y := by
    have hcop : Nat.Coprime p (Nat.card ↥f.ker) := by
      have hmap : f.ker.map (Subgroup.inclusion hYL0) ≤ GLAPPrimeCore p ↥L0 := by
        rintro _ ⟨k, hk, rfl⟩
        have hk1 : f k = 1 := hk
        have hk2 : QuotientGroup.mk (Subgroup.inclusion hYL0 k) = (1 : ↥L0 ⧸ GLAPPrimeCore p ↥L0) := hk1
        exact (QuotientGroup.eq_one_iff _).1 hk2
      have hcard : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL0)) = Nat.card ↥f.ker :=
        Subgroup.card_map_of_injective (f := Subgroup.inclusion hYL0)
          (Subgroup.inclusion_injective hYL0)
      have hdvd : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL0)) ∣
          Nat.card ↥(GLAPPrimeCore p ↥L0) := Subgroup.card_dvd_of_le hmap
      have h2 := Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L0))
      rw [hcard] at h2
      exact h2
    exact le_glaPPrimeCore_of_normal (p := p) ↥Y (K := f.ker) inferInstance hcop
  have hkerge : GLAPPrimeCore p ↥Y ≤ f.ker := by
    intro t ht
    have hTn : (GLAPPrimeCore p ↥Y).Normal := inferInstance
    have hmapN : ((GLAPPrimeCore p ↥Y).map f).Normal := hTn.map f hsurj
    have hcop : Nat.Coprime p (Nat.card ↥((GLAPPrimeCore p ↥Y).map f)) := by
      have hdvd := Subgroup.card_map_dvd (GLAPPrimeCore p ↥Y) f
      exact Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥Y))
    have hle := le_glaPPrimeCore_of_normal (p := p) (↥L0 ⧸ GLAPPrimeCore p ↥L0) hmapN hcop
    rw [Lemma1311.glaPPrimeCore_quot_eq_bot p ↥L0] at hle
    have hft : f t ∈ (GLAPPrimeCore p ↥Y).map f := Subgroup.mem_map_of_mem f ht
    exact (Subgroup.mem_bot).1 (hle hft)
  have hker : GLAPPrimeCore p ↥Y = f.ker := le_antisymm hkerge hkerle
  let e1 : (↥Y ⧸ GLAPPrimeCore p ↥Y) ≃* (↥L0 ⧸ GLAPPrimeCore p ↥L0) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  have hYq : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore p ↥Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1.symm hquasi
  have hYqTop : CFSG.Open.IsQuasisimple (↥(⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y))) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)) ≃* (↥Y ⧸ GLAPPrimeCore p ↥Y)).symm
      hYq
  obtain ⟨K, hKc, hKtop⟩ := exists_glaPComponent_barX_eq (p := p) Y
    (K := (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)))
    ⟨le_top, CFSG.Open.IsSubnormal.refl ⊤, hYqTop⟩
  have huniq : ∀ J : Subgroup G, GLAPComponent p Y J → J = K := by
    intro J hJ
    have hc : CFSG.Open.IsComponentOf (barX p Y J) ⊤ := hJ.2.2.1
    have htop : barX p Y J = ⊤ := eq_top_of_isComponentOf_quasisimple hYq hc
    exact glaPComponent_unique hJ hKc (htop.trans hKtop.symm)
  have hlayer : GLAPLayer p Y = K := by
    have hset : {L : Subgroup G | GLAPComponent p Y L} = {K} := by
      ext L
      constructor
      · intro hL
        exact huniq L hL
      · intro hL
        rw [Set.mem_singleton_iff] at hL
        rw [hL]
        exact hKc
    unfold GLAPLayer
    show sSup {L : Subgroup G | GLAPComponent p Y L} = K
    rw [hset, sSup_singleton]
  refine ⟨?_, ?_⟩
  ·
    unfold GLAPPrimeCoreOf
    rintro _ ⟨w, hw, rfl⟩
    have hwf : f w = 1 := by
      have : w ∈ f.ker := by rw [← hker]; exact hw
      exact this
    have hw2 : QuotientGroup.mk (Subgroup.inclusion hYL0 w) = (1 : ↥L0 ⧸ GLAPPrimeCore p ↥L0) := hwf
    exact ⟨Subgroup.inclusion hYL0 w, (QuotientGroup.eq_one_iff _).1 hw2, rfl⟩
  · rw [hlayer, hKtop]

theorem isQuasisimple_barOf_of_pComp {p : ℕ} [Fact p.Prime] {P L0 : Subgroup G}
    (hL0P : GLAPComponent p P L0) : CFSG.Open.IsQuasisimple (barOf p L0) := by
  have e : barOf p L0 ≃* ↥(barX p P L0) := quotEquivBarX (Fact.out : Nat.Prime p) hL0P.1 hL0P.2.1
  have hc : CFSG.Open.IsComponentOf (barX p P L0) ⊤ := hL0P.2.2.1
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hc.2.2

theorem mem_normalizer_of_centBar {p : ℕ} {X L : Subgroup G} {c : G} (hc : c ∈ centBar p X L) :
    c ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hmem, -⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨γ, -, hγc⟩ := Subgroup.mem_map.1 hmem
  rw [← hγc]
  exact γ.2

theorem gLBConj_centralizer_singleton_of_comm {d b : G} (hbd : d * b = b * d) :
    GLBConj b (Subgroup.centralizer ({d} : Set G)) = Subgroup.centralizer ({d} : Set G) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  have hbdb : b⁻¹ * d * b = d := by rw [mul_assoc, hbd, ← mul_assoc, inv_mul_cancel, one_mul]
  constructor
  · intro h
    have h1 : b⁻¹ * (d * (b * y * b⁻¹)) * b = b⁻¹ * ((b * y * b⁻¹) * d) * b := by rw [h]
    have e1 : b⁻¹ * (d * (b * y * b⁻¹)) * b = d * y := by
      calc b⁻¹ * (d * (b * y * b⁻¹)) * b = (b⁻¹ * d * b) * y := by group
        _ = d * y := by rw [hbdb]
    have e2 : b⁻¹ * ((b * y * b⁻¹) * d) * b = y * d := by
      calc b⁻¹ * ((b * y * b⁻¹) * d) * b = y * (b⁻¹ * d * b) := by group
        _ = y * d := by rw [hbdb]
    rw [e1, e2] at h1
    exact h1
  · intro h
    have h1 : b * (d * y) * b⁻¹ = b * (y * d) * b⁻¹ := by rw [h]
    have hdb' : b⁻¹ * d = d * b⁻¹ := by
      calc b⁻¹ * d = b⁻¹ * d * b * b⁻¹ := by group
        _ = d * b⁻¹ := by rw [hbdb]
    calc d * (b * y * b⁻¹) = b * (b⁻¹ * d * b) * y * b⁻¹ := by group
      _ = b * (d * y) * b⁻¹ := by rw [hbdb]; group
      _ = b * (y * d) * b⁻¹ := h1
      _ = b * y * (d * b⁻¹) := by group
      _ = b * y * (b⁻¹ * d) := by rw [hdb']
      _ = b * y * b⁻¹ * d := by group

theorem le_L1of' {p : ℕ} {M D L0 : Subgroup G} : L0 ≤ L1of p M D L0 := by
  refine le_iSup₂_of_le (1 : G) (Istar p M D).one_mem ?_
  exact le_of_eq (gLBConj_eq_of_mem_normalizer (one_mem _)).symm

theorem piLayer_le_self' (p : ℕ) (H : Subgroup G) : piLayer p H ≤ H := by
  unfold piLayer
  exact iSup₂_le fun L hL => hL.1.1

theorem setting_facts {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1) :
    orderOf b = p ∧ b ∈ M ∧ b ∈ Subgroup.centralizer ({d} : Set G) ∧ GLBConj b L0 = L0 ∧
      (∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0) ∧
      L0 ≤ M ∧ CFSG.Open.IsQuasisimple (barOf p L0) := by
  haveI : Fact p.Prime := ⟨GLStanding.prime h.standing⟩
  have hbU : b ∈ U := (Subgroup.mem_inf.1 hb).2
  have hbB : b ∈ B := hU.1.1 hbU
  have hBM : B ≤ M := (le_sup_right : B ≤ A ⊔ B).trans (h.hR.2.trans h.hR.1.1)
  have hbM : b ∈ M := hBM hbB
  have hbord : orderOf b = p := orderOf_eq_prime (hU.1.2.1.2 b hbU) hb1
  have hbC : b ∈ Subgroup.centralizer ({d} : Set G) := hU.2.1 hbU
  have hdb : d * b = b * d := Subgroup.mem_centralizer_iff.1 hbC d (Set.mem_singleton d)
  set P : Subgroup G := piLayer p (Istar p M D ⊓ Subgroup.centralizer ({d} : Set G)) with hPdef
  have hH : GLBConj b (Istar p M D ⊓ Subgroup.centralizer ({d} : Set G)) =
      Istar p M D ⊓ Subgroup.centralizer ({d} : Set G) := by
    have hI : GLBConj b (Istar p M D) = Istar p M D := istar_conj_eq p hbM
    have hC := gLBConj_centralizer_singleton_of_comm hdb
    have hIiff : ∀ y : G, b * y * b⁻¹ ∈ Istar p M D ↔ y ∈ Istar p M D := fun y => by
      rw [← mem_gLBConj, hI]
    have hCiff : ∀ y : G, b * y * b⁻¹ ∈ Subgroup.centralizer ({d} : Set G) ↔
        y ∈ Subgroup.centralizer ({d} : Set G) := fun y => by
      rw [← mem_gLBConj, hC]
    ext y
    rw [mem_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf, hIiff, hCiff]
  have hPb : GLBConj b P = P := by
    rw [hPdef, ← piLayer_gLBConj, hH]
  have hPI : P ≤ Istar p M D := (piLayer_le_self' p _).trans inf_le_left
  have hL0L1 : L0 ≤ L1of p M D L0 := le_L1of'
  have hbL1 : GLBConj b (L1of p M D L0) = L1of p M D L0 :=
    gLBConj_eq_of_mem_normalizer (mem_normalizer_of_centBar hb)
  have hN : ∀ q ∈ Istar p M D, GLBConj q (GLAPPrimeCoreOf p (L1of p M D L0)) =
      GLAPPrimeCoreOf p (L1of p M D L0) := by
    intro q hq
    rw [← glaPPrimeCoreOf_gLBConj, L1of_gLBConj_eq_of_mem_istar hq]
  have hcb : ∀ x ∈ L1of p M D L0, (b * x * b⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p (L1of p M D L0) :=
    fun x hx => inv_mul_mem_glaPPrimeCoreOf_of_centBar hb hx
  have hcb' : ∀ x ∈ L1of p M D L0, (b⁻¹ * x * b)⁻¹ * x ∈ GLAPPrimeCoreOf p (L1of p M D L0) := by
    intro x hx
    have hb' : b⁻¹ ∈ centBar p U (L1of p M D L0) := (centBar p U (L1of p M D L0)).inv_mem hb
    have := inv_mul_mem_glaPPrimeCoreOf_of_centBar hb' hx
    rwa [inv_inv] at this
  have hL0P : GLAPComponent p P L0 := h.hL0
  have hnorm : GLBConj b L0 = L0 :=
    glbConj_eq_of_pComp hL0P hPI hPb hL0L1 hbL1 hN hcb hcb'
  have hcomm := comm_mem_glaPPrimeCoreOf hL0L1 hnorm hcb
  have hL0M : L0 ≤ M := by
    have hI : Istar p M D ≤ M := by
      unfold Istar
      exact iSup₂_le fun g hg => by
        exact (gLBConj_le_iff_of_mem hg _).2 (Iof_le_M p M D)
    exact (hL0P.1.trans (piLayer_le_self' p _ |>.trans inf_le_left)).trans hI
  exact ⟨hbord, hbM, hbC, hnorm, hcomm, hL0M, isQuasisimple_barOf_of_pComp hL0P⟩

theorem barOf_L0b_iso {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1) :
    Nonempty (barOf p (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) ≃* barOf p L0) := by
  haveI : Fact p.Prime := ⟨GLStanding.prime h.standing⟩
  obtain ⟨hbord, -, -, hnorm, hcomm, -, hquasi⟩ := setting_facts h hU hb hb1
  exact barOf_glaPLayer_inf_cent_iso hbord hnorm hcomm hquasi

theorem barX_le_glaPLayer_inf_cent {p : ℕ} [Fact p.Prime] {M L0 : Subgroup G} {b : G}
    (hL0M : L0 ≤ M) (hL0core : GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M)
    (hbord : orderOf b = p) (hnorm : GLBConj b L0 = L0)
    (hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0)
    (hquasi : CFSG.Open.IsQuasisimple (barOf p L0)) :
    barX p M L0 ≤ barX p M (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) := by
  obtain ⟨hinf, htop⟩ := covering_data hbord hnorm hcomm hquasi
  set Y : Subgroup G := L0 ⊓ Subgroup.centralizer ({b} : Set G) with hYdef
  have hYL0 : Y ≤ L0 := inf_le_left
  have hLY : GLAPLayer p Y ≤ M := by
    have : GLAPLayer p Y ≤ Y := by
      unfold GLAPLayer
      exact sSup_le fun L hL => hL.1
    exact this.trans (hYL0.trans hL0M)
  have hle : barX p Y Y ≤ barX p Y (GLAPLayer p Y) := by
    rw [barX_self, htop]
  apply barX_le_of_forall hLY
  intro k hk
  obtain ⟨y, hyY, n, hn, hkyn⟩ := cover_centralizer hbord hnorm hcomm k hk
  obtain ⟨j, hj, hjy⟩ := exists_of_barX_le hle hyY hyY
  refine ⟨j, hj, ?_⟩
  have h1 : j⁻¹ * y ∈ GLAPPrimeCoreOf p M := hL0core (hinf hjy)
  have h2 : n ∈ GLAPPrimeCoreOf p M := hL0core hn
  have hfac : j⁻¹ * k = (j⁻¹ * y) * n := by
    rw [hkyn]
    group
  rw [hfac]
  exact (GLAPPrimeCoreOf p M).mul_mem h1 h2

theorem not_le_piOf_of_setting {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1)
    (hL0core : GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M) :
    ¬ (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
        GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)))) ≤ piOf p d := by
  haveI : Fact p.Prime := ⟨GLStanding.prime h.standing⟩
  intro hL
  obtain ⟨hbord, hbM, -, hnorm, hcomm, hL0M, hquasi⟩ := setting_facts h hU hb hb1
  have h1 : GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)) ≤ piOf p d := by
    refine le_trans ?_ hL
    refine le_iSup₂_of_le (1 : G) (one_mem _) ?_
    exact le_of_eq (gLBConj_eq_of_mem_normalizer (one_mem _)).symm
  have hpiS : piOf p d ≤ piStar p D := by
    unfold piOf piStar
    exact le_iSup_of_le d (le_iSup_of_le h.hd.1 (le_iSup_of_le h.hd.2 le_sup_left))
  have hcov := barX_le_glaPLayer_inf_cent hL0M hL0core hbord hnorm hcomm hquasi
  exact h.notCov (hcov.trans (Lemma1311.barX_mono' p (h1.trans hpiS)))

end Setting

section Pi

variable {G : Type} [Group G] [Finite G]

theorem le_piOf_of_comp' {p : ℕ} {d : G} {L : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) L)
    (hPi : IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)) : L ≤ piOf p d :=
  le_iSup₂_of_le (f := fun L (_ : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) L ∧
    IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L)) => L) L ⟨hL, hPi⟩ le_rfl

theorem normal_central_or_top {X : Type} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hX : CFSG.Open.IsQuasisimple X) : N ≤ Subgroup.center X ∨ N = ⊤ :=
  CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hX N
    (CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_normal hN)

end Pi

section Inputs

@[expose] def Input18_3Two : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → ∀ x y : G, orderOf x = p → orderOf y = p →
    x * y = y * x → ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x, y} : Set G)) J →
    GLAPComponent p ((⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) ⊓
      Subgroup.centralizer ({x} : Set G)) J

end Inputs

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem isPiGroup_barOf_L0 {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) :
    IsPiGroup p (↥L0 ⧸ GLAPPrimeCore p ↥L0) := by
  haveI : Fact p.Prime := ⟨GLStanding.prime h.standing⟩
  obtain ⟨S, hS, hPi, hEq⟩ := Lemma1311.pComp_piLayer_summand (GLStanding.prime h.standing) h.hL0
  have hSL0 : S = L0 := hEq.symm
  subst hSL0
  exact hPi

theorem gLBConj_istar_inf_centralizer {p : ℕ} {M D : Subgroup G} {d t : G} (htM : t ∈ M)
    (hdt : d * t = t * d) :
    GLBConj t (Istar p M D ⊓ Subgroup.centralizer ({d} : Set G)) =
      Istar p M D ⊓ Subgroup.centralizer ({d} : Set G) := by
  have hI : GLBConj t (Istar p M D) = Istar p M D := istar_conj_eq p htM
  have hC := gLBConj_centralizer_singleton_of_comm hdt
  have hIiff : ∀ y : G, t * y * t⁻¹ ∈ Istar p M D ↔ y ∈ Istar p M D := fun y => by
    rw [← mem_gLBConj, hI]
  have hCiff : ∀ y : G, t * y * t⁻¹ ∈ Subgroup.centralizer ({d} : Set G) ↔
      y ∈ Subgroup.centralizer ({d} : Set G) := fun y => by
    rw [← mem_gLBConj, hC]
  ext y
  rw [mem_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf, hIiff, hCiff]

theorem not_le_M_of_setting {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1)
    (hL0core : GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M)
    (hB1 : GLAPComponent p (Subgroup.centralizer ({d} : Set G))
      (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
        GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))))) :
    ¬ (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
        GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)))) ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨GLStanding.prime h.standing⟩
  intro hLM
  obtain ⟨hbord, hbM, hbC, hnorm, hcomm, hL0M, hquasi⟩ := setting_facts h hU hb hb1
  set L := ⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)),
    GLBConj g (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) with hLdef
  set L0b := GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)) with hL0bdef
  have hdb : d * b = b * d := Subgroup.mem_centralizer_iff.1 hbC d (Set.mem_singleton d)
  set T : Subgroup G := M ⊓ Subgroup.centralizer ({d} : Set G) with hTdef
  have hNT : Istar p M D ⊓ Subgroup.centralizer ({d} : Set G) ≤ T :=
    inf_le_inf_right _ (istar_le_M p M D)
  have hTN : T ≤ Subgroup.normalizer ((Istar p M D ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :
      Set G) := by
    intro t ht
    obtain ⟨htM, htC⟩ := Subgroup.mem_inf.1 ht
    have hdt : d * t = t * d := Subgroup.mem_centralizer_iff.1 htC d (Set.mem_singleton d)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [← mem_gLBConj, gLBConj_istar_inf_centralizer htM hdt]
  obtain ⟨S, hS, hPi, hEq⟩ := Lemma1311.pComp_piLayer_summand (GLStanding.prime h.standing) h.hL0
  have hL0N : GLAPComponent p (Istar p M D ⊓ Subgroup.centralizer ({d} : Set G)) L0 := by
    rw [hEq]; exact hS
  have hL0T : GLAPComponent p T L0 :=
    Lemma1311.glaPComponent_of_normal (GLStanding.prime h.standing) hNT hTN hL0N
  have hLT : L ≤ T := le_inf hLM hB1.1
  have hLp : GLAPComponent p T L := glaPComponent_of_le (GLStanding.prime h.standing) hB1 hLT inf_le_right
  by_cases hEqL : L = L0
  ·
    have hPiL : IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L) := by
      rw [hEqL]
      exact isPiGroup_barOf_L0 h
    exact not_le_piOf_of_setting h hU hb hb1 hL0core (le_piOf_of_comp' hB1 hPiL)
  ·
    have hne : barX p T L ≠ barX p T L0 := fun heq => hEqL (glaPComponent_unique hLp hL0T heq)
    have hcommT : ⁅barX p T L, barX p T L0⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne (barX p T L) (barX p T L0)
        hLp.2.2.1 hL0T.2.2.1 hne
    have hL0coreT : GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p T := by
      have hsn : IsSubnormal L0 T := hL0T.2.1
      exact glaPPrimeCoreOf_le_of_isSubnormal (GLStanding.prime h.standing) hsn
    have hcovT := barX_le_glaPLayer_inf_cent (M := T) hL0T.1 hL0coreT hbord hnorm hcomm hquasi
    have hL0bL : L0b ≤ L := by
      refine le_iSup₂_of_le (1 : G) (one_mem _) ?_
      exact le_of_eq (gLBConj_eq_of_mem_normalizer (one_mem _)).symm
    have hle : barX p T L0 ≤ barX p T L := hcovT.trans (Lemma1311.barX_mono' p hL0bL)
    have hcent : barX p T L ≤ Subgroup.centralizer ((barX p T L0 : Subgroup _) : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcommT
    have hcommL0 : ∀ x ∈ barX p T L0, ∀ y ∈ barX p T L0, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 (hcent (hle hy)) x hx
    have hq : CFSG.Open.IsQuasisimple ↥(barX p T L0) := hL0T.2.2.1.2.2
    have hbot : commutator ↥(barX p T L0) = ⊥ := by
      show ⁅(⊤ : Subgroup ↥(barX p T L0)), (⊤ : Subgroup ↥(barX p T L0))⁆ = ⊥
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subtype.ext (hcommL0 y.1 y.2 x.1 x.2)
    have hqtop : commutator ↥(barX p T L0) = ⊤ := hq.1
    have htriv : ∀ x : ↥(barX p T L0), x = 1 := by
      intro x
      have hx : x ∈ commutator ↥(barX p T L0) := by
        rw [hqtop]
        exact Subgroup.mem_top _
      rw [hbot] at hx
      exact Subgroup.mem_bot.1 hx
    have hnt : Nontrivial (↥(barX p T L0) ⧸ Subgroup.center ↥(barX p T L0)) := hq.2.1
    obtain ⟨a, b', hab⟩ := exists_pair_ne
      (↥(barX p T L0) ⧸ Subgroup.center ↥(barX p T L0))
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b'
    rw [htriv x, htriv y]

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313

end
