module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma105
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem le_normalizer_comm {K H₁ H₂ : Subgroup G} (h₁ : K ≤ Subgroup.normalizer (H₁ : Set G))
    (h₂ : K ≤ Subgroup.normalizer (H₂ : Set G)) :
    K ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₁ hg), Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₂ hg)]

structure TData (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b : G) (S : Subgroup G) : Prop where
  le_I : S ≤ Ipart p L b
  two : IsPGroup 2 S
  norm : B ≤ Subgroup.normalizer (S : Set G)
  not_le : ¬ S ≤ GLAPPrimeCoreOf p (Ipart p L b)
  big : 8 < Nat.card S
  cent : ∀ c ∈ B, (⁅S, Subgroup.zpowers c⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (Ipart p L b) → c ∈ Dgrp b x

theorem not_B_le_D (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    ¬ B ≤ Dgrp b x := by
  intro hle
  obtain ⟨-, -, hD2⟩ := dgrp_facts hc h
  have hp := hc.ctx.prime
  have h1 : Nat.card B ≤ Nat.card (Dgrp b x) := Subgroup.card_le_of_le hle
  have h4 : p ^ 4 ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right hp.pos hc.ctx.rank_ge
  rw [hD2] at h1
  have : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem exists_TData (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b) :
    ∃ S : Subgroup G, TData p B x L b S := by
  classical
  have hS := sstar_triple h.star
  have hp := hc.ctx.prime
  obtain ⟨hDB, hDel, hD2⟩ := dgrp_facts hc h
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x))) :=
    oddCore_of_noTwoLocal hc h hxD hS.2.1.2.1 (no_two_local hc hin h hd5 hcase)
  have hcentral : ∀ T : Subgroup G, T ≤ GLAPPrimeCoreOf p (cx x) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥ := by
    intro T hTO hT2 _
    rw [eq_bot_of_le_odd hT2 hodd hTO]
    simp
  have hTL := exists_T_in_L hc hin.l103 h hcentral
  obtain ⟨T0, hT0I, hT02, hT0B, hT0O⟩ := h.b_choice hTL
  obtain ⟨S, ⟨hSI, hS2, hSB, hSO⟩, hmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {S : Subgroup G | S ≤ Ipart p L b ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
      ¬ S ≤ GLAPPrimeCoreOf p (Ipart p L b)}) ⟨T0, hT0I, hT02, hT0B, hT0O⟩
  have hLcomp : GLAPComponent p (cx x) L := hS.2.2
  have hchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hbp : b ^ p = 1 := (B_el h).2 b h.mem
  obtain ⟨hIcomp, hIchev⟩ := hin.i91comp (cx x) L b hLcomp hchev hbp h.prop h.I_ne
  have hBNI : B ≤ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) := (B_le_N_J hc h hxD).1
  obtain ⟨hcent, hsmall⟩ := hin.i1312 hp hc.ctx.odd (L ⊓ cx b) (Ipart p L b) B S hIcomp hIchev (B_el h) hBNI hSI hS2 hSB hSO
    (fun S' hSS' hS'I hS'2 hS'B hS'O => le_antisymm (hmax ⟨hS'I, hS'2, hS'B, hS'O⟩ hSS') hSS')
  refine ⟨S, hSI, hS2, hSB, hSO, ?_, fun c hcB hcS => (h.cent_I c hcB).1 (hcent c hcB hcS)⟩
  by_contra hle
  push_neg at hle
  obtain ⟨B₀, hB₀B, hcardB, hB₀⟩ := hsmall hle
  have hB₀D : B₀ ≤ Dgrp b x := fun c hc0 =>
    (h.cent_I c (hB₀B hc0)).1 (hcent c (hB₀B hc0) (hB₀ c hc0))
  have h1 : Nat.card B₀ ≤ Nat.card (Dgrp b x) := Subgroup.card_le_of_le hB₀D
  have h4 : p ^ 4 ≤ Nat.card B := by
    rw [hS.1.2.1]
    exact Nat.pow_le_pow_right hp.pos hc.ctx.rank_ge
  rw [hD2] at h1
  have h3 : Nat.card B ≤ p * p ^ 2 := hcardB.trans (Nat.mul_le_mul_left p h1)
  have h5 : p * p ^ 2 < p ^ 4 := by
    calc p * p ^ 2 = p ^ 3 := by ring
      _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem essential_105 (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {S : Subgroup G} (hT : TData p B x L b S) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) :
    IsEssential p B a := by
  have haB : a ∈ B := (dgrp_facts hc h).1 ha
  refine ⟨haB, ha1, S, hT.le_I.trans (Ipart_le_cx h ha), hT.two, hT.norm, ?_, ?_⟩
  · obtain ⟨c, hcB, hcD⟩ : ∃ c ∈ B, c ∉ Dgrp b x := by
      by_contra hno
      push_neg at hno
      exact not_B_le_D hc h hno
    intro hbot
    have h1 : (⁅S, Subgroup.zpowers c⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (Ipart p L b) := by
      refine le_trans ?_ bot_le
      rw [← hbot]
      exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.2 hcB)
    exact hcD (hT.cent c hcB h1)
  · intro _
    refine ⟨fun e => ?_⟩
    have h8 : Nat.card S = Nat.card (QuaternionGroup 2) := Nat.card_congr e.toEquiv
    rw [Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card] at h8
    have := hT.big
    omega

theorem T_of_TData (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b)
    {S : Subgroup G} (hT : TData p B x L b S) :
    ∃ T : Subgroup G, T ≤ Ipart p L b ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p (Ipart p L b) ∧ (⁅B, T⁆ : Subgroup G) = T ∧ T ≠ ⊥ := by
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hTS : (⁅S, B⁆ : Subgroup G) ≤ S := comm_le_left_of_normalizes hT.norm
  have hnle : ¬ (⁅S, B⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (Ipart p L b) := by
    intro hle
    refine not_B_le_D hc h fun c hcB => hT.cent c hcB ?_
    exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.2 hcB)).trans hle
  have hS2' : ¬ p ∣ Nat.card S := by
    intro hdvd
    obtain ⟨k, hk⟩ := hT.two.exists_card_eq
    rw [hk] at hdvd
    have := (Nat.Prime.dvd_of_dvd_pow hp hdvd)
    have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
    exact hc.ctx.odd h2
  refine ⟨⁅S, B⁆, hTS.trans hT.le_I, hT.two.to_le hTS, le_normalizer_comm hT.norm Subgroup.le_normalizer, hnle,
    ?_, fun hbot => hnle (hbot ▸ bot_le)⟩
  rw [Subgroup.commutator_comm]
  exact CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp (isPGroup_of_isElemAbelian (B_el h))
    hT.norm hS2'

@[expose] def isExcL (i : TauCeti.CFSGIndex) : Prop := S9.isSp4eight i ∨ S9.isL3char2 i ∨ S9.isU3char2 i

theorem l3_of_exc {S : Type} [Group S] (hn : ¬ catalogIs S (fun i => S9.isSp4eight i ∨ S9.isU3char2 i))
    (h : catalogIs S isExcL) : catalogIs S S9.isL3char2 := by
  obtain ⟨i, hi, f⟩ := h
  rcases hi with h1 | h2 | h3
  · exact absurd ⟨i, Or.inl h1, f⟩ hn
  · exact ⟨i, h2, f⟩
  · exact absurd ⟨i, Or.inr h3, f⟩ hn

theorem not_sp4_u3 (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) (hp3 : p = 3) (hTL : HasTL p B L) :
    ¬ catalogIs (PSimple p L) (fun i => S9.isSp4eight i ∨ S9.isU3char2 i) := by
  subst hp3
  obtain ⟨T, hTL', hT2, hTB, hTO⟩ := hTL
  exact hin.i1015 (cx x) L B T (sstar_triple h.star).2.2 (sstar_norm h.star) (B_el h) (p3_mul_cent_le hc h.star)
    hTL' hT2 hTB hTO

private theorem lemma105more_coprime_pPrimeCore (p : ℕ) (H : Type*) [Group H] [Finite H] :
    Nat.Coprime p (Nat.card (CFSG.pPrimeCore p H)) := by
  refine Nat.coprime_of_dvd fun k hk hkp hkn => ?_
  haveI : Fact k.Prime := ⟨hk⟩
  have hle : CFSG.pPrimeCore p H ≤ CFSG.pPrimeCore k H :=
    sSup_le_sSup fun N hN => ⟨hN.1, Nat.Coprime.coprime_dvd_left hkp hN.2⟩
  have hd : Nat.card (CFSG.pPrimeCore p H) ∣ Nat.card (CFSG.pPrimeCore k H) :=
    Subgroup.card_dvd_of_le hle
  have hk2 : k ∣ Nat.card (CFSG.pPrimeCore k H) := hkn.trans hd
  exact hk.ne_one (CFSG.pPrimeCore_coprime_card.eq_one_of_dvd hk2)

private theorem lemma105more_normalizer_zpowers {g x : G} (hg : g * x = x * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  have hc : Commute g x := hg
  have hgi : Commute g⁻¹ x := hc.inv_left
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, rfl⟩
    have hk : Commute g (x ^ k) := hc.zpow_right k
    have hconj : g * x ^ k * g⁻¹ = x ^ k := by
      rw [hk.eq]
      group
    exact ⟨k, hconj.symm⟩
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hk' : Commute g⁻¹ (x ^ k) := hgi.zpow_right k
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [← hk] at h1
    rw [h1]
    have hk2 : g⁻¹ * x ^ k * g = x ^ k := by
      calc g⁻¹ * x ^ k * g = x ^ k * g⁻¹ * g := by rw [hk'.eq]
        _ = x ^ k := by group
    rw [hk2]

private theorem lemma105more_normalizer_centralizer {g a : G} (hg : g * a = a * g) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hga : g⁻¹ * a = a * g⁻¹ := by
    calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hg]
      _ = a * g⁻¹ := by group
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    calc g * y * g⁻¹ * a = g * y * (g⁻¹ * a) := by group
      _ = g * y * (a * g⁻¹) := by rw [hga]
      _ = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = g * a * y * g⁻¹ := by group
      _ = a * g * y * g⁻¹ := by rw [hg]
      _ = a * (g * y * g⁻¹) := by group
  · intro hy
    have hgag : g⁻¹ * a * g = a := by
      calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
        _ = g⁻¹ * (g * a) := by rw [hg]
        _ = a := by group
    calc y * a = y * (g⁻¹ * a * g) := by rw [hgag]
      _ = g⁻¹ * (g * y * g⁻¹ * a) * g := by group
      _ = g⁻¹ * (a * (g * y * g⁻¹)) * g := by rw [hy]
      _ = (g⁻¹ * a * g) * y := by group
      _ = a * y := by rw [hgag]

private theorem lemma105more_card_zpowers {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hx hx1]

private theorem lemma105more_card_sup {p : ℕ} (hp : p.Prime) {A B : Subgroup G} (hA : Nat.card A = p)
    (hB : Nat.card B = p) (hBN : B ≤ Subgroup.normalizer (A : Set G)) (hBA : ¬ B ≤ A) :
    Nat.card (A ⊔ B : Subgroup G) = p ^ 2 := by
  have hdvd : Nat.card (A ⊓ B : Subgroup G) ∣ p := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  have hcop : Nat.card (A ⊓ B : Subgroup G) = 1 := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact h1
    · exfalso
      have heq : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hB, h1])
      exact hBA (by rw [← heq]; exact inf_le_left)
  have hmul := card_sup_mul_card_inf_of_le_normalizer hBN
  rw [hcop, hA, hB, mul_one, ← sq] at hmul
  exact hmul

private theorem lemma105more_gLBConj_iSup₂ (g : G) {H : Subgroup G} (F : G → Subgroup G) :
    GLBConj g (⨆ x ∈ H, F x) = ⨆ x ∈ H, GLBConj g (F x) := by
  unfold GLBConj
  simp only [Subgroup.map_iSup]

private theorem lemma105more_gLBConj_closureIn_le {I H : Subgroup G} {g : G}
    (hI : g ∈ Subgroup.normalizer (I : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) :
    GLBConj g (closureIn I H) ≤ closureIn I H := by
  have hI' : GLBConj g I = I := mem_normalizer_iff_gLBConj_eq.1 hI
  rw [closureIn_eq_iSup_gLBConj I H, lemma105more_gLBConj_iSup₂]
  refine iSup₂_le fun h hh => ?_
  have hh' : g⁻¹ * h * g ∈ H := by
    refine (Subgroup.mem_normalizer_iff.1 hH (g⁻¹ * h * g)).2 ?_
    have : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rw [this]
    exact hh
  calc GLBConj g (GLBConj h I) = GLBConj (h * g) I := gLBConj_gLBConj g h I
    _ = GLBConj (g * (g⁻¹ * h * g)) I := by group
    _ = GLBConj (g⁻¹ * h * g) (GLBConj g I) := (gLBConj_gLBConj _ _ _).symm
    _ = GLBConj (g⁻¹ * h * g) I := by rw [hI']
    _ ≤ ⨆ k ∈ H, GLBConj k I := le_biSup (fun k => GLBConj k I) hh'

private theorem lemma105more_normalizer_closureIn {I H : Subgroup G} {g : G}
    (hI : g ∈ Subgroup.normalizer (I : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((closureIn I H : Subgroup G) : Set G) := by
  have hIinv : g⁻¹ ∈ Subgroup.normalizer (I : Set G) := Subgroup.inv_mem _ hI
  have hHinv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := Subgroup.inv_mem _ hH
  have h1 := lemma105more_gLBConj_closureIn_le hI hH
  have h2 := lemma105more_gLBConj_closureIn_le hIinv hHinv
  rw [mem_normalizer_iff_gLBConj_eq]
  apply le_antisymm h1
  calc closureIn I H = GLBConj g (GLBConj g⁻¹ (closureIn I H)) :=
        (gLBConj_gLBConj_inv g _).symm
    _ ≤ GLBConj g (closureIn I H) := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g h2

private theorem lemma105more_pQuot_gLBConj (p : ℕ) (K : Subgroup G) (g : G) :
    Nonempty (PQuot p (GLBConj g K) ≃* PQuot p K) := by
  let c : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  let e : ↥K ≃* ↥(K.map c) := Subgroup.equivMapOfInjective K c (MulAut.conj g⁻¹).injective
  have hmap : Subgroup.map e.toMonoidHom (GLAPPrimeCore p ↥K) = GLAPPrimeCore p ↥(K.map c) :=
    CFSG.pPrimeCore_map_iso p e
  exact ⟨(QuotientGroup.congr (GLAPPrimeCore p ↥K) (GLAPPrimeCore p ↥(K.map c)) e hmap).symm⟩

private theorem lemma105more_mem_normalizer_of_conj_eq {u v : G} {K : Subgroup G}
    (h : GLBConj u K = GLBConj v K) : u * v⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have := congrArg (GLBConj v⁻¹) h
  rwa [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this

private theorem lemma105more_three_conj {B : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hB : IsElemAbelian p B) {K : Subgroup G} (hnB : ¬ B ≤ Subgroup.normalizer (K : Set G)) :
    ∃ g₀ ∈ B, ∃ g₁ ∈ B, ∃ g₂ ∈ B, GLBConj g₀ K ≠ GLBConj g₁ K ∧
      GLBConj g₀ K ≠ GLBConj g₂ K ∧ GLBConj g₁ K ≠ GLBConj g₂ K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set S : Subgroup ↥B := (Subgroup.normalizer (K : Set G)).subgroupOf B with hS
  have hStop : S ≠ ⊤ := by
    rw [hS, Ne, Subgroup.subgroupOf_eq_top]
    exact hnB
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hB).exists_card_eq
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (hn ▸ Subgroup.index_dvd_card S)
  have hi1 : S.index ≠ 1 := fun h => hStop (Subgroup.index_eq_one.1 h)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi1 (by rw [hi]; simp)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hidx : 3 ≤ S.index := by
    rw [hi]
    exact le_trans hp3 (Nat.le_self_pow hi0 p)
  have hcard : 2 < Nat.card (↥B ⧸ S) := by
    rw [← Subgroup.index_eq_card]
    omega
  haveI : Fintype (↥B ⧸ S) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨q₀, q₁, q₂, h01, h02, h12⟩ := Fintype.two_lt_card_iff.1 hcard
  obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk_surjective q₀
  obtain ⟨u₁, hu₁⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨u₂, hu₂⟩ := QuotientGroup.mk_surjective q₂
  have key : ∀ u v : ↥B, (u : ↥B ⧸ S) ≠ (v : ↥B ⧸ S) → GLBConj (u : G) K ≠ GLBConj (v : G) K := by
    intro u v huv heq
    apply huv
    rw [QuotientGroup.eq]
    have hmem := lemma105more_mem_normalizer_of_conj_eq heq
    have hcomm : (u : G) * (v : G)⁻¹ = (v : G)⁻¹ * (u : G) := by
      have := isElemAbelian_commute hB u.2 v.2
      calc (u : G) * (v : G)⁻¹ = (v : G)⁻¹ * ((v : G) * (u : G)) * (v : G)⁻¹ := by group
        _ = (v : G)⁻¹ * ((u : G) * (v : G)) * (v : G)⁻¹ := by rw [this]
        _ = (v : G)⁻¹ * (u : G) := by group
    have hmem' : (u : G)⁻¹ * (v : G) ∈ Subgroup.normalizer (K : Set G) := by
      have h1 : ((u : G)⁻¹ * (v : G)) = ((v : G)⁻¹ * (u : G))⁻¹ := by group
      rw [h1]
      exact Subgroup.inv_mem _ (hcomm ▸ hmem)
    rw [hS, Subgroup.mem_subgroupOf]
    simpa using hmem'
  refine ⟨u₀, u₀.2, u₁, u₁.2, u₂, u₂.2, ?_, ?_, ?_⟩
  · refine key u₀ u₁ ?_
    rw [hu₀, hu₁]
    exact h01
  · refine key u₀ u₂ ?_
    rw [hu₀, hu₂]
    exact h02
  · refine key u₁ u₂ ?_
    rw [hu₁, hu₂]
    exact h12

private theorem lemma105more_card_Dgrp {B : Subgroup G} {b x : G} (hB : IsElemAbelian p B) (hp : p.Prime)
    (hbB : b ∈ B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hbx : b ∉ Subgroup.zpowers x) :
    Nat.card (Dgrp b x) = p ^ 2 := by
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hbp : b ^ p = 1 := hB.2 b hbB
  have hb1 : b ≠ 1 := fun h => hbx (h ▸ Subgroup.one_mem _)
  have hA : Nat.card (Subgroup.zpowers x) = p := lemma105more_card_zpowers hp hxp hx1
  have hBc : Nat.card (Subgroup.zpowers b) = p := lemma105more_card_zpowers hp hbp hb1
  have hBN : Subgroup.zpowers b ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (lemma105more_normalizer_zpowers (isElemAbelian_commute hB hbB hxB))
  have hBA : ¬ Subgroup.zpowers b ≤ Subgroup.zpowers x := fun h => hbx (h (Subgroup.mem_zpowers b))
  rw [dgrp_eq_sup, sup_comm]
  exact lemma105more_card_sup hp hA hBc hBN hBA

private theorem lemma105more_complement {B : Subgroup G} {b x a : G} (hB : IsElemAbelian p B) (hp : p.Prime)
    (hDB : Dgrp b x ≤ B) (hD : Nat.card (Dgrp b x) = p ^ 2) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) :
    ∃ x' ∈ Dgrp b x, x' ∉ Subgroup.zpowers a ∧
      Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x' := by
  have haB : a ∈ B := hDB ha
  have hap : a ^ p = 1 := hB.2 a haB
  have hA : Nat.card (Subgroup.zpowers a) = p := lemma105more_card_zpowers hp hap ha1
  obtain ⟨d, hdD, hdA⟩ : ∃ d ∈ Dgrp b x, d ∉ Subgroup.zpowers a := by
    by_contra hcon
    push_neg at hcon
    have hle : Dgrp b x ≤ Subgroup.zpowers a := fun d hd => hcon d hd
    have h1 : Nat.card (Dgrp b x) ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
    rw [hD, hA] at h1
    have hp2 : p < p ^ 2 := by nlinarith [hp.two_le]
    exact absurd h1 (not_le.2 hp2)
  have hdB : d ∈ B := hDB hdD
  have hd1 : d ≠ 1 := fun h => hdA (h ▸ Subgroup.one_mem _)
  have hdp : d ^ p = 1 := hB.2 d hdB
  have hdcard : Nat.card (Subgroup.zpowers d) = p := lemma105more_card_zpowers hp hdp hd1
  have hBN : Subgroup.zpowers d ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (lemma105more_normalizer_zpowers (isElemAbelian_commute hB hdB haB))
  have hBA : ¬ Subgroup.zpowers d ≤ Subgroup.zpowers a := fun h => hdA (h (Subgroup.mem_zpowers d))
  have hsup : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers d : Subgroup G) = p ^ 2 :=
    lemma105more_card_sup hp hA hdcard hBN hBA
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ Dgrp b x :=
    sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hdD)
  have heq : Subgroup.zpowers a ⊔ Subgroup.zpowers d = Dgrp b x :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hsup, hD]))
  exact ⟨d, hdD, hdA, heq.symm⟩

private theorem lemma105more_normalizer_inf_cent {L : Subgroup G} {g b : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgb : g * b = b * g) :
    g ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  have hgC := lemma105more_normalizer_centralizer hgb
  rw [Subgroup.mem_normalizer_iff] at hgL hgC ⊢
  intro y
  simp only [Subgroup.mem_inf]
  exact and_congr (hgL y) (hgC y)

private theorem lemma105more_x_mem {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    x ∈ B :=
  (sstar_triple h.star).2.1.1

private theorem lemma105more_x_ne_one {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    x ≠ 1 :=
  (sstar_triple h.star).2.1.2.1

private theorem lemma105more_D_le_B {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    Dgrp b x ≤ B := by
  refine Subgroup.closure_le _ |>.2 ?_
  intro k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl
  · exact h.mem
  · exact lemma105more_x_mem h

private theorem lemma105more_B_le_N_Ipart {B : Subgroup G} {x : G} {L : Subgroup G} {b g : G} (h : Cfg p B x L b)
    (hg : g ∈ B) : g ∈ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) := by
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := sstar_norm h.star hg
  have hgb : g * b = b * g := isElemAbelian_commute (B_el h) hg h.mem
  exact mem_normalizer_glaPLayer (lemma105more_normalizer_inf_cent hgL hgb)

private theorem lemma105more_B_le_N_Jpart {B : Subgroup G} {x : G} {L : Subgroup G} {b a g : G} (h : Cfg p B x L b)
    (ha : a ∈ B) (hg : g ∈ B) :
    g ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) := by
  have hga : g * a = a * g := isElemAbelian_commute (B_el h) hg ha
  exact lemma105more_normalizer_closureIn (lemma105more_B_le_N_Ipart h hg)
    (mem_normalizer_glaPLayer (lemma105more_normalizer_centralizer hga))

private theorem lemma105more_I_comp_CD (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    GLAPComponent p (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) (Ipart p L b) := by
  have hp := hc.ctx.prime
  have hLcomp : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hbp : b ^ p = 1 := (B_el h).2 b h.mem
  have hIcomp : GLAPComponent p (L ⊓ cx b) (Ipart p L b) :=
    (hin.i91comp (cx x) L b hLcomp hchev hbp h.prop h.I_ne).1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert _ _)
  have hEq : L ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) = L ⊓ cx b := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hgL, hgD⟩
      refine ⟨hgL, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hgD b hbD).symm
    · rintro ⟨hgL, hgb⟩
      refine ⟨hgL, ?_⟩
      have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hLcomp.1 hgL)
      have hle : Dgrp b x ≤ Subgroup.centralizer ({g} : Set G) := by
        refine Subgroup.closure_le _ |>.2 ?_
        intro k hk
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgb).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 hgx.symm
      exact Subgroup.mem_centralizer_iff.2 fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G))
      (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) := by
    have hCD : Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) ≤ cx x :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD)
    have := isSubnormal_inf hLcomp.2.1 (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G))
    rwa [inf_eq_right.2 hCD] at this
  have hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G))
      (Ipart p L b) := by
    rw [hEq]
    exact hIcomp
  exact glaPComponent_of_isSubnormal' hp hsub hJ

theorem core_inf_le {I J : Subgroup G} (hIJ : I ≤ J) :
    I ⊓ GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p I := by
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := lemma105more_coprime_pPrimeCore p ↥J
  have hmem : ∀ N : Subgroup ↥I, N.Normal → Nat.Coprime p (Nat.card N) →
      N ≤ GLAPPrimeCore p ↥I :=
    fun N hN hc => le_sSup (s := {K : Subgroup ↥I | K.Normal ∧ Nat.Coprime p (Nat.card K)}) ⟨hN, hc⟩
  set N : Subgroup ↥I := (GLAPPrimeCore p ↥J).comap (Subgroup.inclusion hIJ) with hNdef
  have hNcop : Nat.Coprime p (Nat.card N) := by
    have h1 : Nat.card (N.map (Subgroup.inclusion hIJ)) = Nat.card N :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIJ)
    have h2 : N.map (Subgroup.inclusion hIJ) ≤ GLAPPrimeCore p ↥J := Subgroup.map_comap_le _ _
    have h3 : Nat.card (N.map (Subgroup.inclusion hIJ)) ∣ Nat.card (GLAPPrimeCore p ↥J) :=
      Subgroup.card_dvd_of_le h2
    rw [← h1]
    exact Nat.Coprime.coprime_dvd_right h3 hcop
  have hNle : N ≤ GLAPPrimeCore p ↥I := hmem N inferInstance hNcop
  rintro g ⟨hgI, hgO⟩
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hgO
  let z : ↥I := ⟨g, hgI⟩
  have hzN : z ∈ N := by
    rw [hNdef, Subgroup.mem_comap]
    have : Subgroup.inclusion hIJ z = y := Subtype.ext hyg.symm
    rw [this]
    exact hy
  exact Subgroup.mem_map_of_mem I.subtype (hNle hzN)

theorem exists_K_not_norm (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hns : ¬ GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)) :
    ∃ (K : Subgroup G) (x' : G), GLAPComponent p (cx a) K ∧ K ≤ Jpart p (Ipart p L b) a ∧
      closureIn K B = Jpart p (Ipart p L b) a ∧ Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x' ∧
      x' ∉ Subgroup.normalizer (K : Set G) := by
  classical
  have hp := hc.ctx.prime
  have hB := B_el h
  have hDB : Dgrp b x ≤ B := lemma105more_D_le_B h
  have hxB : x ∈ B := lemma105more_x_mem h
  have hD : Nat.card (Dgrp b x) = p ^ 2 :=
    lemma105more_card_Dgrp hB hp h.mem hxB (lemma105more_x_ne_one h) h.not_mem
  obtain ⟨x', hx'D, hx'a, hDeq⟩ := lemma105more_complement hB hp hDB hD ha ha1
  have haB : a ∈ B := hDB ha
  have hx'B : x' ∈ B := hDB hx'D
  have hax' : a * x' = x' * a := isElemAbelian_commute hB haB hx'B
  have hEx : Subgroup.zpowers x' ≤ cx a :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hax'.symm)
  have hEel : IsElemAbelian p (Subgroup.zpowers x') :=
    isElemAbelian_mono hB (Subgroup.zpowers_le.2 hx'B)
  have hEqCD : cx a ⊓ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) =
      Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) := by
    rw [hDeq]
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 h1
      have hgx : g * x' = x' * g := (Subgroup.mem_centralizer_iff.1 h2 x' (Subgroup.mem_zpowers x')).symm
      have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers x' ≤ Subgroup.centralizer ({g} : Set G) :=
        sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hga.symm))
          (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hgx.symm))
      exact Subgroup.mem_centralizer_iff.2 fun k hk =>
        (Subgroup.mem_centralizer_singleton_iff.1 (hle hk))
    · intro hg
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · have ha' : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers x' :=
          (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers x') (Subgroup.mem_zpowers a)
        exact (Subgroup.mem_centralizer_iff.1 hg a ha').symm
      · exact Subgroup.mem_centralizer_iff.2 fun k hk =>
          Subgroup.mem_centralizer_iff.1 hg k ((le_sup_right : Subgroup.zpowers x' ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers x') hk)
  have hI' : GLAPComponent p (cx a ⊓ Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G))
      (Ipart p L b) := by
    rw [hEqCD]
    exact lemma105more_I_comp_CD hc hin h
  have hIle : Ipart p L b ≤ Jpart p (Ipart p L b) a := le_closureIn_self _ _
  have hIne : Ipart p L b ≠ ⊥ := h.I_ne
  obtain ⟨𝒞, h𝒞comp, hsup, -, htrans⟩ :=
    hin.l104.i183 G (cx a) (S8.isKGroup_cx hc.ctx ha1) p hp (Subgroup.zpowers x') hEx hEel
      (Ipart p L b) hI'
  have hJ𝒞 : Jpart p (Ipart p L b) a = ⨆ L' ∈ 𝒞, L' := by
    rw [hsup, Jpart, closureIn_eq_iSup_gLBConj]
  have hsubC : ∀ L' ∈ 𝒞, L' ≤ Jpart p (Ipart p L b) a := fun L' hL' => by
    rw [hJ𝒞]
    exact le_iSup₂ (f := fun L'' (_ : L'' ∈ 𝒞) => L'') L' hL'
  have hcl : ∀ L₁ ∈ 𝒞, closureIn L₁ B = Jpart p (Ipart p L b) a := by
    intro L₁ h₁
    apply le_antisymm
    · rw [closureIn_eq_iSup_gLBConj]
      refine iSup₂_le fun g hg => ?_
      calc GLBConj g L₁ ≤ GLBConj g (Jpart p (Ipart p L b) a) :=
            CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g (hsubC L₁ h₁)
        _ = Jpart p (Ipart p L b) a :=
            mem_normalizer_iff_gLBConj_eq.1 (lemma105more_B_le_N_Jpart h haB hg)
    · rw [hJ𝒞]
      refine iSup₂_le fun L₂ h₂ => ?_
      obtain ⟨e, he, hee⟩ := htrans L₁ h₁ L₂ h₂
      have heB : e ∈ B := (Subgroup.zpowers_le.2 hx'B) he
      rw [← hee, closureIn_eq_iSup_gLBConj]
      exact le_iSup₂ (f := fun g (_ : g ∈ B) => GLBConj g L₁) e heB
  by_contra hcon
  push_neg at hcon
  have hsing : ∀ L₁ ∈ 𝒞, ∀ L₂ ∈ 𝒞, L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂
    obtain ⟨e, he, hee⟩ := htrans L₁ h₁ L₂ h₂
    have hx'N : x' ∈ Subgroup.normalizer (L₁ : Set G) :=
      hcon L₁ x' (h𝒞comp L₁ h₁) (hsubC L₁ h₁) (hcl L₁ h₁) hDeq
    have hN : e ∈ Subgroup.normalizer (L₁ : Set G) := (Subgroup.zpowers_le.2 hx'N) he
    rw [← hee]
    exact (mem_normalizer_iff_gLBConj_eq.1 hN).symm
  have hne : 𝒞.Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    apply hIne
    apply eq_bot_iff.2
    have hJbot : Jpart p (Ipart p L b) a = ⊥ := by
      rw [hJ𝒞, hem]
      simp
    exact hJbot ▸ hIle
  obtain ⟨L₀, hL₀⟩ := hne
  have hJeq : Jpart p (Ipart p L b) a = L₀ := by
    apply le_antisymm
    · rw [hJ𝒞]
      exact iSup₂_le fun L' hL' => le_of_eq (hsing L' hL' L₀ hL₀)
    · exact hsubC L₀ hL₀
  exact hns (by rw [hJeq]; exact h𝒞comp L₀ hL₀)

private theorem lemma105more_quot_center_equiv {Q S : Type} [Group Q] [Group S] [IsSimpleGroup S]
    (hQ : Nontrivial (Q ⧸ Subgroup.center Q)) (e : Q ≃* S) :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* S) := by
  haveI : IsSimpleGroup Q := e.isSimpleGroup
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h1 | h1
    · exact h1
    · exfalso
      haveI : Subsingleton (Q ⧸ Subgroup.center Q) := by
        rw [h1]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton (Q ⧸ Subgroup.center Q) ‹_›
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

theorem Ibar_iso_Kbar (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {a : G} (ha : a ∈ Dgrp b x) (hess : IsEssential p B a)
    {K : Subgroup G} {x' : G} (hK : GLAPComponent p (cx a) K)
    (hKJ : closureIn K B = Jpart p (Ipart p L b) a)
    (hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x')
    (hx'K : x' ∉ Subgroup.normalizer (K : Set G)) :
    Nonempty (PQuot p (Ipart p L b) ≃* PSimple p K) := by
  have hp := hc.ctx.prime
  have hDB : Dgrp b x ≤ B := lemma105more_D_le_B h
  have hx'D : x' ∈ Dgrp b x := by
    rw [hDeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
  have hx'B : x' ∈ B := hDB hx'D
  have hIcomp : GLAPComponent p (cs (Dgrp b x)) (Ipart p L b) := lemma105more_I_comp_CD hc hin h
  have hIJ : Ipart p L b ≤ Jpart p (Ipart p L b) a := le_closureIn_self _ _
  have hIx' : Ipart p L b ≤ cx x' :=
    (Ipart_le_cs h).trans (Subgroup.centralizer_le (by simpa using hx'D))
  have hsub : closureIn K B ⊓ cx x' ≤ cs (Dgrp b x) := by
    intro g hg
    have hga : g ∈ cx a := Jpart_le_cx h ha (by rw [← hKJ]; exact hg.1)
    have hDg : Dgrp b x ≤ cx g := by
      rw [hDeq]
      exact sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hga).symm))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hg.2).symm))
    exact Subgroup.mem_centralizer_iff.2 fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.1 (hDg hd)
  have hIJ' : GLAPComponent p (closureIn K B ⊓ cx x') (Ipart p L b) :=
    glaPComponent_of_le hp hIcomp (le_inf (by rw [hKJ]; exact hIJ) hIx') hsub
  exact hin.i1122 B a K x' (sstar_triple h.star).1 hess hK hx'B hx'K (Ipart p L b) hIJ'

theorem Ibar_pSimple_iso (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {K : Subgroup G} (hK : ∃ X : Subgroup G, GLAPComponent p X K)
    (e : Nonempty (PQuot p (Ipart p L b) ≃* PSimple p K)) :
    Nonempty (PSimple p (Ipart p L b) ≃* PSimple p K) := by
  have hp := hc.ctx.prime
  obtain ⟨X, hKX⟩ := hK
  obtain ⟨e⟩ := e
  haveI : IsSimpleGroup (PSimple p K) := (isQuasisimple_pQuot_of_glaPComponent hp hKX).2
  have hLcomp : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hbp : b ^ p = 1 := (B_el h).2 b h.mem
  obtain ⟨hIcomp, -⟩ := hin.i91comp (cx x) L b hLcomp hchev hbp h.prop h.I_ne
  haveI : IsSimpleGroup (PSimple p (Ipart p L b)) :=
    (isQuasisimple_pQuot_of_glaPComponent hp hIcomp).2
  exact lemma105more_quot_center_equiv (inferInstance) e

theorem type_of_Ibar_exc (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hp3 : p = 3)
    (hI : catalogIs (PSimple p (Ipart p L b)) excIndex) : catalogIs (PSimple p L) isExcL := by
  subst hp3
  have hLcomp : GLAPComponent 3 (cx x) L := (sstar_triple h.star).2.2
  have hchev : IsChevSimple 2 (PSimple 3 L) := sstar_chev2 hc h.star
  have hbp : b ^ 3 = 1 := (B_el h).2 b h.mem
  obtain ⟨hIcomp, -⟩ := hin.i91comp (cx x) L b hLcomp hchev hbp h.prop h.I_ne
  exact hin.l103.more.i91type.exc (cx x) L b hLcomp hchev hbp h.prop (h.td4_g2 rfl) hIcomp h.I_ne hI

theorem type_of_exc (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {a : G} (ha : a ∈ Dgrp b x) (hess : IsEssential p B a)
    {K : Subgroup G} {x' : G} (hK : GLAPComponent p (cx a) K)
    (hKJ : closureIn K B = Jpart p (Ipart p L b) a)
    (hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x')
    (hx'K : x' ∉ Subgroup.normalizer (K : Set G)) (hexc : IsExcType p K) :
    p = 3 ∧ catalogIs (PSimple p L) isExcL := by
  obtain ⟨f⟩ := Ibar_pSimple_iso hc hin h ⟨cx a, hK⟩ (Ibar_iso_Kbar hc hin h ha hess hK hKJ hDeq hx'K)
  exact ⟨hexc.1, type_of_Ibar_exc hc hin h hexc.1 ((catalogIs_congr f).2 hexc.2.2)⟩

theorem not_single_type (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hess : IsEssential p B a) (hns : ¬ GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)) :
    p = 3 ∧ catalogIs (PSimple p L) isExcL := by
  obtain ⟨K, x', hK, -, hKJ, hDeq, hx'K⟩ := exists_K_not_norm hc hin h ha ha1 hns
  have hnB : ¬ B ≤ Subgroup.normalizer (K : Set G) := fun hB => by
    refine hx'K (hB ?_)
    refine lemma105more_D_le_B h ?_
    rw [hDeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
  exact type_of_exc hc hin h ha hess hK hKJ hDeq hx'K
    (hin.i1131 B a K (sstar_triple h.star).1 hess hK hnB)

theorem Ja_SL3 (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) (hess : IsEssential p B a)
    (hns : ¬ GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)) (hp3 : p = 3)
    (hL3 : catalogIs (PSimple p L) S9.isL3char2) :
    ∃ K : Subgroup G, GLAPComponent p (cx a) K ∧ ¬ B ≤ Subgroup.normalizer (K : Set G) ∧
      catalogIs (PSimple p K) S9.isL3char2 ∧ Nat.card (Subgroup.center (PQuot p K)) = 3 ∧
      closureIn K B = Jpart p (Ipart p L b) a := by
  obtain ⟨K, x', hK, -, hKJ, hDeq, hx'K⟩ := exists_K_not_norm hc hin h ha ha1 hns
  have hnB : ¬ B ≤ Subgroup.normalizer (K : Set G) := fun hB => by
    refine hx'K (hB ?_)
    refine lemma105more_D_le_B h ?_
    rw [hDeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
  have hexc : IsExcType p K := hin.i1131 B a K (sstar_triple h.star).1 hess hK hnB
  obtain ⟨f⟩ := Ibar_pSimple_iso hc hin h ⟨cx a, hK⟩ (Ibar_iso_Kbar hc hin h ha hess hK hKJ hDeq hx'K)
  subst hp3
  have hLcomp : GLAPComponent 3 (cx x) L := (sstar_triple h.star).2.2
  have hchev : IsChevSimple 2 (PSimple 3 L) := sstar_chev2 hc h.star
  have hbp : b ^ 3 = 1 := (B_el h).2 b h.mem
  obtain ⟨hIcomp, -⟩ := hin.i91comp (cx x) L b hLcomp hchev hbp h.prop h.I_ne
  have hI3 := hin.l103.more.i91type.l3 (cx x) L b hLcomp hbp h.prop hIcomp h.I_ne hL3
  exact ⟨K, hK, hnB, (catalogIs_congr f).1 hI3, hexc.2.1, hKJ⟩

theorem single_comp (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) {S : Subgroup G} (hT : TData p B x L b S) {a : G} (ha : a ∈ Dgrp b x)
    (ha1 : a ≠ 1) (hTL : HasTL p B L) :
    GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) := by
  by_contra hns
  have hess := essential_105 hc h hT ha ha1
  obtain ⟨hp3, hty⟩ := not_single_type hc hin h ha ha1 hess hns
  have hL3 := l3_of_exc (not_sp4_u3 hc hin h hp3 hTL) hty
  obtain ⟨K, hK, hnK, hKty, hKZ, hKJ⟩ := Ja_SL3 hc hin h ha ha1 hess hns hp3 hL3
  subst hp3
  have haB : a ∈ B := (dgrp_facts hc h).1 ha
  have hIJ : Ipart 3 L b ≤ Jpart 3 (Ipart 3 L b) a := le_closureIn_self _ _
  have hSJ : S ≤ closureIn K B := by
    rw [hKJ]
    exact hT.le_I.trans hIJ
  have h114 := hin.i114 (cx a) B K (S8.isKGroup_cx hc.ctx ha1)
    (isElemAbelian_le_centralizer (B_el h) haB) (sstar_triple h.star).1 hK hnK hKty hKZ S hSJ hT.two hT.norm
  rw [hKJ] at h114
  exact hT.not_le ((le_inf hT.le_I h114).trans (core_inf_le hIJ))

theorem exc_J_eq_Ibar (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b)
    {S : Subgroup G} (hT : TData p B x L b S) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a))
    (hexc : IsExcType p (Jpart p (Ipart p L b) a)) :
    Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a := by
  have hp3 : p = 3 := hexc.1
  subst hp3
  by_contra hlt
  obtain ⟨T, hTI, hT2, hTB, hTO, -, -⟩ := T_of_TData hc h hT
  have hIJ : Ipart 3 L b ≤ Jpart 3 (Ipart 3 L b) a := le_closureIn_self _ _
  have hH : H104 3 B x L b a :=
    ⟨ha, ha1, essential_105 hc h hT ha ha1, hsingle, hlt, T, hTI.trans hIJ, hT2, hTB,
      fun hle => hTO ((le_inf hTI hle).trans (core_inf_le hIJ))⟩
  obtain ⟨hS2, hfield | ⟨-, htd, -, -⟩⟩ := lemma104_ab hc hin.l104 h hd5 hcase hH
  · obtain ⟨d, -, hd⟩ := hfield
    exact hin.l103.more.excfield (cx a) _ d hsingle hexc hd
  · exact (hin.l103.dist.td4_exc _ hS2.2 htd hexc.2.2).elim

theorem exc_Ibar_J (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b)
    {S : Subgroup G} (hT : TData p B x L b S) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hess : IsEssential p B a) (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a))
    {K : Subgroup G} (hK : GLAPComponent p (cx a) K)
    (hiso : Nonempty (PQuot p K ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (hnB : ¬ B ≤ Subgroup.normalizer (K : Set G)) :
    p = 3 ∧ IsExcType p (Jpart p (Ipart p L b) a) ∧
      Nonempty (PSimple p (Ipart p L b) ≃* PSimple p (Jpart p (Ipart p L b) a)) := by
  have hexc : IsExcType p K := hin.i1131 B a K (sstar_triple h.star).1 hess hK hnB
  have hexcJ : IsExcType p (Jpart p (Ipart p L b) a) := (isExcType_congr hiso).1 hexc
  have hsup := exc_J_eq_Ibar hc hin h hd5 hcase hT ha ha1 hsingle hexcJ
  have hIJ : Ipart p L b ≤ Jpart p (Ipart p L b) a := le_closureIn_self _ _
  obtain ⟨e⟩ := (cover_facts hc.ctx.prime hIJ hsup).2
  exact ⟨hexc.1, hexcJ, nonempty_pSimple_congr e⟩

theorem type_of_not_norm_same (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b)
    {S : Subgroup G} (hT : TData p B x L b S) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hess : IsEssential p B a) (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a))
    {K : Subgroup G} (hK : GLAPComponent p (cx a) K)
    (hiso : Nonempty (PQuot p K ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (hnB : ¬ B ≤ Subgroup.normalizer (K : Set G)) :
    p = 3 ∧ catalogIs (PSimple p L) isExcL := by
  obtain ⟨hp3, hexcJ, ⟨f⟩⟩ := exc_Ibar_J hc hin h hd5 hcase hT ha ha1 hess hsingle hK hiso hnB
  exact ⟨hp3, type_of_Ibar_exc hc hin h hp3 ((catalogIs_congr f).2 hexcJ.2.2)⟩

theorem J3_of_not_norm_same (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b)
    {S : Subgroup G} (hT : TData p B x L b S) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hess : IsEssential p B a) (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a))
    {K : Subgroup G} (hK : GLAPComponent p (cx a) K)
    (hiso : Nonempty (PQuot p K ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (hnB : ¬ B ≤ Subgroup.normalizer (K : Set G)) (hL3 : catalogIs (PSimple p L) S9.isL3char2) :
    catalogIs (PSimple p (Jpart p (Ipart p L b) a)) S9.isL3char2 ∧
      Nat.card (Subgroup.center (PQuot p (Jpart p (Ipart p L b) a))) = 3 := by
  obtain ⟨hp3, hexcJ, ⟨f⟩⟩ := exc_Ibar_J hc hin h hd5 hcase hT ha ha1 hess hsingle hK hiso hnB
  subst hp3
  have hLcomp : GLAPComponent 3 (cx x) L := (sstar_triple h.star).2.2
  have hchev : IsChevSimple 2 (PSimple 3 L) := sstar_chev2 hc h.star
  have hbp : b ^ 3 = 1 := (B_el h).2 b h.mem
  obtain ⟨hIcomp, -⟩ := hin.i91comp (cx x) L b hLcomp hchev hbp h.prop h.I_ne
  have hI3 := hin.l103.more.i91type.l3 (cx x) L b hLcomp hbp h.prop hIcomp h.I_ne hL3
  exact ⟨(catalogIs_congr f).1 hI3, hexcJ.2.1⟩

theorem four_components (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)) {K : Subgroup G}
    (hK : GLAPComponent p (cx a) K) (hiso : Nonempty (PQuot p K ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (hnB : ¬ B ≤ Subgroup.normalizer (K : Set G)) :
    ∃ K₁ K₂ K₃ K₄ : Subgroup G, K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₁ ≠ K₄ ∧ K₂ ≠ K₃ ∧ K₂ ≠ K₄ ∧ K₃ ≠ K₄ ∧
      GLAPComponent p (cx a) K₁ ∧ GLAPComponent p (cx a) K₂ ∧ GLAPComponent p (cx a) K₃ ∧
      GLAPComponent p (cx a) K₄ ∧ Nonempty (PQuot p K₁ ≃* PQuot p (Jpart p (Ipart p L b) a)) ∧
      Nonempty (PQuot p K₂ ≃* PQuot p (Jpart p (Ipart p L b) a)) ∧
      Nonempty (PQuot p K₃ ≃* PQuot p (Jpart p (Ipart p L b) a)) ∧
      Nonempty (PQuot p K₄ ≃* PQuot p (Jpart p (Ipart p L b) a)) := by
  classical
  have hp := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hB := B_el h
  have hDB : Dgrp b x ≤ B := lemma105more_D_le_B h
  have haB : a ∈ B := hDB ha
  have hBJ : ∀ g ∈ B, g ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    fun g hg => lemma105more_B_le_N_Jpart h haB hg
  obtain ⟨g₀, hg₀, g₁, hg₁, g₂, hg₂, h01, h02, h12⟩ := lemma105more_three_conj hp hp2 hB hnB
  have hCa : ∀ g ∈ B, GLBConj g (cx a) = cx a := fun g hg =>
    mem_normalizer_iff_gLBConj_eq.1 (lemma105more_normalizer_centralizer (isElemAbelian_commute hB hg haB))
  have hconjC : ∀ g ∈ B, GLAPComponent p (cx a) (GLBConj g K) := fun g hg => by
    have := glaPComponent_gLBConj hK g
    rwa [hCa g hg] at this
  have hconjIso : ∀ g : G, Nonempty (PQuot p (GLBConj g K) ≃* PQuot p (Jpart p (Ipart p L b) a)) :=
    fun g => by
      obtain ⟨e1⟩ := lemma105more_pQuot_gLBConj p K g
      obtain ⟨e2⟩ := hiso
      exact ⟨e1.trans e2⟩
  have hne : ∀ g ∈ B, Jpart p (Ipart p L b) a ≠ GLBConj g K := by
    intro g hg heq
    apply hnB
    have hKg : GLBConj g⁻¹ (GLBConj g K) = K := by
      rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
    rw [← heq] at hKg
    have hK' : K = Jpart p (Ipart p L b) a := by
      rw [← hKg]
      exact mem_normalizer_iff_gLBConj_eq.1 (hBJ g⁻¹ (B.inv_mem hg))
    rw [hK']
    exact fun g' hg' => hBJ g' hg'
  refine ⟨Jpart p (Ipart p L b) a, GLBConj g₀ K, GLBConj g₁ K, GLBConj g₂ K,
    hne g₀ hg₀, hne g₁ hg₁, hne g₂ hg₂, h01, h02, h12, hsingle, hconjC g₀ hg₀, hconjC g₁ hg₁,
    hconjC g₂ hg₂, ⟨MulEquiv.refl _⟩, hconjIso g₀, hconjIso g₁, hconjIso g₂⟩

private theorem lemma105more_r4_comm_barX {X K L : Subgroup G} (hK : GLAPComponent p X K)
    (hL : GLAPComponent p X L) (hne : K ≠ L) :
    ∀ x ∈ barX p X K, ∀ y ∈ barX p X L, x * y = y * x := by
  have hne' : barX p X K ≠ barX p X L := fun h => hne (glaPComponent_unique hK hL h)
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK.2.2.1 hL.2.2.1 hne'
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

private theorem lemma105more_r4_card_barX {C E : Subgroup G} (hp : p.Prime) (hE : IsPGroup p E)
    (hEC : E ≤ C) : Nat.card (barX p C E) = Nat.card E := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (E.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp hp hE hEC
  have hrange : f.range = barX p C E := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]

private theorem lemma105more_r4_card_center_barX {C K : Subgroup G} (hp : p.Prime) (hKC : K ≤ C)
    (hsn : IsSubnormal K C) {n : ℕ} (h : Nat.card (Subgroup.center (PQuot p K)) = n) :
    Nat.card (Subgroup.center ↥(barX p C K)) = n := by
  rw [← h]
  exact (Nat.card_congr (Subgroup.centerCongr (quotEquivBarX hp hKC hsn)).toEquiv).symm

private theorem lemma105more_r4_card_le_of_central {Q : Type} [Group Q] [Finite Q]
    {K W : Subgroup Q} (hK : Nat.card (Subgroup.center ↥K) = 3) (hWK : W ≤ K)
    (hW : ∀ x ∈ W, ∀ y ∈ K, x * y = y * x) : Nat.card W ≤ 3 := by
  have hle : W.subgroupOf K ≤ Subgroup.center ↥K := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hz' : (z : Q) ∈ W := Subgroup.mem_subgroupOf.1 hz
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hW (z : Q) hz' (g : Q) g.2).symm
  have h1 : Nat.card (W.subgroupOf K) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv
  rw [← h1, ← hK]
  exact Subgroup.card_le_of_le hle

private theorem lemma105more_r4_three_mul_le {Q : Type} [Group Q] [Finite Q] {A B : Subgroup Q}
    (hB : B ≤ Subgroup.normalizer (A : Set Q)) (hB9 : Nat.card B = 9)
    (hI : Nat.card (A ⊓ B : Subgroup Q) ≤ 3) :
    3 * Nat.card A ≤ Nat.card (A ⊔ B : Subgroup Q) := by
  have h := card_sup_mul_card_inf_of_le_normalizer hB
  rw [hB9] at h
  nlinarith [Nat.mul_le_mul_left (Nat.card (A ⊔ B : Subgroup Q)) hI]

private theorem lemma105more_r4_cent_of {Q : Type} [Group Q] {X Y X' Y' : Subgroup Q}
    (c : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hX : X' ≤ X) (hY : Y' ≤ Y) :
    Y' ≤ Subgroup.centralizer (X' : Set Q) :=
  fun y hy => Subgroup.mem_centralizer_iff.2 (fun h hh => c h (hX hh) y (hY hy))

private theorem lemma105more_r4_symm {Q : Type} [Group Q] {A B : Subgroup Q}
    (h : A ≤ Subgroup.centralizer (B : Set Q)) : B ≤ Subgroup.centralizer (A : Set Q) :=
  fun b hb => Subgroup.mem_centralizer_iff.2
    (fun a ha => ((Subgroup.mem_centralizer_iff.1 (h ha)) b hb).symm)

private theorem lemma105more_r4_comm_of_isElemAbelian {Q : Type} [Group Q] {p : ℕ} {A : Subgroup Q}
    (hA : IsElemAbelian p A) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

private theorem lemma105more_r4_sup_elemAbelian {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    {A B : Subgroup Q} (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hBA : B ≤ Subgroup.centralizer (A : Set Q)) : IsElemAbelian p (A ⊔ B : Subgroup Q) := by
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hBA hb)) a ha
  have hi : ∀ a ∈ A, ∀ x ∈ A ⊔ B, a * x = x * a := by
    intro a ha
    have hS : A ⊔ B ≤ Subgroup.centralizer ({a} : Set Q) := by
      refine sup_le (fun a' ha' => Subgroup.mem_centralizer_iff.2 ?_)
        (fun b hb => Subgroup.mem_centralizer_iff.2 ?_)
      · intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact lemma105more_r4_comm_of_isElemAbelian hA a ha a' ha'
      · intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hAB a ha b hb
    intro x hx
    exact Subgroup.mem_centralizer_iff.1 (hS hx) a (Set.mem_singleton a)
  have hii : ∀ b ∈ B, ∀ x ∈ A ⊔ B, b * x = x * b := by
    intro b hb
    have hS : A ⊔ B ≤ Subgroup.centralizer ({b} : Set Q) := by
      refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 ?_)
        (fun b' hb' => Subgroup.mem_centralizer_iff.2 ?_)
      · intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hAB a ha b hb).symm
      · intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact lemma105more_r4_comm_of_isElemAbelian hB b hb b' hb'
    intro x hx
    exact Subgroup.mem_centralizer_iff.1 (hS hx) b (Set.mem_singleton b)
  have hcomm : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
    intro x hx
    have hS : A ⊔ B ≤ Subgroup.centralizer ({x} : Set Q) := by
      refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 ?_)
        (fun b hb => Subgroup.mem_centralizer_iff.2 ?_)
      · intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hi a ha x hx).symm
      · intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hii b hb x hx).symm
    intro y hy
    exact Subgroup.mem_centralizer_iff.1 (hS hy) x (Set.mem_singleton x)
  have hexp : ∀ x ∈ A ⊔ B, x ^ p = 1 := by
    let Ω : Subgroup Q :=
      { carrier := {x | x ∈ A ⊔ B ∧ x ^ p = 1}
        mul_mem' := fun {x y} hx hy => ⟨(A ⊔ B).mul_mem hx.1 hy.1, by
          have hc : Commute x y := hcomm x hx.1 y hy.1
          rw [hc.mul_pow, hx.2, hy.2, one_mul]⟩
        one_mem' := ⟨(A ⊔ B).one_mem, by rw [one_pow]⟩
        inv_mem' := fun {x} hx => ⟨(A ⊔ B).inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
    have hΩ : A ⊔ B ≤ Ω :=
      sup_le (fun a ha => ⟨Subgroup.mem_sup_left ha, hA.2 a ha⟩)
        (fun b hb => ⟨Subgroup.mem_sup_right hb, hB.2 b hb⟩)
    exact fun x hx => (hΩ hx).2
  exact ⟨⟨⟨fun u v => Subtype.ext (hcomm u u.2 v v.2)⟩⟩, fun x hx => hexp x hx⟩

private theorem lemma105more_r4_barX_ne_bot {C K T : Subgroup G} (hp : p.Prime) (hKC : K ≤ C)
    (hsn : IsSubnormal K C) (hTK : T ≤ K) (hT : ¬ T ≤ GLAPPrimeCoreOf p K) :
    barX p C T ≠ ⊥ := by
  intro hbot
  apply hT
  have hTC : T ≤ C := hTK.trans hKC
  have hTO : T ≤ GLAPPrimeCoreOf p C := by
    intro t ht
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨t, hTC ht⟩ : ↥C ⧸ GLAPPrimeCore p ↥C) ∈
        barX p C T :=
      Subgroup.mem_map.2 ⟨⟨t, hTC ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
  exact le_inf hTK hTO

private theorem lemma105more_r4_barX_mono {C S S' : Subgroup G} (h : S ≤ S') :
    barX p C S ≤ barX p C S' := by
  rintro _ ⟨c, hc, rfl⟩
  exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hc)), rfl⟩

private theorem lemma105more_r4_isPGroup_map {q : ℕ} {C T : Subgroup G} (hT : IsPGroup q T)
    (hTC : T ≤ C) : IsPGroup q ↥(barX p C T) :=
  IsPGroup.map (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm) _

private theorem lemma105more_r4_isPGroup_of {Q : Type} [Group Q] {p : ℕ} {E : Subgroup Q}
    (hE : IsElemAbelian p E) : IsPGroup p E :=
  fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩

theorem rank_of_four (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (hp3 : p = 3)
    (hJ3 : catalogIs (PSimple p (Jpart p (Ipart p L b) a)) S9.isL3char2)
    (hJZ : Nat.card (Subgroup.center (PQuot p (Jpart p (Ipart p L b) a))) = 3)
    {K₁ K₂ K₃ K₄ : Subgroup G} (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h14 : K₁ ≠ K₄) (h23 : K₂ ≠ K₃)
    (h24 : K₂ ≠ K₄) (h34 : K₃ ≠ K₄) (hK₁ : GLAPComponent p (cx a) K₁) (hK₂ : GLAPComponent p (cx a) K₂)
    (hK₃ : GLAPComponent p (cx a) K₃) (hK₄ : GLAPComponent p (cx a) K₄)
    (e₁ : Nonempty (PQuot p K₁ ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (e₂ : Nonempty (PQuot p K₂ ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (e₃ : Nonempty (PQuot p K₃ ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (e₄ : Nonempty (PQuot p K₄ ≃* PQuot p (Jpart p (Ipart p L b) a))) :
    5 ≤ GLATwoLocalRank p ↥(cx a) := by
  subst hp3
  set C : Subgroup G := cx a with hCdef
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hcen : ∀ {K : Subgroup G}, Nonempty (PQuot 3 K ≃* PQuot 3 (Jpart 3 (Ipart 3 L b) a)) →
      Nat.card (Subgroup.center (PQuot 3 K)) = 3 := by
    rintro K ⟨e⟩
    exact (card_center_pQuot_congr e).trans hJZ
  have hcat : ∀ {K : Subgroup G}, Nonempty (PQuot 3 K ≃* PQuot 3 (Jpart 3 (Ipart 3 L b) a)) →
      catalogIs (PSimple 3 K) S9.isL3char2 := by
    rintro K ⟨e⟩
    obtain ⟨f⟩ := nonempty_pSimple_congr e
    exact (catalogIs_congr f).2 hJ3
  obtain ⟨E₁, T₁, hE₁K, hE₁, hE₁c, hT₁K, hT₁2, hE₁T, hT₁n⟩ :=
    hin.l103.more.sl3tor C K₁ hK₁ (hcat e₁) (hcen e₁)
  obtain ⟨E₂, _, hE₂K, hE₂, hE₂c, _, _, _, _⟩ :=
    hin.l103.more.sl3tor C K₂ hK₂ (hcat e₂) (hcen e₂)
  obtain ⟨E₃, _, hE₃K, hE₃, hE₃c, _, _, _, _⟩ :=
    hin.l103.more.sl3tor C K₃ hK₃ (hcat e₃) (hcen e₃)
  obtain ⟨E₄, _, hE₄K, hE₄, hE₄c, _, _, _, _⟩ :=
    hin.l103.more.sl3tor C K₄ hK₄ (hcat e₄) (hcen e₄)
  have hKC₁ : K₁ ≤ C := hK₁.1
  have hKC₂ : K₂ ≤ C := hK₂.1
  have hKC₃ : K₃ ≤ C := hK₃.1
  have hKC₄ : K₄ ≤ C := hK₄.1
  have hsn₁ : IsSubnormal K₁ C := hK₁.2.1
  have hsn₂ : IsSubnormal K₂ C := hK₂.2.1
  have hsn₃ : IsSubnormal K₃ C := hK₃.2.1
  have hsn₄ : IsSubnormal K₄ C := hK₄.2.1
  have hz₂ : Nat.card (Subgroup.center ↥(barX 3 C K₂)) = 3 :=
    lemma105more_r4_card_center_barX hp hKC₂ hsn₂ (hcen e₂)
  have hz₃ : Nat.card (Subgroup.center ↥(barX 3 C K₃)) = 3 :=
    lemma105more_r4_card_center_barX hp hKC₃ hsn₃ (hcen e₃)
  have hz₄ : Nat.card (Subgroup.center ↥(barX 3 C K₄)) = 3 :=
    lemma105more_r4_card_center_barX hp hKC₄ hsn₄ (hcen e₄)
  have hEC₁ : E₁ ≤ C := hE₁K.trans hKC₁
  have hEC₂ : E₂ ≤ C := hE₂K.trans hKC₂
  have hEC₃ : E₃ ≤ C := hE₃K.trans hKC₃
  have hEC₄ : E₄ ≤ C := hE₄K.trans hKC₄
  have hn₁ : Nat.card (barX 3 C E₁) = 9 := by
    rw [lemma105more_r4_card_barX hp (lemma105more_r4_isPGroup_of hE₁) hEC₁]
    simpa using hE₁c
  have hn₂ : Nat.card (barX 3 C E₂) = 9 := by
    rw [lemma105more_r4_card_barX hp (lemma105more_r4_isPGroup_of hE₂) hEC₂]
    simpa using hE₂c
  have hn₃ : Nat.card (barX 3 C E₃) = 9 := by
    rw [lemma105more_r4_card_barX hp (lemma105more_r4_isPGroup_of hE₃) hEC₃]
    simpa using hE₃c
  have hn₄ : Nat.card (barX 3 C E₄) = 9 := by
    rw [lemma105more_r4_card_barX hp (lemma105more_r4_isPGroup_of hE₄) hEC₄]
    simpa using hE₄c
  have hA1 : IsElemAbelian 3 (barX 3 C E₁) := isElemAbelian_barX hE₁
  have hB2 : IsElemAbelian 3 (barX 3 C E₂) := isElemAbelian_barX hE₂
  have hB3 : IsElemAbelian 3 (barX 3 C E₃) := isElemAbelian_barX hE₃
  have hB4 : IsElemAbelian 3 (barX 3 C E₄) := isElemAbelian_barX hE₄
  have c12 := lemma105more_r4_comm_barX hK₁ hK₂ h12
  have c13 := lemma105more_r4_comm_barX hK₁ hK₃ h13
  have c14 := lemma105more_r4_comm_barX hK₁ hK₄ h14
  have c23 := lemma105more_r4_comm_barX hK₂ hK₃ h23
  have c24 := lemma105more_r4_comm_barX hK₂ hK₄ h24
  have c34 := lemma105more_r4_comm_barX hK₃ hK₄ h34
  have hE₁Q : barX 3 C E₁ ≤ barX 3 C K₁ := lemma105more_r4_barX_mono hE₁K
  have hE₂Q : barX 3 C E₂ ≤ barX 3 C K₂ := lemma105more_r4_barX_mono hE₂K
  have hE₃Q : barX 3 C E₃ ≤ barX 3 C K₃ := lemma105more_r4_barX_mono hE₃K
  have hE₄Q : barX 3 C E₄ ≤ barX 3 C K₄ := lemma105more_r4_barX_mono hE₄K
  have hT₁Q : barX 3 C T₁ ≤ barX 3 C K₁ := lemma105more_r4_barX_mono hT₁K
  have cE12 := lemma105more_r4_cent_of (X := barX 3 C K₂) (Y := barX 3 C K₁)
    (X' := barX 3 C K₂) (Y' := barX 3 C E₁) (fun x hx y hy => (c12 y hy x hx).symm) le_rfl hE₁Q
  have cE13 := lemma105more_r4_cent_of (X := barX 3 C K₃) (Y := barX 3 C K₁)
    (X' := barX 3 C K₃) (Y' := barX 3 C E₁) (fun x hx y hy => (c13 y hy x hx).symm) le_rfl hE₁Q
  have cE14 := lemma105more_r4_cent_of (X := barX 3 C K₄) (Y := barX 3 C K₁)
    (X' := barX 3 C K₄) (Y' := barX 3 C E₁) (fun x hx y hy => (c14 y hy x hx).symm) le_rfl hE₁Q
  have cE23 := lemma105more_r4_cent_of (X := barX 3 C K₃) (Y := barX 3 C K₂)
    (X' := barX 3 C K₃) (Y' := barX 3 C E₂) (fun x hx y hy => (c23 y hy x hx).symm) le_rfl hE₂Q
  have cE24 := lemma105more_r4_cent_of (X := barX 3 C K₄) (Y := barX 3 C K₂)
    (X' := barX 3 C K₄) (Y' := barX 3 C E₂) (fun x hx y hy => (c24 y hy x hx).symm) le_rfl hE₂Q
  have cE34 := lemma105more_r4_cent_of (X := barX 3 C K₄) (Y := barX 3 C K₃)
    (X' := barX 3 C K₄) (Y' := barX 3 C E₃) (fun x hx y hy => (c34 y hy x hx).symm) le_rfl hE₃Q
  have hBA2 : barX 3 C E₂ ≤ Subgroup.centralizer (barX 3 C E₁ : Set _) :=
    lemma105more_r4_cent_of (X := barX 3 C K₁) (Y := barX 3 C K₂) (X' := barX 3 C E₁)
      (Y' := barX 3 C E₂) c12 hE₁Q hE₂Q
  have hAK2 := sup_le cE13 cE23
  have hAK3 := sup_le (sup_le cE14 cE24) cE34
  have hBA3 : barX 3 C E₃ ≤ Subgroup.centralizer ((barX 3 C E₁ ⊔ barX 3 C E₂ : Subgroup _) : Set _) :=
    fun y hy => lemma105more_r4_symm hAK2 (hE₃Q hy)
  have hBA4 : barX 3 C E₄ ≤
      Subgroup.centralizer ((barX 3 C E₁ ⊔ barX 3 C E₂ ⊔ barX 3 C E₃ : Subgroup _) : Set _) :=
    fun y hy => lemma105more_r4_symm hAK3 (hE₄Q hy)
  have hA₂ := lemma105more_r4_sup_elemAbelian hA1 hB2 hBA2
  have hA₃ := lemma105more_r4_sup_elemAbelian hA₂ hB3 hBA3
  have hA₄ := lemma105more_r4_sup_elemAbelian hA₃ hB4 hBA4
  have hI₂ : Nat.card (barX 3 C E₁ ⊓ barX 3 C E₂ : Subgroup _) ≤ 3 :=
    lemma105more_r4_card_le_of_central hz₂ (inf_le_right.trans hE₂Q)
      (fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (cE12 hx.1) y hy).symm)
  have hI₃ : Nat.card ((barX 3 C E₁ ⊔ barX 3 C E₂) ⊓ barX 3 C E₃ : Subgroup _) ≤ 3 :=
    lemma105more_r4_card_le_of_central hz₃ (inf_le_right.trans hE₃Q)
      (fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hAK2 hx.1) y hy).symm)
  have hI₄ : Nat.card ((barX 3 C E₁ ⊔ barX 3 C E₂ ⊔ barX 3 C E₃) ⊓ barX 3 C E₄ : Subgroup _) ≤ 3 :=
    lemma105more_r4_card_le_of_central hz₄ (inf_le_right.trans hE₄Q)
      (fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hAK3 hx.1) y hy).symm)
  have hc₂ : 3 * Nat.card (barX 3 C E₁ : Subgroup _) ≤
      Nat.card (barX 3 C E₁ ⊔ barX 3 C E₂ : Subgroup _) :=
    lemma105more_r4_three_mul_le (hBA2.trans (Subgroup.centralizer_le_normalizer _)) hn₂ hI₂
  have hc₃ : 3 * Nat.card (barX 3 C E₁ ⊔ barX 3 C E₂ : Subgroup _) ≤
      Nat.card (barX 3 C E₁ ⊔ barX 3 C E₂ ⊔ barX 3 C E₃ : Subgroup _) :=
    lemma105more_r4_three_mul_le (hBA3.trans (Subgroup.centralizer_le_normalizer _)) hn₃ hI₃
  have hc₄ : 3 * Nat.card (barX 3 C E₁ ⊔ barX 3 C E₂ ⊔ barX 3 C E₃ : Subgroup _) ≤
      Nat.card (barX 3 C E₁ ⊔ barX 3 C E₂ ⊔ barX 3 C E₃ ⊔ barX 3 C E₄ : Subgroup _) :=
    lemma105more_r4_three_mul_le (hBA4.trans (Subgroup.centralizer_le_normalizer _)) hn₄ hI₄
  have h243 : 243 ≤ Nat.card (barX 3 C E₁ ⊔ barX 3 C E₂ ⊔ barX 3 C E₃ ⊔ barX 3 C E₄ :
      Subgroup _) := by
    omega
  obtain ⟨n, hn⟩ := (lemma105more_r4_isPGroup_of hA₄).exists_card_eq
  have h5n : 5 ≤ n := by
    by_contra hlt
    rw [not_le] at hlt
    have h81 : 3 ^ n ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h243' : 243 ≤ 3 ^ n := hn ▸ h243
    norm_num at h81
    linarith
  have hpr : n ≤ CFSG.Open.pRank 3 (barX 3 C E₁ ⊔ barX 3 C E₂ ⊔ barX 3 C E₃ ⊔ barX 3 C E₄ :
      Subgroup _) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hA₄ hn
  have hTbne : barX 3 C T₁ ≠ ⊥ := lemma105more_r4_barX_ne_bot hp hKC₁ hsn₁ hT₁K hT₁n
  have hTb2 : IsPGroup 2 ↥(barX 3 C T₁) := lemma105more_r4_isPGroup_map hT₁2 (hT₁K.trans hKC₁)
  have hN1 : barX 3 C E₁ ≤ Subgroup.normalizer ((barX 3 C T₁ : Subgroup _) : Set _) :=
    barX_le_normalizer hE₁T
  have hN2 : barX 3 C E₂ ≤ Subgroup.normalizer ((barX 3 C T₁ : Subgroup _) : Set _) :=
    (lemma105more_r4_cent_of (X := barX 3 C K₁) (Y := barX 3 C K₂) (X' := barX 3 C T₁)
      (Y' := barX 3 C E₂) c12 hT₁Q hE₂Q).trans (Subgroup.centralizer_le_normalizer _)
  have hN3 : barX 3 C E₃ ≤ Subgroup.normalizer ((barX 3 C T₁ : Subgroup _) : Set _) :=
    (lemma105more_r4_cent_of (X := barX 3 C K₁) (Y := barX 3 C K₃) (X' := barX 3 C T₁)
      (Y' := barX 3 C E₃) c13 hT₁Q hE₃Q).trans (Subgroup.centralizer_le_normalizer _)
  have hN4 : barX 3 C E₄ ≤ Subgroup.normalizer ((barX 3 C T₁ : Subgroup _) : Set _) :=
    (lemma105more_r4_cent_of (X := barX 3 C K₁) (Y := barX 3 C K₄) (X' := barX 3 C T₁)
      (Y' := barX 3 C E₄) c14 hT₁Q hE₄Q).trans (Subgroup.centralizer_le_normalizer _)
  have hTbN := sup_le (sup_le (sup_le hN1 hN2) hN3) hN4
  have hpN := CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_normalizes
    hp hTbne hTb2 hTbN
  have hNdvd : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCore 3 ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (lemma105more_coprime_pPrimeCore 3 ↥C)
  have hquot := CFSG.LocalAnalysis.GLTheoremB.glaTwoLocalRank_quotient_le hp (by norm_num)
    (GLAPPrimeCore 3 ↥C) hNdvd
  exact h5n.trans (hpr.trans (hpN.trans hquot))

theorem rank_five_of_orbit (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {a : G} (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a)) {K : Subgroup G}
    (hK : GLAPComponent p (cx a) K) (hiso : Nonempty (PQuot p K ≃* PQuot p (Jpart p (Ipart p L b) a)))
    (hnB : ¬ B ≤ Subgroup.normalizer (K : Set G)) (hp3 : p = 3)
    (hJ3 : catalogIs (PSimple p (Jpart p (Ipart p L b) a)) S9.isL3char2)
    (hJZ : Nat.card (Subgroup.center (PQuot p (Jpart p (Ipart p L b) a))) = 3) :
    5 ≤ GLATwoLocalRank p G := by
  obtain ⟨K₁, K₂, K₃, K₄, h12, h13, h14, h23, h24, h34, hK₁, hK₂, hK₃, hK₄, e₁, e₂, e₃, e₄⟩ :=
    four_components hc hin h ha ha1 hsingle hK hiso hnB
  exact (rank_of_four hc hin h ha hp3 hJ3 hJZ h12 h13 h14 h23 h24 h34 hK₁ hK₂ hK₃ hK₄ e₁ e₂ e₃ e₄).trans
    (glaTwoLocalRank_subgroup_le hc.ctx.prime.one_lt (cx a))

theorem rank_le_four_L3 (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hp3 : p = 3)
    (hL3 : catalogIs (PSimple p L) S9.isL3char2) : GLATwoLocalRank p G ≤ 4 := by
  subst hp3
  have hS := sstar_triple h.star
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hxp : x ^ 3 = 1 := hS.1.1.2 x hS.2.1.1
  have h1 := hin.l103.more.autl3 (cx x) L B hS.2.2 hL3 (sstar_norm h.star) (B_el h)
  rw [cent_B_eq hc h.star, Nat.card_zpowers, orderOf_eq_prime hxp hx1, hS.1.2.1] at h1
  by_contra hlt
  push_neg at hlt
  have h5 : 3 ^ 5 ≤ 3 ^ GLATwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hlt
  have h6 := h5.trans h1
  norm_num at h6

theorem norm_same_type (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b)
    {S : Subgroup G} (hT : TData p B x L b S) {a : G}
    (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) (hTL : HasTL p B L)
    {K : Subgroup G} (hK : GLAPComponent p (cx a) K)
    (hiso : Nonempty (PQuot p K ≃* PQuot p (Jpart p (Ipart p L b) a))) :
    B ≤ Subgroup.normalizer (K : Set G) := by
  by_contra hnB
  have hess := essential_105 hc h hT ha ha1
  have hsingle := single_comp hc hin h hT ha ha1 hTL
  obtain ⟨hp3, hty⟩ := type_of_not_norm_same hc hin h hd5 hcase hT ha ha1 hess hsingle hK hiso hnB
  have hL3 := l3_of_exc (not_sp4_u3 hc hin h hp3 hTL) hty
  obtain ⟨hJ3, hJZ⟩ := J3_of_not_norm_same hc hin h hd5 hcase hT ha ha1 hess hsingle hK hiso hnB hL3
  have h5 := rank_five_of_orbit hc hin h ha ha1 hsingle hK hiso hnB hp3 hJ3 hJZ
  have h4 := rank_le_four_L3 hc hin h hp3 hL3
  omega

theorem lemma105 (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hcase : CaseAB G p B x L b) :
    Concl105 G p B x L b := by
  obtain ⟨S, hT⟩ := exists_TData hc hin h hd5 hcase
  have hno := no_two_local hc hin h hd5 hcase
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x))) :=
    oddCore_of_noTwoLocal hc h hxD (sstar_triple h.star).2.1.2.1 hno
  have hcentral : ∀ T : Subgroup G, T ≤ GLAPPrimeCoreOf p (cx x) → IsPGroup 2 T →
      B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥ := by
    intro T hTO hT2 _
    rw [eq_bot_of_le_odd hT2 hodd hTO]
    simp
  have hTL := exists_T_in_L hc hin.l103 h hcentral
  exact
    { odd_comm := odd_comm hc hin h hcase
      no_two_local := hno
      odd_core := fun a ha ha1 => oddCore_of_noTwoLocal hc h ha ha1 hno
      T_exists := T_of_TData hc h hT
      single := fun a ha ha1 => ⟨single_comp hc hin h hT ha ha1 hTL, fun K hK hiso =>
        norm_same_type hc hin h hd5 hcase hT ha ha1 hTL hK hiso⟩
      essential := fun a ha ha1 => essential_105 hc h hT ha ha1 }

end S10

end CFSG.LocalAnalysis.GLTheoremA
