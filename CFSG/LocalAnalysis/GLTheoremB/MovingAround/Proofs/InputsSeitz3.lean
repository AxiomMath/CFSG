module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex IsTwoPow Bal207Index IsL2EightIndex
  IsF4EightIndex IsD4FourIndex FourIndex Seitz2310CubeSimple isLThreeFour_of_index planeGen_of_kfact
  closure_eq_seitzHyperGamma)
open CFSG.LieType.Seitz (seitzHyperGamma fixedPoints mem_fixedPoints)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)
open GL83.CompFam

@[expose] def SeitzQuasiHigh : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → p ^ 2 ≤ Nat.card E →
      (p ^ 4 ≤ Nat.card E ∨ Subgroup.center K ≠ ⊥) →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
        seitzHyperGamma p E = ⊤

theorem exc_of_d2Exc {p : ℕ} {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (h : IsD2SeitzException p d.1) :
    (ExcIndex p d.1 ∧ ¬ IsSixIndex d.1) ∨ (p = 3 ∧ IsLThreeFour S) := by
  rcases h with ⟨hp, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ |
      ⟨q, hq2, hq3, hd | hd⟩ | hd⟩ | ⟨hp, hd | hd⟩
  · subst hp
    left
    rw [hd]
    simp [ExcIndex, IsL2EightIndex, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow, hq2, hq3]
  · exact Or.inr ⟨hp, isLThreeFour_of_index d q hd ⟨hq2, hq3⟩ e⟩
  · subst hp
    left
    rw [hd]
    simp [ExcIndex, Bal207Index, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow, hq2, hq3]
  · subst hp
    left
    rw [hd]
    simp [ExcIndex, Bal207Index, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow, hq2, hq3]
  · subst hp
    left
    rw [hd]
    simp [ExcIndex, Bal207Index, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow, hq2, hq3]
  · subst hp
    left
    rw [hd]
    simp [ExcIndex, Bal207Index, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex]
  · subst hp
    left
    rw [hd]
    simp [ExcIndex, Bal207Index, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex]
  · subst hp
    left
    rw [hd]
    simp [ExcIndex, Bal207Index, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex]

theorem not_d2Exc {p : ℕ} {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hex : ¬ ExcIndex p d.1 ∨ IsSixIndex d.1)
    (hL34 : ¬ (p = 3 ∧ IsLThreeFour S)) : ¬ IsD2SeitzException p d.1 := by
  intro h
  rcases exc_of_d2Exc d e h with ⟨h1, h2⟩ | h3
  · rcases hex with h | h
    · exact h h1
    · exact h2 h
  · exact hL34 h3

theorem excIndex_ge_five {p : ℕ} (hp5 : 5 ≤ p) {d : TauCeti.LieTypeIndex} (h : ExcIndex p d) :
    p = 5 ∧ (d = .tits ∨ d = .suzuki 2 ∨ d = .reeF4 2) := by
  rcases h with h | ⟨h3, -⟩
  · cases d <;> simp only [Bal207Index] at h
    case tits => exact ⟨h.resolve_left (by omega), Or.inl rfl⟩
    case suzuki m =>
      obtain ⟨h1, rfl⟩ := h
      exact ⟨h1, Or.inr (Or.inl rfl)⟩
    case reeF4 m =>
      obtain ⟨h1, rfl⟩ := h
      exact ⟨h1, Or.inr (Or.inr rfl)⟩
    all_goals exact absurd h.1 (by omega)
  · omega

theorem isLThreeFour_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : IsLThreeFour T) :
    IsLThreeFour S := by
  obtain ⟨F, hF, hFin, hcard, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFin, hcard, ⟨e.trans f⟩⟩

theorem pRank_mulAut_le_two_of_l34 {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (h : IsLThreeFour (K ⧸ Subgroup.center K)) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 :=
  (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (quotientCenterAut' K)
    (quotientCenterAut'_injective hperf)).trans (pRank_mulAut_le_two_of_isLThreeFour h)

section Quasi

variable {K : Type} [Group K]

noncomputable def equivCenterQuot (hZ : Subgroup.center K = ⊥) : K ≃* K ⧸ Subgroup.center K :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)

theorem isSimpleGroup_of_center_eq_bot (hq : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup K := by
  haveI := hq.2
  exact MulEquiv.isSimpleGroup (equivCenterQuot hZ)

theorem exists_noncomm_of_quasisimple (hq : CFSG.Open.IsQuasisimple K) : ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.exists_noncomm_quot hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem mem_fixedPoints_zpowers {S : Type*} [Group S] {f : MulAut S} {s : S} (hs : f s = s) :
    s ∈ fixedPoints (Subgroup.zpowers f) := by
  rw [mem_fixedPoints]
  intro φ hφ
  have h : Subgroup.zpowers f ≤ MulAction.stabilizer (MulAut S) s :=
    (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact hs)
  exact MulAction.mem_stabilizer_iff.1 (h hφ)

theorem relIndex_zpowers {S : Type*} [Group S] {p : ℕ} (hp : p.Prime) {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) {f : MulAut S} (hf : f ∈ E) (hf1 : f ≠ 1) :
    (Subgroup.zpowers f).relIndex E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : Subgroup.zpowers f ≤ E := (Subgroup.zpowers_le).2 hf
  have hc : Nat.card (Subgroup.zpowers f) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE.2 f hf) hf1
  have h := Subgroup.relIndex_mul_card (Subgroup.zpowers f) E
  rw [inf_of_le_left hle, hc, hcard] at h
  have h' : (Subgroup.zpowers f).relIndex E * p = p * p := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hp.pos h'

theorem seitzHyperGamma_eq_top_of_plane (h2 : KFactSeitzRankTwo) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center K = ⊥) (d : TauCeti.ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) (hpd : p ≠ d.1.characteristic)
    (hnd : ¬ IsD2SeitzException p d.1) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) : seitzHyperGamma p E = ⊤ := by
  have hgen := planeGen_of_kfact h2 hp hp2 d ((equivCenterQuot hZ).trans e) hpd hnd hE hcard
  rw [← closure_eq_seitzHyperGamma, eq_top_iff, ← hgen]
  refine Subgroup.closure_mono ?_
  rintro s ⟨f, hf, hf1, hfs⟩
  exact ⟨Subgroup.zpowers f, (Subgroup.zpowers_le).2 hf, relIndex_zpowers hp hE hcard hf hf1,
    mem_fixedPoints.1 (mem_fixedPoints_zpowers hfs)⟩

variable [Finite K]

theorem seitzHyperGamma_eq_top_of_seitz (h2 : KFactSeitzRankTwo) (h3 : Seitz2310CubeSimple)
    (hR : SeitzQuasiHigh) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : CFSG.Open.IsQuasisimple K)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hpd : p ≠ d.1.characteristic) (hL34 : ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hE2 : p ^ 2 ≤ Nat.card E)
    (hex : ¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) :
    seitzHyperGamma p E = ⊤ := by
  by_cases hhigh : p ^ 4 ≤ Nat.card E ∨ Subgroup.center K ≠ ⊥
  · exact hR p hp hp2 K hq d hd hpd hL34 E hE hE2 hhigh hex
  push Not at hhigh
  obtain ⟨hlt, hZ⟩ := hhigh
  obtain ⟨e⟩ := hd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hE
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [← hk]; exact hE2)
  have hk4 : k < 4 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by rw [← hk]; exact hlt)
  interval_cases k
  · exact seitzHyperGamma_eq_top_of_plane h2 hp hp2 hZ d e hpd
      (not_d2Exc d e (hex.imp_right And.left) hL34) hE hk
  · exact h3 p hp hp2 K (isSimpleGroup_of_center_eq_bot hq hZ) (exists_noncomm_of_quasisimple hq) d
      ⟨(equivCenterQuot hZ).trans e⟩ hpd
      (fun h => hL34 ⟨h.1, isLThreeFour_congr (equivCenterQuot hZ).symm h.2⟩) E hE hk hex

end Quasi

section Aut

variable {Y : Type} [Group Y]

@[expose] noncomputable def autIm (B K : Subgroup Y) : Subgroup (MulAut ↥K) :=
  (B.subgroupOf (Subgroup.normalizer (K : Set Y))).map K.normalizerMonoidHom

@[expose] noncomputable def autPre (B K : Subgroup Y) (F : Subgroup (MulAut ↥K)) : Subgroup Y :=
  ((B.subgroupOf (Subgroup.normalizer (K : Set Y))) ⊓ F.comap K.normalizerMonoidHom).map
    (Subgroup.normalizer (K : Set Y)).subtype

theorem autPre_le (B K : Subgroup Y) (F : Subgroup (MulAut ↥K)) : autPre B K F ≤ B := by
  rintro _ ⟨n, ⟨hn, -⟩, rfl⟩
  exact Subgroup.mem_subgroupOf.1 hn

theorem isElemAbelian_autIm {p : ℕ} {B : Subgroup Y} (hB : IsElemAbelian p B) (K : Subgroup Y) :
    IsElemAbelian p (autIm B K) :=
  CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hB _) _

theorem mem_centralizer_autPre {B K : Subgroup Y} {F : Subgroup (MulAut ↥K)} {k : ↥K}
    (hk : k ∈ fixedPoints F) : (k : Y) ∈ Subgroup.centralizer (autPre B K F : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨n, ⟨-, hnF⟩, rfl⟩
  have h1 : K.normalizerMonoidHom n k = k := (mem_fixedPoints.1 hk) _ hnF
  have h2 : ((K.normalizerMonoidHom n k : ↥K) : Y) = (n : Y) * k * (n : Y)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe K n k
  rw [h1] at h2
  show (n : Y) * k = k * n
  calc (n : Y) * k = (n : Y) * k * (n : Y)⁻¹ * n := by group
    _ = k * n := by rw [← h2]

theorem ker_inf_eq_bot {B K : Subgroup Y} (hBC : B ⊓ Subgroup.centralizer (K : Set Y) = ⊥) :
    K.normalizerMonoidHom.ker ⊓ B.subgroupOf (Subgroup.normalizer (K : Set Y)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.normalizerMonoidHom_ker] at hx1
  have h : (x : Y) ∈ B ⊓ Subgroup.centralizer (K : Set Y) :=
    ⟨Subgroup.mem_subgroupOf.1 hx2, Subgroup.mem_subgroupOf.1 hx1⟩
  rw [hBC, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem card_map_of_ker_inf {G H : Type*} [Group G] [Group H] (φ : G →* H) (A : Subgroup G)
    (h : φ.ker ⊓ A = ⊥) : Nat.card (A.map φ) = Nat.card A := by
  have h1 := Subgroup.relIndex_mul_card φ.ker A
  rw [h, Subgroup.card_bot, mul_one, Subgroup.relIndex_ker] at h1
  exact h1

theorem card_autIm {B K : Subgroup Y} (hBN : B ≤ Subgroup.normalizer (K : Set Y))
    (hBC : B ⊓ Subgroup.centralizer (K : Set Y) = ⊥) : Nat.card (autIm B K) = Nat.card B := by
  unfold autIm
  rw [card_map_of_ker_inf _ _ (ker_inf_eq_bot hBC)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv

theorem card_autPre {B K : Subgroup Y} (hBC : B ⊓ Subgroup.centralizer (K : Set Y) = ⊥)
    {F : Subgroup (MulAut ↥K)} (hF : F ≤ autIm B K) : Nat.card (autPre B K F) = Nat.card F := by
  unfold autPre
  rw [Subgroup.card_map_of_injective (Subgroup.normalizer (K : Set Y)).subtype_injective]
  set H := B.subgroupOf (Subgroup.normalizer (K : Set Y)) ⊓ F.comap K.normalizerMonoidHom with hH
  have hmap : H.map K.normalizerMonoidHom = F := by
    apply le_antisymm
    · rintro _ ⟨a, ⟨-, ha⟩, rfl⟩
      exact ha
    · intro f hf
      obtain ⟨a, ha, rfl⟩ := hF hf
      exact ⟨a, ⟨ha, hf⟩, rfl⟩
  have hker : K.normalizerMonoidHom.ker ⊓ H = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ inf_le_left).trans (ker_inf_eq_bot hBC).le)
  rw [← card_map_of_ker_inf _ _ hker, hmap]

theorem le_centGenI_of_autIm {p : ℕ} {B K : Subgroup Y} (hBN : B ≤ Subgroup.normalizer (K : Set Y))
    (hBC : B ⊓ Subgroup.centralizer (K : Set Y) = ⊥) (h : seitzHyperGamma p (autIm B K) = ⊤) :
    K ≤ centGenI p B K := by
  have key : (seitzHyperGamma p (autIm B K)).map K.subtype ≤ centGenI p B K := by
    unfold seitzHyperGamma
    rw [Subgroup.map_iSup]
    refine iSup_le fun F => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hF => ?_
    have hcard : Nat.card B ≤ p * Nat.card (autPre B K F) := by
      rw [card_autPre hBC hF.1]
      have h1 := Subgroup.relIndex_mul_card F (autIm B K)
      rw [inf_of_le_left hF.1, hF.2, card_autIm hBN hBC] at h1
      exact le_of_eq h1.symm
    refine le_trans ?_ (le_centGenI (autPre_le B K F) hcard)
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k.2, mem_centralizer_autPre hk⟩
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥K) ∈ seitzHyperGamma p (autIm B K) := by rw [h]; exact Subgroup.mem_top _
  exact key ⟨⟨x, hx⟩, hx', rfl⟩

variable [Finite Y]

theorem two_le_pRank_of_card {p : ℕ} (hp : p.Prime) {A : Subgroup Y} (hA : IsElemAbelian p A)
    (h : p ^ 2 ≤ Nat.card A) : 2 ≤ CFSG.Open.pRank p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hA
  have h2 : 2 ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [← hj]; exact h)
  exact h2.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hA hj)

theorem le_glbCore_of_centGenI {p : ℕ} (hp : p.Prime) {B E K : Subgroup Y} (hEB : E ≤ B)
    (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E) (h : K ≤ centGenI p E K) :
    K ≤ GLBCore p 2 B := by
  refine h.trans (iSup_le fun A => ?_)
  obtain ⟨hAE, hAc⟩ := A.2
  have hAel : IsElemAbelian p A.1 := elem_mono hE hAE
  have hA2 : p ^ 2 ≤ Nat.card A.1 := by
    have h1 : p * p ^ 2 ≤ p * Nat.card A.1 := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card E := hE3
        _ ≤ p * Nat.card A.1 := hAc
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore (hAE.trans hEB) (two_le_pRank_of_card hp hAel hA2)))

theorem le_glbCore_of_centGenI_central {p : ℕ} (hp : p.Prime) {B E C K : Subgroup Y}
    (hB : IsElemAbelian p B) (hEB : E ≤ B) (hCB : C ≤ B)
    (hCK : C ≤ Subgroup.centralizer (K : Set Y)) (hEC : E ⊓ C = ⊥) (hC : C ≠ ⊥)
    (hE2 : p ^ 2 ≤ Nat.card E) (h : K ≤ centGenI p E K) : K ≤ GLBCore p 2 B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hCel : IsElemAbelian p C := elem_mono hB hCB
  have hCp : p ≤ Nat.card C := by
    obtain ⟨c, hc⟩ := GL83.CompFam.exists_card_eq_pow hCel
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, pow_zero] at hc
      exact absurd (Subgroup.eq_bot_of_card_eq C hc) hC
    · rw [hc]
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ c := Nat.pow_le_pow_right hp.pos h0
  refine h.trans (iSup_le fun A => ?_)
  obtain ⟨hAE, hAc⟩ := A.2
  have hAC : A.1 ⊓ C = ⊥ := le_bot_iff.1 (hEC ▸ inf_le_inf_right C hAE)
  have hcomm : ∀ x ∈ A.1, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    elem_comm hB (hEB (hAE hx)) (hCB hy)
  have hDB : A.1 ⊔ C ≤ B := sup_le (hAE.trans hEB) hCB
  have hAp : p ≤ Nat.card A.1 := by
    have h1 : p * p ≤ p * Nat.card A.1 := by
      calc p * p = p ^ 2 := by ring
        _ ≤ Nat.card E := hE2
        _ ≤ p * Nat.card A.1 := hAc
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hD2 : p ^ 2 ≤ Nat.card (A.1 ⊔ C : Subgroup Y) := by
    rw [card_sup_of_commute_of_inf_eq_bot hcomm hAC, pow_two]
    exact Nat.mul_le_mul hAp hCp
  have hle : K ⊓ Subgroup.centralizer (A.1 : Set Y) ≤
      Subgroup.centralizer ((A.1 ⊔ C : Subgroup Y) : Set Y) := by
    rintro x ⟨hxK, hxA⟩
    have hsub : A.1 ⊔ C ≤ Subgroup.centralizer ({x} : Set Y) := by
      refine sup_le (fun a ha => ?_) (fun c hc => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxA a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          ((Subgroup.mem_centralizer_iff.1 (hCK hc) x hxK).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsub hg)
  exact hle.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore hDB (two_le_pRank_of_card hp (elem_mono hB hDB) hD2)))

theorem pow_succ_mul_le {p : ℕ} (hp : p.Prime) {B K : Subgroup Y} (hB : IsElemAbelian p B) {a : ℕ}
    (h : p ^ a * Nat.card (cen B K) < Nat.card (stab B K)) :
    p ^ (a + 1) * Nat.card (cen B K) ≤ Nat.card (stab B K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ : ∃ s, Nat.card (stab B K) = p ^ s :=
    GL83.CompFam.exists_card_eq_pow (elem_mono hB inf_le_left)
  obtain ⟨c, hc⟩ : ∃ c, Nat.card (cen B K) = p ^ c :=
    GL83.CompFam.exists_card_eq_pow (elem_mono hB inf_le_left)
  rw [hs, hc, ← pow_add] at h ⊢
  have h1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem exists_faithful {p : ℕ} (hp : p.Prime) {B K : Subgroup Y} (hB : IsElemAbelian p B) {k : ℕ}
    (hk : p ^ k * Nat.card (cen B K) ≤ Nat.card (stab B K)) :
    ∃ E : Subgroup Y, E ≤ stab B K ∧ E ⊓ Subgroup.centralizer (K : Set Y) = ⊥ ∧ Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNel : IsElemAbelian p (stab B K) := elem_mono hB inf_le_left
  obtain ⟨B₁, hB₁N, hB₁C, hB₁sup⟩ := InputsSeitz.exists_complement_elem hp hNel (cen_le_stab B K)
  have hcomm : ∀ x ∈ B₁, ∀ y ∈ cen B K, x * y = y * x := fun x hx y hy =>
    elem_comm hNel (hB₁N hx) (cen_le_stab B K hy)
  have hcard : Nat.card (stab B K) = Nat.card B₁ * Nat.card (cen B K) := by
    rw [← card_sup_of_commute_of_inf_eq_bot hcomm hB₁C, hB₁sup]
  have hle : p ^ k ≤ Nat.card B₁ := by
    rw [hcard] at hk
    exact Nat.le_of_mul_le_mul_right hk Nat.card_pos
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow (elem_mono hNel hB₁N)
  have hkj : k ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [← hj]; exact hle)
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ k ∣ Nat.card B₁ by rw [hj]; exact pow_dvd_pow p hkj)
  refine ⟨E₀.map B₁.subtype, (Subgroup.map_subtype_le E₀).trans hB₁N, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxE, hxC⟩
    have hxB₁ : x ∈ B₁ := Subgroup.map_subtype_le E₀ hxE
    have hx : x ∈ B₁ ⊓ cen B K := ⟨hxB₁, (hB₁N hxB₁).1, hxC⟩
    rwa [hB₁C] at hx
  · rw [Subgroup.card_map_of_injective B₁.subtype_injective, hE₀]

end Aut

theorem input23_10Faith_of_seitz (h2 : KFactSeitzRankTwo) (h3 : Seitz2310CubeSimple)
    (hR : SeitzQuasiHigh) : InputsSeitz.Input23_10Faith := by
  intro p q hp hp5 hq hqp Y _ _ _ K B hK hB hBN hBC hcard _ hlie hexc
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hdq⟩ := hlie
  have hdq' : d.1.characteristic = q := hdq
  have hpd : p ≠ d.1.characteristic := fun h => hqp (hdq'.symm.trans h.symm)
  have hex : ¬ ExcIndex p d.1 := by
    intro h
    obtain ⟨hp5', hd1⟩ := excIndex_ge_five hp5 h
    apply hexc hp5'
    obtain ⟨e⟩ := hd
    rcases hd1 with h1 | h1 | h1
    · exact Or.inl ⟨d, h1, ⟨e⟩⟩
    · exact Or.inr (Or.inr ⟨d, h1, ⟨e⟩⟩)
    · exact Or.inr (Or.inl ⟨d, h1, ⟨e⟩⟩)
  have hE2 : p ^ 2 ≤ Nat.card (autIm B K) := by
    rw [card_autIm hBN hBC]
    obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hB
    rw [hk] at hcard ⊢
    have hk1 : 1 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by rwa [pow_one])
    exact Nat.pow_le_pow_right hp.pos hk1
  have hgen := seitzHyperGamma_eq_top_of_seitz h2 h3 hR hp (by omega) hK.2.2 d hd hpd
    (fun h => absurd h.1 (by omega)) (isElemAbelian_autIm hB K) hE2 (Or.inl hex)
  refine InputsSeitz.isGMinusOne_of_centGenI hp hB hK ?_
  rw [show stab B K = B from inf_eq_left.2 hBN]
  exact le_centGenI_of_autIm hBN hBC hgen

@[expose] def Input23_19ChevExc : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian p B → 4 ≤ CFSG.Open.pRank p B →
      CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧
        CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (↥K ⧸ Subgroup.center ↥K)) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) →
      p ^ (CFSG.Open.pRank p B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        (p = d.1.characteristic ∨
          (ExcIndex p d.1 ∧ ¬ (p = 5 ∧ d.1 = .tits) ∧
            (Subgroup.center ↥K ≠ ⊥ ∨ B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∨
              IsD2SeitzException p d.1))) →
        K ≤ GLBCore p 2 B

theorem input23_19ChevExc_of_core (h : InputsSeitz.Input23_19ChevCore) : Input23_19ChevExc :=
  fun X _ _ hKX p hp hp2 hcore B hB hB4 hrk K hK hch haut _ _ _ _ =>
    h X hKX p hp hp2 hcore B hB hB4 hrk K hK hch haut

section ChevCore

set_option linter.unusedSectionVars false


theorem pRank_five_mulAut_le_two_of_tits {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut K)) ≤ 2 :=
  (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (quotientCenterAut' K)
    (quotientCenterAut'_injective hperf)).trans (CFSG.AGLEmbedding.pRank_five_mulAut_tits d hd e)

theorem input23_19ChevCore_of_seitz (h2 : KFactSeitzRankTwo)
    (h3 : Seitz2310CubeSimple) (hR : SeitzQuasiHigh) (hX : Input23_19ChevExc) :
    InputsSeitz.Input23_19ChevCore := by
  intro X _ _ hKX p hp hp2 hcore B hB hB4 hrk K hK hch haut
  haveI : Fact p.Prime := ⟨hp⟩
  have hBcard : Nat.card B = p ^ CFSG.Open.pRank p B := GL83.PiGen.card_eq_pow_pRank hB
  by_cases hsmall : Nat.card (stab B K) ≤ p ^ (CFSG.Open.pRank p B - 2) * Nat.card (cen B K)
  · exact InputsSeitz.le_glbCore_of_card_stab_le hp hB hK 2 (CFSG.Open.pRank p B - 2) (by omega)
      (by rw [hBcard]; exact Nat.pow_le_pow_right hp.pos (by omega)) hsmall
  push Not at hsmall
  have htype : (∃ n, IsAltType n (↥K ⧸ Subgroup.center ↥K)) ∨
      ∃ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) := by
    obtain ⟨q, -, -, hc⟩ := hch
    rcases hc with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
      · simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
      · simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
      · exact Or.inr ⟨d, ⟨e⟩⟩
      · simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
    · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · exact Or.inl ⟨n, ⟨e⟩⟩
      · exact Or.inr ⟨d, ⟨e⟩⟩
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
  rcases htype with ⟨n, hA⟩ | ⟨d, hd⟩
  · exact InputsSeitz.le_glbCore_of_alt hp hp2 hB hB4 hrk hK hA
  by_cases hpd : p = d.1.characteristic
  · exact hX X hKX p hp hp2 hcore B hB hB4 hrk K hK hch haut hsmall d hd (Or.inl hpd)
  obtain ⟨e⟩ := hd
  have h3le : p ^ 3 * Nat.card (cen B K) ≤ Nat.card (stab B K) :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))).trans
      (pow_succ_mul_le hp hB hsmall)
  have hL34 : ¬ (p = 3 ∧ IsLThreeFour (↥K ⧸ Subgroup.center ↥K)) := by
    rintro ⟨rfl, h⟩
    have h1 := pRank_mulAut_le_two_of_l34 hK.2.2.1 h
    omega
  by_cases hgood : ¬ ExcIndex p d.1
  · obtain ⟨E, hEN, hEC, hEcard⟩ := exists_faithful hp hB h3le
    have hEB : E ≤ B := hEN.trans inf_le_left
    have hENK : E ≤ Subgroup.normalizer (K : Set X) := hEN.trans inf_le_right
    have hEel : IsElemAbelian p E := elem_mono hB hEB
    have hgen := seitzHyperGamma_eq_top_of_seitz h2 h3 hR hp hp2 hK.2.2 d ⟨e⟩ hpd hL34
      (isElemAbelian_autIm hEel K)
      (by rw [card_autIm hENK hEC, hEcard]; exact Nat.pow_le_pow_right hp.pos (by norm_num))
      (Or.inl hgood)
    exact le_glbCore_of_centGenI hp hEB hEel hEcard.ge (le_centGenI_of_autIm hENK hEC hgen)
  have hexc : ExcIndex p d.1 := not_not.1 hgood
  by_cases hroute : Subgroup.center ↥K = ⊥ ∧ cen B K ≠ ⊥ ∧ ¬ IsD2SeitzException p d.1
  · obtain ⟨hZ, hC1, hnd⟩ := hroute
    obtain ⟨E₂, hE₂N, hE₂C, hE₂card⟩ := exists_faithful hp hB (k := 2)
      ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by norm_num))).trans h3le)
    have hE₂B : E₂ ≤ B := hE₂N.trans inf_le_left
    have hE₂NK : E₂ ≤ Subgroup.normalizer (K : Set X) := hE₂N.trans inf_le_right
    have hE₂el : IsElemAbelian p E₂ := elem_mono hB hE₂B
    have hgen := seitzHyperGamma_eq_top_of_plane h2 hp hp2 hZ d e hpd hnd
      (isElemAbelian_autIm hE₂el K) (by rw [card_autIm hE₂NK hE₂C, hE₂card])
    have hE₂cen : E₂ ⊓ cen B K = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left _ (inf_le_right : cen B K ≤ _)).trans hE₂C.le)
    exact le_glbCore_of_centGenI_central hp hB hE₂B inf_le_left inf_le_right hE₂cen hC1 hE₂card.ge
      (le_centGenI_of_autIm hE₂NK hE₂C hgen)
  have htits : ¬ (p = 5 ∧ d.1 = .tits) := by
    rintro ⟨rfl, hd⟩
    have h1 := pRank_five_mulAut_le_two_of_tits hK.2.2.1 d hd e
    omega
  refine hX X hKX p hp hp2 hcore B hB hB4 hrk K hK hch haut hsmall d ⟨e⟩ (Or.inr ⟨hexc, htits, ?_⟩)
  by_cases hZ : Subgroup.center ↥K = ⊥
  · by_cases hC1 : cen B K = ⊥
    · exact Or.inr (Or.inl hC1)
    · exact Or.inr (Or.inr (by by_contra hnd; exact hroute ⟨hZ, hC1, hnd⟩))
  · exact Or.inl hZ

end ChevCore

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

@[expose] def Rank3CuResExc : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          ((∃ n : ℕ, IsAltType n (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc))) ∨
            ∃ i : TauCeti.ValidLieTypeIndex,
              Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
              i.1.characteristic ≠ 3 ∧
              ExcIndex 3 i.1 ∧
              (Subgroup.center (barOf 3 Kc) ≠ ⊥ ∨
                barX 3 (Cg u) B ⊓
                  Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
                    Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) = ⊥ ∨
                IsD2SeitzException 3 i.1)) →
          Kc ≤ M

theorem rank3CuResExc_of_rank3CuRes (h : Claims1310.Rank3CuRes) : Rank3CuResExc := by
  intro G _ _ m p B M E A D T R L0 d hc h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal _
  exact h hc h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal

theorem rank3CuRes_of_seitz (h2 : KFactSeitzRankTwo) (h3 : Seitz2310CubeSimple) (hR : SeitzQuasiHigh)
    (hX : Rank3CuResExc) : Claims1310.Rank3CuRes := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
  have h139b' := h139b
  have hgood0 := hgood
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hS : GLStanding G m 3 := h.standing
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hBm : CFSG.Open.pRank 3 B = m := Claims1310.pRank_B_eq h
  have hB4 : 4 ≤ CFSG.Open.pRank 3 B := hBm ▸ hS.four_le
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  rcases hgood with hAlt | ⟨q, hq3, hL⟩ | hA2
  · exact hX h h139b' hU u hu hu1 hlt Kc hKc hgood0 hN haut hcen hpi hbal (Or.inl hAlt)
  swap
  · exfalso
    have h1 := InputsSeitz.pRank_top_le_of_forall hp hA2
    omega
  obtain ⟨i, ⟨e⟩, hiq⟩ := hL
  have hiq' : i.1.characteristic = q := hiq
  have hi3 : i.1.characteristic ≠ 3 := hiq' ▸ hq3
  have hpi3 : 3 ≠ i.1.characteristic := fun h => hi3 h.symm
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hqK : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg u) Kc) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eK.symm (Lemma1313.isQuasisimple_barOf_of_pComp hKc)
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group :=
    (Lemma1315b.centerQuotEquiv eK.symm).trans e
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  have hstab : stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = barX 3 (Cg u) B := inf_eq_left.2 hBtN
  have hcen3 : Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 := by
    obtain ⟨c, hc⟩ : ∃ c, Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) = 3 ^ c :=
      GL83.CompFam.exists_card_eq_pow (elem_mono hBtel inf_le_left)
    have hcr : c ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl (elem_mono hBtel inf_le_left) hc).trans hcen
    rw [hc]
    calc 3 ^ c ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hcr
      _ = 3 := by norm_num
  have h3le : 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤
      Nat.card (stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) := by
    rw [hstab, GL83.PiGen.card_eq_pow_pRank hBtel, hBtrk]
    calc 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 ^ 3 * 3 :=
          Nat.mul_le_mul_left _ hcen3
      _ = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hB4
  have hL34b : ¬ IsLThreeFour (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc)) := fun h => by
    have h1 := pRank_mulAut_le_two_of_l34 (Lemma1313.isQuasisimple_barOf_of_pComp hKc).1 h
    omega
  by_cases hgood' : ¬ ExcIndex 3 i.1
  · obtain ⟨Ee, hEN, hEC, hEcard⟩ := exists_faithful hp hBtel h3le
    have hEB : Ee ≤ barX 3 (Cg u) B := hEN.trans inf_le_left
    have hENK := hEN.trans inf_le_right
    have hEel : IsElemAbelian 3 Ee := elem_mono hBtel hEB
    have hL34 : ¬ (3 = 3 ∧
        IsLThreeFour (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc))) :=
      fun h => hL34b (isLThreeFour_congr (Lemma1315b.centerQuotEquiv eK) h.2)
    have hgen := seitzHyperGamma_eq_top_of_seitz h2 h3 hR hp (by norm_num) hqK i ⟨eZ⟩ hpi3 hL34
      (isElemAbelian_autIm hEel _) (by rw [card_autIm hENK hEC, hEcard]; norm_num) (Or.inl hgood')
    exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
      (le_glbCore_of_centGenI hp hEB hEel hEcard.ge (le_centGenI_of_autIm hENK hEC hgen))
  have hexc : ExcIndex 3 i.1 := not_not.1 hgood'
  by_cases hroute : Subgroup.center (barOf 3 Kc) = ⊥ ∧
      cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≠ ⊥ ∧ ¬ IsD2SeitzException 3 i.1
  · obtain ⟨hZ, hC1, hnd⟩ := hroute
    have hZt : Subgroup.center ↥(barX 3 (Cg u) Kc) = ⊥ := by
      rw [← Subgroup.map_center_eq eK, hZ, Subgroup.map_bot]
    obtain ⟨E₂, hE₂N, hE₂C, hE₂card⟩ := exists_faithful hp hBtel (k := 2)
      ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by norm_num))).trans h3le)
    have hE₂B : E₂ ≤ barX 3 (Cg u) B := hE₂N.trans inf_le_left
    have hE₂NK := hE₂N.trans inf_le_right
    have hE₂el : IsElemAbelian 3 E₂ := elem_mono hBtel hE₂B
    have hgen := seitzHyperGamma_eq_top_of_plane h2 hp (by norm_num) hZt i eZ hpi3 hnd
      (isElemAbelian_autIm hE₂el _) (by rw [card_autIm hE₂NK hE₂C, hE₂card])
    have hE₂cen : E₂ ⊓ cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left _ (inf_le_right :
        cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤ _)).trans hE₂C.le)
    exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
      (le_glbCore_of_centGenI_central hp hBtel hE₂B inf_le_left inf_le_right hE₂cen hC1 hE₂card.ge
        (le_centGenI_of_autIm hE₂NK hE₂C hgen))
  refine hX h h139b' hU u hu hu1 hlt Kc hKc hgood0 hN haut hcen hpi hbal
    (Or.inr ⟨i, ⟨e⟩, hi3, hexc, ?_⟩)
  by_cases hZ : Subgroup.center (barOf 3 Kc) = ⊥
  · by_cases hC1 : cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = ⊥
    · exact Or.inr (Or.inl hC1)
    · exact Or.inr (Or.inr (by by_contra hnd; exact hroute ⟨hZ, hC1, hnd⟩))
  · exact Or.inl hZ

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3

end
