module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PI
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open KFactsSmall
open scoped commutatorElement Pointwise

theorem dvd_card_normalClosure_of_mem_sigmaM_aux_gamma_gen {G : Type} [Group G] [Finite G]
    {M : Subgroup G} (hO1217 : O1217At G M) {q r : ℕ}
    (hq : q ∈ sigmaM G M) (hq5 : 5 ≤ q) (hr : r.Prime) (hr2 : r ≠ 2) {E P₀ : Subgroup ↥M}
    (hEa : IsElemAbelian r E) (hE : Nat.card E = r ^ 2)
    (hP₀rk : 2 ≤ CFSG.Open.pRank q P₀) {x : ↥M}
    (hx : ∀ e ∈ E, ∀ y ∈ P₀, y * (x * e * x⁻¹) = (x * e * x⁻¹) * y) :
    rankThreeGamma 1 r (E.map M.subtype) ≤ M := by
  have hqP : q.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1
  obtain ⟨E₀, hE₀le, hE₀a, hE₀c⟩ := CFSG.SectionRank.exists_pRank hqP.one_lt P₀
  set xG : G := (x : G) with hxG
  have hxM : xG ∈ M := x.2
  set E1 : Subgroup G := (E.map M.subtype).map (MulAut.conj xG).toMonoidHom with hE1
  set PG : Subgroup G := P₀.map M.subtype with hPG
  have hE1M : E1 ≤ M := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact M.mul_mem (M.mul_mem hxM e.2) (M.inv_mem hxM)
  have hE1a : IsElemAbelian r E1 :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hEa M.subtype) _
  have hE1c : Nat.card E1 = r ^ 2 := by
    rw [hE1, Subgroup.card_map_of_injective (MulAut.conj xG).injective,
      Subgroup.card_map_of_injective M.subtype_injective, hE]
  have hPGc : PG ≤ Subgroup.centralizer (E1 : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    have h1 := congrArg (fun w : ↥M => (w : G)) (hx e he y hy)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    simpa [MulAut.conj_apply] using h1.symm
  have hPGM : PG ≤ M := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hdvd : q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E1 : Set G)) := by
    have h1 : Nat.card PG ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E1 : Set G)) :=
      Subgroup.card_dvd_of_le (le_inf hPGM hPGc)
    have h2 : Nat.card PG = Nat.card P₀ := Subgroup.card_map_of_injective M.subtype_injective
    have h3 : q ∣ Nat.card P₀ := by
      refine dvd_trans ?_ (Subgroup.card_dvd_of_le hE₀le)
      rw [hE₀c]
      exact dvd_pow_self q (by omega)
    rw [h2] at h1
    exact h3.trans h1
  have hA : ∀ A : Subgroup G, A ≤ E1 → Nat.card A = r →
      2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G)) := by
    intro A hAE _
    have hPGA : PG ≤ Subgroup.centralizer (A : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.2 fun a ha =>
        Subgroup.mem_centralizer_iff.1 (hPGc hz) a (hAE ha)
    calc 2 ≤ CFSG.Open.pRank q P₀ := hP₀rk
      _ ≤ CFSG.Open.pRank q PG :=
        CFSG.SectionRank.pRank_le_map hqP.one_lt M.subtype M.subtype_injective P₀
      _ ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G)) :=
        CFSG.SectionRank.pRank_mono hqP.one_lt
          (le_inf hPGM (hPGA.trans (Subgroup.centralizer_le_normalizer _)))
  have hΓ : rankThreeGamma 1 r E1 ≤ M :=
    hO1217 q r hq hq5 hr hr2 E1 hE1M hE1a hE1c hdvd hA
  exact gamma_le_of_le_lift_aux_conj hxM hr hΓ

section L34Transport

variable {G : Type} [Group G] [Finite G]

theorem exists_L34Config_of_sylow_aux_isSylowOf_map {P K : Subgroup G} (ψ : G ≃* G) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P.map ψ.toMonoidHom) (K.map ψ.toMonoidHom) ↔
      CFSG.ABGLocalTools.IsSylowOf 2 P K := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff, CFSG.ABGLocalTools.isSylowOf_iff,
    Subgroup.map_le_map_iff_of_injective ψ.injective,
    Subgroup.relIndex_map_map_of_injective _ _ ψ.injective]
  constructor
  · rintro ⟨hle, hP, hdvd⟩
    exact ⟨hle, hP.of_equiv (P.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm, hdvd⟩
  · rintro ⟨hle, hP, hdvd⟩
    exact ⟨hle, hP.map ψ.toMonoidHom, hdvd⟩

theorem exists_L34Config_of_sylow_aux_quotEquiv {T R : Subgroup G} {Q : Type} [Group Q]
    (ψ : G ≃* G) (h : QuotEquiv T R Q) :
    QuotEquiv (T.map ψ.toMonoidHom) (R.map ψ.toMonoidHom) Q := by
  obtain ⟨hn, ⟨f⟩⟩ := h
  let e : ↥T ≃* ↥(T.map ψ.toMonoidHom) := ψ.subgroupMap T
  have hmap : (R.subgroupOf T).map e.toMonoidHom =
      (R.map ψ.toMonoidHom).subgroupOf (T.map ψ.toMonoidHom) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : G), ht, rfl⟩
    · intro hy
      obtain ⟨t, htT, hty⟩ := y.2
      refine ⟨⟨t, htT⟩, ?_, Subtype.ext hty⟩
      obtain ⟨r, hr, hrt⟩ := (hy : (y : G) ∈ R.map ψ.toMonoidHom)
      have : r = t := ψ.injective (hrt.trans hty.symm)
      subst this
      exact hr
  haveI : ((R.map ψ.toMonoidHom).subgroupOf (T.map ψ.toMonoidHom)).Normal :=
    hmap ▸ hn.map e.toMonoidHom e.surjective
  exact ⟨this, ⟨(QuotientGroup.congr (R.subgroupOf T) _ e hmap).symm.trans f⟩⟩

theorem exists_L34Config_of_sylow_aux_quaternion {A T : Subgroup G} (ψ : G ≃* G)
    (h : ∃ Q : Subgroup (MulAut ↥A),
      Q ≤ (T.subgroupOf (Subgroup.normalizer (A : Set G))).map A.normalizerMonoidHom ∧
        Nonempty (↥Q ≃* QuaternionGroup 2)) :
    ∃ Q : Subgroup (MulAut ↥(A.map ψ.toMonoidHom)),
      Q ≤ ((T.map ψ.toMonoidHom).subgroupOf
        (Subgroup.normalizer ((A.map ψ.toMonoidHom : Subgroup G) : Set G))).map
          (A.map ψ.toMonoidHom).normalizerMonoidHom ∧
        Nonempty (↥Q ≃* QuaternionGroup 2) := by
  obtain ⟨Q, hQle, ⟨e⟩⟩ := h
  let eA : ↥A ≃* ↥(A.map ψ.toMonoidHom) := ψ.subgroupMap A
  let Φ : MulAut ↥A ≃* MulAut ↥(A.map ψ.toMonoidHom) := MulAut.congr eA
  refine ⟨Q.map Φ.toMonoidHom, ?_,
    ⟨(Q.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans e⟩⟩
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨n, hn, rfl⟩ := hQle hq
  have hnT : (n : G) ∈ T := hn
  have hnN : ψ (n : G) ∈ Subgroup.normalizer ((A.map ψ.toMonoidHom : Subgroup G) : Set G) := by
    have : ψ (n : G) ∈ (Subgroup.normalizer (A : Set G)).map ψ.toMonoidHom := ⟨(n : G), n.2, rfl⟩
    rwa [Subgroup.map_normalizer_eq_of_bijective A ψ.bijective] at this
  refine ⟨⟨ψ (n : G), hnN⟩, ⟨(n : G), hnT, rfl⟩, ?_⟩
  ext ⟨a', a, ha, rfl⟩
  show ψ (n : G) * ψ a * (ψ (n : G))⁻¹ = ψ ((n : G) * ψ.symm (ψ a) * (n : G)⁻¹)
  simp

theorem exists_L34Config_of_sylow_aux_map_symm (ψ : G ≃* G) (K : Subgroup G) :
    (K.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => by simp
  rw [this, Subgroup.map_id]

theorem exists_L34Config_of_sylow_aux_maximal {A R : Subgroup G} (ψ : G ≃* G)
    (h : IsMaxInvariantTwo A R) :
    IsMaxInvariantTwo (A.map ψ.toMonoidHom) (R.map ψ.toMonoidHom) := by
  obtain ⟨hR, hAR, hmax⟩ := h
  refine ⟨hR.map ψ.toMonoidHom, ?_, ?_⟩
  · rw [← Subgroup.map_normalizer_eq_of_bijective R ψ.bijective]
    exact Subgroup.map_mono hAR
  · intro S hS hAS hRS
    have hS' : IsPGroup 2 (S.map ψ.symm.toMonoidHom) := hS.map ψ.symm.toMonoidHom
    have h1 : A ≤ Subgroup.normalizer ((S.map ψ.symm.toMonoidHom : Subgroup G) : Set G) := by
      rw [← Subgroup.map_normalizer_eq_of_bijective S ψ.symm.bijective]
      have := Subgroup.map_mono (f := ψ.symm.toMonoidHom) hAS
      rwa [exists_L34Config_of_sylow_aux_map_symm] at this
    have h2 : R ≤ S.map ψ.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := ψ.symm.toMonoidHom) hRS
      rwa [exists_L34Config_of_sylow_aux_map_symm] at this
    have h3 := hmax _ hS' h1 h2
    have h4 : (S.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = S := by
      have := exists_L34Config_of_sylow_aux_map_symm ψ.symm S
      rwa [MulEquiv.symm_symm] at this
    rw [← h4, h3]

theorem exists_L34Config_of_sylow_aux_perm {A T : Subgroup G} (ψ : G ≃* G)
    (h : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    ((A.map ψ.toMonoidHom : Subgroup G) : Set G) * ((T.map ψ.toMonoidHom : Subgroup G) : Set G) =
      ((T.map ψ.toMonoidHom : Subgroup G) : Set G) * ((A.map ψ.toMonoidHom : Subgroup G) : Set G) := by
  simp only [Subgroup.coe_map]
  rw [← Set.image_mul, ← Set.image_mul, h]

theorem exists_L34Config_of_sylow_aux_transitive {A T : Subgroup G} (ψ : G ≃* G)
    (h : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      ∃ t ∈ T ⊓ Subgroup.normalizer (A : Set G), t * a * t⁻¹ = b) :
    ∀ a ∈ A.map ψ.toMonoidHom, a ≠ 1 → ∀ b ∈ A.map ψ.toMonoidHom, b ≠ 1 →
      ∃ t ∈ T.map ψ.toMonoidHom ⊓
        Subgroup.normalizer ((A.map ψ.toMonoidHom : Subgroup G) : Set G), t * a * t⁻¹ = b := by
  rintro _ ⟨a, ha, rfl⟩ ha1 _ ⟨b, hb, rfl⟩ hb1
  obtain ⟨t, ⟨htT, htN⟩, hta⟩ := h a ha (fun h1 => ha1 (by simp [h1])) b hb
    (fun h1 => hb1 (by simp [h1]))
  refine ⟨ψ t, ⟨⟨t, htT, rfl⟩, ?_⟩, ?_⟩
  · rw [← Subgroup.map_normalizer_eq_of_bijective A ψ.bijective]
    exact ⟨t, htN, rfl⟩
  · show ψ t * ψ a * (ψ t)⁻¹ = ψ b
    rw [← map_inv, ← map_mul, ← map_mul, hta]

theorem exists_L34Config_of_sylow_aux_solvable {M R H' : Subgroup G} (ψ : G ≃* G)
    (hM : M.map ψ.toMonoidHom = M)
    (h : Group.IsSolvable ↥(H' ⊓ M ⊓ Subgroup.normalizer (R : Set G))) :
    Group.IsSolvable ↥(H'.map ψ.toMonoidHom ⊓ M ⊓
      Subgroup.normalizer ((R.map ψ.toMonoidHom : Subgroup G) : Set G)) := by
  have heq : H'.map ψ.toMonoidHom ⊓ M ⊓
      Subgroup.normalizer ((R.map ψ.toMonoidHom : Subgroup G) : Set G) =
        (H' ⊓ M ⊓ Subgroup.normalizer (R : Set G)).map ψ.toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ ψ.injective, Subgroup.map_inf _ _ _ ψ.injective, hM,
      Subgroup.map_normalizer_eq_of_bijective R ψ.bijective]
  rw [heq]
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((H' ⊓ M ⊓ Subgroup.normalizer (R : Set G)).equivMapOfInjective ψ.toMonoidHom
      ψ.injective).symm.toMonoidHom) (MulEquiv.injective _)

theorem exists_L34Config_of_sylow_aux_map {M A T₀ R H' : Subgroup G} (h : L34Config M A T₀ R H')
    (ψ : G ≃* G) (hM : M.map ψ.toMonoidHom = M) :
    L34Config M (A.map ψ.toMonoidHom) (T₀.map ψ.toMonoidHom) (R.map ψ.toMonoidHom)
      (H'.map ψ.toMonoidHom) where
  le_M := hM ▸ Subgroup.map_mono h.le_M
  elemAbelian := CFSG.SectionRank.isElemAbelian_map h.elemAbelian ψ.toMonoidHom
  card_eq := (Subgroup.card_map_of_injective ψ.injective).trans h.card_eq
  gamma := by
    have h1 : rankThreeGamma 1 3 (A.map ψ.toMonoidHom) = (rankThreeGamma 1 3 A).map ψ.toMonoidHom :=
      CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_equiv (p := 3) (k := 1) ψ A
    rw [h1]
    exact (Subgroup.map_mono h.gamma).trans_eq hM
  sylow := by
    have := (exists_L34Config_of_sylow_aux_isSylowOf_map ψ).2 h.sylow
    rwa [hM] at this
  not_sylow := fun hs => h.not_sylow ((exists_L34Config_of_sylow_aux_isSylowOf_map ψ).1 hs)
  perm := exists_L34Config_of_sylow_aux_perm ψ h.perm
  core := by
    rw [← Subgroup.map_sup, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 ψ, ← h.core]
  normalizer_le := by
    rw [← Subgroup.map_normalizer_eq_of_bijective R ψ.bijective]
    exact Subgroup.map_mono h.normalizer_le
  maximal := exists_L34Config_of_sylow_aux_maximal ψ h.maximal
  maxLocal := CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map h.maxLocal ψ
  le_H := Subgroup.map_mono h.le_H
  not_le_M := fun hle =>
    h.not_le_M ((Subgroup.map_le_map_iff_of_injective ψ.injective).1 (hle.trans_eq hM.symm))
  solvable := exists_L34Config_of_sylow_aux_solvable ψ hM h.solvable
  quotient := h.quotient.imp (exists_L34Config_of_sylow_aux_quotEquiv ψ)
    (exists_L34Config_of_sylow_aux_quotEquiv ψ)
  quaternion := exists_L34Config_of_sylow_aux_quaternion ψ h.quaternion
  transitive := exists_L34Config_of_sylow_aux_transitive ψ h.transitive

end L34Transport

theorem exists_L34Config_of_sylow {G : Type} [Group G] [Finite G] {M T T₀ A R H' : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (h : L34Config M A T₀ R H') :
    ∃ A₁ R₁ H₁ : Subgroup G, L34Config M A₁ T R₁ H₁ := by
  obtain ⟨m, hm, hmT⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj h.sylow hT
  have hTeq : T = T₀.map (MulAut.conj m).toMonoidHom := by
    ext x
    rw [hmT x, gamma_le_of_le_lift_aux_mem_map_conj]
  have hM : M.map (MulAut.conj m).toMonoidHom = M := by
    ext x
    rw [gamma_le_of_le_lift_aux_mem_map_conj]
    constructor
    · intro hx
      have := M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm)
      simpa [mul_assoc] using this
    · intro hx
      exact M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm
  subst hTeq
  exact ⟨_, _, _, exists_L34Config_of_sylow_aux_map h (MulAut.conj m) hM⟩

theorem dvd_card_normalClosure_of_mem_sigmaM_aux_Ti_gen {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hne : L ≠ Subgroup.normalClosure (L : Set ↥M)) {Ti : Subgroup ↥M} (hTi : Ti = T₁ ∨ Ti = T₂)
    (hE9 : ∃ E : Subgroup ↥M, E ≤ Subgroup.normalClosure (L : Set ↥M) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ E ≤ Subgroup.normalizer (Ti : Set ↥M))
    {p : ℕ} (hp : p ∈ sigmaM G M)
    (hZ : ¬ p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M)) →
      ∃ P₀ : Subgroup ↥M, IsPGroup p P₀ ∧ 2 ≤ CFSG.Open.pRank p P₀ ∧
        ∀ y ∈ P₀, ∀ j ∈ Subgroup.normalClosure (L : Set ↥M), ⁅y, j⁆ ∈ CFSG.pCore 2 ↥M) :
    p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M)) := by
  by_contra hpJ
  set J : Subgroup ↥M := Subgroup.normalClosure (L : Set ↥M) with hJ
  have hqP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp3 : p ≠ 3 := fun h => h11 (h ▸ hp)
  have hp5 : 5 ≤ p := by
    have h2 := hqP.two_le
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hqP
    exact absurd hqP (by norm_num)
  obtain ⟨P₀, hP₀p, hP₀rk, hP₀c⟩ := hZ hpJ
  obtain ⟨E, hEJ, hEa, hEc, hEN⟩ := hE9
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hEc]; norm_num)
  have hN2 : IsPGroup 2 (O2In J) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).to_le inf_le_right
  have hNL : O2In J ≤ J := inf_le_left
  have hJn : J.Normal := Subgroup.normalClosure_normal
  have hconj : ∀ l ∈ J, ∀ n ∈ O2In J, l * n * l⁻¹ ∈ O2In J := fun l hl n hn =>
    ⟨J.mul_mem (J.mul_mem hl (hNL hn)) (J.inv_mem hl),
      (inferInstance : (CFSG.pCore 2 ↥M).Normal).conj_mem n hn.2 l⟩
  have hLN : J ≤ Subgroup.normalizer (O2In J : Set ↥M) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hconj l hl n, fun h => ?_⟩
    have h1 := hconj l⁻¹ (J.inv_mem hl) _ h
    simpa [mul_assoc] using h1
  have hcomm : ∀ y ∈ P₀, ∀ l ∈ J, y * l * y⁻¹ * l⁻¹ ∈ O2In J := fun y hy l hl =>
    ⟨J.mul_mem (hJn.conj_mem l hl y) (J.inv_mem hl), hP₀c y hy l hl⟩
  obtain ⟨x, -, hx⟩ := exists_conj_centralized_aux_main hqP hp2 Nat.prime_three (by norm_num) hN2
    hNL hLN hEp hEJ hP₀p hcomm
  have hΓ : rankThreeGamma 1 3 (E.map M.subtype) ≤ M :=
    dvd_card_normalClosure_of_mem_sigmaM_aux_gamma_gen hO1217 hp hp5 Nat.prime_three
      (by norm_num) hEa (by rw [hEc]; norm_num) hP₀rk hx
  have hne1 : Ti ≠ ⊥ := by
    rcases hTi with rfl | rfl
    · exact ctx.pair.ne_bot₁
    · exact ctx.pair.ne_bot₂
  have hle : Ti ≤ T.subgroupOf M := by
    rcases hTi with rfl | rfl
    · exact ctx.pair.le_center.trans (omegaOneCenterOf_le_subgroup _)
    · exact ctx.pair.le₂
  have hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic := by
    rcases hTi with rfl | rfl
    · exact ctx.pair.char₁
    · exact ctx.pair.char₂
  obtain ⟨H₀, hH₀max, hH₀le, hH₀ne⟩ :=
    exists_maxTwoLocal_normalizer_gen ctx.sylow.le ctx.sylow.isPGroup ctx.notLe hne1 hle hchar
  have hEH : E.map M.subtype ≤ H₀ :=
    (Subgroup.map_mono hEN).trans ((map_subtype_normalizer_le Ti).trans hH₀le)
  have hEM : E.map M.subtype ≤ M := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hEab : IsElemAbelian 3 (E.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hEa M.subtype
  have hEcard : Nat.card (E.map M.subtype) = 9 := by
    rw [← hEc]
    exact Nat.card_congr (E.equivMapOfInjective M.subtype M.subtype_injective).toEquiv.symm
  obtain ⟨A₀, T₀, R₀, H', hcfg⟩ :=
    hO1521 h11 (E.map M.subtype) hEM hEab hEcard hΓ H₀ hH₀max hEH hH₀ne
  obtain ⟨A₁, R₁, H₁, hcfg'⟩ := exists_L34Config_of_sylow ctx.sylow hcfg
  obtain ⟨hLn, -, -⟩ := h21 A₁ R₁ H₁ hcfg' Ls L hLs hL
  exact hne (Subgroup.normalClosure_eq_self L).symm

theorem dvd_card_normalClosure_of_mem_sigmaM_aux_gen {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hne : L ≠ Subgroup.normalClosure (L : Set ↥M))
    (hE9 : ∃ E : Subgroup ↥M, E ≤ Subgroup.normalClosure (L : Set ↥M) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ E ≤ Subgroup.normalizer (T₁ : Set ↥M))
    {p : ℕ} (hp : p ∈ sigmaM G M)
    (hZ : ¬ p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M)) →
      ∃ P₀ : Subgroup ↥M, IsPGroup p P₀ ∧ 2 ≤ CFSG.Open.pRank p P₀ ∧
        ∀ y ∈ P₀, ∀ j ∈ Subgroup.normalClosure (L : Set ↥M), ⁅y, j⁆ ∈ CFSG.pCore 2 ↥M) :
    p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M)) :=
  dvd_card_normalClosure_of_mem_sigmaM_aux_Ti_gen hO1217 hO1521 ctx h11 h21 hLs hL hne
    (Or.inl rfl) hE9 hp hZ

section SigmaDvd

variable {X : Type} [Group X] [Finite X]

theorem sigmaM_eq_five_aux_dvd_barO2 {J : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ Nat.card J) : p ∣ Nat.card ↥(barO2 J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  have hy : orderOf (x : X) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hne : QuotientGroup.mk' (CFSG.pCore 2 X) (x : X) ≠ 1 := by
    intro h1
    have hmem : (x : X) ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨(x : X), hmem⟩
    have h2 : orderOf (x : X) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [hy] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) (x : X)) = p := by
    have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) (x : X)) ∣ p :=
      hy ▸ orderOf_map_dvd _ (x : X)
    rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hne
    · exact h2
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 X) (x : X) ∈ barO2 J := ⟨(x : X), x.2, rfl⟩
  have h3 := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥(barO2 J))
  rw [Subgroup.orderOf_mk, hord] at h3
  exact h3

end SigmaDvd

theorem sigmaM_eq_five_aux_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    {J : Subgroup ↥M} (hcp : IsCentralProdA6Z3 ↥(barO2 J))
    (hdvd : ∀ p ∈ sigmaM G M, p ∣ Nat.card J) :
    sigmaM G M = {5} := by
  have key : ∀ p ∈ sigmaM G M, p = 5 := by
    intro p hp
    have hqP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
    have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
    have hp3 : p ≠ 3 := fun h => h11 (h ▸ hp)
    have h1 : p ∣ Nat.card ↥(barO2 J) := sigmaM_eq_five_aux_dvd_barO2 hqP hp2 (hdvd p hp)
    obtain ⟨K₁, K₂, hK₁, hK₂, hsup, hcomm, -, -⟩ := hcp
    have hcomm' : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.1 (hcomm hx) y hy).symm
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ hcomm'
    rw [hsup, Subgroup.card_top] at hcard
    have h2 : p ∣ Nat.card K₁ * Nat.card K₂ := h1.trans (Dvd.intro _ hcard)
    rcases (Nat.Prime.dvd_mul hqP).1 h2 with h | h
    · rcases primes_of_isAltSixCoverThree hK₁ hqP h with h' | h' | h'
      · exact absurd h' hp2
      · exact absurd h' hp3
      · exact h'
    · rcases primes_of_isAltSixCoverThree hK₂ hqP h with h' | h' | h'
      · exact absurd h' hp2
      · exact absurd h' hp3
      · exact h'
  ext p
  constructor
  · intro hp
    exact key p hp
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    obtain ⟨q, hq⟩ := ctx.p_mem
    rwa [key q hq] at hq

section SevenDvd

variable {X : Type} [Group X] [Finite X]

theorem sigmaM_eq_seven_aux_card_sup (S : Finset (Subgroup X)) (hS : ∀ K ∈ S, IsC2 K) :
    Nat.card ↥(barO2 (S.sup id)) ∣ ∏ K ∈ S, Nat.card ↥(barO2 K) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert L S' hLS ih =>
    have hL : IsC2 L := hS L (Finset.mem_insert_self _ _)
    have hS' : ∀ K ∈ S', IsC2 K := fun K hK => hS K (Finset.mem_insert_of_mem hK)
    have ih' := ih hS'
    have hc : ∀ a ∈ barO2 L, ∀ b ∈ barO2 (S'.sup id), a * b = b * a := by
      intro a ha b hb
      have hBle : S'.sup id ≤ (Subgroup.centralizer ({a} : Set (X ⧸ CFSG.pCore 2 X))).comap
          (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
        refine Finset.sup_le (fun K hK => ?_)
        have hne : L ≠ K := fun h => hLS (h ▸ hK)
        have hcomm := isC2_commute_of_ne hL (hS' K hK) hne
        have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
        intro y hy
        have h2 := (Subgroup.mem_centralizer_iff.1 h1) (QuotientGroup.mk' _ y)
          (Subgroup.mem_map_of_mem _ hy)
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact h2.symm
      obtain ⟨y, hy, rfl⟩ := hb
      have := hBle hy
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
      exact this a rfl
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (barO2 L)
      (barO2 (S'.sup id)) hc
    have e : barO2 (L ⊔ S'.sup id) = barO2 L ⊔ barO2 (S'.sup id) := Subgroup.map_sup _ _ _
    rw [Finset.prod_insert hLS, Finset.sup_insert]
    show Nat.card ↥(barO2 (L ⊔ S'.sup id)) ∣ _
    rw [e]
    exact (Dvd.intro _ hcard).trans (mul_dvd_mul_left _ ih')

theorem sigmaM_eq_seven_aux_dvd {L : Subgroup X} (hL : IsC2 L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ Nat.card (Subgroup.normalClosure (L : Set X))) : p ∣ Nat.card ↥(barO2 L) := by
  classical
  set T : Set (Subgroup X) :=
    {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} with hT
  have hfin : T.Finite := Set.toFinite _
  set S : Finset (Subgroup X) := hfin.toFinset with hS
  have hmemS : ∀ K, K ∈ S ↔ K ∈ T := fun K => hfin.mem_toFinset
  have hCS : ∀ K ∈ S, IsC2 K := fun K hK => ((hmemS K).1 hK).1
  have hconj : ∀ K ∈ S, ∃ x : X, K = L.map (MulAut.conj x).toMonoidHom := fun K hK =>
    isC2_le_normalClosure_conj hL ((hmemS K).1 hK).1 ((hmemS K).1 hK).2
  have hsup : S.sup id = Subgroup.normalClosure (L : Set X) := by
    apply le_antisymm
    · exact Finset.sup_le (fun K hK => ((hmemS K).1 hK).2)
    · rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro bb hbb
      obtain ⟨c, hc, hconj'⟩ := Group.mem_conjugatesOfSet_iff.1 hbb
      obtain ⟨d, rfl⟩ := isConj_iff.1 hconj'
      have hK : L.map (MulAut.conj d).toMonoidHom ∈ S := by
        rw [hmemS]
        refine ⟨liftOf_conj_aux4 hL d, ?_⟩
        rintro _ ⟨e, he, rfl⟩
        exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem e
          (Subgroup.le_normalClosure he) d
      have hbbmem : d * c * d⁻¹ ∈ L.map (MulAut.conj d).toMonoidHom :=
        ⟨c, hc, by simp [MulAut.conj_apply]⟩
      exact (Finset.le_sup (f := id) hK) hbbmem
  have h1 := sigmaM_eq_five_aux_dvd_barO2 hp hp2 h
  have h2 := sigmaM_eq_seven_aux_card_sup S hCS
  rw [hsup] at h2
  obtain ⟨K, hK, hpK⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 (h1.trans h2)
  obtain ⟨x, rfl⟩ := hconj K hK
  rw [barO2_map_conj, Subgroup.card_map_of_injective (MulAut.conj _).injective] at hpK
  exact hpK

end SevenDvd

theorem sigmaM_eq_seven_aux_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    {L : Subgroup ↥M} (hL : IsC2 L) (hL3 : IsLThreeOfExp 1 ↥(barO2 L))
    (hdvd : ∀ p ∈ sigmaM G M, p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M))) :
    sigmaM G M = {7} := by
  have key : ∀ p ∈ sigmaM G M, p = 7 := by
    intro p hp
    have hqP : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
    have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
    have hp3 : p ≠ 3 := fun h => h11 (h ▸ hp)
    rcases primes_of_isLThreeOfExp_one hL3 hqP (sigmaM_eq_seven_aux_dvd hL hqP hp2 (hdvd p hp)) with
      h' | h' | h'
    · exact absurd h' hp2
    · exact absurd h' hp3
    · exact h'
  ext p
  constructor
  · intro hp
    exact key p hp
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    obtain ⟨q, hq⟩ := ctx.p_mem
    rwa [key q hq] at hq

end CFSG.LocalAnalysis.RankThreeUC.S15
