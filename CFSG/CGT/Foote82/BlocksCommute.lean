module

public import CFSG.CGT.Foote82.BlockBasics
import CFSG.CGT.PushingUpLit.BlocksCommuteSchur
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFooteBlocks

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_quotAction {S P : Type*} [Group S] [Group P] (N : Subgroup P) [N.Normal]
    (σ : S →* MulAut P) (h : ∀ s x, x ∈ N ↔ σ s x ∈ N) :
    ∃ σ' : S →* MulAut (P ⧸ N), ∀ s x, σ' s (QuotientGroup.mk x) = QuotientGroup.mk (σ s x) := by
  have hmap : ∀ s, N.map (σ s : P ≃* P).toMonoidHom = N := by
    intro s
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h s x).1 hx
    · intro hy
      refine ⟨(σ s).symm y, ?_, by simp⟩
      exact (h s _).2 (by simpa using hy)
  refine ⟨{ toFun := fun s => QuotientGroup.congr N N (σ s) (hmap s)
            map_one' := ?_
            map_mul' := ?_ }, fun s x => rfl⟩
  · refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      show (↑((σ 1) x) : P ⧸ N) = ↑x
      rw [map_one]; rfl
  · intro s s'
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      show (↑((σ (s * s')) x) : P ⧸ N) = ↑((σ s) ((σ s') x))
      rw [map_mul]; rfl

theorem commutator_mem_of_schur {U Z A B : Subgroup G}
    (hZU : Z ≤ U)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) (hBZ : B ≤ Subgroup.normalizer (Z : Set G))
    (hab : ∀ u ∈ U, ∀ v ∈ U, ⁅u, v⁆ ∈ Z) (hlt : Z < U)
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ U → A ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = U)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, ∀ u ∈ U, ⁅⁅a, b⁆, u⁆ ∈ Z)
    (hperf : ⁅B, B⁆ = B) :
    ∀ b ∈ B, ∀ u ∈ U, ⁅b, u⁆ ∈ Z := by
  classical
  let N : Subgroup U := Z.subgroupOf U
  have hmemN : ∀ x : U, x ∈ N ↔ (x : G) ∈ Z := fun x => Iff.rfl
  have hNn : N.Normal := ⟨fun z hz u => by
    rw [hmemN] at hz ⊢
    have e : ((u * z * u⁻¹ : U) : G) = ⁅(u : G), (z : G)⁆ * z := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact Z.mul_mem (hab _ u.2 _ z.2) hz⟩
  haveI : N.Normal := hNn
  have hPc : ∀ x y : U ⧸ N, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H u =>
      induction y using QuotientGroup.induction_on with
      | H v =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmemN]
        have e : (((u * v)⁻¹ * (v * u) : U) : G) = ⁅(v : G)⁻¹, (u : G)⁻¹⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [e]
        exact hab _ (U.inv_mem v.2) _ (U.inv_mem u.2)
  letI : CommGroup (U ⧸ N) := { (inferInstance : Group (U ⧸ N)) with mul_comm := hPc }
  let σ₀ : A →* MulAut U := (Subgroup.normalizerMonoidHom U).comp (Subgroup.inclusion hAU)
  let τ₀ : B →* MulAut U := (Subgroup.normalizerMonoidHom U).comp (Subgroup.inclusion hBU)
  have hσ₀ : ∀ (a : A) (x : U), ((σ₀ a x : U) : G) = a * x * (a : G)⁻¹ :=
    fun a x => Subgroup.normalizerMonoidHom_apply_apply_coe U _ x
  have hτ₀ : ∀ (b : B) (x : U), ((τ₀ b x : U) : G) = b * x * (b : G)⁻¹ :=
    fun b x => Subgroup.normalizerMonoidHom_apply_apply_coe U _ x
  have hσN : ∀ (a : A) (x : U), x ∈ N ↔ σ₀ a x ∈ N := by
    intro a x
    rw [hmemN, hmemN, hσ₀]
    exact Subgroup.mem_normalizer_iff.1 (hAZ a.2) x
  have hτN : ∀ (b : B) (x : U), x ∈ N ↔ τ₀ b x ∈ N := by
    intro b x
    rw [hmemN, hmemN, hτ₀]
    exact Subgroup.mem_normalizer_iff.1 (hBZ b.2) x
  obtain ⟨σ, hσ⟩ := exists_quotAction N σ₀ hσN
  obtain ⟨τ, hτ⟩ := exists_quotAction N τ₀ hτN
  have hσ' : ∀ (s : A) (x : U ⧸ N),
      x ∈ (⊥ : Subgroup (U ⧸ N)) ↔ σ s x ∈ (⊥ : Subgroup (U ⧸ N)) := by
    intro s x
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    exact ⟨fun h => by rw [h, map_one], fun h => (σ s).injective (by rw [h, map_one])⟩
  have hτ' : ∀ (t : B) (x : U ⧸ N),
      x ∈ (⊥ : Subgroup (U ⧸ N)) ↔ τ t x ∈ (⊥ : Subgroup (U ⧸ N)) := by
    intro t x
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    exact ⟨fun h => by rw [h, map_one], fun h => (τ t).injective (by rw [h, map_one])⟩
  have hne : (⊥ : Subgroup (U ⧸ N)) ≠ ⊤ := by
    intro h
    obtain ⟨u, huU, huZ⟩ := (SetLike.lt_iff_le_and_exists.1 hlt).2
    have h1 : (QuotientGroup.mk (⟨u, huU⟩ : U) : U ⧸ N) ∈ (⊤ : Subgroup (U ⧸ N)) := trivial
    rw [← h, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hmemN] at h1
    exact huZ h1
  have hirr' : ∀ J' : Subgroup (U ⧸ N), (⊥ : Subgroup (U ⧸ N)) ≤ J' →
      (∀ s : A, ∀ x ∈ J', σ s x ∈ J') → J' = ⊥ ∨ J' = ⊤ := by
    intro J' _ hJ'
    let W : Subgroup G := (J'.comap (QuotientGroup.mk' N)).map U.subtype
    have hmemW : ∀ g : G, g ∈ W ↔ ∃ h : g ∈ U, (QuotientGroup.mk ⟨g, h⟩ : U ⧸ N) ∈ J' := by
      intro g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, hx⟩
      · rintro ⟨h, hJ⟩
        exact ⟨⟨g, h⟩, hJ, rfl⟩
    have hZW : Z ≤ W := fun z hz => (hmemW z).2 ⟨hZU hz, by
      have : (QuotientGroup.mk ⟨z, hZU hz⟩ : U ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff _).2 ((hmemN _).2 hz)
      rw [this]
      exact J'.one_mem⟩
    have hWU : W ≤ U := Subgroup.map_subtype_le _
    have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro a ha w hw
      obtain ⟨hwU, hwJ⟩ := (hmemW w).1 hw
      have hawU : a * w * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hAU ha) w).1 hwU
      refine (hmemW _).2 ⟨hawU, ?_⟩
      have h1 := hJ' ⟨a, ha⟩ _ hwJ
      rw [hσ] at h1
      have e : σ₀ ⟨a, ha⟩ ⟨w, hwU⟩ = ⟨a * w * a⁻¹, hawU⟩ := Subtype.ext (hσ₀ _ _)
      rwa [e] at h1
    rcases hirr W hZW hWU hAW with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      induction x using QuotientGroup.induction_on with
      | H u =>
        have hu : (u : G) ∈ W := (hmemW u).2 ⟨u.2, hx⟩
        rw [h] at hu
        rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, hmemN]
        exact hu
    · right
      rw [eq_top_iff]
      intro x _
      induction x using QuotientGroup.induction_on with
      | H u =>
        have hu : (u : G) ∈ W := by rw [h]; exact u.2
        exact ((hmemW u).1 hu).2
  have hcomm' : ∀ (s : A) (t : B) (x : U ⧸ N),
      σ s (τ t x) * (τ t (σ s x))⁻¹ ∈ (⊥ : Subgroup (U ⧸ N)) := by
    intro s t x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [Subgroup.mem_bot, hτ, hσ, hσ, hτ, mul_inv_eq_one, QuotientGroup.eq, hmemN]
      have hu' : (t : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (t : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.1 (hBU t.2) _).1
          ((Subgroup.mem_normalizer_iff.1 (hAU s.2) _).1 u.2)
      have e : (((σ₀ s (τ₀ t u))⁻¹ * (τ₀ t (σ₀ s u)) : U) : G) =
          ⁅⁅(s : G), (t : G)⁆, ((t : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (t : G)⁻¹)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ₀, hτ₀, commutatorElement_def]
        group
      rw [e]
      exact hcomm _ s.2 _ t.2 _ (U.inv_mem hu')
  have hperf' : commutator ↥B = ⊤ := (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
  have key := CFSG.CGT.PushingUpLit.schur_trivial_of_perfect (⊥ : Subgroup (U ⧸ N)) σ τ hσ' hτ'
    hne hirr' hcomm' hperf'
  intro b hb u hu
  have h1 := key ⟨b, hb⟩ (QuotientGroup.mk ⟨u, hu⟩)
  rw [hτ, Subgroup.mem_bot, mul_inv_eq_one, QuotientGroup.eq_iff_div_mem, hmemN] at h1
  have e : (((τ₀ ⟨b, hb⟩ ⟨u, hu⟩) / ⟨u, hu⟩ : U) : G) = ⁅b, u⁆ := by
    rw [div_eq_mul_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ₀, commutatorElement_def]
  rw [e] at h1
  exact h1

private theorem isComponent_map_pCore {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hsn : L.IsSubnormal) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    CFSG.IsComponent (L.map (QuotientGroup.mk' (CFSG.pCore 2 Y))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 Y) with hπ
  set f : L →* Y ⧸ CFSG.pCore 2 Y := π.comp L.subtype with hf
  have hker : f.ker = CFSG.pCore 2 L := by
    apply le_antisymm
    · have h2 : IsPGroup 2 f.ker := by
        intro x
        have hx : ((x : L) : Y) ∈ CFSG.pCore 2 Y := by
          have : π ((x : L) : Y) = 1 := MonoidHom.mem_ker.mp x.2
          rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)) ⟨_, hx⟩
        exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
      exact le_sSup ⟨inferInstance, h2⟩
    · intro x hx
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact CFSG.CGT.PushingUpLit.oTwoIn_le_pCore hsn ⟨x, hx, rfl⟩
  have hrange : f.range = L.map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)) hq,
    hsn.map (QuotientGroup.mk'_surjective _)⟩

private theorem isComponent_of_isFooteBlock {H J : Subgroup G} (hJ : IsFooteBlock H J) :
    CFSG.IsComponent ((J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
  have hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
    ⟨⟨hJ.quasisimple.1⟩, hJ.quasisimple.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
        hJ.quasisimple⟩
  set e : J.subgroupOf H ≃* J := Subgroup.subgroupOfEquivOfLe hJ.le
  exact isComponent_map_pCore (CFSG.Open.IsSubnormal.subgroupOf hJ.subnormal)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (CFSG.pCore_map_iso 2 e.symm)) hq)

private theorem foote_dichotomy {H J K : Subgroup G} (hJ : IsFooteBlock H J)
    (hK : IsFooteBlock H K) :
    (J ≤ K ⊔ pCoreOf 2 H ∧ K ≤ J ⊔ pCoreOf 2 H) ∨ ∀ x ∈ J, ∀ y ∈ K, ⁅x, y⁆ ∈ pCoreOf 2 H := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hle : ∀ {A B : Subgroup G}, A ≤ H →
      (A.subgroupOf H).map π ≤ (B.subgroupOf H).map π → A ≤ B ⊔ pCoreOf 2 H := by
    intro A B hAH h x hx
    obtain ⟨y, hy, hyx⟩ := h (Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.2 hx : (⟨x, hAH hx⟩ : H) ∈ A.subgroupOf H))
    have hq : y⁻¹ * ⟨x, hAH hx⟩ ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.1 hyx
    have e : x = (y : G) * ((y⁻¹ * ⟨x, hAH hx⟩ : H) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hy) ⟨_, hq, rfl⟩
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_of_isFooteBlock hJ)
    (isComponent_of_isFooteBlock hK) with heq | hcomm
  · exact Or.inl ⟨hle hJ.le heq.le, hle hK.le heq.ge⟩
  · right
    intro x hx y hy
    have h1 : ⁅π ⟨x, hJ.le hx⟩, π ⟨y, hK.le hy⟩⁆ ∈
        ⁅(J.subgroupOf H).map π, (K.subgroupOf H).map π⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr hx)) (Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr hy))
    rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, by simp [commutatorElement_def]⟩

private theorem le_oTwoUpper_of_isFooteBlock {H J : Subgroup G} (hJ : IsFooteBlock H J) :
    J ≤ CFSG.Quasithin.oTwoUpper J :=
  CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.le_of_forall_odd_mem_of_twoResidual hJ.residual
    fun _ hx hxo => CFSG.Quasithin.mem_oTwoUpper_of_odd hx hxo

private theorem eq_oTwoUpper_sup {H K : Subgroup G} (hK : IsFooteBlock H K) :
    K = CFSG.Quasithin.oTwoUpper (K ⊔ pCoreOf 2 H) := by
  have hX : K = CFSG.Quasithin.oTwoUpper K :=
    le_antisymm (le_oTwoUpper_of_isFooteBlock hK) (CFSG.Quasithin.oTwoUpper_le K)
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hK.le.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  refine (CFSG.Quasithin.a4_2_2 hX hK.subnormal
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) ?_).1
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 H) K hKQ, sup_comm,
    Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H) hKQ]

private theorem le_of_le_sup_pCoreOf {H J K : Subgroup G} (hJ : IsFooteBlock H J)
    (hK : IsFooteBlock H K) (h : J ≤ K ⊔ pCoreOf 2 H) : J ≤ K :=
  calc J ≤ CFSG.Quasithin.oTwoUpper J := le_oTwoUpper_of_isFooteBlock hJ
    _ ≤ CFSG.Quasithin.oTwoUpper (K ⊔ pCoreOf 2 H) := CFSG.Quasithin.oTwoUpper_mono h
    _ = K := (eq_oTwoUpper_sup hK).symm

private theorem le_normalizer_of_commutator_mem {H J K : Subgroup G} (hJ : IsFooteBlock H J)
    (hK : IsFooteBlock H K) (h : ∀ x ∈ J, ∀ y ∈ K, ⁅x, y⁆ ∈ pCoreOf 2 H) :
    J ≤ Subgroup.normalizer (K : Set G) := by
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hconj : ∀ x ∈ J, ∀ z ∈ K ⊔ pCoreOf 2 H, x * z * x⁻¹ ∈ K ⊔ pCoreOf 2 H := by
    intro x hx
    have hle : K ⊔ pCoreOf 2 H ≤ (K ⊔ pCoreOf 2 H).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun q hq => ?_)
      · show x * y * x⁻¹ ∈ K ⊔ pCoreOf 2 H
        have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by simp [commutatorElement_def, mul_assoc]
        rw [e, sup_comm]
        exact Subgroup.mul_mem_sup (h x hx y hy) hy
      · show x * q * x⁻¹ ∈ K ⊔ pCoreOf 2 H
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hHQ (hJ.le hx)) q).1 hq)
    exact fun z hz => hle hz
  have key : ∀ x ∈ J, ∀ y ∈ K, x * y * x⁻¹ ∈ K := by
    intro x hx y hy
    have hxN : x ∈ Subgroup.normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨fun hz => hconj x hx z hz, fun hz => ?_⟩
      have := hconj x⁻¹ (inv_mem hx) _ hz
      simpa [mul_assoc] using this
    have hy' : y ∈ CFSG.Quasithin.oTwoUpper (K ⊔ pCoreOf 2 H) := by
      rw [← eq_oTwoUpper_sup hK]
      exact hy
    have := CFSG.Quasithin.conj_mem_oTwoUpper hxN hy'
    rwa [← eq_oTwoUpper_sup hK] at this
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key x hx g hg, fun hg => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hg
  simpa [mul_assoc] using this

private theorem inf_pCoreOf_le_blockQ {H K : Subgroup G} (hK : IsFooteBlock H K) :
    K ⊓ pCoreOf 2 H ≤ blockQ K := by
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hK.le.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le inf_le_right)
  exact (le_inf Subgroup.le_normalizer hKQ).trans Subgroup.inf_normalizer_le_normalizer_inf

omit [Finite G] in
private theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

omit [Finite G] in
private theorem mem_normalizer_centralizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ c ∈ Subgroup.centralizer (K : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) k).1 hk
      simpa using this
    have h1 := hc _ hk'
    calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * k := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨key g hg c, fun h => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ h⟩

omit [Finite G] in
private theorem mem_normalizer_blockU {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer (blockU K : Set G) :=
  mem_normalizer_commutator (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hg) hg

omit [Finite G] in
private theorem mem_normalizer_blockZ {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer (blockZ K : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨mem_normalizer_blockU hg, mem_normalizer_centralizer hg⟩

omit [Finite G] in
private theorem mem_normalizer_center {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hg, mem_normalizer_centralizer hg⟩

omit [Finite G] in
theorem three_subgroups_mod {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set K := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hmap : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf K, B.subgroupOf K⁆, C.subgroupOf K⁆).map K.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔
        ⁅⁅(A.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)),
          (B.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆,
          (C.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem blocks_commute {H J K : Subgroup G} (hJ : IsFooteBlock H J) (hK : IsFooteBlock H K)
    (hne : J ≠ K) : ⁅J, K⁆ = ⊥ := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hQH : pCoreOf 2 H ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hQK : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.le_normalizer_of_isSubnormal_of_twoResidual
      hK.subnormal hK.residual hQ2 hQH hHQ
  have hJKQ : ∀ x ∈ J, ∀ y ∈ K, ⁅x, y⁆ ∈ pCoreOf 2 H := by
    rcases foote_dichotomy hJ hK with ⟨h1, h2⟩ | h
    · exact absurd (le_antisymm (le_of_le_sup_pCoreOf hJ hK h1) (le_of_le_sup_pCoreOf hK hJ h2))
        hne
    · exact h
  have hJK : J ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_commutator_mem hJ hK hJKQ
  have hQKc : ⁅pCoreOf 2 H, K⁆ ≤ blockQ K :=
    (le_inf (Subgroup.le_normalizer_iff_commutator_le_right.1 hQK)
      (Subgroup.le_normalizer_iff_commutator_le_left.1 (hK.le.trans hHQ))).trans
        (inf_pCoreOf_le_blockQ hK)
  have hUQ : ⁅blockU K, pCoreOf 2 H⁆ ≤ blockZ K :=
    IsFooteBlock.commutator_blockU_le_blockZ hK hQ2 hQK hQKc
  have hJKc : ⁅J, K⁆ ≤ blockQ K :=
    (le_inf (Subgroup.le_normalizer_iff_commutator_le_right.1 hJK)
      (Subgroup.commutator_le.2 hJKQ)).trans (inf_pCoreOf_le_blockQ hK)
  have hKJU : ⁅K, J⁆ ≤ blockU K := IsFooteBlock.commutator_le_blockU hK hJK hJKc
  have hKU : K ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.normalizer_commutator_ge_right (blockQ K) K
  have hcomm : ∀ a ∈ K, ∀ b ∈ J, ∀ u ∈ blockU K, ⁅⁅a, b⁆, u⁆ ∈ blockZ K := by
    intro a ha b hb u hu
    have hab : ⁅a, b⁆ ∈ pCoreOf 2 H := by
      rw [← commutatorElement_inv]
      exact inv_mem (hJKQ b hb a ha)
    have h1 : ⁅u, ⁅a, b⁆⁆ ∈ blockZ K := hUQ (Subgroup.commutator_mem_commutator hu hab)
    rw [← commutatorElement_inv]
    exact inv_mem h1
  have hZ : ∀ b ∈ J, ∀ u ∈ blockU K, ⁅b, u⁆ ∈ blockZ K :=
    commutator_mem_of_schur (CFSG.RankThree.PartTwo.blockZ_le_blockU K) hKU
      (fun g hg => mem_normalizer_blockZ (Subgroup.le_normalizer hg))
      (fun g hg => mem_normalizer_blockU (hJK hg)) (fun g hg => mem_normalizer_blockZ (hJK hg))
      (fun u hu v hv => IsFooteBlock.commutator_mem_blockZ hK hu hv) hK.chief.1 hK.chief.2 hcomm
      (IsFooteBlock.commutator_eq hJ)
  have hKJ2 : ⁅⁅K, J⁆, J⁆ ≤ K ⊓ Subgroup.centralizer (K : Set G) := by
    refine ((Subgroup.commutator_mono hKJU le_rfl).trans ?_).trans
      (inf_le_inf_right _ (CFSG.RankThree.PartTwo.blockU_le_self K))
    refine Subgroup.commutator_le.2 fun u hu b hb => ?_
    rw [← commutatorElement_inv]
    exact inv_mem (hZ b hb u hu)
  have hJKN : ⁅J, K⁆ ≤ K ⊓ Subgroup.centralizer (K : Set G) := by
    have h := three_subgroups_mod (X := J) (Y := K) (Z := J)
      (N := K ⊓ Subgroup.centralizer (K : Set G))
      (fun g hg => mem_normalizer_center (hJK hg))
      (fun g hg => mem_normalizer_center (Subgroup.le_normalizer hg))
      (fun g hg => mem_normalizer_center (hJK hg))
      (by rw [Subgroup.commutator_comm J K]; exact hKJ2) hKJ2
    rwa [IsFooteBlock.commutator_eq hJ] at h
  have h3 : ⁅⁅J, K⁆, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hJKN.trans inf_le_right)
  have h1 : ⁅⁅K, J⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm K J]; exact h3
  have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h3
  rw [IsFooteBlock.commutator_eq hK, Subgroup.commutator_comm] at h4
  exact h4

end CFSG.CGT.Foote82
