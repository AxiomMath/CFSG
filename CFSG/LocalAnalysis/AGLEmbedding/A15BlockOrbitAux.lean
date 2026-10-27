module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizerAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

section General

variable {Y : Type*} [Group Y] [Finite Y]

theorem coprime_card_inf_centralizer_of_pCore_eq_bot {p : ℕ} [Fact p.Prime]
    (hY : CFSG.pCore p Y = ⊥) {K : Subgroup Y} (hK : IsSubnormal K ⊤) :
    Nat.Coprime p (Nat.card (K ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y)) := by
  have hp : p.Prime := Fact.out
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzo : orderOf (z : Y) = p := by rw [Subgroup.orderOf_coe, hz]
  have hW : IsSubnormal (Subgroup.zpowers (z : Y)) ⊤ :=
    isSubnormal_of_le_inf_centralizer hK ((Subgroup.zpowers_le).mpr z.2)
  have hzp : IsPGroup p (Subgroup.zpowers (z : Y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hzo, pow_one]
  have h1 := cfsg_subnormal_pCoreOf_le p hW
  rw [pCoreOf_top_eq_pCore, hY] at h1
  have h4 : Subgroup.zpowers (z : Y) ≤ pCoreOf p (Subgroup.zpowers (z : Y)) :=
    normal_pGroup_le_pCoreOf p _ _ le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) hzp
  have hbot := le_bot_iff.mp (h4.trans h1)
  have hz1 : (z : Y) = 1 := by
    have : (z : Y) ∈ Subgroup.zpowers (z : Y) := Subgroup.mem_zpowers _
    rwa [hbot, Subgroup.mem_bot] at this
  rw [hz1, orderOf_one] at hzo
  exact hp.one_lt.ne hzo

omit [Finite Y] in
private theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup Y}
    (hB : B ≤ Subgroup.normalizer (A : Set Y)) :
    Nat.card (A ⊔ B : Subgroup Y) * Nat.card (A ⊓ B : Subgroup Y) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set Y)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ X : Subgroup Y, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N)
    (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

omit [Finite Y] in
theorem coprime_card_sup_of_le_normalizer {p : ℕ} {A B : Subgroup Y}
    (hB : B ≤ Subgroup.normalizer (A : Set Y)) (hA : Nat.Coprime p (Nat.card A))
    (hB' : Nat.Coprime p (Nat.card B)) : Nat.Coprime p (Nat.card (A ⊔ B : Subgroup Y)) :=
  Nat.Coprime.coprime_dvd_right (Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer hB))
    (Nat.Coprime.mul_right hA hB')

theorem false_of_card_sup_five {P₀ P₁ T : Subgroup Y} (hcard : Nat.card P₁ = Nat.card P₀)
    (hN : P₁ ≤ Subgroup.normalizer (P₀ : Set Y))
    (hcop : Nat.Coprime 5 (Nat.card (P₀ ⊓ P₁ : Subgroup Y))) (hT : T ≤ P₀ ⊔ P₁)
    (hT3 : Nat.card T = 5 ^ 3)
    (hsyl : ∀ n : ℕ, 5 ^ n ∣ Nat.card (P₀ ⊔ P₁ : Subgroup Y) → n ≤ 3) : False := by
  have h := card_sup_mul_card_inf_of_le_normalizer hN
  obtain ⟨a, m, hm, hP⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := P₀)).ne' 5 (by norm_num)
  rw [hcard, hP] at h
  have hm5 : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm
  have hprod : Nat.card (P₀ ⊔ P₁ : Subgroup Y) * Nat.card (P₀ ⊓ P₁ : Subgroup Y) =
      5 ^ (2 * a) * (m * m) := by
    rw [h]
    ring
  have h1 : 5 ^ (2 * a) ∣ Nat.card (P₀ ⊔ P₁ : Subgroup Y) :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ hcop) ⟨m * m, hprod⟩
  have h2 : 5 ^ 3 ∣ 5 ^ (2 * a) := by
    have h3 : 5 ^ 3 ∣ 5 ^ (2 * a) * (m * m) :=
      ((hT3 ▸ Subgroup.card_dvd_of_le hT).trans (Dvd.intro _ rfl)).trans hprod.dvd
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 3 (hm5.mul_right hm5)) h3
  have h4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have h5 := hsyl _ h1
  omega

omit [Finite Y] in
private theorem zpowers_inf_eq_bot_of_not_mem {p : ℕ} (hp : p.Prime) {D : Subgroup Y} {w : Y}
    (hw : orderOf w = p) (hwD : w ∉ D) : Subgroup.zpowers w ⊓ D = ⊥ := by
  have : Finite (Subgroup.zpowers w) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zpowers, hw]
    exact hp.ne_zero
  have hdvd : Nat.card (Subgroup.zpowers w ⊓ D : Subgroup Y) ∣ p := by
    rw [← hw, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · have heq : Subgroup.zpowers w ⊓ D = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, Nat.card_zpowers, hw])
    have hle : Subgroup.zpowers w ≤ D := by
      rw [← heq]
      exact inf_le_right
    exact (hwD (hle (Subgroup.mem_zpowers w))).elim

omit [Finite Y] in
private theorem isElemAbelian_zpowers_of_orderOf {p : ℕ} {w : Y} (hw : orderOf w = p) :
    IsElemAbelian p (Subgroup.zpowers w) := by
  refine ⟨inferInstance, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hw, pow_orderOf_eq_one,
    one_zpow]

omit [Finite Y] in
private theorem isElemAbelian_sup_of_le_centralizer {p : ℕ} {A B : Subgroup Y}
    (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hAB : A ≤ Subgroup.centralizer (B : Set Y)) : IsElemAbelian p (A ⊔ B) := by
  have hAA : A ≤ Subgroup.centralizer (A : Set Y) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1
  have hBB : B ≤ Subgroup.centralizer (B : Set Y) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hB.1
  have hBA : B ≤ Subgroup.centralizer (A : Set Y) := Subgroup.le_centralizer_iff.mp hAB
  refine ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp (sup_le ?_ ?_), fun x hx => ?_⟩
  · exact Subgroup.le_centralizer_iff.mp (sup_le hAA hBA)
  · exact Subgroup.le_centralizer_iff.mp (sup_le hAB hBB)
  · have hx' : x ∈ ((A : Set Y) * (B : Set Y)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B
        (hAB.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hc : Commute a b := (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb).symm
    rw [hc.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem four_le_pRank_of_commuting_triple {A B C E : Subgroup Y} {y z : Y}
    (hAB : A ≤ Subgroup.centralizer (B : Set Y)) (hAC : A ≤ Subgroup.centralizer (C : Set Y))
    (hBC : B ≤ Subgroup.centralizer (C : Set Y)) (hEA : E ≤ A) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2) (hyB : y ∈ B) (hy : orderOf y = 3)
    (hyC : y ∉ Subgroup.centralizer (B : Set Y)) (hzC : z ∈ C) (hz : orderOf z = 3)
    (hzC' : z ∉ Subgroup.centralizer (C : Set Y)) : 4 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  have hyB' : Subgroup.zpowers y ≤ B := (Subgroup.zpowers_le).mpr hyB
  have hzC'' : Subgroup.zpowers z ≤ C := (Subgroup.zpowers_le).mpr hzC
  have hEy : E ≤ Subgroup.centralizer (Subgroup.zpowers y : Set Y) :=
    hEA.trans (hAB.trans (Subgroup.centralizer_le hyB'))
  have hyE : Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set Y) :=
    (Subgroup.le_centralizer_iff.mp hEy).trans (Subgroup.centralizer_le_normalizer _)
  have hEy0 : E ⊓ Subgroup.zpowers y = ⊥ := by
    rw [inf_comm, eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem Nat.prime_three hy hyC]
    exact inf_le_inf_left _ (hEA.trans hAB)
  set F := E ⊔ Subgroup.zpowers y with hF
  have hF27 : Nat.card F = 3 ^ 3 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hyE
    rw [hEy0, Subgroup.card_bot, mul_one, hE9, Nat.card_zpowers, hy] at h1
    rw [hF, h1]
    norm_num
  have hFel : IsElemAbelian 3 F :=
    isElemAbelian_sup_of_le_centralizer hE (isElemAbelian_zpowers_of_orderOf hy) hEy
  have hFC : F ≤ Subgroup.centralizer (C : Set Y) := sup_le (hEA.trans hAC) (hyB'.trans hBC)
  have hFz : F ≤ Subgroup.centralizer (Subgroup.zpowers z : Set Y) :=
    hFC.trans (Subgroup.centralizer_le hzC'')
  have hzF : Subgroup.zpowers z ≤ Subgroup.normalizer (F : Set Y) :=
    (Subgroup.le_centralizer_iff.mp hFz).trans (Subgroup.centralizer_le_normalizer _)
  have hFz0 : F ⊓ Subgroup.zpowers z = ⊥ := by
    rw [inf_comm, eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem Nat.prime_three hz hzC']
    exact inf_le_inf_left _ hFC
  have h81 : Nat.card (F ⊔ Subgroup.zpowers z : Subgroup Y) = 3 ^ 4 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hzF
    rw [hFz0, Subgroup.card_bot, mul_one, hF27, Nat.card_zpowers, hz] at h1
    rw [h1]
    norm_num
  exact le_csSup (pRank_bddAbove 3 Nat.prime_three ⊤) ⟨_, le_top,
    isElemAbelian_sup_of_le_centralizer hFel (isElemAbelian_zpowers_of_orderOf hz) hFz, h81⟩

end General

section Lifts

variable {G : Type} [Group G]

theorem card_eq_sixty_of_barM {M K₀ N : Subgroup G} {P O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hsec : ∀ L : Subgroup G, L ≤ K₀ → ∀ (V : Subgroup L) [V.Normal], N.subgroupOf L ≤ V →
      IsSimpleGroup (L ⧸ V) → (∃ a b : L ⧸ V, a * b ≠ b * a) → Nat.card (L ⧸ V) = 60)
    (hK₀ : ∀ U ≤ P, (U.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ K₀)
    (hO : ∀ x : M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) x ∈ P → (x : G) ∈ N →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) x ∈ O)
    (U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hU : U ≤ P) (V : Subgroup U) [V.Normal]
    (hOV : O.subgroupOf U ≤ V) (hsimple : IsSimpleGroup (U ⧸ V))
    (hnc : ∃ a b : U ⧸ V, a * b ≠ b * a) : Nat.card (U ⧸ V) = 60 := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Uh : Subgroup G := (U.comap mk).map M.subtype with hUh
  have hUhM : Uh ≤ M := Subgroup.map_subtype_le _
  let ψ : ↥Uh →* ↥M ⧸ CFSG.pCore 2 ↥M := mk.comp (Subgroup.inclusion hUhM)
  have hψ : ∀ x, ψ x ∈ U := by
    rintro ⟨_, m, hm, rfl⟩
    exact hm
  let θ : ↥Uh →* ↥U ⧸ V := (QuotientGroup.mk' V).comp (ψ.codRestrict U hψ)
  have hθ : Function.Surjective θ := by
    refine (QuotientGroup.mk'_surjective V).comp ?_
    rintro ⟨u, hu⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) u
    exact ⟨⟨m, m, hu, rfl⟩, rfl⟩
  let e : ↥Uh ⧸ θ.ker ≃* ↥U ⧸ V := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  have hNθ : N.subgroupOf Uh ≤ θ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr (hOV (Subgroup.mem_subgroupOf.mpr
      (hO _ (hU (hψ x)) (Subgroup.mem_subgroupOf.mp hx))))
  have : IsSimpleGroup (↥U ⧸ V) := hsimple
  have : Nontrivial (↥Uh ⧸ θ.ker) := e.toEquiv.nontrivial
  have hnc' : ∃ a b : ↥Uh ⧸ θ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  rw [← Nat.card_congr e.toEquiv]
  exact hsec Uh (hK₀ U hU) θ.ker hNθ
    (IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective) hnc'

theorem exists_surjective_range_mk {A : Type*} [Group A] {M J N : Subgroup G} (hJM : J ≤ M)
    (hQN : pCoreOf 2 M ≤ N) {O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hO : ∀ x : J, QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hJM x) ∈ O ↔
      (x : G) ∈ N)
    {φ : J →* A} (hφs : Function.Surjective φ) (hφ : ∀ x, φ x = 1 ↔ (x : G) ∈ N) :
    ∃ φ' : ↥((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hJM)).range →* A,
      Function.Surjective φ' ∧ ∀ z, φ' z = 1 ↔ (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ O := by
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hJM) with hf
  have hker : f.rangeRestrict.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : f x = 1 := congrArg Subtype.val hx
    exact (hφ x).mpr (hQN (coe_mem_pCoreOf_two_of_mk_eq_one _ h1))
  set φ' := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨φ, hker⟩
  have hcomp : ∀ x, φ' (f.rangeRestrict x) = φ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hker⟩ x
  refine ⟨φ', fun a => ?_, fun z => ?_⟩
  · obtain ⟨x, rfl⟩ := hφs a
    exact ⟨_, hcomp x⟩
  · obtain ⟨x, rfl⟩ := f.rangeRestrict_surjective z
    rw [hcomp, hφ, MonoidHom.coe_rangeRestrict]
    exact (hO x).symm

end Lifts

section Blocks

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.mk_mem_blockPL_sup {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hb : StmtBlockInnerNormalizer) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hC : C ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) {x : M}
    (hxK : (x : G) ∈ H ⊓ M) (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) x ∈ barM M L ⊔ C) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) x ∈ blockPL M (pCoreOf 2 H) L ⊔ C :=
  h.toTwoLocalPhaseThree.mk_mem_blockPL_sup h.isKGroup.1 h86 hL (hb h h84 h86 hD2 hL) hC hxK hx

theorem barM_le_centralizer_of_ne {M L L' : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hL' : IsTwoPrimeComponent M L') (hne : L ≠ L') :
    barM M L ≤ Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.component hL'.component
      fun he => hne (hL.eq_of_barM_eq hL' he))

theorem D1PhaseThree.card_blockPL_map_conj {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) {L : Subgroup G} {k : G} (hk : k ∈ H ⊓ M) :
    Nat.card (blockPL M (pCoreOf 2 H) (L.map (MulAut.conj k).toMonoidHom)) =
      Nat.card (blockPL M (pCoreOf 2 H) L) :=
  h.toD1Escape.toTwoLocalPair.card_blockPL_map_conj hk

end Blocks

end CFSG.AGLEmbedding
