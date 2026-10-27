module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KDChev
public import CFSG.LocalAnalysis.GLTheoremA.S6.I183Diag
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsInterface
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.S3.KDAmbSolv
public import CFSG.LocalAnalysis.GLTheoremA.PartI.U42
import CFSG.HardMathSupport.Solomon.Coordinator.B2SmallSimple
import CFSG.Quasithin.Background.SzG11G94Solv
public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieQ
public import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p q : ℕ}

@[expose] def KDChevDownQ (p q : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple q S → ∀ α : MulAut S, α ^ p = 1 →
      ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I → IsChevSimple q (PSimple p I)

theorem kdChevDownQ_self_iff (p : ℕ) : KDChevDownQ p p ↔ KDChevDown p := Iff.rfl

theorem chevQ_step (hp : p.Prime) (hD : KDChevDownQ p q) {X K : Subgroup G}
    (hK : GLAPComponent p X K) (hchev : IsChevSimple q (PSimple p K)) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : a ^ p = 1) {L : Subgroup G}
    (hL : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L) :
    IsChevSimple q (PSimple p L) := by
  obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian hp hK
  have hap' : IsPGroup p (Subgroup.zpowers a) := isPGroup_zpowers_of_pow_eq_one hap
  have hα : chevAut p K ⟨a, ha⟩ ^ p = 1 := chevAut_pow_eq_one p K ha hap
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp ha hap' hL
  exact chev_isChevSimple_of_mulEquiv e
    (hD (PSimple p K) hsimple hnonab hchev _ hα _ (glaPComponent_chevTransfer hp ha hap' hL))


section Diagonal

open CFSG.HardMathSupport.Solomon.Coordinator (b3Lie_isQuasisimple_of_simple b3Lie_center_eq_bot)

theorem glaPPrimeCore_pSimple_eq_bot (hp : p.Prime) {X C : Subgroup G}
    (hC : GLAPComponent p X C) : GLAPPrimeCore p (PSimple p C) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTs, -⟩ := chev_pSimple_simple_nonabelian hp hC
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hC
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p (PSimple p C)) with h | h
  · exact h
  · exfalso
    haveI : Group.IsPerfect (PQuot p C) := ⟨hq.1⟩
    have h1 : ¬ p ∣ Nat.card (PQuot p C ⧸ Subgroup.center (PQuot p C)) := by
      have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p (PSimple p C))) :=
        CFSG.pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at hcop
      exact (hp.coprime_iff_not_dvd).1 hcop
    have h2 : ¬ p ∣ Nat.card (PQuot p C) :=
      CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp h1
    have hbot : GLAPPrimeCore p (PQuot p C) = ⊥ :=
      CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥C) p
    have hle : (⊤ : Subgroup (PQuot p C)) ≤ GLAPPrimeCore p (PQuot p C) := by
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [Subgroup.card_top]
      exact (hp.coprime_iff_not_dvd).2 h2
    rw [hbot, top_le_iff] at hle
    haveI := isQuasisimple_nontrivial hq
    exact absurd hle.symm ((Subgroup.nontrivial_iff_ne_bot _).1 inferInstance)

private theorem chevQ_conj_mem_centMod {L : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hc : c ∈ centModSubgroup p L) :
    g * c * g⁻¹ ∈ centModSubgroup p L := by
  obtain ⟨hcN, hcJ⟩ := hc
  refine ⟨?_, fun l hl => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcN) (Subgroup.inv_mem _ hg)
  · have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) l).1 hl
      simpa using this
    have h1 := hcJ _ hl'
    have h2 : g * ⁅g⁻¹ * l * g, c⁆ * g⁻¹ ∈ GLAPPrimeCoreOf p L :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hg) _).1 h1
    have h3 : ⁅l, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * l * g, c⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h3]; exact h2

private theorem chevQ_normalizer_le_normalizer_centMod (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (centModSubgroup p L : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => chevQ_conj_mem_centMod hb hy, fun hy => ?_⟩
  have := chevQ_conj_mem_centMod (Subgroup.inv_mem _ hb) hy
  simpa [mul_assoc] using this

private theorem chevQ_mem_sup_mul {A N : Subgroup G} (h : A ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ A ⊔ N) : ∃ a ∈ A, ∃ n ∈ N, x = a * n := by
  have hx' : x ∈ ((A ⊔ N : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A N h] at hx'
  obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, n, hn, rfl⟩

private theorem chevQ_chevAut_of_mem {C : Subgroup G} {c : G} (hc : c ∈ C) :
    chevAut p C ⟨c, Subgroup.le_normalizer hc⟩ = MulAut.conj (chevQuotHom p C ⟨c, hc⟩) := by
  ext t
  obtain ⟨k, rfl⟩ := chevQuotHom_surjective p C t
  rw [chevAut_chevQuotHom, MulAut.conj_apply]
  have h : C.normalizerMonoidHom ⟨c, Subgroup.le_normalizer hc⟩ k = ⟨c, hc⟩ * k * ⟨c, hc⟩⁻¹ :=
    Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv]

theorem pSimple_equiv_of_surjective_simple (hp : p.Prime) {H J : Subgroup G}
    (hJ : GLAPComponent p H J) {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hna : ∃ a b : T, a * b ≠ b * a) (hbot : GLAPPrimeCore p T = ⊥) (f : ↥J →* T)
    (hf : Function.Surjective f) : Nonempty (PSimple p J ≃* T) := by
  have hTz : Subgroup.center T = ⊥ := b3Lie_center_eq_bot hna
  have hTq : CFSG.Open.IsQuasisimple T := b3Lie_isQuasisimple_of_simple hna
  have hA := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have eB : (T ⧸ GLAPPrimeCore p T) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hB : CFSG.Open.IsQuasisimple (T ⧸ GLAPPrimeCore p T) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eB.symm hTq
  obtain ⟨φ⟩ := nonempty_pSimple_equiv_of_surjective hp f hf hA hB
  exact ⟨φ.trans ((QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB)).trans
    ((QuotientGroup.quotientMulEquivOfEq hTz).trans QuotientGroup.quotientBot))⟩

theorem pSimple_equiv_of_diag (hp : p.Prime) {X H C J : Subgroup G}
    (hC : GLAPComponent p X C) (hJ : GLAPComponent p H J)
    (hJC : J ≤ C ⊔ centModSubgroup p C) (hCJ : C ≤ J ⊔ centModSubgroup p C) :
    Nonempty (PSimple p J ≃* PSimple p C) := by
  classical
  set N := centModSubgroup p C with hN
  have hNnorm : N ≤ Subgroup.normalizer (C : Set G) := fun g hg => hg.1
  have hNN : Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (N : Set G) :=
    chevQ_normalizer_le_normalizer_centMod C
  have hJnorm : J ≤ Subgroup.normalizer (C : Set G) :=
    hJC.trans (sup_le Subgroup.le_normalizer hNnorm)
  have hdecC : ∀ c ∈ C, ∃ j ∈ J, ∃ n ∈ N, c = j * n := fun c hc =>
    chevQ_mem_sup_mul (hJnorm.trans hNN) (hCJ hc)
  have hdecJ : ∀ j ∈ J, ∃ c ∈ C, ∃ n ∈ N, j = c * n := fun j hj =>
    chevQ_mem_sup_mul (Subgroup.le_normalizer.trans hNN) (hJC hj)
  obtain ⟨hTs, hTna⟩ := chev_pSimple_simple_nonabelian hp hC
  have hTz : Subgroup.center (PSimple p C) = ⊥ := chev_center_eq_bot_of_simple_nonabelian hTna
  have hbot := glaPPrimeCore_pSimple_eq_bot hp hC
  let ι : PSimple p C →* MulAut (PSimple p C) := MulAut.conj
  have hι : Function.Injective ι := by
    intro s t hst
    have hz : t * s⁻¹ ∈ Subgroup.center (PSimple p C) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := DFunLike.congr_fun hst (s⁻¹ * x * s)
      simp only [ι, MulAut.conj_apply] at h1
      calc x * (t * s⁻¹) = (t * (s⁻¹ * x * s) * t⁻¹) * (t * s⁻¹) := by
            rw [← h1]; group
        _ = (t * s⁻¹) * x := by group
    rw [hTz, Subgroup.mem_bot, mul_inv_eq_one] at hz
    exact hz.symm
  let e : PSimple p C ≃* ι.range := MonoidHom.ofInjective hι
  let ψ : ↥J →* MulAut (PSimple p C) := (chevAut p C).comp (Subgroup.inclusion hJnorm)
  have hn1 : ∀ n (hn : n ∈ N), chevAut p C ⟨n, hNnorm hn⟩ = 1 := fun n hn =>
    (chevAut_eq_one_iff hp hC (hNnorm hn)).2 (centMod_iff.2 hn)
  have hψ : ∀ j : ↥J, ψ j ∈ ι.range := by
    intro j
    obtain ⟨c, hc, n, hn, hjcn⟩ := hdecJ j.1 j.2
    have h1 : (⟨j.1, hJnorm j.2⟩ : ↥(Subgroup.normalizer (C : Set G))) =
        ⟨c, Subgroup.le_normalizer hc⟩ * ⟨n, hNnorm hn⟩ := Subtype.ext hjcn
    show chevAut p C ⟨j.1, hJnorm j.2⟩ ∈ ι.range
    rw [h1, map_mul, hn1 n hn, mul_one, chevQ_chevAut_of_mem hc]
    exact ⟨_, rfl⟩
  let ψ' : ↥J →* ι.range := ψ.codRestrict ι.range hψ
  let f : ↥J →* PSimple p C := (e.symm : ι.range →* PSimple p C).comp ψ'
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨k, rfl⟩ := chevQuotHom_surjective p C t
    obtain ⟨j, hj, n, hn, hcjn⟩ := hdecC k.1 k.2
    refine ⟨⟨j, hj⟩, ?_⟩
    have h1 : (⟨k.1, Subgroup.le_normalizer k.2⟩ : ↥(Subgroup.normalizer (C : Set G))) =
        ⟨j, hJnorm hj⟩ * ⟨n, hNnorm hn⟩ := Subtype.ext hcjn
    have h3 := chevQ_chevAut_of_mem (p := p) k.2
    rw [h1, map_mul, hn1 n hn, mul_one] at h3
    show e.symm (ψ' ⟨j, hj⟩) = chevQuotHom p C k
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact h3
  exact pSimple_equiv_of_surjective_simple hp hJ hTna hbot f hf

end Diagonal


section Core

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

private theorem chevQ_exists_hyperplane (hp : p.Prime) {B : Subgroup G} (hB : IsElemAbelian p B)
    (hB1 : B ≠ ⊥) :
    ∃ B₁ : Subgroup G, B₁ ≤ B ∧ (B₁.subgroupOf B).index = p ∧ ∃ d ∈ B, d ∉ B₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  haveI : Group.IsNilpotent B := hBp.isNilpotent
  haveI : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).2 hB1
  have hnt : (⊥ : Subgroup ↥B) ≠ ⊤ := bot_ne_top
  obtain ⟨H, hH, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup ↥B)).resolve_left hnt
  have hidx : H.index = p := hBp.isCoatom_iff_index_eq_prime.1 hH
  have hHB : (H.map B.subtype).subgroupOf B = H :=
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective H
  refine ⟨H.map B.subtype, Subgroup.map_subtype_le H, by rw [hHB]; exact hidx, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hH.1
  rw [Subgroup.eq_top_iff']
  intro x
  have : (x : G) ∈ H.map B.subtype := hcon x x.2
  obtain ⟨y, hy, hyx⟩ := this
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

private theorem chevQ_eq_sup_zpowers (hp : p.Prime) {B₁ B : Subgroup G} (hB₁B : B₁ ≤ B)
    (hidx : (B₁.subgroupOf B).index = p) {d : G} (hdB : d ∈ B) (hdB₁ : d ∉ B₁) :
    B₁ ⊔ Subgroup.zpowers d = B := by
  have hMD : B₁ ⊔ Subgroup.zpowers d ≤ B := sup_le hB₁B (Subgroup.zpowers_le.2 hdB)
  have hAM : B₁ ≤ B₁ ⊔ Subgroup.zpowers d := le_sup_left
  have hmul := Subgroup.relIndex_mul_relIndex B₁ (B₁ ⊔ Subgroup.zpowers d) B hAM hMD
  have hAD' : B₁.relIndex B = p := hidx
  rw [hAD'] at hmul
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ hmul) with h1 | h1
  · exfalso
    have : B₁ ⊔ Subgroup.zpowers d ≤ B₁ := (Subgroup.relIndex_eq_one.1 h1)
    exact hdB₁ (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  · rw [h1] at hmul
    have h2 : (B₁ ⊔ Subgroup.zpowers d).relIndex B = 1 :=
      Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one p).symm)
    exact le_antisymm hMD (Subgroup.relIndex_eq_one.1 h2)

private theorem chevQ_le_centralizer {A B : Subgroup G} (hA : IsElemAbelian p A) (hBA : B ≤ A) :
    A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
  Subgroup.mem_centralizer_iff.2 fun b hb => isElemAbelian_commute hA (hBA hb) ha

private theorem chevQ_centralizer_facts {K A B : Subgroup G} (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hKA : K ⊔ A = ⊤) (hBA : B ≤ A) :
    A ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) ∧
    Subgroup.centralizer (B : Set G) ≤ (K ⊓ Subgroup.centralizer (B : Set G)) ⊔ A ∧
    IsSubnormal (K ⊓ Subgroup.centralizer (B : Set G)) (Subgroup.centralizer (B : Set G)) := by
  have hAC := chevQ_le_centralizer hA hBA
  have h1 : A ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    fun a ha => chev_inf_centralizer_le_normalizer hAK B ⟨ha, hAC ha⟩
  have h2 : Subgroup.centralizer (B : Set G) ≤ (K ⊓ Subgroup.centralizer (B : Set G)) ⊔ A := by
    intro y hy
    have hy' : y ∈ A ⊔ K := by rw [sup_comm, hKA]; exact Subgroup.mem_top y
    obtain ⟨a, ha, k, hk, rfl⟩ := chevQ_mem_sup_mul hAK hy'
    have hkC : k ∈ Subgroup.centralizer (B : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAC ha)) hy
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left ⟨hk, hkC⟩)
  have h3 : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    h2.trans (sup_le Subgroup.le_normalizer h1)
  refine ⟨h1, h2, IsSubnormal.step inf_le_right ?_ (IsSubnormal.refl _)⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 h3

private theorem chevQ_pcomp_of_centralizer (hp : p.Prime) {K A B₁ L : Subgroup G}
    (hA : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hKA : K ⊔ A = ⊤)
    (hB₁A : B₁ ≤ A) (hL : GLAPComponent p (Subgroup.centralizer (B₁ : Set G)) L) :
    GLAPComponent p (K ⊓ Subgroup.centralizer (B₁ : Set G)) L := by
  obtain ⟨hAn, hle, -⟩ := chevQ_centralizer_facts hA hAK hKA hB₁A
  have hLK : L ≤ K ⊓ Subgroup.centralizer (B₁ : Set G) :=
    chevTools_perfect_le_of_sup hp hAn (isPGroup_of_isElemAbelian hA) (hL.1.trans hle)
      (glaPComponent_perfect hL)
  exact glaPComponent_of_le hp hL hLK inf_le_right

theorem chevQ_core (hp : p.Prime) (hp2 : p ≠ 2) (hD : KDChevDownQ p q) (h183 : Input18_3_4)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y) {K A : Subgroup Y}
    (hK : GLAPComponent p K K) (hchev : IsChevSimple q (PSimple p K))
    (hA : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set Y)) (hKA : K ⊔ A = ⊤) :
    ∀ (B : Subgroup Y), B ≤ A → ∀ J : Subgroup Y,
      GLAPComponent p (K ⊓ Subgroup.centralizer (B : Set Y)) J → IsChevSimple q (PSimple p J) := by
  suffices h : ∀ n : ℕ, ∀ B : Subgroup Y, Nat.card B = n → B ≤ A → ∀ J : Subgroup Y,
      GLAPComponent p (K ⊓ Subgroup.centralizer (B : Set Y)) J → IsChevSimple q (PSimple p J) from
    fun B hBA J hJ => h _ B rfl hBA J hJ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hn hBA J hJ
  by_cases hB1 : B = ⊥
  ·
    subst hB1
    have e : K ⊓ Subgroup.centralizer (((⊥ : Subgroup Y) : Subgroup Y) : Set Y) = K := by
      refine inf_eq_left.2 fun k _ => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have : c = 1 := by simpa using hc
      rw [this, one_mul, mul_one]
    rw [e] at hJ
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
    obtain ⟨-, hall, -⟩ := glaPLayer_of_isQuasisimple (Y := K) hq
    have hJK : J = K := (hall J hJ).trans (hall K hK).symm
    exact hJK ▸ hchev
  · obtain ⟨B₁, hB₁B, hidx, d, hdB, hdB₁⟩ := chevQ_exists_hyperplane hp (isElemAbelian_mono hA hBA) hB1
    have hBel : IsElemAbelian p B := isElemAbelian_mono hA hBA
    have hB₁A : B₁ ≤ A := hB₁B.trans hBA
    have hcard : Nat.card B₁ < n := by
      rw [← hn]
      exact card_lt_of_lt' (lt_of_le_of_ne hB₁B fun h => hdB₁ (h ▸ hdB))
    have hX₁K : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (B₁ : Set Y)) :=
      hY.of_injective _ (Subgroup.centralizer (B₁ : Set Y)).subtype_injective
    have hBX₁ : B ≤ Subgroup.centralizer (B₁ : Set Y) := chevQ_le_centralizer hBel hB₁B
    have hCB : Subgroup.centralizer (B : Set Y) ≤ Subgroup.centralizer (B₁ : Set Y) :=
      Subgroup.centralizer_le hB₁B
    have hJC : GLAPComponent p (Subgroup.centralizer (B : Set Y)) J :=
      glaPComponent_of_isSubnormal' hp (chevQ_centralizer_facts hA hAK hKA hBA).2.2 hJ
    have hJ' : GLAPComponent p (Subgroup.centralizer (B₁ : Set Y) ⊓ Subgroup.centralizer (B : Set Y)) J := by
      rwa [inf_eq_right.2 hCB]
    obtain ⟨𝒞, hcomp, hsup, hinv, htrans⟩ := h183 Y _ hX₁K p hp B hBX₁ hBel J hJ'
    have hCchev : ∀ C ∈ 𝒞, IsChevSimple q (PSimple p C) := fun C hC =>
      ih _ hcard B₁ rfl hB₁A C (chevQ_pcomp_of_centralizer hp hA hAK hKA hB₁A (hcomp C hC))
    have hJle : J ≤ ⨆ C ∈ 𝒞, C := by
      rw [hsup]
      exact (gLBConj_one J).symm.le.trans (le_iSup₂
        (f := fun g (_ : g ∈ GLAPLayer p (Subgroup.centralizer (B₁ : Set Y))) => GLBConj g J)
        (1 : Y) (Subgroup.one_mem _))
    by_cases hdiag : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂
    ·
      have hcov := i183DiagAt_holds Y p hp hp2 B₁ B J 𝒞 hBel hB₁B hidx hX₁K hJC hcomp hsup hinv
        htrans hdiag
      obtain ⟨C₁, hC₁, -⟩ := hdiag
      have hJC' : J ≤ C₁ ⊔ centModSubgroup p C₁ := hJle.trans (iSup₂_le fun C hC => by
        by_cases hCC : C = C₁
        · exact hCC ▸ le_sup_left
        · exact (le_centModSubgroup_of_ne hp (hcomp C hC) (hcomp C₁ hC₁) hCC).trans le_sup_right)
      obtain ⟨e⟩ := pSimple_equiv_of_diag hp (hcomp C₁ hC₁) hJC hJC' (hcov C₁ hC₁)
      exact chev_isChevSimple_of_mulEquiv e (hCchev C₁ hC₁)
    ·
      push Not at hdiag
      obtain ⟨C, hC⟩ : ∃ C, C ∈ 𝒞 := by
        by_contra h
        push Not at h
        have h0 : (⨆ C ∈ 𝒞, C) = ⊥ := by simp [h]
        rw [h0, le_bot_iff] at hJle
        exact glaPComponent_ne_bot' hJC hJle
      have hall : ∀ C' ∈ 𝒞, C' = C := fun C' hC' => hdiag C' hC' C hC
      have hJCC : J ≤ C := hJle.trans (iSup₂_le fun C' hC' => (hall C' hC').le)
      have hdN : d ∈ Subgroup.normalizer (C : Set Y) := by
        rw [mem_normalizer_iff_gLBConj_eq]
        exact hall _ (hinv C hC d hdB)
      have hBeq := chevQ_eq_sup_zpowers hp hB₁B hidx hdB hdB₁
      have hCeq : C ⊓ Subgroup.centralizer (B : Set Y) =
          C ⊓ Subgroup.centralizer ({d} : Set Y) := by
        refine le_antisymm (inf_le_inf_left C (Subgroup.centralizer_le (by simpa using hdB))) ?_
        intro y hy
        refine ⟨hy.1, ?_⟩
        have hyB₁ : y ∈ Subgroup.centralizer (B₁ : Set Y) := (hcomp C hC).1 hy.1
        have hle : B ≤ Subgroup.centralizer ({y} : Set Y) := by
          rw [← hBeq]
          refine sup_le (fun b hb => ?_) ?_
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.1 hyB₁ b hb
          · rw [Subgroup.zpowers_le]
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm
        show y ∈ Subgroup.centralizer (B : Set Y)
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
      have hJd : GLAPComponent p (C ⊓ Subgroup.centralizer ({d} : Set Y)) J := by
        have h1 : GLAPComponent p (C ⊓ Subgroup.centralizer (B : Set Y)) J :=
          glaPComponent_of_le hp hJC (le_inf hJCC hJC.1) inf_le_right
        rwa [hCeq] at h1
      exact chevQ_step hp hD (hcomp C hC) (hCchev C hC) hdN (hBel.2 d hdB) hJd

private theorem chevQ_pSimple_equiv_subgroupOf (p : ℕ) {H L : Subgroup G} (hLH : L ≤ H) :
    Nonempty (PSimple p L ≃* PSimple p (L.subgroupOf H)) := by
  obtain ⟨g⟩ := nonempty_pQuot_equiv_subgroupOf p hLH
  exact ⟨QuotientGroup.congr _ _ g.symm (Subgroup.map_center_eq g.symm)⟩

theorem chevClosureQAt_of_kdChevDownQ (h183 : Input18_3_4)
    (hD : ∀ q : ℕ, q.Prime → KDChevDownQ p q) : ChevClosureQAt G p := by
  intro hp hp2 q hq X K A hX hK hchev hA hAK J hJ
  classical
  set H : Subgroup G := K ⊔ A with hH
  have hKH : K ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hKX : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hX hK.1
  have hHK : CFSG.Open.IsKGroup ↥H :=
    chevTools_isKGroup_sup hp hKX hAK (isPGroup_of_isElemAbelian hA)
  have hKK : GLAPComponent p K K := glaPComponent_of_le hp hK le_rfl hK.1
  have hK' : GLAPComponent p (K.subgroupOf H) (K.subgroupOf H) :=
    glaPComponent_subgroupOf hp hKH hKK
  obtain ⟨eK⟩ := chevQ_pSimple_equiv_subgroupOf p hKH
  have hchev' : IsChevSimple q (PSimple p (K.subgroupOf H)) :=
    chev_isChevSimple_of_mulEquiv eK.symm hchev
  have hA' : IsElemAbelian p (A.subgroupOf H) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (Subtype.ext (isElemAbelian_commute hA a.2 b.2))
    · exact Subtype.ext (by simpa using hA.2 (x : G) hx)
  have hAK' : A.subgroupOf H ≤ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 (hAK hx) (h : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hKA' : K.subgroupOf H ⊔ A.subgroupOf H = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup K A)
  have hJle : K ⊓ Subgroup.centralizer (A : Set G) ≤ H := inf_le_left.trans hKH
  have hJ1 := glaPComponent_subgroupOf hp hJle hJ
  have hcen : (Subgroup.centralizer (A : Set G)).subgroupOf H =
      Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H) := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_subgroupOf_inf_centralizer hAH,
      Subgroup.inf_subgroupOf_left]
  have hinf : (K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H =
      K.subgroupOf H ⊓ Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H) := by
    rw [← hcen]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hinf] at hJ1
  have hres := chevQ_core hp hp2 (hD q hq) h183 (Y := ↥H) hHK hK' hchev' hA' hAK' hKA'
    (A.subgroupOf H) le_rfl (J.subgroupOf H) hJ1
  obtain ⟨eJ⟩ := chevQ_pSimple_equiv_subgroupOf p (hJ.1.trans hJle)
  exact chev_isChevSimple_of_mulEquiv eJ hres

end Core


section Transport

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

private theorem chevQ_fixSubgroup_one {K : Type} [Group K] : fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

private theorem chevQ_fixSubgroup_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (α : MulAut S) :
    fixSubgroup (MulAut.congr e α) = (fixSubgroup α).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    rw [mem_fixSubgroup] at hy
    have h2 : e (α (e.symm y)) = y := hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixSubgroup]
    have h3 := congrArg e.symm h2
    simpa using h3
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup] at hx
    rw [mem_fixSubgroup]
    show e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]

theorem chevQ_transport (hp : p.Prime) {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) {α : MulAut S} {I : Subgroup S} (hI : GLAPComponent p (fixSubgroup α) I) :
    GLAPComponent p (fixSubgroup (MulAut.congr e α)) (I.map e.toMonoidHom) ∧
      Nonempty (PSimple p I ≃* PSimple p (I.map e.toMonoidHom)) := by
  have hker : Nat.Coprime p (Nat.card ↥(fixSubgroup α ⊓ e.toMonoidHom.ker)) := by
    have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective
    rw [hk, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have h1 := glaPComponent_map hp e.toMonoidHom hker hI
  rw [← chevQ_fixSubgroup_congr] at h1
  exact ⟨h1, nonempty_pSimple_equiv_map hp e.toMonoidHom hI h1⟩

private theorem chevQ_false_of_solvable {T : Type} [Group T] [Finite T] {X I : Subgroup T}
    (hsolv : Group.IsSolvable ↥X) (hI : GLAPComponent p X I) : False := by
  haveI := hsolv
  have hJX : I ≤ X := hI.1
  have hperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
  have hne : I ≠ ⊥ := glaPComponent_ne_bot' hI
  have hJ'ne : I.subgroupOf X ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJX, h0, Subgroup.map_bot]
  have hlt : ⁅I.subgroupOf X, I.subgroupOf X⁆ < I.subgroupOf X :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅I.subgroupOf X, I.subgroupOf X⁆ = I.subgroupOf X := by
    apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJX]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

private theorem chevQ_isSubnormal_top {T : Type} [Group T] [IsSimpleGroup T] {H K : Subgroup T}
    (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K hle hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · exact Or.inl (le_bot_iff.1 (hM ▸ hle))
    · subst hM
      haveI : H.Normal :=
        ⟨fun n hn' g => (Subgroup.normal_subgroupOf_iff le_top).1 hn n g hn' (Subgroup.mem_top g)⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

private theorem chevQ_glaPPrimeCore_simple (hp : p.Prime) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] {X I : Subgroup S} (hI : GLAPComponent p X I) :
    GLAPPrimeCore p S = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p S) with h | h
  · exact h
  · exfalso
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hI
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p S)) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hcop
    have hIcop : Nat.Coprime p (Nat.card ↥I) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card I) hcop
    have hle : (⊤ : Subgroup ↥I) ≤ GLAPPrimeCore p ↥I := by
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [Subgroup.card_top]
      exact hIcop
    haveI := isQuasisimple_nontrivial hq
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot p I)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [QuotientGroup.eq]
    exact hle (Subgroup.mem_top _)

theorem chevQ_pSimple_top_equiv (hp : p.Prime) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {I : Subgroup S} (hI : GLAPComponent p (⊤ : Subgroup S) I) :
    Nonempty (PSimple p I ≃* S) := by
  have hIt : I = ⊤ := by
    rcases chevQ_isSubnormal_top hI.2.1 rfl with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · exact h
  subst hIt
  exact pSimple_equiv_of_surjective_simple hp hI hna (chevQ_glaPPrimeCore_simple hp hI)
    (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).toMonoidHom Subgroup.topEquiv.surjective

private theorem chevQ_conj_of_pow {S : Type} [Group S] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (Outer S)) [Finite (Outer S)] (α : MulAut S) (hα : α ^ p = 1) :
    ∃ g : S, MulAut.conj g = α := by
  let π : MulAut S →* Outer S := QuotientGroup.mk' (inner S)
  have hp' : π α ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hord : orderOf (π α) ∣ p := orderOf_dvd_of_pow_eq_one hp'
  have hdvd : orderOf (π α) ∣ Nat.card (Outer S) := orderOf_dvd_natCard _
  have hmem : α ∈ inner S := by
    rcases (Nat.dvd_prime hp).1 hord with h1 | h1
    · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
    · rw [h1] at hdvd
      exact absurd hdvd h
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg⟩

private theorem chevQ_card_outer {S : Type} [Group S] (hz : Subgroup.center S = ⊥) {n : ℕ}
    (hS : Nat.card S = n) (hA : Nat.card (MulAut S) = 2 * n) (hn : n ≠ 0) :
    Nat.card (Outer S) = 2 := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut S => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hz, Subgroup.mem_bot] at hc
    exact hc
  have hinner : Nat.card (inner S) = Nat.card S := Nat.card_range_of_injective hinj
  have hidx := (inner S).card_mul_index
  rw [hinner, hS, hA] at hidx
  have hO : (inner S).index = Nat.card (Outer S) := rfl
  rw [hO] at hidx
  have : n * Nat.card (Outer S) = n * 2 := by rw [mul_comm n 2]; exact hidx
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) this

private theorem chevQ_pow_eq_one_of_conj {S : Type} [Group S] (hz : Subgroup.center S = ⊥) {p : ℕ}
    {g : S} (hα : (MulAut.conj g : MulAut S) ^ p = 1) : g ^ p = 1 := by
  have h1 : MulAut.conj (g ^ p) = 1 := by
    rw [map_pow]
    exact hα
  have h2 : g ^ p ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h3 := congrArg (fun φ : MulAut S => φ h) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  rw [hz, Subgroup.mem_bot] at h2
  exact h2

private theorem chevQ_fix_conj {S : Type} [Group S] (g : S) :
    fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set S) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_iff]
  simp only [MulAut.conj_apply, Set.mem_singleton_iff, forall_eq]
  exact mul_inv_eq_iff_eq_mul

end Transport


section Ambiguous

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def KDAmbDownQ (p q : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (i : TauCeti.CFSGIndex), ambiguousChev q i →
    Nonempty (S ≃* i.Group) → ∀ α : MulAut S, α ^ p = 1 → α ≠ 1 →
      ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I → IsChevSimple q (PSimple p I)

private theorem chevQ_l2_carrier {q' : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q').Valid) (hq4 : 4 ≤ q'.card) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group ∧
      Nat.card (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group =
        q'.card * (q'.card ^ 2 - 1) / Nat.gcd 2 (q'.card - 1) := by
  haveI : Fact q'.p.Prime := ⟨q'.prime_p⟩
  have hK : Nat.card (GaloisField q'.p q'.exponent) = q'.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q'.p q'.exponent q'.exponent_pos.ne'
  let ePSL := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q' hv
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
      (GaloisField q'.p q'.exponent)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; exact hq4)
  refine ⟨ePSL.isSimpleGroup, ?_⟩
  have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (K := GaloisField q'.p q'.exponent) (n := 2) (by norm_num)
  rw [hK] at h1
  rw [Nat.card_congr (ePSL.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField q'.p q'.exponent))).toEquiv, h1]
  simp [Finset.Icc_self]

private theorem chevQ_dvd_504_cases : ∀ d < 73, d ∣ 504 → d.primeFactors.card ≤ 2 ∨ d = 42 := by
  decide +kernel

private theorem chevQ_isSolvable_of_card_504 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Nat.card S = 504) {H : Subgroup S} (hH : H ≠ ⊤) : Group.IsSolvable H := by
  have hfac := CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt.card_dvd_factorial_index hH
  rw [hS] at hfac
  have hmul := Subgroup.card_mul_index H
  rw [hS] at hmul
  have hidx1 : H.index ≠ 1 := fun h => hH (Subgroup.index_eq_one.1 h)
  have hidx0 : H.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    omega
  have hidx : 7 ≤ H.index := by
    by_contra hlt
    push Not at hlt
    interval_cases h : H.index <;> simp_all [Nat.factorial] <;> omega
  have hle : Nat.card H ≤ 72 := by
    by_contra hgt
    push Not at hgt
    have : 73 * 7 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) hidx
    omega
  have hdvd : Nat.card H ∣ 504 := ⟨H.index, hmul.symm⟩
  rcases chevQ_dvd_504_cases _ (by omega) hdvd with h | h
  · exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two h
  · exact CFSG.Quasithin.SzG11G94.isSolvable_of_squarefree_card
      (by rw [h]; exact CFSG.Quasithin.SzG11G94.squarefree_forty_two)

private theorem chevQ_fixSubgroup_ne_top {S : Type} [Group S] {α : MulAut S} (hα1 : α ≠ 1) :
    fixSubgroup α ≠ ⊤ := fun h =>
  hα1 (MulEquiv.ext fun x => mem_fixSubgroup.1 (h ▸ Subgroup.mem_top x))

theorem ambiguous_L27_noPComponent {q' : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q').Valid) (hq' : q'.card = 7)
    (α : MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group) (hα1 : α ≠ 1)
    (I : Subgroup (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group) :
    ¬ GLAPComponent p (fixSubgroup α) I := by
  intro hI
  obtain ⟨hsimple, hcard⟩ := chevQ_l2_carrier hv (by rw [hq']; norm_num)
  rw [hq'] at hcard
  norm_num at hcard
  haveI := hsimple
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact chevQ_false_of_solvable
    (CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt.isSolvable_of_card_168 hcard
      (chevQ_fixSubgroup_ne_top hα1)) hI

theorem ambiguous_L28_noPComponent {q' : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q').Valid) (hq' : q'.card = 8)
    (α : MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group) (hα1 : α ≠ 1)
    (I : Subgroup (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group) :
    ¬ GLAPComponent p (fixSubgroup α) I := by
  intro hI
  obtain ⟨hsimple, hcard⟩ := chevQ_l2_carrier hv (by rw [hq']; norm_num)
  rw [hq'] at hcard
  norm_num at hcard
  haveI := hsimple
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A 1 q', hv⟩).Group :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact chevQ_false_of_solvable
    (chevQ_isSolvable_of_card_504 hcard (chevQ_fixSubgroup_ne_top hα1)) hI

private theorem chevQ_nonab_of_card_not_prime {T : Type} [Group T] [IsSimpleGroup T]
    (hc : ¬ (Nat.card T).Prime) : ∃ a b : T, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup T := { ‹Group T› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := T)).1 ‹IsSimpleGroup T›)

private theorem chevQ_prime_dvd_25920 {r : ℕ} (hr : r.Prime) (h : r ∣ 25920) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  have h' : r ∣ 2 ^ 6 * 3 ^ 4 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
        (hr.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1))

private theorem chevQ_u42_cent_solvable {S : Type} [Group S] [Finite S]
    (hcard : Nat.card S = 25920) (h15 : ∀ x : S, orderOf x ≠ 15) (g : S) (hg5 : g ^ 5 = 1)
    (hg1 : g ≠ 1) : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set S)) := by
  have hord : orderOf g = 5 := orderOf_eq_prime hg5 hg1
  have hnd : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({g} : Set S)) := by
    intro hdvd
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have hcomm : Commute g (h : S) := by
      have hmem : (h : S) ∈ Subgroup.centralizer ({g} : Set S) := h.2
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem g (Set.mem_singleton g)
    have hordh : orderOf (h : S) = 3 := by rw [Subgroup.orderOf_coe, hh]
    have hco : (orderOf g).Coprime (orderOf (h : S)) := by
      rw [hord, hordh]
      norm_num
    have hx : orderOf (g * (h : S)) = 15 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hord, hordh]
    exact h15 _ hx
  have hdvdS : Nat.card (Subgroup.centralizer ({g} : Set S)) ∣ 25920 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card _
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card (Subgroup.centralizer ({g} : Set S))).primeFactors ⊆
      ({2, 5} : Finset ℕ) := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrm : r ∣ Nat.card (Subgroup.centralizer ({g} : Set S)) :=
      Nat.dvd_of_mem_primeFactors hr
    rcases chevQ_prime_dvd_25920 hrp (hrm.trans hdvdS) with h | h | h
    · simp [h]
    · exact absurd (h ▸ hrm) hnd
    · simp [h]
  exact (Finset.card_le_card hsub).trans (by decide)

theorem ambiguous_U42_noPComponent (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {q' : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 3 q').Valid)
    (hq' : q'.card = 2)
    (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group) (hα : α ^ p = 1) (hα1 : α ≠ 1)
    (I : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group) :
    ¬ GLAPComponent p (fixSubgroup α) I := by
  intro hI
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard2 : q'.p ^ q'.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq'
  have hpq : q'.p = 2 := by
    have hdvd : q'.p ∣ 2 := by
      rw [← hcard2]
      exact dvd_pow_self q'.p q'.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_two).1 hdvd
  have hfq : q'.exponent = 1 := by
    rw [hpq] at hcard2
    exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q'.exponent = 2 ^ 1 by simpa using hcard2)
  have hmodel : Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group .PSU 4 2 1 := by
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q' hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group)
    rw [hpq, hfq] at h
    exact Or.inl ⟨by decide, h⟩
  obtain ⟨hAut, hS⟩ := CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 hmodel
  haveI hfin : Finite (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group :=
    Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  haveI hsimple : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 4 2 1 (by
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q' hv
        (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group)
      rw [hpq, hfq] at h
      exact h)).2
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group, a * b ≠ b * a :=
    chevQ_nonab_of_card_not_prime (by rw [hS]; norm_num)
  have hz := chev_center_eq_bot_of_simple_nonabelian hnc
  have hout := chevQ_card_outer hz hS (by omega) (by norm_num)
  haveI : Finite (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group) :=
    Nat.finite_of_card_ne_zero (by rw [hout]; norm_num)
  have hpout : ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q', hv⟩).Group) := by
    rw [hout]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  obtain ⟨g, rfl⟩ := chevQ_conj_of_pow hp hpout α hα
  have hg : g ^ p = 1 := chevQ_pow_eq_one_of_conj hz hα
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hpS : p ∣ 25920 := by
    have := orderOf_dvd_natCard g
    rwa [orderOf_eq_prime hg hg1, hS] at this
  have hp5 : p = 5 := by
    rcases chevQ_prime_dvd_25920 hp hpS with h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact h
  subst hp5
  rw [chevQ_fix_conj] at hI
  exact chevQ_false_of_solvable (chevQ_u42_cent_solvable hS (u42_noFifteen hv hq') g hg hg1) hI

private theorem chevQ_prime_dvd_6048 {r : ℕ} (hr : r.Prime) (h : r ∣ 6048) :
    r = 2 ∨ r = 3 ∨ r = 7 := by
  have h' : r ∣ 2 ^ 5 * 3 ^ 3 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
        (hr.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1))

private theorem chevQ_cent_solvable_of_central {S : Type} [Group S] [Finite S] {p n : ℕ}
    (hp : p.Prime) (hS : Nat.card S = p * n) (hn : n.primeFactors.card ≤ 2) (g : S)
    (hg : g ^ p = 1) (hg1 : g ≠ 1) : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set S)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup S := Subgroup.centralizer ({g} : Set S) with hC
  have hgC : g ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  let g' : ↥C := ⟨g, hgC⟩
  have hg'c : g' ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  set Z : Subgroup ↥C := Subgroup.zpowers g' with hZ
  have hZc : Z ≤ Subgroup.center ↥C := Subgroup.zpowers_le.2 hg'c
  haveI : Z.Normal := Subgroup.normal_of_le_center hZc
  haveI hZsolv : Group.IsSolvable ↥Z :=
    isSolvable_of_comm fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hZc a.2) b.1).symm)
  have hord : orderOf g' = p :=
    orderOf_eq_prime (Subtype.ext hg) (fun h => hg1 (congrArg Subtype.val h))
  have hZcard : Nat.card Z = p := by rw [hZ, Nat.card_zpowers, hord]
  haveI hQsolv : Group.IsSolvable (↥C ⧸ Z) := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have h1 : Nat.card (↥C ⧸ Z) * p = Nat.card ↥C := by
      rw [← hZcard]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
    have h2 : Nat.card ↥C ∣ p * n := hS ▸ Subgroup.card_subgroup_dvd_card C
    rw [← h1, mul_comm] at h2
    have h3 : Nat.card (↥C ⧸ Z) ∣ n := Nat.dvd_of_mul_dvd_mul_left hp.pos h2
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hS
      exact Nat.card_pos.ne' hS
    exact (Finset.card_le_card (Nat.primeFactors_mono h3 hn0)).trans hn
  exact solvable_of_ker_le_range Z.subtype (QuotientGroup.mk' Z) (by simp)

theorem ambiguous_U33_noPComponent
    (hp : p.Prime) (hp2 : p ≠ 2) (hInner : KDChevInner p) {q' : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q').Valid) (hq' : q'.card = 3)
    (α : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group) (hα : α ^ p = 1) (hα1 : α ≠ 1)
    (I : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group) :
    ¬ GLAPComponent p (fixSubgroup α) I := by
  intro hI
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard3 : q'.p ^ q'.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq'
  have hpq : q'.p = 3 := by
    have hdvd : q'.p ∣ 3 := by
      rw [← hcard3]
      exact dvd_pow_self q'.p q'.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_three).1 hdvd
  have hfq : q'.exponent = 1 := by
    rw [hpq] at hcard3
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ q'.exponent = 3 ^ 1 by simpa using hcard3)
  have hmodel' := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q' hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group)
  rw [hpq, hfq] at hmodel'
  have hmodel : Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group .PSU 3 3 1 :=
    Or.inl ⟨by decide, hmodel'⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hmodel
  have hAut := CFSG.GH74.KGroups.U33.card_mulAut e
  have hS : Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group = 6048 := by
    rw [Nat.card_congr e.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  haveI hfin : Finite (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group :=
    Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  haveI hsimple : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hmodel').2
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group, a * b ≠ b * a :=
    chevQ_nonab_of_card_not_prime (by rw [hS]; norm_num)
  have hz := chev_center_eq_bot_of_simple_nonabelian hnc
  have hout := chevQ_card_outer hz hS (by omega) (by norm_num)
  haveI : Finite (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group) :=
    Nat.finite_of_card_ne_zero (by rw [hout]; norm_num)
  have hpout : ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group) := by
    rw [hout]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  obtain ⟨g, rfl⟩ := chevQ_conj_of_pow hp hpout α hα
  have hg : g ^ p = 1 := chevQ_pow_eq_one_of_conj hz hα
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hpS : p ∣ 6048 := by
    have := orderOf_dvd_natCard g
    rwa [orderOf_eq_prime hg hg1, hS] at this
  rcases chevQ_prime_dvd_6048 hp hpS with h | h | h
  · exact absurd h hp2
  · subst h
    have hchev : IsChevSimple 3 (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩).Group :=
      Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 q', hv⟩, by
        show TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.twistedA 2 q') = 3
        rw [TauCeti.LieTypeIndex.characteristic_twistedA]
        exact hpq, ⟨MulEquiv.refl _⟩⟩
    have hbot := hInner _ hsimple hnc hchev _ hα hα1 ⟨g, rfl⟩
    have hle : I ≤ GLAPLayer 3 (fixSubgroup (MulAut.conj g)) := le_sSup hI
    rw [hbot] at hle
    exact glaPComponent_ne_bot' hI (le_bot_iff.1 hle)
  · subst h
    rw [chevQ_fix_conj] at hI
    refine chevQ_false_of_solvable (chevQ_cent_solvable_of_central (n := 864) hp (by rw [hS])
      ?_ g hg hg1) hI
    decide +kernel

theorem ambiguous_lie_noPComponent
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hInner : KDChevInner p) (hpq : p ≠ q)
    (d : TauCeti.ValidLieTypeIndex) (hd : ambiguousChev q (TauCeti.CFSGIndex.lie d))
    (α : MulAut (TauCeti.CFSGIndex.lie d).Group) (hα : α ^ p = 1) (hα1 : α ≠ 1)
    (I : Subgroup (TauCeti.CFSGIndex.lie d).Group) :
    ¬ GLAPComponent p (fixSubgroup α) I := by
  obtain ⟨ld, hv⟩ := d
  cases ld
  case A r q' =>
    rcases r with _ | _ | r
    · simp [ambiguousChev] at hd
    · simp only [ambiguousChev] at hd
      rcases hd with ⟨hq7, rfl⟩ | ⟨hq8, rfl⟩
      · exact ambiguous_L27_noPComponent hv hq7 α hα1 I
      · exact ambiguous_L28_noPComponent hv hq8 α hα1 I
    · simp [ambiguousChev] at hd
  case twistedA r q' =>
    rcases r with _ | _ | _ | _ | r
    · simp [ambiguousChev] at hd
    · simp [ambiguousChev] at hd
    · simp only [ambiguousChev] at hd
      obtain ⟨hq3, rfl⟩ := hd
      exact ambiguous_U33_noPComponent hp hp2 hInner hv hq3 α hα hα1 I
    · simp only [ambiguousChev] at hd
      obtain ⟨hq2, rfl⟩ := hd
      exact ambiguous_U42_noPComponent hp hp2 hpq hv hq2 α hα hα1 I
    · simp [ambiguousChev] at hd
  all_goals simp [ambiguousChev] at hd

private theorem chevQ_amb_alt (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (hi : ambiguousChev q (TauCeti.CFSGIndex.alternating n hn))
    (β : MulAut (alternatingGroup (Fin n))) (hβ : β ^ p = 1) (hβ1 : β ≠ 1)
    (I : Subgroup (alternatingGroup (Fin n))) (hI : GLAPComponent p (fixSubgroup β) I) :
    IsChevSimple q (PSimple p I) := by
  obtain ⟨m, hm5, hmn, ⟨e⟩⟩ := kdAltDown_holds n p hn hp hp2 β hβ hβ1 I hI
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨h5m, hpm⟩ := max_le_iff.1 hm5
  simp only [ambiguousChev] at hi
  have hn8 : n = 8 ∧ q = 2 := by
    rcases hi with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, hq2⟩
    · exfalso; omega
    · exfalso; omega
    · exact ⟨rfl, hq2⟩
  obtain ⟨hn8, hq2⟩ := hn8
  have hm : m = 5 := by omega
  subst hm
  subst hq2
  have hA5 : IsChevSimple 2 (alternatingGroup (Fin 5)) :=
    Or.inr ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num), Or.inl ⟨rfl, Or.inl rfl⟩,
      ⟨MulEquiv.refl _⟩⟩
  exact chev_isChevSimple_of_mulEquiv e hA5

private theorem chevQ_amb_core
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hInner : KDChevInner p) (hA : KDAmbSolv p)
    (i : TauCeti.CFSGIndex) [Finite i.Group] (hi : ambiguousChev q i) (β : MulAut i.Group)
    (hβ : β ^ p = 1) (hβ1 : β ≠ 1) (I : Subgroup i.Group)
    (hI : GLAPComponent p (fixSubgroup β) I) : IsChevSimple q (PSimple p I) := by
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | alternating n hn => exact chevQ_amb_alt hp hp2 hn hi β hβ hβ1 I hI
  | lie d =>
    by_cases hpq : p = q
    · subst hpq
      exact (chevQ_false_of_solvable (hA _ hi β hβ hβ1) hI).elim
    · exact (ambiguous_lie_noPComponent hp hp2 hInner hpq d hi β hβ hβ1 I hI).elim
  | sporadic s => simp [ambiguousChev] at hi

theorem kdAmbDownQ_holds
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hInner : KDChevInner p) (hA : KDAmbSolv p) :
    KDAmbDownQ p q := by
  intro S _ _ i hi ⟨e⟩ α hα hα1 I hI
  haveI : Finite i.Group := Finite.of_equiv S e.toEquiv
  obtain ⟨hβ, ⟨e₁⟩⟩ := chevQ_transport hp e hI
  have hβp : MulAut.congr e α ^ p = 1 := by rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  exact chev_isChevSimple_of_mulEquiv e₁ (chevQ_amb_core hp hp2 hInner hA i hi _ hβp hβ1 _ hβ)

end Ambiguous


section LieStep

open CFSG.HardMathSupport.Solomon.Coordinator (lieIndexChar)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (LieCompsOn)
open CFSG.Yardstones.Md42047359a2a (lieFamily)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem chevQ_lieIndexChar (d : TauCeti.LieTypeIndex) :
    lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]

theorem kdChevDownQ_of_lieComps (hp : p.Prime)
    (hLC : ∀ F, LieCompsOn p F) (hInner : q = p → KDChevInner p) (hAmb : KDAmbDownQ p q) :
    KDChevDownQ p q := by
  intro S _ _ hS hna hchev α hα I hI
  by_cases hα1 : α = 1
  · subst hα1
    rw [chevQ_fixSubgroup_one] at hI
    obtain ⟨e⟩ := chevQ_pSimple_top_equiv hp hna hI
    exact chev_isChevSimple_of_mulEquiv e hchev
  · have hchev0 := hchev
    rcases hchev0 with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | cyclic r hr => exact (show False from hi).elim
      | alternating n hn => exact (show False from hi).elim
      | sporadic s => exact (show False from hi).elim
      | lie d =>
        by_cases hin : q = p ∧ α ∈ inner S
        · exfalso
          obtain ⟨hqp, hαin⟩ := hin
          have hbot := hInner hqp S hS hna (hqp ▸ hchev) α hα hα1 hαin
          exact glaPComponent_ne_bot' hI (le_bot_iff.1 (hbot ▸ le_sSup hI))
        · have hcond : lieIndexChar d.1 ≠ p ∨ ∀ a : S, MulAut.conj a ≠ α := by
            rw [chevQ_lieIndexChar, show d.1.characteristic = q from hi]
            by_cases hqp : q = p
            · exact Or.inr fun a ha => hin ⟨hqp, MonoidHom.mem_range.2 ⟨a, ha⟩⟩
            · exact Or.inl hqp
          have hexp := hLC (lieFamily d.1) S hS hna d rfl ⟨e⟩ α hα hα1 hcond
          rw [chevQ_lieIndexChar, show d.1.characteristic = q from hi] at hexp
          exact lieCompsExport_isChevSimple hp hexp hI
    · exact hAmb S i hi ⟨e⟩ α hα hα1 I hI

end LieStep


section Final

set_option linter.unusedSectionVars false


open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (LieCompsOn)

theorem chevClosureQAt_of_lieComps (hLC : ∀ F, LieCompsOn p F)
    (hLQ : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.LieQConstrainedInner p) :
    ChevClosureQAt G p := by
  intro hp hp2
  have hAmbSolv : KDAmbSolv p := kdAmbSolv_holds hp hp2 u42_fixSubgroup_solvable
  have hInner : KDChevInner p :=
    kdChevInner_of hp hp2 (kdCharP_of_lieQConstrainedInner hp hLQ) hAmbSolv
  exact chevClosureQAt_of_kdChevDownQ input18_3_4_holds (fun q _ =>
    kdChevDownQ_of_lieComps hp hLC (fun _ => hInner) (kdAmbDownQ_holds hp hp2 hInner hAmbSolv))
    hp hp2

theorem chevClosureAt_of_lieComps (hLC : ∀ F, LieCompsOn p F)
    (hLQ : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.LieQConstrainedInner p) :
    ChevClosureAt G p :=
  chevClosureAt_of_chevClosureQAt (chevClosureQAt_of_lieComps hLC hLQ)

end Final

end CFSG.LocalAnalysis.GLTheoremA
