module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux2
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.PreuniquenessRankFour.Helpers

section Cyclic

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {R : Sylow p X}
  {X₀ : Subgroup X}

theorem mem_zpowers_of_mem_centralizer_of_pow_eq_one
    (h : ReducedNongeneration p X R X₀) {E : Subgroup X} [E.Normal] (hER : E ≤ (R : Subgroup X))
    (hcard : Nat.card E = p ^ 3) (hexp : ∀ x ∈ E, x ^ p = 1) {z : X}
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) {y : X}
    (hyR : y ∈ (R : Subgroup X)) (hyC : y ∈ Subgroup.centralizer (E : Set X)) (hyp : y ^ p = 1) :
    y ∈ Subgroup.zpowers z := by
  have hp := h.prime
  by_contra hyz
  obtain ⟨B, hBE, hB, hBcard⟩ := exists_isElemAbelian_card_sq_of_card_cube hcard hexp
  have hy1 : y ≠ 1 := fun h1 => hyz (h1 ▸ Subgroup.one_mem _)
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hyE : y ∉ E := fun hyE => hyz (inf_centralizer_eq_of_center_map hZE ▸ ⟨hyE, hyC⟩)
  have hrank2 : 2 ≤ Open.pRank p E :=
    le_csSup (pRank_bddAbove p hp E) ⟨B, hBE, hB, hBcard⟩
  have hHrank : 3 ≤ Open.pRank p (E ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (E : Set X))) :=
    three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hB hBcard hyord
      (fun hyB => hyE (hBE hyB)) (Subgroup.centralizer_le hBE hyC) (hBE.trans le_sup_left)
      (Subgroup.mem_sup_right ⟨hyR, hyC⟩)
  have hN := normalizer_le_weakCore p hER hrank2 hHrank
  rw [Subgroup.normalizer_eq_top] at hN
  exact h.ne_top (top_le_iff.mp (hN.trans h.weakCore_le))

theorem isCyclic_inf_centralizer3
    (h : ReducedNongeneration p X R X₀) {E : Subgroup X} [E.Normal] (hER : E ≤ (R : Subgroup X))
    (hcard : Nat.card E = p ^ 3) (hexp : ∀ x ∈ E, x ^ p = 1) {z : X}
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) (hzp : orderOf z = p) :
    IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (E : Set X) : Subgroup X) := by
  have hp := h.prime
  by_contra hnc
  obtain ⟨B, hB, hBcard⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (hp.odd_of_ne_two h.ne_two) (R.isPGroup'.to_inf_left (K := Subgroup.centralizer (E : Set X)))
    hnc
  have hle : B.map ((R : Subgroup X) ⊓ Subgroup.centralizer (E : Set X)).subtype ≤
      Subgroup.zpowers z := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_zpowers_of_mem_centralizer_of_pow_eq_one h hER hcard hexp hZE b.2.1 b.2.2 ?_
    have h1 : (⟨b, hb⟩ : B) ^ p = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p B) ⟨b, hb⟩
    have h2 : b ^ p = 1 := congrArg Subtype.val h1
    exact congrArg Subtype.val h2
  have hcardle := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hBcard, Nat.card_zpowers,
    hzp] at hcardle
  have hp1 := hp.one_lt
  nlinarith [hp.two_le]

end Cyclic

section Action

open CFSG.SectionRank.Ccomm

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def centerQuotientActionNormal (E : Subgroup X) [E.Normal]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) :
    X →* GL (Fin 2) (ZMod p) :=
  (elemAutEquivGL e).toMonoidHom.comp
    ((autQuotient (Subgroup.center E)).comp (MulAut.conjNormal (H := E)))

theorem coe_inv_mul_conjNormal {E : Subgroup X} [E.Normal] (x : X) (u : E) :
    ((u⁻¹ * MulAut.conjNormal x u : E) : X) = (u : X)⁻¹ * (x * u * x⁻¹) := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]

theorem mem_ker_centerQuotientActionNormal {E : Subgroup X} [E.Normal] {z : X}
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) {x : X} :
    x ∈ (centerQuotientActionNormal E e).ker ↔ ∀ u ∈ E, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
  have hzn : (Subgroup.zpowers z).Normal := normal_zpowers_of_center_map hZE
  have key : x ∈ (centerQuotientActionNormal E e).ker ↔
      MulAut.conjNormal (H := E) x ∈ (autQuotient (Subgroup.center E)).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (elemAutEquivGL e) ((autQuotient (Subgroup.center E)) (MulAut.conjNormal x)) = 1 ↔ _
    exact (elemAutEquivGL e).map_eq_one_iff
  have hmem : ∀ v : E, v ∈ Subgroup.center E ↔ (v : X) ∈ Subgroup.zpowers z := fun v => by
    rw [← hZE]
    exact (Subgroup.mem_map_iff_mem E.subtype_injective).symm
  rw [key, mem_ker_autQuotient]
  constructor
  · intro h u hu
    have h1 := (hmem _).mp (h ⟨u, hu⟩)
    rw [coe_inv_mul_conjNormal] at h1
    have := hzn.conj_mem _ h1 u
    convert this using 1
    group
  · intro h u
    rw [hmem, coe_inv_mul_conjNormal]
    have := hzn.conj_mem _ (h u u.2) (u : X)⁻¹
    convert this using 1
    group

theorem centerQuotientActionNormal_eq (E : Subgroup X) [E.Normal]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (g : Subgroup.normalizer (E : Set X)) :
    centerQuotientActionNormal E e (g : X) = centerQuotientAction E e g := by
  have : E.normalizerMonoidHom g = MulAut.conjNormal (H := E) (g : X) := by
    ext u
    rfl
  unfold centerQuotientActionNormal centerQuotientAction
  simp [this]

end Action

theorem layer_eq_bot_of_exists_selfCentralizing {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime]
    (hcon : ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup p Q ∧ Subgroup.centralizer (Q : Set X) ≤ Q) :
    CFSG.layer X = ⊥ := by
  obtain ⟨Q, hQn, hQp, hQc⟩ := hcon
  have hQO : Q ≤ CFSG.pCore p X := le_sSup ⟨hQn, hQp⟩
  exact CFSG.layer_eq_bot_of_isCharacteristicP X p
    ((Subgroup.centralizer_le hQO).trans (hQc.trans hQO))

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.PreuniquenessRankFour.Helpers CFSG.LocalAnalysis.RankThreeTheoremC

theorem ReducedNongeneration.structure_of_layer_eq_bot3
    {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}
    (h : ReducedNongeneration p X R X₀) (hlayer : CFSG.layer X = ⊥) {z : X}
    (hz : z ∈ Subgroup.centralizer ((R : Subgroup X) : Set X)) (hzp : orderOf z = p) :
    Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X ∧
    ∃ E C : Subgroup X, E.Normal ∧ E ≤ CFSG.pCore p X ∧ C ≤ (R : Subgroup X) ∧
      Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
      (Subgroup.center E).map E.subtype = Subgroup.zpowers z ∧
      IsCyclic C ∧ Subgroup.zpowers z ≤ C ∧ (∀ y ∈ C, y ^ p = 1 → y ∈ Subgroup.zpowers z) ∧
      C = (R : Subgroup X) ⊓ Subgroup.centralizer (E : Set X) ∧
      C = CFSG.pCore p X ⊓ Subgroup.centralizer (E : Set X) ∧
      Subgroup.centralizer (E : Set X) = C ∧ E ⊓ C = Subgroup.zpowers z ∧
      E ⊔ C = CFSG.pCore p X ∧ (CFSG.pCore p X).relIndex (R : Subgroup X) = p ∧
      (∀ x : X, x ∈ CFSG.pCore p X ↔ ∀ u ∈ E, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.zpowers z) ∧
      ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
        StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set X)).subgroupOf
          (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e) := by
  have hp := h.prime
  have hQn : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hQp : IsPGroup p (CFSG.pCore p X) := CFSG.pCore_isPGroup
  have hQR : CFSG.pCore p X ≤ (R : Subgroup X) := hQp.le_sylow_of_normal R
  have hQc : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X p h.core_eq_bot hlayer
  refine ⟨hQc, ?_⟩
  obtain ⟨E, hEn, hEQ, hEcard, hEexp, hEZ, e, hSL'⟩ := h.exists_extraspecial_sl_two hQp hQc hz hzp
  have hSL : StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set X)).subgroupOf
      (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e) :=
    statedSL_le_map_centerQuotientAction E _ e fun a ha => by
      obtain ⟨x, hx, hxa⟩ := hSL' a ha
      exact ⟨x, hx, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x, hxa⟩
  have hnc : ∃ a b : E, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact not_forall_mul_comm_of_mulEquiv e hcon
  have hQE := commutator_mem_zpowers_of_normal_pGroup hQp hEQ hEcard hEZ hzp e hSL
  have hQsup : CFSG.pCore p X ≤ E ⊔ Subgroup.centralizer (E : Set X) := fun q hq =>
    mem_sup_centralizer_of_commutator_mem hEcard hnc hEZ (hQE q hq)
  have hERs : E ≤ (R : Subgroup X) := hEQ.trans hQR
  have hcyc := isCyclic_inf_centralizer3 h hERs hEcard hEexp hEZ hzp
  have hCQ := inf_centralizer_le_of_isCyclic3 hEQ hQR hQsup hcyc hQc
  set C : Subgroup X := (R : Subgroup X) ⊓ Subgroup.centralizer (E : Set X) with hC
  have hzE : Subgroup.zpowers z ≤ E := hEZ ▸ Subgroup.map_subtype_le _
  have hCz : Subgroup.zpowers z ≤ C :=
    le_inf (hzE.trans hERs) ((inf_centralizer_eq_of_center_map hEZ).ge.trans inf_le_right)
  have hQC : CFSG.pCore p X ⊓ Subgroup.centralizer (E : Set X) = C :=
    le_antisymm (inf_le_inf_right _ hQR) (le_inf hCQ inf_le_right)
  have hQeq : E ⊔ C = CFSG.pCore p X := by
    have := eq_sup_inf_of_le_sup3 hEQ hQsup
    rw [hQC] at this
    exact this.symm
  have hΩ : ∀ y ∈ C, y ^ p = 1 → y ∈ Subgroup.zpowers z := fun y hy hyp =>
    mem_zpowers_of_mem_centralizer_of_pow_eq_one h hERs hEcard hEexp hEZ hy.1 hy.2 hyp
  have hDC : Subgroup.centralizer (E : Set X) = C := by
    have hDp := isPGroup_centralizer_of_isCyclic hQp hQc hQC hQeq hcyc fun y hy hyp =>
      hzE (hΩ y hy hyp)
    have hDQ : Subgroup.centralizer (E : Set X) ≤ CFSG.pCore p X := le_sSup ⟨inferInstance, hDp⟩
    exact le_antisymm (hQC ▸ le_inf hDQ le_rfl) inf_le_right
  have hker : ∀ x : X, x ∈ CFSG.pCore p X ↔ ∀ u ∈ E, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
    intro x
    refine ⟨hQE x, fun hx => ?_⟩
    have := mem_sup_centralizer_of_commutator_mem hEcard hnc hEZ hx
    rw [hDC, hQeq] at this
    exact this
  have hkerρ : (centerQuotientActionNormal E e).ker = CFSG.pCore p X :=
    Subgroup.ext fun x => (mem_ker_centerQuotientActionNormal hEZ e).trans (hker x).symm
  have hrel : (CFSG.pCore p X).relIndex (R : Subgroup X) =
      Nat.card ((R : Subgroup X).map (centerQuotientActionNormal E e)) := by
    rw [← hkerρ, Subgroup.relIndex_ker]
  have hpg : IsPGroup p ((R : Subgroup X).map (centerQuotientActionNormal E e)) := R.isPGroup'.map _
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk2
    refine CFSG.RankThree.SubgroupLists.not_sq_dvd_card_GL_two (p := p) ?_
    have hdvd : Nat.card ((R : Subgroup X).map (centerQuotientActionNormal E e)) ∣
        Nat.card (GL (Fin 2) (ZMod p)) := Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd
    exact (pow_dvd_pow p (by omega : 2 ≤ k)).trans hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : (CFSG.pCore p X).relIndex (R : Subgroup X) = 1 := by rw [hrel, hk, pow_zero]
    exact h.not_sylow_le_of_normal hQp (Subgroup.relIndex_eq_one.mp h1)
  have hrelp : (CFSG.pCore p X).relIndex (R : Subgroup X) = p := by
    rw [hrel, hk, show k = 1 by omega, pow_one]
  have hEC : E ⊓ C = Subgroup.zpowers z := by
    refine le_antisymm ?_ (le_inf hzE hCz)
    rw [← inf_centralizer_eq_of_center_map hEZ]
    exact inf_le_inf_left _ (hDC ▸ le_rfl)
  exact ⟨E, C, hEn, hEQ, inf_le_left, hEcard, hEexp, hEZ, hcyc, hCz, hΩ, rfl, hQC.symm, hDC, hEC,
    hQeq, hrelp, hker, e, hSL⟩

end CFSG.AGLEmbedding
