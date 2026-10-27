module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup

@[expose] def IsDoublePair {X : Type*} [Group X] (x : X) (L : Subgroup X) (m : ℕ) : Prop :=
  orderOf x = 2 ∧ L ≤ centralizer ({x} : Set X) ∧
    IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) ∧ Odd m ∧ 7 ≤ m ∧
    Open.fusionZStar L ≠ pPrimeCore 2 L ∧
    Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin m))

theorem fusionZStar_eq_comap (L : Type*) [Group L] :
    Open.fusionZStar L =
      (center (L ⧸ pPrimeCore 2 L)).comap (QuotientGroup.mk' (pPrimeCore 2 L)) := by
  have h : Open.fusionOddCore L = pPrimeCore 2 L := by
    unfold Open.fusionOddCore pPrimeCore
    congr 1
    ext K
    simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
  have key : ∀ (N N' : Subgroup L) [N.Normal] [N'.Normal], N = N' →
      (center (L ⧸ N)).comap (QuotientGroup.mk' N) =
        (center (L ⧸ N')).comap (QuotientGroup.mk' N') := by
    intro N N' _ _ hN
    subst hN
    rfl
  exact key _ _ h

theorem oddCore_eq_pPrimeCore (G : Type*) [Group G] : CFSG.oddCore G = pPrimeCore 2 G := by
  unfold CFSG.oddCore pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem pPrimeCore_le_fusionZStar (L : Type*) [Group L] :
    pPrimeCore 2 L ≤ Open.fusionZStar L := by
  rw [fusionZStar_eq_comap]
  intro l hl
  rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff l).mpr hl]
  exact one_mem _

theorem fusionZStar_eq_iff (L : Type*) [Group L] :
    Open.fusionZStar L = pPrimeCore 2 L ↔ center (L ⧸ pPrimeCore 2 L) = ⊥ := by
  rw [fusionZStar_eq_comap]
  constructor
  · intro h
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) q
    have hl : l ∈ (center (L ⧸ pPrimeCore 2 L)).comap (QuotientGroup.mk' (pPrimeCore 2 L)) :=
      hq
    rw [h] at hl
    rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hl
  · intro h
    rw [h, MonoidHom.comap_bot, QuotientGroup.ker_mk']

noncomputable def coreQuotientCenterEquiv (L : Type*) [Group L] :
    (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃* L ⧸ Open.fusionZStar L :=
  (QuotientGroup.quotientMulEquivOfEq
      (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 L))
        (center (L ⧸ pPrimeCore 2 L))).symm).trans
    ((QuotientGroup.quotientQuotientEquivQuotient _ _ (by
        intro l hl
        rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff l).mpr hl]
        exact one_mem _)).trans
      (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_comap L).symm))

theorem alt_nonabelian {m : ℕ} (hm : 4 ≤ m) :
    ∃ a b : alternatingGroup (Fin m), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hZ : center (alternatingGroup (Fin m)) = ⊤ :=
    eq_top_iff.2 fun a _ => mem_center_iff.2 fun b => h b a
  rw [alternatingGroup.center_eq_bot (by simpa using hm)] at hZ
  have : Nontrivial (alternatingGroup (Fin m)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  exact bot_ne_top hZ

theorem alt_isPerfect {m : ℕ} (hm : 5 ≤ m) : Group.IsPerfect (alternatingGroup (Fin m)) := by
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  exact (LocalCores.isQuasisimple_of_isSimpleGroup (alt_nonabelian (by omega))).1.1

theorem map_center_eq_of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (center Q).map e.toMonoidHom = center Q' := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hz
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    change e g' * e z = e z * e g'
    rw [← map_mul, ← map_mul, hz g']
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_center_iff] at hy
    rw [SetLike.mem_coe, mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy (e g)]

noncomputable def centerQuotCongr {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    Q ⧸ center Q ≃* Q' ⧸ center Q' :=
  QuotientGroup.congr _ _ e (map_center_eq_of_mulEquiv e)

noncomputable def coreQuotCongr {P R : Type*} [Group P] [Group R] (e : P ≃* R) :
    P ⧸ pPrimeCore 2 P ≃* R ⧸ pPrimeCore 2 R :=
  QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)

noncomputable def fusionZStarQuotOfCore {P R : Type*} [Group P] [Group R]
    (φ : P ⧸ pPrimeCore 2 P ≃* R ⧸ pPrimeCore 2 R) :
    P ⧸ Open.fusionZStar P ≃* R ⧸ Open.fusionZStar R :=
  (coreQuotientCenterEquiv P).symm.trans ((centerQuotCongr φ).trans (coreQuotientCenterEquiv R))

noncomputable def fusionZStarQuotCongr {P R : Type*} [Group P] [Group R] (e : P ≃* R) :
    P ⧸ Open.fusionZStar P ≃* R ⧸ Open.fusionZStar R :=
  fusionZStarQuotOfCore (coreQuotCongr e)

theorem center_isPGroup_two {Q : Type*} [Group Q] [Finite Q] (h : pPrimeCore 2 Q = ⊥) :
    IsPGroup 2 (center Q) := by
  intro z
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨k, ?_⟩
  set w : center Q := z ^ 2 ^ k with hw
  have hwm : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  have hle : (zpowers (w : Q)) ≤ pPrimeCore 2 Q := by
    have hc : zpowers (w : Q) ≤ center Q := zpowers_le.mpr w.2
    refine le_sSup ⟨normal_of_le_center hc, ?_⟩
    rw [Nat.card_zpowers, orderOf_submonoid, hwm]
    exact Nat.coprime_two_left.mpr hm
  rw [h, le_bot_iff, zpowers_eq_bot] at hle
  exact Subtype.ext hle

theorem card_center_le_two (hS : SolAltLit.SchurAlternatingMultiplierInput) {Q : Type*}
    [Group Q] [Finite Q] [Group.IsPerfect Q] (hO : pPrimeCore 2 Q = ⊥) {m : ℕ} (hm : 5 ≤ m)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin m)) : Nat.card (center Q) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (alternatingGroup (Fin m)) := alt_isPerfect hm
  set p : Q →* alternatingGroup (Fin m) := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
    with hpdef
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : p.ker = center Q := by
    ext x
    rw [MonoidHom.mem_ker, hpdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨-, h, -, -, -, hmap, -⟩ :=
    RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier p hp
      (hker ▸ le_rfl)
  obtain ⟨-, hcardM⟩ := hS m hm
  have hfin : Finite (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin m))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardM]; split_ifs <;> norm_num)
  have hdvd : Nat.card p.ker ∣
      Nat.card (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin m))) := by
    rw [← hmap]
    exact Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective h _)
  have h6 : Nat.card p.ker ∣ 6 := by
    rw [hcardM] at hdvd
    split_ifs at hdvd with h67
    · exact hdvd
    · exact dvd_trans hdvd (by norm_num)
  rw [hker] at h6
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (center_isPGroup_two hO)
  rw [hk] at h6 ⊢
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have := dvd_trans this h6
    norm_num at this
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num

variable {X : Type*} [Group X] [Finite X]

theorem IsDoublePair.coreQuotient (hS : SolAltLit.SchurAlternatingMultiplierInput) {x : X}
    {L : Subgroup X} {m : ℕ} (hP : IsDoublePair x L m) :
    Group.IsPerfect (L ⧸ pPrimeCore 2 L) ∧ IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
      Nat.card (center (L ⧸ pPrimeCore 2 L)) = 2 ∧
      Nonempty ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃*
        alternatingGroup (Fin m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLx, hL, -, hm7, hne, ⟨e⟩⟩ := hP
  have hq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hLx)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hL)
  have hperf : Group.IsPerfect (L ⧸ pPrimeCore 2 L) := hq.1
  let e' := (coreQuotientCenterEquiv L).trans e
  have hle := card_center_le_two hS (pPrimeCore_quotient_pPrimeCore_eq_bot 2) (by omega) e'
  have hne' : center (L ⧸ pPrimeCore 2 L) ≠ ⊥ := fun h => hne ((fusionZStar_eq_iff L).mpr h)
  have hge : 2 ≤ Nat.card (center (L ⧸ pPrimeCore 2 L)) := by
    by_contra h
    apply hne'
    exact Subgroup.eq_bot_of_card_le _ (by omega)
  exact ⟨hperf, hq, le_antisymm hle hge, ⟨e'⟩⟩

end CFSG.ComponentClassification.Sol78
