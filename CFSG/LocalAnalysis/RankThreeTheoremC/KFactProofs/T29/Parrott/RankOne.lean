module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Assembly
public import CFSG.LocalAnalysis.GL83PartI.I713.Linear
public import CFSG.LocalAnalysis.GL83PartI.I713.Unitary
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL3
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section RankOne

theorem pRank_le_one_of_card_le {G : Type*} [Group G] [Finite G]
    (h : ∀ E : Subgroup G, IsElemAbelian 3 E → Nat.card E ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 1 :=
  CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => by simpa using h E hE

theorem card_le_three_of_sylow_isCyclic {G : Type*} [Group G] [Finite G]
    (hcyc : ∀ R : Sylow 3 G, IsCyclic R) {E : Subgroup G} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨R, hER⟩ := hEp.exists_le_sylow
  haveI := hcyc R
  haveI : IsCyclic E := by
    have : IsCyclic ↥(E.subgroupOf (R : Subgroup G)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hER).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hER).surjective
  exact card_le_three_of_cyclic (W := E) fun w => Subtype.ext (by simpa using hE.2 w w.2)

theorem exists_lift_elemAbelian {G H : Type*} [Group G] [Group H] [Finite G] {π : G →* H}
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) {E : Subgroup H}
    (hE : IsElemAbelian 3 E) : ∃ F : Subgroup G, IsElemAbelian 3 F ∧ Nat.card F = Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite H := Finite.of_surjective π hπ
  have hEp : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hπ 3 Q
  rw [Sylow.coe_mapSurjective] at hEQ
  have hinjS : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), π a = π b → a = b := by
    intro a ha b hb hab
    have hm : a * b⁻¹ ∈ (S : Subgroup G) ⊓ π.ker := by
      refine Subgroup.mem_inf.2 ⟨mul_mem ha (inv_mem hb), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    have hp : IsPGroup 3 ↥((S : Subgroup G) ⊓ π.ker) := S.isPGroup'.to_le inf_le_left
    have hbot : (S : Subgroup G) ⊓ π.ker = ⊥ := by
      by_contra hne
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hne ((Subgroup.card_eq_one).1 (by simpa using hk))
      exact hker ((hk ▸ dvd_pow_self 3 hk0 : 3 ∣ Nat.card ↥((S : Subgroup G) ⊓ π.ker)).trans
        (Subgroup.card_dvd_of_le inf_le_right))
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hm
  set F : Subgroup G := E.comap π ⊓ (S : Subgroup G)
  refine ⟨F, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · show (a : G) * b = (b : G) * a
    refine hinjS _ (mul_mem a.2.2 b.2.2) _ (mul_mem b.2.2 a.2.2) ?_
    rw [map_mul, map_mul]
    exact hE.comm a.2.1 b.2.1
  · refine hinjS _ (pow_mem ha.2 3) _ (one_mem _) ?_
    rw [map_pow, map_one]
    exact hE.2 _ ha.1
  · have hbij : Function.Bijective (fun x : F => (⟨π x, x.2.1⟩ : E)) := by
      refine ⟨fun x y hxy => Subtype.ext (hinjS _ x.2.2 _ y.2.2
        (congrArg Subtype.val hxy)), ?_⟩
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := hEQ hy
      exact ⟨⟨x, hy, hx⟩, rfl⟩
    exact Nat.card_congr (Equiv.ofBijective _ hbij)

theorem pRank_top_le_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {π : G →* H} (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) :
    CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup H)
  obtain ⟨F, hF, hFc⟩ := exists_lift_elemAbelian hπ hker hE
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hF (hFc.trans hcard)

theorem pRank_projSL_two_le_one {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (hF7 : 7 ≤ Nat.card F) (hp3 : p ≠ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 2 F))) ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card F) := by
    rw [hF]
    exact Nat.Coprime.pow_right f ((Nat.coprime_primes Nat.prime_three Fact.out).2 (Ne.symm hp3))
  have hcyc := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF hF7 3
    (by norm_num) hcop
  let e := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact pRank_le_one_of_card_le fun E hE => card_le_three_of_sylow_isCyclic hcyc hE

theorem not_three_dvd_card_ker_projSL_three {F : Type} [Field F] [Finite F]
    (h1 : ¬ 3 ∣ Nat.card F - 1) :
    ¬ 3 ∣ Nat.card
      (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))).ker := by
  rw [QuotientGroup.ker_mk']
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 x.2
  have hdet : ((x : ↥(StatedSL 3 F)) : GL (Fin 3) F).val.det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL (x : ↥(StatedSL 3 F)).2
  have hc3 : (c : F) ^ 3 = 1 := by
    rw [← hc] at hdet
    simpa [Matrix.det_smul] using hdet
  have hcu : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  have hord : orderOf c ∣ Nat.gcd 3 (Nat.card F - 1) := by
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcu) ?_
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard c
  have hg : Nat.gcd 3 (Nat.card F - 1) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (Nat.card F - 1)) with h | h
    · exact h
    · exact absurd (h ▸ Nat.gcd_dvd_right 3 (Nat.card F - 1)) h1
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hord
  have hx1 : x = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [← hc, hord, map_one]
    rfl
  rw [hx1, orderOf_one] at hx
  omega

theorem pRank_projSL_three_le_one {F : Type} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ e) (hq : p ^ e % 3 = 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 F))) ≤ 1 := by
  have hSL := CFSG.RankThree.PartTwo.Sec4.Res417Four.pRank_statedSL_three_le_one hF hq
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hSL
  refine (pRank_top_le_of_surjective (QuotientGroup.mk'_surjective _)
    (not_three_dvd_card_ker_projSL_three ?_)).trans hSL
  rw [hF]
  omega

theorem not_three_dvd_card_ker_projSU_three {F : Type} [Field F] {p e : ℕ}
    (h : UnitaryFieldData p e F) (h3 : ¬ 3 ∣ p ^ e + 1) :
    ¬ 3 ∣ Nat.card (QuotientGroup.mk'
      ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ e) F))).ker := by
  have := h.finite
  rw [QuotientGroup.ker_mk']
  intro hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  obtain ⟨l, hl⟩ := Subgroup.mem_subgroupOf.1 x.2
  have hl' : Matrix.GeneralLinearGroup.scalar (Fin 3) l ∈ StatedSU 3 (p ^ e) F := by
    rw [hl]
    exact (x : ↥(StatedSU 3 (p ^ e) F)).2
  obtain ⟨hdet, hunit⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp hl'
  have hl3 : (l : F) ^ 3 = 1 := by
    have : (Matrix.scalar (Fin 3) (l : F)).det = 1 := by simpa using hdet
    simpa [Matrix.det_smul] using this
  have hlq : (l : F) ^ (p ^ e + 1) = 1 := by
    have h00 := congrFun (congrFun hunit 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, UnitaryFieldData.bar_apply] at h00
    rw [pow_succ]
    exact h00
  have hpow : ∀ k : ℕ, (l : F) ^ k = (l : F) ^ (k % 3) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hl3, one_pow, one_mul]
  have hl1 : (l : F) = 1 := by
    rw [hpow] at hlq
    rcases (show (p ^ e + 1) % 3 = 1 ∨ (p ^ e + 1) % 3 = 2 by omega) with h1 | h1
    · rw [h1, pow_one] at hlq
      exact hlq
    · rw [h1] at hlq
      have h32 : (l : F) ^ 3 = (l : F) ^ 2 * l := by ring
      rw [hl3, hlq, one_mul] at h32
      exact h32.symm
  have hx1 : x = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [← hl, show l = 1 from Units.ext hl1, map_one]
    rfl
  rw [hx1, orderOf_one] at hx
  omega

theorem pRank_projSU_three_le_one {F : Type} [Field F] {p e : ℕ} (h : UnitaryFieldData p e F)
    (hq : p ^ e % 3 = 1) :
    letI := h.finite
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 (p ^ e) F))) ≤ 1 := by
  letI := h.finite
  have hSU := CFSG.RankThree.PartTwo.Sec4.Res417Four.pRank_statedSU_three_le_one h hq
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hSU
  exact (pRank_top_le_of_surjective (QuotientGroup.mk'_surjective _)
    (not_three_dvd_card_ker_projSU_three h (by omega))).trans hSU

end RankOne

section Aut

theorem pRank_mulAut_le_two_of_outClause {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hK : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 1)
    (hO : GL83.I713.OutClauseFor K) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have h1 := GL83.I713.pRank_mulAut_le Nat.prime_three (GL83.I713.center_eq_bot_of_simple hnab)
  have h2 := hO 3 Nat.prime_three (by norm_num) hK
  omega

theorem rankOneAut_holds : RankOneAut := by
  intro d hch hd K _ _ hs hnab ⟨e⟩
  obtain ⟨dd, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  rw [LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  cases dd with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_A] using hch
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    refine pRank_mulAut_le_two_of_outClause hnab ?_ (GL83.I713.outClauseFor_classical_PSL hm)
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := hm
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) f]
    rcases hd with rfl | ⟨rfl, hq⟩
    · have h4 : 4 ≤ q.card := hr.2 rfl
      have hnd : ¬ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9) := fun h =>
        hdup (Or.inl ⟨rfl, h⟩)
      have h6 : q.card ≠ 6 := by
        intro h6
        have hpp := q.isPrimePow_card
        rw [h6] at hpp
        exact absurd hpp (by decide)
      have hF7 : 7 ≤ Nat.card F := by
        rw [hF, ← PrimePower.card_def]
        omega
      exact pRank_projSL_two_le_one hF hF7 hp3
    · exact pRank_projSL_three_le_one hF (by rw [← PrimePower.card_def]; exact hq)
  | twistedA r q =>
    obtain ⟨rfl, hq⟩ := hd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    refine pRank_mulAut_le_two_of_outClause hnab ?_ (GL83.I713.outClauseFor_classical_PSU hnab hm)
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := hm
    have hU : UnitaryFieldData q.p q.exponent F :=
      ⟨q.prime_p, q.exponent_pos, by rw [hF, ← pow_mul, mul_comm]⟩
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) f]
    exact pRank_projSU_three_le_one hU (by rw [← PrimePower.card_def]; exact hq)
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | reeF4 k => exact hd.elim
  | tits => exact hd.elim

end Aut

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
