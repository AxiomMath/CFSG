module

public import CFSG.GH74.GLS.C3.Layer1.BkGen4L34
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.PU3.Rows

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem psl2_nonabelian {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
  have hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
    refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
    grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at h4
    omega
  by_contra hcomm
  push Not at hcomm
  have htop := SL2Simple.PSL_commutator_eq_top hF
  have hbot : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcomm y x
  exact (bot_ne_top : (⊥ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≠ ⊤)
    (hbot.symm.trans htop)

theorem psl2_data {Y : Type} [Group Y] {p f : ℕ} (h : Blueprint.LieModel Y .PSL 2 p f) :
    IsSimpleGroup Y ∧ (∃ a b : Y, a * b ≠ b * a) ∧ Group.IsSolvable (Outer Y) := by
  rcases h with ⟨-, ⟨hp, hf, -, h22, h23⟩, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · let e' : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      by_contra hlt
      interval_cases hpf : p ^ f
      · exact h22 rfl
      · exact h23 rfl
    have : Finite F := Nat.finite_of_card_ne_zero (by omega)
    refine ⟨?_, ?_, ?_⟩
    · have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
      exact e'.isSimpleGroup
    · obtain ⟨a, b, hab⟩ := psl2_nonabelian h4
      exact ⟨e'.symm a, e'.symm b, fun hc => hab (by simpa using congrArg e' hc)⟩
    · exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv F e'
  all_goals exact absurd h0 (by norm_num)

theorem alt7_data {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) :
    IsSimpleGroup Y ∧ (∃ a b : Y, a * b ≠ b * a) ∧ Group.IsSolvable (Outer Y) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨e.isSimpleGroup, ?_,
    CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_solvable_of_equiv_outside_six
      (Or.inr le_rfl) e⟩
  have hnc : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, ?_⟩, ?_⟩
    · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
    · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
    · decide
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩

theorem l2_data {Y : Type} [Group Y] {P : ℕ → Prop} (h : HasL2Model Y P) :
    IsSimpleGroup Y ∧ (∃ a b : Y, a * b ≠ b * a) ∧ Group.IsSolvable (Outer Y) := by
  obtain ⟨_, _, _, _, _, hL⟩ := h
  exact psl2_data hL

theorem kBar_data
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G}
    {ρ : Th2Row} {B : Subgroup G} (h2 : Th2M2 x y K T S M ρ B) :
    IsSimpleGroup (kBar K) ∧ (∃ a b : kBar K, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (kBar K)) := by
  have hrow := h2.row
  cases ρ
  · exact l2_data hrow.1
  · exact l2_data hrow.1
  · exact l2_data (P := fun q => Odd q ∧ IsFM9 q ∧ q ≠ 5) hrow
  · obtain ⟨e⟩ := hrow.1
    exact alt7_data e
  · obtain ⟨e⟩ := hrow.1
    exact alt7_data e
  · obtain ⟨e⟩ := hrow.1
    exact alt7_data e
  · exact l2_data hrow.1
  · exact l2_data hrow.1
  · exact l2_data hrow.1
  · exact absurd hrow
      (C3.Layer1.Bk.b_gen4_noL34_elem_proof G hG.gen4 x K h2.std.orderOf_x h2.std.comp)

section Bar

variable {G : Type} [Group G]

@[expose] noncomputable def barRestrict {K L : Subgroup G} (hKL : K ≤ L) : ↥K →* kBar L :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (Subgroup.inclusion hKL)

theorem barRestrict_surjective {K L : Subgroup G} (hKL : K ≤ L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) : Function.Surjective (barRestrict hKL) := by
  intro y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : (pPrimeCoreOf 2 L ⊔ K).subgroupOf L = ⊤ := by
    rw [← hLeq]
    exact Subgroup.subgroupOf_self L
  rw [Subgroup.subgroupOf_sup (TwoThin.pPrimeCoreOf_le L) hKL] at h1
  have h2 : (pPrimeCoreOf 2 L).subgroupOf L = pPrimeCore 2 ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h2] at h1
  have hl : l ∈ pPrimeCore 2 ↥L ⊔ K.subgroupOf L := by rw [h1]; exact Subgroup.mem_top l
  obtain ⟨n, hn, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hl
  refine ⟨⟨k, hk⟩, ?_⟩
  show (QuotientGroup.mk (Subgroup.inclusion hKL ⟨k, hk⟩) : kBar L) = QuotientGroup.mk (n * k)
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
  rfl

theorem barRestrict_ker [Finite G] {K L : Subgroup G} (hKL : K ≤ L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) : (barRestrict hKL).ker = pPrimeCore 2 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg := barRestrict_surjective hKL hLeq
  apply le_antisymm
  · have hcomap : (barRestrict hKL).ker = (pPrimeCore 2 ↥L).comap (Subgroup.inclusion hKL) := by
      ext k
      simp [barRestrict, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    have hcop : Nat.Coprime 2 (Nat.card (barRestrict hKL).ker) := by
      rw [hcomap]
      exact Nat.Coprime.coprime_dvd_right
        (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hKL))
        CFSG.pPrimeCore_coprime_card
    exact CFSG.GroupTheory.le_pPrimeCore_of_normal inferInstance hcop
  · intro k hk
    have hle := CFSG.Semidihedral.OddCoreQuotient.pPrimeCore_map_le_of_surjective 2
      (barRestrict hKL) hg
    have h2 : (barRestrict hKL) k ∈ pPrimeCore 2 (kBar L) := hle (Subgroup.mem_map_of_mem _ hk)
    rw [CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥L, Subgroup.mem_bot] at h2
    exact h2

theorem kBar_equiv [Finite G] {K L : Subgroup G} (hKL : K ≤ L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) : Nonempty (kBar L ≃* kBar K) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (barRestrict_surjective hKL hLeq)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (barRestrict_ker hKL hLeq))⟩

theorem two_le_pRank_of_kBar [Finite G] {L : Subgroup G} (hs : IsSimpleGroup (kBar L))
    (hnc : ∃ a b : kBar L, a * b ≠ b * a) : 2 ≤ pRank 2 ↥L := by
  have := hs
  have h1 : 2 ≤ pRank 2 (kBar L) :=
    CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hnc)
      (by
        rw [CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc,
          Subgroup.card_bot]
        exact odd_one)
  have h2 : pRank 2 (kBar L) = pRank 2 ↥L :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 CFSG.pPrimeCore_coprime_card)
  omega

end Bar

end CFSG.GH74.GLS.PU3.Rows

namespace CFSG.GH74.GLS.PU3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem rows_data
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K T S M : Subgroup G}
    {ρ : Th2Row} {B : Subgroup G}
    (h2 : Th2M2 x y K T S M ρ B) (_hKM : K ≤ M) {L : Subgroup G}
    (hL : IsMinSubnormalIn K M L) (_hLcomp : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) :
    IsSimpleGroup (kBar L) ∧ (∃ a b : kBar L, a * b ≠ b * a) ∧ 2 ≤ pRank 2 ↥L ∧
      Group.IsSolvable (Outer (kBar L)) := by
  obtain ⟨hs, hnc, hout⟩ := Rows.kBar_data hG h2
  obtain ⟨e⟩ := Rows.kBar_equiv hL.1 hLeq
  have := hs
  have := hout
  have hsL : IsSimpleGroup (kBar L) := e.isSimpleGroup
  have hncL : ∃ a b : kBar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  exact ⟨hsL, hncL, Rows.two_le_pRank_of_kBar hsL hncL,
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm⟩

end CFSG.GH74.GLS.PU3
