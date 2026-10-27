module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Four

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

section S3cGeneric

variable {X : Type*} [Group X]

theorem s39c_injective_mk' (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) :
    Function.Injective ((QuotientGroup.mk' O).comp Q.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxO : (x : X) ∈ O := (QuotientGroup.eq_one_iff _).1 hx
  obtain ⟨k, hk⟩ := hQ x
  have h1 : orderOf (x : X) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf (x : X) ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨x, hxO⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2))

theorem s39c_card_map_mk' (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) :
    Nat.card (Q.map (QuotientGroup.mk' O)) = Nat.card Q := by
  have hinj := s39c_injective_mk' O hO hQ
  have hr : ((QuotientGroup.mk' O).comp Q.subtype).range = Q.map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem s39c_card_le_two_of_sylow [Finite X] {C : Subgroup X} {z : X} (hz : orderOf z = 2)
    (S₀ : Sylow 2 C) (hS₀ : (S₀ : Subgroup C).map C.subtype = zpowers z)
    {Q : Subgroup X} (hQC : Q ≤ C) (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf C) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  have hSc : Nat.card (S : Subgroup C) = 2 := by
    rw [Nat.card_congr (Sylow.equiv S S₀).toEquiv,
      ← card_map_of_injective (subtype_injective _), hS₀, Nat.card_zpowers, hz]
  rw [← Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv]
  exact (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hS)).trans hSc.le

theorem s39c_card_eq_mul_map [Finite X] (O : Subgroup X) [O.Normal] (A : Subgroup X) :
    ∃ m : ℕ, m ∣ Nat.card O ∧ Nat.card A = m * Nat.card (A.map (QuotientGroup.mk' O)) := by
  set φ : A →* X ⧸ O := (QuotientGroup.mk' O).comp A.subtype with hφ
  have hrange : φ.range = A.map (QuotientGroup.mk' O) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  refine ⟨Nat.card φ.ker, ?_, ?_⟩
  · have hker : φ.ker.map A.subtype ≤ O := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hx
    rw [← card_map_of_injective A.subtype_injective]
    exact Subgroup.card_dvd_of_le hker
  · rw [← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem s39c_not_isPGroup_of_simple {Z : Type*} [Group Z] [Finite Z] [IsSimpleGroup Z]
    (hnab : ∃ x y : Z, x * y ≠ y * x) : ¬ IsPGroup 2 Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hZ
  have : Nontrivial Z := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨⟨x * y, y * x, hxy⟩⟩
  have h1 := CFSG.ComponentClassification.Helpers.center_eq_bot Z hnab
  have h2 := hZ.center_nontrivial
  rw [h1] at h2
  exact not_nontrivial (⊥ : Subgroup Z) h2

theorem s39c_pgroup_normal_in_prod_eq_bot [Finite X] {D D₁ D₂ Y : Subgroup X}
    (hD : D₁ ⊔ D₂ = D) (hcomm : ⁅D₁, D₂⁆ = ⊥)
    (hs₁ : IsSimpleGroup D₁) (hn₁ : ∃ x y : D₁, x * y ≠ y * x)
    (hs₂ : IsSimpleGroup D₂) (hn₂ : ∃ x y : D₂, x * y ≠ y * x)
    (hC : centralizer (D : Set X) = ⊥)
    (hYD : Y ≤ D) (hY : IsPGroup 2 Y) (hYn : ∀ g ∈ D, g ∈ normalizer (Y : Set X)) : Y = ⊥ := by
  have hcomm' : D₁ ≤ centralizer (D₂ : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hcomm'' : D₂ ≤ centralizer (D₁ : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 ((Subgroup.commutator_comm D₂ D₁).trans hcomm)
  have hN₁ : D ≤ normalizer (D₁ : Set X) := by
    rw [← hD]
    refine sup_le Subgroup.le_normalizer (fun b hb => ?_)
    refine mem_normalizer_fintype fun a ha => ?_
    have e : b * a * b⁻¹ = a := by
      rw [← mem_centralizer_iff.1 (hcomm'' hb) a ha]; group
    rw [e]
    exact ha
  have hN₂ : D ≤ normalizer (D₂ : Set X) := by
    rw [← hD]
    refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
    refine mem_normalizer_fintype fun b hb => ?_
    have e : a * b * a⁻¹ = b := by
      rw [← mem_centralizer_iff.1 (hcomm' ha) b hb]; group
    rw [e]
    exact hb
  have key : ∀ (Di : Subgroup X), Di ≤ D → D ≤ normalizer (Di : Set X) → IsSimpleGroup Di →
      (∃ x y : Di, x * y ≠ y * x) → Di ≤ centralizer (Y : Set X) := by
    intro Di hDiD hDin hsi hni
    have hnorm : Di ≤ normalizer ((Y ⊓ Di : Subgroup X) : Set X) := by
      intro g hg
      refine mem_normalizer_fintype fun y hy => ?_
      obtain ⟨hyY, hyD⟩ := Subgroup.mem_inf.1 hy
      exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hYn g (hDiD hg)) y).1 hyY,
        (mem_normalizer_iff.1 (hDin (hDiD hg)) y).1 hyD⟩
    have hbot : Y ⊓ Di = ⊥ := by
      haveI := hsi
      haveI : ((Y ⊓ Di).subgroupOf Di).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hnorm
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y ⊓ Di).subgroupOf Di) with h0 | h0
      · rw [eq_bot_iff]
        intro x hx
        have hxD : x ∈ Di := (Subgroup.mem_inf.1 hx).2
        have : (⟨x, hxD⟩ : Di) ∈ (Y ⊓ Di).subgroupOf Di := hx
        rw [h0, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      · exfalso
        have hDiY : Di ≤ Y := fun x hx => by
          have : (⟨x, hx⟩ : Di) ∈ (Y ⊓ Di).subgroupOf Di := by rw [h0]; exact mem_top _
          exact (Subgroup.mem_inf.1 this).1
        exact s39c_not_isPGroup_of_simple hni (hY.to_le hDiY)
    intro x hx
    refine mem_centralizer_iff.2 fun y hy => ?_
    have hyD : y ∈ D := hYD hy
    have hc : y * x * y⁻¹ * x⁻¹ ∈ Y ⊓ Di := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h1 : x * y⁻¹ * x⁻¹ ∈ Y :=
          (mem_normalizer_iff.1 (hYn x (hDiD hx)) y⁻¹).1 (inv_mem hy)
        have e : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
        rw [e]
        exact mul_mem hy h1
      · have h1 : y * x * y⁻¹ ∈ Di := (mem_normalizer_iff.1 (hDin hyD) x).1 hx
        exact mul_mem h1 (inv_mem hx)
    rw [hbot, Subgroup.mem_bot] at hc
    calc y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
      _ = x * y := by rw [hc, one_mul]
  have hY1 := key D₁ (hD ▸ le_sup_left) hN₁ hs₁ hn₁
  have hY2 := key D₂ (hD ▸ le_sup_right) hN₂ hs₂ hn₂
  have hDY : D ≤ centralizer (Y : Set X) := hD ▸ sup_le hY1 hY2
  have hYC : Y ≤ centralizer (D : Set X) := fun y hy =>
    mem_centralizer_iff.2 fun g hg => (mem_centralizer_iff.1 (hDY hg) y hy).symm
  rw [hC] at hYC
  exact le_bot_iff.1 hYC

theorem s39c_dvd_map [Finite X] (O : Subgroup X) [O.Normal] (A : Subgroup X) {m : ℕ}
    (hm : Nat.Coprime m (Nat.card O)) (hA : m ∣ Nat.card A) :
    m ∣ Nat.card (A.map (QuotientGroup.mk' O)) := by
  obtain ⟨m', hm', hcard⟩ := s39c_card_eq_mul_map O A
  rw [hcard] at hA
  exact (hm.coprime_dvd_right hm').dvd_of_dvd_mul_left hA

end S3cGeneric

section S3cStd

variable {X : Type} [Group X] [Finite X]

theorem s39c_std_quotient {A : Subgroup X} {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Fintype k]
    (hk : Fintype.card k = 2 ^ n) (φ : A ≃* SL(2, k)) {t : X} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set X))
    (hAn : (A.subgroupOf (centralizer ({t} : Set X))).Normal)
    (hrank : ∀ P : Subgroup X, P ≤ centralizer (A : Set X) → IsPGroup 2 P → Nat.card P ≤ 2) :
    Nonempty (↥(A.map (QuotientGroup.mk' (standardComponentOddCore X))) ≃* SL(2, k)) ∧
    orderOf (QuotientGroup.mk' (standardComponentOddCore X) t) = 2 ∧
    (∀ Q : Subgroup (X ⧸ standardComponentOddCore X),
      Q ≤ centralizer (((A.map (QuotientGroup.mk' (standardComponentOddCore X)) :
        Subgroup (X ⧸ standardComponentOddCore X)) : Set (X ⧸ standardComponentOddCore X))) →
      IsPGroup 2 Q → Nat.card Q ≤ 2) ∧
    ¬ 2 ∣ (zpowers (QuotientGroup.mk' (standardComponentOddCore X) t)).relIndex
      (centralizer (((A.map (QuotientGroup.mk' (standardComponentOddCore X)) :
        Subgroup (X ⧸ standardComponentOddCore X)) : Set (X ⧸ standardComponentOddCore X)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := GMSK.two_eq_zero_of_card (K := k) (by omega) hk
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
    GMSK.sl2_isSimpleGroup h2 (hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n))
  have : IsSimpleGroup A := φ.isSimpleGroup
  have hnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
    exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩
  have hE : ∃ E : Subgroup X, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hE4⟩ := GMSK.exists_elementaryAbelian_four h2
      (hk ▸ pow_dvd_pow 2 hn : 2 ^ 2 ∣ Fintype.card k)
    set f' : Multiplicative k →* X :=
      A.subtype.comp (φ.symm.toMonoidHom.comp (GMSK.sl2Upper k))
    have hf : Function.Injective f' :=
      A.subtype_injective.comp (φ.symm.injective.comp GMSK.sl2Upper_injective)
    have hEf : CFSG.IsElementaryAbelian 2 (E.map f') := CFSG.IsElementaryAbelian.map f'
    refine ⟨E.map f', ?_, ⟨hEf.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, by rw [card_map_of_injective hf, hE4]⟩
    rintro _ ⟨x, -, rfl⟩
    exact (φ.symm (GMSK.sl2Upper k x)).2
  have hAt : A ≤ centralizer ({t} : Set X) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htA a ha)
  obtain ⟨hinj, -, hθt, -, -, -, -, -, -, -, ⟨S₀, hS₀⟩, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab hE ht hAt hAn (GMSK.exists_sylow_inf_centralizer_eq_zpowers ht htA hrank)
      (standardComponentOddCore X) (GMSK.odd_card_standardComponentOddCore _)
  refine ⟨⟨?_⟩, hθt, fun Q hQC hQ2 => ?_, ?_⟩
  · refine (MulEquiv.ofBijective ((QuotientGroup.mk' (standardComponentOddCore X)).subgroupMap A)
      ⟨fun x y hxy => ?_, (QuotientGroup.mk' (standardComponentOddCore X)).subgroupMap_surjective A⟩).symm.trans φ
    exact Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
  · exact s39c_card_le_two_of_sylow hθt S₀ hS₀ hQC hQ2
  · have hsub : (zpowers (QuotientGroup.mk' (standardComponentOddCore X) t)).subgroupOf
        (centralizer (((A.map (QuotientGroup.mk' (standardComponentOddCore X)) :
          Subgroup (X ⧸ standardComponentOddCore X)) : Set (X ⧸ standardComponentOddCore X)))) =
        (S₀ : Subgroup _) := by
      rw [← hS₀, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        (Subgroup.subtype_injective _)]
    rw [Subgroup.relIndex, hsub]
    exact S₀.not_dvd_index

theorem s39c_not_normal_of_card {A : Subgroup X} {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k]
    [Fintype k] (hk : Fintype.card k = 2 ^ n) (φ : A ≃* SL(2, k)) {t : X} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set X))
    (hAn : (A.subgroupOf (centralizer ({t} : Set X))).Normal)
    (hrank : ∀ P : Subgroup X, P ≤ centralizer (A : Set X) → IsPGroup 2 P → Nat.card P ≤ 2)
    {P : Subgroup X} (hP : IsPGroup 2 P) (hcard : 2 * (2 ^ n * n) < Nat.card P) :
    ¬ (A.map (QuotientGroup.mk' (standardComponentOddCore X))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hN
  obtain ⟨⟨e⟩, -, hC, -⟩ := s39c_std_quotient hn hk φ ht htA hAn hrank
  have hOodd : Odd (Nat.card (standardComponentOddCore X)) :=
    GMSK.odd_card_standardComponentOddCore _
  set Pt : Subgroup (X ⧸ standardComponentOddCore X) :=
    P.map (QuotientGroup.mk' (standardComponentOddCore X)) with hPt
  have hPtpg : IsPGroup 2 Pt := hP.map _
  have hcardPt : Nat.card Pt = Nat.card P := s39c_card_map_mk' _ hOodd hP
  haveI : (A.map (QuotientGroup.mk' (standardComponentOddCore X))).Normal := hN
  have hdvd := GMSK.Sporadic.card_dvd_of_normal_sl2
    (A.map (QuotientGroup.mk' (standardComponentOddCore X))) (n := n) (by omega) hk e Pt hPtpg
  have hC2 := hC _ inf_le_right (hPtpg.to_inf_left)
  have hPle : Nat.card Pt ≤ 2 * (2 ^ n * n) :=
    (Nat.le_of_dvd (Nat.mul_pos Nat.card_pos (Nat.mul_pos (by positivity) (by omega))) hdvd).trans
      (Nat.mul_le_mul_right _ hC2)
  rw [hcardPt] at hPle
  omega

end S3cStd

section S3cOrders

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39c_t_mem_B₆ (hp : d.CaseHyp) : d.t ∈ d.B₆ :=
  hp.hyp.F_sup_B₃_le_B₆ (mem_sup_right (mem_sup_left (mem_zpowers d.t)))

theorem s39c_t_not_mem_D (hi : d.Sec39Input) : d.t ∉ d.D := by
  intro ht
  have h1 : proj d.D ⟨d.t, hi.t_mem⟩ = 1 := proj_eq_one_iff.2 ht
  have h2 := hi.order_two
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem s39c_D_le_B₆ (he : d.Sec39e) : d.D ≤ d.B₆ :=
  ((he.maximal d.D).2 (Or.inr rfl)).prop.2.1

theorem s39c_card_D_le (hp : d.CaseHyp) (he : d.Sec39e) (hi : d.Sec39Input) :
    Nat.card d.D ≤ (2 ^ f) ^ 16 := by
  have hDB := s39c_D_le_B₆ he
  have hB6 : Nat.card d.B₆ = 2 * (2 ^ f) ^ 16 := by
    rw [hp.hyp.card_B₆ hp.gms, hp.hyp.card_FB₃ hp.gms]
    ring
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hDB
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (Nat.card_pos (α := d.B₆)).ne' hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    have hDeq : d.D = d.B₆ := Subgroup.eq_of_le_of_card_ge hDB hm.le
    exact s39c_t_not_mem_D hi (hDeq ▸ s39c_t_mem_B₆ hp)
  have hm2 : 2 ≤ m := by omega
  rw [hB6] at hm
  nlinarith [Nat.card_pos (α := d.D)]

theorem s39c_exists_sylow_L₂ (hp : d.CaseHyp) :
    ∃ S : Subgroup G, IsSylowOf 2 S d.L₂ ∧ d.P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL := hp.hyp.P_le_L₂ hp.gms
  have hP2 : IsPGroup 2 (d.P.subgroupOf d.L₂) := d.isPGroup_P.comap_subtype
  obtain ⟨Q, hQ⟩ := hP2.exists_le_sylow
  exact ⟨(Q : Subgroup d.L₂).map d.L₂.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPL hx⟩, hQ hx, rfl⟩⟩

end S3cOrders

section S3cC2

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39c_pow_dvd_card_N₂ (d : Data G h) : (2 ^ f) ^ 3 ∣ Nat.card d.N₂ := by
  obtain ⟨hU, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) (by norm_num)
    (by norm_num)
  have h1 : Nat.card (hypSU h 1 1) = Nat.card d.N₂ := Nat.card_congr d.N₂equiv.toEquiv
  rw [← h1]
  have h2 : Nat.card (P : Subgroup (hypSU h 1 1)) ∣ Nat.card (hypSU h 1 1) :=
    Subgroup.card_subgroup_dvd_card _
  rwa [hP, hU] at h2

theorem s39c_pow_dvd_M₂ (hp : d.ProductCaseHyp) : (2 ^ f) ^ 6 ∣ Nat.card d.M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSharp, hM₂⟩ := hp.hyp.sec3_3_two hp.gms
  obtain ⟨⟨-, -, -, hnc, -, halt, -⟩, -⟩ := hSharp
  set C₂ : Subgroup G := centralizer (d.I₂ : Set G) with hC₂
  set O₂ := standardComponentOddCore C₂ with hO₂
  have hOodd : Odd (Nat.card O₂) := GMSK.odd_card_standardComponentOddCore C₂
  have hcop : ∀ n : ℕ, Nat.Coprime ((2 ^ f) ^ n) (Nat.card O₂) := fun n =>
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hOodd))
  have hN₂C : d.N₂ ≤ C₂ := d.N₂_le_centralizer_I₂
  have hM₂C : d.M₂ ≤ C₂ := Subgroup.map_subtype_le _
  rcases halt.or with hA | hB
  · exfalso
    apply hp.caseB
    have := hA.1
    rw [hnc] at this
    exact this
  · obtain ⟨D₁, D₂, -, -, -, -, -, -, -, -, -, -, -, -, ψ, -, -⟩ := hB
    have hcardD := Nat.card_congr ψ.toEquiv
    rw [Nat.card_prod] at hcardD
    have h3 : (2 ^ f) ^ 3 ∣ Nat.card ((d.N₂.subgroupOf C₂).map (QuotientGroup.mk' O₂)) := by
      refine s39c_dvd_map O₂ _ (hcop 3) ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hN₂C).toEquiv]
      exact s39c_pow_dvd_card_N₂ d
    have h4 : (2 ^ f) ^ 6 ∣ Nat.card (normalClosure (((d.N₂.subgroupOf C₂).map
        (QuotientGroup.mk' O₂) : Subgroup (C₂ ⧸ O₂)) : Set (C₂ ⧸ O₂))) := by
      rw [hcardD, show (2 ^ f) ^ 6 = (2 ^ f) ^ 3 * (2 ^ f) ^ 3 by ring]
      exact mul_dvd_mul h3 h3
    rw [hnc, ← hM₂] at h4
    obtain ⟨m', -, hcard⟩ := s39c_card_eq_mul_map O₂ (d.M₂.subgroupOf C₂)
    rw [Nat.card_congr (subgroupOfEquivOfLe hM₂C).toEquiv] at hcard
    exact h4.trans ⟨m', by rw [hcard, mul_comm]⟩

theorem s39c_E_inf_M₂ (hp : d.ProductCaseHyp) (hE2 : IsPGroup 2 d.E)
    (hME : d.M₂ ≤ normalizer (d.E : Set G)) : d.E ⊓ d.M₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSharp, hM₂⟩ := hp.hyp.sec3_3_two hp.gms
  obtain ⟨⟨-, -, -, hnc, hC, halt, -⟩, -⟩ := hSharp
  set C₂ : Subgroup G := centralizer (d.I₂ : Set G) with hC₂
  set O₂ := standardComponentOddCore C₂ with hO₂
  have hOodd : Odd (Nat.card O₂) := GMSK.odd_card_standardComponentOddCore C₂
  have hM₂C : d.M₂ ≤ C₂ := Subgroup.map_subtype_le _
  rcases halt.or with hA | hB
  · exfalso
    apply hp.caseB
    have := hA.1
    rw [hnc] at this
    exact this
  · obtain ⟨D₁, D₂, -, -, -, hs₁, hn₁, hs₂, hn₂, hsup, -, hcomm, -, -, -, -⟩ := hB
    set Y : Subgroup C₂ := (d.E ⊓ d.M₂).subgroupOf C₂ with hY
    have hYpg : IsPGroup 2 Y := (hE2.to_inf_left).comap_subtype
    have hY2 : Y.map (QuotientGroup.mk' O₂) = ⊥ := by
      refine s39c_pgroup_normal_in_prod_eq_bot (D₁ := D₁) (D₂ := D₂) hsup hcomm hs₁ hn₁ hs₂ hn₂ hC
        ?_ (hYpg.map _) ?_
      · rw [hnc, ← hM₂]
        refine Subgroup.map_mono ?_
        intro y hy
        exact (Subgroup.mem_inf.1 (mem_subgroupOf.1 hy)).2
      · intro g hg
        rw [hnc, ← hM₂] at hg
        obtain ⟨m, hm, rfl⟩ := hg
        have hmM : (m : G) ∈ d.M₂ := hm
        have hmY : m ∈ normalizer (Y : Set C₂) := by
          refine mem_normalizer_iff.2 fun y => ?_
          change (y : G) ∈ d.E ⊓ d.M₂ ↔ ((m * y * m⁻¹ : C₂) : G) ∈ d.E ⊓ d.M₂
          have e : ((m * y * m⁻¹ : C₂) : G) = (m : G) * (y : G) * (m : G)⁻¹ := rfl
          rw [e, Subgroup.mem_inf, Subgroup.mem_inf,
            mem_normalizer_iff.1 (hME hmM) (y : G),
            mem_normalizer_iff.1 (le_normalizer hmM) (y : G)]
        exact Subgroup.le_normalizer_map (QuotientGroup.mk' O₂) ⟨m, hmY, rfl⟩
    have hcard : Nat.card Y = 1 := by
      rw [← s39c_card_map_mk' O₂ hOodd hYpg, hY2, Subgroup.card_bot]
    have hEM : Nat.card (d.E ⊓ d.M₂ : Subgroup G) = 1 := by
      rw [← hcard, hY, Nat.card_congr
        (subgroupOfEquivOfLe (inf_le_right.trans hM₂C : d.E ⊓ d.M₂ ≤ C₂)).toEquiv]
    exact Subgroup.eq_bot_of_card_eq _ hEM

theorem s39c_card_S_ge (hp : d.ProductCaseHyp) (k : d.Know92) {S : Subgroup G}
    (hS : IsSylowOf 2 S d.L₂) : (2 ^ f) ^ 20 ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : d.L₂ = d.E ⊔ d.M₂ := k.s8.1
  have hME : d.M₂ ≤ normalizer (d.E : Set G) :=
    ((hL ▸ le_sup_right : d.M₂ ≤ d.L₂)).trans d.L₂_le_normalizer_E
  have hE2 : IsPGroup 2 d.E := hp.hyp.isPGroup_E hp.gms
  have hEM := s39c_E_inf_M₂ hp hE2 hME
  have h1 := Common.card_sup_mul_card_inf_eq hME
  rw [← hL, hEM, Subgroup.card_bot, mul_one, hp.hyp.card_E hp.gms] at h1
  have h2 : (2 ^ f) ^ 20 ∣ Nat.card d.L₂ := by
    rw [h1, show (2 ^ f) ^ 20 = (2 ^ f) ^ 14 * (2 ^ f) ^ 6 by ring]
    exact mul_dvd_mul_left _ (s39c_pow_dvd_M₂ hp)
  obtain ⟨Q, rfl⟩ := hS
  have h3 := Q.pow_dvd_card_of_pow_dvd_card (p := 2) (n := f * 20)
    (by rw [pow_mul]; exact h2)
  rw [Subgroup.card_map_of_injective d.L₂.subtype_injective]
  have h4 := Nat.le_of_dvd Nat.card_pos h3
  rwa [pow_mul] at h4

end S3cC2

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39c_four_mul_lt (f : ℕ) (hf : 2 ≤ f) : 4 * f < 2 ^ (2 * f) := by
  induction f, hf using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have e : 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by rw [mul_add, pow_add]; ring
    rw [e]
    omega

theorem sec39_notNormal (hp : d.ProductCaseHyp) (k : d.Know92) (he : d.Sec39e)
    (hi : d.Sec39Input) : d.Sec39NotNormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hN
  have hf2 : 2 ≤ f := hp.hyp.two_le
  obtain ⟨kf, _, _, hkf, ⟨e0⟩⟩ := hi.field
  have hrank : ∀ P : Subgroup (Bar d.D), P ≤ centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) :
      Set (Bar d.D)) → IsPGroup 2 P → Nat.card P ≤ 2 := hi.rank
  obtain ⟨S, hS, hPS⟩ := s39c_exists_sylow_L₂ hp.toCaseHyp
  obtain ⟨hSED, -, hDchar⟩ := k.s9_1 S hS hPS
  have hDS : d.D ≤ S := hSED ▸ le_sup_right
  have hSN : S ≤ normalizer (d.D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).1 inferInstance
  have hSpg : IsPGroup 2 S := hS.isPGroup
  have hbSpg : IsPGroup 2 (bar d.D S) := isPGroup_bar hSpg
  have hcardbar : Nat.card (bar d.D S) * Nat.card d.D = Nat.card S := card_bar_mul hDS hSN
  have hq4 : (2 ^ f) ^ 4 ≤ Nat.card (bar d.D S) := by
    have h1 := s39c_card_S_ge hp k hS
    have h2 := s39c_card_D_le hp he hi
    rw [← hcardbar] at h1
    have h3 : (2 ^ f) ^ 4 * (2 ^ f) ^ 16 ≤ Nat.card (bar d.D S) * (2 ^ f) ^ 16 :=
      calc (2 ^ f) ^ 4 * (2 ^ f) ^ 16 = (2 ^ f) ^ 20 := by ring
        _ ≤ Nat.card (bar d.D S) * Nat.card d.D := h1
        _ ≤ Nat.card (bar d.D S) * (2 ^ f) ^ 16 := Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hnum := s39c_four_mul_lt f hf2
  have hbig : 2 * (2 ^ (2 * f) * (2 * f)) < Nat.card (bar d.D S) := by
    have h5 : 2 ^ (2 * f) * (4 * f) < (2 ^ f) ^ 4 :=
      calc 2 ^ (2 * f) * (4 * f) < 2 ^ (2 * f) * 2 ^ (2 * f) :=
            Nat.mul_lt_mul_of_pos_left hnum (by positivity)
        _ = (2 ^ f) ^ 4 := by ring
    calc 2 * (2 ^ (2 * f) * (2 * f)) = 2 ^ (2 * f) * (4 * f) := by ring
      _ < (2 ^ f) ^ 4 := h5
      _ ≤ Nat.card (bar d.D S) := hq4
  exact s39c_not_normal_of_card (by omega) hkf e0 hi.order_two hi.centralizes hi.normal hrank
    hbSpg hbig hN

end Data

namespace CaseBParts

theorem sec39NotNormal : Sec39NotNormalStatement :=
  fun _ _ _ _ _ _ _ _ hp k he hi => Data.sec39_notNormal hp k he hi

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
