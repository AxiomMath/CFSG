module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Omega
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Section3
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitExclusion
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallAbelianModels
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Th.Max3.Relations
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem exists_pow_not_mem_sq_mem {G : Type*} [Group G] {T : Subgroup G} {g : G} (hg : g ∉ T)
    {n : ℕ} (hn : g ^ 2 ^ n = 1) : ∃ m : ℕ, g ^ 2 ^ m ∉ T ∧ (g ^ 2 ^ m) ^ 2 ∈ T := by
  classical
  have hex : ∃ j, g ^ 2 ^ (j + 1) ∈ T := by
    rcases n with _ | n
    · rw [pow_zero, pow_one] at hn
      exact absurd (hn ▸ one_mem T) hg
    · exact ⟨n, hn ▸ one_mem T⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · rcases h : Nat.find hex with _ | j
    · rw [pow_zero, pow_one]
      exact hg
    · have := Nat.find_min hex (show j < Nat.find hex by omega)
      exact this
  · rw [← pow_mul, ← pow_succ]
    exact Nat.find_spec hex

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem gen4_of_le_T {U : Subgroup X} (hU : U ≤ S.data.T) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = U := by
  classical
  set U' : Subgroup S.data.T := U.subgroupOf S.data.T with hU'
  have hQ : U'.map S.data.ψ ≤ P0 := by
    rintro _ ⟨g, -, rfl⟩
    exact S.data.ψ_mem_P0 g
  obtain ⟨s, hs, hsU⟩ := exists_finset_closure_eq_of_le_P0 hQ
  have hKc : IsCyclic (S.data.K.subgroupOf S.data.T) :=
    (subgroupOfEquivOfLe (inf_le_left : S.data.K ≤ S.data.T)).isCyclic.mpr
      (S.data.config.isCyclic_inf_kernel S.data.syl)
  have hle : U' ⊓ S.data.ψ.ker ≤ S.data.K.subgroupOf S.data.T := by
    intro g hg
    exact ⟨g.2, (S.data.ψ_eq_one_iff g).mp (mem_inf.mp hg).2⟩
  have : IsCyclic (U' ⊓ S.data.ψ.ker : Subgroup S.data.T) := Subgroup.isCyclic_of_le hle
  obtain ⟨r, hr, hrU⟩ := exists_finset_closure_eq_of_isCyclic (U' ⊓ S.data.ψ.ker)
  obtain ⟨u, hu, huU⟩ := exists_finset_closure_eq_of_map S.data.ψ U' hs hsU hr hrU
  refine ⟨u.image S.data.T.subtype, Finset.card_image_le.trans hu, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, huU, hU', subgroupOf_map_subtype,
    inf_of_le_left hU]

theorem not_sylow (hnot : ¬ SectRank4 X) (P : Sylow 2 X) : (P : Subgroup X) ≠ S.data.T := by
  intro hP
  exact hnot fun Q hQ =>
    exists_finset_closure_eq_of_sylow P (fun U hU => S.gen4_of_le_T (hP ▸ hU)) Q hQ

theorem eq_T_of_le' {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hTQ : S.data.T ≤ Q)
    (hQC : Q ≤ centralizer ({S.t} : Set X)) : Q = S.data.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf (centralizer ({S.t} : Set X))) :=
    hQ.comap_of_injective _ (subtype_injective _)
  have hsyl : (S.data.syl : Subgroup _) ≤ Q.subgroupOf (centralizer ({S.t} : Set X)) := by
    intro c hc
    exact hTQ ⟨c, hc, rfl⟩
  have heq := S.data.syl.is_maximal' hQ' hsyl
  apply le_antisymm _ hTQ
  intro q hq
  have : (⟨q, hQC hq⟩ : centralizer ({S.t} : Set X)) ∈ Q.subgroupOf (centralizer ({S.t} : Set X)) :=
    hq
  rw [heq] at this
  exact ⟨_, this, rfl⟩


theorem mem_B_cases {b : X} (hb : b ∈ S.B) :
    b = 1 ∨ b = S.z ∨ b = S.t ∨ b = S.t * S.z ∨ b = S.k ∨ b = S.z * S.k ∨ b = S.t * S.k ∨
      b = S.t * S.z * S.k := by
  have hbE : b ∈ S.E S.y := by
    rw [S.E_eq_B_sup]
    exact mem_sup_left hb
  obtain ⟨a, β, γ, δ, rfl⟩ := S.eq_of_mem_E S.y_mem S.y_sq (S.z_comm_of_mem_T S.y_mem.1) hbE
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hkB : S.k ∈ S.B := subset_closure (by simp)
  fin_cases β
  · fin_cases a <;> fin_cases γ <;> fin_cases δ <;> simp [hzt, mul_assoc]
  · exfalso
    apply S.y_not_mem_B
    have hrest : S.z ^ (a : ℕ) * S.t ^ (γ : ℕ) * S.k ^ (δ : ℕ) ∈ S.B :=
      mul_mem (mul_mem (pow_mem hzB _) (pow_mem htB _)) (pow_mem hkB _)
    have hyt : S.y * S.t = S.t * S.y := S.data.commute_t S.y_mem.1
    have hyz : S.z * S.y = S.y * S.z := S.z_comm_of_mem_T S.y_mem.1
    have : S.y = (S.z ^ (a : ℕ))⁻¹ * (S.z ^ (a : ℕ) * S.y ^ ((1 : Fin 2) : ℕ) * S.t ^ (γ : ℕ) *
        S.k ^ (δ : ℕ)) * (S.t ^ (γ : ℕ) * S.k ^ (δ : ℕ))⁻¹ := by
      simp only [Fin.val_one, pow_one]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (pow_mem hzB _)) hb)
      (inv_mem (mul_mem (pow_mem htB _) (pow_mem hkB _)))

theorem mem_B_cases' {c : X} (hc : c = S.k ∨ c = S.t * S.k) {b : X} (hb : b ∈ S.B) :
    (b = 1 ∨ b = S.z ∨ b = c ∨ b = S.z * c) ∨
      (b = S.t ∨ b = S.t * S.z ∨ b = S.t * c ∨ b = S.t * S.z * c) := by
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have ht2 : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]
  rcases S.mem_B_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [← mul_assoc, ht2, one_mul]
  · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [← hzt, mul_assoc S.z S.t, ← mul_assoc S.t S.t, ht2, one_mul]
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · refine Or.inl (Or.inr (Or.inr (Or.inr ?_)))
    rw [← hzt, mul_assoc]

theorem exists_T₁ (hnot : ¬ SectRank4 X) :
    ∃ T₁ : Subgroup X, IsPGroup 2 T₁ ∧ S.data.T ≤ T₁ ∧ T₁ ≤ normalizer (S.data.T : Set X) ∧
      (∀ Q : Subgroup X, IsPGroup 2 Q → T₁ ≤ Q → Q ≤ normalizer (S.data.T : Set X) → Q = T₁) ∧
      ∃ c : X, (c = S.k ∨ c = S.t * S.k) ∧ ∃ w ∈ T₁, w ∉ S.data.T ∧ w ^ 2 ∈ S.data.T ∧
        w * S.z * w⁻¹ = S.z ∧ w * c * w⁻¹ = c ∧
        ((Nat.card T₁ = 4 * Nat.card S.data.T ∧ ∀ b ∈ S.B, ConjTo S.t b ↔
            b = S.t ∨ b = S.t * S.z ∨ b = S.t * c ∨ b = S.t * S.z * c) ∨
          (Nat.card T₁ = 2 * Nat.card S.data.T ∧
            (∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = w * S.t * w⁻¹) ∧
            (w * S.t * w⁻¹ = S.t * S.z ∨ w * S.t * w⁻¹ = S.t * c ∨
              w * S.t * w⁻¹ = S.t * S.z * c))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := S.data.T with hT
  set N := normalizer (T : Set X) with hN
  obtain ⟨w₀, hw₀N, hw₀T, hw₀p⟩ := exists_mem_normalizer_not_mem S.data.isPGroup_T
    (S.not_sylow hnot)
  have hTN : T ≤ N := le_normalizer
  have hU : T ⊔ zpowers w₀ ≤ N := sup_le hTN (zpowers_le.mpr hw₀N)
  have hU' : IsPGroup 2 ((T ⊔ zpowers w₀).subgroupOf N) :=
    hw₀p.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  set T₁ : Subgroup X := (Q : Subgroup N).map N.subtype with hT₁
  have hT₁p : IsPGroup 2 T₁ := Q.isPGroup'.map _
  have hT₁N : T₁ ≤ N := map_subtype_le _
  have hUT₁ : T ⊔ zpowers w₀ ≤ T₁ := fun g hg => ⟨⟨g, hU hg⟩, hQ hg, rfl⟩
  have hTT₁ : T ≤ T₁ := le_sup_left.trans hUT₁
  have hw₀T₁ : w₀ ∈ T₁ := hUT₁ (mem_sup_right (mem_zpowers _))
  have hcardT₁ : Nat.card T₁ = 2 ^ (Nat.card N).factorization 2 := by
    rw [hT₁, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity]
  have hmax : ∀ Q' : Subgroup X, IsPGroup 2 Q' → T₁ ≤ Q' → Q' ≤ N → Q' = T₁ := by
    intro Q' hQ' hle hQ'N
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    obtain ⟨m, hm⟩ := hQ'.exists_card_eq
    have hdvd : Nat.card Q' ∣ Nat.card N := Subgroup.card_dvd_of_le hQ'N
    rw [hm] at hdvd ⊢
    rw [hcardT₁]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, w₀ ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hw₀p ⟨w₀, mem_sup_right (mem_zpowers _)⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  obtain ⟨m, hwT, hw2⟩ := exists_pow_not_mem_sq_mem hw₀T hn
  set w := w₀ ^ 2 ^ m with hw
  have hwT₁ : w ∈ T₁ := pow_mem hw₀T₁ _
  have hwN : w ∈ N := hT₁N hwT₁
  have hwt : w * S.t * w⁻¹ ≠ S.t := by
    intro h
    have hwC : w ∈ centralizer ({S.t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc w * S.t = w * S.t * w⁻¹ * w := by group
        _ = S.t * w := by rw [h]
    have hle : T ⊔ zpowers w ≤ T₁ := sup_le hTT₁ (zpowers_le.mpr hwT₁)
    have heq := S.eq_T_of_le' (hT₁p.to_le hle) le_sup_left
      (sup_le S.data.T_le_centralizer (zpowers_le.mpr hwC))
    exact hwT (heq ▸ mem_sup_right (mem_zpowers w))
  obtain ⟨c, hc, hfix⟩ := S.exists_fix_B hwN hw2 hwt
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hcB : c ∈ S.B := by
    rcases hc with rfl | rfl
    · exact subset_closure (by simp)
    · exact mul_mem htB (subset_closure (by simp))
  have hwz : w * S.z * w⁻¹ = S.z := (hfix S.z hzB).mpr (Or.inr (Or.inl rfl))
  have hwc : w * c * w⁻¹ = c := (hfix c hcB).mpr (Or.inr (Or.inr (Or.inl rfl)))
  set O : Set X := {b | ∃ g ∈ N, g * S.t * g⁻¹ = b} with hO
  have hOconj : ∀ b ∈ S.B, ConjTo S.t b ↔ b ∈ O := by
    intro b hb
    constructor
    · intro h
      exact S.exists_normalizer_conj_eq hb h
    · rintro ⟨g, -, hg⟩
      exact ⟨g, hg⟩
  have hOB : ∀ b ∈ O, b ∈ S.B := by
    rintro _ ⟨g, hg, rfl⟩
    exact S.conj_mem_B hg htB
  have hTw : IsPGroup 2 (T ⊔ zpowers w : Subgroup X) :=
    hT₁p.to_le (sup_le hTT₁ (zpowers_le.mpr hwT₁))
  have hTlt : T < T ⊔ zpowers w := by
    refine lt_of_le_of_ne le_sup_left fun h => hwT ?_
    change w ∈ T
    rw [h]
    exact mem_sup_right (mem_zpowers w)
  have hOsub : ∀ b ∈ O, b = S.t ∨ b = S.t * S.z ∨ b = S.t * c ∨ b = S.t * S.z * c := by
    intro b hbO
    have hb := hOB b hbO
    rcases S.mem_B_cases' hc hb with hb' | hb'
    · exfalso
      have hwb : w * b * w⁻¹ = b := (hfix b hb).mpr hb'
      have hle : T ⊔ zpowers w ≤ centralizer ({b} : Set X) := by
        refine sup_le (fun h hh => mem_centralizer_singleton_iff.mpr
          (S.central_of_mem_B hb hh).symm) ?_
        rw [zpowers_le, mem_centralizer_singleton_iff]
        calc w * b = w * b * w⁻¹ * w := by group
          _ = b * w := by rw [hwb]
      exact S.not_conjTo_of_le_centralizer hTw hTlt hle ((hOconj b hb).mpr hbO)
    · exact hb'
  have hidx : (N ⊓ centralizer ({S.t} : Set X)).relIndex N = O.ncard :=
    relIndex_inf_centralizer_eq_ncard N S.t
  have hTC : Nat.card T =
      2 ^ (Nat.card (N ⊓ centralizer ({S.t} : Set X) : Subgroup X)).factorization 2 :=
    S.card_T_eq_of_le (le_inf hTN S.data.T_le_centralizer) inf_le_right
  have hcard := card_eq_mul_two_pow (P := T₁) (Q := T) inf_le_left hcardT₁ hTC
  rw [hidx] at hcard
  have htO : S.t ∈ O := ⟨1, one_mem _, by group⟩
  have hwtO : w * S.t * w⁻¹ ∈ O := ⟨w, hwN, rfl⟩
  have hO4 : O ⊆ ({S.t, S.t * S.z, S.t * c, S.t * S.z * c} : Set X) := by
    intro b hb
    rcases hOsub b hb with h | h | h | h <;> simp [h]
  have hOle : O.ncard ≤ 4 := by
    calc O.ncard ≤ ({S.t, S.t * S.z, S.t * c, S.t * S.z * c} : Set X).ncard :=
          Set.ncard_le_ncard hO4 (Set.toFinite _)
      _ ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        rw [Set.ncard_singleton]
  have hOge : 2 ≤ O.ncard := by
    have hsub : ({S.t, w * S.t * w⁻¹} : Set X) ⊆ O := by
      intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl
      · exact htO
      · exact hwtO
    calc 2 = ({S.t, w * S.t * w⁻¹} : Set X).ncard := (Set.ncard_pair (Ne.symm hwt)).symm
      _ ≤ O.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hTT₁lt : Nat.card T < Nat.card T₁ :=
    Subgroup.card_lt_of_lt (lt_of_lt_of_le hTlt (sup_le hTT₁ (zpowers_le.mpr hwT₁)))
  refine ⟨T₁, hT₁p, hTT₁, hT₁N, hmax, c, hc, w, hwT₁, hwT, hw2, hwz, hwc, ?_⟩
  have hO3 : O.ncard ≠ 3 := by
    intro h3
    rw [h3, show (3 : ℕ).factorization 2 = 0 from
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), pow_zero, mul_one] at hcard
    omega
  have hcases : O.ncard = 2 ∨ O.ncard = 4 := by omega
  rcases hcases with h2 | h4
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [hcard, h2, Nat.Prime.factorization_self Nat.prime_two, pow_one, mul_comm]
    · have hOeq : O = ({S.t, w * S.t * w⁻¹} : Set X) := by
        symm
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
        · intro b hb
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with rfl | rfl
          · exact htO
          · exact hwtO
        · rw [h2, Set.ncard_pair (Ne.symm hwt)]
      intro b hb
      rw [hOconj b hb, hOeq]
      simp
    · rcases hOsub _ hwtO with h | h | h | h
      · exact absurd h hwt
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · left
    refine ⟨?_, ?_⟩
    · rw [hcard, h4, show (4 : ℕ).factorization 2 = 2 by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
        simp, mul_comm]
      norm_num
    · have hOeq : O = ({S.t, S.t * S.z, S.t * c, S.t * S.z * c} : Set X) := by
        refine Set.eq_of_subset_of_ncard_le hO4 ?_ (Set.toFinite _)
        rw [h4]
        refine (Set.ncard_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        rw [Set.ncard_singleton]
      intro b hb
      rw [hOconj b hb, hOeq]
      simp

end A7Base

end CFSG.ComponentClassification.HSFLit
