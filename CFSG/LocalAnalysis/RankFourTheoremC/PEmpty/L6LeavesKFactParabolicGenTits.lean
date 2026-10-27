module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenCore
public import CFSG.Milestones.ASVolI.F4Native
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.LieType.BorelTits Subgroup

theorem mem_sylow_of_normalizer {T : Type*} [Group T] [Finite T] (S : Sylow 2 T) {B : Subgroup T}
    (hBS : B ≤ normalizer ((S : Subgroup T) : Set T)) {y : T} (hy : y ∈ B) {m : ℕ}
    (hym : y ^ 2 ^ m = 1) : y ∈ (S : Subgroup T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (Subgroup.zpowers y) := by
    have hdvd : orderOf y ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hym
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hsup : IsPGroup 2 ((S : Subgroup T) ⊔ Subgroup.zpowers y : Subgroup T) :=
    S.isPGroup'.to_sup_of_normal_left' hz (Subgroup.zpowers_le.mpr (hBS hy))
  have hmax := S.is_maximal' hsup le_sup_left
  exact (le_sup_right.trans hmax.le) (Subgroup.mem_zpowers y)

theorem pCoreOf_ne_bot_of_small_index {T : Type*} [Group T] [Finite T] (S : Sylow 2 T)
    {B P : Subgroup T} (hSB : (S : Subgroup T) ≤ B)
    (hBS : B ≤ normalizer ((S : Subgroup T) : Set T)) (hBP : B ≤ P) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card (S : Subgroup T)) (hr : ¬ 2 ^ k ∣ (B.relIndex P).factorial) :
    pCoreOf 2 P ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  set C : Subgroup ↥P := (B.subgroupOf P).normalCore with hC
  have hCn : C.Normal := Subgroup.normalCore_normal (B.subgroupOf P)
  have hCB : C ≤ B.subgroupOf P := Subgroup.normalCore_le _
  set C' : Subgroup T := C.map P.subtype with hC'
  have hC'B : C' ≤ B := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hCB hc)
  have hC'P : C' ≤ P := Subgroup.map_subtype_le C
  have hPC' : P ≤ normalizer (C' : Set T) := by
    intro p hp
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨p, hp⟩ * c * ⟨p, hp⟩⁻¹, hCn.conj_mem c hc ⟨p, hp⟩, rfl⟩
    · rintro ⟨c, hc, hch⟩
      refine ⟨⟨p, hp⟩⁻¹ * c * ⟨p, hp⟩, ?_, ?_⟩
      · have := hCn.conj_mem c hc (⟨p, hp⟩⁻¹)
        simpa using this
      · have hch' : (c : T) = p * h * p⁻¹ := hch
        show (p⁻¹ * (c : T) * p : T) = h
        rw [hch']
        group
  set Q' : Subgroup T := C' ⊓ (S : Subgroup T) with hQ'
  have hconj : ∀ p ∈ P, ∀ y ∈ Q', p * y * p⁻¹ ∈ Q' := by
    intro p hp y hy
    have hyC : p * y * p⁻¹ ∈ C' := (mem_normalizer_iff.mp (hPC' hp) y).mp hy.1
    obtain ⟨m, hm⟩ := S.isPGroup' ⟨y, hy.2⟩
    have hm' : y ^ 2 ^ m = 1 := congrArg Subtype.val hm
    refine ⟨hyC, mem_sylow_of_normalizer S hBS (hC'B hyC) (m := m) ?_⟩
    rw [conj_pow, hm']
    simp
  have hPQ' : P ≤ normalizer (Q' : Set T) := fun p hp =>
    mem_normalizer_iff.2 fun n => ⟨hconj p hp n, fun h => by
      have h' := hconj p⁻¹ (P.inv_mem hp) _ h
      have e : p⁻¹ * (p * n * p⁻¹) * p⁻¹⁻¹ = n := by group
      rwa [e] at h'⟩
  have hQ'p : IsPGroup 2 Q' := S.isPGroup'.to_le inf_le_right
  have hle : Q' ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hC'P) hPQ' hQ'p
  rw [hbot, le_bot_iff] at hle
  have hodd : ¬ 2 ∣ Nat.card C := by
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2
    have hx1 : ((x : ↥P) : T) ^ 2 ^ 1 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      have h' := congrArg (fun z : C => ((z : ↥P) : T)) this
      simpa using h'
    have hxC' : ((x : ↥P) : T) ∈ C' := ⟨(x : ↥P), x.2, rfl⟩
    have hxS : ((x : ↥P) : T) ∈ (S : Subgroup T) :=
      mem_sylow_of_normalizer S hBS (hC'B hxC') hx1
    have hxQ : ((x : ↥P) : T) ∈ Q' := ⟨hxC', hxS⟩
    rw [hle, Subgroup.mem_bot] at hxQ
    have hx0 : x = 1 := Subtype.ext (Subtype.ext hxQ)
    rw [hx0, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hPC : Nat.card C * C.index = Nat.card P := Subgroup.card_mul_index C
  have hSP : Nat.card (S : Subgroup T) ∣ Nat.card P := Subgroup.card_dvd_of_le (hSB.trans hBP)
  have h2k : 2 ^ k ∣ Nat.card C * C.index := by
    rw [hPC]
    exact hk.trans hSP
  have hcop : Nat.Coprime (2 ^ k) (Nat.card C) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).pow_left k
  have hdvd : 2 ^ k ∣ C.index := hcop.dvd_of_dvd_mul_left h2k
  have hidx : C.index ∣ (B.subgroupOf P).index.factorial :=
    Subgroup.index_normalCore_dvd_factorial_index (B.subgroupOf P)
  exact hr (hdvd.trans hidx)

theorem sup_eq_top_of_lieParabolics {T : Type} [Group T] {p : ℕ} {B P₁ P₂ : Subgroup T}
    (hP : CFSG.ASVolI.ChF.IsLieParabolics p ⊤ B P₁ P₂) : P₁ ⊔ P₂ = ⊤ := by
  obtain ⟨-, hne, -, hmax⟩ := hP
  obtain ⟨-, -, -, hP1max⟩ := (hmax P₁).mpr (Or.inl rfl)
  obtain ⟨-, -, -, hP2max⟩ := (hmax P₂).mpr (Or.inr rfl)
  by_contra hR
  have h1 : P₁ ⊔ P₂ = P₁ := by
    by_contra h
    exact hR (hP1max _ (lt_of_le_of_ne le_sup_left (Ne.symm h)) le_top)
  have h2 : P₁ ⊔ P₂ = P₂ := by
    by_contra h
    exact hR (hP2max _ (lt_of_le_of_ne le_sup_right (Ne.symm h)) le_top)
  exact hne (h1.symm.trans h2)

theorem hasParGen_of_lieParabolics_index {T : Type} [Group T] [Finite T] {B P₁ P₂ : Subgroup T}
    (h : CFSG.ASVolI.ChF.IsLieParabolics 2 ⊤ B P₁ P₂) {k : ℕ} (hk : 2 ^ k ∣ Nat.card T)
    (h₁ : ¬ 2 ^ k ∣ (B.relIndex P₁).factorial) (h₂ : ¬ 2 ^ k ∣ (B.relIndex P₂).factorial) :
    HasParGen T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen := sup_eq_top_of_lieParabolics h
  obtain ⟨⟨S, ⟨-, hS2, hSi⟩, hB⟩, -, -, hQ⟩ := h
  have hodd : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSi
  let W : Sylow 2 T := hS2.toSylow hodd
  have hW : (W : Subgroup T) = S := IsPGroup.toSylow_coe hS2 hodd
  rw [top_inf_eq] at hB
  obtain ⟨hBP₁, -⟩ := (hQ P₁).mpr (Or.inl rfl)
  obtain ⟨hBP₂, -⟩ := (hQ P₂).mpr (Or.inr rfl)
  have hN : normalizer ((W : Subgroup T) : Set T) = B := by rw [hW, hB]
  have hSB : (W : Subgroup T) ≤ B := by
    rw [← hN]
    exact le_normalizer
  have hBW : B ≤ normalizer ((W : Subgroup T) : Set T) := hN.ge
  have hWk : 2 ^ k ∣ Nat.card (W : Subgroup T) := W.pow_dvd_card_of_pow_dvd_card hk
  have hc₁ := pCoreOf_ne_bot_of_small_index W hSB hBW hBP₁ hWk h₁
  have hc₂ := pCoreOf_ne_bot_of_small_index W hSB hBW hBP₂ hWk h₂
  refine ⟨W, parabGen_eq_top_of_family (fun i : Bool => if i then P₁ else P₂) (fun i => ?_)
    (fun i => ?_) ?_⟩
  · cases i
    · show normalizer ((W : Subgroup T) : Set T) ≤ P₂
      rw [hN]
      exact hBP₂
    · show normalizer ((W : Subgroup T) : Set T) ≤ P₁
      rw [hN]
      exact hBP₁
  · cases i
    · exact hc₂
    · exact hc₁
  · rw [iSup_bool_eq]
    simpa using hgen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots in
theorem hasParGen_of_titsModel
    {G : Type} [Group G] [Finite G] {f : ℕ} (h : ReeTitsModel G .Tits 2 f) : HasParGen G := by
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv G 2 f h
  have hcard : Nat.card G = 17971200 :=
    (Nat.card_congr eT.toEquiv).trans CFSG.Sporadic.Schreier.Tits.card_titsD
  obtain ⟨⟨-, -, -, -, hf1⟩, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  have ha : a = 0 := by omega
  subst ha
  have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hscope : ReeScope K 0 := by
    show Nat.card K = 2 ^ (2 * 0 + 1)
    rw [hK2]
    norm_num
  obtain ⟨hlie, h5, h3, -⟩ := CFSG.ASVolI.burnsideF4h_titsParentAssembly K hscope
  let e' : G ≃* DerivedCentralQuotient (reeGroup K 0) := e
  haveI : Finite (DerivedCentralQuotient (reeGroup K 0)) := Finite.of_equiv G e'.toEquiv
  have hk : 2 ^ 4 ∣ Nat.card (DerivedCentralQuotient (reeGroup K 0)) := by
    rw [← Nat.card_congr e'.toEquiv, hcard]
    norm_num
  have hT := hasParGen_of_lieParabolics_index hlie hk (by rw [h5]; decide) (by rw [h3]; decide)
  exact hasParGen_of_mulEquiv e'.symm hT

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
