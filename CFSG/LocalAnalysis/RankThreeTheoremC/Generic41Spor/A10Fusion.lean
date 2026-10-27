module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneQuot
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.LinesCore
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Five
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIEndgame41Aux
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC TypeSE U3Lemma33
  fusion_P_le_C_of_fix)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem typeSE_a10 : TypeSE IsA10Type 5 := by
  intro K _ _ hK
  obtain ⟨-, ⟨e⟩⟩ := hK
  have hn : 5 ≤ 10 := by norm_num
  exact ⟨Or.inr (Or.inr (Or.inl ⟨le_rfl, ⟨e⟩⟩)),
    TauCeti.CFSGIndex.alternating 10 hn, ⟨e.trans (MulEquiv.refl _)⟩⟩

theorem a10_fusion_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSig : SignalizerTwoGroupKFact) (hX : A10Facts) (hXe : A10Ext)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) : A10StageB P x J ψ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : (5 : ℕ).Prime := by norm_num
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hxo : orderOf x = 5 := orderOf_eq_prime hxp hx1
  obtain ⟨hTcard, hTel, hxJ⟩ := plane_T_structure hX.sylow hc
  have hSab := plane_abelian hX.sylow hX.noOuter hc
  have hΩ := plane_omega hX.sylow hX.noOuter hc
  have hL33 := plane_lemma33 hS hD1 hSig hX.sylow hX.noOuter typeSE_a10 hc
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hSC : ∀ s ∈ u3S P x, s * x = x * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp hs.2
  have hxT : x ∉ u3T P x J := fun h => hxJ (hTJ h)
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  haveI : IsMulCommutative (u3T P x J) := hTel.1
  obtain ⟨S', hS'1, hS'2, hinj, hlift⟩ := plane_quotient_data hc ψ hψ hker
  have hline : ∀ (s t : G) (hs : s ∈ u3T P x J) (ht : t ∈ u3T P x J),
      ψ ⟨s, hTJ hs⟩ ∈ Subgroup.zpowers (ψ ⟨t, hTJ ht⟩) ↔ s ∈ Subgroup.zpowers t := by
    intro s t hs ht
    constructor
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hkT : t ^ k ∈ u3T P x J := zpow_mem ht k
      have h3 : (⟨t ^ k, hTJ hkT⟩ : ↥J) = (⟨t, hTJ ht⟩ : ↥J) ^ k := Subtype.ext (by simp)
      have h4 : ψ ⟨s, hTJ hs⟩ = ψ ⟨t ^ k, hTJ hkT⟩ := by
        rw [h3, map_zpow, hk]
      have hst := hinj s hs (t ^ k) hkT h4
      rw [hst]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
    · intro hmem
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h3 : (⟨t ^ k, hTJ hs⟩ : ↥J) = (⟨t, hTJ ht⟩ : ↥J) ^ k := Subtype.ext (by simp)
      rw [h3, map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  obtain ⟨c₁, c₂, hc₁S, hc₂S, hc₁1, hc₂c₁, hcent1, hcent2, ⟨n₀, hn₀N, hn₀⟩, hEtr⟩ :=
    a10_fiveCycleLines Q hQ S'
  obtain ⟨σ, hσN, hσ⟩ := a10_scalars Q hQ S'
  obtain ⟨t₁, ht₁T, rfl⟩ := hS'2 c₁ hc₁S
  obtain ⟨t₂, ht₂T, rfl⟩ := hS'2 c₂ hc₂S
  have ht₁p : t₁ ^ 5 = 1 := hTel.2 t₁ ht₁T
  have ht₂p : t₂ ^ 5 = 1 := hTel.2 t₂ ht₂T
  have ht₁1 : t₁ ≠ 1 := by
    intro h
    apply hc₁1
    have : (⟨t₁, hTJ ht₁T⟩ : ↥J) = 1 := Subtype.ext h
    rw [this, map_one]
  have hc₂1 : ψ ⟨t₂, hTJ ht₂T⟩ ≠ 1 := by
    intro h
    apply hc₂c₁
    rw [h]
    exact Subgroup.one_mem _
  have ht₂1 : t₂ ≠ 1 := by
    intro h
    apply hc₂1
    have : (⟨t₂, hTJ ht₂T⟩ : ↥J) = 1 := Subtype.ext h
    rw [this, map_one]
  have ht₂t₁ : t₂ ∉ Subgroup.zpowers t₁ := fun h => hc₂c₁ ((hline t₂ t₁ ht₂T ht₁T).mpr h)
  have hto₁ : orderOf t₁ = 5 := orderOf_eq_prime ht₁p ht₁1
  have hto₂ : orderOf t₂ = 5 := orderOf_eq_prime ht₂p ht₂1
  have hgen : ∀ t ∈ u3T P x J, t ≠ 1 → ∀ s ∈ Subgroup.zpowers t, s ≠ 1 →
      Subgroup.zpowers s = Subgroup.zpowers t := fun t ht ht1 s hs hs1 =>
    eg41_zpowers_eq_of_mem hp (orderOf_eq_prime (hTel.2 t ht) ht1) hs hs1
  set Γ : Subgroup G := J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) with hΓ
  have hΓx : ∀ γ ∈ Γ, γ * x = x * γ := fun γ hγ =>
    Subgroup.mem_centralizer_singleton_iff.mp (hc.le_cent hγ.1)
  have hact : ∀ γ (hγ : γ ∈ Γ) (t : G) (ht : t ∈ u3T P x J),
      ∃ h : γ * t * γ⁻¹ ∈ u3T P x J, ψ ⟨γ * t * γ⁻¹, hTJ h⟩ =
        ψ ⟨γ, hγ.1⟩ * ψ ⟨t, hTJ ht⟩ * (ψ ⟨γ, hγ.1⟩)⁻¹ := by
    intro γ hγ t ht
    have h : γ * t * γ⁻¹ ∈ u3T P x J := (Subgroup.mem_normalizer_iff.mp hγ.2 t).mp ht
    refine ⟨h, ?_⟩
    have : (⟨γ * t * γ⁻¹, hTJ h⟩ : ↥J) = ⟨γ, hγ.1⟩ * ⟨t, hTJ ht⟩ * (⟨γ, hγ.1⟩ : ↥J)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  obtain ⟨γ₀, hγ₀Γ, hγ₀⟩ : ∃ γ ∈ Γ, γ * t₁ * γ⁻¹ ∈ Subgroup.zpowers t₂ := by
    obtain ⟨γ, hγJ, hγN, hψγ⟩ := hlift n₀ hn₀N
    refine ⟨γ, ⟨hγJ, hγN⟩, ?_⟩
    obtain ⟨h, hψ'⟩ := hact γ ⟨hγJ, hγN⟩ t₁ ht₁T
    rw [← hline _ t₂ h ht₂T, hψ', hψγ]
    exact hn₀
  obtain ⟨γσ, hγσΓ, hγσ⟩ : ∃ γ ∈ Γ, ∀ t (ht : t ∈ u3T P x J), γ * t * γ⁻¹ = t * t := by
    obtain ⟨γ, hγJ, hγN, hψγ⟩ := hlift σ hσN
    refine ⟨γ, ⟨hγJ, hγN⟩, fun t ht => ?_⟩
    obtain ⟨h, hψ'⟩ := hact γ ⟨hγJ, hγN⟩ t ht
    have htt : t * t ∈ u3T P x J := (u3T P x J).mul_mem ht ht
    apply hinj _ h _ htt
    rw [hψ', hψγ, hσ _ (hS'1 t ht)]
    have : (⟨t * t, hTJ htt⟩ : ↥J) = ⟨t, hTJ ht⟩ * ⟨t, hTJ ht⟩ := rfl
    rw [this, map_mul]
  have hγσpow : ∀ (i : ℕ) (t : G), t ∈ u3T P x J → γσ ^ i * t * (γσ ^ i)⁻¹ = t ^ (2 ^ i) := by
    intro i t ht
    induction i with
    | zero => simp
    | succ i ih =>
      calc γσ ^ (i + 1) * t * (γσ ^ (i + 1))⁻¹
          = γσ * (γσ ^ i * t * (γσ ^ i)⁻¹) * γσ⁻¹ := by rw [pow_succ']; group
        _ = γσ * t ^ (2 ^ i) * γσ⁻¹ := by rw [ih]
        _ = (γσ * t * γσ⁻¹) ^ (2 ^ i) := (conj_pow).symm
        _ = (t * t) ^ (2 ^ i) := by rw [hγσ t ht]
        _ = t ^ (2 ^ (i + 1)) := by rw [← pow_two, ← pow_mul, pow_succ']
  have hPow : ∀ t ∈ u3T P x J, t ≠ 1 → ∀ k : ℕ, ¬ 5 ∣ k → ∃ γ ∈ Γ, γ * t * γ⁻¹ = t ^ k := by
    intro t ht ht1 k hk
    have ht5 : t ^ 5 = 1 := hTel.2 t ht
    have hk' : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    have key : ∀ i : ℕ, 2 ^ i % 5 = k % 5 → ∃ γ ∈ Γ, γ * t * γ⁻¹ = t ^ k := by
      intro i hi
      refine ⟨γσ ^ i, Subgroup.pow_mem _ hγσΓ i, ?_⟩
      have h := hγσpow i t ht
      rw [h, pow_eq_pow_mod (2 ^ i) ht5, pow_eq_pow_mod k ht5, hi]
    rcases hk' with h | h | h | h
    · exact key 0 (by simp [h])
    · exact key 1 (by simp [h])
    · exact key 3 (by simp [h])
    · exact key 2 (by simp [h])
  set SL : Finset (Subgroup G) := {Subgroup.zpowers t₁, Subgroup.zpowers t₂} with hSL
  have hSLc : SL.card ≤ 2 := Finset.card_le_two
  have hnotSL : ∀ s ∈ u3T P x J, s ≠ 1 → Subgroup.zpowers s ∉ SL → s ∉ Subgroup.zpowers t₁ ∧
      s ∉ Subgroup.zpowers t₂ := by
    intro s hs hs1 hsSL
    refine ⟨fun h => hsSL ?_, fun h => hsSL ?_⟩
    · rw [hSL, Finset.mem_insert]
      exact Or.inl (hgen t₁ ht₁T ht₁1 s h hs1)
    · rw [hSL, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (hgen t₂ ht₂T ht₂1 s h hs1)
  have htrans : ∀ s ∈ u3T P x J, ∀ s' ∈ u3T P x J, s ≠ 1 → s' ≠ 1 → Subgroup.zpowers s ∉ SL →
      Subgroup.zpowers s' ∉ SL → ∃ γ ∈ Γ, γ * s * γ⁻¹ ∈ Subgroup.zpowers s' := by
    intro s hs s' hs' hs1 hs'1 hsSL hs'SL
    obtain ⟨hs₁, hs₂⟩ := hnotSL s hs hs1 hsSL
    obtain ⟨hs'₁, hs'₂⟩ := hnotSL s' hs' hs'1 hs'SL
    obtain ⟨nb, hnbN, hnb⟩ := hEtr (ψ ⟨s, hTJ hs⟩) (hS'1 s hs)
      (fun h => hs₁ ((hline s t₁ hs ht₁T).mp h)) (fun h => hs₂ ((hline s t₂ hs ht₂T).mp h))
      (ψ ⟨s', hTJ hs'⟩) (hS'1 s' hs')
      (fun h => hs'₁ ((hline s' t₁ hs' ht₁T).mp h)) (fun h => hs'₂ ((hline s' t₂ hs' ht₂T).mp h))
    obtain ⟨γ, hγJ, hγN, hψγ⟩ := hlift nb hnbN
    refine ⟨γ, ⟨hγJ, hγN⟩, ?_⟩
    obtain ⟨h, hψ'⟩ := hact γ ⟨hγJ, hγN⟩ s hs
    rw [← hline _ s' h hs', hψ', hψγ]
    exact hnb
  have hSyl : IsSylowOf 5 (u3S P x) (Subgroup.centralizer ({x} : Set G)) := hc.generic.2.2.1
  have hNtrans := conjLinesIn_normalizer_trans hSyl hSab
  have hD := lines_core (p := 5) (by norm_num) SL hx1 hxp hTS hSC hTel hTcard hxT hΩ hL33 hΓx hPow
    hSLc htrans hNtrans
  set D : Set (Subgroup G) := conjLinesIn x (u3S P x) with hDdef
  have hx0 : Subgroup.zpowers x ∈ D := by
    refine ⟨1, ?_, Subgroup.zpowers_le.mpr hxS⟩
    rw [map_conj_zpowers, one_mul, inv_one, mul_one]
  have hconjD : ∀ (γ : G) (A : Subgroup G), A ∈ D → A.map (MulAut.conj γ).toMonoidHom ≤ u3S P x →
      A.map (MulAut.conj γ).toMonoidHom ∈ D := by
    rintro γ A ⟨g, hAg, -⟩ hle
    exact ⟨γ * g, by rw [hAg, map_conj_map_conj], hle⟩
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine fusion_P_le_C_of_fix hc ?_
    intro y hyP hyN
    set D₀ : Finset (Subgroup G) := insert (Subgroup.zpowers x) SL with hD₀
    set Df : Finset (Subgroup G) := D₀.filter (· ∈ D) with hDf
    have hmemDf : ∀ A, A ∈ Df ↔ A ∈ D := by
      intro A
      rw [hDf, Finset.mem_filter, hD₀, Finset.mem_insert]
      exact ⟨fun h => h.2, fun h => ⟨hD A h, h⟩⟩
    have hDfcard : Df.card ≤ 3 := by
      have h1 : Df.card ≤ D₀.card := Finset.card_filter_le _ _
      have h2 : D₀.card ≤ SL.card + 1 := Finset.card_insert_le _ _
      omega
    have hyD : ∀ A ∈ D, A.map (MulAut.conj y).toMonoidHom ∈ D := by
      intro A hA
      refine hconjD y A hA ?_
      obtain ⟨g, hAg, hAS⟩ := hA
      rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hyN a).mp (hAS ha)
    let f : Function.End ↥Df := fun A =>
      ⟨A.1.map (MulAut.conj y).toMonoidHom, (hmemDf _).2 (hyD _ ((hmemDf _).1 A.2))⟩
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨y, hyP⟩
    have hym : y ^ (5 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hf : f ^ 5 ^ m = 1 := by
      have key : ∀ k : ℕ, ∀ A : ↥Df,
          ((f ^ k) A).1 = A.1.map (MulAut.conj (y ^ k)).toMonoidHom := by
        intro k
        induction k with
        | zero =>
          intro A
          rw [pow_zero, pow_zero, map_conj_one]
          rfl
        | succ k ih =>
          intro A
          rw [pow_succ, pow_succ]
          change ((f ^ k) (f A)).1 = _
          rw [ih (f A)]
          show (A.1.map (MulAut.conj y).toMonoidHom).map (MulAut.conj (y ^ k)).toMonoidHom = _
          rw [map_conj_map_conj]
      funext A
      apply Subtype.ext
      rw [key, hym, map_conj_one]
      rfl
    have hx0f : Subgroup.zpowers x ∈ Df := (hmemDf _).2 hx0
    have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥Df) (p := 5) (n := m) hf
    have hfx : f ⟨Subgroup.zpowers x, hx0f⟩ = ⟨Subgroup.zpowers x, hx0f⟩ := by
      by_contra hne
      have hlt : Fintype.card (Function.fixedPoints f) < Fintype.card ↥Df :=
        Fintype.card_subtype_lt (x := ⟨Subgroup.zpowers x, hx0f⟩) hne
      have hc3 : Fintype.card ↥Df ≤ 3 := by
        rw [Fintype.card_coe]
        exact hDfcard
      unfold Nat.ModEq at hmod
      omega
    have h1 := congrArg Subtype.val hfx
    change (Subgroup.zpowers x).map (MulAut.conj y).toMonoidHom = Subgroup.zpowers x at h1
    rw [map_conj_zpowers] at h1
    have h2 : y * x * y⁻¹ ∈ Subgroup.zpowers (y * x * y⁻¹) := Subgroup.mem_zpowers _
    rwa [h1] at h2
  have hSP : (u3S P x : Subgroup G) = (P : Subgroup G) :=
    le_antisymm inf_le_left (le_inf le_rfl hPC)
  have hDP : conjLines x (P : Subgroup G) = D := by
    have h : conjLinesIn x (u3S P x) = conjLinesIn x (P : Subgroup G) := by rw [hSP]
    exact h.symm
  have hD1' : ∀ A ∈ D, A = Subgroup.zpowers x ∨ A = Subgroup.zpowers t₁ ∨
      A = Subgroup.zpowers t₂ := by
    intro A hA
    rcases hD A hA with h | h
    · exact Or.inl h
    · rw [hSL, Finset.mem_insert, Finset.mem_singleton] at h
      exact Or.inr h
  unfold A10StageB
  refine ⟨hPC, ?_⟩
  rw [hDP]
  by_cases hA : Subgroup.zpowers t₁ ∈ D ∨ Subgroup.zpowers t₂ ∈ D
  · right
    have hγ₀1 : γ₀ * t₁ * γ₀⁻¹ ≠ 1 := by
      intro h
      apply ht₁1
      have : t₁ = γ₀⁻¹ * (γ₀ * t₁ * γ₀⁻¹) * γ₀ := by group
      rw [h] at this
      simpa using this
    have hswap : (Subgroup.zpowers t₁).map (MulAut.conj γ₀).toMonoidHom = Subgroup.zpowers t₂ := by
      rw [map_conj_zpowers]
      exact hgen t₂ ht₂T ht₂1 _ hγ₀ hγ₀1
    have h12 : Subgroup.zpowers t₁ ∈ D ∧ Subgroup.zpowers t₂ ∈ D := by
      rcases hA with h | h
      · refine ⟨h, ?_⟩
        rw [← hswap]
        refine hconjD γ₀ _ h ?_
        rw [hswap]
        exact (Subgroup.zpowers_le.mpr ht₂T).trans hTS
      · refine ⟨?_, h⟩
        have hinv : Subgroup.zpowers t₁ =
            (Subgroup.zpowers t₂).map (MulAut.conj γ₀⁻¹).toMonoidHom := by
          rw [← hswap, map_conj_cancel]
        rw [hinv]
        refine hconjD γ₀⁻¹ _ h ?_
        rw [← hinv]
        exact (Subgroup.zpowers_le.mpr ht₁T).trans hTS
    have hfc₁ : IsFiveCycleLine J (u3T P x J) ψ (Subgroup.zpowers t₁) := by
      unfold IsFiveCycleLine
      exact ⟨Subgroup.zpowers_le.mpr ht₁T, by rw [Nat.card_zpowers, hto₁], t₁, hTJ ht₁T,
        Subgroup.mem_zpowers t₁, hc₁1, hcent1⟩
    have hfc₂ : IsFiveCycleLine J (u3T P x J) ψ (Subgroup.zpowers t₂) := by
      unfold IsFiveCycleLine
      exact ⟨Subgroup.zpowers_le.mpr ht₂T, by rw [Nat.card_zpowers, hto₂], t₂, hTJ ht₂T,
        Subgroup.mem_zpowers t₂, hc₂1, hcent2⟩
    have hne : Subgroup.zpowers t₁ ≠ Subgroup.zpowers t₂ := by
      intro h
      apply ht₂t₁
      rw [h]
      exact Subgroup.mem_zpowers t₂
    refine ⟨Subgroup.zpowers t₁, Subgroup.zpowers t₂, hne, hfc₁, hfc₂, ?_⟩
    ext A
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact hD1' A
    · rintro (rfl | rfl | rfl)
      · exact hx0
      · exact h12.1
      · exact h12.2
  · left
    ext A
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hAD
      rcases hD1' A hAD with h | h | h
      · exact h
      · exact absurd (Or.inl (h ▸ hAD)) hA
      · exact absurd (Or.inr (h ▸ hAD)) hA
    · rintro rfl
      exact hx0

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
