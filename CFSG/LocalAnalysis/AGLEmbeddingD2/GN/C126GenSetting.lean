module

public import CFSG.Quasithin.Background.C1GNNotation
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

structure GenSetting (H T M V Y : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  min : MinParabolic H T M
  charTwo : CharTwo H
  red : IsTwoReducedIn H V
  hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  hVZ : V = VZ T H
  Y_le : Y ≤ H
  Y_res : twoResidual Y = Y
  Y_C : Y ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H
  Y_card : Nat.card (autI hV Y) = 3
  Q_norm : pCoreOf 2 H ≤ Subgroup.normalizer (Y : Set G)
  S_norm : baum T ≤ Subgroup.normalizer (Y : Set G)
  gen : Y ⊔ T = H

theorem charTwo_of_pCore_le {X U : Subgroup G} (hF : CharTwo X) (hQU : pCoreOf 2 X ≤ U)
    (hUX : U ≤ X) : CharTwo U := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hF hUX hQU

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hB
  have h2 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h3 := Subgroup.relIndex_mul_card A B
  have h4 : A ⊓ (B ⊔ A) = A := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [sup_comm] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem twoResidual_mono {A B : Subgroup G} (h : A ≤ B) : twoResidual A ≤ twoResidual B := by
  have hBn : A ≤ Subgroup.normalizer (twoResidual B : Set G) :=
    h.trans (le_normalizer_twoResidual B)
  have hn : A ≤ Subgroup.normalizer ((A ⊓ twoResidual B : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hBn hg⟩
  have h2 : ∀ y ∈ A, ∃ k : ℕ, y ^ 2 ^ k ∈ A ⊓ twoResidual B := fun y hy => by
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient B y (h hy)
    exact ⟨k, A.pow_mem hy _, hk⟩
  exact (twoResidual_le_of_isTwoQuotient inf_le_left hn h2).trans inf_le_right

@[expose] def R₁ (H T : Subgroup G) : Subgroup G := pCoreOf 2 H ⊔ baum T

theorem not_mem_pCoreOf_of_orderOf_three (H : Subgroup G) {x : G} (hx3 : orderOf x = 3) :
    x ∉ pCoreOf 2 H := by
  intro hx
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hx⟩
  have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h1
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
  omega

omit [Finite G] in
theorem pCoreOf_le_R₁ (H T : Subgroup G) : pCoreOf 2 H ≤ R₁ H T := le_sup_left

omit [Finite G] in
theorem baum_le_R₁ (H T : Subgroup G) : baum T ≤ R₁ H T := le_sup_right

namespace GenSetting

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} (s : GenSetting H T M V Y hV)

include s

omit [Finite G] in
theorem hT : IsSylowTwoOf T H := s.min.isSylow

omit [Finite G] in
theorem H_le_N : H ≤ Subgroup.normalizer (V : Set G) := s.red.2.1

omit [Finite G] in
theorem not_H_le_C : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
  s.hJ ((thompsonJ_le T).trans (s.hT.1.trans h))

theorem Q_le_T : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf s.hT

theorem Q_le_C : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) :=
  MinParabolic.pCoreOf_le_centralizer s.red

theorem T_inf_C : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H :=
  s.min.inf_centralizer_eq_pCoreOf s.red s.not_H_le_C

theorem R_le_T : R₁ H T ≤ T := sup_le s.Q_le_T (C1GN.baum_le T)

theorem R_pGroup : IsPGroup 2 (R₁ H T) := s.hT.2.1.to_le s.R_le_T

theorem thompsonJ_R : thompsonJ (R₁ H T) = thompsonJ T :=
  B6.thompsonJ_eq_of_le ((B6.thompsonJ_le_baum T).trans (baum_le_R₁ H T)) s.R_le_T

theorem baum_R : baum (R₁ H T) = baum T := by
  ext x
  unfold baum
  rw [s.thompsonJ_R]
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨s.R_le_T h.1, h.2⟩, fun h => ⟨baum_le_R₁ H T (by
    simpa [baum] using h), h.2⟩⟩

theorem Y_inf_T : Y ⊓ T ≤ pCoreOf 2 H := by
  intro t ht
  have htN : t ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (s.Y_le ht.1)
  set φ := convI hV ⟨t, htN⟩ with hφ
  have h3 : orderOf φ ∣ 3 := by
    have hmem : φ ∈ autI hV Y := convI_mem_autI hV ht.1 htN
    have := Subgroup.orderOf_dvd_natCard (autI hV Y) hmem
    rwa [s.Y_card] at this
  obtain ⟨k, hk⟩ := s.hT.2.1 ⟨t, ht.2⟩
  have ht1 : t ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hpow : φ ^ (2 ^ k) = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨t, htN⟩ : Subgroup.normalizer (V : Set G)) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using ht1)
    rw [this, map_one]
  have h2 : orderOf φ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf φ = 1 := by
    have := Nat.dvd_gcd h3 h2
    have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    rw [hg] at this
    exact Nat.dvd_one.1 this
  have hφ1 : φ = 1 := orderOf_eq_one_iff.1 h1
  have hc : t ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV ⟨t, htN⟩).1 hφ1
  rw [← s.T_inf_C]
  exact ⟨ht.2, hc⟩

theorem Y_inf_R : Y ⊓ R₁ H T = Y ⊓ pCoreOf 2 H :=
  le_antisymm (le_inf inf_le_left ((inf_le_inf_left Y s.R_le_T).trans s.Y_inf_T))
    (inf_le_inf_left Y (pCoreOf_le_R₁ H T))

theorem Y_inf_C : Y ⊓ Subgroup.centralizer (V : Set G) = Y ⊓ pCoreOf 2 H :=
  le_antisymm (le_inf inf_le_left (s.Y_C))
    (inf_le_inf_left Y s.Q_le_C)

theorem relIndex_Y : (Y ⊓ pCoreOf 2 H).relIndex Y = 3 := by
  have h1 := card_autI_mul_card_inf hV (A := Y) (s.Y_le.trans s.H_le_N)
  rw [s.Y_card, s.Y_inf_C] at h1
  have h2 := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 H) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 H ≤ Y)] at h2
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 H) := Nat.card_pos
  have : (Y ⊓ pCoreOf 2 H).relIndex Y * Nat.card ↥(Y ⊓ pCoreOf 2 H) =
      3 * Nat.card ↥(Y ⊓ pCoreOf 2 H) := by rw [h2, ← h1]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem sandwich_Y {K : Subgroup G} (h1 : Y ⊓ pCoreOf 2 H ≤ K) (h2 : K ≤ Y) :
    K = Y ⊓ pCoreOf 2 H ∨ K = Y := by
  have h := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [s.relIndex_Y] at h
  have hdvd : (K.relIndex Y) ∣ 3 := Dvd.intro_left _ h
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1' | h3'
  · right
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.1 h1')
  · left
    rw [h3'] at h
    have : (Y ⊓ pCoreOf 2 H).relIndex K = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 this) h1

theorem exists_order_three : ∃ x ∈ Y, orderOf x = 3 := by
  have hdvd : 3 ∣ Nat.card Y := by
    have h2 := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 H) Y
    rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 H ≤ Y), s.relIndex_Y] at h2
    exact Dvd.intro _ h2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end GenSetting
theorem isSolvable_of_isPGroup_two {K : Subgroup G} (h : IsPGroup 2 K) :
    Group.IsSolvable ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isNilpotent
  infer_instance

namespace GenSetting

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} (s : GenSetting H T M V Y hV)

include s

omit [Finite G] in
theorem R_le_normalizer : R₁ H T ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le s.Q_norm s.S_norm

theorem P₁_le : Y ⊔ R₁ H T ≤ H := sup_le s.Y_le (s.R_le_T.trans s.hT.1)

omit [Finite G] in
theorem P₁_le_normalizer : Y ⊔ R₁ H T ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer s.R_le_normalizer

omit [Finite G] in
theorem card_P₁ : Nat.card ↥(Y ⊔ R₁ H T) * Nat.card ↥(Y ⊓ R₁ H T) =
    Nat.card Y * Nat.card (R₁ H T) :=
  card_sup_mul_card_inf_of_le_normalizer s.R_le_normalizer

theorem relIndex_R_P₁ : (R₁ H T).relIndex (Y ⊔ R₁ H T) = 3 := by
  have h1 := Subgroup.relIndex_mul_card (R₁ H T) (Y ⊔ R₁ H T)
  rw [inf_eq_left.2 (le_sup_right : R₁ H T ≤ Y ⊔ R₁ H T)] at h1
  have h2 := s.card_P₁
  have h3 := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 H) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 H ≤ Y), s.relIndex_Y] at h3
  rw [s.Y_inf_R] at h2
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 H) := Nat.card_pos
  have hposR : 0 < Nat.card (R₁ H T) := Nat.card_pos
  have : (R₁ H T).relIndex (Y ⊔ R₁ H T) * (Nat.card (R₁ H T) * Nat.card ↥(Y ⊓ pCoreOf 2 H)) =
      3 * (Nat.card (R₁ H T) * Nat.card ↥(Y ⊓ pCoreOf 2 H)) := by
    calc _ = Nat.card ↥(Y ⊔ R₁ H T) * Nat.card ↥(Y ⊓ pCoreOf 2 H) := by rw [← h1]; ring
      _ = Nat.card Y * Nat.card (R₁ H T) := h2
      _ = _ := by rw [← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposR hpos) this

theorem sylow_P₁ : IsSylowTwoOf (R₁ H T) (Y ⊔ R₁ H T) := by
  refine ⟨le_sup_right, s.R_pGroup, ?_⟩
  have : ((R₁ H T).subgroupOf (Y ⊔ R₁ H T)).index = 3 := s.relIndex_R_P₁
  rw [this]
  omega

theorem sandwich_P₁ {K : Subgroup G} (h1 : R₁ H T ≤ K) (h2 : K ≤ Y ⊔ R₁ H T) :
    K = R₁ H T ∨ K = Y ⊔ R₁ H T := by
  have hYK : Y ⊓ pCoreOf 2 H ≤ K ⊓ Y :=
    le_inf ((inf_le_right.trans (pCoreOf_le_R₁ H T)).trans h1) inf_le_left
  rcases s.sandwich_Y hYK inf_le_right with h | h
  · left
    refine le_antisymm (fun k hk => ?_) h1
    have hk' : k ∈ ((Y ⊔ R₁ H T : Subgroup G) : Set G) := h2 hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y (R₁ H T) s.R_le_normalizer] at hk'
    obtain ⟨y, hy, r, hr, rfl⟩ := hk'
    have hyK : y ∈ K ⊓ Y := ⟨by simpa using K.mul_mem hk (K.inv_mem (h1 hr)), hy⟩
    rw [h] at hyK
    exact (R₁ H T).mul_mem (pCoreOf_le_R₁ H T hyK.2) hr
  · right
    exact le_antisymm h2 (sup_le (inf_eq_right.1 h) h1)

theorem not_Y_le_normalizer_baum : ¬ Y ≤ Subgroup.normalizer (baum T : Set G) := by
  intro hY
  have hT : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hH : H ≤ Subgroup.normalizer (baum T : Set G) := s.gen ▸ sup_le hY hT
  have hS : baum T ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((C1GN.baum_le T).trans s.hT.1) hH
      (s.hT.2.1.to_le (C1GN.baum_le T))
  exact s.hJ ((B6.thompsonJ_le_baum T).trans (hS.trans s.Q_le_C))

theorem not_P₁_le_normalizer : ¬ Y ⊔ R₁ H T ≤ Subgroup.normalizer (R₁ H T : Set G) := by
  intro h
  apply s.not_Y_le_normalizer_baum
  have h1 : Y ≤ Subgroup.normalizer (R₁ H T : Set G) := le_sup_left.trans h
  intro y hy
  have := normalizer_le_normalizer_baum (R₁ H T) (h1 hy)
  rwa [s.baum_R] at this

theorem R_lt_P₁ : R₁ H T < Y ⊔ R₁ H T := by
  refine lt_of_le_of_ne le_sup_right fun h => s.not_P₁_le_normalizer ?_
  rw [← h]
  exact Subgroup.le_normalizer

theorem minParabolic_P₁ : MinParabolic (Y ⊔ R₁ H T) (R₁ H T) (R₁ H T) where
  isSylow := s.sylow_P₁
  not_normal := s.not_P₁_le_normalizer
  uniqueMax := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨⟨s.R_lt_P₁, fun K hK hKP => ?_⟩, le_rfl⟩, ?_⟩
    · rcases s.sandwich_P₁ hK.le hKP with h | h
      · exact absurd h hK.ne'
      · exact h
    · rintro N ⟨⟨hlt, _⟩, hRN⟩
      rcases s.sandwich_P₁ hRN hlt.le with h | h
      · exact h
      · exact absurd h hlt.ne

theorem Y_eq_sup {x : G} (hx : x ∈ Y) (hx3 : orderOf x = 3) :
    Y = (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x := by
  have hle : (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x ≤ Y :=
    sup_le inf_le_left ((Subgroup.zpowers_le).2 hx)
  rcases s.sandwich_Y le_sup_left hle with h | h
  · exfalso
    apply not_mem_pCoreOf_of_orderOf_three H hx3
    have : x ∈ (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [h] at this
    exact this.2
  · exact h.symm

theorem isSolvable_Y : Group.IsSolvable ↥Y := by
  obtain ⟨x, hxY, hx3⟩ := s.exists_order_three
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hxY, le_normalizer_pCoreOf 2 H (s.Y_le hxY)⟩
  have h2 : Group.IsSolvable ↥(Y ⊓ pCoreOf 2 H) :=
    isSolvable_of_isPGroup_two ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  have h3 : Group.IsSolvable ↥(Subgroup.zpowers x) := inferInstance
  rw [s.Y_eq_sup hxY hx3]
  exact A3.isSolvable_sup_of_le_normalizer hN

theorem isSolvable_P₁ : Group.IsSolvable ↥(Y ⊔ R₁ H T) := by
  have h1 := s.isSolvable_Y
  have h2 := isSolvable_of_isPGroup_two s.R_pGroup
  exact A3.isSolvable_sup_of_le_normalizer s.R_le_normalizer

theorem charTwo_P₁ : CharTwo (Y ⊔ R₁ H T) :=
  charTwo_of_pCore_le s.charTwo ((pCoreOf_le_R₁ H T).trans le_sup_right) s.P₁_le

theorem twoResidual_P₁ : twoResidual (Y ⊔ R₁ H T) = Y := by
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left s.P₁_le_normalizer
    (isTwoQuotient_of_sup_eq s.R_pGroup s.P₁_le_normalizer (sup_comm _ _))) ?_
  have := twoResidual_mono (le_sup_left : Y ≤ Y ⊔ R₁ H T)
  rwa [s.Y_res] at this

end GenSetting

end CFSG.AGLEmbeddingD2.GN
