module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Defs
public import CFSG.Quasithin.Recognition.M12AscTrans
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open Matrix
open scoped MatrixGroups

@[expose] def Sec4FusionEF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z → ∀ x ∈ E ⊔ F, orderOf x = 2 →
      (∃ h : G, h⁻¹ * x * h = z) ∨ ∃ h : G, h⁻¹ * x * h ∈ R

@[expose] def Sec4FusionY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z → ∀ y ∈ iX z E ⊔ iX z F, orderOf y = 2 →
      ∃ h ∈ iX z E ⊔ iX z F, h⁻¹ * y * h ∈ E ⊔ F

@[expose] def Step410Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
      (∃ φ : ↥(centralizer ({z} : Set G)) →* ProjGenLinGroup (Fin 2) (ZMod 7),
          Function.Surjective φ ∧ φ.ker = Q.subgroupOf (centralizer ({z} : Set G))) →
      ∃ t ∈ S₁, orderOf t = 2 ∧
        (∃ U : Subgroup G, U ≤ centralizer ({t} : Set G) ∧ Nat.card U = 9) ∧
        ∀ h : G, h⁻¹ * t * h ∉ R

theorem card_PGL27 : Nat.card (ProjGenLinGroup (Fin 2) (ZMod 7)) = 336 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [CFSG.BenderSuzuki.External.huppertXI13_card_pgl2, Nat.card_zmod]
  norm_num

theorem card_GL32 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem factorization_two_pow_mul {k m : ℕ} (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))]
  simp

theorem card_eq_card_ker_mul {H K : Type*} [Group H] [Group K] (φ : H →* K)
    (hφ : Function.Surjective φ) : Nat.card H = Nat.card φ.ker * Nat.card K := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]

theorem orderOf_inv_mul_mul {G : Type*} [Group G] (a t : G) :
    orderOf (a⁻¹ * t * a) = orderOf t := by
  have := orderOf_injective (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective t
  simpa [MulAut.conj_apply] using this

theorem iX_le {G : Type} [Group G] (z : G) (X : Subgroup G) :
    iX z X ≤ centralizer ({z} : Set G) ⊓ normalizer (X : Set G) := by
  rw [iX, AS76b.oUpperTwoPrime, closure_le]
  exact fun _ hx => hx.1

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_le_centralizer_of_isPGroup {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) :
    AS76b.oddCoreIn (normalizer (Q : Set G)) ≤ centralizer (Q : Set G) := by
  intro o ho
  rw [mem_centralizer_iff]
  intro q hq
  have hoN : o ∈ normalizer (Q : Set G) := AS76b.oddCoreIn_le _ ho
  have hqO : q ∈ normalizer ((AS76b.oddCoreIn (normalizer (Q : Set G)) : Subgroup G) : Set G) :=
    AS76b.le_normalizer_oddCoreIn _ (le_normalizer hq)
  have hkQ : q * o * q⁻¹ * o⁻¹ ∈ Q := by
    rw [show q * o * q⁻¹ * o⁻¹ = q * (o * q⁻¹ * o⁻¹) by group]
    exact Q.mul_mem hq ((mem_normalizer_iff.mp hoN _).mp (Q.inv_mem hq))
  have hkO : q * o * q⁻¹ * o⁻¹ ∈ AS76b.oddCoreIn (normalizer (Q : Set G)) :=
    mul_mem ((mem_normalizer_iff.mp hqO o).mp ho) (inv_mem ho)
  have hk : q * o * q⁻¹ * o⁻¹ ∈ AS76b.oddCoreIn (normalizer (Q : Set G)) ⊓ Q := ⟨hkO, hkQ⟩
  rw [AS76b.oddCoreIn_inf_eq_bot hQ2, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk
  exact hk

theorem eq_of_le_sup_oddCoreIn {Q T : Subgroup G} (hT2 : IsPGroup 2 T) (hQT : Q ≤ T)
    (hT : T ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) : T = Q := by
  refine le_antisymm (fun t ht => ?_) hQT
  have hQO : Q ≤ normalizer ((AS76b.oddCoreIn (normalizer (Q : Set G)) : Subgroup G) : Set G) :=
    le_normalizer.trans (AS76b.le_normalizer_oddCoreIn (normalizer (Q : Set G)))
  have ht2 : t ∈ ((Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)) : Subgroup G) : Set G) := hT ht
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q _ hQO] at ht2
  obtain ⟨q, hq, o, ho, rfl⟩ := ht2
  show q * o ∈ Q
  have hoT : o ∈ T := by
    have := T.mul_mem (T.inv_mem (hQT hq)) ht
    rwa [inv_mul_cancel_left] at this
  have ho1 : o ∈ AS76b.oddCoreIn (normalizer (Q : Set G)) ⊓ T := ⟨ho, hoT⟩
  rw [AS76b.oddCoreIn_inf_eq_bot hT2, mem_bot] at ho1
  rw [ho1, mul_one]
  exact hq

theorem odd_relIndex_sup_oddCoreIn {Q Y : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQY : Q ≤ Y) :
    Odd (Q.relIndex ((Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) ⊓ Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) ⊓ Y with hM
  have hQM : Q ≤ M := le_inf le_sup_left hQY
  have hQ' : IsPGroup 2 (Q.subgroupOf M) := hQ2.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  have hT2 : IsPGroup 2 ((S : Subgroup M).map M.subtype) := S.isPGroup'.map M.subtype
  have hQT : Q ≤ (S : Subgroup M).map M.subtype := fun q hq =>
    ⟨⟨q, hQM hq⟩, hS (show (⟨q, hQM hq⟩ : M) ∈ Q.subgroupOf M from hq), rfl⟩
  have hTQ := eq_of_le_sup_oddCoreIn hT2 hQT ((map_subtype_le _).trans inf_le_left)
  have hsyl : IsSylowOf 2 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
  rw [hTQ] at hsyl
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (isSylowOf_iff.mp hsyl).2.2)

theorem card_eq_of_ker_sup {Q Y K : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQY : Q ≤ Y) (hYK : Y ≤ K)
    (hK : Nat.card K = 2 * (Nat.card Q * 168)) (ψ : ↥Y →* GL (Fin 3) (ZMod 2))
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf Y) :
    Nat.card Y = Nat.card Q * 168 := by
  set M := (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) ⊓ Y with hM
  have h1 := card_eq_card_ker_mul ψ hψ
  rw [hker, ← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,
    card_GL32] at h1
  have h2 := Subgroup.relIndex_mul_card Q M
  rw [inf_eq_left.mpr (le_inf le_sup_left hQY)] at h2
  have hodd := odd_relIndex_sup_oddCoreIn hQ2 hQY
  have hdvd := Subgroup.card_dvd_of_le hYK
  rw [hK, h1, ← h2] at hdvd
  have ht : Q.relIndex M ∣ 2 := by
    refine Nat.dvd_of_mul_dvd_mul_right
      (Nat.mul_pos (Nat.card_pos (α := Q)) (by norm_num : 0 < 168)) ?_
    rwa [mul_assoc] at hdvd
  have ht1 : Q.relIndex M = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 ht with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [h1, ← h2, ht1, one_mul]

end OddCore

theorem step410_of (h47 : Step47) (hEF : Sec4FusionEF) (hY : Sec4FusionY)
    (hout : Step410Outer) : Step410 := by
  intro G _ _ A R g E F S₁ Q z hQ hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := hP
  have hS₁C : S₁ ≤ centralizer ({z} : Set G) := by
    intro s hs
    have hz : z ∈ centerIn S₁ := by rw [hQ.center_S₁]; exact mem_zpowers z
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hz.2) s hs
  have hcardC : Nat.card (centralizer ({z} : Set G)) = 2 ^ 11 * 21 := by
    rw [card_eq_card_ker_mul φ hφ, hker, card_PGL27,
      Nat.card_congr (subgroupOfEquivOfLe (hQ.le.trans hS₁C)).toEquiv, hQ.card]
    norm_num
  obtain ⟨⟨hQY, ψ, hψ, hψker⟩, -, -⟩ := h47 G A R g E F S₁ Q z hQ
  have hYC : iX z E ⊔ iX z F ≤ centralizer ({z} : Set G) :=
    sup_le ((iX_le z E).trans inf_le_left) ((iX_le z F).trans inf_le_left)
  have hcardY : Nat.card (iX z E ⊔ iX z F : Subgroup G) = 2 ^ 10 * 21 := by
    rw [card_eq_of_ker_sup (IsPGroup.of_card hQ.card) hQY hYC
      (by rw [hcardC, hQ.card]; norm_num) ψ hψ hψker, hQ.card]
    norm_num
  have hYindex : (iX z E ⊔ iX z F).relIndex (centralizer ({z} : Set G)) = 2 := by
    have h := Subgroup.relIndex_mul_card (iX z E ⊔ iX z F) (centralizer ({z} : Set G))
    rw [inf_eq_left.mpr hYC, hcardY, hcardC] at h
    omega
  have hCN : centralizer ({z} : Set G) ≤ normalizer ((iX z E ⊔ iX z F : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYC).mp
      (Subgroup.normal_of_index_eq_two hYindex)
  have hS₁C' : IsSylowOf 2 S₁ (centralizer ({z} : Set G)) := hQ.sylow.of_le hS₁C le_top
  have hSY : IsSylowOf 2 (S₁ ⊓ (iX z E ⊔ iX z F)) (iX z E ⊔ iX z F) :=
    hS₁C'.inf_of_le_normalizer hYC hCN
  have hcS₁ : Nat.card S₁ = 2 ^ 11 := by
    rw [hS₁C'.card_eq, hcardC, factorization_two_pow_mul (by decide)]
  have hcSY : Nat.card (S₁ ⊓ (iX z E ⊔ iX z F) : Subgroup G) = 2 ^ 10 := by
    rw [hSY.card_eq, hcardY, factorization_two_pow_mul (by decide)]
  have hindex : (S₁ ⊓ (iX z E ⊔ iX z F)).relIndex S₁ = 2 := by
    have h := Subgroup.relIndex_mul_card (S₁ ⊓ (iX z E ⊔ iX z F)) S₁
    rw [inf_eq_left.mpr inf_le_left, hcSY, hcS₁] at h
    omega
  have hcardS : Nat.card S₁ = 2 ^ (Nat.card G).factorization 2 := by
    have := hQ.sylow.card_eq
    rwa [card_top] at this
  obtain ⟨t, htS, ht2, ⟨U, hUt, hU9⟩, htR⟩ := hout G A R g E F S₁ Q z hQ ⟨φ, hφ, hker⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have htz : ∀ c : G, c⁻¹ * t * c ≠ z := by
    intro c hc
    have hle : rightConjugate U c ≤ centralizer ({z} : Set G) := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have hu := mem_centralizer_singleton_iff.mp (hUt hx)
      rw [mem_centralizer_singleton_iff, ← hc]
      calc x * (c⁻¹ * t * c) = c⁻¹ * ((c * x * c⁻¹) * t) * c := by group
        _ = c⁻¹ * (t * (c * x * c⁻¹)) * c := by rw [hu]
        _ = (c⁻¹ * t * c) * x := by group
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [rightConjugate_card, hU9, hcardC] at hdvd
    omega
  have hQu : ∀ a : G, a⁻¹ * t * a ∉ S₁ ⊓ (iX z E ⊔ iX z F) := by
    intro a ha
    obtain ⟨h, -, hhEF⟩ := hY G A R g E F S₁ Q z hQ _ (mem_inf.mp ha).2
      (by rw [orderOf_inv_mul_mul]; exact ht2)
    have hx2 : orderOf (h⁻¹ * (a⁻¹ * t * a) * h) = 2 := by
      rw [orderOf_inv_mul_mul, orderOf_inv_mul_mul, ht2]
    have hconj : ∀ b : G, b⁻¹ * (h⁻¹ * (a⁻¹ * t * a) * h) * b =
        (a * h * b)⁻¹ * t * (a * h * b) := fun b => by group
    rcases hEF G A R g E F S₁ Q z hQ _ hhEF hx2 with ⟨b, hb⟩ | ⟨b, hb⟩
    · rw [hconj] at hb
      exact htz _ hb
    · rw [hconj] at hb
      exact htR _ hb
  obtain ⟨X₀, hX₀, hidx, -, -⟩ := CFSG.Quasithin.thompson_transfer_index_two
    (Sylow.ofCard S₁ hcardS) (Q := S₁ ⊓ (iX z E ⊔ iX z F))
    (by rw [Sylow.coe_ofCard]; exact hindex) htt (by rw [Sylow.coe_ofCard]; exact htS) hQu
  exact ⟨X₀, hX₀, hidx⟩

end CFSG.ComponentClassification.AS81
