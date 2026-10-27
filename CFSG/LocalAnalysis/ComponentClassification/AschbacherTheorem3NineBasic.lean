module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndexBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem exists_four_of_involutions {a b : X} (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hcomm : a * b = b * a) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) = 4 ∧
      Open.IsElemAbelian 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.zpowers a
  set B := Subgroup.zpowers b
  have horda : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hordb : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hmem2 : ∀ c : X, orderOf c = 2 → ∀ x ∈ Subgroup.zpowers c, x = 1 ∨ x = c := by
    intro c hc x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hc]
    rcases Int.emod_two_eq_zero_or_one i with h0 | h1
    · left
      simp [h0]
    · right
      simp [h1]
  have hcommAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    rcases hmem2 a horda x hx with rfl | rfl <;> rcases hmem2 b hordb y hy with rfl | rfl <;>
      simp [hcomm]
  have hAC : A ≤ Subgroup.centralizer (B : Set X) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hcommAB x hx y hy).symm
  have hBN : B ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.le_centralizer_iff.mp hAC).trans (Subgroup.centralizer_le_normalizer _)
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    rw [Subgroup.mem_bot]
    rcases hmem2 a horda x hxa with h1 | rfl
    · exact h1
    · rcases hmem2 b hordb x hxb with h2 | h2
      · exact absurd h2 ha1
      · exact absurd h2 hab
  have hcard : Nat.card (A ⊔ B : Subgroup X) = 4 := by
    rw [card_sup_of_le_normalizer hBN hAB, Nat.card_zpowers, Nat.card_zpowers, horda, hordb]
  have hEcomm : IsMulCommutative (A ⊔ B : Subgroup X) :=
    isMulCommutative_sup (Subgroup.zpowers_isMulCommutative a)
      (Subgroup.zpowers_isMulCommutative b) hAC
  have hE2 : ∀ x ∈ A ⊔ B, x ^ 2 = 1 := by
    intro x hx
    have hxmem : x ∈ (A : Set X) * (B : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B
        (hAC.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hxmem
    have hu2 : u ^ 2 = 1 := by rcases hmem2 a horda u hu with rfl | rfl <;> simp [ha2]
    have hw2 : w ^ 2 = 1 := by rcases hmem2 b hordb w hw with rfl | rfl <;> simp [hb2]
    calc (u * w) ^ 2 = u * (w * u) * w := by simp only [pow_two, mul_assoc]
      _ = u * (u * w) * w := by rw [hcommAB u hu w hw]
      _ = u ^ 2 * w ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [hu2, hw2, one_mul]
  exact ⟨hcard, hEcomm, hE2⟩

theorem exists_four_le {T : Subgroup X} (hm : 1 < pRank 2 T) :
    ∃ E : Subgroup X, E ≤ T ∧ Nat.card E = 4 ∧ Open.IsElemAbelian 2 E := by
  obtain ⟨E₀, hE₀T, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two T
  have h4 : 4 ≤ Nat.card E₀ := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 T := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨a, ha, b, hb, ha1, hb1, hba⟩ := exists_two_ne_one h4
  have hab : a * b = b * a := congrArg Subtype.val (hE₀.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hcard4, hel⟩ := exists_four_of_involutions (hE₀.2 a ha) (hE₀.2 b hb) ha1 hb1
    (Ne.symm hba) hab
  exact ⟨_, (sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)).trans hE₀T,
    hcard4, hel⟩

theorem le_of_centralizers_le {E O H : Subgroup X} (hcard : Nat.card E = 4)
    (hel : Open.IsElemAbelian 2 E) (hEN : E ≤ Subgroup.normalizer (O : Set X))
    (hodd : Odd (Nat.card O))
    (hC : ∀ e ∈ E, e ≠ 1 → O ⊓ Subgroup.centralizer {e} ≤ H) : O ≤ H := by
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two E O (fun x => Subtype.ext (by rw [Subgroup.coe_pow]; exact hel.2 _ x.2))
    (by rw [hcard]; norm_num) (fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2))
    hEN]
  refine iSup_le fun e => iSup_le fun he => ?_
  exact hC e e.2 fun h1 => he (Subtype.ext h1)

theorem exists_sq_mem_of_lt {M N : Subgroup X} (hMN : M < N) (hN : IsPGroup 2 N) :
    ∃ y ∈ N, y ∈ Subgroup.normalizer (M : Set X) ∧ y ∉ M ∧ y ^ 2 ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : M ≤ N := hMN.le
  set M' := M.subgroupOf N
  have hM' : M' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hMN.ne
    apply le_antisymm hle
    intro x hx
    have : (⟨x, hx⟩ : N) ∈ M' := htop ▸ Subgroup.mem_top _
    exact this
  have : Group.IsNilpotent N := hN.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent M' hM'
  obtain ⟨y, hyN, hyM⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hN) y
  have hex : ∃ i : ℕ, y ^ (2 ^ (i + 1)) ∈ M' := by
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd (hk ▸ M'.one_mem) hyM
    · refine ⟨k, ?_⟩
      rw [← hk, pow_orderOf_eq_one]
      exact M'.one_mem
  classical
  set i₀ := Nat.find hex
  have hi₀ : y ^ (2 ^ (i₀ + 1)) ∈ M' := Nat.find_spec hex
  have hz : y ^ (2 ^ i₀) ∉ M' := by
    rcases Nat.eq_zero_or_pos i₀ with h0 | hpos
    · rw [h0, pow_zero, pow_one]
      exact hyM
    · have hmin := Nat.find_min hex (show i₀ - 1 < i₀ by omega)
      rwa [show i₀ - 1 + 1 = i₀ by omega] at hmin
  refine ⟨((y ^ (2 ^ i₀) : N) : X), (y ^ (2 ^ i₀)).2, ?_,
    fun h => hz (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  · have hzN : y ^ (2 ^ i₀) ∈ Subgroup.normalizer (M' : Set N) :=
      Subgroup.pow_mem _ hyN _
    rw [← Subgroup.subgroupOf_normalizer_eq hle] at hzN
    exact hzN
  · have : (y ^ (2 ^ i₀)) ^ 2 = y ^ (2 ^ (i₀ + 1)) := by rw [← pow_mul, pow_succ]
    rw [← Subgroup.coe_pow, this]
    exact hi₀

theorem card_eq_two_pow_pRank {E : Subgroup X} (hE : Open.IsElemAbelian 2 E) :
    Nat.card E = 2 ^ pRank 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one]; exact hE.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have h1 : k ≤ pRank 2 E := CFSG.SectionRank.le_pRank one_lt_two le_rfl hE hk
  have h2 : pRank 2 E ≤ k := CFSG.SectionRank.pRank_le one_lt_two fun F hFE _ => by
    rw [← hk]
    exact Subgroup.card_le_of_le hFE
  rw [hk, le_antisymm h1 h2]

end CFSG.ComponentClassification.AschbacherTheorem3
