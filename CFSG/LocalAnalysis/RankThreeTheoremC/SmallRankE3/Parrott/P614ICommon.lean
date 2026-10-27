module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G} {x z : G}
  {H S K : Subgroup G}

theorem core_le_S (hyp : Hyp P M x z H S) : pCoreOf 2 H ≤ S := hyp.optimal.core_le

theorem S_le_H (hyp : Hyp P M x z H S) : S ≤ H := hyp.optimal.maxInv.1.1

theorem S_le_M (hyp : Hyp P M x z H S) : S ≤ M :=
  hyp.optimal.ext.pair.isMax.1.1.trans inf_le_right

theorem isPGroup_S (hyp : Hyp P M x z H S) : IsPGroup 2 S := hyp.optimal.maxInv.1.2.1

theorem S_ne_bot (hyp : Hyp P M x z H S) : S ≠ ⊥ := hyp.optimal.ext.pair.ne_bot

theorem B_le_normalizer_S (hyp : Hyp P M x z H S) :
    zpowers x ⊔ zpowers z ≤ normalizer (S : Set G) := hyp.optimal.maxInv.1.2.2

theorem isPGroup_core (hyp : Hyp P M x z H S) : IsPGroup 2 (pCoreOf 2 H) :=
  (isPGroup_S hyp).to_le (core_le_S hyp)

theorem core_le_M (hyp : Hyp P M x z H S) : pCoreOf 2 H ≤ M := (core_le_S hyp).trans (S_le_M hyp)

theorem H_le_normalizer_core (hyp : Hyp P M x z H S) :
    H ≤ normalizer (pCoreOf 2 H : Set G) := hyp.optimal.eq_normalizer.le

theorem isTwoLocal_H (hyp : Hyp P M x z H S) : IsTwoLocal H := hyp.optimal.ext.pair.isTwoLocal

theorem charTwo_H (hyp : Hyp P M x z H S) :
    H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H :=
  hyp.setting.charTwo H (isTwoLocal_H hyp)

theorem B_le_H (hyp : Hyp P M x z H S) : zpowers x ⊔ zpowers z ≤ H := hyp.optimal.ext.pair.le

theorem z_pow_three (hyp : Hyp P M x z H S) : z ^ 3 = 1 := hyp.central.pow_eq_one

theorem z_ne_one (hyp : Hyp P M x z H S) : z ≠ 1 := hyp.central.ne_one

theorem orderOf_z (hyp : Hyp P M x z H S) : orderOf z = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (z_pow_three hyp) (z_ne_one hyp)

theorem z_mem_H (hyp : Hyp P M x z H S) : z ∈ H :=
  B_le_H hyp (mem_sup_right (mem_zpowers z))

theorem z_mem_K (h618 : Stage618 M H K z) : z ∈ K := h618.comp.mem (mem_zpowers z)

theorem z_mem_normalizer_S (hyp : Hyp P M x z H S) : z ∈ normalizer (S : Set G) :=
  B_le_normalizer_S hyp (mem_sup_right (mem_zpowers z))

theorem not_mem_of_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) {w : G} (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) : w ∉ Q := by
  intro hw
  obtain ⟨n, hn⟩ := hQ ⟨w, hw⟩
  have h1 : w ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : orderOf w ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_eq_prime hw3 hw1] at h2
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem z_not_mem_core (hyp : Hyp P M x z H S) : z ∉ pCoreOf 2 H :=
  not_mem_of_isPGroup_two (isPGroup_core hyp) (z_pow_three hyp) (z_ne_one hyp)

theorem exists_core_not_comm (hyp : Hyp P M x z H S) :
    ∃ o ∈ pCoreOf 2 H, o * z ≠ z * o := by
  by_contra hcon
  push Not at hcon
  refine z_not_mem_core hyp (charTwo_H hyp ⟨z_mem_H hyp, mem_centralizer_iff.2 fun o ho => ?_⟩)
  exact (hcon o ho)

omit [Finite G] in
theorem normalizer_le_normalizer_of_char {S₀ : Subgroup G} (h1 : S₀ ≤ S)
    (h3 : (S₀.subgroupOf S).Characteristic) :
    normalizer (S : Set G) ≤ normalizer (S₀ : Set G) := by
  have key : ∀ g ∈ normalizer (S : Set G), ∀ c ∈ S₀, g * c * g⁻¹ ∈ S₀ := by
    intro g hg c hc
    let φ : S ≃* S :=
      { toFun := fun s => ⟨g * s * g⁻¹, (mem_normalizer_iff.mp hg s).mp s.2⟩
        invFun := fun s => ⟨g⁻¹ * s * g, (mem_normalizer_iff''.mp hg s).mp s.2⟩
        left_inv := fun s => Subtype.ext (by simp [mul_assoc])
        right_inv := fun s => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
    have hc' : (⟨c, h1 hc⟩ : S) ∈ S₀.subgroupOf S := hc
    exact characteristic_iff_map_le.mp h3 φ (mem_map_of_mem φ.toMonoidHom hc')
  intro g hg
  refine mem_normalizer_iff.mpr fun c => ⟨key g hg c, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

theorem normalizer_S_le_M (hyp : Hyp P M x z H S) : normalizer (S : Set G) ≤ M := by
  refine hyp.optimal.char_le S le_rfl (S_ne_bot hyp) ?_
  rw [subgroupOf_self]
  exact Subgroup.topCharacteristic

theorem isMaxTwoInvariantIn_of_le (hyp : Hyp P M x z H S) {N : Subgroup G} (hN : IsTwoLocal N)
    (hBN : zpowers x ⊔ zpowers z ≤ N) (hNM : ¬ N ≤ M) (hSN : S ≤ N) :
    IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) N S := by
  refine ⟨⟨hSN, isPGroup_S hyp, B_le_normalizer_S hyp⟩, fun S' hS' hSS' => ?_⟩
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt := CFSG.Goldschmidt.G310.lt_inf_normalizer hS'.2.1 hSS' (Ne.symm hne)
  have hR : IsTwoInvariantIn (zpowers x ⊔ zpowers z) (N ⊓ M) (S' ⊓ normalizer (S : Set G)) := by
    refine ⟨le_inf (inf_le_left.trans hS'.1) (inf_le_right.trans (normalizer_S_le_M hyp)),
      hS'.2.1.to_le inf_le_left, ?_⟩
    exact (le_inf hS'.2.2 ((B_le_normalizer_S hyp).trans le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨S₁, hRS₁, hS₁⟩ := exists_isMaxTwoInvariantIn_of_le hR
  have hcard : Nat.card S < Nat.card S₁ :=
    (Subgroup.card_lt_of_lt hlt).trans_le (Subgroup.card_le_of_le hRS₁)
  have hS₁1 : S₁ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    have : 0 < Nat.card S := Nat.card_pos
    omega
  exact hyp.optimal.ext.max N S₁ ⟨hN, hBN, hNM, hS₁, hS₁1⟩ (Or.inl hcard)

theorem localPair_of_le (hyp : Hyp P M x z H S) {N : Subgroup G} (hN : IsTwoLocal N)
    (hBN : zpowers x ⊔ zpowers z ≤ N) (hNM : ¬ N ≤ M) (hSN : S ≤ N) : LocalPair M x z N S :=
  ⟨hN, hBN, hNM, isMaxTwoInvariantIn_of_le hyp hN hBN hNM hSN, hyp.optimal.char_le⟩

theorem sit_of_hyp (hyp : Hyp P M x z H S) : Sit P M x z :=
  ⟨hyp.setting, hyp.u0, hyp.d1, hyp.situation, hyp.point, hyp.central⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
