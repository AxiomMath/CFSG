module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResPairDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

namespace LieClAut

theorem isPGroup_zpowers_of_pow_three {Y : Type*} [Group Y] {x : Y} (hx : x ^ 3 = 1) :
    IsPGroup 3 (zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  change (x ^ m) ^ 3 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem exists_commute_of_indepPair {Y : Type*} [Group Y] [Finite Y] {y₁ y₂ : Y}
    (hc : Commute y₁ y₂) (h1 : y₁ ^ 3 = 1) (h2 : y₂ ^ 3 = 1)
    (hind : ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j)
    {z : Y} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ y : Y, y ^ 3 = 1 ∧ Commute z y ∧ y ∉ zpowers z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : IsPGroup 3 ↥(zpowers y₁ ⊔ zpowers y₂ : Subgroup Y) := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three h1)
      (isPGroup_zpowers_of_pow_three h2) ?_
    refine (zpowers_le).2 ((centralizer_le_normalizer _) ?_)
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hw
    exact ((hc.zpow_right m).eq).symm
  obtain ⟨S, hS⟩ := hF.exists_le_sylow
  obtain ⟨S', hS'⟩ := (isPGroup_zpowers_of_pow_three hz3).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y S S'
  have hconjS : ∀ x ∈ zpowers y₁ ⊔ zpowers y₂, g * x * g⁻¹ ∈ (S' : Subgroup Y) := by
    intro x hx
    have hmem : (MulAut.conj g).toMonoidHom x ∈ ((g • S : Sylow 3 Y) : Subgroup Y) :=
      Subgroup.mem_map_of_mem _ (hS hx)
    rw [hg] at hmem
    simpa using hmem
  set w₁ := g * y₁ * g⁻¹ with hw₁
  set w₂ := g * y₂ * g⁻¹ with hw₂
  have hw₁S : w₁ ∈ (S' : Subgroup Y) := hconjS _ (mem_sup_left (mem_zpowers y₁))
  have hw₂S : w₂ ∈ (S' : Subgroup Y) := hconjS _ (mem_sup_right (mem_zpowers y₂))
  have hzS : z ∈ (S' : Subgroup Y) := hS' (mem_zpowers z)
  have hpow : ∀ (y : Y) (i : ℤ), (g * y * g⁻¹) ^ i = g * y ^ i * g⁻¹ := fun y i => by
    rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
  have hw3 : ∀ y : Y, y ^ 3 = 1 → (g * y * g⁻¹) ^ 3 = 1 := fun y hy => by
    rw [← MulAut.conj_apply, ← map_pow, hy, map_one]
  by_cases hcz : Commute z w₁ ∧ Commute z w₂
  ·
    by_cases h₁ : w₁ ∈ zpowers z
    · refine ⟨w₂, hw3 y₂ h2, hcz.2, fun h₂ => ?_⟩
      obtain ⟨a, ha⟩ := mem_zpowers_iff.1 h₁
      obtain ⟨b, hb⟩ := mem_zpowers_iff.1 h₂
      have hrel : y₁ ^ b * y₂ ^ (-a) = 1 := by
        have : w₁ ^ b * w₂ ^ (-a) = 1 := by
          rw [← ha, ← hb, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm a b, mul_neg,
            add_neg_cancel, zpow_zero]
        rw [hw₁, hw₂, hpow, hpow] at this
        have h' : g * (y₁ ^ b * y₂ ^ (-a)) * g⁻¹ = 1 := by
          rw [← this]
          group
        simpa using h'
      obtain ⟨hb3, ha3⟩ := hind _ _ hrel
      have hz1' : ∀ c : ℤ, (3 : ℤ) ∣ c → z ^ c = 1 := fun c hc' => by
        obtain ⟨d, rfl⟩ := hc'
        rw [zpow_mul, zpow_ofNat, hz3, one_zpow]
      have hy1 : y₁ = 1 := by
        have : w₁ = 1 := by
          rw [← ha]
          exact hz1' a (by simpa using (Int.dvd_neg.1 ha3))
        rw [hw₁] at this
        have h' : y₁ = g⁻¹ * (g * y₁ * g⁻¹) * g := by group
        rw [h', this]
        group
      have := hind 1 0 (by rw [hy1]; simp)
      omega
    · exact ⟨w₁, hw3 y₁ h1, hcz.1, h₁⟩
  ·
    have hP : IsPGroup 3 (S' : Subgroup Y) := S'.isPGroup'
    haveI : Nontrivial (S' : Subgroup Y) := ⟨⟨⟨z, hzS⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    haveI := hP.center_nontrivial
    have h3 : 3 ∣ Nat.card (center (S' : Subgroup Y)) := by
      rcases (hP.to_subgroup (center _)).card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card).ne'
      · exact h
    obtain ⟨c, hc3⟩ := exists_prime_orderOf_dvd_card' 3 h3
    set w : Y := ((c : (S' : Subgroup Y)) : Y) with hwdef
    have hwc : ∀ x ∈ (S' : Subgroup Y), Commute x w := fun x hx => by
      have := (mem_center_iff.1 c.2) ⟨x, hx⟩
      exact congrArg Subtype.val this
    have hwo : orderOf w = 3 := by
      rw [hwdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc3]
    refine ⟨w, by rw [← hwo]; exact pow_orderOf_eq_one w, hwc z hzS, fun hwz => hcz ?_⟩
    have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have hle : zpowers w ≤ zpowers z := (zpowers_le).2 hwz
    have heq : zpowers w = zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hwo])
    have hzw : z ∈ zpowers w := heq ▸ mem_zpowers z
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hzw
    exact ⟨((hwc _ hw₁S).zpow_right m).symm, ((hwc _ hw₂S).zpow_right m).symm⟩

theorem three_le_pRank_of_commute {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) {ρ : G} (hρH : ρ ∈ H)
    (hρ3 : ρ ^ 3 = 1) (hρE : ρ ∉ E) (hρc : ∀ a ∈ E, a * ρ = ρ * a) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set G)) := by
  set Q := E ⊔ zpowers ρ with hQ
  have hQab : CFSG.Assembly.IsElemAbelian 3 Q :=
    CFSG.RankThree.PartTwo.Sec4.isElemAbelian_sup_zpowers hE hρ3 hρc
  have hQc : Nat.card Q = 3 ^ 3 := by
    rw [hQ, CFSG.RankThree.PartTwo.Sec4.card_sup_zpowers_of_not_mem hρ3 hρc hρE, hEc]
    norm_num
  refine CFSG.SectionRank.le_pRank (by norm_num) (le_inf (sup_le hEH ((zpowers_le).2 hρH))
    fun q hq => ?_) hQab hQc
  rw [mem_centralizer_iff]
  intro a ha
  exact congrArg Subtype.val (hQab.1.is_comm.comm ⟨a, le_sup_left (a := E) ha⟩ ⟨q, hq⟩)

theorem conj_apply_mul {X : Type*} [Group X] (β : MulAut X) (x : X) :
    MulAut.conj (β x) * β = β * MulAut.conj x := by
  ext y
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem isElemAbelian_zpowers {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    IsElemAbelian 3 (zpowers x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨m, hm⟩ := mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 b.2
    change (a : G) * b = b * a
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isElemAbelian_card_of_pair {G : Type} [Group G] [Finite G] {y₁ y₂ : G}
    (hc : Commute y₁ y₂) (h1 : y₁ ^ 3 = 1) (h2 : y₂ ^ 3 = 1)
    (hind : ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j) :
    IsElemAbelian 3 (zpowers y₁ ⊔ zpowers y₂) ∧ Nat.card ↥(zpowers y₁ ⊔ zpowers y₂) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy₁ : y₁ ≠ 1 := fun h => by
    have := (hind 1 0 (by rw [h]; simp)).1
    omega
  have hcomm : ∀ a ∈ zpowers y₁, a * y₂ = y₂ * a := fun a ha => by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    exact (hc.zpow_left m).eq
  have hy₂ : y₂ ∉ zpowers y₁ := fun h => by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 h
    have := (hind (-m) 1 (by rw [zpow_one, ← hm, ← zpow_add, neg_add_cancel, zpow_zero])).2
    omega
  refine ⟨CFSG.RankThree.PartTwo.Sec4.isElemAbelian_sup_zpowers (isElemAbelian_zpowers h1) h2
    hcomm, ?_⟩
  rw [CFSG.RankThree.PartTwo.Sec4.card_sup_zpowers_of_not_mem h2 hcomm hy₂, Nat.card_zpowers,
    orderOf_eq_prime h1 hy₁]

theorem three_le_pRank_of_fixesPair {X C : Type} [Group X] [Finite X] [Group C] [Finite C]
    [IsCyclic C] (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H)
    (Φ : MulAut X →* C) (hΦ : ∀ x : X, Φ (MulAut.conj x) = 1)
    (hD : ∀ δ : MulAut X, Φ δ = 1 → δ ∈ (MulAut.conj : X →* MulAut X).range)
    (htw : ∀ τ : C, τ ^ 3 = 1 → τ ≠ 1 → ∃ β₀ : MulAut X, β₀ ^ 3 = 1 ∧ Φ β₀ = τ)
    (hfix : ∀ γ : MulAut X, γ ^ 3 = 1 → γ ∉ (MulAut.conj : X →* MulAut X).range →
      KFactProofs.Stroth.AlmostSimple.FixesIndepPair 3 γ)
    (huniq : ∀ E F : Subgroup X, IsElemAbelian 3 E → Nat.card E = 9 → IsElemAbelian 3 F →
      Nat.card F = 9 → ∃ g : X, ∀ e ∈ E, g * e * g⁻¹ ∈ F)
    {α : MulAut X} (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have hconj := conj_injective_of_center hc
  have hΦI : ∀ δ ∈ I, Φ δ = 1 := by
    rintro _ ⟨x, rfl⟩
    exact hΦ x
  obtain ⟨k, hk⟩ := hα
  have hφk : Φ α ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hφ1 : Φ α ≠ 1 := fun h1 => hαn (hD α h1)
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hφk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hφ1 (orderOf_eq_one_iff.1 (by rw [hjo, pow_zero]))
  set α₁ := α ^ 3 ^ (j - 1) with hα₁
  have hτ' : Φ α₁ = Φ α ^ 3 ^ (j - 1) := by rw [hα₁, map_pow]
  have hτ3 : Φ α₁ ^ 3 = 1 := by
    rw [hτ', ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hjo,
      pow_orderOf_eq_one]
  have hτ1 : Φ α₁ ≠ 1 := by
    intro h
    rw [hτ'] at h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hjo] at h1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h1
    omega
  obtain ⟨β₀, hβ₀3, hβ₀Φ⟩ := htw _ hτ3 hτ1
  have hβ₀H : β₀ ∈ H := by
    have hδ : β₀ * α₁⁻¹ ∈ I := hD _ (by rw [map_mul, map_inv, hβ₀Φ, mul_inv_cancel])
    have : β₀ = (β₀ * α₁⁻¹) * α₁ := by group
    rw [this]
    exact H.mul_mem (hinn hδ) (H.pow_mem hαH _)
  have hβ₀n : β₀ ∉ I := fun h => hτ1 (by rw [← hβ₀Φ]; exact hΦI _ h)
  by_cases hEI : E ≤ I
  ·
    set E₀ := E.comap (MulAut.conj : X →* MulAut X) with hE₀
    have hE₀c : Nat.card E₀ = 9 := by
      rw [← Subgroup.card_map_of_injective hconj, hE₀, Subgroup.map_comap_eq,
        inf_eq_right.2 hEI, hEc]
    have hE₀ab : IsElemAbelian 3 E₀ := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hconj ?_)⟩⟩, fun x hx => hconj ?_⟩
      · have := hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩
        simpa using congrArg Subtype.val this
      · rw [map_pow, hE.2 _ hx, map_one]
    obtain ⟨y₁, y₂, hc12, h1, h2, hind, hf1, hf2⟩ := hfix β₀ hβ₀3 hβ₀n
    obtain ⟨hFab, hFc⟩ := isElemAbelian_card_of_pair hc12 h1 h2 hind
    obtain ⟨g, hg⟩ := huniq E₀ _ hE₀ab hE₀c hFab hFc
    have hfixF : ∀ x ∈ zpowers y₁ ⊔ zpowers y₂, β₀ x = x := by
      have hle : zpowers y₁ ⊔ zpowers y₂ ≤ β₀.toMonoidHom.eqLocus (MonoidHom.id X) :=
        sup_le ((zpowers_le).2 hf1) ((zpowers_le).2 hf2)
      exact fun x hx => hle hx
    set β := (MulAut.conj g)⁻¹ * β₀ * MulAut.conj g with hβ
    have hβe : ∀ e ∈ E₀, β e = e := fun e he => by
      have h := hfixF _ (hg e he)
      rw [hβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, h]
      simp only [MulAut.inv_apply, MulAut.conj_symm_apply]
      group
    refine three_le_pRank_of_commute hEH hE hEc (ρ := β) ?_ ?_ ?_ ?_
    · exact H.mul_mem (H.mul_mem (H.inv_mem (hinn ⟨g, rfl⟩)) hβ₀H) (hinn ⟨g, rfl⟩)
    · have : β = MulAut.conj (MulAut.conj g)⁻¹ β₀ := by rw [hβ, MulAut.conj_apply, inv_inv]
      rw [this, ← map_pow, hβ₀3, map_one]
    · intro hβE
      apply hβ₀n
      have h := hEI hβE
      have : β₀ = MulAut.conj g * β * (MulAut.conj g)⁻¹ := by rw [hβ]; group
      rw [this]
      exact I.mul_mem (I.mul_mem ⟨g, rfl⟩ h) (I.inv_mem ⟨g, rfl⟩)
    · intro a ha
      obtain ⟨e, rfl⟩ := hEI ha
      have := conj_apply_mul β e
      rwa [hβe e ha] at this
  ·
    obtain ⟨γ, hγE, hγn⟩ := Set.not_subset.1 hEI
    have hγ3 : γ ^ 3 = 1 := hE.2 γ hγE
    have hγo : orderOf γ = 3 := orderOf_eq_prime hγ3 fun h => hγn (h ▸ I.one_mem)
    have hΦγ1 : Φ γ ≠ 1 := fun h => hγn (hD γ h)
    have hΦγ3 : Φ γ ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
    have hzγ : Nat.card (zpowers γ) = 3 := by rw [Nat.card_zpowers, hγo]
    obtain ⟨a, haE, haγ⟩ : ∃ a ∈ E, a ∉ zpowers γ := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.card_le_of_le (H := E) (K := zpowers γ) hcon
      omega
    have ha3 : a ^ 3 = 1 := hE.2 a haE
    obtain ⟨ζ, hζE, hζI, hζ1⟩ : ∃ ζ ∈ E, ζ ∈ I ∧ ζ ≠ 1 := by
      by_cases hΦa : Φ a = 1
      · exact ⟨a, haE, hD a hΦa, fun h => haγ (h ▸ one_mem _)⟩
      have hΦa3 : Φ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
      rcases eq_or_eq_inv_of_isCyclic hΦγ3 hΦγ1 hΦa3 hΦa with h | h
      · refine ⟨a * γ⁻¹, E.mul_mem haE (E.inv_mem hγE), hD _ (by rw [map_mul, map_inv, h,
          mul_inv_cancel]), fun h1 => haγ ?_⟩
        rw [mul_inv_eq_one] at h1
        rw [h1]
        exact mem_zpowers γ
      · refine ⟨a * γ, E.mul_mem haE hγE, hD _ (by rw [map_mul, h, inv_mul_cancel]),
          fun h1 => haγ ?_⟩
        rw [mul_eq_one_iff_eq_inv] at h1
        rw [h1]
        exact inv_mem (mem_zpowers γ)
    obtain ⟨z, rfl⟩ := hζI
    have hz1 : z ≠ 1 := fun h => hζ1 (by rw [h, map_one])
    have hz3 : z ^ 3 = 1 := hconj (by rw [map_pow, hE.2 _ hζE, map_one])
    have hcomγ : MulAut.conj z * γ = γ * MulAut.conj z :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hζE⟩ ⟨γ, hγE⟩)
    have hγz : γ z = z := hconj (by
      have h := conj_apply_mul γ z
      rw [← hcomγ] at h
      exact mul_right_cancel h)
    obtain ⟨y₁, y₂, hc12, h1, h2, hind, hf1, hf2⟩ := hfix γ hγ3 hγn
    set Fx := γ.toMonoidHom.eqLocus (MonoidHom.id X) with hFx
    have hy₁F : y₁ ∈ Fx := hf1
    have hy₂F : y₂ ∈ Fx := hf2
    have hzF : z ∈ Fx := hγz
    obtain ⟨y, hy3, hyz, hyn⟩ := exists_commute_of_indepPair (Y := Fx) (y₁ := ⟨y₁, hy₁F⟩)
      (y₂ := ⟨y₂, hy₂F⟩) (Subtype.ext hc12.eq) (Subtype.ext h1) (Subtype.ext h2)
      (fun i j hij => hind i j (by simpa using congrArg Subtype.val hij)) (z := ⟨z, hzF⟩)
      (Subtype.ext hz3) (fun h => hz1 (congrArg Subtype.val h))
    have hyγ : γ (y : X) = y := y.2
    have hcz : ∀ b ∈ zpowers (MulAut.conj z), b * γ = γ * b := fun b hb => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
      exact ((Commute.zpow_left hcomγ m)).eq
    have hγnz : γ ∉ zpowers (MulAut.conj z) := fun h => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 h
      exact hγn ⟨z ^ m, map_zpow _ _ _⟩
    have hzo : orderOf (MulAut.conj z) = 3 := orderOf_eq_prime (hE.2 _ hζE) hζ1
    have hsup : zpowers (MulAut.conj z) ⊔ zpowers γ = E := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le ((zpowers_le).2 hζE) ((zpowers_le).2 hγE)) ?_
      rw [CFSG.RankThree.PartTwo.Sec4.card_sup_zpowers_of_not_mem hγ3 hcz hγnz,
        Nat.card_zpowers, hzo, hEc]
    have hEI3 : E ⊓ I = zpowers (MulAut.conj z) := by
      have hle : zpowers (MulAut.conj z) ≤ E ⊓ I := (zpowers_le).2 ⟨hζE, z, rfl⟩
      have hdvd : Nat.card ↥(E ⊓ I) ∣ 9 := hEc ▸ Subgroup.card_dvd_of_le inf_le_left
      have h3 : 3 ∣ Nat.card ↥(E ⊓ I) := by
        have := Subgroup.card_dvd_of_le hle
        rwa [Nat.card_zpowers, hzo] at this
      have hne : Nat.card ↥(E ⊓ I) ≠ 9 := fun h9 => hEI (by
        have := Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ I ≤ E) (by rw [h9, hEc])
        rw [← this]
        exact inf_le_right)
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
        (show Nat.card ↥(E ⊓ I) ∣ 3 ^ 2 from hdvd)
      have hi1 : i = 1 := by
        interval_cases i
        · rw [hi', pow_zero] at h3
          omega
        · rfl
        · exact absurd hi' (by simpa using hne)
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [hi', hi1, Nat.card_zpowers, hzo, pow_one]
    refine three_le_pRank_of_commute hEH hE hEc (ρ := MulAut.conj (y : X)) (hinn ⟨_, rfl⟩)
      (by rw [← map_pow, show (y : X) ^ 3 = 1 from congrArg Subtype.val hy3, map_one]) ?_ ?_
    · intro hyE
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hEI3 ▸ ⟨hyE, _, rfl⟩ : MulAut.conj (y : X) ∈
        zpowers (MulAut.conj z))
      apply hyn
      refine mem_zpowers_iff.2 ⟨m, Subtype.ext (hconj ?_)⟩
      rw [← hm, Subgroup.coe_zpow, map_zpow]
    · intro b hb
      rw [← hsup] at hb
      have hcen : zpowers (MulAut.conj z) ⊔ zpowers γ ≤
          centralizer ({MulAut.conj (y : X)} : Set (MulAut X)) := by
        refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_) <;>
          rw [mem_centralizer_singleton_iff]
        · rw [← map_mul, ← map_mul, show (y : X) * z = z * y from
            (congrArg Subtype.val hyz.eq).symm]
        · have := conj_apply_mul γ (y : X)
          rw [hyγ] at this
          exact this.symm
      exact mem_centralizer_singleton_iff.1 (hcen hb)

end LieClAut

end CFSG.LocalAnalysis.RankThreeTheoremC
