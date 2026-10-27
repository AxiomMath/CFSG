module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

namespace Endings

variable {G : Type} [Group G] [Finite G]

structure Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T : Subgroup G) : Prop where
  seitz : SeitzSetting G L
  three_le : 3 ≤ f
  lieModel : LieModel L .PSL 2 2 f
  card_sylow : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  orderOf_t : orderOf t = 2
  mem_centralizer : t ∈ centralizer (L : Set G)
  le_normalizer : T ≤ normalizer (zpowers t : Set G)
  sylow : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
    (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G))

theorem card_le_of_isPGroup {K T X : Subgroup G} (hTK : T ≤ K)
    (hT : ∃ P : Sylow 2 K, (P : Subgroup K) = T.subgroupOf K) (hXK : X ≤ K)
    (hX : IsPGroup 2 X) : Nat.card X ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT
  have hX' : IsPGroup 2 (X.subgroupOf K) := hX.of_equiv (subgroupOfEquivOfLe hXK).symm
  obtain ⟨P', hP'⟩ := hX'.exists_le_sylow
  have h1 : Nat.card (X.subgroupOf K) ≤ Nat.card P' := card_le_of_le hP'
  have h2 : Nat.card P' = Nat.card P := Nat.card_congr (Sylow.equiv P' P).toEquiv
  have h3 : Nat.card (P : Subgroup K) = Nat.card T := by
    rw [hP]
    exact Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv
  have h4 : Nat.card (X.subgroupOf K) = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXK).toEquiv
  rw [← h4, ← h3]
  exact h1.trans h2.le

theorem card_sup_zpowers_le {U : Subgroup G} {t : G} (htt : t * t = 1)
    (htU : zpowers t ≤ normalizer (U : Set G)) : Nat.card (U ⊔ zpowers t : Subgroup G) ≤
      2 * Nat.card U := by
  classical
  let F : (U ⊔ zpowers t : Subgroup G) → Bool × U := fun v =>
    if hv : (v : G) ∈ U then (true, ⟨v, hv⟩) else
      (false, ⟨v * t, by
        obtain ⟨u, hu, h | h⟩ := exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU v.2
        · exact absurd (h ▸ hu) hv
        · rw [← h, mul_assoc, htt, mul_one]
          exact hu⟩)
  have hF : Function.Injective F := by
    intro v v' hvv
    by_cases hv : (v : G) ∈ U <;> by_cases hv' : (v' : G) ∈ U <;>
      simp only [F, hv, hv', dite_true, dite_false, Prod.mk.injEq] at hvv
    · exact Subtype.ext (congrArg (fun z : U => (z : G)) hvv.2)
    · exact absurd hvv.1 (by decide)
    · exact absurd hvv.1 (by decide)
    · exact Subtype.ext (mul_right_cancel (congrArg (fun z : U => (z : G)) hvv.2))
  have h1 := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

theorem two_mul_lt_two_pow {f : ℕ} (hf : 3 ≤ f) : 2 * f < 2 ^ f := by
  induction f, hf using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega

theorem psl2_ending_facts (hGold : Goldschmidt1974) {L : Subgroup G} {f : ℕ} {t : G}
    {T : Subgroup G} (hS : Setting G L f t T) :
    t ∈ T ∧ t * t = 1 ∧ t ∉ T ⊓ L ∧ T ≤ centralizer ({t} : Set G) ∧
    (∀ u ∈ T ⊓ L, u * u = 1) ∧
    T ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G) = T ⊓ L ⊔ zpowers t ∧
    ((T ⊓ L ⊔ zpowers t).subgroupOf T).Normal ∧
    (∀ [((T ⊓ L ⊔ zpowers t).subgroupOf T).Normal],
      IsCyclic (T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T)) ∧
    (∀ p ∈ T, p ∉ T ⊓ L ⊔ zpowers t →
      Nat.card (T ⊓ L ⊓ centralizer ({p} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ f) ∧
    (∀ a ∈ T ⊓ L, ∀ g : G, g⁻¹ * a * g ∈ T ⊓ L ⊔ zpowers t → g⁻¹ * a * g ∈ T ⊓ L) ∧
    (∀ v ∈ T ⊓ L ⊔ zpowers t, v ∉ T ⊓ L → ∃ g : G, g⁻¹ * t * g = v) ∧
    (∀ a ∈ centralizer ({t} : Set G), ∀ b ∈ centralizer ({t} : Set G), a * b = b * a →
      a ^ 4 = 1 → b ^ 4 = 1 → a ^ 2 ≠ 1 → b ^ 2 ≠ 1 → a ^ 2 = b ^ 2) ∧
    (¬ T ≤ T ⊓ L ⊔ zpowers t → 16 ≤ 2 ^ f) ∧
    (∀ X : Subgroup G, X ≤ centralizer ({t} : Set G) → IsPGroup 2 X →
      Nat.card X < (2 ^ f) ^ 2) ∧
    T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∧ Nat.card (T ⊓ L : Subgroup G) = 2 ^ f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hf, hL, hS2, ht, htC, hTN, hT⟩ := hS
  have hdata := gmsNormalRootData_of_psl2_of_card_sylow_eq_two h hf hL hS2 ht htC hTN hT
  have hNC := normalizer_zpowers_eq_centralizer_of_involution ht
  have hTH : T ≤ centralizer ({t} : Set G) := hNC ▸ hTN
  have hT' : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
      (P : Subgroup _) = T.subgroupOf (centralizer ({t} : Set G)) := by
    rw [← hNC]
    exact hT
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨-, -, -, -, ⟨-, -, -, hUcard⟩, -, ⟨-, -, -, hRP, hPNU, hUR, hCPU, -⟩⟩ := id hdata
  have htT : t ∈ T := hRP (mem_zpowers t)
  have htU : t ∉ T ⊓ L := fun h' => ht1 (by
    have : t ∈ T ⊓ L ⊓ zpowers t := mem_inf.mpr ⟨h', mem_zpowers t⟩
    rwa [hUR, mem_bot] at this)
  have hV2 : ∀ v ∈ T ⊓ L ⊔ zpowers t, v * v = 1 := fun v hv => by
    rw [← sq]
    exact SteinbergBV.gms_sq_V hdata v hv
  have hU2 : ∀ u ∈ T ⊓ L, u * u = 1 := fun u hu => hV2 u (mem_sup_left hu)
  obtain ⟨⟨K, _, _, _, hKcard, e, -, -, φ, hequiv, -, hker⟩, hVn, hquot, -⟩ :=
    SteinbergBT.gms_normal_root_singer_action_and_weak_closure hdata
  have hcyc : IsCyclic (T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) := (@hquot hVn).1
  have hdvd : Nat.card (T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) ∣ f := (@hquot hVn).2.1
  have hfix : ∀ p ∈ T, p ∉ T ⊓ L ⊔ zpowers t →
      Nat.card (T ⊓ L ⊓ centralizer ({p} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ f := by
    intro p hp hpV
    have hφp : φ ⟨p, hp⟩ ≠ 1 := fun h1 => hpV (by
      have hmem : (⟨p, hp⟩ : T) ∈ φ.ker := h1
      rw [hker] at hmem
      exact hmem)
    exact SteinbergBT.card_inf_centralizer_sq_le hKcard e φ hequiv hPNU ⟨p, hp⟩ hφp
  obtain ⟨-, -, -, -, -, -, -, hpart, hsc, -⟩ :=
    psl2_stage_zero_full_of_card_sylow_eq_two hGold h hf hL hS2 ht htC hTN hT
  have hconjt : ∀ v ∈ T ⊓ L ⊔ zpowers t, v ∉ T ⊓ L → ∃ g : G, g⁻¹ * t * g = v := by
    intro v hv hvU
    obtain ⟨Q, ⟨⟨k, rfl, -⟩, hvQ⟩, -⟩ := hpart v hv hvU
    obtain ⟨r, hr, hrv⟩ := mem_map.mp hvQ
    rcases eq_one_or_eq_of_mem_zpowers htt hr with rfl | rfl
    · exact absurd (by rw [← hrv, map_one]; exact one_mem _) hvU
    · exact ⟨k, by rw [← hrv]; simp⟩
  have hK2T : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a → a ^ 4 = 1 → b ^ 4 = 1 → a ^ 2 ≠ 1 →
      b ^ 2 ≠ 1 → a ^ 2 = b ^ 2 := fun a ha b hb hab ha4 hb4 ha2 hb2 =>
    @sq_eq_sq_of_isCyclic_quotient G _ _ T (T ⊓ L ⊔ zpowers t) hVn hcyc hV2 a b ha hb hab ha4 hb4
      ha2 hb2
  have hK2 : ∀ a ∈ centralizer ({t} : Set G), ∀ b ∈ centralizer ({t} : Set G), a * b = b * a →
      a ^ 4 = 1 → b ^ 4 = 1 → a ^ 2 ≠ 1 → b ^ 2 ≠ 1 → a ^ 2 = b ^ 2 :=
    fun a ha b hb hab ha4 hb4 ha2 hb2 => sq_eq_sq_of_isSylow hT' hK2T ha hb hab ha4 hb4 ha2 hb2
  have hQp : IsPGroup 2 (T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) :=
    (SteinbergBV.gms_isPGroup_P hdata).to_quotient _
  have h16 : ¬ T ≤ T ⊓ L ⊔ zpowers t → 16 ≤ 2 ^ f := by
    intro hTV
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hTV
      intro τ hτ
      have hsub : Subsingleton (T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
      have h1 : (QuotientGroup.mk ⟨τ, hτ⟩ : T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) = 1 :=
        Subsingleton.elim _ _
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact h1
    have h2f : 2 ∣ f := (hk ▸ dvd_pow_self 2 hk0 : 2 ∣ _).trans hdvd
    have hf4 : 4 ≤ f := by
      obtain ⟨r, rfl⟩ := h2f
      omega
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
  have hsmall : ∀ X : Subgroup G, X ≤ centralizer ({t} : Set G) → IsPGroup 2 X →
      Nat.card X < (2 ^ f) ^ 2 := by
    intro X hXK hX
    have hle := card_le_of_isPGroup hTH hT' hXK hX
    have hVT : T ⊓ L ⊔ zpowers t ≤ T := sup_le inf_le_left (zpowers_le.mpr htT)
    have hTcard : Nat.card T = Nat.card (T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) *
        Nat.card (T ⊓ L ⊔ zpowers t : Subgroup G) := by
      rw [card_eq_card_quotient_mul_card_subgroup ((T ⊓ L ⊔ zpowers t).subgroupOf T)]
      congr 1
      exact Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv
    have htUn : zpowers t ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      zpowers_le.mpr (hPNU htT)
    have hVcard := card_sup_zpowers_le htt htUn
    rw [hUcard] at hVcard
    have hQ := Nat.le_of_dvd (by omega) hdvd
    have h2f := two_mul_lt_two_pow hf
    have hpos : 0 < 2 ^ f := by positivity
    calc Nat.card X ≤ Nat.card T := hle
      _ ≤ f * (2 * 2 ^ f) := by rw [hTcard]; exact Nat.mul_le_mul hQ hVcard
      _ = (2 * f) * 2 ^ f := by ring
      _ < 2 ^ f * 2 ^ f := Nat.mul_lt_mul_of_pos_right h2f hpos
      _ = (2 ^ f) ^ 2 := by ring
  exact ⟨htT, htt, htU, hTH, hU2, hCPU, hVn, fun {_} => hcyc, hfix, hsc.2, hconjt, hK2, h16,
    hsmall, hPNU, hUcard⟩

theorem not_conj_of_homocyclic (hGold : Goldschmidt1974) {L : Subgroup G} {f : ℕ} {t : G}
    {T : Subgroup G} (hS : Setting G L f t T) {W W' : Subgroup G} (hUW : T ⊓ L ≤ W)
    (hTW : T ≤ normalizer (W : Set G)) (hWU : W ≤ centralizer ((T ⊓ L : Subgroup G) : Set G))
    (hW'ab : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a) (hUW' : T ⊓ L ≤ W')
    (hΩ' : ∀ w ∈ W', w * w = 1 → w ∈ T ⊓ L) (h℧' : ∀ u ∈ T ⊓ L, ∃ w ∈ W', w * w = u)
    (hWW' : W ≤ normalizer (W' : Set G)) (hTW' : T ≤ normalizer (W' : Set G)) :
    ∀ y ∈ W ⊔ T, y ∉ W ⊔ zpowers t → y * y = 1 → ∀ g : G, g⁻¹ * t * g ≠ y := by
  obtain ⟨-, -, -, -, hU2, -, -, -, hfix, -, -, hK2, h16, -, hTU, hUcard⟩ :=
    psl2_ending_facts hGold hS
  intro y hy hyV hyy g hg
  obtain ⟨w, hw, τ, hτ, rfl⟩ := exists_mul_eq_of_mem_sup hTW hy
  have hτV : τ ∉ T ⊓ L ⊔ zpowers t := fun h => hyV (mul_mem (mem_sup_left hw)
    ((sup_le (hUW.trans le_sup_left) le_sup_right : T ⊓ L ⊔ zpowers t ≤ W ⊔ zpowers t) h))
  have hq16 := h16 fun h => hτV (h hτ)
  have hτU : ∀ u ∈ T ⊓ L, τ * u * τ⁻¹ ∈ T ⊓ L := fun u hu =>
    (mem_normalizer_iff.mp (hTU hτ) u).mp hu
  have hyu : ∀ u ∈ T ⊓ L, (w * τ) * u * (w * τ)⁻¹ = τ * u * τ⁻¹ := by
    intro u hu
    have hc := mem_centralizer_iff.mp (hWU hw) _ (hτU u hu)
    calc (w * τ) * u * (w * τ)⁻¹ = w * (τ * u * τ⁻¹) * w⁻¹ := by group
      _ = τ * u * τ⁻¹ * w * w⁻¹ := by rw [hc]
      _ = τ * u * τ⁻¹ := by group
  have hCeq : T ⊓ L ⊓ centralizer ({w * τ} : Set G) = T ⊓ L ⊓ centralizer ({τ} : Set G) := by
    ext u
    simp only [mem_inf, mem_centralizer_singleton_iff]
    refine ⟨fun ⟨hu, h⟩ => ⟨hu, ?_⟩, fun ⟨hu, h⟩ => ⟨hu, ?_⟩⟩
    · have h1 : τ * u * τ⁻¹ = u := by
        rw [← hyu u hu, ← h]
        group
      calc u * τ = τ * u * τ⁻¹ * τ := by rw [h1]
        _ = τ * u := by group
    · have h1 : (w * τ) * u * (w * τ)⁻¹ = u := by
        rw [hyu u hu, ← h]
        group
      calc u * (w * τ) = (w * τ) * u * (w * τ)⁻¹ * (w * τ) := by rw [h1]
        _ = (w * τ) * u := by group
  have hyW' : ∀ x ∈ W', (w * τ) * x * (w * τ)⁻¹ ∈ W' := fun x hx =>
    (mem_normalizer_iff.mp (mul_mem (hWW' hw) (hTW' hτ)) x).mp hx
  have hyU : ∀ u ∈ T ⊓ L, (w * τ) * u * (w * τ)⁻¹ ∈ T ⊓ L := fun u hu => by
    rw [hyu u hu]
    exact hτU u hu
  have hcard : Nat.card (T ⊓ L ⊓ centralizer ({w * τ} : Set G) : Subgroup G) ^ 2 ≤
      Nat.card (T ⊓ L : Subgroup G) := by
    rw [hCeq, hUcard]
    exact hfix τ hτ hτV
  obtain ⟨a, -, b, -, hay, hby, hab, ha1, hb1, hab2, ha4, hb4⟩ :=
    exists_sq_ne_of_involution hW'ab hUW' hU2 hΩ' h℧' hyW' hyU hyy hcard (hUcard ▸ hq16)
  have hgt : g * (w * τ) * g⁻¹ = t := by rw [← hg]; group
  have hcomm : ∀ x : G, (w * τ) * x = x * (w * τ) →
      g * x * g⁻¹ ∈ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff, ← hgt]
    calc g * x * g⁻¹ * (g * (w * τ) * g⁻¹) = g * (x * (w * τ)) * g⁻¹ := by group
      _ = g * ((w * τ) * x) * g⁻¹ := by rw [hx]
      _ = g * (w * τ) * g⁻¹ * (g * x * g⁻¹) := by group
  have hconj4 : ∀ x : G, x ^ 4 = 1 → (g * x * g⁻¹) ^ 4 = 1 := fun x hx => by
    rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hconj2 : ∀ x : G, x * x ≠ 1 → (g * x * g⁻¹) ^ 2 ≠ 1 := fun x hx h => by
    rw [conj_pow] at h
    have h' : g * x ^ 2 = g * 1 := by
      rw [mul_one]
      exact mul_inv_eq_one.mp h
    exact hx (by rw [← sq]; exact mul_left_cancel h')
  have hcab : (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
    calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hab]
      _ = _ := by group
  have := hK2 _ (hcomm a hay) _ (hcomm b hby) hcab (hconj4 a ha4) (hconj4 b hb4) (hconj2 a ha1)
    (hconj2 b hb1)
  rw [conj_pow, conj_pow] at this
  exact hab2 (by rw [← sq, ← sq]; exact mul_left_cancel (mul_right_cancel this))

theorem not_conj_mem_of_card (hGold : Goldschmidt1974) {L : Subgroup G} {f : ℕ} {t : G}
    {T : Subgroup G} (hS : Setting G L f t T) {W : Subgroup G} (hWp : IsPGroup 2 W)
    (hcent : ∀ w ∈ W, w * w = 1 →
      (2 ^ f) ^ 2 ≤ Nat.card (W ⊓ centralizer ({w} : Set G) : Subgroup G)) :
    ∀ g : G, g⁻¹ * t * g ∉ W := by
  obtain ⟨-, htt, -, -, -, -, -, -, -, -, -, -, -, hsmall, -, -⟩ := psl2_ending_facts hGold hS
  intro g hg
  have hww : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  have h1 := hcent _ hg hww
  set X := (W ⊓ centralizer ({g⁻¹ * t * g} : Set G)).map (MulAut.conj g).toMonoidHom with hX
  have hXC : X ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxc := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hxc]
      _ = t * (g * x * g⁻¹) := by group
  have hXp : IsPGroup 2 X := ((hWp.to_le inf_le_left).map _)
  have hXcard : Nat.card X = Nat.card (W ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G) :=
    card_map_of_injective (MulAut.conj g).injective
  have := hsmall X hXC hXp
  omega

theorem false_of_ending (hGold : Goldschmidt1974) {L : Subgroup G} {f : ℕ} {t : G}
    {T : Subgroup G} (hS : Setting G L f t T) {W : Subgroup G}
    (hSyl : ∃ S : Sylow 2 G, (S : Subgroup G) = W ⊔ T) (hTW : T ≤ normalizer (W : Set G))
    (hUW : T ⊓ L ≤ W) (hWU : W ≤ centralizer ((T ⊓ L : Subgroup G) : Set G)) (htW : t ∉ W)
    (h1 : ∀ g : G, g⁻¹ * t * g ∉ W)
    (h3 : ∀ y ∈ W ⊔ T, y ∉ W ⊔ zpowers t → y * y = 1 → ∀ g : G, g⁻¹ * t * g ≠ y) : False := by
  obtain ⟨htT, htt, htU, hTH, hU2, hCTU, hVn, hcyc, -, -, hconjt, -, -, -, hTU, -⟩ :=
    psl2_ending_facts hGold hS
  have hst := hS.seitz.standardSetting
  have := hst.simple
  have htUn : zpowers t ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := zpowers_le.mpr (hTU htT)
  have hWT : W ⊓ T = T ⊓ L := by
    refine le_antisymm (fun τ hτ => ?_) (le_inf hUW inf_le_left)
    obtain ⟨hτW, hτT⟩ := mem_inf.mp hτ
    have hτV : τ ∈ T ⊓ L ⊔ zpowers t := by
      rw [← hCTU]
      exact mem_inf.mpr ⟨hτT, hWU hτW⟩
    obtain ⟨u, hu, rfl | rfl⟩ := exists_eq_or_eq_mul_of_mem_sup_zpowers htt htUn hτV
    · exact hu
    · exact absurd (by simpa using mul_mem (inv_mem (hUW hu)) hτW) htW
  have h2 : ∀ u ∈ T ⊓ L, ∃ g : G, g⁻¹ * t * g = u * t := fun u hu =>
    hconjt _ (mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))) fun h =>
      htU (by simpa using mul_mem (inv_mem hu) h)
  obtain ⟨S, hSc⟩ := hSyl
  have hSp : IsPGroup 2 (W ⊔ T : Subgroup G) := hSc ▸ S.isPGroup'
  have hSidx : ¬ 2 ∣ (W ⊔ T).index := hSc ▸ S.not_dvd_index
  have := hVn
  exact not_exists_normal_index_two hst.nonab
    (exists_normal_index_two_of_ending hSp hSidx hTW hWT hU2 htT htW htt hTH hcyc h1 h2 h3)

theorem false_of_gms41 (hGold : Goldschmidt1974) {L : Subgroup G} {f : ℕ} {t : G}
    {T : Subgroup G} (hS : Setting G L f t T) {W W' : Subgroup G}
    (hW'ab : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a) (hUW' : T ⊓ L ≤ W') (hW'W : W' ≤ W)
    (hΩ' : ∀ w ∈ W', w * w = 1 → w ∈ T ⊓ L) (h℧' : ∀ u ∈ T ⊓ L, ∃ w ∈ W', w * w = u)
    (hWW' : W ≤ normalizer (W' : Set G)) (hTW' : T ≤ normalizer (W' : Set G))
    (hWU : W ≤ centralizer ((T ⊓ L : Subgroup G) : Set G))
    (hTW : T ≤ normalizer (W : Set G)) (htW : t ∉ W)
    (hcent : ∀ w ∈ W, w * w = 1 →
      (2 ^ f) ^ 2 ≤ Nat.card (W ⊓ centralizer ({w} : Set G) : Subgroup G))
    (hSyl : ∃ S : Sylow 2 G, (S : Subgroup G) = W ⊔ T) : False := by
  have hWp : IsPGroup 2 W := by
    obtain ⟨S, hSc⟩ := hSyl
    exact (hSc ▸ S.isPGroup' : IsPGroup 2 (W ⊔ T : Subgroup G)).to_le le_sup_left
  have hUW := hUW'.trans hW'W
  exact false_of_ending hGold hS hSyl hTW hUW hWU htW (not_conj_mem_of_card hGold hS hWp hcent)
    (not_conj_of_homocyclic hGold hS hUW hTW hWU hW'ab hUW' hΩ' h℧' hWW' hTW')

theorem false_of_gms43_of_no_involution (hGold : Goldschmidt1974) {L : Subgroup G} {f : ℕ}
    {t : G} {T : Subgroup G} (hS : Setting G L f t T) {W : Subgroup G}
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWcard : (2 ^ f) ^ 2 ≤ Nat.card W) (hUW : T ⊓ L ≤ W) (hTW : T ≤ normalizer (W : Set G))
    (htW : t ∉ W) (hSyl : ∃ S : Sylow 2 G, (S : Subgroup G) = W ⊔ T)
    (hinv : ∀ y ∈ W ⊔ T, y * y = 1 → y ∈ W ⊔ zpowers t) : False := by
  have hWp : IsPGroup 2 W := by
    obtain ⟨S, hSc⟩ := hSyl
    exact (hSc ▸ S.isPGroup' : IsPGroup 2 (W ⊔ T : Subgroup G)).to_le le_sup_left
  have hWU : W ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) := fun w hw =>
    mem_centralizer_iff.mpr fun u hu => hWab u (hUW hu) w hw
  have hcent : ∀ w ∈ W, w * w = 1 →
      (2 ^ f) ^ 2 ≤ Nat.card (W ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    intro w hw _
    have heq : W ⊓ centralizer ({w} : Set G) = W :=
      inf_eq_left.mpr fun x hx => mem_centralizer_singleton_iff.mpr (hWab x hx w hw)
    rw [heq]
    exact hWcard
  exact false_of_ending hGold hS hSyl hTW hUW hWU htW (not_conj_mem_of_card hGold hS hWp hcent)
    fun y hy hyV hyy _ _ => hyV (hinv y hy hyy)

theorem exists_sylow_of_no_involution (hGold : Goldschmidt1974) {L : Subgroup G} {f : ℕ}
    {t : G} {T : Subgroup G} (hS : Setting G L f t T) {W : Subgroup G}
    (hWel : ∀ w ∈ W, w * w = 1) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWcard : (2 ^ f) ^ 2 ≤ Nat.card W) (hUW : T ⊓ L ≤ W) (hTW : T ≤ normalizer (W : Set G))
    (hCt : W ⊓ centralizer ({t} : Set G) ≤ T ⊓ L)
    (hsyl : IsSylowOf 2 (W ⊔ T) (normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G)))
    (hinv : ∀ y ∈ W ⊔ T, y * y = 1 → y ∈ W ⊔ zpowers t) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = W ⊔ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, htt, htU, -, -, -, -, -, -, -, hconjt, -, -, -, -, -⟩ := psl2_ending_facts hGold hS
  have hWp : IsPGroup 2 W := hsyl.isPGroup.to_le le_sup_left
  have hcent : ∀ w ∈ W, w * w = 1 →
      (2 ^ f) ^ 2 ≤ Nat.card (W ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    intro w hw _
    have heq : W ⊓ centralizer ({w} : Set G) = W :=
      inf_eq_left.mpr fun x hx => mem_centralizer_singleton_iff.mpr (hWab x hx w hw)
    rw [heq]
    exact hWcard
  have h1 := not_conj_mem_of_card hGold hS hWp hcent
  have htN : zpowers t ≤ normalizer (W : Set G) := zpowers_le.mpr (hTW htT)
  have hstep1 : ∀ n ∈ normalizer ((W ⊔ T : Subgroup G) : Set G), ∀ r ∈ W ⊔ zpowers t,
      n * r * n⁻¹ ∈ W ⊔ zpowers t := by
    intro n hn r hr
    have hinvol : ∀ x ∈ W ⊔ T, x * x = 1 → n * x * n⁻¹ ∈ W ⊔ zpowers t := fun x hx hxx =>
      hinv _ ((mem_normalizer_iff.mp hn x).mp hx) (by
        calc n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
          _ = 1 := by rw [hxx]; group)
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup htN hr
    rw [show n * (w * z) * n⁻¹ = (n * w * n⁻¹) * (n * z * n⁻¹) by group]
    refine mul_mem (hinvol w (mem_sup_left hw) (hWel w hw)) ?_
    rcases eq_one_or_eq_of_mem_zpowers htt hz with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · exact hinvol _ (mem_sup_right htT) htt
  have hRt : ∀ g : G, g⁻¹ * t * g ∈ W ⊔ zpowers t → g⁻¹ * t * g ∈ T ⊓ L ⊔ zpowers t := by
    intro g hg
    obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_eq_of_mem_sup htN hg
    rcases eq_one_or_eq_of_mem_zpowers htt hz with rfl | rfl
    · exact absurd (by rw [← hwz, mul_one]; exact hw) (h1 g)
    · have hinv2 : w * t * (w * t) = 1 := by
        rw [hwz]
        calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [htt]; group
      have hw1 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hWel w hw)
      have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      have hwt : w * t = t * w := by
        have h' : t * w * t = w := by
          have : w * (t * w * t) = 1 := by rw [← hinv2]; group
          rw [eq_inv_of_mul_eq_one_right this, hw1]
        calc w * t = t * w * t * t := by rw [h']
          _ = t * w * (t * t) := by group
          _ = t * w := by rw [htt, mul_one]
      have hwU : w ∈ T ⊓ L := hCt (mem_inf.mpr ⟨hw, mem_centralizer_singleton_iff.mpr hwt⟩)
      rw [← hwz]
      exact mul_mem (mem_sup_left hwU) (mem_sup_right (mem_zpowers t))
  have hVR : T ⊓ L ⊔ zpowers t ≤ W ⊔ zpowers t := sup_le (hUW.trans le_sup_left) le_sup_right
  have hstep2 : ∀ n : G, (∀ r ∈ W ⊔ zpowers t, n * r * n⁻¹ ∈ W ⊔ zpowers t) →
      n ∈ normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) := by
    intro n hn
    have hconjR : ∀ v ∈ T ⊓ L ⊔ zpowers t, v ∉ T ⊓ L → n * v * n⁻¹ ∈ T ⊓ L ⊔ zpowers t := by
      intro v hv hvU
      obtain ⟨g, hg⟩ := hconjt v hv hvU
      have e : (g * n⁻¹)⁻¹ * t * (g * n⁻¹) = n * (g⁻¹ * t * g) * n⁻¹ := by group
      have := hRt (g * n⁻¹) (by rw [e, hg]; exact hn v (hVR hv))
      rwa [e, hg] at this
    refine GMS28.mem_normalizer_of_conj_mem_of_finite fun v hv => ?_
    by_cases hvU : v ∈ T ⊓ L
    · have hvt : v * t ∉ T ⊓ L := fun h => htU (by simpa using mul_mem (inv_mem hvU) h)
      have h1' := hconjR (v * t) (mul_mem (mem_sup_left hvU) (mem_sup_right (mem_zpowers t))) hvt
      have h2' := hconjR t (mem_sup_right (mem_zpowers t)) htU
      have e : n * v * n⁻¹ = (n * (v * t) * n⁻¹) * (n * t * n⁻¹) := by
        rw [show (n * (v * t) * n⁻¹) * (n * t * n⁻¹) = n * v * (t * t) * n⁻¹ by group, htt,
          mul_one]
      rw [e]
      exact mul_mem h1' h2'
    · exact hconjR v hv hvU
  have hP : IsPGroup 2 (W ⊔ T : Subgroup G) := hsyl.isPGroup
  by_cases htop : IsSylowOf 2 (W ⊔ T) ⊤
  · obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp htop
    rw [relIndex_top_right] at hidx
    exact ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx⟩
  · exfalso
    obtain ⟨S, hPS, z, hzS, hzN, hzP⟩ := GMS28.exists_mem_normalizer_of_not_isSylowOf hP htop
    have hzV := hstep2 z (hstep1 z hzN)
    have hle : W ⊔ T ⊔ zpowers z ≤ normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) :=
      sup_le hsyl.le (zpowers_le.mpr hzV)
    have hp' : IsPGroup 2 (W ⊔ T ⊔ zpowers z : Subgroup G) :=
      S.isPGroup'.to_le (sup_le hPS (zpowers_le.mpr hzS))
    have heq := hsyl.eq_of_le le_sup_left hle hp'
    exact hzP (heq ▸ mem_sup_right (mem_zpowers z))

@[expose] def GMS43InvolutionCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T V₁ U₁ : Subgroup G)
    (y d : G), Goldschmidt1974 → Setting G L f t T →
    GMS28.Result (zpowers t) L (T ⊓ L) T f t V₁ U₁ y d → (∀ u ∈ U₁, u * u = 1) →
    (∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t) → False

theorem false_of_gms43 (hGold : Goldschmidt1974) (hcase : GMS43InvolutionCase) {L : Subgroup G}
    {f : ℕ} {t : G} {T : Subgroup G} (hS : Setting G L f t T) {V₁ U₁ : Subgroup G} {y d : G}
    (hR : GMS28.Result (zpowers t) L (T ⊓ L) T f t V₁ U₁ y d) (hel : ∀ u ∈ U₁, u * u = 1) :
    False := by
  by_cases hx : ∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t
  · exact hcase G L f t T V₁ U₁ y d hGold hS hR hel hx
  push Not at hx
  obtain ⟨htT, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := psl2_ending_facts hGold hS
  have hab : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := by
    intro a ha b hb
    have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hel a ha)
    have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hel b hb)
    have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hel _ (mul_mem ha hb))
    rw [mul_inv_rev, h1, h2] at h3
    exact h3.symm
  have ht1 : t ≠ 1 := by
    rintro rfl
    have h2 := hS.orderOf_t
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have htU₁ : t ∉ U₁ := fun h => ht1 (by
    have : t ∈ U₁ ⊓ zpowers t := mem_inf.mpr ⟨h, mem_zpowers t⟩
    rwa [hR.inf_eq_bot, mem_bot] at this)
  have hsyl : IsSylowOf 2 (U₁ ⊔ T)
      (normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G)) := by
    have h1 := hR.sylow_sup
    rwa [← hR.sup_eq, sup_assoc, sup_eq_right.mpr (zpowers_le.mpr htT)] at h1
  have hcard : (2 ^ f) ^ 2 ≤ Nat.card U₁ := hR.card.ge
  obtain ⟨S, hSc⟩ := exists_sylow_of_no_involution hGold hS hel hab hcard hR.U_le
    hR.le_normalizer_P hR.centralizer_eq.le hsyl hx
  exact false_of_gms43_of_no_involution hGold hS hab hcard hR.U_le hR.le_normalizer_P htU₁
    ⟨S, hSc⟩ hx

end Endings

end CFSG.SeitzReduction.RankOne
