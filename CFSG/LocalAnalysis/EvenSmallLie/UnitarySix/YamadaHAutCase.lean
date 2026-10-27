module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutType
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutL1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5HAutTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQFSetting
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQSetting

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3
open CFSG.EvenSmallLie.UnitarySix.YamadaD


variable {G : Type} [Group G] {L : Subgroup G} {t : G} {e : L ≃* T46}
  {Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693)}

theorem card_le_of_perm
    (hcard : ∀ P : Subgroup G, P ≤ L ⊓ centralizer ({(sec3DData e t).e} : Set G) ⊓
      normalizer ((sec3DData e t).A₃ : Set G) → IsPGroup 2 P → Nat.card P ≤ 2 ^ 6)
    {Q : Subgroup (Equiv.Perm (Fin 693))} (hQT : Q ≤ T46)
    (hQe : ∀ y ∈ Q, y * wP [4, 17] = wP [4, 17] * y)
    (hQn : Q ≤ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693)))) (h2 : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 ^ 6 := by
  set Q' : Subgroup G := (Q.subgroupOf T46).map (iotaG e) with hQ'
  have hcQ : Nat.card Q' = Nat.card Q := by
    rw [hQ', card_map_of_injective iotaG_injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv
  have h2' : IsPGroup 2 Q' := (h2.of_equiv (subgroupOfEquivOfLe hQT).symm).map _
  rw [← hcQ]
  refine hcard Q' ?_ h2'
  rintro _ ⟨y, hy, rfl⟩
  have hyQ : (y : Equiv.Perm (Fin 693)) ∈ Q := mem_subgroupOf.1 hy
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨iotaG_mem y, ?_⟩, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    rw [show (sec3DData e t).e = gw e [4, 17] from rfl, gw_eq [4, 17] (by decide), ← map_mul,
      ← map_mul]
    exact congrArg (iotaG e) (Subtype.ext (hQe y hyQ))
  · have h1 : (y : Equiv.Perm (Fin 693)) ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) ⊓
        T46 := ⟨normalizer_chA4_le_normalizer_A3 y.2 (hQn hyQ), y.2⟩
    have h3 : iotaG e y ∈ normalizer (toG e chA3.grp : Set G) ⊓ L := by
      rw [normalizer_toG (grp_le_T46 gensOK_chA3)]
      exact iotaG_mem_toG.2 h1
    exact h3.1

theorem field_comm_wP (a : ℕ) {w : List ℕ} (hd : ∀ k ∈ w, k ∈ dLetters)
    (hs : ∀ k ∈ w, k ∈ sLetters) : dP ^ a * sP * wP w = wP w * (dP ^ a * sP) := by
  have h1 : Commute (dP ^ a) (wP w) := (Commute.pow_left (dP_comm_wP w hd) a)
  have h2 : Commute sP (wP w) := sP_comm_wP w hs
  exact (h1.mul_left h2).eq

theorem field_conj_u₂ (a : ℕ) : dP ^ a * sP * gP 1 * (dP ^ a * sP)⁻¹ = gP 0 * gP 1 := by
  have h1 : sP * gP (0 + 1) * sP⁻¹ = gP 0 * gP (0 + 1) := letter_spec.2.2 0 (by decide)
  have h2 : Commute (dP ^ a) (gP 0 * gP 1) := by
    refine Commute.pow_left ?_ a
    have e0 := letter_spec.1 0 (by decide)
    have e1 := letter_spec.1 1 (by decide)
    exact (Commute.mul_right e0 e1)
  calc dP ^ a * sP * gP 1 * (dP ^ a * sP)⁻¹ = dP ^ a * (sP * gP 1 * sP⁻¹) * (dP ^ a)⁻¹ := by
        group
    _ = dP ^ a * (gP 0 * gP 1) * (dP ^ a)⁻¹ := by rw [h1]
    _ = gP 0 * gP 1 := by rw [h2.eq]; group

theorem card_inf_le (hΘ : ThetaSpec t e Θ)
    (hcard : ∀ P : Subgroup G, P ≤ L ⊓ centralizer ({(sec3DData e t).e} : Set G) ⊓
      normalizer ((sec3DData e t).A₃ : Set G) → IsPGroup 2 P → Nat.card P ≤ 2 ^ 6)
    {P : Subgroup G} (hP : P ≤ (sec3DData e t).H ⊓ centralizer ({(sec3DData e t).e} : Set G) ⊓
      normalizer ((sec3DData e t).A₄ : Set G)) (h2 : IsPGroup 2 P) :
    P ≤ centralizer ({t} : Set G) ∧
      Nat.card ((P.subgroupOf (centralizer ({t} : Set G))).map Θ ⊓ T46 :
        Subgroup (Equiv.Perm (Fin 693))) ≤ 2 ^ 6 := by
  have hPC : P ≤ centralizer ({t} : Set G) := fun x hx => (hP hx).1.1
  refine ⟨hPC, card_le_of_perm hcard inf_le_right ?_ ?_
    ((ThetaSpec.isPGroup_map h2).to_le inf_le_left)⟩
  · rintro y ⟨⟨x, hx, rfl⟩, -⟩
    have hxP : (x : G) ∈ P := mem_subgroupOf.1 hx
    have hc : (x : G) * (sec3DData e t).e = (sec3DData e t).e * x :=
      mem_centralizer_singleton_iff.1 (hP hxP).1.2
    rw [show (sec3DData e t).e = gw e [4, 17] from rfl, gw_eq [4, 17] (by decide)] at hc
    exact (hΘ.comm_iotaG_iff x _).1 hc
  · rintro y ⟨⟨x, hx, rfl⟩, -⟩
    have hxP : (x : G) ∈ P := mem_subgroupOf.1 hx
    exact (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA4) x).1 (hP hxP).2

theorem hypNF_or_hypF [Finite G] (hΘ : ThetaSpec t e Θ) (ht : orderOf t = 2)
    (hcard : ∀ P : Subgroup G, P ≤ L ⊓ centralizer ({(sec3DData e t).e} : Set G) ⊓
      normalizer ((sec3DData e t).A₃ : Set G) → IsPGroup 2 P → Nat.card P ≤ 2 ^ 6) :
    HypNF (sec3DData e t) ∨ ∃ φ, HypF (sec3DData e t) φ := by
  by_cases hfield : ∃ x : centralizer ({t} : Set G), ∃ l ∈ T46, ∃ a < 3, Θ x = l * dP ^ a * sP
  · obtain ⟨x₀, l, hl, a, ha, hx₀⟩ := hfield
    set m : centralizer ({t} : Set G) :=
      ⟨iotaG e (⟨l, hl⟩ : T46)⁻¹, hΘ.L_le_centralizer (iotaG_mem _)⟩ with hm
    have hΘm : Θ m = l⁻¹ := by
      rw [hm, hΘ.apply_iotaG]
      rfl
    set φC := m * x₀ with hφC
    have hΘφ : Θ φC = dP ^ a * sP := by
      rw [hφC, map_mul, hΘm, hx₀]
      group
    right
    refine ⟨(φC : G), ?_⟩
    have hconj : ∀ (w w' : List ℕ) (hw : ∀ k ∈ w, k < 18) (hw' : ∀ k ∈ w', k < 18),
        dP ^ a * sP * wP w * (dP ^ a * sP)⁻¹ = wP w' →
        (φC : G) * gw e w * (φC : G)⁻¹ = gw e w' := by
      intro w w' hw hw' h
      rw [gw_eq w hw, gw_eq w' hw', hΘ.conj_iotaG_eq_iff, hΘφ]
      exact h
    have hfix : ∀ w : List ℕ, (∀ k ∈ w, k ∈ dLetters) → (∀ k ∈ w, k ∈ sLetters) →
        dP ^ a * sP * wP w * (dP ^ a * sP)⁻¹ = wP w := by
      intro w hd hs
      rw [field_comm_wP a hd hs]
      group
    exact {
      φ_comm_t := mem_centralizer_singleton_iff.1 φC.2
      φ_comm_e := by
        have h := hconj [4, 17] [4, 17] (by decide) (by decide) (hfix _ (by decide) (by decide))
        rw [show (sec3DData e t).e = gw e [4, 17] from rfl]
        calc (φC : G) * gw e [4, 17] = (φC : G) * gw e [4, 17] * (φC : G)⁻¹ * φC := by group
          _ = gw e [4, 17] * φC := by rw [h]
      φ_norm_A₄ := by
        refine (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA4) φC).2 ?_
        rw [hΘφ]
        exact mul_mem (pow_mem norm_chA4.1 a) norm_chA4.2
      φ_u₁ := hconj [0] [0] (by decide) (by decide) (hfix _ (by decide) (by decide))
      φ_u₂ := by
        have h := hconj [1] [0, 1] (by decide) (by decide) (by
          rw [wP_single, field_conj_u₂ a]
          simp [wP])
        rw [show (sec3DData e t).u₂ = gw e [1] from rfl, show (sec3DData e t).u₁ = gw e [0] from rfl,
          h, ← gw_append]
        rfl
      φ_a₀ := hconj [11] [11] (by decide) (by decide) (hfix _ (by decide) (by decide))
      φ_sq := by
        have h1 : Θ (φC * φC) = 1 := by rw [map_mul, hΘφ, dP_pow_mul_sP_sq]
        have h2 := (hΘ.eq_one_iff (φC * φC)).1 h1
        have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
        rcases Yamada.eq_one_or_eq_of_mem_zpowers ht2 h2 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr h3
      φ_not_mem := fun h => by
        have h1 := (hΘ.mem_L_sup_iff φC).1 h
        rw [hΘφ] at h1
        exact dP_pow_mul_sP_not_mem ha h1
      card_le := fun P hP h2 => by
        obtain ⟨hPC, hb⟩ := card_inf_le hΘ hcard hP h2
        have h1 := hΘ.card_le_two_mul ht hPC
        have h3 := card_le_two_mul_inf (X := (P.subgroupOf (centralizer ({t} : Set G))).map Θ)
          (by rintro _ ⟨x, -, rfl⟩; exact hΘ.mem_autT x) (ThetaSpec.isPGroup_map h2)
        calc Nat.card P ≤ 2 * (2 * 2 ^ 6) := by omega
          _ = 2 ^ 8 := by norm_num }
  · left
    refine ⟨fun P hP h2 => ?_⟩
    obtain ⟨hPC, hb⟩ := card_inf_le hΘ hcard hP h2
    have hle : (P.subgroupOf (centralizer ({t} : Set G))).map Θ ≤ T46 := by
      rintro y ⟨x, hx, rfl⟩
      by_contra hyT
      obtain ⟨k, hk⟩ := (ThetaSpec.isPGroup_map (Θ := Θ) h2) ⟨Θ x, x, hx, rfl⟩
      have hk' : (Θ x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨l, hl, a, ha, h⟩ := field_of_pow_two_pow (hΘ.mem_autT x) hk' hyT
      exact hfield ⟨x, l, hl, a, ha, h⟩
    rw [inf_eq_left.2 hle] at hb
    have h1 := hΘ.card_le_two_mul ht hPC
    calc Nat.card P ≤ 2 * 2 ^ 6 := by omega
      _ = 2 ^ 7 := by norm_num

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
