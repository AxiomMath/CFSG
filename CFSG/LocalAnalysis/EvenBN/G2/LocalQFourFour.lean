module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyOne
public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

theorem mem_normalizer_centralizer_of_mem_normalizer {G : Type*} [Group G] {N : Subgroup G}
    {x : G} (hx : x ∈ normalizer (N : Set G)) :
    x ∈ normalizer (centralizer (N : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hy z hz
    have hz' : x⁻¹ * z * x ∈ N := by
      have := (mem_normalizer_iff.1 (inv_mem hx) z).1 hz
      rwa [inv_inv] at this
    have e := hy _ hz'
    calc z * (x * y * x⁻¹) = x * ((x⁻¹ * z * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * z * x)) * x⁻¹ := by rw [e]
      _ = x * y * x⁻¹ * z := by group
  · intro hy z hz
    have e := hy _ ((mem_normalizer_iff.1 hx z).1 hz)
    calc z * y = x⁻¹ * ((x * z * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * (x * z * x⁻¹)) * x := by rw [e]
      _ = y * z := by group

theorem le_centralizer_of_inf_centralizer_le {G : Type*} [Group G] [Finite G]
    {A N J : Subgroup G} (hAN : A ≤ normalizer (N : Set G))
    (hJA : J ≤ normalizer (A : Set G)) (hJN : J ≤ centralizer (N : Set G))
    (hsolv : Group.IsSolvable A) (hcop : (Nat.card J).Coprime (Nat.card A))
    (hfix : A ⊓ centralizer (J : Set G) ≤ N) (hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) :
    A ≤ centralizer (N : Set G) := by
  intro a ha
  have hAC : A ≤ normalizer ((A ⊓ centralizer (N : Set G) : Subgroup G) : Set G) := fun x hx =>
    Common.mem_normalizer_inf (le_normalizer hx)
      (mem_normalizer_centralizer_of_mem_normalizer (hAN hx))
  have hJC : J ≤ normalizer ((A ⊓ centralizer (N : Set G) : Subgroup G) : Set G) := fun j hj =>
    Common.mem_normalizer_inf (hJA hj) (mem_normalizer_centralizer_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ (hJN hj)))
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime inf_le_left hAC
    hJA hJC hsolv hcop ha fun j hj => by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hJA hj) a).1 ha),
        mem_centralizer_iff.2 fun z hz => ?_⟩
      have hz' : a * z * a⁻¹ ∈ N := (mem_normalizer_iff.1 (hAN ha) z).1 hz
      have e1 : z * j = j * z := mem_centralizer_iff.1 (hJN hj) z hz
      have e1' : z * j⁻¹ = j⁻¹ * z := by
        calc z * j⁻¹ = j⁻¹ * (j * z) * j⁻¹ := by group
          _ = j⁻¹ * (z * j) * j⁻¹ := by rw [e1]
          _ = j⁻¹ * z := by group
      have e2 : (a * z * a⁻¹) * j = j * (a * z * a⁻¹) := mem_centralizer_iff.1 (hJN hj) _ hz'
      calc z * (a⁻¹ * (j * a * j⁻¹)) = a⁻¹ * (j * (a * z * a⁻¹)) * a * j⁻¹ := by
            rw [← e2]; group
        _ = a⁻¹ * j * a * (z * j⁻¹) := by group
        _ = a⁻¹ * j * a * (j⁻¹ * z) := by rw [e1']
        _ = a⁻¹ * (j * a * j⁻¹) * z := by group
  exact mul_mem (mem_centralizer_iff.2 fun z hz => hNab z hz c (hfix hc)) (Subgroup.mem_inf.1 hn).2

namespace Model


variable (K : Type) [Field K] [CharP K 2]

theorem Y_le_SbY : Y K ≤ SbY K := by
  rintro _ ⟨E, F, rfl⟩
  exact ⟨0, E, F, rfl⟩

theorem M_inf_SbY : M K ⊓ SbY K = Y K := by
  refine le_antisymm ?_
    (le_inf ((Y_le_W (K := K)).trans ((W_le_F (K := K)).trans (F_le_M (K := K)))) (Y_le_SbY K))
  rintro _ ⟨⟨A, C, D, E, F, rfl⟩, ⟨b, e, f, h⟩⟩
  obtain ⟨hA, -, hC, hD, -, -⟩ := g2N_injective h
  rw [hA, hC, hD]
  exact ⟨E, F, rfl⟩

theorem W_inf_SbY : W K ⊓ SbY K = Y K := by
  refine le_antisymm ?_ (le_inf (Y_le_W (K := K)) (Y_le_SbY K))
  rintro _ ⟨⟨D, E, F, rfl⟩, ⟨b, e, f, h⟩⟩
  obtain ⟨-, -, -, hD, -, -⟩ := g2N_injective h
  rw [hD]
  exact ⟨E, F, rfl⟩

theorem X_inf_SbY : X K ⊓ SbY K = Y K := by
  refine le_antisymm ?_ (le_inf (Y_le_X (K := K)) (Y_le_SbY K))
  rintro _ ⟨⟨C, E, F, rfl⟩, ⟨b, e, f, h⟩⟩
  obtain ⟨-, -, hC, -, -, -⟩ := g2N_injective h
  rw [hC]
  exact ⟨E, F, rfl⟩

end Model

namespace G2Data

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (d : G2Data L K)

theorem M_inf_centralizer_J₁_four (hK4 : Nat.card K = 4) :
    d.M ⊓ centralizer (d.J₁ : Set G) = d.Y := by
  calc d.M ⊓ centralizer (d.J₁ : Set G) = d.M ⊓ (d.S ⊓ centralizer (d.J₁ : Set G)) := by
        rw [← inf_assoc, inf_eq_left.2 d.inclusions.2.2.2.2.2.2.2.2.1]
    _ = d.Y := by
        rw [d.S_inf_centralizer_J₁_four hK4, G2Data.M, G2Data.sbY, ← d.image_inf,
          Model.M_inf_SbY]
        rfl

theorem W_inf_centralizer_J₁_four (hK4 : Nat.card K = 4) :
    d.W ⊓ centralizer (d.J₁ : Set G) = d.Y := by
  have hWS : d.W ≤ d.S := d.inclusions.2.2.2.2.1.trans
    (d.inclusions.2.2.2.2.2.1.trans d.inclusions.2.2.2.2.2.2.2.1)
  calc d.W ⊓ centralizer (d.J₁ : Set G) = d.W ⊓ (d.S ⊓ centralizer (d.J₁ : Set G)) := by
        rw [← inf_assoc, inf_eq_left.2 hWS]
    _ = d.Y := by
        rw [d.S_inf_centralizer_J₁_four hK4, G2Data.W, G2Data.sbY, ← d.image_inf,
          Model.W_inf_SbY]
        rfl

theorem X_inf_centralizer_J₁_four (hK4 : Nat.card K = 4) :
    d.X ⊓ centralizer (d.J₁ : Set G) = d.Y := by
  have hXS : d.X ≤ d.S := d.inclusions.2.2.2.1.trans
    (d.inclusions.2.2.2.2.2.1.trans d.inclusions.2.2.2.2.2.2.2.1)
  calc d.X ⊓ centralizer (d.J₁ : Set G) = d.X ⊓ (d.S ⊓ centralizer (d.J₁ : Set G)) := by
        rw [← inf_assoc, inf_eq_left.2 hXS]
    _ = d.Y := by
        rw [d.S_inf_centralizer_J₁_four hK4, G2Data.X, G2Data.sbY, ← d.image_inf,
          Model.X_inf_SbY]
        rfl

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFourJ₁

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaY₂_le_centralizer_J₁_four (h : Setup G L f t) (d : G2Data L K)
    (hD : h.DoublingFacts d) (hK4 : Nat.card K = 4) :
    yamadaY₂ d t ≤ centralizer (d.J₁ : Set G) := by
  refine sup_le hD.le_centralizer_J₁ ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_centralizer_iff]
  intro j hj
  have hj' : j ∈ d.J₁.map (MulAut.conj d.wb).toMonoidHom := by
    rw [(d.Ji_conj_G).1, ← (d.yamada_3_9_4_four_G hK4).2.1]
    exact hj
  obtain ⟨j', hj'', rfl⟩ := hj'
  have e : j' * u = u * j' := mem_centralizer_iff.1 (hD.le_centralizer_J₁ hu) j' hj''
  show d.wb * j' * d.wb⁻¹ * (d.wb * u * d.wb⁻¹) = d.wb * u * d.wb⁻¹ * (d.wb * j' * d.wb⁻¹)
  calc d.wb * j' * d.wb⁻¹ * (d.wb * u * d.wb⁻¹) = d.wb * (j' * u) * d.wb⁻¹ := by group
    _ = d.wb * (u * j') * d.wb⁻¹ := by rw [e]
    _ = d.wb * u * d.wb⁻¹ * (d.wb * j' * d.wb⁻¹) := by group

theorem yamadaM₂_inf_centralizer_J₁_four (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (hK4 : Nat.card K = 4) :
    yamadaM₂ d t ⊓ centralizer (d.J₁ : Set G) = yamadaY₂ d t := by
  have hY₂J := h.yamadaY₂_le_centralizer_J₁_four d hD hK4
  refine le_antisymm (fun x hx => ?_)
    (le_inf (le_sup_right : yamadaY₂ d t ≤ d.M ⊔ yamadaY₂ d t) hY₂J)
  obtain ⟨hxM, hxJ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨m, hm, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer'
    ((h.M_le_centralizer_yamadaY₂ d hK hD).trans (Subgroup.centralizer_le_normalizer _)) _ hxM
  have hmJ : m ∈ centralizer (d.J₁ : Set G) := by
    have := mul_mem hxJ (inv_mem (hY₂J hy))
    rwa [mul_inv_cancel_right] at this
  have hmY : m ∈ d.Y := by
    rw [← d.M_inf_centralizer_J₁_four hK4]
    exact Subgroup.mem_inf.2 ⟨hm, hmJ⟩
  exact mul_mem (h.Y_le_yamadaY₂ d hK hD hmY) hy

theorem yamadaL₃_inf_centralizer_J₁_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (hK4 : Nat.card K = 4) :
    yamadaL₃ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaL₂ d t := by
  intro x hx
  obtain ⟨hxL₃, hxJ⟩ := Subgroup.mem_inf.1 hx
  have hxV : x ∈ normalizer (yamadaV₂ d t : Set G) := LieType.BorelTits.pCoreOf_le 2 _ hxL₃
  have ht := h.t_mem_centralizer_J₁ d
  have hκY : t * x * t * x⁻¹ ∈ d.Y := by
    rw [← d.W_inf_centralizer_J₁_four hK4]
    exact Subgroup.mem_inf.2 ⟨h.crossed_mem_W hW d hK hD hxV,
      mul_mem (mul_mem (mul_mem ht hxJ) ht) (inv_mem hxJ)⟩
  exact h.yamadaL₃_inf_le d hK hD (Subgroup.mem_inf.2
    ⟨hxL₃, (h.crossed_mem_Y_iff hW d hK hD hxV).1 hκY⟩)

theorem inf_centralizer_J₁_le_yamadaY₂_four (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hK4 : Nat.card K = 4) {A : Subgroup G} (hAL₃ : A ≤ yamadaL₃ d t)
    (hAL₂ : A ⊓ yamadaL₂ d t ≤ yamadaM₂ d t) :
    A ⊓ centralizer (d.J₁ : Set G) ≤ yamadaY₂ d t := by
  intro x hx
  obtain ⟨hxA, hxJ⟩ := Subgroup.mem_inf.1 hx
  have hxL₂ := h.yamadaL₃_inf_centralizer_J₁_four hW d hK hD hK4
    (Subgroup.mem_inf.2 ⟨hAL₃ hxA, hxJ⟩)
  rw [← h.yamadaM₂_inf_centralizer_J₁_four d hK hD hK4]
  exact Subgroup.mem_inf.2 ⟨hAL₂ (Subgroup.mem_inf.2 ⟨hxA, hxL₂⟩), hxJ⟩

theorem le_centralizer_yamadaY₂_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (hK4 : Nat.card K = 4)
    {A : Subgroup G} (hAL₃ : A ≤ yamadaL₃ d t) (hAL₂ : A ⊓ yamadaL₂ d t ≤ yamadaM₂ d t)
    (hJA : d.J₁ ≤ normalizer (A : Set G)) :
    A ≤ centralizer (yamadaY₂ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hAL₃
  have hsolv : Group.IsSolvable A := by
    have := hA2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₁).Coprime (Nat.card A) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA2
    rw [hk, d.card_J₁, hK4]
    exact Nat.Coprime.pow_right k (by norm_num)
  refine le_centralizer_of_inf_centralizer_le (fun x hx => ?_) hJA
    (Subgroup.le_centralizer_iff.1 (h.yamadaY₂_le_centralizer_J₁_four d hD hK4)) hsolv hcop
    (h.inf_centralizer_J₁_le_yamadaY₂_four hW d hK hD hK4 hAL₃ hAL₂)
    fun x hx y hy => h.yamadaY₂_mul_comm d hK hD hx hy
  exact (h.yamada_5_23_1 hW d hK hD).2.2.2.1 (LieType.BorelTits.pCoreOf_le 2 _ (hAL₃ hx))

theorem yamadaX₂_inf_centralizer_J₁_four (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (hK4 : Nat.card K = 4) :
    yamadaX₂ d t ⊓ centralizer (d.J₁ : Set G) = yamadaY₂ d t := by
  have hY₂J := h.yamadaY₂_le_centralizer_J₁_four d hD hK4
  refine le_antisymm (fun x hx => ?_)
    (le_inf (le_sup_right : yamadaY₂ d t ≤ d.X ⊔ yamadaY₂ d t) hY₂J)
  obtain ⟨hxX, hxJ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer'
    ((h.X_le_centralizer_yamadaY₂ d hK hD).trans (Subgroup.centralizer_le_normalizer _)) _ hxX
  have haJ : a ∈ centralizer (d.J₁ : Set G) := by
    have := mul_mem hxJ (inv_mem (hY₂J hy))
    rwa [mul_inv_cancel_right] at this
  have haY : a ∈ d.Y := by
    rw [← d.X_inf_centralizer_J₁_four hK4]
    exact Subgroup.mem_inf.2 ⟨ha, haJ⟩
  exact mul_mem (h.Y_le_yamadaY₂ d hK hD haY) hy

theorem yamadaR₄_inf_centralizer_J₁_four (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (hK4 : Nat.card K = 4) :
    yamadaR₄ d t ⊓ centralizer (d.J₁ : Set G) ≤ yamadaR₂ d t := by
  intro x hx
  obtain ⟨hxR₄, hxJ⟩ := Subgroup.mem_inf.1 hx
  have hxU : x ∈ normalizer (yamadaU₂ d t : Set G) := LieType.BorelTits.pCoreOf_le 2 _ hxR₄
  have ht := h.t_mem_centralizer_J₁ d
  have hκX := h.crossed_mem_X hW d hK hD hxU
  have hκY : t * x * t * x⁻¹ ∈ d.Y := by
    rw [← d.X_inf_centralizer_J₁_four hK4]
    exact Subgroup.mem_inf.2 ⟨hκX, mul_mem (mul_mem (mul_mem ht hxJ) ht) (inv_mem hxJ)⟩
  obtain ⟨_, _, φ, hφ, -⟩ := h.yamada_5_25_3 hW d hK hD
  have e := hφ ⟨x, hxR₄⟩ ⟨_, hκX⟩ (h.conj_t_eq_mul_crossed x)
  have h1 : (QuotientGroup.mk (⟨_, hκX⟩ : d.X) : d.X ⧸ d.Y.subgroupOf d.X) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hκY)
  rw [h1, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at e
  exact mem_subgroupOf.1 e

theorem inf_centralizer_J₁_le_yamadaY₂_four_of_le_yamadaR₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hK4 : Nat.card K = 4) {A : Subgroup G} (hAR₄ : A ≤ yamadaR₄ d t)
    (hAR₂ : A ⊓ yamadaR₂ d t ≤ yamadaX₂ d t) :
    A ⊓ centralizer (d.J₁ : Set G) ≤ yamadaY₂ d t := by
  intro x hx
  obtain ⟨hxA, hxJ⟩ := Subgroup.mem_inf.1 hx
  have hxR₂ := h.yamadaR₄_inf_centralizer_J₁_four hW d hK hD hK4
    (Subgroup.mem_inf.2 ⟨hAR₄ hxA, hxJ⟩)
  rw [← h.yamadaX₂_inf_centralizer_J₁_four d hK hD hK4]
  exact Subgroup.mem_inf.2 ⟨hAR₂ (Subgroup.mem_inf.2 ⟨hxA, hxR₂⟩), hxJ⟩

theorem le_centralizer_yamadaY₂_four_of_le_yamadaR₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    (hK4 : Nat.card K = 4) {A : Subgroup G} (hAR₄ : A ≤ yamadaR₄ d t)
    (hAR₂ : A ⊓ yamadaR₂ d t ≤ yamadaX₂ d t) (hJA : d.J₁ ≤ normalizer (A : Set G)) :
    A ≤ centralizer (yamadaY₂ d t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hAR₄
  have hsolv : Group.IsSolvable A := by
    have := hA2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₁).Coprime (Nat.card A) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA2
    rw [hk, d.card_J₁, hK4]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  refine le_centralizer_of_inf_centralizer_le (fun x hx => ?_) hJA
    (Subgroup.le_centralizer_iff.1 (h.yamadaY₂_le_centralizer_J₁_four d hD hK4)) hsolv hcop
    (h.inf_centralizer_J₁_le_yamadaY₂_four_of_le_yamadaR₄ hW d hK hD hK4 hAR₄ hAR₂)
    fun x hx y hy => h.yamadaY₂_mul_comm d hK hD hx hy
  exact hFY (hEF (hRE ((h.yamada_5_25_1 hW d hK hD).2.2.2
    (LieType.BorelTits.pCoreOf_le 2 _ (hAR₄ hx)))))


end QFourJ₁

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
