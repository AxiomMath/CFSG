module

public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

@[expose] def NoOddNormal (H : Subgroup G) : Prop :=
  ∀ M : Subgroup G, M ≤ H → (M.subgroupOf H).Normal → Odd (Nat.card M) → M = ⊥

theorem TightDatum.le_centralizer_of_maxPerfect [Finite G] {R : Subgroup G} {S : Sylow 2 R}
    {t : G} (hD : TightDatum R S t) {N H : Subgroup G} [N.Normal] (hHN : H ≤ N)
    (hHt : H ≤ Subgroup.centralizer ({t} : Set G)) [Group.IsPerfect H]
    (hmax : ∀ M : Subgroup G, M ≤ N → M ≤ Subgroup.centralizer ({t} : Set G) → ⁅M, M⁆ = M →
      M ≤ H)
    (hodd : NoOddNormal H) : R ≤ Subgroup.centralizer (H : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hrt : r ∈ Subgroup.centralizer ({t} : Set G) := hD.cent hr
  have hM : H.map (MulAut.conj r).toMonoidHom ≤ H := by
    refine hmax _ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (inferInstance : N.Normal).conj_mem _ (hHN hx) r
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrt (hHt hx)) (Subgroup.inv_mem _ hrt)
    · rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hconj : ∀ x ∈ H, r * x * r⁻¹ ∈ H := fun x hx => hM ⟨x, hx, rfl⟩
  set M₀ : Subgroup G := H ⊓ oddCoreImg R with hM₀def
  have hM₀n : (M₀.subgroupOf H).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨hmH, hmO⟩ := Subgroup.mem_inf.mp hm
    refine Subgroup.mem_inf.mpr ⟨?_, datum_conj_mem_oddCoreImg hD (hHt g.2) hmO⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hmH) (Subgroup.inv_mem _ g.2)
  have hM₀odd : Odd (Nat.card M₀) :=
    (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hM₀ : M₀ = ⊥ := hodd M₀ inf_le_left hM₀n hM₀odd
  have hcH : ⁅h, r⁆ ∈ H := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine Subgroup.mul_mem _ hh ?_
    rw [← mul_assoc]
    exact hconj _ (Subgroup.inv_mem _ hh)
  have hc : ⁅h, r⁆ ∈ M₀ :=
    Subgroup.mem_inf.mpr ⟨hcH, datum_commutator_mem hD hHt h hh r hr⟩
  rw [hM₀, Subgroup.mem_bot] at hc
  exact commutatorElement_eq_one_iff_mul_comm.mp hc

theorem noOddNormal_of_isSimpleGroup [Finite G] {H : Subgroup G} [IsSimpleGroup H]
    (hnab : ∃ a b : H, a * b ≠ b * a) : NoOddNormal H := by
  intro M hMH hMn hMo
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf H) with h | h
  · rwa [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hMH] at h
  · exfalso
    have hHM : H ≤ M := fun x hx => by
      have : (⟨x, hx⟩ : H) ∈ M.subgroupOf H := h ▸ Subgroup.mem_top _
      exact this
    have hodd : Odd (Nat.card H) := by
      rwa [le_antisymm hMH hHM] at hMo
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)) a b)

theorem noOddNormal_of_equiv_sl2 {H : Subgroup G} {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (e : H ≃* SL(2, F)) : NoOddNormal H := by
  intro M hMH hMn hMo
  have hcard : Nat.card (M.subgroupOf H) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv
  have h1 := normal_odd_of_equiv_sl2 hF (by omega) e (M.subgroupOf H) hMn (by rwa [hcard])
  rwa [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hMH] at h1

namespace Q5Cent

theorem sup_le_normalizer {K L : Subgroup G} (hKL : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) :
    K ⊔ L ≤ Subgroup.normalizer (K : Set G) := by
  refine sup_le Subgroup.le_normalizer fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcx : ∀ z ∈ K, y * z * y⁻¹ = z := fun z hz => by
    rw [← hKL z hz y hy, mul_inv_cancel_right]
  constructor
  · intro hx
    rwa [hcx x hx]
  · intro hx
    have hz := hKL _ hx y hy
    have h1 : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * ((y * x * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [hz]
        _ = y * x * y⁻¹ := by group
    rw [h1]
    exact hx

theorem commute_of_noOddNormal {K L M : Subgroup G} (hKL : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hK : NoOddNormal K) (hMH : M ≤ K ⊔ L) (hMn : (M.subgroupOf (K ⊔ L)).Normal)
    (hMo : Odd (Nat.card M)) {m a : G} (hm : m ∈ M) (ha : a ∈ K) : m * a = a * m := by
  have haH : a ∈ K ⊔ L := Subgroup.mem_sup_left ha
  have hconjM : ∀ g ∈ K ⊔ L, ∀ x ∈ M, g * x * g⁻¹ ∈ M := fun g hg x hx => by
    have := hMn.conj_mem ⟨x, hMH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
    rwa [Subgroup.mem_subgroupOf] at this
  have hKM : ((M ⊓ K).subgroupOf K).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxM, hxK⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hconjM _ (Subgroup.mem_sup_left g.2) _ hxM,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hxK) (Subgroup.inv_mem _ g.2)⟩
  have hbot : M ⊓ K = ⊥ :=
    hK _ inf_le_right hKM (hMo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hc : m * a * m⁻¹ * a⁻¹ ∈ M ⊓ K := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mul_assoc, mul_assoc]
      refine Subgroup.mul_mem _ hm ?_
      rw [← mul_assoc]
      exact hconjM _ haH _ (Subgroup.inv_mem _ hm)
    · have hmN := sup_le_normalizer hKL (hMH hm)
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hmN a).mp ha)
        (Subgroup.inv_mem _ ha)
  rw [hbot, Subgroup.mem_bot] at hc
  calc m * a = m * a * m⁻¹ * a⁻¹ * (a * m) := by group
    _ = a * m := by rw [hc, one_mul]

end Q5Cent

theorem noOddNormal_sup {H₁ H₂ : Subgroup G} (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a)
    (h₁ : NoOddNormal H₁) (h₂ : NoOddNormal H₂)
    (hZ : ∀ z ∈ H₁ ⊔ H₂, (∀ x ∈ H₁ ⊔ H₂, z * x = x * z) → Odd (orderOf z) → z = 1) :
    NoOddNormal (H₁ ⊔ H₂) := by
  intro M hMH hMn hMo
  have hcomm' : ∀ a ∈ H₂, ∀ b ∈ H₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  rw [sup_comm] at hMH hMn
  have c₂ := fun {m a : G} (hm : m ∈ M) (ha : a ∈ H₂) =>
    Q5Cent.commute_of_noOddNormal hcomm' h₂ hMH hMn hMo hm ha
  rw [sup_comm] at hMH hMn
  have c₁ := fun {m a : G} (hm : m ∈ M) (ha : a ∈ H₁) =>
    Q5Cent.commute_of_noOddNormal hcomm h₁ hMH hMn hMo hm ha
  rw [eq_bot_iff]
  intro m hm
  have hle : H₁ ⊔ H₂ ≤ Subgroup.centralizer ({m} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (c₁ hm ha).symm)
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (c₂ hm ha).symm)
  have hz : ∀ x ∈ H₁ ⊔ H₂, m * x = x * m := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
  exact Subgroup.mem_bot.mpr (hZ m (hMH hm) hz
    (hMo.of_dvd_nat (Subgroup.orderOf_dvd_natCard M hm)))

end CFSG.ClassicalInvolution.Q3.TA3
