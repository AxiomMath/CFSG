module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC1
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG.RankTwoShapes
open scoped Pointwise

namespace UTSylow

variable {X : Type} [Group X] (D : UTSylow X)

theorem Z_comm {z t : X} (hz : z ∈ D.Z) (ht : t ∈ (D.T : Subgroup X)) : z * t = t * z := by
  obtain ⟨u, hu, rfl⟩ := hz
  obtain ⟨v, rfl⟩ := D.exists_toX ht
  rw [← map_mul, ← map_mul, (ut_mul_comm_iff u v).mpr (by
    rw [(mem_Zu.mp hu).1, (mem_Zu.mp hu).2, zero_mul, mul_zero])]

theorem Z_sq {z : X} (hz : z ∈ D.Z) : z * z = 1 := by
  obtain ⟨u, hu, rfl⟩ := hz
  rw [← map_mul, (ut_mul_self_eq_one_iff u).mpr (Or.inl (mem_Zu.mp hu).1), map_one]

theorem comm_mem_Z {x y : X} (hx : x ∈ (D.T : Subgroup X)) (hy : y ∈ (D.T : Subgroup X)) :
    x⁻¹ * y⁻¹ * x * y ∈ D.Z := by
  obtain ⟨u, rfl⟩ := D.exists_toX hx
  obtain ⟨v, rfl⟩ := D.exists_toX hy
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact ⟨_, mem_Zu.mpr (ut_comm_mem_Z u v), rfl⟩

theorem comm_mem_Z' {x y : X} (hx : x ∈ (D.T : Subgroup X)) (hy : y ∈ (D.T : Subgroup X)) :
    x * y * x⁻¹ * y⁻¹ ∈ D.Z := by
  have h := D.comm_mem_Z (inv_mem hx) (inv_mem hy)
  rwa [inv_inv, inv_inv] at h

theorem centric_cases {Q : Subgroup X} (hQT : Q ≤ (D.T : Subgroup X))
    (hcen : centralizer (Q : Set X) ⊓ (D.T : Subgroup X) ≤ Q) :
    Q = D.T ∨ Q = D.E ∨ Q = D.F ∨ (∀ x, x ∈ D.Z ↔ x ∈ Q ∧ x ∈ centralizer (Q : Set X)) ∨
      (∀ x, x ∈ D.Z ↔ x ∈ Q ∧ x * x = 1) := by
  have hZT := D.Z_le_T
  have hZC : D.Z ≤ centralizer (Q : Set X) := fun z hz =>
    mem_centralizer_iff.mpr fun q hq => (D.Z_comm hz (hQT hq)).symm
  have hZQ : D.Z ≤ Q := fun z hz => hcen (mem_inf.mpr ⟨hZC hz, hZT hz⟩)
  by_cases hab : ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₂ ≠ q₂ * q₁
  · obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ := hab
    refine Or.inr (Or.inr (Or.inr (Or.inl fun x => ⟨fun hx => ⟨hZQ hx, hZC hx⟩, ?_⟩)))
    rintro ⟨hxQ, hxC⟩
    obtain ⟨w, rfl⟩ := D.exists_toX (hQT hxQ)
    obtain ⟨u, rfl⟩ := D.exists_toX (hQT hq₁)
    obtain ⟨v, rfl⟩ := D.exists_toX (hQT hq₂)
    have h1 := mem_centralizer_iff.mp hxC _ hq₁
    have h2 := mem_centralizer_iff.mp hxC _ hq₂
    rw [← map_mul, ← map_mul] at h1 h2 hne
    exact D.toX_mem_Z_iff.mpr (ut_mem_Z_of_comm_comm (fun h => hne (by rw [h]))
      (D.toX_injective h1).symm (D.toX_injective h2).symm)
  · push Not at hab
    have hTZ : ¬ (D.T : Subgroup X) ≤ D.Z := fun h => by
      have := h (D.toX_mem ⟨1, 0, 0⟩)
      exact absurd (D.toX_mem_Z_iff.mp this).1 (by decide)
    have hQZ : ¬ Q ≤ D.Z := fun h => hTZ fun t ht =>
      h (hcen (mem_inf.mpr ⟨mem_centralizer_iff.mpr fun q hq => (D.Z_comm (h hq) ht), ht⟩))
    obtain ⟨q, hqQ, hqZ⟩ := Set.not_subset.mp hQZ
    obtain ⟨u, rfl⟩ := D.exists_toX (hQT hqQ)
    have hu : ¬ (u.a = 0 ∧ u.b = 0) := fun h => hqZ (D.toX_mem_Z_iff.mpr h)
    have hcomm : ∀ x ∈ Q, ∃ w, D.toX w = x ∧ w * u = u * w := fun x hx => by
      obtain ⟨w, rfl⟩ := D.exists_toX (hQT hx)
      exact ⟨w, rfl, D.toX_injective (by rw [map_mul, map_mul]; exact hab _ hx _ hqQ)⟩
    by_cases hub : u.b = 0
    · have hua : u.a ≠ 0 := fun h => hu ⟨h, hub⟩
      refine Or.inr (Or.inl (le_antisymm (fun x hx => ?_) fun x hx => ?_))
      · obtain ⟨w, rfl, hw⟩ := hcomm x hx
        exact D.toX_mem_E_iff.mpr (ut_b_eq_zero_of_comm_E hub hua hw)
      · obtain ⟨w, hw, rfl⟩ := hx
        refine hcen (mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_, D.toX_mem w⟩)
        obtain ⟨w', rfl, hw'⟩ := hcomm y hy
        have hb' := ut_b_eq_zero_of_comm_E hub hua hw'
        rw [← map_mul, ← map_mul, (ut_mul_comm_iff w' w).mpr (by
          rw [hb', mem_Eu.mp hw, mul_zero, mul_zero])]
    · by_cases hua : u.a = 0
      · refine Or.inr (Or.inr (Or.inl (le_antisymm (fun x hx => ?_) fun x hx => ?_)))
        · obtain ⟨w, rfl, hw⟩ := hcomm x hx
          exact D.toX_mem_F_iff.mpr (ut_a_eq_zero_of_comm_F hua hub hw)
        · obtain ⟨w, hw, rfl⟩ := hx
          refine hcen (mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_, D.toX_mem w⟩)
          obtain ⟨w', rfl, hw'⟩ := hcomm y hy
          have ha' := ut_a_eq_zero_of_comm_F hua hub hw'
          rw [← map_mul, ← map_mul, (ut_mul_comm_iff w' w).mpr (by
            rw [ha', mem_Fu.mp hw, zero_mul, zero_mul])]
      · refine Or.inr (Or.inr (Or.inr (Or.inr fun x => ⟨fun hx => ⟨hZQ hx, D.Z_sq hx⟩, ?_⟩)))
        rintro ⟨hxQ, hx2⟩
        obtain ⟨w, rfl, hw⟩ := hcomm x hxQ
        rw [← map_mul, ← map_one D.toX] at hx2
        exact D.toX_mem_Z_iff.mpr (ut_mem_Z_of_comm_mixed hua hub hw (D.toX_injective hx2))

variable [Finite X]

theorem not_isAlperinSubgroup_of_char {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (D.T : Subgroup X) Q) (hQT : Q ≠ D.T)
    (hZ : ∀ n ∈ normalizer (Q : Set X), ∀ z ∈ D.Z, n * z * n⁻¹ ∈ D.Z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQle, -, hcen, hrad⟩ := hQ
  have hZT := D.Z_le_T
  have hZQ : D.Z ≤ Q := fun z hz => hcen (mem_inf.mpr ⟨mem_centralizer_iff.mpr fun q hq =>
    (D.Z_comm hz (hQle hq)).symm, hZT hz⟩)
  let R : Subgroup X :=
    { carrier := {g | g ∈ normalizer (Q : Set X) ∧ (∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ D.Z) ∧
        ∀ z ∈ D.Z, g * z = z * g}
      mul_mem' := by
        rintro g h ⟨hgN, hgQ, hgZ⟩ ⟨hhN, hhQ, hhZ⟩
        refine ⟨mul_mem hgN hhN, fun q hq => ?_, fun z hz => ?_⟩
        · have hq' : h * q * h⁻¹ ∈ Q := (mem_normalizer_iff.mp hhN q).mp hq
          have h1 := hhQ q hq
          have h2 := hgQ _ hq'
          have h3 : g * (h * q * h⁻¹ * q⁻¹) * g⁻¹ = h * q * h⁻¹ * q⁻¹ := by
            rw [hgZ _ h1, mul_assoc, mul_inv_cancel, mul_one]
          have : g * h * q * (g * h)⁻¹ * q⁻¹ =
              (g * (h * q * h⁻¹) * g⁻¹ * (h * q * h⁻¹)⁻¹) * (h * q * h⁻¹ * q⁻¹) := by group
          rw [this]
          exact mul_mem h2 h1
        · rw [mul_assoc, hhZ z hz, ← mul_assoc, hgZ z hz, mul_assoc]
      one_mem' := by
        refine ⟨one_mem _, fun q _ => ?_, fun z _ => by rw [one_mul, mul_one]⟩
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _
      inv_mem' := by
        rintro g ⟨hgN, hgQ, hgZ⟩
        refine ⟨inv_mem hgN, fun q hq => ?_, fun z hz => ?_⟩
        · have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem hgN) q).mp hq
          have h1 := hgQ _ hq'
          rw [show g * (g⁻¹ * q * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * q * g⁻¹⁻¹)⁻¹ =
            q * (g⁻¹ * q * g⁻¹⁻¹)⁻¹ by group] at h1
          have h2 := inv_mem h1
          rwa [show (q * (g⁻¹ * q * g⁻¹⁻¹)⁻¹)⁻¹ = g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ by group] at h2
        · have h := hgZ z hz
          calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * z) * g⁻¹ := by rw [h]
            _ = z * g⁻¹ := by group }
  have hRN : R ≤ normalizer (Q : Set X) := fun g hg => hg.1
  have hRnorm : normalizer (Q : Set X) ≤ normalizer (R : Set X) := by
    intro n hn
    refine mem_normalizer_fintype fun g hg => ?_
    obtain ⟨hgN, hgQ, hgZ⟩ := hg
    refine ⟨mul_mem (mul_mem hn hgN) (inv_mem hn), fun q hq => ?_, fun z hz => ?_⟩
    · have hq' : n⁻¹ * q * n⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem hn) q).mp hq
      have h := hZ n hn _ (hgQ _ hq')
      rwa [show n * (g * (n⁻¹ * q * n⁻¹⁻¹) * g⁻¹ * (n⁻¹ * q * n⁻¹⁻¹)⁻¹) * n⁻¹ =
        n * g * n⁻¹ * q * (n * g * n⁻¹)⁻¹ * q⁻¹ by group] at h
    · have hz' := hZ n⁻¹ (inv_mem hn) z hz
      have h := hgZ _ hz'
      calc n * g * n⁻¹ * z = n * (g * (n⁻¹ * z * n⁻¹⁻¹)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * z * n⁻¹⁻¹) * g) * n⁻¹ := by rw [h]
        _ = z * (n * g * n⁻¹) := by group
  have hQC : Q ⊔ centralizer (Q : Set X) ≤ R := by
    refine sup_le (fun q hq => ⟨le_normalizer hq, fun q' hq' => D.comm_mem_Z' (hQle hq)
      (hQle hq'), fun z hz => D.Z_comm hz (hQle hq) |>.symm⟩) fun c hc => ?_
    refine ⟨centralizer_le_normalizer Q hc, fun q hq => ?_, fun z hz => ?_⟩
    · rw [← mem_centralizer_iff.mp hc q hq, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · exact (mem_centralizer_iff.mp hc z (hZQ hz)).symm
  have hTR : (D.T : Subgroup X) ≤ R := by
    intro t ht
    refine ⟨mem_normalizer_fintype fun q hq => ?_, fun q hq => D.comm_mem_Z' ht (hQle hq),
      fun z hz => (D.Z_comm hz ht).symm⟩
    have h := hZQ (D.comm_mem_Z' ht (hQle hq))
    rw [show t * q * t⁻¹ = t * q * t⁻¹ * q⁻¹ * q by group]
    exact mul_mem h hq
  have hsq : ∀ g ∈ R, g * g ∈ centralizer (Q : Set X) := by
    rintro g ⟨-, hgQ, hgZ⟩
    rw [mem_centralizer_iff]
    intro q hq
    have h1 := hgQ q hq
    set z := g * q * g⁻¹ * q⁻¹ with hz
    have hgq : g * q * g⁻¹ = z * q := by rw [hz]; group
    have h2 : g * g * q * (g * g)⁻¹ = q := by
      calc g * g * q * (g * g)⁻¹ = g * (g * q * g⁻¹) * g⁻¹ := by group
        _ = g * (z * q) * g⁻¹ := by rw [hgq]
        _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
        _ = z * (z * q) := by rw [hgZ z h1, mul_inv_cancel_right, hgq]
        _ = q := by rw [← mul_assoc, D.Z_sq h1, one_mul]
    calc q * (g * g) = g * g * q * (g * g)⁻¹ * (g * g) := by rw [h2]
      _ = g * g * q := by group
  have hidx : ∃ k : ℕ, ((Q ⊔ centralizer (Q : Set X)).subgroupOf R).index = 2 ^ k := by
    have hnorm : ((centralizer (Q : Set X)).subgroupOf R).Normal := by
      refine ⟨fun x hx g => mem_subgroupOf.mpr ?_⟩
      have hgN := hRN g.2
      rw [mem_subgroupOf] at hx
      rw [mem_centralizer_iff]
      intro q hq
      have hq' : (g : X)⁻¹ * q * (g : X)⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem hgN) q).mp hq
      have h := mem_centralizer_iff.mp hx _ hq'
      change q * ((g : X) * (x : X) * (g : X)⁻¹) = (g : X) * (x : X) * (g : X)⁻¹ * q
      calc q * ((g : X) * (x : X) * (g : X)⁻¹) =
          (g : X) * (((g : X)⁻¹ * q * (g : X)⁻¹⁻¹) * (x : X)) * (g : X)⁻¹ := by group
        _ = (g : X) * ((x : X) * ((g : X)⁻¹ * q * (g : X)⁻¹⁻¹)) * (g : X)⁻¹ := by rw [h]
        _ = (g : X) * (x : X) * (g : X)⁻¹ * q := by group
    have hP : IsPGroup 2 (↥R ⧸ (centralizer (Q : Set X)).subgroupOf R) := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨1, ?_⟩
      rw [pow_one, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hsq g g.2
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
    have hdvd : ((Q ⊔ centralizer (Q : Set X)).subgroupOf R).index ∣ 2 ^ m := by
      rw [← hm]
      exact index_dvd_of_le fun x hx => mem_subgroupOf.mpr (mem_sup_right (mem_subgroupOf.mp hx))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hk⟩
  have hReq := hrad R hQC hRN hRnorm hidx
  apply hQT
  refine le_antisymm hQle fun t ht => ?_
  have htR : t ∈ Q ⊔ centralizer (Q : Set X) := hReq ▸ hTR ht
  have hmul : ((Q ⊔ centralizer (Q : Set X) : Subgroup X) : Set X) =
      (Q : Set X) * (centralizer (Q : Set X) : Set X) :=
    coe_mul_of_right_le_normalizer_left Q _ (centralizer_le_normalizer Q)
  have htm : t ∈ (Q : Set X) * (centralizer (Q : Set X) : Set X) := hmul ▸ htR
  obtain ⟨q, hq, c, hc, hqc⟩ := htm
  have hcT : c ∈ (D.T : Subgroup X) := by
    have hc' : c = q⁻¹ * t := by rw [← hqc]; group
    rw [hc']
    exact mul_mem (inv_mem (hQle hq)) ht
  rw [← hqc]
  exact mul_mem hq (hcen (mem_inf.mpr ⟨hc, hcT⟩))

theorem eq_of_isAlperinSubgroup {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (D.T : Subgroup X) Q) : Q = D.T ∨ Q = D.E ∨ Q = D.F := by
  obtain ⟨hQT, -, hcen, -⟩ := id hQ
  rcases D.centric_cases hQT hcen with h | h | h | hZ | hZ
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · by_cases hT : Q = D.T
    · exact Or.inl hT
    refine (D.not_isAlperinSubgroup_of_char hQ hT fun n hn z hz => ?_).elim
    obtain ⟨hzQ, hzC⟩ := (hZ z).mp hz
    refine (hZ _).mpr ⟨(mem_normalizer_iff.mp hn z).mp hzQ, mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq' : n⁻¹ * q * n⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem hn) q).mp hq
    have h := mem_centralizer_iff.mp hzC _ hq'
    calc q * (n * z * n⁻¹) = n * ((n⁻¹ * q * n⁻¹⁻¹) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * q * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
      _ = n * z * n⁻¹ * q := by group
  · by_cases hT : Q = D.T
    · exact Or.inl hT
    refine (D.not_isAlperinSubgroup_of_char hQ hT fun n hn z hz => ?_).elim
    obtain ⟨hzQ, hz2⟩ := (hZ z).mp hz
    refine (hZ _).mpr ⟨(mem_normalizer_iff.mp hn z).mp hzQ, ?_⟩
    rw [show n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ by group, hz2, mul_one,
      mul_inv_cancel]

end UTSylow

end CFSG.ComponentClassification.GHarris.ThmC
