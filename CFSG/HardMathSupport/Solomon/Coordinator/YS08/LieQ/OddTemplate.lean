module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Template

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.OppCl

section OddTemplate

variable {F : Type} [Field F] {q : ℕ} [Fact q.Prime] {V : Type} [AddCommGroup V] [Module F V]
  {H : Type} [Group H]

theorem commute_of_mk_commute (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZo : Nat.Coprime (Nat.card Z) q) {x k : H} {n : ℕ} (hk : k ^ q ^ n = 1)
    (h : QuotientGroup.mk' Z x * QuotientGroup.mk' Z k =
      QuotientGroup.mk' Z k * QuotientGroup.mk' Z x) :
    x * k = k * x := by
  have h1 : QuotientGroup.mk' Z (x * k) = QuotientGroup.mk' Z (k * x) := by
    rw [map_mul, map_mul]
    exact h
  obtain ⟨z, hz, hzk⟩ := (QuotientGroup.mk'_eq_mk' Z).mp h1
  have hzi : ∀ g : H, g * z⁻¹ = z⁻¹ * g := fun g =>
    Subgroup.mem_center_iff.mp (hZc (Z.inv_mem hz)) g
  have e1 : x * k = k * x * z⁻¹ := by
    calc x * k = x * k * z * z⁻¹ := by group
      _ = k * x * z⁻¹ := by rw [hzk]
  have hconj : x * k * x⁻¹ = k * z⁻¹ := by
    calc x * k * x⁻¹ = (k * x * z⁻¹) * x⁻¹ := by rw [e1]
      _ = k * (x * z⁻¹ * x⁻¹) := by group
      _ = k * (z⁻¹ * x * x⁻¹) := by rw [hzi x]
      _ = k * z⁻¹ := by group
  have hpow : z⁻¹ ^ q ^ n = 1 := by
    have h2 : (x * k * x⁻¹) ^ q ^ n = 1 := by
      rw [show x * k * x⁻¹ = MulAut.conj x k from rfl, ← map_pow, hk, map_one]
    rw [hconj] at h2
    have hcomm : Commute k z⁻¹ := hzi k
    rw [hcomm.mul_pow, hk, one_mul] at h2
    exact h2
  have hzo : z = 1 := by
    have hord : orderOf z⁻¹ = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (by
          rw [orderOf_inv]
          exact Z.orderOf_dvd_natCard hz) (Nat.Coprime.pow_right _ hZo))
        (orderOf_dvd_of_pow_eq_one hpow)
    rw [orderOf_eq_one_iff, inv_eq_one] at hord
    exact hord
  rw [hzo, mul_one] at hzk
  exact hzk

variable [Finite F] [CharP F q] [Finite V] [Finite H]

theorem exists_flagKernel_eq (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZo : Nat.Coprime (Nat.card Z) q) (ρ : H →* Module.End F V) (hρ : Function.Injective ρ)
    (𝔉 : Subgroup H → ℕ → Submodule F V)
    (h0 : ∀ Q : Subgroup H, IsPGroup q Q → 𝔉 Q 0 = ⊥)
    (htop : ∀ Q : Subgroup H, IsPGroup q Q → ∃ m, 𝔉 Q m = ⊤)
    (hnorm : ∀ Q : Subgroup H, IsPGroup q Q → Subgroup.normalizer (Q : Set H) ≤ flagStab ρ (𝔉 Q))
    (hker : ∀ Q : Subgroup H, IsPGroup q Q → Q ≤ flagKernel ρ (𝔉 Q))
    {R : Subgroup (H ⧸ Z)} (hR : IsRadical q R) :
    ∃ Qt : Subgroup H, IsPGroup q Qt ∧ Qt.map (QuotientGroup.mk' Z) = R ∧
      flagKernel ρ (𝔉 Qt) = Qt ∧ Qt ≠ ⊥ := by
  obtain ⟨Qt, hQt2, hQtmap⟩ := exists_isPGroup_map_eq (r := q) Z hR.2.1
  obtain ⟨m, hm⟩ := htop Qt hQt2
  have hKF2 : IsPGroup q (flagKernel ρ (𝔉 Qt)) := isPGroup_flagKernel ρ q hρ (h0 Qt hQt2) hm
  have hQtKF : Qt ≤ flagKernel ρ (𝔉 Qt) := hker Qt hQt2
  have hNnorm : Subgroup.normalizer (Qt : Set H) =
      (Subgroup.normalizer (R : Set (H ⧸ Z))).comap (QuotientGroup.mk' Z) := by
    rw [normalizer_eq_comap_normalizer_map Z hZc hZo hQt2, hQtmap]
  have hcore : pCoreOf q (Subgroup.normalizer (Qt : Set H)) ≤ Qt := by
    intro x hx
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup q (Subgroup.normalizer (Qt : Set H))) ⟨x, hx⟩
    have hxn : x ^ q ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : QuotientGroup.mk' Z x ∈
        (pCoreOf q (Subgroup.normalizer (Qt : Set H))).map (QuotientGroup.mk' Z) := ⟨x, hx, rfl⟩
    have h2 := map_pCoreOf_le (QuotientGroup.mk' Z) _ h1
    have h3 : (Subgroup.normalizer (Qt : Set H)).map (QuotientGroup.mk' Z) =
        Subgroup.normalizer (R : Set (H ⧸ Z)) := by
      rw [hNnorm, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]
    rw [h3, hR.2.2.1, ← hQtmap] at h2
    exact mem_of_mk_mem_map Z hZc hZo hQt2 h2 hxn
  have hbase : flagKernel ρ (𝔉 Qt) ⊓ Subgroup.normalizer (Qt : Set H) ≤ Qt := by
    refine le_trans ?_ hcore
    refine le_pCoreOf_of_le_normalizer q inf_le_right ?_ (hKF2.to_le inf_le_left)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ Subgroup.normalizer (Qt : Set H), ∀ n ∈ flagKernel ρ (𝔉 Qt) ⊓
        Subgroup.normalizer (Qt : Set H), g * n * g⁻¹ ∈ flagKernel ρ (𝔉 Qt) ⊓
          Subgroup.normalizer (Qt : Set H) := by
      intro g hg n hn
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (flagStab_le_normalizer_flagKernel ρ (𝔉 Qt)
          (hnorm Qt hQt2 hg)) n).mp hn1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hn2) (Subgroup.inv_mem _ hg)
    intro n
    refine ⟨fun hn => key g hg n hn, fun hn => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hn
    simpa [mul_assoc] using this
  have hKFeq : flagKernel ρ (𝔉 Qt) = Qt :=
    (eq_of_inf_normalizer_le' (Fact.out : q.Prime) hKF2 hQtKF hbase).symm
  have hQt0 : Qt ≠ ⊥ := by
    rintro rfl
    apply hR.1
    rw [← hQtmap, Subgroup.map_bot]
  exact ⟨Qt, hQt2, hQtmap, hKFeq, hQt0⟩

theorem radRigidInner_of_rigid (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZo : Nat.Coprime (Nat.card Z) q) (ρ : H →* Module.End F V) (hρ : Function.Injective ρ)
    (𝔉 : Subgroup H → ℕ → Submodule F V)
    (h0 : ∀ Q : Subgroup H, IsPGroup q Q → 𝔉 Q 0 = ⊥)
    (htop : ∀ Q : Subgroup H, IsPGroup q Q → ∃ m, 𝔉 Q m = ⊤)
    (hnorm : ∀ Q : Subgroup H, IsPGroup q Q → Subgroup.normalizer (Q : Set H) ≤ flagStab ρ (𝔉 Q))
    (hker : ∀ Q : Subgroup H, IsPGroup q Q → Q ≤ flagKernel ρ (𝔉 Q))
    (hscal : ∀ x : H, (∃ c : F, ∀ v, ρ x v = c • v) → x ∈ Z)
    (hrigid : ∀ Q : Subgroup H, IsPGroup q Q → flagKernel ρ (𝔉 Q) ≠ ⊥ → ∀ x : H,
      Nat.Coprime (orderOf x) q → (∀ k ∈ flagKernel ρ (𝔉 Q), x * k = k * x) →
        ∃ c : F, ∀ v, ρ x v = c • v) :
    RadRigidInner q (H ⧸ Z) := by
  intro R hR y hy hyo
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨Qt, hQt, hQtmap, hKF, hQt0⟩ :=
    exists_flagKernel_eq Z hZc hZo ρ hρ 𝔉 h0 htop hnorm hker hR
  have hxo : Nat.Coprime (orderOf x) q := by
    set m := orderOf (x : H ⧸ Z) with hm
    have hxm : x ^ m ∈ Z := by
      have h1 : ((x : H ⧸ Z)) ^ m = 1 := pow_orderOf_eq_one _
      rw [← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    have h2 : (x ^ m) ^ Nat.card Z = 1 := by
      have h3 : ((⟨x ^ m, hxm⟩ : Z) ^ Nat.card Z : Z) = 1 := pow_card_eq_one'
      have h4 := congrArg (fun z : Z => (z : H)) h3
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mk] using h4
    have hdvd : orderOf x ∣ m * Nat.card Z := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul]
      exact h2
    exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_mul_iff_left.2 ⟨hyo, hZo⟩)
  have hcomm : ∀ k ∈ flagKernel ρ (𝔉 Qt), x * k = k * x := by
    intro k hk
    rw [hKF] at hk
    obtain ⟨n, hn⟩ := hQt ⟨k, hk⟩
    have hkn : k ^ q ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine commute_of_mk_commute Z hZc hZo hkn ?_
    have := hy (QuotientGroup.mk' Z k) (hQtmap ▸ Subgroup.mem_map_of_mem _ hk)
    exact this
  obtain ⟨c, hc⟩ := hrigid Qt hQt (by rw [hKF]; exact hQt0) x hxo hcomm
  exact (QuotientGroup.eq_one_iff x).2 (hscal x ⟨c, hc⟩)

end OddTemplate

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
