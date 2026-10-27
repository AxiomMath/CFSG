module

public import CFSG.Assembly.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_mem_coset_frattini {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (ψ : H ≃* H) (hψ : ψ ^ r = 1)
    (hcomm : ∀ z, ψ z * z⁻¹ ∈ frattini H) (x : H) :
    ∃ y, ψ y = y ∧ x⁻¹ * y ∈ frattini H := by
  classical
  have := Fintype.ofFinite H
  have hfr : ∀ z, ψ z ∈ frattini H ↔ z ∈ frattini H := by
    intro z
    have := SetLike.ext_iff.mp (Subgroup.characteristic_iff_comap_eq.mp (inferInstance : (frattini H).Characteristic) ψ) z
    simpa using this
  have hmem : ∀ y, x⁻¹ * y ∈ frattini H → x⁻¹ * ψ y ∈ frattini H := by
    intro y hy
    have h1 : x⁻¹ * ψ x ∈ frattini H := by
      have := inv_mem (hcomm x⁻¹)
      simpa using this
    have h2 : ψ (x⁻¹ * y) ∈ frattini H := (hfr _).2 hy
    have := mul_mem h1 h2
    simpa [map_mul, mul_assoc] using this
  let α := {y : H // x⁻¹ * y ∈ frattini H}
  let f : Function.End α := fun y => ⟨ψ y.1, hmem y.1 y.2⟩
  have hpow : ∀ n : ℕ, ∀ y : α, ((f ^ n) y).1 = (ψ ^ n) y.1 := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ]
      exact ih (f y)
  have hf : f ^ r ^ 1 = 1 := by
    rw [pow_one]
    funext y
    apply Subtype.ext
    rw [hpow, hψ]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := r) (n := 1) hf
  have hcard : Fintype.card α = Nat.card (frattini H) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft x⁻¹) (fun a => Iff.rfl))
  obtain ⟨k, hk⟩ := (hH.to_subgroup (frattini H)).exists_card_eq
  have hndvd : ¬ r ∣ Fintype.card α := by
    rw [hcard, hk]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 (hr.out.dvd_of_dvd_pow hd)
    exact hr2 this
  have hpos : 0 < Fintype.card f.fixedPoints := by
    rcases Nat.eq_zero_or_pos (Fintype.card f.fixedPoints) with h0 | h0
    · exfalso
      apply hndvd
      rw [h0] at hmod
      exact (Nat.modEq_zero_iff_dvd).1 hmod
    · exact h0
  obtain ⟨⟨y, hy⟩⟩ := Fintype.card_pos_iff.1 hpos
  exact ⟨y.1, congrArg Subtype.val hy, y.2⟩

theorem eq_of_forall_comm_mem_frattini {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (ψ : H ≃* H) (hψ : ψ ^ r = 1)
    (hcomm : ∀ z, ψ z * z⁻¹ ∈ frattini H) (y : H) : ψ y = y := by
  let K : Subgroup H := MonoidHom.eqLocus ψ.toMonoidHom (MonoidHom.id H)
  have hsup : K ⊔ frattini H = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hxy⟩ := exists_fixed_mem_coset_frattini hH hr2 ψ hψ hcomm x
    have hyK : y ∈ K := hy
    have : x = y * (x⁻¹ * y)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hyK (inv_mem hxy)
  have hK : K = ⊤ := frattini_nongenerating hsup
  have : y ∈ K := hK ▸ Subgroup.mem_top y
  exact this

theorem mem_centralizer_of_comm_mem_frattini {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) {s : G}
    (hs : s ∈ Subgroup.normalizer (Q : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hsr : s ^ r = 1)
    (h : ∀ q ∈ Q, s * q * s⁻¹ * q⁻¹ ∈ (frattini ↥Q).map Q.subtype) :
    s ∈ Subgroup.centralizer (Q : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  let ψ : Q ≃* Q := Q.normalizerMonoidHom ⟨s, hs⟩
  have hψ : ψ ^ r = 1 := by
    have : (⟨s, hs⟩ : Subgroup.normalizer (Q : Set G)) ^ r = 1 := Subtype.ext (by simp [hsr])
    show (Q.normalizerMonoidHom ⟨s, hs⟩) ^ r = 1
    rw [← map_pow, this, map_one]
  have hcomm : ∀ z : Q, ψ z * z⁻¹ ∈ frattini ↥Q := by
    intro z
    obtain ⟨w, hw, hwe⟩ := h z.1 z.2
    have hwz : w = ψ z * z⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, InvMemClass.coe_inv]
      simp only [Subgroup.coe_subtype] at hwe
      rw [hwe]
      simp [ψ, mul_assoc]
    rwa [← hwz]
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have := eq_of_forall_comm_mem_frattini hQ2 hr2 ψ hψ hcomm ⟨q, hq⟩
  have h2 := congrArg Subtype.val this
  have h3 : s * q * s⁻¹ = q := by simpa [ψ] using h2
  exact (mul_inv_eq_iff_eq_mul.1 h3).symm

theorem mem_of_commutator_mem_frattini {N Q : Subgroup G} (hQ : Q = pCoreOf 2 N)
    (hC : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) {n : G} (hn : n ∈ N)
    (h : ∀ q ∈ Q, n * q * n⁻¹ * q⁻¹ ∈ (frattini ↥Q).map Q.subtype) : n ∈ Q := by
  have hQN : Q ≤ N := hQ ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hnorm : N ≤ Subgroup.normalizer (Q : Set G) :=
    hQ ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hQ2 : IsPGroup 2 Q := hQ ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  set Φ : Subgroup G := (frattini ↥Q).map Q.subtype with hΦ
  have hΦnorm : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Φ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (frattini ↥Q)
  have hconj : ∀ g ∈ N, ∀ x ∈ Φ, g * x * g⁻¹ ∈ Φ := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hΦnorm (hnorm hg)) x).mp hx
  have hconjQ : ∀ g ∈ N, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hnorm hg) q).mp hq
  let C : Subgroup G :=
    { carrier := {n | n ∈ N ∧ ∀ q ∈ Q, n * q * n⁻¹ * q⁻¹ ∈ Φ}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun q hq => ?_⟩
        have := mul_mem (hconj a ha _ (hb' q hq)) (ha' q hq)
        convert this using 1
        group
      one_mem' := ⟨one_mem _, fun q hq => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun q hq => ?_⟩
        have := hconj a⁻¹ (inv_mem ha) _ (inv_mem (ha' q hq))
        convert this using 1
        group }
  have hCN : C ≤ N := fun x hx => hx.1
  have hCnorm : N ≤ Subgroup.normalizer (C : Set G) := by
    have key : ∀ g ∈ N, ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
      rintro g hg x ⟨hx, hx'⟩
      refine ⟨mul_mem (mul_mem hg hx) (inv_mem hg), fun q hq => ?_⟩
      have hq' : g⁻¹ * q * g ∈ Q := by simpa using hconjQ g⁻¹ (inv_mem hg) q hq
      have := hconj g hg _ (hx' _ hq')
      convert this using 1
      group
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx
  have hC2 : IsPGroup 2 C := by
    rw [IsPGroup.iff_orderOf]
    intro c
    rw [← Subgroup.orderOf_coe]
    by_contra hcon
    push Not at hcon
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (orderOf (c : G)) with ⟨k, hk⟩ | ⟨r, hr, hrd, hodd⟩
    · exact hcon k hk
    · have hne : orderOf (c : G) ≠ 0 := (orderOf_pos _).ne'
      set s : G := (c : G) ^ (orderOf (c : G) / r) with hs
      have hsord : orderOf s = r := orderOf_pow_orderOf_div hne hrd
      have hsC : s ∈ C := pow_mem c.2 _
      have hsr : s ^ r = 1 := hsord ▸ pow_orderOf_eq_one s
      have hr2 : r ≠ 2 := by
        rintro rfl
        exact absurd hodd (by decide)
      have hcent := mem_centralizer_of_comm_mem_frattini hQ2 (hnorm hsC.1) hr hr2 hsr
        (fun q hq => hsC.2 q hq)
      have hsQ : s ∈ Q := hC ⟨hsC.1, hcent⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ2) ⟨s, hsQ⟩
      rw [Subgroup.orderOf_mk, hsord] at hk
      have := (Nat.Prime.pow_eq_iff hr).1 hk.symm
      exact hr2 this.1.symm
  have hCQ : C ≤ pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCN hCnorm hC2
  rw [hQ]
  exact hCQ ⟨hn, h⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
