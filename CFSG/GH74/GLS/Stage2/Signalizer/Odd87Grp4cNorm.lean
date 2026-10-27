module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cQ8

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.GH74.GLS.Stage1.Main CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Arith

theorem prime_pow_dvd_24 {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hn : 1 ≤ n)
    (hdvd : p ^ n ∣ 24) : p = 3 ∧ n = 1 := by
  have hp24 : p ∣ 24 := (dvd_pow_self p (by omega)).trans hdvd
  have hp3 : p = 3 := by
    have h24' : p ∣ 2 ^ 3 * 3 := by simpa using hp24
    rcases (Nat.Prime.dvd_mul hp).mp h24' with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)) hodd
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  subst hp3
  refine ⟨rfl, ?_⟩
  by_contra hcon
  have h2n : 2 ≤ n := by omega
  have h9 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 h2n
  have := h9.trans hdvd
  omega

end Arith

section Action

variable {A : Type} [Group A] [Finite A] {p : ℕ} {V X : Subgroup A} {z : A}

omit [Finite A] in
theorem exists_not_mem_centralizer (hV : ⁅V, X⁆ = V) (hne : V ≠ ⊥) :
    ∃ x ∈ X, x ∉ centralizer (V : Set A) := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hV, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hcon

theorem card_range_actOnK_X (h : Setup412 p V X z) (hV : ⁅V, X⁆ = V) (hne : V ≠ ⊥)
    (e : ↥V ≃* QuaternionGroup 2) : p = 3 ∧ Nat.card (actOnKHom V X h.XW).range = 3 := by
  have h24 := natCard_mulAut_of_quaternion e
  have : Fact p.Prime := ⟨h.prime⟩
  set φ := actOnKHom V X h.XW with hφ
  have hpg : IsPGroup p ↥φ.range :=
    h.Xp.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hdvd : p ^ n ∣ 24 := by
    have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hn, h24] at this
  obtain ⟨x₀, hx₀X, hx₀C⟩ := exists_not_mem_centralizer hV hne
  have hφ1 : φ ⟨x₀, hx₀X⟩ ≠ 1 := by
    intro hc
    have : (⟨x₀, hx₀X⟩ : ↥X) ∈ φ.ker := hc
    rw [hφ, actOnKHom_ker, mem_subgroupOf] at this
    exact hx₀C this
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hn
    have hbot : φ.range = ⊥ := (Subgroup.card_eq_one).mp hn
    apply hφ1
    have : φ ⟨x₀, hx₀X⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hp3, hn1'⟩ := prime_pow_dvd_24 h.prime h.odd hn1 hdvd
  refine ⟨hp3, ?_⟩
  rw [hn, hn1', hp3, pow_one]

theorem relIndex_centralizer_eq_three (h : Setup412 p V X z) (hV : ⁅V, X⁆ = V) (hne : V ≠ ⊥)
    (e : ↥V ≃* QuaternionGroup 2) : (centralizer (V : Set A)).relIndex X = 3 := by
  obtain ⟨-, hcard⟩ := card_range_actOnK_X h hV hne e
  have h1 := Subgroup.index_ker (actOnKHom V X h.XW)
  rw [actOnKHom_ker] at h1
  rw [Subgroup.relIndex]
  rw [h1, hcard]

omit [Finite A] in
theorem mem_Z_of_commute (h : Setup412 p V X z) (hC : Core412 V X z) {c : A} (hc : c ∈ V)
    (hcz : c * z = z * c) : c ∈ V ⊓ centralizer (V : Set A) := by
  rw [hC.Z_eq_fix]
  exact Subgroup.mem_inf.2 ⟨hc, CoreA.mem_centralizer_of_commute h hc hcz⟩

omit [Finite A] in
theorem not_inner_of_z (h : Setup412 p V X z) (hC : Core412 V X z) (hzN : z ∈ normalizer (V : Set A))
    (v : ↥V) :
    actOnKHom V (normalizer (V : Set A)) le_rfl ⟨z, hzN⟩ ≠ MulAut.conj v := by
  intro he
  have hk : ∀ k : ↥V, z * (k : A) * z⁻¹ = (v : A) * k * (v : A)⁻¹ := by
    intro k
    have := congrArg (fun m : MulAut ↥V => ((m k : ↥V) : A)) he
    simpa [actOnKHom_apply, MulAut.conj_apply] using this
  have hvz : (v : A) * z = z * (v : A) := by
    have h1 := hk v
    have : z * (v : A) * z⁻¹ = v := by rw [h1]; group
    calc (v : A) * z = (z * (v : A) * z⁻¹) * z := by rw [this]
      _ = z * (v : A) := by group
  have hvZ : (v : A) ∈ V ⊓ centralizer (V : Set A) := mem_Z_of_commute h hC v.2 hvz
  apply hC.nonab
  intro a ha b hb
  have hz_fix : ∀ k : ↥V, z * (k : A) * z⁻¹ = k := by
    intro k
    rw [hk k]
    have := mem_centralizer_iff.mp hvZ.2 k k.2
    calc (v : A) * k * (v : A)⁻¹ = (k : A) * v * (v : A)⁻¹ := by rw [this]
      _ = k := by group
  have haz : a * z = z * a := by
    have := hz_fix ⟨a, ha⟩
    simp only at this
    calc a * z = (z * a * z⁻¹) * z := by rw [this]
      _ = z * a := by group
  have haZ : a ∈ V ⊓ centralizer (V : Set A) := mem_Z_of_commute h hC ha haz
  exact (mem_centralizer_iff.mp haZ.2 b hb).symm

theorem normIso_perm_four (h : Setup412 p V X z) (hV : ⁅V, X⁆ = V) (hne : V ≠ ⊥)
    (e : ↥V ≃* QuaternionGroup 2) : NormIso V (Equiv.Perm (Fin 4)) := by
  have hC : Core412 V X z := core412_of_setup h hV hne
  obtain ⟨θ⟩ := mulAut_equiv_perm_of_quaternion e
  have h24 := natCard_mulAut_of_quaternion e
  have hXN : X ≤ normalizer (V : Set A) := h.XW
  have hzN : z ∈ normalizer (V : Set A) := h.zW
  let ψ : ↥(normalizer (V : Set A)) →* MulAut ↥V := actOnKHom V (normalizer (V : Set A)) le_rfl
  have hψker : ψ.ker = (centralizer (V : Set A)).subgroupOf (normalizer (V : Set A)) :=
    actOnKHom_ker V (normalizer (V : Set A)) le_rfl
  have hV8 : Nat.card ↥V = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hnc : ¬ ∀ a b : ↥V, a * b = b * a := by
    intro hc
    have h1 := hc (e.symm (QuaternionGroup.a 1)) (e.symm (QuaternionGroup.xa 0))
    have h2 := congrArg e h1
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    revert h2
    decide
  have hZ2 : Nat.card (Subgroup.center ↥V) = 2 := card_center_eq_two_of_card_eight hV8 hnc
  have hRtop : ψ.range = ⊤ := by
    set Inn := (MulAut.conj : ↥V →* MulAut ↥V).range with hInn
    have hInnR : Inn ≤ ψ.range := by
      rintro _ ⟨v, rfl⟩
      refine ⟨⟨(v : A), Subgroup.le_normalizer v.2⟩, ?_⟩
      refine MulEquiv.ext fun k => Subtype.ext ?_
      simp [ψ, actOnKHom_apply, MulAut.conj_apply]
    have hInn4 : Nat.card Inn = 4 := by
      have := natCard_range_conj_mul_natCard_center ↥V
      rw [← hInn, hV8, hZ2] at this
      omega
    obtain ⟨-, hcardX⟩ := card_range_actOnK_X h hV hne e
    have hXR : (actOnKHom V X hXN).range ≤ ψ.range := by
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨(b : A), hXN b.2⟩, rfl⟩
    have h4R : 4 ∣ Nat.card ψ.range := hInn4 ▸ Subgroup.card_dvd_of_le hInnR
    have h3R : 3 ∣ Nat.card ψ.range := hcardX ▸ Subgroup.card_dvd_of_le hXR
    have h12R : 12 ∣ Nat.card ψ.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4R h3R
    have hRdvd : Nat.card ψ.range ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card ψ.range
    have hRle : Nat.card ψ.range ≤ 24 := Nat.le_of_dvd (by norm_num) hRdvd
    have hRpos : 0 < Nat.card ψ.range := Nat.card_pos
    have hR : Nat.card ψ.range = 12 ∨ Nat.card ψ.range = 24 := by
      obtain ⟨c, hc⟩ := h12R
      have : c ≤ 2 := by omega
      interval_cases c <;> omega
    rcases hR with hR12 | hR24
    · exfalso
      have hζ : ψ ⟨z, hzN⟩ ∈ ψ.range := ⟨_, rfl⟩
      have hnormal : (Inn.subgroupOf ψ.range).Normal := by
        have := inn_normal ↥V
        exact Subgroup.Normal.subgroupOf this _
      have hrel := Subgroup.relIndex_mul_card Inn ψ.range
      rw [inf_eq_left.mpr hInnR, hInn4, hR12] at hrel
      have hidx : (Inn.subgroupOf ψ.range).index = 3 := by
        rw [← Subgroup.relIndex]; omega
      have hpow := Subgroup.pow_index_mem (Inn.subgroupOf ψ.range) (⟨ψ ⟨z, hzN⟩, hζ⟩ : ↥ψ.range)
      rw [hidx] at hpow
      have hz2 : ψ ⟨z, hzN⟩ * ψ ⟨z, hzN⟩ = 1 := by
        rw [← map_mul]
        have : (⟨z, hzN⟩ : ↥(normalizer (V : Set A))) * ⟨z, hzN⟩ = 1 := Subtype.ext h.z2
        rw [this, map_one]
      have hcube : (⟨ψ ⟨z, hzN⟩, hζ⟩ : ↥ψ.range) ^ 3 = ⟨ψ ⟨z, hzN⟩, hζ⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow]
        calc ψ ⟨z, hzN⟩ ^ 3 = (ψ ⟨z, hzN⟩ * ψ ⟨z, hzN⟩) * ψ ⟨z, hzN⟩ := by
              simp only [pow_succ, pow_zero, one_mul]
          _ = ψ ⟨z, hzN⟩ := by rw [hz2, one_mul]
      rw [hcube] at hpow
      have hmem : ψ ⟨z, hzN⟩ ∈ Inn := Subgroup.mem_subgroupOf.mp hpow
      obtain ⟨v, hv⟩ := hmem
      exact not_inner_of_z h hC hzN v hv.symm
    · exact Subgroup.eq_top_of_card_eq _ (by rw [hR24, h24])
  have hπsurj : Function.Surjective ((θ : MulAut ↥V →* Equiv.Perm (Fin 4)).comp ψ) :=
    θ.surjective.comp (MonoidHom.range_eq_top.mp hRtop)
  have hπker : ((θ : MulAut ↥V →* Equiv.Perm (Fin 4)).comp ψ).ker =
      (centralizer (V : Set A)).subgroupOf (normalizer (V : Set A)) := by
    rw [MonoidHom.ker_mulEquiv_comp, hψker]
  have hnorm : ((centralizer (V : Set A)).subgroupOf (normalizer (V : Set A))).Normal := by
    rw [← hπker]; exact MonoidHom.normal_ker _
  exact ⟨hnorm, ⟨(QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hπsurj)⟩⟩

end Action

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
