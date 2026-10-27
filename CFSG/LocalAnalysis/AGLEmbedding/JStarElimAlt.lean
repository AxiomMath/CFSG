module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.LocalAnalysis.AGLEmbedding.JStarElimAltAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding

open Equiv

theorem exists_prime_dvd_pow_sub_one_coprime {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 3 ≤ n) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ p ^ n - 1 ∧ ℓ.Coprime 6 ∧ ℓ.Coprime (p - 1) := by
  obtain ⟨ℓ, hℓ, hdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p) (by omega) hn
  have h1 : ¬ ℓ ∣ p - 1 := by simpa using hprim 1 one_pos (by omega)
  have h2 : ¬ ℓ ∣ p ^ 2 - 1 := hprim 2 two_pos (by omega)
  have hl2 : ℓ ≠ 2 := by
    rintro rfl
    exact h1 (hp.even_sub_one (by omega)).two_dvd
  have hl3 : ℓ ≠ 3 := by
    rintro rfl
    apply h2
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
      omega
    have hpp : p * p % 3 = 1 := by
      rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h <;> simp [Nat.mul_mod, h]
    have : 1 ≤ p * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [sq]
    omega
  refine ⟨ℓ, hℓ, hdvd, (Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun h6 => ?_,
    (Nat.Prime.coprime_iff_not_dvd hℓ).mpr h1⟩
  rcases (Nat.Prime.dvd_mul hℓ).mp (show ℓ ∣ 2 * 3 from h6) with h | h
  · exact hl2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h)
  · exact hl3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h)

theorem false_of_surjective_psl2GF_of_five_le {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hn : 3 ≤ n) {J : Type*} [Group J] [Finite J] (ι : J →* Perm (Fin (3 * p)))
    (hι : Function.Injective ι) (φ : J →* PSL2GF p n) (hφ : Function.Surjective φ) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨ℓ, hℓ, hℓdvd, hℓ6, hℓp⟩ := exists_prime_dvd_pow_sub_one_coprime hp hp5 hn
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨E⟩ : Nonempty (Sylow p J) := inferInstance
  set U : Subgroup (PSL2GF p n) := (E : Subgroup J).map φ with hUdef
  have hUcard : Nat.card U = p ^ n := by
    have := (psl2GF_sylow p n (by omega) (E.mapSurjective hφ)).2
    rwa [Sylow.coe_mapSurjective] at this
  obtain ⟨ψ, hψinj, hψrange, hψ⟩ :=
    exists_torus_param_of_mulEquiv_psl2GF (by omega) (by omega) Subgroup.topEquiv U le_top hUcard
  have hU : ∀ u ∈ U, ∃ a, ψ a = u := fun u hu => by rwa [← hψrange] at hu
  obtain ⟨μ, hμ⟩ : ∃ μ : (GaloisField p n)ˣ, orderOf μ = ℓ := by
    apply exists_prime_orderOf_dvd_card'
    rwa [Nat.card_units, GaloisField.card p n (by omega)]
  obtain ⟨c, -, hc⟩ := hψ μ
  have hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U := by
    intro u hu
    obtain ⟨a, rfl⟩ := hU u hu
    rw [hc a, ← hψrange]
    exact ⟨_, rfl⟩
  obtain ⟨j, hj⟩ := hφ c
  set M : Subgroup J := U.comap φ with hMdef
  have hEM : (E : Subgroup J) ≤ M := Subgroup.le_comap_map φ E
  have hjEM : ((j • E : Sylow p J) : Subgroup J) ≤ M := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change φ (MulAut.conj j • y) ∈ U
    rw [MulAut.smul_def, MulAut.conj_apply, map_mul, map_mul, map_inv, hj]
    exact hcU _ (Subgroup.mem_map_of_mem φ hy)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M ((j • E).subtype hjEM) (E.subtype hEM)
  rw [Sylow.smul_subtype] at hk
  have hgE : ((k : J) * j) • E = E := by
    rw [mul_smul]
    exact Sylow.subtype_injective hk
  set g : J := (k : J) * j with hgdef
  have hgN : g ∈ Subgroup.normalizer ((E : Subgroup J) : Set J) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hgE
  obtain ⟨b, hb⟩ := hU _ k.2
  have hgψ : ∀ a, φ g * ψ a * (φ g)⁻¹ =
      ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a)) := by
    intro a
    rw [hgdef, map_mul, hj, ← hb, mul_inv_rev,
      show ψ b * c * ψ a * (c⁻¹ * (ψ b)⁻¹) = ψ b * (c * ψ a * c⁻¹) * (ψ b)⁻¹ by group, hc a,
      ← map_inv, ← map_mul, ← map_mul, mul_comm b, mul_inv_cancel_right]
  have hiter : ∀ i : ℕ, ∀ a, φ g ^ i * ψ a * (φ g ^ i)⁻¹ =
      ψ (Multiplicative.ofAdd (((μ : GaloisField p n) ^ 2) ^ i * Multiplicative.toAdd a)) := by
    intro i
    induction i with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      rw [pow_succ' (φ g) i, mul_inv_rev,
        show φ g * φ g ^ i * ψ a * ((φ g ^ i)⁻¹ * (φ g)⁻¹) =
          φ g * (φ g ^ i * ψ a * (φ g ^ i)⁻¹) * (φ g)⁻¹ by group,
        ih, hgψ, toAdd_ofAdd, pow_succ' ((μ : GaloisField p n) ^ 2) i, mul_assoc]
  obtain ⟨e', m, hm, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' ℓ hℓ.one_lt.ne'
  have hxord : orderOf (g ^ m) ∣ ℓ ^ e' :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one])
  obtain ⟨e, he, hφe⟩ : ∃ e ∈ (E : Subgroup J), φ e = ψ (Multiplicative.ofAdd 1) := by
    have : ψ (Multiplicative.ofAdd 1) ∈ U := by rw [← hψrange]; exact ⟨_, rfl⟩
    exact Subgroup.mem_map.mp this
  have hne : g ^ m * e * (g ^ m)⁻¹ ≠ e := by
    intro heq
    have h2 := congrArg φ heq
    rw [map_mul, map_mul, map_inv, map_pow, hφe, hiter, toAdd_ofAdd, mul_one] at h2
    have h3 := congrArg Multiplicative.toAdd (hψinj h2)
    simp only [toAdd_ofAdd] at h3
    have h4 : μ ^ (2 * m) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul, Units.val_one]
      exact h3
    rw [← orderOf_dvd_iff_pow_eq_one, hμ] at h4
    rcases (Nat.Prime.dvd_mul hℓ).mp h4 with h5 | h5
    · exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp hℓ6 (h5.trans (by norm_num))
    · exact hm h5
  have hord : orderOf (ι (g ^ m)) ∣ ℓ ^ e' := (orderOf_map_dvd ι _).trans hxord
  have hcard : Nat.card (Fin (3 * p)) = 3 * p := Nat.card_fin _
  have hcomm := conj_eq_of_mem_normalizer_of_card_lt (E.isPGroup'.map ι)
    (by rw [hcard]; omega) (by rw [hcard]; nlinarith)
    (Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι (pow_mem hgN m)))
    ((Nat.Coprime.pow_left e' hℓ6).coprime_dvd_left hord)
    ((Nat.Coprime.pow_left e' hℓp).coprime_dvd_left hord) (Subgroup.mem_map_of_mem ι he)
  exact hne (hι (by rw [map_mul, map_mul, map_inv]; exact hcomm))

theorem false_of_surjective_psl2GF_three {n : ℕ} (hn : 3 ≤ n) {J : Type*} [Group J]
    (ι : J →* Perm (Fin (3 * 3))) (hι : Function.Injective ι) (φ : J →* PSL2GF 3 n)
    (hφ : Function.Surjective φ) : False := by
  have hdvd := (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_dvd_of_injective ι hι)
  rw [Nat.card_perm, Nat.card_fin, show Nat.factorial (3 * 3) = 362880 by decide,
    CFSG.SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num)
      (GaloisField.card 3 n (by omega))] at hdvd
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
  · norm_num at hdvd
  · norm_num at hdvd
  · have h6 := (pow_dvd_pow 3 h5).trans ((Dvd.intro _ rfl).trans hdvd)
    norm_num at h6

theorem false_of_surjective_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    {J : Type*} [Group J] [Finite J] (ι : J →* Perm (Fin (3 * p))) (hι : Function.Injective ι)
    (φ : J →* PSL2GF p n) (hφ : Function.Surjective φ) : False := by
  have hp : p.Prime := Fact.out
  rcases hp.eq_two_or_odd with h | h
  · exact hp2 h
  rcases (show p = 3 ∨ 5 ≤ p by have := hp.two_le; omega) with rfl | hp5
  · exact false_of_surjective_psl2GF_three hn ι hι φ hφ
  · exact false_of_surjective_psl2GF_of_five_le hp5 hn ι hι φ hφ

theorem kFactJStarElimAlt : KFactJStarElimAlt := by
  rintro p n _ hp2 hn L _ _ ⟨e⟩ ⟨A, J, -, -, -, φ, hφ, -⟩
  have hp : p.Prime := Fact.out
  have h3p : 9 ≤ 3 * p := by have := hp.two_le; omega
  let Θ : MulAut L ≃* Perm (Fin (3 * p)) := (MulAut.congr e).trans (MulEquiv.ofBijective _
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj (3 * p) (by omega)
      (by omega))).symm
  have : Finite (MulAut L) := Finite.of_injective Θ Θ.injective
  exact false_of_surjective_psl2GF hp2 hn (Θ.toMonoidHom.comp J.subtype)
    (Θ.injective.comp J.subtype_injective) φ hφ

end CFSG.AGLEmbedding
