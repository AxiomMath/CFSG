module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

namespace CyclicColumnSum

open Equiv

section Sylow

variable {H : Type u} [Group H]

theorem centralizer_eq (W P : Subgroup H) (hPW : P ≤ W) (hodd : Odd (Nat.card W))
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hP1 : P ≠ ⊥) :
    Subgroup.centralizer (P : Set H) = Subgroup.centralizer (W : Set H) := by
  apply le_antisymm
  · intro h hh
    by_contra hhW
    apply hP1
    rw [eq_bot_iff]
    intro p hp
    have h1 := hinv h hhW p (hPW hp)
    have h2 : h * p * h⁻¹ = p := by
      rw [← Subgroup.mem_centralizer_iff.mp hh p hp, mul_inv_cancel_right]
    rw [h2] at h1
    have hp2 : p ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel p
    exact Subgroup.mem_bot.mpr (CyclicSymmetricFour.eq_one_of_sq_eq_one W hodd (hPW hp) hp2)
  · exact Subgroup.centralizer_le fun x hx => hPW hx

end Sylow

section Sums

open scoped Classical

variable {H : Type u} [Group H] [Fintype H]

theorem sum_involutions (K : Subgroup H) (χ : H → ℂ)
    (hχ : ∀ x c : H, χ (c * x * c⁻¹) = χ x) (t x : H)
    (hconjt : ∀ u, u ∈ K → orderOf u = 2 → IsConj u t)
    (hconjx : ∀ u, u ∉ K → orderOf u = 2 → IsConj u x) :
    ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2), χ u =
      (Nat.card {u : H // u ∈ K ∧ orderOf u = 2} : ℂ) * χ t +
        (Nat.card {u : H // u ∉ K ∧ orderOf u = 2} : ℂ) * χ x := by
  have hconst : ∀ u c, IsConj u c → χ u = χ c := by
    intro u c huc
    obtain ⟨g, hg⟩ := isConj_iff.mp huc
    rw [← hg, hχ]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun u => u ∈ K)]
  have hcard1 : ((Finset.univ.filter (fun u : H => orderOf u = 2)).filter
      (fun u => u ∈ K)).card = Nat.card {u : H // u ∈ K ∧ orderOf u = 2} := by
    rw [Finset.filter_filter, CyclicSymmetricFour.card_filter_eq_nat_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
  have hcard2 : ((Finset.univ.filter (fun u : H => orderOf u = 2)).filter
      (fun u => u ∉ K)).card = Nat.card {u : H // u ∉ K ∧ orderOf u = 2} := by
    rw [Finset.filter_filter, CyclicSymmetricFour.card_filter_eq_nat_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
  rw [Finset.sum_congr rfl fun u hu => hconst u t (by
      rw [Finset.mem_filter, Finset.mem_filter] at hu
      exact hconjt u hu.2 hu.1.2),
    Finset.sum_congr rfl fun u hu => hconst u x (by
      rw [Finset.mem_filter, Finset.mem_filter] at hu
      exact hconjx u hu.2 hu.1.2),
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard1, hcard2]

end Sums

section Core

open scoped Classical

theorem column_sum_core {H : Type u} [Group H] [Fintype H] (W : Subgroup H) [W.Normal]
    [IsCyclic W] (hodd : Odd (Nat.card W)) {n : ℕ} (hn : 2 ≤ n)
    (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))
    (hautE : ∀ s, autE s = MulAut.conjNormal s)
    (hcenter : ∀ a : alternatingGroup (Fin n), (∀ b, a * b = b * a) → a = 1)
    (hconjA : ∀ g g' : alternatingGroup (Fin n), g ^ 2 = 1 → g ≠ 1 → g' ^ 2 = 1 → g' ≠ 1 →
      ∃ c : alternatingGroup (Fin n), c * g * c⁻¹ = g')
    (hconjS : ∀ s s' : Perm (Fin n), Perm.sign s = -1 → s ^ 2 = 1 → Perm.sign s' = -1 →
      s' ^ 2 = 1 → ∃ c : Perm (Fin n), c * s * c⁻¹ = s')
    (a cin cout c : ℕ) (ha : Nat.card (alternatingGroup (Fin n)) = a)
    (hcin : Nat.card {g : alternatingGroup (Fin n) // g ^ 2 = 1 ∧ g ≠ 1} = cin)
    (hcout : Nat.card {s : Perm (Fin n) // Perm.sign s = -1 ∧ s ^ 2 = 1} = cout)
    (hcin8 : cin * 8 = 2 * a) (hcoutc : cout * c = 2 * a)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (ψ : Subgroup.centralizer (W : Set H) ⧸ W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃*
      alternatingGroup (Fin n))
    (P₂ : Sylow 2 H) (eP : (P₂ : Subgroup H) ≃* DihedralGroup 4)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hℓm : ℓ ∣ Nat.card W) (hℓa : ¬ ℓ ∣ a)
    (P Q : Subgroup H) (hPW : P ≤ W) (hPcard : Nat.card P = ℓ ^ (Nat.card W).factorization ℓ)
    (hQW : Q ≤ W) (hQcard : Nat.card Q * ℓ ^ (Nat.card W).factorization ℓ = Nat.card W)
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ (J : Subgroup H) (π : Subgroup.centralizer (W : Set H) →* P),
      J ≤ Subgroup.centralizer (W : Set H) ∧
      (J.subgroupOf (Subgroup.centralizer (W : Set H))).Characteristic ∧
      Nat.Coprime ℓ (Nat.card J) ∧ P ⊔ J = Subgroup.centralizer (W : Set H) ∧ P ⊓ J = ⊥ ∧
      (∀ p ∈ P, ∀ j ∈ J, p * j = j * p) ∧ Q ≤ J ∧ J.Normal ∧
      (∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ P → (π k : H) = k) ∧
      (∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1) ∧
      (∀ u v : H, orderOf u = 2 → orderOf v = 2 →
        (IsConj u v ↔ (u ∈ Subgroup.centralizer (W : Set H) ↔
          v ∈ Subgroup.centralizer (W : Set H)))) ∧
      Nat.card {u : H // u ∈ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} = cin ∧
      Nat.card {u : H // u ∉ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} =
        cout * Nat.card W ∧
      (∀ u ∈ Subgroup.centralizer (W : Set H), orderOf u = 2 →
        Nat.card (Subgroup.centralizer {u}) = 8 * Nat.card W) ∧
      (∀ u : H, u ∉ Subgroup.centralizer (W : Set H) → orderOf u = 2 →
        Nat.card (Subgroup.centralizer {u}) = c) ∧
      ∀ lam : P →* ℂˣ, orderOf lam = ℓ →
        ∃ θε θμ : basis.index,
          (∀ h : H, (basis.representation θε).character h =
            if h ∈ Subgroup.centralizer (W : Set H) then 1 else -1) ∧
          Module.finrank ℂ (basis.representation θμ).vector = 2 ∧
          (∀ h : H, inducedFunction (Subgroup.centralizer (W : Set H))
              (fun k => 1 - (lam (π k) : ℂ)) h =
            1 + (basis.representation θε).character h - (basis.representation θμ).character h) ∧
          ∀ t ∈ Subgroup.centralizer (W : Set H), orderOf t = 2 →
            ∀ x : H, x ∉ Subgroup.centralizer (W : Set H) → orderOf x = 2 →
            (basis.representation θμ).character t = 2 ∧
            (basis.representation θμ).character x = 0 ∧
            (∀ α : basis.index, (Nat.card H : ℂ)⁻¹ *
                ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u =
              (basis.representation α).character t / (8 * (Nat.card W : ℂ)) +
                (basis.representation α).character x / c) ∧
            ∑ α : basis.index, characterPairing
                (inducedFunction (Subgroup.centralizer (W : Set H))
                  (fun k => 1 - (lam (π k) : ℂ))) (basis.representation α).character *
                ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u) ^ 2 /
                (basis.representation α).character 1 = 2 / (c : ℂ) ^ 2 ∧
            (Nat.card H : ℂ) * ∑ α : basis.index, characterPairing
                (inducedFunction (Subgroup.centralizer (W : Set H))
                  (fun k => 1 - (lam (π k) : ℂ))) (basis.representation α).character *
                ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u) ^ 2 /
                (basis.representation α).character 1 =
              4 * a * (Nat.card W : ℂ) / (c : ℂ) ^ 2 := by
  have hℓp : ℓ.Prime := Fact.out
  have hWK : W ≤ Subgroup.centralizer (W : Set H) := CyclicInversion.le_centralizer_of_isCyclic W
  have hKn : (Subgroup.centralizer (W : Set H)).Normal := Subgroup.normal_of_index_eq_two hindex
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hapos : 0 < a := ha ▸ Nat.card_pos
  have hKcard : Nat.card (Subgroup.centralizer (W : Set H)) = a * Nat.card W := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (W.subgroupOf (Subgroup.centralizer (W : Set H))),
      Nat.card_congr ψ.toEquiv, ha, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv]
  have hHcard : Nat.card H = 2 * a * Nat.card W := by
    rw [← (Subgroup.centralizer (W : Set H)).card_mul_index, hKcard, hindex]
    ring
  obtain ⟨σH, hσsurj, hσker, hσK⟩ := CyclicAlternatingFive.exists_perm_hom W hn autE hautE
    hcenter hodd hWK hindex ψ P₂ eP
  have hinner := CyclicAlternatingFive.card_inner_involutions W σH hodd hWK hσsurj hσker hσK
  rw [hcin] at hinner
  have houter := CyclicAlternatingFive.card_outer_involutions W σH hodd hWK hinv hσsurj hσker
    hσK
  rw [hcout, mul_comm] at houter
  have hclass := CyclicAlternatingFive.isConj_involutions_iff W σH hodd hWK hinv hindex hσsurj
    hσker hσK hconjA hconjS
  have hcent := CyclicAlternatingFive.card_centralizer_mul W σH hodd hWK hinv hindex hσsurj
    hσker hσK hconjA hconjS
  have hcin0 : 0 < cin := by omega
  have hcout0 : 0 < cout := by
    rcases Nat.eq_zero_or_pos cout with h | h
    · rw [h, zero_mul] at hcoutc
      omega
    · exact h
  have hcentin : ∀ u ∈ Subgroup.centralizer (W : Set H), orderOf u = 2 →
      Nat.card (Subgroup.centralizer {u}) = 8 * Nat.card W := by
    intro u huK hu
    have h1 := hcent u hu
    have h2 : Nat.card {v : H // (v ∈ Subgroup.centralizer (W : Set H) ↔
        u ∈ Subgroup.centralizer (W : Set H)) ∧ orderOf v = 2} = cin := by
      rw [← hinner]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
        ⟨fun h => ⟨h.1.mpr huK, h.2⟩, fun h => ⟨iff_of_true h.1 huK, h.2⟩⟩)
    rw [h2, hHcard] at h1
    refine Nat.eq_of_mul_eq_mul_right hcin0 ?_
    rw [h1, ← hcin8]
    ring
  have hcentout : ∀ u : H, u ∉ Subgroup.centralizer (W : Set H) → orderOf u = 2 →
      Nat.card (Subgroup.centralizer {u}) = c := by
    intro u huK hu
    have h1 := hcent u hu
    have h2 : Nat.card {v : H // (v ∈ Subgroup.centralizer (W : Set H) ↔
        u ∈ Subgroup.centralizer (W : Set H)) ∧ orderOf v = 2} = cout * Nat.card W := by
      rw [← houter]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
        ⟨fun h => ⟨fun hv => huK (h.1.mp hv), h.2⟩, fun h => ⟨iff_of_false h.1 huK, h.2⟩⟩)
    rw [h2, hHcard] at h1
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hcout0 hWpos) ?_
    rw [h1, ← hcoutc]
    ring
  have hℓ2a : ¬ ℓ ∣ 2 * a := fun h => by
    rcases (Nat.Prime.dvd_mul hℓp).mp h with h2 | h2
    · have := Nat.le_of_dvd two_pos h2
      omega
    · exact hℓa h2
  have hPsyl : Nat.card P = ℓ ^ (Nat.card H).factorization ℓ := by
    rw [hPcard, hHcard, Nat.factorization_mul (by positivity) hWpos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hℓ2a, zero_add]
  obtain ⟨S, rfl⟩ : ∃ S : Sylow ℓ H, (S : Subgroup H) = P := ⟨Sylow.ofCard P hPsyl, rfl⟩
  have hSodd : Odd (Nat.card (S : Subgroup H)) := by
    rw [hPcard]
    exact (hℓp.odd_of_ne_two (by omega)).pow
  have hS1 : (S : Subgroup H) ≠ ⊥ := by
    intro h
    have h1 : Nat.card (S : Subgroup H) = 1 := by rw [h, Subgroup.card_bot]
    rw [hPcard] at h1
    have h2 : 1 ≤ (Nat.card W).factorization ℓ :=
      (hℓp.dvd_iff_one_le_factorization hWpos.ne').mp hℓm
    have h3 := Nat.one_lt_pow (by omega : (Nat.card W).factorization ℓ ≠ 0) hℓp.one_lt
    omega
  have hKP := centralizer_eq W S hPW hodd hinv hS1
  have : IsCyclic (S : Subgroup H) := Subgroup.isCyclic_of_le hPW
  obtain ⟨N, hNn, hcop, hpq⟩ := CyclicInversion.exists_centralizer_normal_complement S
  have hcomp := CyclicInversion.isComplement'_complement S N _ hPcard hcop hpq
  rw [← hKP] at hclass hinner houter hcentin hcentout hindex hinv hKn ⊢
  have hKnS : (Subgroup.centralizer (S : Set H)).Normal := hKn
  have hJK : N.map (Subgroup.centralizer (S : Set H)).subtype ≤
      Subgroup.centralizer (S : Set H) := Subgroup.map_subtype_le N
  have hchar := CyclicInversion.map_complement_characteristic S N hcop hpq
  have hJn : (N.map (Subgroup.centralizer (S : Set H)).subtype).Normal := by
    have h1 : ((N.map (Subgroup.centralizer (S : Set H)).subtype).subgroupOf
        (Subgroup.centralizer (S : Set H))).map (Subgroup.centralizer (S : Set H)).subtype =
          N.map (Subgroup.centralizer (S : Set H)).subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJK]
    rw [← h1]
    infer_instance
  set J := N.map (Subgroup.centralizer (S : Set H)).subtype with hJ
  have hQcop : Nat.Coprime ℓ (Nat.card Q) := by
    rw [Nat.Prime.coprime_iff_not_dvd hℓp]
    intro hdvd
    have h2 : ℓ ^ ((Nat.card W).factorization ℓ + 1) ∣
        Nat.card Q * ℓ ^ (Nat.card W).factorization ℓ := by
      rw [pow_succ, mul_comm (Nat.card Q)]
      exact mul_dvd_mul_left _ hdvd
    rw [hQcard] at h2
    exact Nat.pow_succ_factorization_not_dvd hWpos.ne' hℓp h2
  have hQJ : Q ≤ J := by
    intro q hq
    rw [CyclicInversion.mem_map_complement_iff S N hcop hpq]
    refine ⟨?_, Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Q hq) hQcop⟩
    have h1 : q ∈ Subgroup.centralizer ((S : Subgroup H) : Set H) := by
      rw [hKP]
      exact hWK (hQW hq)
    exact h1
  have hJmem : ∀ k : Subgroup.centralizer (S : Set H), (k : H) ∈ J → k ∈ N := by
    rintro k ⟨m, hm, hmk⟩
    rwa [← (Subtype.ext hmk : m = k)]
  have hπW : ∀ k : Subgroup.centralizer ((S : Subgroup H) : Set H),
      (k : H) ∈ (S : Subgroup H) → (CyclicInversion.complementProjection S N hcomp k : H) = k :=
    fun k hk => CyclicInversion.complementProjection_of_mem S N hcomp k hk
  have hπJ : ∀ k : Subgroup.centralizer ((S : Subgroup H) : Set H), (k : H) ∈ J →
      CyclicInversion.complementProjection S N hcomp k = 1 :=
    fun k hk => CyclicInversion.complementProjection_of_mem_complement S N hcomp k (hJmem k hk)
  have hdecomp : ∀ k : Subgroup.centralizer ((S : Subgroup H) : Set H),
      ((CyclicInversion.complementProjection S N hcomp k : (S : Subgroup H)) : H)⁻¹ * k ∈ J :=
    fun k => ⟨_, CyclicInversion.inv_inclusion_projection_mul_mem S N hcomp k, rfl⟩
  have hWK' : (S : Subgroup H) ≤ Subgroup.centralizer ((S : Subgroup H) : Set H) :=
    CyclicInversion.sylow_le_centralizer S
  have hinvS : ∀ h, h ∉ Subgroup.centralizer ((S : Subgroup H) : Set H) →
      ∀ p ∈ (S : Subgroup H), h * p * h⁻¹ = p⁻¹ := fun h hh p hp => hinv h hh p (hPW hp)
  refine ⟨J, CyclicInversion.complementProjection S N hcomp, hJK, hchar,
    by rw [CyclicInversion.card_map_complement]; exact hcop,
    CyclicInversion.sup_map_complement S N hcomp,
    CyclicInversion.inf_map_complement S N _ hPcard hcop hpq,
    fun p hp j hj => Subgroup.mem_centralizer_iff.mp (hJK hj) p hp, hQJ, hJn, hπW, hπJ, hclass,
    hinner, houter, hcentin, hcentout, ?_⟩
  intro lam hlam
  have hlam2 : lam ^ 2 ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hlam] at h1
    have := Nat.le_of_dvd two_pos h1
    omega
  obtain ⟨θμ, hθμ⟩ := CyclicSymmetricFour.exists_label_induced_linear (S : Subgroup H) J
    (CyclicInversion.complementProjection S N hcomp) basis hindex hWK' hJK hJn hinvS hπW hπJ
    hdecomp lam hlam2
  obtain ⟨θε, hθε⟩ := CyclicInversion.exists_label_of_linear basis
    (CyclicSymmetricFour.indexTwoSign _ hindex)
  have hT := CyclicSymmetricFour.column_apply (S : Subgroup H) J
    (CyclicInversion.complementProjection S N hcomp) hindex hWK' hJK hJn hinvS hπW hπJ hdecomp lam
  have hμ := CyclicSymmetricFour.induced_linear_apply (S : Subgroup H) J
    (CyclicInversion.complementProjection S N hcomp) hindex hWK' hJK hJn hinvS hπW hπJ hdecomp lam
  have hε : ∀ h : H, (basis.representation θε).character h =
      if h ∈ Subgroup.centralizer ((S : Subgroup H) : Set H) then 1 else -1 := by
    intro h
    rw [hθε h, CyclicSymmetricFour.indexTwoSign_apply]
  have hμt : ∀ t ∈ Subgroup.centralizer ((S : Subgroup H) : Set H), orderOf t = 2 →
      (basis.representation θμ).character t = 2 := by
    intro t ht htord
    have hπt : CyclicInversion.complementProjection S N hcomp ⟨t, ht⟩ = 1 := by
      apply Subtype.ext
      have ht2 : (⟨t, ht⟩ : Subgroup.centralizer ((S : Subgroup H) : Set H)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← htord]
        exact pow_orderOf_eq_one t
      have h1 : ((CyclicInversion.complementProjection S N hcomp ⟨t, ht⟩ :
          (S : Subgroup H)) : H) ^ 2 = 1 := by
        rw [← Subgroup.coe_pow, ← map_pow, ht2, map_one]
        rfl
      exact CyclicSymmetricFour.eq_one_of_sq_eq_one (S : Subgroup H) hSodd
        (CyclicInversion.complementProjection S N hcomp ⟨t, ht⟩).2 h1
    rw [hθμ, hμ t, dite_eq_left ht, hπt, inv_one, map_one, Units.val_one]
    norm_num
  have hμx : ∀ x : H, x ∉ Subgroup.centralizer ((S : Subgroup H) : Set H) →
      (basis.representation θμ).character x = 0 := by
    intro x hx
    rw [hθμ, hμ x, dite_eq_right hx]
  have hμ1 : (basis.representation θμ).character 1 = 2 := by
    rw [hθμ, hμ 1, dite_eq_left (Subgroup.one_mem _)]
    have h1 : CyclicInversion.complementProjection S N hcomp
        ⟨1, Subgroup.one_mem _⟩ = 1 := map_one _
    rw [h1, inv_one, map_one, Units.val_one]
    norm_num
  have hε1 : (basis.representation θε).character 1 = 1 := by
    rw [hε, ite_eq_left (Subgroup.one_mem _)]
  have hTfun : ∀ h : H, inducedFunction (Subgroup.centralizer ((S : Subgroup H) : Set H))
      (fun k => 1 - (lam (CyclicInversion.complementProjection S N hcomp k) : ℂ)) h =
        (basis.representation principal).character h + (basis.representation θε).character h -
          (basis.representation θμ).character h := by
    intro h
    rw [hT h, hθε h, hθμ, hprincipal, Pi.one_apply]
  refine ⟨θε, θμ, hε, ?_, fun h => by rw [hTfun h, hprincipal, Pi.one_apply], ?_⟩
  · have h1 : (basis.representation θμ).character 1 =
        Module.finrank ℂ (basis.representation θμ).vector := by
      rw [FiniteComplexRepresentation.character, Representation.char_one]
    rw [hμ1] at h1
    exact_mod_cast h1.symm
  intro t ht htord x hx hxord
  have hconjt : ∀ u, u ∈ Subgroup.centralizer ((S : Subgroup H) : Set H) → orderOf u = 2 →
      IsConj u t := fun u hu huo => (hclass u t huo htord).mpr (iff_of_true hu ht)
  have hconjx : ∀ u, u ∉ Subgroup.centralizer ((S : Subgroup H) : Set H) → orderOf u = 2 →
      IsConj u x := fun u hu huo => (hclass u x huo hxord).mpr (iff_of_false hu hx)
  have hm : (Nat.card W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hWpos.ne'
  have hc0 : (c : ℂ) ≠ 0 := by
    have : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hcoutc
        omega
      · exact h
    exact Nat.cast_ne_zero.mpr this.ne'
  have hcin8' : (cin : ℂ) * 8 = 2 * a := by exact_mod_cast hcin8
  have hcoutc' : (cout : ℂ) * c = 2 * a := by exact_mod_cast hcoutc
  have hcinne : (cin : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hcin0.ne'
  have hcoutne : (cout : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hcout0.ne'
  have havg : ∀ α : basis.index, (Nat.card H : ℂ)⁻¹ *
      ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2), (basis.representation α).character u =
        (basis.representation α).character t / (8 * (Nat.card W : ℂ)) +
          (basis.representation α).character x / c := by
    intro α
    rw [sum_involutions _ (basis.representation α).character
      (fun g c => Representation.char_conj _ g c) t x hconjt hconjx, hinner, houter, hHcard]
    push_cast
    have e1 : ((2 : ℂ) * a * Nat.card W)⁻¹ * (cin * (basis.representation α).character t) =
        (basis.representation α).character t / (8 * (Nat.card W : ℂ)) := by
      rw [show (2 : ℂ) * a * Nat.card W = cin * (8 * Nat.card W) by rw [← hcin8']; ring]
      field_simp
    have e2 : ((2 : ℂ) * a * Nat.card W)⁻¹ *
        (cout * Nat.card W * (basis.representation α).character x) =
          (basis.representation α).character x / c := by
      rw [show (2 : ℂ) * a * Nat.card W = cout * Nat.card W * c by rw [← hcoutc']; ring]
      field_simp
    rw [mul_add, e1, e2]
  have hsum : ∑ α : basis.index, characterPairing
      (inducedFunction (Subgroup.centralizer ((S : Subgroup H) : Set H))
        (fun k => 1 - (lam (CyclicInversion.complementProjection S N hcomp k) : ℂ)))
        (basis.representation α).character *
      ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
        (basis.representation α).character u) ^ 2 /
      (basis.representation α).character 1 = 2 / (c : ℂ) ^ 2 := by
    simp_rw [mul_div_assoc]
    rw [CyclicSymmetricFour.sum_pairing_three basis principal θε θμ _ hTfun, havg, havg, havg,
      hprincipal]
    simp only [Pi.one_apply]
    rw [hε t, ite_eq_left ht, hε x, ite_eq_right hx, hμt t ht htord, hμx x hx, hε1, hμ1]
    field_simp
    ring
  refine ⟨hμt t ht htord, hμx x hx, havg, hsum, ?_⟩
  rw [hsum, hHcard]
  push_cast
  field_simp
  ring

end Core

end CyclicColumnSum

open CyclicColumnSum

open scoped Classical in
theorem odd_cyclic_A4_A5_inversion_normalizer_principal_sylow_column_sum
    {H : Type u} [Group H] [Fintype H] (W : Subgroup H) [W.Normal] [IsCyclic W]
    (hodd : Odd (Nat.card W)) (d : ℕ) (hd : d = 4 ∨ d = 5)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hinv : ∀ h, h ∉ Subgroup.centralizer (W : Set H) → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
    (hquot : Nonempty (Subgroup.centralizer (W : Set H) ⧸
      W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃* alternatingGroup (Fin d)))
    (hdihedral : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hℓm : ℓ ∣ Nat.card W)
    (hℓd : ¬ ℓ ∣ Nat.card (alternatingGroup (Fin d)))
    (P Q : Subgroup H) (hPW : P ≤ W) (hPcard : Nat.card P = ℓ ^ (Nat.card W).factorization ℓ)
    (hQW : Q ≤ W) (hQcard : Nat.card Q * ℓ ^ (Nat.card W).factorization ℓ = Nat.card W)
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ (J : Subgroup H) (π : Subgroup.centralizer (W : Set H) →* P),
      J ≤ Subgroup.centralizer (W : Set H) ∧
      (J.subgroupOf (Subgroup.centralizer (W : Set H))).Characteristic ∧
      Nat.Coprime ℓ (Nat.card J) ∧ P ⊔ J = Subgroup.centralizer (W : Set H) ∧ P ⊓ J = ⊥ ∧
      (∀ p ∈ P, ∀ j ∈ J, p * j = j * p) ∧ Q ≤ J ∧ J.Normal ∧
      (∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ P → (π k : H) = k) ∧
      (∀ k : Subgroup.centralizer (W : Set H), (k : H) ∈ J → π k = 1) ∧
      (∀ u v : H, orderOf u = 2 → orderOf v = 2 →
        (IsConj u v ↔ (u ∈ Subgroup.centralizer (W : Set H) ↔
          v ∈ Subgroup.centralizer (W : Set H)))) ∧
      Nat.card {u : H // u ∈ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} =
        (if d = 4 then 3 else 15) ∧
      Nat.card {u : H // u ∉ Subgroup.centralizer (W : Set H) ∧ orderOf u = 2} =
        (if d = 4 then 6 else 10) * Nat.card W ∧
      (∀ u ∈ Subgroup.centralizer (W : Set H), orderOf u = 2 →
        Nat.card (Subgroup.centralizer {u}) = 8 * Nat.card W) ∧
      (∀ u : H, u ∉ Subgroup.centralizer (W : Set H) → orderOf u = 2 →
        Nat.card (Subgroup.centralizer {u}) = if d = 4 then 4 else 12) ∧
      ∀ lam : P →* ℂˣ, orderOf lam = ℓ →
        ∃ θε θμ : basis.index,
          (∀ h : H, (basis.representation θε).character h =
            if h ∈ Subgroup.centralizer (W : Set H) then 1 else -1) ∧
          Module.finrank ℂ (basis.representation θμ).vector = 2 ∧
          (∀ h : H, inducedFunction (Subgroup.centralizer (W : Set H))
              (fun k => 1 - (lam (π k) : ℂ)) h =
            1 + (basis.representation θε).character h - (basis.representation θμ).character h) ∧
          ∀ t ∈ Subgroup.centralizer (W : Set H), orderOf t = 2 →
            ∀ x : H, x ∉ Subgroup.centralizer (W : Set H) → orderOf x = 2 →
            (basis.representation θμ).character t = 2 ∧
            (basis.representation θμ).character x = 0 ∧
            (∀ α : basis.index, (Nat.card H : ℂ)⁻¹ *
                ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u =
              (basis.representation α).character t / (8 * (Nat.card W : ℂ)) +
                (basis.representation α).character x / ((if d = 4 then 4 else 12 : ℕ) : ℂ)) ∧
            ∑ α : basis.index, characterPairing
                (inducedFunction (Subgroup.centralizer (W : Set H))
                  (fun k => 1 - (lam (π k) : ℂ))) (basis.representation α).character *
                ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u) ^ 2 /
                (basis.representation α).character 1 =
              2 / ((if d = 4 then 4 else 12 : ℕ) : ℂ) ^ 2 ∧
            (Nat.card H : ℂ) * ∑ α : basis.index, characterPairing
                (inducedFunction (Subgroup.centralizer (W : Set H))
                  (fun k => 1 - (lam (π k) : ℂ))) (basis.representation α).character *
                ((Nat.card H : ℂ)⁻¹ * ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2),
                  (basis.representation α).character u) ^ 2 /
                (basis.representation α).character 1 =
              if d = 4 then 3 * (Nat.card W : ℂ) else 5 * (Nat.card W : ℂ) / 3 := by
  obtain ⟨ψ⟩ := hquot
  obtain ⟨P₂, ⟨eP⟩⟩ := hdihedral
  rcases hd with rfl | rfl
  · have ha : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    obtain ⟨J, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ :=
      column_sum_core W hodd (by norm_num) CyclicSymmetricFour.autEquiv
        CyclicSymmetricFour.autEquiv_apply CyclicSymmetricFour.alternating_eq_one_of_forall_commute
        CyclicSymmetricFour.alternating_involution_conj CyclicSymmetricFour.odd_involution_conj
        12 3 6 4 ha CyclicSymmetricFour.nat_card_alternating_involutions
        CyclicSymmetricFour.nat_card_odd_involutions (by norm_num) (by norm_num) hindex hinv ψ P₂
        eP ℓ hℓ hℓm (ha ▸ hℓd) P Q hPW hPcard hQW hQcard basis principal hprincipal
    refine ⟨J, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      fun lam hlam => ?_⟩
    obtain ⟨θε, θμ, g1, g2, g3, g4⟩ := h16 lam hlam
    refine ⟨θε, θμ, g1, g2, g3, fun t ht htord x hx hxord => ?_⟩
    obtain ⟨k1, k2, k3, k4, k5⟩ := g4 t ht htord x hx hxord
    refine ⟨k1, k2, k3, k4, ?_⟩
    rw [k5]
    push_cast
    norm_num
    ring
  · have ha : Nat.card (alternatingGroup (Fin 5)) = 60 :=
      CyclicAlternatingFive.nat_card_alternating
    obtain ⟨J, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ :=
      column_sum_core W hodd (by norm_num) CyclicAlternatingFive.autEquiv
        CyclicAlternatingFive.autEquiv_apply
        CyclicAlternatingFive.alternating_eq_one_of_forall_commute
        CyclicAlternatingFive.alternating_involution_conj
        CyclicAlternatingFive.odd_involution_conj
        60 15 10 12 ha CyclicAlternatingFive.nat_card_alternating_involutions
        CyclicAlternatingFive.nat_card_odd_involutions (by norm_num) (by norm_num) hindex hinv ψ P₂
        eP ℓ hℓ hℓm (ha ▸ hℓd) P Q hPW hPcard hQW hQcard basis principal hprincipal
    refine ⟨J, π, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      fun lam hlam => ?_⟩
    obtain ⟨θε, θμ, g1, g2, g3, g4⟩ := h16 lam hlam
    refine ⟨θε, θμ, g1, g2, g3, fun t ht htord x hx hxord => ?_⟩
    obtain ⟨k1, k2, k3, k4, k5⟩ := g4 t ht htord x hx hxord
    refine ⟨k1, k2, k3, k4, ?_⟩
    rw [k5]
    push_cast
    norm_num
    ring

end CFSG.Semidihedral.Principal
