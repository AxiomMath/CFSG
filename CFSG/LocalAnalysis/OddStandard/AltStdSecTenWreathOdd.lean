module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathRigid
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathNorm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

theorem exists_inner_of_odd_order {J : Subgroup X} (eJ : J ≃* alternatingGroup (Fin 8)) {g : X}
    (hg : g ∈ normalizer (J : Set X)) (hodd : Odd (orderOf g)) :
    ∃ k ∈ J, ∀ y ∈ J, g * y * g⁻¹ = k * y * k⁻¹ := by
  let g' : normalizer (J : Set X) := ⟨g, hg⟩
  set a : Equiv.Perm (Fin 8) := AltStdBal.rho eJ (le_refl 8) g' with ha_def
  have hdiv : orderOf a ∣ orderOf g := by
    have h1 : orderOf a ∣ orderOf g' := orderOf_map_dvd (AltStdBal.rho eJ (le_refl 8)) g'
    simpa [g'] using h1
  have hodd_a : Odd (orderOf a) := Odd.of_dvd_nat hodd hdiv
  have hsign : Equiv.Perm.sign a = 1 := by
    have h2 : orderOf (Equiv.Perm.sign a) ∣ orderOf a := orderOf_map_dvd Equiv.Perm.sign a
    have hodd' : Odd (orderOf (Equiv.Perm.sign a)) := Odd.of_dvd_nat hodd_a h2
    have hsq : (Equiv.Perm.sign a) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign a) with h | h <;> rw [h] <;> simp
    have h3 : orderOf (Equiv.Perm.sign a) ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 hsq
    obtain ⟨l, hl⟩ := hodd'
    have hle : orderOf (Equiv.Perm.sign a) ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    exact orderOf_eq_one_iff.1 (by omega)
  have ha : a ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.2 hsign
  set k : J := eJ.symm ⟨a, ha⟩ with hk_def
  refine ⟨(k : X), k.2, ?_⟩
  have hkJ : (k : X) ∈ normalizer (J : Set X) := Subgroup.le_normalizer k.2
  have hrho_k : AltStdBal.rho eJ (le_refl 8) (⟨(k : X), hkJ⟩ : normalizer (J : Set X)) = a := by
    rw [AltStdBal.rho_of_mem eJ (le_refl 8) k hkJ, hk_def]
    simp
  have hcent : g * (k : X)⁻¹ ∈ centralizer (J : Set X) := by
    have h1 : AltStdBal.rho eJ (le_refl 8)
        (g' * (⟨(k : X), hkJ⟩ : normalizer (J : Set X))⁻¹) = 1 := by
      rw [map_mul, map_inv, hrho_k]
      show a * a⁻¹ = 1
      group
    have h2 := (AltStdBal.rho_eq_one_iff eJ (le_refl 8) _).1 h1
    simpa [g'] using h2
  intro y hy
  have hz : (k : X) * y * (k : X)⁻¹ ∈ J := mul_mem (mul_mem k.2 hy) (inv_mem k.2)
  have hcz : (g * (k : X)⁻¹) * ((k : X) * y * (k : X)⁻¹) * (g * (k : X)⁻¹)⁻¹
      = (k : X) * y * (k : X)⁻¹ := by
    rw [← mem_centralizer_iff.1 hcent _ hz]
    group
  calc g * y * g⁻¹
      = (g * (k : X)⁻¹) * ((k : X) * y * (k : X)⁻¹) * (g * (k : X)⁻¹)⁻¹ := by group
    _ = (k : X) * y * (k : X)⁻¹ := hcz

theorem WreathK.mem_layer_of_odd (hE : ExactShape t A 8) (hK : WreathK t A K)
    (hO : CFSG.oddCore X = ⊥) {g : X} (hg : Odd (orderOf g)) : g ∈ CFSG.layer X := by
  have ht : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hE.order, pow_two] at h
    exact h
  have hgN : g ∈ normalizer (K : Set X) :=
    mem_of_odd_of_index_two (hK.index_normalizer ht) hg
  obtain ⟨k, hk, hk_act⟩ := exists_inner_of_odd_order hK.iso.some hgN hg
  have hgN' : g ∈ normalizer (conjSub t K : Set X) := hK.mem_normalizer_conjSub hgN
  have eK' : conjSub t K ≃* alternatingGroup (Fin 8) :=
    (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans
      hK.iso.some
  obtain ⟨k', hk', hk'_act⟩ := exists_inner_of_odd_order eK' hgN' hg
  set h : X := (k * k')⁻¹ * g with hh_def
  have hcentK : h ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hcy : y * k' = k' * y := hK.commute hy hk'
    have hconj : h * y * h⁻¹ = y := by
      calc h * y * h⁻¹ = (k * k')⁻¹ * (g * y * g⁻¹) * (k * k') := by
            rw [hh_def]; group
        _ = (k * k')⁻¹ * (k * y * k⁻¹) * (k * k') := by rw [hk_act y hy]
        _ = k'⁻¹ * y * k' := by rw [mul_inv_rev]; group
        _ = y := by
            calc k'⁻¹ * y * k' = k'⁻¹ * (y * k') := by group
              _ = k'⁻¹ * (k' * y) := by rw [hcy]
              _ = y := by group
    have hhy : h * y = y * h := by
      have h1 : (h * y) * h⁻¹ = (y * h) * h⁻¹ := by rw [hconj]; group
      exact mul_right_cancel h1
    exact hhy.symm
  have hcentK' : h ∈ centralizer (conjSub t K : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have hcy : k * y = y * k := hK.commute hk hy
    have hcomm : k * k' = k' * k := hK.commute hk hk'
    have hconj : h * y * h⁻¹ = y := by
      calc h * y * h⁻¹ = (k * k')⁻¹ * (g * y * g⁻¹) * (k * k') := by
            rw [hh_def]; group
        _ = (k * k')⁻¹ * (k' * y * k'⁻¹) * (k * k') := by rw [hk'_act y hy]
        _ = k⁻¹ * y * k := by rw [hcomm, mul_inv_rev]; group
        _ = y := by
            calc k⁻¹ * y * k = k⁻¹ * (y * k) := by group
              _ = k⁻¹ * (k * y) := by rw [← hcy]
              _ = y := by group
    have hhy : h * y = y * h := by
      have h1 : (h * y) * h⁻¹ = (y * h) * h⁻¹ := by rw [hconj]; group
      exact mul_right_cancel h1
    exact hhy.symm
  have hcent : h ∈ centralizer (((K ⊔ conjSub t K : Subgroup X)) : Set X) := by
    have hKW : K ≤ centralizer ({h} : Set X) := by
      intro y hy
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hcentK y hy
    have hK'W : conjSub t K ≤ centralizer ({h} : Set X) := by
      intro y hy
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hcentK' y hy
    have hsupW : (K ⊔ conjSub t K : Subgroup X) ≤ centralizer ({h} : Set X) :=
      sup_le hKW hK'W
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (hsupW hy)
  rw [← hK.layer] at hcent
  rw [WreathK.centralizer_layer_eq_bot hE hK hO] at hcent
  have hh : h = 1 := Subgroup.mem_bot.1 hcent
  have hg_eq : g = k * k' := by
    have hthis : (k * k')⁻¹ * g = 1 := by rw [← hh_def]; exact hh
    calc g = (k * k') * ((k * k')⁻¹ * g) := by group
      _ = (k * k') * 1 := by rw [hthis]
      _ = k * k' := by rw [mul_one]
  rw [hK.layer, hg_eq]
  exact mul_mem (le_sup_left (a := K) hk) (le_sup_right (b := conjSub t K) hk')

theorem WreathK.exists_card_centralizer_eq (hE : ExactShape t A 8) (hK : WreathK t A K)
    (hO : CFSG.oddCore X = ⊥) (s : X) :
    ∃ j : ℕ, Nat.card ↥(centralizer ({s} : Set X)) =
      Nat.card ↥(CFSG.layer X ⊓ centralizer ({s} : Set X)) * 2 ^ j := by
  let E : Subgroup X := CFSG.layer X
  let C : Subgroup X := centralizer ({s} : Set X)
  haveI hEchar : E.Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : Finite (X ⧸ E) :=
    Finite.of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
  have hindex : ∃ b : ℕ, E.index = 2 ^ b := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hquot : IsPGroup 2 (X ⧸ E) := by
      rw [isPGroup_iff_orderOf_dvd_pow]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E q
      have hg0 : orderOf g ≠ 0 := orderOf_ne_zero_iff.2 (isOfFinOrder_of_finite g)
      obtain ⟨a, m, hm, hg_eq⟩ := Nat.exists_eq_two_pow_mul_odd hg0
      refine ⟨a, ?_⟩
      have hne : 0 < 2 ^ a := pow_pos (by norm_num) a
      have hpow : orderOf (g ^ (2 ^ a)) = m := by
        rw [orderOf_pow_of_dvd (Nat.pos_iff_ne_zero.1 hne) ⟨m, by rw [hg_eq]⟩, hg_eq,
          Nat.mul_div_cancel_left m hne]
      have hmem : g ^ (2 ^ a) ∈ E :=
        WreathK.mem_layer_of_odd hE hK hO (by rw [hpow]; exact hm)
      have h1 : QuotientGroup.mk' E (g ^ (2 ^ a)) = 1 := by
        have hker : g ^ (2 ^ a) ∈ (QuotientGroup.mk' E).ker := by
          rwa [QuotientGroup.ker_mk']
        exact MonoidHom.mem_ker.1 hker
      exact orderOf_dvd_iff_pow_eq_one.2 (by rw [← map_pow, h1])
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := X ⧸ E)).1 hquot
    exact ⟨n, by rw [Subgroup.index_eq_card, hn]⟩
  obtain ⟨b, hb⟩ := hindex
  have hdvd : E.relIndex C ∣ E.index :=
    Subgroup.relIndex_dvd_index_of_normal (H := E) (K := C)
  rw [hb] at hdvd
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨j, ?_⟩
  have hcard := Subgroup.relIndex_mul_card (H := E) (K := C)
  rw [hj] at hcard
  rw [mul_comm] at hcard
  exact hcard.symm

end CFSG.OddStandard.AltStdSec.SwapPattern
