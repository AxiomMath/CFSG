module

public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.GroupTheory.SylowLiftSurjective

public section

namespace CFSG.GroupTheory

open CFSG.RankThree.CentralCover CFSG.RankThree.Classical2

variable {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem comap_closure_comm_of_inverters (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {S : Set T}
    (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hinv : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (∃ g : T, g * s * g⁻¹ = s⁻¹ ∧ g * t * g⁻¹ = t) ∨
        (∃ g : T, g * t * g⁻¹ = t⁻¹ ∧ g * s * g⁻¹ = s)) :
    ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ, x * y = y * x := by
  refine comap_closure_comm hφ hker hS ?_
  rintro s hs t ht
  by_cases hst : s = t
  · subst hst
    exact liftComm_self hφ s
  · rcases hinv s hs t ht hst with ⟨g, hgs, hgt⟩ | ⟨g, hgt, hgs⟩
    · exact liftComm_eq_one_of_conj_inv hφ hker (hodd s hs) (hS s hs t ht)
        (pow_orderOf_eq_one s) g hgs hgt
    · have h1 : liftComm φ hφ t s = 1 :=
        liftComm_eq_one_of_conj_inv hφ hker (hodd t ht) (hS t ht s hs)
          (pow_orderOf_eq_one t) g hgt hgs
      have h2 := liftComm_swap hφ s t
      rw [h1] at h2
      exact inv_eq_one.mp h2.symm

theorem isMulCommutative_sylow_of_comap_comm [Finite Y] {r : ℕ} [Fact r.Prime]
    (hφ : Function.Surjective φ)
    (D : Sylow r T) (hD : ∀ x ∈ (D : Subgroup T).comap φ, ∀ y ∈ (D : Subgroup T).comap φ,
      x * y = y * x) (P : Sylow r Y) : IsMulCommutative (P : Subgroup Y) := by
  classical
  haveI : Finite T := Finite.of_surjective φ hφ
  obtain ⟨Tstar, hTp, hidx, hle⟩ :=
    exists_isPGroup_not_dvd_index_map_le φ hφ Fact.out (T := (D : Subgroup T)) D.not_dvd_index
  have hTle : Tstar ≤ (D : Subgroup T).comap φ := Subgroup.map_le_iff_le_comap.mp hle
  have hTcomm : IsMulCommutative (Tstar : Subgroup Y) :=
    ⟨⟨fun a b => Subtype.ext (hD a.1 (hTle a.2) b.1 (hTle b.2))⟩⟩
  let Q : Sylow r Y := hTp.toSylow hidx
  have hQ : (Q : Subgroup Y) = Tstar := IsPGroup.toSylow_coe hTp hidx
  haveI : IsMulCommutative (Q : Subgroup Y) := by rw [hQ]; exact hTcomm
  refine ⟨⟨fun a b => (Sylow.equiv Q P).symm.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact IsMulCommutative.is_comm.comm _ _

theorem exists_elemAbelian_le_pRank_centralizer_of_comap_comm [Finite Y]
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {r p a b : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) {D E : Subgroup T}
    (hDr : ∀ x ∈ D, x ^ r = 1)
    (hEp : ∀ x ∈ E, x ^ p = 1)
    (hc : ∀ x ∈ (D ⊔ E).comap φ, ∀ y ∈ (D ⊔ E).comap φ, x * y = y * x)
    (ha : r ^ a ≤ Nat.card D) (hb : p ^ b ≤ Nat.card E) :
    ∃ A : Subgroup Y, CFSG.Open.IsElemAbelian r A ∧ Nat.card A = r ^ a ∧
      b ≤ CFSG.Open.pRank p (⊤ : Subgroup (Subgroup.centralizer (A : Set Y))) := by
  classical
  have hDcomm : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x :=
    fun x hx y hy => hc x (Subgroup.comap_mono le_sup_left hx) y
      (Subgroup.comap_mono le_sup_left hy)
  have hEcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x :=
    fun x hx y hy => hc x (Subgroup.comap_mono le_sup_right hx) y
      (Subgroup.comap_mono le_sup_right hy)
  obtain ⟨A, hAD, hAab, hAcard, -⟩ := exists_elemAbelian_le_centralizer (p := r) hφ hker hr hr2
    hDr hDcomm ha (u := 1) (one_pow 2) (fun x _ => by rw [map_one]; exact Commute.one_left x)
  obtain ⟨B, hBE, hBab, hBcard, -⟩ := exists_elemAbelian_le_centralizer (p := p) hφ hker hp hp2
    hEp hEcomm hb (u := 1) (one_pow 2) (fun x _ => by rw [map_one]; exact Commute.one_left x)
  have hBA : B ≤ Subgroup.centralizer (A : Set Y) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hc x (Subgroup.comap_mono le_sup_left (hAD hx)) b
      (Subgroup.comap_mono le_sup_right (hBE hb))
  refine ⟨A, hAab, hAcard, ?_⟩
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := B) ?_ ?_ hBcard
    (Subgroup.inclusion hBA) (Subgroup.inclusion_injective hBA) le_top
  · intro x y
    exact hBab.1.is_comm.comm x y
  · intro x
    exact Subtype.ext (hBab.2 x x.2)

section Sylow

theorem not_dvd_index_map_comap_sylow_two [Finite Y] [Finite T] (hφ : Function.Surjective φ)
    {U : Subgroup T} (hU : ¬ 2 ∣ U.index) (P : Sylow 2 (U.comap φ)) :
    ¬ 2 ∣ ((P : Subgroup (U.comap φ)).map (U.comap φ).subtype).index := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPcard : Nat.card (P : Subgroup (U.comap φ)) =
      2 ^ (Nat.card (U.comap φ)).factorization 2 := Sylow.card_eq_multiplicity P
  have hRcard : Nat.card ((P : Subgroup (U.comap φ)).map (U.comap φ).subtype) =
      Nat.card (P : Subgroup (U.comap φ)) :=
    Subgroup.card_map_of_injective (U.comap φ).subtype_injective
  have hidx : (U.comap φ).index = U.index := Subgroup.index_comap_of_surjective U hφ
  have hYcard : Nat.card Y = Nat.card (U.comap φ) * (U.comap φ).index :=
    (Subgroup.card_mul_index (U.comap φ)).symm
  have hfac : (Nat.card Y).factorization 2 = (Nat.card (U.comap φ)).factorization 2 := by
    rw [hYcard, Nat.factorization_mul (Nat.card_pos.ne') (Subgroup.index_ne_zero_of_finite),
      Finsupp.add_apply, hidx, Nat.factorization_eq_zero_of_not_dvd hU, add_zero]
  have hcard : Nat.card ((P : Subgroup (U.comap φ)).map (U.comap φ).subtype) =
      2 ^ (Nat.card Y).factorization 2 := by rw [hRcard, hPcard, hfac]
  have hQidx :=
    (Sylow.ofCard ((P : Subgroup (U.comap φ)).map (U.comap φ).subtype) hcard).not_dvd_index
  rwa [Sylow.coe_ofCard] at hQidx

end Sylow

end CFSG.GroupTheory
