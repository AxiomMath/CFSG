module

public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import CFSG.GH74.GLS.Stage1.Thm4.Pure
import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

open Subgroup CFSG

class CentralInv {X : Type} [Group X] (x : X) : Prop where
  comm : ∀ g : X, g * x = x * g
  sq : x * x = 1
  ne : x ≠ 1

section CI

variable {X : Type} [Group X] {x : X}

theorem CentralInv.mem_center [h : CentralInv x] : x ∈ center X :=
  Subgroup.mem_center_iff.2 h.comm

instance centralInv_normal [h : CentralInv x] : (zpowers x).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g x := h.comm g
    have : g * x ^ k * g⁻¹ = x ^ k := by
      rw [(hc.zpow_right k).eq]; group
    rw [this]; exact Subgroup.zpow_mem_zpowers x k⟩

theorem CentralInv.orderOf_eq [h : CentralInv x] : orderOf x = 2 :=
  orderOf_eq_prime (by simpa [pow_two] using h.sq) h.ne

theorem CentralInv.mem_zpowers [h : CentralInv x] {s : X} (hs : s ∈ zpowers x) : s = 1 ∨ s = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  have h2 : orderOf x = 2 := h.orderOf_eq
  have hk : x ^ k = x ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h2]; rfl
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [hk, h0]; simp
  · right; rw [hk, h1]; simp

theorem CentralInv.isPGroup [h : CentralInv x] : IsPGroup 2 (zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_eq]; norm_num)

end CI

section Quot

variable {X : Type} [Group X] [Finite X]

abbrev Qx (x : X) [CentralInv x] : Type := X ⧸ zpowers x

abbrev Qh (x : X) [CentralInv x] : Type := Qx x ⧸ pPrimeCore 2 (Qx x)

@[expose] def piH (x : X) [CentralInv x] : X →* Qh x :=
  (QuotientGroup.mk' (pPrimeCore 2 (Qx x))).comp (QuotientGroup.mk' (zpowers x))

omit [Finite X] in
theorem piH_surjective (x : X) [CentralInv x] : Function.Surjective (piH x) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem pPrimeCore_Qx (x : X) [h : CentralInv x] :
    pPrimeCore 2 (Qx x) = (pPrimeCore 2 X).map (QuotientGroup.mk' (zpowers x)) :=
  central_p_subgroup_prime_core_quotient (zpowers x)
    (Subgroup.zpowers_le.2 h.mem_center) h.isPGroup

theorem ker_piH (x : X) [CentralInv x] :
    (piH x).ker = pPrimeCore 2 X ⊔ zpowers x := by
  have h1 : (piH x).ker = (pPrimeCore 2 (Qx x)).comap (QuotientGroup.mk' (zpowers x)) := by
    rw [piH, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [h1, pPrimeCore_Qx, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem odd_card_pPrimeCore (Y : Type) [Group Y] [Finite Y] : Odd (Nat.card (pPrimeCore 2 Y)) :=
  (Nat.coprime_two_left).1 (pPrimeCore_coprime_card (p := 2) (G := Y))

theorem two_elt_mem_zpowers (x : X) [h : CentralInv x] {g : X}
    (hg : g ∈ pPrimeCore 2 X ⊔ zpowers x) {m : ℕ} (hgm : g ^ (2 ^ m) = 1) : g ∈ zpowers x := by
  obtain ⟨o, ho, s, hs, hos⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  rw [← hos] at hgm ⊢
  have hm : (o * s) ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, hgm, one_pow]
  have hcx : Commute o x := h.comm o
  have hcomm : Commute o s := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact hcx.zpow_right k
  have key : ∀ {o' : X}, o' ∈ pPrimeCore 2 X → o' ^ (2 ^ (m + 1)) = 1 → o' = 1 := by
    intro o' ho' h'
    have h1 : (⟨o', ho'⟩ : pPrimeCore 2 X) ^ (2 ^ (m + 1)) = 1 := Subtype.ext (by simpa using h')
    exact congrArg Subtype.val (Stage1.Thm4.eq_one_of_pow_two_pow_of_odd (odd_card_pPrimeCore X) h1)
  rcases h.mem_zpowers hs with hs1 | hs1
  · rw [hs1] at hm ⊢
    have := key ho (by simpa using hm)
    rw [this]; simp
  · rw [hs1] at hm hcomm ⊢
    have hxx : x ^ (2 ^ (m + 1)) = 1 := by
      rw [pow_succ', pow_mul, pow_two, h.sq, one_pow]
    have h2 : o ^ (2 ^ (m + 1)) = 1 := by
      rw [hcomm.mul_pow, hxx, mul_one] at hm
      exact hm
    have := key ho h2
    rw [this, one_mul]; exact Subgroup.mem_zpowers x

omit [Finite X] in
theorem orderOf_conj_eq {u : X} (c : X) : orderOf (c * u * c⁻¹) = orderOf u := by
  have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective u
  simpa using this

theorem conj_lift (x : X) [h : CentralInv x] {u v : X} (hu : orderOf u = 2) (hv : orderOf v = 2)
    {c : X} (hc : piH x (c * u * c⁻¹) = piH x v) : IsConj u v ∨ IsConj (u * x) v := by
  have hker : v⁻¹ * (c * u * c⁻¹) ∈ (piH x).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hc, inv_mul_cancel]
  rw [ker_piH] at hker
  obtain ⟨o, ho, s, hs, hos⟩ := Subgroup.mem_sup_of_normal_left.1 hker
  have hcu : orderOf (c * u * c⁻¹) = 2 := by rw [orderOf_conj_eq, hu]
  have hodd := odd_card_pPrimeCore X
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  rcases h.mem_zpowers hs with hs1 | hs1
  · left
    rw [hs1, mul_one] at hos
    have hmem : (c * u * c⁻¹)⁻¹ * v ∈ pPrimeCore 2 X := by
      have : (c * u * c⁻¹)⁻¹ * v = o⁻¹ := by rw [hos]; group
      rw [this]; exact Subgroup.inv_mem _ ho
    have h1 : IsConj (c * u * c⁻¹) v :=
      Stage1.Thm4.isConj_of_mem_coset (N := pPrimeCore 2 X) hodd hcu hv hmem
    exact (isConj_iff.2 ⟨c, rfl⟩ : IsConj u (c * u * c⁻¹)).trans h1
  · right
    rw [hs1] at hos
    have hcx : ∀ g : X, g * x = x * g := h.comm
    have hux : u * x ≠ 1 := by
      intro h1
      have hux' : u = x := by
        have : u = x⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]; exact inv_eq_of_mul_eq_one_right h.sq
      have hw : c * u * c⁻¹ = x := by
        rw [hux']
        calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [h.comm c]
          _ = x := by group
      rw [hw] at hos
      have hvo : v⁻¹ = o := by
        have : v⁻¹ * x = o * x := hos.symm
        exact mul_right_cancel this
      have : v ∈ pPrimeCore 2 X := by
        rw [← inv_inv v, hvo]; exact Subgroup.inv_mem _ ho
      have hd : orderOf v ∣ Nat.card (pPrimeCore 2 X) := by
        have := orderOf_dvd_natCard (⟨v, this⟩ : pPrimeCore 2 X)
        rwa [Subgroup.orderOf_mk] at this
      rw [hv] at hd
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd)
    have hux2 : (u * x) ^ 2 = 1 := by
      rw [(show Commute u x from h.comm u).mul_pow, hu2, pow_two x, h.sq, one_mul]
    have hord : orderOf (u * x) = 2 := orderOf_eq_prime hux2 hux
    have hw' : c * (u * x) * c⁻¹ = (c * u * c⁻¹) * x := by
      calc c * (u * x) * c⁻¹ = c * u * (x * c⁻¹) := by group
        _ = c * u * (c⁻¹ * x) := by rw [← h.comm c⁻¹]
        _ = (c * u * c⁻¹) * x := by group
    have hcw : orderOf (c * (u * x) * c⁻¹) = 2 := by rw [orderOf_conj_eq, hord]
    have hmem : (c * (u * x) * c⁻¹)⁻¹ * v ∈ pPrimeCore 2 X := by
      have : (c * (u * x) * c⁻¹)⁻¹ * v = o⁻¹ := by
        rw [hw']
        have : v⁻¹ * (c * u * c⁻¹) = o * x := hos.symm
        have h3 : (c * u * c⁻¹) = v * (o * x) := by
          calc c * u * c⁻¹ = v * (v⁻¹ * (c * u * c⁻¹)) := by group
            _ = v * (o * x) := by rw [this]
        rw [h3]
        have hx2 : x * x = 1 := h.sq
        calc ((v * (o * x)) * x)⁻¹ * v = (v * o * (x * x))⁻¹ * v := by group
          _ = o⁻¹ := by rw [hx2]; group
      rw [this]; exact Subgroup.inv_mem _ ho
    have h1 : IsConj (c * (u * x) * c⁻¹) v :=
      Stage1.Thm4.isConj_of_mem_coset (N := pPrimeCore 2 X) hodd hcw hv hmem
    exact (isConj_iff.2 ⟨c, rfl⟩ : IsConj (u * x) (c * (u * x) * c⁻¹)).trans h1

theorem exists_normal_complement (x : X) [h : CentralInv x] (T : Sylow 2 X) {D : Subgroup X}
    (hD : D ≤ T) (hdisj : zpowers x ⊓ D = ⊥) (hsup : zpowers x ⊔ D = T) :
    ∃ K : Subgroup X, K.Normal ∧ zpowers x ⊓ K = ⊥ ∧ zpowers x ⊔ K = ⊤ ∧ commutator X ≤ K := by
  obtain ⟨K, hK1, hK2⟩ := (Quasithin.gaschutz h.isPGroup T).2 ⟨D, hD, hdisj, hsup⟩
  have hcen : ∀ y ∈ zpowers x, ∀ a : X, a * y = y * a := fun y hy =>
    Subgroup.mem_center_iff.1 ((Subgroup.zpowers_le.2 h.mem_center) hy)
  have hnorm : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    have hg : g ∈ zpowers x ⊔ K := by rw [hK2]; exact Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    have : y * z * k * (y * z)⁻¹ = z * k * z⁻¹ := by
      have h1 := hcen y hy
      calc y * z * k * (y * z)⁻¹ = y * (z * k * z⁻¹) * y⁻¹ := by group
        _ = (z * k * z⁻¹) * y * y⁻¹ := by rw [← h1 (z * k * z⁻¹)]
        _ = z * k * z⁻¹ := by group
    rw [this]
    exact K.mul_mem (K.mul_mem hz hk) (K.inv_mem hz)
  refine ⟨K, hnorm, hK1, hK2, ?_⟩
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := K) (H := zpowers x)
    (by rw [sup_comm]; exact hK2) inferInstance

theorem x_not_mem_commutator (x : X) [h : CentralInv x] (T : Sylow 2 X) {D : Subgroup X}
    (hD : D ≤ T) (hdisj : zpowers x ⊓ D = ⊥) (hsup : zpowers x ⊔ D = T) : x ∉ commutator X := by
  obtain ⟨K, -, hK1, -, hcomm⟩ := exists_normal_complement x T hD hdisj hsup
  intro hx
  have : x ∈ zpowers x ⊓ K := ⟨Subgroup.mem_zpowers x, hcomm hx⟩
  rw [hK1] at this
  exact h.ne ((Subgroup.mem_bot).1 this)

end Quot

section Dih

variable {X : Type} [Group X] [Finite X] (x : X) [CentralInv x]

structure DihData (ψ : DihedralGroup 4 →* X) (T : Sylow 2 X) : Prop where
  inj : Function.Injective ψ
  sup : (T : Subgroup X) = zpowers x ⊔ ψ.range
  disj : zpowers x ⊓ ψ.range = ⊥

variable {x} {ψ : DihedralGroup 4 →* X} {T : Sylow 2 X}

theorem DihData.psi_mem_R (hD : DihData x ψ T) {g : DihedralGroup 4}
    (hg : ψ g ∈ pPrimeCore 2 X ⊔ zpowers x) : g = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, g ^ (2 ^ m) = 1 := ⟨3, by
    have : orderOf g ∣ 2 ^ 3 := by
      have h1 : orderOf g ∣ Nat.card (DihedralGroup 4) := orderOf_dvd_natCard g
      rw [DihedralGroup.nat_card] at h1
      simpa using h1
    exact orderOf_dvd_iff_pow_eq_one.1 this⟩
  have h2 : ψ g ∈ zpowers x := two_elt_mem_zpowers x hg (m := m) (by rw [← map_pow, hm, map_one])
  have h3 : ψ g ∈ zpowers x ⊓ ψ.range := ⟨h2, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩
  rw [hD.disj] at h3
  exact hD.inj (by rw [(Subgroup.mem_bot).1 h3, map_one])

theorem DihData.piPsi_injective (hD : DihData x ψ T) : Function.Injective ((piH x).comp ψ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : ψ g ∈ (piH x).ker := hg
  rw [ker_piH] at this
  exact hD.psi_mem_R this

end Dih

end CFSG.GH74.GLS.Stage1.Thm6.Prod.L145
