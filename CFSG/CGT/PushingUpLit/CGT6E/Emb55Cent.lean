module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V] {G T Y H Q : Subgroup (MulAut V)}

theorem central_coprime_six_eq_one (hsec : Sec5Hyp V G T Y) (hYH : Y ≤ H)
    (hgen : ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → Y ≤ N →
      H ≤ N)
    {z : MulAut V} {m : ℕ} (hzm : z ^ m = 1) (hm : Nat.Coprime m 6) (hzH : z ∈ H)
    (hzc : ∀ h ∈ H, z * h = h * z) : z = 1 := by
  have hm2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hm
  have hmodd : Odd m := Nat.Coprime.odd_of_right hm2
  have hk : ∀ x ∈ Y, z * x * z⁻¹ ∈ Y := fun x hx => by
    have : z * x * z⁻¹ = x := by rw [hzc x (hYH hx)]; group
    rw [this]; exact hx
  have hk' : ∀ x ∈ Y, z⁻¹ * x * z⁻¹⁻¹ ∈ Y := fun x hx => by
    have h1 : z⁻¹ * x * z⁻¹⁻¹ = x := by
      have := hzc x (hYH hx)
      calc z⁻¹ * x * z⁻¹⁻¹ = z⁻¹ * (x * z) := by group
        _ = z⁻¹ * (z * x) := by rw [this]
        _ = x := by group
    rw [h1]; exact hx
  have hzstab : z ∈ stabV (commV Y) := by
    intro w
    refine ⟨fun hw => ?_, fun hw => G6.apply_mem_commV hk hw⟩
    have := G6.apply_mem_commV hk' hw
    simpa using this
  have hUtriv : ∀ u ∈ commV Y, z u = u := by
    set ρ := resStab (commV Y) ⟨z, hzstab⟩ with hρ
    have hW : ∀ w : ↥(commV Y), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hsec.elem w)
    have h6 : Nat.card (MulAut ↥(commV Y)) = 6 := card_mulAut_of_card_four hW hsec.ucard
    have hρm : ρ ^ m = 1 := by
      rw [hρ, ← map_pow]
      have : (⟨z, hzstab⟩ : stabV (commV Y)) ^ m = 1 := Subtype.ext (by simpa using hzm)
      rw [this, map_one]
    have hd6 : orderOf ρ ∣ 6 := h6 ▸ orderOf_dvd_natCard ρ
    have hdm : orderOf ρ ∣ m := orderOf_dvd_of_pow_eq_one hρm
    have h1 : orderOf ρ = 1 := Nat.eq_one_of_dvd_coprimes hm hdm hd6
    have hρ1 : ρ = 1 := orderOf_eq_one_iff.mp h1
    intro u hu
    have := congrArg (fun φ : MulAut ↥(commV Y) => ((φ ⟨u, hu⟩ : ↥(commV Y)) : V)) hρ1
    simpa [hρ, resStab_apply] using this
  let N : Subgroup (MulAut V) :=
    { carrier := {x | x ∈ H ∧ ∀ v : V, z (x v * v⁻¹) = x v * v⁻¹}
      one_mem' := ⟨H.one_mem, fun v => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun v => by
        have e : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
          simp [MulAut.mul_apply]
        rw [e, map_mul, ha.2 (b v), hb.2 v]⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun v => by
        have e : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by simp
        rw [e, map_inv, ha.2 (a⁻¹ v)]⟩ }
  have hNnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    refine ⟨H.mul_mem (H.mul_mem hg hn.1) (H.inv_mem hg), fun v => ?_⟩
    have e : (g * n * g⁻¹) v * v⁻¹ = g (n (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
      simp [MulAut.mul_apply]
    have hcomm : ∀ u : V, z (g u) = g (z u) := fun u => by
      have := congrArg (fun φ : MulAut V => φ u) (hzc g hg)
      simpa [MulAut.mul_apply] using this
    rw [e, hcomm, hn.2 (g⁻¹ v)]
  have hYN : Y ≤ N := fun y hy => ⟨hYH hy, fun v => hUtriv _ (G6.mem_commV_of_mem hy v)⟩
  have hHN : H ≤ N := hgen N (fun n hn => hn.1) hNnorm hYN
  have hodd : Odd (orderOf z) := Odd.of_dvd_nat hmodd (orderOf_dvd_of_pow_eq_one hzm)
  let Ufix : Subgroup V :=
    { carrier := {w | z w = w}
      one_mem' := map_one z
      mul_mem' := fun {a b} ha hb => by
        show z (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show z a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hle : commV (Subgroup.zpowers z) ≤ Ufix := by
    rw [G6.commV_le_iff]
    intro x hx v
    exact (hHN (Subgroup.zpowers_le.mpr hzH hx)).2 v
  exact eq_one_of_trivial_on_commV hsec.elem (Subgroup.mem_zpowers z) hodd (fun w hw => hle hw)

theorem central_odd_le_Q (hsec : Sec5Hyp V G T Y) (hYH : Y ≤ H)
    (hgen : ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → Y ≤ N →
      H ≤ N)
    (hQmax : ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) →
      IsPGroup 3 ↥N → N ≤ Q)
    {z : MulAut V} (hzH : z ∈ H) (hzc : ∀ h ∈ H, z * h = h * z) (hodd : Odd (orderOf z)) :
    z ∈ Q := by
  obtain ⟨k, m, hm, hdecomp⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 3
    (by norm_num)
  have hmodd : Odd m := Odd.of_dvd_nat hodd ⟨3 ^ k, by rw [hdecomp]; ring⟩
  have hm3 : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm
  have hm2 : Nat.Coprime 2 m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by have := Nat.odd_iff.mp hmodd; omega)
  have hm6 : Nat.Coprime m 6 := by
    have := Nat.Coprime.mul_right hm2.symm hm3.symm
    simpa using this
  have hz'm : (z ^ 3 ^ k) ^ m = 1 := by
    rw [← pow_mul, ← hdecomp]
    exact pow_orderOf_eq_one z
  have hz'c : ∀ h ∈ H, z ^ 3 ^ k * h = h * z ^ 3 ^ k := fun h hh =>
    (Commute.pow_left (show Commute z h from hzc h hh) _).eq
  have hz1 : z ^ 3 ^ k = 1 :=
    central_coprime_six_eq_one hsec hYH hgen hz'm hm6 (H.pow_mem hzH _) hz'c
  have hNH : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.mpr hzH
  have hNnorm : ∀ g ∈ H, ∀ n ∈ Subgroup.zpowers z, g * n * g⁻¹ ∈ Subgroup.zpowers z := by
    intro g hg n hn
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * z ^ j = z ^ j * g :=
      (Commute.zpow_right (show Commute g z from (hzc g hg).symm) j).eq
    rw [this]
    simp
  have hN3 : IsPGroup 3 ↥(Subgroup.zpowers z) := by
    intro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    show (z ^ j) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz1, one_zpow]
  exact hQmax _ hNH hNnorm hN3 (Subgroup.mem_zpowers z)

omit [Finite V] in
theorem centralizes_of_gen {Y H S : Subgroup (MulAut V)}
    (hgen : ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → Y ≤ N →
      H ≤ N)
    (hYH : Y ≤ H) (hSinv : ∀ h ∈ H, ∀ x ∈ S, h * x * h⁻¹ ∈ S)
    (hYS : ∀ y ∈ Y, ∀ x ∈ S, y * x = x * y) : ∀ h ∈ H, ∀ x ∈ S, h * x = x * h := by
  set N : Subgroup (MulAut V) := H ⊓ Subgroup.centralizer (S : Set (MulAut V)) with hN
  have hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh (Subgroup.mem_inf.mp hn).1) (H.inv_mem hh),
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : h⁻¹ * x * h ∈ S := by simpa using hSinv h⁻¹ (H.inv_mem hh) x hx
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 _ hx'
    calc x * (h * n * h⁻¹) = h * ((h⁻¹ * x * h) * n) * h⁻¹ := by group
      _ = h * (n * (h⁻¹ * x * h)) * h⁻¹ := by rw [this]
      _ = (h * n * h⁻¹) * x := by group
  have hYN : Y ≤ N := fun y hy =>
    Subgroup.mem_inf.mpr ⟨hYH hy, Subgroup.mem_centralizer_iff.mpr fun x hx => (hYS y hy x hx).symm⟩
  have hHN : H ≤ N := hgen N (fun n hn => (Subgroup.mem_inf.mp hn).1) hNnorm hYN
  intro h hh x hx
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hHN hh)).2 x hx).symm

end CFSG.CGT.PushingUpLit.CGT6E
