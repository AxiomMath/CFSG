module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Facts
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RA

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P38

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

theorem card_le_sq_fixed {A : Type} [CommGroup A] [Finite A] (hexp : ∀ u : A, u * u = 1)
    (c : A →* A) (hc : ∀ u, c (c u) = u) :
    Nat.card A ≤ Nat.card ↥(MonoidHom.eqLocus c (MonoidHom.id A)) ^ 2 := by
  let ν : A →* A :=
    { toFun := fun u => u * c u
      map_one' := by simp
      map_mul' := fun u v => by
        rw [map_mul]
        exact mul_mul_mul_comm u v (c u) (c v) }
  have hker : ν.ker = MonoidHom.eqLocus c (MonoidHom.id A) := by
    ext u
    rw [MonoidHom.mem_ker]
    show u * c u = 1 ↔ c u = u
    constructor
    · intro h
      have : c u = u⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact (inv_eq_of_mul_eq_one_right (hexp u))
    · intro h
      rw [h]
      exact hexp u
  have hrange : ν.range ≤ MonoidHom.eqLocus c (MonoidHom.id A) := by
    rintro _ ⟨u, rfl⟩
    show c (u * c u) = u * c u
    rw [map_mul, hc, mul_comm]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ν.ker
  have h2 : Nat.card (A ⧸ ν.ker) = Nat.card ν.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ν).toEquiv
  have h3 : Nat.card ν.range ≤ Nat.card ↥(MonoidHom.eqLocus c (MonoidHom.id A)) :=
    Subgroup.card_le_of_le hrange
  rw [h2, hker] at h1
  rw [h1, sq]
  exact Nat.mul_le_mul h3 le_rfl

theorem dihedral_center_le_commutator {n : ℕ} (hn : 4 ∣ n) :
    center (DihedralGroup n) ≤ ⁅(⊤ : Subgroup (DihedralGroup n)), ⊤⁆ := by
  obtain ⟨k, rfl⟩ := hn
  rw [DihedralGroup.center_eq_closure_of_even_ne_two ⟨2 * k, by ring⟩ (by omega), zpowers_le]
  have h1 : ⁅(DihedralGroup.r 1 : DihedralGroup (4 * k)), (DihedralGroup.sr 0 : DihedralGroup
      (4 * k))⁆ = DihedralGroup.r 2 := by
    rw [commutatorElement_def, DihedralGroup.inv_r, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    congr 1
    ring
  have h2 : DihedralGroup.r (((4 * k / 2 : ℕ)) : ZMod (4 * k)) = DihedralGroup.r 2 ^ k := by
    rw [DihedralGroup.r_pow, show 4 * k / 2 = 2 * k by omega, Nat.cast_mul, Nat.cast_ofNat]
  rw [h2, ← h1]
  exact pow_mem (commutator_mem_commutator (mem_top _) (mem_top _)) k

theorem mem_commutator_of_dihedral {S : Type*} [Group S] {R : Subgroup S} {n : ℕ} (hn : 4 ∣ n)
    (ρ : R ≃* DihedralGroup n) {c : S} (hc : c ∈ R) (hcZ : ∀ r ∈ R, c * r = r * c) :
    c ∈ ⁅R, R⁆ := by
  have hcen : ρ ⟨c, hc⟩ ∈ center (DihedralGroup n) := by
    rw [mem_center_iff]
    intro d
    obtain ⟨d', rfl⟩ := ρ.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcZ d' d'.2).symm
  have hmap : Subgroup.map (R.subtype.comp ρ.symm.toMonoidHom)
      ⁅(⊤ : Subgroup (DihedralGroup n)), ⊤⁆ ≤ ⁅R, R⁆ := by
    rw [map_commutator]
    apply commutator_mono <;> rintro _ ⟨x, -, rfl⟩ <;> exact (ρ.symm x).2
  have := hmap ⟨_, dihedral_center_le_commutator hn hcen, rfl⟩
  simpa using this

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

structure L37Data (x : G) (K T : Subgroup G) (f z : G) : Prop where
  ha : thompsonJ2 T = (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x)
  hb : (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) = ⊥
  hc : zCenter (thompsonJ2 T) = zpowers z ⊔ zpowers f ⊔ zpowers x
  hd : ∀ P₀ : Subgroup G, IsDihedralMaxIn P₀ (T ⊓ K) →
    T ⊓ centralizer ({f} : Set G) = T ⊓ normalizer (P₀ : Set G)

namespace Env37

variable (E : Env37 x y K T V W f z) (D : L37Data x K T f z)

include E

theorem hEf : ∀ e ∈ zpowers f ⊔ zpowers x, e * f = f * e := fun _ he =>
  mem_centralizer_singleton_iff.1
    ((sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 E.hfx.symm))) he)

theorem hEx : ∀ e ∈ zpowers f ⊔ zpowers x, e * x = x * e := fun _ he =>
  mem_centralizer_singleton_iff.1
    ((sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 E.hfx))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))) he)

theorem hEE : ∀ e₁ ∈ zpowers f ⊔ zpowers x, ∀ e₂ ∈ zpowers f ⊔ zpowers x, e₁ * e₂ = e₂ * e₁ := by
  intro e₁ he₁ e₂ he₂
  have hle : zpowers f ⊔ zpowers x ≤ centralizer ({e₂} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hEf e₂ he₂).symm))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hEx e₂ he₂).symm))
  exact mem_centralizer_singleton_iff.1 (hle he₁)

theorem hEP : ∀ e ∈ zpowers f ⊔ zpowers x, ∀ p ∈ T ⊓ K, e * p = p * e := by
  intro e he p hp
  have hle : zpowers f ⊔ zpowers x ≤ centralizer ({p} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hfP p hp)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hxc p hp.1).symm))
  exact mem_centralizer_singleton_iff.1 (hle he)

theorem z_mem_commutator : z ∈ ⁅T ⊓ K, T ⊓ K⁆ := by
  obtain ⟨n, hn3, -, k, hk, hk2, ⟨ρ⟩⟩ := E.hdih
  have h4 : 4 ∣ k := by
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h2 : k = 2 ^ (n - 1) := by omega
    rw [h2]
    have := pow_dvd_pow 2 (show 2 ≤ n - 1 by omega)
    simpa using this
  exact mem_commutator_of_dihedral h4 ρ E.hzP (fun r hr => (E.hzc r hr.1).symm)

include D

theorem commutator_J_le : ⁅thompsonJ2 T, thompsonJ2 T⁆ ≤ T ⊓ K := by
  rw [D.ha, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨p₁, hp₁, e₁, he₁, rfl⟩ := Thm1P310.exists_mul_of_mem_sup
    (fun u hu w hw => (E.hEP w hw u hu).symm) hg₁
  obtain ⟨p₂, hp₂, e₂, he₂, rfl⟩ := Thm1P310.exists_mul_of_mem_sup
    (fun u hu w hw => (E.hEP w hw u hu).symm) hg₂
  have h1 : e₁ * p₂ = p₂ * e₁ := E.hEP e₁ he₁ p₂ hp₂
  have h2 : e₂ * p₁⁻¹ = p₁⁻¹ * e₂ := E.hEP e₂ he₂ p₁⁻¹ ((T ⊓ K).inv_mem hp₁)
  have h3 : e₁ * e₂ = e₂ * e₁ := E.hEE e₁ he₁ e₂ he₂
  have key : ⁅p₁ * e₁, p₂ * e₂⁆ = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ := by
    rw [commutatorElement_def]
    calc p₁ * e₁ * (p₂ * e₂) * (p₁ * e₁)⁻¹ * (p₂ * e₂)⁻¹
        = p₁ * (e₁ * p₂) * e₂ * e₁⁻¹ * p₁⁻¹ * e₂⁻¹ * p₂⁻¹ := by group
      _ = p₁ * (p₂ * e₁) * e₂ * e₁⁻¹ * p₁⁻¹ * e₂⁻¹ * p₂⁻¹ := by rw [h1]
      _ = p₁ * p₂ * (e₁ * e₂ * e₁⁻¹) * p₁⁻¹ * e₂⁻¹ * p₂⁻¹ := by group
      _ = p₁ * p₂ * e₂ * p₁⁻¹ * e₂⁻¹ * p₂⁻¹ := by rw [h3]; group
      _ = p₁ * p₂ * (e₂ * p₁⁻¹) * e₂⁻¹ * p₂⁻¹ := by group
      _ = p₁ * p₂ * (p₁⁻¹ * e₂) * e₂⁻¹ * p₂⁻¹ := by rw [h2]
      _ = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ := by group
  rw [key]
  exact (T ⊓ K).mul_mem ((T ⊓ K).mul_mem ((T ⊓ K).mul_mem hp₁ hp₂) ((T ⊓ K).inv_mem hp₁))
    ((T ⊓ K).inv_mem hp₂)

theorem normalizes_z : ∀ n ∈ normalizer (T : Set G), n * z * n⁻¹ = z := by
  intro n hn
  have hnJ : ∀ w ∈ ⁅thompsonJ2 T, thompsonJ2 T⁆, n * w * n⁻¹ ∈ ⁅thompsonJ2 T, thompsonJ2 T⁆ := by
    intro w hw
    have hmap : ⁅thompsonJ2 T, thompsonJ2 T⁆.map (MulAut.conj n).toMonoidHom ≤
        ⁅thompsonJ2 T, thompsonJ2 T⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (Thm1P39R.thompsonJ2_conj_le hn) (Thm1P39R.thompsonJ2_conj_le hn)
    exact hmap ⟨w, hw, by simp [MulAut.conj_apply]⟩
  have hzJ : z ∈ ⁅thompsonJ2 T, thompsonJ2 T⁆ := by
    refine Subgroup.commutator_mono ?_ ?_ E.z_mem_commutator
    · rw [D.ha]; exact le_sup_left
    · rw [D.ha]; exact le_sup_left
  have hnzP : n * z * n⁻¹ ∈ T ⊓ K := E.commutator_J_le D (hnJ z hzJ)
  have hn' : n⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hn
  have hcen : ∀ p ∈ T ⊓ K, (n * z * n⁻¹) * p = p * (n * z * n⁻¹) := by
    intro p hp
    have hp' : n⁻¹ * p * n ∈ T := by
      have := (Subgroup.mem_normalizer_iff.1 hn' p).1 hp.1
      simpa using this
    have hc := E.hzc _ hp'
    calc (n * z * n⁻¹) * p = n * (z * (n⁻¹ * p * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * p * n) * z) * n⁻¹ := by rw [← hc]
      _ = p * (n * z * n⁻¹) := by group
  rcases E.hzu _ hnzP hcen with h | h
  · exfalso
    apply E.hz1
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · exact h

end Env37

section Klein

variable {G : Type} [Group G]

theorem card_klein_of_comm {f x : G} (hf2 : orderOf f = 2) (hx2 : orderOf x = 2)
    (hfx : f * x = x * f) (hne : f ≠ x) : Nat.card ↥(zpowers f ⊔ zpowers x) = 4 := by
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hcomm : Commute f x := hfx
  have hnorm : zpowers x ≤ normalizer ((zpowers f : Subgroup G) : Set G) := by
    refine le_trans (zpowers_le.2 ?_) (Subgroup.centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact (hcomm.zpow_left k).eq
  have hdisj : Disjoint (zpowers f) (zpowers x) := by
    refine Subgroup.disjoint_def.2 ?_
    intro g hgf hgx
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hff hgf with h1 | h1
    · exact h1
    · rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hxx hgx with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hne
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, Nat.card_zpowers, hf2, hx2]

theorem three_comm_sq {z f x : G} (hz : z * z = 1) (hf : f * f = 1) (hx : x * x = 1)
    (hzf : z * f = f * z) (hzx : z * x = x * z) (hfx : f * x = x * f) :
    (∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x, ∀ v ∈ zpowers z ⊔ zpowers f ⊔ zpowers x,
      u * v = v * u) ∧ ∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x, u * u = 1 := by
  set A : Subgroup G := zpowers z ⊔ zpowers f ⊔ zpowers x with hA
  have hzA : z ∈ A := Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers z))
  have hfA : f ∈ A := Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers f))
  have hxA : x ∈ A := Subgroup.mem_sup_right (mem_zpowers x)
  have hz_cent : ∀ u ∈ A, u * z = z * u := fun u hu => by
    have hle : A ≤ centralizer ({z} : Set G) :=
      sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hzf.symm)))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hzx.symm))
    exact mem_centralizer_singleton_iff.1 (hle hu)
  have hf_cent : ∀ u ∈ A, u * f = f * u := fun u hu => by
    have hle : A ≤ centralizer ({f} : Set G) :=
      sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hzf))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hfx.symm))
    exact mem_centralizer_singleton_iff.1 (hle hu)
  have hx_cent : ∀ u ∈ A, u * x = x * u := fun u hu => by
    have hle : A ≤ centralizer ({x} : Set G) :=
      sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hzx))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hfx)))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    exact mem_centralizer_singleton_iff.1 (hle hu)
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := by
    intro u hu v hv
    have hle : A ≤ centralizer ({v} : Set G) :=
      sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hz_cent v hv).symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hf_cent v hv).symm)))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hx_cent v hv).symm))
    exact mem_centralizer_singleton_iff.1 (hle hu)
  refine ⟨hcomm, ?_⟩
  let Sub : Subgroup G :=
    { carrier := {u | u ∈ A ∧ u * u = 1}
      one_mem' := ⟨A.one_mem, by simp⟩
      mul_mem' := fun {u v} hu hv => by
        refine ⟨A.mul_mem hu.1 hv.1, ?_⟩
        calc u * v * (u * v) = u * (v * u) * v := by group
          _ = u * (u * v) * v := by rw [hcomm v hv.1 u hu.1]
          _ = (u * u) * (v * v) := by group
          _ = 1 := by rw [hu.2, hv.2, one_mul]
      inv_mem' := fun {u} hu => by
        refine ⟨A.inv_mem hu.1, ?_⟩
        calc u⁻¹ * u⁻¹ = (u * u)⁻¹ := by group
          _ = 1 := by rw [hu.2]; simp }
  have hle : A ≤ Sub :=
    sup_le (sup_le (zpowers_le.2 ⟨hzA, hz⟩) (zpowers_le.2 ⟨hfA, hf⟩)) (zpowers_le.2 ⟨hxA, hx⟩)
  exact fun u hu => (hle hu).2

end Klein

namespace Env37

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}
  (E : Env37 x y K T V W f z) (D : L37Data x K T f z)

omit D in
include E in
theorem hzf : z * f = f * z := E.hfz.symm

include E D

theorem z_ne_x : z ≠ x := by
  intro h
  have hz1 := E.hz1
  have : z ∈ (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) :=
    ⟨E.hzP, by rw [h]; exact Subgroup.mem_sup_right (mem_zpowers x)⟩
  rw [D.hb, Subgroup.mem_bot] at this
  exact hz1 this

theorem card_A : Nat.card ↥(zpowers z ⊔ zpowers f ⊔ zpowers x) = 8 := by
  rw [sup_assoc]
  have hKl := card_klein_of_comm E.cfg.hf2 E.cfg.hx2 E.hfx E.hfne
  have hnorm : zpowers f ⊔ zpowers x ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    refine le_trans (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_))
      (Subgroup.centralizer_le_normalizer _)
    · rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute z f from E.hzf) k).eq
    · rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute z x from E.hzx) k).eq
  have hdisj : Disjoint (zpowers z) (zpowers f ⊔ zpowers x) := by
    refine Subgroup.disjoint_def.2 ?_
    intro g hgz hgfx
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers E.hzz hgz with h1 | h1
    · exact h1
    · exfalso
      have : z ∈ (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) := ⟨E.hzP, h1 ▸ hgfx⟩
      rw [D.hb, Subgroup.mem_bot] at this
      exact E.hz1 this
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj, hKl,
    Nat.card_zpowers, E.hz2']

omit D in
theorem mem_B_or_f_mul : ∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x,
    u ∈ zpowers z ⊔ zpowers x ∨ ∃ w ∈ zpowers z ⊔ zpowers x, u = f * w := by
  intro u hu
  have hzB : z ∈ zpowers z ⊔ zpowers x := Subgroup.mem_sup_left (mem_zpowers z)
  have hxB : x ∈ zpowers z ⊔ zpowers x := Subgroup.mem_sup_right (mem_zpowers x)
  rcases Thm1P39R.mem_three_cases E.hzz E.hf2 E.hx2 E.hzf E.hzx E.hfx hu with
    (h | h | h | h) | (h | h | h | h)
  · left; rw [h]; exact one_mem _
  · left; rw [h]; exact hzB
  · right; exact ⟨1, one_mem _, by rw [h, mul_one]⟩
  · right; exact ⟨z, hzB, by rw [h, E.hzf]⟩
  · left; rw [h]; exact hxB
  · left; rw [h]; exact (zpowers z ⊔ zpowers x).mul_mem hzB hxB
  · right; exact ⟨x, hxB, h⟩
  · right
    refine ⟨z * x, (zpowers z ⊔ zpowers x).mul_mem hzB hxB, ?_⟩
    rw [h]
    calc z * f * x = f * z * x := by rw [E.hzf]
      _ = f * (z * x) := by rw [mul_assoc]

theorem exists_fixed_f_mul {a : G}
    (hnorm : ∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x, a * u * a⁻¹ ∈ zpowers z ⊔ zpowers f ⊔ zpowers x)
    (hax : a * x * a⁻¹ ≠ x)
    (ha2 : ∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x, a ^ 2 * u * (a ^ 2)⁻¹ = u) :
    ∃ w ∈ zpowers z ⊔ zpowers x, a * (f * w) * a⁻¹ = f * w := by
  classical
  obtain ⟨hAc, hAsq⟩ := three_comm_sq E.hzz E.hf2 E.hx2 E.hzf E.hzx E.hfx
  set A : Subgroup G := zpowers z ⊔ zpowers f ⊔ zpowers x with hAdef
  set B : Subgroup G := zpowers z ⊔ zpowers x with hBdef
  have hzA : z ∈ A := Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers z))
  have hxA : x ∈ A := Subgroup.mem_sup_right (mem_zpowers x)
  have hBA : B ≤ A := sup_le (zpowers_le.2 hzA) (zpowers_le.2 hxA)
  let _ : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun u v => Subtype.ext (hAc u u.2 v v.2) }
  let c : ↥A →* ↥A := MonoidHom.mk' (fun u => ⟨a * (u : G) * a⁻¹, hnorm u u.2⟩)
    (fun u v => Subtype.ext (by simp [mul_assoc]))
  have hc : ∀ u, c (c u) = u := fun u => Subtype.ext (by
    show a * (a * (u : G) * a⁻¹) * a⁻¹ = u
    have := ha2 u u.2
    calc a * (a * (u : G) * a⁻¹) * a⁻¹ = a ^ 2 * u * (a ^ 2)⁻¹ := by simp only [sq]; group
      _ = u := this)
  have hexp : ∀ u : ↥A, u * u = 1 := fun u => Subtype.ext (hAsq u u.2)
  have hbound := card_le_sq_fixed hexp c hc
  have hA8 : Nat.card ↥A = 8 := E.card_A D
  rw [hA8] at hbound
  by_contra hno
  push Not at hno
  set F := MonoidHom.eqLocus c (MonoidHom.id ↥A) with hF
  have hFB : F ≤ B.subgroupOf A := by
    intro u hu
    have hcu : a * (u : G) * a⁻¹ = u := congrArg Subtype.val hu
    rcases E.mem_B_or_f_mul u u.2 with hB | ⟨w, hw, huw⟩
    · exact hB
    · exfalso
      apply hno w hw
      rw [← huw]
      exact hcu
  have hxB : (⟨x, hxA⟩ : ↥A) ∈ B.subgroupOf A := Subgroup.mem_sup_right (mem_zpowers x)
  have hxF : (⟨x, hxA⟩ : ↥A) ∉ F := fun h => hax (congrArg Subtype.val h)
  have hBcard : Nat.card ↥(B.subgroupOf A) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]
    exact card_klein_of_comm E.hz2' E.cfg.hx2 E.hzx (E.z_ne_x D)
  have hdvd : Nat.card ↥F ∣ 2 ^ 2 := by
    have := Subgroup.card_dvd_of_le hFB
    rw [hBcard] at this
    simpa using this
  obtain ⟨i, hi, hFi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hFle : Nat.card ↥F ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have hi2 : i = 2 := by
      by_contra hne
      have : i ≤ 1 := by omega
      have : 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    rw [hi2] at hFi
    have : F = B.subgroupOf A :=
      Subgroup.eq_of_le_of_card_ge hFB (by rw [hBcard, hFi]; norm_num)
    exact hxF (this ▸ hxB)
  have h1 : Nat.card ↥F ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hFle 2
  omega

variable {S : Subgroup G} {a : G}

omit D in
theorem mem_T_of_comm_x (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) {n : G} (hnS : n ∈ S)
    (hnx : n * x = x * n) : n ∈ T := by
  have hQp : IsPGroup 2 ↥(T ⊔ zpowers n) :=
    hS.isPGroup.to_le (sup_le hTS (zpowers_le.2 hnS))
  have hQC : T ⊔ zpowers n ≤ centralizer ({x} : Set G) :=
    sup_le E.hCx (zpowers_le.2 (mem_centralizer_singleton_iff.2 hnx))
  have := E.cfg.setup.sylowT.eq_of_le le_sup_left hQC hQp
  rw [← this]
  exact Subgroup.mem_sup_right (mem_zpowers n)

omit E D in
theorem lt_twoPart_of_ssup (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (haS : a ∈ S) (haT : a ∉ T) {g : G}
    (hTg : ∀ t ∈ T, t * g = g * t) (hag : a * g = g * a) :
    Nat.card ↥T < twoPartCard (centralizer ({g} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 ↥(T ⊔ zpowers a) :=
    hS.isPGroup.to_le (sup_le hTS (zpowers_le.2 haS))
  have hQC : T ⊔ zpowers a ≤ centralizer ({g} : Set G) :=
    sup_le (fun t ht => mem_centralizer_singleton_iff.2 (hTg t ht))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hag))
  obtain ⟨P', hP'⟩ := exists_isSylowOf (G := G) 2 (centralizer ({g} : Set G))
  have h1 : Nat.card ↥(T ⊔ zpowers a) ≤ Nat.card ↥P' :=
    Thm1L3.card_le_of_isPGroup_of_isSylowOf hQp hQC hP'
  have h2 : Nat.card ↥P' = twoPartCard (centralizer ({g} : Set G)) := hP'.card_eq
  have h3 : Nat.card ↥T < Nat.card ↥(T ⊔ zpowers a) := by
    by_contra hge
    push Not at hge
    have : T ⊔ zpowers a = T := (Subgroup.eq_of_le_of_card_ge le_sup_left hge).symm
    exact haT (this ▸ Subgroup.mem_sup_right (mem_zpowers a))
  omega

include D

theorem not_central_f (hle : Nat.card ↥V ≤ Nat.card ↥T) (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S)
    (haS : a ∈ S) (haN : a ∈ normalizer (T : Set G)) (haT : a ∉ T) (ha2 : a ^ 2 ∈ T) :
    ¬ ∀ t ∈ T, t * f = f * t := by
  intro hfZ
  have hAcent : ∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x, ∀ t ∈ T, t * u = u * t := by
    intro u hu t ht
    have hle' : zpowers z ⊔ zpowers f ⊔ zpowers x ≤ centralizer ({t} : Set G) :=
      sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hzc t ht).symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hfZ t ht).symm)))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hxc t ht).symm))
    exact (mem_centralizer_singleton_iff.1 (hle' hu)).symm
  have haJ : a ∈ normalizer ((thompsonJ2 T : Subgroup G) : Set G) :=
    Thm1L3.mem_normalizer_of_conj_le fun j hj => Thm1P39R.conj_mem_thompsonJ2 haN hj
  have hnorm : ∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x,
      a * u * a⁻¹ ∈ zpowers z ⊔ zpowers f ⊔ zpowers x := by
    intro u hu
    rw [← D.hc] at hu ⊢
    exact Thm1P39R.conj_mem_zCenter haJ hu
  have hax : a * x * a⁻¹ ≠ x := by
    intro h
    exact haT (E.mem_T_of_comm_x hS hTS haS (by
      have : a * x = x * a := by
        calc a * x = (a * x * a⁻¹) * a := by group
          _ = x * a := by rw [h]
      exact this))
  have ha2' : ∀ u ∈ zpowers z ⊔ zpowers f ⊔ zpowers x, a ^ 2 * u * (a ^ 2)⁻¹ = u := by
    intro u hu
    have := hAcent u hu (a ^ 2) ha2
    calc a ^ 2 * u * (a ^ 2)⁻¹ = u * a ^ 2 * (a ^ 2)⁻¹ := by rw [this]
      _ = u := by group
  obtain ⟨w, hw, hfix⟩ := E.exists_fixed_f_mul D hnorm hax ha2'
  have hf₁ := E.isFMember_f_mul w hw
  have hf₁A : f * w ∈ zpowers z ⊔ zpowers f ⊔ zpowers x :=
    (zpowers z ⊔ zpowers f ⊔ zpowers x).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers f)))
      ((sup_le (le_trans le_sup_left le_sup_left) le_sup_right : zpowers z ⊔ zpowers x ≤
        zpowers z ⊔ zpowers f ⊔ zpowers x) hw)
  have hag : a * (f * w) = (f * w) * a := by
    calc a * (f * w) = (a * (f * w) * a⁻¹) * a := by group
      _ = (f * w) * a := by rw [hfix]
  have hlt := lt_twoPart_of_ssup hS hTS haS haT (g := f * w)
    (fun t ht => hAcent _ hf₁A t ht) hag
  have hbd := E.bound hle hf₁
  omega

theorem inf_centralizer_zCenter :
    T ⊓ centralizer ((zCenter (thompsonJ2 T) : Subgroup G) : Set G) =
      T ⊓ centralizer ({f} : Set G) := by
  ext t
  simp only [mem_inf]
  constructor
  · rintro ⟨htT, htc⟩
    refine ⟨htT, ?_⟩
    have hf : f ∈ zCenter (thompsonJ2 T) := by
      rw [D.hc]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers f))
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htc f hf).symm
  · rintro ⟨htT, htf⟩
    refine ⟨htT, ?_⟩
    have hle : zpowers z ⊔ zpowers f ⊔ zpowers x ≤ centralizer ({t} : Set G) := by
      refine sup_le (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 (E.hzc t htT).symm
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 htf).symm
      · exact mem_centralizer_singleton_iff.2 (E.hxc t htT).symm
    refine mem_centralizer_iff.2 fun g hg => ?_
    rw [D.hc] at hg
    exact mem_centralizer_singleton_iff.1 (hle hg)

omit D in
theorem T_normalizes_P : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
  ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), E.hKN t (E.hCx ht) p hp.2⟩

end Env37

omit [Finite G] in
theorem map_conj_eq_iff {P₀ : Subgroup G} {t : G} :
    P₀.map (MulAut.conj t).toMonoidHom = P₀ ↔ t ∈ normalizer (P₀ : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_normalizer_iff.2 fun w => ?_
    constructor
    · intro hw
      rw [← h]
      exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
    · intro hw
      rw [← h] at hw
      obtain ⟨p, hp, hpw⟩ := hw
      have : p = w := by
        simpa [MulAut.conj_apply] using hpw
      rw [← this]
      exact hp
  · intro h
    ext w
    rw [Thm1P39R.mem_map_conj_iff]
    have := Subgroup.mem_normalizer_iff.1 ((normalizer (P₀ : Set G)).inv_mem h) w
    simpa using this.symm

namespace Env37

variable (E : Env37 x y K T V W f z) (D : L37Data x K T f z) {S : Subgroup G} {a : G}

include E D

theorem card_T_eq (hnc : ¬ ∀ t ∈ T, t * f = f * t) :
    Nat.card ↥T = 2 * Nat.card ↥(T ⊓ centralizer ((zCenter (thompsonJ2 T) : Subgroup G) : Set G)) := by
  obtain ⟨n, hn3, hdn⟩ := E.hdih
  obtain ⟨P₀, hP₀⟩ := Thm1P39R.exists_isDihedralMaxIn hn3 hdn
  set M : Subgroup G := T ⊓ centralizer ({f} : Set G) with hM
  have hMeq : M = T ⊓ normalizer (P₀ : Set G) := D.hd P₀ hP₀
  rw [E.inf_centralizer_zCenter D, ← hM]
  have hMT : M ≤ T := inf_le_left
  have hMne : M ≠ T := by
    intro h
    apply hnc
    intro t ht
    have : t ∈ M := h ▸ ht
    exact mem_centralizer_singleton_iff.1 this.2
  obtain ⟨t₀, ht₀T, ht₀M⟩ : ∃ t₀ ∈ T, t₀ ∉ M := by
    by_contra hall
    push Not at hall
    exact hMne (le_antisymm hMT hall)
  have hconj : ∀ t ∈ T, IsDihedralMaxIn (P₀.map (MulAut.conj t).toMonoidHom) (T ⊓ K) := fun t ht =>
    Thm1P39R.isDihedralMaxIn_map_conj hP₀ (E.T_normalizes_P t ht)
  have hnormiff : ∀ t ∈ T, t ∈ M ↔ P₀.map (MulAut.conj t).toMonoidHom = P₀ := by
    intro t ht
    rw [hMeq, map_conj_eq_iff]
    exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
  have hcover : ∀ t ∈ T, t ∈ M ∨ t₀⁻¹ * t ∈ M := by
    intro t ht
    by_contra hcon
    push Not at hcon
    obtain ⟨htM, h0M⟩ := hcon
    have hB := hconj t₀ ht₀T
    have hC := hconj t ht
    have h1 : P₀.map (MulAut.conj t₀).toMonoidHom ≠ P₀ := fun h => ht₀M ((hnormiff t₀ ht₀T).2 h)
    have h2 : P₀.map (MulAut.conj t).toMonoidHom ≠ P₀ := fun h => htM ((hnormiff t ht).2 h)
    rcases Thm1P39R.eq_of_isDihedralMaxIn_three hn3 hdn hP₀ hB hC with h | h | h
    · exact h1 h.symm
    · apply h0M
      rw [hnormiff _ (T.mul_mem (T.inv_mem ht₀T) ht)]
      have : P₀.map (MulAut.conj (t₀⁻¹ * t)).toMonoidHom =
          (P₀.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t₀⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext g
        simp [MulAut.conj_apply, mul_assoc]
      rw [this, ← h, Subgroup.map_map]
      ext g
      simp [MulAut.conj_apply, mul_assoc]
    · exact h2 h.symm
  set M' : Subgroup ↥T := M.subgroupOf T with hM'
  have hM'top : M' ≠ ⊤ := by
    intro h
    apply ht₀M
    have : (⟨t₀, ht₀T⟩ : ↥T) ∈ M' := h ▸ Subgroup.mem_top _
    exact this
  have hidx1 : M'.index ≠ 1 := fun h => hM'top (Subgroup.index_eq_one.1 h)
  have hidx2 : M'.index ≤ 2 := by
    have hsurj : Function.Surjective (fun b : Bool =>
        (QuotientGroup.mk (cond b (1 : ↥T) ⟨t₀, ht₀T⟩) : ↥T ⧸ M')) := by
      intro q
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
      rcases hcover t t.2 with h | h
      · refine ⟨true, ?_⟩
        show (QuotientGroup.mk (1 : ↥T) : ↥T ⧸ M') = QuotientGroup.mk t
        rw [QuotientGroup.eq, inv_one, one_mul]
        exact h
      · refine ⟨false, ?_⟩
        show (QuotientGroup.mk (⟨t₀, ht₀T⟩ : ↥T) : ↥T ⧸ M') = QuotientGroup.mk t
        rw [QuotientGroup.eq]
        exact h
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa [Subgroup.index] using this
  have hidxpos : 0 < M'.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hidx : M'.index = 2 := by omega
  have hcard := Subgroup.index_mul_card M'
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMT).toEquiv] at hcard
  exact hcard.symm

omit D in
theorem zCenter_T_eq (hnc : ¬ ∀ t ∈ T, t * f = f * t) : zCenter T = zpowers x ⊔ zpowers z := by
  apply le_antisymm
  · intro g hg
    have hgA : g ∈ zpowers z ⊔ zpowers f ⊔ zpowers x :=
      E.cent_P_le hg.1 (fun p hp => (hg.2 p hp.1).symm)
    rcases E.mem_B_or_f_mul g hgA with hB | ⟨w, hw, hgw⟩
    · rwa [sup_comm] at hB
    · exfalso
      apply hnc
      intro t ht
      have hwt : t * w = w * t := by
        have hle : zpowers z ⊔ zpowers x ≤ centralizer ({t} : Set G) := by
          refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
          · exact mem_centralizer_singleton_iff.2 (E.hzc t ht).symm
          · exact mem_centralizer_singleton_iff.2 (E.hxc t ht).symm
        exact (mem_centralizer_singleton_iff.1 (hle hw)).symm
      have hwt' : t * w⁻¹ = w⁻¹ * t := by
        calc t * w⁻¹ = w⁻¹ * (w * t) * w⁻¹ := by group
          _ = w⁻¹ * (t * w) * w⁻¹ := by rw [hwt]
          _ = w⁻¹ * t := by group
      have hf : f = g * w⁻¹ := by rw [hgw]; group
      calc t * f = t * (g * w⁻¹) := by rw [← hf]
        _ = (t * g) * w⁻¹ := by group
        _ = (g * t) * w⁻¹ := by rw [hg.2 t ht]
        _ = g * (t * w⁻¹) := by group
        _ = g * (w⁻¹ * t) := by rw [hwt']
        _ = (g * w⁻¹) * t := by group
        _ = f * t := by rw [← hf]
  · exact sup_le (zpowers_le.2 ⟨E.hxT, E.hxc⟩) (zpowers_le.2 ⟨E.hzP.1, E.hzc⟩)

omit D in
theorem a_not_comm_x (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (haS : a ∈ S) (haT : a ∉ T) :
    a * x * a⁻¹ ≠ x := by
  intro h
  refine haT (E.mem_T_of_comm_x hS hTS haS ?_)
  calc a * x = (a * x * a⁻¹) * a := by group
    _ = x * a := by rw [h]

theorem a_x_conj (hnc : ¬ ∀ t ∈ T, t * f = f * t) (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S)
    (haS : a ∈ S) (haN : a ∈ normalizer (T : Set G)) (haT : a ∉ T) (ha2 : a ^ 2 ∈ T) :
    a * x * a⁻¹ = x * z := by
  have hZ := E.zCenter_T_eq hnc
  have hxZ : x ∈ zCenter T := ⟨E.hxT, E.hxc⟩
  have hax := E.a_not_comm_x hS hTS haS haT
  have hmem : a * x * a⁻¹ ∈ zpowers x ⊔ zpowers z := by
    rw [← hZ]
    exact Thm1P39R.conj_mem_zCenter haN hxZ
  rcases Thm1G33.klein_cases E.hx2 E.hzz E.hzx.symm hmem with h | h | h | h
  · exfalso
    have h1 : x = 1 := by
      calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group
    have h2 := E.cfg.hx2
    rw [h1, orderOf_one] at h2
    omega
  · exact absurd h hax
  · exfalso
    have hz := E.normalizes_z D a haN
    have hx2 : a ^ 2 * x * (a ^ 2)⁻¹ = x := by
      have := E.hxc _ ha2
      calc a ^ 2 * x * (a ^ 2)⁻¹ = x * a ^ 2 * (a ^ 2)⁻¹ := by rw [this]
        _ = x := by group
    apply E.z_ne_x D
    calc z = a * z * a⁻¹ := hz.symm
      _ = a * (a * x * a⁻¹) * a⁻¹ := by rw [h]
      _ = a ^ 2 * x * (a ^ 2)⁻¹ := by simp only [sq]; group
      _ = x := hx2
  · exact h

theorem normalizer_S_eq (hnc : ¬ ∀ t ∈ T, t * f = f * t) (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S)
    (haS : a ∈ S) (haN : a ∈ normalizer (T : Set G)) (haT : a ∉ T) (ha2 : a ^ 2 ∈ T) :
    S ⊓ normalizer (T : Set G) = T ⊔ zpowers a := by
  apply le_antisymm
  · rintro n ⟨hnS, hnN⟩
    have hZ := E.zCenter_T_eq hnc
    have hxZ : x ∈ zCenter T := ⟨E.hxT, E.hxc⟩
    have hmem : n * x * n⁻¹ ∈ zpowers x ⊔ zpowers z := by
      rw [← hZ]
      exact Thm1P39R.conj_mem_zCenter hnN hxZ
    have hnz := E.normalizes_z D n hnN
    have hax := E.a_x_conj D hnc hS hTS haS haN haT ha2
    rcases Thm1G33.klein_cases E.hx2 E.hzz E.hzx.symm hmem with h | h | h | h
    · exfalso
      have h1 : x = 1 := by
        calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
          _ = 1 := by rw [h]; group
      have h2 := E.cfg.hx2
      rw [h1, orderOf_one] at h2
      omega
    ·
      have hnT : n ∈ T := E.mem_T_of_comm_x hS hTS hnS (by
        calc n * x = (n * x * n⁻¹) * n := by group
          _ = x * n := by rw [h])
      exact Subgroup.mem_sup_left hnT
    · exfalso
      apply E.z_ne_x D
      have h1 : n * z * n⁻¹ = n * x * n⁻¹ := by rw [hnz, h]
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = n⁻¹ * (n * x * n⁻¹) * n := by rw [h1]
        _ = x := by group
    · have hcomm : a⁻¹ * n * x = x * (a⁻¹ * n) := by
        have h1 : n * x * n⁻¹ = a * x * a⁻¹ := by rw [h, hax]
        calc a⁻¹ * n * x = a⁻¹ * (n * x * n⁻¹) * n := by group
          _ = a⁻¹ * (a * x * a⁻¹) * n := by rw [h1]
          _ = x * (a⁻¹ * n) := by group
      have hanT : a⁻¹ * n ∈ T :=
        E.mem_T_of_comm_x hS hTS (S.mul_mem (S.inv_mem haS) hnS) hcomm
      have : n = a * (a⁻¹ * n) := by group
      rw [this]
      exact (T ⊔ zpowers a).mul_mem (Subgroup.mem_sup_right (mem_zpowers a))
        (Subgroup.mem_sup_left hanT)
  · exact sup_le (le_inf hTS Subgroup.le_normalizer) (zpowers_le.2 ⟨haS, haN⟩)

theorem not_normal_P₀ (hle : Nat.card ↥V ≤ Nat.card ↥T) (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S)
    (haS : a ∈ S) (haN : a ∈ normalizer (T : Set G)) (haT : a ∉ T) (ha2 : a ^ 2 ∈ T) :
    ∀ P₀ : Subgroup G, IsDihedralMaxIn P₀ (T ⊓ K) → ¬ ∀ t ∈ T, ∀ p ∈ P₀, t * p * t⁻¹ ∈ P₀ := by
  intro P₀ hP₀ hall
  apply E.not_central_f D hle hS hTS haS haN haT ha2
  intro t ht
  have htN : t ∈ normalizer (P₀ : Set G) :=
    Thm1L3.mem_normalizer_of_conj_le fun p hp => hall t ht p hp
  have : t ∈ T ⊓ normalizer (P₀ : Set G) := ⟨ht, htN⟩
  rw [← D.hd P₀ hP₀] at this
  exact mem_centralizer_singleton_iff.1 this.2

end Env37

end CFSG.GH74.GLS.C3.Layer1.Thm1P38
