module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisReduce
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL34a
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem exists_conj_of_inv_mul_inv {X : Type*} [Group X] {v o : X} (hv : v * v = 1)
    (hvo : v * o * (v * o) = 1) (hodd : Odd (orderOf o)) :
    ∃ k : ℕ, (o ^ k)⁻¹ * v * o ^ k = v * o := by
  obtain ⟨n, hn⟩ := hodd
  have hinv : v * o * v = o⁻¹ := by
    calc v * o * v = v * o * v * (o * o⁻¹) := by group
      _ = (v * o * (v * o)) * o⁻¹ := by group
      _ = o⁻¹ := by rw [hvo, one_mul]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hpow : ∀ k : ℕ, v * o ^ k * v = (o ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => simp [hv]
    | succ k ih =>
      calc v * o ^ (k + 1) * v = (v * o ^ k * v) * (v * o * v) := by
            rw [pow_succ]
            calc v * (o ^ k * o) * v = v * o ^ k * (v⁻¹ * v) * o * v := by group
              _ = v * o ^ k * v * (v * o * v) := by rw [hvinv]; group
        _ = (o ^ (k + 1))⁻¹ := by rw [ih, hinv, pow_succ]; group
  refine ⟨n + 1, ?_⟩
  set p := o ^ (n + 1) with hp
  have ho : p * p = o := by
    rw [hp, ← pow_add, show n + 1 + (n + 1) = orderOf o + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have key : v * p⁻¹ * v = p := by
    have h := congrArg (·⁻¹) (hpow (n + 1))
    simp only [mul_inv_rev, hvinv, inv_inv] at h
    rw [← hp] at h
    simpa [mul_assoc] using h
  calc p⁻¹ * v * p = (v * v) * p⁻¹ * v * p := by rw [hv, one_mul]
    _ = v * (v * p⁻¹ * v) * p := by group
    _ = v * (p * p) := by rw [key, mul_assoc]
    _ = v * o := by rw [ho]

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

abbrev Mb : Type := ↥D.M ⧸ pPrimeCore 2 ↥D.M

abbrev piM : ↥D.M →* D.Mb := QuotientGroup.mk' (pPrimeCore 2 ↥D.M)

abbrev SM : Subgroup ↥D.M := (D.S : Subgroup G).subgroupOf D.M

@[expose] def sylowSM : Sylow 2 ↥D.M := D.S.subtype D.S_le_M

omit [Finite G] in
theorem coe_sylowSM : (D.sylowSM : Subgroup ↥D.M) = D.SM := Sylow.coe_subtype _ _

theorem piM_comp_injective : Function.Injective (D.piM.comp D.SM.subtype) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hsO : (s : ↥D.M) ∈ pPrimeCore 2 ↥D.M := (QuotientGroup.eq_one_iff _).mp hs
  have hP : IsPGroup 2 D.SM := by
    rw [← D.coe_sylowSM]
    exact D.sylowSM.isPGroup'
  have h : (s : ↥D.M) ∈ D.SM ⊓ pPrimeCore 2 ↥D.M := ⟨s.2, hsO⟩
  rw [inf_pPrimeCore_eq_bot hP, mem_bot] at h
  exact Subtype.ext h

@[expose] def sylowMb : Sylow 2 D.Mb :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  D.sylowSM.mapSurjective (QuotientGroup.mk'_surjective _)

theorem coe_sylowMb : (D.sylowMb : Subgroup D.Mb) = D.SM.map D.piM := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sylowMb, Sylow.coe_mapSurjective, D.coe_sylowSM]

abbrev barS (s : (D.S : Subgroup G)) : D.Mb := D.piM ⟨s, D.S_le_M s.2⟩

theorem barS_mem (s : (D.S : Subgroup G)) : D.barS s ∈ (D.sylowMb : Subgroup D.Mb) := by
  rw [D.coe_sylowMb]
  exact mem_map_of_mem _ (mem_subgroupOf.mpr s.2)

theorem barS_injective : Function.Injective D.barS := by
  intro s t h
  have h' := D.piM_comp_injective (a₁ := ⟨⟨s, D.S_le_M s.2⟩, mem_subgroupOf.mpr s.2⟩)
    (a₂ := ⟨⟨t, D.S_le_M t.2⟩, mem_subgroupOf.mpr t.2⟩) h
  exact Subtype.ext (congrArg (fun w : D.SM => ((w : ↥D.M) : G)) h')

@[expose] def homMb : HSFLit.GHGroup →* (D.sylowMb : Subgroup D.Mb) where
  toFun g := ⟨D.barS (D.equiv g), D.barS_mem _⟩
  map_one' := by
    apply Subtype.ext
    change D.piM ⟨((D.equiv 1 : (D.S : Subgroup G)) : G), _⟩ = 1
    rw [show (⟨((D.equiv 1 : (D.S : Subgroup G)) : G), D.S_le_M (D.equiv 1).2⟩ : ↥D.M) = 1 from
      Subtype.ext (by simp)]
    exact map_one _
  map_mul' g h := by
    apply Subtype.ext
    change D.piM ⟨((D.equiv (g * h) : (D.S : Subgroup G)) : G), _⟩ =
      D.piM ⟨((D.equiv g : (D.S : Subgroup G)) : G), _⟩ *
        D.piM ⟨((D.equiv h : (D.S : Subgroup G)) : G), _⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp)

theorem homMb_bijective : Function.Bijective D.homMb := by
  refine ⟨fun g h hgh => D.equiv.injective (D.barS_injective (congrArg Subtype.val hgh)), ?_⟩
  rintro ⟨y, hy⟩
  rw [D.coe_sylowMb] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  refine ⟨D.equiv.symm ⟨s, mem_subgroupOf.mp hs⟩, Subtype.ext ?_⟩
  change D.piM ⟨((D.equiv (D.equiv.symm ⟨s, _⟩) : (D.S : Subgroup G)) : G), _⟩ = D.piM s
  congr 1
  exact Subtype.ext (by simp)

@[expose] def equivMb : HSFLit.GHGroup ≃* (D.sylowMb : Subgroup D.Mb) :=
  MulEquiv.ofBijective D.homMb D.homMb_bijective

@[expose] def toMb : GHSylow D.Mb := ⟨D.sylowMb, D.equivMb⟩

theorem toMb_toG (s : SE) : D.toMb.toG s = D.piM ⟨D.toG s, D.S_le_M (D.toG_mem s)⟩ := rfl

theorem pPrimeCore_Mb : pPrimeCore 2 D.Mb = ⊥ := pPrimeCore_quotient_eq_bot Nat.prime_two

theorem z_comm_Mb : ∀ y : D.Mb, y * D.toMb.z = D.toMb.z * y := by
  intro y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥D.M) y
  rw [GHSylow.z, D.toMb_toG, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp m.2)

theorem exists_conj_M_of_conj_Mb {u v : ↥D.M} (hu : u * u = 1) (hv : v * v = 1) {g : D.Mb}
    (h : g⁻¹ * D.piM u * g = D.piM v) : ∃ m : ↥D.M, m⁻¹ * u * m = v := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥D.M) g
  set w := g₀⁻¹ * u * g₀ with hw
  have hw2 : w * w = 1 := by
    rw [hw, show g₀⁻¹ * u * g₀ * (g₀⁻¹ * u * g₀) = g₀⁻¹ * (u * u) * g₀ by group, hu]
    group
  have hwv : D.piM w = D.piM v := by
    rw [hw, map_mul, map_mul, map_inv]
    exact h
  set o := v⁻¹ * w with ho
  have hoO : o ∈ pPrimeCore 2 ↥D.M := by
    rw [ho]
    exact (QuotientGroup.eq).mp hwv.symm
  have hodd : Odd (orderOf o) := by
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥D.M)) := pPrimeCore_coprime_card
    have hdvd : orderOf o ∣ Nat.card (pPrimeCore 2 ↥D.M) := by
      rw [← Subgroup.orderOf_mk o hoO]
      exact orderOf_dvd_natCard _
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop (h2.trans hdvd))
  have hvo : v * o = w := by rw [ho, mul_inv_cancel_left]
  obtain ⟨k, hk⟩ := exists_conj_of_inv_mul_inv hv (by rw [hvo]; exact hw2) hodd
  refine ⟨g₀ * (o ^ k)⁻¹, ?_⟩
  rw [hvo] at hk
  calc (g₀ * (o ^ k)⁻¹)⁻¹ * u * (g₀ * (o ^ k)⁻¹) = o ^ k * w * (o ^ k)⁻¹ := by rw [hw]; group
    _ = o ^ k * ((o ^ k)⁻¹ * v * o ^ k) * (o ^ k)⁻¹ := by rw [hk]
    _ = v := by group

end GHSylow

end CFSG.ComponentClassification.GHarris
