module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Rho
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lift
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold

open Subgroup CFSG.Open CFSG.Goldschmidt

variable {X : Type} [Group X] [Finite X]

@[expose] def incl (A : Subgroup X) : ↥A →* ↥(nc A) := Subgroup.inclusion Subgroup.le_normalClosure

@[expose] noncomputable def piA (A : Subgroup X) : ↥A →* Mbar A := (proj A).comp (incl A)

theorem piA_apply (A : Subgroup X) (a : ↥A) :
    piA A a = proj A ⟨(a : X), Subgroup.le_normalClosure a.2⟩ := rfl

theorem eq_one_of_mem_oddCore_of_sq {M : Type*} [Group M] [Finite M] {w : M}
    (hw : w ∈ goldschmidtOddCore M) (hw2 : w ^ 2 = 1) : w = 1 := by
  have hodd := CFSG.ComponentClassification.OddCore.odd_card M
  have h1 : orderOf (⟨w, hw⟩ : goldschmidtOddCore M) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext hw2)
  have h2 : Odd (orderOf (⟨w, hw⟩ : goldschmidtOddCore M)) :=
    hodd.of_dvd_nat (orderOf_dvd_natCard _)
  have h3 : orderOf (⟨w, hw⟩ : goldschmidtOddCore M) = 1 := by
    obtain ⟨k, hk⟩ := h2
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

theorem piA_injective {A : Subgroup X} (hA2 : ∀ a ∈ A, a ^ 2 = 1) : Function.Injective (piA A) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : incl A a ∈ goldschmidtOddCore ↥(nc A) := (QuotientGroup.eq_one_iff _).1 ha
  have h1 : incl A a = 1 :=
    eq_one_of_mem_oddCore_of_sq hmem (Subtype.ext (hA2 a a.2))
  have h2 : (((incl A a : ↥(nc A)) : X)) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

theorem Abar_eq_range (A : Subgroup X) : Abar A = (piA A).range := by
  unfold Abar piA
  rw [MonoidHom.range_comp, incl, Subgroup.inclusion_range]

theorem mem_Abar_iff (A : Subgroup X) {q : Mbar A} : q ∈ Abar A ↔ ∃ a : ↥A, piA A a = q := by
  rw [Abar_eq_range, MonoidHom.mem_range]

theorem piA_mem_Abar (A : Subgroup X) (a : ↥A) : piA A a ∈ Abar A :=
  (mem_Abar_iff A).2 ⟨a, rfl⟩

theorem isElemAbelian_Abar {A : Subgroup X} (hEA : IsElemAbelian 2 A) : IsElemAbelian 2 (Abar A) := by
  haveI := hEA.1
  refine ⟨?_, ?_⟩
  · rw [Abar_eq_range]
    infer_instance
  · intro q hq
    obtain ⟨a, rfl⟩ := (mem_Abar_iff A).1 hq
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hEA.2 a a.2)
    rw [this, map_one]

theorem card_Abar {A : Subgroup X} (hEA : IsElemAbelian 2 A) : Nat.card (Abar A) = Nat.card A := by
  rw [Abar_eq_range]
  exact (Nat.card_congr (MonoidHom.ofInjective (piA_injective hEA.2)).toEquiv).symm

theorem rhoHom_piA (A : Subgroup X) {g : X} (hg : g ∈ normalizer (A : Set X)) (a : ↥A) :
    rhoHom A g (piA A a) = piA A ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg a).1 a.2⟩ := rfl

theorem rhoHom_mem_Abar (A : Subgroup X) {g : X} (hg : g ∈ normalizer (A : Set X)) {q : Mbar A}
    (hq : q ∈ Abar A) : rhoHom A g q ∈ Abar A := by
  obtain ⟨a, rfl⟩ := (mem_Abar_iff A).1 hq
  rw [rhoHom_piA A hg]
  exact piA_mem_Abar A _

theorem rhoHom_fpf {A : Subgroup X} (hEA : IsElemAbelian 2 A) {x : X}
    (hx : x ∈ normalizer (A : Set X)) (hfpf : ∀ a ∈ A, x * a * x⁻¹ = a → a = 1) :
    ∀ q ∈ Abar A, rhoHom A x q = q → q = 1 := by
  intro q hq h
  obtain ⟨a, rfl⟩ := (mem_Abar_iff A).1 hq
  rw [rhoHom_piA A hx] at h
  have h1 := piA_injective hEA.2 h
  have h2 : x * (a : X) * x⁻¹ = a := congrArg Subtype.val h1
  have h3 : (a : X) = 1 := hfpf a a.2 h2
  rw [show a = 1 from Subtype.ext h3, map_one]

@[expose] noncomputable def Ubar (A U : Subgroup X) : Subgroup (Mbar A) := (U.subgroupOf A).map (piA A)

theorem Ubar_le_Abar (A U : Subgroup X) : Ubar A U ≤ Abar A := by
  rw [Abar_eq_range]
  exact Subgroup.map_le_range _ _

theorem card_Ubar {A U : Subgroup X} (hEA : IsElemAbelian 2 A) (hUA : U ≤ A) :
    Nat.card (Ubar A U) = Nat.card U := by
  unfold Ubar
  rw [Subgroup.card_map_of_injective (piA_injective hEA.2)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv

theorem piA_mem_Ubar_iff {A U : Subgroup X} (hEA : IsElemAbelian 2 A) (a : ↥A) :
    piA A a ∈ Ubar A U ↔ (a : X) ∈ U := by
  constructor
  · rintro ⟨u, hu, hua⟩
    have := piA_injective hEA.2 hua
    rw [← this]
    exact hu
  · intro h
    exact ⟨a, h, rfl⟩

theorem rhoHom_fixed_iff {A U : Subgroup X} (hEA : IsElemAbelian 2 A) {t : X}
    (ht : t ∈ normalizer (A : Set X)) (hCt : ∀ a ∈ A, t * a * t⁻¹ = a ↔ a ∈ U) {q : Mbar A}
    (hq : q ∈ Abar A) : rhoHom A t q = q ↔ q ∈ Ubar A U := by
  obtain ⟨a, rfl⟩ := (mem_Abar_iff A).1 hq
  rw [rhoHom_piA A ht, piA_mem_Ubar_iff hEA]
  constructor
  · intro h
    exact (hCt a a.2).1 (congrArg Subtype.val (piA_injective hEA.2 h))
  · intro h
    exact congrArg (piA A) (Subtype.ext ((hCt a a.2).2 h))

theorem exists_sylow_Mbar (S : Sylow 2 X) (A : Subgroup X) :
    ∃ Sb : Sylow 2 (Mbar A), (Sb : Subgroup (Mbar A)) = Sbar (S : Subgroup X) A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PM, hPM⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (Subgroup.normalClosure_normal : (nc A).Normal).isSubnormal
  have hPMeq : (PM : Subgroup ↥(nc A)) = (S : Subgroup X).subgroupOf (nc A) := by
    apply Subgroup.map_injective (nc A).subtype_injective
    rw [hPM, Subgroup.subgroupOf_map_subtype]
  refine ⟨PM.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, hPMeq]
  rfl

theorem isSolvable_fixSub_rhoHom (A : Subgroup X) {t : X} (ht2 : t * t = 1)
    (hsolv : Group.IsSolvable ↥(centralizer ({t} : Set X))) :
    Group.IsSolvable ↥(P5.fixSub (rhoHom A t)) := by
  have hker : Odd (Nat.card (proj A).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card _
  refine Lift.isSolvable_fixSub_of_odd_kernel (proj A) (QuotientGroup.mk'_surjective _) hker
    (τ := MulAut.conjNormal t) ?_ (fun m => rfl) ?_
  · rw [← map_pow, show t ^ 2 = 1 by rw [sq]; exact ht2, map_one]
  · have hmem : ∀ m : ↥(P5.fixSub (MulAut.conjNormal t : MulAut ↥(nc A))),
        (((m : ↥(nc A)) : X)) ∈ centralizer ({t} : Set X) := by
      intro m
      have h := P5.mem_fixSub.1 m.2
      have h2 : t * ((m : ↥(nc A)) : X) * t⁻¹ = (m : ↥(nc A)) := by
        rw [← MulAut.conjNormal_apply]
        exact congrArg Subtype.val h
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((m : ↥(nc A)) : X) * t = (t * ((m : ↥(nc A)) : X) * t⁻¹) * t := by rw [h2]
        _ = t * ((m : ↥(nc A)) : X) := by group
    let f : ↥(P5.fixSub (MulAut.conjNormal t : MulAut ↥(nc A))) →* ↥(centralizer ({t} : Set X)) :=
      ((nc A).subtype.comp (P5.fixSub (MulAut.conjNormal t : MulAut ↥(nc A))).subtype).codRestrict
        (centralizer ({t} : Set X)) hmem
    haveI := hsolv
    refine solvable_of_solvable_injective (f := f) fun m₁ m₂ h => ?_
    apply Subtype.ext
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'

theorem normalizer_transitive_of_bar {A : Subgroup X} (hEA : IsElemAbelian 2 A)
    (htrans : ∀ a ∈ Abar A, ∀ b ∈ Abar A, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ normalizer (Abar A : Set (Mbar A)), n⁻¹ * a * n = b) :
    ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (A : Set X), n⁻¹ * a * n = b := by
  intro a ha b hb ha1 hb1
  have hinj := piA_injective hEA.2
  have hne : ∀ c : ↥A, (c : X) ≠ 1 → piA A c ≠ 1 := by
    intro c hc h
    apply hc
    have := hinj (h.trans (map_one (piA A)).symm)
    exact congrArg Subtype.val this
  obtain ⟨nb, hnb, hnab⟩ := htrans (piA A ⟨a, ha⟩) (piA_mem_Abar A _) (piA A ⟨b, hb⟩)
    (piA_mem_Abar A _) (hne ⟨a, ha⟩ ha1) (hne ⟨b, hb⟩ hb1)
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥(nc A)) nb
  have hker : Odd (Nat.card (proj A).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card _
  have hA0 : IsPGroup 2 (A.subgroupOf (nc A)) := fun g => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    have := hEA.2 _ g.2
    simpa using this⟩
  obtain ⟨k, hk, n', hn', hmk⟩ := Lift.exists_mul_normalizer_of_normalizer_map (proj A) hker hA0
    (m := m) hnb
  have hnN : (n' : X) ∈ normalizer (A : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h0 := Subgroup.mem_normalizer_iff.1 hn'
    constructor
    · intro hy
      exact (h0 ⟨y, Subgroup.le_normalClosure hy⟩).1 hy
    · intro hy
      have hyM : y ∈ nc A := by
        have h1 : (n' : X)⁻¹ * ((n' : X) * y * (n' : X)⁻¹) * (n' : X) ∈ nc A :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ n'.2)
            (Subgroup.le_normalClosure hy)) n'.2
        have h2 : (n' : X)⁻¹ * ((n' : X) * y * (n' : X)⁻¹) * (n' : X) = y := by group
        rwa [h2] at h1
      exact (h0 ⟨y, hyM⟩).2 hy
  refine ⟨(n' : X), hnN, ?_⟩
  have hinvN : (n' : X)⁻¹ ∈ normalizer (A : Set X) := Subgroup.inv_mem _ hnN
  have hcA : (n' : X)⁻¹ * a * (n' : X) ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 hinvN a).1 ha
    simpa using this
  have hc : piA A ⟨(n' : X)⁻¹ * a * (n' : X), hcA⟩ = piA A ⟨b, hb⟩ := by
    have h1 : piA A ⟨(n' : X)⁻¹ * a * (n' : X), hcA⟩ =
        (proj A n')⁻¹ * piA A ⟨a, ha⟩ * proj A n' := by
      rw [piA_apply, piA_apply]
      have : (⟨(n' : X)⁻¹ * a * (n' : X), Subgroup.le_normalClosure hcA⟩ : ↥(nc A)) =
          n'⁻¹ * ⟨a, Subgroup.le_normalClosure ha⟩ * n' := rfl
      rw [this, map_mul, map_mul, map_inv]
    rw [h1]
    have h2 : (proj A n') = (proj A k)⁻¹ * proj A m := by
      rw [hmk]
      group
    have hkA : proj A k ∈ Abar A := ⟨k, hk, rfl⟩
    have hcomm : proj A k * piA A ⟨a, ha⟩ = piA A ⟨a, ha⟩ * proj A k :=
      (isElemAbelian_Abar hEA).1.is_comm.comm ⟨_, hkA⟩ ⟨_, piA_mem_Abar A _⟩ |> congrArg Subtype.val
    rw [h2, ← hnab]
    calc ((proj A k)⁻¹ * proj A m)⁻¹ * piA A ⟨a, ha⟩ * ((proj A k)⁻¹ * proj A m)
        = (proj A m)⁻¹ * ((proj A k * piA A ⟨a, ha⟩) * (proj A k)⁻¹) * proj A m := by group
      _ = (proj A m)⁻¹ * (piA A ⟨a, ha⟩ * proj A k * (proj A k)⁻¹) * proj A m := by rw [hcomm]
      _ = (proj A m)⁻¹ * piA A ⟨a, ha⟩ * proj A m := by group
  exact congrArg Subtype.val (hinj hc)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Gold
