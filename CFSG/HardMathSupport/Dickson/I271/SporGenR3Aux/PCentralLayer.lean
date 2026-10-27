module

public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.HardMathSupport.Dickson.I271.PCentralLayer

open Subgroup
open scoped Pointwise

theorem exists_conj_mem_sylow_of_orderOf {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (P : Sylow p H) {y : H} (hy : orderOf y = p) :
    ∃ c : H, c * y * c⁻¹ ∈ (P : Subgroup H) := by
  have hcard : Nat.card (zpowers y) = p ^ 1 := by rw [Nat.card_zpowers, hy, pow_one]
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨c, ?_⟩
  have hmem : y ∈ (Q : Subgroup H) := hQ (mem_zpowers y)
  have h1 : MulAut.conj c • y ∈ MulAut.conj c • (Q : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hmem
  rwa [← Sylow.coe_subgroup_smul, hc, MulAut.smul_def, MulAut.conj_apply] at h1

variable {X : Type*} [Group X] [Finite X]

theorem coprime_orderOf_of_mem_center_layer {p : ℕ} (hp : p.Prime)
    (hcon : ∀ K : Subgroup X, CFSG.IsComponent K → ¬ p ∣ Nat.card (center K)) {x : X}
    (hx : x ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype) : Nat.Coprime p (orderOf x) := by
  rw [(CFSG.LocalCores.layer_center (G := X)).1] at hx
  have key : x ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype ∧
      Nat.Coprime p (orderOf x) := by
    refine Subgroup.iSup_induction
      (fun K : CFSG.LocalCores.ComponentIndex X => (center K.1).map K.1.subtype)
      (C := fun x => x ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype ∧
        Nat.Coprime p (orderOf x)) hx ?_ ?_ ?_
    · intro K y hy
      refine ⟨CFSG.LocalCores.center_component_le_center_layer K.2 hy, ?_⟩
      have h1 : orderOf y ∣ Nat.card ((center K.1).map K.1.subtype) :=
        Subgroup.orderOf_dvd_natCard _ hy
      have h2 : Nat.card ((center K.1).map K.1.subtype) = Nat.card (center K.1) :=
        Nat.card_congr ((center K.1).equivMapOfInjective K.1.subtype
          K.1.subtype_injective).toEquiv.symm
      rw [h2] at h1
      exact Nat.Coprime.coprime_dvd_right h1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (hcon K.1 K.2))
    · exact ⟨one_mem _, by simp⟩
    · rintro a b ⟨ha, hapq⟩ ⟨hb, hbpq⟩
      refine ⟨mul_mem ha hb, ?_⟩
      have hcomm : Commute a b := by
        have hac := ((CFSG.LocalCores.mem_map_center_iff (CFSG.layer X)).1 ha).2
        have hbE := ((CFSG.LocalCores.mem_map_center_iff (CFSG.layer X)).1 hb).1
        exact (mem_centralizer_iff.1 hac b hbE).symm
      refine Nat.Coprime.coprime_dvd_right hcomm.orderOf_mul_dvd_lcm ?_
      exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_right hapq hbpq)
  exact key.2

theorem exists_component_dvd_card_center {p : ℕ} (hp : p.Prime) {z : X} (hzo : orderOf z = p)
    (hzc : z ∈ center X) {P : Subgroup X}
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hZ : ∀ c ∈ P, (∀ g ∈ P, c * g = g * c) → c ∈ zpowers z)
    (hO : CFSG.pPrimeCore p X = ⊥) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    ∃ K' : Subgroup X, CFSG.IsComponent K' ∧ p ∣ Nat.card (center K') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨E, hE⟩ : ∃ E : Subgroup X, E = CFSG.layer X := ⟨_, rfl⟩
  haveI : E.Characteristic := hE ▸ CFSG.LocalCores.layer_characteristic (G := X)
  haveI hEn : E.Normal := inferInstance
  have hKE : K ≤ E := hE ▸ CFSG.LocalCores.component_le_layer hK
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have hEne : E ≠ ⊥ := fun h =>
    (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance (le_bot_iff.1 (h ▸ hKE))
  have hpE : p ∣ Nat.card E := by
    by_contra h
    have hcop : Nat.Coprime p (Nat.card E) := (Nat.Prime.coprime_iff_not_dvd hp).2 h
    have hle : E ≤ CFSG.pPrimeCore p X := le_sSup ⟨hEn, hcop⟩
    rw [hO] at hle
    exact hEne (le_bot_iff.1 hle)
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := E) p hpE
  have hy : orderOf (e : X) = p := by rw [Subgroup.orderOf_coe]; exact he
  let S : Sylow p X := Sylow.ofCard P hP
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow_of_orderOf S hy
  have hcP : c * (e : X) * c⁻¹ ∈ P := hc
  have hcE : c * (e : X) * c⁻¹ ∈ E := hEn.conj_mem _ e.2 c
  have hco : orderOf (c * (e : X) * c⁻¹) = p := by
    rw [← MulAut.conj_apply]
    exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective _).trans hy
  have hcne : c * (e : X) * c⁻¹ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hco
    exact hp.one_lt.ne hco
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hPp
  have hHne : E.subgroupOf P ≠ ⊥ := by
    intro h
    have : (⟨c * (e : X) * c⁻¹, hcP⟩ : P) ∈ E.subgroupOf P := hcE
    rw [h, Subgroup.mem_bot] at this
    exact hcne (congrArg Subtype.val this)
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := P) hHne
  obtain ⟨⟨w, hwE, hwZ⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hmeet
  have hwcomm : ∀ g ∈ P, (w : X) * g = g * w := fun g hg =>
    (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hwZ) ⟨g, hg⟩)).symm
  have hwz : (w : X) ∈ zpowers z := hZ w w.2 hwcomm
  have hwne : (w : X) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  have hzcard : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, hzo]
  have hwo : orderOf (w : X) = p := by
    have hd : orderOf (w : X) ∣ p := hzcard ▸ Subgroup.orderOf_dvd_natCard _ hwz
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hwne
    · exact h
  have hzw : zpowers (w : X) = zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hwz) ?_
    rw [hzcard, Nat.card_zpowers, hwo]
  have hzE : z ∈ E := by
    have : z ∈ zpowers (w : X) := hzw ▸ mem_zpowers z
    have hwE' : (w : X) ∈ E := hwE
    exact (zpowers_le.2 hwE') this
  have hzZ : z ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype :=
    (CFSG.LocalCores.mem_map_center_iff (CFSG.layer X)).2
      ⟨hE ▸ hzE, mem_centralizer_iff.2 fun h _ => (Subgroup.mem_center_iff.1 hzc) h⟩
  have hcop := coprime_orderOf_of_mem_center_layer hp hcon hzZ
  rw [hzo] at hcop
  exact hp.one_lt.ne' ((Nat.coprime_self p).1 hcop)

end CFSG.HardMathSupport.Dickson.I271.PCentralLayer
