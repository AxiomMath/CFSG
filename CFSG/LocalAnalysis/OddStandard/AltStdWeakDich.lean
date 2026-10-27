module

public import CFSG.LocalAnalysis.OddStandard.AltStdWeakShape
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section P2

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

omit [Finite X] in
theorem inf_centralizer_le_zpowers_of_weakShape (h : WeakShape t A m) (hm : 5 ≤ m)
    {P : Subgroup X} [P.Normal] (hP : IsPGroup 2 P) :
    P ⊓ centralizer ({t} : Set X) ≤ zpowers t := by
  obtain ⟨e⟩ := h.iso
  have hsimple : IsSimpleGroup A := isSimpleGroup_of_alt hm e
  set W : Subgroup X := P ⊓ centralizer ({t} : Set X) with hW
  have hnormal : ((A ⊓ W).subgroupOf A).Normal := by
    refine ⟨fun n hn a => ?_⟩
    have hn' : (n : X) ∈ A ⊓ W := hn
    obtain ⟨hnA, hnW⟩ := Subgroup.mem_inf.1 hn'
    obtain ⟨hnP, hnC⟩ := Subgroup.mem_inf.1 hnW
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem a.2 hnA) (inv_mem a.2),
      Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · exact (inferInstance : P.Normal).conj_mem _ hnP _
    · exact mul_mem (mul_mem (h.le_cent a.2) hnC) (inv_mem (h.le_cent a.2))
  have hAW : A ⊓ W = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ((A ⊓ W).subgroupOf A) with hD | hD
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxA, hxW⟩ := Subgroup.mem_inf.1 hx
      have : (⟨x, hxA⟩ : A) ∈ (A ⊓ W).subgroupOf A := hx
      rw [hD] at this
      have h1 : (⟨x, hxA⟩ : A) = 1 := this
      simpa using congrArg Subtype.val h1
    · exfalso
      obtain ⟨x, hx3⟩ := exists_orderOf_three (by omega : 3 ≤ m)
      have hxW : ((e.symm x : A) : X) ∈ W := by
        have : e.symm x ∈ (A ⊓ W).subgroupOf A := by rw [hD]; trivial
        exact (Subgroup.mem_inf.1 this).2
      have hxP : ((e.symm x : A) : X) ∈ P := (Subgroup.mem_inf.1 hxW).1
      have hord : orderOf ((e.symm x : A) : X) = 3 := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx3]
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨((e.symm x : A) : X), hxP⟩
      rw [Subgroup.orderOf_mk, hord] at hk
      rcases k with _ | k
      · simp at hk
      · rw [pow_succ] at hk
        omega
  intro w hw
  have hwC : w ∈ centralizer ({t} : Set X) := (Subgroup.mem_inf.1 hw).2
  have hwcent : w ∈ centralizer (A : Set X) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hwN : w ∈ normalizer (A : Set X) := h.cent_le_norm hwC
    have h1 : w * a * w⁻¹ * a⁻¹ ∈ A := by
      have := mul_mem ((mem_normalizer_iff.1 hwN a).1 ha) (inv_mem ha)
      simpa [mul_assoc] using this
    have h2 : w * a * w⁻¹ * a⁻¹ ∈ W := by
      have haw : a * w⁻¹ * a⁻¹ ∈ W := by
        refine Subgroup.mem_inf.2
          ⟨(inferInstance : P.Normal).conj_mem _ (inv_mem (Subgroup.mem_inf.1 hw).1) _, ?_⟩
        exact mul_mem (mul_mem (h.le_cent ha) (inv_mem hwC)) (inv_mem (h.le_cent ha))
      have := mul_mem hw haw
      simpa [mul_assoc] using this
    have h3 : w * a * w⁻¹ * a⁻¹ ∈ A ⊓ W := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [hAW] at h3
    have h4 : w * a * w⁻¹ * a⁻¹ = 1 := h3
    calc a * w = (w * a * w⁻¹ * a⁻¹)⁻¹ * (w * a) := by group
      _ = w * a := by rw [h4]; group
  obtain ⟨k, hk⟩ := hP ⟨w, (Subgroup.mem_inf.1 hw).1⟩
  refine h.two_mem w ⟨hwcent, hwC⟩ k ?_
  simpa using congrArg Subtype.val hk

theorem mem_center_of_pCore_ne_bot_of_le (ht : orderOf t = 2)
    (hW : CFSG.pCore 2 X ⊓ centralizer ({t} : Set X) ≤ zpowers t)
    (hP : CFSG.pCore 2 X ≠ ⊥) : t ∈ center X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 X with hPdef
  have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have key : ∀ x ∈ zpowers t, x ≠ 1 → x = t := by
    intro x hx hx1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · exfalso
      apply hx1
      rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul]
      have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
      rw [this]; simp
    · rw [← Int.emod_add_mul_ediv k 2, hk, zpow_add, zpow_mul]
      have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
      rw [this]; simp
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hP
  have hZnt : Nontrivial (center ↥P) := IsPGroup.center_nontrivial hPp
  have hZp : IsPGroup 2 (center ↥P) := hPp.to_subgroup _
  have hZd : 2 ∣ Nat.card (center ↥P) := by
    rcases hZp.card_eq_or_dvd with h1 | h1
    · exfalso
      have := Nat.card_eq_one_iff_unique.1 h1
      exact not_subsingleton _ this.1
    · exact h1
  by_cases htP : t ∈ P
  · obtain ⟨z₀, hz₀⟩ := exists_ne (1 : center ↥P)
    have hz₀t : ((z₀ : P) : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.1 z₀.2 ⟨t, htP⟩
      exact congrArg Subtype.val this.symm
    have hz₀ne : ((z₀ : P) : X) ≠ 1 := by
      intro h1
      apply hz₀
      exact Subtype.ext (Subtype.ext h1)
    have hzt : ((z₀ : P) : X) = t :=
      key _ (hW (Subgroup.mem_inf.2 ⟨(z₀ : P).2, hz₀t⟩)) hz₀ne
    have htcent : ∀ x ∈ P, x * t = t * x := by
      intro x hx
      have := Subgroup.mem_center_iff.1 z₀.2 ⟨x, hx⟩
      have h2 : x * ((z₀ : P) : X) = ((z₀ : P) : X) * x := congrArg Subtype.val this
      rw [hzt] at h2
      exact h2
    have hPle : ∀ x ∈ P, x ∈ zpowers t := fun x hx =>
      hW (Subgroup.mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 (htcent x hx)⟩)
    rw [mem_center_iff]
    intro g
    have hgt : g * t * g⁻¹ ∈ zpowers t := hPle _ ((inferInstance : P.Normal).conj_mem t htP g)
    have hord : orderOf (g * t * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact ht
    have heq : g * t * g⁻¹ = t :=
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.eq_of_orderOf_eq_two_of_isCyclic
        (inferInstance : IsCyclic (zpowers t)) hgt (mem_zpowers t) hord ht
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [heq]
  · exfalso
    have hbot : ∀ x ∈ P, x ∈ centralizer ({t} : Set X) → x = 1 := by
      intro x hxP hxC
      by_contra hx1
      exact htP (key x (hW (Subgroup.mem_inf.2 ⟨hxP, hxC⟩)) hx1 ▸ hxP)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := center ↥P) 2 hZd
    have huc : ∀ x : P, x * (u : P) = (u : P) * x := fun x => Subgroup.mem_center_iff.1 u.2 x
    set u0 : X := ((u : P) : X) with hu0
    have hu0P : u0 ∈ P := (u : P).2
    have hu0ord : orderOf u0 = 2 := by
      have h1 : orderOf (u : P) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact hu
      rw [hu0, Subgroup.orderOf_coe, h1]
    have hu0sq : u0 * u0 = 1 := by rw [← sq, ← hu0ord]; exact pow_orderOf_eq_one u0
    set u1 : X := t * u0 * t⁻¹ with hu1
    have hu1P : u1 ∈ P := (inferInstance : P.Normal).conj_mem u0 hu0P t
    have hcomm : u0 * u1 = u1 * u0 := by
      have := huc ⟨u1, hu1P⟩
      exact (congrArg Subtype.val this).symm
    have e1 : u1 * t = t * u0 := by rw [hu1]; group
    have e2 : t * u1 = u0 * t := by
      rw [hu1]
      calc t * (t * u0 * t⁻¹) = (t * t) * u0 * t⁻¹ := by group
        _ = u0 * t := by rw [ht2, ht1]; group
    have hv : u0 * u1 = 1 := by
      apply hbot _ (mul_mem hu0P hu1P)
      rw [mem_centralizer_singleton_iff]
      calc u0 * u1 * t = u0 * (u1 * t) := by group
        _ = u0 * (t * u0) := by rw [e1]
        _ = (u0 * t) * u0 := by group
        _ = (t * u1) * u0 := by rw [e2]
        _ = t * (u1 * u0) := by group
        _ = t * (u0 * u1) := by rw [hcomm]
    have hu10 : u1 = u0 := by
      have := eq_inv_of_mul_eq_one_right hv
      rwa [inv_eq_of_mul_eq_one_right hu0sq] at this
    have hu0C : u0 ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      rw [hu10] at e1
      exact e1
    have := hbot u0 hu0P hu0C
    rw [this, orderOf_one] at hu0ord
    omega

theorem mem_center_of_pCore_ne_bot_of_weakShape (h : WeakShape t A m) (hm : 5 ≤ m)
    (hP : CFSG.pCore 2 X ≠ ⊥) : t ∈ center X :=
  mem_center_of_pCore_ne_bot_of_le h.order
    (inf_centralizer_le_zpowers_of_weakShape h hm CFSG.pCore_isPGroup) hP

theorem inf_le_zpowers_of_mem_center (hO : CFSG.oddCore X = ⊥) (h : WeakShape t A m)
    (hc : t ∈ center X) :
    centralizer (A : Set X) ⊓ centralizer ({t} : Set X) ≤ zpowers t := by
  have hCt : centralizer ({t} : Set X) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.1 hc g
  have hAn : A.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_le_iff.1 (hCt ▸ h.cent_le_norm)
  have d := cyc_of_weakShape h
  have heq := AltStdBal.eq_of_normal_of_isCyclic_sylow hO d.le d.pgroup d.odd_index d.cyclic
  intro y hy
  rw [← heq]
  exact hy.1

end P2

section Comp

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem exists_component_of_weakShape (hO : CFSG.oddCore X = ⊥) (h : WeakShape t A m)
    (hm : 5 ≤ m) :
    ∃ K : Subgroup X, CFSG.IsComponent K ∧
      (∀ L : Subgroup X, CFSG.IsComponent L →
        L = K ∨ L = K.map (MulAut.conj t).toMonoidHom) ∧
      (K.map (MulAut.conj t).toMonoidHom = K → A ≤ K) ∧
      (K.map (MulAut.conj t).toMonoidHom ≠ K →
        ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
          (A : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g}) := by
  classical
  have hpp : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [← ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]; exact hO
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.order] at this
  obtain ⟨-, K, hKc, -, -, -, hiff, hKK1, hKt'⟩ :=
    SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer hpp ht2 h.le_cent
      (isComponent_subgroupOf_centralizer_of_weakShape h hm)
  refine ⟨K, hKc, ?_, fun hKK => (hKK1 hKK).1, fun hKK => ⟨(hKt' hKK).1, (hKt' hKK).2.2.1⟩⟩
  intro L hL
  by_contra hne
  push Not at hne
  have hAL : ⁅A, L⁆ = ⊥ := by
    by_contra hAL
    rcases (hiff L hL).1 hAL with h1 | h1
    · exact hne.1 h1
    · exact hne.2 h1
  have hLC : L ≤ centralizer (A : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hAL
  have hsolv := solvable_centralizer_of_weakShape h
  have hLs : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLC)
      (Subgroup.inclusion_injective hLC)
  have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have : Group.IsPerfect L := hL.1.1
  exact Group.IsPerfect.not_isSolvable L hLs

end Comp

section Wreath

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

omit [Finite X] in
theorem mem_map_conj_iff_exists {K : Subgroup X} {x : X} :
    x ∈ K.map (MulAut.conj t).toMonoidHom ↔ ∃ k ∈ K, t * k * t⁻¹ = x := by
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem centralizer_layer_eq_bot (hF : CFSG.fittingSubgroup X = ⊥) :
    centralizer (CFSG.layer X : Set X) = ⊥ := by
  have hFL : CFSG.generalizedFitting X = CFSG.layer X := by
    simp only [CFSG.generalizedFitting.eq_sup]
    rw [hF, bot_sup_eq]
  rw [eq_bot_iff]
  intro x hx
  have hxL : x ∈ CFSG.layer X := by
    have h1 := CFSG.centralizer_generalizedFitting_le X (by rw [hFL]; exact hx)
    rwa [hFL] at h1
  have hmem : x ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype := by
    refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext ?_), rfl⟩
    exact (mem_centralizer_iff.1 hx g g.2)
  have h2 := center_layer_le_fitting (X := X) hmem
  rw [hF] at h2
  exact h2

theorem eq_one_of_wreath (hF : CFSG.fittingSubgroup X = ⊥) {K : Subgroup X}
    (hall : ∀ L : Subgroup X, CFSG.IsComponent L →
      L = K ∨ L = K.map (MulAut.conj t).toMonoidHom)
    (hKc : CFSG.IsComponent K) (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hA : (A : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g}) {d : X}
    (hd : d ∈ centralizer (A : Set X) ⊓ centralizer ({t} : Set X))
    (hdK : ∀ k ∈ K, d * k * d⁻¹ ∈ K) : d = 1 := by
  set Kt := K.map (MulAut.conj t).toMonoidHom with hKtdef
  have hKtc : CFSG.IsComponent Kt := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hKc
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 hd.2
  have hlayer : CFSG.layer X = K ⊔ Kt := by
    apply le_antisymm
    · refine sSup_le (fun L hL => ?_)
      rcases hall L hL with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_sSup hKc) (le_sSup hKtc)
  have hKKt : K ≤ centralizer (Kt : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hdisj : ∀ x ∈ K, x ∈ Kt → x = 1 := by
    intro x hxK hxKt
    have hzc : ∀ l ∈ CFSG.layer X, l * x = x * l := by
      intro l hl
      rw [hlayer] at hl
      have hle : K ⊔ Kt ≤ centralizer ({x} : Set X) := by
        refine sup_le (fun k hk => ?_) (fun k hk => ?_)
        · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hKKt hk) x hxKt).symm
        · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hKKt hxK) k hk)
      exact mem_centralizer_singleton_iff.1 (hle hl)
    have hxL : x ∈ CFSG.layer X := by rw [hlayer]; exact mem_sup_left hxK
    have hmem : x ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype :=
      ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext (hzc g g.2)), rfl⟩
    have h2 := center_layer_le_fitting (X := X) hmem
    rw [hF] at h2
    exact h2
  have hdK' : ∀ k ∈ K, d * k * d⁻¹ = k := by
    intro k hk
    obtain ⟨k', hk'K, hk'⟩ : ∃ k' ∈ K, d * k * d⁻¹ = k' := ⟨_, hdK k hk, rfl⟩
    have haA : k * (t * k * t⁻¹) ∈ A := by
      have : k * (t * k * t⁻¹) ∈ (A : Set X) := by rw [hA]; exact ⟨k, hk, rfl⟩
      exact this
    have hfix : d * (k * (t * k * t⁻¹)) * d⁻¹ = k * (t * k * t⁻¹) := by
      have := mem_centralizer_iff.1 hd.1 _ haA
      calc d * (k * (t * k * t⁻¹)) * d⁻¹ = (k * (t * k * t⁻¹)) * d * d⁻¹ := by rw [this]
        _ = k * (t * k * t⁻¹) := by group
    have hconj : d * (t * k * t⁻¹) * d⁻¹ = t * k' * t⁻¹ := by
      have hdt' : d⁻¹ * t = t * d⁻¹ := by
        calc d⁻¹ * t = d⁻¹ * (t * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * t) * d⁻¹ := by rw [hdt]
          _ = t * d⁻¹ := by group
      calc d * (t * k * t⁻¹) * d⁻¹ = (d * t) * k * (t⁻¹ * d⁻¹) := by group
        _ = (t * d) * k * (t⁻¹ * d⁻¹) := by rw [hdt]
        _ = t * (d * k * d⁻¹) * (d * t⁻¹ * d⁻¹) := by group
        _ = t * k' * t⁻¹ := by
          have : d * t⁻¹ * d⁻¹ = t⁻¹ := by
            calc d * t⁻¹ * d⁻¹ = (d * t * d⁻¹)⁻¹ := by group
              _ = t⁻¹ := by rw [hdt]; group
          rw [this, hk']
    have heq : k' * (t * k' * t⁻¹) = k * (t * k * t⁻¹) := by
      calc k' * (t * k' * t⁻¹) = (d * k * d⁻¹) * (d * (t * k * t⁻¹) * d⁻¹) := by
            rw [hconj, hk']
        _ = d * (k * (t * k * t⁻¹)) * d⁻¹ := by group
        _ = k * (t * k * t⁻¹) := hfix
    have hmemK : k⁻¹ * k' ∈ K := mul_mem (inv_mem hk) hk'K
    have hmemKt : k⁻¹ * k' ∈ Kt := by
      rw [mem_map_conj_iff_exists]
      refine ⟨k * k'⁻¹, mul_mem hk (inv_mem hk'K), ?_⟩
      have h1 : k⁻¹ * k' = (t * k * t⁻¹) * (t * k' * t⁻¹)⁻¹ := by
        calc k⁻¹ * k' = k⁻¹ * (k' * (t * k' * t⁻¹)) * (t * k' * t⁻¹)⁻¹ := by group
          _ = k⁻¹ * (k * (t * k * t⁻¹)) * (t * k' * t⁻¹)⁻¹ := by rw [heq]
          _ = (t * k * t⁻¹) * (t * k' * t⁻¹)⁻¹ := by group
      rw [h1]
      group
    have := hdisj _ hmemK hmemKt
    calc d * k * d⁻¹ = k' := hk'
      _ = k * (k⁻¹ * k') := by group
      _ = k := by rw [this, mul_one]
  have hdKt : ∀ x ∈ Kt, d * x * d⁻¹ = x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_map_conj_iff_exists.1 hx
    have h1 := hdK' k hk
    have hdt' : d⁻¹ * t = t * d⁻¹ := by
      calc d⁻¹ * t = d⁻¹ * (t * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * t) * d⁻¹ := by rw [hdt]
        _ = t * d⁻¹ := by group
    calc d * (t * k * t⁻¹) * d⁻¹ = (d * t) * k * (t⁻¹ * d⁻¹) := by group
      _ = (t * d) * k * (t⁻¹ * d⁻¹) := by rw [hdt]
      _ = t * (d * k * d⁻¹) * (d * t⁻¹ * d⁻¹) := by group
      _ = t * k * t⁻¹ := by
        rw [h1]
        have : d * t⁻¹ * d⁻¹ = t⁻¹ := by
          calc d * t⁻¹ * d⁻¹ = (d * t * d⁻¹)⁻¹ := by group
            _ = t⁻¹ := by rw [hdt]; group
        rw [this]
  have hdC : d ∈ centralizer (CFSG.layer X : Set X) := by
    rw [mem_centralizer_iff, hlayer]
    intro x hx
    have hle : K ⊔ Kt ≤ centralizer ({d} : Set X) := by
      refine sup_le (fun k hk => ?_) (fun k hk => ?_)
      · rw [mem_centralizer_singleton_iff]
        have := hdK' k hk
        calc k * d = (d * k * d⁻¹) * d := by rw [this]
          _ = d * k := by group
      · rw [mem_centralizer_singleton_iff]
        have := hdKt k hk
        calc k * d = (d * k * d⁻¹) * d := by rw [this]
          _ = d * k := by group
    exact (mem_centralizer_singleton_iff.1 (hle hx))
  rw [centralizer_layer_eq_bot hF] at hdC
  exact hdC

theorem inf_le_zpowers_of_wreath (hF : CFSG.fittingSubgroup X = ⊥) (h : WeakShape t A m)
    {K : Subgroup X} (hKc : CFSG.IsComponent K)
    (hall : ∀ L : Subgroup X, CFSG.IsComponent L →
      L = K ∨ L = K.map (MulAut.conj t).toMonoidHom)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hA : (A : Set X) = {g | ∃ k ∈ K, k * (t * k * t⁻¹) = g}) :
    centralizer (A : Set X) ⊓ centralizer ({t} : Set X) ≤ zpowers t := by
  intro d hd
  have ht2 : t * t = 1 := by rw [← sq, ← h.order]; exact pow_orderOf_eq_one t
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 hd.2
  have hdKc : CFSG.IsComponent (K.map (MulAut.conj d).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj d) hKc
  rcases hall _ hdKc with h1 | h1
  · have hdK : ∀ k ∈ K, d * k * d⁻¹ ∈ K := by
      intro k hk
      have : d * k * d⁻¹ ∈ K.map (MulAut.conj d).toMonoidHom := ⟨k, hk, by simp⟩
      rwa [h1] at this
    rw [eq_one_of_wreath hF hall hKc hcomm hA hd hdK]
    exact one_mem _
  · have htD := mem_inf_of_weakShape h
    have hdtD := mul_mem hd htD
    have hdK : ∀ k ∈ K, d * t * k * (d * t)⁻¹ ∈ K := by
      intro k hk
      have hmem : d * k * d⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := by
        have : d * k * d⁻¹ ∈ K.map (MulAut.conj d).toMonoidHom := ⟨k, hk, by simp⟩
        rwa [h1] at this
      obtain ⟨k₁, hk₁, hk₁e⟩ := mem_map_conj_iff_exists.1 hmem
      have : d * t * k * (d * t)⁻¹ = k₁ := by
        calc d * t * k * (d * t)⁻¹ = t * (d * k * d⁻¹) * t⁻¹ := by
              rw [hdt]; group
          _ = t * (t * k₁ * t⁻¹) * t⁻¹ := by rw [hk₁e]
          _ = (t * t) * k₁ * (t * t)⁻¹ := by group
          _ = k₁ := by rw [ht2]; group
      rw [this]
      exact hk₁
    have h2 := eq_one_of_wreath hF hall hKc hcomm hA hdtD hdK
    have : d = t := by
      calc d = d * t * t := by rw [mul_assoc, ht2, mul_one]
        _ = t := by rw [h2, one_mul]
    rw [this]
    exact mem_zpowers t

end Wreath

end CFSG.OddStandard.AltStdSec
