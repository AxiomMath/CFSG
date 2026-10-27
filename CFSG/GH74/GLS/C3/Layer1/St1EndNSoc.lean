module

public import CFSG.GH74.GLS.C3.Layer1.Th2P86Abs
public import CFSG.GH74.E2.TermBasic

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.Soc

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2.P85
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_noncomm_of_quasisimple {K : Subgroup X} (hK : CFSG.IsQuasisimple ↥K) :
    ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  have hKcomm : ⁅K, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k1 hk1
    rw [mem_centralizer_iff]
    intro k2 hk2
    exact hcon k2 hk2 k1 hk1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  have hbot : K = ⊥ := by rw [← hKperf]; exact hKcomm
  exact (Subgroup.nontrivial_iff_ne_bot K).1 this hbot

theorem comp_le_or_le {D K P S : Subgroup X} (hKq : CFSG.IsQuasisimple ↥K) (hK : IsCompIn D K)
    (hPD : P ≤ D) (hSD : S ≤ D)
    (hPn : D ≤ normalizer (P : Set X)) (hSn : D ≤ normalizer (S : Set X))
    (hKPS : K ≤ P ⊔ S) : K ≤ P ∨ K ≤ S := by
  have hKD : K ≤ D := hK.1
  have hPnorm : (P.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPD).2 hPn
  have hSnorm : (S.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSD).2 hSn
  have h1 := CFSG.LocalCores.component_subnormal_subgroup hK.2 hPnorm.isSubnormal
  have h2 := CFSG.LocalCores.component_subnormal_subgroup hK.2 hSnorm.isSubnormal
  have key : ∀ T : Subgroup X, T ≤ D →
      (K.subgroupOf D ≤ T.subgroupOf D ∨ ⁅K.subgroupOf D, T.subgroupOf D⁆ = ⊥) →
      (K ≤ T ∨ ∀ k ∈ K, ∀ t ∈ T, k * t = t * k) := by
    intro T hTD h
    rcases h with h | h
    · left
      intro k hk
      exact h (show (⟨k, hKD hk⟩ : ↥D) ∈ K.subgroupOf D from hk)
    · right
      intro k hk t ht
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      have h' := mem_centralizer_iff.1
        (h (show (⟨k, hKD hk⟩ : ↥D) ∈ K.subgroupOf D from hk)) ⟨t, hTD ht⟩
        (show (⟨t, hTD ht⟩ : ↥D) ∈ T.subgroupOf D from ht)
      exact (congrArg Subtype.val h').symm
  rcases key P hPD h1 with hP | hP
  · exact Or.inl hP
  rcases key S hSD h2 with hS | hS
  · exact Or.inr hS
  exfalso
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_quasisimple hKq
  apply hab
  have hle : P ⊔ S ≤ centralizer (K : Set X) := by
    refine sup_le ?_ ?_
    · intro p hp
      rw [mem_centralizer_iff]
      intro k hk
      exact hP k hk p hp
    · intro s hs
      rw [mem_centralizer_iff]
      intro k hk
      exact hS k hk s hs
  have := hle (hKPS ha)
  rw [mem_centralizer_iff] at this
  exact (this b hb).symm

theorem component_le_of_no_involution {J Λ : Subgroup X} (hJ : J.IsSubnormal)
    (hno : ∀ b : X, orderOf b = 2 → ¬ J ≤ centralizer ({b} : Set X))
    (hΛ : CFSG.IsComponent Λ) : Λ ≤ J := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hΛ hJ with h | h
  · exact h
  · exfalso
    obtain ⟨b, hbΛ, hb2⟩ := CFSG.GH74.GLS.EvenCore.exists_involution_of_isComponent hΛ
    refine hno b hb2 fun j hj => ?_
    have h1 := Subgroup.commutator_mem_commutator hbΛ hj
    rw [h, Subgroup.mem_bot] at h1
    exact mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

theorem eq_layer_of_min {K J : Subgroup X} (hKlayer : K ≤ CFSG.layer X) (hKJ : K ≤ J)
    (hJ : J.IsSubnormal)
    (hmin : ∀ J' : Subgroup X, K ≤ J' → J' ≤ J → J'.IsSubnormal → J' = J)
    (hno : ∀ b : X, orderOf b = 2 → ¬ J ≤ centralizer ({b} : Set X)) : J = CFSG.layer X := by
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have hn : (CFSG.layer X).Normal := inferInstance
  apply le_antisymm
  · have h := hmin (J ⊓ CFSG.layer X) (le_inf hKJ hKlayer) inf_le_left (hJ.inf hn.isSubnormal)
    exact inf_eq_left.1 h
  · exact sSup_le fun M hM => component_le_of_no_involution hJ hno hM

theorem fitting_eq_bot (hcore : pPrimeCore 2 X = ⊥)
    (hno : ∀ b : X, orderOf b = 2 → ¬ CFSG.layer X ≤ centralizer ({b} : Set X)) :
    fittingSubgroup X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hFn : (fittingSubgroup X).Normal := inferInstance
  have hFp : IsPGroup 2 ↥(fittingSubgroup X) :=
    CFSG.isPGroup_of_nilpotent_normal (fittingSubgroup X) hFn inferInstance hcore
  obtain ⟨b, hbF, hb2⟩ := Th2.exists_involution_mem hFp hne
  have hcomm : ⁅fittingSubgroup X, CFSG.layer X⁆ = ⊥ := CFSG.LocalCores.fitting_layer_commute
  refine hno b hb2 fun l hl => ?_
  have h1 := Subgroup.commutator_mem_commutator hbF hl
  rw [hcomm, Subgroup.mem_bot] at h1
  exact mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

omit [Finite X] in
theorem layer_center_trivial (hF : fittingSubgroup X = ⊥) :
    ∀ z ∈ CFSG.layer X, (∀ e ∈ CFSG.layer X, z * e = e * z) → z = 1 := by
  intro z hz hzc
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have hLn : (CFSG.layer X).Normal := inferInstance
  have hnormal : ((center ↥(CFSG.layer X)).map (CFSG.layer X).subtype).Normal := inferInstance
  have hnil : Group.IsNilpotent ↥((center ↥(CFSG.layer X)).map (CFSG.layer X).subtype) :=
    Group.nilpotent_of_mulEquiv ((center ↥(CFSG.layer X)).equivMapOfInjective
      (CFSG.layer X).subtype (CFSG.layer X).subtype_injective)
  have hle : (center ↥(CFSG.layer X)).map (CFSG.layer X).subtype ≤ fittingSubgroup X :=
    le_sSup ⟨hnormal, hnil⟩
  rw [hF, le_bot_iff] at hle
  have hzmem : z ∈ (center ↥(CFSG.layer X)).map (CFSG.layer X).subtype := by
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    show (⟨z, hz⟩ : ↥(CFSG.layer X)) ∈ center ↥(CFSG.layer X)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2).symm
  rw [hle, Subgroup.mem_bot] at hzmem
  exact hzmem

omit [Finite X] in
theorem mem_sup_of_commute {A B : Subgroup X} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {e : X}
    (he : e ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, e = a * b := by
  let T : Subgroup X :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h1 := h a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← h1]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 := h a ha b hb
        have h2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := (Commute.inv_inv (h1 : Commute a b)).eq
        rw [mul_inv_rev, h2] }
  have hle : A ⊔ B ≤ T :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩) (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle he

omit [Finite X] in
theorem le_normalizer_sup {D A B : Subgroup X} (hA : D ≤ normalizer (A : Set X))
    (hB : D ≤ normalizer (B : Set X)) : D ≤ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [Subgroup.le_normalizer_iff] at hA hB ⊢
  intro d hd n hn
  have hmap : (A ⊔ B).map (MulAut.conj d).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (by rintro _ ⟨a, ha, rfl⟩; exact hA d hd a ha)
      (by rintro _ ⟨b, hb, rfl⟩; exact hB d hd b hb)
  exact hmap ⟨n, hn, rfl⟩

theorem comp_comm {M M' : Subgroup X} (hM : CFSG.IsComponent M) (hM' : CFSG.IsComponent M')
    (hne : M' ≠ M) : ∀ m' ∈ M', ∀ m ∈ M, m' * m = m * m' := by
  have h := (CFSG.LocalCores.distinct_components_commute hM' hM).resolve_left hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  intro m' hm' m hm
  exact (mem_centralizer_iff.1 (h hm') m hm).symm

theorem layer_le_normalizer {M : Subgroup X} (hM : CFSG.IsComponent M) :
    CFSG.layer X ≤ normalizer (M : Set X) := by
  refine sSup_le fun M' hM' => ?_
  by_cases h : M' = M
  · rw [h]; exact Subgroup.le_normalizer
  · rw [Subgroup.le_normalizer_iff]
    intro m' hm' k hk
    rw [comp_comm hM hM' h m' hm' k hk, mul_inv_cancel_right]
    exact hk

theorem comp_le_centralizer_sup {Λ Λ' M : Subgroup X} (hΛ : CFSG.IsComponent Λ)
    (hΛ' : CFSG.IsComponent Λ') (hM : CFSG.IsComponent M) (h1 : M ≠ Λ) (h2 : M ≠ Λ') :
    M ≤ centralizer ((Λ ⊔ Λ' : Subgroup X) : Set X) := by
  intro m hm
  rw [mem_centralizer_iff]
  intro n hn
  have hle : Λ ⊔ Λ' ≤ centralizer ({m} : Set X) := by
    refine sup_le ?_ ?_
    · intro l hl
      rw [mem_centralizer_singleton_iff]
      exact (comp_comm hΛ hM h1 m hm l hl).symm
    · intro l hl
      rw [mem_centralizer_singleton_iff]
      exact (comp_comm hΛ' hM h2 m hm l hl).symm
  exact mem_centralizer_singleton_iff.1 (hle hn)

theorem le_orbit_prod {x : X} (hx2 : orderOf x = 2) {K : Subgroup X}
    (hKq : CFSG.IsQuasisimple ↥K) (hKc : IsCompIn (centralizer ({x} : Set X)) K)
    (hKE : K ≤ CFSG.layer X)
    (hZ : ∀ z ∈ CFSG.layer X, (∀ e ∈ CFSG.layer X, z * e = e * z) → z = 1)
    {Λ : Subgroup X} (hΛ : CFSG.IsComponent Λ) (hKΛ : ∃ k ∈ K, ∃ l ∈ Λ, k * l ≠ l * k) :
    K ≤ Λ ⊔ Λ.map (MulAut.conj x).toMonoidHom := by
  have hx1 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx2, pow_two] at h
    exact h
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
  have hΛ' : CFSG.IsComponent (Λ.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hΛ
  have hconj2 : ∀ g : X, x * (x * g * x⁻¹) * x⁻¹ = g := by
    intro g
    rw [hxinv]
    calc x * (x * g * x) * x = (x * x) * g * (x * x) := by group
      _ = g := by rw [hx1]; simp
  generalize hΛ'def : Λ.map (MulAut.conj x).toMonoidHom = Λ' at hΛ' ⊢
  have hΛ'x : ∀ l ∈ Λ, x * l * x⁻¹ ∈ Λ' := by
    intro l hl
    rw [← hΛ'def]
    exact ⟨l, hl, rfl⟩
  have hΛx : ∀ l' ∈ Λ', x * l' * x⁻¹ ∈ Λ := by
    intro l' hl'
    rw [← hΛ'def] at hl'
    obtain ⟨l, hl, rfl⟩ := hl'
    show x * (x * l * x⁻¹) * x⁻¹ ∈ Λ
    rw [hconj2]
    exact hl
  have hNx : ∀ n ∈ Λ ⊔ Λ', x * n * x⁻¹ ∈ Λ ⊔ Λ' := by
    have h1 : Λ.map (MulAut.conj x).toMonoidHom ≤ Λ ⊔ Λ' := by
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.mem_sup_right (hΛ'x a ha)
    have h2 : Λ'.map (MulAut.conj x).toMonoidHom ≤ Λ ⊔ Λ' := by
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_sup_left (hΛx b hb)
    have hmap : (Λ ⊔ Λ').map (MulAut.conj x).toMonoidHom ≤ Λ ⊔ Λ' := by
      rw [Subgroup.map_sup]
      exact sup_le h1 h2
    intro n hn
    exact hmap ⟨n, hn, rfl⟩
  have hNE : Λ ⊔ Λ' ≤ CFSG.layer X :=
    sup_le (CFSG.LocalCores.component_le_layer hΛ) (CFSG.LocalCores.component_le_layer hΛ')
  have hEN : CFSG.layer X ≤ normalizer ((Λ ⊔ Λ' : Subgroup X) : Set X) :=
    le_normalizer_sup (layer_le_normalizer hΛ) (layer_le_normalizer hΛ')
  have hEN' := Subgroup.le_normalizer_iff.1 hEN
  have hcommN : ∀ M : Subgroup X, CFSG.IsComponent M → M ≠ Λ → M ≠ Λ' →
      M ≤ centralizer ((Λ ⊔ Λ' : Subgroup X) : Set X) := fun M hM h1 h2 =>
    comp_le_centralizer_sup hΛ hΛ' hM h1 h2
  have hER : CFSG.layer X ≤ (Λ ⊔ Λ') ⊔ (centralizer ((Λ ⊔ Λ' : Subgroup X) : Set X) ⊓ CFSG.layer X) := by
    refine sSup_le fun M hM => ?_
    by_cases h1 : M = Λ
    · rw [h1]; exact le_sup_of_le_left le_sup_left
    by_cases h2 : M = Λ'
    · rw [h2]; exact le_sup_of_le_left le_sup_right
    exact le_sup_of_le_right (le_inf (hcommN M hM h1 h2) (CFSG.LocalCores.component_le_layer hM))
  have hEnormal : (CFSG.layer X).Normal := by
    have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hRN : ∀ n ∈ Λ ⊔ Λ', ∀ r ∈ centralizer ((Λ ⊔ Λ' : Subgroup X) : Set X) ⊓ CFSG.layer X,
      n * r = r * n := fun n hn r hr => mem_centralizer_iff.1 (Subgroup.mem_inf.1 hr).1 n hn
  have hxR : ∀ r ∈ centralizer ((Λ ⊔ Λ' : Subgroup X) : Set X) ⊓ CFSG.layer X,
      x * r * x⁻¹ ∈ centralizer ((Λ ⊔ Λ' : Subgroup X) : Set X) ⊓ CFSG.layer X := by
    intro r hr
    refine Subgroup.mem_inf.2 ⟨?_, hEnormal.conj_mem r (Subgroup.mem_inf.1 hr).2 x⟩
    rw [mem_centralizer_iff]
    intro n hn
    have hn2 : x * n * x ∈ Λ ⊔ Λ' := by simpa [hxinv] using hNx n hn
    have hc := hRN _ hn2 r hr
    calc n * (x * r * x⁻¹) = x * ((x * n * x) * r) * x⁻¹ := by
          have : x * ((x * n * x) * r) * x⁻¹ = (x * x) * n * (x * r * x⁻¹) := by group
          rw [this, hx1, one_mul]
      _ = x * (r * (x * n * x)) * x⁻¹ := by rw [hc]
      _ = (x * r * x⁻¹) * n := by
          have : x * (r * (x * n * x)) * x⁻¹ = (x * r * x⁻¹) * (x * x) * n * (x * x⁻¹) := by group
          rw [this, hx1]
          simp
  set N : Subgroup X := Λ ⊔ Λ' with hNdef
  set R : Subgroup X := centralizer (N : Set X) ⊓ CFSG.layer X with hRdef
  have hRE : R ≤ CFSG.layer X := inf_le_right
  have hKPS : K ≤ (N ⊓ centralizer ({x} : Set X)) ⊔ (R ⊓ centralizer ({x} : Set X)) := by
    intro k hk
    have hkE : k ∈ CFSG.layer X := hKE hk
    obtain ⟨n, hn, r, hr, hkeq⟩ := mem_sup_of_commute hRN (hER hkE)
    have hkx : x * k * x⁻¹ = k := by
      have h1 : k * x = x * k := mem_centralizer_singleton_iff.1 (hKc.1 hk)
      rw [← h1]
      group
    have hn1 : x * n * x⁻¹ ∈ N := hNx n hn
    have hr1 : x * r * x⁻¹ ∈ R := hxR r hr
    have hprod : (x * n * x⁻¹) * (x * r * x⁻¹) = n * r := by
      calc (x * n * x⁻¹) * (x * r * x⁻¹) = x * (n * r) * x⁻¹ := by group
        _ = n * r := by rw [← hkeq]; exact hkx
    have hzN : n⁻¹ * (x * n * x⁻¹) ∈ N := N.mul_mem (N.inv_mem hn) hn1
    have hzR : n⁻¹ * (x * n * x⁻¹) ∈ R := by
      have h2 : n⁻¹ * (x * n * x⁻¹) = r * (x * r * x⁻¹)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc n⁻¹ * (x * n * x⁻¹) * (x * r * x⁻¹) = n⁻¹ * ((x * n * x⁻¹) * (x * r * x⁻¹)) := by group
          _ = n⁻¹ * (n * r) := by rw [hprod]
          _ = r := by group
      rw [h2]
      exact R.mul_mem hr (R.inv_mem hr1)
    have hz1 : n⁻¹ * (x * n * x⁻¹) = 1 := by
      generalize n⁻¹ * (x * n * x⁻¹) = z at hzN hzR ⊢
      apply hZ _ (hNE hzN)
      intro e he
      obtain ⟨n', hn', r', hr', rfl⟩ := mem_sup_of_commute hRN (hER he)
      have h1 : z * n' = n' * z := (hRN n' hn' _ hzR).symm
      have h2 : z * r' = r' * z := hRN _ hzN r' hr'
      calc z * (n' * r') = (z * n') * r' := (mul_assoc _ _ _).symm
        _ = (n' * z) * r' := by rw [h1]
        _ = n' * (z * r') := mul_assoc _ _ _
        _ = n' * (r' * z) := by rw [h2]
        _ = n' * r' * z := (mul_assoc _ _ _).symm
    have hnx : x * n * x⁻¹ = n := (inv_mul_eq_one.1 hz1).symm
    have hrx : x * r * x⁻¹ = r := by
      rw [hnx] at hprod
      exact mul_left_cancel hprod
    have hnC : n ∈ centralizer ({x} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have : x * n = n * x := by
        calc x * n = (x * n * x⁻¹) * x := by group
          _ = n * x := by rw [hnx]
      exact this.symm
    have hrC : r ∈ centralizer ({x} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have : x * r = r * x := by
        calc x * r = (x * r * x⁻¹) * x := by group
          _ = r * x := by rw [hrx]
      exact this.symm
    rw [hkeq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hn, hnC⟩) (Subgroup.mem_inf.2 ⟨hr, hrC⟩)
  have hD : IsCompIn (CFSG.layer X ⊓ centralizer ({x} : Set X)) K :=
    CFSG.GH74.E2.isCompIn_mono hKc (le_inf hKE hKc.1) inf_le_right
  have hPD : N ⊓ centralizer ({x} : Set X) ≤ CFSG.layer X ⊓ centralizer ({x} : Set X) :=
    inf_le_inf_right _ hNE
  have hSD : R ⊓ centralizer ({x} : Set X) ≤ CFSG.layer X ⊓ centralizer ({x} : Set X) :=
    inf_le_inf_right _ hRE
  have hPn : CFSG.layer X ⊓ centralizer ({x} : Set X) ≤
      normalizer ((N ⊓ centralizer ({x} : Set X) : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd p hp
    obtain ⟨hdE, hdC⟩ := Subgroup.mem_inf.1 hd
    obtain ⟨hpN, hpC⟩ := Subgroup.mem_inf.1 hp
    exact Subgroup.mem_inf.2 ⟨hEN' d hdE p hpN,
      (centralizer ({x} : Set X)).mul_mem ((centralizer ({x} : Set X)).mul_mem hdC hpC)
        ((centralizer ({x} : Set X)).inv_mem hdC)⟩
  have hSn : CFSG.layer X ⊓ centralizer ({x} : Set X) ≤
      normalizer ((R ⊓ centralizer ({x} : Set X) : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd s hs
    obtain ⟨hdE, hdC⟩ := Subgroup.mem_inf.1 hd
    obtain ⟨hsR, hsC⟩ := Subgroup.mem_inf.1 hs
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, hEnormal.conj_mem s (Subgroup.mem_inf.1 hsR).2 d⟩,
      (centralizer ({x} : Set X)).mul_mem ((centralizer ({x} : Set X)).mul_mem hdC hsC)
        ((centralizer ({x} : Set X)).inv_mem hdC)⟩
    rw [mem_centralizer_iff]
    intro n hn
    have hn' : d⁻¹ * n * d⁻¹⁻¹ ∈ N := hEN' d⁻¹ ((CFSG.layer X).inv_mem hdE) n hn
    have hc := hRN _ hn' s hsR
    calc n * (d * s * d⁻¹) = d * ((d⁻¹ * n * d⁻¹⁻¹) * s) * d⁻¹ := by group
      _ = d * (s * (d⁻¹ * n * d⁻¹⁻¹)) * d⁻¹ := by rw [hc]
      _ = (d * s * d⁻¹) * n := by group
  rcases comp_le_or_le hKq hD hPD hSD hPn hSn hKPS with h | h
  · exact h.trans (inf_le_left)
  · exfalso
    obtain ⟨k, hk, l, hl, hne⟩ := hKΛ
    exact hne (hRN l (Subgroup.mem_sup_left hl) k (Subgroup.mem_inf.1 (h hk)).1).symm

omit [Finite X] in
theorem conj_map_mul (T : Subgroup X) (g h : X) :
    T.map (MulAut.conj (g * h)).toMonoidHom =
      (T.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite X] in
theorem conj_map_one (T : Subgroup X) : T.map (MulAut.conj (1 : X)).toMonoidHom = T := by
  ext y
  simp

omit [Finite X] in
theorem conj_map_cancel (T : Subgroup X) (g : X) :
    (T.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = T := by
  rw [← conj_map_mul, inv_mul_cancel, conj_map_one]

omit [Finite X] in
theorem not_mem_commutator_of_swap {x : X} {Λ : Subgroup X} (hΛ : CFSG.IsComponent Λ)
    (hne : Λ.map (MulAut.conj x).toMonoidHom ≠ Λ)
    (hcomps : ∀ M : Subgroup X, CFSG.IsComponent M →
      M = Λ ∨ M = Λ.map (MulAut.conj x).toMonoidHom) :
    x ∉ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
  let H : Subgroup X := normalizer (Λ : Set X)
  have hH : ∀ g, g ∈ H ↔ Λ.map (MulAut.conj g).toMonoidHom = Λ := fun g =>
    Subgroup.mem_normalizer_iff_map_conj_eq
  have hxH : x ∉ H := fun h => hne ((hH x).1 h)
  have hprod : ∀ g h : X, g ∉ H → h ∉ H → g * h ∈ H := by
    intro g h hg hh
    have hΛg : CFSG.IsComponent (Λ.map (MulAut.conj g).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv _ hΛ
    have hΛh : CFSG.IsComponent (Λ.map (MulAut.conj h).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv _ hΛ
    have e_g : Λ.map (MulAut.conj g).toMonoidHom = Λ.map (MulAut.conj x).toMonoidHom :=
      (hcomps _ hΛg).resolve_left (fun h' => hg ((hH g).2 h'))
    have e_h : Λ.map (MulAut.conj h).toMonoidHom = Λ.map (MulAut.conj x).toMonoidHom :=
      (hcomps _ hΛh).resolve_left (fun h' => hh ((hH h).2 h'))
    rw [hH, conj_map_mul, e_h]
    have hc : CFSG.IsComponent ((Λ.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv _ (CFSG.LocalCores.isComponent_map_mulEquiv _ hΛ)
    rcases hcomps _ hc with h1 | h1
    · exact h1
    · exfalso
      apply hne
      have h2 : (Λ.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom =
          Λ.map (MulAut.conj g).toMonoidHom := by rw [h1, e_g]
      have h3 := congrArg (fun T => T.map (MulAut.conj g⁻¹).toMonoidHom) h2
      simpa only [conj_map_cancel] using h3
  have hinv : ∀ g : X, g ∉ H → g⁻¹ ∉ H := fun g hg h => hg (by simpa using H.inv_mem h)
  intro hx
  apply hxH
  have hle : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H
    · exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    · have h1 : b * a⁻¹ ∉ H := fun h => hb (by simpa using H.mul_mem h ha)
      have h3 := hprod _ _ h1 (hinv b hb)
      have : a * b * a⁻¹ * b⁻¹ = a * ((b * a⁻¹) * b⁻¹) := by group
      rw [this]
      exact H.mul_mem ha h3
    · have h1 : a * b ∉ H := fun h => ha (by simpa using H.mul_mem h (H.inv_mem hb))
      have h3 := hprod _ _ h1 (hinv a ha)
      exact H.mul_mem h3 (H.inv_mem hb)
    · have h1 := hprod a b ha hb
      have h2 := hprod a⁻¹ b⁻¹ (hinv a ha) (hinv b hb)
      have : a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) := by group
      rw [this]
      exact H.mul_mem h1 h2
  exact hle hx

theorem exists_min_subnormal (K : Subgroup X) :
    ∃ J : Subgroup X, K ≤ J ∧ J.IsSubnormal ∧
      ∀ J' : Subgroup X, K ≤ J' → J' ≤ J → J'.IsSubnormal → J' = J := by
  let s : Set (Subgroup X) := {J | K ≤ J ∧ J.IsSubnormal}
  have hne : s.Nonempty := ⟨⊤, le_top, Subgroup.normal_top.isSubnormal⟩
  obtain ⟨L, hLs, hmin⟩ := Set.exists_min_image s (fun J => Nat.card J) (Set.toFinite s) hne
  exact ⟨L, hLs.1, hLs.2, fun J hKJ hJL hJs =>
    Subgroup.eq_of_le_of_card_ge hJL (hmin J ⟨hKJ, hJs⟩)⟩

theorem socle_or_swap (hcore : pPrimeCore 2 X = ⊥) {x : X} (hx2 : orderOf x = 2) {K : Subgroup X}
    (hKq : CFSG.IsQuasisimple ↥K) (hKc : IsCompIn (centralizer ({x} : Set X)) K)
    (hterm : IsTerminalSub K) (hKns : ¬ K.IsSubnormal) :
    (∃ Λ : Subgroup X, IsSimpleSocle Λ ⊤ ∧ K ≤ Λ) ∨
    (∃ Λ : Subgroup X, CFSG.IsComponent Λ ∧ Λ.map (MulAut.conj x).toMonoidHom ≠ Λ ∧
      ∀ M : Subgroup X, CFSG.IsComponent M →
        M = Λ ∨ M = Λ.map (MulAut.conj x).toMonoidHom) := by
  have hx1 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx2, pow_two] at h
    exact h
  have hKE : K ≤ CFSG.layer X :=
    CFSG.GH74.E2.component_le_layer_of_balance hcore hx1 (M := centralizer ({x} : Set X))
      (fun m => by rw [mem_centralizer_singleton_iff]) hKc.1 hKc.2
  obtain ⟨J, hKJ, hJ, hmin⟩ := exists_min_subnormal K
  have hne : K ≠ J := fun h => hKns (h ▸ hJ)
  have hno : ∀ b : X, orderOf b = 2 → ¬ J ≤ centralizer ({b} : Set X) :=
    fun b hb => not_le_centralizer_of_minSubnormal hKJ hJ hmin hne hterm hb
  have hJE : J = CFSG.layer X := eq_layer_of_min hKE hKJ hJ hmin hno
  have hno' : ∀ b : X, orderOf b = 2 → ¬ CFSG.layer X ≤ centralizer ({b} : Set X) := by
    rw [← hJE]; exact hno
  have hZ := layer_center_trivial (fitting_eq_bot hcore hno')
  obtain ⟨Λ, hΛ, hKΛ⟩ : ∃ Λ : Subgroup X, CFSG.IsComponent Λ ∧ ∃ k ∈ K, ∃ l ∈ Λ, k * l ≠ l * k := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_quasisimple hKq
    apply hab
    have hle : CFSG.layer X ≤ centralizer ({a} : Set X) := by
      refine sSup_le fun M hM l hl => ?_
      rw [mem_centralizer_singleton_iff]
      exact (hcon M hM a ha l hl).symm
    exact (mem_centralizer_singleton_iff.1 (hle (hKE hb))).symm
  have hKN := le_orbit_prod hx2 hKq hKc hKE hZ hΛ hKΛ
  have hΛ' : CFSG.IsComponent (Λ.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hΛ
  set Λ' : Subgroup X := Λ.map (MulAut.conj x).toMonoidHom with hΛ'def
  have hNJ : Λ ⊔ Λ' ≤ J :=
    sup_le (component_le_of_no_involution hJ hno hΛ) (component_le_of_no_involution hJ hno hΛ')
  have hNE : Λ ⊔ Λ' ≤ CFSG.layer X :=
    sup_le (CFSG.LocalCores.component_le_layer hΛ) (CFSG.LocalCores.component_le_layer hΛ')
  have hEN : CFSG.layer X ≤ normalizer ((Λ ⊔ Λ' : Subgroup X) : Set X) :=
    le_normalizer_sup (layer_le_normalizer hΛ) (layer_le_normalizer hΛ')
  have hEnormal : (CFSG.layer X).Normal := by
    have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hNsub : (Λ ⊔ Λ').IsSubnormal := by
    have hn : ((Λ ⊔ Λ').subgroupOf (CFSG.layer X)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).2 hEN
    exact Subgroup.IsSubnormal.trans hNE hn.isSubnormal hEnormal.isSubnormal
  have hNeq : Λ ⊔ Λ' = J := hmin _ hKN hNJ hNsub
  by_cases hΛx : Λ' = Λ
  · left
    have hJΛ : J = Λ := by rw [← hNeq, hΛx, sup_idem]
    refine ⟨Λ, ?_, ?_⟩
    · refine isSimpleSocle_top_of_component hcore hΛ (fun b hb => ?_)
      rw [← hJΛ]
      exact hno b hb
    · rw [hΛx, sup_idem] at hKN
      exact hKN
  · right
    refine ⟨Λ, hΛ, hΛx, fun M hM => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hMN : M ≤ Λ ⊔ Λ' := hNeq ▸ component_le_of_no_involution hJ hno hM
    have hMC := comp_le_centralizer_sup hΛ hΛ' hM h1 h2
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_quasisimple hM.1
    apply hab
    exact (mem_centralizer_iff.1 (hMC ha) b (hMN hb)).symm


end CFSG.GH74.GLS.C3.Layer1.EndN.Soc
