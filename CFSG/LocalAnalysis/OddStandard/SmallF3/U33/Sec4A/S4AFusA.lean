module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma mul_self_eq_one_of_mem_closure (h : Ctx0 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ closure {t, (x₁ * x₂) ^ 2}) : g * g = 1 := by
  rcases mem_closure_t_z h hg with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact t_mul_self h.hyp
  · exact (z_mul_self_ne_one h).1
  · have hcomm : Commute t ((x₁ * x₂) ^ 2) := t_commute_z h
    have ht2 : t ^ 2 = 1 := by rw [pow_two, t_mul_self h.hyp]
    have hz2 : ((x₁ * x₂) ^ 2) ^ 2 = 1 := by rw [pow_two, (z_mul_self_ne_one h).1]
    calc t * (x₁ * x₂) ^ 2 * (t * (x₁ * x₂) ^ 2) = (t * (x₁ * x₂) ^ 2) ^ 2 :=
          (pow_two _).symm
      _ = t ^ 2 * ((x₁ * x₂) ^ 2) ^ 2 := hcomm.mul_pow 2
      _ = 1 := by rw [ht2, hz2, mul_one]

private lemma conj_t_eq_t_or_t_mul_z (h : Ctx t L S x₁ x₂ lam rho tau) {m : G}
    (hm : m ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G)) :
    m * t * m⁻¹ = t ∨ m * t * m⁻¹ = t * (x₁ * x₂) ^ 2 := by
  have hz := normalizer_fixes_z h.toCtx0 hm
  have hmt : m * t * m⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} :=
    ((Subgroup.mem_set_normalizer_iff).mp hm t).mp (Subgroup.subset_closure (by simp))
  rcases mem_closure_t_z h.toCtx0 hmt with h1 | h1 | h1 | h1
  · exfalso
    have ht1 : t = 1 := by
      calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
    exact t_ne_one h.hyp ht1
  · exact Or.inl h1
  · exfalso
    have htz : t = (x₁ * x₂) ^ 2 := by
      calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
        _ = m⁻¹ * (m * (x₁ * x₂) ^ 2 * m⁻¹) * m := by rw [h1, hz]
        _ = (x₁ * x₂) ^ 2 := by group
    exact t_not_mem_L h.hyp (htz ▸ (y_z_mem_L h.toCtx0).2)
  · exact Or.inr h1

theorem normalizer_S_le_normalizer_E (h : Ctx t L S x₁ x₂ lam rho tau) {n : G}
    (hn : n ∈ normalizer (S : Set G)) :
    n ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro g hg
  have hgS : g ∈ S := (Subgroup.mem_inf.mp (h.center_ge hg)).1
  have hgC : g ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.mem_inf.mp (h.center_ge hg)).2
  have hgnS : n * g * n⁻¹ ∈ S :=
    ((Subgroup.mem_set_normalizer_iff).mp hn g).mp hgS
  have hmemC : n * g * n⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S :=
      ((Subgroup.mem_set_normalizer_iff'').mp hn s).mp hs
    have hcomm : (n⁻¹ * s * n) * g = g * (n⁻¹ * s * n) :=
      Subgroup.mem_centralizer_iff.mp hgC (n⁻¹ * s * n) hs'
    calc s * (n * g * n⁻¹) = n * (n⁻¹ * s * n) * g * n⁻¹ := by group
      _ = n * ((n⁻¹ * s * n) * g) * n⁻¹ := by group
      _ = n * (g * (n⁻¹ * s * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * g * n⁻¹) * s := by group
  have hsq : (n * g * n⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc (n * g * n⁻¹) * (n * g * n⁻¹) = n * (g * g) * n⁻¹ := by group
      _ = 1 := by rw [mul_self_eq_one_of_mem_closure h.toCtx0 hg]; group
  exact h.center_omega (n * g * n⁻¹) ⟨hgnS, hmemC⟩ hsq

theorem normalizer_E_fixes_t (h : Ctx t L S x₁ x₂ lam rho tau) (hS : ¬ 2 ∣ S.index) {n : G}
    (hn : n ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G)) :
    n * t * n⁻¹ = t := by
  let E : Subgroup G := closure {t, (x₁ * x₂) ^ 2}
  let N : Subgroup G := normalizer (E : Set G)
  let C : Subgroup G := N ⊓ invCent t
  have hnN : n ∈ N := hn
  have hSN : S ≤ N := by
    intro s hs
    change s ∈ normalizer (E : Set G)
    apply mem_normalizer_of_conj_mem
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (S : Set G) :=
      (Subgroup.mem_inf.mp (h.center_ge hg)).2
    have hcomm : g * s = s * g :=
      (Subgroup.mem_centralizer_iff.mp hgC s hs).symm
    have hconj : s * g * s⁻¹ = g := by
      calc s * g * s⁻¹ = g * s * s⁻¹ := by rw [hcomm]
        _ = g := by group
    rw [hconj]
    exact hg
  have hSC : S ≤ C := fun s hs => ⟨hSN hs, h.le_invCent hs⟩
  have h2 : C.relIndex N ≤ 2 := by
    by_cases hall : ∀ m ∈ N, m * t * m⁻¹ = t
    · have hNC : N ≤ C := by
        intro m hm
        refine ⟨hm, ?_⟩
        refine mem_invCent_iff.mpr ?_
        have hm' := hall m hm
        calc m * t = (m * t * m⁻¹) * m := by group
          _ = t * m := by rw [hm']
      have hEq : C = N := le_antisymm inf_le_left hNC
      rw [hEq]
      simp
    · obtain ⟨a, haN, hane⟩ : ∃ a ∈ N, a * t * a⁻¹ ≠ t := by
        by_contra hcon
        apply hall
        intro m hm
        by_contra hmt
        exact hcon ⟨m, hm, hmt⟩
      have hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2 :=
        (conj_t_eq_t_or_t_mul_z h haN).resolve_left hane
      have hz : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 :=
        (z_mul_self_ne_one h.toCtx0).1
      have ha_inv_z : a⁻¹ * (x₁ * x₂) ^ 2 * a = (x₁ * x₂) ^ 2 := by
        simpa using normalizer_fixes_z h.toCtx0 (N.inv_mem haN)
      have ha_inv_t : a⁻¹ * t * a = t * (x₁ * x₂) ^ 2 := by
        have h1 : t = (a⁻¹ * t * a) * (x₁ * x₂) ^ 2 := by
          calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
            _ = a⁻¹ * (t * (x₁ * x₂) ^ 2) * a := by rw [hat]
            _ = (a⁻¹ * t * a) * (a⁻¹ * (x₁ * x₂) ^ 2 * a) := by group
            _ = (a⁻¹ * t * a) * (x₁ * x₂) ^ 2 := by rw [ha_inv_z]
        calc a⁻¹ * t * a
            = (a⁻¹ * t * a) * ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2) := by rw [hz, mul_one]
          _ = ((a⁻¹ * t * a) * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by group
          _ = t * (x₁ * x₂) ^ 2 := by rw [← h1]
      have hcover : ∀ m ∈ N, m ∈ C ∨ a⁻¹ * m ∈ C := by
        intro m hm
        rcases conj_t_eq_t_or_t_mul_z h hm with hmt | hmt
        · left
          refine ⟨hm, ?_⟩
          refine mem_invCent_iff.mpr ?_
          calc m * t = (m * t * m⁻¹) * m := by group
            _ = t * m := by rw [hmt]
        · right
          refine ⟨N.mul_mem (N.inv_mem haN) hm, ?_⟩
          refine mem_invCent_iff.mpr ?_
          have hconj : (a⁻¹ * m) * t * (a⁻¹ * m)⁻¹ = t := by
            calc (a⁻¹ * m) * t * (a⁻¹ * m)⁻¹
                = a⁻¹ * (m * t * m⁻¹) * a := by group
              _ = a⁻¹ * (t * (x₁ * x₂) ^ 2) * a := by rw [hmt]
              _ = (a⁻¹ * t * a) * (a⁻¹ * (x₁ * x₂) ^ 2 * a) := by group
              _ = (t * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by rw [ha_inv_t, ha_inv_z]
              _ = t := by rw [mul_assoc, hz, mul_one]
          calc (a⁻¹ * m) * t = ((a⁻¹ * m) * t * (a⁻¹ * m)⁻¹) * (a⁻¹ * m) := by group
            _ = t * (a⁻¹ * m) := by rw [hconj]
      exact relIndex_le_two_of_forall (N := N) (C := C) inf_le_left a haN hcover
  have hSodd : ¬ 2 ∣ S.relIndex N := by
    intro h2dvd
    apply hS
    rw [← Subgroup.relIndex_mul_index hSN]
    exact dvd_mul_of_dvd_left h2dvd N.index
  have hEq : C = N := eq_of_relIndex_le_two_of_odd (N := N) (C := C) (S := S)
    inf_le_left hSC hSodd h2
  have hnC : n ∈ C := by rw [hEq]; exact hnN
  have hnt : n * t = t * n := mem_invCent_iff.mp hnC.2
  calc n * t * n⁻¹ = t * n * n⁻¹ := by rw [hnt]
    _ = t := by group

theorem E_fusion_free (h : Ctx t L S x₁ x₂ lam rho tau) (hS : ¬ 2 ∣ S.index) {x g : G}
    (hx : x ∈ closure {t, (x₁ * x₂) ^ 2}) (hg : g⁻¹ * x * g ∈ closure {t, (x₁ * x₂) ^ 2}) :
    g⁻¹ * x * g = x := by
  let E : Subgroup G := closure {t, (x₁ * x₂) ^ 2}
  have hxE : x ∈ E := hx
  have hgE : g⁻¹ * x * g ∈ E := hg
  have hxC : x ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.mem_inf.mp (h.center_ge hxE)).2
  have hgC : g⁻¹ * x * g ∈ Subgroup.centralizer (S : Set G) :=
    (Subgroup.mem_inf.mp (h.center_ge hgE)).2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sy, hSy⟩ := exists_sylow_coe_eq (S := S) h.isPGroup hS
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex Sy
  have hSySet : (Sy : Set G) = (S : Set G) := by
    show ((Sy : Subgroup G) : Set G) = (S : Set G)
    rw [hSy]
  have hxSy : x ∈ Subgroup.centralizer (Sy : Set G) := by
    rw [hSySet]
    exact hxC
  have hgSy : g⁻¹ * x * g ∈ Subgroup.centralizer (Sy : Set G) := by
    rw [hSySet]
    exact hgC
  obtain ⟨n, hnN, hnconj⟩ :=
    Sy.conj_eq_normalizer_conj_of_mem_centralizer x g hxSy hgSy
  have hnN_S : n ∈ normalizer (S : Set G) := by
    rw [← hSySet]
    exact hnN
  have hninv_S : n⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hnN_S
  have hninv_E : n⁻¹ ∈ normalizer (E : Set G) := by
    simpa [E] using normalizer_S_le_normalizer_E h hninv_S
  have ht_fix : n⁻¹ * t * n = t := by
    simpa [E] using normalizer_E_fixes_t h hS hninv_E
  have hz_fix : n⁻¹ * (x₁ * x₂) ^ 2 * n = (x₁ * x₂) ^ 2 := by
    simpa [E] using normalizer_fixes_z h.toCtx0 hninv_E
  have hfix : n⁻¹ * x * n = x := by
    rcases mem_closure_t_z h.toCtx0 hxE with h1 | h1 | h1 | h1
    · rw [h1]; group
    · rw [h1]; exact ht_fix
    · rw [h1]; exact hz_fix
    · rw [h1]
      calc n⁻¹ * (t * (x₁ * x₂) ^ 2) * n
          = (n⁻¹ * t * n) * (n⁻¹ * (x₁ * x₂) ^ 2 * n) := by group
        _ = t * (x₁ * x₂) ^ 2 := by rw [ht_fix, hz_fix]
  calc g⁻¹ * x * g = n⁻¹ * x * n := hnconj
    _ = x := hfix

theorem not_conj_t_z (h : Ctx t L S x₁ x₂ lam rho tau) (hS : ¬ 2 ∣ S.index) (g : G) :
    g * t * g⁻¹ ≠ (x₁ * x₂) ^ 2 := by
  intro hconj
  have hxE : t ∈ closure {t, (x₁ * x₂) ^ 2} := Subgroup.subset_closure (by simp)
  have hgE : (g⁻¹)⁻¹ * t * g⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} := by
    rw [inv_inv, hconj]
    exact Subgroup.subset_closure (by simp)
  have hfus := E_fusion_free h hS hxE hgE
  rw [inv_inv] at hfus
  have ht : (x₁ * x₂) ^ 2 = t := by rw [← hconj, hfus]
  exact t_not_mem_L h.hyp (ht ▸ (y_z_mem_L h.toCtx0).2)

theorem not_conj_t_tz (h : Ctx t L S x₁ x₂ lam rho tau) (hS : ¬ 2 ∣ S.index) (g : G) :
    g * t * g⁻¹ ≠ t * (x₁ * x₂) ^ 2 := by
  intro hconj
  have hxE : t ∈ closure {t, (x₁ * x₂) ^ 2} := Subgroup.subset_closure (by simp)
  have hgE : (g⁻¹)⁻¹ * t * g⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} := by
    rw [inv_inv, hconj]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hfus := E_fusion_free h hS hxE hgE
  rw [inv_inv] at hfus
  have hzt : t * (x₁ * x₂) ^ 2 = t := hconj.symm.trans hfus
  have hz1 : (x₁ * x₂) ^ 2 = 1 := by
    have h' := congrArg (fun u => t⁻¹ * u) hzt
    simpa using h'
  exact (z_mul_self_ne_one h.toCtx0).2 hz1

theorem not_conj_z_tz (h : Ctx t L S x₁ x₂ lam rho tau) (hS : ¬ 2 ∣ S.index) (g : G) :
    g * (x₁ * x₂) ^ 2 * g⁻¹ ≠ t * (x₁ * x₂) ^ 2 := by
  intro hconj
  have hxE : (x₁ * x₂) ^ 2 ∈ closure {t, (x₁ * x₂) ^ 2} :=
    Subgroup.subset_closure (by simp)
  have hgE : (g⁻¹)⁻¹ * (x₁ * x₂) ^ 2 * g⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} := by
    rw [inv_inv, hconj]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hfus := E_fusion_free h hS hxE hgE
  rw [inv_inv] at hfus
  have hzt : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 := hconj.symm.trans hfus
  have ht1 : t = 1 := by
    have h' := congrArg (fun u => u * ((x₁ * x₂) ^ 2)⁻¹) hzt
    simpa using h'
  exact t_ne_one h.hyp ht1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
