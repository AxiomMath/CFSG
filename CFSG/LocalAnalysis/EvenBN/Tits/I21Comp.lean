module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Toolbox
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Comp

open Subgroup CFSG.Open

theorem pPrimeCore_eq_bot {G : Type*} [Group G] (hO : standardComponentOddCore G = ⊥) :
    CFSG.pPrimeCore 2 G = ⊥ := by
  rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore]
  exact hO

section Counting

theorem exists_fixed_involution {K : Type*} [Group K] [Finite K] (α : K →* K)
    (hα : ∀ x, α (α x) = x) (heven : 2 ∣ Nat.card K) :
    ∃ i : K, i ≠ 1 ∧ i ^ 2 = 1 ∧ α i = i := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let f : Function.End K := ⇑α
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext x
    exact hα x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  let H : Subgroup K := MonoidHom.eqLocus α (MonoidHom.id K)
  have h2 : 2 ∣ Nat.card H := by
    have hH : Nat.card H = Nat.card f.fixedPoints :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
    rw [hH]
    exact (Nat.ModEq.dvd_iff hmod (dvd_refl 2)).mp heven
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have hs' : orderOf (s : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hs
  refine ⟨s, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hs'
    omega
  · rw [← hs']
    exact pow_orderOf_eq_one _
  · exact s.2

end Counting

section Invariance

variable {G : Type*} [Group G] {t : G}

theorem false_of_commute_conj {K : Subgroup G} [Nontrivial K] [Group.IsPerfect K]
    (ht : t * t = 1) (hsol : Group.IsSolvable (centralizer ({t} : Set G)))
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥) : False := by
  set K' := K.map (MulAut.conj t).toMonoidHom
  have hcent : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    have h1 : a ∈ centralizer (K' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha
    exact ((Subgroup.mem_centralizer_iff.mp h1) b hb).symm
  have hmem : ∀ l ∈ K, t * l * t⁻¹ ∈ K' := fun l hl => ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨φ, hφ⟩ : ∃ φ : K →* G, ∀ l : K, φ l = (l : G) * (t * (l : G) * t⁻¹) := by
    refine ⟨MonoidHom.mk' (fun l : K => (l : G) * (t * (l : G) * t⁻¹)) ?_, fun l => rfl⟩
    intro a b
    have h1 : (b : G) * (t * (a : G) * t⁻¹) = (t * (a : G) * t⁻¹) * b :=
      hcent b b.2 _ (hmem a a.2)
    calc ((a * b : K) : G) * (t * ((a * b : K) : G) * t⁻¹)
        = (a : G) * ((b : G) * (t * (a : G) * t⁻¹)) * (t * (b : G) * t⁻¹) := by
          change (a : G) * b * (t * ((a : G) * b) * t⁻¹) = _
          group
      _ = (a : G) * ((t * (a : G) * t⁻¹) * b) * (t * (b : G) * t⁻¹) := by rw [h1]
      _ = (a : G) * (t * (a : G) * t⁻¹) * ((b : G) * (t * (b : G) * t⁻¹)) := by
          simp only [mul_assoc]
  have hφC : ∀ l : K, φ l ∈ centralizer ({t} : Set G) := by
    intro l
    have hm := hmem l l.2
    have e1 : t * (t * (l : G) * t⁻¹) * t⁻¹ = l := by
      rw [ht']
      calc t * (t * (l : G) * t) * t = (t * t) * l * (t * t) := by simp only [mul_assoc]
        _ = l := by rw [ht, one_mul, mul_one]
    have e2 : t * ((l : G) * (t * l * t⁻¹)) * t⁻¹ = (l : G) * (t * l * t⁻¹) := by
      calc t * ((l : G) * (t * l * t⁻¹)) * t⁻¹
          = (t * (l : G) * t⁻¹) * (t * (t * l * t⁻¹) * t⁻¹) := by group
        _ = (t * (l : G) * t⁻¹) * l := by rw [e1]
        _ = (l : G) * (t * l * t⁻¹) := (hcent l l.2 _ hm).symm
    rw [hφ, Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp e2).symm
  let φ' : K →* centralizer ({t} : Set G) := φ.codRestrict _ hφC
  have hker : φ'.ker ≤ (center K).subtype.range := by
    intro l hl
    rw [Subgroup.range_subtype]
    have h1 : φ l = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
      simpa [φ'] using this
    rw [hφ] at h1
    have hlK' : (l : G) ∈ K' := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact K'.inv_mem (hmem l l.2)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent g g.2 l hlK')
  haveI : Group.IsSolvable (center K) := inferInstance
  haveI := hsol
  exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_ker_le_range _ φ' hker)

end Invariance

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Comp

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_layer_ne_bot (h : Sec622Bar G t u x)
    (hnc : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 Q → ¬ centralizer (Q : Set G) ≤ Q) :
    CFSG.layer G ≠ ⊥ := by
  intro hlayer
  have hcore : CFSG.pPrimeCore 2 G = ⊥ := I21.Comp.pPrimeCore_eq_bot h.oddCore
  exact hnc (CFSG.pCore 2 G) CFSG.pCore_normal CFSG.pCore_isPGroup
    (CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot G 2 hcore hlayer)

theorem sec622_component_t_invariant (h : Sec622Bar G t u x) {K : Subgroup G}
    (hK : CFSG.IsComponent K) : K.map (MulAut.conj t).toMonoidHom = K := by
  have hK' : CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with heq | hcomm
  · exact heq.symm
  · exfalso
    haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    haveI : Group.IsPerfect K := hK.1.1
    exact I21.Comp.false_of_commute_conj h.secTwo.t_mul_t (sec622_centralizer_solvable h) hcomm

theorem sec622_component_contains_zj (h : Sec622Bar G t u x)
    (hN : ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N)
    (hfus : ∀ j : ℕ, ∃ g : G, g * t * g⁻¹ = t * (x ^ j * u ^ 2)) {K : Subgroup G}
    (hK : CFSG.IsComponent K) (htK : K.map (MulAut.conj t).toMonoidHom = K) :
    ∃ j : ℕ, x ^ j * u ^ 2 ∈ K := by
  obtain ⟨N, hNn, hNi, htN⟩ := hN
  have hKN : K ≤ N := sec622_le_of_perfect hNn hNi hK.1.1
  haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have hpp : CFSG.pPrimeCore 2 G = ⊥ := I21.Comp.pPrimeCore_eq_bot h.oddCore
  have heven : 2 ∣ Nat.card K := by
    by_contra hnd
    have hodd : Odd (Nat.card K) := Nat.odd_iff.mpr (by omega)
    exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance
      (CFSG.Walter.eq_bot_of_isSubnormal_of_odd hpp hK.2 hodd)
  have ht1 : t * t = 1 := h.secTwo.t_mul_t
  have hconj : ∀ l : G, l ∈ K → t * l * t⁻¹ ∈ K := fun l hl => by
    have := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hl
    rw [htK] at this
    simpa [MulAut.conj_apply] using this
  let α : K →* K := MonoidHom.mk' (fun l => ⟨t * (l : G) * t⁻¹, hconj l l.2⟩) (by
    intro a b
    apply Subtype.ext
    change t * ((a : G) * b) * t⁻¹ = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹)
    group)
  have hα : ∀ l, α (α l) = l := by
    intro l
    apply Subtype.ext
    change t * (t * (l : G) * t⁻¹) * t⁻¹ = l
    rw [inv_eq_of_mul_eq_one_right ht1]
    calc t * (t * (l : G) * t) * t = (t * t) * l * (t * t) := by simp only [mul_assoc]
      _ = l := by rw [ht1, one_mul, mul_one]
  obtain ⟨i, hi1, hi2, hiα⟩ := I21.Comp.exists_fixed_involution α hα heven
  have hit : t * (i : G) * t⁻¹ = i := congrArg Subtype.val hiα
  have hiC : (i : G) ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hit).symm
  have hi1' : (i : G) ≠ 1 := fun h1 => hi1 (Subtype.ext h1)
  have hi2' : (i : G) ^ 2 = 1 := congrArg Subtype.val hi2
  rcases sec622_involutions_centralizer h hiC hi1' hi2' with hi | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact absurd (hi ▸ hKN i.2) htN
  · exact ⟨j, hj ▸ i.2⟩
  · exfalso
    obtain ⟨g, hg⟩ := hfus j
    have hgN : g * t * g⁻¹ ∈ N := by
      rw [hg, ← hj]
      exact hKN i.2
    have h1 := hNn.conj_mem _ hgN g⁻¹
    have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
    rw [e] at h1
    exact htN h1

end CFSG.LocalAnalysis.EvenBN.Tits
