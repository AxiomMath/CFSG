module

public import CFSG.GH74.GLS.C3.Layer1.Th2P615Cfg
public import CFSG.GH74.GLS.C3.Layer2.Final
public import CFSG.GH74.GLS.C3.Layer1.Th2P615

public section

namespace CFSG.GH74.GLS

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Th2

theorem nat_card_centralizer_perm_eleven (σ : Perm (Fin 11)) (hσ : orderOf σ = 2)
    (hn : numMoved σ = 8) : Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 11)))) = 2 ^ 8 * 3 ^ 2 := by
  have hp : (orderOf σ).Prime := by rw [hσ]; exact Nat.prime_two
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [hσ] at hm
  have hsum : σ.cycleType.sum = 8 := by
    rw [Equiv.Perm.sum_cycleType, ← numMoved_eq_card_support, hn]
  rw [hm, Multiset.sum_replicate] at hsum
  have hm3 : m = 3 := by simp at hsum; omega
  subst hm3
  rw [Equiv.Perm.nat_card_centralizer, hm]
  simp [Nat.factorial]

theorem isSolvable_centralizer_alt_eleven (v : alternatingGroup (Fin 11)) (hv : orderOf v = 2)
    (hn : numMoved (v : Perm (Fin 11)) = 8) :
    Group.IsSolvable ↥(centralizer ({v} : Set (alternatingGroup (Fin 11)))) := by
  have hσ : orderOf (v : Perm (Fin 11)) = 2 := by rw [Subgroup.orderOf_coe]; exact hv
  have hsol : Group.IsSolvable ↥(centralizer ({(v : Perm (Fin 11))} : Set (Perm (Fin 11)))) :=
    CFSG.Walter.JT.isSolvable_of_card_eq_two_pow_mul_three_pow
      (nat_card_centralizer_perm_eleven _ hσ hn)
  let f : ↥(centralizer ({v} : Set (alternatingGroup (Fin 11)))) →*
      ↥(centralizer ({(v : Perm (Fin 11))} : Set (Perm (Fin 11)))) :=
    { toFun := fun g => ⟨((g : alternatingGroup (Fin 11)) : Perm (Fin 11)), by
        rw [mem_centralizer_singleton_iff]
        have := mem_centralizer_singleton_iff.1 g.2
        exact congrArg Subtype.val this⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro g h hgh
  have h0 : ((f g : ↥(centralizer ({(v : Perm (Fin 11))} : Set (Perm (Fin 11))))) : Perm (Fin 11)) =
      ((f h : ↥(centralizer ({(v : Perm (Fin 11))} : Set (Perm (Fin 11))))) : Perm (Fin 11)) :=
    congrArg Subtype.val hgh
  exact Subtype.ext (Subtype.ext h0)

theorem isSolvable_centralizer_of_conj {G : Type} [Group G] {u v d : G} (h : d * u * d⁻¹ = v)
    (hv : Group.IsSolvable ↥(centralizer ({v} : Set G))) :
    Group.IsSolvable ↥(centralizer ({u} : Set G)) := by
  let f : ↥(centralizer ({u} : Set G)) →* ↥(centralizer ({v} : Set G)) :=
    { toFun := fun y => ⟨d * (y : G) * d⁻¹, by
        rw [mem_centralizer_singleton_iff, ← h]
        have hy : (y : G) * u = u * (y : G) := mem_centralizer_singleton_iff.1 y.2
        calc d * (y : G) * d⁻¹ * (d * u * d⁻¹) = d * ((y : G) * u) * d⁻¹ := by group
          _ = d * (u * (y : G)) * d⁻¹ := by rw [hy]
          _ = d * u * d⁻¹ * (d * (y : G) * d⁻¹) := by group⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun y z => by apply Subtype.ext; simp [mul_assoc] }
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro y z hyz
  have h1 : d * (y : G) * d⁻¹ = d * (z : G) * d⁻¹ := congrArg Subtype.val hyz
  exact Subtype.ext (by simpa using h1)

section Fus

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem aconfig7_solvable_centralizer
    (hCv : B_L2_Cv) (hG : C3Hyp G) (h : IsAConfig 7 x K T Q S a) :
    ∀ u : G, orderOf u = 2 → (¬ ∃ c : G, c * x * c⁻¹ = u) →
      Group.IsSolvable ↥(centralizer ({u} : Set G)) := by
  intro u hu hux
  have hn : (7 : ℕ) = 6 ∨ (7 : ℕ) = 7 := Or.inr rfl
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four ▸ le_rfl
  obtain ⟨hsimp, hnab, -⟩ := isKProperSimple_iff.1 hG.kproper
  have hnt := h.exists_noncomm hn hG4
  obtain ⟨ι, hι1, hιQ, hιT⟩ := h.exists_equiv_Fgrp_T0 hn hnt
  let c : Coord h := ⟨ι, hι1, hιQ, hιT⟩
  have hW2 := b_L2_W2 G hG 7 x K T Q S a hn h
  have hM := c.modelIso hn hW2
  obtain ⟨Sg, S', φ, hcl, hφ⟩ := fusion_of_modelIso h c hn hsimp hnab hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSgSyl : IsSylowOf 2 (Sg : Subgroup G) ⊤ := by
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top]
    exact Sg.card_eq_multiplicity
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hup : IsPGroup 2 ↥(zpowers u) :=
    (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hu2).isPGroup 2 _
  obtain ⟨g, -, hgW⟩ := Th2.exists_cj_le_of_isSylowOf hSgSyl le_top hup
  have hmem : g * u * g⁻¹ ∈ (Sg : Subgroup G) := by
    refine hgW ((mem_cj_iff g _ _).2 ?_)
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e]
    exact mem_zpowers u
  have hord : orderOf (g * u * g⁻¹) = 2 := by
    rw [CFSG.BenderGlauberman.orderOf_conj_eq]; exact hu
  rcases hcl ⟨g * u * g⁻¹, hmem⟩ (by rw [Subgroup.orderOf_mk]; exact hord) with hx | hv
  · exfalso
    apply hux
    obtain ⟨d, hd⟩ := isConj_iff.1 hx
    refine ⟨g⁻¹ * d⁻¹, ?_⟩
    have hd' : d * (g * u * g⁻¹) * d⁻¹ = x := hd
    calc g⁻¹ * d⁻¹ * x * (g⁻¹ * d⁻¹)⁻¹ = g⁻¹ * (d⁻¹ * x * d) * g := by group
      _ = g⁻¹ * (d⁻¹ * (d * (g * u * g⁻¹) * d⁻¹) * d) * g := by rw [hd']
      _ = u := by group
  · obtain ⟨v', hv'2, hv'8, ⟨e⟩⟩ := hCv G hG 7 x K T Q S a hn h
    have : Group.IsSolvable ↥(centralizer ({v'} : Set (alternatingGroup (Fin 11)))) :=
      isSolvable_centralizer_alt_eleven v' hv'2 hv'8
    have hsolv : Group.IsSolvable ↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    obtain ⟨d, hd⟩ := isConj_iff.1 hv
    refine isSolvable_centralizer_of_conj (d := d * g) ?_ hsolv
    have hd' : d * (g * u * g⁻¹) * d⁻¹ = x * (a * x * a⁻¹) := hd
    rw [← hd']
    group

end Fus

@[expose] def B_prop412a_3b_nt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥(T ⊓ CxK x K) = 4 → T < S → CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K) →
        ¬ IsTerminalPair 2 x K →
        ∀ u : G, orderOf u = 2 → (¬ ∃ c : G, c * x * c⁻¹ = u) →
          Group.IsSolvable ↥(centralizer ({u} : Set G))

theorem b_prop412a_3b_of
    (hc5 : B_thm2_cent5) (hfus : C3.Layer1.Bk.B_L114_fusion57)
    (hfin : C3.Layer1.Bk.B_L114_final57) (hCv : B_L2_Cv) (hnt : B_prop412a_3b_nt) :
    B_prop412a_3b := by
  intro G _ _ hG x y K T S hs h7 hQ4 hTS hQel u hu hux
  by_cases hterm : IsTerminalPair 2 x K
  · obtain ⟨a, h⟩ := hs.exists_aconfig hc5 hfus hfin hG h7 hQ4 hTS hQel hterm
    exact aconfig7_solvable_centralizer hCv hG h u hu hux
  · exact hnt G hG x y K T S hs h7 hQ4 hTS hQel hterm u hu hux

end CFSG.GH74.GLS
