module

public import CFSG.ClassicalInvolution.Q3.TL4D1ME8C
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

open Matrix
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2D (isPGroup_mem card_mem)

theorem sl3Two_transitive : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), M.1 *ᵥ w = v := by
  decide +kernel

theorem exists_fixed_ne : ∀ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), A * A = 1 →
    ∀ w : Fin 3 → ZMod 2, ∃ v, v ≠ 0 ∧ v ≠ w ∧ A.1 *ᵥ v = v := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem mem_of_e8 (hO2 : TightInO2 t) {E : Subgroup Y} (hE : E8Struct ⊤ E) : t ∈ E := by
  obtain ⟨P, hPn, hP2, htP⟩ := hO2
  exact hE.core P le_top (fun x _ q hq => hPn.conj_mem q hq x) hP2 htP

theorem exists_omegaStar_e8 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {E : Subgroup Y} (hE : E8Struct ⊤ E) :
    ∃ y : Y, y * t * y⁻¹ ≠ t ∧ tightCore R ∈
      omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (conjSub y (tightCore R)) := by
  have hut := hd.isUniqueInvolution_core
  have hK₀ := CoreAssembly.mem_conjClass_self (tightCore R)
  have htE : t ∈ E := mem_of_e8 hO2 hE
  obtain ⟨e, he⟩ := exists_e8Basis hE.sq hE.card
  have htE' : e8Coord e (e8Inv he t) = t := e8Coord_e8Inv he htE
  obtain ⟨q⟩ : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := hc.1
  set j : Y := ((q.symm (QuaternionGroup.a 1) : R) : Y) with hjdef
  have hjK : j ∈ tightCore R := hd.sylow_core.1 ⟨q.symm (.a 1), (q.symm (.a 1)).2, rfl⟩
  have hj4 : orderOf j = 4 := by
    rw [hjdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
      QuaternionGroup.orderOf_a_one]
  have hjj : j * j = t := by
    have hsq : j * j * (j * j) = 1 :=
      calc j * j * (j * j) = j ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := hj4 ▸ pow_orderOf_eq_one j
    have hne : j * j ≠ 1 := fun h => by
      have := orderOf_dvd_of_pow_eq_one (show j ^ 2 = 1 by rw [pow_two, h])
      rw [hj4] at this
      exact absurd this (by norm_num)
    exact (hut.unique _ (mul_mem hjK hjK) hsq).resolve_left hne
  have hAA : e8Hom hE he ⟨j, Subgroup.mem_top j⟩ * e8Hom hE he ⟨j, Subgroup.mem_top j⟩ = 1 := by
    rw [← map_mul, e8Hom_eq_one_iff]
    show j * j ∈ E
    rw [hjj]
    exact htE
  obtain ⟨v, hv0, hvt, hAv⟩ := exists_fixed_ne _ hAA (e8Inv he t)
  set a := e8Coord e v with hadef
  have hja : j * a * j⁻¹ = a := by
    have h1 := conj_e8Coord_e8Hom hE he ⟨j, Subgroup.mem_top j⟩ v
    rw [hAv] at h1
    exact h1
  have hat : a ≠ t := fun h => hvt (e8Coord_injective he (h.trans htE'.symm))
  have hw0 : e8Inv he t ≠ 0 := fun h => hut.ne_one (by rw [← htE', h, e8Coord_zero])
  obtain ⟨M, hM⟩ := sl3Two_transitive v (e8Inv he t) hv0 hw0
  obtain ⟨y, hy⟩ := e8Hom_surjective hE he M
  have hyt : (y : Y) * t * (y : Y)⁻¹ = a := by
    rw [← htE', conj_e8Coord_e8Hom hE he y, hy, hM]
  have hne : tightCore R ≠ conjSub (y : Y) (tightCore R) := fun h => by
    have huKa := hut.conj (y : Y)
    rw [hyt, ← h] at huKa
    exact hat (hut.eq huKa).symm
  have hjN : j ∈ Subgroup.normalizer ((conjSub (y : Y) (tightCore R) : Subgroup Y) : Set Y) := by
    have hja' : j * a = a * j :=
      calc j * a = j * a * j⁻¹ * j := by group
        _ = a * j := by rw [hja]
    have hjc : (y : Y)⁻¹ * j * y ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : Y)⁻¹ * j * y * t = (y : Y)⁻¹ * (j * (y * t * (y : Y)⁻¹)) * y := by group
        _ = (y : Y)⁻¹ * ((y * t * (y : Y)⁻¹) * j) * y := by rw [hyt, hja']
        _ = t * ((y : Y)⁻¹ * j * y) := by group
    rw [mem_normalizer_iff_conjSub_eq]
    have h1 := mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core hjc)
    calc conjSub j (conjSub (y : Y) (tightCore R))
        = conjSub (y : Y) (conjSub ((y : Y)⁻¹ * j * y) (tightCore R)) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub (y : Y) (tightCore R) := by rw [h1]
  have h2K : IsPGroup 2 ↥(tightCore R) := isPGroup_mem hd hc hO2 _ hK₀
  have hU : Subgroup.zpowers j ∈ USet (CoreAssembly.conjClass (tightCore R)) :=
    mem_USet_of_natCard hK₀ ⟨le_rfl, h2K, fun V hV _ hKV => le_antisymm hV hKV⟩
      (Subgroup.zpowers_le.mpr hjK) inferInstance
      (by rw [card_mem hd hc hO2 _ hK₀, Nat.card_zpowers, hj4]; norm_num)
  exact ⟨y, fun h => hat (hyt.symm.trans h), hK₀, hne, Subgroup.zpowers j, hU,
    Subgroup.zpowers_le.mpr hjK, Subgroup.zpowers_le.mpr hjN⟩

theorem exists_omegaStarNbr_of_e8 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {E : Subgroup Y} (hE : E8Struct ⊤ E) :
    ∃ K ∈ CoreAssembly.conjClass (tightCore R),
      (omegaStarNbr (CoreAssembly.conjClass (tightCore R)) K).Nonempty := by
  obtain ⟨y, -, hy⟩ := exists_omegaStar_e8 hd hc hO2 hE
  exact ⟨_, ⟨y, rfl⟩, _, hy⟩

theorem false_of_e8 (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    (hEd : TightEdgeless R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hZ : MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W) {E : Subgroup Y}
    (hE : E8Struct ⊤ E) : False := by
  obtain ⟨e3⟩ := Q3T6.Mu.muIsoS3_of_shape hd.partIHypG hW hEd
    (exists_omegaStarNbr_of_e8 hd hc hO2 hE)
  obtain ⟨e2⟩ := hZ
  have h1 := Nat.card_congr (e3.symm.trans e2).toEquiv
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin] at h1
  exact absurd h1 (by decide)

theorem sl3Two_stab_transitive : ∀ w w' : Fin 3 → ZMod 2, w ≠ 0 → w ≠ Pi.single 0 1 → w' ≠ 0 →
    w' ≠ Pi.single 0 1 → ∃ M : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      M.1 *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ M.1 *ᵥ w = w' := by
  decide +kernel

theorem exists_e8Basis_of_mem {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hsq : ∀ x ∈ E, x * x = 1) (hc : Nat.card E = 8) {a : G} (ha : a ∈ E) (ha1 : a ≠ 1) :
    ∃ e : Fin 3 → G, E8Basis E e ∧ e 0 = a := by
  classical
  obtain ⟨b, hb, hb1⟩ := TL4.exists_mem_not_mem (E := E) {1, a} (by
    rw [hc]; exact lt_of_le_of_lt (Finset.card_le_two) (by norm_num))
  obtain ⟨c, hc', hc1⟩ := TL4.exists_mem_not_mem (E := E) {1, a, b, a * b} (by
    rw [hc]; exact lt_of_le_of_lt (Finset.card_le_four) (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb1 hc1
  refine ⟨![a, b, c], ⟨hsq, hc, fun k => ?_, ha1, hb1, hc1⟩, rfl⟩
  fin_cases k
  · exact ha
  · exact hb
  · exact hc'

theorem dstarConnected_of_e8 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {E : Subgroup Y} (hE : E8Struct ⊤ E) :
    T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) := by
  have hΩ := hd.hypOmegaGen
  have hut := hd.isUniqueInvolution_core
  have hK₀ := CoreAssembly.mem_conjClass_self (tightCore R)
  have htE : t ∈ E := mem_of_e8 hO2 hE
  have hfix : ∀ g : Y, g * t * g⁻¹ = t → conjSub g (tightCore R) = tightCore R := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core
      (Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc g * t = (g * t * g⁻¹) * g := by group
          _ = t * g := by rw [hg])))
  have hconjE : ∀ g : Y, g * t * g⁻¹ ∈ E := fun g => hE.normal g (Subgroup.mem_top g) t htE
  have hne1 : ∀ g : Y, g * t * g⁻¹ ≠ 1 := fun g h => hut.ne_one (by
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this)
  obtain ⟨y, hyt, hedge⟩ := exists_omegaStar_e8 hd hc hO2 hE
  obtain ⟨e, he, he0⟩ := exists_e8Basis_of_mem hE.sq hE.card htE hut.ne_one
  have hte : e8Coord e (Pi.single 0 1) = t := by rw [e8Coord_single, he0]
  have hcoord : ∀ x ∈ E, x ≠ 1 → x ≠ t →
      e8Inv he x ≠ 0 ∧ e8Inv he x ≠ Pi.single 0 1 := fun x hx hx1 hxt =>
    ⟨fun h => hx1 (by rw [← e8Coord_e8Inv he hx, h, e8Coord_zero]),
      fun h => hxt (by rw [← e8Coord_e8Inv he hx, h, hte])⟩
  have hall : ∀ g : Y, conjSub g (tightCore R) ≠ tightCore R →
      tightCore R ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R))
        (conjSub g (tightCore R)) := by
    intro g hg
    have hgt : g * t * g⁻¹ ≠ t := fun h => hg (hfix g h)
    obtain ⟨hw0, hw1⟩ := hcoord _ (hconjE y) (hne1 y) hyt
    obtain ⟨hw0', hw1'⟩ := hcoord _ (hconjE g) (hne1 g) hgt
    obtain ⟨M, hM0, hM⟩ := sl3Two_stab_transitive _ _ hw0 hw1 hw0' hw1'
    obtain ⟨h, hh⟩ := e8Hom_surjective hE he M
    have hht : (h : Y) * t * (h : Y)⁻¹ = t := by
      rw [← hte, conj_e8Coord_e8Hom hE he h, hh, hM0]
    have hhc : (h : Y) * (y * t * y⁻¹) * (h : Y)⁻¹ = g * t * g⁻¹ := by
      rw [← e8Coord_e8Inv he (hconjE y), conj_e8Coord_e8Hom hE he h, hh, hM,
        e8Coord_e8Inv he (hconjE g)]
    have h1 := omegaStarNbr_conj hΩ.conjInvariant hedge (h : Y)
    rw [hfix _ hht, ← conjSub_mul] at h1
    have hhy : conjSub ((h : Y) * y) (tightCore R) = conjSub g (tightCore R) := by
      have h2 : (g⁻¹ * ((h : Y) * y)) * t * (g⁻¹ * ((h : Y) * y))⁻¹ = t := by
        calc (g⁻¹ * ((h : Y) * y)) * t * (g⁻¹ * ((h : Y) * y))⁻¹
            = g⁻¹ * ((h : Y) * (y * t * y⁻¹) * (h : Y)⁻¹) * g := by group
          _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hhc]
          _ = t := by group
      calc conjSub ((h : Y) * y) (tightCore R)
          = conjSub g (conjSub (g⁻¹ * ((h : Y) * y)) (tightCore R)) := by
            rw [← conjSub_mul]
            congr 1
            group
        _ = conjSub g (tightCore R) := by rw [hfix _ h2]
    rwa [hhy] at h1
  have hto : ∀ g : Y, Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R)))
      (tightCore R) (conjSub g (tightCore R)) := fun g => by
    by_cases hg : conjSub g (tightCore R) = tightCore R
    · exact (congrArg (Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R)))
        (tightCore R)) hg).mpr Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨⟨g, rfl⟩, Or.inr (hall g hg)⟩
  have hfrom : ∀ g : Y, Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R)))
      (conjSub g (tightCore R)) (tightCore R) := fun g => by
    by_cases hg : conjSub g (tightCore R) = tightCore R
    · exact (congrArg (fun J => Relation.ReflTransGen
        (dstarAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) hg).mpr
        Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hK₀, Or.inl (hall g hg)⟩
  rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
  exact (hfrom g).trans (hto g')

end CFSG.ClassicalInvolution.Q3.TL4.SecIdE2
