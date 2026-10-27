module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecClq

open Matrix
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (E8Struct)
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem mem_omegaNbr_core_of_e8 (hd : TightDatum R S t) (hO2 : TightInO2 t) {E : Subgroup Y}
    (hE : E8Struct ⊤ E) {y : Y}
    (hedge : conjSub y (tightCore R) ∈ omegaNbr (CoreAssembly.conjClass (tightCore R))
      (tightCore R)) {g : Y} (hg : conjSub g (tightCore R) ≠ tightCore R) :
    conjSub g (tightCore R) ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  have hΩ := hd.hypOmegaGen
  have hut := hd.isUniqueInvolution_core
  have htE : t ∈ E := SecIdE2.mem_of_e8 hO2 hE
  have hfix : ∀ x : Y, x * t * x⁻¹ = t → conjSub x (tightCore R) = tightCore R := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core
      (Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc x * t = (x * t * x⁻¹) * x := by group
          _ = t * x := by rw [hx])))
  have hconjE : ∀ x : Y, x * t * x⁻¹ ∈ E := fun x => hE.normal x (Subgroup.mem_top x) t htE
  have hne1 : ∀ x : Y, x * t * x⁻¹ ≠ 1 := fun x h => hut.ne_one (by
    have := congrArg (fun w => x⁻¹ * w * x) h
    simpa [mul_assoc] using this)
  have hyt : y * t * y⁻¹ ≠ t := fun h => hedge.2.1 (hfix y h)
  have hgt : g * t * g⁻¹ ≠ t := fun h => hg (hfix g h)
  obtain ⟨e, he, he0⟩ := SecIdE2.exists_e8Basis_of_mem hE.sq hE.card htE hut.ne_one
  have hte : e8Coord e (Pi.single 0 1) = t := by rw [e8Coord_single, he0]
  have hcoord : ∀ x ∈ E, x ≠ 1 → x ≠ t →
      e8Inv he x ≠ 0 ∧ e8Inv he x ≠ Pi.single 0 1 := fun x hx hx1 hxt =>
    ⟨fun h => hx1 (by rw [← e8Coord_e8Inv he hx, h, e8Coord_zero]),
      fun h => hxt (by rw [← e8Coord_e8Inv he hx, h, hte])⟩
  obtain ⟨hw0, hw1⟩ := hcoord _ (hconjE y) (hne1 y) hyt
  obtain ⟨hw0', hw1'⟩ := hcoord _ (hconjE g) (hne1 g) hgt
  obtain ⟨M, hM0, hM⟩ := SecIdE2.sl3Two_stab_transitive _ _ hw0 hw1 hw0' hw1'
  obtain ⟨h, hh⟩ := e8Hom_surjective hE he M
  have hht : (h : Y) * t * (h : Y)⁻¹ = t := by
    rw [← hte, conj_e8Coord_e8Hom hE he h, hh, hM0]
  have hhc : (h : Y) * (y * t * y⁻¹) * (h : Y)⁻¹ = g * t * g⁻¹ := by
    rw [← e8Coord_e8Inv he (hconjE y), conj_e8Coord_e8Hom hE he h, hh, hM,
      e8Coord_e8Inv he (hconjE g)]
  have h1 := omegaNbr_conj hΩ.conjInvariant hedge (h : Y)
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

theorem dConnected_of_e8_edge (hd : TightDatum R S t) (hO2 : TightInO2 t) {E : Subgroup Y}
    (hE : E8Struct ⊤ E) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    DConnected (CoreAssembly.conjClass (tightCore R)) := by
  have hK₀ := CoreAssembly.mem_conjClass_self (tightCore R)
  obtain ⟨y, rfl⟩ := hJ.1
  have hto : ∀ g : Y, Relation.ReflTransGen
      (fun M N => N ∈ CoreAssembly.conjClass (tightCore R) ∧
        dAdj (CoreAssembly.conjClass (tightCore R)) M N) (tightCore R)
      (conjSub g (tightCore R)) := fun g => by
    by_cases hg : conjSub g (tightCore R) = tightCore R
    · rw [hg]
    · exact Relation.ReflTransGen.single
        ⟨⟨g, rfl⟩, Or.inl (mem_omegaNbr_core_of_e8 hd hO2 hE hJ hg)⟩
  have hfrom : ∀ g : Y, Relation.ReflTransGen
      (fun M N => N ∈ CoreAssembly.conjClass (tightCore R) ∧
        dAdj (CoreAssembly.conjClass (tightCore R)) M N) (conjSub g (tightCore R))
      (tightCore R) := fun g => by
    by_cases hg : conjSub g (tightCore R) = tightCore R
    · rw [hg]
    · exact Relation.ReflTransGen.single
        ⟨hK₀, Or.inr (mem_omegaNbr_core_of_e8 hd hO2 hE hJ hg)⟩
  rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
  exact (hfrom g).trans (hto g')

end CFSG.ClassicalInvolution.Q3.TL4.SecClq
