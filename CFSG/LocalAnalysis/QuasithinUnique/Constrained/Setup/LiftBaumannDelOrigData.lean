module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelSpan
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelGen

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization

section Deleted

variable {G : Type} [Group G] [Finite G]

structure DeletedOriginalData (R V : Subgroup G) : Prop where
  l_gen : ∃ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
    autOn (oddOrderSubgroup (⊤ : Subgroup G)) V ≤
        autOn (thompsonJ R ⊔ CFSG.conjugate (thompsonJ R) l) V ∧
      (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer ((CFSG.conjugate (thompsonJ R) l : Subgroup G) :
            Set G)).relIndex V ≤
        (V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)).relIndex V
  baum_eq : autOn (baum R) V = autOn (thompsonJ R) V
  V_span : (⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
      Campbell.cj (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) l) = V
  V_split : V = ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ ⊔
    (V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G))
  J_C : ⁅thompsonJ R, V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)⁆ = ⊥

theorem deleted_original_data
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc)
    (hdel : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V) :
    DeletedOriginalData R V := by
  classical
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  have hF : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hS.card_eq
  have hred := hS.reduced
  have hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hnorm : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS hLc
  have hbridge := even_SL2_original_bridge hS hLc
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  have hbK : autOn L V = oddOrderSubgroup (autOn (⊤ : Subgroup G) V) := hbridge.K_eq
  have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
    rw [hbK]
    exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
  have hdelF : DeletedFamily ((autOn (⊤ : Subgroup G) V).map ψ) n r
      (fun i => (Lc i).map ψ) := by
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdelF, -⟩
    · exfalso
      apply hdel
      have h1 := (himg.natural hnat).2.1.1
      rw [← hKL] at h1
      exact (Subgroup.map_le_map_iff_of_injective (binPsi θ).injective).1 h1
    · exact hdelF
  have ctx := familyCtx_of_layer hS.two_le hF (isCompListIn_map (binPsi θ) hLc)
    hmax.offenders.family.layer
  have common := hmax.offenders.family.common
  obtain ⟨-, hcard, ψi, βi, Ai, h5, hD, hdata⟩ := himg.deleted hdelF
  have hcompat := fun i => (hdata i).1
  have halt := fun i => (hdata i).2.1
  have hAB : ∀ i, Ai i ≤ blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc i).map ψ) :=
    fun i => ((hdata i).2.2.1).trans inf_le_right
  have hAs : ∀ i, ∃ a b c d ω : ℙ F (Fin 2 → F), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ω ≠ a ∧ ω ≠ b ∧ ω ≠ c ∧ ω ≠ d ∧
      ((Ai i).subgroupOf (blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc i).map ψ))).map
          (ψi i).toMonoidHom =
        Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm (ℙ F (Fin 2 → F)))) :=
    fun i => by
      obtain ⟨a, b, c, d, ω, h1, h2, h3, h4, h5', h6, h7, h8, h9, h10, hmap, -⟩ := (hdata i).2.2.2
      exact ⟨a, b, c, d, ω, h1, h2, h3, h4, h5', h6, h7, h8, h9, h10, hmap⟩
  have hAs' : ∀ i, ∃ a b c d : ℙ F (Fin 2 → F), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      ((Ai i).subgroupOf (blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc i).map ψ))).map
          (ψi i).toMonoidHom =
        Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm (ℙ F (Fin 2 → F)))) :=
    fun i => by
      obtain ⟨a, b, c, d, ω, h1, h2, h3, h4, h5', h6, -, -, -, -, hmap⟩ := hAs i
      exact ⟨a, b, c, d, h1, h2, h3, h4, h5', hmap⟩
  obtain ⟨g, hgK, hgen⟩ := deleted_exists_gen_element ctx h5 common ψi Ai halt hAB hAs
  have hgK' : g⁻¹ ∈ (autOn L V).map ψ := by
    rw [hKL, ctx.layer.K_eq]
    exact Subgroup.inv_mem _ hgK
  obtain ⟨φ, hφ, hφg⟩ := hgK'
  obtain ⟨x, hxL, hxφ⟩ := mem_autOn_iff.1 hφ
  have hφg' : binPsi θ φ = g⁻¹ := hφg
  have := hVn
  have hψc : binPsi θ (MulAut.conjNormal (H := V) ((x : G)⁻¹)) = g := by
    have h1 : MulAut.conjNormal (H := V) ((x : G)⁻¹) = φ⁻¹ := by
      rw [map_inv, ← BlueprintB2.conjAct_eq_conjNormal V x, hxφ]
    rw [h1, map_inv, hφg', inv_inv]
  have hconj : (autOn (CFSG.conjugate (thompsonJ R) (x : G)) V).map ψ =
      B6.conjSub g ((autOn (thompsonJ R) V).map ψ) := by
    rw [autOn_conjugate V (thompsonJ R) (x : G), Subgroup.map_map]
    have hcomp : ψ.comp (MulAut.conj (MulAut.conjNormal (H := V) ((x : G)⁻¹))).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp ψ := by
      ext a
      simp [hψ, ← hψc]
    rw [hcomp, ← Subgroup.map_map]
    rfl
  have hF1 : autOn L V ≤ autOn (thompsonJ R ⊔ CFSG.conjugate (thompsonJ R) (x : G)) V := by
    refine (Subgroup.map_le_map_iff_of_injective (f := ψ) (binPsi θ).injective).1 ?_
    have hsup : autOn (thompsonJ R ⊔ CFSG.conjugate (thompsonJ R) (x : G)) V =
        autOn (thompsonJ R) V ⊔ autOn (CFSG.conjugate (thompsonJ R) (x : G)) V := by
      rw [autOn_eq_map_conjNormal, autOn_eq_map_conjNormal, autOn_eq_map_conjNormal,
        Subgroup.map_sup]
    rw [hKL, hsup, Subgroup.map_sup, hconj, ctx.layer.K_eq, hD]
    exact hgen
  have hVW : Nat.card ↥V = Nat.card W := Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)
  have hcardJ : Nat.card ↥(V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) =
      Nat.card ↥(fixGL ((autOn (thompsonJ R) V).map ψ)) := natCard_centralizer_eq θ (hnorm _)
  have hcardJl : Nat.card ↥(V ⊓ Subgroup.centralizer
      ((CFSG.conjugate (thompsonJ R) (x : G) : Subgroup G) : Set G)) =
      Nat.card ↥(fixGL ((autOn (thompsonJ R) V).map ψ)) := by
    rw [natCard_centralizer_eq θ (hnorm _), hconj, fixGL_conjSub]
    exact natCard_map_linearEquiv g _
  have hcardL : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) =
      Nat.card ↥(fixGL (oddGen ((autOn (⊤ : Subgroup G) V).map ψ))) := by
    rw [natCard_centralizer_eq θ (hnorm _), hKL]
  have hKcard := card_V_deleted ctx hdelF
  have hr1 : (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)).relIndex V = 2 ^ (2 * r) := by
    refine relIndex_eq_of_card ?_
    rw [hVW, hcard, hcardJ]
  have hr2 : (V ⊓ Subgroup.centralizer
      ((CFSG.conjugate (thompsonJ R) (x : G) : Subgroup G) : Set G)).relIndex V =
        2 ^ (2 * r) := by
    refine relIndex_eq_of_card ?_
    rw [hVW, hcard, hcardJl]
  have hr3 : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V = 2 ^ (4 * r) := by
    refine relIndex_eq_of_card ?_
    rw [hVW, hKcard, hcardL, mul_comm]
  have hcodim : (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)).relIndex V *
      (V ⊓ Subgroup.centralizer
        ((CFSG.conjugate (thompsonJ R) (x : G) : Subgroup G) : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := by
    rw [hr1, hr2, hr3, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hspan := deleted_span ctx common h5 ψi βi hcompat Ai halt hAB hAs'
  have hVspan : (⨆ l ∈ L, Campbell.cj (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) l) = V := by
    refine vspan_of_dict θ (hnorm (thompsonJ R)) ?_
    rw [hKL, hD]
    exact hspan
  have hsplit : V ≤ ⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) := by
    refine split_of_dict θ (hnorm L) ?_
    rw [hKL]
    exact V_eq_of_ctx ctx
  have hCD : fixGL (oddGen ((autOn (⊤ : Subgroup G) V).map ψ)) ≤
      fixGL ((autOn (thompsonJ R) V).map ψ) := by
    rw [hD]
    exact deleted_fixGL_le common hAB
  have hJC : ∀ j ∈ thompsonJ R, ∀ c ∈ V ⊓ Subgroup.centralizer (L : Set G), j * c = c * j := by
    intro j hj c hc
    have h1 : vecOf θ ⟨c, hc.1⟩ ∈ fixGL (oddGen ((autOn (⊤ : Subgroup G) V).map ψ)) := by
      rw [← hKL]
      exact (mem_fixGL_map_autOn_iff θ (hnorm L) ⟨c, hc.1⟩).2 fun a ha =>
        Subgroup.mem_centralizer_iff.1 hc.2 a ha
    exact (mem_fixGL_map_autOn_iff θ (hnorm (thompsonJ R)) ⟨c, hc.1⟩).1 (hCD h1) j hj
  refine ⟨⟨(x : G), hxL, hF1, hcodim⟩, ?_, hVspan, ?_, ?_⟩
  · exact Subgroup.map_injective (f := ψ) (binPsi θ).injective himg.baumann_eq.symm
  · refine le_antisymm hsplit ?_
    refine sup_le (Subgroup.commutator_le.2 fun v hv l _ => ?_) inf_le_left
    have h1 : (l : G) * v⁻¹ * l⁻¹ ∈ V := hVn.conj_mem _ (V.inv_mem hv) l
    have h2 := V.mul_mem hv h1
    simpa [commutatorElement_def, mul_assoc] using h2
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun j hj =>
      Subgroup.mem_centralizer_iff.2 fun c hc => (hJC j hj c hc).symm

end Deleted

end CFSG.QuasithinUnique.Setup.Lift
