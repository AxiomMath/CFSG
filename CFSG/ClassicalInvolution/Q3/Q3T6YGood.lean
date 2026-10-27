module

public import CFSG.ClassicalInvolution.Q3.Q3T6YOut
public import CFSG.ClassicalInvolution.Q3.Q3T6YXSide
public import CFSG.ClassicalInvolution.Q3.Q3T6BLAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
  CFSG.ClassicalInvolution.Q3.Q3T6X
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

section Good

variable {X Y : Subgroup F} {x y : F} {R : Subgroup F}

theorem exists_good_member' (hs : Swap X x y) (hR : SwapSylow X y R) (hY : Mem3 Y y)
    (hxY : x ∈ Subgroup.normalizer (Y : Set F))
    (hout : ∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a) {e f : F} (he : e ∈ R ⊓ X) (hf : f ∈ R ⊓ X)
    (he2 : e * e = x) (hf2 : f * f = x) (hfe : f * e * f⁻¹ = e⁻¹) :
    ∃ Y' : Subgroup F, Mem3 Y' y ∧ x ∈ Subgroup.normalizer (Y' : Set F) ∧
      (∀ a ∈ Y', orderOf a = 4 → a * x ≠ x * a) ∧ ∀ k ∈ Y', ⁅diag y e, k⁆ ∈ oddCoreOf Y' := by
  classical
  have hX := hs.member
  have hx2 : x * x = 1 := hX.mul_self
  have hnt : ¬ ∀ j ∈ Y, ⁅x, j⁆ ∈ oddCoreOf Y := fun htriv => by
    obtain ⟨a, haY, ha4, hax⟩ := exists_comm_order_four_of_trivial hY hxY hx2 htriv
    exact hout a haY ha4 hax
  set K : Subgroup F := deltaStar X y with hKdef
  have hKle : K ≤ swapFix X y := oddClosure_le _
  have htK : ∀ k ∈ K, k * y = y * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKle hk).2
  have hzK : ∀ k ∈ K, k * x = x * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (deltaStar_le_Cz hs hk)
  have hδK : ∀ q ∈ R ⊓ X, diag y q ∈ K := fun q hq =>
    diag_mem_deltaStar hs hq.2 (hR.comm_conj hq)
  have hδ2 : ∀ q ∈ R ⊓ X, q * q = x → diag y q * diag y q = 1 := fun q hq hq2 =>
    diag_mul_self hx2 hs.comm hq2 (hR.comm_conj hq)
  have hδx : ∀ q ∈ R ⊓ X, diag y q * x = x * diag y q := fun q hq =>
    (diag_comm_x (hX.mul_comm_of_mem hq.2)
      (hs.twin.mul_comm_of_mem (conj_mem_conjSub hq.2))).symm
  have hδ1 : ∀ q ∈ R ⊓ X, q * q = x → diag y q ≠ 1 := fun q hq hq2 =>
    (SwapSylow.diag_ne hs hR hq hq2).1
  rcases abstract_dichotomy' (K := K) hY hx2 hxY hnt htK hzK (oddClosure_le_closure_odd _)
      (isSubnormal_deltaStar hs) with hI | ⟨d, hdK, hd1, hd2, hdA⟩
  · exact ⟨Y, hY, hxY, hout, fun k hk => (hI _ (hδK e he)).2 k hk⟩
  · obtain ⟨eY⟩ := Q3T6.nonempty_equiv_of_memberU hY.member
    have hKA : K ≤ Subgroup.normalizer
        ((twinProd K Y ⊓ Subgroup.centralizer ({x} : Set F) : Subgroup F) : Set F) :=
      le_normalizer_twinProd_inf_centralizer hzK
    have hP : ∀ q ∈ R ⊓ X, q * q = x → diag y q ∈ twinProd K Y := by
      intro q hq hq2
      obtain ⟨c, hcK, k, hkK, hck⟩ :=
        exists_conj_diag_involution hs hdK hd2 hd1 hq.2 hq2 (hR.comm_conj hq)
      have hkd : k * d * k⁻¹ ∈ twinProd K Y ⊓ Subgroup.centralizer ({x} : Set F) :=
        (Subgroup.mem_normalizer_iff.mp (hKA hkK) d).mp hdA
      have hcd : c * (k * d * k⁻¹) * c⁻¹ ∈
          twinProd K Y ⊓ Subgroup.centralizer ({x} : Set F) :=
        (Subgroup.mem_normalizer_iff.mp (hKA hcK) _).mp hkd
      have e1 : diag y q = c * (k * d * k⁻¹) * c⁻¹ := hck
      rw [e1]
      exact hcd.1
    have hact : ∀ q ∈ R ⊓ X, q * q = x → ∃ hN : diag y q ∈ Subgroup.normalizer (Y : Set F),
        Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ ∈ Q3T6.inn3 := fun q hq hq2 =>
      twinProd_act_mem_inn3' hY htK eY (hP q hq hq2)
    set τ := Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ with hτ
    have hρ1 : τ ≠ 1 := fun h1 => hnt ((Q3T6.normalizerToAutSL3_eq_one_iff eY ⟨x, hxY⟩).mp h1)
    have hτ2 : τ * τ = 1 := by
      rw [hτ, ← map_mul]
      have : (⟨x, hxY⟩ * ⟨x, hxY⟩ : Subgroup.normalizer (Y : Set F)) = 1 := Subtype.ext hx2
      rw [this, map_one]
    have hτout : τ ∉ Q3T6.inn3 := not_mem_inn3_of_outer' hY eY hxY hx2 hρ1 hout
    have hef2 : (e * f) * (e * f) = x := by
      calc (e * f) * (e * f) = e * (f * e * f⁻¹) * (f * f) := by group
        _ = e * e⁻¹ * x := by rw [hfe, hf2]
        _ = x := by group
    have hefX : e * f ∈ R ⊓ X := (R ⊓ X).mul_mem he hf
    have hαprops : ∀ q ∈ R ⊓ X, q * q = x → ∀ hN : diag y q ∈ Subgroup.normalizer (Y : Set F),
        Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ * Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ = 1 ∧
          Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ * τ =
            τ * Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ := by
      intro q hq hq2 hN
      constructor
      · rw [← map_mul]
        have : (⟨diag y q, hN⟩ * ⟨diag y q, hN⟩ : Subgroup.normalizer (Y : Set F)) = 1 :=
          Subtype.ext (hδ2 q hq hq2)
        rw [this, map_one]
      · rw [hτ, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hδx q hq)
    have hcent : ∃ q₀ ∈ R ⊓ X, q₀ * q₀ = x ∧ ∀ k ∈ Y, ⁅diag y q₀, k⁆ ∈ oddCoreOf Y := by
      have hcen : ∀ q ∈ R ⊓ X, ∀ hN : diag y q ∈ Subgroup.normalizer (Y : Set F),
          Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ = 1 →
            ∀ k ∈ Y, ⁅diag y q, k⁆ ∈ oddCoreOf Y := fun q _ hN h1 =>
        (Q3T6.normalizerToAutSL3_eq_one_iff eY ⟨diag y q, hN⟩).mp h1
      obtain ⟨hNe, hine⟩ := hact e he he2
      obtain ⟨hNf, hinf⟩ := hact f hf hf2
      obtain ⟨hNef, hinef⟩ := hact (e * f) hefX hef2
      set α₁ := Q3T6.normalizerToAutSL3 eY ⟨diag y e, hNe⟩ with hα₁
      set α₂ := Q3T6.normalizerToAutSL3 eY ⟨diag y f, hNf⟩ with hα₂
      have hα₃ : Q3T6.normalizerToAutSL3 eY ⟨diag y (e * f), hNef⟩ = α₁ * α₂ := by
        rw [hα₁, hα₂, ← map_mul]
        congr 1
        exact Subtype.ext (diag_mul hR he hf).symm
      obtain ⟨h1sq, h1c⟩ := hαprops e he he2 hNe
      obtain ⟨h2sq, h2c⟩ := hαprops f hf hf2 hNf
      by_cases h1 : α₁ = 1
      · exact ⟨e, he, he2, hcen e he hNe h1⟩
      by_cases h2 : α₂ = 1
      · exact ⟨f, hf, hf2, hcen f hf hNf h2⟩
      by_cases h12 : α₁ = α₂
      · refine ⟨e * f, hefX, hef2, hcen (e * f) hefX hNef ?_⟩
        rw [hα₃, ← h12]
        exact h1sq
      · exact absurd (eq_of_commuting_involutions_inn3 τ α₁ α₂ hτ2 hτout hine hinf h1sq h2sq h1 h2
          h1c h2c) h12
    obtain ⟨q₀, hq₀, hq₀2, hq₀c⟩ := hcent
    obtain ⟨c, hcK, k, hkK, hck⟩ :=
      exists_conj_diag_involution hs (hδK q₀ hq₀) (hδ2 q₀ hq₀ hq₀2) (hδ1 q₀ hq₀ hq₀2) he.2 he2
        (hR.comm_conj he)
    set g : F := c * k with hg
    have hgK : g ∈ K := K.mul_mem hcK hkK
    have hgy : g * y = y * g := htK g hgK
    have hgx : g * x = x * g := hzK g hgK
    have hde : diag y e = g * diag y q₀ * g⁻¹ := by
      calc diag y e = c * (k * diag y q₀ * k⁻¹) * c⁻¹ := hck
        _ = g * diag y q₀ * g⁻¹ := by rw [hg]; group
    refine ⟨conjSub g Y, hY.conj_of_commute hgy, ?_, ?_, ?_⟩
    · apply AscHypOmega.mem_normalizer_of_conjSub_eq
      calc conjSub x (conjSub g Y) = conjSub (x * g) Y := (conjSub_mul _ _ _).symm
        _ = conjSub (g * x) Y := by rw [hgx]
        _ = conjSub g (conjSub x Y) := conjSub_mul _ _ _
        _ = conjSub g Y := by rw [conjSub_eq_of_mem_normalizer hxY]
    · intro a' ha' ha4 hax
      have hk0 : g⁻¹ * a' * g ∈ Y := mem_conjSub_iff.mp ha'
      refine hout (g⁻¹ * a' * g) hk0 ?_ ?_
      · rw [← ha4]
        have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a'
        simpa using this
      · have hgxi : g⁻¹ * x = x * g⁻¹ := by
          calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hgx]
            _ = x * g⁻¹ := by group
        calc g⁻¹ * a' * g * x = g⁻¹ * (a' * x) * g := by
              calc g⁻¹ * a' * g * x = g⁻¹ * a' * (g * x) := by group
                _ = g⁻¹ * a' * (x * g) := by rw [hgx]
                _ = g⁻¹ * (a' * x) * g := by group
          _ = g⁻¹ * (x * a') * g := by rw [hax]
          _ = x * (g⁻¹ * a' * g) := by
              calc g⁻¹ * (x * a') * g = (g⁻¹ * x) * a' * g := by group
                _ = (x * g⁻¹) * a' * g := by rw [hgxi]
                _ = x * (g⁻¹ * a' * g) := by group
    · intro k' hk'
      have hk0 : g⁻¹ * k' * g ∈ Y := mem_conjSub_iff.mp hk'
      rw [AscFusion.oddCoreOf_conjSub', mem_conjSub_iff]
      have h1 := hq₀c _ hk0
      have e1 : g⁻¹ * ⁅diag y e, k'⁆ * g = ⁅diag y q₀, g⁻¹ * k' * g⁆ := by
        rw [hde]
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact h1

end Good

end CFSG.ClassicalInvolution.Q3.Q3T6Y
