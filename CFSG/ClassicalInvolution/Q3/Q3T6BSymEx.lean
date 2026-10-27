module

public import CFSG.ClassicalInvolution.Q3.Q3T6BCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem not_mem_inn3_of_outer {Y : Subgroup F} {y x : F} (hY : Mem3 Y y) (hyex : ExAt y)
    (eY : Y ⧸ classicalInvolutionOddCore Y ≃* SL(2, ZMod 3))
    (hxY : x ∈ Subgroup.normalizer (Y : Set F)) (hx2 : x * x = 1)
    (hρ1 : Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ ≠ 1)
    (hout : ∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a) :
    Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ ∉ Q3T6.inn3 := by
  classical
  rintro ⟨b, hb⟩
  have hOY : oddCoreOf Y = ⊥ := Mem3.oddCoreOf_eq_bot hY hyex
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (eY.symm b)
  have hbk : eY (QuotientGroup.mk k) = b := by rw [hk, MulEquiv.apply_symm_apply]
  have hkN : (k : F) ∈ Subgroup.normalizer (Y : Set F) := Subgroup.le_normalizer k.2
  have hτk : Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ =
      Q3T6.normalizerToAutSL3 eY ⟨(k : F), hkN⟩ := by
    rw [Q3T6.normalizerToAutSL3_of_mem eY k.2, hbk, hb]
  have hxk : ∀ l ∈ Y, (x * (k : F)⁻¹) * l = l * (x * (k : F)⁻¹) := by
    intro l hl
    have h1 : Q3T6.normalizerToAutSL3 eY (⟨x, hxY⟩ * ⟨(k : F), hkN⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hτk, mul_inv_cancel]
    have h2 := (Q3T6.normalizerToAutSL3_eq_one_iff eY _).mp h1 l hl
    rw [hOY, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hxkc : x * (k : F) = (k : F) * x := by
    have h1 := hxk k k.2
    have e1 : x = (k : F) * x * (k : F)⁻¹ := by
      calc x = (x * (k : F)⁻¹) * k := by group
        _ = (k : F) * (x * (k : F)⁻¹) := h1
        _ = (k : F) * x * (k : F)⁻¹ := by group
    calc x * (k : F) = ((k : F) * x * (k : F)⁻¹) * k := by rw [← e1]
      _ = (k : F) * x := by group
  have hτ2 : Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ * Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hxY⟩ * ⟨x, hxY⟩ : Subgroup.normalizer (Y : Set F)) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hkk1 : Q3T6.normalizerToAutSL3 eY (⟨(k : F), hkN⟩ * ⟨(k : F), hkN⟩) = 1 := by
    rw [map_mul, ← hτk]
    exact hτ2
  have hkkc : ∀ l ∈ Y, ((k : F) * k) * l = l * ((k : F) * k) := by
    intro l hl
    have h2 := (Q3T6.normalizerToAutSL3_eq_one_iff eY _).mp hkk1 l hl
    rw [hOY, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  rcases Mem3.eq_one_or_eq_of_central hY hyex (Y.mul_mem k.2 k.2) hkkc with hk2 | hk2
  ·
    apply hρ1
    have hk1 : (k : F) = 1 ∨ (k : F) = y := hY.isUniqueInvolution.unique k k.2 hk2
    rw [hτk, Q3T6.normalizerToAutSL3_eq_one_iff]
    intro l hl
    rcases hk1 with h | h
    · show ⁅(k : F), l⁆ ∈ oddCoreOf Y
      rw [h]
      simp
    · show ⁅(k : F), l⁆ ∈ oddCoreOf Y
      rw [h, hOY, Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hY.mul_comm_of_mem hl).symm
  ·
    have hk4 : orderOf (k : F) = 4 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h1 : ¬ (k : F) ^ 2 ^ 1 = 1 := by
        rw [pow_one, pow_two, hk2]
        exact hY.ne_one
      have h2 : (k : F) ^ 2 ^ (1 + 1) = 1 := by
        rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, pow_two, hk2, hY.mul_self]
      have := orderOf_eq_prime_pow h1 h2
      rwa [show (2 : ℕ) ^ (1 + 1) = 4 from rfl] at this
    exact hout k k.2 hk4 hxkc.symm

section Good

variable {X Y : Subgroup F} {x y : F}

theorem exists_good_member (hs : Swap X x y) (hxex : ExAt x) (hyex : ExAt y) (hY : Mem3 Y y)
    (hxY : x ∈ Subgroup.normalizer (Y : Set F))
    (hout : ∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a) {e f : F} (he : e ∈ X) (hf : f ∈ X)
    (he2 : e * e = x) (hf2 : f * f = x) (hfe : f * e * f⁻¹ = e⁻¹) :
    ∃ Y' : Subgroup F, Mem3 Y' y ∧ x ∈ Subgroup.normalizer (Y' : Set F) ∧
      (∀ a ∈ Y', orderOf a = 4 → a * x ≠ x * a) ∧ ∀ k ∈ Y', diag y e * k = k * diag y e := by
  classical
  have hx2 : x * x = 1 := hs.member.mul_self
  have hc := hs.comm_twin hxex
  have hOY : oddCoreOf Y = ⊥ := Mem3.oddCoreOf_eq_bot hY hyex
  have hnt : ¬ ∀ j ∈ Y, ⁅x, j⁆ ∈ oddCoreOf Y := fun htriv => by
    obtain ⟨a, haY, ha4, hax⟩ := exists_comm_order_four_of_trivial hY hxY hx2 htriv
    exact hout a haY ha4 hax
  rcases diag_dichotomy hs hxex hyex hY hxY hnt with hI | hII
  ·
    refine ⟨Y, hY, hxY, hout, fun k hk => ?_⟩
    have h1 := (hI e he).2 k hk
    rw [hOY, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  ·
    set Δ : Subgroup F := diagGroupOf hs hxex with hΔ
    have htK : ∀ k ∈ Δ, k * y = y * k := fun k hk => diagGroupOf_comm_y hs hxex hk
    obtain ⟨eY⟩ := Q3T6.nonempty_equiv_of_memberU hY.member
    have hact : ∀ q ∈ X, q * q = x →
        ∃ hN : diag y q ∈ Subgroup.normalizer (Y : Set F),
          Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ ∈ Q3T6.inn3 :=
      fun q hq hq2 => twinProd_act_mem_inn3 hY htK hyex eY (hII q hq hq2)
    set τ := Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ with hτ
    have hρ1 : τ ≠ 1 := fun h1 => hnt ((Q3T6.normalizerToAutSL3_eq_one_iff eY ⟨x, hxY⟩).mp h1)
    have hτ2 : τ * τ = 1 := by
      rw [hτ, ← map_mul]
      have : (⟨x, hxY⟩ * ⟨x, hxY⟩ : Subgroup.normalizer (Y : Set F)) = 1 := Subtype.ext hx2
      rw [this, map_one]
    have hτout : τ ∉ Q3T6.inn3 := not_mem_inn3_of_outer hY hyex eY hxY hx2 hρ1 hout
    have hef2 : (e * f) * (e * f) = x := by
      calc (e * f) * (e * f) = e * (f * e * f⁻¹) * (f * f) := by group
        _ = e * e⁻¹ * x := by rw [hfe, hf2]
        _ = x := by group
    have hefX : e * f ∈ X := X.mul_mem he hf
    have hαprops : ∀ q ∈ X, q * q = x → ∀ hN : diag y q ∈ Subgroup.normalizer (Y : Set F),
        Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ * Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ = 1 ∧
          Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ * τ =
            τ * Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ := by
      intro q hq hq2 hN
      have hcq : q * (y * q * y⁻¹) = (y * q * y⁻¹) * q := hc q hq _ (conj_mem_conjSub hq)
      have hd2 : diag y q * diag y q = 1 := diag_mul_self hx2 hs.comm hq2 hcq
      have hdx : diag y q * x = x * diag y q := (diag_comm_xy hs hxex hq).1
      constructor
      · rw [← map_mul]
        have : (⟨diag y q, hN⟩ * ⟨diag y q, hN⟩ : Subgroup.normalizer (Y : Set F)) = 1 :=
          Subtype.ext hd2
        rw [this, map_one]
      · rw [hτ, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hdx
    have hcent : ∃ q₀ ∈ X, q₀ * q₀ = x ∧ ∀ k ∈ Y, diag y q₀ * k = k * diag y q₀ := by
      have hcen : ∀ q ∈ X, ∀ hN : diag y q ∈ Subgroup.normalizer (Y : Set F),
          Q3T6.normalizerToAutSL3 eY ⟨diag y q, hN⟩ = 1 → ∀ k ∈ Y, diag y q * k = k * diag y q := by
        intro q hq hN h1 k hk
        have h2 := (Q3T6.normalizerToAutSL3_eq_one_iff eY ⟨diag y q, hN⟩).mp h1 k hk
        rw [hOY, Subgroup.mem_bot] at h2
        exact commutatorElement_eq_one_iff_mul_comm.mp h2
      obtain ⟨hNe, hine⟩ := hact e he he2
      obtain ⟨hNf, hinf⟩ := hact f hf hf2
      obtain ⟨hNef, hinef⟩ := hact (e * f) hefX hef2
      set α₁ := Q3T6.normalizerToAutSL3 eY ⟨diag y e, hNe⟩ with hα₁
      set α₂ := Q3T6.normalizerToAutSL3 eY ⟨diag y f, hNf⟩ with hα₂
      have hα₃ : Q3T6.normalizerToAutSL3 eY ⟨diag y (e * f), hNef⟩ = α₁ * α₂ := by
        rw [hα₁, hα₂, ← map_mul]
        congr 1
        exact Subtype.ext (diag_mul_of_mem hs hxex he hf)
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
    obtain ⟨q₀, hq₀X, hq₀2, hq₀c⟩ := hcent
    obtain ⟨a, haX, hacon⟩ := Mem3.exists_conj_in_member hs.member hq₀X he hq₀2 he2
    set c : F := diag y a with hcdef
    have hcΔ : c ∈ Δ := diag_mem_diagGroupOf hs hxex haX
    have hcy : c * y = y * c := diagGroupOf_comm_y hs hxex hcΔ
    have hcx : c * x = x * c := diagGroupOf_comm_x hs hxex hcΔ
    have hde : diag y e = c * diag y q₀ * c⁻¹ := by
      rw [← hacon]
      exact diag_conj_of_mem hs hxex haX hq₀X
    refine ⟨conjSub c Y, hY.conj_of_commute hcy, ?_, ?_, ?_⟩
    · apply AscHypOmega.mem_normalizer_of_conjSub_eq
      calc conjSub x (conjSub c Y) = conjSub (x * c) Y := (conjSub_mul _ _ _).symm
        _ = conjSub (c * x) Y := by rw [hcx]
        _ = conjSub c (conjSub x Y) := conjSub_mul _ _ _
        _ = conjSub c Y := by rw [conjSub_eq_of_mem_normalizer hxY]
    · intro a' ha' ha4 hax
      have hk0 : c⁻¹ * a' * c ∈ Y := mem_conjSub_iff.mp ha'
      refine hout (c⁻¹ * a' * c) hk0 ?_ ?_
      · rw [← ha4]
        have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective a'
        simpa using this
      · have hcxi : c⁻¹ * x = x * c⁻¹ := by
          calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
            _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
            _ = x * c⁻¹ := by group
        calc c⁻¹ * a' * c * x = c⁻¹ * (a' * x) * c := by
              calc c⁻¹ * a' * c * x = c⁻¹ * a' * (c * x) := by group
                _ = c⁻¹ * a' * (x * c) := by rw [hcx]
                _ = c⁻¹ * (a' * x) * c := by group
          _ = c⁻¹ * (x * a') * c := by rw [hax]
          _ = x * (c⁻¹ * a' * c) := by
              calc c⁻¹ * (x * a') * c = (c⁻¹ * x) * a' * c := by group
                _ = (x * c⁻¹) * a' * c := by rw [hcxi]
                _ = x * (c⁻¹ * a' * c) := by group
    · intro k hk
      have hk0 : c⁻¹ * k * c ∈ Y := mem_conjSub_iff.mp hk
      have h1 := hq₀c _ hk0
      calc diag y e * k = c * diag y q₀ * c⁻¹ * k := by rw [hde]
        _ = c * (diag y q₀ * (c⁻¹ * k * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * k * c) * diag y q₀) * c⁻¹ := by rw [h1]
        _ = k * (c * diag y q₀ * c⁻¹) := by group
        _ = k * diag y e := by rw [hde]

end Good

section Chain

variable {X Y : Subgroup F} {x y : F}

theorem symOuter_of_exact (hX : Mem3 X x) (hY : Mem3 Y y) (hxex : ExAt x) (hyex : ExAt y)
    (hxY : x ∈ Subgroup.normalizer (Y : Set F))
    (hout : ∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a) : y ∈ Subgroup.normalizer (X : Set F) := by
  by_contra hy
  have hxy : x * y = y * x := Mem3.comm_of_mem_normalizer hY hxY
  have hs : Swap X x y :=
    ⟨hX, hY.mul_self, hxy.symm, fun he => hy (AscHypOmega.mem_normalizer_of_conjSub_eq he)⟩
  obtain ⟨R, hR⟩ := hs.exists_swapSylow
  obtain ⟨e, he, f, hf, he2, hf2, hfe⟩ := hR.exists_anticomm hs
  have hxx := hX.mul_self
  have hc := hR.comm_conj he
  have hex : e * x = x * e := hX.mul_comm_of_mem he.2
  have hdx : x * diag y e = diag y e * x :=
    diag_comm_x hex (hs.twin.mul_comm_of_mem (conj_mem_conjSub he.2))
  have hd2 : diag y e * diag y e = 1 := diag_mul_self hxx hs.comm he2 hc
  obtain ⟨Y', hY', hxY', hout', hcent⟩ :=
    exists_good_member hs hxex hyex hY hxY hout he.2 hf.2 he2 hf2 hfe
  have hdN : diag y e ∈ Subgroup.normalizer (Y' : Set F) :=
    Subgroup.centralizer_le_normalizer (Y' : Set F)
      (Subgroup.mem_centralizer_iff.mpr fun k hk => (hcent k hk).symm)
  have hdtriv : ∀ k ∈ Y', ⁅diag y e, k⁆ ∈ oddCoreOf Y' := fun k hk => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcent k hk)]
    exact (oddCoreOf Y').one_mem
  obtain ⟨κ, hκY, hκx, hκd⟩ :=
    exists_inverting_commuting hY' hxx hd2 hdx hxY' hdN hout' hdtriv
  obtain ⟨g, hg, hgx⟩ := exists_conj_diag_eq_y hs hR he hf he2 hfe hκd hκx
  have hδ : g⁻¹ * y * g⁻¹⁻¹ = diag y e := by
    calc g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * (g * diag y e * g⁻¹) * g⁻¹⁻¹ := by rw [hg]
      _ = diag y e := by group
  have hI : Mem3 (conjSub g⁻¹ Y') (diag y e) := by
    have h1 := hY'.conj g⁻¹
    rwa [hδ] at h1
  have hδex : ExAt (diag y e) := by
    have h1 := exAt_conj hyex g⁻¹
    rwa [hδ] at h1
  have hdyN : diag y e * y ∈ Subgroup.normalizer (Y' : Set F) :=
    Subgroup.mul_mem _ hdN (Subgroup.le_normalizer hY'.mem)
  have hxI : x ∈ Subgroup.normalizer (conjSub g⁻¹ Y' : Set F) := by
    apply AscHypOmega.mem_normalizer_of_conjSub_eq
    have h1 : x * g⁻¹ = g⁻¹ * (diag y e * y) := by rw [← hgx]; group
    calc conjSub x (conjSub g⁻¹ Y') = conjSub (x * g⁻¹) Y' := (conjSub_mul _ _ _).symm
      _ = conjSub (g⁻¹ * (diag y e * y)) Y' := by rw [h1]
      _ = conjSub g⁻¹ (conjSub (diag y e * y) Y') := conjSub_mul _ _ _
      _ = conjSub g⁻¹ Y' := by rw [conjSub_eq_of_mem_normalizer hdyN]
  have hxtriv : ∀ i ∈ conjSub g⁻¹ Y', ⁅x, i⁆ ∈ oddCoreOf (conjSub g⁻¹ Y') := by
    intro i hi
    have hk : g * i * g⁻¹ ∈ Y' := by
      have := mem_conjSub_iff.mp hi
      simpa using this
    rw [AscFusion.oddCoreOf_conjSub', mem_conjSub_iff]
    have h1 : g * ⁅x, i⁆ * g⁻¹ = ⁅diag y e * y, g * i * g⁻¹⁆ := by
      rw [← hgx]
      simp only [commutatorElement_def]
      group
    have h2 : ⁅diag y e * y, g * i * g⁻¹⁆ = ⁅diag y e, g * i * g⁻¹⁆ := by
      have hyk : y * (g * i * g⁻¹) = (g * i * g⁻¹) * y := (hY'.mul_comm_of_mem hk).symm
      simp only [commutatorElement_def]
      calc diag y e * y * (g * i * g⁻¹) * (diag y e * y)⁻¹ * (g * i * g⁻¹)⁻¹
          = diag y e * (y * (g * i * g⁻¹) * y⁻¹) * (diag y e)⁻¹ * (g * i * g⁻¹)⁻¹ := by group
        _ = diag y e * (g * i * g⁻¹) * (diag y e)⁻¹ * (g * i * g⁻¹)⁻¹ := by
          rw [hyk]
          group
    have h3 : (g⁻¹)⁻¹ * ⁅x, i⁆ * g⁻¹ = g * ⁅x, i⁆ * g⁻¹ := by rw [inv_inv]
    rw [h3, h1, h2]
    exact hdtriv _ hk
  have hdX : diag y e ∈ Subgroup.normalizer (X : Set F) := SwapSylow.diag_mem_normalizer hs he.2
  have hcomm := bal368_of_exact hI hX hδex hxex hxtriv hdX f hf.2
  have hdf : ⁅diag y e, f⁆ = x := by
    have h1 : ⁅f, diag y e⁆ = x := by
      rw [commutatorElement_def, diag_conj hs hR he hf he2 hfe]
      group
    rw [← commutatorElement_inv, h1]
    exact inv_eq_of_mul_eq_one_right hxx
  rw [hdf] at hcomm
  exact not_mem_oddCoreOf_of_orderOf_two hX.orderOf_eq_two hcomm

end Chain

end CFSG.ClassicalInvolution.Q3.Q3T6B
