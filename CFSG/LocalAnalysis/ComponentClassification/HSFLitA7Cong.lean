module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitCong
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Bar
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7E

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem card_conj_z_modEq_of_sigma (Λ : A7Sigma S.t S.L S.data)
    (hzt : ∀ g ∈ centralizer ({S.t} : Set X), g * S.z * g⁻¹ ≠ S.t * S.z) :
    {b | ∃ g ∈ centralizer ({S.t} : Set X), g * S.z * g⁻¹ = b}.ncard ≡ 1 [MOD 4] := by
  classical
  set C : Subgroup X := centralizer ({S.t} : Set X) with hC
  set Y₀ : Subgroup C := (centralizer {a0 ^ 2}).comap (S.ΨC Λ) with hY₀
  set Y : Subgroup X := Y₀.map C.subtype with hY
  have hmemY : ∀ g, g ∈ Y ↔ g ∈ C ∧ S.act Λ g * a0 ^ 2 = a0 ^ 2 * S.act Λ g := by
    intro g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, ?_⟩
      change S.act Λ (h : X) * _ = _ * S.act Λ (h : X)
      rw [S.act_of_mem Λ h.2]
      have := mem_centralizer_singleton_iff.mp (show (S.ΨC Λ) h ∈ centralizer {a0 ^ 2} from hh)
      exact this
    · rintro ⟨hg, hcomm⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      change (S.ΨC Λ) ⟨g, hg⟩ ∈ centralizer {a0 ^ 2}
      rw [mem_centralizer_singleton_iff, ← S.act_of_mem Λ hg]
      exact hcomm
  have hYC : Y ≤ C := map_subtype_le _
  have hzC : S.z ∈ C := S.data.T_le_centralizer S.z_mem.1
  have hCzY : C ⊓ centralizer ({S.z} : Set X) ≤ Y := by
    intro g hg
    obtain ⟨hgC, hgz⟩ := mem_inf.mp hg
    rw [hmemY]
    refine ⟨hgC, ?_⟩
    rw [← S.act_z Λ, ← S.act_mul Λ hgC hzC, ← S.act_mul Λ hzC hgC,
      (mem_centralizer_singleton_iff.mp hgz)]
  have hsurj : Function.Surjective (S.ΨC Λ) := MonoidHom.range_eq_top.mp (S.range_ΨC Λ)
  have hYidx : Y.relIndex C = 105 := by
    rw [relIndex, hY]
    change ((Y₀.map C.subtype).comap C.subtype).index = 105
    rw [comap_map_eq_self_of_injective (subtype_injective C), hY₀,
      index_comap_of_surjective _ hsurj,
      show (a0 ^ 2 : Perm (Fin 7)) = swap 0 2 * swap 1 3 by decide]
    exact index_centralizer_swap_swap
  have hmul := relIndex_mul_relIndex (C ⊓ centralizer ({S.z} : Set X)) Y C hCzY hYC
  have hinf : (C ⊓ centralizer ({S.z} : Set X)).relIndex Y =
      (Y ⊓ centralizer ({S.z} : Set X)).relIndex Y := by
    rw [← inf_relIndex_right (C ⊓ centralizer ({S.z} : Set X)) Y,
      ← inf_relIndex_right (Y ⊓ centralizer ({S.z} : Set X)) Y]
    congr 1
    apply le_antisymm
    · exact le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_right)) inf_le_right
    · exact le_inf (le_inf (inf_le_left.trans (inf_le_left.trans hYC))
        (inf_le_left.trans inf_le_right)) inf_le_right
  rw [relIndex_inf_centralizer_eq_ncard, hinf, relIndex_inf_centralizer_eq_ncard, hYidx] at hmul
  rw [← hmul]
  set F : Set X := {y | ∃ g ∈ Y, g * S.z * g⁻¹ = y} with hF
  have hxY : S.x ∈ Y := by
    rw [hmemY]
    refine ⟨S.data.T_le_centralizer S.x_mem.1, ?_⟩
    rw [S.act_of_mem_T Λ S.x_mem.1, S.ψ_x]
    decide
  have hFx : ∀ f ∈ F, S.x * f * S.x⁻¹ ∈ F := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨S.x * g, mul_mem hxY hg, by group⟩
  have hFx' : ∀ f ∈ F, S.x⁻¹ * f * S.x ∈ F := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨S.x⁻¹ * g, mul_mem (inv_mem hxY) hg, by group⟩
  have : Fintype F := Fintype.ofFinite F
  let π : Perm F :=
    { toFun := fun f => ⟨S.x * f * S.x⁻¹, hFx f f.2⟩
      invFun := fun f => ⟨S.x⁻¹ * f * S.x, hFx' f f.2⟩
      left_inv := fun f => Subtype.ext (by simp [mul_assoc])
      right_inv := fun f => Subtype.ext (by simp [mul_assoc]) }
  have hπpow : ∀ (n : ℕ) (f : F), ((π ^ n) f : X) = S.x ^ n * f * (S.x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
      intro f
      rw [pow_succ', Perm.mul_apply]
      change S.x * ((π ^ n) f : X) * S.x⁻¹ = _
      rw [ih, pow_succ']
      group
  have hπ4 : π ^ 4 = 1 := by
    ext f
    rw [hπpow, S.x_pow_four]
    simp
  have hfix : Fintype.card (Function.fixedPoints ⇑(π ^ 2)) = 1 := by
    rw [Fintype.card_eq_one_iff]
    have hzF : S.z ∈ F := ⟨1, one_mem _, by group⟩
    have hzfix : (π ^ 2) ⟨S.z, hzF⟩ = ⟨S.z, hzF⟩ := by
      apply Subtype.ext
      rw [hπpow]
      change S.x ^ 2 * S.x ^ 2 * (S.x ^ 2)⁻¹ = S.x ^ 2
      group
    refine ⟨⟨⟨S.z, hzF⟩, hzfix⟩, fun f => ?_⟩
    obtain ⟨⟨f, ⟨g, hg, rfl⟩⟩, hf⟩ := f
    apply Subtype.ext
    apply Subtype.ext
    change g * S.z * g⁻¹ = S.z
    have hf' := congrArg Subtype.val (show (π ^ 2) _ = _ from hf)
    rw [hπpow] at hf'
    change S.z * (g * S.z * g⁻¹) * S.z⁻¹ = g * S.z * g⁻¹ at hf'
    obtain ⟨hgC, hgcomm⟩ := (hmemY g).mp hg
    set f := g * S.z * g⁻¹ with hfdef
    have hfC : f ∈ C := mul_mem (mul_mem hgC hzC) (inv_mem hgC)
    have hz2 : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))
    have hzinv : S.z⁻¹ = S.z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2]
    have hfz : S.z * f = f * S.z := by
      calc S.z * f = S.z * f * S.z⁻¹ * S.z := by group
        _ = f * S.z := by rw [hf']
    have hf2 : f ^ 2 = 1 := by rw [hfdef, conj_pow, hz2]; group
    have hact : S.act Λ (S.z * f) = 1 := by
      rw [S.act_mul Λ hzC hfC, hfdef, S.act_conj Λ hgC hzC, S.act_z Λ, ← mul_assoc, ← mul_assoc,
        show a0 ^ 2 * S.act Λ g = S.act Λ g * a0 ^ 2 from hgcomm.symm]
      calc S.act Λ g * a0 ^ 2 * a0 ^ 2 * (S.act Λ g)⁻¹ =
          S.act Λ g * (a0 ^ 2 * a0 ^ 2) * (S.act Λ g)⁻¹ := by
            group
        _ = 1 := by rw [show (a0 ^ 2 * a0 ^ 2 : Perm (Fin 7)) = 1 by decide]; group
    have hsq : (S.z * f) ^ 2 = 1 := by
      rw [(show Commute S.z f from hfz).mul_pow, hz2, hf2, one_mul]
    rcases S.eq_one_or_eq_t_of_sq Λ (mul_mem hzC hfC) hact hsq with h | h
    · calc f = S.z⁻¹ * (S.z * f) := by group
        _ = S.z := by rw [h, mul_one, hzinv]
    · exfalso
      apply hzt g hgC
      calc g * S.z * g⁻¹ = S.z⁻¹ * (S.z * f) := by rw [hfdef]; group
        _ = S.t * S.z := by
          rw [h, hzinv]
          exact S.z_comm_of_mem_T S.data.t_mem_T
  have hF1 := card_modEq_card_fixedPoints_sq π hπ4
  rw [hfix] at hF1
  have hFc : F.ncard = Fintype.card F := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [hFc]
  calc Fintype.card F * 105 ≡ 1 * 105 [MOD 4] := Nat.ModEq.mul_right _ hF1.symm
    _ ≡ 1 [MOD 4] := by decide

theorem card_conj_z_modEq
    (hzt : ∀ g ∈ centralizer ({S.t} : Set X), g * S.z * g⁻¹ ≠ S.t * S.z) :
    {b | ∃ g ∈ centralizer ({S.t} : Set X), g * S.z * g⁻¹ = b}.ncard ≡ 1 [MOD 4] := by
  rcases S.facts with h | hΛ
  · exact h.card_conj_z hzt
  · obtain ⟨Λ⟩ := hΛ
    exact S.card_conj_z_modEq_of_sigma Λ hzt

end A7Base

end CFSG.ComponentClassification.HSFLit
