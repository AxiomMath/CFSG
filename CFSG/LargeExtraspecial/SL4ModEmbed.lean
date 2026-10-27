module

public import CFSG.LargeExtraspecial.SL4ModCodes
public import CFSG.LargeExtraspecial.SL4ModSpinSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native

@[expose] def rep (d : CosetData) (k : ℕ) : SL4 := wordProd d.words[k]!

@[expose] def facSL (j : ℕ) (p : Bool × ℕ × ℕ) : SL4 :=
  if p.1 then uSL p.2.1 * genN (j + 3) * uSL p.2.2 else uSL p.2.1

theorem hasCode_facSL (j : ℕ) (p : Bool × ℕ × ℕ) :
    HasCode (facSL j p) (facCode j p.1 p.2.1 p.2.2) := by
  unfold facSL facCode
  split_ifs
  · exact ((hasCode_uSL _).mul (hasCode_genN _)).mul (hasCode_uSL _)
  · exact hasCode_uSL _

theorem gen_mul_rep {j : ℕ} {d : CosetData} (h : checkTau j d = true) {s : ℕ} (hs : s < 6)
    {k : ℕ} (hk : k < 105) :
    genN s * rep d ((d.tau[s]!)[k]! % 105) = rep d k * facSL j ((d.fac[s]!)[k]!) := by
  rw [checkTau, List.all_eq_true] at h
  have h' := h s (List.mem_range.mpr hs)
  rw [List.all_eq_true] at h'
  have h'' := h' k (List.mem_range.mpr hk)
  rw [beq_iff_eq] at h''
  exact ((hasCode_genN s).mul (hasCode_wordProd _)).eq
    ((hasCode_wordProd _).mul (hasCode_facSL j _)) h''

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : SL4 →* (V ≃ₗ[ZMod 2] V))

@[expose] def IsFixPj (j : ℕ) (f : Module.Dual (ZMod 2) V) : Prop :=
  (∀ u ∈ U, ∀ w, f (ρ u w) = f w) ∧ ∀ w, f (ρ (genN (j + 3)) w) = f w

theorem IsFixPj.facSL {j : ℕ} {f : Module.Dual (ZMod 2) V} (hf : IsFixPj ρ j f)
    (p : Bool × ℕ × ℕ) (w : V) : f (ρ (facSL j p) w) = f w := by
  unfold SL4Mod.facSL
  split_ifs
  · rw [act_mul, act_mul, hf.1 _ (uSL_mem _), hf.2, hf.1 _ (uSL_mem _)]
  · exact hf.1 _ (uSL_mem _) w

@[expose] def iota (d : CosetData) (f : Module.Dual (ZMod 2) V) :
    V →ₗ[ZMod 2] (Fin 105 → ZMod 2) :=
  LinearMap.pi fun k => f ∘ₗ ((ρ (rep d k.val)⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)

theorem iota_apply (d : CosetData) (f : Module.Dual (ZMod 2) V) (w : V) (k : Fin 105) :
    iota ρ d f w k = f (ρ (rep d k.val)⁻¹ w) := rfl

theorem iota_gen {j : ℕ} {d : CosetData} (h : checkTau j d = true) {f : Module.Dual (ZMod 2) V}
    (hf : IsFixPj ρ j f) {s : ℕ} (hs : s < 6) (w : V) :
    iota ρ d f (ρ (genN s) w) = iota ρ d f w ∘ tauF d.tau[s]! := by
  funext k
  have hrel := gen_mul_rep h hs k.isLt
  set k' := (d.tau[s]!)[k.val]! % 105
  have e : (rep d k.val)⁻¹ * genN s = facSL j ((d.fac[s]!)[k.val]!) * (rep d k')⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hrel, mul_assoc, mul_inv_cancel, mul_one]
  rw [iota_apply, Function.comp_apply, iota_apply, ← act_mul, e, act_mul, hf.facSL]
  rfl

@[expose] def IsIrredGen : Prop :=
  ∀ W : Submodule (ZMod 2) V, (∀ s < 6, ∀ w ∈ W, ρ (genN s) w ∈ W) → W = ⊥ ∨ W = ⊤

variable {ρ}

theorem act_inv_act (g : SL4) (w : V) : ρ g⁻¹ (ρ g w) = w := by
  rw [← act_mul, inv_mul_cancel, map_one]
  rfl

theorem iota_injective (hirr : IsIrredGen ρ) {j : ℕ} {d : CosetData} (h : checkTau j d = true)
    {f : Module.Dual (ZMod 2) V} (hf : IsFixPj ρ j f) (hf0 : f ≠ 0) :
    Function.Injective (iota ρ d f) := by
  rw [← LinearMap.ker_eq_bot]
  rcases hirr (LinearMap.ker (iota ρ d f)) (fun s hs w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      rw [iota_gen ρ h hf hs, hw]
      rfl) with h0 | htop
  · exact h0
  · exfalso
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (LinearMap.ext hcon)
    have hmem : ρ (rep d 0) w ∈ LinearMap.ker (iota ρ d f) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at hmem
    have := congrFun hmem 0
    rw [iota_apply] at this
    exact hw (by simpa [act_inv_act] using this)

theorem isTauInv_range_iota {j : ℕ} {d : CosetData} (h : checkTau j d = true)
    {f : Module.Dual (ZMod 2) V} (hf : IsFixPj ρ j f) :
    IsTauInv d.tau (LinearMap.range (iota ρ d f)) := by
  rintro s hs F ⟨w, rfl⟩
  exact ⟨ρ (genN s) w, iota_gen ρ h hf hs w⟩

theorem range_iota_le (hirr : IsIrredGen ρ) {j : ℕ} {d : CosetData} (h : checkTau j d = true)
    {f : Module.Dual (ZMod 2) V} (hf : IsFixPj ρ j f) (Y : Submodule (ZMod 2) (Fin 105 → ZMod 2))
    (hY : IsTauInv d.tau Y) (hYX : Y ≤ LinearMap.range (iota ρ d f)) (hY0 : Y ≠ ⊥) :
    LinearMap.range (iota ρ d f) ≤ Y := by
  rcases hirr (Y.comap (iota ρ d f)) (fun s hs w hw => by
      rw [Submodule.mem_comap] at hw ⊢
      rw [iota_gen ρ h hf hs]
      exact hY s hs _ hw) with h0 | htop
  · exfalso
    apply hY0
    rw [eq_bot_iff]
    intro F hF
    obtain ⟨w, rfl⟩ := hYX hF
    have : w ∈ Y.comap (iota ρ d f) := hF
    rw [h0, Submodule.mem_bot] at this
    rw [this, map_zero, Submodule.mem_bot]
  · rintro F ⟨w, rfl⟩
    have : w ∈ Y.comap (iota ρ d f) := htop ▸ Submodule.mem_top
    exact this

end CFSG.LargeExtraspecial.SL4Mod
