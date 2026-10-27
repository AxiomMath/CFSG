module

public import CFSG.LargeExtraspecial.S14W4LocDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup CFSG.LargeExtraspecial.S4

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}

theorem fixSub_ne_bot (hcard : 1 < Nat.card T.Qt) (k : T.M) (hk : ∃ n : ℕ, k ^ 2 ^ n = 1) :
    fixSub T (zpowers (T.ρ k)) ≠ ⊥ := by
  have : Nontrivial T.Qt := Finite.one_lt_card_iff_nontrivial.mp hcard
  have hfix := exists_fixed_of_isPGroup T (isPGroup_zpowers_ρ k hk) (U := ⊤)
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  obtain ⟨u, -, hu0, hu⟩ := hfix
  intro h0
  have hu' : u ∈ fixSub T (zpowers (T.ρ k)) := hu
  rw [h0] at hu'
  exact hu0 ((Submodule.mem_bot (ZMod 2)).mp hu')

theorem fixSub_isInv (k : T.M)
    (hcomm : ∀ r : T.M, (r : X) ∈ R → T.ρ k * T.ρ r = T.ρ r * T.ρ k) :
    W4Dict.IsInv T R (fixSub T (zpowers (T.ρ k))) := by
  intro r hr v hv
  have hv' : ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v = v := (mem_fixSub_zpowers_iff _ v).mp hv
  refine (mem_fixSub_zpowers_iff _ _).mpr ?_
  calc ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) (((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v)
      = ((T.ρ k * T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v := rfl
    _ = ((T.ρ r * T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v :=
      congrArg (fun y : T.O => (y : T.Qt ≃ₗ[ZMod 2] T.Qt) v) (hcomm r hr)
    _ = ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) (((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v) := rfl
    _ = ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v :=
      congrArg ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) hv'

theorem map_isInv (k : T.M)
    (hcomm : ∀ r : T.M, (r : X) ∈ R → T.ρ k * T.ρ r = T.ρ r * T.ρ k)
    (W : Submodule (ZMod 2) T.Qt) (hW : W4Dict.IsInv T R W) :
    W4Dict.IsInv T R (W.map ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt).toLinearMap) := by
  intro r hr v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  refine Submodule.mem_map.mpr ⟨((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w, hW r hr w hw, ?_⟩
  calc ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) (((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w)
      = ((T.ρ k * T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w := rfl
    _ = ((T.ρ r * T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w :=
      congrArg (fun y : T.O => (y : T.Qt ≃ₗ[ZMod 2] T.Qt) w) (hcomm r hr)
    _ = _ := rfl

theorem card_map_ρ (k : T.M) (W : Submodule (ZMod 2) T.Qt) :
    Nat.card (W.map ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt).toLinearMap) = Nat.card W :=
  (Nat.card_congr (Submodule.equivMapOfInjective _
    (LinearEquiv.injective ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt)) W).toEquiv).symm

omit [Finite X] in
theorem card_bot_submodule : Nat.card (⊥ : Submodule (ZMod 2) T.Qt) = 1 := Nat.card_unique

omit [Finite X] in
theorem card_top_submodule : Nat.card (⊤ : Submodule (ZMod 2) T.Qt) = Nat.card T.Qt :=
  Nat.card_congr Submodule.topEquiv.toEquiv

theorem zpowers_mapsTo (e : T.O) (W : Submodule (ZMod 2) T.Qt)
    (hW : ∀ v ∈ W, (e : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W) :
    ∀ x ∈ zpowers e, ∀ v ∈ W, (x : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W := by
  intro x hx v hv
  have hpow : ∀ n : ℕ, ((e ^ n : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W := by
    intro n
    induction n with
    | zero => exact hv
    | succ n ih =>
      have e1 : ((e ^ (n + 1) : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v =
          (e : T.Qt ≃ₗ[ZMod 2] T.Qt) (((e ^ n : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v) := by
        rw [pow_succ']
        rfl
      exact e1 ▸ hW _ ih
  have hfo : IsOfFinOrder e := isOfFinOrder_of_finite e
  obtain ⟨n, hn⟩ := (hfo.mem_powers_iff_mem_zpowers (y := x)).mpr hx
  exact hn ▸ hpow n

theorem false_of_fixSub_eq (hcard : Nat.card T.Qt = 2 ^ 8) (k : T.M)
    (hk : ∃ n : ℕ, k ^ 2 ^ n = 1)
    (hcomm : ∀ r : T.M, (r : X) ∈ R → T.ρ k * T.ρ r = T.ρ r * T.ρ k)
    {W₁ W₂ : Submodule (ZMod 2) T.Qt} (h2 : W4Dict.IsInv T R W₂) (h12 : W₁ ⊓ W₂ = ⊥)
    (hc2 : Nat.card W₂ = 2 ^ 4)
    (hall : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = W₁ ∨ W = W₂ ∨ W = ⊤)
    (hF : fixSub T (zpowers (T.ρ k)) = W₁) : False := by
  have hinv := map_isInv k hcomm W₂ h2
  have hc' := (card_map_ρ k W₂).trans hc2
  have hW₂0 : W₂ ≠ ⊥ := fun h0 => by
    have h3 := congrArg (fun W : Submodule (ZMod 2) T.Qt => Nat.card W) h0
    simp only [card_bot_submodule, hc2] at h3
    norm_num at h3
  rcases hall _ hinv with h | h | h | h
  · have h3 := congrArg (fun W : Submodule (ZMod 2) T.Qt => Nat.card W) h
    simp only [card_bot_submodule, hc'] at h3
    norm_num at h3
  · apply hW₂0
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    have h1 : ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w ∈ W₁ := h.le (Submodule.mem_map_of_mem hw)
    have h3 := (mem_fixSub_zpowers_iff _ _).mp (hF.ge h1)
    have h4 : ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w = w := LinearEquiv.injective _ h3
    have h6 : w ∈ W₁ := hF.le ((mem_fixSub_zpowers_iff _ _).mpr h4)
    exact (Submodule.mem_bot (ZMod 2)).mp (h12.le ⟨h6, hw⟩)
  · have hU := zpowers_mapsTo (T.ρ k) W₂ fun v hv => h.le (Submodule.mem_map_of_mem hv)
    obtain ⟨u, huW, hu0, hu⟩ := exists_fixed_of_isPGroup T (isPGroup_zpowers_ρ k hk) hU hW₂0
    have hu1 : u ∈ W₁ := hF.le hu
    exact hu0 ((Submodule.mem_bot (ZMod 2)).mp (h12.le ⟨hu1, huW⟩))
  · have h3 := congrArg (fun W : Submodule (ZMod 2) T.Qt => Nat.card W) h
    simp only [card_top_submodule, hc', hcard] at h3
    norm_num at h3

theorem mem_Q_of_comm (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R) (k : T.M)
    (hk : ∃ n : ℕ, k ^ 2 ^ n = 1)
    (hcomm : ∀ r : T.M, (r : X) ∈ R → T.ρ k * T.ρ r = T.ρ r * T.ρ k) : k ∈ T.Q := by
  have hF0 := fixSub_ne_bot (by rw [hcard]; norm_num) k hk
  have hFi := fixSub_isInv k hcomm
  have hFtop : fixSub T (zpowers (T.ρ k)) = ⊤ := by
    rcases hL with hirr | ⟨W₁, W₂, h1, h2, h12, hc1, hc2, hall⟩
    · exact (hirr _ hFi).resolve_left hF0
    · rcases hall _ hFi with h | h | h | h
      · exact absurd h hF0
      · exact (false_of_fixSub_eq hcard k hk hcomm h2 h12 hc2 hall h).elim
      · refine (false_of_fixSub_eq hcard k hk hcomm h1 (inf_comm W₂ W₁ ▸ h12) hc1
          (fun W hW => ?_) h).elim
        rcases hall W hW with h' | h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))
      · exact h
  have hρ : T.ρ k = 1 := Subtype.ext (LinearEquiv.ext fun v =>
    (mem_fixSub_zpowers_iff _ v).mp (hFtop.ge Submodule.mem_top))
  exact T.mem_Q_of_ρ_eq_one hρ

theorem comm_of_mem_Q {k r : T.M} (h : k * r * k⁻¹ * r⁻¹ ∈ T.Q) :
    T.ρ k * T.ρ r = T.ρ r * T.ρ k := by
  have h1 : T.ρ (k * r * k⁻¹ * r⁻¹) = 1 := T.ρ_eq_one_of_mem_Q h
  simp only [map_mul, map_inv] at h1
  calc T.ρ k * T.ρ r = (T.ρ k * T.ρ r * (T.ρ k)⁻¹ * (T.ρ r)⁻¹) * (T.ρ r * T.ρ k) := by group
    _ = T.ρ r * T.ρ k := by rw [h1, one_mul]

end CFSG.LargeExtraspecial.S14.W4Loc
