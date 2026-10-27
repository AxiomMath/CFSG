module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerStep
public import CFSG.LieType.SeitzGeneration.QuasiHighLift
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverLayer

open Matrix CFSG.Open CFSG.LieType.Seitz
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open scoped commutatorElement

variable {G C : Type*} [Group G] [Group C] {π : G →* C}

theorem commute_of_comp_commute_of_perfect {A : Type*} [Group A] (hA : commutator A = ⊤)
    (hker : π.ker ≤ Subgroup.center G) {α : A →* G} {g : G}
    (h : ∀ a, Commute (π (α a)) (π g)) : ∀ a, Commute (α a) g := by
  haveI : Group.IsPerfect A := ⟨hA⟩
  have hcomp : π.comp α = π.comp ((MulAut.conj g).toMonoidHom.comp α) := by
    ext a
    change π (α a) = π ((MulAut.conj g) (α a))
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    calc π (α a) = π (α a) * π g * (π g)⁻¹ := by group
      _ = π g * π (α a) * (π g)⁻¹ := by rw [Commute.eq (h a)]
  intro a
  have ha : α a = g * α a * g⁻¹ := by
    have h1 := DFunLike.congr_fun
      (CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker hcomp) a
    rw [MonoidHom.comp_apply] at h1
    change α a = (MulAut.conj g) (α a) at h1
    rwa [MulAut.conj_apply] at h1
  rw [commute_iff_eq]
  conv_lhs => rw [ha]
  group

theorem range_le_of_comp_range_le_of_perfect {A : Type*} [Group A]
    (hA : commutator A = ⊤) (hker : π.ker ≤ Subgroup.center G) {α : A →* G}
    {H : Subgroup G} (h : ∀ a, π (α a) ∈ H.map π) : α.range ≤ H := by
  have hsub : α.range ≤ H ⊔ Subgroup.center G := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨w, hw, hπw⟩ := Subgroup.mem_map.1 (h a)
    have hz : w⁻¹ * α a ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπw, inv_mul_cancel]
    exact Subgroup.mem_sup_of_normal_right.2 ⟨w, hw, w⁻¹ * α a, hker hz, by group⟩
  have hperf : α.range = ⁅α.range, α.range⁆ := by
    have e := map_commutator_eq A α
    rwa [hA, Subgroup.map_top] at e
  rw [hperf]
  calc ⁅α.range, α.range⁆ ≤ ⁅H ⊔ Subgroup.center G, H ⊔ Subgroup.center G⁆ :=
        Subgroup.commutator_mono hsub hsub
    _ ≤ H := by
      rw [Subgroup.commutator_le]
      rintro x hx y hy
      obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
      obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
      have e : ⁅h₁ * z₁, h₂ * z₂⁆ = ⁅h₁, h₂⁆ := by
        rw [Subgroup.mem_center_iff.1 hz₁ h₁, Subgroup.mem_center_iff.1 hz₂ h₂]
        exact CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hz₁ hz₂ h₁ h₂
      rw [e]
      exact Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator hh₁ hh₂)

theorem exists_lift_SL3 {k : Type} [Field k] [Finite k] (hk : 5 ≤ Nat.card k)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (ρ₀ : SpecialLinearGroup (Fin 3) k →* C) :
    ∃ ρ : SpecialLinearGroup (Fin 3) k →* G, π.comp ρ = ρ₀ := by
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
    (m := 2) (F := k) (E := CFSG.LieType.Steinberg.pullback ρ₀ π) le_rfl hk
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := ρ₀) (η := π) hπ)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center (β := ρ₀) (η := π) hker)
  refine ⟨(MonoidHom.snd (SpecialLinearGroup (Fin 3) k) G).comp
    ((CFSG.LieType.Steinberg.pullback ρ₀ π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : CFSG.LieType.Steinberg.pullback ρ₀ π) :
      SpecialLinearGroup (Fin 3) k × G).1 = x := hs x
  have h2' := CFSG.LieType.Steinberg.mem_pullback.1 (s x).2
  rw [h1] at h2'
  show π (((s x : CFSG.LieType.Steinberg.pullback ρ₀ π) :
    SpecialLinearGroup (Fin 3) k × G).2) = ρ₀ x
  exact h2'.symm

theorem exists_lift_frames {Y : Type*} [Group Y] (hY : commutator Y = ⊤)
    (hnab : ∃ x y : Y, x * y ≠ y * x)
    (hlift : ∀ β : Y →* C, ∃ α : Y →* G, π.comp α = β)
    (hker : π.ker ≤ Subgroup.center G) (ind : MulAut G →* MulAut C)
    (hind : ∀ (f : MulAut G) (g : G), π (f g) = ind f (π g))
    {E : Subgroup (MulAut G)} {𝒟 : Subgroup (MulAut Y)}
    {ρ₀ : Fin 3 → Y →* C} (hρ₀ : ∀ i, Function.Injective (ρ₀ i))
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ₀ i s * ρ₀ j t = ρ₀ j t * ρ₀ i s)
    (hdec : ∀ ε ∈ E, ∃ m : Fin 3,
      (∀ i, (ρ₀ i).range.map (ind ε).toMonoidHom = (ρ₀ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ a ∈ 𝒟, ∀ s, ind ε (ρ₀ i s) = ρ₀ i (a s))) :
    ∃ ρ : Fin 3 → Y →* G, (∀ i, π.comp (ρ i) = ρ₀ i) ∧
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s) ∧
      (∀ σ : MulAut G, (∀ i s, ind σ (ρ₀ i s) = ρ₀ i s) → ∀ i s, σ (ρ i s) = ρ i s) ∧
      ∀ ε ∈ E, ∃ m : Fin 3, (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ a ∈ 𝒟, ∀ s, ε (ρ i s) = ρ i (a s)) := by
  classical
  haveI : Group.IsPerfect Y := ⟨hY⟩
  choose ρlift hρlift using hlift
  let ρ : Fin 3 → Y →* G := fun i => ρlift (ρ₀ i)
  have hρ : ∀ i, π.comp (ρ i) = ρ₀ i := fun i => hρlift (ρ₀ i)
  have hρpt : ∀ (i : Fin 3) (s : Y), π (ρ i s) = ρ₀ i s :=
    fun i s => DFunLike.congr_fun (hρ i) s
  have hρinj : ∀ i, Function.Injective (ρ i) := by
    intro i s t hst
    apply hρ₀ i
    rw [← hρpt i s, ← hρpt i t]
    exact congrArg (fun x => π x) hst
  have hρcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s := by
    intro i j hij s t
    have h := commute_of_comp_commute_of_perfect (π := π) hY hker (α := ρ i) (g := ρ j t)
      (fun a => by
        rw [hρpt i a, hρpt j t]
        exact hcomm i j hij a t)
    exact Commute.eq (h s)
  have hne : ∀ i j : Fin 3, i ≠ j → (ρ₀ i).range ≠ (ρ₀ j).range := by
    intro i j hij heq
    obtain ⟨x, y, hxy⟩ := hnab
    have hy : ρ₀ i y ∈ (ρ₀ j).range := by
      rw [← heq]
      exact ⟨y, rfl⟩
    rw [MonoidHom.mem_range] at hy
    obtain ⟨t, ht⟩ := hy
    exact hxy (hρ₀ i (by
      rw [map_mul, map_mul, ← ht]
      exact hcomm i j hij x t))
  let m : (ε : MulAut G) → ε ∈ E → Fin 3 := fun ε hε => Classical.choose (hdec ε hε)
  have hm : ∀ (ε : MulAut G) (hε : ε ∈ E) (i : Fin 3),
      (ρ₀ i).range.map (ind ε).toMonoidHom = (ρ₀ (i + m ε hε)).range :=
    fun ε hε => (Classical.choose_spec (hdec ε hε)).1
  have hm0 : ∀ (ε : MulAut G) (hε : ε ∈ E), m ε hε = 0 → ∀ i,
      ∃ a ∈ 𝒟, ∀ s, ind ε (ρ₀ i s) = ρ₀ i (a s) :=
    fun ε hε => (Classical.choose_spec (hdec ε hε)).2
  have hmneg : ∀ (ε : MulAut G) (hε : ε ∈ E), m (ε⁻¹) (E.inv_mem hε) + m ε hε = 0 := by
    intro ε hε
    have hid : (ind ε).toMonoidHom.comp (ind ε⁻¹).toMonoidHom = MonoidHom.id C := by
      ext x
      show ind ε (ind ε⁻¹ x) = x
      rw [map_inv, ← MulAut.mul_apply, mul_inv_cancel]
      simp
    have h2 := hm (ε⁻¹) (E.inv_mem hε) (0 : Fin 3)
    have h3' := congrArg (fun H : Subgroup C => H.map (ind ε).toMonoidHom) h2
    rw [Subgroup.map_map, hid, Subgroup.map_id] at h3'
    rw [hm ε hε (0 + m (ε⁻¹) (E.inv_mem hε))] at h3'
    have h0 : (0 : Fin 3) = 0 + m (ε⁻¹) (E.inv_mem hε) + m ε hε := by
      by_contra hne'
      exact (hne 0 (0 + m (ε⁻¹) (E.inv_mem hε) + m ε hε) hne') h3'
    have h0' : (0 : Fin 3) = m (ε⁻¹) (E.inv_mem hε) + m ε hε := by simpa using h0
    exact h0'.symm
  have hrange : ∀ (ε : MulAut G) (hε : ε ∈ E) (i : Fin 3),
      (ρ i).range.map ε.toMonoidHom = (ρ (i + m ε hε)).range := by
    intro ε hε i
    apply le_antisymm
    · have hle := range_le_of_comp_range_le_of_perfect (π := π) hY hker
        (α := ε.toMonoidHom.comp (ρ i)) (H := (ρ (i + m ε hε)).range) (by
          intro s
          show π (ε (ρ i s)) ∈ (ρ (i + m ε hε)).range.map π
          rw [hind ε (ρ i s), hρpt i s]
          have h2 : ind ε (ρ₀ i s) ∈ (ρ₀ i).range.map (ind ε).toMonoidHom :=
            Subgroup.mem_map_of_mem _ ⟨s, rfl⟩
          rw [hm ε hε i] at h2
          rw [MonoidHom.mem_range] at h2
          obtain ⟨u, hu⟩ := h2
          exact ⟨ρ (i + m ε hε) u, ⟨u, rfl⟩, by
            rw [hρpt (i + m ε hε) u]
            exact hu⟩)
      rwa [MonoidHom.range_comp] at hle
    · intro x hx
      obtain ⟨t, rfl⟩ := hx
      have hle := range_le_of_comp_range_le_of_perfect (π := π) hY hker
        (α := (ε⁻¹).toMonoidHom.comp (ρ (i + m ε hε)))
        (H := (ρ ((i + m ε hε) + m (ε⁻¹) (E.inv_mem hε))).range) (by
          intro s
          show π (ε⁻¹ (ρ (i + m ε hε) s)) ∈
            (ρ ((i + m ε hε) + m (ε⁻¹) (E.inv_mem hε))).range.map π
          rw [hind (ε⁻¹) (ρ (i + m ε hε) s),
            hρpt (i + m ε hε) s]
          have h2 : ind (ε⁻¹) (ρ₀ (i + m ε hε) s) ∈
              (ρ₀ (i + m ε hε)).range.map (ind (ε⁻¹)).toMonoidHom :=
            Subgroup.mem_map_of_mem _ ⟨s, rfl⟩
          rw [hm (ε⁻¹) (E.inv_mem hε) (i + m ε hε)] at h2
          rw [MonoidHom.mem_range] at h2
          obtain ⟨u, hu⟩ := h2
          exact ⟨ρ ((i + m ε hε) + m (ε⁻¹) (E.inv_mem hε)) u, ⟨u, rfl⟩,
            (hρpt ((i + m ε hε) + m (ε⁻¹) (E.inv_mem hε)) u).trans hu⟩)
      have hidx : (i + m ε hε) + m (ε⁻¹) (E.inv_mem hε) = i := by
        rw [add_assoc, add_comm (m ε hε) (m (ε⁻¹) (E.inv_mem hε)), hmneg ε hε, add_zero]
      rw [hidx] at hle
      exact ⟨ε⁻¹ (ρ (i + m ε hε) t), hle ⟨t, rfl⟩, by simp⟩
  have hconj : ∀ (ε : MulAut G) (hε : ε ∈ E), m ε hε = 0 → ∀ i,
      ∃ a ∈ 𝒟, ∀ s, ε (ρ i s) = ρ i (a s) := by
    intro ε hε h0 i
    obtain ⟨a, haD, ha⟩ := hm0 ε hε h0 i
    refine ⟨a, haD, fun s => ?_⟩
    have hcomp : π.comp (ε.toMonoidHom.comp (ρ i)) =
        π.comp ((ρ i).comp a.toMonoidHom) := by
      ext s
      exact calc π (ε (ρ i s)) = ind ε (π (ρ i s)) := hind ε (ρ i s)
        _ = ind ε (ρ₀ i s) := by rw [hρpt i s]
        _ = ρ₀ i (a s) := ha s
        _ = π (ρ i (a s)) := (hρpt i (a s)).symm
    simpa using DFunLike.congr_fun
      (CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker hcomp) s
  have hfix : ∀ (σ : MulAut G), (∀ i s, ind σ (ρ₀ i s) = ρ₀ i s) →
      ∀ i s, σ (ρ i s) = ρ i s := by
    intro σ hσρ i
    have hcomp : π.comp (σ.toMonoidHom.comp (ρ i)) = π.comp (ρ i) := by
      ext s
      change π (σ (ρ i s)) = π (ρ i s)
      rw [hind σ (ρ i s), hρpt i s]
      exact hσρ i s
    have h := CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker hcomp
    intro s
    simpa using DFunLike.congr_fun h s
  refine ⟨ρ, hρ, hρinj, hρcomm, hfix, fun ε hε => ⟨m ε hε, hrange ε hε, hconj ε hε⟩⟩

theorem exists_lift_layer_le_seitzHyperGamma {k : Type} [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (ind : MulAut G →* MulAut C)
    (hind : ∀ (f : MulAut G) (g : G), π (f g) = ind f (π g))
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    {ρ₀ : Fin 3 → SpecialLinearGroup (Fin 3) k →* C} (hρ₀ : ∀ i, Function.Injective (ρ₀ i))
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ₀ i s * ρ₀ j t = ρ₀ j t * ρ₀ i s)
    {σ : MulAut G} (hσ : σ ∈ E) (hσ1 : σ ≠ 1) (hσρ : ∀ i s, ind σ (ρ₀ i s) = ρ₀ i s)
    (hdec : ∀ ε ∈ E, ∃ m : Fin 3,
      (∀ i, (ρ₀ i).range.map (ind ε).toMonoidHom = (ρ₀ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ γ : GL (Fin 3) k, ∀ s, ind ε (ρ₀ i s) = ρ₀ i (conjSL γ s))) :
    ∃ ρ : Fin 3 → SpecialLinearGroup (Fin 3) k →* G,
      (∀ i, π.comp (ρ i) = ρ₀ i) ∧ ∀ i, (ρ i).range ≤ seitzHyperGamma 3 E := by
  haveI : Group.IsPerfect (SpecialLinearGroup (Fin 3) k) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (n := 3) (by norm_num)
  have hA : commutator (SpecialLinearGroup (Fin 3) k) = ⊤ := Group.IsPerfect.commutator_eq_top
  have hk : 5 ≤ Nat.card k := four_lt_card_of_three_dvd h3 h4
  have hdec' : ∀ ε ∈ E, ∃ m : Fin 3,
      (∀ i, (ρ₀ i).range.map (ind ε).toMonoidHom = (ρ₀ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ a ∈ (conjSL (K := k)).range, ∀ s,
          ind ε (ρ₀ i s) = ρ₀ i (a s)) := by
    intro ε hε
    obtain ⟨m, hm1, hm2⟩ := hdec ε hε
    exact ⟨m, hm1, fun h0 i => by
      obtain ⟨γ, hγ⟩ := hm2 h0 i
      exact ⟨conjSL γ, ⟨γ, rfl⟩, hγ⟩⟩
  obtain ⟨ρ, hρ, hρinj, hρcomm, hfix, hdecρ⟩ :=
    exists_lift_frames (Y := SpecialLinearGroup (Fin 3) k) (C := C) (π := π)
      hA (exists_not_commute_SL3 (K := k) h3)
      (fun β => exists_lift_SL3 (k := k) hk hπ hker β) hker ind hind hρ₀ hcomm hdec'
  refine ⟨ρ, hρ, fun i => ?_⟩
  have hdecγ : ∀ ε ∈ E, ∃ m : Fin 3,
      (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ γ : GL (Fin 3) k, ∀ s, ε (ρ i s) = ρ i (conjSL γ s)) := by
    intro ε hε
    obtain ⟨m, hm1, hm2⟩ := hdecρ ε hε
    exact ⟨m, hm1, fun h0 i => by
      obtain ⟨a, ⟨γ, rfl⟩, ha⟩ := hm2 h0 i
      exact ⟨γ, ha⟩⟩
  exact layerStep_of_three_copies h3 h4 hE hcard hρinj hρcomm hσ hσ1
    (hfix σ hσρ) hdecγ i

theorem seitzHyperGamma_eq_top_of_layers (hperf : commutator G = ⊤)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G) {p : ℕ}
    {E : Subgroup (MulAut G)} {ι : Type*} (L : ι → Subgroup G)
    (hL : ∀ j, L j ≤ seitzHyperGamma p E)
    (hgen : (⊤ : Subgroup C) ≤ ⨆ j, (L j).map π) : seitzHyperGamma p E = ⊤ := by
  have hmap : (seitzHyperGamma p E).map π = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup C) ≤ ⨆ j, (L j).map π := hgen
      _ ≤ (seitzHyperGamma p E).map π := iSup_le fun j => Subgroup.map_mono (hL j)
  have hsup : seitzHyperGamma p E ⊔ Subgroup.center G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : π g ∈ (seitzHyperGamma p E).map π := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.1 hg
    have hz : h⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
    have e : g = h * (h⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hh (hker hz)
  exact CFSG.LieType.SeitzGeneration.QuasiHigh.eq_top_of_sup_center_eq_top hperf hsup

theorem seitzHyperGamma_eq_top_of_uniPlaneGen_layers (hperf : commutator G = ⊤)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (ind : MulAut G →* MulAut C) {p r : ℕ} {E P : Subgroup (MulAut G)}
    (hgen : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniPlaneGen r (P.map ind))
    (L : MulAut G → Subgroup G)
    (hL : ∀ φ ∈ P, ind φ ≠ 1 → L φ ≤ seitzHyperGamma p E)
    (hr : ∀ φ ∈ P, ind φ ≠ 1 → ∀ c : C, ind φ c = c → (∃ n : ℕ, c ^ (r ^ n) = 1) →
      c ∈ (L φ).map π) : seitzHyperGamma p E = ⊤ := by
  have hgen' : (⊤ : Subgroup C) ≤
      ⨆ j : {φ : MulAut G // φ ∈ P ∧ ind φ ≠ 1}, (L (j : MulAut G)).map π := by
    have hclo : Subgroup.closure {s : C | ∃ e ∈ P.map ind, e ≠ 1 ∧ e s = s ∧
        ∃ n : ℕ, s ^ (r ^ n) = 1} = ⊤ := hgen
    rw [← hclo, Subgroup.closure_le]
    rintro c ⟨e, he, he1, hfix, n, hpow⟩
    rw [Subgroup.mem_map] at he
    obtain ⟨φ, hφP, rfl⟩ := he
    exact Subgroup.mem_iSup_of_mem ⟨φ, hφP, he1⟩ (hr φ hφP he1 c hfix ⟨n, hpow⟩)
  exact seitzHyperGamma_eq_top_of_layers (p := p) (E := E)
    (ι := {φ : MulAut G // φ ∈ P ∧ ind φ ≠ 1}) hperf hπ hker
    (fun j => L j.1) (fun j => hL j.1 j.2.1 j.2.2) hgen'

end CFSG.LieType.SeitzGeneration.CubeCoverLayer
