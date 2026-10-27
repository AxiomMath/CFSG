module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Egl

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup
open scoped commutatorElement

variable {Y V : Type} [Group Y] [AddCommGroup V] [Module (ZMod 2) V]

theorem rho_conj_sub_one (ρ : Representation (ZMod 2) Y V) (n m : Y) (v : V) :
    ρ n ((ρ m - 1) v) = (ρ (n * m * n⁻¹) - 1) (ρ n v) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ n⁻¹),
    ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem commSub_invariant (ρ : Representation (ZMod 2) Y V) {H N : Subgroup Y}
    (hn : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) {n : Y} (hnN : n ∈ N) {w : V}
    (hw : w ∈ commSub ρ H) : ρ n w ∈ commSub ρ H := by
  refine Submodule.iSup_induction _ (motive := fun w => ρ n w ∈ commSub ρ H) hw ?_ ?_ ?_
  · intro h w' hw'
    refine Submodule.iSup_induction _ (motive := fun w => ρ n w ∈ commSub ρ H) hw' ?_ ?_ ?_
    · intro hh w'' hw''
      obtain ⟨u, rfl⟩ := hw''
      rw [rho_conj_sub_one]
      exact apply_sub_one_mem_commSub (hn n hnN h hh) _
    · simp
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  · simp
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb


theorem endgame_Y [Finite Y] [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) Y V)
    {P J E N₁ N₀ : Subgroup Y} {z : Y}
    (hP : IsPGroup 5 P) (hJP : J ≤ P) (hJe : CFSG.Open.IsElemAbelian 5 J)
    (hJcard : Nat.card J = 5 ^ 4) (hEJ : E ≤ J) (hEcard : Nat.card E = 5 ^ 3)
    (hEP : E ≤ ⁅J, P⁆) (hPN : P ≤ N₁)
    (hJn : ∀ g ∈ N₁, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hEn : ∀ g ∈ N₁, ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hN₀N : N₀ ≤ N₁) (hN₀n : ∀ g ∈ N₁, ∀ m ∈ N₀, g * m * g⁻¹ ∈ N₀) (hEN₀ : E ≤ N₀)
    (hirr : ∀ S : Subgroup Y, S ≤ N₁ → S.relIndex N₁ ≤ 5 → ∀ F : Subgroup Y, F ≤ E →
      (∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ ∈ F) → F = ⊥ ∨ F = E)
    (hz : z ∈ E) (hρz : ρ z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (commSub ρ N₀) ≤ 36) : False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have hW0inv : ∀ n ∈ N₁, ∀ w ∈ commSub ρ E, ρ n w ∈ commSub ρ E :=
    fun n hn w hw => commSub_invariant ρ hEn hn hw
  have hW0ne : commSub ρ E ≠ ⊥ := by
    intro h
    apply hρz
    refine LinearMap.ext fun u => ?_
    have h1 : (ρ z - 1) u ∈ commSub ρ E := apply_sub_one_mem_commSub hz u
    rw [h, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    exact h1
  let 𝒮 : Set (Submodule (ZMod 2) V) :=
    {U | U ≤ commSub ρ E ∧ U ≠ ⊥ ∧ ∀ n ∈ N₁, ∀ u ∈ U, ρ n u ∈ U}
  have h𝒮ne : 𝒮.Nonempty := ⟨commSub ρ E, le_rfl, hW0ne, hW0inv⟩
  obtain ⟨V₁, ⟨hV₁W, hV₁ne, hV₁inv⟩, hmin⟩ := Set.exists_min_image 𝒮
    (fun U => Module.finrank (ZMod 2) U) (Set.toFinite 𝒮) h𝒮ne
  have hirrV : ∀ U : Submodule (ZMod 2) V, U ≤ V₁ → (∀ n ∈ N₁, ∀ u ∈ U, ρ n u ∈ U) → U ≠ ⊥ →
      U = V₁ := by
    intro U hUV hUinv hUne
    exact Submodule.eq_of_le_of_finrank_le hUV (hmin U ⟨hUV.trans hV₁W, hUne, hUinv⟩)
  letI : Fintype E := Fintype.ofFinite E
  have hodd : Odd (Fintype.card E) := by
    rw [Fintype.card_eq_nat_card, hEcard]
    decide
  have hfixV : ∀ w : V, w ∈ V₁ → (∀ e ∈ E, ρ e w = w) → w = 0 := by
    intro w hw hfw
    exact (Submodule.disjoint_def.mp (disjoint_fixSub_commSub ρ E hodd)) _
      (mem_fixSub.mpr hfw) (hV₁W hw)
  let U₁ : Submodule (ZMod 2) V := ⨆ m ∈ N₀, V₁.map (ρ m - 1)
  have hU₁V : U₁ ≤ V₁ := by
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hV₁inv m (hN₀N hm) u hu
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact V₁.sub_mem h1 hu
  have hU₁inv : ∀ n ∈ N₁, ∀ w ∈ U₁, ρ n w ∈ U₁ := by
    intro n hn w hw
    refine Submodule.iSup_induction _ (motive := fun w => ρ n w ∈ U₁) hw ?_ ?_ ?_
    · intro m w' hw'
      refine Submodule.iSup_induction _ (motive := fun w => ρ n w ∈ U₁) hw' ?_ ?_ ?_
      · intro hm w'' hw''
        obtain ⟨u, hu, rfl⟩ := hw''
        rw [rho_conj_sub_one]
        exact Submodule.mem_iSup_of_mem (n * m * n⁻¹) (Submodule.mem_iSup_of_mem
          (hN₀n n hn m hm) ⟨ρ n u, hV₁inv n hn u hu, rfl⟩)
      · simp
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    · simp
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  have hU₁ne : U₁ ≠ ⊥ := by
    intro h
    apply hV₁ne
    rw [Submodule.eq_bot_iff]
    intro w hw
    refine hfixV w hw fun e he => ?_
    have h1 : (ρ e - 1) w ∈ U₁ :=
      Submodule.mem_iSup_of_mem e (Submodule.mem_iSup_of_mem (hEN₀ he) ⟨w, hw, rfl⟩)
    rw [h, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    exact h1
  have hU₁eq : U₁ = V₁ := hirrV U₁ hU₁V hU₁inv hU₁ne
  have hV₁dim : Module.finrank (ZMod 2) V₁ ≤ 36 := by
    refine le_trans (Submodule.finrank_mono ?_) hdim
    rw [← hU₁eq]
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨u, -, rfl⟩
    exact apply_sub_one_mem_commSub hm u
  let ρ₁ : Representation (ZMod 2) ↥N₁ ↥V₁ :=
    { toFun := fun n => (ρ (n : Y)).restrict (fun u hu => hV₁inv n n.2 u hu)
      map_one' := by
        refine LinearMap.ext fun u => Subtype.ext ?_
        simp
      map_mul' := fun a b => by
        refine LinearMap.ext fun u => Subtype.ext ?_
        simp }
  have hρ₁ : ∀ (n : ↥N₁) (u : ↥V₁), ((ρ₁ n u : ↥V₁) : V) = ρ (n : Y) (u : V) := fun n u => rfl
  haveI : Nontrivial ↥V₁ := Submodule.nontrivial_iff_ne_bot.mpr hV₁ne
  haveI : Finite ↥V₁ := inferInstance
  have hJN : J ≤ N₁ := hJP.trans hPN
  have hEN : E ≤ N₁ := hEJ.trans hJN
  have hcardsub : ∀ {K : Subgroup Y}, K ≤ N₁ → Nat.card (K.subgroupOf N₁) = Nat.card K :=
    fun {K} hK => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  refine endgame_core ρ₁ (P := P.subgroupOf N₁) (J := J.subgroupOf N₁) (E := E.subgroupOf N₁)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hP.of_injective (Subgroup.subgroupOfEquivOfLe hPN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPN).injective
  · exact fun x hx => hJP hx
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · refine Subtype.ext (Subtype.ext ?_)
      exact congrArg (fun t : ↥J => (t : Y)) (hJe.1.is_comm.comm
        (⟨((a : ↥(J.subgroupOf N₁)) : ↥N₁).1, a.2⟩ : J)
        ⟨((b : ↥(J.subgroupOf N₁)) : ↥N₁).1, b.2⟩)
    · exact Subtype.ext (hJe.2 _ hx)
  · rw [hcardsub hJN, hJcard]
  · intro g j hj
    exact hJn g g.2 j hj
  · exact fun x hx => hEJ hx
  · rw [hcardsub hEN, hEcard]
  · intro g e he
    exact hEn g g.2 e he
  ·
    intro e he
    have h1 : (e : Y) ∈ ⁅J, P⁆ := hEP he
    have h2 : ⁅J.subgroupOf N₁, P.subgroupOf N₁⁆.map N₁.subtype = ⁅J, P⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJN,
        Subgroup.map_subgroupOf_eq_of_le hPN]
    rw [← h2] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    have : x = e := Subtype.ext hxe
    rwa [this] at hx
  · intro S' hS' F' hF'E hF'inv
    have hSN : S'.map N₁.subtype ≤ N₁ := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hrel : (S'.map N₁.subtype).relIndex N₁ = S'.index := by
      rw [Subgroup.relIndex]
      change ((S'.map N₁.subtype).comap N₁.subtype).index = _
      rw [Subgroup.comap_map_eq_self_of_injective N₁.subtype_injective]
    have hFE : F'.map N₁.subtype ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact hF'E hx
    have hinv : ∀ s ∈ S'.map N₁.subtype, ∀ f ∈ F'.map N₁.subtype,
        s * f * s⁻¹ ∈ F'.map N₁.subtype := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨f, hf, rfl⟩
      exact ⟨s * f * s⁻¹, hF'inv s hs f hf, by simp⟩
    rcases hirr _ hSN (by rw [hrel]; exact hS') _ hFE hinv with h | h
    · left
      have h1 := (Subgroup.map_eq_bot_iff _).mp h
      rw [N₁.ker_subtype] at h1
      exact le_bot_iff.mp h1
    · right
      calc F' = (F'.map N₁.subtype).comap N₁.subtype :=
            (Subgroup.comap_map_eq_self_of_injective N₁.subtype_injective F').symm
        _ = E.subgroupOf N₁ := by rw [h]; rfl
  · exact hV₁dim
  · intro w hw
    refine Subtype.ext (hfixV w w.2 fun e he => ?_)
    have h1 := hw ⟨e, hEN he⟩ (Subgroup.mem_subgroupOf.mpr he)
    exact congrArg Subtype.val h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
