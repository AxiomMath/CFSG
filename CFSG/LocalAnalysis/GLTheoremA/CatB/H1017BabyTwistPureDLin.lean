module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureDSeven
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.PureD

open Module CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
variable {E : Type*} [CommGroup E]

theorem exists_ne_one_six_le_finrank_Csub [Finite E] (hE3 : ∀ e : E, e ^ 3 = 1)
    (ρ : E →* Module.End (ZMod 2) V) (hρ : ∀ e : E, (∀ v, ρ e v = v) → e = 1)
    (hE : Nat.card E = 3 ^ 4) : ∃ a : E, a ≠ 1 ∧ 6 ≤ finrank (ZMod 2) (Csub ρ a ⊤) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : ∀ e : E, ∀ u ∈ (⊤ : Submodule (ZMod 2) V), ρ e u ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun _ _ _ => Submodule.mem_top
  obtain ⟨y₀, hy₀⟩ : ∃ y : E, y ≠ 1 := by
    by_contra! h
    have h1 : Nat.card E = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => (h a).trans (h c).symm⟩, ⟨1⟩⟩
    rw [hE] at h1
    norm_num at h1
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image {a : E | a ≠ 1}
    (fun a => finrank (ZMod 2) (Csub ρ a ⊤)) (Set.toFinite _) ⟨y₀, hy₀⟩
  refine ⟨a, ha, ?_⟩
  by_contra! hlt
  have hidx : (fixSub ρ (Csub ρ a ⊤)).index ≤ 9 := by
    have h := index_fixSub_le hE3 ρ _ _ rfl fun e u hu => Csub_invariant ρ a ⊤ hU hu
    have h2 : 3 ^ (finrank (ZMod 2) (Csub ρ a ⊤) / 2) ≤ 3 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact h.trans (h2.trans (by norm_num))
  have hK9 : 9 ≤ Nat.card (fixSub ρ (Csub ρ a ⊤)) := by
    have h := (fixSub ρ (Csub ρ a ⊤)).card_mul_index
    rw [hE] at h
    by_contra! h8
    have := Nat.mul_le_mul (Nat.le_of_lt_succ h8) hidx
    omega
  have hDinv : ∀ e : E, ∀ u ∈ Dsub ρ a ⊤, ρ e u ∈ Dsub ρ a ⊤ :=
    fun e u hu => Dsub_invariant ρ a ⊤ hU hu
  have hfpf : ∀ b ∈ fixSub ρ (Csub ρ a ⊤), b ≠ 1 → Csub ρ b (Dsub ρ a ⊤) = ⊥ := by
    intro b hb hb1
    by_contra hne
    have hle : Csub ρ a ⊤ ⊔ Csub ρ b (Dsub ρ a ⊤) ≤ Csub ρ b ⊤ := sup_le
      (fun x hx => (mem_Csub ρ b ⊤).2 ⟨Submodule.mem_top, mem_fixSub.1 hb x hx⟩)
      (fun x hx => (mem_Csub ρ b ⊤).2 ⟨Submodule.mem_top, ((mem_Csub ρ b _).1 hx).2⟩)
    have hdisj : Csub ρ a ⊤ ⊓ Csub ρ b (Dsub ρ a ⊤) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ Csub ρ a ⊤ ⊓ Dsub ρ a ⊤ :=
        ⟨(Submodule.mem_inf.1 hx).1, ((mem_Csub ρ b _).1 (Submodule.mem_inf.1 hx).2).1⟩
      rwa [Csub_inf_Dsub] at hx'
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Csub ρ a ⊤) (Csub ρ b (Dsub ρ a ⊤))
    rw [hdisj, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_mono hle
    have h3 := Submodule.one_le_finrank_iff.2 hne
    have h4 : finrank (ZMod 2) (Csub ρ b ⊤) ≤ finrank (ZMod 2) (Csub ρ a ⊤) := hmax b hb1
    omega
  have hfaith : ∀ b ∈ fixSub ρ (Csub ρ a ⊤), (∀ u ∈ Dsub ρ a ⊤, ρ b u = u) → b = 1 := by
    intro b hb hbD
    refine hρ b fun v => ?_
    have hv : v ∈ Csub ρ a ⊤ ⊔ Dsub ρ a ⊤ := by
      rw [Csub_add_Dsub ρ hE3 a ⊤ hU]
      exact Submodule.mem_top
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, mem_fixSub.1 hb c hc, hbD d hd]
  obtain ⟨y, hyK, hy1⟩ : ∃ y ∈ fixSub ρ (Csub ρ a ⊤), y ≠ 1 := by
    by_contra! h
    rw [(Subgroup.eq_bot_iff_forall _).2 h, Subgroup.card_bot] at hK9
    omega
  have hsub : (fixSub ρ (Csub ρ a ⊤) : Set E) ⊆ {1, y, y⁻¹} := by
    intro z hz
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    by_cases hyz : y * z = 1
    · exact Or.inr (Or.inr (eq_inv_of_mul_eq_one_right hyz))
    refine Or.inr (Or.inl ?_)
    have h3 : ∀ u ∈ Dsub ρ a ⊤, ρ y u = ρ z u := fun u hu =>
      eq_of_three ρ hE3 _ hDinv y z (hfpf y hyK hy1) (hfpf z hz hz1)
        (hfpf _ (Subgroup.mul_mem _ hyK hz) hyz) hu
    have h4 : y * z⁻¹ = 1 := hfaith _ (Subgroup.mul_mem _ hyK (Subgroup.inv_mem _ hz))
      fun u hu => by
        rw [map_mul, Module.End.mul_apply, h3 _ (hDinv _ u hu), ← Module.End.mul_apply,
          ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    exact (mul_inv_eq_one.1 h4).symm
  have h3 : Nat.card (fixSub ρ (Csub ρ a ⊤)) ≤ 3 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc (fixSub ρ (Csub ρ a ⊤) : Set E).ncard ≤ ({1, y, y⁻¹} : Set E).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({y, y⁻¹} : Set E).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ ({y⁻¹} : Set E).ncard + 1 + 1 := by
          have := Set.ncard_insert_le y ({y⁻¹} : Set E)
          omega
      _ = 3 := by rw [Set.ncard_singleton]
  omega

section Form

variable (b : LinearMap.BilinForm (ZMod 2) V)

theorem apply_eq_zero_of_mem_Csub_of_mem_Dsub (ρ : E →* Module.End (ZMod 2) V) {a : E}
    (ha : ∀ u v, b (ρ a u) (ρ a v) = b u v) {x y : V} (hx : x ∈ Csub ρ a ⊤)
    (hy : y ∈ Dsub ρ a ⊤) : b x y = 0 := by
  have hx' : ρ a x = x := ((mem_Csub ρ a ⊤).1 hx).2
  have hy' : ρ a (ρ a y) + ρ a y + y = 0 := ((mem_Dsub ρ a ⊤).1 hy).2
  have h1 : b x (ρ a y) = b x y := by
    calc b x (ρ a y) = b (ρ a x) (ρ a y) := by rw [hx']
      _ = b x y := ha x y
  have h2 : b x (ρ a (ρ a y)) = b x y := by
    calc b x (ρ a (ρ a y)) = b (ρ a x) (ρ a (ρ a y)) := by rw [hx']
      _ = b x (ρ a y) := ha x (ρ a y)
      _ = b x y := h1
  have h3 := congrArg (b x) hy'
  rw [map_add, map_add, h1, h2, map_zero] at h3
  have key : ∀ c : ZMod 2, c + c + c = c := by decide
  rwa [key] at h3

theorem nondegenerate_restrict_Csub [Finite E] (hE3 : ∀ e : E, e ^ 3 = 1) (hb : b.Nondegenerate)
    (hsymm : ∀ u v, b u v = b v u) (ρ : E →* Module.End (ZMod 2) V) {a : E}
    (ha : ∀ u v, b (ρ a u) (ρ a v) = b u v) : (b.restrict (Csub ρ a ⊤)).Nondegenerate := by
  have hU : ∀ e : E, ∀ u ∈ (⊤ : Submodule (ZMod 2) V), ρ e u ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun _ _ _ => Submodule.mem_top
  have hleft : ∀ x : Csub ρ a ⊤, (∀ w : Csub ρ a ⊤, b x w = 0) → x = 0 := by
    intro x hx
    have hall : ∀ v, b x v = 0 := by
      intro v
      have hv : v ∈ Csub ρ a ⊤ ⊔ Dsub ρ a ⊤ := by
        rw [Csub_add_Dsub ρ hE3 a ⊤ hU]
        exact Submodule.mem_top
      obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hv
      have hxc : b x c = 0 := hx ⟨c, hc⟩
      rw [map_add, hxc, apply_eq_zero_of_mem_Csub_of_mem_Dsub b ρ ha x.2 hd, add_zero]
    exact Subtype.ext (hb.1 _ hall)
  refine ⟨fun x hx => hleft x hx, fun y hy => hleft y fun w => ?_⟩
  rw [hsymm]
  exact hy w

theorem exists_hyperbolic_triple [Finite E] (hE3 : ∀ e : E, e ^ 3 = 1) (hb : b.Nondegenerate)
    (hbalt : b.IsAlt) (ρ : E →* Module.End (ZMod 2) V) {a : E}
    (ha : ∀ u v, b (ρ a u) (ρ a v) = b u v) (h6 : 6 ≤ finrank (ZMod 2) (Csub ρ a ⊤)) :
    ∃ e f : Fin 3 → V, (∀ i, ρ a (e i) = e i) ∧ (∀ i, ρ a (f i) = f i) ∧
      (∀ i j, b (e i) (e j) = 0) ∧ (∀ i j, b (f i) (f j) = 0) ∧
      ∀ i j, b (e i) (f j) = if i = j then 1 else 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsymm : ∀ u v, b u v = b v u := fun u v => by
    rw [← hbalt.neg_eq u v, ZMod.neg_eq_self_mod_two]
  have hnd := nondegenerate_restrict_Csub b hE3 hb hsymm ρ ha
  have halt : (b.restrict (Csub ρ a ⊤)).IsAlt := fun x => hbalt.self_eq_zero x
  obtain ⟨m, bW, hbW⟩ := halt.exists_basis_toMatrix_eq_J hnd
  have hm : 3 ≤ m := by
    have := finrank_eq_card_basis bW
    rw [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hJ : ∀ x y, b (bW x) (bW y) = Matrix.J (Fin m) (ZMod 2) x y := fun x y => by
    rw [← hbW, LinearMap.BilinForm.toMatrix_apply]
    rfl
  have hfix : ∀ x, ρ a (bW x) = bW x := fun x => ((mem_Csub ρ a ⊤).1 (bW x).2).2
  refine ⟨fun i => bW (Sum.inl (Fin.castLE hm i)), fun i => bW (Sum.inr (Fin.castLE hm i)),
    fun i => hfix _, fun i => hfix _, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [hJ]
    simp [Matrix.J]
  · rw [hJ]
    simp [Matrix.J]
  · rw [hJ]
    simp [Matrix.J, Matrix.one_apply, ZMod.neg_eq_self_mod_two, Fin.castLE_inj]

theorem exists_commute_isometry_orderOf_seven [Finite E] (hE3 : ∀ e : E, e ^ 3 = 1)
    (hb : b.Nondegenerate) (hbalt : b.IsAlt) (ρ : E →* Module.End (ZMod 2) V)
    (hρ : ∀ e : E, (∀ v, ρ e v = v) → e = 1) (hiso : ∀ e u v, b (ρ e u) (ρ e v) = b u v)
    (hE : Nat.card E = 3 ^ 4) :
    ∃ a : E, a ≠ 1 ∧ ∃ T : V ≃ₗ[ZMod 2] V, T ∈ TauCeti.BilinForm.isometryGroup b ∧
      orderOf T = 7 ∧ ∀ x, T (ρ a x) = ρ a (T x) := by
  obtain ⟨a, ha, h6⟩ := exists_ne_one_six_le_finrank_Csub hE3 ρ hρ hE
  obtain ⟨e, f, hea, hfa, hee, hff, hef⟩ :=
    exists_hyperbolic_triple b hE3 hb hbalt ρ (hiso a) h6
  obtain ⟨T, hT, hT7, hTc⟩ := exists_isometry_orderOf_seven hbalt e f hee hff hef
  exact ⟨a, ha, T, hT, hT7, hTc (ρ a) (hiso a) hea hfa⟩

end Form

end CFSG.LocalAnalysis.GLTheoremA.H1017.PureD
