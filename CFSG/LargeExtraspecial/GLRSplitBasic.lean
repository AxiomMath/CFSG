module

public import CFSG.LargeExtraspecial.GLRConfig

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

namespace Config

theorem polar_eq_zero_of_mem_At {v w : S.Qt} (hv : v ∈ C.At) (hw : w ∈ C.At) :
    polar S.q v w = 0 := by
  rw [polar, C.q_At _ (C.At.add_mem hv hw), C.q_At _ hv, C.q_At _ hw, sub_zero, sub_zero]

theorem polar_eq_zero_of_mem_Bt {v w : S.Qt} (hv : v ∈ C.Bt) (hw : w ∈ C.Bt) :
    polar S.q v w = 0 := by
  rw [polar, C.q_Bt _ (C.Bt.add_mem hv hw), C.q_Bt _ hv, C.q_Bt _ hw, sub_zero, sub_zero]

theorem finrank_Qt : finrank (ZMod 2) S.Qt = 2 * S.width := S.finrank_Qt_eq_two_mul_width

theorem orthogonal_eq_self {W : Submodule (ZMod 2) S.Qt} (hW : ∀ v ∈ W, S.q v = 0)
    (hdim : finrank (ZMod 2) W = S.width) :
    LinearMap.BilinForm.orthogonal S.q.polarBilin W = W := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    change polar S.q u v = 0
    rw [polar, hW _ (W.add_mem hu hv), hW _ hu, hW _ hv, sub_zero, sub_zero]
  have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width, hdim] at h1
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, hdim]; omega)).symm

theorem mem_At_of_forall_polar {v : S.Qt} (h : ∀ w ∈ C.At, polar S.q w v = 0) : v ∈ C.At := by
  rw [← orthogonal_eq_self C.q_At C.finrank_At, LinearMap.BilinForm.mem_orthogonal_iff]
  exact h

theorem mem_Bt_of_forall_polar {v : S.Qt} (h : ∀ w ∈ C.Bt, polar S.q w v = 0) : v ∈ C.Bt := by
  rw [← orthogonal_eq_self C.q_Bt C.finrank_Bt, LinearMap.BilinForm.mem_orthogonal_iff]
  exact h

theorem eq_zero_of_mem_inf {v : S.Qt} (hA : v ∈ C.At) (hB : v ∈ C.Bt) : v = 0 := by
  have : v ∈ C.At ⊓ C.Bt := ⟨hA, hB⟩
  rwa [C.inf_eq, Submodule.mem_bot] at this

theorem eq_zero_of_mem_Bt_of_forall_polar {w : S.Qt} (hw : w ∈ C.Bt)
    (h : ∀ v ∈ C.At, polar S.q v w = 0) : w = 0 :=
  C.eq_zero_of_mem_inf (C.mem_At_of_forall_polar h) hw

theorem eq_zero_of_mem_At_of_forall_polar {v : S.Qt} (hv : v ∈ C.At)
    (h : ∀ w ∈ C.Bt, polar S.q w v = 0) : v = 0 :=
  C.eq_zero_of_mem_inf hv (C.mem_Bt_of_forall_polar h)

theorem exists_eq_add (v : S.Qt) : ∃ a ∈ C.At, ∃ b ∈ C.Bt, a + b = v := by
  have : v ∈ C.At ⊔ C.Bt := by rw [C.sup_eq]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, h⟩ := Submodule.mem_sup.mp this
  exact ⟨a, ha, b, hb, h⟩

theorem eq_of_add_eq {a a' b b' : S.Qt} (ha : a ∈ C.At) (ha' : a' ∈ C.At) (hb : b ∈ C.Bt)
    (hb' : b' ∈ C.Bt) (h : a + b = a' + b') : a = a' ∧ b = b' := by
  have h1 : a - a' = b' - b := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
  have h2 : a - a' = 0 := C.eq_zero_of_mem_inf (C.At.sub_mem ha ha') (h1 ▸ C.Bt.sub_mem hb' hb)
  refine ⟨sub_eq_zero.mp h2, ?_⟩
  rw [h2] at h1
  exact (sub_eq_zero.mp h1.symm).symm

theorem exists_mem_Bt_polar_eq (f : C.At →+ ZMod 2) :
    ∃ w ∈ C.Bt, ∀ v (hv : v ∈ C.At), polar S.q v w = f ⟨v, hv⟩ := by
  let Φ : C.Bt →ₗ[ZMod 2] Dual (ZMod 2) C.At :=
    ((S.q.polarBilin.domRestrict₁₂ C.At C.Bt).flip)
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    refine Subtype.ext (C.eq_zero_of_mem_Bt_of_forall_polar w.2 fun v hv => ?_)
    have := LinearMap.congr_fun hw ⟨v, hv⟩
    exact this
  have hrank : finrank (ZMod 2) C.Bt = finrank (ZMod 2) (Dual (ZMod 2) C.At) := by
    rw [Subspace.dual_finrank_eq, C.finrank_At, C.finrank_Bt]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hΦ
  obtain ⟨w, hw⟩ := hsurj (f.toZModLinearMap 2)
  refine ⟨w, w.2, fun v hv => ?_⟩
  have := LinearMap.congr_fun hw ⟨v, hv⟩
  exact this

theorem polar_apply_apply (x : S.O) (v w : S.Qt) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      polar S.q v w := by
  simp only [polar, ← map_add]
  rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2]

theorem apply_inv_apply (x : S.O) (v : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
  LinearEquiv.apply_symm_apply _ v

theorem inv_apply_apply (x : S.O) (v : S.Qt) :
    ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
  LinearEquiv.symm_apply_apply _ v

theorem mul_apply (x y : S.O) (v : S.Qt) :
    ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem eq_one_of_forall_At {x : S.O} (hx : x ∈ C.Xbar)
    (h : ∀ v ∈ C.At, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : x = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun u => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := C.exists_eq_add u
  have hb' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b := by
    have := C.eq_zero_of_mem_Bt_of_forall_polar (C.Bt.sub_mem (C.apply_Bt x hx b hb) hb)
      fun v hv => by
        rw [polar_sub_right, ← polar_apply_apply x v b, h v hv, sub_self]
    exact sub_eq_zero.mp this
  change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b) = a + b
  rw [map_add, h a ha, hb']

theorem eq_one_of_forall_Bt {x : S.O} (hx : x ∈ C.Xbar)
    (h : ∀ v ∈ C.Bt, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : x = 1 := by
  refine C.eq_one_of_forall_At hx fun a ha => ?_
  have := C.eq_zero_of_mem_At_of_forall_polar (C.At.sub_mem (C.apply_At x hx a ha) ha)
    fun v hv => by
      rw [polar_sub_right, ← polar_apply_apply x v a, h v hv, sub_self]
  exact sub_eq_zero.mp this

theorem mul_mem_Xbar_iff {σ τ : S.O} (hσ : σ ∈ S.Mbar) (hτ : τ ∈ S.Mbar) :
    σ * τ ∈ C.Xbar ↔ (σ ∈ C.Xbar ↔ τ ∈ C.Xbar) := by
  have h2 : (C.Xbar.subgroupOf S.Mbar).index = 2 := C.relIndex_Xbar
  have := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨σ, hσ⟩) (b := ⟨τ, hτ⟩)
  rw [mem_subgroupOf, mem_subgroupOf, mem_subgroupOf] at this
  exact this

theorem mul_mem_Xbar_of_not_mem {σ τ : S.O} (hσ : σ ∈ S.Mbar) (hτ : τ ∈ S.Mbar)
    (hσX : σ ∉ C.Xbar) (hτX : τ ∉ C.Xbar) : σ * τ ∈ C.Xbar :=
  (C.mul_mem_Xbar_iff hσ hτ).mpr (iff_of_false hσX hτX)

theorem conj_mem_Xbar {g x : S.O} (hg : g ∈ S.Mbar) (hx : x ∈ C.Xbar) :
    g * x * g⁻¹ ∈ C.Xbar := by
  have h2 : (C.Xbar.subgroupOf S.Mbar).index = 2 := C.relIndex_Xbar
  have hn := Subgroup.normal_of_index_eq_two h2
  have := hn.conj_mem ⟨x, C.Xbar_le hx⟩ (by rw [mem_subgroupOf]; exact hx) ⟨g, hg⟩
  rw [mem_subgroupOf] at this
  exact this

theorem exists_not_mem_Xbar : ∃ σ ∈ S.Mbar, σ ∉ C.Xbar := by
  by_contra! h
  have h1 : C.Xbar.relIndex S.Mbar = 1 := Subgroup.relIndex_eq_one.mpr h
  rw [C.relIndex_Xbar] at h1
  exact absurd h1 (by norm_num)

theorem apply_mem_Bt_of_not_mem {σ : S.O} (hσ : σ ∈ S.Mbar) (hσX : σ ∉ C.Xbar) {v : S.Qt}
    (hv : v ∈ C.At) : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ C.Bt := by
  rw [← C.map_At σ hσ hσX]
  exact Submodule.mem_map_of_mem hv

theorem apply_mem_At_of_not_mem {σ : S.O} (hσ : σ ∈ S.Mbar) (hσX : σ ∉ C.Xbar) {v : S.Qt}
    (hv : v ∈ C.Bt) : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ C.At := by
  rw [← C.map_At σ hσ hσX] at hv
  obtain ⟨a, ha, rfl⟩ := hv
  have := C.apply_At _ (C.mul_mem_Xbar_of_not_mem hσ hσ hσX hσX) a ha
  exact this

theorem eq_zero_of_forall_Xbar {v : S.Qt} (h : ∀ x ∈ C.Xbar, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    v = 0 := by
  have hinv : ∀ x ∈ C.Xbar, ∀ w ∈ Submodule.span (ZMod 2) {v},
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Submodule.span (ZMod 2) {v} := by
    intro x hx w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, h x hx]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  by_contra hv
  have hdim : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 := finrank_span_singleton hv
  have h4 := C.four_le_width
  rcases C.invariant _ hinv with h0 | h0 | h0 | h0
  · exact hv (Submodule.span_singleton_eq_bot.mp h0)
  · rw [h0, C.finrank_At] at hdim
    omega
  · rw [h0, C.finrank_Bt] at hdim
    omega
  · rw [h0, finrank_top, finrank_Qt] at hdim
    omega

@[expose] noncomputable def A : Subgroup G := S.clPre C.At

@[expose] noncomputable def B : Subgroup G := S.clPre C.Bt

@[expose] noncomputable def X : Subgroup G := (C.Xbar.comap S.ρ).map S.M.subtype

theorem mem_X_iff {g : G} : g ∈ C.X ↔ ∃ h : g ∈ S.M, S.ρ ⟨g, h⟩ ∈ C.Xbar := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem X_le_M : C.X ≤ S.M := fun _ hg => (C.mem_X_iff.mp hg).1

theorem ρ_mem_Xbar {g : G} (hg : g ∈ C.X) (h : g ∈ S.M) : S.ρ ⟨g, h⟩ ∈ C.Xbar := by
  obtain ⟨_, hg'⟩ := C.mem_X_iff.mp hg
  exact hg'

theorem ρ_mem_Mbar (g : S.M) : S.ρ g ∈ S.Mbar := ⟨g, rfl⟩

theorem QG_le_X : S.QG ≤ C.X := by
  intro g hg
  obtain ⟨h, -⟩ := S.mem_QG_iff.mp hg
  refine C.mem_X_iff.mpr ⟨h, ?_⟩
  rw [(S.ρ_eq_one_iff ⟨g, h⟩).mpr hg]
  exact C.Xbar.one_mem

theorem mem_X_iff_of_mem_M {g : G} (hg : g ∈ S.M) : g ∈ C.X ↔ S.ρ ⟨g, hg⟩ ∈ C.Xbar :=
  ⟨fun h => C.ρ_mem_Xbar h hg, fun h => C.mem_X_iff.mpr ⟨hg, h⟩⟩

theorem mul_mem_X_iff {g h : G} (hg : g ∈ S.M) (hh : h ∈ S.M) :
    g * h ∈ C.X ↔ (g ∈ C.X ↔ h ∈ C.X) := by
  rw [C.mem_X_iff_of_mem_M (S.M.mul_mem hg hh), C.mem_X_iff_of_mem_M hg,
    C.mem_X_iff_of_mem_M hh]
  have : S.ρ ⟨g * h, S.M.mul_mem hg hh⟩ = S.ρ ⟨g, hg⟩ * S.ρ ⟨h, hh⟩ := by
    rw [← map_mul]
    rfl
  rw [this]
  exact C.mul_mem_Xbar_iff (ρ_mem_Mbar _) (ρ_mem_Mbar _)

theorem mul_mem_X_of_not_mem {g h : G} (hg : g ∈ S.M) (hh : h ∈ S.M) (hgX : g ∉ C.X)
    (hhX : h ∉ C.X) : g * h ∈ C.X :=
  (C.mul_mem_X_iff hg hh).mpr (iff_of_false hgX hhX)

theorem conj_mem_X {g x : G} (hg : g ∈ S.M) (hx : x ∈ C.X) : g * x * g⁻¹ ∈ C.X := by
  have hxM := C.X_le_M hx
  have hgxM : g * x * g⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hg hxM) (S.M.inv_mem hg)
  rw [C.mem_X_iff_of_mem_M hgxM]
  have : S.ρ ⟨g * x * g⁻¹, hgxM⟩ = S.ρ ⟨g, hg⟩ * S.ρ ⟨x, hxM⟩ * (S.ρ ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact C.conj_mem_Xbar (ρ_mem_Mbar _) (C.ρ_mem_Xbar hx hxM)

theorem exists_not_mem_X : ∃ g ∈ S.M, g ∉ C.X := by
  obtain ⟨σ, ⟨g, rfl⟩, hσ⟩ := C.exists_not_mem_Xbar
  exact ⟨g, g.2, fun h => hσ (C.ρ_mem_Xbar h g.2)⟩

theorem X_eq : C.X = normalizer (C.A : Set G) ⊓ S.M := C.normalizer_inf_M.symm

theorem X_le_normalizer : C.X ≤ normalizer (C.A : Set G) := by
  rw [X_eq]
  exact inf_le_left

theorem A_le_QG : C.A ≤ S.QG := S.clPre_le_QG _

theorem B_le_QG : C.B ≤ S.QG := S.clPre_le_QG _

theorem z_mem_A : S.z ∈ C.A := S.z_mem_clPre _

theorem A_comm {a b : G} (ha : a ∈ C.A) (hb : b ∈ C.A) : a * b = b * a :=
  (S.polar_cl_eq_zero_iff ha.1 hb.1).mp (C.polar_eq_zero_of_mem_At ha.2 hb.2)

theorem B_comm {a b : G} (ha : a ∈ C.B) (hb : b ∈ C.B) : a * b = b * a :=
  (S.polar_cl_eq_zero_iff ha.1 hb.1).mp (C.polar_eq_zero_of_mem_Bt ha.2 hb.2)

theorem A_mul_self {a : G} (ha : a ∈ C.A) : a * a = 1 := by
  rw [← pow_two]
  exact (S.q_cl_eq_zero_iff ha.1).mp (C.q_At _ ha.2)

theorem B_mul_self {a : G} (ha : a ∈ C.B) : a * a = 1 := by
  rw [← pow_two]
  exact (S.q_cl_eq_zero_iff ha.1).mp (C.q_Bt _ ha.2)

theorem card_A : Nat.card C.A = 2 ^ (S.width + 1) := by
  rw [A, S.card_clPre, S.card_submodule, C.finrank_At, pow_succ, mul_comm]

theorem cl_conj {g x : G} (hg : g ∈ S.M) (hx : x ∈ S.QG) :
    S.cl (g * x * g⁻¹) = (S.ρ ⟨g, hg⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) :=
  (S.ρ_cl ⟨g, hg⟩ hx).symm

theorem conj_mem_A {g a : G} (hg : g ∈ C.X) (ha : a ∈ C.A) : g * a * g⁻¹ ∈ C.A := by
  have hgM := C.X_le_M hg
  refine ⟨S.conj_mem_QG hgM ha.1, ?_⟩
  rw [cl_conj hgM ha.1]
  exact C.apply_At _ (C.ρ_mem_Xbar hg hgM) _ ha.2

theorem conj_mem_B {g a : G} (hg : g ∈ C.X) (ha : a ∈ C.B) : g * a * g⁻¹ ∈ C.B := by
  have hgM := C.X_le_M hg
  refine ⟨S.conj_mem_QG hgM ha.1, ?_⟩
  rw [cl_conj hgM ha.1]
  exact C.apply_Bt _ (C.ρ_mem_Xbar hg hgM) _ ha.2

theorem conj_mem_B_of_not_mem_X {g a : G} (hg : g ∈ S.M) (hgX : g ∉ C.X) (ha : a ∈ C.A) :
    g * a * g⁻¹ ∈ C.B := by
  refine ⟨S.conj_mem_QG hg ha.1, ?_⟩
  rw [cl_conj hg ha.1]
  exact C.apply_mem_Bt_of_not_mem (ρ_mem_Mbar _)
    (fun h => hgX (C.mem_X_iff.mpr ⟨hg, h⟩)) ha.2

theorem conj_mem_A_of_not_mem_X {g a : G} (hg : g ∈ S.M) (hgX : g ∉ C.X) (ha : a ∈ C.B) :
    g * a * g⁻¹ ∈ C.A := by
  refine ⟨S.conj_mem_QG hg ha.1, ?_⟩
  rw [cl_conj hg ha.1]
  exact C.apply_mem_At_of_not_mem (ρ_mem_Mbar _)
    (fun h => hgX (C.mem_X_iff.mpr ⟨hg, h⟩)) ha.2

end Config

end CFSG.LargeExtraspecial.GLR
