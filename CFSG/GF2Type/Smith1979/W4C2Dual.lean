module

public import CFSG.LargeExtraspecial.GLRLinInv
public import CFSG.LargeExtraspecial.S12Main
public import CFSG.LargeExtraspecial.A2ModCfgSL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.GLR

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace Dual

theorem apply_mul (x y : S.O) (v : S.Qt) :
    ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

abbrev img (σ : S.O) (W : Submodule (ZMod 2) S.Qt) : Submodule (ZMod 2) S.Qt :=
  W.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)

theorem map_eq_of_forall_mem {W : Submodule (ZMod 2) S.Qt} {x : S.O}
    (hx : ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) : img x W = W := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rintro _ ⟨v, hv, rfl⟩
  exact hx v hv

theorem conj_mem_Xbar12 {g : G} {σ x : S.O} (hσ : σ ∈ S.Mbar) (hx : x ∈ S.Xbar12 g) :
    σ⁻¹ * x * σ ∈ S.Xbar12 g :=
  (mem_normalizer_iff''.mp (Setting.Mbar_le_normalizer_Xbar12 hσ) x).mp hx

theorem apply_mem_img {g : G} {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ x ∈ S.Xbar12 g, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) {σ : S.O}
    (hσ : σ ∈ S.Mbar) {x : S.O} (hx : x ∈ S.Xbar12 g) {v : S.Qt} (hv : v ∈ img σ W) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ img σ W := by
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  refine Submodule.mem_map.mpr ⟨((σ⁻¹ * x * σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w,
    hW _ (conj_mem_Xbar12 hσ hx) w hw, ?_⟩
  change ((σ * (σ⁻¹ * x * σ) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = _
  rw [show σ * (σ⁻¹ * x * σ) = x * σ by group, Subgroup.coe_mul, LinearEquiv.mul_apply]
  rfl

theorem mem_img_or_mem {g : G} {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ x ∈ S.Xbar12 g, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (hind : (S.Xbar12 g).relIndex S.Mbar = 2) {σ : S.O} (hσ : σ ∈ S.Mbar)
    (hσX : σ ∉ S.Xbar12 g) {m : S.O} (hm : m ∈ S.Mbar) :
    ((∀ v ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) ∧
        ∀ v ∈ img σ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ img σ W) ∨
      ((∀ v ∈ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ img σ W) ∧
        ∀ v ∈ img σ W, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) := by
  by_cases hmX : m ∈ S.Xbar12 g
  · exact Or.inl ⟨hW m hmX, fun v hv => apply_mem_img hW hσ hmX hv⟩
  right
  have hσ' : σ⁻¹ ∉ S.Xbar12 g := fun h => hσX (by simpa using (S.Xbar12 g).inv_mem h)
  have hmσ : m * σ ∈ S.Xbar12 g := s12_mul_mem_of_relIndex_two hind hm hσ hmX hσX
  have hmσ' : m * σ⁻¹ ∈ S.Xbar12 g :=
    s12_mul_mem_of_relIndex_two hind hm (S.Mbar.inv_mem hσ) hmX hσ'
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have e : ((m * σ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [← apply_mul, inv_mul_cancel_right]
    rw [← e]
    exact apply_mem_img hW hσ hmσ' (Submodule.mem_map_of_mem hv)
  · obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have e : ((m * σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
        (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := rfl
    change (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ W
    rw [← e]
    exact hW _ hmσ w hw

theorem sup_eq_top_inf_eq_bot {g : G} (hred : ¬ S.IsReducible12) {W : Submodule (ZMod 2) S.Qt}
    (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hW : ∀ x ∈ S.Xbar12 g, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (hind : (S.Xbar12 g).relIndex S.Mbar = 2) {σ : S.O} (hσ : σ ∈ S.Mbar)
    (hσX : σ ∉ S.Xbar12 g) : W ⊔ img σ W = ⊤ ∧ W ⊓ img σ W = ⊥ := by
  have key : ∀ U : Submodule (ZMod 2) S.Qt,
      (∀ m ∈ S.Mbar, ∀ v ∈ U, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_contra hc
    push Not at hc
    exact hred ⟨U, hc.1, hc.2, fun m v hv => hU _ ⟨m, rfl⟩ v hv⟩
  refine ⟨(key _ fun m hm v hv => ?_).resolve_left fun h => hW0 ?_,
    (key _ fun m hm v hv => ?_).resolve_right fun h => hWt ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    rcases mem_img_or_mem hW hind hσ hσX hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Submodule.add_mem _ (Submodule.mem_sup_left (h1 a ha))
        (Submodule.mem_sup_right (h2 b hb))
    · exact Submodule.add_mem _ (Submodule.mem_sup_right (h1 a ha))
        (Submodule.mem_sup_left (h2 b hb))
  · exact eq_bot_iff.mpr (le_sup_left.trans h.le)
  · rcases mem_img_or_mem hW hind hσ hσX hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 v hv.1, h2 v hv.2⟩
    · exact ⟨h2 v hv.2, h1 v hv.1⟩
  · exact eq_top_iff.mpr (h.ge.trans inf_le_left)

@[expose] noncomputable def resW (X : Subgroup S.O) (W : Submodule (ZMod 2) S.Qt)
    (hW : ∀ x ∈ X, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) : X →* (W ≃ₗ[ZMod 2] W) where
  toFun x := LinearEquiv.ofSubmodules ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) W W
    (map_eq_of_forall_mem (hW x x.2))
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

theorem eq_one_of_fix {g : G} {W : Submodule (ZMod 2) S.Qt} {σ : S.O} (hσ : σ ∈ S.Mbar)
    (hsup : W ⊔ img σ W = ⊤)
    (hfix : ∀ x ∈ S.Xbar12 g, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {x : S.O}
    (hx : x ∈ S.Xbar12 g) : x = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have hv : v ∈ W ⊔ img σ W := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, ha, _, ⟨w, hw, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
  have h2 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
    have h3 := hfix _ (conj_mem_Xbar12 hσ hx) w hw
    have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (((σ⁻¹ * x * σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
      rw [← apply_mul, ← apply_mul, show σ * (σ⁻¹ * x * σ) = x * σ by group]
    rw [e, h3]
  rw [map_add, hfix x hx a ha, LinearEquiv.coe_coe, h2]
  rfl

theorem faithful {g : G} [IsSimpleGroup (S.Xbar12 g)] {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ x ∈ S.Xbar12 g, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) {σ : S.O}
    (hσ : σ ∈ S.Mbar) (hsup : W ⊔ img σ W = ⊤) :
    ∀ x ∈ S.Xbar12 g, (∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → x = 1 := by
  have hker : ∀ x : S.Xbar12 g, x ∈ (resW (S.Xbar12 g) W hW).ker ↔
      ∀ v ∈ W, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h v hv
      exact congrArg (fun f : W ≃ₗ[ZMod 2] W => ((f ⟨v, hv⟩ : W) : S.Qt)) h
    · intro h
      exact LinearEquiv.ext fun v => Subtype.ext (h v v.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resW (S.Xbar12 g) W hW).ker with h | h
  · intro x hx hxv
    have h1 : (⟨x, hx⟩ : S.Xbar12 g) ∈ (resW (S.Xbar12 g) W hW).ker := (hker _).mpr hxv
    rw [h] at h1
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h1)
  · exfalso
    have hone : ∀ x ∈ S.Xbar12 g, x = 1 := fun x hx =>
      eq_one_of_fix hσ hsup (fun y hy => (hker ⟨y, hy⟩).mp (by rw [h]; exact Subgroup.mem_top _)) hx
    obtain ⟨a, b, hab⟩ := exists_pair_ne (S.Xbar12 g)
    exact hab (Subtype.ext ((hone a a.2).trans (hone b b.2).symm))

theorem resW_bijective {X : Subgroup S.O} {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ x ∈ X, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (hfaith : ∀ x ∈ X, (∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → x = 1)
    (hn : finrank (ZMod 2) W = S.width)
    (hcard : Nat.card X = Nat.card (GL (Fin S.width) (ZMod 2))) :
    Function.Bijective (resW X W hW) := by
  have hinj : Function.Injective (resW X W hW) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine Subtype.ext (hfaith x x.2 fun v hv => ?_)
    exact congrArg (fun f : W ≃ₗ[ZMod 2] W => ((f ⟨v, hv⟩ : W) : S.Qt)) hx
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W))
      (fun _ _ he => LinearEquiv.ext (congrFun he))
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_linearEquiv hn, hcard]

theorem polar_eq_q_of_induces {X : Subgroup S.O} {W : Submodule (ZMod 2) S.Qt}
    (hind : ∀ f : W ≃ₗ[ZMod 2] W, ∃ x ∈ X, ∀ a : W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = f a)
    {u w : S.Qt} (hu : u ∈ W) (hw : w ∈ W) (_hu0 : u ≠ 0) (hw0 : w ≠ 0) (hwu : w ≠ u) :
    polar S.q w u = S.q u := by
  have hnot : w ∉ Submodule.span (ZMod 2) ({u} : Set S.Qt) := by
    intro hm
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hm
    rcases zmod2_eq_zero_or_one t with rfl | rfl
    · rw [zero_smul] at ht
      exact hw0 ht.symm
    · rw [one_smul] at ht
      exact hwu ht.symm
  obtain ⟨f, hfw, hfu⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hfu0 : f u = 0 := hfu (Submodule.mem_span_singleton_self u)
  have hfw1 : f w = 1 := zmod2_eq_one_of_ne_zero hfw
  let T : W →ₗ[ZMod 2] W := LinearMap.id + LinearMap.smulRight (f ∘ₗ W.subtype) ⟨u, hu⟩
  have hT : ∀ a : W, ((T a : W) : S.Qt) = a + f a • u := fun _ => rfl
  have hinv : Function.Involutive T := by
    intro a
    apply Subtype.ext
    rw [hT, hT, map_add, map_smul, hfu0, smul_zero, add_zero, add_assoc, two_vec, add_zero]
  obtain ⟨x, hx, hxa⟩ := hind (LinearEquiv.ofInvolutive T hinv)
  have h1 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + f w • u := hxa ⟨w, hw⟩
  have h2 : S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = S.q w :=
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 w
  rw [h1, hfw1, one_smul, QuadraticMap.map_add (⇑S.q) w u] at h2
  have h3 : ∀ a b c : ZMod 2, a + b + c = a → c = b := by decide
  exact h3 _ _ _ h2

theorem exists_two_independent {W : Submodule (ZMod 2) S.Qt} (hW : finrank (ZMod 2) W = 4)
    {u : S.Qt} (hu0 : u ≠ 0) :
    ∃ w₁ ∈ W, ∃ w₂ ∈ W, w₁ ≠ 0 ∧ w₁ ≠ u ∧ w₂ ≠ 0 ∧ w₂ ≠ u ∧ w₁ + w₂ ≠ 0 ∧
      w₁ + w₂ ≠ u := by
  obtain ⟨w₁, hw₁, hw₁U⟩ : ∃ w₁ ∈ W, w₁ ∉ Submodule.span (ZMod 2) ({u} : Set S.Qt) := by
    by_contra hc
    push Not at hc
    have h1 := Submodule.finrank_mono (show W ≤ Submodule.span (ZMod 2) {u} from hc)
    have h2 := finrank_span_singleton (K := ZMod 2) hu0
    omega
  obtain ⟨w₂, hw₂, hw₂U⟩ : ∃ w₂ ∈ W, w₂ ∉ Submodule.span (ZMod 2) ({u, w₁} : Set S.Qt) := by
    by_contra hc
    push Not at hc
    have h1 := Submodule.finrank_mono (show W ≤ Submodule.span (ZMod 2) {u, w₁} from hc)
    have h2 := finrank_span_le_two (S := S) u w₁
    omega
  have hu_mem : u ∈ Submodule.span (ZMod 2) ({u, w₁} : Set S.Qt) :=
    Submodule.subset_span (by simp)
  have hw₁_mem : w₁ ∈ Submodule.span (ZMod 2) ({u, w₁} : Set S.Qt) :=
    Submodule.subset_span (by simp)
  refine ⟨w₁, hw₁, w₂, hw₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact hw₁U (Submodule.zero_mem _)
  · rintro rfl
    exact hw₁U (Submodule.mem_span_singleton_self _)
  · rintro rfl
    exact hw₂U (Submodule.zero_mem _)
  · rintro rfl
    exact hw₂U hu_mem
  · intro h
    have : w₂ = w₁ := add_left_cancel (h.trans (two_vec (S := S) w₁).symm)
    exact hw₂U (this ▸ hw₁_mem)
  · intro h
    have : w₂ = w₁ + u := by
      calc w₂ = (w₁ + w₁) + w₂ := by rw [two_vec, zero_add]
        _ = w₁ + (w₁ + w₂) := by rw [add_assoc]
        _ = w₁ + u := by rw [h]
    exact hw₂U (this ▸ Submodule.add_mem _ hw₁_mem hu_mem)

theorem q_eq_zero_of_induces {X : Subgroup S.O} {W : Submodule (ZMod 2) S.Qt}
    (hW : finrank (ZMod 2) W = 4)
    (hind : ∀ f : W ≃ₗ[ZMod 2] W, ∃ x ∈ X, ∀ a : W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = f a) :
    ∀ v ∈ W, S.q v = 0 := by
  intro u hu
  by_cases hu0 : u = 0
  · rw [hu0]
    exact QuadraticMap.map_zero _
  obtain ⟨w₁, hw₁, w₂, hw₂, h10, h1u, h20, h2u, h120, h12u⟩ := exists_two_independent hW hu0
  have e1 := polar_eq_q_of_induces hind hu hw₁ hu0 h10 h1u
  have e2 := polar_eq_q_of_induces hind hu hw₂ hu0 h20 h2u
  have e3 := polar_eq_q_of_induces hind hu (W.add_mem hw₁ hw₂) hu0 h120 h12u
  rw [QuadraticMap.polar_add_left, e1, e2] at e3
  have h3 : ∀ a : ZMod 2, a + a = a → a = 0 := by decide
  exact h3 _ e3

end Dual

open Dual

theorem exists_pair_of_residual_w4 (hSL : S12SL4ModuleInput) {g : G} {t : S.O}
    (hw : S.width = 4) (hR : S.S12GammaLResidual g t) :
    ∃ A B : Submodule (ZMod 2) S.Qt, Pair S (S.Xbar12 g) A B ∧
      ∀ σ ∈ S.Mbar, σ ∉ S.Xbar12 g →
        A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B := by
  obtain ⟨-, -, hred, hind, ⟨φ⟩, -⟩ := hR
  obtain ⟨σ, hσ, hσX⟩ : ∃ σ ∈ S.Mbar, σ ∉ S.Xbar12 g := by
    by_contra hc
    push Not at hc
    have h1 : (S.Xbar12 g).relIndex S.Mbar = 1 := Subgroup.relIndex_eq_one.mpr hc
    omega
  have hdim : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have φ4 : S.Xbar12 g ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := by
    rw [hw] at φ
    exact φ
  haveI : IsSimpleGroup (S.Xbar12 g) := by
    haveI := A2Mod.isSimpleGroup_sl_zmodTwo (k := S.width) (by omega)
    exact φ.isSimpleGroup
  set H := (S.Xbar12 g).map S.O.subtype
  have ψ : H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ((S.Xbar12 g).equivMapOfInjective S.O.subtype (subtype_injective _)).symm.trans φ4
  obtain ⟨W, hW0, hWt, hWH⟩ := hSL S.Qt hdim H ⟨ψ⟩
  have hW : ∀ x ∈ S.Xbar12 g, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W :=
    fun x hx v hv => hWH _ ⟨x, hx, rfl⟩ v hv
  obtain ⟨hsup, hinf⟩ := sup_eq_top_inf_eq_bot hred hW0 hWt hW hind hσ hσX
  have hBdim : finrank (ZMod 2) (img σ W) = finrank (ZMod 2) W :=
    LinearEquiv.finrank_map_eq _ _
  have hWdim : finrank (ZMod 2) W = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (img σ W)
    rw [hsup, hinf, finrank_top, finrank_bot, hBdim, hdim] at h
    omega
  have hcard : Nat.card (S.Xbar12 g) = Nat.card (GL (Fin S.width) (ZMod 2)) := by
    rw [Nat.card_congr φ.toEquiv, card_SL_eq_card_GL]
  have hbij := resW_bijective hW (faithful hW hσ hsup) (hWdim.trans hw.symm) hcard
  have hq : ∀ v ∈ W, S.q v = 0 := q_eq_zero_of_induces hWdim fun f => by
    obtain ⟨x, hx⟩ := hbij.2 f
    refine ⟨x, x.2, fun a => ?_⟩
    rw [← hx]
    rfl
  refine ⟨W, img σ W, ⟨hq, ?_, hinf, hsup, hWdim.trans hw.symm,
    hBdim.trans (hWdim.trans hw.symm), hW, fun x hx v hv => apply_mem_img hW hσ hx hv, hcard⟩,
    fun σ' hσ' hσ'X => ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [LinearEquiv.coe_coe, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup σ.2]
    exact hq u hu
  · have hx : σ' * σ⁻¹ ∈ S.Xbar12 g :=
      s12_mul_mem_of_relIndex_two hind hσ' (S.Mbar.inv_mem hσ) hσ'X
        (fun h => hσX (by simpa using (S.Xbar12 g).inv_mem h))
    have e : σ' = (σ' * σ⁻¹) * σ := by group
    rw [e, Subgroup.coe_mul, LinearEquiv.mul_eq_trans, LinearEquiv.coe_trans, Submodule.map_comp]
    exact map_eq_of_forall_mem fun v hv => apply_mem_img hW hσ hx hv

end CFSG.GF2Type.Smith1979.W4C2
