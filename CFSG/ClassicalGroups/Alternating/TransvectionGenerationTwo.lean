module

public import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.ClassicalGroups.Alternating

open Module Submodule
open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

theorem eq_zero_or_eq_one_of_card_eq_two [Finite K] (hcard : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  rcases eq_or_ne x 0 with h | h
  · exact Or.inl h
  · right
    obtain ⟨y, hy0, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hcard
    rw [hy x h, hy 1 one_ne_zero]

theorem closure_symplecticTransvection_pair_eq_bilinIsometryGroup [Finite K] [CharP K 2]
    [FiniteDimensional K V] (hcard : Nat.card K = 2) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (hdim : finrank K V = 2) {e f : V} (hef : B e f = 1) :
    Subgroup.closure
        ({symplecticTransvection B hB e 1, symplecticTransvection B hB f 1} :
          Set (LinearMap.GeneralLinearGroup K V)) = bilinIsometryGroup B := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at hef
    exact zero_ne_one hef
  set H : Subgroup (LinearMap.GeneralLinearGroup K V) := Subgroup.closure
    ({symplecticTransvection B hB e 1, symplecticTransvection B hB f 1} :
      Set (LinearMap.GeneralLinearGroup K V))
  have hHle : H ≤ bilinIsometryGroup B := by
    rw [show H = _ from rfl, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact symplecticTransvection_mem_bilinIsometryGroup hB e 1
    · exact symplecticTransvection_mem_bilinIsometryGroup hB f 1
  have hTe : symplecticTransvection B hB e 1 ∈ H :=
    Subgroup.subset_closure (by simp)
  have hTf : symplecticTransvection B hB f 1 ∈ H :=
    Subgroup.subset_closure (by simp)
  have hL : pointRadical B hB e ≤ H := by
    rintro _ ⟨w, c, hew, rfl⟩
    obtain ⟨t, rfl⟩ := exists_eq_smul_of_apply_eq_zero hB hBn hdim he0 hew
    have hstep : siegel B hB e (t • e) c = siegel B hB e 0 c := by
      simpa using siegel_add_smul_self_of_two_eq_zero h2 hB (v := e) (w := 0) (map_zero (B e)) t c
    rw [hstep, siegel_zero_right]
    rcases eq_zero_or_eq_one_of_card_eq_two hcard c with rfl | rfl
    · rw [symplecticTransvection_zero]
      exact one_mem H
    · exact hTe
  have hsf : siegel B hB f 0 1 ∈ H := by
    rw [siegel_zero_right]
    exact hTf
  have hBfe : B f e ≠ 0 := by
    rw [← hB.neg_eq e f, hef]
    simp
  have hgen := pointRadical_sup_zpowers_siegel h2 hB hBn (u := f) (v := e) (w := 0) (c := 1)
    hBfe (map_zero _) one_ne_zero
  refine le_antisymm hHle ?_
  rw [← hgen]
  exact sup_le hL (Subgroup.zpowers_le.mpr hsf)


section Extension

variable {U W : Submodule K V}

noncomputable def isComplExtendEquiv (h : IsCompl U W) (φ : W ≃ₗ[K] W) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U W h).symm ≪≫ₗ ((LinearEquiv.refl K U).prodCongr φ) ≪≫ₗ
    Submodule.prodEquivOfIsCompl U W h

theorem isComplExtendEquiv_apply_left (h : IsCompl U W) (φ : W ≃ₗ[K] W) {x : V} (hx : x ∈ U) :
    isComplExtendEquiv h φ x = x := by
  rw [isComplExtendEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    show x = ((⟨x, hx⟩ : U) : V) from rfl, Submodule.prodEquivOfIsCompl_symm_apply_left,
    LinearEquiv.prodCongr_apply, map_zero, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]

theorem isComplExtendEquiv_apply_right (h : IsCompl U W) (φ : W ≃ₗ[K] W) (w : W) :
    isComplExtendEquiv h φ w = φ w := by
  rw [isComplExtendEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]

noncomputable def isComplExtendGL (h : IsCompl U W) :
    LinearMap.GeneralLinearGroup K W →* LinearMap.GeneralLinearGroup K V where
  toFun φ := LinearMap.GeneralLinearGroup.ofLinearEquiv (isComplExtendEquiv h φ.toLinearEquiv)
  map_one' := Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => isComplExtendEquiv_apply_left h _ hx)
    (fun x hx => isComplExtendEquiv_apply_right h _ ⟨x, hx⟩)
  map_mul' φ ψ := Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => by
      change isComplExtendEquiv h _ x = isComplExtendEquiv h _ (isComplExtendEquiv h _ x)
      rw [isComplExtendEquiv_apply_left h _ hx, isComplExtendEquiv_apply_left h _ hx,
        isComplExtendEquiv_apply_left h _ hx])
    (fun x hx => by
      change isComplExtendEquiv h _ ((⟨x, hx⟩ : W) : V) =
        isComplExtendEquiv h _ (isComplExtendEquiv h _ ((⟨x, hx⟩ : W) : V))
      rw [isComplExtendEquiv_apply_right, isComplExtendEquiv_apply_right,
        isComplExtendEquiv_apply_right]
      rfl)

theorem isComplExtendGL_apply_left (h : IsCompl U W) (φ : LinearMap.GeneralLinearGroup K W)
    {x : V} (hx : x ∈ U) : (isComplExtendGL h φ : V →ₗ[K] V) x = x :=
  isComplExtendEquiv_apply_left h _ hx

theorem isComplExtendGL_apply_right (h : IsCompl U W) (φ : LinearMap.GeneralLinearGroup K W)
    (w : W) : (isComplExtendGL h φ : V →ₗ[K] V) w = (φ : W →ₗ[K] W) w :=
  isComplExtendEquiv_apply_right h _ w

theorem isComplExtendGL_symplecticTransvection (hB : B.IsAlt) (h : IsCompl U W)
    (hUW : ∀ x ∈ U, ∀ y ∈ W, B x y = 0) (w : W) (c : K) :
    isComplExtendGL h (symplecticTransvection (B.restrict W) (isAlt_restrict hB W) w c) =
      symplecticTransvection B hB w c :=
  Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => by
      rw [isComplExtendGL_apply_left h _ hx, symplecticTransvection_apply, hUW x hx w w.2, mul_zero,
        zero_smul, add_zero])
    (fun x hx => by
      change (isComplExtendGL h _ : V →ₗ[K] V) ((⟨x, hx⟩ : W) : V) =
        (symplecticTransvection B hB w c : V →ₗ[K] V) x
      rw [isComplExtendGL_apply_right, symplecticTransvection_apply, symplecticTransvection_apply]
      rfl)

end Extension

section Transport

variable {U W : Submodule K V}

theorem isComplExtendGL_mem_of_closure [FiniteDimensional K V] (hB : B.IsAlt) (h : IsCompl U W)
    (hUW : ∀ x ∈ U, ∀ y ∈ W, B x y = 0)
    (H : Subgroup (LinearMap.GeneralLinearGroup K V)) {s : Finset W}
    (hgen : Subgroup.closure
      ((fun x => symplecticTransvection (B.restrict W) (isAlt_restrict hB W) x 1) '' (s : Set W)) =
      bilinIsometryGroup (B.restrict W))
    (hH : ∀ x ∈ s, symplecticTransvection B hB (x : V) 1 ∈ H) :
    ∀ g ∈ bilinIsometryGroup (B.restrict W), isComplExtendGL h g ∈ H := by
  intro g hg
  rw [← hgen] at hg
  have hmap := Subgroup.mem_map_of_mem (isComplExtendGL h) hg
  rw [MonoidHom.map_closure] at hmap
  have hle : Subgroup.closure ((isComplExtendGL h) ''
      ((fun x => symplecticTransvection (B.restrict W) (isAlt_restrict hB W) x 1) ''
        (s : Set W))) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [isComplExtendGL_symplecticTransvection hB h hUW x 1]
    exact hH x hx
  exact hle hmap

theorem symplecticTransvection_mem_of_isComplExtendGL [FiniteDimensional K V] (hB : B.IsAlt)
    (h : IsCompl U W) (hUW : ∀ x ∈ U, ∀ y ∈ W, B x y = 0)
    (H : Subgroup (LinearMap.GeneralLinearGroup K V)) {s : Finset W}
    (hgen : Subgroup.closure
      ((fun x => symplecticTransvection (B.restrict W) (isAlt_restrict hB W) x 1) '' (s : Set W)) =
      bilinIsometryGroup (B.restrict W))
    (hH : ∀ x ∈ s, symplecticTransvection B hB (x : V) 1 ∈ H) (w : W) :
    symplecticTransvection B hB (w : V) 1 ∈ H := by
  have hg := isComplExtendGL_mem_of_closure hB h hUW H hgen hH
    (symplecticTransvection (B.restrict W) (isAlt_restrict hB W) w 1)
    (symplecticTransvection_mem_bilinIsometryGroup (isAlt_restrict hB W) w 1)
  rwa [isComplExtendGL_symplecticTransvection hB h hUW w 1] at hg

theorem symplecticTransvection_add_mem_of_isComplExtendGL [FiniteDimensional K V] [Finite K]
    [CharP K 2] (hB : B.IsAlt) {e : V} (he : e ∈ U) {W : Submodule K V}
    (h : IsCompl U W) (hUW : ∀ x ∈ U, ∀ y ∈ W, B x y = 0)
    (H : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hext : ∀ g ∈ bilinIsometryGroup (B.restrict W), isComplExtendGL h g ∈ H)
    (hHle : H ≤ bilinIsometryGroup B) (hWnd : (B.restrict W).Nondegenerate)
    {w₀ : W} (hw₀ : w₀ ≠ 0)
    (h1 : symplecticTransvection B hB (e + (w₀ : V)) 1 ∈ H) :
    ∀ w : W, w ≠ 0 → symplecticTransvection B hB (e + (w : V)) 1 ∈ H := by
  intro w hw
  obtain ⟨g, hg, hgw⟩ :=
    (alternating_transvection_vector_transitivity (isAlt_restrict hB W) hWnd).2 w₀ w hw₀ hw
  have hgS := closure_symplecticTransvection_le_bilinIsometryGroup (isAlt_restrict hB W) hg
  have hgext := hext g hgS
  have hiso := mem_bilinIsometryGroup.mp (hHle hgext)
  have hconj := SteinbergBQ.symplecticTransvection_conj hB hiso (e + (w₀ : V)) 1
  have hmap : (isComplExtendGL h g : V →ₗ[K] V) (e + (w₀ : V)) = e + (w : V) := by
    rw [map_add, isComplExtendGL_apply_left h g he, isComplExtendGL_apply_right h g w₀, hgw]
  rw [hmap] at hconj
  rw [← hconj]
  exact mul_mem (mul_mem hgext h1) (inv_mem hgext)

theorem pointRadical_le_of_transvections [Finite K] [CharP K 2] (hcard : Nat.card K = 2)
    (hB : B.IsAlt) {e f : V} {W : Submodule K V} (hef : B e f = 1)
    (h : IsCompl (span K {e, f}) W)
    (hUW : ∀ x ∈ span K {e, f}, ∀ y ∈ W, B x y = 0)
    (H : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hTe : symplecticTransvection B hB e 1 ∈ H)
    (hTw : ∀ w : W, symplecticTransvection B hB (w : V) 1 ∈ H)
    (hTew : ∀ w : W, w ≠ 0 → symplecticTransvection B hB (e + (w : V)) 1 ∈ H) :
    pointRadical B hB e ≤ H := by
  intro g hg
  obtain ⟨u, c, heu, rfl⟩ := hg
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨p, hp, w, hw, hpu⟩ :=
    Submodule.mem_sup.mp (by rw [h.sup_eq_top]; trivial : u ∈ span K {e, f} ⊔ W)
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hp
  rw [← hpu] at heu ⊢
  have hes : e ∈ span K {e, f} := Submodule.subset_span (by simp)
  have hwe : B e w = 0 := hUW e hes w hw
  have hβ : β = 0 := by
    have h0 := heu
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, hef, mul_one, mul_zero, add_zero] at h0
    rw [hwe, add_zero, zero_add] at h0
    exact h0
  rw [hβ, zero_smul, add_zero] at heu ⊢
  have huw : B e w = 0 := hwe
  have hstep : siegel B hB e (α • e + (w : V)) c = siegel B hB e (w : V) c := by
    rw [add_comm (α • e) (w : V)]
    exact siegel_add_smul_self_of_two_eq_zero h2 hB huw α c
  rw [hstep]
  have hsig1 : siegel B hB e w 1 =
      symplecticTransvection B hB (e + w) 1 * symplecticTransvection B hB w 1 := by
    simpa using siegel_smul_eq_mul h2 hB huw (1 : K)
  rcases eq_zero_or_eq_one_of_card_eq_two hcard c with rfl | rfl
  · rcases eq_or_ne w 0 with rfl | hw0
    · rw [siegel_zero]
      exact one_mem H
    · have hm : siegel B hB e w 1 * symplecticTransvection B hB e 1 = siegel B hB e w 0 := by
        rw [← siegel_zero_right hB e 1]
        have hmul := siegel_mul hB huw (map_zero (B e)) (1 : K) 1
        rw [map_zero, add_zero, CharTwo.add_self_eq_zero, zero_add] at hmul
        exact hmul
      rw [← hm, hsig1]
      exact mul_mem (mul_mem (hTew ⟨w, hw⟩ (fun h => hw0 (congrArg Subtype.val h)))
        (hTw ⟨w, hw⟩)) hTe
  · rcases eq_or_ne w 0 with rfl | hw0
    · rw [siegel_zero_right]
      exact hTe
    · rw [hsig1]
      exact mul_mem (hTew ⟨w, hw⟩ (fun h => hw0 (congrArg Subtype.val h))) (hTw ⟨w, hw⟩)

end Transport

theorem exists_card_le_five_closure_eq_two [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hcard : Nat.card K = 2) (hB : B.IsAlt) (hBn : B.Nondegenerate) (hdim : finrank K V = 4) :
    ∃ s : Finset V, (∀ x ∈ s, x ≠ 0) ∧ s.card ≤ finrank K V + 1 ∧
      Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) =
        bilinIsometryGroup B := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by rw [hdim]; norm_num)
  obtain ⟨e₁, he₁⟩ := exists_ne (0 : V)
  obtain ⟨⟨f₁, he₁f₁⟩, hsplit₁⟩ := alternating_hyperbolic_splitting hB hBn he₁
  obtain ⟨-, -, -, hcompl₁, hW₁nd, hW₁dim⟩ := hsplit₁ f₁ he₁f₁
  set W₁ := B.orthogonal (span K {e₁, f₁}) with hW₁def
  have hW₁dim' : finrank K W₁ = 2 := by rw [hW₁dim, hdim]
  haveI : Nontrivial W₁ := Module.nontrivial_of_finrank_pos (R := K) (M := W₁) (by omega)
  obtain ⟨e₂, he₂⟩ := exists_ne (0 : W₁)
  obtain ⟨⟨f₂, he₂f₂⟩, -⟩ := alternating_hyperbolic_splitting (isAlt_restrict hB W₁) hW₁nd he₂
  have hf₁ : f₁ ≠ 0 := by
    intro h
    rw [h, map_zero] at he₁f₁
    exact zero_ne_one he₁f₁
  have hf₂ : f₂ ≠ 0 := by
    intro h
    rw [h, map_zero] at he₂f₂
    exact zero_ne_one he₂f₂
  set e' : V := e₁ + f₁ with he'def
  have hself : ∀ x : W₁, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have hw₀ : (e₂ + f₂ : W₁) ≠ 0 := by
    intro h
    have heq : (e₂ : W₁) = f₂ := by
      calc e₂ = e₂ + 0 := (add_zero e₂).symm
        _ = e₂ + (f₂ + f₂) := by rw [hself]
        _ = (e₂ + f₂) + f₂ := by rw [add_assoc]
        _ = 0 + f₂ := by rw [h]
        _ = f₂ := zero_add f₂
    have h0 : (B.restrict W₁) e₂ f₂ = 0 := by
      rw [heq, (isAlt_restrict hB W₁).self_eq_zero]
    rw [h0] at he₂f₂
    exact zero_ne_one he₂f₂
  have he'_mem : e' ∈ span K {e₁, f₁} := by
    rw [he'def]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have he'ne : e' ≠ 0 := by
    intro h
    have h0 : B e₁ e' = 1 := by
      rw [he'def, map_add, he₁f₁, hB.self_eq_zero, zero_add]
    rw [h, map_zero] at h0
    exact zero_ne_one h0
  have hU : ∀ x ∈ span K {e₁, f₁}, ∀ y ∈ W₁, B x y = 0 := fun x hx y hy => hy x hx
  have hBew : B (e₂ : V) (((e₂ + f₂ : W₁)) : V) = 1 := by
    rw [Submodule.coe_add, map_add, hB.self_eq_zero, zero_add]
    exact he₂f₂
  have he'w₀ : e' + (((e₂ + f₂ : W₁)) : V) ≠ 0 := by
    intro h
    have h0 : B (e₂ : V) (e' + (((e₂ + f₂ : W₁)) : V)) = 0 := by rw [h, map_zero]
    have hBe' : B (e₂ : V) e' = 0 := (hB.eq_iff).mpr (hU e' he'_mem e₂ e₂.2)
    rw [map_add, hBe', hBew, zero_add] at h0
    exact one_ne_zero h0
  let s : Finset V := {e₁, f₁, (e₂ : V), (f₂ : V), e' + (((e₂ + f₂ : W₁)) : V)}
  set H : Subgroup (LinearMap.GeneralLinearGroup K V) :=
    Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) with hHdef
  have hHle : H ≤ bilinIsometryGroup B := by
    rw [show H = _ from rfl, Subgroup.closure_le]
    rintro _ ⟨x, -, rfl⟩
    exact symplecticTransvection_mem_bilinIsometryGroup hB x 1
  have hmem : ∀ x ∈ s, symplecticTransvection B hB x 1 ∈ H :=
    fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩
  have hUW₁ : ∀ x ∈ span K {e₁, f₁}, ∀ y ∈ W₁, B x y = 0 := hU
  have hgenW : Subgroup.closure
      ((fun x => symplecticTransvection (B.restrict W₁) (isAlt_restrict hB W₁) x 1) ''
        (({e₂, f₂} : Finset W₁) : Set W₁)) = bilinIsometryGroup (B.restrict W₁) := by
    have hset : (({e₂, f₂} : Finset W₁) : Set W₁) = ({e₂, f₂} : Set W₁) := by ext x; simp
    rw [hset, Set.image_pair]
    exact closure_symplecticTransvection_pair_eq_bilinIsometryGroup hcard (isAlt_restrict hB W₁)
      hW₁nd hW₁dim' he₂f₂
  have hHgen : ∀ x ∈ ({e₂, f₂} : Finset W₁),
      symplecticTransvection B hB (x : V) 1 ∈ H := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem _ (by simp [s])
    · exact hmem _ (by simp [s])
  have hext : ∀ g ∈ bilinIsometryGroup (B.restrict W₁), isComplExtendGL hcompl₁ g ∈ H :=
    isComplExtendGL_mem_of_closure hB hcompl₁ hUW₁ H hgenW hHgen
  have hTw : ∀ w : W₁, symplecticTransvection B hB (w : V) 1 ∈ H := fun w =>
    symplecticTransvection_mem_of_isComplExtendGL hB hcompl₁ hUW₁ H hgenW hHgen w
  have hTe₁ : symplecticTransvection B hB e₁ 1 ∈ H := hmem _ (by simp [s])
  have hTf₁ : symplecticTransvection B hB f₁ 1 ∈ H := hmem _ (by simp [s])
  have hTe' : symplecticTransvection B hB e' 1 ∈ H := by
    have hc := SteinbergBQ.symplecticTransvection_conj hB
      (mem_bilinIsometryGroup.mp (symplecticTransvection_mem_bilinIsometryGroup hB f₁ 1)) e₁ 1
    rw [show (symplecticTransvection B hB f₁ 1 : V →ₗ[K] V) e₁ = e' from by
      rw [symplecticTransvection_apply, he₁f₁, one_mul, one_smul]] at hc
    rw [← hc]
    exact mul_mem (mul_mem hTf₁ hTe₁) (inv_mem hTf₁)
  have hTu : symplecticTransvection B hB (e' + (((e₂ + f₂ : W₁)) : V)) 1 ∈ H :=
    hmem _ (by simp [s])
  have hTew : ∀ w : W₁, w ≠ 0 → symplecticTransvection B hB (e' + (w : V)) 1 ∈ H :=
    symplecticTransvection_add_mem_of_isComplExtendGL hB he'_mem hcompl₁ hUW₁ H hext hHle
      hW₁nd hw₀ hTu
  have hspan' : span K {e', f₁} = span K {e₁, f₁} := by
    have hmem2 : f₁ ∈ span K {e₁, f₁} := Submodule.subset_span (by simp)
    have hmem3 : e₁ ∈ span K {e', f₁} := by
      have hx : e' + f₁ = e₁ := by
        rw [he'def, add_assoc, show f₁ + f₁ = 0 from by
          rw [← two_smul K f₁, h2, zero_smul], add_zero]
      rw [← hx]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    have hmem4 : f₁ ∈ span K {e', f₁} := Submodule.subset_span (by simp)
    apply le_antisymm
    · exact Submodule.span_le.mpr (by
        rw [Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨he'_mem, hmem2⟩)
    · exact Submodule.span_le.mpr (by
        rw [Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hmem3, hmem4⟩)
  have hcompl' : IsCompl (span K {e', f₁}) W₁ := by rw [hspan']; exact hcompl₁
  have hUW' : ∀ x ∈ span K {e', f₁}, ∀ y ∈ W₁, B x y = 0 := by
    intro x hx y hy
    rw [hspan'] at hx
    exact hUW₁ x hx y hy
  have he'f₁ : B e' f₁ = 1 := by
    rw [he'def, map_add, LinearMap.add_apply, he₁f₁, hB.self_eq_zero, add_zero]
  have hL : pointRadical B hB e' ≤ H :=
    pointRadical_le_of_transvections hcard hB he'f₁ hcompl' hUW' H hTe' hTw hTew
  have hsf : siegel B hB f₁ 0 1 ∈ H := by
    rw [siegel_zero_right]
    exact hTf₁
  have hBf₁e' : B f₁ e' ≠ 0 := by
    rw [← hB.neg_eq e' f₁, he'f₁]
    simp
  have hgen := pointRadical_sup_zpowers_siegel h2 hB hBn (u := f₁) (v := e') (w := 0) (c := 1)
    hBf₁e' (map_zero _) one_ne_zero
  refine ⟨s, ?_, ?_, le_antisymm hHle ?_⟩
  · intro x hx
    rw [show s = {e₁, f₁, (e₂ : V), (f₂ : V), e' + (((e₂ + f₂ : W₁)) : V)} from rfl] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact he₁
    · exact hf₁
    · exact fun h => he₂ (Subtype.ext h)
    · exact fun h => hf₂ (Subtype.ext h)
    · exact he'w₀
  · rw [hdim]
    rw [show s = {e₁, f₁, (e₂ : V), (f₂ : V), e' + (((e₂ + f₂ : W₁)) : V)} from rfl]
    exact Finset.card_le_five
  · rw [← hgen]
    exact sup_le hL (Subgroup.zpowers_le.mpr hsf)

theorem exists_card_le_three_closure_eq_two [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hcard : Nat.card K = 2) (hB : B.IsAlt) (hBn : B.Nondegenerate) (hdim : finrank K V = 2) :
    ∃ s : Finset V, (∀ x ∈ s, x ≠ 0) ∧ s.card ≤ finrank K V + 1 ∧
      Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) =
        bilinIsometryGroup B := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
  obtain ⟨e, he⟩ := exists_ne (0 : V)
  obtain ⟨⟨f, hef⟩, -⟩ := alternating_hyperbolic_splitting hB hBn he
  have hf : f ≠ 0 := by
    intro h
    rw [h, map_zero] at hef
    exact zero_ne_one hef
  refine ⟨{e, f}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact he
    · exact hf
  · rw [hdim]
    calc ({e, f} : Finset V).card ≤ 2 := Finset.card_le_two
      _ ≤ 2 + 1 := by norm_num
  · have hset : (({e, f} : Finset V) : Set V) = ({e, f} : Set V) := by ext x; simp
    rw [hset, Set.image_pair]
    exact closure_symplecticTransvection_pair_eq_bilinIsometryGroup hcard hB hBn hdim hef

universe u v

private theorem exists_card_le_closure_eq_aux_two {K : Type u} [Field K] [Finite K] [CharP K 2]
    (hcard : Nat.card K = 2) (m : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : BilinForm K V)
      (hB : B.IsAlt), B.Nondegenerate → finrank K V = m →
      ∃ s : Finset V, (∀ x ∈ s, x ≠ 0) ∧ s.card ≤ m + 1 ∧
        Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) =
          bilinIsometryGroup B := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V _ _ _ B hB hBn hm
    rcases subsingleton_or_nontrivial V with hV | hV
    · refine ⟨∅, by simp, by simp, ?_⟩
      have h1 : ∀ g : LinearMap.GeneralLinearGroup K V, g = 1 := fun g =>
        Units.ext (LinearMap.ext fun x => Subsingleton.elim _ _)
      rw [Finset.coe_empty, Set.image_empty, Subgroup.closure_empty]
      ext g
      rw [h1 g]
      simp only [Subgroup.mem_bot]
      exact ⟨fun _ => one_mem _, fun _ => trivial⟩
    · haveI : Nontrivial V := hV
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      obtain ⟨e, he⟩ := exists_ne (0 : V)
      obtain ⟨⟨f, hef⟩, hsplit⟩ := alternating_hyperbolic_splitting hB hBn he
      obtain ⟨hspan2, -, -, hcompl, hWnd, hWdim⟩ := hsplit f hef
      have hm2 : 2 ≤ m := by
        rw [← hm, ← hspan2]
        exact Submodule.finrank_le _
      by_cases hm2' : m = 2
      · rw [hm2'] at hm ⊢
        simpa [hm] using exists_card_le_three_closure_eq_two hcard hB hBn hm
      by_cases hm4' : m = 4
      · rw [hm4'] at hm ⊢
        simpa [hm] using exists_card_le_five_closure_eq_two hcard hB hBn hm
      ·
        have heven : Even m := by
          rw [← hm]
          exact LinearMap.BilinForm.IsAlt.even_finrank hB hBn
        obtain ⟨k, hk⟩ := heven
        have hm6 : 6 ≤ m := by omega
        set W := B.orthogonal (span K {e, f}) with hWdef
        have hWm : finrank K W = m - 2 := by rw [hWdim, hm]
        obtain ⟨sW, hsW0, hsWc, hsWgen⟩ :=
          ih (m - 2) (by omega) W (B.restrict W) (isAlt_restrict hB W) hWnd hWm
        have hHW : ∀ x ∈ span K {e, f}, ∀ y ∈ W, B x y = 0 := fun x hx y hy => hy x hx
        have hWge : 4 ≤ finrank K W := by rw [hWm]; omega
        haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (M := W) (by omega)
        obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
        obtain ⟨⟨g, hw₀g⟩, hsplitW⟩ :=
          alternating_hyperbolic_splitting (isAlt_restrict hB W) hWnd hw₀ne
        obtain ⟨-, -, -, hcomplW, hW₂nd, hW₂dim⟩ := hsplitW g hw₀g
        set W₂ := (B.restrict W).orthogonal (span K {w₀, g}) with hW₂def
        have hW₂dim' : finrank K W₂ = finrank K W - 2 := hW₂dim
        haveI : Nontrivial W₂ := Module.nontrivial_of_finrank_pos (R := K) (M := W₂) (by omega)
        obtain ⟨w₁, hw₁ne⟩ := exists_ne (0 : W₂)
        have hw₁0 : ((w₁ : W₂) : W) ≠ 0 := fun h => hw₁ne (Subtype.ext h)
        have hBw₀w₁ : B (w₀ : V) (((w₁ : W₂) : W) : V) = 0 :=
          (LinearMap.BilinForm.mem_orthogonal_iff).mp w₁.2 w₀ (Submodule.subset_span (by simp))
        let sW' : Finset V := sW.map ⟨Subtype.val, Subtype.val_injective⟩
        let s : Finset V := insert (e + (w₀ : V)) (insert f sW')
        set H : Subgroup (LinearMap.GeneralLinearGroup K V) :=
          Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) with hHdef
        have hHle : H ≤ bilinIsometryGroup B := by
          rw [show H = _ from rfl, Subgroup.closure_le]
          rintro _ ⟨x, -, rfl⟩
          exact symplecticTransvection_mem_bilinIsometryGroup hB x 1
        have hmem : ∀ x ∈ s, symplecticTransvection B hB x 1 ∈ H :=
          fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩
        have hmemS : ∀ x ∈ sW, ((x : W) : V) ∈ s := fun x hx =>
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨x, hx, rfl⟩))
        have hHgen : ∀ x ∈ sW, symplecticTransvection B hB ((x : W) : V) 1 ∈ H :=
          fun x hx => hmem _ (hmemS x hx)
        have hext : ∀ g ∈ bilinIsometryGroup (B.restrict W), isComplExtendGL hcompl g ∈ H :=
          isComplExtendGL_mem_of_closure hB hcompl hHW H hsWgen hHgen
        have hTw : ∀ w : W, symplecticTransvection B hB (w : V) 1 ∈ H := fun w =>
          symplecticTransvection_mem_of_isComplExtendGL hB hcompl hHW H hsWgen hHgen w
        have hespan : e ∈ span K {e, f} := Submodule.subset_span (by simp)
        have hTe₀ : symplecticTransvection B hB (e + (w₀ : V)) 1 ∈ H :=
          hmem _ (Finset.mem_insert_self _ _)
        have hTf : symplecticTransvection B hB f 1 ∈ H :=
          hmem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hTew : ∀ w : W, w ≠ 0 → symplecticTransvection B hB (e + (w : V)) 1 ∈ H :=
          symplecticTransvection_add_mem_of_isComplExtendGL hB hespan hcompl hHW H hext hHle
            hWnd hw₀ne hTe₀
        have hTew₁ : symplecticTransvection B hB (e + (((w₁ : W₂) : W) : V)) 1 ∈ H :=
          hTew ((w₁ : W₂) : W) hw₁0
        have hselfV : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
        have hBfe : B f e = 1 := by
          rw [← hB.neg_eq e f, hef, CharTwo.neg_eq]
        have hBew : ∀ w : W, B e (w : V) = 0 := fun w => hHW e hespan w w.2
        have hfspan : f ∈ span K {e, f} := Submodule.subset_span (by simp)
        have hBfw : ∀ w : W, B f (w : V) = 0 := fun w => hHW f hfspan w w.2
        have hw₁e : B (((w₁ : W₂) : W) : V) e = 0 :=
          (hB.eq_iff).mpr (hBew ((w₁ : W₂) : W))
        have hw₁f : B (((w₁ : W₂) : W) : V) f = 0 :=
          (hB.eq_iff).mpr (hBfw ((w₁ : W₂) : W))
        have hw₁w₀ : B (((w₁ : W₂) : W) : V) (w₀ : V) = 0 :=
          (hB.eq_iff).mpr hBw₀w₁
        have hw₀e : B (w₀ : V) e = 0 := (hB.eq_iff).mpr (hBew w₀)
        have hTefw₀ : symplecticTransvection B hB (e + f + (w₀ : V)) 1 ∈ H := by
          have hiso := mem_bilinIsometryGroup.mp (hHle hTe₀)
          have hc := SteinbergBQ.symplecticTransvection_conj hB hiso f 1
          have hval : (symplecticTransvection B hB (e + (w₀ : V)) 1 : V →ₗ[K] V) f =
              e + f + (w₀ : V) := by
            rw [symplecticTransvection_apply]
            have hBf : B f (e + (w₀ : V)) = 1 := by
              rw [map_add, hBfe, hBfw w₀]
              simp
            rw [hBf, one_mul, one_smul]
            calc f + (e + (w₀ : V)) = (f + e) + (w₀ : V) := by rw [add_assoc]
              _ = (e + f) + (w₀ : V) := by rw [add_comm f e]
          rw [hval] at hc
          rw [← hc]
          exact mul_mem (mul_mem hTe₀ hTf) (inv_mem hTe₀)
        have hTfw : symplecticTransvection B hB (f + (w₀ : V) + (((w₁ : W₂) : W) : V)) 1 ∈ H := by
          have hiso := mem_bilinIsometryGroup.mp (hHle hTefw₀)
          have hc := SteinbergBQ.symplecticTransvection_conj hB hiso
            (e + (((w₁ : W₂) : W) : V)) 1
          have hBval : B (e + (((w₁ : W₂) : W) : V)) (e + f + (w₀ : V)) = 1 := by
            simp only [map_add, LinearMap.add_apply, hB.self_eq_zero, hef, hBew w₀,
              hw₁e, hw₁f, hw₁w₀, zero_add, add_zero]
          have hval : (symplecticTransvection B hB (e + f + (w₀ : V)) 1 : V →ₗ[K] V)
              (e + (((w₁ : W₂) : W) : V)) = f + (w₀ : V) + (((w₁ : W₂) : W) : V) := by
            rw [symplecticTransvection_apply, hBval, one_mul, one_smul]
            calc (e + (((w₁ : W₂) : W) : V)) + (e + f + (w₀ : V))
                = (e + e) + ((((w₁ : W₂) : W) : V) + (f + (w₀ : V))) := by abel
              _ = 0 + ((((w₁ : W₂) : W) : V) + (f + (w₀ : V))) := by rw [hselfV e]
              _ = f + (w₀ : V) + (((w₁ : W₂) : W) : V) := by rw [zero_add]; abel
          rw [hval] at hc
          rw [← hc]
          exact mul_mem (mul_mem hTefw₀ hTew₁) (inv_mem hTefw₀)
        have hneg : ∀ x : W, -x = x := fun x => by
          rw [neg_eq_iff_add_eq_zero, ← two_smul K x, h2, zero_smul]
        have hw : (w₀ + ((w₁ : W₂) : W)) ≠ 0 := by
          intro hh
          have h1 : (w₀ : W) = ((w₁ : W₂) : W) := by
            have h' : (w₀ : W) = -(((w₁ : W₂) : W)) := eq_neg_of_add_eq_zero_left hh
            rwa [hneg] at h'
          have hw₀in : (w₀ : W) ∈ W₂ := h1 ▸ (w₁ : W₂).2
          have hmem : (w₀ : W) ∈ (⊥ : Submodule K W) := by
            have h2' : (w₀ : W) ∈ span K {w₀, g} ⊓ W₂ :=
              ⟨Submodule.subset_span (by simp), hw₀in⟩
            rwa [hcomplW.inf_eq_bot] at h2'
          have h0 : (w₀ : W) = 0 := by simpa using hmem
          exact hw₀ne h0
        have hTewsum : symplecticTransvection B hB
            (e + (w₀ : V) + (((w₁ : W₂) : W) : V)) 1 ∈ H := by
          have := hTew (w₀ + ((w₁ : W₂) : W)) hw
          simpa [Submodule.coe_add, add_assoc] using this
        have hBsum : B (f + (w₀ : V) + (((w₁ : W₂) : W) : V))
            (e + (w₀ : V) + (((w₁ : W₂) : W) : V)) = 1 := by
          simp only [map_add, LinearMap.add_apply, hB.self_eq_zero, hBfe, hBfw w₀,
            hBfw ((w₁ : W₂) : W), hw₀e, hBw₀w₁, hw₁e, hw₁w₀, zero_add, add_zero]
        have hTef : symplecticTransvection B hB (e + f) 1 ∈ H := by
          have hiso := mem_bilinIsometryGroup.mp (hHle hTewsum)
          have hc := SteinbergBQ.symplecticTransvection_conj hB hiso
            (f + (w₀ : V) + (((w₁ : W₂) : W) : V)) 1
          have hval : (symplecticTransvection B hB
              (e + (w₀ : V) + (((w₁ : W₂) : W) : V)) 1 : V →ₗ[K] V)
              (f + (w₀ : V) + (((w₁ : W₂) : W) : V)) = e + f := by
            rw [symplecticTransvection_apply, hBsum, one_mul, one_smul]
            calc (f + (w₀ : V) + (((w₁ : W₂) : W) : V))
                + (e + (w₀ : V) + (((w₁ : W₂) : W) : V))
                = (f + e) + ((w₀ : V) + (((w₁ : W₂) : W) : V))
                    + ((w₀ : V) + (((w₁ : W₂) : W) : V)) := by abel
              _ = (f + e) + 0 := by
                have hww : ((w₀ : V) + (((w₁ : W₂) : W) : V)) +
                    ((w₀ : V) + (((w₁ : W₂) : W) : V)) = 0 := hselfV _
                rw [add_assoc, hww]
              _ = e + f := by rw [add_comm f e, add_zero]
          rw [hval] at hc
          rw [← hc]
          exact mul_mem (mul_mem hTewsum hTfw) (inv_mem hTewsum)
        have hTe : symplecticTransvection B hB e 1 ∈ H := by
          have hiso := mem_bilinIsometryGroup.mp (hHle hTf)
          have hc := SteinbergBQ.symplecticTransvection_conj hB hiso (e + f) 1
          have hval : (symplecticTransvection B hB f 1 : V →ₗ[K] V) (e + f) = e := by
            rw [symplecticTransvection_apply]
            have hBf : B (e + f) f = 1 := by
              rw [map_add, LinearMap.add_apply, hef, hB.self_eq_zero]
              simp
            rw [hBf, one_mul, one_smul]
            calc (e + f) + f = e + (f + f) := by rw [add_assoc]
              _ = e + 0 := by rw [hselfV f]
              _ = e := add_zero e
          rw [hval] at hc
          rw [← hc]
          exact mul_mem (mul_mem hTf hTef) (inv_mem hTf)
        have hL : pointRadical B hB e ≤ H :=
          pointRadical_le_of_transvections hcard hB hef hcompl hHW H hTe hTw hTew
        have hsf : siegel B hB f 0 1 ∈ H := by
          rw [siegel_zero_right]
          exact hTf
        have hBfe' : B f e ≠ 0 := by
          rw [hBfe]
          exact one_ne_zero
        have hgen := pointRadical_sup_zpowers_siegel h2 hB hBn (u := f) (v := e) (w := 0) (c := 1)
          hBfe' (map_zero _) one_ne_zero
        have hew₀ : e + (w₀ : V) ≠ 0 := by
          intro hh
          have h0 : B (e + (w₀ : V)) f = 1 := by
            rw [map_add, LinearMap.add_apply, hef, (hB.eq_iff).mpr (hBfw w₀)]
            simp
          rw [hh, map_zero, LinearMap.zero_apply] at h0
          exact zero_ne_one h0
        have hf0 : f ≠ 0 := by
          intro hh
          rw [hh, map_zero] at hef
          exact zero_ne_one hef
        refine ⟨s, ?_, ?_, le_antisymm hHle ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hew₀
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hf0
          · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
            exact fun hh => hsW0 y hy (Subtype.ext hh)
        · calc s.card ≤ (insert f sW').card + 1 := Finset.card_insert_le _ _
            _ ≤ sW'.card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
            _ = sW.card + 2 := by rw [Finset.card_map]
            _ ≤ m + 1 := by omega
        · rw [← hgen]
          exact sup_le hL (Subgroup.zpowers_le.mpr hsf)

theorem exists_card_le_closure_symplecticTransvection_eq_two {K : Type u} {V : Type v}
    [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : BilinForm K V} (hcard : Nat.card K = 2) (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    ∃ s : Finset V, (∀ x ∈ s, x ≠ 0) ∧ s.card ≤ finrank K V + 1 ∧
      Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) =
        bilinIsometryGroup B :=
  exists_card_le_closure_eq_aux_two (K := K) hcard (finrank K V) V B hB hBn rfl

end CFSG.ClassicalGroups.Alternating
