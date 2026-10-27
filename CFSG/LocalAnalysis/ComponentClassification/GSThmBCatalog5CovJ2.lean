module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovBase
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.Sporadic.SmallOddCore.J2Local

public section

namespace CFSG.ComponentClassification.GSThmB.CovJ2

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier

section Local

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.LocalAnalysis.ComponentInitial

theorem card_centralizer_of_component
    {x₀ : NativeSporadic.J2} (hx : orderOf x₀ = 2) {B : Subgroup NativeSporadic.J2}
    (hB : CFSG.Assembly.IsComponentOf B (centralizer ({x₀} : Set NativeSporadic.J2))) :
    Nat.card (centralizer ({x₀} : Set NativeSporadic.J2)) = 240 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : NativeSporadic.J2 →* Equiv.Perm (Fin 315) :=
    j2P.subtype.comp j2PermEquiv.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp j2PermEquiv.injective
  have hrange : ι.range = j2P := by
    rw [hιdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr j2PermEquiv.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hτP : ι x₀ ∈ j2P := hrange ▸ ⟨x₀, rfl⟩
  have hτ : orderOf (ι x₀) = 2 := by rw [orderOf_injective ι hι, hx]
  have hB' : CFSG.Assembly.IsComponentOf (B.map ι)
      (j2P ⊓ centralizer ({ι x₀} : Set (Equiv.Perm (Fin 315)))) := by
    have := (isComponentOf_map_iff hι).2 hB
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  have hcard : Nat.card (centralizer ({x₀} : Set NativeSporadic.J2)) =
      Nat.card ↥(j2P ⊓ centralizer ({ι x₀} : Set (Equiv.Perm (Fin 315)))) := by
    rw [← Subgroup.card_map_of_injective hι, map_centralizer_eq_inf hι, hrange,
      Set.image_singleton]
  rw [hcard]
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, hτeq⟩ := hcover (ι x₀) (j2P_le_j2R hτP) hτ
  set f := (MulAut.conj g⁻¹).toMonoidHom with hfdef
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hfτ : f (ι x₀) = tp 315 r.rep := by
    rw [hτeq, hfdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hBr : CFSG.Assembly.IsComponentOf ((B.map ι).map f)
      (j2P ⊓ centralizer ({tp 315 r.rep} : Set (Equiv.Perm (Fin 315)))) := by
    have h := (isComponentOf_map_iff hfinj).2 hB'
    rwa [map_conj_inf_centralizer j2P (j2P.inv_mem hg), Set.image_singleton, hfτ] at h
  have hcardr : Nat.card ↥(j2P ⊓ centralizer ({ι x₀} : Set (Equiv.Perm (Fin 315)))) =
      Nat.card ↥(j2P ⊓ centralizer ({tp 315 r.rep} : Set (Equiv.Perm (Fin 315)))) := by
    rw [← Subgroup.card_map_of_injective hfinj, map_conj_inf_centralizer j2P (j2P.inv_mem hg),
      Set.image_singleton, hfτ]
  rw [hcardr]
  have htrP : tp 315 r.rep ∈ j2P := by
    rw [← hfτ, hfdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hτP) (j2P.inv_mem (j2P.inv_mem hg))
  set B' := (B.map ι).map f
  have hBq := hBr.2.2
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exfalso
    exact ((hrows _ List.mem_cons_self).2.2.1.1 rfl) htrP
  · exact (hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)).2.2.2.2.1
  · exfalso
    obtain ⟨hQcard, hQC2, hC2Q, hC2cent⟩ := j2_Q_facts
    have hC2 : genOf 315 j2C2Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
      have h := (hrows _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))).2.2.2.1
      dsimp only [CFSG.Sporadic.SmallOddCore.j2C] at h
      rw [genOf, j2C2Gens]
      exact h
    dsimp only at hBr
    rw [← hC2] at hBr
    rcases isComponentOf_le_or_commute hBr hQC2 hC2Q with hle | hcomm
    · exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 5) (by rw [hQcard]; norm_num)) hle
    · have hle : B' ≤ genOf 315 j2C2Gens ⊓
          centralizer (genOf 315 j2QGens : Set (Equiv.Perm (Fin 315))) := by
        intro x hx
        refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
        rw [mem_centralizer_iff]
        intro y hy
        have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
        rw [mem_centralizer_iff] at this
        exact this y hy
      exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 1) (by rw [hC2cent]; norm_num)) hle

end Local

section Main

open CFSG.ComponentClassification.J2Cover

theorem card_fix_conj (σ τ : Equiv.Perm (Fin 315)) :
    Fintype.card {p // (σ * τ * σ⁻¹) p = p} = Fintype.card {p // τ p = p} :=
  Fintype.card_congr (Equiv.subtypeEquiv σ⁻¹ fun p => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq])

theorem fixedCount_of_eq_conj {q : P} {c r : Equiv.Perm (Fin 315)}
    (h : (q : Equiv.Perm (Fin 315)) = c * r * c⁻¹) :
    Lift.fixedCount q = Nat.card {p : Fin 315 // r p = p} := by
  rw [Lift.fixedCount_eq_fixCount, Models.fixCount, h, card_fix_conj, Nat.card_eq_fintype_card]

theorem exists_disp_pair
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.J2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) :
    ∃ u v : NativeSporadic.J2, orderOf u = 2 ∧ Lift.fixedCount (nativeEquivP u) = 15 ∧
      ∀ U V : L, π U = u → π V = v → U⁻¹ * V⁻¹ * U * V = t := by
  obtain ⟨x, y, hx, hy, hxy, hc, hd⟩ := j2_pair_displacement
  have hd' := hd L hLq t ht hZ π hπ hker
  set e := nativeEquivP
  set π₁ : L →* P := e.toMonoidHom.comp π with hπ₁def
  have hπ₁ : Function.Surjective π₁ := e.surjective.comp hπ
  have hker₁ : π₁.ker = zpowers t := by
    rw [← hker]
    ext v
    simp only [hπ₁def, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨hfc, h11, -⟩ := j2_double_cover_involution_lift_orders hLq ht hZ π₁ hπ₁ hker₁
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  have hsq : ∀ (w : NativeSporadic.J2) (W : L), π W = w → orderOf w = 2 →
      Lift.fixedCount (e w) = 11 → W * W = 1 := by
    intro w W hW hw h11'
    have hW1 : π₁ W = e w := by rw [hπ₁def, MonoidHom.comp_apply, hW]; rfl
    have := h11 W (by rw [hW1, MulEquiv.orderOf_eq, hw]) (by rw [hW1]; exact h11')
    rw [← sq, ← this, pow_orderOf_eq_one]
  have hfc' : ∀ w : NativeSporadic.J2, orderOf w = 2 →
      Lift.fixedCount (e w) = 11 ∨ Lift.fixedCount (e w) = 15 :=
    fun w hw => hfc (e w) (by rw [MulEquiv.orderOf_eq, hw])
  by_cases h1 : Lift.fixedCount (e x) = 15
  · exact ⟨x, y, hx, h1, hd'⟩
  by_cases h2 : Lift.fixedCount (e y) = 15
  · refine ⟨y, x, hy, h2, fun U V hU hV => ?_⟩
    have := hd' V U hV hU
    calc U⁻¹ * V⁻¹ * U * V = (V⁻¹ * U⁻¹ * V * U)⁻¹ := by group
      _ = t := by rw [this, htinv]
  have hx2 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hxy2 : orderOf (x * y) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (x * y) ^ 2 = x * (y * x) * y := by rw [sq]; group
        _ = (x * x) * (y * y) := by rw [← hc]; group
        _ = 1 := by rw [hx2, hy2, one_mul]
    · intro h
      apply hxy
      calc x = x * (y * y) := by rw [hy2, mul_one]
        _ = (x * y) * y := by group
        _ = y := by rw [h, one_mul]
  by_cases h3 : Lift.fixedCount (e (x * y)) = 15
  · refine ⟨x * y, x, hxy2, h3, fun U V hU hV => ?_⟩
    have hY' : π (V⁻¹ * U) = y := by
      rw [map_mul, map_inv, hU, hV, ← mul_assoc, inv_mul_cancel, one_mul]
    have := hd' V (V⁻¹ * U) hV hY'
    calc U⁻¹ * V⁻¹ * U * V = (V⁻¹ * (V⁻¹ * U)⁻¹ * V * (V⁻¹ * U))⁻¹ := by group
      _ = t := by rw [this, htinv]
  exfalso
  obtain ⟨X, hX⟩ := hπ x
  obtain ⟨Y, hY⟩ := hπ y
  have hX2 := hsq x X hX hx ((hfc' x hx).resolve_right h1)
  have hY2 := hsq y Y hY hy ((hfc' y hy).resolve_right h2)
  have hXY2 := hsq (x * y) (X * Y) (by rw [map_mul, hX, hY]) hxy2
    ((hfc' _ hxy2).resolve_right h3)
  have hXi : X⁻¹ = X := inv_eq_of_mul_eq_one_right hX2
  have hYi : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hY2
  have h1' : t = 1 := by
    rw [← hd' X Y hX hY, hXi, hYi, ← hXY2]
    group
  rw [h1', orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem ordA_one_ne_604800 (m : ℕ) : Open.ordA 1 m ≠ 604800 :=
  Cov.ordA_one_ne_of_lt (B := 108) (by norm_num) (by decide) m

theorem card_centralizerIn_eq
    (x : NativeSporadic.J2) :
    Nat.card (centralizerIn P ((nativeEquivP x : P) : Equiv.Perm (Fin 315))) =
      Nat.card (centralizer ({x} : Set NativeSporadic.J2)) := by
  set f : NativeSporadic.J2 →* Equiv.Perm (Fin 315) :=
    P.subtype.comp nativeEquivP.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp nativeEquivP.injective
  have hrange : f.range = P := by
    rw [hfdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr nativeEquivP.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [← Subgroup.card_map_of_injective hf, CFSG.Sporadic.SmallOddCore.map_centralizer_eq_inf hf,
    hrange, Set.image_singleton]
  rfl

theorem exists_conj_of_card
    {x y : NativeSporadic.J2} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hcx : Nat.card (centralizer ({x} : Set NativeSporadic.J2)) = 240)
    (hfy : Lift.fixedCount (nativeEquivP y) = 15) : ∃ g, g * y * g⁻¹ = x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfA, hfT, -, -, -, hcA, -, hcT, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  set e := nativeEquivP
  have hmem : ∀ z : NativeSporadic.J2, ((e z : P) : Equiv.Perm (Fin 315)) ∈ P := fun z => (e z).2
  have hord : ∀ z : NativeSporadic.J2, orderOf z = 2 →
      orderOf ((e z : P) : Equiv.Perm (Fin 315)) = 2 := fun z hz => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz]
  obtain ⟨r₁, hr₁, c₁, hc₁, h₁⟩ := inner_classes.1 _ (hmem x) (hord x hx)
  obtain ⟨r₂, hr₂, c₂, hc₂, h₂⟩ := inner_classes.1 _ (hmem y) (hord y hy)
  have hr₁A : r₁ = permA := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr₁
    rcases hr₁ with rfl | rfl
    · rfl
    · exfalso
      have h := card_centralizerIn_eq x
      rw [hcx, h₁, centralizerIn_conj P hc₁,
        Subgroup.card_map_of_injective (MulAut.conj c₁).injective, hcT] at h
      exact absurd h (by norm_num)
  have hr₂A : r₂ = permA := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr₂
    rcases hr₂ with rfl | rfl
    · rfl
    · exfalso
      rw [fixedCount_of_eq_conj h₂, hfT] at hfy
      exact absurd hfy (by norm_num)
  subst hr₁A hr₂A
  set g' : P := ⟨c₁ * c₂⁻¹, P.mul_mem hc₁ (P.inv_mem hc₂)⟩
  refine ⟨e.symm g', e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, g', h₁, h₂]
  group

theorem twist_outer
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.J2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (α : MulAut L)
    (hα : α * α = 1) (hout : ∀ n : L, ¬ ∀ y, α y = n * y * n⁻¹) : ∃ h : L, α h = h * t := by
  obtain ⟨π₁, hπ₁def⟩ : ∃ f : L →* P, f = nativeEquivP.toMonoidHom.comp π := ⟨_, rfl⟩
  have hπ₁ : Function.Surjective π₁ := by
    rw [hπ₁def, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact nativeEquivP.surjective.comp hπ
  have hker₁ : π₁.ker = zpowers t := by
    rw [← hker]
    ext v
    simp only [hπ₁def, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have htc : t ∈ center L := hZ ▸ mem_zpowers t
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hα1 : α ≠ 1 := fun h1 => hout 1 fun y => by rw [h1]; simp
  set L' := Cov.Lsub α
  set eL := Cov.eL α
  have hLq' : CFSG.Assembly.IsQuasisimple L' := by
    rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hLq ⊢
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eL).1 hLq
  set t' : L' := eL t
  have ht' : orderOf t' = 2 := by rw [MulEquiv.orderOf_eq, ht]
  have hZ' : center L' = zpowers t' := by
    rw [← Subgroup.map_center_eq eL, hZ, MonoidHom.map_zpowers]
    rfl
  set π' : L' →* P := π₁.comp eL.symm.toMonoidHom with hπ'def
  have hπ' : Function.Surjective π' := hπ₁.comp eL.symm.surjective
  have hker' : π'.ker = zpowers t' := by
    ext v
    rw [MonoidHom.mem_ker, hπ'def, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker₁,
      mem_zpowers_iff, mem_zpowers_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, eL.symm.injective ?_⟩
      rw [map_zpow, MulEquiv.symm_apply_apply]
      exact hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hk, map_zpow, MulEquiv.symm_apply_apply]
  have hCL : centralizer ((L' : Subgroup (Cov.Semi α)) : Set (Cov.Semi α)) =
      zpowers (t' : Cov.Semi α) := by
    rw [Cov.centralizer_Lsub α hα hout, hZ, MonoidHom.map_zpowers]
    rfl
  obtain ⟨hconj, -⟩ :=
    ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section hLq' ht' hZ' π' hπ'
      hker' hCL
  set p := Cov.pElt α
  have hp : orderOf p = 2 := Cov.orderOf_pElt α hα hα1
  have hpL : p ∉ L' := Cov.pElt_not_mem α hα1
  have hαt : α t = t := by
    have hc : α t ∈ center L := by
      rw [mem_center_iff]
      intro g
      calc g * α t = α (α.symm g * t) := by rw [map_mul, MulEquiv.apply_symm_apply]
        _ = α (t * α.symm g) := by rw [mem_center_iff.mp htc]
        _ = α t * g := by rw [map_mul, MulEquiv.apply_symm_apply]
    rw [hZ] at hc
    rcases Cov.eq_one_or_eq_of_mem_zpowers ht2 hc with h | h
    · exfalso
      have h1 : t = 1 := α.injective (by rw [h, map_one])
      rw [h1, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · exact h
  set y : Cov.Semi α := SemidirectProduct.inl t * p with hydef
  have htL : (SemidirectProduct.inl t : Cov.Semi α) ∈ L' := ⟨t, rfl⟩
  have hyL : y ∉ L' := fun hy => hpL (by
    have := L'.mul_mem (L'.inv_mem htL) hy
    rwa [hydef, ← mul_assoc, inv_mul_cancel, one_mul] at this)
  have hy2 : y * y = 1 := by
    calc y * y = SemidirectProduct.inl t * (p * SemidirectProduct.inl t * p⁻¹) * (p * p) := by
          rw [hydef]; group
      _ = 1 := by
        rw [Cov.pElt_conj, Cov.pElt_mul_self α hα, hαt, mul_one, ← map_mul, ht2, map_one]
  have hyo : orderOf y = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hy2) fun h => hyL (h ▸ one_mem _)
  obtain ⟨l, hl⟩ := hconj p y hpL hp hyL hyo
  obtain ⟨l₀, hl₀⟩ := l.2
  refine ⟨l₀, ?_⟩
  rw [← hl₀] at hl
  have h1 : SemidirectProduct.inl l₀ * p * (SemidirectProduct.inl l₀)⁻¹ =
      SemidirectProduct.inl (l₀ * (α l₀)⁻¹) * p := by
    calc SemidirectProduct.inl l₀ * p * (SemidirectProduct.inl l₀)⁻¹ =
        SemidirectProduct.inl l₀ * (p * SemidirectProduct.inl l₀⁻¹ * p⁻¹) * p := by
          rw [map_inv]; group
      _ = SemidirectProduct.inl (l₀ * (α l₀)⁻¹) * p := by
          rw [Cov.pElt_conj, map_inv, ← map_mul]
  rw [h1, hydef] at hl
  have h2 : l₀ * (α l₀)⁻¹ = t := SemidirectProduct.inl_injective (mul_right_cancel hl)
  calc α l₀ = t⁻¹ * l₀ := by rw [← h2]; group
    _ = l₀ * t := by rw [htinv, mem_center_iff.mp htc]

theorem false_of_top
    {M : Subgroup NativeSporadic.J2} (hM : CFSG.Assembly.IsComponentOf M ⊤)
    (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) : False := by
  have : IsSimpleGroup NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hnc : ∃ a b : NativeSporadic.J2, a * b ≠ b * a := by
    refine ⟨nativeEquivP.symm pa, nativeEquivP.symm pb, fun h => pa_pb_ne ?_⟩
    have := congrArg nativeEquivP h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact this
  have hcard : Nat.card NativeSporadic.J2 = 604800 := CFSG.Sporadic.J2.card_J2
  refine Cov.false_of_component_top hnc hM hMt (fun q => ?_) ?_
  · rw [hcard]
    exact ordA_one_ne_604800 q
  · rw [hcard]
    norm_num

theorem twist_inner
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.J2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (X : L)
    (hX2 : X * X ∈ center L) {M : Subgroup NativeSporadic.J2}
    (hM : CFSG.Assembly.IsComponentOf M (centralizer ({π X} : Set NativeSporadic.J2)))
    (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) : ∃ h : L, X * h * X⁻¹ = h * t := by
  have htc : t ∈ center L := hZ ▸ mem_zpowers t
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set x₀ := π X with hx₀def
  have hx2 : x₀ * x₀ = 1 := by
    have h1 : π (X * X) = 1 := by
      rw [← MonoidHom.mem_ker, hker, ← hZ]
      exact hX2
    rwa [map_mul] at h1
  by_cases hx1 : x₀ = 1
  · exfalso
    have hc : centralizer ({x₀} : Set NativeSporadic.J2) = ⊤ := by
      rw [hx1]
      exact eq_top_iff.mpr fun z _ => mem_centralizer_singleton_iff.mpr (by group)
    rw [hc] at hM
    exact false_of_top hM hMt
  have hxo : orderOf x₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have h240 := card_centralizer_of_component hxo hM
  obtain ⟨u, v, hu, hu15, hd⟩ := exists_disp_pair hLq ht hZ π hπ hker
  obtain ⟨g, hg⟩ := exists_conj_of_card hxo hu h240 hu15
  obtain ⟨G, hG⟩ := hπ g
  obtain ⟨V, hV⟩ := hπ v
  set U := G⁻¹ * X * G with hUdef
  have hU : π U = u := by
    rw [hUdef, map_mul, map_mul, map_inv, hG, ← hx₀def, ← hg]
    group
  have hd' := hd U V hU hV
  have hU2 : U * U ∈ center L := by
    have h1 : U * U = G⁻¹ * (X * X) * G := by rw [hUdef]; group
    rw [h1, mem_center_iff.mp hX2 G⁻¹, inv_mul_cancel_right]
    exact hX2
  have h1 : U⁻¹ * V * U = V * t := by
    calc U⁻¹ * V * U = V * (U⁻¹ * V⁻¹ * U * V)⁻¹ := by group
      _ = V * t := by rw [hd', htinv]
  have hconj : U * V * U⁻¹ = V * t := by
    calc U * V * U⁻¹ = (U * U) * (U⁻¹ * V * U) * (U * U)⁻¹ := by group
      _ = (U * U) * (V * t) * (U * U)⁻¹ := by rw [h1]
      _ = V * t := by rw [(mem_center_iff.mp hU2 (V * t)).symm]; group
  refine ⟨G * V * G⁻¹, ?_⟩
  have hXU : X = G * U * G⁻¹ := by rw [hUdef]; group
  calc X * (G * V * G⁻¹) * X⁻¹ = G * (U * V * U⁻¹) * G⁻¹ := by rw [hXU]; group
    _ = G * V * (t * G⁻¹) := by rw [hconj]; group
    _ = G * V * G⁻¹ * t := by rw [← mem_center_iff.mp htc G⁻¹]; group

theorem twist
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.J2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (α : MulAut L) (hα : α * α = 1)
    (β : MulAut NativeSporadic.J2) (hβ : ∀ x, π (α x) = β (π x))
    {M : Subgroup NativeSporadic.J2} (hM : CFSG.Assembly.IsComponentOf M (fixSub β))
    (hMt : Cov.SmallQ (↥M ⧸ center ↥M)) : ∃ h : L, α h = h * t := by
  by_cases hinn : ∃ X : L, ∀ y, α y = X * y * X⁻¹
  · obtain ⟨X, hX⟩ := hinn
    rw [Cov.fixSub_eq_of_inner π hπ α β hβ X hX] at hM
    obtain ⟨h, hh⟩ := twist_inner hLq ht hZ π hπ hker X
      (Cov.mul_self_mem_center_of_inner α hα X hX) hM hMt
    exact ⟨h, by rw [hX]; exact hh⟩
  · push Not at hinn
    exact twist_outer hLq ht hZ π hπ hker α hα fun n hn => (hinn n).elim fun y hy => hy (hn y)

end Main

end CFSG.ComponentClassification.GSThmB.CovJ2
