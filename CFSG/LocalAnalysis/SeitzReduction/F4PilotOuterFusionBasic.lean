module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionClass
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionB

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

section Def

variable {C : Type*} [Group C]

@[expose] def TwoCentralTwistedFusion (η : MulAut C) : Prop :=
  ⁅η.toMonoidHom.eqLocus (MonoidHom.id C), η.toMonoidHom.eqLocus (MonoidHom.id C)⁆ =
      η.toMonoidHom.eqLocus (MonoidHom.id C) ∧
    ∃ (m₀ : C) (y₀ : η.toMonoidHom.eqLocus (MonoidHom.id C)), (y₀ : C) ≠ 1 ∧
      (η m₀)⁻¹ * m₀ = y₀ ∧
      ∀ β : MulAut (η.toMonoidHom.eqLocus (MonoidHom.id C)), ∃ S : Sylow 2 C,
        ∀ u ∈ (S : Subgroup C), u * (β y₀ : C) = (β y₀ : C) * u

end Def

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem conj_inv_mem_centralizer_singleton {t g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) :
    g * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
  have hst : g⁻¹ * t * g * t = t * (g⁻¹ * t * g) := mem_centralizer_singleton_iff.1 hsC
  rw [mem_centralizer_singleton_iff]
  calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * t * g * t) * g⁻¹ := by rw [hst]
    _ = t * (g * t * g⁻¹) := by group

theorem exists_mulEquiv_conj_eq (hset : StandardSetting G L) {C : Type*} [Group C]
    (e : L ≃* C) {η : MulAut C}
    (hcan : ∀ α : MulAut C, α ^ 2 = 1 → α ∉ (MulAut.conj : C →* MulAut C).range →
      ∃ ψ : MulAut C, ψ * α * ψ⁻¹ = η)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {x : G} (hxC : x ∈ centralizer ({t} : Set G)) (hx2 : x * x = 1)
    (hxL : x ∉ L ⊔ zpowers t) :
    ∃ ε : L ≃* C, ∀ l l' : L, (l' : G) = x * l * x⁻¹ → ε l' = η (ε l) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hN : x ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht hxC
  set α : MulAut L := L.normalizerMonoidHom ⟨x, hN⟩ with hαdef
  have hα : ∀ l : L, ((α l : L) : G) = x * l * x⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hN⟩ l
  have hα2 : α ^ 2 = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [sq, MulAut.mul_apply, MulAut.one_apply, hα, hα]
    calc x * (x * (l : G) * x⁻¹) * x⁻¹ = (x * x) * l * (x * x)⁻¹ := by group
      _ = l := by rw [hx2, one_mul, inv_one, mul_one]
  have hαo : α ∉ (MulAut.conj : L →* MulAut L).range := by
    rintro ⟨l, hl⟩
    refine hxL (mem_sup_zpowers_of_conj_eq htC ht hKt hxC l.2 fun y hy => ?_)
    have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [h, hα]
  obtain ⟨ψ, hψ⟩ := hcan ((e.symm.trans α).trans e) ((pow_two_conj_eq_one_iff e α).2 hα2)
    fun h => hαo ((conj_mem_range_conj_iff e α).1 h)
  have hψ' : ∀ c, ψ (((e.symm.trans α).trans e) c) = η (ψ c) := fun c => by
    rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  refine ⟨e.trans ψ, fun l l' hl' => ?_⟩
  have hl : l' = α l := Subtype.ext (hl'.trans (hα l).symm)
  rw [hl, MulEquiv.trans_apply, MulEquiv.trans_apply, ← hψ' (e l), conj_mulEquiv_apply,
    MulEquiv.symm_apply_apply]

theorem conj_inv_not_mem_sup_zpowers (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hZ : center L = ⊥)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hsL : g⁻¹ * t * g ∉ L ⊔ zpowers t) :
    g * t * g⁻¹ ∉ L ⊔ zpowers t := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht't : g * t * g⁻¹ * t = t * (g * t * g⁻¹) :=
    mem_centralizer_singleton_iff.1 (conj_inv_mem_centralizer_singleton hsC)
  intro hmem
  obtain ⟨w, hwL, hw⟩ := exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hmem
  rcases hw with hw | hw
  · exact conj_not_mem_of_forall_perfect hset hOut hZ hperf htC ht g⁻¹
      (by rw [inv_inv, hw]; exact hwL)
  · have hw' : w = t * (g * t * g⁻¹) := by rw [hw, ← mul_assoc, htt, one_mul]
    have hw1 : w ≠ 1 := by
      intro h1
      apply hsL
      have h2 : g * t * g⁻¹ = t := by rw [hw, h1, mul_one]
      have hs : g⁻¹ * t * g = t := by
        calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h2]
          _ = t := by group
      rw [hs]
      exact mem_sup_right (mem_zpowers t)
    have hw2 : w ^ 2 = 1 := by
      rw [sq, hw']
      calc t * (g * t * g⁻¹) * (t * (g * t * g⁻¹)) =
            t * ((g * t * g⁻¹) * t) * (g * t * g⁻¹) := by group
        _ = t * (t * (g * t * g⁻¹)) * (g * t * g⁻¹) := by rw [ht't]
        _ = (t * t) * (g * (t * t) * g⁻¹) := by group
        _ = 1 := by rw [htt]; group
    have hwo : orderOf w = 2 := orderOf_eq_prime hw2 hw1
    obtain ⟨P, hP, hwP, hPL, hPw⟩ := hperf w hwL hwo
    have hPt : P ≤ centralizer ({t} : Set G) := hPL.trans (le_centralizer_of_mem_centralizer htC)
    have hPt' : P ≤ centralizer ({g⁻¹⁻¹ * t * g⁻¹} : Set G) := by
      intro p hp
      rw [inv_inv, hw]
      exact mem_centralizer_singleton_mul (hPt hp) (hPw hp)
    obtain ⟨l, hl, hlw⟩ := (std_perfect_le_inf_conjugate hset hOut htC ht g⁻¹ hP hPt hPt' hwP).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hlw
    have hl' : l = g⁻¹ * t * g * t := by
      calc l = g⁻¹ * (g * l * g⁻¹) * g := by group
        _ = g⁻¹ * (t * (g * t * g⁻¹)) * g := by rw [hlw, hw']
        _ = g⁻¹ * t * g * t := by group
    apply hsL
    have he : g⁻¹ * t * g = l * t := by rw [hl', mul_assoc (g⁻¹ * t * g) t t, htt, mul_one]
    rw [he]
    exact mul_mem (mem_sup_left hl) (mem_sup_right (mem_zpowers t))

theorem outerFusionTwoCentral_of_twoCentralTwistedFusion (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hZ : center L = ⊥)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    {C : Type*} [Group C] (e : L ≃* C) {η : MulAut C}
    (hcan : ∀ α : MulAut C, α ^ 2 = 1 → α ∉ (MulAut.conj : C →* MulAut C).range →
      ∃ ψ : MulAut C, ψ * α * ψ⁻¹ = η)
    (hη : TwoCentralTwistedFusion η) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    OuterFusionTwoCentral L t := by
  intro g hsC hsL
  set F := η.toMonoidHom.eqLocus (MonoidHom.id C) with hFdef
  obtain ⟨hFperf, m₀, y₀, hy₀1, hmy₀, hβ⟩ := hη
  have hmemF : ∀ c : C, c ∈ F ↔ η c = c := fun c => Iff.rfl
  have : Finite C := Finite.of_equiv L e.toEquiv
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set s := g⁻¹ * t * g with hsdef
  have hss : s * s = 1 := by
    calc s * s = g⁻¹ * (t * t) * g := by rw [hsdef]; group
      _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have ht'C := conj_inv_mem_centralizer_singleton hsC
  have ht't' : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have ht'L := conj_inv_not_mem_sup_zpowers hset hOut hZ hperf ht hKt hsC hsL
  obtain ⟨ε₁, hε₁⟩ := exists_mulEquiv_conj_eq hset e hcan ht hKt hsC hss hsL
  obtain ⟨ε₂, hε₂⟩ := exists_mulEquiv_conj_eq hset e hcan ht hKt ht'C ht't' ht'L
  have hsN : s ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht hsC
  have hsfix : ∀ a : L, ε₁ a ∈ F → (a : G) * s = s * a := by
    intro a ha
    have hmem : s * (a : G) * s⁻¹ ∈ L := (mem_normalizer_iff.1 hsN a).1 a.2
    have h1 := hε₁ a ⟨_, hmem⟩ rfl
    rw [(hmemF _).1 ha] at h1
    have h2 : s * (a : G) * s⁻¹ = a := congrArg Subtype.val (ε₁.injective h1)
    calc (a : G) * s = s * a * s⁻¹ * s := by rw [h2]
      _ = s * a := by group
  set Θ : Subgroup G := (F.map ε₁.symm.toMonoidHom).map L.subtype with hΘdef
  have hΘperf : ⁅Θ, Θ⁆ = Θ := by rw [hΘdef, ← map_commutator, ← map_commutator, hFperf]
  have hΘL : Θ ≤ L := map_subtype_le _
  have hΘt : Θ ≤ centralizer ({t} : Set G) :=
    hΘL.trans (le_centralizer_of_mem_centralizer htC)
  have hΘs : Θ ≤ centralizer ({s} : Set G) := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact hsfix (ε₁.symm w) (by simpa using hw)
  have hΘLg := std_perfect_le_inf_conjugate hset hOut htC ht g hΘperf hΘt hΘs
  have hgL : ∀ w ∈ F, g * (ε₁.symm w : G) * g⁻¹ ∈ L := by
    intro w hw
    have hmem : (ε₁.symm w : G) ∈ Θ := ⟨ε₁.symm w, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨l, hl, hl'⟩ := (hΘLg hmem).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hl'
    rw [← hl']
    simpa [mul_assoc] using hl
  have hFix2 : ∀ w (hw : w ∈ F), ε₂ ⟨g * (ε₁.symm w : G) * g⁻¹, hgL w hw⟩ ∈ F := by
    intro w hw
    rw [hmemF]
    refine (hε₂ _ _ ?_).symm
    have hc := mem_centralizer_iff.1 htC _ (ε₁.symm w).2
    calc g * (ε₁.symm w : G) * g⁻¹ = g * ((ε₁.symm w : G) * t * t) * g⁻¹ := by
          rw [mul_assoc (ε₁.symm w : G), htt, mul_one]
      _ = g * (t * (ε₁.symm w : G) * t) * g⁻¹ := by rw [hc]
      _ = g * t * g⁻¹ * (g * (ε₁.symm w : G) * g⁻¹) * (g * t⁻¹ * g⁻¹) := by
          rw [inv_eq_of_mul_eq_one_right htt]
          group
      _ = g * t * g⁻¹ * (g * (ε₁.symm w : G) * g⁻¹) * (g * t * g⁻¹)⁻¹ := by group
  let φ₁ : F →* G := (MulAut.conj g).toMonoidHom.comp
    (L.subtype.comp (ε₁.symm.toMonoidHom.comp F.subtype))
  have hφ₁ : ∀ w : F, φ₁ w = g * (ε₁.symm w : G) * g⁻¹ := fun w => rfl
  let φ₂ : F →* L := φ₁.codRestrict L fun w => by rw [hφ₁]; exact hgL w w.2
  let β₀ : F →* F := (ε₂.toMonoidHom.comp φ₂).codRestrict F fun w => hFix2 w w.2
  have hβ₀ : ∀ w : F, (β₀ w : C) = ε₂ ⟨g * (ε₁.symm w : G) * g⁻¹, hgL w w.2⟩ := fun w => rfl
  have hinj : Function.Injective β₀ := by
    intro w w' h
    have h1 := congrArg Subtype.val h
    rw [hβ₀, hβ₀] at h1
    have h2 := congrArg Subtype.val (ε₂.injective h1)
    simp only at h2
    have h3 : (ε₁.symm w : G) = ε₁.symm w' := by
      have := congrArg (fun x => g⁻¹ * x * g) h2
      simpa [mul_assoc] using this
    exact Subtype.ext (ε₁.symm.injective (Subtype.ext h3))
  let β : MulAut F := MulEquiv.ofBijective β₀ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨S, hS⟩ := hβ β
  set m : L := ε₁.symm m₀ with hmdef
  set y : L := ε₁.symm y₀ with hydef
  have hmL : s * (m : G) * s⁻¹ ∈ L := (mem_normalizer_iff.1 hsN m).1 m.2
  have hsm : ε₁ ⟨_, hmL⟩ = η m₀ := by
    rw [hε₁ m ⟨_, hmL⟩ rfl, hmdef, MulEquiv.apply_symm_apply]
  have hyG : (y : G) = s * (m : G)⁻¹ * s⁻¹ * m := by
    have h1 : y = (⟨_, hmL⟩ : L)⁻¹ * m := by
      apply ε₁.injective
      rw [map_mul, map_inv, hsm, hydef, hmdef, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, hmy₀]
    rw [h1, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hkey : (m : G)⁻¹ * s * m = s * y := by
    rw [hyG]
    calc (m : G)⁻¹ * s * m = (m : G)⁻¹ * s⁻¹ * m := by rw [hsinv]
      _ = s * (s * (m : G)⁻¹ * s⁻¹ * m) := by
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hss, one_mul]
  have hzL : g * (y : G) * g⁻¹ ∈ L := hgL y₀ y₀.2
  refine ⟨g * m * g⁻¹, g * (y : G) * g⁻¹, hzL, ?_, ?_, ?_⟩
  · calc (g * (m : G) * g⁻¹)⁻¹ * t * (g * m * g⁻¹) = g * ((m : G)⁻¹ * s * m) * g⁻¹ := by
          rw [hsdef]; group
      _ = g * (s * y) * g⁻¹ := by rw [hkey]
      _ = t * (g * y * g⁻¹) := by rw [hsdef]; group
  · intro h1
    apply hy₀1
    have hy1 : (y : G) = 1 := by
      calc (y : G) = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hy1' : y = 1 := Subtype.ext hy1
    rw [← MulEquiv.apply_symm_apply ε₁ (y₀ : C), ← hydef, hy1', map_one]
  ·
    have hβy : (β y₀ : C) = ε₂ ⟨g * (y : G) * g⁻¹, hzL⟩ := hβ₀ y₀
    refine ⟨S.comapOfInjective ε₂.toMonoidHom ε₂.injective (by
      rw [MonoidHom.range_eq_top.2 ε₂.surjective]; exact le_top), fun u hu => ?_⟩
    have hu' : ε₂ u ∈ (S : Subgroup C) := hu
    have h1 := hS (ε₂ u) hu'
    rw [hβy, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (ε₂.injective h1)

end Standard

end CFSG.SeitzReduction.F4Pilot
