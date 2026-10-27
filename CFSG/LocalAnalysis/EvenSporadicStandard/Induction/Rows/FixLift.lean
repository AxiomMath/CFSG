module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CentralLift

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup

variable {X : Type*} [Group X]

theorem card_comap_of_surjective {Q : Type*} [Group Q] (π : X →* Q)
    (hπ : Function.Surjective π) (V : Subgroup Q) :
    Nat.card (V.comap π) = Nat.card V * Nat.card π.ker := by
  let ψ : ↥(V.comap π) →* ↥V :=
    { toFun := fun d => ⟨π d, d.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : X) (b : X)) }
  have hker : ψ.ker = π.ker.subgroupOf (V.comap π) := by
    ext d
    simp [ψ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    obtain ⟨x, rfl⟩ := hπ v
    exact ⟨⟨x, hv⟩, rfl⟩
  have hle : π.ker ≤ V.comap π := fun z hz => by
    show π z ∈ V
    rw [MonoidHom.mem_ker.1 hz]
    exact V.one_mem
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.topEquiv).toEquiv] at h1
  rw [mul_comm]
  exact h1.symm

theorem exists_conj_of_cover (hperf : Group.IsPerfect X)
    (hinn : ∀ α : MulAut (X ⧸ center X), ∃ g : X ⧸ center X, α = MulAut.conj g)
    (α : MulAut X) : ∃ g : X, α = MulAut.conj g := by
  have hmap : (center X).map α.toMonoidHom = center X := Subgroup.map_center_eq α
  let αq : X ⧸ center X ≃* X ⧸ center X := QuotientGroup.congr (center X) (center X) α hmap
  obtain ⟨gq, hgq⟩ := hinn αq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gq
  have hmem : ∀ k : X, (α k)⁻¹ * (g * k * g⁻¹) ∈ center X := by
    intro k
    have h1 := DFunLike.congr_fun hgq (k : X ⧸ center X)
    have h2 : ((α k : X) : X ⧸ center X) = ((g * k * g⁻¹ : X) : X ⧸ center X) := h1
    exact QuotientGroup.eq.1 h2
  let lam : X →* ↥(center X) :=
    { toFun := fun k => ⟨(α k)⁻¹ * (g * k * g⁻¹), hmem k⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hmem a)
        show (α (a * b))⁻¹ * (g * (a * b) * g⁻¹) =
          ((α a)⁻¹ * (g * a * g⁻¹)) * ((α b)⁻¹ * (g * b * g⁻¹))
        calc (α (a * b))⁻¹ * (g * (a * b) * g⁻¹)
            = (α b)⁻¹ * ((α a)⁻¹ * (g * a * g⁻¹)) * (g * b * g⁻¹) := by
              rw [map_mul]
              group
          _ = ((α a)⁻¹ * (g * a * g⁻¹)) * (α b)⁻¹ * (g * b * g⁻¹) := by
              rw [hc ((α b)⁻¹)]
          _ = ((α a)⁻¹ * (g * a * g⁻¹)) * ((α b)⁻¹ * (g * b * g⁻¹)) := by
              rw [mul_assoc _ ((α b)⁻¹)] }
  have hker : commutator X ≤ lam.ker := Abelianization.commutator_subset_ker lam
  have htop : commutator X = ⊤ := Group.isPerfect_def.1 hperf
  refine ⟨g, MulEquiv.ext fun k => ?_⟩
  have hk : k ∈ lam.ker := hker (htop ▸ Subgroup.mem_top k)
  have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
  simp only [lam, OneMemClass.coe_one] at h1
  rw [MulAut.conj_apply]
  exact inv_mul_eq_one.1 h1

@[expose] def twistedCommHom {Zc : Subgroup X} (hZ : Zc ≤ center X) {D : Subgroup X} {g : X}
    (hc : ∀ d ∈ D, d * g * d⁻¹ * g⁻¹ ∈ Zc) : ↥D →* X where
  toFun d := (d : X) * g * (d : X)⁻¹ * g⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hca := hc _ a.2
    have hcb := hc _ b.2
    have e : ((a * b : ↥D) : X) * g * ((a * b : ↥D) : X)⁻¹ * g⁻¹ =
        ((a : X) * ((b : X) * g * (b : X)⁻¹ * g⁻¹) * (a : X)⁻¹) *
          ((a : X) * g * (a : X)⁻¹ * g⁻¹) := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    have hcen : ∀ z ∈ Zc, ∀ y : X, y * z = z * y := fun z hz y =>
      Subgroup.mem_center_iff.1 (hZ hz) y
    have hc' := hcen _ hcb (a : X)
    rw [e, show (a : X) * ((b : X) * g * (b : X)⁻¹ * g⁻¹) * (a : X)⁻¹ =
        (b : X) * g * (b : X)⁻¹ * g⁻¹ by
      calc (a : X) * ((b : X) * g * (b : X)⁻¹ * g⁻¹) * (a : X)⁻¹
          = ((b : X) * g * (b : X)⁻¹ * g⁻¹) * (a : X) * (a : X)⁻¹ := by rw [hc']
        _ = (b : X) * g * (b : X)⁻¹ * g⁻¹ := mul_inv_cancel_right _ _]
    exact hcen _ hca _

theorem exists_elemAbelian_commuting_of_cover [Finite X] {Q : Type*} [Group Q] (π : X →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center X) (hZ : Nat.card π.ker ≤ 2) (g : X)
    (V : Subgroup Q) (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hVs : ∀ v ∈ V, v * v = 1)
    (hV : 2 ^ 6 ≤ Nat.card V) (hVg : ∀ v ∈ V, v * π g = π g * v) :
    ∃ A : Subgroup X, IsElementaryAbelian 2 A ∧ (∀ a ∈ A, g * a = a * g) ∧
      ∃ k, 3 ≤ k ∧ Nat.card A = 2 ^ k := by
  set N : Subgroup X := V.comap π with hN
  have hkerN : π.ker ≤ N := fun z hz => by
    show π z ∈ V
    rw [MonoidHom.mem_ker.1 hz]
    exact V.one_mem
  have hmemN : ∀ d, d ∈ N ↔ π d ∈ V := fun d => Iff.rfl
  have hcomm : ∀ d ∈ N, d * g * d⁻¹ * g⁻¹ ∈ π.ker := fun d hd => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have h1 := hVg _ ((hmemN d).1 hd)
    calc π d * π g * (π d)⁻¹ * (π g)⁻¹ = π g * π d * (π d)⁻¹ * (π g)⁻¹ := by rw [h1]
      _ = 1 := by group
  let ψ := twistedCommHom hker hcomm
  set E₁ : Subgroup X := N ⊓ centralizer ({g} : Set X) with hE₁
  have hψker : ψ.ker = E₁.subgroupOf N := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_centralizer_singleton_iff]
    show (d : X) * g * (d : X)⁻¹ * g⁻¹ = 1 ↔ _
    refine ⟨fun e => ⟨d.2, ?_⟩, fun e => ?_⟩
    · rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at e
      exact e
    · calc (d : X) * g * (d : X)⁻¹ * g⁻¹ = g * (d : X) * (d : X)⁻¹ * g⁻¹ := by rw [e.2]
        _ = 1 := by group
  have hrange : Nat.card ψ.range ≤ 2 := by
    refine le_trans (Subgroup.card_le_of_le (K := π.ker) ?_) hZ
    rintro _ ⟨d, rfl⟩
    exact hcomm _ d.2
  have hNE : Nat.card N ≤ 2 * Nat.card E₁ := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hψker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E₁ ≤ N)).toEquiv] at h1
    calc Nat.card N = _ := h1.symm
      _ ≤ Nat.card E₁ * 2 := Nat.mul_le_mul_left _ hrange
      _ = _ := mul_comm _ _
  have hNcard := card_comap_of_surjective π hπ V
  have hkerE : π.ker ≤ E₁ := fun z hz => ⟨hkerN hz, by
    show z ∈ centralizer ({g} : Set X)
    rw [mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.1 (hker hz) g).symm⟩
  let Z' : Subgroup ↥E₁ := π.ker.subgroupOf E₁
  have hZ'card : Nat.card Z' = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerE).toEquiv
  have hE : CentralLift Z' (⊤ : Subgroup ↥E₁) 1 :=
    { central := by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_center_iff.1 (hker hz) (y : X)
      le := le_top
      sq_mem := fun e _ => by
        show ((e * e : ↥E₁) : X) ∈ π.ker
        rw [MonoidHom.mem_ker, Subgroup.coe_mul, map_mul]
        exact hVs _ ((hmemN _).1 e.2.1)
      comm_mem := fun e _ f _ => by
        show (((e * f * e⁻¹ * f⁻¹ : ↥E₁)) : X) ∈ π.ker
        rw [MonoidHom.mem_ker]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        have := hVc _ ((hmemN _).1 e.2.1) _ ((hmemN _).1 f.2.1)
        calc π e * π f * (π e)⁻¹ * (π f)⁻¹ = π f * π e * (π e)⁻¹ * (π f)⁻¹ := by rw [this]
          _ = 1 := by group
      bound := fun A hA _ => by
        rw [pow_one]
        exact (Subgroup.card_le_of_le hA).trans (hZ'card.le.trans hZ) }
  have hn : 2 ^ 5 * Nat.card Z' ≤ Nat.card (⊤ : Subgroup ↥E₁) := by
    rw [hZ'card, Nat.card_congr (Subgroup.topEquiv).toEquiv]
    have hpos : 0 < Nat.card π.ker := Nat.card_pos
    rw [hNcard] at hNE
    nlinarith
  obtain ⟨A', -, hA', k, hk, hAk⟩ :=
    CentralLift.exists_elementaryAbelian_of_central_lift hE hn (n := 5) (t := 3)
      (by intro k hk; omega)
  refine ⟨A'.map E₁.subtype, ?_, ?_, k, hk, ?_⟩
  · refine isElementaryAbelian_of_sq_eq_one _ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := hA'.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A') ⟨b, hb⟩
      exact congrArg (fun z : A' => ((z : ↥E₁) : X)) this
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A') a ha
      simpa [pow_two] using congrArg (fun z : ↥E₁ => (z : X)) h1
  · rintro _ ⟨a, -, rfl⟩
    exact (mem_centralizer_singleton_iff.1 a.2.2).symm
  · rw [← hAk]
    exact (Nat.card_congr (A'.equivMapOfInjective E₁.subtype E₁.subtype_injective).toEquiv).symm

theorem involutionFixes_of_cover [Finite X] (hperf : Group.IsPerfect X)
    (hz : Nat.card (center X) ≤ 2)
    (hinn : ∀ α : MulAut (X ⧸ center X), ∃ g : X ⧸ center X, α = MulAut.conj g)
    (hV : ∀ s : X ⧸ center X, s ≠ 1 → s * s = 1 → ∃ V : Subgroup (X ⧸ center X),
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ (∀ v ∈ V, v * v = 1) ∧ 2 ^ 6 ≤ Nat.card V ∧
        ∀ v ∈ V, v * s = s * v)
    (α : MulAut X) (h1 : α ≠ 1) (h2 : α * α = 1) :
    ∃ E : Subgroup X, (∀ x ∈ E, α x = x) ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ 8 ≤ Nat.card E := by
  obtain ⟨g, rfl⟩ := exists_conj_of_cover hperf hinn α
  have hg : g ∉ center X := fun hgc => h1 (MulEquiv.ext fun y => by
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.1 hgc y).symm)
  have hgg : g * g ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := DFunLike.congr_fun h2 y
    rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.one_apply] at this
    calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [this]
      _ = g * g * y := by group
  have hs1 : (g : X ⧸ center X) ≠ 1 := fun h => hg (QuotientGroup.eq_one_iff g |>.1 h)
  have hs2 : (g : X ⧸ center X) * (g : X ⧸ center X) = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff (g * g)).2 hgg
  obtain ⟨V, hVc, hVs, hV6, hVg⟩ := hV _ hs1 hs2
  have hker : (QuotientGroup.mk' (center X)).ker ≤ center X := by
    rw [QuotientGroup.ker_mk']
  obtain ⟨A, hA, hAg, k, hk, hAk⟩ := exists_elemAbelian_commuting_of_cover
    (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _) hker
    (by rwa [QuotientGroup.ker_mk']) g V hVc hVs hV6 hVg
  refine ⟨A, fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_, ?_⟩
  · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact hAg x hx
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hx
    simpa [pow_two] using this
  · have := hA.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rw [hAk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem exists_elemAbelian_of_ext {P : Type*} [Group P] [Finite P] (Z N : Subgroup P)
    (hZc : Z ≤ center P) (hZN : Z ≤ N) (hsq : ∀ e : P, e * e ∈ Z)
    (hcomm : ∀ e f : P, e * f * e⁻¹ * f⁻¹ ∈ Z) (hZ2 : Nat.card Z = 2)
    (hN : 2 ^ 12 ≤ Nat.card N) :
    ∃ A : Subgroup P, A ≤ N ∧ IsElementaryAbelian 2 A ∧ ∃ k, 6 ≤ k ∧ Nat.card A = 2 ^ k := by
  have h : CentralLift Z N 1 :=
    { central := hZc
      le := hZN
      sq_mem := fun e _ => hsq e
      comm_mem := fun e _ f _ => hcomm e f
      bound := fun A hA _ => by
        rw [pow_one]
        exact (Subgroup.card_le_of_le hA).trans hZ2.le }
  have hn : 2 ^ 11 * Nat.card Z ≤ Nat.card N := by
    rw [hZ2]
    calc 2 ^ 11 * 2 = 2 ^ 12 := by norm_num
      _ ≤ Nat.card N := hN
  obtain ⟨A, hAN, hA, k, hk, hAk⟩ := CentralLift.exists_elementaryAbelian_of_central_lift h hn
    (t := 6) (by intro k hk; omega)
  exact ⟨A, hAN, hA, k, hk, hAk⟩

theorem fixes_of_mulEquiv {K C : Type*} [Group K] [Group C] (ε : K ≃* C)
    (h : ∀ α : MulAut C, α ≠ 1 → α * α = 1 → ∃ E : Subgroup C, (∀ x ∈ E, α x = x) ∧
      (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ 8 ≤ Nat.card E)
    (α : MulAut K) (h1 : α ≠ 1) (h2 : α * α = 1) :
    ∃ E : Subgroup K, (∀ x ∈ E, α x = x) ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ 8 ≤ Nat.card E := by
  let α' : MulAut C := (ε.symm.trans α).trans ε
  have hα'1 : α' ≠ 1 := fun h' => h1 (MulEquiv.ext fun x => by
    have := DFunLike.congr_fun h' (ε x)
    simp only [α', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at this
    exact ε.injective this)
  have hα'2 : α' * α' = 1 := MulEquiv.ext fun c => by
    have := DFunLike.congr_fun h2 (ε.symm c)
    simp only [α', MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply] at this ⊢
    rw [this, MulEquiv.apply_symm_apply]
  obtain ⟨E', hfix, hsq, hcomm, hcard⟩ := h α' hα'1 hα'2
  refine ⟨E'.map ε.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    have := hfix c hc
    simp only [α', MulEquiv.trans_apply] at this
    show α (ε.symm c) = ε.symm c
    apply ε.injective
    rw [MulEquiv.apply_symm_apply]
    exact this
  · rintro _ ⟨c, hc, rfl⟩
    show ε.symm c * ε.symm c = 1
    rw [← map_mul, hsq c hc, map_one]
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    show ε.symm c * ε.symm d = ε.symm d * ε.symm c
    rw [← map_mul, ← map_mul, hcomm c hc d hd]
  · rw [← Nat.card_congr (E'.equivMapOfInjective ε.symm.toMonoidHom ε.symm.injective).toEquiv]
    exact hcard

end CFSG.EvenSporadicStandard.Induction.Hyp
