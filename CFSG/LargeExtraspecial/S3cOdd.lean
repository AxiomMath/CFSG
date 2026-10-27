module

public import CFSG.LargeExtraspecial.S3cShult
public import CFSG.LargeExtraspecial.S3cRad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)
open TauCeti.QuadraticMap (orthogonalGroup)

section Generic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem commSpace_mul_le (g h : V ≃ₗ[ZMod 2] V) :
    commSpace (g * h) ≤ commSpace g ⊔ commSpace h := by
  intro y hy
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
  rw [show (g * h) v - v = (g (h v) - h v) + (h v - v) by rw [LinearEquiv.mul_apply]; abel]
  exact Submodule.add_mem_sup (mem_commSpace.mpr ⟨h v, rfl⟩) (mem_commSpace.mpr ⟨v, rfl⟩)

theorem commSpace_pow_le (g : V ≃ₗ[ZMod 2] V) (k : ℕ) : commSpace (g ^ k) ≤ commSpace g := by
  induction k with
  | zero =>
    intro y hy
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    simp
  | succ k ih =>
    rw [pow_succ']
    exact (commSpace_mul_le g (g ^ k)).trans (sup_le le_rfl ih)

end Generic

namespace TransvectionConfig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {a : V} {W : Submodule (ZMod 2) V} {L : Subgroup (V ≃ₗ[ZMod 2] V)}
  (C : TransvectionConfig q a W L)
include C

theorem polar_a_eq_zero_of_apply_eq {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ L) (ht1 : t ≠ 1) {v : V}
    (hv : t v = v) : polar q a v = 0 := by
  rcases zmod2_eq_zero_or_eq_one (polar q a v) with h | h
  · exact h
  exfalso
  obtain ⟨φ, rfl⟩ := C.exists_sOf_eq ht
  apply ht1
  rw [C.sOf_eq_one_iff]
  refine C.lineW.linearMap_qext (LinearMap.ext fun w => ?_)
  have := C.polar_sOf_sub h φ w
  rw [hv, sub_self, polar_zero_left] at this
  simpa using this.symm

theorem apply_u_of_commute [FiniteDimensional (ZMod 2) V] {x s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L)
    (hsx : s * x = x * s) {u : V} (hu : u ∉ (ZMod 2) ∙ a)
    (hcomm : commSpace x = Submodule.span (ZMod 2) {a, u}) : s u = u ∨ s u = u + a := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Submodule.zero_mem _)
  have hua : u ≠ a := fun h => hu (by rw [h]; exact Submodule.mem_span_singleton_self a)
  have huC : u ∈ commSpace x := by
    rw [hcomm]
    exact Submodule.subset_span (by simp)
  have hsuC : s u ∈ commSpace x := by
    obtain ⟨v, hv⟩ := mem_commSpace.mp huC
    refine mem_commSpace.mpr ⟨s v, ?_⟩
    rw [← hv, map_sub, ← LinearEquiv.mul_apply, ← hsx, LinearEquiv.mul_apply]
  rw [hcomm] at hsuC
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hsuC
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one d with rfl | rfl
  · exfalso
    apply hu0
    have : s u = 0 := by rw [← hcd]; simp
    simpa using congrArg s.symm this
  · left
    rw [← hcd]
    simp
  · exfalso
    apply hua
    have : s u = s a := by rw [← hcd, C.fix s hs]; simp
    exact s.injective this
  · right
    rw [← hcd]
    simp [add_comm]

theorem card_commute_le_two [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {x ι : V ≃ₗ[ZMod 2] V} (hx : x ∈ L) (hxN : x ∈ pointRadical q a) (hx1 : x ≠ 1)
    (hιO : ι ∈ orthogonalGroup q) {m : ℕ} (hm : Odd m) (hιm : ι ^ m = 1)
    (hinv : x * ι * x = ι⁻¹) (hιa : ι a ≠ a) :
    Nat.card {s : V ≃ₗ[ZMod 2] V // s ∈ L ∧ s * ι = ι * s} ≤ 2 := by
  classical
  have ha0 := C.ha0
  have haq := C.q_a
  obtain ⟨u, hau, hxu⟩ := (mem_pointRadical_iff hq ha0 haq).mp hxN
  have hu : u ∉ (ZMod 2) ∙ a := by
    intro hu
    apply hx1
    rw [hxu, (eichler_eq_one_iff hq ha0 haq hau).mpr hu]
  have hcomm : commSpace x = Submodule.span (ZMod 2) {a, u} := by
    rw [hxu]
    exact (eichler_type_of_not_mem_span hq ha0 haq hau hu).1
  have hxx : x * x = 1 := C.sq x hx
  set x' := ι⁻¹ * x * ι with hx'
  have hxι : x * ι⁻¹ * x = ι := by
    calc x * ι⁻¹ * x = x * (x * ι * x) * x := by rw [hinv]
      _ = (x * x) * ι * (x * x) := by group
      _ = ι := by rw [hxx, one_mul, mul_one]
  have hsq : ι ^ 2 = x * x' := by
    rw [hx', pow_two, ← mul_assoc, ← mul_assoc, hxι]
  obtain ⟨k, rfl⟩ := hm
  have hιk : (ι ^ 2) ^ (k + 1) = ι := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hιm, one_mul]
  have hcommι : commSpace ι ≤ commSpace x ⊔ commSpace x' := by
    calc commSpace ι = commSpace ((ι ^ 2) ^ (k + 1)) := by rw [hιk]
      _ ≤ commSpace (ι ^ 2) := commSpace_pow_le _ _
      _ = commSpace (x * x') := by rw [hsq]
      _ ≤ commSpace x ⊔ commSpace x' := commSpace_mul_le _ _
  obtain ⟨w, hwι, hwa⟩ : ∃ w ∈ commSpace ι, polar q a w ≠ 0 := by
    by_contra h
    push Not at h
    apply hιa
    have hperp : ∀ v, polar q (ι⁻¹ a - a) v = 0 := by
      intro v
      have h1 := h (ι v - v) (mem_commSpace.mpr ⟨v, rfl⟩)
      have h2 : polar q (ι⁻¹ a) v = polar q a (ι v) := by
        have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (inv_mem hιO) a (ι v)
        rwa [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'] at this
      rw [QuadraticMap.polar_sub_left, h2, ← QuadraticMap.polar_sub_right, h1]
    have h0 : ι⁻¹ a - a = 0 :=
      hq.1 _ fun v => by rw [polarBilin_apply_apply]; exact hperp v
    calc ι a = ι (ι⁻¹ a) := by rw [sub_eq_zero.mp h0]
      _ = a := apply_inv_apply ι a
  have hZ : ∀ t ∈ L, t * ι = ι * t → t u = u → t = 1 := by
    intro t ht htι htu
    by_contra ht1
    have hfix1 : ∀ y ∈ commSpace x, t y = y := by
      intro y hy
      rw [hcomm] at hy
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [map_add, map_smul, map_smul, C.fix t ht, htu]
    have hfix2 : ∀ y ∈ commSpace x', t y = y := by
      intro y hy
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      have hy' : x (ι v) - ι v ∈ commSpace x := mem_commSpace.mpr ⟨ι v, rfl⟩
      have e : x' v - v = ι⁻¹ (x (ι v) - ι v) := by
        rw [hx', map_sub, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply']
        rfl
      have htι' : Commute t ι⁻¹ := (Commute.inv_right htι)
      rw [e, ← LinearEquiv.mul_apply, htι'.eq, LinearEquiv.mul_apply, hfix1 _ hy']
    have htw : t w = w := by
      obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp (hcommι hwι)
      rw [map_add, hfix1 y hy, hfix2 y' hy']
    exact hwa (C.polar_a_eq_zero_of_apply_eq ht ht1 htw)
  let f : {s : V ≃ₗ[ZMod 2] V // s ∈ L ∧ s * ι = ι * s} → Bool := fun s => decide (s.1 u = u)
  have hf : Function.Injective f := by
    rintro ⟨s, hs, hsι⟩ ⟨s', hs', hs'ι⟩ hss'
    have hsu := C.apply_u_of_commute hs (C.comm s hs x hx) hu hcomm
    have hs'u := C.apply_u_of_commute hs' (C.comm s' hs' x hx) hu hcomm
    simp only [f, decide_eq_decide] at hss'
    have heq : s u = s' u := by
      rcases hsu with h1 | h1 <;> rcases hs'u with h2 | h2
      · rw [h1, h2]
      · exact absurd (h2.symm.trans (hss'.mp h1)) (fun h => ha0 (by simpa using h))
      · exact absurd (h1.symm.trans (hss'.mpr h2)) (fun h => ha0 (by simpa using h))
      · rw [h1, h2]
    have hcι : (s⁻¹ * s') * ι = ι * (s⁻¹ * s') :=
      ((Commute.inv_left hsι).mul_left hs'ι).eq
    have h1 := hZ (s⁻¹ * s') (mul_mem (inv_mem hs) hs') hcι (by
      rw [LinearEquiv.mul_apply, ← heq,
        CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'])
    have : s = s' := by
      calc s = s * (s⁻¹ * s') := by rw [h1, mul_one]
        _ = s' := by group
    exact Subtype.ext this
  calc Nat.card {s : V ≃ₗ[ZMod 2] V // s ∈ L ∧ s * ι = ι * s} ≤ Nat.card Bool :=
        Nat.card_le_card_of_injective f hf
    _ = 2 := by simp

end TransvectionConfig

namespace Setting

open Subgroup

universe u

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem commute_of_fix_of_Lbar_inf_eq {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {x : S.O} (hx : x ∈ S.Lbar g) (hx1 : x ≠ 1)
    (hxN : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hD : ∀ s ∈ S.Lbar g,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) → s = 1 ∨ s = x)
    {m : S.O} (hmM : m ∈ S.Mbar)
    (hma : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) :
    m * x = x * m := by
  obtain ⟨⟨h, hh⟩, rfl⟩ := MonoidHom.mem_range.mp hmM
  have hL := S.Lbar_mul_eq_of_fix haQ hne hh hma
  have hmem : S.ρ ⟨h, hh⟩ * x * (S.ρ ⟨h, hh⟩)⁻¹ ∈ S.Lbar g := by
    rw [← hL, S.Lbar_mul hh]
    exact ⟨x, hx, rfl⟩
  have hmN : ((S.ρ ⟨h, hh⟩ * x * (S.ρ ⟨h, hh⟩)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
      pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
    have := conj_mem_pointRadical (m := ((S.ρ ⟨h, hh⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (S.ρ ⟨h, hh⟩).2 hxN
    rw [hma] at this
    simpa using this
  rcases hD _ hmem hmN with h1 | h1
  · exfalso
    apply hx1
    calc x = (S.ρ ⟨h, hh⟩)⁻¹ * (S.ρ ⟨h, hh⟩ * x * (S.ρ ⟨h, hh⟩)⁻¹) * S.ρ ⟨h, hh⟩ := by
          group
      _ = 1 := by rw [h1]; group
  · calc S.ρ ⟨h, hh⟩ * x = S.ρ ⟨h, hh⟩ * x * (S.ρ ⟨h, hh⟩)⁻¹ * S.ρ ⟨h, hh⟩ := by group
      _ = x * S.ρ ⟨h, hh⟩ := by rw [h1]

theorem card_Lbar_commute_le_two (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) {x : S.O} (hx : x ∈ S.Lbar g) (hx1 : x ≠ 1)
    (hxN : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hD : ∀ s ∈ S.Lbar g,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) → s = 1 ∨ s = x)
    {ι : S.O} (hιM : ι ∈ S.Mbar) {m : ℕ} (hm : Odd m) (hιm : ι ^ m = 1)
    (hinv : x * ι * x = ι⁻¹) (hι1 : ι ≠ 1) :
    Nat.card {s : S.Qt ≃ₗ[ZMod 2] S.Qt // s ∈ S.LbarLin g ∧
      s * (ι : S.Qt ≃ₗ[ZMod 2] S.Qt) = (ι : S.Qt ≃ₗ[ZMod 2] S.Qt) * s} ≤ 2 := by
  have C := S.transvectionConfig hTI hn haQ hne hno hirr
  have hxx : x * x = 1 := by
    have := S.sq_eq_one_of_mem_Lbar haQ hx
    rwa [pow_two] at this
  have hιa : (ι : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹) := by
    intro hfix
    apply hι1
    have hc := S.commute_of_fix_of_Lbar_inf_eq haQ hne hx hx1 hxN hD hιM hfix
    have h2 : ι * ι = 1 := by
      have : ι⁻¹ = ι := by
        rw [← hinv, hc.symm, mul_assoc, hxx, mul_one]
      calc ι * ι = ι * ι⁻¹ := by rw [this]
        _ = 1 := mul_inv_cancel ι
    obtain ⟨k, rfl⟩ := hm
    rw [pow_succ, pow_mul, pow_two, h2, one_pow, one_mul] at hιm
    exact hιm
  have hx1' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h => hx1 (Subtype.ext h)
  refine C.card_commute_le_two S.q_nondegenerate (S.coe_mem_LbarLin hx) hxN hx1' ι.2 hm
    (by rw [← Subgroup.coe_pow, hιm]; rfl) (by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hinv]
      rfl) hιa

end Setting

end CFSG.LargeExtraspecial
