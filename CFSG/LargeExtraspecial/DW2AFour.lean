module

public import CFSG.LargeExtraspecial.DWTransConj
public import CFSG.LargeExtraspecial.DW2ABasic
public import CFSG.LargeExtraspecial.DWTransFaith
public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem polar_sub_eq_of_mul_self {t : S.O} (htt : t * t = 1) (u w : S.Qt) :
    polar S.q ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) w =
      polar S.q u ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
  have h1 : polar S.q ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) u) w =
      polar S.q u ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    have := polar_apply_apply t ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) u) w
    rw [← this]
    congr 1
    change ((t * t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u
    rw [htt]
    rfl
  rw [polar_sub_left, polar_sub_right, h1]

theorem isTypeA_two_of_conj {x a : G} (hxQ : x ∈ S.QG) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hxz : x ≠ S.z) (haM : a ∈ S.M) (ha2 : a * a = 1) (hρ : S.ρ ⟨a, haM⟩ ≠ 1)
    (hc : ∀ c ∈ S.QG, c * x = x * c → a * c * a⁻¹ = c ∨ a * c * a⁻¹ = c * x) :
    IsTypeA S.q ((S.ρ ⟨a, haM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
      S.cl x ∈ commSpace ((S.ρ ⟨a, haM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  set m : S.M := ⟨a, haM⟩ with hm
  set τ : S.O := S.ρ m with hτ
  set t : S.Qt ≃ₗ[ZMod 2] S.Qt := (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with ht
  have htO : t ∈ S.O := τ.2
  have hττ : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : m * m = 1 := Subtype.ext ha2
    rw [this, map_one]
  have htt : t * t = 1 := by
    change ((τ * τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1
    rw [hττ]
    rfl
  have htρ : ∀ c ∈ S.QG, t (S.cl c) = S.cl (a * c * a⁻¹) := fun c hcQ => S.ρ_cl m hcQ
  set v := S.cl x with hv
  have hv0 : v ≠ 0 := by
    rw [hv, Ne, S.cl_eq_zero_iff hxQ]
    tauto
  have hqv : S.q v = 0 := (S.q_cl_eq_zero_iff hxQ).mpr hx2
  have htv : t v = v := by
    rw [hv, htρ x hxQ]
    rcases hc x hxQ rfl with h | h
    · rw [h]
    · exfalso
      apply hx1
      have h1 : a * x * a⁻¹ = 1 := by rw [h, ← pow_two, hx2]
      have := congrArg (fun y => a⁻¹ * y * a) h1
      simpa [mul_assoc] using this
  have hN : ∀ u, polar S.q v u = 0 → t u - u = 0 ∨ t u - u = v := by
    intro u hu
    obtain ⟨c, hcQ, rfl⟩ := S.exists_cl u
    have hcx : c * x = x * c := ((S.polar_cl_eq_zero_iff hxQ hcQ).mp hu).symm
    rw [htρ c hcQ]
    rcases hc c hcQ hcx with h | h
    · left
      rw [h, sub_self]
    · right
      rw [h, S.cl_mul hcQ hxQ, add_sub_cancel_left]
  have hsa := polar_sub_eq_of_mul_self hττ
  obtain ⟨y, hy⟩ := exists_polar_eq_one hv0
  set c := t y - y with hcdef
  have hNu : ∀ u, polar S.q v u = 0 → t u - u = polar S.q u c • v := by
    intro u hu
    have key := hsa u y
    rcases hN u hu with h | h
    · rw [h, polar_zero_left] at key
      rw [h, ← key, zero_smul]
    · rw [h, hy] at key
      rw [h, ← key, one_smul]
  have hvc : polar S.q v c = 0 := by
    have := hsa v y
    rw [htv, sub_self, polar_zero_left] at this
    exact this.symm
  have hcspan : c ∉ ZMod 2 ∙ v := by
    intro hcv
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hcv
    rcases zmod2_cases μ with rfl | rfl
    ·
      rw [zero_smul] at hμ
      apply hρ
      refine Subtype.ext (LinearEquiv.ext fun w => ?_)
      change t w = w
      by_cases hw : polar S.q v w = 0
      · have := hNu w hw
        rw [← hμ, polar_zero_right, zero_smul, sub_eq_zero] at this
        exact this
      · have hw' : polar S.q v w = 1 := (zmod2_cases _).resolve_left hw
        have hwy : polar S.q v (w + y) = 0 := by
          rw [polar_add_right, hw', hy]
          rfl
        have h1 := hNu (w + y) hwy
        rw [← hμ, polar_zero_right, zero_smul, map_add, sub_eq_zero] at h1
        have h2 : t y = y := by
          have : t y - y = 0 := hμ.symm
          exact sub_eq_zero.mp this
        rw [h2] at h1
        exact add_right_cancel h1
    ·
      rw [one_smul] at hμ
      have hq := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup htO y
      have hty : t y = y + v := by
        have : t y - y = v := hμ.symm
        rw [← this]
        abel
      rw [hty, QuadraticMap.map_add S.q, hqv, add_zero, polar_comm, hy] at hq
      have := congrArg (· - S.q y) hq
      simp only [add_sub_cancel_left, sub_self] at this
      exact absurd this (by decide)
  obtain ⟨u₀, hu₀v, hu₀c⟩ : ∃ u₀, polar S.q v u₀ = 0 ∧ polar S.q u₀ c = 1 := by
    by_contra h
    push Not at h
    apply hcspan
    rw [← perp_perp (ZMod 2 ∙ v), mem_perp]
    intro u hu
    have hu' : polar S.q v u = 0 := by
      have := mem_perp.mp hu v (Submodule.mem_span_singleton_self v)
      exact this
    exact (zmod2_cases _).resolve_right (h u hu')
  have hspan : commSpace t = Submodule.span (ZMod 2) {v, c} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
      by_cases hu : polar S.q v u = 0
      · rw [hNu u hu]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
      · have hu' : polar S.q v u = 1 := (zmod2_cases _).resolve_left hu
        have huy : polar S.q v (u + y) = 0 := by
          rw [polar_add_right, hu', hy]
          rfl
        have h1 := hNu (u + y) huy
        have h2 : t u - u = polar S.q (u + y) c • v + c := by
          have e1 : t u - u = (t (u + y) - (u + y)) - (t y - y) := by rw [map_add]; abel
          rw [e1, h1, ← hcdef, sub_eq_add_zmod2]
        rw [h2]
        exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
          (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    · rw [Submodule.span_le]
      rintro w (rfl | rfl)
      · have := hNu u₀ hu₀v
        rw [hu₀c, one_smul] at this
        rw [← this]
        exact sub_mem_commSpace t u₀
      · exact sub_mem_commSpace t y
  obtain ⟨yg, hygQ, rfl⟩ := S.exists_cl y
  set w := yg⁻¹ * (a * yg * a⁻¹) with hw
  have hwQ : w ∈ S.QG := S.QG.mul_mem (S.QG.inv_mem hygQ) (S.conj_mem_QG haM hygQ)
  have hcw : c = S.cl w := by
    rw [hcdef, htρ yg hygQ, hw, S.cl_mul (S.QG.inv_mem hygQ) (S.conj_mem_QG haM hygQ),
      S.cl_inv hygQ, sub_eq_add_zmod2, add_comm]
  have hqc : S.q c = 0 := by
    rw [hcw, S.q_cl_eq_zero_iff hwQ]
    have hwx : w * x = x * w := by
      have := hvc
      rw [hcw, hv, S.polar_cl_eq_zero_iff hxQ hwQ] at this
      exact this.symm
    have hinv : a * w * a⁻¹ = w⁻¹ := by
      calc a * w * a⁻¹ = a * yg⁻¹ * a⁻¹ * ((a * a) * yg * (a⁻¹ * a⁻¹)) := by rw [hw]; group
        _ = a * yg⁻¹ * a⁻¹ * yg := by rw [ha2, ← mul_inv_rev, ha2, inv_one, one_mul, mul_one]
        _ = w⁻¹ := by rw [hw]; group
    rcases hc w hwQ hwx with h | h
    · rw [hinv] at h
      rw [pow_two]
      have := congrArg (· * w) h
      simpa using this.symm
    · exfalso
      rw [hinv] at h
      have hx' : x = (w * w)⁻¹ := by
        have := congrArg (fun y => w⁻¹ * y) h
        simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
        rw [← this]
        exact (mul_inv_rev w w).symm
      rcases S.sq_eq_one_or_z hwQ with h2 | h2
      · rw [pow_two] at h2
        rw [h2, inv_one] at hx'
        exact hx1 hx'
      · rw [pow_two] at h2
        rw [h2, S.z_inv] at hx'
        exact hxz hx'
  refine ⟨⟨TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup htO, fun h => hρ ?_, htt, ?_,
    ?_⟩, ?_⟩
  · exact Subtype.ext h
  · rw [hspan]
    exact finrank_span_pair_of_not_mem hv0 hcspan
  · intro w' hw'
    rw [hspan] at hw'
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw'
    rw [QuadraticMap.map_add S.q, QuadraticMap.map_smul, QuadraticMap.map_smul, hqv, hqc,
      polar_smul_left, polar_smul_right, hvc]
    simp
  · rw [hspan]
    exact Submodule.subset_span (Set.mem_insert _ _)

section ThreeFour

variable {W : Submodule (ZMod 2) S.Qt} (hW : IsMbarInvariant S W) (hWs : ∀ v ∈ W, S.q v = 0)
  {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxB : S.cl (g * S.z * g⁻¹) ∈ perp S W)
  (hxA : S.cl (g * S.z * g⁻¹) ∉ W)

include hxA in
omit [Finite G] in
theorem conj_ne_z_of_not_mem : g * S.z * g⁻¹ ≠ S.z := by
  intro e
  apply hxA
  rw [e, S.cl_z]
  exact zero_mem _

include hW hxQ hxA in
theorem z_not_mem_conjSub : S.z ∉ conjSub (S.clPre W) g := by
  intro hz
  have hne := conj_ne_z_of_not_mem hxA
  obtain ⟨u, -, huz, hux⟩ := S.exists_swap rfl hxQ hne
  have hM := M_le_normalizer_clPre hW
  rw [conjSub_eq_of_conj_eq hM (h' := u) huz.symm, mem_conjSub] at hz
  have e : u⁻¹ * S.z * u = g * S.z * g⁻¹ := by
    nth_rewrite 1 [← hux]
    group
  rw [e] at hz
  exact hxA hz.2

include hW hxQ hxB in
theorem z_mem_conjSub_perp : S.z ∈ conjSub (S.clPre (perp S W)) g := by
  by_cases hne : g * S.z * g⁻¹ = S.z
  · rw [mem_conjSub]
    have : g⁻¹ * S.z * g = S.z := by
      calc g⁻¹ * S.z * g = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hne]
        _ = S.z := by group
    rw [this]
    exact S.z_mem_clPre _
  obtain ⟨u, -, huz, hux⟩ := S.exists_swap rfl hxQ hne
  have hM := M_le_normalizer_clPre hW.perp
  rw [conjSub_eq_of_conj_eq hM (h' := u) huz.symm, mem_conjSub]
  have e : u⁻¹ * S.z * u = g * S.z * g⁻¹ := by
    nth_rewrite 1 [← hux]
    group
  rw [e]
  exact ⟨hxQ, hxB⟩

include hW hxQ hxB in
theorem conjSub_le_M : conjSub (S.clPre W) g ≤ S.M := by
  intro b hb
  have hz := z_mem_conjSub_perp hW hxQ hxB
  rw [mem_conjSub] at hb hz
  rw [S.mem_M_iff]
  have hc : (g⁻¹ * b * g) * (g⁻¹ * S.z * g) = (g⁻¹ * S.z * g) * (g⁻¹ * b * g) :=
    (S.polar_cl_eq_zero_iff hb.1 hz.1).mp (mem_perp.mp hz.2 _ hb.2)
  have := congrArg (fun y => g * y * g⁻¹) hc
  simpa [mul_assoc] using this

include hW hxQ hxA in
theorem eq_of_mem_conjSub_QG {b : G} (hb : b ∈ conjSub (S.clPre W) g) (hbQ : b ∈ S.QG) :
    b = 1 ∨ b = g * S.z * g⁻¹ := by
  have hM := M_le_normalizer_clPre hW
  have hne := conj_ne_z_of_not_mem hxA
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := fun h => hxA (h ▸ zero_mem _)
  have hzJ : S.z ∉ conjSub (S.clPre W) g ⊓ S.QG := fun hz => z_not_mem_conjSub hW hxQ hxA hz.1
  have hnorm : ∀ q ∈ S.QG, q * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * q →
      ∀ j ∈ conjSub (S.clPre W) g ⊓ S.QG, q * j * q⁻¹ ∈ conjSub (S.clPre W) g ⊓ S.QG := by
    intro q hq hqx j hj
    have hqM : q ∈ (S.conjBy g).M := by
      rw [(S.conjBy g).mem_M_iff, Setting.conjBy_z]
      exact hqx
    exact ⟨(mem_normalizer_iff.mp (conjBy_M_le_normalizer hM g hqM) j).mp hj.1,
      S.conj_mem_QG (S.QG_le_M hq) hj.2⟩
  have hx_mem : g * S.z * g⁻¹ ∈ conjSub (S.clPre W) g := conj_mem_conjSub (S.z_mem_clPre W)
  rcases eq_of_forall_conj_mem (T := S) hxQ hx0 inf_le_right hzJ hnorm ⟨hb, hbQ⟩ with
    h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · refine absurd ?_ (z_not_mem_conjSub hW hxQ hxA)
    have := (conjSub (S.clPre W) g).mul_mem ((conjSub (S.clPre W) g).inv_mem hx_mem) (h1 ▸ hb)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

include hW hxQ hxB hxA in
theorem conj_eq_or_of_commute {a c : G} (ha : a ∈ conjSub (S.clPre W) g) (hcQ : c ∈ S.QG)
    (hcx : c * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * c) :
    a * c * a⁻¹ = c ∨ a * c * a⁻¹ = c * (g * S.z * g⁻¹) := by
  have hM := M_le_normalizer_clPre hW
  have haM := conjSub_le_M hW hxQ hxB ha
  have hcM : c ∈ (S.conjBy g).M := by
    rw [(S.conjBy g).mem_M_iff, Setting.conjBy_z]
    exact hcx
  have h1 : a * c * a⁻¹ * c⁻¹ ∈ conjSub (S.clPre W) g := by
    have := (mem_normalizer_iff.mp (conjBy_M_le_normalizer hM g hcM) a⁻¹).mp
      ((conjSub (S.clPre W) g).inv_mem ha)
    rw [show a * c * a⁻¹ * c⁻¹ = a * (c * a⁻¹ * c⁻¹) by group]
    exact (conjSub (S.clPre W) g).mul_mem ha this
  have h2 : a * c * a⁻¹ * c⁻¹ ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG haM hcQ) (S.QG.inv_mem hcQ)
  rcases eq_of_mem_conjSub_QG hW hxQ hxA h1 h2 with h | h
  · left
    calc a * c * a⁻¹ = a * c * a⁻¹ * c⁻¹ * c := by group
      _ = c := by rw [h, one_mul]
  · right
    calc a * c * a⁻¹ = a * c * a⁻¹ * c⁻¹ * c := by group
      _ = (g * S.z * g⁻¹) * c := by rw [h]
      _ = c * (g * S.z * g⁻¹) := hcx.symm

include hW hxQ hxB hxA in
theorem conj_eq_of_mem_clPre {a c : G} (ha : a ∈ conjSub (S.clPre W) g)
    (hc : c ∈ S.clPre W) : a * c * a⁻¹ = c := by
  have hM := M_le_normalizer_clPre hW
  have haM := conjSub_le_M hW hxQ hxB ha
  have hcx : c * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * c :=
    (S.polar_cl_eq_zero_iff hc.1 hxQ).mp (mem_perp.mp hxB _ hc.2)
  rcases conj_eq_or_of_commute hW hxQ hxB hxA ha hc.1 hcx with h | h
  · exact h
  · exfalso
    apply hxA
    have h1 : a * c * a⁻¹ ∈ S.clPre W := (mem_normalizer_iff.mp (hM haM) c).mp hc
    rw [h] at h1
    have := (S.clPre W).mul_mem ((S.clPre W).inv_mem hc) h1
    rw [← mul_assoc, inv_mul_cancel, one_mul] at this
    exact this.2

include hW hxQ hxB hxA in
theorem ρ_conjSub_fix {a : G} (ha : a ∈ conjSub (S.clPre W) g) {w : S.Qt} (hw : w ∈ W) :
    ((S.ρ ⟨a, conjSub_le_M hW hxQ hxB ha⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl w
  rw [S.ρ_cl _ hcQ]
  change S.cl (a * c * a⁻¹) = S.cl c
  rw [conj_eq_of_mem_clPre hW hxQ hxB hxA ha ⟨hcQ, hw⟩]

include hWs in
theorem mul_self_of_mem_conjSub {a : G} (ha : a ∈ conjSub (S.clPre W) g) : a * a = 1 := by
  rw [mem_conjSub] at ha
  have h := sq_eq_one_of_mem_clPre hWs ha
  rw [pow_two] at h
  have := congrArg (fun y => g * y * g⁻¹) h
  simp only [mul_assoc, mul_inv_cancel_left, mul_one, mul_inv_cancel] at this
  calc a * a = g * (g⁻¹ * a * g) * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = 1 := by rw [mul_assoc g, h, mul_one, mul_inv_cancel]

include hW hWs hxQ hxB hxA in
theorem isTypeA_ρ_conjSub {a : G} (ha : a ∈ conjSub (S.clPre W) g)
    (hρ : S.ρ ⟨a, conjSub_le_M hW hxQ hxB ha⟩ ≠ 1) :
    IsTypeA S.q ((S.ρ ⟨a, conjSub_le_M hW hxQ hxB ha⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
      S.cl (g * S.z * g⁻¹) ∈
        commSpace ((S.ρ ⟨a, conjSub_le_M hW hxQ hxB ha⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hne := conj_ne_z_of_not_mem hxA
  have hx1 : g * S.z * g⁻¹ ≠ 1 := S.s12_conj_z_ne_one g
  exact isTypeA_two_of_conj hxQ (S.s12_conj_z_sq g) hx1 hne _ (mul_self_of_mem_conjSub hWs ha) hρ
    fun c hcQ hcx => conj_eq_or_of_commute hW hxQ hxB hxA ha hcQ hcx

end ThreeFour

end CFSG.LargeExtraspecial.DW
