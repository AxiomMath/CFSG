module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotKernel
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms

section Fusion

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def PerfectTwistedFusion (α : MulAut X) : Prop :=
  ∃ m y : X, y ≠ 1 ∧ (α m)⁻¹ * m = y ∧
    ∃ P : Subgroup X, ⁅P, P⁆ = P ∧ y ∈ P ∧ ∀ p ∈ P, α p = p

theorem PerfectTwistedFusion.of_mulEquiv (e : X ≃* Y) {α : MulAut X} {β : MulAut Y}
    (h : ∀ x, e (α x) = β (e x)) (hβ : PerfectTwistedFusion β) : PerfectTwistedFusion α := by
  obtain ⟨m, y, hy, hmy, P, hP, hyP, hPβ⟩ := hβ
  have h' : ∀ x, α (e.symm x) = e.symm (β x) := fun x => by
    apply e.injective
    rw [h, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine ⟨e.symm m, e.symm y, fun h1 => hy ?_, ?_, P.map e.symm.toMonoidHom, ?_, ⟨y, hyP, rfl⟩,
    ?_⟩
  · rw [← e.apply_symm_apply y, h1, map_one]
  · rw [h', ← map_inv, ← map_mul, hmy]
  · rw [← map_commutator, hP]
  · rintro _ ⟨p, hp, rfl⟩
    exact (h' p).trans (congrArg e.symm (hPβ p hp))

theorem PerfectTwistedFusion.of_conj {α β ψ : MulAut X} (h : ψ * α * ψ⁻¹ = β)
    (hβ : PerfectTwistedFusion β) : PerfectTwistedFusion α :=
  PerfectTwistedFusion.of_mulEquiv ψ (fun x => by
    rw [← h, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply])
    hβ

theorem conj_mulEquiv_apply (e : X ≃* Y) (α : MulAut X) (y : Y) :
    ((e.symm.trans α).trans e) y = e (α (e.symm y)) :=
  rfl

theorem conj_mem_range_conj_iff (e : X ≃* Y) (α : MulAut X) :
    (e.symm.trans α).trans e ∈ (MulAut.conj : Y →* MulAut Y).range ↔
      α ∈ (MulAut.conj : X →* MulAut X).range := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, MulEquiv.ext fun x => ?_⟩
    have h := congrArg (fun φ : MulAut Y => φ (e x)) hc
    simp only [conj_mulEquiv_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
    rw [MulAut.conj_apply]
    apply e.injective
    rw [← h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨e c, MulEquiv.ext fun y => ?_⟩
    rw [conj_mulEquiv_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]

theorem pow_two_conj_eq_one_iff (e : X ≃* Y) (α : MulAut X) :
    ((e.symm.trans α).trans e) ^ 2 = 1 ↔ α ^ 2 = 1 := by
  constructor
  · intro h
    refine MulEquiv.ext fun x => ?_
    have h' := congrArg (fun φ : MulAut Y => φ (e x)) h
    simp only [sq, MulAut.mul_apply, conj_mulEquiv_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply] at h'
    rw [sq, MulAut.mul_apply, MulAut.one_apply]
    exact e.injective h'
  · intro h
    refine MulEquiv.ext fun y => ?_
    have h' := congrArg (fun φ : MulAut X => φ (e.symm y)) h
    simp only [sq, MulAut.mul_apply, MulAut.one_apply] at h'
    simp only [sq, MulAut.mul_apply, conj_mulEquiv_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply, h', MulEquiv.apply_symm_apply]

theorem forall_perfectTwistedFusion_of_mulEquiv (e : X ≃* Y)
    (hY : ∀ β : MulAut Y, β ^ 2 = 1 → β ∉ (MulAut.conj : Y →* MulAut Y).range →
      PerfectTwistedFusion β)
    (α : MulAut X) (hα : α ^ 2 = 1) (hαo : α ∉ (MulAut.conj : X →* MulAut X).range) :
    PerfectTwistedFusion α :=
  PerfectTwistedFusion.of_mulEquiv e (fun x => by
      rw [conj_mulEquiv_apply, MulEquiv.symm_apply_apply])
    (hY _ ((pow_two_conj_eq_one_iff e α).2 hα) fun h => hαo ((conj_mem_range_conj_iff e α).1 h))

end Fusion

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_eq_or_eq_mul_of_mem_sup_zpowers {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) {x : G} (hx : x ∈ L ⊔ zpowers t) :
    ∃ y ∈ L, x = y ∨ x = t * y := by
  have hle : zpowers t ≤ normalizer (L : Set G) :=
    (zpowers_le (H := normalizer (L : Set G))).2 (centralizer_le_normalizer _ htC)
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left L (zpowers t) hle,
    Set.mem_mul] at hx
  obtain ⟨y, hyL, z, hz, rfl⟩ := hx
  rcases eq_one_or_eq_of_mem_zpowers ht hz with rfl | rfl
  · exact ⟨y, hyL, .inl (mul_one y)⟩
  · exact ⟨y, hyL, .inr (mem_centralizer_iff.1 htC y hyL)⟩

theorem exists_conj_ne_mem_sup_zpowers_of_fusion (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L))
    (hfus : ∀ α : MulAut L, α ^ 2 = 1 → α ∉ (MulAut.conj : L →* MulAut L).range →
      PerfectTwistedFusion α)
    {t : G} (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ g⁻¹ * t * g ∈ L ⊔ zpowers t := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hK ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  obtain ⟨g, hne, hc, hN, -⟩ := exists_conj_mem_normalizer_not_mem_centralizer hset htC ht hK
  set s := g⁻¹ * t * g with hs
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by
    calc s * s = g⁻¹ * (t * t) * g := by rw [hs]; group
      _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsCt : s ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hc
  set α : MulAut L := L.normalizerMonoidHom ⟨s, hN⟩
  have hα : ∀ l : L, ((α l : L) : G) = s * l * s⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hN⟩ l
  by_cases hin : α ∈ (MulAut.conj : L →* MulAut L).range
  ·
    obtain ⟨l, hl⟩ := hin
    refine ⟨g, hne, mem_sup_zpowers_of_conj_eq htC ht hK hsCt l.2 fun y hy => ?_⟩
    have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [h, hα]
  ·
    have hα2 : α ^ 2 = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [sq, MulAut.mul_apply, MulAut.one_apply, hα, hα]
      calc s * (s * (l : G) * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
        _ = l := by rw [hs2, one_mul, inv_one, mul_one]
    obtain ⟨m, y, hy1, hmy, P, hP, hyP, hPα⟩ := hfus α hα2 hin
    have hmy' : ((α m : L) : G)⁻¹ * m = y := by
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, hmy]
    rw [hα, hsinv] at hmy'
    have key : (m : G)⁻¹ * s * m = s * y := by
      rw [← hmy']
      calc (m : G)⁻¹ * s * m = (m : G)⁻¹ * s⁻¹ * m := by rw [hsinv]
        _ = s * ((s * m * s)⁻¹ * m) := by group
    set PG := P.map L.subtype with hPGdef
    have hPG : ⁅PG, PG⁆ = PG := by rw [hPGdef, ← map_commutator, hP]
    have hPGt : PG ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨p, -, rfl⟩
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC p p.2)
    have hPGs : PG ≤ centralizer ({s} : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      have h := congrArg Subtype.val (hPα p hp)
      rw [hα] at h
      rw [mem_centralizer_singleton_iff]
      calc (p : G) * s = (s * p * s⁻¹) * s := by rw [h]
        _ = s * p := by group
    have hPL := std_perfect_le_inf_conjugate hset hOut htC ht g hPG hPGt hPGs
    obtain ⟨l, hlL, hly⟩ := (hPL ⟨y, hyP, rfl⟩).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hly
    change g⁻¹ * l * g = (y : G) at hly
    have hl1 : l ≠ 1 := fun h => hy1 (Subtype.ext (by
      rw [← hly, h, mul_one, inv_mul_cancel, OneMemClass.coe_one]))
    have hconj : (g * m * g⁻¹)⁻¹ * t * (g * m * g⁻¹) = t * l := by
      calc (g * m * g⁻¹)⁻¹ * t * (g * m * g⁻¹) = g * ((m : G)⁻¹ * s * m) * g⁻¹ := by
            rw [hs]; group
        _ = g * (s * (g⁻¹ * l * g)) * g⁻¹ := by rw [key, hly]
        _ = t * l := by rw [hs]; group
    refine ⟨g * m * g⁻¹, ?_, ?_⟩ <;> rw [hconj]
    · exact fun h => hl1 (mul_eq_left.1 h)
    · exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hlL)

end Standard

end CFSG.SeitzReduction.F4Pilot
