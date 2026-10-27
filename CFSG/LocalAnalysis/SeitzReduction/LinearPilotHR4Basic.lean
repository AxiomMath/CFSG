module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem PerfectTwistedFusionIn.of_mulEquiv (e : X ≃* Y) {α : MulAut X} {β : MulAut Y}
    {Q : Y → Prop} (h : ∀ x, e (α x) = β (e x)) (hβ : PerfectTwistedFusionIn β Q) :
    PerfectTwistedFusionIn α fun x => Q (e x) := by
  obtain ⟨m, y, hy, hmy, hQ, P, hP, hyP, hPβ⟩ := hβ
  have h' : ∀ x, α (e.symm x) = e.symm (β x) := fun x => by
    apply e.injective
    rw [h, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine ⟨e.symm m, e.symm y, fun h1 => hy ?_, ?_, ?_, P.map e.symm.toMonoidHom, ?_,
    ⟨y, hyP, rfl⟩, ?_⟩
  · rw [← e.apply_symm_apply y, h1, map_one]
  · rw [h', ← map_inv, ← map_mul, hmy]
  · show Q (e (e.symm y))
    rwa [MulEquiv.apply_symm_apply]
  · rw [← map_commutator, hP]
  · rintro _ ⟨p, hp, rfl⟩
    exact (h' p).trans (congrArg e.symm (hPβ p hp))

theorem forall_perfectTwistedFusionIn_of_mulEquiv (e : X ≃* Y) {Q : Y → Prop}
    (hY : ∀ β : MulAut Y, β ^ 2 = 1 → β ∉ (MulAut.conj : Y →* MulAut Y).range →
      PerfectTwistedFusionIn β Q)
    (α : MulAut X) (hα : α ^ 2 = 1) (hαo : α ∉ (MulAut.conj : X →* MulAut X).range) :
    PerfectTwistedFusionIn α fun x => Q (e x) :=
  PerfectTwistedFusionIn.of_mulEquiv e (fun x => by
      rw [F4Pilot.conj_mulEquiv_apply, MulEquiv.symm_apply_apply])
    (hY _ ((F4Pilot.pow_two_conj_eq_one_iff e α).2 hα)
      fun h => hαo ((F4Pilot.conj_mem_range_conj_iff e α).1 h))

end Transport

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem orderOf_eq_two_of_eq_or_eq_mul {t x y : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) (hyL : y ∈ L) (hx : orderOf x = 2) (hne : x ≠ t)
    (hxy : x = y ∨ x = t * y) : orderOf y = 2 := by
  rcases hxy with rfl | rfl
  · exact hx
  · have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
    have hx2 : (t * y) * (t * y) = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    have hc : (t * y) * t = t * (t * y) := by
      rw [mul_assoc, ← mem_centralizer_iff.1 htC y hyL]
    have hy' : y = t * (t * y) := by rw [← mul_assoc, ht2, one_mul]
    rw [hy']
    exact F4Pilot.orderOf_mul_eq_two_of_commute ht2 hx2 hc hne

omit [Finite G] in
theorem normalizerMonoidHom_mem_range_conj_of_mem_sup {t x : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) (hN : x ∈ normalizer (L : Set G))
    (hx : x ∈ L ⊔ zpowers t) :
    L.normalizerMonoidHom ⟨x, hN⟩ ∈ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨y, hyL, hy⟩ := F4Pilot.exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hx
  refine ⟨⟨y, hyL⟩, MulEquiv.ext fun l => Subtype.ext ?_⟩
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hN⟩ l, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rcases hy with rfl | rfl
  · rfl
  · have hm : y * (l : G) * y⁻¹ ∈ L := mul_mem (mul_mem hyL l.2) (inv_mem hyL)
    calc y * (l : G) * y⁻¹ = t * (y * l * y⁻¹) * t⁻¹ := by
          rw [← mem_centralizer_iff.1 htC _ hm, mul_inv_cancel_right]
      _ = t * y * l * (t * y)⁻¹ := by group

theorem exists_conj_inner_or_twistedFusion (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {Q : L → Prop}
    (hfus : ∀ α : MulAut L, α ^ 2 = 1 → α ∉ (MulAut.conj : L →* MulAut L).range →
      PerfectTwistedFusionIn α Q)
    {t : G} (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) ∧
      g⁻¹ * t * g ∈ normalizer (L : Set G) ∧
      ((∃ y ∈ L, orderOf y = 2 ∧ (g⁻¹ * t * g = y ∨ g⁻¹ * t * g = t * y)) ∨
        (g⁻¹ * t * g ∉ L ⊔ zpowers t ∧
          ∃ (m y : L) (P : Subgroup G), Q y ∧ orderOf (y : G) = 2 ∧
            (m : G)⁻¹ * (g⁻¹ * t * g) * m = (g⁻¹ * t * g) * y ∧
            ⁅P, P⁆ = P ∧ (y : G) ∈ P ∧ P ≤ L ⊓ conjugate L g ∧
            P ≤ centralizer ({g⁻¹ * t * g} : Set G))) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hK ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  obtain ⟨g, hne, hc, hN, -⟩ :=
    F4Pilot.exists_conj_mem_normalizer_not_mem_centralizer hset htC ht hK
  set s := g⁻¹ * t * g with hs
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by
    calc s * s = g⁻¹ * (t * t) * g := by rw [hs]; group
      _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hso : orderOf s = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at h
    rw [hs, h, ht]
  have hsCt : s ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hc
  set α : MulAut L := L.normalizerMonoidHom ⟨s, hN⟩
  have hα : ∀ l : L, ((α l : L) : G) = s * l * s⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hN⟩ l
  refine ⟨g, hne, hc, hN, ?_⟩
  by_cases hin : α ∈ (MulAut.conj : L →* MulAut L).range
  ·
    left
    obtain ⟨l, hl⟩ := hin
    have hmem : s ∈ L ⊔ zpowers t :=
      F4Pilot.mem_sup_zpowers_of_conj_eq htC ht hK hsCt l.2 fun y hy => by
        have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
        rw [h, hα]
    obtain ⟨y, hyL, hy⟩ := F4Pilot.exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hmem
    exact ⟨y, hyL, orderOf_eq_two_of_eq_or_eq_mul ht htC hyL hso hne hy, hy⟩
  ·
    right
    refine ⟨fun hmem => hin (normalizerMonoidHom_mem_range_conj_of_mem_sup ht htC hN hmem), ?_⟩
    have hα2 : α ^ 2 = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [sq, MulAut.mul_apply, MulAut.one_apply, hα, hα]
      calc s * (s * (l : G) * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
        _ = l := by rw [hs2, one_mul, inv_one, mul_one]
    obtain ⟨m, y, hy1, hmy, hQ, P, hP, hyP, hPα⟩ := hfus α hα2 hin
    have hyinv : α y = y⁻¹ := by
      rw [← hmy]
      exact inv_apply_mul_eq_of_sq_eq_one hα2 m
    have hyy : y * y = 1 := by
      have h := hPα y hyP
      rw [hyinv] at h
      calc y * y = y⁻¹ * y := by rw [h]
        _ = 1 := inv_mul_cancel y
    have hyo : orderOf (y : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq, hyy]) hy1
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
    exact ⟨m, y, PG, hQ, hyo, key, hPG, ⟨y, hyP, rfl⟩,
      std_perfect_le_inf_conjugate hset hOut htC ht g hPG hPGt hPGs, hPGs⟩

omit [Finite G] in
theorem mem_conjugate_iff {g x : G} : x ∈ conjugate L g ↔ g * x * g⁻¹ ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have he : g * (g⁻¹ * l * g) * g⁻¹ = l := by group
    rw [he]
    exact hl
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem exists_conj_inner_or_conj_eq_mul (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {Q : L → Prop}
    (hfus : ∀ α : MulAut L, α ^ 2 = 1 → α ∉ (MulAut.conj : L →* MulAut L).range →
      PerfectTwistedFusionIn α Q)
    {t : G} (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    (∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) ∧
        ∃ y ∈ L, orderOf y = 2 ∧ (g⁻¹ * t * g = y ∨ g⁻¹ * t * g = t * y)) ∨
      ∃ c h : G, c⁻¹ * t * c ≠ t ∧ (c⁻¹ * t * c) * t = t * (c⁻¹ * t * c) ∧
        t ∉ conjugate L c ⊔ zpowers (c⁻¹ * t * c) ∧
        ∃ l ∈ L, orderOf l = 2 ∧ h⁻¹ * t * h = t * l ∧ l ∈ conjugate L c ∧
          (∃ hl : c * l * c⁻¹ ∈ L, Q ⟨c * l * c⁻¹, hl⟩) ∧
          ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ l ∈ P ∧ P ≤ L ⊓ conjugate L c ∧
            P ≤ centralizer ({c⁻¹ * t * c} : Set G) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hK ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  obtain ⟨g, hne, hc, -, hcase⟩ := exists_conj_inner_or_twistedFusion hset hOut hfus ht hK
  rcases hcase with ⟨y, hyL, hy, hgy⟩ | ⟨hnot, m, y, P, hQ, hyo, key, hP, hyP, hPL, hPs⟩
  · exact Or.inl ⟨g, hne, hc, y, hyL, hy, hgy⟩
  · right
    set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
    have hφx : ∀ x, φ x = g * x * g⁻¹ := fun x => rfl
    have hct : (g⁻¹)⁻¹ * t * g⁻¹ = g * t * g⁻¹ := by rw [inv_inv]
    have hyLg : (y : G) ∈ conjugate L g := (hPL hyP).2
    have hlL : g * (y : G) * g⁻¹ ∈ L := mem_conjugate_iff.1 hyLg
    have hconjL : ∀ x : G, x ∈ conjugate L g⁻¹ ↔ g⁻¹ * x * g ∈ L := fun x => by
      rw [mem_conjugate_iff, inv_inv]
    refine ⟨g⁻¹, g * m * g⁻¹, ?_, ?_, ?_, g * y * g⁻¹, hlL, ?_, ?_, ?_, ?_, ?_⟩
    ·
      rw [hct]
      intro h
      apply hne
      calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
        _ = t := by group
    ·
      rw [hct]
      calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [hc]
        _ = t * (g * t * g⁻¹) := by group
    ·
      rw [hct]
      intro hmem
      apply hnot
      have hmap : (conjugate L g⁻¹ ⊔ zpowers (g * t * g⁻¹)).comap φ = L ⊔ zpowers t := by
        have h1 : conjugate L g⁻¹ = L.map φ := by
          rw [conjugate, inv_inv]
        have h2 : zpowers (g * t * g⁻¹) = (zpowers t).map φ := by
          rw [MonoidHom.map_zpowers, hφx]
        rw [h1, h2, ← Subgroup.map_sup, comap_map_eq_self_of_injective (MulEquiv.injective _)]
      rw [← hmap, mem_comap, hφx]
      convert hmem using 1
      group
    ·
      have h := MulEquiv.orderOf_eq (MulAut.conj g) (y : G)
      rw [MulAut.conj_apply] at h
      rw [h, hyo]
    ·
      calc (g * m * g⁻¹)⁻¹ * t * (g * m * g⁻¹) = g * ((m : G)⁻¹ * (g⁻¹ * t * g) * m) * g⁻¹ := by
            group
        _ = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by rw [key]
        _ = t * (g * y * g⁻¹) := by group
    ·
      rw [hconjL]
      convert y.2 using 1
      group
    ·
      have hyeq : g⁻¹ * (g * (y : G) * g⁻¹) * g⁻¹⁻¹ = y := by group
      have hl : g⁻¹ * (g * (y : G) * g⁻¹) * g⁻¹⁻¹ ∈ L := by
        rw [hyeq]
        exact y.2
      refine ⟨hl, ?_⟩
      convert hQ using 1
      exact Subtype.ext hyeq
    ·
      refine ⟨P.map φ, ?_, ⟨y, hyP, rfl⟩, ?_, ?_⟩
      · rw [← map_commutator, hP]
      · rintro _ ⟨p, hp, rfl⟩
        have hpL : p ∈ L := (hPL hp).1
        have hpg : p ∈ conjugate L g := (hPL hp).2
        refine mem_inf.2 ⟨?_, ?_⟩
        · rw [hφx]
          exact mem_conjugate_iff.1 hpg
        · rw [hconjL, hφx]
          have he : g⁻¹ * (g * p * g⁻¹) * g = p := by group
          rw [he]
          exact hpL
      · rintro _ ⟨p, hp, rfl⟩
        have hpL : p ∈ L := (hPL hp).1
        have h : p * t = t * p := mem_centralizer_iff.1 htC p hpL
        rw [hct, mem_centralizer_singleton_iff, hφx]
        calc g * p * g⁻¹ * (g * t * g⁻¹) = g * (p * t) * g⁻¹ := by group
          _ = g * (t * p) * g⁻¹ := by rw [h]
          _ = g * t * g⁻¹ * (g * p * g⁻¹) := by group

end Standard

end CFSG.SeitzReduction.LinearPilot
