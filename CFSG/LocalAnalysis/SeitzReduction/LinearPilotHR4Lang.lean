module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR4Basic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms

section Lang

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def IsLangSurjective (α : MulAut X) : Prop :=
  ∀ z : X, α z = z⁻¹ → ∃ x : X, (α x)⁻¹ * x = z

theorem IsLangSurjective.of_mulEquiv (e : X ≃* Y) {α : MulAut X} {β : MulAut Y}
    (h : ∀ x, e (α x) = β (e x)) (hβ : IsLangSurjective β) : IsLangSurjective α := by
  intro z hz
  have hz' : β (e z) = (e z)⁻¹ := by rw [← h, hz, map_inv]
  obtain ⟨x, hx⟩ := hβ (e z) hz'
  refine ⟨e.symm x, e.injective ?_⟩
  rw [map_mul, map_inv, h, MulEquiv.apply_symm_apply, hx]

theorem IsLangSurjective.of_conj {α β ψ : MulAut X} (h : ψ * α * ψ⁻¹ = β)
    (hβ : IsLangSurjective β) : IsLangSurjective α :=
  IsLangSurjective.of_mulEquiv ψ (fun x => by
    rw [← h, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply])
    hβ

end Lang

section Standard

variable {G : Type} [Group G] {L : Subgroup G}

theorem exists_conj_eq_mul_of_isLangSurjective {t g : G} (ht2 : t * t = 1)
    (htC : t ∈ centralizer (L : Set G)) (hN : g⁻¹ * t * g ∈ normalizer (L : Set G))
    (hLang : IsLangSurjective (L.normalizerMonoidHom ⟨g⁻¹ * t * g, hN⟩)) {l : G} (hlL : l ∈ L)
    (hlg : l ∈ conjugate L g⁻¹) (hl2 : l * l = 1) : ∃ h : G, h⁻¹ * t * h = t * l := by
  set s := g⁻¹ * t * g with hs
  set α : MulAut L := L.normalizerMonoidHom ⟨s, hN⟩
  have hα : ∀ x : L, ((α x : L) : G) = s * x * s⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hN⟩ x
  have hs2 : s * s = 1 := by
    calc s * s = g⁻¹ * (t * t) * g := by rw [hs]; group
      _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hyL : g⁻¹ * l * g ∈ L := by
    have h := mem_conjugate_iff.1 hlg
    rwa [inv_inv] at h
  set y : L := ⟨g⁻¹ * l * g, hyL⟩ with hydef
  have htl : t * l = l * t := (mem_centralizer_iff.1 htC l hlL).symm
  have hαy : α y = y := by
    apply Subtype.ext
    rw [hα, hydef, hs]
    calc g⁻¹ * t * g * (g⁻¹ * l * g) * (g⁻¹ * t * g)⁻¹ = g⁻¹ * (t * l) * t⁻¹ * g := by group
      _ = g⁻¹ * l * g := by rw [htl]; group
  have hyy : y * y = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hydef, Subgroup.coe_one]
    calc g⁻¹ * l * g * (g⁻¹ * l * g) = g⁻¹ * (l * l) * g := by group
      _ = 1 := by rw [hl2, mul_one, inv_mul_cancel]
  have hyinv : α y = y⁻¹ := by rw [hαy, inv_eq_of_mul_eq_one_right hyy]
  obtain ⟨x, hx⟩ := hLang y hyinv
  have hx' : ((α x : L) : G)⁻¹ * x = y := by
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, hx]
  rw [hα, hsinv] at hx'
  have key : (x : G)⁻¹ * s * x = s * y := by
    rw [← hx']
    calc (x : G)⁻¹ * s * x = (x : G)⁻¹ * s⁻¹ * x := by rw [hsinv]
      _ = s * ((s * x * s)⁻¹ * x) := by group
  refine ⟨g * x * g⁻¹, ?_⟩
  calc (g * x * g⁻¹)⁻¹ * t * (g * x * g⁻¹) = g * ((x : G)⁻¹ * s * x) * g⁻¹ := by
        rw [hs]; group
    _ = g * (s * (g⁻¹ * l * g)) * g⁻¹ := by rw [key]
    _ = t * l := by rw [hs]; group

theorem exists_conj_eq_mul_of_isLangSurjective_of_perfect [Finite G] (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t g : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) (hN : g⁻¹ * t * g ∈ normalizer (L : Set G))
    (hLang : IsLangSurjective (L.normalizerMonoidHom ⟨g⁻¹ * t * g, hN⟩)) {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) (hPL : P ≤ L) (hPt' : P ≤ centralizer ({g * t * g⁻¹} : Set G)) {l : G}
    (hlP : l ∈ P) (hl2 : l * l = 1) : ∃ h : G, h⁻¹ * t * h = t * l := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hPt : P ≤ centralizer ({t} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC p (hPL hp))
  have hPt'' : P ≤ centralizer ({(g⁻¹)⁻¹ * t * g⁻¹} : Set G) := by
    rwa [inv_inv]
  have hPLg := std_perfect_le_inf_conjugate hset hOut htC ht g⁻¹ hP hPt hPt''
  exact exists_conj_eq_mul_of_isLangSurjective ht2 htC hN hLang (hPL hlP) (hPLg hlP).2 hl2

omit [Group G] in
theorem mul_self_eq_one_of_twisted {X : Type*} [Group X] {α : MulAut X} (hα : α ^ 2 = 1)
    {m y : X} (hmy : (α m)⁻¹ * m = y) (hy : α y = y) : y * y = 1 := by
  have hyinv : α y = y⁻¹ := by
    rw [← hmy]
    exact inv_apply_mul_eq_of_sq_eq_one hα m
  calc y * y = y⁻¹ * y := by rw [← hyinv, hy]
    _ = 1 := inv_mul_cancel y

theorem exists_conj_inner_or_eq_mul_of_isLangSurjective [Finite G] (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {Q : L → Prop}
    (hfus : ∀ α : MulAut L, α ^ 2 = 1 → α ∉ (MulAut.conj : L →* MulAut L).range →
      PerfectTwistedFusionIn α Q)
    {t g : G} (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hne : g⁻¹ * t * g ≠ t) (hc : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g))
    (hN : g⁻¹ * t * g ∈ normalizer (L : Set G))
    (hLang : IsLangSurjective (L.normalizerMonoidHom ⟨g⁻¹ * t * g, hN⟩)) :
    (g * t * g⁻¹ ≠ t ∧ (g * t * g⁻¹) * t = t * (g * t * g⁻¹) ∧
        ∃ y ∈ L, orderOf y = 2 ∧ (g * t * g⁻¹ = y ∨ g * t * g⁻¹ = t * y)) ∨
      ∃ (h : G) (y : L), Q y ∧ orderOf (y : G) = 2 ∧ h⁻¹ * t * h = t * y := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hK ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set t' := g * t * g⁻¹ with ht'
  have hne' : t' ≠ t := by
    intro h
    apply hne
    calc g⁻¹ * t * g = g⁻¹ * t' * g := by rw [h]
      _ = t := by rw [ht']; group
  have hc' : t' * t = t * t' := by
    calc t' * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by rw [ht']; group
      _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [hc]
      _ = t * t' := by rw [ht']; group
  have ht'o : orderOf t' = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) t
    rw [MulAut.conj_apply] at h
    rw [ht', h, ht]
  have ht'Ct : t' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hc'
  have hN' : t' ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht ht'Ct
  set α' : MulAut L := L.normalizerMonoidHom ⟨t', hN'⟩
  have hα' : ∀ l : L, ((α' l : L) : G) = t' * l * t'⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t', hN'⟩ l
  have ht'2 : t' * t' = 1 := by rw [← sq, ← ht'o, pow_orderOf_eq_one]
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  by_cases hin : α' ∈ (MulAut.conj : L →* MulAut L).range
  ·
    left
    obtain ⟨l, hl⟩ := hin
    have hmem : t' ∈ L ⊔ zpowers t :=
      F4Pilot.mem_sup_zpowers_of_conj_eq htC ht hK ht'Ct l.2 fun y hy => by
        have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
        rw [h, hα']
    obtain ⟨y, hyL, hy⟩ := F4Pilot.exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hmem
    exact ⟨hne', hc', y, hyL, orderOf_eq_two_of_eq_or_eq_mul ht htC hyL ht'o hne' hy, hy⟩
  ·
    right
    have hα'2 : α' ^ 2 = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [sq, MulAut.mul_apply, MulAut.one_apply, hα', hα']
      calc t' * (t' * (l : G) * t'⁻¹) * t'⁻¹ = (t' * t') * l * (t' * t')⁻¹ := by group
        _ = l := by rw [ht'2, one_mul, inv_one, mul_one]
    obtain ⟨m, y, hy1, hmy, hQ, P, hP, hyP, hPα⟩ := hfus α' hα'2 hin
    have hyy : y * y = 1 := mul_self_eq_one_of_twisted hα'2 hmy (hPα y hyP)
    have hyo : orderOf (y : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq, hyy]) hy1
    set PG := P.map L.subtype with hPGdef
    have hPG : ⁅PG, PG⁆ = PG := by rw [hPGdef, ← map_commutator, hP]
    have hPGL : PG ≤ L := map_subtype_le P
    have hPGt' : PG ≤ centralizer ({t'} : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      have h := congrArg Subtype.val (hPα p hp)
      rw [hα'] at h
      rw [mem_centralizer_singleton_iff]
      calc (p : G) * t' = (t' * p * t'⁻¹) * t' := by rw [h]
        _ = t' * p := by group
    have hyy' : (y : G) * y = 1 := by rw [← Subgroup.coe_mul, hyy, Subgroup.coe_one]
    obtain ⟨h, hh⟩ := exists_conj_eq_mul_of_isLangSurjective_of_perfect hset hOut ht htC hN hLang
      hPG hPGL hPGt' ⟨y, hyP, rfl⟩ hyy'
    exact ⟨h, y, hQ, hyo, hh⟩

end Standard

end CFSG.SeitzReduction.LinearPilot
