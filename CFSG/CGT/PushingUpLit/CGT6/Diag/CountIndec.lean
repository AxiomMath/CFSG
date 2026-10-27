module

public import CFSG.CGT.PushingUpLit.CGT6.EmbConjMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

namespace Diag.Count

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

section Natural

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)} {n : ℕ}

theorem card_commV (hn : 1 ≤ n)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) :
    Nat.card ↥(commV Y) = Nat.card ↥(commV Y ⊓ fixV Y) * 2 ^ (2 * n) := by
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hnat
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rw [hβk, card_sl_model hn] at h1
  have h2 : Nat.card ↥((commV Y ⊓ fixV Y).subgroupOf (commV Y)) =
      Nat.card ↥(commV Y ⊓ fixV Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem not_commV_le_fixV [Finite V] (hn : 1 ≤ n)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) : ¬ commV Y ≤ fixV Y := by
  intro h
  have h1 := card_commV hn hnat
  rw [inf_eq_left.mpr h] at h1
  have hpos : 0 < Nat.card ↥(commV Y) := Nat.card_pos
  have h2 : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
  nlinarith

theorem eq_commV_of_not_le [Finite V] (hperf : ⁅Y, Y⁆ = Y)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) {A : Subgroup V}
    (hAU : A ≤ commV Y) (hA : ∀ g ∈ Y, ∀ a ∈ A, g a ∈ A) (hnle : ¬ A ≤ commV Y ⊓ fixV Y) :
    A = commV Y := by
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  obtain ⟨a₀, ha₀A, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hv₀ : Multiplicative.toAdd (β ⟨a₀, hAU ha₀A⟩) ≠ 0 := by
    intro h0
    apply ha₀C
    have h1 : β ⟨a₀, hAU ha₀A⟩ = 1 := by
      rw [← ofAdd_toAdd (β _), h0, ofAdd_zero]
    have h2 : (⟨a₀, hAU ha₀A⟩ : ↥(commV Y)) ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hcover : ∀ v : Fin 2 → Fq n,
      ∃ p : ↥(commV Y), (p : V) ∈ A ∧ β p = Multiplicative.ofAdd v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨1, A.one_mem, by rw [map_one, hv, ofAdd_zero]⟩
    · obtain ⟨g, hg⟩ := Glue.exists_sl2_mulVec_eq_of_ne_zero hv₀ hv
      have hxU : ((θ.symm g : ↥Y) : MulAut V) a₀ ∈ commV Y :=
        hinv _ (θ.symm g).2 a₀ (hAU ha₀A)
      refine ⟨⟨((θ.symm g : ↥Y) : MulAut V) a₀, hxU⟩, hA _ (θ.symm g).2 a₀ ha₀A, ?_⟩
      refine (hβe (θ.symm g) ⟨a₀, hAU ha₀A⟩ hxU).trans ?_
      rw [MulEquiv.apply_symm_apply]
      exact congrArg Multiplicative.ofAdd hg
  refine le_antisymm hAU ((USelf_of_perfect hperf) A (fun g hg u hu => ?_))
  obtain ⟨p, hpA, hpβ⟩ := hcover (Multiplicative.toAdd (β ⟨u, hu⟩))
  rw [ofAdd_toAdd] at hpβ
  have hker : p⁻¹ * ⟨u, hu⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpβ, inv_mul_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at hker
  have hc : (p : V)⁻¹ * u ∈ commV Y ⊓ fixV Y := hker
  have hgc : g ((p : V)⁻¹ * u) = (p : V)⁻¹ * u := (mem_fixV.mp hc.2) g hg
  have h2 : g u = g (p : V) * ((p : V)⁻¹ * u) := by
    calc g u = g ((p : V) * ((p : V)⁻¹ * u)) := by rw [mul_inv_cancel_left]
      _ = g (p : V) * g ((p : V)⁻¹ * u) := map_mul g _ _
      _ = g (p : V) * ((p : V)⁻¹ * u) := by rw [hgc]
  rw [h2]
  have h3 : g (p : V) * ((p : V)⁻¹ * u) * u⁻¹ = g (p : V) * (p : V)⁻¹ := by group
  rw [h3]
  exact mul_mem (hA g hg p hpA) (inv_mem hpA)

end Natural

section Induced

variable {V : Type} [CommGroup V] [Finite V] {Y : Subgroup (MulAut V)} {n : ℕ}

theorem invariant_cases (hperf : ⁅Y, Y⁆ = Y)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) (A : Subgroup ↥(commV Y))
    (hA : GInv (resHom Y).range A) :
    A = ⊤ ∨ A ≤ (commV Y ⊓ fixV Y).subgroupOf (commV Y) := by
  by_cases hle : A ≤ (commV Y ⊓ fixV Y).subgroupOf (commV Y)
  · exact Or.inr hle
  · left
    have h1 : ¬ A.map (commV Y).subtype ≤ commV Y ⊓ fixV Y := fun h =>
      hle (Subgroup.map_le_iff_le_comap.mp h)
    have h2 := eq_commV_of_not_le hperf hnat (A := A.map (commV Y).subtype)
      (by rintro _ ⟨a, -, rfl⟩; exact a.2)
      (by
        rintro g hg _ ⟨a, ha, rfl⟩
        exact ⟨resHom Y ⟨g, hg⟩ a, hA _ ⟨⟨g, hg⟩, rfl⟩ a ha, rfl⟩) h1
    rw [eq_top_iff]
    intro u _
    have h3 : (u : V) ∈ A.map (commV Y).subtype := by rw [h2]; exact u.2
    obtain ⟨a, ha, hau⟩ := h3
    have h4 : a = u := Subtype.ext hau
    exact h4 ▸ ha

theorem indecomposable (hn : 1 ≤ n) (hperf : ⁅Y, Y⁆ = Y)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) :
    ∀ A B : Subgroup ↥(commV Y), GInv (resHom Y).range A → GInv (resHom Y).range B →
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥ := by
  intro A B hA hB hinf hsup
  rcases invariant_cases hperf hnat A hA with hA1 | hA1
  · right
    rw [hA1, top_inf_eq] at hinf
    exact hinf
  rcases invariant_cases hperf hnat B hB with hB1 | hB1
  · left
    rw [hB1, inf_top_eq] at hinf
    exact hinf
  exfalso
  have hle : commV Y ≤ fixV Y := by
    intro u hu
    have h1 : (⟨u, hu⟩ : ↥(commV Y)) ∈ A ⊔ B := hsup ▸ Subgroup.mem_top _
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp h1
    have h2 : (⟨u, hu⟩ : ↥(commV Y)) ∈ (commV Y ⊓ fixV Y).subgroupOf (commV Y) := by
      rw [← hab]
      exact mul_mem (hA1 ha) (hB1 hb)
    exact (Subgroup.mem_subgroupOf.mp h2).2
  exact not_commV_le_fixV hn hnat hle

omit [Finite V] in
theorem injective_resHom_of_nat
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) :
    Function.Injective (resHom Y) := by
  obtain ⟨-, θ, β, hβs, -, hβe⟩ := hnat
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfixU : ∀ u : ↥(commV Y), (g : MulAut V) (u : V) = u := fun u =>
    congrArg (fun x : MulAut ↥(commV Y) => ((x u : ↥(commV Y)) : V)) hg
  have hθ : θ g = 1 := by
    apply sl2_eq_one_of_mulVec_fix
    intro w
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have h1 := hβe g u (apply_mem_commV_self Y g.2 u.2)
    have h2 : (⟨(g : MulAut V) (u : V), apply_mem_commV_self Y g.2 u.2⟩ : ↥(commV Y)) = u :=
      Subtype.ext (hfixU u)
    rw [h2, hu] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simpa [slAct] using h3.symm
  exact θ.injective (hθ.trans (map_one θ).symm)

omit [Finite V] in
theorem commV_range_resHom (hperf : ⁅Y, Y⁆ = Y) : commV (resHom Y).range = ⊤ := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  rw [eq_top_iff]
  intro u _
  obtain ⟨p, hp, hpu⟩ := commV_le_of_perfect Y ((commV (resHom Y).range).map (commV Y).subtype)
    (fun g w => ⟨resHom Y g w * w⁻¹,
      Subgroup.subset_closure ⟨resHom Y g, ⟨g, rfl⟩, w, rfl⟩, rfl⟩) u.2
  have h1 : p = u := Subtype.ext hpu
  rwa [← h1]

omit [Finite V] in
theorem natSection_restrict (hperf : ⁅Y, Y⁆ = Y)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) :
    IsNatSectionBy (slAct n) (resHom Y).range (commV (resHom Y).range)
      (commV (resHom Y).range ⊓ fixV (resHom Y).range) := by
  have hinj := injective_resHom_of_nat hnat
  have htop := commV_range_resHom hperf
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  let θ' : ↥(resHom Y).range ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
    (MonoidHom.ofInjective hinj).symm.trans θ
  have hθ' : ∀ g : ↥Y, θ' ⟨resHom Y g, g, rfl⟩ = θ g := fun g => by
    have : (MonoidHom.ofInjective hinj).symm ⟨resHom Y g, g, rfl⟩ = g :=
      (MonoidHom.ofInjective hinj).symm_apply_eq.mpr rfl
    simp [θ', this]
  let e : ↥(commV (resHom Y).range) →* ↥(commV Y) := (commV (resHom Y).range).subtype
  have he : Function.Surjective e := fun u => ⟨⟨u, htop ▸ Subgroup.mem_top u⟩, rfl⟩
  refine ⟨fun x hx p hp => commV_invariant hx hp, θ', β.comp e, hβs.comp he, ?_, ?_⟩
  · ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : e p ∈ β.ker := h
      rw [hβk, Subgroup.mem_subgroupOf] at h1
      refine ⟨p.2, fun x hx => ?_⟩
      obtain ⟨g, rfl⟩ := hx
      exact Subtype.ext (h1.2 g g.2)
    · rintro ⟨-, hp⟩
      have h1 : e p ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        refine ⟨(p : ↥(commV Y)).2, fun g hg => ?_⟩
        exact congrArg Subtype.val (hp (resHom Y ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩)
      exact h1
  · rintro ⟨x, g, rfl⟩ p hp
    have h1 := hβe g (e p) (apply_mem_commV_self Y g.2 (e p).2)
    rw [hθ' g]
    exact h1

theorem card_fix_le (hn : 2 ≤ n) (hV : ∀ v : V, v ^ 2 = 1) (hperf : ⁅Y, Y⁆ = Y)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) :
    Nat.card ↥(commV Y ⊓ fixV Y) ≤ 2 ^ n := by
  have hsec := natSection_restrict hperf hnat
  have hind := indecomposable (by omega) hperf hnat
  have hVU : ∀ u : ↥(commV Y), u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV (u : V))
  have h2 := (h1NaturalSL2_holds n hn ↥(commV Y) hVU (resHom Y).range hind hsec).2
  have htop := commV_range_resHom hperf
  have hmap : (commV (resHom Y).range ⊓ fixV (resHom Y).range).map (commV Y).subtype =
      commV Y ⊓ fixV Y := by
    ext x
    constructor
    · rintro ⟨s, ⟨-, hs2⟩, rfl⟩
      refine ⟨s.2, fun g hg => ?_⟩
      exact congrArg Subtype.val (hs2 (resHom Y ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩)
    · rintro ⟨hx1, hx2⟩
      refine ⟨⟨x, hx1⟩, ⟨htop ▸ Subgroup.mem_top _, ?_⟩, rfl⟩
      rintro _ ⟨g, rfl⟩
      exact Subtype.ext (hx2 g g.2)
  have hcard : Nat.card ↥(commV Y ⊓ fixV Y) =
      Nat.card ↥(commV (resHom Y).range ⊓ fixV (resHom Y).range) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (commV Y).subtype_injective
  rwa [hcard]

theorem card_commV_le (hn : 2 ≤ n) (hV : ∀ v : V, v ^ 2 = 1) (hperf : ⁅Y, Y⁆ = Y)
    (hnat : IsNatSectionBy (slAct n) Y (commV Y) (commV Y ⊓ fixV Y)) :
    Nat.card ↥(commV Y) ≤ 2 ^ (3 * n) := by
  rw [card_commV (by omega) hnat]
  calc Nat.card ↥(commV Y ⊓ fixV Y) * 2 ^ (2 * n) ≤ 2 ^ n * 2 ^ (2 * n) :=
        Nat.mul_le_mul_right _ (card_fix_le hn hV hperf hnat)
    _ = 2 ^ (3 * n) := by rw [← pow_add]; ring_nf

end Induced

end Diag.Count

end CFSG.CGT.PushingUpLit.CGT6
