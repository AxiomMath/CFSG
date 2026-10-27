module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatBase
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5A

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_injective_pSimple {X L : Subgroup G} (hL : GLAPComponent 3 X L) :
    Function.Injective (MulAut.conj : PSimple 3 L →* MulAut (PSimple 3 L)) := by
  haveI : Group.IsPerfect (PQuot 3 L) := ⟨(isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL).1⟩
  have hZ : Subgroup.center (PSimple 3 L) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (PQuot 3 L)
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (PSimple 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun φ : MulAut (PSimple 3 L) => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc

theorem exists_rho {X L A : Subgroup G} (hL : GLAPComponent 3 X L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hinn : ∀ a ∈ A, InducesInnerMod 3 L a) :
    ∃ ρ : ↥A →* PSimple 3 L, ∀ a : ↥A, chevAut 3 L ⟨a, hAN a.2⟩ = MulAut.conj (ρ a) := by
  have hκ := conj_injective_pSimple hL
  let ψ : A →* MulAut (PSimple 3 L) := (chevAut 3 L).comp (Subgroup.inclusion hAN)
  have hψ : ∀ a : A, ψ a ∈ (MulAut.conj : PSimple 3 L →* MulAut (PSimple 3 L)).range := by
    intro a
    have h1 := (inducesInnerMod_iff_barAut_mem_inner (p := 3) (hAN a.2)).1 (hinn a a.2)
    exact CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_inner_le h1
  let ρ : A →* PSimple 3 L :=
    (MonoidHom.ofInjective hκ).symm.toMonoidHom.comp (ψ.codRestrict _ hψ)
  refine ⟨ρ, fun a => ?_⟩
  have h2 : (MonoidHom.ofInjective hκ) (ρ a) = ψ.codRestrict _ hψ a := by
    show (MonoidHom.ofInjective hκ) ((MonoidHom.ofInjective hκ).symm (ψ.codRestrict _ hψ a)) = _
    exact (MonoidHom.ofInjective hκ).apply_symm_apply _
  exact congrArg Subtype.val h2.symm

theorem rho_eq_one_iff {X L A : Subgroup G} (hL : GLAPComponent 3 X L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {ρ : ↥A →* PSimple 3 L}
    (hρ : ∀ a : ↥A, chevAut 3 L ⟨a, hAN a.2⟩ = MulAut.conj (ρ a)) (a : ↥A) :
    ρ a = 1 ↔ (a : G) ∈ centModSubgroup 3 L := by
  have hκ := conj_injective_pSimple hL
  rw [← centMod_iff, ← chevAut_eq_one_iff Nat.prime_three hL (hAN a.2), hρ a]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    exact hκ (h.trans (map_one _).symm)

theorem B_inf_centMod {B : Subgroup G} {x : G} {L : Subgroup G} (hBe : IsElemAbelian 3 B)
    (hxB : x ∈ B) (hx1 : x ≠ 1) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hcyc : CycModSylow 3 L) : B ⊓ centModSubgroup 3 L = Subgroup.zpowers x := by
  have hx3 : x ^ 3 = 1 := hBe.2 x hxB
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxY : Subgroup.zpowers x ≤ B ⊓ centModSubgroup 3 L :=
    Subgroup.zpowers_le.2 ⟨hxB, mem_centMod_of_mem_centralizer hxL⟩
  refine le_antisymm ?_ hxY
  set Y := B ⊓ centModSubgroup 3 L with hY
  have hYp : IsPGroup 3 ↥Y := (isPGroup_of_isElemAbelian hBe).to_le inf_le_left
  have hYc : IsCyclic ↥Y := hcyc Y (fun g hg => centMod_iff.2 hg.2) hYp
  have hcard : Nat.card ↥Y ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => Subtype.ext (hBe.2 g (g.2.1)))
  have hle : Nat.card ↥Y ≤ Nat.card ↥(Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, hxo]
    exact Nat.le_of_dvd (by norm_num) hcard
  exact (Subgroup.eq_of_le_of_card_ge hxY hle).ge

theorem exists_noncyclic_pSubgroup_of_surjective {p : ℕ} [Fact p.Prime] {M S : Type*} [Group M]
    [Finite M] [Group S] (f : M →* S) (hf : Function.Surjective f) {E : Subgroup S}
    (hE : IsPGroup p ↥E) (hnc : ¬ IsCyclic ↥E) :
    ∃ Q : Subgroup M, IsPGroup p ↥Q ∧ ¬ IsCyclic ↥Q := by
  let H : Subgroup M := E.comap f
  let g : ↥H →* ↥E := f.subgroupComap E
  have hg : Function.Surjective g := by
    intro e
    obtain ⟨m, hm⟩ := hf e
    exact ⟨⟨m, by simp [H, Subgroup.mem_comap, hm]⟩, Subtype.ext hm⟩
  obtain ⟨P⟩ : Nonempty (Sylow p ↥H) := inferInstance
  refine ⟨(P : Subgroup ↥H).map H.subtype, P.isPGroup'.map _, fun hcyc => hnc ?_⟩
  have hP : IsCyclic ↥(P : Subgroup ↥H) :=
    (Subgroup.equivMapOfInjective (P : Subgroup ↥H) H.subtype H.subtype_injective).isCyclic.2 hcyc
  have htop : IsPGroup p (⊤ : Subgroup ↥E) := hE.of_equiv Subgroup.topEquiv.symm
  have hQ : (P.mapSurjective hg : Subgroup ↥E) = ⊤ := ((P.mapSurjective hg).3 htop le_top).symm
  rw [Sylow.coe_mapSurjective] at hQ
  have hsurj : Function.Surjective (g.comp (P : Subgroup ↥H).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hQ
  exact isCyclic_of_surjective _ hsurj

theorem not_isCyclic_of_exponent {p : ℕ} (hp : p.Prime) {S : Type*} [Group S] {E : Subgroup S}
    (hE : ∀ e ∈ E, e ^ p = 1) (hcard : p < Nat.card ↥E) : ¬ IsCyclic ↥E := by
  intro hc
  have h : Nat.card ↥E ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => Subtype.ext (hE g g.2))
  exact absurd (Nat.le_of_dvd hp.pos h) (not_le.2 hcard)

theorem exists_act {B : Subgroup G} {x : G} {L : Subgroup G} (hS : IsSStarMax 3 B x L)
    (hinn : ∀ b ∈ B, InducesInnerMod 3 L b) :
    ∃ ρ : ↥B →* PSimple 3 L,
      (∀ b : ↥B, chevAut 3 L ⟨b, (IsSStarMax.normalizes hS) b.2⟩ = MulAut.conj (ρ b)) ∧
      (∀ b : ↥B, ρ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x) ∧ 3 * Nat.card ρ.range = Nat.card ↥B ∧
      IsElemAbelian 3 ρ.range := by
  have hBm := (IsSStarMax.bmax hS)
  have hBe : IsElemAbelian 3 B := hBm.1
  obtain ⟨hxB, hx1, -⟩ := (IsSStarMax.essential hS)
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := IsSTriple.mem_centralizer
    ⟨hBm, (IsSStarMax.essential hS), (IsSStarMax.component hS)⟩
  obtain ⟨ρ, hρ⟩ := exists_rho (IsSStarMax.component hS) (IsSStarMax.normalizes hS) hinn
  have hcent := B_inf_centMod hBe hxB hx1 hxL (IsSStarMax.cycMod hS)
  have hker : ∀ b : ↥B, ρ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
    intro b
    rw [rho_eq_one_iff (IsSStarMax.component hS) (IsSStarMax.normalizes hS) hρ b, ← hcent]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hxo : orderOf x = 3 := orderOf_eq_prime (hBe.2 x hxB) hx1
  have hkerEq : ρ.ker = (Subgroup.zpowers x).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker b
  have hcard : 3 * Nat.card ρ.range = Nat.card ↥B := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hxB)).toEquiv,
      Nat.card_zpowers, hxo] at h1
    exact h1
  refine ⟨ρ, hρ, hker, hcard, ?_⟩
  haveI := hBe.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨a', ha'⟩ := ρ.mem_range.1 a.2
    obtain ⟨b', hb'⟩ := ρ.mem_range.1 b.2
    apply Subtype.ext
    show (a : PSimple 3 L) * (b : PSimple 3 L) = (b : PSimple 3 L) * (a : PSimple 3 L)
    rw [← ha', ← hb', ← map_mul, ← map_mul, mul_comm' a' b']
  · obtain ⟨a', ha'⟩ := ρ.mem_range.1 ha
    have ha3 : a' ^ 3 = 1 := Subtype.ext (by simpa using hBe.2 (a' : G) a'.2)
    rw [← ha', ← map_pow, ha3, map_one]

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
