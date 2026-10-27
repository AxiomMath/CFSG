module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.EvenSporadicStandard

open Subgroup
open scoped Pointwise

section Commuting

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_le_centralizer {A B : Subgroup G}
    (hAB : B ≤ centralizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (hAB hb) a ha
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        rw [mul_assoc, ← mul_assoc b, ← hcomm a' ha' b hb]
        group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [mul_one]⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by rw [mul_one]⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩)
  exact hle hx

noncomputable def mulEquivProdSup {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    (hd : Disjoint A B) : A × B ≃* (A ⊔ B : Subgroup G) :=
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    mem_centralizer_iff.1 (hAB b.2) a a.2
  have hinj : Function.Injective (A.subtype.noncommCoprod B.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨A.subtype_injective, B.subtype_injective, by simpa only [range_subtype] using hd⟩
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]))

theorem map_center_eq_inf_centralizer (L : Subgroup G) :
    (center L).map L.subtype = L ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.2, mem_centralizer_iff.2 fun l hl =>
      congrArg Subtype.val (mem_center_iff.1 hz ⟨l, hl⟩)⟩
  · rintro x ⟨hxL, hxC⟩
    exact ⟨⟨x, hxL⟩, mem_center_iff.2 fun l =>
      Subtype.ext (mem_centralizer_iff.1 hxC l l.2), rfl⟩

theorem mem_sup_centralizer_iff {L : Subgroup G} {g : G} :
    g ∈ L ⊔ centralizer (L : Set G) ↔ ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹ := by
  constructor
  · intro hg
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hg
    refine ⟨l, hl, fun x hx => ?_⟩
    have hcx : c * x = x * c := (mem_centralizer_iff.1 hc x hx).symm
    calc l * c * x * (l * c)⁻¹ = l * (c * x) * c⁻¹ * l⁻¹ := by group
      _ = l * x * l⁻¹ := by rw [hcx]; group
  · rintro ⟨l, hl, hx⟩
    have hc : l⁻¹ * g ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx'
      calc x * (l⁻¹ * g) = l⁻¹ * (l * x * l⁻¹) * g := by group
        _ = l⁻¹ * (g * x * g⁻¹) * g := by rw [hx x hx']
        _ = l⁻¹ * g * x := by group
    have hg' : g = l * (l⁻¹ * g) := by group
    rw [hg']
    exact mul_mem_sup hl hc

theorem centralizer_singleton_inf_sup_centralizer {L : Subgroup G} {t : G}
    (ht : t ∈ centralizer (L : Set G)) :
    centralizer ({t} : Set G) ⊓ (L ⊔ centralizer (L : Set G)) =
      L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  have hLM : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  refine le_antisymm (fun g ⟨hg, hgs⟩ => ?_)
    (le_inf (sup_le hLM inf_le_right) (sup_le_sup_left inf_le_left L))
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hgs
  have hcM : c ∈ centralizer ({t} : Set G) := by
    have := (centralizer ({t} : Set G)).mul_mem (inv_mem (hLM hl)) hg
    rwa [inv_mul_cancel_left] at this
  exact mul_mem_sup hl ⟨hc, hcM⟩

theorem centralizer_singleton_eq_sup_inf {L : Subgroup G} {t : G}
    (ht : t ∈ centralizer (L : Set G))
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    centralizer ({t} : Set G) = L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  rw [← centralizer_singleton_inf_sup_centralizer ht, inf_eq_left.2 hinn]

theorem disjoint_of_le_centralizer_of_center_eq_bot {L R : Subgroup G}
    (hR : R ≤ centralizer (L : Set G)) (hZ : center L = ⊥) : Disjoint L R := by
  have h1 : L ⊓ centralizer (L : Set G) = ⊥ := by
    rw [← map_center_eq_inf_centralizer, hZ, Subgroup.map_bot]
  exact disjoint_iff.2 (eq_bot_iff.2 ((inf_le_inf_left L hR).trans h1.le))

theorem normalizerMonoidHom_eq_conj_iff {L : Subgroup G} {g : G}
    (hg : g ∈ normalizer (L : Set G)) (l : L) :
    L.normalizerMonoidHom ⟨g, hg⟩ = MulAut.conj l ↔
      ∀ x ∈ L, g * x * g⁻¹ = (l : G) * x * (l : G)⁻¹ := by
  constructor
  · intro h x hx
    exact congrArg (fun α : MulAut L => ((α ⟨x, hx⟩ : L) : G)) h
  · intro h
    exact MulEquiv.ext fun x => Subtype.ext (h x x.2)

theorem normalizer_le_sup_centralizer_of_mulAut_inner {L : Subgroup G}
    (hinner : ∀ α : MulAut L, ∃ l : L, α = MulAut.conj l) :
    normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) := by
  intro g hg
  obtain ⟨l, hl⟩ := hinner (L.normalizerMonoidHom ⟨g, hg⟩)
  exact mem_sup_centralizer_iff.2 ⟨l, l.2, (normalizerMonoidHom_eq_conj_iff hg l).1 hl⟩

theorem normal_range_conj (Y : Type*) [Group Y] : ((MulAut.conj : Y →* MulAut Y).range).Normal := by
  constructor
  rintro _ ⟨y, rfl⟩ β
  refine ⟨β y, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem mulAut_inner_of_inner_centerQuotient {L : Type*} [Group L] (hL : commutator L = ⊤)
    (hinner : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) (α : MulAut L) :
    ∃ l : L, α = MulAut.conj l := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL
  obtain ⟨q, hq⟩ :=
    hinner (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L α)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective L
    (hq.trans (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj l).symm)⟩

theorem normalizer_le_sup_centralizer_of_inner {L : Subgroup G} (hL : commutator L = ⊤)
    (hinner : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) :
    normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) :=
  normalizer_le_sup_centralizer_of_mulAut_inner (mulAut_inner_of_inner_centerQuotient hL hinner)

noncomputable def normalizerAction (L : Subgroup G) :
    normalizer (L : Set G) →* MulAut (L ⧸ center L) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L).comp
    L.normalizerMonoidHom

theorem normalizerAction_apply {L : Subgroup G} (g : normalizer (L : Set G)) (x l : L)
    (h : (l : G) = (g : G) * x * (g : G)⁻¹) :
    normalizerAction L g (x : L ⧸ center L) = (l : L ⧸ center L) := by
  have hl : L.normalizerMonoidHom g x = l := Subtype.ext h.symm
  exact (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
    (L.normalizerMonoidHom g) x).trans (by rw [hl]; rfl)

theorem normalizerAction_eq_one_iff {L : Subgroup G} (hL : commutator L = ⊤)
    (g : normalizer (L : Set G)) :
    normalizerAction L g = 1 ↔ (g : G) ∈ centralizer (L : Set G) := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL
  have h1 : normalizerAction L g = 1 ↔ L.normalizerMonoidHom g = 1 := by
    rw [← (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective L).eq_iff,
      map_one]
    rfl
  rw [h1, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf]

theorem normalizerAction_mem_range_conj_iff {L : Subgroup G} (hL : commutator L = ⊤)
    (g : normalizer (L : Set G)) :
    normalizerAction L g ∈ (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range ↔
      (g : G) ∈ L ⊔ centralizer (L : Set G) := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL
  obtain ⟨g, hg⟩ := g
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine mem_sup_centralizer_iff.2 ⟨l, l.2, ?_⟩
    refine (normalizerMonoidHom_eq_conj_iff hg l).1
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective L ?_)
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
    exact hq.symm
  · intro hgs
    obtain ⟨l, hl, hx⟩ := mem_sup_centralizer_iff.1 hgs
    refine ⟨((⟨l, hl⟩ : L) : L ⧸ center L), ?_⟩
    have hψ := (normalizerMonoidHom_eq_conj_iff hg ⟨l, hl⟩).2 hx
    change MulAut.conj _ = CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L
      (L.normalizerMonoidHom ⟨g, hg⟩)
    rw [hψ, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
    rfl

variable [Finite G]

theorem exists_map_center_eq_zpowers {L : Subgroup G} (hZ : Nat.card (center L) = 2) :
    ∃ z : G, orderOf z = 2 ∧ (center L).map L.subtype = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (center L) := by rw [hZ]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 h2
  have hzG : orderOf (((z : L) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have hzmem : ((z : L) : G) ∈ (center L).map L.subtype := ⟨(z : L), z.2, rfl⟩
  refine ⟨((z : L) : G), hzG, ?_⟩
  refine (eq_of_le_of_card_ge (zpowers_le.2 hzmem) ?_).symm
  rw [Subgroup.card_map_of_injective L.subtype_injective, hZ, Nat.card_zpowers, hzG]

end Commuting

end CFSG.EvenSporadicStandard
