module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup

theorem isTwoComponentIn_of_normal_of_even {G : Type*} [Group G] {J A : Subgroup G} [Finite J]
    (hJA : J ≤ A) (hn : (J.subgroupOf A).Normal) (hq : IsQuasisimple J)
    (h2 : 2 ∣ Nat.card J) : IsTwoComponentIn J A := by
  have hodd : Odd (Nat.card (pPrimeCore 2 J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOc : pPrimeCore 2 J ≤ center J := by
    rcases LocalCores.quasisimple_normal_subgroups hq
        (inferInstance : (pPrimeCore 2 J).Normal) with h | h
    · exfalso
      rw [h, card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    · exact h
  exact ⟨hJA, Subgroup.Normal.isSubnormal hn, hq.1,
    (LocalCores.quasisimple_central_quotient hq _ hOc).1⟩

section Lift

variable {S G : Type*} [Group S] [Group G] (π : S →* G) (B : Subgroup G)

@[expose] def liftJ : Subgroup S :=
  ⁅B.comap π, B.comap π⁆

theorem liftJ_le_comap : liftJ π B ≤ B.comap π :=
  Subgroup.commutator_le_self _

@[expose] def liftH : B.comap π →* B :=
  (π.comp (B.comap π).subtype).codRestrict B fun x => x.2

@[expose] def liftJEquiv : _root_.commutator (B.comap π) ≃* liftJ π B :=
  ((_root_.commutator (B.comap π)).equivMapOfInjective (B.comap π).subtype
    (B.comap π).subtype_injective).trans (MulEquiv.subgroupCongr (map_subtype_commutator _))

theorem coe_liftJEquiv (x : _root_.commutator (B.comap π)) :
    (liftJEquiv π B x : S) = ((x : B.comap π) : S) :=
  rfl

variable {π B}

theorem map_liftJ (hB : B ≤ π.range) (hBp : Group.IsPerfect B) : (liftJ π B).map π = B := by
  have hH : (B.comap π).map π = B := by rw [map_comap_eq, inf_eq_right.mpr hB]
  rw [liftJ, map_commutator, hH, Subgroup.isPerfect_iff.mp hBp]

theorem exists_ker_mul_mem_liftJ (hB : B ≤ π.range) (hBp : Group.IsPerfect B) {x : S}
    (hx : π x ∈ B) : ∃ k ∈ π.ker, k * x ∈ liftJ π B := by
  rw [← map_liftJ hB hBp] at hx
  obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
  refine ⟨y * x⁻¹, ?_, by rwa [inv_mul_cancel_right]⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, mul_inv_cancel]

theorem liftJ_le_centralizer (hker : π.ker ≤ center S) {u : S}
    (hBu : B ≤ centralizer {π u}) : liftJ π B ≤ centralizer {u} := by
  have h1 : ⁅B.comap π, zpowers u⁆ ≤ center S := by
    rw [commutator_le]
    intro x hx y hy
    apply hker
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute (π x) (π u) := mem_centralizer_singleton_iff.mp (hBu hx)
    rw [MonoidHom.mem_ker, map_commutatorElement, map_zpow, commutatorElement_eq_one_iff_mul_comm]
    exact (hc.zpow_right k).eq
  have h2 : ⁅⁅B.comap π, zpowers u⁆, B.comap π⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono h1 le_rfl).trans (commutator_center_left _).le)
  have h3 : ⁅⁅zpowers u, B.comap π⁆, B.comap π⁆ = ⊥ := by
    rw [commutator_comm (zpowers u)]
    exact h2
  have h4 : ⁅⁅B.comap π, B.comap π⁆, zpowers u⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate h2 h3
  exact (commutator_eq_bot_iff_le_centralizer.mp h4).trans
    (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers u)))

theorem conj_mem_liftJ {c : S} (hc : ∀ b ∈ B, π c * b * (π c)⁻¹ ∈ B) {x : S}
    (hx : x ∈ liftJ π B) : c * x * c⁻¹ ∈ liftJ π B := by
  have hH : (B.comap π).map (MulAut.conj c).toMonoidHom ≤ B.comap π := by
    rintro _ ⟨h, hh, rfl⟩
    change π (c * h * c⁻¹) ∈ B
    rw [map_mul, map_mul, map_inv]
    exact hc _ hh
  have h1 : (MulAut.conj c).toMonoidHom x ∈ (liftJ π B).map (MulAut.conj c).toMonoidHom :=
    mem_map_of_mem _ hx
  rw [liftJ, map_commutator] at h1
  exact commutator_mono hH hH h1

theorem normal_liftJ {u : S} (hc : ∀ c ∈ centralizer {u}, ∀ b ∈ B, π c * b * (π c)⁻¹ ∈ B) :
    ((liftJ π B).subgroupOf (centralizer {u})).Normal := by
  refine ⟨fun a ha b => ?_⟩
  rw [mem_subgroupOf] at ha ⊢
  exact conj_mem_liftJ (hc _ b.2) ha

theorem liftH_surjective (hB : B ≤ π.range) : Function.Surjective (liftH π B) := by
  rintro ⟨b, hb⟩
  obtain ⟨s, rfl⟩ := hB hb
  exact ⟨⟨s, hb⟩, rfl⟩

theorem ker_liftH_le (hker : π.ker ≤ center S) : (liftH π B).ker ≤ center (B.comap π) := by
  intro x hx
  have h1 : (x : S) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val ((liftH π B).mem_ker.mp hx)
  exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hker h1) g)

theorem exists_liftJ_hom (hker : π.ker ≤ center S) (hB : B ≤ π.range)
    (hBp : Group.IsPerfect B) :
    Group.IsPerfect (liftJ π B) ∧ ∃ g : liftJ π B →* B, Function.Surjective g ∧
      g.ker ≤ center (liftJ π B) ∧ ∀ x, (g x : G) = π x := by
  obtain ⟨-, hP, hs⟩ := LocalCores.central_extension_derived_of_surjective (liftH π B)
    (liftH_surjective hB) (ker_liftH_le hker) hBp
  set g := ((liftH π B).comp (_root_.commutator (B.comap π)).subtype).comp
    (liftJEquiv π B).symm.toMonoidHom with hg
  have hgx : ∀ x, (g x : G) = π x := by
    intro x
    have h1 : (((liftJEquiv π B).symm x : _root_.commutator (B.comap π)) : B.comap π) =
        ((x : S)) := by
      rw [← coe_liftJEquiv, MulEquiv.apply_symm_apply]
    change π ((((liftJEquiv π B).symm x : _root_.commutator (B.comap π)) : B.comap π) : S) =
      π x
    rw [h1]
  refine ⟨?_, g, hs.comp (liftJEquiv π B).symm.surjective, fun x hx => ?_, hgx⟩
  · have := hP
    exact Group.IsPerfect.ofSurjective (f := (liftJEquiv π B).toMonoidHom)
      (liftJEquiv π B).surjective
  · have h1 : (x : S) ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hgx, (MonoidHom.mem_ker).mp hx, OneMemClass.coe_one]
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hker h1) y)

theorem isQuasisimple_liftJ (hker : π.ker ≤ center S) (hB : B ≤ π.range)
    (hBq : IsQuasisimple B) : IsQuasisimple (liftJ π B) := by
  obtain ⟨hP, g, hg, hgk, -⟩ := exists_liftJ_hom hker hB hBq.1
  exact (LocalCores.isQuasisimple_iff_of_surjective hP g hg hgk).mpr hBq

theorem nonempty_liftJ_quotCenter (hker : π.ker ≤ center S) (hB : B ≤ π.range)
    (hBp : Group.IsPerfect B) :
    Nonempty (liftJ π B ⧸ center (liftJ π B) ≃* B ⧸ center B) := by
  obtain ⟨hP, g, hg, hgk, -⟩ := exists_liftJ_hom hker hB hBp
  have hc : center (liftJ π B) = ((QuotientGroup.mk' (center B)).comp g).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      LocalCores.comap_center_eq_of_perfect hP g hg hgk]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hg))⟩

end Lift

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
