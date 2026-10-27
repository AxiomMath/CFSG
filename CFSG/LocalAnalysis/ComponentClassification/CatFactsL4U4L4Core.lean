module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Det
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Proj

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

@[expose] noncomputable def projToPGL (n : ℕ) (F : Type) [Field F] :
    StatedProj (StatedSL n F) →* ProjGenLinGroup (Fin n) F :=
  QuotientGroup.lift _ (ProjGenLinGroup.mk.comp (StatedSL n F).subtype) (by
    intro x hx
    rw [Subgroup.mem_subgroupOf, StatedScalars] at hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
      GeneralLinearGroup.center_eq_range_scalar]
    exact hx)

theorem projToPGL_mk (n : ℕ) (A : StatedSL n F) :
    projToPGL n F (QuotientGroup.mk A) = ProjGenLinGroup.mk (A : GL (Fin n) F) := rfl

theorem projToPGL_injective (n : ℕ) : Function.Injective (projToPGL n F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, projToPGL_mk, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar] at hx
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars]
  exact hx

theorem det_eq_one_of_mem_statedSL {n : ℕ} {A : GL (Fin n) F} (hA : A ∈ StatedSL n F) :
    (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem not_mem_of_isPGroup_two {Y : Type*} [Group Y] {Z : Subgroup Y} (hZ : IsPGroup 2 Z)
    {y : Y} {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hy : orderOf y = s) : y ∉ Z := by
  intro hyZ
  obtain ⟨k, hk⟩ := hZ ⟨y, hyZ⟩
  have h1 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hy] at h2
  exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1 (hs.dvd_of_dvd_pow h2))

variable [Fintype F]

theorem card_mod_four_of_inner_L4 {Y : Type} [Group Y] [Finite Y]
    (hZ2 : IsPGroup 2 (Subgroup.center Y)) (hq : Odd (Fintype.card F))
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL 4 F)) {ℓ y : Y}
    (hℓ : ℓ ∉ Subgroup.center Y) (hℓ2 : ℓ ^ 2 ∈ Subgroup.center Y) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsq : s ∣ Fintype.card F ^ 2 + 1) (hy : orderOf y = s)
    (hyℓ : y * ℓ = ℓ * y) : Fintype.card F % 4 = 3 := by
  classical
  have := Fact.mk hs
  set π : Y →* ProjGenLinGroup (Fin 4) F :=
    (projToPGL 4 F).comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))) with hπ
  have hπker : ∀ u : Y, π u = 1 ↔ u ∈ Subgroup.center Y := by
    intro u
    rw [hπ, MonoidHom.comp_apply, (projToPGL_injective 4).eq_iff' (map_one _), MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk ℓ))
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (π y)
  have hx : π ℓ = ProjGenLinGroup.mk (k₀ : GL (Fin 4) F) := by
    rw [hπ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, ← hk₀, projToPGL_mk]
  have hyZ : y ∉ Subgroup.center Y := not_mem_of_isPGroup_two hZ2 hs hs2 hy
  obtain ⟨l, hl, hns⟩ := not_isSquare_of_comm_odd_order (n := 4) (e := 1) (by norm_num) hq hs
    hs2 (by simpa using hsq) (by norm_num) (k₀ : GL (Fin 4) F)
    (by rw [← hx]; exact fun h1 => hℓ ((hπker ℓ).1 h1))
    (by rw [← hx, ← map_pow]; exact (hπker _).2 hℓ2) g
    (by rw [hg]; exact fun h1 => hyZ ((hπker y).1 h1))
    (by rw [hg, ← map_pow, show y ^ s = 1 by rw [← hy]; exact pow_orderOf_eq_one y, map_one])
    (by rw [hg, ← hx, ← map_mul, ← map_mul, hyℓ])
  obtain ⟨-, hneg⟩ := sq_eq_neg_one_of_det_eq_one (k₀ : GL (Fin 4) F) l hl hns
    (det_eq_one_of_mem_statedSL k₀.2)
  rw [FiniteField.isSquare_neg_one_iff] at hneg
  omega

end CFSG.ComponentClassification.CatFactsL4U4
