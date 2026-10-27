module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31F
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Red

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem l31f_exists_involution {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥) : ∃ s ∈ R, orderOf s = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hR) u
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hu1 (orderOf_eq_one_iff.mp (by simpa using hj))
  have h2dvd : 2 ∣ orderOf u := by rw [hj]; exact dvd_pow_self 2 hj0
  refine ⟨((u ^ (orderOf u / 2) : ↥R) : G), (u ^ (orderOf u / 2)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (orderOf_pos u).ne' h2dvd

theorem l31f_isSection_hat {G : Type} [Group G] [Finite G] {H J R : Subgroup G}
    (hJ : IsPCompIn 2 H J)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)))
    {s : G} (hsR : s ∈ R) : IsSection (Hat J) ↥(centralizer ({s} : Set G)) := by
  obtain ⟨-, -, -, hcomm, hJ0J, hcover⟩ := l31_reduce hJ hR
  have hJ0c : redJ0 J R ≤ centralizer ({s} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm x hx s hsR
  refine ⟨(redJ0 J R).subgroupOf (centralizer ({s} : Set G)),
    (hatMap J hJ0J).comp (Subgroup.subgroupOfEquivOfLe hJ0c).toMonoidHom, ?_⟩
  intro q
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, hx, n, hn, hjx⟩ := hcover j j.2
  refine ⟨(Subgroup.subgroupOfEquivOfLe hJ0c).symm ⟨x, hx⟩, ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    hatMap_apply]
  obtain ⟨n', hn', rfl⟩ := hn
  rw [QuotientGroup.eq]
  have h1 : (⟨x, hJ0J hx⟩ : ↥J)⁻¹ * j = n' := by
    apply Subtype.ext
    simp [hjx]
  exact h1 ▸ hn'

theorem l31f_of_pcomp (hInv : InvSec)
    {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S)
    {H J R : Subgroup G} (hJ : IsPCompIn 2 H J)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)))
    (hR1 : R ≠ ⊥) :
    (NativeSporadic.IsSporadic (Hat J) .M11 ∨
      ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ (Odd (p ^ f) ∨ p ^ f = 4) ∧
        (LieModel (Hat J) .PSL 3 p f ∨ LieModel (Hat J) .PSU 3 p f)) →
    NativeSporadic.IsSporadic (Hat J) .M11 ∧ IsDoubleCoverOfAlt (CentralizerBar z) 11 := by
  intro hf
  obtain ⟨hRpg, -⟩ := l31_reduce hJ hR
  obtain ⟨s, hsR, hs2⟩ := l31f_exists_involution hRpg hR1
  exact l31_f_core hInv hctx hs2 (TwoThin.isQuasisimple_hat hJ) (l31f_isSection_hat hJ hR hsR) hf

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
