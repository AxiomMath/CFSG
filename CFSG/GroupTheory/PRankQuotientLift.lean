module

public import CFSG.GH74.GLS.Stage1.Thm6.Lift
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27A

public section

namespace CFSG.GroupTheory

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_isPGroup_of_coprime_kernel (N : Subgroup Y) [N.Normal] {p : ℕ} (hp : p.Prime)
    (hcop : p.Coprime (Nat.card N)) {K : Subgroup (Y ⧸ N)} (hK : IsPGroup p ↥K) :
    ∃ D : Subgroup Y, IsPGroup p ↥D ∧ Nonempty (↥D ≃* ↥K) ∧
      D ⊔ N = K.comap (QuotientGroup.mk' N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hDp, hDmap, hDinf⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.exists_lift_pSubgroup N
      ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop) K hK
  refine ⟨D, hDp, ?_, ?_⟩
  ·
    let φ : ↥D →* ↥K :=
      { toFun := fun x =>
          ⟨QuotientGroup.mk' N x, by rw [← hDmap]; exact Subgroup.mem_map_of_mem _ x.2⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    have hφinj : Function.Injective φ := by
      intro a b hab
      have h1 : (QuotientGroup.mk' N) (a : Y) = (QuotientGroup.mk' N) (b : Y) :=
        congrArg Subtype.val hab
      have h2 : (QuotientGroup.mk' N) ((a : Y) * (b : Y)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 : (a : Y) * (b : Y)⁻¹ ∈ N := (QuotientGroup.eq_one_iff _).mp h2
      have h4 : (a : Y) * (b : Y)⁻¹ ∈ D := D.mul_mem a.2 (D.inv_mem b.2)
      have h5 : (a : Y) * (b : Y)⁻¹ = 1 := by
        have := Subgroup.mem_inf.mpr ⟨h4, h3⟩
        rw [hDinf] at this
        simpa using this
      exact Subtype.ext (mul_inv_eq_one.mp h5)
    have hφsurj : Function.Surjective φ := by
      intro y
      have hy : (y : Y ⧸ N) ∈ D.map (QuotientGroup.mk' N) := by rw [hDmap]; exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩
  · rw [← hDmap, QuotientGroup.comap_map_mk', sup_comm]

theorem two_le_pRank_of_quotient (N : Subgroup Y) [N.Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ N))) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective (K := ⊤)
    ((QuotientGroup.mk' N).comp Subgroup.topEquiv.toMonoidHom) ?_ hp2 h
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact ⟨⟨x, trivial⟩, rfl⟩

end CFSG.GroupTheory
