module

public import CFSG.GH74.GLS.LU.Local.Torus7
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.LU.Local.GoodPrime
public import CFSG.GH74.GLS.LU.Local.Torus6

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

theorem luKStepLeaf₁
    : LUKStepLeaf₁ := by
  intro G _ _ hG p f hp hp2 hq z S K₁ K₂ t u hH ε hne he
  have hX : LUCtx G p f z S K₁ K₂ t u ε := ⟨hG, hp, hp2, hq, hH, he⟩
  obtain ⟨hc, hs, -, -, -⟩ := hH
  obtain ⟨h₀, hh₀⟩ := exists_h₀ hs
  have hf : 0 < f := Nat.pos_of_ne_zero fun h0 => by rw [h0, pow_zero] at hq; omega
  obtain ⟨r, hrp, hr2, hrne, hrdvd, hrf, hgood⟩ :=
    exists_good_prime' hp hp2 hf ε he.eps hq hne he.mod8
  have hr : GoodR p f r := ⟨hrp, hr2, hrne, hrf, hgood⟩
  have : Fact r.Prime := ⟨hrp⟩
  have hrH : r ∣ Nat.card ↥(K₁ ⊓ centralizer ({u} : Set G)) := by
    have : (r : ℤ) ∣ (Nat.card ↥(K₁ ⊓ centralizer ({u} : Set G)) : ℤ) := by
      rw [he.H_card]; exact hrdvd
    exact Int.natCast_dvd_natCast.mp this
  obtain ⟨a₁', ha₁'⟩ := exists_prime_orderOf_dvd_card' r hrH
  have ha₁ : (a₁' : G) ∈ K₁ ⊓ centralizer ({u} : Set G) := a₁'.2
  have hord : orderOf (a₁' : G) = r := by rw [Subgroup.orderOf_coe]; exact ha₁'
  obtain ⟨a₀, ha₀, ha₀ord⟩ := exists_a0_of hX hr ha₁ hord
  obtain ⟨x, hx1, hxz, hxu, hxK₁, hxL, hdec, hnc₂, -⟩ := exists_x hX hr ha₁ hord ha₀ ha₀ord hh₀
  have hx' : XData z K₁ K₂ x r := ⟨hxz, hxK₁, hdec, hnc₂⟩
  obtain ⟨v, hv, w, hw, hzv, huw⟩ := exists_v_w hX hh₀
  obtain ⟨hhz, hgz⟩ := h_conj hc hs hw hzv huw
  have hxv : x * v = v * x := hxL v hv
  have hxw : x * w = w * x := hxK₁ w hw
  have hxh : x * (v * w) = (v * w) * x := by
    have c1 : Commute x v := hxv
    have c2 : Commute x w := hxw
    exact (c1.mul_right c2).eq
  have htL := t_norm_L hX hh₀
  have htN : t ∈ normalizer ((cj K₁ (v * w) : Subgroup G) : Set G) := by
    rcases cj_eq_or hc hh₀ hhz with e | e
    · rw [e]; exact htL
    · rw [e]
      exact norm₂_of_norm₁ (comps_u hX hh₀) (mem_centralizer_singleton_iff.mpr hs.ut.symm) htL
  refine ⟨u, v * w, x, hxz, hxh.symm, Or.inl rfl, hhz, htN, hx1,
    fun k hk => mem_centralizer_singleton_iff.mpr (hxK₁ k hk).symm, kcomp_CY hX hx',
    fun T => cyclic_sylow_CY hX hx' T, hD1_CY hX hr hx' hxu, v⁻¹, ?_, ?_⟩
  · have c1 : Commute x v⁻¹ := (show Commute x v from hxv).inv_right
    exact c1.eq.symm
  · rw [inv_inv]; exact hgz

end CFSG.GH74.GLS.LU.Local
