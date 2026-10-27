module

public import CFSG.CGT.T75F.Omega1
public import CFSG.CGT.T75F.WclAbel
import CFSG.CGT.Timmesfeld75.Fusion
public import CFSG.CGT.Timmesfeld75.Sec5SevenB

public section

namespace CFSG.CGT.T75F

open CFSG.Open CFSG.CGT.Timmesfeld75

theorem isPGroup_two_zpowers {K : Type*} [Group K] {b : K} (hb : b * b = 1) :
    IsPGroup 2 (Subgroup.zpowers b) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hb2]

theorem sec57Shult_of_goldschmidt (hG : Goldschmidt1974) : Sec57Shult := by
  intro G _ T T₁ hy hS _ hab hcase
  by_contra hA
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  obtain ⟨S₀, τ, hTS₀, hτA, hτ1, hτ2, hτS₀, hτc⟩ := exists_central_of_secA hy hA
  have hWab := isMulCommutative_wcl hy hS hab hcase hτA hτ1
  have hcomm := involutions_commute_of_wcl_abelian hG hy.nonab S₀ hτ1 hτ2 hτS₀ hτc hWab
  obtain ⟨x, hx⟩ := hy.pair.conj
  obtain ⟨⟨s, hs⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hy.pair.nontriv
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hsT : s ∈ T := (mem_normIn.1 hs).1
  have hsN : s ∈ Subgroup.normalizer (T₁ : Set G) := (mem_normIn.1 hs).2
  have hs2 : s * s = 1 := elemAbelian_mul_self hy.pair.wc.1 hsT
  have hel₁ : IsElemAbelian 2 T₁ := by
    rw [hx]
    exact isElemAbelian_conjSubgroup hy.pair.wc.1 x
  have hP : IsPGroup 2 (Subgroup.zpowers s ⊔ T₁ : Subgroup G) :=
    (isPGroup_two_zpowers hs2).to_sup_of_normal_right' (isPGroup_two_of_isElemAbelian hel₁)
      (Subgroup.zpowers_le.2 hsN)
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S₀ S'
  have hcomm' : ∀ a ∈ ((g • S₀ : Sylow 2 G) : Subgroup G),
      ∀ b ∈ ((g • S₀ : Sylow 2 G) : Subgroup G), a * a = 1 → b * b = 1 → a * b = b * a := by
    intro a ha b hb ha2 hb2
    have ha' := (mem_sylow_smul_iff_inv_mul_mul_mem S₀ g a).1 ha
    have hb' := (mem_sylow_smul_iff_inv_mul_mul_mem S₀ g b).1 hb
    refine mul_comm_of_conj_mul_comm (g := g) (hcomm _ ha' _ hb' ?_ ?_)
    · calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [ha2]; group
    · calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
        _ = 1 := by rw [hb2]; group
  have hsS' : s ∈ ((g • S₀ : Sylow 2 G) : Subgroup G) :=
    hS' (Subgroup.mem_sup_left (Subgroup.mem_zpowers s))
  have hle : conjSubgroup x T ≤ Subgroup.centralizer ({s} : Set G) := by
    intro y hy'
    rw [← hx] at hy'
    have hyy : y * y = 1 := elemAbelian_mul_self hel₁ hy'
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hcomm' y (hS' (Subgroup.mem_sup_right hy')) s hsS' hyy hs2)
  exact hy.pair.ne (hx.trans ((hy.pair.wc.2 s hsT hs1).2 x hle))

end CFSG.CGT.T75F
