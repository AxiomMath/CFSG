module

public import CFSG.ClassicalInvolution.Sp62Rec.FourLift
public import CFSG.ClassicalInvolution.Sp62Rec.Pkg

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open
open scoped Pointwise

theorem exists_four_isConj_of_surjective {H H' : Type*} [Group H] [Group H'] [Finite H]
    (φ : H →* H') (hφ : Function.Surjective φ) (hK : Odd (Nat.card φ.ker)) {z : H}
    (hz : z * z = 1) (D : Subgroup H') (hD4 : Nat.card D = 4) (hD2 : ∀ d ∈ D, d * d = 1)
    (hDz : ∀ d ∈ D, d ≠ 1 → IsConj d (φ z)) :
    ∃ D₀ : Subgroup H, Nat.card D₀ = 4 ∧ (∀ d ∈ D₀, d * d = 1) ∧
      ∀ d ∈ D₀, d ≠ 1 → IsConj d z := by
  let ψ : H ⧸ φ.ker ≃* H' := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let j : H' →* H ⧸ φ.ker := ψ.symm.toMonoidHom
  have hj : Function.Injective j := ψ.symm.injective
  have hjz : j (φ z) = (z : H ⧸ φ.ker) := (ψ.symm_apply_eq).2 rfl
  have hD'4 : Nat.card (D.map j) = 4 := by
    rw [Subgroup.card_map_of_injective hj, hD4]
  have hD'2 : ∀ d ∈ D.map j, d * d = 1 := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
    rw [← map_mul, hD2 d₀ hd₀, map_one]
  have hD'z : ∀ d ∈ D.map j, d ≠ 1 → IsConj d (z : H ⧸ φ.ker) := by
    intro d hd hd1
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
    have hd₀1 : d₀ ≠ 1 := fun h => hd1 (by rw [h, map_one])
    have h := j.map_isConj (hDz d₀ hd₀ hd₀1)
    rwa [hjz] at h
  exact exists_four_isConj_of_quotient φ.ker hK hz (D.map j) hD'4 hD'2 hD'z

private theorem eq_one_of_mem_odd_of_mul_self_eq_one {H : Type*} [Group H] (K : Subgroup H)
    (hK : Odd (Nat.card K)) {x : H} (hx : x ∈ K) (hx2 : x * x = 1) : x = 1 := by
  by_contra hx1
  have hp : (⟨x, hx⟩ : K) ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext hx2
  have hne : (⟨x, hx⟩ : K) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hord : orderOf (⟨x, hx⟩ : K) = 2 := orderOf_eq_prime hp hne
  have hdvd : orderOf (⟨x, hx⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  rw [hord] at hdvd
  exact hK.not_two_dvd_nat hdvd


theorem exists_conj_eq_pi12_or_pi3 {G : Type} [Group G] [Finite G] {z e : G} {B : Subgroup G}
    {T : Sylow 2 G} (φ : ↥B →* ↥Hhat) (hφ : Function.Surjective φ) (hK : Odd (Nat.card φ.ker))
    (hTB : (T : Subgroup G) ≤ B) (hzT : z ∈ (T : Subgroup G))
    (hzc : ∀ x ∈ (T : Subgroup G), z * x = x * z) (hzB : z ∈ B) (heB : e ∈ B)
    (he : φ ⟨e, heB⟩ = ⟨alpha, alpha_mem_Hhat⟩) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hze : z ≠ e)
    (he2 : e * e = 1) (hcomm : z * e = e * z)
    (hS0 : Nat.card S0 = 512) (hH : Nat.card Hhat = 23040)
    (hZ : ∀ x ∈ S0, (∀ y ∈ S0, x * y = y * x) → x = 1 ∨ x = alpha ∨ x = pi12 ∨ x = pi3)
    (hα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2)))) :
    ∃ c ∈ Hhat, c * ((φ ⟨z, hzB⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) * c⁻¹ = pi12 ∨
      c * ((φ ⟨z, hzB⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) * c⁻¹ = pi3 := by
  haveI : Finite ↥Hhat := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  let TB : Sylow 2 ↥B := T.subtype hTB
  let P : Sylow 2 ↥Hhat := TB.mapSurjective hφ
  have hzTB : (⟨z, hzB⟩ : ↥B) ∈ (T : Subgroup G).subgroupOf B := Subgroup.mem_subgroupOf.2 hzT
  have hwP : φ ⟨z, hzB⟩ ∈ (P : Subgroup ↥Hhat) := by
    show φ ⟨z, hzB⟩ ∈ ((T : Subgroup G).subgroupOf B).map φ
    exact Subgroup.mem_map.2 ⟨⟨z, hzB⟩, hzTB, rfl⟩
  have hPcomm : ∀ p ∈ (P : Subgroup ↥Hhat), φ ⟨z, hzB⟩ * p = p * φ ⟨z, hzB⟩ := by
    intro p hp
    have hp' : p ∈ ((T : Subgroup G).subgroupOf B).map φ := hp
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hp'
    have hbT : (b : G) ∈ (T : Subgroup G) := Subgroup.mem_subgroupOf.1 hb
    have hbz : (⟨z, hzB⟩ : ↥B) * b = b * ⟨z, hzB⟩ := Subtype.ext (hzc _ hbT)
    rw [← map_mul, ← map_mul, hbz]
  have hS0card : Nat.card (S0.subgroupOf Hhat) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_Hhat).toEquiv, hS0]
  have hS0p : IsPGroup 2 (S0.subgroupOf Hhat) :=
    IsPGroup.of_card (n := 9) (by rw [hS0card]; norm_num)
  have hS0idx : ¬ 2 ∣ (S0.subgroupOf Hhat).index := by
    have h := Subgroup.card_mul_index (S0.subgroupOf Hhat)
    rw [hS0card, hH] at h
    have h45 : (S0.subgroupOf Hhat).index = 45 := by omega
    rw [h45]
    norm_num
  let S1 : Sylow 2 ↥Hhat := IsPGroup.toSylow hS0p hS0idx
  have hS1coe : (S1 : Subgroup ↥Hhat) = S0.subgroupOf Hhat := rfl
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥Hhat) P S1
  have hS1 : (S1 : Subgroup ↥Hhat) = MulAut.conj c • (P : Subgroup ↥Hhat) :=
    (congrArg (fun X : Sylow 2 ↥Hhat => (X : Subgroup ↥Hhat)) hc).symm.trans
      Sylow.coe_subgroup_smul
  have hconjP : ∀ y ∈ (S1 : Subgroup ↥Hhat), c⁻¹ * y * c ∈ (P : Subgroup ↥Hhat) := by
    intro y hy
    rw [hS1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact hy
  have hconjS : ∀ p ∈ (P : Subgroup ↥Hhat), c * p * c⁻¹ ∈ (S1 : Subgroup ↥Hhat) := by
    intro p hp
    rw [hS1]
    exact Subgroup.smul_mem_pointwise_smul p (MulAut.conj c) _ hp
  have hyS : c * φ ⟨z, hzB⟩ * c⁻¹ ∈ (S1 : Subgroup ↥Hhat) := hconjS _ hwP
  have hycomm : ∀ s ∈ (S1 : Subgroup ↥Hhat),
      (c * φ ⟨z, hzB⟩ * c⁻¹) * s = s * (c * φ ⟨z, hzB⟩ * c⁻¹) := by
    intro s hs
    have hp := hPcomm _ (hconjP s hs)
    calc (c * φ ⟨z, hzB⟩ * c⁻¹) * s = c * (φ ⟨z, hzB⟩ * (c⁻¹ * s * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * s * c) * φ ⟨z, hzB⟩) * c⁻¹ := by rw [hp]
      _ = s * (c * φ ⟨z, hzB⟩ * c⁻¹) := by group
  have hYS0 : ((c * φ ⟨z, hzB⟩ * c⁻¹ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ S0 := by
    have h := hyS
    rw [hS1coe] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hYcomm : ∀ s ∈ S0, ((c * φ ⟨z, hzB⟩ * c⁻¹ : ↥Hhat) : StatedSp 3 (ZMod 2)) * s =
      s * ((c * φ ⟨z, hzB⟩ * c⁻¹ : ↥Hhat) : StatedSp 3 (ZMod 2)) := by
    intro s hs
    have hsH : s ∈ Hhat := S0_le_Hhat hs
    have hs1 : (⟨s, hsH⟩ : ↥Hhat) ∈ (S1 : Subgroup ↥Hhat) := by
      rw [hS1coe]
      exact Subgroup.mem_subgroupOf.2 hs
    exact congrArg Subtype.val (hycomm _ hs1)
  rcases hZ _ hYS0 hYcomm with hY | hY | hY | hY
  ·
    exfalso
    have h : c * φ ⟨z, hzB⟩ * c⁻¹ = 1 := Subtype.ext hY
    have hw1 : φ ⟨z, hzB⟩ = 1 := by
      calc φ ⟨z, hzB⟩ = c⁻¹ * (c * φ ⟨z, hzB⟩ * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    have hker : (⟨z, hzB⟩ : ↥B) ∈ φ.ker := MonoidHom.mem_ker.2 hw1
    have hsq : (⟨z, hzB⟩ : ↥B) * ⟨z, hzB⟩ = 1 := Subtype.ext hz2
    exact hz1 (congrArg Subtype.val (eq_one_of_mem_odd_of_mul_self_eq_one φ.ker hK hker hsq))
  ·
    exfalso
    have hcent : ∀ g : ↥Hhat,
        (⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) * g = g * ⟨alpha, alpha_mem_Hhat⟩ := by
      intro g
      apply Subtype.ext
      have hg := hα g.2
      rw [Subgroup.mem_centralizer_iff] at hg
      exact hg alpha (Set.mem_singleton alpha)
    have h : c * φ ⟨z, hzB⟩ * c⁻¹ = ⟨alpha, alpha_mem_Hhat⟩ := Subtype.ext hY
    have hwa : φ ⟨z, hzB⟩ = ⟨alpha, alpha_mem_Hhat⟩ := by
      calc φ ⟨z, hzB⟩ = c⁻¹ * (c * φ ⟨z, hzB⟩ * c⁻¹) * c := by group
        _ = c⁻¹ * (⟨alpha, alpha_mem_Hhat⟩ * c) := by rw [h]; group
        _ = c⁻¹ * (c * ⟨alpha, alpha_mem_Hhat⟩) := by rw [hcent c]
        _ = ⟨alpha, alpha_mem_Hhat⟩ := by group
    have he2' : (⟨e, heB⟩ : ↥B) * ⟨e, heB⟩ = 1 := Subtype.ext he2
    have haa : (⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) * ⟨alpha, alpha_mem_Hhat⟩ = 1 := by
      rw [← he, ← map_mul, he2', map_one]
    have hzeK : (⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hwa, he, haa]
    have hsq : (⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩ * ((⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩) = 1 := by
      apply Subtype.ext
      show z * e * (z * e) = 1
      calc z * e * (z * e) = z * (e * z) * e := by group
        _ = z * (z * e) * e := by rw [← hcomm]
        _ = (z * z) * (e * e) := by group
        _ = 1 := by rw [hz2, he2, one_mul]
    have hze1 : (⟨z, hzB⟩ : ↥B) * ⟨e, heB⟩ = 1 :=
      eq_one_of_mem_odd_of_mul_self_eq_one φ.ker hK hzeK hsq
    have hze1' : z * e = 1 := congrArg Subtype.val hze1
    apply hze
    calc z = z * (e * e) := by rw [he2, mul_one]
      _ = z * e * e := by group
      _ = e := by rw [hze1', one_mul]
  · exact ⟨(c : StatedSp 3 (ZMod 2)), c.2, Or.inl hY⟩
  · exact ⟨(c : StatedSp 3 (ZMod 2)), c.2, Or.inr hY⟩

end CFSG.ClassicalInvolution.Sp62Rec
