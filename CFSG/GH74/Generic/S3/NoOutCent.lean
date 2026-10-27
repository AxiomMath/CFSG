module

public import CFSG.GH74.Generic.S3.NoOutInner
public import CFSG.GH74.Generic.S3.NoOutS4
public import CFSG.GH74.Generic.S3.NoOutB4
public import CFSG.GH74.Generic.S3.LinEvenNbr

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.KGroups.L3Eps (InvDataB4)
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_apply_mk coe_conjOn conjOn)

section Cent

variable {G : Type} [Group G] [Finite G]

theorem no_central_conj {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K)
    (honly : OnlyInvX x K) (hfus : NoFusionAt x K) {t : StatedLieTag} {p f : ℕ} {y : G} {Iw Iv : Subgroup G}
    (hnd : NbrData G t p f x y Iw Iv) (himg : imgBar x Iw = K)
    (H0 : IsComponent (S45.barSub (y * x) Iv)) {z : G} (hz2 : z * z = 1) (hzx : z * x = x * z)
    (hzy : z * y = y * z) (hzne : z ≠ x) (hconj : IsConj x z) {O : Subgroup G} (hOodd : Odd (Nat.card O))
    (hOnorm : ∀ i ∈ Iv, ∀ o ∈ O, i * o * i⁻¹ ∈ O) (hcent : ∀ i ∈ Iv, z * i * z⁻¹ * i⁻¹ ∈ O) : False := by
  classical
  have : Group.IsPerfect ↥Iw := hnd.Iw_quasisimple.1
  have hzC : z ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hzx
  have hzN : z ∈ normalizer (Iw : Set G) := hnd.comp_w.le_normalizer hzC
  obtain ⟨S, hS⟩ := hnd.exists_S_B4
  have himgS := hnd.image_Iv_B4 hS
  set π : ↥Iw →* ↥Iw ⧸ center ↥Iw := QuotientGroup.mk' (center ↥Iw) with hπ
  set R : Subgroup (↥Iw ⧸ center ↥Iw) := ((O ⊓ Iw).subgroupOf Iw).map π with hR
  have hOI : Odd (Nat.card ↥(O ⊓ Iw)) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_left)
  have hsub : Nat.card ↥((O ⊓ Iw).subgroupOf Iw) = Nat.card ↥(O ⊓ Iw) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : O ⊓ Iw ≤ Iw)).toEquiv
  have hRodd : Odd (Nat.card R) := Odd.of_dvd_nat (hsub ▸ hOI) (Subgroup.card_map_dvd _ _)
  have hRS : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs r hr
    obtain ⟨i, hiIv, rfl⟩ := (himgS s).1 hs
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have hr₀' : ((r₀ : ↥Iw) : G) ∈ O ⊓ Iw := hr₀
    refine ⟨i * r₀ * i⁻¹, ?_, by simp [hπ]⟩
    show ((i * r₀ * i⁻¹ : ↥Iw) : G) ∈ O ⊓ Iw
    exact ⟨hOnorm _ hiIv _ hr₀'.1, (i * r₀ * i⁻¹).2⟩
  have hfix : ∀ s ∈ S, normalizerAct Iw ⟨z, hzN⟩ s * s⁻¹ ∈ R := by
    intro s hs
    obtain ⟨i, hiIv, rfl⟩ := (himgS s).1 hs
    rw [normalizerAct_apply_mk]
    refine ⟨conjOn Iw ⟨z, hzN⟩ i * i⁻¹, ?_, by simp [hπ]⟩
    show ((conjOn Iw ⟨z, hzN⟩ i * i⁻¹ : ↥Iw) : G) ∈ O ⊓ Iw
    exact ⟨hcent i hiIv, (conjOn Iw ⟨z, hzN⟩ i * i⁻¹).2⟩
  obtain ⟨m, hm, hact⟩ := b4_inner (M := Iw) hnd.y_Iw hnd.mk_y_ne_one hnd.y_sq hS hzN hz2 hzy R hRodd hRS hfix
  exact inner_false_of_isConj hset honly hfus hnd himg H0 hconj hzne hzx ⟨m, hm, hact⟩

theorem zStar_at_u {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K)
    (honly : OnlyInvX x K) (hfus : NoFusionAt x K) {t : StatedLieTag} {p f : ℕ} {y : G} {Iw Iv : Subgroup G}
    (hnd : NbrData G t p f x y Iw Iv) (himg : imgBar x Iw = K)
    (H0 : IsComponent (S45.barSub (y * x) Iv)) {u : G} (hu : u = y ∨ u = y * x)
    (hcomp : IsComponent (S45.barSub u Iv)) :
    ∃ O : Subgroup G, O ≤ centralizer ({u} : Set G) ∧
      (∀ c ∈ centralizer ({u} : Set G), ∀ o ∈ O, c * o * c⁻¹ ∈ O) ∧ Odd (Nat.card O) ∧
      ∀ h ∈ centralizer ({u} : Set G), h * x * h⁻¹ * x⁻¹ ∈ O := by
  have hx2 := hnd.x_sq
  have hxy : x * y = y * x := hnd.comm.symm
  have hIvx : ∀ i ∈ Iv, i * x = x * i := fun i hi =>
    mem_centralizer_singleton_iff.1 (hnd.Iw_le (hnd.Iv_le hi))
  have hIvy : ∀ i ∈ Iv, i * y = y * i := hnd.Iv_central
  have hxu : x * u = u * x := by
    rcases hu with hu | hu
    · rw [hu]; exact hxy
    · rw [hu]
      calc x * (y * x) = (x * y) * x := by rw [mul_assoc]
        _ = (y * x) * x := by rw [hxy]
  have hIv : Iv ≤ centralizer ({u} : Set G) := by
    intro i hi
    rw [mem_centralizer_singleton_iff]
    rcases hu with hu | hu
    · rw [hu]; exact hIvy i hi
    · rw [hu]
      calc i * (y * x) = (i * y) * x := by rw [mul_assoc]
        _ = (y * i) * x := by rw [hIvy i hi]
        _ = y * (i * x) := mul_assoc _ _ _
        _ = y * (x * i) := by rw [hIvx i hi]
        _ = (y * x) * i := by rw [mul_assoc]
  refine zStar_of_component hxu hx2 hnd.x_ne_one hIv hcomp (fun i hi => (hIvx i hi).symm) ?_
  intro z hz2 hzx hzu hzne hconj hcent
  have hzy : z * y = y * z := by
    rcases hu with hu | hu
    · rw [hu] at hzu; exact hzu
    · rw [hu] at hzu
      have : z * y * x = y * z * x := by
        calc z * y * x = z * (y * x) := by rw [mul_assoc]
          _ = (y * x) * z := hzu
          _ = y * (x * z) := by rw [mul_assoc]
          _ = y * (z * x) := by rw [hzx]
          _ = y * z * x := by rw [mul_assoc]
      exact mul_right_cancel this
  exact no_central_conj hset honly hfus hnd himg H0 hz2 hzx hzy hzne hconj (oc_odd u)
    (fun i hi o ho => oc_conj u (hIv hi) ho) hcent

end Cent

end CFSG.GH74.Generic.S3
