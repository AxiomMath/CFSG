module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDiag
public import CFSG.GroupTheory.InnerCentralizerProjection
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open CFSG.CGT.PushingUpLit.CGT6.Nine7 (IsCompIn)

variable {G : Type} [Group G]

private theorem conj_conj_eq_conj_conj {c t x : G} (hct : c * t = t * c) :
    MulAut.conj t (MulAut.conj c x) = MulAut.conj c (MulAut.conj t x) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hct]

private theorem map_conj_map_conj_eq_self {t : G} (ht : t ^ 2 = 1) (K : Subgroup G) :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      MonoidHom.id G :=
    MonoidHom.ext fun x => conj_conj_of_sq_eq_one ht x
  rw [hcomp, Subgroup.map_id]

private theorem range_swapDiag_le_sup (K : Subgroup G) (t : G)
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    (swapDiag K t hc).range ≤ K ⊔ K.map (MulAut.conj t).toMonoidHom := by
  rintro _ ⟨k, rfl⟩
  exact (K ⊔ K.map (MulAut.conj t).toMonoidHom).mul_mem
    (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ k.2))

theorem map_conj_le_centralizer_map {P : Subgroup G} {t g : G} (hgt : g * t = t * g)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    P.map (MulAut.conj g).toMonoidHom ≤
      centralizer (((P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj t).toMonoidHom :
        Subgroup G) : Set G) := by
  rintro x hx
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
  have hconj : MulAut.conj t (MulAut.conj g q₀) = MulAut.conj g (MulAut.conj t q₀) :=
    conj_conj_eq_conj_conj hgt
  change MulAut.conj t (MulAut.conj g q₀) * MulAut.conj g p =
    MulAut.conj g p * MulAut.conj t (MulAut.conj g q₀)
  rw [hconj, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  have hcomm := Subgroup.mem_centralizer_iff.mp (hc hp) (MulAut.conj t q₀)
    (Subgroup.mem_map_of_mem _ hq₀)
  rw [MulAut.conj_apply] at hcomm
  calc (g * (t * q₀ * t⁻¹) * g⁻¹) * (g * p * g⁻¹)
      = g * ((t * q₀ * t⁻¹) * p) * g⁻¹ := by group
    _ = g * (p * (t * q₀ * t⁻¹)) * g⁻¹ := by rw [hcomm]
    _ = (g * p * g⁻¹) * (g * (t * q₀ * t⁻¹) * g⁻¹) := by group

private theorem swapDiag_map_conj_apply {P : Subgroup G} {t g : G} (hgt : g * t = t * g)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    {p : G} (hp : p ∈ P) :
    (swapDiag (P.map (MulAut.conj g).toMonoidHom) t
        (map_conj_le_centralizer_map hgt hc))
        ⟨MulAut.conj g p, Subgroup.mem_map_of_mem _ hp⟩ =
      MulAut.conj g ((swapDiag P t hc) ⟨p, hp⟩) := by
  simp only [swapDiag_apply]
  rw [map_mul, conj_conj_eq_conj_conj hgt]

theorem isCompIn_of_isComponent {P X : Subgroup G} (hPX : P ≤ X)
    (h : IsComponent (P.subgroupOf X)) : IsCompIn P X := by
  refine ⟨hPX, h.2, ?_⟩
  have hq : CFSG.IsQuasisimple ↥P :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPX).symm h.1
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq

theorem isComponent_of_isCompIn {P X : Subgroup G} (h : IsCompIn P X) :
    IsComponent (P.subgroupOf X) := by
  refine ⟨?_, h.2.1⟩
  have hq : CFSG.IsQuasisimple ↥P := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr h.2.2
  exact CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) hq

theorem mem_centralizer_of_map_conj_eq {P : Subgroup G} {t c : G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hP : Group.IsPerfect ↥P) (hcP : P.map (MulAut.conj c).toMonoidHom = P)
    (hct : c * t = t * c) (hcK : c ∈ centralizer ((swapDiag P t hc).range : Set G)) :
    c ∈ centralizer (P : Set G) := by
  refine CFSG.mem_centralizer_of_commutator_mem_center hP
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcP) ?_
  intro j hj
  have hcj : MulAut.conj c j ∈ P := by
    rw [← hcP]
    exact Subgroup.mem_map_of_mem _ hj
  have hdP : MulAut.conj c j * j⁻¹ ∈ P := P.mul_mem hcj (P.inv_mem hj)
  have hφcj : (swapDiag P t hc) ⟨MulAut.conj c j, hcj⟩ =
      MulAut.conj c ((swapDiag P t hc) ⟨j, hj⟩) := by
    simp only [swapDiag_apply]
    rw [map_mul, conj_conj_eq_conj_conj hct]
  have hφfix : MulAut.conj c ((swapDiag P t hc) ⟨j, hj⟩) =
      (swapDiag P t hc) ⟨j, hj⟩ := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hcK
      ((swapDiag P t hc) ⟨j, hj⟩) ⟨⟨j, hj⟩, rfl⟩
    rw [MulAut.conj_apply, ← hcomm]
    group
  have hdker : (swapDiag P t hc) (⟨MulAut.conj c j * j⁻¹, hdP⟩ : ↥P) = 1 := by
    have hdeq : (⟨MulAut.conj c j * j⁻¹, hdP⟩ : ↥P) =
        ⟨MulAut.conj c j, hcj⟩ * ⟨j, hj⟩⁻¹ := by
      ext
      simp
    rw [hdeq, map_mul, map_inv, hφcj, hφfix]
    simp
  exact Subgroup.mem_map.mpr ⟨⟨MulAut.conj c j * j⁻¹, hdP⟩,
    CFSG.OddStandard.HigherRank.F3.ker_swapDiag_le_center hc
      (MonoidHom.mem_ker.mpr hdker), rfl⟩

theorem mul_mem_centralizer_of_map_conj_eq_map {P : Subgroup G} {t c : G} (ht : t ^ 2 = 1)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hP : Group.IsPerfect ↥P)
    (hcP : P.map (MulAut.conj c).toMonoidHom = P.map (MulAut.conj t).toMonoidHom)
    (hct : c * t = t * c) (hcK : c ∈ centralizer ((swapDiag P t hc).range : Set G)) :
    t * c ∈ centralizer (P : Set G) := by
  have hmap : P.map (MulAut.conj (t * c)).toMonoidHom = P := by
    rw [map_mul]
    change P.map ((MulAut.conj t).toMonoidHom.comp (MulAut.conj c).toMonoidHom) = P
    rw [← Subgroup.map_map, hcP, map_conj_map_conj_eq_self ht P]
  have hct' : (t * c) * t = t * (t * c) := by
    rw [mul_assoc, hct]
  have hcK' : t * c ∈ centralizer ((swapDiag P t hc).range : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hcK ⊢
    have htK : ∀ y ∈ (swapDiag P t hc).range, y * t = t * y := by
      intro y hy
      obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hy
      have h := conj_swapDiag P ht hc k
      rw [MulAut.conj_apply] at h
      calc (swapDiag P t hc k) * t =
            (t * (swapDiag P t hc k) * t⁻¹) * t := by rw [h]
        _ = t * (swapDiag P t hc k) := by group
    intro x hx
    calc x * (t * c) = (x * t) * c := by group
      _ = (t * x) * c := by rw [htK x hx]
      _ = t * (x * c) := by group
      _ = t * (c * x) := by rw [hcK x hx]
      _ = (t * c) * x := by group
  exact mem_centralizer_of_map_conj_eq hc hP hmap hct' hcK'

theorem conj_eq_of_mem_center_of_odd [Finite G] {P : Subgroup G} {t : G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hodd : Odd (Nat.card (center ↥(swapDiag P t hc).range))) {z : G} (hzP : z ∈ P)
    (hzc : z ∈ centralizer (P : Set G)) (hz : z * z = 1) : t * z * t⁻¹ = z := by
  have hzcenter : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro p
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc (p : G) p.2)
  set u : ↥(swapDiag P t hc).range :=
    (swapDiag P t hc).rangeRestrict ⟨z, hzP⟩ with hu
  have hu_mem : u ∈ Subgroup.center ↥(swapDiag P t hc).range := by
    have hmap := Subgroup.map_center_le_center
      (f := (swapDiag P t hc).rangeRestrict) (swapDiag P t hc).rangeRestrict_surjective
    exact hmap (Subgroup.mem_map.mpr ⟨⟨z, hzP⟩, hzcenter, rfl⟩)
  have hφz_sq : ((swapDiag P t hc) ⟨z, hzP⟩) * ((swapDiag P t hc) ⟨z, hzP⟩) = 1 := by
    rw [swapDiag_apply]
    have hz_comm : z * MulAut.conj t z = MulAut.conj t z * z :=
      (Subgroup.mem_centralizer_iff.mp (hc hzP) _
        (Subgroup.mem_map_of_mem _ hzP)).symm
    have hzt_sq : MulAut.conj t z * MulAut.conj t z = 1 := by
      have h := congrArg (MulAut.conj t) hz
      simpa [map_mul] using h
    calc z * MulAut.conj t z * (z * MulAut.conj t z)
        = z * (MulAut.conj t z * z) * MulAut.conj t z := by group
      _ = z * (z * MulAut.conj t z) * MulAut.conj t z := by rw [← hz_comm]
      _ = (z * z) * (MulAut.conj t z * MulAut.conj t z) := by group
      _ = 1 := by rw [hz, hzt_sq, mul_one]
  have hu_sq : u * u = 1 := by
    rw [hu]
    apply Subtype.ext
    exact hφz_sq
  have hdvd : orderOf u ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hu_sq
  have hodd' : Odd (orderOf u) :=
    Odd.of_dvd_nat hodd
      (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥(swapDiag P t hc).range) hu_mem)
  have hu1 : u = 1 :=
    orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Odd.coprime_two_right hodd') hdvd)
  have hzz : z * MulAut.conj t z = 1 := by
    have h := congrArg Subtype.val hu1
    simpa [hu, swapDiag_apply] using h
  rw [← MulAut.conj_apply, ← inv_eq_of_mul_eq_one_right hzz,
    inv_eq_of_mul_eq_one_right hz]

theorem range_swapDiag_map_conj {P : Subgroup G} {t g : G} (hgt : g * t = t * g)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    (swapDiag (P.map (MulAut.conj g).toMonoidHom) t
        (map_conj_le_centralizer_map hgt hc)).range =
      (swapDiag P t hc).range.map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨p, hp, hxp⟩ := Subgroup.mem_map.mp x.2
    have hx : (⟨MulAut.conj g p, Subgroup.mem_map_of_mem _ hp⟩ : ↥(P.map
        (MulAut.conj g).toMonoidHom)) = x := Subtype.ext hxp
    refine Subgroup.mem_map.mpr ⟨(swapDiag P t hc) ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, ?_⟩
    rw [← hx]
    exact (swapDiag_map_conj_apply hgt hc hp).symm
  · rintro _ ⟨y, ⟨⟨p, hp⟩, rfl⟩, rfl⟩
    refine ⟨⟨MulAut.conj g p, Subgroup.mem_map_of_mem _ hp⟩, ?_⟩
    exact swapDiag_map_conj_apply hgt hc hp

theorem eq_or_eq_map_of_range_swapDiag_eq [Finite G] {X P Q : Subgroup G} {t : G}
    (ht : t ^ 2 = 1) (htX : t ∈ normalizer (X : Set G)) (hP : IsCompIn P X) (hQ : IsCompIn Q X)
    (hcP : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hcQ : Q ≤ centralizer ((Q.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (heq : (swapDiag Q t hcQ).range = (swapDiag P t hcP).range)
    (hnab : ∃ a ∈ (swapDiag P t hcP).range, ∃ b ∈ (swapDiag P t hcP).range, a * b ≠ b * a) :
    Q = P ∨ Q = P.map (MulAut.conj t).toMonoidHom := by
  have htXmap : X.map (MulAut.conj t).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htX
  have hXconj : CFSG.conjugate X t⁻¹ = X := by
    simpa [CFSG.conjugate] using htXmap
  have hPt : IsCompIn (P.map (MulAut.conj t).toMonoidHom) X := by
    have h := hP.cj t⁻¹
    rw [hXconj] at h
    simpa [CFSG.conjugate] using h
  have hQt : IsCompIn (Q.map (MulAut.conj t).toMonoidHom) X := by
    have h := hQ.cj t⁻¹
    rw [hXconj] at h
    simpa [CFSG.conjugate] using h
  by_contra hcon
  push Not at hcon
  have hQt_ne_P : Q.map (MulAut.conj t).toMonoidHom ≠ P := by
    intro hEq
    apply hcon.2
    have h := congrArg (fun H : Subgroup G => H.map (MulAut.conj t).toMonoidHom) hEq
    rwa [map_conj_map_conj_eq_self ht Q] at h
  have hQt_ne_Pt : Q.map (MulAut.conj t).toMonoidHom ≠
      P.map (MulAut.conj t).toMonoidHom := by
    intro hEq
    apply hcon.1
    have h := congrArg (fun H : Subgroup G => H.map (MulAut.conj t).toMonoidHom) hEq
    rwa [map_conj_map_conj_eq_self ht Q, map_conj_map_conj_eq_self ht P] at h
  have hPQ : P ≤ centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.CGT.PushingUpLit.CGT6.Nine7.commute_of_isCompIn_ne hP hQ (Ne.symm hcon.1))
  have hPQt : P ≤ centralizer ((Q.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.CGT.PushingUpLit.CGT6.Nine7.commute_of_isCompIn_ne hP hQt
        (Ne.symm hQt_ne_P))
  have hPtQ : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.CGT.PushingUpLit.CGT6.Nine7.commute_of_isCompIn_ne hPt hQ
        (Ne.symm hcon.2))
  have hPtQt : P.map (MulAut.conj t).toMonoidHom ≤
      centralizer ((Q.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.CGT.PushingUpLit.CGT6.Nine7.commute_of_isCompIn_ne hPt hQt
        (Ne.symm hQt_ne_Pt))
  have hPcen : P ≤ centralizer
      ((Q ⊔ Q.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hPQ hPQt
  have hPtcen : P.map (MulAut.conj t).toMonoidHom ≤ centralizer
      ((Q ⊔ Q.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hPtQ hPtQt
  have hKle : (swapDiag P t hcP).range ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom :=
    range_swapDiag_le_sup P t hcP
  have hKC : (swapDiag P t hcP).range ≤ centralizer
      ((Q ⊔ Q.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    hKle.trans (sup_le hPcen hPtcen)
  have hKQ : (swapDiag P t hcP).range ≤ Q ⊔ Q.map (MulAut.conj t).toMonoidHom := by
    rw [← heq]
    exact range_swapDiag_le_sup Q t hcQ
  have hKCK : (swapDiag P t hcP).range ≤
      centralizer ((swapDiag P t hcP).range : Set G) :=
    hKC.trans (Subgroup.centralizer_le hKQ)
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  exact hab (Subgroup.mem_centralizer_iff.mp (hKCK ha) b hb).symm

end CFSG.ComponentClassification.HarrisLit
