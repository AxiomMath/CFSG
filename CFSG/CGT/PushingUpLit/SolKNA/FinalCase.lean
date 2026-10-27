module

public import CFSG.CGT.PushingUpLit.SolKNA.FinalCaseB
public import CFSG.RankThree.GF2n.Tim78S31Core

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G]

theorem false_of_isolated [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) : False := by
  classical
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hN, hodd, hcomm⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hiso
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [← sq] at ht2) ht1
  have heven : Even (Nat.card G) := by
    rw [even_iff_two_dvd, ← hord]
    exact orderOf_dvd_natCard t
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hcent : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hcomm g
      rw [hbot, Subgroup.mem_bot] at h1
      calc g * t = (g * t * g⁻¹ * t⁻¹) * t * g := by group
        _ = t * g := by rw [h1]; group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · rw [hc, Subgroup.mem_bot] at hcent
      exact ht1 hcent
    · obtain ⟨a, b, hab⟩ := hnab
      have : a ∈ Subgroup.center G := by rw [hc]; trivial
      rw [Subgroup.mem_center_iff] at this
      exact hab (this b).symm
  · rw [htop, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven

def zGen (R : Subgroup G) : Subgroup G :=
  ⨆ (k : G) (_ : conjSubgroup k (zCenter R) ≤ Subgroup.normalizer (R : Set G)),
    conjSubgroup k (zCenter R)

theorem le_zGen {R : Subgroup G} {k : G}
    (hk : conjSubgroup k (zCenter R) ≤ Subgroup.normalizer (R : Set G)) :
    conjSubgroup k (zCenter R) ≤ zGen R :=
  le_iSup₂ (f := fun k (_ : conjSubgroup k (zCenter R) ≤ Subgroup.normalizer (R : Set G)) =>
    conjSubgroup k (zCenter R)) k hk

theorem conj_zGen_le {R : Subgroup G} {g : G}
    (hg : ∀ k : G, conjSubgroup k (zCenter R) ≤ Subgroup.normalizer (R : Set G) →
      conjSubgroup (g * k) (zCenter R) ≤ Subgroup.normalizer (R : Set G)) :
    conjSubgroup g (zGen R) ≤ zGen R := by
  unfold zGen
  rw [conjSubgroup, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun k hk => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  show conjSubgroup g (conjSubgroup k (zCenter R)) ≤ _
  rw [← conjSubgroup_mul]
  exact le_iSup₂ (f := fun k (_ : conjSubgroup k (zCenter R) ≤
    Subgroup.normalizer (R : Set G)) => conjSubgroup k (zCenter R)) (g * k) (hg k hk)

theorem normalizer_le_normalizer_zGen [Finite G] (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (zGen R : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff]
  refine Subgroup.eq_of_le_of_card_ge (conj_zGen_le fun k hk => ?_)
    (by rw [CFSG.RankThree.GF2n.card_conjSubgroup])
  rw [conjSubgroup_mul]
  calc conjSubgroup m (conjSubgroup k (zCenter R)) ≤ conjSubgroup m (Subgroup.normalizer
        (R : Set G)) := Subgroup.map_mono hk
    _ = Subgroup.normalizer (R : Set G) :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hm)

namespace FinalCase

variable [Finite G] {R : Subgroup G} {z : G} (F : FinalCase G R z)
include F

theorem zGen_comm_pGroup :
    (∀ x ∈ zGen R, ∀ y ∈ zGen R, x * y = y * x) ∧ IsPGroup 2 ↥(zGen R) := by
  have hW : zGen R = ⨆ i : {k : G // conjSubgroup k (zCenter R) ≤
      Subgroup.normalizer (R : Set G)}, conjSubgroup i.1 (zCenter R) := by
    unfold zGen
    exact iSup_subtype'
  rw [hW]
  exact iSup_comm_pGroup _ (fun i => F.isPGroup_Z.map (MulAut.conj i.1).toMonoidHom)
    (fun i j a ha b hb => F.Z_comm_of_le i.2 j.2 a ha b hb)

theorem conj_inv_mul_le {g k : G}
    (hg : conjSubgroup g (zCenter R) ≤ Subgroup.normalizer (R : Set G))
    (hk : conjSubgroup k (zCenter R) ≤ Subgroup.normalizer (R : Set G)) :
    conjSubgroup (g⁻¹ * k) (zCenter R) ≤ Subgroup.normalizer (R : Set G) := by
  intro w hw
  rw [mem_conjSubgroup] at hw
  have hx : g * w * g⁻¹ ∈ conjSubgroup k (zCenter R) := by
    rw [mem_conjSubgroup, show k⁻¹ * (g * w * g⁻¹) * k = (g⁻¹ * k)⁻¹ * w * (g⁻¹ * k) by group]
    exact hw
  have hzg : g * z * g⁻¹ ∈ conjSubgroup g (zCenter R) := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact F.z_mem
  have hcomm := F.Z_comm_of_le hk hg _ hx _ hzg
  have hwz : w * z = z * w := by
    calc w * z = g⁻¹ * ((g * w * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * w * g⁻¹)) * g := by rw [hcomm]
      _ = z * w := by group
  rw [← F.cent_z]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hwz

theorem mem_normalizer_of_conj_Z_le {g : G}
    (hg : conjSubgroup g (zCenter R) ≤ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer (R : Set G) := by
  have h1 : g⁻¹ ∈ Subgroup.normalizer (zGen R : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    exact Subgroup.eq_of_le_of_card_ge (conj_zGen_le fun k hk => F.conj_inv_mul_le hg hk)
      (by rw [CFSG.RankThree.GF2n.card_conjSubgroup])
  have h2 : g ∈ Subgroup.normalizer (zGen R : Set G) := by
    simpa using (Subgroup.normalizer (zGen R : Set G)).inv_mem h1
  have hWne : zGen R ≠ ⊥ := by
    intro hbot
    apply F.Z_ne_bot
    have hZW : zCenter R ≤ zGen R := by
      have := le_zGen (R := R) (k := 1) (by
        rw [CFSG.RankThree.GF2n.conjSubgroup_one]
        exact (inf_le_left.trans Subgroup.le_normalizer))
      rwa [CFSG.RankThree.GF2n.conjSubgroup_one] at this
    rw [hbot] at hZW
    exact le_bot_iff.mp hZW
  have hN : Subgroup.normalizer (zGen R : Set G) = Subgroup.normalizer (R : Set G) := by
    by_contra hne
    exact F.max.2 _ (lt_of_le_of_ne (normalizer_le_normalizer_zGen R) (Ne.symm hne))
      ⟨zGen R, hWne, F.zGen_comm_pGroup.2, rfl⟩
  rw [← hN]
  exact h2

theorem false : False := by
  refine false_of_isolated F.simple F.nonab F.z_ne (F.Z_sq z F.z_mem) fun g hg => ?_
  have hgz : g * z * g⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
    rw [← F.cent_z]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hg
  have hgM := F.mem_normalizer_of_conj_Z_le (F.conj_Z_le_normalizer hgz)
  rw [← F.cent_z] at hgM
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hgM
  calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hc]
    _ = z := by group

end FinalCase

end CFSG.CGT.PushingUpLit.SolKNA
