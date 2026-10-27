module

public import CFSG.GF2Type.Aschbacher1976Full.HSBurnsideLayer2
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCGen
public import CFSG.GF2Type.Aschbacher1976Full.HSTransYV

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransY

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G] {z : G} {Z A : Subgroup G} {T : Sylow 2 G}

theorem elemV (c : BL.Ctx z 2 Z A T) (hti : HSTI z)
    (hcard : Nat.card (ET (T : Subgroup G) z) = 8) : ElemV z (ET (T : Subgroup G) z) where
  comm a ha b hb := c.WZ_comm a (c.mem_WZ_of_mem_ET hti ha) b (c.mem_WZ_of_mem_ET hti hb)
  sq a ha := by
    rcases (c.mem_ET_iff hti).mp ha with rfl | ha
    · exact one_mul 1
    · exact BL.mul_self_of_isConj c.hz ha.1
  card_eq := hcard
  le_F a ha := by
    rcases (c.mem_ET_iff hti).mp ha with rfl | ha
    · exact (Fz z).one_mem
    · exact c.VS_subset_F hti ha
  z_mem := Subgroup.subset_closure ⟨IsConj.refl z, by rw [c.ZF_self]; exact c.Z_le_T⟩

theorem sq_mem_ET (c : BL.Ctx z 2 Z A T) {g b : G} (hgT : conjugate Z g ≤ (T : Subgroup G))
    (hb : b ∈ conjugate Z g) : b * b ∈ ET (T : Subgroup G) z := by
  have hx : g * b * g⁻¹ ∈ Z := Width.mem_conjugate_iff.mp hb
  have hbb : b * b = g⁻¹ * (g * b * g⁻¹) ^ 2 * g := by rw [pow_two]; group
  rcases Width.sq_F c.hD c.hz (c.Z_le_F hx) with h | h
  · rw [hbb, h, mul_one, inv_mul_cancel]
    exact one_mem _
  · rw [hbb, h]
    exact Subgroup.subset_closure
      ⟨isConj_iff.mpr ⟨g⁻¹, by group⟩, by rw [c.ZF_conj_eq]; exact hgT⟩

theorem sq_mem_of_mem_WZ (c : BL.Ctx z 2 Z A T) {x : G} (hx : x ∈ BL.WZ Z (T : Subgroup G)) :
    x * x ∈ ET (T : Subgroup G) z := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ BL.WZ Z (T : Subgroup G) ∧ x * x ∈ ET (T : Subgroup G) z}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, ?_⟩
        have hab : Commute b a := c.WZ_comm b hb.1 a ha.1
        rw [hab.mul_mul_mul_comm a b]
        exact mul_mem ha.2 hb.2
      one_mem' := ⟨one_mem _, by rw [mul_one]; exact one_mem _⟩
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, ?_⟩
        rw [← mul_inv_rev]
        exact inv_mem ha.2 }
  have hle : BL.WZ Z (T : Subgroup G) ≤ S := by
    refine iSup₂_le fun B hB => ?_
    obtain ⟨g, rfl, hgT⟩ := hB
    exact fun b hb => ⟨BL.le_WZ ⟨g, rfl, hgT⟩ hb, sq_mem_ET c hgT hb⟩
  exact (hle hx).2

theorem exists_sq_mem_WZ (c : BL.Ctx z 2 Z A T) (hti : HSTI z) {v : G}
    (hv : v ∈ ET (T : Subgroup G) z) : ∃ y ∈ BL.WZ Z (T : Subgroup G), y * y = v := by
  rcases (c.mem_ET_iff hti).mp hv with rfl | hvS
  · exact ⟨1, one_mem _, one_mul 1⟩
  · obtain ⟨y, hy⟩ := PartC.exists_gen c.hD c.hz c.hF2 hvS.1
    refine ⟨y, c.ZF_le_WZ hvS (hy ▸ Subgroup.mem_zpowers y), ?_⟩
    rw [← pow_two]
    exact (PartC.gen_props c.hD c.hz c.hF2 hvS.1 hy).2

theorem sixtyfour_le_card_WZ (c : BL.Ctx z 2 Z A T) (hti : HSTI z)
    (hcard : Nat.card (ET (T : Subgroup G) z) = 8) :
    64 ≤ Nat.card (BL.WZ Z (T : Subgroup G)) := by
  set W := BL.WZ Z (T : Subgroup G) with hW
  let φ : ↥W →* ↥W := MonoidHom.mk' (fun x => x * x) (fun a b => by
    have hab : Commute b a := Subtype.ext (c.WZ_comm b b.2 a a.2)
    exact hab.mul_mul_mul_comm a b)
  have hVW : ET (T : Subgroup G) z ≤ W := fun x hx => c.mem_WZ_of_mem_ET hti hx
  have hcardV : Nat.card ((ET (T : Subgroup G) z).subgroupOf W) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv, hcard]
  have hker : (ET (T : Subgroup G) z).subgroupOf W ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    show (x : G) * (x : G) = 1
    exact (elemV c hti hcard).sq _ hx
  have hrange : (ET (T : Subgroup G) z).subgroupOf W ≤ φ.range := by
    intro x hx
    obtain ⟨y, hyW, hy⟩ := exists_sq_mem_WZ c hti hx
    exact ⟨⟨y, hyW⟩, Subtype.ext hy⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : 8 ≤ Nat.card φ.ker := hcardV ▸ Subgroup.card_le_of_le hker
  have h3 : 8 ≤ Nat.card φ.range := hcardV ▸ Subgroup.card_le_of_le hrange
  nlinarith

theorem card_WZ_ge (c : BL.Ctx z 2 Z A T) (hti : HSTI z)
    (hcard : Nat.card (ET (T : Subgroup G) z) = 8)
    (hne : Nat.card (BL.WZ Z (T : Subgroup G)) ≠ 64) :
    128 ≤ Nat.card (BL.WZ Z (T : Subgroup G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 (BL.WZ Z (T : Subgroup G)) := T.isPGroup'.to_le BL.WZ_le
  obtain ⟨m, hm⟩ := hW2.exists_card_eq
  have h64 := sixtyfour_le_card_WZ c hti hcard
  rw [hm] at h64 hne ⊢
  by_contra hlt
  push Not at hlt
  have hm6 : m ≤ 6 := by
    by_contra h
    push Not at h
    have : 2 ^ 7 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hm6' : 6 ≤ m := by
    by_contra h
    push Not at h
    have : 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : m = 6 := by omega
  subst this
  exact hne (by norm_num)

theorem conj_mem_WZ (c : BL.Ctx z 2 Z A T) (hti : HSTI z) {n : G}
    (hn : n ∈ Subgroup.normalizer (ET (T : Subgroup G) z : Set G)) {x : G}
    (hx : x ∈ BL.WZ Z (T : Subgroup G)) : n * x * n⁻¹ ∈ BL.WZ Z (T : Subgroup G) := by
  have hle : BL.WZ Z (T : Subgroup G) ≤
      (BL.WZ Z (T : Subgroup G)).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun B hB => ?_
    obtain ⟨g, rfl, hgT⟩ := hB
    intro b hb
    rw [Subgroup.mem_comap]
    show n * b * n⁻¹ ∈ BL.WZ Z (T : Subgroup G)
    have hu : g⁻¹ * z * g ∈ ET (T : Subgroup G) z :=
      Subgroup.subset_closure ⟨isConj_iff.mpr ⟨g⁻¹, by group⟩, by rw [c.ZF_conj_eq]; exact hgT⟩
    have hnu : n * (g⁻¹ * z * g) * n⁻¹ ∈ ET (T : Subgroup G) z :=
      (Subgroup.mem_normalizer_iff.mp hn _).mp hu
    have hu1 : g⁻¹ * z * g ≠ 1 := BL.ne_one_of_isConj c.hz (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    have hnu1 : n * (g⁻¹ * z * g) * n⁻¹ ≠ 1 := by
      intro h
      apply hu1
      calc g⁻¹ * z * g = n⁻¹ * (n * (g⁻¹ * z * g) * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    have hnuS := ((c.mem_ET_iff hti).mp hnu).resolve_left hnu1
    refine c.ZF_le_WZ hnuS ?_
    rw [PartC.mem_ZF_conj_iff, show n⁻¹ * (n * b * n⁻¹) * n = b by group, c.ZF_conj_eq]
    exact hb
  simpa using hle hx

end CFSG.GF2Type.Aschbacher1976Full.HS.TransY
