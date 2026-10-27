module

public import CFSG.GF2Type.Aschbacher1976Full.HSBurnsideLayer2
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCardSylow
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCardBound
public import CFSG.GF2Type.Aschbacher1976Full.WidthZ1

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

namespace Card

variable {G : Type} [Group G] [Finite G]

theorem ZF_inv_conj_eq {z : G} {w : ℕ} {Z A : Subgroup G} (hD : Width.Z4Data z w Z A)
    (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) (g : G) :
    ZF (g⁻¹ * z * g) = conjugate Z g := by
  show centerAt (g⁻¹ * z * g) = conjugate Z g
  rw [centerAt_conj z g]
  exact congrArg (fun K => conjugate K g)
    (Subgroup.ext fun _ => Width.mem_centerAt_iff hD hz hF2)

theorem isPGroup_ZF {z u : G} {w : ℕ} {Z A : Subgroup G} (hD : Width.Z4Data z w Z A)
    (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) (hu : IsConj z u) : IsPGroup 2 ↥(ZF u) := by
  obtain ⟨g, rfl⟩ := BL.exists_inv_conj hu
  rw [ZF_inv_conj_eq hD hz hF2]
  exact IsPGroup.of_card (n := 2) (by rw [Width.card_conjugate', hD.card_Z]; norm_num)

theorem three_le_card {E : Subgroup G} {a b c : G} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card E := by
  have h3 : ({a, b, c} : Set G).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Set G) ⊆ (E : Set G) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3] at h
  have e : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  omega

theorem eq_four_or_eight {n : ℕ} (h3 : 3 ≤ 2 ^ n) (h8 : 2 ^ n ≤ 8) : 2 ^ n = 4 ∨ 2 ^ n = 8 := by
  have hn : n ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> simp_all

end Card

theorem hsPartCard_holds : HSPartCard := by
  intro G _ _ z hset hti
  obtain ⟨⟨-, -, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 (Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  obtain ⟨u, hucj, hunz, huH⟩ := hti.1
  have hK2 : IsPGroup 2 ↥(ZF u ⊔ Fz z) :=
    (Card.isPGroup_ZF hD hz hF2 hucj).to_sup_of_normal_right' hF2 (Card.le_normalizer_Fz huH)
  obtain ⟨T, hKT, hTH⟩ := Card.exists_sylow hD hz hF2 le_sup_right
    (sup_le huH (Card.Fz_le_Hz z)) hK2
  have c : BL.Ctx z 2 Z A T := ⟨hD, hz, hF2, hTH⟩
  refine ⟨T, hTH, ?_⟩
  have hETF : ET (T : Subgroup G) z ≤ Fz z := by
    intro x hx
    rcases (c.mem_ET_iff hti).mp hx with rfl | hx
    · exact (Fz z).one_mem
    · exact c.VS_subset_F hti hx
  have hETel : CFSG.Open.IsElemAbelian 2 (ET (T : Subgroup G) z) := by
    refine And.intro ⟨⟨fun a b => Subtype.ext ?_⟩⟩ ?_
    · exact c.WZ_comm a.1 (c.mem_WZ_of_mem_ET hti a.2) b.1 (c.mem_WZ_of_mem_ET hti b.2)
    · intro x hx
      rcases (c.mem_ET_iff hti).mp hx with rfl | hx
      · exact one_pow 2
      · rw [sq]
        exact BL.mul_self_of_isConj hz hx.1
  have hle8 : Nat.card ↥(ET (T : Subgroup G) z) ≤ 2 ^ 3 :=
    Card.card_elemAbelian_le hD hz hETF hETel
  have hz_mem : z ∈ ET (T : Subgroup G) z :=
    Subgroup.subset_closure ⟨IsConj.refl z, by rw [c.ZF_self]; exact c.Z_le_T⟩
  have hu_mem : u ∈ ET (T : Subgroup G) z :=
    Subgroup.subset_closure ⟨hucj, le_sup_left.trans hKT⟩
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have h3 : 3 ≤ Nat.card ↥(ET (T : Subgroup G) z) :=
    Card.three_le_card (one_mem _) hz_mem hu_mem hz1.symm (BL.ne_one_of_isConj hz hucj).symm
      hunz.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hF2.to_le hETF)
  rw [hn] at h3 hle8 ⊢
  exact Card.eq_four_or_eight h3 hle8

end CFSG.GF2Type.Aschbacher1976Full.HS
