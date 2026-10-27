module

public import CFSG.GH74.QTGen4.U42.GSideCoords
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

variable {G : Type} [Group G] [Finite G] {T L V H I : Subgroup G}

theorem H_eq_sup_B (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I) :
    H = I ⊔ (H ⊓ (L ⊔ T)) := by
  have hL1B : S.L1 ≤ H ⊓ (L ⊔ T) := by
    refine le_inf ?_ (S.L1_le_L.trans le_sup_left)
    rw [D.H_eq_gen]
    exact le_sup_of_le_left le_sup_left
  have hTB : T ≤ H ⊓ (L ⊔ T) := le_inf (S.T_le_H hH) le_sup_right
  have hsup : S.L1 ⊔ I ⊔ T ≤ I ⊔ (H ⊓ (L ⊔ T)) :=
    sup_le (sup_le (hL1B.trans le_sup_right) le_sup_left) (hTB.trans le_sup_right)
  exact le_antisymm (D.H_eq_gen.le.trans hsup) (sup_le D.I_le inf_le_left)

theorem card_H_eq_three_mul_B (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I) :
    Nat.card ↥H = 3 * Nat.card ↥(H ⊓ (L ⊔ T)) := by
  have hHM : ¬ H ≤ L ⊔ T := by
    rw [← D.M_eq]
    exact hH.2.2
  have hIM : ¬ I ≤ L ⊔ T := fun h =>
    hHM ((H_eq_sup_B S hH D).le.trans (sup_le h inf_le_right))
  have hdvdT : Nat.card ↥(T ⊓ I) ∣ Nat.card ↥(I ⊓ (L ⊔ T)) :=
    Subgroup.card_dvd_of_le (le_inf inf_le_right (inf_le_left.trans le_sup_right))
  have hdvdI : Nat.card ↥(I ⊓ (L ⊔ T)) ∣ Nat.card ↥I :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [S.card_inf_I hH D] at hdvdT
  rw [S.card_I D] at hdvdI
  have hJ : Nat.card ↥(I ⊓ (L ⊔ T)) = 64 := by
    obtain ⟨k, hk⟩ := hdvdT
    obtain ⟨m, hm⟩ := hdvdI
    have hkm : k * m = 3 := by
      have h64 : 64 * (k * m) = 64 * 3 := by
        rw [hk] at hm
        linarith
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h64
    have hk3 : k ∣ 3 := ⟨m, hkm.symm⟩
    have hk_le : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk3
    interval_cases k
    · simp at hkm
    · omega
    · norm_num at hk3
    · exfalso
      have hcard : Nat.card ↥I ≤ Nat.card ↥(I ⊓ (L ⊔ T)) := by
        rw [S.card_I D]
        omega
      have heq : I ⊓ (L ⊔ T) = I := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
      exact hIM (by rw [← heq]; exact inf_le_right)
  haveI : (I.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer D.I_le).mpr D.I_normal
  have hinf : ∀ X Y : Subgroup G, (X ⊓ Y).subgroupOf H = X.subgroupOf H ⊓ Y.subgroupOf H :=
    fun X Y => by
      ext x
      simp [Subgroup.mem_subgroupOf]
  have hBH : H ⊓ (L ⊔ T) ⊔ I = H := (sup_comm _ _).trans (H_eq_sup_B S hH D).symm
  have hsup : (H ⊓ (L ⊔ T)).subgroupOf H ⊔ I.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (show H ⊓ (L ⊔ T) ≤ H from inf_le_left) D.I_le, hBH,
      Subgroup.subgroupOf_self]
  have hcardA : Nat.card ↥((H ⊓ (L ⊔ T)).subgroupOf H) = Nat.card ↥(H ⊓ (L ⊔ T)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show H ⊓ (L ⊔ T) ≤ H from inf_le_left)).toEquiv
  have hcardL : Nat.card ↥(I.subgroupOf H) = 192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.I_le).toEquiv, S.card_I D]
  have hZ : (H ⊓ (L ⊔ T)) ⊓ I = I ⊓ (L ⊔ T) :=
    le_antisymm (fun x hx => ⟨hx.2, hx.1.2⟩) (fun x hx => ⟨⟨D.I_le hx.1, hx.2⟩, hx.1⟩)
  have hcardAL : Nat.card ↥((H ⊓ (L ⊔ T)).subgroupOf H ⊓ I.subgroupOf H) = 64 := by
    rw [← hinf, hZ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show I ⊓ (L ⊔ T) ≤ H from
        inf_le_left.trans D.I_le)).toEquiv, hJ]
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_normal
    ((H ⊓ (L ⊔ T)).subgroupOf H) (I.subgroupOf H)
  rw [hsup, Subgroup.card_top, hcardAL, hcardA, hcardL] at hprod
  omega

theorem mem_H_iff_fix_four (S : A5.Setting G T L V) (hH : H ∈ S.Hz) (D : Data13515 S H I)
    (m : ↥(L ⊔ T)) :
    (m : G) ∈ H ↔ S.frame.ρ ⟨(m : G), LT_le_normalizer S m.2⟩ 4 = 4 := by
  have hmN := LT_le_normalizer S m.2
  rw [D.H_eq]
  show (m : G) ∈ Subgroup.centralizer ({S.z} : Set G) ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine S.rho_four_of_conj_z hmN ?_
    calc (m : G) * S.z * (m : G)⁻¹ = S.z * (m : G) * (m : G)⁻¹ := by rw [h]
      _ = S.z := by group
  · intro h
    have h1 : (m : G) * S.z * (m : G)⁻¹ = S.z :=
      (S.conj_eq_iff ⟨(m : G), hmN⟩ ⟨S.z, S.z_mem_V⟩).2 (by rw [S.psi_z]; exact pact_W4 h)
    calc (m : G) * S.z = ((m : G) * S.z * (m : G)⁻¹) * (m : G) := by group
      _ = S.z * (m : G) := by rw [h1]

end CFSG.GH74.QTGen4.U42
