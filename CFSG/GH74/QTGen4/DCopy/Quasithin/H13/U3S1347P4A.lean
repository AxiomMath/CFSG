module

public import CFSG.Quasithin.H13.U3S1347P4A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_a6_of_K2_F4 (h1332 : Stmt13_3_2_F4)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂ : oTwoRes H₂ = l2Of S) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨h5, -, -, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  rcases a6_or_hatA6_of_isA6On S.frame.L_le (s134_pCoreOf_L_le S) h5 (s134_isA6On S) with
    he | hhat
  · exact he
  exfalso
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := exists_l0_c hhat.2.1
  have hcZ : c ∈ o2Z L := oTwoRes_le _ hcl0
  have hcC : c ∈ centralizer (V : Set G) := s134_o2Z_le_centralizer S hcZ
  have hcN : c ∈ normalizer (V : Set G) := S.frame.L_le (o2Z_le_L hcZ)
  have hcH : c ∈ H₂ := by
    have hcL2 : c ∈ l2Of S := by
      refine A6.oTwoRes_mono (fun y hy => mem_inf.2 ⟨o2Z_le_L hy, ?_⟩) hcl0
      exact centralizer_le_normalizer _ (centralizer_le
        (SetLike.coe_subset_coe.2 (S.pre_le_V _)) (s134_o2Z_le_centralizer S hy))
    rw [← hK₂] at hcL2
    exact oTwoRes_le _ hcL2

  set P : Subgroup G := (D6sub.comap S.frame.ρ).map (normalizer (V : Set G)).subtype with hP
  have hTP : T ≤ P := fun t ht => ⟨⟨t, S.frame.T_le ht⟩, S.frame.T_D _ ht, rfl⟩
  have hcP : c ∈ P := by
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    show S.frame.ρ ⟨c, hcN⟩ ∈ D6sub
    rw [(s134_rho_eq_one_iff S ⟨c, hcN⟩).2 hcC]
    exact one_mem _
  set X := T ⊔ zpowers c with hX
  have hXP : X ≤ P := sup_le hTP (zpowers_le.2 hcP)
  have hXH : X ≤ H₂ := sup_le h.inH₂.1 (zpowers_le.2 hcH)
  have h3 := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hm := relIndex_mul_relIndex T X H₂ le_sup_left hXH
  rw [h3] at hm
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hm) with h1 | h1
  ·
    have hcT : c ∈ T := relIndex_eq_one.1 h1 (mem_sup_right (mem_zpowers c))
    apply hcO
    have hco : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.h13.sylow.1) ⟨c, hcT⟩
    have hk' : orderOf c = 2 ^ k := (Subgroup.orderOf_coe ⟨c, hcT⟩).trans hk
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans (hk' ▸ hco)
      omega
    have hc1 : c = 1 := orderOf_eq_one_iff.1 (by rw [hk', hk0, pow_zero])
    rw [hc1]
    exact one_mem _
  ·
    rw [h1] at hm
    have h2 : X.relIndex H₂ = 1 := by omega
    obtain ⟨y, hyL2, hyN, hyρ⟩ := s134_exists_c2_mem_L2 S
    rw [← hK₂] at hyL2
    obtain ⟨y', hy', hyy'⟩ := hXP (relIndex_eq_one.1 h2 (oTwoRes_le _ hyL2))
    have e : y' = ⟨y, hyN⟩ := Subtype.ext hyy'
    have hD : InD6 (S.frame.ρ y') := hy'
    rw [e, hyρ] at hD
    exact c2perm_not_inD6 hD

end CFSG.Quasithin.H13.U3
