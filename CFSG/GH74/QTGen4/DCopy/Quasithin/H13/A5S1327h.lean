module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327dS331
public import CFSG.Quasithin.H13.A5S1327h

public section
namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

variable (S : Setting G T L V)
include S

theorem exists_R1_not_comm_F4 (h331 : Stmt3_3_1_F4)
    (h311 : Theorem311Stmt) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc) :
    ∃ r : ↥(S.H0 H), (r : G) ∈ S.R1 ∧ ∃ z ∈ Zc,
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) r * z *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) r)⁻¹ ≠ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N3 := CFSG.pPrimeCore 3 ↥(S.H0 H) with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hTH : T ≤ H := hH.1.1
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  by_contra hall
  push Not at hall
  by_cases hPR : pCoreOf 2 H ⊓ oTwoUpper H ≤ S.R1
  · exact S.false_of_P_le_R1_F4 h331 h311 hH hHZ hsolv hS3 hPR
  obtain ⟨p, hpP, hpR⟩ := IsConcreteLE.not_le_iff_exists.1 hPR
  have hpT : p ∈ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH) hpP.1
  have hpZ : ∀ z ∈ Zc, π ⟨p, hTI hpT⟩ * z * (π ⟨p, hTI hpT⟩)⁻¹ = z := by
    have hmem : π ⟨p, hTI hpT⟩ ∈ K ⊔ Zc := by
      rw [hc.sup_eq]
      exact S.map_oTwoUpper_le hpP.2
    obtain ⟨k, hk, z', hz', he⟩ := exists_mul_of_mem_sup_comm hc.comm hmem
    intro z hz
    rw [he]
    have h1 : k * z = z * k := hc.comm k hk z hz
    have h2 : z' * z = z * z' := comm_of_card_three hc.card_Zc hz' hz
    calc k * z' * z * (k * z')⁻¹ = k * (z' * z) * z'⁻¹ * k⁻¹ := by group
      _ = k * (z * z') * z'⁻¹ * k⁻¹ := by rw [h2]
      _ = k * z * k⁻¹ := by group
      _ = z := by rw [h1]; group
  have hTZ : ∀ (t : G) (ht : t ∈ T), ∀ z ∈ Zc, π ⟨t, hTI ht⟩ * z * (π ⟨t, hTI ht⟩)⁻¹ = z := by
    intro t ht z hz
    by_cases htR : t ∈ S.R1
    · exact hall ⟨t, hTI ht⟩ htR z hz
    · have htp := S.mul_inv_mem_R1 ht hpT htR hpR
      have htpT : t * p⁻¹ ∈ T := T.mul_mem ht (T.inv_mem hpT)
      have e : (⟨t, hTI ht⟩ : ↥(S.H0 H)) = ⟨t * p⁻¹, hTI htpT⟩ * ⟨p, hTI hpT⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul]
      have ha := hall ⟨t * p⁻¹, hTI htpT⟩ htp z hz
      calc π ⟨t * p⁻¹, hTI htpT⟩ * π ⟨p, hTI hpT⟩ * z *
            (π ⟨t * p⁻¹, hTI htpT⟩ * π ⟨p, hTI hpT⟩)⁻¹ =
          π ⟨t * p⁻¹, hTI htpT⟩ * (π ⟨p, hTI hpT⟩ * z * (π ⟨p, hTI hpT⟩)⁻¹) *
            (π ⟨t * p⁻¹, hTI htpT⟩)⁻¹ := by group
        _ = z := by rw [hpZ z hz, ha]
  have hTK : ∀ (t : G) (ht : t ∈ T), π ⟨t, hTI ht⟩ ∈ K := by
    intro t ht
    by_contra htK
    obtain ⟨y, hy, hne⟩ := (hc.outer _ (S.map_T_mem_inf hTH ht) htK).2.2 1 (Subgroup.one_mem _)
    apply hne
    rw [hTZ t ht y hy]
    group
  set Tb := (T.subgroupOf (S.H0 H)).map π with hTb
  have hTbK : Tb ≤ K := by
    rintro _ ⟨⟨t, htI⟩, ht, rfl⟩
    exact hTK t ht
  have hinf8 : Nat.card ↥(S.G1bar H ⊓ S.G2bar H) = 8 := by
    obtain ⟨e⟩ := hc.dihedral
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hinf2 : IsPGroup 2 ↥(S.G1bar H ⊓ S.G2bar H) :=
    IsPGroup.of_card (n := 3) (by rw [hinf8]; norm_num)
  have hTb_le : Tb ≤ S.G1bar H ⊓ S.G2bar H := by
    rintro _ ⟨⟨t, htI⟩, ht, rfl⟩
    exact S.map_T_mem_inf hTH ht
  have hTb_eq : S.G1bar H ⊓ S.G2bar H = Tb := by
    set P := A4.toSylow (isSylowTwoOf_of_le S.h13.sylow hTI) with hP
    set P' := P.mapSurjective (QuotientGroup.mk'_surjective N3) with hP'
    have hP'coe : (P' : Subgroup (↥(S.H0 H) ⧸ N3)) = Tb := by
      rw [hP', Sylow.coe_mapSurjective, hP, A4.toSylow_coe]
    rw [← hP'coe]
    exact P'.is_maximal' hinf2 (hP'coe ▸ hTb_le)
  have hTb8 : Nat.card ↥Tb = 8 := by rw [← hTb_eq, hinf8]
  have hTb2 : IsPGroup 2 ↥Tb := hTb_eq ▸ hinf2
  have h4 := hc.card_two_le (Tb.subgroupOf K) (A4.isPGroup_subgroupOf_of_le hTbK hTb2)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTbK).toEquiv, hTb8] at h4
  omega

end Setting

end CFSG.Quasithin.H13.A5
