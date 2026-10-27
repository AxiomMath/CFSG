module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk4
public import CFSG.Quasithin.Background.F6ComponentBound
public import CFSG.Quasithin.Background.F918P1
public import CFSG.Quasithin.H13.A5S136sz0
public import CFSG.Quasithin.H13.L32A706b
public import CFSG.Quasithin.H13.L32AC47a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V : Subgroup G}

theorem l1_star_normal_F4 (h1332 : Stmt13_3_2_F4) {X : Subgroup G}
    (S : Setting147 G T L V (X ⊔ (l1 T L V ⊔ T)))
    (hXn : l1 T L V ⊔ T ≤ Subgroup.normalizer (X : Set G))
    (hcomm : ∀ y ∈ l1 T L V, ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (X ⊔ (l1 T L V ⊔ T))) :
    (modO2Image (X ⊔ (l1 T L V ⊔ T)) (l1 T L V)).Normal := by
  have hl1H : l1 T L V ≤ X ⊔ (l1 T L V ⊔ T) := Setting147.l1H' S
  have hl1N : l1 T L V ⊔ T ≤ Subgroup.normalizer (l1 T L V : Set G) :=
    sup_le Subgroup.le_normalizer (Setting147.T_le_N_l1_F4 S h1332)
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨l, hl, rfl⟩ := mem_modO2Image'.mp hn
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(X ⊔ (l1 T L V ⊔ T))) g
  obtain ⟨x, hx, m, hm, hxm⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hXn).mp h.2
  have hl' : (m * l * m⁻¹ : G) ∈ l1 T L V := (Subgroup.mem_normalizer_iff.mp (hl1N hm) l).mp hl
  have hl'H : (m * l * m⁻¹ : G) ∈ X ⊔ (l1 T L V ⊔ T) := hl1H hl'
  have hxH : x ∈ X ⊔ (l1 T L V ⊔ T) := Subgroup.mem_sup_left hx
  refine mem_modO2Image'.mpr ⟨⟨m * l * m⁻¹, hl'H⟩, hl', ?_⟩
  have hcm := Setting147.mk_commute_of_mem ⟨_, hl'H⟩ ⟨x, hxH⟩ (hcomm _ hl' x hx)
  have e : h * l * h⁻¹ = (⟨x, hxH⟩ : ↥(X ⊔ (l1 T L V ⊔ T))) * ⟨m * l * m⁻¹, hl'H⟩ *
      (⟨x, hxH⟩ : ↥(X ⊔ (l1 T L V ⊔ T)))⁻¹ :=
    Subtype.ext (by simp [hxm, mul_assoc])
  rw [← map_mul, ← map_inv, ← map_mul, e, map_mul, map_mul, map_inv, ← hcm,
    mul_inv_cancel_right]

theorem false_of_l1_comm_F4 (h7 : Lemma14_7_7_F4) (h1332 : Stmt13_3_2_F4)
    {X K : Subgroup G} (S : Setting147 G T L V (X ⊔ (l1 T L V ⊔ T)))
    (hXn : l1 T L V ⊔ T ≤ Subgroup.normalizer (X : Set G))
    (hcomm : ∀ y ∈ l1 T L V, ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (X ⊔ (l1 T L V ⊔ T)))
    (hK : K ∈ cComp (X ⊔ (l1 T L V ⊔ T))) {e : ℕ} (hSz : IsSz e (cStar K)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := h7 G T L V _ S (l1_star_normal_F4 h1332 S hXn hcomm)
  obtain ⟨φ⟩ := modO2_mulEquiv hK
  have hKsz : IsSz e ↥(modO2Image (X ⊔ (l1 T L V ⊔ T)) K) :=
    isSz_congr ((cStarEquiv K).trans φ) hSz
  have hsub : (modO2Image (X ⊔ (l1 T L V ⊔ T)) K).IsSubnormal :=
    A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hcop : Nat.Coprime 3 (Nat.card ↥(modO2Image (X ⊔ (l1 T L V ⊔ T)) K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (H13.A5.ConfSz.three_not_dvd_card hKsz)
  have hbot := F6.eq_bot_of_isSubnormal_of_coprime 3 hP hsub hcop
  have hnt := (H13.A5.ConfSz.isSimpleGroup hKsz).toNontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hbot

end CFSG.Quasithin.H13.L32A.C
