module

public import CFSG.Quasithin.H13.U3S1347B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS13410C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1343

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_exists_HM_F4 (h135 : A6.Stmt13_3_5_F4) (S : A6.Setting134 G T L V) :
    ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzL, hCz⟩ := (h135 G T L V S.h13 S.irr).2.2 (s134_isA6On S)
  obtain ⟨-, hzT, hz2⟩ := mem_quasithinOmegaOneCenter_iff.1 (mem_inf.1 hz).2
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  refine ⟨_, ⟨fun t ht => mem_centralizer_singleton_iff.2 ?_, fun hO => hz1 ?_⟩, hCz⟩
  · exact mem_centralizer_iff.1 hzT t ht
  · have hle : zpowers z ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
      refine le_pCoreOf_of_le_normalizer (zpowers_le.2 hzC) (fun y hy => ?_) ?_
      · refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
        exact (Commute.zpow_left (mem_centralizer_singleton_iff.1 hy).symm k).eq
      · exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_eq_prime hz2 hz1)
    rw [hO, le_bot_iff, zpowers_eq_bot] at hle
    exact hle

theorem s1347_not_le_M_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G) := by
  intro hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := s1347_inH hedge S h
  have hZ := s134_card_Z_F4 h1332 hC58 h317 h56 S (s134_exists_HM_F4 h135 S)
  have key : ∀ {H : Subgroup G}, H ≤ H₁ ⊔ H₂ → T ≤ H → T.relIndex H = 3 →
      Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H) →
      cZ T (oTwoRes H) = quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) := by
    intro H hH hTH h3 hidx
    have hKL : oTwoRes H ≤ L := (closure_le _).2 fun x hx => by
      obtain ⟨hxH, m, hm, hxm⟩ := hx
      have hx3 := pow_three_of_relIndex_three S.h13.sylow.1 hTH h3 hxH hm hxm
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · exact NQS134.mem_L_of_orderOf_three_F4 h1332 h1228 S (hM (hH hxH))
          (orderOf_eq_prime hx3 hx1)
    have hle : quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ≤ cZ T (oTwoRes H) :=
      inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hKL))
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [← cZ_eq_cZ_oTwoRes (A5.isSylowTwoOf_of_le S.h13.sylow hTH)]
    omega
  exact s1347_false_of_cZ_eq S h hH₀
    ((key le_sup_left h.inH₁.1 (s1347_relIndex_three S h.inH₁.1 h.s3₁) h.index₁).trans
      (key le_sup_right h.inH₂.1 (s1347_relIndex_three S h.inH₂.1 h.s3₂) h.index₂).symm)

theorem s1347_one_first_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) :
    InH T (H₁ ⊔ H₂) ∧ ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G) ∧
      quasithinOmegaOneCenter T = fsuV1 T V ∧
      cZ T H₁ ⊔ cZ T H₂ = quasithinOmegaOneCenter T ∧ cZ T H₁ ⊓ cZ T H₂ = ⊥ ∧
      Nat.card ↥(cZ T H₁) = 2 ∧ Nat.card ↥(cZ T H₂) = 2 := by
  have hH₀ := s1347_inH hedge S h
  have hH₀M := s1347_not_le_M_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hZ := s134_card_Z_F4 h1332 hC58 h317 h56 S ⟨_, hH₀, hH₀M⟩

  obtain ⟨H, hH, hHM⟩ : ∃ H, (H = H₁ ∨ H = H₂) ∧ ¬ H ≤ normalizer (L : Set G) := by
    by_contra hc
    push Not at hc
    exact hH₀M (sup_le (hc H₁ (Or.inl rfl)) (hc H₂ (Or.inr rfl)))
  have hidx : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H) := by
    rcases hH with rfl | rfl
    exacts [h.index₁, h.index₂]
  have hle2 := s134_card_cZ_le S hHM hZ

  have hZV := card_le_of_le (A6.Setting134.ZV_le_ZL S)
  rw [S.card_ZV] at hZV
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by omega
  have hc₁ : Nat.card ↥(cZ T H₁) = 2 := by
    have := h.index₁
    omega
  have hc₂ : Nat.card ↥(cZ T H₂) = 2 := by
    have := h.index₂
    omega

  have hne : cZ T H₁ ≠ cZ T H₂ := fun e => s1347_false_of_cZ_eq S h hH₀ (by
    rw [← cZ_eq_cZ_oTwoRes (A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1),
      ← cZ_eq_cZ_oTwoRes (A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1), e])
  obtain ⟨hsup, hinf⟩ :=
    sup_eq_and_inf_eq_bot_of_card inf_le_left inf_le_left hZ4 hc₁ hc₂ hne
  have hV1 : fsuV1 T V = quasithinOmegaOneCenter T :=
    eq_of_le_of_card_ge inf_le_right (by rw [S.card_V1]; omega)
  exact ⟨hH₀, hH₀M, hV1.symm, hsup, hinf, hc₁, hc₂⟩

end CFSG.Quasithin.H13.U3
