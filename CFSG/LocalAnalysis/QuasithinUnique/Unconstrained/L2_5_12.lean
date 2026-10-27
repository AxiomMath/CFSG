module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Helpers

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

theorem exists_odd_of_not_le_M {U HU : Subgroup G} (hU : IsConfining M U) (hUHU : U ≤ HU)
    (hHUM : ¬ HU ≤ M) : ∃ d ∈ HU, d ≠ 1 ∧ Odd (orderOf d) := by
  by_contra hcon
  have hHU2 : IsPGroup 2 ↥HU := by
    intro x
    refine ⟨(orderOf (x : G)).factorization 2, ?_⟩
    have hx1 : (x : G) ^ 2 ^ (orderOf (x : G)).factorization 2 = 1 := by
      by_contra hne
      exact hcon ⟨(x : G) ^ 2 ^ (orderOf (x : G)).factorization 2, HU.pow_mem x.2 _, hne,
        odd_orderOf_pow_two_part (x : G)⟩
    exact Subtype.ext (by simpa using hx1)
  exact hHUM (hU.of_le hHU2 hUHU).1

theorem Notation25.isGamma_sylow_normalizer (N : Notation25 hs) {U HU Q : Subgroup G}
    (hpair : IsUStarPair M N.H U HU) (hQ2 : IsPGroup 2 Q) (hzQ : N.z ∈ Q) (hHUQ : HU ≤
      Subgroup.normalizer (Q : Set G)) :
    IsGamma M (Subgroup.normalizer (Q : Set G)) ∧
      IsSylowTwoOf U (Subgroup.normalizer (Q : Set G)) := by
  have hDZ : Q ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro hbot
    have hz : N.z ∈ Q ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hzQ, N.tuple.z_mem⟩
    rw [hbot] at hz
    exact N.tuple.z_ne_one (Subgroup.mem_bot.mp hz)
  have hchar : CharTwo (Subgroup.normalizer (Q : Set G)) :=
    charTwo_normalizer_of_inf_center hs.setting.qtke.2.1 hs.setting.sylow hQ2 hDZ
  have hQ1 : Q ≠ ⊥ := fun h => N.tuple.z_ne_one (Subgroup.mem_bot.mp (h ▸ hzQ))
  have hcore : pCoreOf 2 (Subgroup.normalizer (Q : Set G)) ≠ ⊥ := by
    intro hbot
    have hle : Q ≤ pCoreOf 2 (Subgroup.normalizer (Q : Set G)) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Q _ Subgroup.le_normalizer
        ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hQ2
    rw [hbot] at hle
    exact hQ1 (le_bot_iff.mp hle)
  have hUHU : U ≤ HU := hpair.1.1.2.1
  have hUN : U ≤ Subgroup.normalizer (Q : Set G) := hUHU.trans hHUQ
  have hU2 : IsPGroup 2 U := hpair.1.1.1.2.2.1
  have hwit : IsWitnessPair M U (Subgroup.normalizer (Q : Set G)) :=
    ⟨hpair.1.1.1, hUN, hcore, hchar, fun hNM => hpair.1.1.2.2.2.2 (hHUQ.trans hNM)⟩
  refine ⟨⟨hcore, U, _, hwit, le_rfl⟩, ?_⟩
  obtain ⟨U₁, hUU₁, hU₁⟩ := exists_isSylowTwoOf_of_le hUN hU2
  have hconf₁ : IsConfining M U₁ := hpair.1.1.1.of_le hU₁.isPGroup hUU₁
  have hwit₁ : IsWitnessPair M U₁ (Subgroup.normalizer (Q : Set G)) :=
    ⟨hconf₁, hU₁.le, hcore, hchar, fun hNM => hpair.1.1.2.2.2.2 (hHUQ.trans hNM)⟩
  have hcard : Nat.card U₁ ≤ Nat.card U := hpair.2 U₁ hwit₁.isWitness
  have hU₁U : U₁ = U := (Subgroup.eq_of_le_of_card_ge hUU₁ hcard).symm
  rw [← hU₁U]
  exact hU₁

theorem Notation25.exists_four_subgroup (N : Notation25 hs) {t zK : G} (h : Lv2511 N t zK)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) {U HU : Subgroup G}
    (hpair : IsUStarPair M N.H U HU) (hUS : U ≤ N.S) :
    ∃ E : Subgroup G, E ≤ N.SK ∧ IsFourSubgroup E ∧ E ≤ U ∧
      HU ≤ Subgroup.normalizer (E : Set G) := by
  have h254 : Facts254 N := h.facts254
  have h258 : Facts258 N := h.facts258
  have hf : Facts2511 N t zK := h.facts2511
  obtain ⟨-, hUsyl, hz⟩ := h.concl2510.2 U HU hpair
  obtain ⟨-, hZZ⟩ := hz hUS
  have hzKZ : zK ∈ centerOf N.S := by
    rw [hf.centerS_zK]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hzK2 : zK ^ 2 = 1 := hf.centerS_E4.1.2 zK hzKZ
  have hzK2' : zK * zK = 1 := by rw [← sq]; exact hzK2
  have hzK1 : zK ≠ 1 := fun h1 => h254.z_not_mem (by
    have := hf.zK_proj
    rwa [h1, inv_one, one_mul] at this)
  have hzKU : zK ∈ centerOf U := hZZ hzKZ
  have hZ : Subgroup.zpowers zK ≤ quasithinOmegaOneCenter U :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨hzKU, hzK2⟩)
  have hFU : CharTwo HU := hpair.1.1.2.2.2.1
  obtain ⟨hle, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hUsyl hFU hZ
  have hHUH : HU ≤ N.H := hpair.1.2
  have hzKK : zK ∈ N.K := by
    have := hf.zK_mem
    rwa [N.K0_eq hKH] at this
  have hEK : conjClosure (Subgroup.zpowers zK) HU ≤ N.K := by
    refine conjClosure_le fun x hx z hz => ?_
    have hzK : z ∈ N.K := (Subgroup.zpowers_le.mpr hzKK) hz
    exact (Subgroup.mem_normalizer_iff.mp (hKH (hHUH hx)) z).mp hzK
  have hEU : conjClosure (Subgroup.zpowers zK) HU ≤ U :=
    (hle.trans inf_le_left).trans hUsyl.pCoreOf_le
  have hESK : conjClosure (Subgroup.zpowers zK) HU ≤ N.SK := le_inf (hEU.trans hUS) hEK
  have hnot : ¬ conjClosure (Subgroup.zpowers zK) HU ≤ Subgroup.zpowers zK := by
    intro hsub
    have hcent : ∀ x ∈ HU, x * zK = zK * x := by
      intro x hx
      have hmem : x * zK * x⁻¹ ∈ Subgroup.zpowers zK :=
        hsub (mem_conjClosure hx (Subgroup.mem_zpowers zK))
      rcases mem_zpowers_involution hzK2' hmem with h1 | h1
      · exfalso
        apply hzK1
        calc zK = x⁻¹ * (x * zK * x⁻¹) * x := by group
          _ = 1 := by rw [h1]; group
      · calc x * zK = x * zK * x⁻¹ * x := by group
          _ = zK * x := by rw [h1]
    have hcentt : ∀ x ∈ HU, x * t = t * x := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hf.H_le (hHUH hx))
    have hzSS : N.z ∈ centerOf N.S :=
      ⟨N.tuple.center_le N.tuple.z_mem, Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr N.S_le_T) N.tuple.z_mem.2⟩
    have htZ : t ∈ centerOf N.S := by
      rw [hf.centerS_zK]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have hcomm : t * zK = zK * t := (Subgroup.mem_centralizer_iff.mp htZ.2 zK hzKZ.1).symm
    have ht2 : t * t = 1 := by have := hf.t_sq; rwa [sq] at this
    have hzcl : N.z ∈ Subgroup.closure ({t, zK} : Set G) := by
      rw [← hf.centerS_zK]
      exact hzSS
    have hHUz : HU ≤ Subgroup.centralizer ({N.z} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases mem_closure_pair_of_involutions ht2 hzK2' hcomm hzcl with h1 | h1 | h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact hcentt x hx
      · rw [h1]; exact hcent x hx
      · rw [h1]
        calc x * (t * zK) = (x * t) * zK := by group
          _ = (t * x) * zK := by rw [hcentt x hx]
          _ = t * (x * zK) := by group
          _ = t * (zK * x) := by rw [hcent x hx]
          _ = t * zK * x := by group
    exact hpair.1.1.2.2.2.2 (hHUz.trans
      (hs.setting.centralizer_le_of_mem_center_isSylowTwoOf hs.setting.isSylowTwoOf_M
        N.tuple.z_mem N.tuple.z_ne_one))
  have hE2 : IsPGroup 2 ↥(conjClosure (Subgroup.zpowers zK) HU) :=
    N.tuple.sylow.isPGroup.to_le (hESK.trans N.SK_le_S)
  have hzE : Subgroup.zpowers zK ≤ conjClosure (Subgroup.zpowers zK) HU := le_conjClosure _ _
  have hlt : Subgroup.zpowers zK < conjClosure (Subgroup.zpowers zK) HU :=
    lt_of_le_of_ne hzE (fun h1 => hnot h1.symm.le)
  have hcard2 : Nat.card (Subgroup.zpowers zK) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hzK2 hzK1
  have hcardlt := Subgroup.card_lt_of_lt hlt
  rw [hcard2] at hcardlt
  have hcardle : Nat.card (conjClosure (Subgroup.zpowers zK) HU) ≤ 4 :=
    card_le_four_of_shape (N.tuple.sylow.isPGroup.to_le N.SK_le_S) h258.SK_shape hESK
      (fun x hx => hel.2 x hx)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hE2.exists_card_eq
  have hcard4 : Nat.card (conjClosure (Subgroup.zpowers zK) HU) = 4 := by
    rw [hj] at hcardlt hcardle ⊢
    have hj2 : j = 2 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt' | hgt
      · have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    rw [hj2]
    norm_num
  exact ⟨conjClosure (Subgroup.zpowers zK) HU, hESK, ⟨hel, hcard4⟩, hEU, hred.2.1⟩

end Helpers

theorem lemma2512 : Lemma2512 := by
  intro G _ _ T M hs N t zK h hKH
  have h254 : Facts254 N := h.facts254
  have h258 : Facts258 N := h.facts258
  refine ⟨fun U HU hpair hUS => ?_, fun E hEK hE4 => ?_, fun E E' hEK hE4 hE'K hE'4 _ hH => ?_⟩
  · obtain ⟨E, hEK, hE4, hEU, hHUE⟩ := N.exists_four_subgroup h hKH hpair hUS
    refine ⟨?_, fun Q hQ2 hzQ _ hHUQ => N.isGamma_sylow_normalizer hpair hQ2 hzQ hHUQ⟩
    have hUHU : U ≤ HU := hpair.1.1.2.1
    have hES : E ≤ N.S := hEK.trans N.SK_le_S
    have hE2 : IsPGroup 2 ↥E := N.tuple.sylow.isPGroup.to_le hES
    have hEX : E ≤ N.H ⊓ Subgroup.normalizer (E : Set G) :=
      le_inf (hES.trans N.S_le_H) Subgroup.le_normalizer
    have hHUX : HU ≤ N.H ⊓ Subgroup.normalizer (E : Set G) := le_inf hpair.1.2 hHUE
    have hUY : U ≤ N.S ⊓ Subgroup.normalizer (E : Set G) := le_inf hUS (hUHU.trans hHUE)
    have hY2 : IsPGroup 2 ↥(N.S ⊓ Subgroup.normalizer (E : Set G)) :=
      N.tuple.sylow.isPGroup.to_le inf_le_left
    have hE1 : E ≠ ⊥ := fun h1 => by
      have := hE4.2
      rw [h1, Subgroup.card_bot] at this
      omega
    have hcoreX : pCoreOf 2 (N.H ⊓ Subgroup.normalizer (E : Set G)) ≠ ⊥ := by
      intro hbot
      have hle : E ≤ pCoreOf 2 (N.H ⊓ Subgroup.normalizer (E : Set G)) :=
        CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 E _ hEX
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hEX).mpr inf_le_right) hE2
      rw [hbot] at hle
      exact hE1 (le_bot_iff.mp hle)
    have hwit : IsWitnessPair M (N.S ⊓ Subgroup.normalizer (E : Set G))
        (N.H ⊓ Subgroup.normalizer (E : Set G)) :=
      ⟨hpair.1.1.1.of_le hY2 hUY, inf_le_inf_right _ N.S_le_H, hcoreX,
        N.charTwo_normalizer hKH h254 h258 hEK hE4,
        fun hXM => hpair.1.1.2.2.2.2 (hHUX.trans hXM)⟩
    have hcard : Nat.card ↥(N.S ⊓ Subgroup.normalizer (E : Set G)) ≤ Nat.card U :=
      hpair.2 _ ⟨_, hwit⟩
    have hUeq : U = N.S ⊓ Subgroup.normalizer (E : Set G) :=
      Subgroup.eq_of_le_of_card_ge hUY hcard
    have hEHU : E ≤ HU := hEU.trans hUHU
    have hodd := exists_odd_of_not_le_M hpair.1.1.1 hUHU hpair.1.1.2.2.2.2
    have hres : pResidualOf 2 HU = (N.kleinData h258 hEK hE4).A :=
      N.pResidualOf_eq_A hKH h258 hEK hE4 hpair.1.2 hHUE hEHU hodd
    have hAle : (N.kleinData h258 hEK hE4).A ≤ HU := by
      rw [← hres]
      exact Subgroup.map_subtype_le _
    have hHUeq : HU = N.H ⊓ Subgroup.normalizer (E : Set G) := by
      refine le_antisymm hHUX fun x hx => ?_
      obtain ⟨a, ha, y, hy, rfl⟩ := N.exists_mul_A hKH h254 h258 hEK hE4 hx.1 hx.2
      have hyU : y ∈ U := by rw [hUeq]; exact hy
      exact HU.mul_mem (hAle ha) (hUHU hyU)
    refine ⟨E, hEK, hE4, hHUeq, hUeq, ?_, ?_, (N.inf_centralizer_eq h258 hEK hE4).symm⟩
    · rw [hres]
      exact (N.kleinData h258 hEK hE4).nonempty_equiv_A
    · exact (N.pCoreOf_pResidualOf_eq hKH h258 hEK hE4 hpair.1.2 hHUE hEHU hodd).symm
  · exact N.isSylowTwoOf_normalizer hKH h254 h258 hEK hE4
  · have hodd : ∀ {F : Subgroup G} (hFK : F ≤ N.SK) (hF4 : IsFourSubgroup F),
        ∃ d ∈ N.H ⊓ Subgroup.normalizer (F : Set G), d ≠ 1 ∧ Odd (orderOf d) := by
      intro F hFK hF4
      obtain ⟨d, hdP, hd1, hdodd⟩ := (N.kleinData h258 hFK hF4).exists_odd
      exact ⟨d, ⟨N.K_le_H hdP.1, hdP.2⟩, hd1, hdodd⟩
    have hEX : E ≤ N.H ⊓ Subgroup.normalizer (E : Set G) :=
      le_inf ((hEK.trans N.SK_le_S).trans N.S_le_H) Subgroup.le_normalizer
    have hEX' : E' ≤ N.H ⊓ Subgroup.normalizer (E' : Set G) :=
      le_inf ((hE'K.trans N.SK_le_S).trans N.S_le_H) Subgroup.le_normalizer
    have h1 := N.pCoreOf_pResidualOf_eq hKH h258 hEK hE4 inf_le_left inf_le_right hEX (hodd hEK hE4)
    have h2 := N.pCoreOf_pResidualOf_eq hKH h258 hE'K hE'4 inf_le_left inf_le_right hEX'
      (hodd hE'K hE'4)
    rw [hH] at h1
    exact h1.symm.trans h2

end CFSG.QuasithinUnique
