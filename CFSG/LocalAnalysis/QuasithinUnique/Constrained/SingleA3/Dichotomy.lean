module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwoConfig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Dichotomy.Generic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.CharTwoCentralizer

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup

namespace A3Dich

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem isSylowTwoOf_normalizer (hcs : ConstrainedSetting G T M H S L) {S₀ : Subgroup G}
    (hS₀ : S₀ ≠ ⊥) (hS₀S : S₀ ≤ S) (hHN : H ≤ normalizer (S₀ : Set G)) :
    IsSylowTwoOf S (normalizer (S₀ : Set G)) := by
  have hS₀2 : IsPGroup 2 S₀ := hcs.sylow.isPGroup.to_le hS₀S
  have hΓ : IsGamma M (normalizer (S₀ : Set G)) := by
    refine ⟨fun hbot => hS₀ ?_, ?_⟩
    · have : S₀ ≤ pCoreOf 2 (normalizer (S₀ : Set G)) :=
        le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hS₀2
      rw [hbot] at this
      exact le_bot_iff.mp this
    · obtain ⟨-, U, HU, hp, hle⟩ := hcs.gamma0.isGamma
      exact ⟨U, HU, hp, hle.trans hHN⟩
  exact (hcs.gamma0.overgroup_of_le hcs.setting hcs.sylow_inf hΓ hHN).2.1

theorem mem_of_mem_normalizer (hcs : ConstrainedSetting G T M H S L) {S₀ : Subgroup G}
    (hS₀ : S₀ ≠ ⊥) (hS₀S : S₀ ≤ S) (hHN : H ≤ normalizer (S₀ : Set G)) {t : G} (ht : t ∈ T)
    (htN : t ∈ normalizer (S₀ : Set G)) : t ∈ S := by
  have hSyl := isSylowTwoOf_normalizer hcs hS₀ hS₀S hHN
  have hEq := hSyl.eq_of_le (le_inf hcs.le_T hSyl.le) inf_le_right
    (hcs.setting.isPGroup.to_le inf_le_left)
  exact hEq.le ⟨ht, htN⟩

theorem exists_sq_mem_normalizer {T S : Subgroup G} (hT : IsPGroup 2 T) (hST : S ≤ T)
    (hne : S ≠ T) : ∃ x ∈ T, x ∈ normalizer (S : Set G) ∧ x ∉ S ∧ x ^ 2 ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀, hx₀S⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hT hST hne
  have hex : ∃ k : ℕ, x₀ ^ (2 ^ k) ∈ S := by
    obtain ⟨k, hk⟩ := hT ⟨x₀, hx₀.1⟩
    refine ⟨k, ?_⟩
    have h2 : x₀ ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h2]
    exact S.one_mem
  have hj : x₀ ^ (2 ^ Nat.find hex) ∈ S := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hj
    exact hx₀S hj
  obtain ⟨j, hj'⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨x₀ ^ (2 ^ j), T.pow_mem hx₀.1 _, (normalizer (S : Set G)).pow_mem hx₀.2 _, ?_, ?_⟩
  · intro h
    exact Nat.find_min hex (by omega : j < Nat.find hex) h
  · rw [← pow_mul, ← pow_succ]
    rw [hj'] at hj
    exact hj

end A3Dich

theorem single_A3_dichotomy {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (hcs : ConstrainedSetting G T M H S L) (h3 : IsAltType L 3) (hj : conjJoin S L = L) :
    (∃ U : Subgroup G, Nat.card U = 4 ∧ (∀ u ∈ U, u ^ 2 = 1) ∧ U ≤ T ∧
        T ⊓ Subgroup.centralizer (U : Set G) ≤ U ∧ 16 ≤ Nat.card T) ∨
      ∃ (U R : Subgroup G) (y x c : G), ZTwoConfig T S U R y x c := by
  classical
  obtain ⟨U, D, c, hl⟩ := hcs.a3Local h3 hj
  have hT2 : IsPGroup 2 T := hcs.setting.isPGroup
  have hH : H = L ⊔ S := by rw [hcs.eq_join, hj]
  have hLH : L ≤ H := hH ▸ le_sup_left
  have hSH : S ≤ H := hcs.sylow.1
  have hHU := hl.H_normalizes_U
  have hHD := hl.H_normalizes_D
  have hUne : U ≠ ⊥ := by
    intro h
    have := hl.card_U
    rw [h, Subgroup.card_bot] at this
    omega
  have hN_U : ∀ t ∈ T, t ∈ normalizer (U : Set G) → t ∈ S := fun t ht htN =>
    A3Dich.mem_of_mem_normalizer hcs hUne hl.U_le_S hHU ht htN
  by_cases hD : D = ⊥
  · left
    refine ⟨U, hl.card_U, hl.U_exp, hl.U_le_S.trans hcs.le_T, ?_, ?_⟩
    · intro t ht
      have htN : t ∈ normalizer (U : Set G) :=
        A3Dich.mem_normalizer_of_forall_comm fun u hu =>
          (Subgroup.mem_centralizer_iff.mp ht.2 u hu).symm
      have htS : t ∈ S ⊓ centralizer (U : Set G) := ⟨hN_U t ht.1 htN, ht.2⟩
      rw [hl.S_cent_U, hD, sup_bot_eq] at htS
      exact htS
    · have hS8 : Nat.card S = 8 := by
        have := hl.card_S
        rw [hD, Subgroup.card_bot] at this
        omega
      have h1 : Nat.card S ∣ Nat.card T := Subgroup.card_dvd_of_le hcs.le_T
      have h2 : Nat.card S ≤ Nat.card T := Subgroup.card_le_of_le hcs.le_T
      have h3 : Nat.card S ≠ Nat.card T := fun h =>
        hcs.ne_T (Subgroup.eq_of_le_of_card_ge hcs.le_T h.ge)
      rw [hS8] at h1 h2 h3
      omega
  · right
    obtain ⟨x, hxT, hxN, hxS, hx2⟩ := A3Dich.exists_sq_mem_normalizer hT2 hcs.le_T hcs.ne_T
    have hdata : A3Dich.Data S L U D x :=
      { card_U := hl.card_U
        U_comm := hl.U_comm
        U_le := hl.U_le_S
        D_le := hl.D_le_S
        U_inf_D := hl.U_inf_D
        S_cent_U := hl.S_cent_U
        card_S := hl.card_S
        S_norm_U := hSH.trans hHU
        S_norm_D := hSH.trans hHD
        L_norm_U := hLH.trans hHU
        D_comm_L := hl.D_comm_L
        x_norm := hxN
        x_sq := hx2
        h244 := fun S₀ hS₀ hS₀S hSN hLN hxN' =>
          hxS (A3Dich.mem_of_mem_normalizer hcs hS₀ hS₀S (by rw [hH]; exact sup_le hLN hSN) hxT
            hxN') }
    obtain ⟨hD2, hR8, hnab, hRS, hRD, hSeq⟩ := hdata.main
    have hDcard : Nat.card D = 2 := by
      have h1 : Nat.card D ≠ 1 := fun h => hD (Subgroup.card_eq_one.mp h)
      have h0 : 0 < Nat.card D := Nat.card_pos
      omega
    obtain ⟨⟨y, hyD⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hy2 : orderOf y = 2 := by
      have hdvd : orderOf y ∣ 2 := hDcard ▸ Subgroup.orderOf_dvd_natCard D hyD
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1'
      · exact h
    have hDy : zpowers y = D :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyD)
        (by rw [Nat.card_zpowers, hy2, hDcard])
    subst hDy
    have hcent := I43Dihedral.normalizer_zpowers_eq_centralizer_of_orderOf_eq_two hy2
    have hQne : U ⊔ zpowers y ≠ ⊥ := fun h => hUne (le_bot_iff.mp (le_sup_left.trans h.le))
    refine ⟨U, U ⊔ conjSubgroup U x, y, x, c, ?_⟩
    exact
      { simple := hcs.setting.simple
        nonabelian := hcs.setting.nonabelian
        sylowT := hcs.setting.sylow
        S_le := hcs.le_T
        card_S := by have := hl.card_S; omega
        x_mem := hxT
        x_not_mem := hxS
        x_normalizes := hxN
        x_sq_mem := hx2
        U_le := hl.U_le_S
        card_U := hl.card_U
        U_exp := hl.U_exp
        S_normalizes_U := hdata.S_norm_U
        R_eq := rfl
        R_le := hRS
        card_R := hR8
        R_nonabelian := hnab
        y_mem := hl.D_le_S hyD
        y_order := hy2
        y_comm := fun s hs =>
          Subgroup.mem_centralizer_singleton_iff.mp (hcent ▸ hdata.S_norm_D hs)
        y_not_mem_R := fun h => hy1' (Subgroup.mem_bot.mp (by rw [← hRD]; exact ⟨h, hyD⟩))
        S_eq := hSeq
        c_order := hl.c_order
        c_normalizes := hl.c_normalizes
        c_fpf := hl.c_fpf
        c_comm := (hl.D_comm_L y hyD c hl.c_mem).symm
        N_y := fun t ht htN => A3Dich.mem_of_mem_normalizer hcs hD hl.D_le_S hHD ht htN
        N_U := hN_U
        N_Q := fun t ht htN =>
          A3Dich.mem_of_mem_normalizer hcs hQne (sup_le hl.U_le_S hl.D_le_S)
            (fun h hh => A3Gen.mem_normalizer_sup (hHU hh) (hHD hh)) ht htN
        sylow_Cy := by
          rw [← hcent]
          exact A3Dich.isSylowTwoOf_normalizer hcs hD hl.D_le_S hHD }

end CFSG.QuasithinUnique
