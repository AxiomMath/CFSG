module

public import CFSG.GH74.GLS.C3.Layer1.BkP85SpCfg
public import CFSG.GH74.GLS.C3.Layer1.BkP85SpGlue
public import CFSG.GH74.GLS.C3.Layer1.Th2P88b
public import CFSG.GH74.Generic.S45.LEvSporJ2

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85

@[expose] def B_thm2_p89_J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x y : G) (K T S M L : Subgroup G),
    P85Struct x y K T S M L →
    NativeSporadic.IsSporadic ↥(imgM M L) .J2 → imgM M L = ⊤ →
    gammaK 2 (T ⊓ CxK x K) 1 ≤ M →
    (∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M) →
    ∀ W : Subgroup G, IsSylowOf 2 W ⊤ → W ≤ M → T ⊓ M ≤ W →
      ∀ v ∈ W, orderOf v = 2 → (∀ w ∈ W, v * w = w * v) →
        ¬ centralizer ({v} : Set G) ≤ M → False

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.TwoThin
open CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore

section J2Classes

variable {X : Type} [Group X] [Finite X] {H : Subgroup X}

theorem j2_cent_card (hF : J2Facts H) {t : X} (htH : t ∈ H) (ht2 : orderOf t = 2) :
    Nat.card ↥(centralizer ({t} : Set X) ⊓ H) = 1920 ∨
      Nat.card ↥(centralizer ({t} : Set X) ⊓ H) = 240 := by
  obtain ⟨-, tA, tB, M, E, htA, htB, htA2, htB2, hcover, hcA, hcB, -⟩ := hF
  rcases hcover t htH ht2 with ⟨g, hg, h⟩ | ⟨g, hg, h⟩
  · left
    rw [h, card_cent_conj hg, inf_comm]
    exact hcA
  · right
    rw [h, card_cent_conj hg, inf_comm]
    exact hcB

theorem j2_isConj_of_card_eq (hF : J2Facts H) {t t' : X} (ht : t ∈ H) (ht' : t' ∈ H)
    (ht2 : orderOf t = 2) (ht2' : orderOf t' = 2)
    (hc : Nat.card ↥(centralizer ({t} : Set X) ⊓ H) = Nat.card ↥(centralizer ({t'} : Set X) ⊓ H)) :
    IsConj t t' := by
  obtain ⟨-, tA, tB, M, E, htA, htB, htA2, htB2, hcover, hcA, hcB, -⟩ := hF
  rcases hcover t ht ht2 with ⟨g, hg, h⟩ | ⟨g, hg, h⟩ <;>
    rcases hcover t' ht' ht2' with ⟨g', hg', h'⟩ | ⟨g', hg', h'⟩
  · exact isConj_iff.2 ⟨g' * g⁻¹, by rw [h, h']; group⟩
  · exfalso
    rw [h, h', card_cent_conj hg, card_cent_conj hg', inf_comm, inf_comm (centralizer {tB}),
      hcA, hcB] at hc
    norm_num at hc
  · exfalso
    rw [h, h', card_cent_conj hg, card_cent_conj hg', inf_comm, inf_comm (centralizer {tA}),
      hcA, hcB] at hc
    norm_num at hc
  · exact isConj_iff.2 ⟨g' * g⁻¹, by rw [h, h']; group⟩

theorem not_two_pow_seven_dvd (hF : J2Facts H) {y : X} (hyH : y ∈ H) (hy2 : orderOf y = 2)
    (hnot : ¬ ∃ S : Subgroup X, IsSylowOf 2 S H ∧ y ∈ S ∧ ∀ s ∈ S, s * y = y * s) :
    ¬ 2 ^ 7 ∣ Nat.card ↥(centralizer ({y} : Set X) ⊓ H) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := centralizer ({y} : Set X) ⊓ H with hC
  have hCH : C ≤ H := inf_le_right
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup X) := IsPGroup.of_card (n := 0) (by
    rw [Subgroup.card_bot]
    rfl)
  obtain ⟨S, hS, -⟩ := EvenSporTransfer.exists_isSylowOf_ge (N := C) (A := ⊥) bot_le hbot
  have hSC : S ≤ C := hS.le
  have h7 : 7 ≤ (Nat.card ↥C).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hm : (Nat.card ↥C).factorization 2 ≤ 7 := by
    have h1 : Nat.card ↥S ∣ Nat.card ↥H := Subgroup.card_dvd_of_le (hSC.trans hCH)
    rw [hS.card_eq, hF.card] at h1
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).1 h1
    rwa [factorization_604800] at this
  have hSH : IsSylowOf 2 S H := by
    refine isSylowOf_of_card (hSC.trans hCH) ?_
    rw [hS.card_eq, hF.card, factorization_604800]
    congr 1
    omega
  have hyC : y ∈ C := ⟨mem_centralizer_singleton_iff.2 rfl, hyH⟩
  have hyS : y ∈ S :=
    C3.Layer1.Back.mem_of_isSylowOf_of_central hS hyC
      (fun s (hs : s ∈ centralizer ({y} : Set X) ⊓ H) => mem_centralizer_singleton_iff.1 hs.1) hy2
  have hSC' : S ≤ centralizer ({y} : Set X) ⊓ H := hSC
  exact hnot ⟨S, hSH, hyS, fun s hs => mem_centralizer_singleton_iff.1 (hSC' hs).1⟩

end J2Classes

section SE

variable {G : Type} [Group G] [Finite G]

theorem false_of_stronglyEmbedded [IsSimpleGroup G] {x y : G}
    {K T S M : Subgroup G} (hstd : Th2Std x y K T S) (hx2 : orderOf x = 2)
    (hSE : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) : False := by
  have hB := CFSG.BenderSuzuki.bender_suzuki M hSE
  have hsol := C3.Layer1.Bk.isSolvable_centralizer_of_isBenderGroup hB hx2
  have hKsol : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hstd.K_le_C)
      (Subgroup.inclusion_injective hstd.K_le_C)
  have hq : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  have hqs := TwoThin.isQuasisimple_hat hstd.comp
  have : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) := CFSG.LocalCores.isQuasisimple_nontrivial hqs
  have : Group.IsPerfect (↥K ⧸ pPrimeCore 2 ↥K) := hqs.1
  exact Group.IsPerfect.not_isSolvable _ hq

end SE

section Main

variable {G : Type} [Group G] [Finite G]

theorem p85_J2_top_false
    (hb : B_thm2_p88b)
    (h89 : B_thm2_p89_J2) {x y : G} {K T S M L : Subgroup G} (hs : P85Struct x y K T S M L)
    (hK5 : Nonempty ((↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ≃* alternatingGroup (Fin 5)))
    (hJ2 : NativeSporadic.IsSporadic ↥(imgM M L) .J2) (hLtop : imgM M L = ⊤) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsetup := hs.toP85Setup
  have hstd := hsetup.choice.std
  have hsimp : IsSimpleGroup G := hsetup.hG.kproper.1
  have hMtop : M ≠ ⊤ := hsetup.choice.maximal.1
  have hxM : x ∈ M := x_mem_M hs
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2
    omega
  have hx2M : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
  have hCx : centralizer ({x} : Set G) ≤ M := centralizer_le_M_of_p88b hb hs
  have hgam : gammaK 2 (T ⊓ CxK x K) 1 ≤ M := gammaK_le_M_of_p88b hb hs
  obtain ⟨hK5', hsyl, hrank, hxbQ, hxb2, -⟩ := p85_bar_data hs hK5 hxM
  obtain ⟨W, hWsyl, hWle⟩ := EvenSporTransfer.exists_isSylowOf_ge (N := M) (A := T ⊓ M)
    inf_le_right (hstd.T_pGroup.to_le inf_le_left)
  have hxW : x ∈ W := hWle ⟨hstd.x_mem_T, hxM⟩
  obtain ⟨v, hvW, hv2, hvc⟩ := Th2.L84Syl.exists_involution_mem_center hWsyl.isPGroup hxW hx1
  have hvM : v ∈ M := hWsyl.le hvW
  have hv2M : orderOf (⟨v, hvM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk v hvM).trans hv2
  have hvb2 : orderOf (barMk ↥M ⟨v, hvM⟩) = 2 := orderOf_barMk hv2M
  have hF : J2Facts (imgM M L) := by
    obtain ⟨e⟩ := hJ2
    exact J2Facts.of_equiv (e.trans j2PermEquiv) j2_facts
  have memH : ∀ t : Mb M, t ∈ imgM M L := fun t => by
    rw [hLtop]
    exact Subgroup.mem_top t
  have hcardM : Nat.card (Mb M) = 604800 := by
    rw [← Subgroup.card_top, ← hLtop]
    exact hF.card
  have hKH : imgM M K ≤ imgM M L := imgM_mono hsetup.hL.1
  have hrk : 2 ≤ pRank 2 ↥(centralizer (imgM M K : Set (Mb M)) ⊓ imgM M L) :=
    hrank.trans (C3.Layer1.Back.pRank_mono' (le_inf hsyl.le (by rw [hLtop]; exact le_top)))
  obtain ⟨-, htable⟩ :=
    CFSG.GH74.GLS.b_spor_J2_table_proved (Mb M) (imgM M L) (imgM M K) hJ2 hKH hK5' hrk
  have hxbC : barMk ↥M ⟨x, hxM⟩ ∈ centralizer (imgM M K : Set (Mb M)) ⊓ imgM M L :=
    ⟨hsyl.le hxbQ, memH _⟩
  have hnot2 := not_two_pow_seven_dvd hF (memH _) hxb2 (htable _ hxbC hxb2)
  have hcx : Nat.card ↥(centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M)) ⊓ imgM M L) = 240 := by
    rcases j2_cent_card hF (memH _) hxb2 with h | h
    · exact absurd (by rw [h]; norm_num) hnot2
    · exact h
  have hWb : IsSylowOf 2 (imgM M W) (imgM M M) := isSylowOf_imgM_of_le (le_refl M) hWsyl
  have hMM : imgM M M = ⊤ := by
    unfold imgM
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ barMk_surjective
  rw [hMM] at hWb
  have hWbcard : Nat.card ↥(imgM M W) = 2 ^ 7 := by
    rw [hWb.card_eq, Subgroup.card_top, hcardM, factorization_604800]
  have hWbC : imgM M W ≤ centralizer ({barMk ↥M ⟨v, hvM⟩} : Set (Mb M)) := by
    intro r hr
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hr
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvc _ hm).symm
  have hdvdv : 2 ^ 7 ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨v, hvM⟩} : Set (Mb M)) ⊓ imgM M L) := by
    have := Subgroup.card_dvd_of_le (le_inf hWbC (by rw [hLtop]; exact le_top) :
      imgM M W ≤ centralizer ({barMk ↥M ⟨v, hvM⟩} : Set (Mb M)) ⊓ imgM M L)
    rwa [hWbcard] at this
  have hcv : Nat.card ↥(centralizer ({barMk ↥M ⟨v, hvM⟩} : Set (Mb M)) ⊓ imgM M L) = 1920 := by
    rcases j2_cent_card hF (memH _) hvb2 with h | h
    · exact h
    · rw [h] at hdvdv
      norm_num at hdvdv
  have hcls : ∀ t : Mb M, orderOf t = 2 →
      IsConj t (barMk ↥M ⟨x, hxM⟩) ∨ IsConj t (barMk ↥M ⟨v, hvM⟩) := by
    intro t ht2
    rcases j2_cent_card hF (memH t) ht2 with h | h
    · right
      exact j2_isConj_of_card_eq hF (memH t) (memH _) ht2 hvb2 (by rw [h, hcv])
    · left
      exact j2_isConj_of_card_eq hF (memH t) (memH _) ht2 hxb2 (by rw [h, hcx])
  have hk1 : 2 ^ 7 ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨v, hvM⟩} : Set (Mb M))) := by
    rw [hLtop, inf_top_eq] at hdvdv
    exact hdvdv
  have hk2 : ¬ 2 ^ 7 ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M))) := by
    rw [hLtop, inf_top_eq] at hnot2
    exact hnot2
  have hc : ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M := by
    intro g hgM
    have hw2 : orderOf (g⁻¹ * x * g) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
      simpa [MulAut.conj_apply] using this.trans hx2
    have hw2M : orderOf (⟨g⁻¹ * x * g, hgM⟩ : ↥M) = 2 :=
      (Subgroup.orderOf_mk _ hgM).trans hw2
    have hwb2 : orderOf (barMk ↥M ⟨g⁻¹ * x * g, hgM⟩) = 2 := orderOf_barMk hw2M
    have hdom := two_adic_dom hxM hgM hx2 hw2 hCx (card_centralizer_conj x g)
    rcases hcls _ hwb2 with hconj | hconj
    · obtain ⟨m, hm⟩ := exists_conj_of_barMk_conj hw2M hx2M hconj
      have hmG : (m : G) * x * (m : G)⁻¹ = g⁻¹ * x * g := congrArg Subtype.val hm
      have hcomm : g * (m : G) * x = x * (g * (m : G)) := by
        calc g * (m : G) * x = g * ((m : G) * x * (m : G)⁻¹) * (m : G) := by group
          _ = g * (g⁻¹ * x * g) * (m : G) := by rw [hmG]
          _ = x * (g * (m : G)) := by group
      have hgm : g * (m : G) ∈ M := hCx (mem_centralizer_singleton_iff.2 hcomm)
      have hg : g = g * (m : G) * (m : G)⁻¹ := by group
      rw [hg]
      exact M.mul_mem hgm (M.inv_mem m.2)
    · exfalso
      obtain ⟨c, hcc⟩ := isConj_iff.1 hconj
      have hcard := card_cent_conj (N := (⊤ : Subgroup (Mb M))) (Subgroup.mem_top c)
        (barMk ↥M ⟨g⁻¹ * x * g, hgM⟩)
      rw [hcc, inf_top_eq, inf_top_eq] at hcard
      have h7 : 2 ^ 7 ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨g⁻¹ * x * g, hgM⟩} : Set (Mb M)) ⊓ ⊤) := by
        rw [inf_top_eq, ← hcard]
        exact hk1
      apply hk2
      have := hdom 7 h7
      rwa [inf_top_eq] at this
  have hWG : IsSylowOf 2 W ⊤ := by
    obtain ⟨S', hS'⟩ := EvenSporTransfer.exists_sylow_eq_of_fusion hWsyl hxW hCx
      (fun g hg => ⟨g, hc g hg, rfl⟩)
    rw [isSylowOf_iff]
    refine ⟨le_top, hWsyl.isPGroup, fun hdvd => S'.not_dvd_index ?_⟩
    rw [hS', ← Subgroup.relIndex_top_right]
    exact hdvd
  by_cases hCv : centralizer ({v} : Set G) ≤ M
  ·
    have hnc : ¬ IsConj x v := not_isConj_of_two_adic hxM hvM hx2 hv2 hCx hCv hk1 hk2
    have hfus : ∀ t ∈ M, orderOf t = 2 →
        (∃ c ∈ M, c * x * c⁻¹ = t) ∨ (∃ c ∈ M, c * v * c⁻¹ = t) := by
      intro t htM ht2
      have ht2M : orderOf (⟨t, htM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk t htM).trans ht2
      rcases hcls _ (orderOf_barMk ht2M) with h | h
      · left
        obtain ⟨m, hmx⟩ := exists_conj_of_barMk_conj ht2M hx2M h
        exact ⟨m, m.2, congrArg Subtype.val hmx⟩
      · right
        obtain ⟨m, hmv⟩ := exists_conj_of_barMk_conj ht2M hv2M h
        exact ⟨m, m.2, congrArg Subtype.val hmv⟩
    have hSE := isStronglyEmbedded_of_cent hMtop hxM hx2 hnc hfus hCx hCv
    exact false_of_stronglyEmbedded hstd hx2 hSE
  · exact h89 G x y K T S M L hs hJ2 hLtop hgam hc W hWG hWsyl.le hWle v hvW hv2 hvc hCv

end Main

end CFSG.GH74.GLS.Th2.P85.Sp
