module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB13
public import CFSG.ClassicalInvolution.Q3.Q3AMDB11
public import CFSG.ClassicalInvolution.Q3.Q3AMDB18
public import CFSG.ClassicalInvolution.Q3.Q3T6XQuot

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP
open scoped MatrixGroups commutatorElement

section Lift

theorem sl2_inner_involution {g : SL(2, ZMod 3)}
    (h2 : (MulAut.conj g : MulAut SL(2, ZMod 3)) * MulAut.conj g = 1)
    (h1 : (MulAut.conj g : MulAut SL(2, ZMod 3)) ≠ 1) : g ^ 4 = 1 ∧ g ^ 2 ≠ 1 := by
  have hker := Q3T6.Aut.ker_conj_sl2Three
  have hc2 : g * g ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [← hker, MonoidHom.mem_ker, map_mul]
    exact h2
  have hc1 : g ∉ Subgroup.center SL(2, ZMod 3) := by
    intro hg
    rw [← hker, MonoidHom.mem_ker] at hg
    exact h1 hg
  rw [Q3T6.Aut.mem_center_sl2Three_iff] at hc2 hc1
  revert hc2 hc1
  revert g
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_lift {M : Subgroup G}
    (e : ↥M ⧸ classicalInvolutionOddCore ↥M ≃* SL(2, ZMod 3)) {δ : G}
    (hδ : δ ∈ Subgroup.normalizer (M : Set G)) (hδ2 : δ * δ = 1) {c : SL(2, ZMod 3)}
    (hfix : Q3T6.normalizerToAutSL3 e ⟨δ, hδ⟩ c = c) :
    ∃ x : ↥M, e (QuotientGroup.mk x) = c ∧ (x : G) * δ = δ * (x : G) := by
  obtain ⟨q, rfl⟩ := e.surjective c
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 := Q3T6.normalizerToAutSL3_apply e ⟨δ, hδ⟩ x₀
  rw [hfix] at h1
  have h2 : (QuotientGroup.mk x₀ : ↥M ⧸ classicalInvolutionOddCore ↥M) =
      QuotientGroup.mk (Disconnected.AschTight.normalizerConj M ⟨δ, hδ⟩ x₀) := e.injective h1
  rw [QuotientGroup.eq] at h2
  have hmem : (x₀ : G)⁻¹ * (δ * (x₀ : G) * δ⁻¹) ∈ M :=
    M.mul_mem (M.inv_mem x₀.2) ((Subgroup.mem_normalizer_iff.mp hδ x₀).mp x₀.2)
  have hx : (x₀ : G)⁻¹ * (δ * (x₀ : G) * δ⁻¹) ∈ oddCoreOf M := by
    refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
    have e1 : (⟨(x₀ : G)⁻¹ * (δ * (x₀ : G) * δ⁻¹), hmem⟩ : ↥M) =
        x₀⁻¹ * Disconnected.AschTight.normalizerConj M ⟨δ, hδ⟩ x₀ := rfl
    rw [e1]
    exact h2
  have hPδ : ∀ p ∈ oddCoreOf M, δ * p * δ⁻¹ ∈ oddCoreOf M := by
    intro p hp
    refine conj_mem_oddCoreOf_of_mem_normalizer (fun y hy => ?_) (fun y hy => ?_) hp
    · exact (Subgroup.mem_normalizer_iff.mp hδ y).mp hy
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hδ) y).mp hy
      rwa [inv_inv] at this
  obtain ⟨p, hp, hpe⟩ := Q3T6X.exists_fixed_mul_of_odd hδ2 (oddCoreOf_odd_natCard M) hPδ hx
  obtain ⟨hpM, hpO⟩ := mem_oddCoreOf_iff.mp hp
  refine ⟨⟨(x₀ : G) * p, M.mul_mem x₀.2 hpM⟩, ?_, hpe⟩
  have hmk : (QuotientGroup.mk x₀ : ↥M ⧸ classicalInvolutionOddCore ↥M) =
      QuotientGroup.mk (⟨(x₀ : G) * p, M.mul_mem x₀.2 hpM⟩ : ↥M) := by
    rw [QuotientGroup.eq]
    have e2 : x₀⁻¹ * (⟨(x₀ : G) * p, M.mul_mem x₀.2 hpM⟩ : ↥M) = ⟨p, hpM⟩ :=
      Subtype.ext (by simp)
    rw [e2]
    exact hpO
  exact congrArg e hmk.symm

theorem exists_pow_sq_eq_involution {L : Subgroup G} {e : G} (hL : IsUniqueInvolution L e) {c : G}
    (hcL : c ∈ L) (h4 : c ^ 4 ∈ oddCoreOf L) (h2 : c ^ 2 ∉ oddCoreOf L) :
    ∃ m : ℕ, Odd m ∧ c ^ m * c ^ m = e ∧ (c ^ m) ^ 4 = 1 := by
  have hodd : Odd (orderOf (c ^ 4)) :=
    (oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreOf L) h4)
  refine ⟨orderOf (c ^ 4), hodd, ?_, ?_⟩
  · set m := orderOf (c ^ 4) with hm
    have h44 : (c ^ m) ^ 4 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hm, pow_orderOf_eq_one]
    have hsq : (c ^ m * c ^ m) * (c ^ m * c ^ m) = 1 := by
      have : (c ^ m * c ^ m) * (c ^ m * c ^ m) = (c ^ m) ^ 4 := by group
      rw [this, h44]
    have hne : c ^ m * c ^ m ≠ 1 := by
      intro h1
      apply h2
      obtain ⟨j, hj⟩ := hodd
      have e1 : c ^ 2 = (c ^ m * c ^ m) * ((c ^ 4)⁻¹) ^ j := by
        rw [hj]
        have : c ^ (2 * j + 1) * c ^ (2 * j + 1) = c ^ 2 * (c ^ 4) ^ j := by
          rw [← pow_add, show 2 * j + 1 + (2 * j + 1) = 2 + 4 * j by ring, pow_add, pow_mul]
        rw [this, inv_pow, mul_assoc, mul_inv_cancel, mul_one]
      rw [e1, h1, one_mul]
      exact (oddCoreOf L).pow_mem ((oddCoreOf L).inv_mem h4) j
    have hmem : c ^ m * c ^ m ∈ L := L.mul_mem (L.pow_mem hcL m) (L.pow_mem hcL m)
    rcases hL.unique _ hmem hsq with h | h
    · exact absurd h hne
    · exact h
  · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]

end Lift

section Core


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem PspSetting.false_of_vertex_core (hset : PspSetting Ω K J S R T W z t K')
    {L : Subgroup G} (hL : L ∈ Ω) {l : G} (hl : IsUniqueInvolution L l)
    {M₀ : Subgroup G} (hM₀ : M₀ ∈ Ω) {e₀ : G} (h0 : IsUniqueInvolution M₀ e₀) {e₁ : G}
    (he₁2 : e₁ * e₁ = 1) (hP₁ : ∃ P : Subgroup G, IsSylow2In P M₀ ∧ ∀ x ∈ P, x * e₁ = e₁ * x)
    (hle₀ : e₀ * l = l * e₀) (hle₁ : e₁ * l = l * e₁) (hee : e₀ * e₁ = e₁ * e₀) (hLM : L ≠ M₀)
    (eL : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3))
    (hinn : ∀ he₀C : e₀ ∈ Subgroup.centralizer ({l} : Set G),
      centAct eL (hset.centralizer_le_normalizer_of_mem hL hl) ⟨e₀, he₀C⟩ ∈ Q3T6.inn3)
    (hn0 : ¬ ∃ P : Subgroup G, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({e₀} : Set G))
    (hn1 : ¬ ∃ P : Subgroup G, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({e₁} : Set G))
    (hn01 : ¬ ∃ P : Subgroup G, IsSylow2In P L ∧
      P ≤ Subgroup.centralizer ({e₀ * e₁} : Set G)) : False := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hl2 : l * l = 1 := hl.sq
  have he₀2 : e₀ * e₀ = 1 := h0.sq
  have hCNL := hset.centralizer_le_normalizer_of_mem hL hl
  obtain ⟨eM⟩ := hset.exists_iso_of_mem hM₀
  have hCNM := hset.centralizer_le_normalizer_of_mem hM₀ h0
  have he₀C : e₀ ∈ Subgroup.centralizer ({l} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hle₀
  have he₁C : e₁ ∈ Subgroup.centralizer ({l} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hle₁
  have hlC₀ : l ∈ Subgroup.centralizer ({e₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hle₀.symm
  have he₁C₀ : e₁ ∈ Subgroup.centralizer ({e₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hee.symm
  have hζ₀ : centAct eL hCNL ⟨e₀, he₀C⟩ ≠ 1 := fun h =>
    hn0 (exists_sylow_centralized_of_centAct_eq_one eL hCNL ⟨e₀, he₀C⟩ he₀2 h)
  have hζ₁ : centAct eL hCNL ⟨e₁, he₁C⟩ ≠ 1 := fun h =>
    hn1 (exists_sylow_centralized_of_centAct_eq_one eL hCNL ⟨e₁, he₁C⟩ he₁2 h)
  have hee2 : (e₀ * e₁) * (e₀ * e₁) = 1 := by
    calc (e₀ * e₁) * (e₀ * e₁) = e₀ * (e₁ * e₀) * e₁ := by group
      _ = e₀ * (e₀ * e₁) * e₁ := by rw [hee]
      _ = (e₀ * e₀) * (e₁ * e₁) := by group
      _ = 1 := by rw [he₀2, he₁2, one_mul]
  have he₀₁C : e₀ * e₁ ∈ Subgroup.centralizer ({l} : Set G) := Subgroup.mul_mem _ he₀C he₁C
  have hζ₀₁ : centAct eL hCNL ⟨e₀, he₀C⟩ * centAct eL hCNL ⟨e₁, he₁C⟩ ≠ 1 := by
    intro h
    apply hn01
    refine exists_sylow_centralized_of_centAct_eq_one eL hCNL ⟨e₀ * e₁, he₀₁C⟩ hee2 ?_
    rw [show (⟨e₀ * e₁, he₀₁C⟩ : ↥(Subgroup.centralizer ({l} : Set G))) =
      ⟨e₀, he₀C⟩ * ⟨e₁, he₁C⟩ from rfl, map_mul]
    exact h
  have hζ₀2 : centAct eL hCNL ⟨e₀, he₀C⟩ * centAct eL hCNL ⟨e₀, he₀C⟩ = 1 := by
    rw [← map_mul, show (⟨e₀, he₀C⟩ * ⟨e₀, he₀C⟩ : ↥(Subgroup.centralizer ({l} : Set G))) = 1
      from Subtype.ext he₀2, map_one]
  obtain ⟨g, hg⟩ := Q3T6.mem_inn3_iff.mp (hinn he₀C)
  obtain ⟨hg4, hg2⟩ := sl2_inner_involution (by rw [hg]; exact hζ₀2) (by rw [hg]; exact hζ₀)
  have hfix : Q3T6.normalizerToAutSL3 eL ⟨e₀, hCNL he₀C⟩ g = g := by
    have h1 : Q3T6.normalizerToAutSL3 eL ⟨e₀, hCNL he₀C⟩ = centAct eL hCNL ⟨e₀, he₀C⟩ := rfl
    rw [h1, ← hg]
    simp [MulAut.conj_apply]
  obtain ⟨x, hxc, hxe⟩ := exists_fixed_lift eL (hCNL he₀C) he₀2 hfix
  have h4 : (x : G) ^ 4 ∈ oddCoreOf L := by
    refine mem_oddCoreOf_iff.mpr ⟨(x ^ 4).2, ?_⟩
    have : eL (QuotientGroup.mk (x ^ 4)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, hxc, hg4]
    have h1 : (QuotientGroup.mk (x ^ 4) : ↥L ⧸ classicalInvolutionOddCore ↥L) = 1 :=
      eL.injective (by rw [this, map_one])
    exact (QuotientGroup.eq_one_iff _).mp h1
  have h2 : (x : G) ^ 2 ∉ oddCoreOf L := by
    intro hmem
    obtain ⟨hxL, hxO⟩ := mem_oddCoreOf_iff.mp hmem
    apply hg2
    have h1 : (QuotientGroup.mk (x ^ 2) : ↥L ⧸ classicalInvolutionOddCore ↥L) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hxO
    rw [← hxc, ← map_pow, ← QuotientGroup.mk_pow, h1, map_one]
  obtain ⟨m, hmodd, hm2, hm4⟩ := exists_pow_sq_eq_involution hl x.2 h4 h2
  obtain ⟨hxL, -⟩ : (x : G) ∈ L ∧ True := ⟨x.2, trivial⟩
  set c₂ : G := (x : G) ^ m with hc₂
  have hc₂L : c₂ ∈ L := L.pow_mem x.2 m
  have hc₂e : c₂ * e₀ = e₀ * c₂ := (Commute.pow_left (show Commute (x : G) e₀ from hxe) m).eq
  have hc₂sq : c₂ ^ 2 = l := by rw [pow_two]; exact hm2
  have hord : orderOf c₂ = 4 := by
    have hnot : ¬ c₂ ^ 2 ^ 1 = 1 := by
      rw [pow_one, hc₂sq]
      exact hl.ne_one
    have hfin : c₂ ^ 2 ^ (1 + 1) = 1 := by
      norm_num
      exact hm4
    have := orderOf_eq_prime_pow hnot hfin
    simpa using this
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers c₂) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hcard : 3 ≤ Nat.card ↥(Subgroup.zpowers c₂) := by
    rw [Nat.card_zpowers, hord]
    norm_num
  have hc₂N : Subgroup.zpowers c₂ ≤ Subgroup.normalizer (M₀ : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hM₀ hL (Ne.symm hLM) h0 (Subgroup.zpowers_le.mpr hc₂L)
      hP2 hcard (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc₂e))
  have hc₂mem : c₂ ∈ Subgroup.normalizer (M₀ : Set G) := hc₂N (Subgroup.mem_zpowers _)
  have hlN : l ∈ Subgroup.normalizer (M₀ : Set G) := hCNM hlC₀
  have hlg : Q3T6.normalizerToAutSL3 eM ⟨c₂, hc₂mem⟩ * Q3T6.normalizerToAutSL3 eM ⟨c₂, hc₂mem⟩ =
      Q3T6.normalizerToAutSL3 eM ⟨l, hlN⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hm2
  have hlinn : Q3T6.normalizerToAutSL3 eM ⟨l, hlN⟩ ∈ Q3T6.inn3 := by
    rw [← hlg]
    exact Subgroup.mul_self_mem_of_index_two Q3T6.inn3_index _
  have hl1 : Q3T6.normalizerToAutSL3 eM ⟨l, hlN⟩ ≠ 1 := by
    intro hlam
    have hex := exists_sylow_centralized_of_centAct_eq_one eM hCNM ⟨l, hlC₀⟩ hl2 hlam
    obtain ⟨P, hP, hPl⟩ := hex
    have he₀P : e₀ ∈ P := mem_of_isSylow2In_of_isUniqueInvolution h0 hP
    have hM₀c : Q3.IsClassicalMember3 M₀ e₀ :=
      Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hM₀ h0
    obtain ⟨u, hu, v, hv, huu, hvv, huv⟩ := exists_quaternion_pair_of_isSylow2In hM₀c hP he₀P
    have huC : u ∈ Subgroup.centralizer ({l} : Set G) := by
      have := hPl hu
      rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
      exact this
    have hvC : v ∈ Subgroup.centralizer ({l} : Set G) := by
      have := hPl hv
      rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
      exact this
    set ζ₀ := centAct eL hCNL ⟨e₀, he₀C⟩ with hζ₀def
    have hAA : centAct eL hCNL ⟨u, huC⟩ * centAct eL hCNL ⟨u, huC⟩ = ζ₀ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext huu
    have hBB : centAct eL hCNL ⟨v, hvC⟩ * centAct eL hCNL ⟨v, hvC⟩ = ζ₀ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hvv
    have hcc : centAct eL hCNL ⟨u, huC⟩ * centAct eL hCNL ⟨v, hvC⟩ * (centAct eL hCNL ⟨u, huC⟩)⁻¹ *
        (centAct eL hCNL ⟨v, hvC⟩)⁻¹ = ζ₀ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using huv)
    refine aut_s4b (A := centAct eL hCNL ⟨u, huC⟩) (B := centAct eL hCNL ⟨v, hvC⟩) (ζ := ζ₀)
      (ξa := 1) (ξb := 1) (ξc := 1) hζ₀ hζ₀2 ?_ ?_ (by rw [mul_one]; exact hAA)
      (by rw [mul_one]; exact hBB) (by rw [mul_one]; exact hcc) (by simp) (by simp) (by simp)
    · calc centAct eL hCNL ⟨u, huC⟩ * ζ₀ = centAct eL hCNL ⟨u, huC⟩ *
            (centAct eL hCNL ⟨u, huC⟩ * centAct eL hCNL ⟨u, huC⟩) := by rw [hAA]
        _ = (centAct eL hCNL ⟨u, huC⟩ * centAct eL hCNL ⟨u, huC⟩) *
            centAct eL hCNL ⟨u, huC⟩ := (mul_assoc _ _ _).symm
        _ = ζ₀ * centAct eL hCNL ⟨u, huC⟩ := by rw [hAA]
    · calc centAct eL hCNL ⟨v, hvC⟩ * ζ₀ = centAct eL hCNL ⟨v, hvC⟩ *
            (centAct eL hCNL ⟨v, hvC⟩ * centAct eL hCNL ⟨v, hvC⟩) := by rw [hBB]
        _ = (centAct eL hCNL ⟨v, hvC⟩ * centAct eL hCNL ⟨v, hvC⟩) *
            centAct eL hCNL ⟨v, hvC⟩ := (mul_assoc _ _ _).symm
        _ = ζ₀ * centAct eL hCNL ⟨v, hvC⟩ := by rw [hBB]
  have hlam2 : Q3T6.normalizerToAutSL3 eM ⟨l, hlN⟩ * Q3T6.normalizerToAutSL3 eM ⟨l, hlN⟩ = 1 := by
    rw [← map_mul, show (⟨l, hlN⟩ * ⟨l, hlN⟩ : ↥(Subgroup.normalizer (M₀ : Set G))) = 1 from
      Subtype.ext hl2, map_one]
  obtain ⟨d, hd⟩ := Q3T6.mem_inn3_iff.mp hlinn
  obtain ⟨hd4, hd2⟩ := sl2_inner_involution (by rw [hd]; exact hlam2) (by rw [hd]; exact hl1)
  have hfix' : Q3T6.normalizerToAutSL3 eM ⟨l, hlN⟩ d = d := by
    rw [← hd]
    simp [MulAut.conj_apply]
  obtain ⟨x', hx'c, hx'e⟩ := exists_fixed_lift eM hlN hl2 hfix'
  have h4' : (x' : G) ^ 4 ∈ oddCoreOf M₀ := by
    refine mem_oddCoreOf_iff.mpr ⟨(x' ^ 4).2, ?_⟩
    have : eM (QuotientGroup.mk (x' ^ 4)) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, hx'c, hd4]
    have h1 : (QuotientGroup.mk (x' ^ 4) : ↥M₀ ⧸ classicalInvolutionOddCore ↥M₀) = 1 :=
      eM.injective (by rw [this, map_one])
    exact (QuotientGroup.eq_one_iff _).mp h1
  have h2' : (x' : G) ^ 2 ∉ oddCoreOf M₀ := by
    intro hmem
    obtain ⟨hxL, hxO⟩ := mem_oddCoreOf_iff.mp hmem
    apply hd2
    have h1 : (QuotientGroup.mk (x' ^ 2) : ↥M₀ ⧸ classicalInvolutionOddCore ↥M₀) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hxO
    rw [← hx'c, ← map_pow, ← QuotientGroup.mk_pow, h1, map_one]
  obtain ⟨m', hm'odd, hm'2, hm'4⟩ := exists_pow_sq_eq_involution h0 x'.2 h4' h2'
  have hhM : (x' : G) ^ m' ∈ M₀ := M₀.pow_mem x'.2 m'
  have hhl : (x' : G) ^ m' * l = l * (x' : G) ^ m' :=
    (Commute.pow_left (show Commute (x' : G) l from hx'e) m').eq
  have hhC : (x' : G) ^ m' ∈ Subgroup.centralizer ({l} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hhl
  obtain ⟨ζ₀, hζ₀def⟩ : ∃ ζ₀, ζ₀ = centAct eL hCNL ⟨e₀, he₀C⟩ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A, A = centAct eL hCNL ⟨(x' : G) ^ m', hhC⟩ := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = centAct eL hCNL ⟨e₁, he₁C⟩ := ⟨_, rfl⟩
  have hA : A * A = ζ₀ := by
    rw [hAdef, hζ₀def, ← map_mul]
    congr 1
    exact Subtype.ext hm'2
  have hB2 : B * B = 1 := by
    rw [hBdef, ← map_mul, show (⟨e₁, he₁C⟩ * ⟨e₁, he₁C⟩ :
      ↥(Subgroup.centralizer ({l} : Set G))) = 1 from Subtype.ext he₁2, map_one]
  have hcomm : B * ζ₀ = ζ₀ * B := by
    rw [hBdef, hζ₀def, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hee.symm
  obtain ⟨P, hPsyl, hPcomm⟩ := hP₁
  have hE1 : centAct eM hCNM ⟨e₁, he₁C₀⟩ = 1 :=
    centAct_eq_one_of_commute_sylow eM hCNM hPsyl ⟨e₁, he₁C₀⟩ hPcomm
  have hnO : ⁅e₁, (x' : G) ^ m'⁆ ∈ oddCoreOf M₀ :=
    (centAct_eq_one_iff eM hCNM ⟨e₁, he₁C₀⟩).mp hE1 _ hhM
  obtain ⟨n, hn⟩ : ∃ n : ↥(Subgroup.centralizer ({l} : Set G)),
      n = ⟨e₁, he₁C⟩ * ⟨(x' : G) ^ m', hhC⟩ * ⟨e₁, he₁C⟩⁻¹ * ⟨(x' : G) ^ m', hhC⟩⁻¹ := ⟨_, rfl⟩
  have hnG : (n : G) = ⁅e₁, (x' : G) ^ m'⁆ := by
    rw [hn]
    simp [commutatorElement_def]
  have hconj : B * A * B⁻¹ = centAct eL hCNL n * A := by
    have e1 : (⟨e₁, he₁C⟩ * ⟨(x' : G) ^ m', hhC⟩ * ⟨e₁, he₁C⟩⁻¹ :
        ↥(Subgroup.centralizer ({l} : Set G))) = n * ⟨(x' : G) ^ m', hhC⟩ := by
      rw [hn]
      group
    calc B * A * B⁻¹ = centAct eL hCNL (⟨e₁, he₁C⟩ * ⟨(x' : G) ^ m', hhC⟩ * ⟨e₁, he₁C⟩⁻¹) := by
          rw [hAdef, hBdef, map_mul, map_mul, map_inv]
      _ = centAct eL hCNL (n * ⟨(x' : G) ^ m', hhC⟩) := by rw [e1]
      _ = centAct eL hCNL n * A := by rw [hAdef, map_mul]
  have hξ : Odd (orderOf (centAct eL hCNL n)) := by
    refine odd_orderOf_centAct eL hCNL n ?_
    rw [hnG]
    exact (oddCoreOf_odd_natCard M₀).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard (oddCoreOf M₀) hnO)
  refine aut_s4a (A := A) (B := B) (ζ := ζ₀) (ξ := centAct eL hCNL n) hA ?_ ?_ hB2 ?_ ?_ hcomm
    hconj hξ
  · rw [hζ₀def]
    exact hζ₀
  · rw [hζ₀def]
    exact hζ₀2
  · rw [hBdef]
    exact hζ₁
  · rw [hζ₀def, hBdef]
    exact hζ₀₁

theorem PspSetting.no_sylow_of_not_mem_omegaNbr (hset : PspSetting Ω K J S R T W z t K')
    {M : Subgroup G} (hM : M ∈ Ω) {m : G} (hm : IsUniqueInvolution M m) {L : Subgroup G}
    (hL : L ∈ Ω) (hLM : L ≠ M) (hnot : L ∉ omegaNbr Ω M) :
    ¬ ∃ P : Subgroup G, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({m} : Set G) := by
  rintro ⟨P, hP, hPC⟩
  exact hnot ⟨hL, hLM, P, mem_RSet_of_isSylow2In hL hP, hP.1, fun x hx =>
    hset.centralizer_le_normalizer_of_mem hM hm (hPC hx)⟩

theorem PspSetting.false_of_commuting_partner (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) {L : Subgroup G} (hL : L ∈ Ω) {e : G}
    (he : IsUniqueInvolution L e) (hez : e ≠ z) (hcz : e * z = z * e) (hct : e * t = t * e)
    (hno : ¬ ∃ P : Subgroup G, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({z} : Set G)) :
    False := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    hset.bad.normalizer_eq_centralizer
  have hzt := hset.mul_comm_zt
  have hz2 : z * z = 1 := hstd.hz.sq
  have ht2 : t * t = 1 := hstd.ht.sq
  have hLK : L ∉ omegaNbr Ω K := by
    rintro ⟨-, -, R', hR', hR'L, hR'N⟩
    exact hno ⟨R', Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hL hR' hR'L, hNC ▸ hR'N⟩
  have hLJ := hset.not_mem_omegaNbr_J hD hL he hez hcz hLK
  have hLK' := hset.not_mem_omegaNbr_K' hD hL he hez hcz hLK
  have hLneK : L ≠ K := by
    rintro rfl
    exact hez (he.eq hstd.hz)
  have hLneJ : L ≠ J := fun h => hLK (h ▸ hstd.hJ)
  have hLneK' : L ≠ K' := fun h => hLK (h ▸ hset.nbrK)
  have hnz := hno
  have hnt := hset.no_sylow_of_not_mem_omegaNbr hstd.hJ.1 hstd.ht hL hLneJ hLJ
  have hnzt := hset.no_sylow_of_not_mem_omegaNbr hset.nbrK.1 hset.uniq_mul hL hLneK' hLK'
  obtain ⟨t₁, t₂, t₃, R₁, R₂, R₃, hax⟩ := hset.bad.exists_axis_of_triangle hset.intrinsic
    hstd.stand.mem hstd.hJ hset.nbrK hset.nbrJ hstd.hz hstd.ht hset.uniq_mul rfl
  obtain ⟨eL⟩ := hset.exists_iso_of_mem hL
  have hCNL := hset.centralizer_le_normalizer_of_mem hL he
  have hzC : z ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcz.symm
  have htC : t ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
  have hinn := Q3T6.inn3_index
  have hztC : z * t ∈ Subgroup.centralizer ({e} : Set G) := Subgroup.mul_mem _ hzC htC
  by_cases hz_in : centAct eL hCNL ⟨z, hzC⟩ ∈ Q3T6.inn3
  ·
    exact hset.false_of_vertex_core hL he hstd.stand.mem hstd.hz ht2
      ⟨R₁, hax.syl₁, fun x hx => hax.comm₁₂ x hx t hax.z_mem₂⟩ hcz.symm hct.symm hzt hLneK
      eL (fun _ => hz_in) hnz hnt hnzt
  by_cases ht_in : centAct eL hCNL ⟨t, htC⟩ ∈ Q3T6.inn3
  ·
    refine hset.false_of_vertex_core hL he hstd.hJ.1 hstd.ht hz2
      ⟨R₂, hax.syl₂, fun x hx => (hax.comm₁₂ z hax.z_mem₁ x hx).symm⟩ hct.symm hcz.symm hzt.symm
      hLneJ eL (fun _ => ht_in) hnt hnz ?_
    rw [← hzt]
    exact hnzt
  ·
    have hprod : centAct eL hCNL ⟨z, hzC⟩ * centAct eL hCNL ⟨t, htC⟩ ∈ Q3T6.inn3 :=
      (Subgroup.mul_mem_iff_of_index_two hinn).mpr
        ⟨fun h => absurd h hz_in, fun h => absurd h ht_in⟩
    have hzt_in : ∀ h : z * t ∈ Subgroup.centralizer ({e} : Set G),
        centAct eL hCNL ⟨z * t, h⟩ ∈ Q3T6.inn3 := by
      intro h
      rw [show (⟨z * t, h⟩ : ↥(Subgroup.centralizer ({e} : Set G))) = ⟨z, hzC⟩ * ⟨t, htC⟩ from rfl,
        map_mul]
      exact hprod
    have hle : (z * t) * e = e * (z * t) := by
      calc (z * t) * e = z * (t * e) := by group
        _ = z * (e * t) := by rw [hct]
        _ = (z * e) * t := by group
        _ = (e * z) * t := by rw [hcz]
        _ = e * (z * t) := by group
    have hee : (z * t) * z = z * (z * t) := by
      calc (z * t) * z = z * (t * z) := by group
        _ = z * (z * t) := by rw [hzt]
    have hn01 : ¬ ∃ P : Subgroup G, IsSylow2In P L ∧
        P ≤ Subgroup.centralizer ({(z * t) * z} : Set G) := by
      have h1 : (z * t) * z = t := by
        calc (z * t) * z = z * (t * z) := by group
          _ = z * (z * t) := by rw [hzt]
          _ = (z * z) * t := by group
          _ = t := by rw [hz2, one_mul]
      rw [h1]
      exact hnt
    exact hset.false_of_vertex_core hL he hset.nbrK.1 hset.uniq_mul hz2
      ⟨R₃, hax.syl₃, fun x hx => (hax.comm₁₃ z hax.z_mem₁ x hx).symm⟩ hle hcz.symm hee hLneK'
      eL hzt_in hnzt hnz hn01

end Core

end CFSG.ClassicalInvolution.Q3.Q3AM
