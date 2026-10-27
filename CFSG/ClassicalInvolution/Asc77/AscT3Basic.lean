module

public import CFSG.ClassicalInvolution.Asc77.AscL62Quat
public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Asc77.T3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_of_isPGroup [Finite G] {K A : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hAK : A ≤ K) (hA : IsPGroup 2 A) (h2 : 2 ≤ Nat.card A) : z ∈ A := by
  have h2dvd : 2 ∣ Nat.card ↥A := by
    rcases hA.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    omega
  rcases hz.unique (t : G) (hAK t.2) htsq with h | h
  · exact absurd h htne
  · exact h ▸ t.2

@[expose] noncomputable def sylowOfIsSylow2In {V K : Subgroup G} (h : IsSylow2In V K) :
    Sylow 2 ↥K where
  toSubgroup := V.subgroupOf K
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
    rfl

private theorem natCard_isSylow2In_eq [Finite G] (K : Subgroup G) :
    Nat.card {R : Subgroup G // IsSylow2In R K} = Nat.card (Sylow 2 ↥K) := by
  refine Nat.card_congr
    { toFun := fun R => sylowOfIsSylow2In R.2
      invFun := fun P => ⟨(P : Subgroup ↥K).map K.subtype, isSylow2In_map_sylow K P⟩
      left_inv := fun R => ?_
      right_inv := fun P => ?_ }
  · exact Subtype.ext (Subgroup.map_subgroupOf_eq_of_le R.2.1)
  · apply Sylow.ext
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem exists_sylow_normalized [Finite G] {K W : Subgroup G} (hW : IsPGroup 2 W)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) :
    ∃ R : Subgroup G, IsSylow2In R K ∧ ∀ w ∈ W, conjSub w R = R := by
  have hinv : ∀ w ∈ W, ∀ R ∈ {R : Subgroup G | IsSylow2In R K}, conjSub w R ∈
      {R : Subgroup G | IsSylow2In R K} := by
    intro w hw R hR
    have := IsSylow2In.conj hR w
    rwa [mem_normalizer_iff_conjSub_eq.mp (hWK hw)] at this
  have hodd : ¬ 2 ∣ Nat.card ↥{R : Subgroup G | IsSylow2In R K} := by
    have h1 : Nat.card ↥{R : Subgroup G | IsSylow2In R K} = Nat.card (Sylow 2 ↥K) :=
      natCard_isSylow2In_eq K
    rw [h1]
    exact not_dvd_card_sylow 2 ↥K
  obtain ⟨R, hR, hfix⟩ := exists_fixed_conjSub hW hinv hodd
  exact ⟨R, hR, hfix⟩

section Members

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem isPGroup_two_bot' : IsPGroup 2 (⊥ : Subgroup G) :=
  IsPGroup.of_card (n := 0) (by simp)

theorem omegaNbr_subset_omegaStarNbr [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (K : Subgroup G) : omegaNbr Ω K ⊆ omegaStarNbr Ω K := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  obtain ⟨U, hUR, hUc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_cyclic_index_two
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    have hU0 : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  exact ⟨hJ, hJK, U, ⟨R, hR, hUR, hUc, hrel⟩, hUR.trans hRJ, hUR.trans hRN⟩

theorem twin_mem_omegaNbr [Finite G] (hΩ : HypOmegaMod p f Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) (hLK : L ≠ K) {z : G} (hzK : IsUniqueInvolution K z)
    (hzL : IsUniqueInvolution L z) : L ∈ omegaNbr Ω K := by
  obtain ⟨R, hR, hRL, -⟩ := exists_mem_RSet_ge hL (isPGroup_two_bot' (G := G)) bot_le
  exact ⟨hL, hLK, R, hR, hRL.1, hRL.1.trans (hΩ.le_normalizer_of_twin hL hK hLK hzL hzK)⟩

theorem mem_normalizer_of_mem_omegaStarNbr [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    j ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hU
  have hU2 := hΩ.isPGroup_of_mem_USet hp hU
  exact hUN (mem_of_isPGroup hj hUJ hU2 (by omega))

theorem commute_of_mem_omegaStarNbr [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K) {z j : G} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) : z * j = j * z := by
  have h1 := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp
    (mem_normalizer_of_mem_omegaStarNbr hp hΩ hJ hj))
  exact (by
    have := h1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm)

end Members

section Violation

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

structure AViol (Ω : Set (Subgroup G)) (K J : Subgroup G) (zK zJ : G) : Prop where
  star : J ∈ omegaStarNbr Ω K
  not_nbr : J ∉ omegaNbr Ω K
  hzK : IsUniqueInvolution K zK
  hzJ : IsUniqueInvolution J zJ
  no_conj : ∀ g ∈ pairNormalizers K J zK zJ, conjSub g K ≠ J

theorem not_aEmpty_iff {K : Subgroup G} :
    ¬ AEmpty Ω K ↔ ∃ J zK zJ, AViol Ω K J zK zJ := by
  unfold AEmpty
  push Not
  constructor
  · rintro ⟨J, hJ, hJn, zK, zJ, hzK, hzJ, hg⟩
    exact ⟨J, zK, zJ, ⟨hJ, hJn, hzK, hzJ, hg⟩⟩
  · rintro ⟨J, zK, zJ, ⟨hJ, hJn, hzK, hzJ, hg⟩⟩
    exact ⟨J, hJ, hJn, zK, zJ, hzK, hzJ, hg⟩

namespace AViol

variable {K J : Subgroup G} {zK zJ : G}

theorem mem (h : AViol Ω K J zK zJ) : J ∈ Ω := h.star.1

theorem ne (h : AViol Ω K J zK zJ) : J ≠ K := h.star.2.1

theorem comm [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h : AViol Ω K J zK zJ) :
    zK * zJ = zJ * zK :=
  commute_of_mem_omegaStarNbr hp hΩ h.star h.hzK h.hzJ

theorem ne_involution [Finite G] (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω) (h : AViol Ω K J zK zJ) :
    zJ ≠ zK := by
  intro he
  subst he
  exact h.not_nbr (twin_mem_omegaNbr hΩ hK h.mem h.ne h.hzK h.hzJ)

end AViol

end Violation

section Pair

theorem mem_normalizer_closure_pair [Finite G] {g z j : G}
    (hz : g * z * g⁻¹ ∈ Subgroup.closure ({z, j} : Set G))
    (hj : g * j * g⁻¹ ∈ Subgroup.closure ({z, j} : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
  set Z : Subgroup G := Subgroup.closure ({z, j} : Set G) with hZ
  have hle : conjSub g Z ≤ Z := by
    unfold conjSub
    rw [Subgroup.map_le_iff_le_comap, hZ, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hz
    · exact hj
  have heq : conjSub g Z = Z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_conjSub])
  exact mem_normalizer_iff_conjSub_eq.mpr heq

theorem exists_centralizing_of_twin {K K' : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {g : G} (hg : conjSub g K = K') : g * z * g⁻¹ = z := by
  subst hg
  exact (hz.conj g).eq hz'

end Pair

end CFSG.ClassicalInvolution.Asc77.T3
