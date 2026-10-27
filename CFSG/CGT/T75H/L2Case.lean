module

public import CFSG.CGT.T75H.DihedralS
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.Adapters.StatedPSLTwoSeven

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem isKleinFour_map {X : Type} [Group X] {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (h4 : Nat.card T = 4) (e : G ≃* X) : IsKleinFour (T.map e.toMonoidHom) where
  card_four := by rw [Subgroup.card_map_of_injective e.injective, h4]
  exponent_two := by
    have hcard : Nat.card (T.map e.toMonoidHom) = 4 := by
      rw [Subgroup.card_map_of_injective e.injective, h4]
    have : Finite (T.map e.toMonoidHom) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have : Nontrivial (T.map e.toMonoidHom) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hg
      apply Subtype.ext
      rw [← hxg]
      simp
    rw [← Subgroup.orderOf_coe, ← hxg]
    have h2 : orderOf x = 2 := orderOf_eq_prime (hT.2 x hx) hx1
    show orderOf (e x) = 2
    rw [MulEquiv.orderOf_eq, h2]

theorem exists_eps (q : ℕ) (hq : Odd q) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((q : ℤ) ≡ ε [ZMOD 4]) := by
  obtain ⟨m, hm⟩ := hq
  rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
  · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩

theorem statedClassicalModel_psl_three_two_of_psl_two_seven {X : Type} [Group X]
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 7 1) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven hX

theorem card_centralizer_singleton_equiv {X : Type} [Group X] (e : G ≃* X) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set X)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨e.symm z, ?_⟩
      invFun := fun w => ⟨e w, ?_⟩
      left_inv := fun z => ?_
      right_inv := fun w => ?_ }
  · have := Subgroup.mem_centralizer_singleton_iff.1 z.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg e.symm this
    simpa using h
  · have := Subgroup.mem_centralizer_singleton_iff.1 w.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg e this
  · exact Subtype.ext (by simp)
  · exact Subtype.ext (by simp)

theorem centralizer_eq_of_psl2 {K : Type} [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    (e : G ≃* CFSG.GorensteinWalter.PSL2 K) {T : Subgroup G} (hT : IsElemAbelian 2 T)
    (h4 : Nat.card T = 4) :
    ∀ x : G, (∀ t ∈ T, t * x = x * t) → x ∈ T := by
  intro x hx
  have hV := isKleinFour_map hT h4 e
  have hC := CFSG.GorensteinWalter.psl2_kleinFour_centralizer_eq_self K hK _ hV
  have hmem : e x ∈ Subgroup.centralizer ((T.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    simpa using congrArg e (hx t ht)
  rw [hC] at hmem
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hmem
  have : t = x := e.injective hte
  rwa [← this]

theorem card_centralizer_le_eight [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    (hwc : IsWC T) (hT4 : Nat.card T = 4) (hCT : ∀ x : G, (∀ t ∈ T, t * x = x * t) → x ∈ T) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) ≤ 8 := by
  set C := Subgroup.centralizer ({a} : Set G) with hCdef
  have hCN : C ≤ Subgroup.normalizer (T : Set G) := hwc.centralizer_le_normalizer D.haT D.ha1
  have horb : {v : G | ∃ h ∈ C, v = h * b * h⁻¹} ⊆ {b, b * a} := by
    rintro _ ⟨h, hh, rfl⟩
    have hv : h * b * h⁻¹ ∈ T := conj_mem_of_mem_normalizer (hCN hh) D.hb
    have hha : h * a = a * h := Subgroup.mem_centralizer_singleton_iff.1 hh
    rcases D.hT _ hv with h1 | h1 | h1 | h1
    · exfalso
      apply D.hbL
      have : b = 1 := by
        calc b = h⁻¹ * (h * b * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group
      rw [this]; exact (normIn T T₁).one_mem
    · exfalso
      apply D.hbL
      have : b = a := by
        calc b = h⁻¹ * (h * b * h⁻¹) * h := by group
          _ = h⁻¹ * a * h := by rw [h1]
          _ = h⁻¹ * (a * h) := by group
          _ = h⁻¹ * (h * a) := by rw [hha]
          _ = a := by group
      rw [this]; exact D.ha
    · exact Or.inl h1
    · exact Or.inr h1
  have hncard : Set.ncard {v : G | ∃ h ∈ C, v = h * b * h⁻¹} ≤ 2 := by
    refine (Set.ncard_le_ncard horb (Set.toFinite _)).trans ?_
    exact (Set.ncard_insert_le b {b * a}).trans (by simp)
  have hstab : C ⊓ Subgroup.centralizer ({b} : Set G) ≤ T := by
    rintro x ⟨hxa, hxb⟩
    have hxa' : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hxa
    have hxb' : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hxb
    exact hCT x (D.comm_of_ab (c := x) hxa'.symm hxb'.symm)
  have hcard := card_eq_ncard_orbit_mul_card_centralizer C b
  calc Nat.card C = _ := hcard
    _ ≤ 2 * 4 := Nat.mul_le_mul hncard (hT4 ▸ Subgroup.card_le_of_le hstab)
    _ = 8 := by norm_num

theorem listGroup_of_psl2 [Finite G] (hc : Sec6Ctx T T₁ 2 1) {ℓ a b y : G}
    (D : D8Data T T₁ ℓ a b y) {S : Sylow 2 G} (hS : SylowData T T₁ S) (hC : Cbar T T₁ S = ⊥)
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (h5 : 5 ≤ p ^ k)
    (e : G ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p k)) : ListGroup G := by
  classical
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  have hFcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p k)) :=
    ⟨p, k, Fact.out, hp, Nat.one_le_iff_ne_zero.2 hk, hFcard⟩
  have hT4 : Nat.card T = 4 := by simpa using hc.hT
  have hCT := centralizer_eq_of_psl2 hK e hc.hy.pair.wc.1 hT4
  have hle8 := card_centralizer_le_eight D hc.hy.pair.wc hT4 hCT
  obtain ⟨eS⟩ := sylow_equiv_dihedral D hS hC
  have hS8 : Nat.card (S : Subgroup G) = 8 := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hSa : (S : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [sylow_eq_sStar_of_Cbar_bot D hS hC]
    refine sup_le (fun t ht => ?_) (fun t ht => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (elemAbelian_mul_comm hc.hy.pair.wc.1 ht D.haT)
    · rcases D.hL₁ t ht with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_centralizer_singleton_iff.2 D.comm_aℓ.symm
  have hge8 : 8 ≤ Nat.card (Subgroup.centralizer ({a} : Set G)) :=
    hS8 ▸ Subgroup.card_le_of_le hSa
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ((Nat.card (GaloisField p k) : ℤ) ≡ ε [ZMOD 4]) := by
    rw [hFcard]
    exact exists_eps (p ^ k) hp.pow
  have ht : orderOf (e a) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact D.aa) D.ha1
  obtain ⟨m, hm2, ⟨eC⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hK hε hε1 ht
  have hcardC : 2 * m = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
    rw [← card_centralizer_singleton_equiv e a, Nat.card_congr eC.toEquiv,
      DihedralGroup.nat_card]
  have hq8 : (Nat.card (GaloisField p k) : ℤ) - ε = 8 := by
    rw [← hm2]
    have : 2 * m = 8 := by omega
    omega
  rw [hFcard] at hq8
  rcases hε1 with rfl | rfl
  ·
    have h9 : p ^ k = 9 := by omega
    have : Fintype (GaloisField p k) := Fintype.ofFinite _
    have hcard9 : Fintype.card (GaloisField p k) = 9 := by
      rw [Fintype.card_eq_nat_card, hFcard, h9]
    obtain ⟨e6⟩ :=
      unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField p k) hcard9
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, by norm_num, ⟨e.trans e6⟩⟩)))
  ·
    have h7 : p ^ k = 7 := by omega
    obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).1 h7
    have hm7 := CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv G 7 1 h5 e
    exact Or.inl ⟨3, 1, by norm_num, le_rfl,
      statedClassicalModel_psl_three_two_of_psl_two_seven hm7⟩

theorem listGroup_of_Cbar_bot [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hc : Sec6Ctx T T₁ 2 1) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) {S : Sylow 2 G}
    (hS : SylowData T T₁ S) (hC : Cbar T T₁ S = ⊥) : ListGroup G := by
  obtain ⟨eS⟩ := sylow_equiv_dihedral D hS hC
  rcases CFSG.GorensteinWalter.gorenstein_walter G hna S ⟨4, ⟨eS⟩⟩ with
    h7 | ⟨p, k, hp, hodd, h5, he⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨7, by norm_num, by norm_num, h7⟩)))
  · obtain ⟨e⟩ := he
    exact listGroup_of_psl2 hc D hS hC hodd h5 e

end CFSG.CGT.T75H
