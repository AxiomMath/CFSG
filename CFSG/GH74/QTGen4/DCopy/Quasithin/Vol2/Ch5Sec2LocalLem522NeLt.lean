module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeLt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeSteps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem stmt5_2_2_ne_lt_of_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (h515 : Stmt5_1_5_F4) (h5113 : Stmt5_1_13C_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) : Stmt5_2_2_ne_lt_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp T₁ hT₁ hlt hT₁syl hT₁M hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  set K := oTwoUpper H with hKdef
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1

  have hTY : IsSylowTwoOf T (T ⊔ T₁) := h.isSylowTwoOf le_sup_left
  have hT₁Y : IsSylowTwoOf T₁ (T ⊔ T₁) := isSylowTwoOf_of_isSylowTwo hT₁syl le_sup_right
  obtain ⟨y, hyY, hy⟩ := A4.exists_conj_of_isSylowTwoOf hTY hT₁Y
  have hT₁eq : T.map (MulAut.conj y).toMonoidHom = T₁ := by
    ext x
    rw [hy x, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have e : y⁻¹ * ((MulAut.conj y).toMonoidHom t) * y = t := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact ht
    · intro hx
      exact ⟨y⁻¹ * x * y, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hTKN : T ≤ Subgroup.normalizer (K : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hT₁KN : T₁ ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK]
    exact le_normalizer_conjClosure L₂ T₁
  have hyM : y ∈ M := (sup_le h.T_le hT₁M) hyY
  have hyK : K.map (MulAut.conj y).toMonoidHom = K :=
    map_conj_eq_of_mem_normalizer_ch6 ((sup_le hTKN hT₁KN) hyY)

  set H₀ := H.map (MulAut.conj y).toMonoidHom with hH₀def
  have hyp₁ : Hyp5_1_8 G T₁ M L H₀ n := hT₁eq ▸ hyp.toHyp5_1_8.conj_of_mem hyM
  have hKH₀ : oTwoUpper H₀ = K := by rw [hH₀def, oTwoUpper_map, ← hKdef, hyK]

  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hTLT₀ : T ⊓ L ≤ T₀ := by
    intro x hx
    have hxS : x ∈ S ⊓ L := by
      rw [hSL]
      exact hx
    exact ⟨hx.1, hyp.S_le hxS.1⟩
  have hTL₁ : T₁ ⊓ L = T ⊓ L := by
    have hle : T ⊓ L ≤ T₁ ⊓ L := le_inf (hTLT₀.trans hlt.le) inf_le_right
    have hyL : y ∈ Subgroup.normalizer (L : Set G) := h.normal hyM
    have hcard : Nat.card ↥(T₁ ⊓ L) = Nat.card ↥(T ⊓ L) := by
      have e : (T ⊓ L).map (MulAut.conj y).toMonoidHom = T₁ ⊓ L := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj y).injective, hT₁eq,
          map_conj_eq_of_mem_normalizer_ch6 hyL]
      rw [← e, Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hD₁ : Lin2.IsHallTwoPrimeOf D (borelL T₁ L) := by
    show Lin2.IsHallTwoPrimeOf D (L ⊓ Subgroup.normalizer ((T₁ ⊓ L : Subgroup G) : Set G))
    rw [hTL₁]
    exact hyp.notation59.2.1

  obtain ⟨-, -, h5152⟩ := h515 G T₁ M L H₀ D n hyp₁.toHyp5_0_1 hyp₁.hStar hD₁
  obtain ⟨-, B₁, hB₁, hB₁D⟩ := h5152 hyp₁.lieQuot
  have hN₁ : IsNotation5_1_9 T₁ M L H₀ B₁ D := ⟨inf_comm M H₀ ▸ hB₁, hD₁, hB₁D⟩

  have hV₁ : IsCh5Module T₁ L (V.map (MulAut.conj y).toMonoidHom) :=
    hT₁eq ▸ hyp.ch5Module.conj_of_mem (h.normal hyM)

  obtain ⟨K₁, hK₁, hKeq, -⟩ := hyp.choice
  set K₁' := K₁.map (MulAut.conj y).toMonoidHom with hK₁'def
  have hK₁' : quasithinIsCComponent K₁' H₀ := quasithinIsCComponent_map (MulAut.conj y) hK₁
  have hKeq' : oTwoUpper H₀ = conjClosure K₁' T₁ := by
    rw [hH₀def, oTwoUpper_map, hKeq, map_conjClosure_eq, hT₁eq]

  have hT₁X : T₁ ≤ X₀ := hT₁.1
  have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans (le_sup_left.trans le_sup_left)
  have hKX : K ≤ X₀ := by
    rw [hK]
    exact conjClosure_le fun t ht z hz =>
      X₀.mul_mem (X₀.mul_mem (hT₁X ht) (hL₂X hz)) (X₀.inv_mem (hT₁X ht))
  have hH₀X : H₀ ≤ X₀ := by
    have e : H₀ = K ⊔ T₁ := by
      rw [hH₀def, eq_oTwoUpper_sup_of_isSylowTwoOf' hTH, Subgroup.map_sup, ← hKdef, hyK, hT₁eq]
    rw [e]
    exact sup_le hKX hT₁X
  have hX : InH H₀ X₀ := ⟨hH₀X, hOX⟩

  have hK₁'H₀ : K₁' ≤ H₀ := A3.subnormal_le hK₁'.2.2.1
  have hT₁H₀ : T₁ ≤ H₀ := hyp₁.hStar.1.1
  have hK₁'loc : K₁' ∈ lFamily T₁ := cComp_mem_of_le hK₁' le_sup_left (sup_le hK₁'H₀ hT₁H₀)
  obtain ⟨Kh₁, ⟨hKh₁, hK₁Kh₁⟩, huniq⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc h37 h39 hOX hT₁
      (hK₁'H₀.trans hH₀X) hK₁'loc
  have hhat : IsHatComp X₀ K₁' Kh₁ := ⟨hKh₁, hK₁Kh₁, fun Y hY hK₁Y => huniq Y ⟨hY, hK₁Y⟩⟩

  rcases h5113 G T₁ M L (V.map (MulAut.conj y).toMonoidHom) H₀ B₁ D K₁' X₀ Kh₁ n hyp₁ hN₁ hV₁
      hK₁' hKeq' hX hhat with h1 | h2 | h3
  · apply hyp.Dp_not_le
    have hDpX : Dp ≤ X₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
    have := (le_inf hyp.Dp_le hDpX).trans h1
    rwa [hKH₀] at this
  · have h4 : LieModel (O2Q K) .PSL 2 2 2 := by
      rw [← hKH₀]
      exact h2.1
    exact hyp.false_of_lieModel_two h38 hL₂K h4
  · have h8 : LieModel (O2Q K) .PSL 2 2 3 := by
      rw [← hKH₀]
      exact h3.1
    exact hyp.false_of_lieModel_PSL2 h38 hL₂K (by norm_num) h8

end CFSG.Quasithin.H13
