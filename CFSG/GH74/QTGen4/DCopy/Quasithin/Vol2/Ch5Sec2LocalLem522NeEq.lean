module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEq
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5112Loc
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeSteps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem stmt5_2_2_ne_eq_of_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hF : FactL2LieParabolic) (hLie : Stmt5_2_L2Lie_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h512 : Stmt5_1_12_loc_F4)
    (hlie : Stmt5_1_13_loc_lie) (hD42 : Stmt5_2_2_eq_D42_F4) (h3 : Stmt5_2_2_eq_three_F4)
    (hcart : Stmt5_2_2_eq_cartan_F4) : Stmt5_2_2_ne_eq_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₀syl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hT₀N : T₀ ≤ Subgroup.normalizer (L₂ : Set G) := inf_le_right
  have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans (le_sup_left.trans le_sup_left)
  have hT₀X : T₀ ≤ X₀ := le_sup_right.trans le_sup_left
  have hDpX : Dp ≤ X₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)

  obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
  obtain ⟨hL₂c, k, hk, hbend⟩ : L₂ ∈ cComp L₂ ∧ ∃ k, 2 ≤ k ∧ IsBenderCh5 k (O2Q L₂) := by
    rcases hcase with ⟨⟨k, hk, hB⟩, rfl⟩ | ⟨hnb, hK1eq, P, hP, hL₂P⟩
    · exact ⟨cComp_mem_of_le hK₁ le_rfl (le_of_mem_cComp hK₁), k, hk, hB⟩
    · obtain ⟨k, hk, htype, -, hMK⟩ :=
        nonBender_type_F4 h510 hyp.toHyp5_1_8 hyp.notation59 hK₁ hnb hK1eq
      have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
        A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
      obtain ⟨-, hpsl, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
      exact ⟨cComp_mem_of_le hL₂P le_rfl (le_of_mem_cComp hL₂P), k, hk,
        Or.inl (Or.inl ⟨by decide, hpsl⟩)⟩
  have hL₂T₀ : L₂ ∈ lFamily T₀ := by
    refine cComp_mem_of_subnormal (IsSubnormal.step le_sup_left ?_ (IsSubnormal.refl _)) hL₂c
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT₀N)

  obtain ⟨Lh, ⟨hLh, hL₂Lh⟩, huniq⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc h37 h39 hOX hT₀syl hL₂X hL₂T₀
  have hhat : IsHatComp X₀ L₂ Lh := ⟨hLh, hL₂Lh, fun Y hY hL₂Y => huniq Y ⟨hY, hL₂Y⟩⟩
  have hT₀Lh : T₀ ≤ Subgroup.normalizer (Lh : Set G) := by
    intro t ht
    have hKt : Lh.map (MulAut.conj t).toMonoidHom ∈ cComp X₀ := map_conj_mem_cComp hLh (hT₀X ht)
    have hL₂t : L₂ ≤ Lh.map (MulAut.conj t).toMonoidHom := by
      intro x hx
      have hx' : t⁻¹ * x * t⁻¹⁻¹ ∈ L₂ :=
        (Subgroup.mem_normalizer_iff.mp (hT₀N (T₀.inv_mem ht)) x).mp hx
      refine ⟨t⁻¹ * x * t, hL₂Lh (by simpa using hx'), ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    exact A38.map_conj_eq_iff.mp (hhat.2.2 _ hKt hL₂t)
  have hXN : X₀ ≤ Subgroup.normalizer (Lh : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hOX hT₀syl hLh
    rwa [Emb512.conjClosure_hat_eq hT₀Lh] at this
  have hlt : L₂ < Lh := lt_of_le_of_ne hL₂Lh fun heq => hDp (by
    rw [heq]
    exact hDpX.trans hXN)

  have hodd : ∀ m ∈ Dp, Odd (orderOf m) := by
    intro m hm
    have h1 : orderOf m ∣ p := by
      rw [← hyp.card_Dp]
      have := orderOf_dvd_natCard (⟨m, hm⟩ : ↥Dp)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (by rcases hyp.p_cases with rfl | rfl <;> decide) h1

  have case34 : ∀ k : ℕ, ((SuzukiModel (O2Q L₂) 2 k ∧ Is2F4 k (O2Q Lh)) ∨
      (LieModel (O2Q L₂) .PSL 2 2 k ∧ IsRank2LieChar2 (O2Q Lh))) → False := by
    intro k htype
    by_cases hres : ∃ U P : Subgroup (O2Q Lh), IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ P ⋖ ⊤ ∧
        Group.IsSolvable ↥P
    · exact hD42 G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₀syl Lh k hhat hlt
        htype hres
    ·
      have hD := hyp.notation59.2.1
      have hDcyc := (h.isCyclic_card_of_isHall l2TorusFact hD).1
      have hDs : Group.IsSolvable ↥D := by
        have := hDcyc
        exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
      have hTLs : Group.IsSolvable ↥(T ⊓ L) := by
        have := (h.sylow.1.to_le (inf_le_left : T ⊓ L ≤ T)).isNilpotent
        infer_instance
      have hBs : Group.IsSolvable ↥(borelL T L) := by
        rw [← h.borelL_eq_sup hD, sup_comm]
        exact A3.isSolvable_sup_of_le_normalizer (hD.1.trans inf_le_right)
      have hBTs : Group.IsSolvable ↥(borelL T L ⊔ T) := by
        have : Group.IsSolvable ↥T := by
          have := h.sylow.1.isNilpotent
          infer_instance
        exact A3.isSolvable_sup_of_le_normalizer h.T_le_normalizer_borel
      have hAs : Group.IsSolvable ↥((borelL T L ⊔ T) ⊓ X₀) :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (inf_le_left : (borelL T L ⊔ T) ⊓ X₀ ≤ _))
          (Subgroup.inclusion_injective _)
      have hT₀A : T₀ ≤ (borelL T L ⊔ T) ⊓ X₀ := le_inf (inf_le_left.trans le_sup_right) hT₀X
      have hDpA : Dp ≤ (borelL T L ⊔ T) ⊓ X₀ :=
        le_inf ((hyp.Dp_le.trans hD.1).trans le_sup_left) hDpX
      apply hDp
      intro m hm
      exact hlie G h.simple h.nonabelian h.qtke T₀ X₀ L₂ Lh ((borelL T L ⊔ T) ⊓ X₀) k hOX
        hT₀syl hL₂X hL₂T₀ hT₀N hhat hlt htype hres hT₀A inf_le_right hAs m (hDpA hm)
        (hodd m hm)
  rcases h512 G h.simple h.nonabelian h.qtke T₀ X₀ L₂ Lh k hk hOX hT₀syl hL₂X hL₂T₀ hT₀N hhat hlt
      hbend with h3' | h4' | ⟨hL4, hnl, h314⟩
  · exact case34 k (Or.inl h3')
  · exact case34 k (Or.inr h4')
  ·
    by_cases hR2 : IsRank2LieChar2 (O2Q Lh)
    · exact case34 2 (Or.inr ⟨hL4, hR2⟩)
    have hp3 : p = 3 :=
      h3 G T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp hT₀syl Lh hhat hlt hL4 hnl hR2
        h314
    obtain ⟨hBel, hB9, -⟩ := hcart G T M L V H B D L₂ Dp n p hyp hL₂K hL4
    have hD := hyp.notation59.2.1
    have hDcyc : IsCyclic ↥D := (h.isCyclic_card_of_isHall l2TorusFact hD).1
    have hDp3 : Nat.card ↥Dp = 3 := hyp.card_Dp.trans hp3

    have hBDp : B ≤ Subgroup.normalizer (Dp : Set G) := fun b hb =>
      mem_normalizer_of_le_of_isCyclic hDcyc hyp.Dp_le (hyp.notation59.2.2 hb)
    have hBM : B ≤ M := hyp.notation59.1.1.trans inf_le_left
    have hDpM : Dp ≤ M :=
      (hyp.Dp_le.trans (hyp.notation59.2.1.1.trans inf_le_left)).trans h.L_le
    have hBN := hyp.B_le_normalizer_L2_F4 h510 h331 hR hLie
    exact false_of_card_three_of_elemAbelian_nine h.qtke h.maxTwoLocal.1 hBel hB9 hDp3 hBM hDpM
      hBDp fun hle => hDp (hle.trans hBN)

end CFSG.Quasithin.H13
