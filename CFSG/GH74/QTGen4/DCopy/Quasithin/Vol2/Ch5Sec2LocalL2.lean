module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem ch5L2ChoiceExists_of_F4 (h510 : Stmt5_1_10_F4) (hRP : RankTwoParabolicFact) :
    Ch5L2ChoiceExists_F4 := by
  intro G _ _ T M L H B D n hyp hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨k, hk, hBorel, -, K₁, hK₁, hKeq, hcases⟩ := h510 G T M L H B D n hyp hN
  have hk2 : 2 ≤ k := hk.1
  by_cases hBe : IsBenderAny (O2Q K₁)
  · exact ⟨K₁, K₁, hK₁, hKeq, Or.inl ⟨hBe, rfl⟩⟩
  have h3 : K₁ = oTwoUpper H ∧
      (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) := by
    rcases hcases with ⟨-, h1⟩ | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · exfalso
      apply hBe
      refine ⟨k, hk2, ?_⟩
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · exfalso
      apply hBe
      rw [h1]
      exact ⟨k, hk2, h2⟩
    · exact ⟨h1, h2⟩
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH hKH hHK
  obtain ⟨S₀, hS₀, hMK⟩ := hBorel
  have hTKM : T ⊓ oTwoUpper H ≤ M ⊓ oTwoUpper H := inf_le_inf_right _ h.T_le
  have hS₀eq : T ⊓ oTwoUpper H = S₀ := by
    have hS₀MK : S₀ ≤ M ⊓ oTwoUpper H := by
      rw [hMK]
      exact le_inf hS₀.1 Subgroup.le_normalizer
    have hMKS : M ⊓ oTwoUpper H ≤ Subgroup.normalizer (S₀ : Set G) := by
      rw [hMK]
      exact inf_le_right
    have hS₀syl : IsSylowTwoOf S₀ (M ⊓ oTwoUpper H) := A4.isSylowTwoOf_mono hS₀ hS₀MK inf_le_right
    have hTsyl : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
      A4.isSylowTwoOf_mono hTK hTKM inf_le_right
    have hS₀O : S₀ ≤ pCoreOf 2 (M ⊓ oTwoUpper H) :=
      le_pCoreOf_of_le_normalizer 2 hS₀MK hMKS hS₀.2.1
    have hS₀T : S₀ ≤ T ⊓ oTwoUpper H := hS₀O.trans (F7.isSylowTwoOf_pCoreOf_le hTsyl)
    exact eq_of_isSylowTwoOf_of_le hS₀ hS₀T inf_le_right hTK.2.1
  have hB₀ : oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) =
      M ⊓ oTwoUpper H := by
    rw [hMK, hS₀eq]
  have hKM : ¬ oTwoUpper H ≤ M := by
    intro hle
    apply hH.2.1
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hTH]
    exact sup_le hle h.T_le
  have hB₀ne : oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≠
      oTwoUpper H := by
    rw [hB₀]
    intro heq
    exact hKM (heq ▸ inf_le_left)
  obtain ⟨P, hBP, hPK, hPne, hPmax⟩ := exists_maximal_proper_ge inf_le_left hB₀ne
  have hPns : ¬ Group.IsSolvable ↥P := by
    set π : ↥(oTwoUpper H) →* O2Q (oTwoUpper H) :=
      QuotientGroup.mk' (CFSG.pCore 2 ↥(oTwoUpper H)) with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hker : π.ker = CFSG.pCore 2 ↥(oTwoUpper H) := by
      rw [hπ, QuotientGroup.ker_mk']
    have hPS : CFSG.pCore 2 ↥(oTwoUpper H) ≤ (T ⊓ oTwoUpper H).subgroupOf (oTwoUpper H) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hx' : (x : G) ∈ pCoreOf 2 (oTwoUpper H) :=
        ⟨x, by assumption, rfl⟩
      exact F7.isSylowTwoOf_pCoreOf_le hTK hx'
    have hPSP : (T ⊓ oTwoUpper H).subgroupOf (oTwoUpper H) ≤ P.subgroupOf (oTwoUpper H) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hBP ⟨hx.2, Subgroup.le_normalizer hx⟩
    set Sb := ((T ⊓ oTwoUpper H).subgroupOf (oTwoUpper H)).map π with hSb
    set Pb := (P.subgroupOf (oTwoUpper H)).map π with hPb
    have hSbSyl : IsSylowTwoOf Sb ⊤ := by
      refine ⟨le_top, ?_, ?_⟩
      · have h2 : IsPGroup 2 ↥((T ⊓ oTwoUpper H).subgroupOf (oTwoUpper H)) :=
          hTK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
        exact h2.map π
      · show ¬ 2 ∣ Sb.relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        intro h2
        exact hTK.2.2 (h2.trans (Subgroup.index_map_dvd _ hπs))
    have hNSb : Subgroup.normalizer (Sb : Set (O2Q (oTwoUpper H))) ≤ Pb := by
      intro xb hxb
      obtain ⟨x, rfl⟩ := hπs xb
      have hx1 : x ∈ Subgroup.normalizer ((Sb.comap π : Subgroup ↥(oTwoUpper H)) :
          Set ↥(oTwoUpper H)) := Subgroup.le_normalizer_comap π hxb
      have hcomap : Sb.comap π = (T ⊓ oTwoUpper H).subgroupOf (oTwoUpper H) := by
        rw [hSb, Subgroup.comap_map_eq, hker]
        exact sup_eq_left.mpr hPS
      rw [hcomap] at hx1
      have hxN : (x : G) ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
        mem_normalizer_of_mem_normalizer_subgroupOf inf_le_right hx1
      have hxP : x ∈ P.subgroupOf (oTwoUpper H) := by
        rw [Subgroup.mem_subgroupOf]
        exact hBP ⟨x.2, hxN⟩
      exact Subgroup.mem_map_of_mem π hxP
    have hcomapP : Pb.comap π = P.subgroupOf (oTwoUpper H) := by
      rw [hPb, Subgroup.comap_map_eq, hker]
      exact sup_eq_left.mpr (hPS.trans hPSP)
    have hPbne : Pb ≠ ⊤ := by
      intro htop
      apply hPne
      apply le_antisymm hPK
      intro y hy
      have hy' : (⟨y, hy⟩ : ↥(oTwoUpper H)) ∈ Pb.comap π := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [hcomapP, Subgroup.mem_subgroupOf] at hy'
      exact hy'
    have hPbmax : ∀ Qb : Subgroup (O2Q (oTwoUpper H)), Pb ≤ Qb → Qb ≠ ⊤ → Qb = Pb := by
      intro Qb hPQ hQne
      set Q : Subgroup G := (Qb.comap π).map (oTwoUpper H).subtype with hQ
      have hQK : Q ≤ oTwoUpper H := Subgroup.map_subtype_le _
      have hQsub : Q.subgroupOf (oTwoUpper H) = Qb.comap π :=
        Subgroup.comap_map_eq_self_of_injective (oTwoUpper H).subtype_injective _
      have hPQ' : P ≤ Q := by
        intro p hp
        refine ⟨⟨p, hPK hp⟩, ?_, rfl⟩
        show π ⟨p, hPK hp⟩ ∈ Qb
        exact hPQ (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hp))
      have hQneK : Q ≠ oTwoUpper H := by
        intro hQeq
        apply hQne
        rw [eq_top_iff]
        intro yb _
        obtain ⟨y, rfl⟩ := hπs yb
        have hy : (y : G) ∈ Q := by
          rw [hQeq]
          exact y.2
        have hy' : y ∈ Q.subgroupOf (oTwoUpper H) := Subgroup.mem_subgroupOf.mpr hy
        rw [hQsub] at hy'
        exact hy'
      have hQP := hPmax Q hPQ' hQK hQneK
      rw [← Subgroup.map_comap_eq_self_of_surjective hπs Qb, ← hQsub, hQP]
    have hns := hRP (O2Q (oTwoUpper H)) k hk2 h3.2 Sb Pb hSbSyl hNSb hPbne hPbmax
    intro hsolv
    apply hns
    have hs1 : Group.IsSolvable ↥(P.subgroupOf (oTwoUpper H)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hPK).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPK).injective
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (P.subgroupOf (oTwoUpper H)))
      (π.subgroupMap_surjective _)
  obtain ⟨L₂, hL₂⟩ := exists_mem_cComp_of_not_isSolvable' hPns
  exact ⟨L₂, K₁, hK₁, hKeq, Or.inr ⟨hBe, h3.1, P, ⟨hPK, hBP, hPne, hPmax⟩, hL₂⟩⟩

end CFSG.Quasithin.H13
