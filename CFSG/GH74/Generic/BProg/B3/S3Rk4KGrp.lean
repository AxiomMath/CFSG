module

public import CFSG.GH74.Generic.BProg.B3.S3Rk4Basic
public import CFSG.GH74.Generic.BProg.B3.S3Rk3Trans
public import CFSG.GH74.Generic.BProg.B3.S3PumpFinal

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Rk4KGrp

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.L5U5 Subgroup S3Fusion

variable {G : Type} [Group G] [Finite G]

theorem exists_I {x y y' : G} {K A T : Subgroup G} (h : Setup30 G x K A y) (hT : IsZT x y T)
    (hy'2 : y' * y' = 1) (hxy' : x * y' = y' * x) (hout : y' ∉ K ⊔ CxK x K) :
    ∃ I : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y'} : Set G)) I ∧
      I ≤ K ∧ ∃ a b : G, a ∈ I ∧ b ∈ I ∧ a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
        a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg : Cfg x y K T := cfg_of_setup30 h hT
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3L3Facts.pcomp h
  have hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K) := S3L3Facts.barShape h
  have hy'1 : y' ≠ 1 := fun e => hout (by rw [e]; exact (K ⊔ CxK x K).one_mem)
  have huord : orderOf y' = 2 := orderOf_eq_prime (by rw [sq]; exact hy'2) hy'1
  have huC : y' ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hxy'.symm
  set Kb : Subgroup (CentralizerBar x) := S3.imgBar x K
  set ub : CentralizerBar x := piC x y' with hub
  have hub2 : ub * ub = 1 := by rw [hub, ← piC_mul x huC huC, hy'2, piC_one]
  have hub1 : ub ≠ 1 := fun h' => hy'1 (eq_one_of_piC_eq_one (isPGroup_zpowers_of_involution hy'2)
    (Subgroup.zpowers_le.2 huC) (Subgroup.mem_zpowers y') h')
  have hubord : orderOf ub = 2 := orderOf_eq_prime (by rw [sq]; exact hub2) hub1
  have hout0 : ¬ ∃ k ∈ Kb, ∃ c ∈ centralizer ((Kb : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)), ub = k * c := by
    rintro ⟨k, hk, c, hc, e⟩
    refine hout (S3Rk3Trans.mem_KC_of_piC hcfg huC ?_)
    show ub ∈ Kb ⊔ centralizer ((Kb : Subgroup (CentralizerBar x)) : Set (CentralizerBar x))
    rw [e]
    exact Subgroup.mul_mem_sup hk hc
  have hout' : ∀ k ∈ Kb, ∃ g ∈ Kb, ub * g * ub⁻¹ ≠ k * g * k⁻¹ := by
    intro k hk
    by_contra hcon
    push Not at hcon
    apply hout0
    refine ⟨k, hk, k⁻¹ * ub, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    have h1 := hcon h' hh
    calc h' * (k⁻¹ * ub) = k⁻¹ * (k * h' * k⁻¹) * ub := by group
      _ = k⁻¹ * (ub * h' * ub⁻¹) * ub := by rw [h1]
      _ = (k⁻¹ * ub) * h' := by group
  have hnorm : Kb.Normal := hshape.normal
  have hsimple : IsSimpleGroup ↥Kb := by
    have e : (↥Kb ⧸ center ↥Kb) ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq hshape.centerless).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).mp hshape.quasi.2.1
  have h3 : QShape3 ↥Kb := by
    obtain ⟨t, p, f, ht, hp, hp2, h5, hm⟩ := hshape.model
    refine ⟨p, f, hp, hp2, by omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm
  obtain ⟨Lb, hLb, hrank, -⟩ := S3Outer.lemma302OuterData hnorm hsimple h3 hubord hout'
  have hbar : bar x y' = ub := (bar_of_mem huC).trans (piC_of_mem x huC).symm
  have hLb' : IsPCompIn 2 (centralizer ({bar x y'} : Set (CentralizerBar x)) ⊓ S3.imgBar x K) Lb := by
    rw [hbar, inf_comm]
    exact hLb
  obtain ⟨hLcomp, hLmap⟩ := B1.isPCompIn_liftAt hxy' huord hK hLb'
  set I : Subgroup G := liftAt x y' Lb
  have hIC : I ≤ centralizer ({x} : Set G) :=
    hLcomp.1.trans (B1.centralizer_closure_pair_le_left x y')
  have hIcomp : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y'} : Set G)) I := by
    rw [← B1.centralizer_closure_pair]
    exact hLcomp
  have hIK : I ≤ K := by
    have h1 : I ≤ pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y'} : Set G)) :=
      le_sSup hIcomp
    have hcz : centralizer ((Subgroup.zpowers y' : Subgroup G) : Set G) =
        centralizer ({y'} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y'} : Set G)) ≤
        pLayerOf 2 (centralizer ({x} : Set G)) := by
      have := B2.SD.TwoA7Geo.pLayerOf_inf_centralizer_le_two
        (H := centralizer ({x} : Set G)) (U := Subgroup.zpowers y')
        (Subgroup.zpowers_le.2 huC) (isPGroup_zpowers_of_involution hy'2)
      rwa [hcz] at this
    exact h1.trans (h2.trans (prop304 h).1.le)
  have hφ : (B1.projRes hIC).range = Lb := (B1.range_projRes hIC).trans hLmap
  have hker := B1.not_two_dvd_card_ker_projRes hIC
  have h2I : 2 ≤ CFSG.pRank 2 ↥I := by
    have := S3Rk4Basic.pRank_range_eq (B1.projRes hIC) hker
    rw [hφ] at this
    rw [← this]
    exact hrank
  obtain ⟨a, b, ha2, hb2, ha1, hb1, hab, hcomm⟩ := S3Rk4Basic.exists_two_invol h2I
  refine ⟨I, hIcomp, hIK, a, b, a.2, b.2, congrArg Subtype.val ha2, congrArg Subtype.val hb2,
    fun e => ha1 (Subtype.ext e), fun e => hb1 (Subtype.ext e), fun e => hab (Subtype.ext e),
    congrArg Subtype.val hcomm⟩

end S3Rk4KGrp

end CFSG.GH74.Generic.BProg.B3
