module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25X01
public import CFSG.ClassicalInvolution.Q3.Q3T7SectC
public import CFSG.ClassicalInvolution.Q3.Q3CHS2Gold
public import CFSG.ClassicalInvolution.Uniform.U3Thm4

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3

section Sect


theorem hasLieType_of_hasLieTypeU {X : Type} [Group X] {Φ : Set (Subgroup X)}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (h : HasLieTypeU 3 1 Φ t n) :
    HasLieType 3 1 Φ t n := by
  obtain ⟨D, hc, i, hi⟩ := h
  have hsub : ∀ j : Fin D.card, j = i := fun j => Fin.ext (by
    have h1 := i.2
    have h2 := j.2
    omega)
  let σ : ∀ j, ModelSpec 3 1 (D.kind j) := fun j => (hsub j).symm ▸ hi.modelSpec
  refine ⟨D.toOmegaLieOfSpec σ, hc, i, ?_, ?_⟩
  · change (σ i).tag = t
    rfl
  · change (σ i).rank = n
    rfl

theorem hasOrthType_of_hasOrthTypeU {X : Type} [Group X] {Φ : Set (Subgroup X)} {d : ℕ}
    {ε : Bool} (h : HasOrthTypeU 3 1 Φ d ε) : HasOrthType 3 1 Φ d ε := by
  obtain ⟨t, n, htag, hL⟩ := h
  exact ⟨t, n, htag, hasLieType_of_hasLieTypeU hL⟩

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem dConnected_or_transitive25 {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hlt : Nat.card Y < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) :
    DConnected Φ ∨ ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : Y, conjSub g K = L := by
  by_cases htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : Y, conjSub g K = L
  · exact Or.inr htrans
  left
  push Not at htrans
  obtain ⟨K₀, hK₀, M₀, hM₀, hnc⟩ := htrans
  have hc0 : Commutes K₀ M₀ :=
    h4 (by norm_num) (by norm_num) Y hlt Φ hΦ hO hA K₀ hK₀ M₀ hM₀ (fun ⟨g, hg⟩ => hnc g hg)
  have hne0 : K₀ ≠ M₀ := fun h => hnc 1 (by rw [conjSub_one, h])
  have hadj0 : dAdj Φ K₀ M₀ := dAdj_of_commutes hM₀ hne0 hc0
  have hjoin : ∀ M ∈ Φ,
      Relation.ReflTransGen (fun A B : Subgroup Y => B ∈ Φ ∧ dAdj Φ A B) K₀ M ∧
        Relation.ReflTransGen (fun A B : Subgroup Y => B ∈ Φ ∧ dAdj Φ A B) M K₀ := by
    intro M hM
    by_cases hMc : ∃ g : Y, conjSub g K₀ = M
    · have hnotM : ¬ ∃ g : Y, conjSub g M = M₀ := by
        rintro ⟨g, hg⟩
        obtain ⟨y, rfl⟩ := hMc
        exact hnc (g * y) (by rw [conjSub_mul]; exact hg)
      have hc : Commutes M M₀ :=
        h4 (by norm_num) (by norm_num) Y hlt Φ hΦ hO hA M hM M₀ hM₀ hnotM
      have hne : M ≠ M₀ := fun h => hnotM ⟨1, by rw [conjSub_one, h]⟩
      have hadj : dAdj Φ M M₀ := dAdj_of_commutes hM₀ hne hc
      exact ⟨(Relation.ReflTransGen.single ⟨hM₀, hadj0⟩).tail ⟨hM, dAdj_symm hadj⟩,
        (Relation.ReflTransGen.single ⟨hM₀, hadj⟩).tail ⟨hK₀, dAdj_symm hadj0⟩⟩
    · push Not at hMc
      have hc : Commutes K₀ M :=
        h4 (by norm_num) (by norm_num) Y hlt Φ hΦ hO hA K₀ hK₀ M hM (fun ⟨g, hg⟩ => hMc g hg)
      have hne : K₀ ≠ M := fun h => hMc 1 (by rw [conjSub_one, h])
      have hadj : dAdj Φ K₀ M := dAdj_of_commutes hM hne hc
      exact ⟨Relation.ReflTransGen.single ⟨hM, hadj⟩,
        Relation.ReflTransGen.single ⟨hK₀, dAdj_symm hadj⟩⟩
  intro K hK L hL
  exact (hjoin K hK).2.trans (hjoin L hL).1

@[expose] def Thm8SectBelow' (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
    ∀ Φ : Set (Subgroup X), GenSection Φ → Φ.Nonempty → ¬ DEdgeless Φ → ¬ DConnected Φ →
      ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthType 3 1 Φ d ε

theorem thm8SectBelow'_of_citBelow {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) : Thm8SectBelow' n := by
  intro X _ _ hlt Φ hG hne hNE hNC
  rcases dConnected_or_transitive25 (thm4BelowU_of_citBelowT hn) hlt hG.hyp hG.oddCore hG.aEmpty
    with hc | htrans
  · exact absurd hc hNC
  · obtain ⟨d, ε, hd5, hd8, hU⟩ := Q3T7.thm8SectBelowU_of hn X hlt Φ
      ⟨hG.hyp, hG.oddCore, hG.gen, htrans, hG.aEmpty⟩ hne hNE hNC
    exact ⟨d, ε, hd5, hd8, hasOrthType_of_hasOrthTypeU hU⟩

end Sect

section Goldschmidt

variable {G : Type} [Group G]

theorem exists_quaternion_pair_of_card_eight {R : Subgroup G} (hQ : IsQuatSub R)
    (h8 : Nat.card R = 8) :
    ∃ x ∈ R, ∃ y ∈ R, x * x = y * y ∧ x * x * (x * x) = 1 ∧ x * x ≠ 1 ∧ x * y ≠ y * x := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hQ
  have hcard : Nat.card R = 4 * 2 ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hk1 : k = 1 := by
    have h4 : 4 * 2 ^ k = 8 := by rw [← hcard]; exact h8
    have h2 : 2 ^ k = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hk1
  have e' : R ≃* QuaternionGroup 2 := e
  have k1 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 1 * QuaternionGroup.xa 1) := by decide
  have k2 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0) *
      (QuaternionGroup.xa 0 * QuaternionGroup.xa 0) = 1 := by decide
  have k3 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0) ≠ 1 := by decide
  have k4 : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 1) ≠
      QuaternionGroup.xa 1 * QuaternionGroup.xa 0 := by decide
  refine ⟨(e'.symm (QuaternionGroup.xa 0) : G), (e'.symm _).2,
    (e'.symm (QuaternionGroup.xa 1) : G), (e'.symm _).2, ?_, ?_, ?_, ?_⟩
  · have := congrArg e'.symm k1
    simp only [map_mul] at this
    exact congrArg Subtype.val this
  · have := congrArg e'.symm k2
    simp only [map_mul, map_one] at this
    exact congrArg Subtype.val this
  · intro h
    apply k3
    apply e'.symm.injective
    simp only [map_mul, map_one]
    exact Subtype.ext h
  · intro h
    apply k4
    apply e'.symm.injective
    simp only [map_mul]
    exact Subtype.ext h


theorem l17_8_of_hyp25 [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
    {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {A : Subgroup G} (hAS : A ≤ (S : Subgroup G))
    (hA1 : A ≠ ⊥) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsc : StronglyClosedIn A (S : Subgroup G)) : False := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hz1 : z * z = 1 := hzK.sq
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz1) hzK.ne_one
  obtain ⟨z0, hz0⟩ := hΩ.classical K hst.mem
  obtain ⟨x0, -, y0, -, hxy0⟩ := ih8_exists_noncomm hz0
  have hnab : ∃ a b : G, a * b ≠ b * a := ⟨x0, y0, hxy0⟩
  have hRsyl : IsSylow2In R K := h.hRsyl
  have hR'syl : IsSylow2In R' K' := h.hR'syl
  have h8 : Nat.card R = 8 := Q3T7P25.natCard_isSylow2In_member hΩ hst.mem hRsyl
  obtain ⟨x, hxR, y, hyR, hxy2, hx4, hx1, hxy⟩ :=
    exists_quaternion_pair_of_card_eight (hΩ.isQuatSub_of_mem_RSet hyp.hR.1) h8
  have hxz : x * x = z :=
    (hzK.unique (x * x) (K.mul_mem (hRsyl.1 hxR) (hRsyl.1 hxR)) hx4).resolve_left hx1
  have hyz : y * y = z := hxy2 ▸ hxz
  have hu₂R' : u₂ ∈ R' := hyp.hu₂.1
  have hu₂sq : u₂ * u₂ = z :=
    Asc77.C25X.sq_eq_of_orderOf_four hzK' (hR'syl.1 hu₂R') hyp.hu₂.2.1
  have hc1 : x * u₂ = u₂ * x := h.hcomm x hxR u₂ hu₂R'
  have hc2 : y * u₂ = u₂ * y := h.hcomm y hyR u₂ hu₂R'
  have ha2 : (x * u₂) * (x * u₂) = 1 := by
    calc (x * u₂) * (x * u₂) = x * (u₂ * x) * u₂ := by group
      _ = x * (x * u₂) * u₂ := by rw [← hc1]
      _ = (x * x) * (u₂ * u₂) := by group
      _ = 1 := by rw [hxz, hu₂sq, hz1]
  have hb2 : (y * u₂) * (y * u₂) = 1 := by
    calc (y * u₂) * (y * u₂) = y * (u₂ * y) * u₂ := by group
      _ = y * (y * u₂) * u₂ := by rw [← hc2]
      _ = (y * y) * (u₂ * u₂) := by group
      _ = 1 := by rw [hyz, hu₂sq, hz1]
  have e1 : x * u₂ * (y * u₂) = (x * y) * z := by
    calc x * u₂ * (y * u₂) = x * (u₂ * y) * u₂ := by group
      _ = x * (y * u₂) * u₂ := by rw [← hc2]
      _ = (x * y) * (u₂ * u₂) := by group
      _ = (x * y) * z := by rw [hu₂sq]
  have e2 : y * u₂ * (x * u₂) = (y * x) * z := by
    calc y * u₂ * (x * u₂) = y * (u₂ * x) * u₂ := by group
      _ = y * (x * u₂) * u₂ := by rw [← hc1]
      _ = (y * x) * (u₂ * u₂) := by group
      _ = (y * x) * z := by rw [hu₂sq]
  have hab : x * u₂ * (y * u₂) ≠ y * u₂ * (x * u₂) := by
    intro h'
    rw [e1, e2] at h'
    exact hxy (mul_right_cancel h')
  have ha1 : x * u₂ ≠ 1 := fun h1 => hab (by rw [h1]; simp)
  have hb1 : y * u₂ ≠ 1 := fun h1 => hab (by rw [h1]; simp)
  have ha2' : orderOf (x * u₂) = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hb2' : orderOf (y * u₂) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hxS : x ∈ (S : Subgroup G) := hyp.hR.2.2 hxR
  have hyS : y ∈ (S : Subgroup G) := hyp.hR.2.2 hyR
  have hu₂S : u₂ ∈ (S : Subgroup G) := hyp.hR'.2.2 hu₂R'
  have haC : x * u₂ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS _ ((S : Subgroup G).mul_mem hxS hu₂S))
  have hbC : y * u₂ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS _ ((S : Subgroup G).mul_mem hyS hu₂S))
  have hR2 : IsPGroup 2 R := S.isPGroup'.to_le hyp.hR.2.2
  have hR8 : 8 ≤ Nat.card R := le_of_eq h8.symm
  have hRu : ∀ a ∈ R, ∀ b ∈ R, orderOf a = 2 → orderOf b = 2 → a = b := by
    intro a ha b hb ha2 hb2
    have hsq : ∀ c : G, orderOf c = 2 → c * c = 1 := fun c hc => by
      have := pow_orderOf_eq_one c
      rw [hc, pow_two] at this
      exact this
    have hne : ∀ c : G, orderOf c = 2 → c ≠ 1 := fun c hc h1 => by
      rw [h1, orderOf_one] at hc
      omega
    have hua := (hzK.unique a (hRsyl.1 ha) (hsq a ha2)).resolve_left (hne a ha2)
    have hub := (hzK.unique b (hRsyl.1 hb) (hsq b hb2)).resolve_left (hne b hb2)
    rw [hua, hub]
  have hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A := by
    intro a ha g hg
    have := hsc.2 a ha g⁻¹ (by simpa using hg)
    simpa using this
  have hAab' : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAab a.1 a.2 b.1 b.2)⟩⟩
  exact hA1 (Q3CH.eq_bot_of_stronglyClosed_of_abelian3 hnab hz2 haC hbC ha2' hb2' hab hR2 hR8 hRu
    hst.rank S hAS hAab' hcl)

end Goldschmidt

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
