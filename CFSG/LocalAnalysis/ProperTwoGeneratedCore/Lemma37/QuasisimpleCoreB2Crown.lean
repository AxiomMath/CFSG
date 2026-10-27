module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Fix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CrownLemma
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreSetting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

theorem Setting.commutator_centralQuotient_eq_top (h : Setting J Q B) :
    commutator (J ⧸ Subgroup.center J) = ⊤ := by
  have hs := QuotientGroup.mk'_surjective (Subgroup.center J)
  have h1 := Subgroup.map_commutator (⊤ : Subgroup J) ⊤ (QuotientGroup.mk' (Subgroup.center J))
  rw [Subgroup.map_top_of_surjective _ hs] at h1
  rw [commutator_def, ← h1, ← commutator_def, h.perfect.commutator_eq_top,
    Subgroup.map_top_of_surjective _ hs]

theorem PartC.false_of_caseB2_of_normalized (h : Setting J Q B) {T R P : Subgroup J}
    (hc : PartC T R P (centralElt J) u) (hT : T ≤ R ⊔ P)
    (hφ : Nonempty (P ≃* QuaternionGroup 2)) (hn : PartC.CaseB2Normalized T P)
    (S : Sylow 2 J) (hTS : T ≤ S) (hne : (S : Subgroup J) ≠ T) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hφ
  have hZ : ∀ x, x ∈ Subgroup.center J ↔ x = 1 ∨ x = centralElt J := fun _ => h.mem_center_iff
  have hS2 : IsPGroup 2 (S : Subgroup J) := S.isPGroup'
  obtain ⟨x, hxS, hxN, hxT⟩ := exists_mem_normalizer_not_mem_of_lt_sylow S hTS hne
  have hSN := hc.le_normalizer_of_caseB2Normalized _ hT φ hn hZ h.center_card hS2 hTS hxS hxN
    hxT
  have hswap := hc.swap_of_caseB2Normalized hT φ hn hS2 hTS hxS hxN hxT
  have hxx := hc.mul_self_mem_of_caseB2Normalized hT φ hn hS2 hTS hxS hxN hxT
  set W := T.map (QuotientGroup.mk' (Subgroup.center J)) with hWdef
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    hc.comm_map_of_caseB2 _ hT φ hZ ha hb
  have hmemW : ∀ g : J, (g : J ⧸ Subgroup.center J) ∈ W ↔ g ∈ T :=
    hc.mk_mem_map_iff_of_caseB2 _ hZ
  set S' := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) with hS'def
  have hS' : (S' : Subgroup (J ⧸ Subgroup.center J)) =
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) := Sylow.coe_mapSurjective _ _
  have hWS : W ≤ S' := by
    rw [hS']
    exact Subgroup.map_mono hTS
  have hXS : (x : J ⧸ Subgroup.center J) ∈ (S' : Subgroup (J ⧸ Subgroup.center J)) := by
    rw [hS']
    exact ⟨x, hxS, rfl⟩
  have hXW : (x : J ⧸ Subgroup.center J) ∉ W := fun h' => hxT ((hmemW x).mp h')
  have hXX : (x : J ⧸ Subgroup.center J) * x ∈
      W ⊓ Subgroup.centralizer {(x : J ⧸ Subgroup.center J)} := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr (by group)⟩
    rw [← QuotientGroup.mk_mul]
    exact (hmemW _).mpr hxx
  obtain ⟨p₀, hp₀, hp₀eq⟩ :=
    (hc.mem_inf_centralizer_iff_of_swap _ hT φ hZ hswap.1 hswap.2 hxx).mp hXX
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hp₀eq
  have hp₀W : (p₀ : J ⧸ Subgroup.center J) ∈ W := (hmemW p₀).mpr (hc.right_le hp₀)
  have hcomm₀ := congrArg (fun g : J => (g : J ⧸ Subgroup.center J))
    (hc.commute _ (hswap.1 p₀ hp₀) p₀ hp₀)
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hcomm₀
  set X := (x : J ⧸ Subgroup.center J) with hXdef
  set p := (p₀ : J ⧸ Subgroup.center J) with hpdef
  set y := p⁻¹ * X with hydef
  have hyS : y ∈ (S' : Subgroup (J ⧸ Subgroup.center J)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWS hp₀W)) hXS
  have hyW : y ∉ W := fun h' => hXW (by
    rw [show X = p * y by rw [hydef]; group]
    exact W.mul_mem hp₀W h')
  have hy2 : y ^ 2 = 1 := by
    calc y ^ 2 = p⁻¹ * (X * p⁻¹ * X⁻¹) * (X * X) := by rw [pow_two, hydef]; group
      _ = p⁻¹ * (X * p * X⁻¹)⁻¹ * (p * (X * p * X⁻¹)) := by rw [← hp₀eq]; group
      _ = 1 := by rw [← hcomm₀]; group
  have hinf : W ⊓ Subgroup.centralizer {y} = W ⊓ Subgroup.centralizer {X} := by
    ext w
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun ⟨hw, hwy⟩ => ⟨hw, ?_⟩, fun ⟨hw, hwx⟩ => ⟨hw, ?_⟩⟩
    · have hpw := hWcomm _ hw _ (W.inv_mem hp₀W)
      refine mul_left_cancel (a := p⁻¹) ?_
      calc p⁻¹ * (w * X) = w * p⁻¹ * X := by rw [hpw]; group
        _ = w * y := by rw [hydef]; group
        _ = y * w := hwy
        _ = p⁻¹ * (X * w) := by rw [hydef]; group
    · have hpw := hWcomm _ hw _ (W.inv_mem hp₀W)
      calc w * y = w * p⁻¹ * X := by rw [hydef]; group
        _ = p⁻¹ * (w * X) := by rw [hpw]; group
        _ = p⁻¹ * (X * w) := by rw [hwx]
        _ = y * w := by rw [hydef]; group
  have hΔ : Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup (J ⧸ Subgroup.center J)) = 4 := by
    rw [hinf]
    exact hc.card_inf_centralizer_of_swap _ hT φ hZ h.center_card hswap.1 hswap.2 hxx
  have hidx : W.relIndex (S' : Subgroup (J ⧸ Subgroup.center J)) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff']
    refine ⟨X⁻¹, Subgroup.inv_mem _ hXS, fun b hb => ?_⟩
    rw [hS'] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    have hnot : ∀ c ∈ W, X⁻¹ * c ∈ W → False := fun c hcW hxc =>
      hXW (by
        rw [show X = c * (X⁻¹ * c)⁻¹ by group]
        exact W.mul_mem hcW (W.inv_mem hxc))
    rcases hc.mem_or_inv_mul_mem_of_caseB2Normalized hT φ hn hS2 hTS hxS hxN hxT hs (hSN hs) with
      hsT | hsT
    · exact Or.inr ⟨(hmemW s).mpr hsT, hnot _ ((hmemW s).mpr hsT)⟩
    · have h1 : X⁻¹ * (QuotientGroup.mk' (Subgroup.center J) s) ∈ W := by
        rw [QuotientGroup.mk'_apply, hXdef, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        exact (hmemW _).mpr hsT
      exact Or.inl ⟨h1, fun h2 => hnot _ h2 h1⟩
  exact crown_lemma_of_perfect h.commutator_centralQuotient_eq_top S' hWS hidx
    (fun w hw => by rw [pow_two]; exact hc.mul_self_map_of_caseB2 _ hT φ hZ hw)
    (hc.card_map_of_caseB2 _ hT φ hZ) hyS hyW hy2 hΔ

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
