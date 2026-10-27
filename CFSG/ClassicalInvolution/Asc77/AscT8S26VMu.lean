module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26UTyp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

theorem s26_z2_eq : ∀ x y : Multiplicative (ZMod 2), x ≠ 1 → y ≠ 1 → x = y := by decide

section Edgeless

variable {p f : ℕ} [Fact p.Prime]

theorem s26_dEdgeless_of_muIsoZ2 (h752 : L7_5_2 p f) {H : Type} [Group H] [Finite H]
    {Φ : Set (Subgroup H)} (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) {W' : Subgroup H} (hW' : W' ∈ WSet Φ) (hZ : MuIsoZ2 Φ W') :
    DEdgeless Φ := by
  have key : ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, False := by
    intro K hK J hJ
    obtain ⟨R, T, hRsyl, hTsyl, -, hRT⟩ := AscE186.exists_commuting_sylow_pair hp hq hΦ hK hJ
    have hJΦ : J ∈ Φ := hJ.1
    have hKJ : K ≠ J := hJ.2.1.symm
    have hR2 : IsPGroup 2 ↥R := hRsyl.2.1
    have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
    have hTnR : T ≤ Subgroup.normalizer (R : Set H) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 : x * t = t * x := hRT x hx t ht
        have : t * x * t⁻¹ = x := by rw [← h1]; group
        rw [this]
        exact hx
      · intro hy
        have h1 : (t * x * t⁻¹) * t = t * (t * x * t⁻¹) := hRT _ hy t ht
        have e : x = t * x * t⁻¹ := by
          calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
            _ = t⁻¹ * ((t * x * t⁻¹) * t) := by rw [mul_assoc]
            _ = t⁻¹ * (t * (t * x * t⁻¹)) := by rw [h1]
            _ = t * x * t⁻¹ := by group
        rw [e]
        exact hy
    have hTR2 : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hR2 hTnR
    obtain ⟨S, hS⟩ := hTR2.exists_le_sylow
    have hTS : T ≤ (S : Subgroup H) := le_sup_left.trans hS
    have hRS : R ≤ (S : Subgroup H) := le_sup_right.trans hS
    obtain ⟨η, hη, hηinv⟩ := exists_invariant_mem_etaSet hp hq hΦ S
    obtain ⟨W₁, hW₁, hSN⟩ : ∃ W₁ : Subgroup H, W₁ ∈ WSet Φ ∧
        ∀ s ∈ (S : Subgroup H), s ∈ Subgroup.normalizer (W₁ : Set H) :=
      ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hηinv⟩, rfl⟩, fun s hs =>
        mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hηinv hs)⟩
    have hRD : R ∈ DSet Φ W₁ := ⟨mem_RSet_of_isSylow2In hK hRsyl, fun x hx => hSN x (hRS hx)⟩
    have hTD : T ∈ DSet Φ W₁ := ⟨mem_RSet_of_isSylow2In hJΦ hTsyl, fun x hx => hSN x (hTS hx)⟩
    have hP : PartIHyp p f Φ := ⟨hp, hq, hΦ, hA⟩
    have hTT := Thompson.isTT_muDelta hp hq hΦ hW₁ (thompsonCube H Φ hP W₁ hW₁)
    obtain ⟨r, hr, hrW⟩ := exists_not_mem_of_mem_D hp hq hΦ hW₁ hRD
    obtain ⟨t', ht', htW⟩ := exists_not_mem_of_mem_D hp hq hΦ hW₁ hTD
    obtain ⟨a, ha, haeq⟩ := exists_muDelta_eq_piG hRD hr hrW
    obtain ⟨c, hc, hceq⟩ := exists_muDelta_eq_piG hTD ht' htW
    have hac : a ≠ c := fun e =>
      piG_ne_of_ne_members hp hq hΦ hW₁ hRD hTD hK hJΦ hRsyl hTsyl hKJ hr ht' htW
        (haeq.symm.trans ((congrArg Subtype.val e).trans hceq))
    obtain ⟨e'⟩ := h752 hp hq H Φ hΦ W₁ hW₁ W' hW'
    obtain ⟨e⟩ := hZ
    have e2 := e'.trans e
    have h1 : e2 a ≠ 1 := fun h => hTT.ne_one a ha (e2.injective (by rw [h, map_one]))
    have h2 : e2 c ≠ 1 := fun h => hTT.ne_one c hc (e2.injective (by rw [h, map_one]))
    exact hac (e2.injective (s26_z2_eq _ _ h1 h2))
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact key K hK J h
  · exact key J hJ K h

end Edgeless

section Section

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem s26_genSection_omegaNbrGen {K : Subgroup G} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : ∀ L ∈ Ω, AEmpty Ω L) :
    GenSection p f (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) := by
  have := genSection_layerHull hp hq hΩ hA (omegaNbrGen Ω K)
  rwa [s26_layerHull_omegaNbrGen Ω K] at this

end Section

variable {p f : ℕ} [Fact p.Prime]

theorem s26XEdgeless_of_muZ2 (h752 : L7_5_2 p f) (hZ : S26XMuZ2 p f) : S26XEdgeless p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  obtain ⟨W', hW', hZ2⟩ := hZ G Ω K J S R T W z t hs hdisc hS4
  have hGen := s26_genSection_omegaNbrGen (K := K) hs.stand.odd hs.stand.five hs.stand.hyp
    hs.stand.aEmpty
  exact s26_dEdgeless_of_muIsoZ2 h752 hs.stand.odd hs.stand.five hGen.hyp hGen.aEmpty hW' hZ2

end CFSG.ClassicalInvolution.Asc77
