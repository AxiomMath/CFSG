module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenRep

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

section Components

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem self_mem_dComp' (K : Subgroup G) : K ∈ dComp Ω K := Relation.ReflTransGen.refl

theorem mem_of_mem_dComp' {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ dComp Ω K) : J ∈ Ω := by
  have hJ' : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J :=
    hJ
  induction hJ' with
  | refl => exact hK
  | tail _ hbc _ => exact hbc.1

theorem dComp_trans' {K₁ K J : Subgroup G} (h₁ : K₁ ∈ dComp Ω K) (hJ : J ∈ dComp Ω K₁) :
    J ∈ dComp Ω K :=
  Relation.ReflTransGen.trans h₁ hJ

theorem mem_dComp_of_dAdj {K M N : Subgroup G} (hM : M ∈ dComp Ω K) (hN : N ∈ Ω)
    (h : Disconnected.dAdj Ω M N) : N ∈ dComp Ω K :=
  Relation.ReflTransGen.tail hM ⟨hN, h⟩

end Components

section Boundary

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem dComp_subset_dstarComp (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (K : Subgroup G) :
    dComp Ω K ⊆ dstarComp Ω K := by
  intro J hJ
  have hJ' : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J :=
    hJ
  refine Relation.ReflTransGen.mono (p := dstarAdj Ω) ?_ K J hJ'
  intro M N hMN
  refine ⟨hMN.1, ?_⟩
  rcases hMN.2 with h | h
  · exact Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ M h)
  · exact Or.inr (T3.omegaNbr_subset_omegaStarNbr hp hΩ N h)

theorem exists_boundary_of_dComp_ne (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K) :
    ∃ K₁ ∈ dComp Ω K, ∃ J₁ ∈ omegaStarNbr Ω K₁, J₁ ∉ dComp Ω K := by
  obtain ⟨J, hJ, hJn⟩ : ∃ J ∈ dstarComp Ω K, J ∉ dComp Ω K := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm (dComp_subset_dstarComp hp hΩ K) hcon)
  have key : ∀ J, Relation.ReflTransGen (dstarAdj Ω) K J → J ∉ dComp Ω K →
      ∃ K₁ ∈ dComp Ω K, ∃ J₁ ∈ omegaStarNbr Ω K₁, J₁ ∉ dComp Ω K := by
    intro J hJ
    induction hJ with
    | refl => exact fun h => absurd (self_mem_dComp' K) h
    | @tail b c _ hbc ih =>
      intro hc
      by_cases hbd : b ∈ dComp Ω K
      · refine ⟨b, hbd, c, ?_, hc⟩
        obtain ⟨hcΩ, h | h⟩ := hbc
        · exact h
        · exact T3.omegaStarNbr_symm (l6_2 p f) hp hq hΩ hcΩ (mem_of_mem_dComp' hK hbd) h
      · exact ih hbd
  exact key J hJ hJn

end Boundary

section GroupW

variable {G : Type} [Group G]

theorem conjSub_biSup_le_of_acts {η : Set (Subgroup G)} {x : G} (h : ∀ U ∈ η, conjSub x U ∈ η) :
    conjSub x (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
  rw [conjSub, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun U hU => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ η) => V) _ (h U hU)

theorem le_normalizer_biSup_of_acts {η : Set (Subgroup G)} {R : Subgroup G}
    (h : ∀ r ∈ R, ∀ U ∈ η, conjSub r U ∈ η) :
    R ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) := by
  intro r hr
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm (conjSub_biSup_le_of_acts (h r hr)) ?_
  have h1 := conjSub_mono (n := r) (conjSub_biSup_le_of_acts (h r⁻¹ (R.inv_mem hr)))
  rwa [conjSub_conjSub_inv] at h1

end GroupW

section Existence

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_W_of_mem_omegaStarNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaStarNbr Ω K) :
    ∃ W ∈ WSet Ω, ∃ R ∈ DSet Ω W, ∃ T ∈ DSet Ω W, IsSylow2In R K ∧ IsSylow2In T J := by
  obtain ⟨hJΩ, -, U, hU, hUJ, hUN⟩ := hJ
  have hU2 : IsPGroup 2 U := hΩ.isPGroup_of_mem_USet hp hU
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := hΩ.exists_data_of_mem_USet hp hU
  obtain ⟨R, hRK, hRU⟩ := T3.exists_sylow_normalized hU2 hUN
  have hRmem : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRK
  have hUR : U ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (hRU u hu)
  obtain ⟨S, hS⟩ := (hU2.to_sup_of_normal_right' hRK.2.1 hUR).exists_le_sylow
  have hUS : U ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans hS
  obtain ⟨η, hη, hηinv⟩ := (l6_9_proved p f hp hq G Ω hΩ S).1
  have hηG : η ∈ etaG Ω := ⟨S, hη, hηinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  have hW : (⨆ V ∈ η, V : Subgroup G) ∈ WSet Ω := ⟨η, hηG, rfl⟩
  set W : Subgroup G := ⨆ V ∈ η, V with hWdef
  have hRD : R ∈ DSet Ω W :=
    ⟨hRmem, le_normalizer_biSup_of_acts
      ((l6_10_proved p f hp hq G Ω hΩ S η hηG hηS).1 R hRmem hRS)⟩
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) (hU4.trans (Subgroup.card_le_of_le (le_inf hUJ hUS)))
  have hV₀ : J ⊓ W ∈ η := l6_11_proved p f hp hq G Ω hΩ S η hηG hηS J hJΩ hJS
  have hV₀U : J ⊓ W ∈ USet Ω := (hη.1 hV₀).1
  have hV₀2 : IsPGroup 2 ↥(J ⊓ W) := hΩ.isPGroup_of_mem_USet hp hV₀U
  obtain ⟨-, -, -, -, -, -, -, -, hV₀4⟩ := hΩ.exists_data_of_mem_USet hp hV₀U
  obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJΩ
  have hzV₀ : zJ ∈ J ⊓ W := T3.mem_of_isPGroup hzJ inf_le_left hV₀2 (by omega)
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hWJ : W ≤ Subgroup.normalizer (J : Set G) := by
    refine iSup₂_le fun V hV => ?_
    by_cases hVeq : V = J ⊓ W
    · rw [hVeq]
      exact inf_le_left.trans Subgroup.le_normalizer
    · obtain ⟨Rv, -, J', hJ', hRvJ', hVRv, -, -, hV4⟩ :=
        hΩ.exists_data_of_mem_USet hp (hη.1 hV).1
      have hVJ' : V ≤ J' := hVRv.trans hRvJ'.1
      have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet hp (hη.1 hV).1
      have hJJ' : J ≠ J' := by
        intro hJJ'
        rw [← hJJ'] at hVJ'
        exact hη.2.1 V hV (J ⊓ W) hV₀ hVeq J hJΩ ⟨hVJ', inf_le_left⟩
      refine hΩ.le_normalizer_of_le_centralizer hp hq hJΩ hJ' hJJ' hzJ hVJ' hV2 (by omega) ?_
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hWab v (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV hv) zJ hzV₀.2
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  obtain ⟨T, hTJ, hTW⟩ := T3.exists_sylow_normalized hW2 hWJ
  have hWT : W ≤ Subgroup.normalizer (T : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hTW w hw)
  obtain ⟨S', hS'⟩ := (hW2.to_sup_of_normal_right' hTJ.2.1 hWT).exists_le_sylow
  have hWS' : W ≤ (S' : Subgroup G) := le_sup_left.trans hS'
  have hTS' : T ≤ (S' : Subgroup G) := le_sup_right.trans hS'
  have hηS' : ∀ V ∈ η, V ≤ (S' : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans hWS'
  have hTmem : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hTJ
  have hTD : T ∈ DSet Ω W :=
    ⟨hTmem, le_normalizer_biSup_of_acts
      ((l6_10_proved p f hp hq G Ω hΩ S' η hηG hηS').1 T hTmem hTS')⟩
  exact ⟨W, hW, R, hRD, T, hTD, hRK, hTJ⟩

end Existence

section Connected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem exists_not_mem_W {R K : Subgroup G} (hR : R ∈ DSet Ω W) (hK : K ∈ Ω)
    (hRK : IsSylow2In R K) : ∃ r ∈ R, r ∉ W := by
  obtain ⟨-, -, -, -, hcard⟩ := inf_W_of_mem_D c.hp c.hq c.hΩ c.hW hR hK hRK
  by_contra hcon
  push Not at hcon
  rw [inf_eq_left.mpr hcon] at hcard
  have : 0 < Nat.card R := Nat.card_pos
  omega

theorem mem_dComp_of_connected (hconn : DbarConnected Ω W) {K₁ J₁ R T : Subgroup G}
    (hK₁ : K₁ ∈ Ω) (hJ₁ : J₁ ∈ Ω) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hRK : IsSylow2In R K₁) (hTJ : IsSylow2In T J₁) : J₁ ∈ dComp Ω K₁ := by
  have key : ∀ R', Relation.ReflTransGen (DbarAdj Ω W) R R' →
      R' ∈ DSet Ω W ∧ ∃ K' ∈ dComp Ω K₁, IsSylow2In R' K' := by
    intro R' h
    induction h with
    | refl => exact ⟨hR, K₁, self_mem_dComp' K₁, hRK⟩
    | @tail b d _ hbd ih =>
      obtain ⟨hbD, K', hK'd, hbK'⟩ := ih
      have hK'Ω : K' ∈ Ω := mem_of_mem_dComp' hK₁ hK'd
      obtain ⟨hdD, hadj⟩ := hbd
      obtain ⟨K'', hK''Ω, hdK''⟩ := exists_isSylow2In_of_mem_RSet hdD.1
      refine ⟨hdD, ?_⟩
      by_cases hKeq : K'' = K'
      · exact ⟨K', hK'd, hKeq ▸ hdK''⟩
      · obtain ⟨rb, hrb, hrbW⟩ := c.exists_not_mem_W hbD hK'Ω hbK'
        obtain ⟨rd, hrd, hrdW⟩ := c.exists_not_mem_W hdD hK''Ω hdK''
        let ρ : Rep Ω W := ⟨K', b, rb, hK'Ω, hbD, hbK', hrb, hrbW⟩
        let σ : Rep Ω W := ⟨K'', d, rd, hK''Ω, hdD, hdK'', hrd, hrdW⟩
        rcases hadj with ⟨-, hcomm⟩ | ⟨hle, -⟩
        · have hcm : ρ.img * σ.img = σ.img * ρ.img :=
            (piG_comm_iff (hbD.2 hrb) (hdD.2 hrd)).mpr (hcomm rb hrb rd hrd)
          exact ⟨K'', mem_dComp_of_dAdj hK'd hK''Ω
            (Or.inl (c.omega_of_comm ρ σ (Ne.symm hKeq) hcm)), hdK''⟩
        · exact absurd (c.K_eq_of_img_eq σ ρ
            (piG_eq_of_le_sup c.hp c.hq c.hΩ c.hW hbD hdD hle hrb hrd hrbW hrdW)) hKeq
  obtain ⟨-, K'', hK''d, hTK''⟩ := key T (hconn R hR T hT)
  have hK''Ω : K'' ∈ Ω := mem_of_mem_dComp' hK₁ hK''d
  have hT8 : 8 ≤ Nat.card T := c.hΩ.eight_le_of_mem_RSet c.hp hT.1
  have hKJ : K'' = J₁ := c.hΩ.eq_of_le_of_le hK''Ω hJ₁ hTK''.2.1 (by omega) hTK''.1 hTJ.1
  exact hKJ ▸ hK''d

end Ctx

end Connected

end Thompson

end CFSG.ClassicalInvolution.Asc77
