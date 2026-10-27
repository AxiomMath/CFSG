module

public import CFSG.LieType.SeitzGeneration.CubeCoverE6Line
public import CFSG.LieType.SeitzGeneration.CubeCoverLayer
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerSylowLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerFix24

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.CubeCoverLayer
  CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
open scoped commutatorElement


theorem uniPlaneGen_e6_adjoint {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3)
    (h3 : 3 ∣ Nat.card k - 1)
    (P : Subgroup (MulAut (adjointGroup Tag.E6 k))) (hP : IsElemAbelian 3 P)
    (hcard : Nat.card P = 3 ^ 2) :
    Inputs2311c.UniPlaneGen (ringChar k) P := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card k (ringChar k)
  let q : TauCeti.PrimePower := ⟨ringChar k, n, hℓ, n.pos⟩
  have hqK : Nat.card k = q.card := by
    rw [Nat.card_eq_fintype_card, hn, TauCeti.PrimePower.card_def]
  have hqmod : q.card % 3 = 1 := by
    have hq2 : 2 ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact le_trans hℓ.two_le
        (Nat.le_self_pow (TauCeti.PrimePower.exponent_pos q).ne' q.p)
    have h := h3
    rw [hqK] at h
    omega
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := TauCeti.LieTypeIndex.valid_E6 q
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.E6 q, hv⟩
  obtain ⟨e⟩ := catEquiv_adjointGroup_of_card CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
    q hv k hqK
  let P₀ : Subgroup (MulAut (Cat d)) := P.map (MulAut.congr e.symm).toMonoidHom
  have hP₀ : IsElemAbelian 3 P₀ := hP.map _
  have hcard₀ : Nat.card P₀ = 3 ^ 2 := by
    have h1 : Nat.card P₀ = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.congr e.symm).injective
    rw [h1, hcard]
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
    dsimp [d]
    exact not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_E6 q)
  have hpd : 3 ≠ d.1.characteristic := by
    dsimp [d]
    rw [TauCeti.LieTypeIndex.characteristic_E6]
    exact fun h => hk3 h.symm
  have hgen₀ : Inputs2311c.UniPlaneGen d.1.characteristic P₀ :=
    uniSeitzPlanes_E6_three_one d 3 Nat.prime_three (by norm_num) hpd hex P₀ hP₀ hcard₀
      ⟨rfl, q, rfl, hqmod⟩
  have hchar : d.1.characteristic = ringChar k := by
    dsimp [d]
    rw [TauCeti.LieTypeIndex.characteristic_E6]
  have hgen₁ : Inputs2311c.UniPlaneGen (ringChar k) P₀ := hchar ▸ hgen₀
  have hmapP : P₀.map (MulAut.congr e).toMonoidHom = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hy
      have h1 : (MulAut.congr e).toMonoidHom
          ((MulAut.congr e.symm).toMonoidHom p) = p := by
        ext z
        simp [MulAut.congr_apply]
      rw [h1]
      exact hp
    · intro hx
      refine ⟨MulAut.congr e.symm x, Subgroup.mem_map_of_mem _ hx, ?_⟩
      ext z
      simp [MulAut.congr_apply]
  rw [← hmapP]
  exact (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.uniPlaneGen_map_congr
    e (ringChar k) P₀).2 hgen₁

theorem seitzHyperGamma_eq_top_of_all24Plane {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3) (h3 : 3 ∣ Nat.card k - 1)
    (h4 : Nat.card k ≠ 4)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEd : coverImage θ E ≤ e6Inndiag k)
    {P : Subgroup (MulAut (adjointGroup Tag.E6 k))} (hPE : P ≤ coverImage θ E)
    (hPI : P ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k))
    (hP24 : ∀ s : adjointGroup Tag.E6 k, MulAut.conj s ∈ P → s ≠ 1 →
      Module.finrank k (LinearMap.ker
        (((s : ModGL .E6 k) : Module.End k (RootModule .E6 k)) - 1)) = 24)
    (hgen : Inputs2311c.UniPlaneGen (ringChar k) P) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  let π : K →* adjointGroup Tag.E6 k :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  let ind : MulAut K →* MulAut (adjointGroup Tag.E6 k) :=
    (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)
  have hind : ∀ (f : MulAut K) (g : K), π (f g) = ind f (π g) := by
    intro f g
    simp [π, ind, MulAut.congr, quotientCenterAut']
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
      apply θ.injective
      simpa [π] using hx
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hPE' : P ≤ E.map ind := by
    dsimp only [ind]
    exact hPE
  let Q : Subgroup (MulAut K) := E ⊓ P.comap ind
  have hQmap : Q.map ind = P := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hPE' hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have key : ∀ (φ : MulAut K) (hφ : φ ∈ Q) (hφ1 : ind φ ≠ 1),
      ∃ L : Subgroup K, L ≤ seitzHyperGamma 3 E ∧
        ∀ c : adjointGroup Tag.E6 k, ind φ c = c →
          (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) → c ∈ L.map π := by
    intro φ hφQ hφ1
    obtain ⟨hφE, hφP⟩ := Subgroup.mem_inf.1 hφQ
    have hφI : ind φ ∈ (MulAut.conj :
        adjointGroup Tag.E6 k →* MulAut (adjointGroup Tag.E6 k)).range := hPI hφP
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 hφI
    have hs1 : s ≠ 1 := by
      intro h1
      exact hφ1 (by rw [← hs, h1, map_one])
    have hs24 : Module.finrank k (LinearMap.ker
        (((s : ModGL .E6 k) : Module.End k (RootModule .E6 k)) - 1)) = 24 :=
      hP24 s (by rw [hs]; exact hφP) hs1
    have hsE : MulAut.conj s ∈ coverImage θ E := by
      rw [hs]
      exact hPE' hφP
    obtain ⟨ρ₀, hinj, hcomm, hcent, hdec, hlast⟩ :=
      exists_threeA2_frames hk3 h3 h4 (isElemAbelian_coverImage θ hE) hEd hsE hs24
    have hφne : φ ≠ 1 := fun h1 => hφ1 (by rw [h1, map_one])
    have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
    obtain ⟨ρ, hρcomp, hρle⟩ :=
      exists_lift_layer_le_seitzHyperGamma (π := π) (E := E) (ρ₀ := ρ₀) (σ := φ)
        h3 h4 hπ hker ind hind hE hcard27 hinj hcomm hφE hφne
        (fun i a => by rw [← hs]; exact hcent i a)
        (fun ε hεE => hdec (ind ε) ⟨ε, hεE, rfl⟩)
    refine ⟨⨆ i, (ρ i).range, ?_, ?_⟩
    · exact iSup_le hρle
    · intro c hfix hpow
      have hcs : Commute c s := by
        rw [commute_iff_eq]
        have h := hfix
        rw [show ind φ = MulAut.conj s from hs.symm, MulAut.conj_apply] at h
        calc c * s = (s * c * s⁻¹) * s := by rw [h]
          _ = s * c := by group
      have hmem : c ∈ ⨆ i, (ρ₀ i).range := hlast c hcs hpow
      have hmaple : (⨆ i, (ρ i).range).map π = ⨆ i, (ρ₀ i).range := by
        rw [Subgroup.map_iSup]
        exact iSup_congr fun i => by
          rw [← MonoidHom.range_comp π (ρ i), hρcomp i]
      rw [hmaple]
      exact hmem
  let Lfun : MulAut K → Subgroup K := fun φ =>
    if h : φ ∈ Q ∧ ind φ ≠ 1 then Classical.choose (key φ h.1 h.2) else ⊥
  have hL : ∀ φ ∈ Q, ind φ ≠ 1 → Lfun φ ≤ seitzHyperGamma 3 E := by
    intro φ hφ hφ1
    dsimp only [Lfun]
    rw [dif_pos ⟨hφ, hφ1⟩]
    exact (Classical.choose_spec (key φ hφ hφ1)).1
  have hr : ∀ φ ∈ Q, ind φ ≠ 1 → ∀ c : adjointGroup Tag.E6 k, ind φ c = c →
      (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) → c ∈ (Lfun φ).map π := by
    intro φ hφ hφ1 c hfix hpow
    dsimp only [Lfun]
    rw [dif_pos ⟨hφ, hφ1⟩]
    exact (Classical.choose_spec (key φ hφ hφ1)).2 c hfix hpow
  refine seitzHyperGamma_eq_top_of_uniPlaneGen_layers (π := π)
    hperf hπ hker ind (p := 3) (r := ringChar k) (E := E) (P := Q) ?_ Lfun hL hr
  rw [hQmap]
  exact hgen

theorem seitzHyperGamma_eq_top_e6_inner_cube {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3) (h3 : 3 ∣ Nat.card k - 1)
    (h4 : Nat.card k ≠ 4)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hin : E ≤ (MulAut.conj : K →* MulAut K).range)
    (hnorm : ¬ E6NormalizesR k (coverImage θ E)) :
    seitzHyperGamma 3 E = ⊤ := by
  have hEd : coverImage θ E ≤ e6Inndiag k :=
    (coverImage_le_range_conj θ hin).trans (innerAut_le_e6Inndiag k)
  have hinn : coverImage θ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k) :=
    coverImage_le_range_conj θ hin
  have hcardE : Nat.card (coverImage θ E) = 3 ^ 3 := by
    rw [card_coverImage hperf θ E, hcard]
  have hPlane : E6InnerAll24Plane :=
    e6InnerAll24Plane_of_pieces e6InnerSylowMono_holds e6InnerSylowMonoLine_holds
      e6MonoFixNormalizes_holds e6WeylEllipticOfNoFixed_holds e6MonoEllipticFix24_holds
      e6ThreeA2Conj_holds e6ThreeA2Witness_holds
  obtain ⟨P, hPE, hPcard, hP24⟩ :=
    hPlane k hk3 h3 h4 (coverImage θ E) (isElemAbelian_coverImage θ hE) hcardE hinn hnorm
  have hPab : IsElemAbelian 3 P := (isElemAbelian_coverImage θ hE).mono hPE
  have hgen : Inputs2311c.UniPlaneGen (ringChar k) P :=
    uniPlaneGen_e6_adjoint hk3 h3 P hPab hPcard
  exact seitzHyperGamma_eq_top_of_all24Plane hperf hk3 h3 h4 θ hE hcard hEd hPE
    (hPE.trans hinn) hP24 hgen

theorem seitzHyperGamma_eq_top_e6_diag_all24 {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤)
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3) (h3 : 3 ∣ Nat.card k - 1)
    (h4 : Nat.card k ≠ 4)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 k) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEd : coverImage θ E ≤ e6Inndiag k)
    (hEi : ¬ coverImage θ E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k))
    (hA : E6InnerAll24 k (coverImage θ E)) :
    seitzHyperGamma 3 E = ⊤ := by
  have hEi' : ¬ coverImage θ E ≤ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut
      (adjointGroup Tag.E6 k) := by
    simpa only [CFSG.Fischer.innerAut, CFSG.HardMathSupport.Solomon.LocalBalance.innerAut]
      using hEi
  have hcardE : Nat.card (coverImage θ E) = 3 ^ 3 := by
    rw [card_coverImage hperf θ E, hcard]
  let P : Subgroup (MulAut (adjointGroup Tag.E6 k)) :=
    coverImage θ E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k)
  have hPE : P ≤ coverImage θ E := inf_le_left
  have hPI : P ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 k) := inf_le_right
  have hPcard : Nat.card P = 3 ^ 2 := by
    dsimp only [P]
    simpa only [CFSG.Fischer.innerAut, CFSG.HardMathSupport.Solomon.LocalBalance.innerAut]
      using card_inf_innerAut_of_le_e6Inndiag k hcardE hEd hEi'
  have hPab : IsElemAbelian 3 P := (isElemAbelian_coverImage θ hE).mono hPE
  have hP24 : ∀ s : adjointGroup Tag.E6 k, MulAut.conj s ∈ P → s ≠ 1 →
      Module.finrank k (LinearMap.ker
        (((s : ModGL .E6 k) : Module.End k (RootModule .E6 k)) - 1)) = 24 :=
    fun s hs hs1 => hA s (hPE hs) hs1
  have hgen : Inputs2311c.UniPlaneGen (ringChar k) P :=
    uniPlaneGen_e6_adjoint hk3 h3 P hPab hPcard
  exact seitzHyperGamma_eq_top_of_all24Plane hperf hk3 h3 h4 θ hE hcard hEd hPE hPI hP24 hgen

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
