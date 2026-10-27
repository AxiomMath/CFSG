module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Torus
public import CFSG.HardMathSupport.Malle.SeitzCube.E6D4LineTransport
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6ThreeAssembly

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints twistedTorus)

open CFSG.RankThree.PartOne.KE6 (phi3N)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit)

open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

section Setup

variable
  {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]

theorem exists_d4Line_layer {ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K}
    (hψ : IsSignedFrame K ψ) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpr : p ≠ r)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : SL(3, K)} (hg : orderOf g = p)
    (s : Fin 3) :
    ∃ Y : Subgroup ↥(adjointGroup Tag.E6 K),
      (∀ y ∈ Y, Commute y (ψ 0 g * ψ 1 (g ^ (Nat.card K ^ (s : ℕ))))) ∧
      (∀ S : Set (Fin Tag.E6.rank → ℤ), (∀ α ∈ S, IsRoot Tag.E6 α) →
        (∀ (F : Type) [Field F] (a : Fin Tag.E6.rank → Fˣ) (v : ModGL Tag.E6 F),
          v ∈ rootSpan Tag.E6 F S → v ∈ Subgroup.centralizer
            ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 F)) →
          v ∈ rootSpan Tag.E6 F (rootCharKernel a ∩ S)) →
        (∀ (F : Type) [Field F], parabolicLevi Tag.E6 F (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ≤
          Subgroup.normalizer (rootSpan Tag.E6 F S : Set (ModGL Tag.E6 F))) →
        ∀ u : ↥(adjointGroup Tag.E6 K), (u : ModGL Tag.E6 K) ∈ rootSpan Tag.E6 K S →
          Commute u (ψ 0 g * ψ 1 (g ^ (Nat.card K ^ (s : ℕ)))) → u ∈ Y) ∧
      ψ 2 g ∈ Y ∧ ψ 0 g * ψ 1 (g ^ ((p - 1) * Nat.card K ^ (s : ℕ))) ∈ Y ∧
      (∃ q' : TauCeti.PrimePower, q'.card = Nat.card K ∧ q'.p = r ∧
        CFSG.RankThree.PartOne.Census3.IsoLie ↥Y (.trialityD4 q')) ∧
      (∀ y ∈ Y, (∀ z ∈ Y, z * y = y * z) → y = 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hn⟩ : ∃ n : ℕ+, Nat.card K = r ^ (n : ℕ) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K r
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  set q := Nat.card K with hqdef
  let Ω := AlgebraicClosure K
  haveI : CharP Ω r := charP_of_injective_algebraMap (algebraMap K Ω).injective r
  let Fr : Ω →+* Ω := iterateFrobenius Ω r n
  have hFr : ∀ c, Fr c = c ^ q := fun c => by rw [hn]; exact iterateFrobenius_def r n c
  obtain ⟨ζ, Qs, D, d, hζ, hDc, hgQ, hM⟩ :=
    exists_singer_frobenius (Ω := Ω) (Fr := Fr) hFr hp hp3 hpr hpq hg
  obtain ⟨ψΩ, hΩinj, hΩcomm, hψΩ⟩ := exists_three_sl3_E6_signed Ω
  have hψΩ' : IsSignedFrame Ω ψΩ := hψΩ
  set Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := Units.map (entrywiseHom Fr) with hΦ
  set Qh : ModGL Tag.E6 Ω := frameHom ψΩ hΩcomm Qs with hQh
  have hnQ : Qh⁻¹ * Φ Qh = frameHom ψΩ hΩcomm (Qs⁻¹ * Matrix.SpecialLinearGroup.map Fr Qs) := by
    rw [map_mul, map_inv, frameHom_frob hΩcomm hψΩ' Fr Qs]
  obtain ⟨hn0, hw0⟩ := e6D4_singer_monomial ψΩ hψΩ (Qs⁻¹ * Matrix.SpecialLinearGroup.map Fr Qs) d hM
  have hn' : Qh⁻¹ * Φ Qh ∈ monomialSubgroup Tag.E6 Ω := by rw [hnQ]; exact hn0
  have hw' : weylQuotientHom Tag.E6 Ω ⟨_, hn'⟩ = e6D4wp := by
    have : (⟨Qh⁻¹ * Φ Qh, hn'⟩ : monomialSubgroup Tag.E6 Ω) = ⟨_, hn0⟩ := Subtype.ext hnQ
    rw [this]; exact hw0
  obtain ⟨c, hc, hH1, hH2⟩ := exists_twisted_conj hFr Qh hn' hw'
  set ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.E6 K).subtype with hι
  have hcomp : Fr.comp (algebraMap K Ω) = algebraMap K Ω :=
    RingHom.ext fun c => frobenius_algebraMap hFr c
  have hιΦ : ∀ y, Φ (ι y) = ι y := by
    intro y
    have e : Units.map (entrywiseHom Fr) (ι y) = baseChangeGL Fr (ι y) := Units.ext rfl
    change Units.map (entrywiseHom Fr) (ι y) = ι y
    rw [e]
    change baseChangeGL Fr (baseChangeGL (algebraMap K Ω) (y : ModGL Tag.E6 K)) =
      baseChangeGL (algebraMap K Ω) (y : ModGL Tag.E6 K)
    rw [baseChangeGL_baseChangeGL, hcomp]
  have hdm : ∀ k : ℕ, ((D ^ k : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      Matrix.diagonal fun j => ((e6Dg ζ q k j : Ωˣ) : Ω) := by
    intro k
    rw [Matrix.SpecialLinearGroup.coe_pow, hDc, Matrix.diagonal_pow]
    congr 1
    funext j
    have hqc : Fintype.card K = q := (Nat.card_eq_fintype_card).symm
    fin_cases j <;> simp [e6Dg, ← pow_mul, mul_comm, hqc]
  have hblock : ∀ (i : Fin 3) (k : ℕ), frameBlock ψΩ i (D ^ k) =
      rootDiagUnit Tag.E6 (e6A2TorusChar i (e6Dg ζ q k)) := fun i k =>
    sl3Hom_diag_eq_rootDiagUnit_of_signs i (frameBlock ψΩ i) (e6A2Sign i)
      (fun γ _ => e6A2Sign_eq i γ) (hψΩ i) (e6Dg ζ q k) (D ^ k) (hdm k)
  have hιψ : ∀ (i : Fin 3) (h : SL(3, K)), ι (ψ i h) =
      frameBlock ψΩ i (Matrix.SpecialLinearGroup.map (algebraMap K Ω) h) := fun i h =>
    (frameBlock_map (algebraMap K Ω) hψ hψΩ' i h).symm
  have hgpow : ∀ k : ℕ, Matrix.SpecialLinearGroup.map (algebraMap K Ω) (g ^ k) =
      Qs * D ^ k * Qs⁻¹ := fun k => by rw [map_pow, hgQ, conj_pow]
  have hconjB' : ∀ (i : Fin 3) (k : ℕ), Qh⁻¹ * ι (ψ i (g ^ k)) * Qh = frameBlock ψΩ i (D ^ k) := by
    intro i k
    rw [hιψ, hgpow]
    have := frameHom_conj hΩcomm i Qs (Qs * D ^ k * Qs⁻¹)
    rw [hQh, this]
    congr 2
    group
  have hconjB : ∀ (i : Fin 3) (k : ℕ), Qh⁻¹ * ι (ψ i (g ^ k)) * Qh =
      rootDiagUnit Tag.E6 (e6A2TorusChar i (e6Dg ζ q k)) := fun i k => by
    rw [hconjB', hblock]
  set mw : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω e6D4m with hmw
  set m : ℕ := q ^ (s : ℕ) with hm
  set Δ : ModGL Tag.E6 Ω := rootDiagUnit Tag.E6 (e6KerChar ζ q 1 m) with hΔ
  set e : adjointGroup Tag.E6 K := ψ 0 g * ψ 1 (g ^ m) with he
  have hΔgen : ∀ y : ℕ, Qh⁻¹ * ι (ψ 0 g * ψ 1 (g ^ y)) * Qh =
      rootDiagUnit Tag.E6 (e6KerChar ζ q 1 y) := by
    intro y
    have h0 := hconjB 0 1
    have h1 := hconjB 1 y
    rw [pow_one] at h0
    rw [map_mul]
    calc Qh⁻¹ * (ι (ψ 0 g) * ι (ψ 1 (g ^ y))) * Qh
        = (Qh⁻¹ * ι (ψ 0 g) * Qh) * (Qh⁻¹ * ι (ψ 1 (g ^ y)) * Qh) := by group
      _ = _ := by rw [h0, h1, e6KerChar, rootDiagUnit_mul]
  have hΔe : Qh⁻¹ * ι e * Qh = Δ := hΔgen m
  have hΔtor : Δ ∈ torusGroup Tag.E6 Ω := rootDiagUnit_mem_torusGroup _
  have hxe : (c * mw * Qh⁻¹) * ι e * (c * mw * Qh⁻¹)⁻¹ = mw * Δ * mw⁻¹ := by
    have h : c * mw * Δ * (c * mw)⁻¹ = (c * mw * Qh⁻¹) * ι e * (c * mw * Qh⁻¹)⁻¹ := by
      rw [← hΔe]; group
    rw [← torus_conj_mul_canonicalRep hc hΔtor]
    exact h.symm
  obtain ⟨hx', hker⟩ := e6D4Line_transport (Ω := Ω) (Fr := Fr) (p := p) (q := q) (x := 1) (y := m)
    (ζ := ζ) (s := s) hFr hp hp3 hζ hpq (by simp [hp.one_lt.ne']) (by simp [hm])
  have hFr' : ∀ c, Fr c = c ^ (r ^ (n : ℕ)) := fun c => by rw [hFr, hn]
  obtain ⟨-, hPfin, hPqs, -, -, e12, g', he12, hconjL, ⟨hequiv⟩⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.phi3_D4_layer_data' (K := K) (Ω := Ω) (ℓ := r)
      (f := (n : ℕ)) n.pos hn hFr' hx' hker
  set x' : ModGL Tag.E6 Ω := mw * Δ * mw⁻¹ with hx'def
  set Pk : Subgroup (ModGL Tag.E6 Ω) :=
    rootSpan Tag.E6 Ω (torusRootKernel x') ⊓ twistedFixedPoints (phi3N Ω) Φ with hPk
  haveI : Finite Pk := hPfin
  have hPadj : Pk ≤ adjointGroup Tag.E6 Ω := inf_le_left.trans (rootSpan_le_adjointGroup Ω _)
  have hPperf : ⁅Pk, Pk⁆ = Pk := Subgroup.isPerfect_iff.mp hPqs.1
  set H : ModGL Tag.E6 Ω := c * mw * Qh⁻¹ with hH
  have hQhadj : Qh ∈ adjointGroup Tag.E6 Ω :=
    mul_mem (mul_mem (ψΩ 0 Qs).2 (ψΩ 1 Qs).2) (ψΩ 2 Qs).2
  have hHadj : H ∈ adjointGroup Tag.E6 Ω :=
    mul_mem (mul_mem (CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' hc)
      (canonicalRep_mem_adjointGroup _ Ω e6D4m)) (inv_mem hQhadj)
  have hPfix : ∀ z ∈ Pk, Units.map (entrywiseHom Fr) (H⁻¹ * z * H) = H⁻¹ * z * H :=
    fun z hz => hH2 z hz.2
  obtain ⟨hsurj, ⟨eY⟩⟩ := exists_layer_equiv (K := K) hFr H hHadj Pk hPadj hPperf hPfix
  have hlay : ∀ u : adjointGroup Tag.E6 K, layerHom K Ω H u = H * ι u * H⁻¹ := fun u => rfl
  have hSig : rootCharKernel (e6KerChar ζ q 1 m) = e6BlockRoots 2 ∪ e6MixedRoots s :=
    rootCharKernel_e6KerChar_mixed hp hp3 hζ hpq (by simp [hp.one_lt.ne']) (by simp [hm])
  have hSigroot : ∀ α ∈ rootCharKernel (e6KerChar ζ q 1 m), IsRoot Tag.E6 α := fun α hα => hα.1
  obtain ⟨a', hconj', hchi'⟩ := exists_conj_rootDiagUnit (Ω := Ω) (e6KerChar ζ q 1 m) e6D4m
  have hx'a : x' = rootDiagUnit Tag.E6 a' := by rw [hconj', hx'def, hΔ]
  have hkerx' : torusRootKernel x' =
      (fun γ => e6D4m • γ) '' rootCharKernel (e6KerChar ζ q 1 m) := by
    rw [hx'a, torusRootKernel_rootDiagUnit, rootCharKernel_of_rootChar e6D4m hchi']
  have hmemY : ∀ (u : adjointGroup Tag.E6 K) (v : ModGL Tag.E6 Ω),
      v ∈ rootSpan Tag.E6 Ω (rootCharKernel (e6KerChar ζ q 1 m)) → Qh⁻¹ * ι u * Qh = v →
        u ∈ Pk.comap (layerHom K Ω H) := by
    intro u v hv hvu
    have h1 : H * ι u * H⁻¹ = c * mw * v * (c * mw)⁻¹ := by rw [← hvu, hH]; group
    refine ⟨?_, ?_⟩
    · show layerHom K Ω H u ∈ rootSpan Tag.E6 Ω (torusRootKernel x')
      rw [hlay, h1, hkerx']
      exact conj_cm_mem_rootSpan hSigroot hc hv e6D4m
    · exact hH1 (ι u) (hιΦ u)
  have hex : (∃ q' : TauCeti.PrimePower, q'.card = Nat.card K ∧ q'.p = r ∧
        CFSG.RankThree.PartOne.Census3.IsoLie ↥(Pk.comap (layerHom K Ω H)) (.trialityD4 q')) ∧
      (∀ y ∈ Pk.comap (layerHom K Ω H), (∀ z ∈ Pk.comap (layerHom K Ω H), z * y = y * z) →
        y = 1) := by
    have hk₃ := CFSG.RankThree.PartOne.KE6.natCard_cubicSubfield (Ω := Ω) (ℓ := r) (f := (n : ℕ))
      n.pos
    have : IsAlgClosure (CFSG.RankThree.PartOne.KE6.cubicSubfield (Ω := Ω) r (n : ℕ)) Ω :=
      ⟨inferInstance, CFSG.RankThree.PartOne.KE6.isAlgebraic_cubicSubfield hn⟩
    have : CharP (CFSG.RankThree.PartOne.KE6.cubicSubfield (Ω := Ω) r (n : ℕ)) r := inferInstance
    let σ₃ : CFSG.RankThree.PartOne.KE6.cubicSubfield (Ω := Ω) r (n : ℕ) →+*
        CFSG.RankThree.PartOne.KE6.cubicSubfield (Ω := Ω) r (n : ℕ) :=
      iterateFrobenius _ r (n : ℕ)
    have hσ₃ : ∀ c, σ₃ c = c ^ (r ^ (n : ℕ)) := fun c => iterateFrobenius_def r (n : ℕ) c
    have hfin₃ : Finite (CFSG.RankThree.PartOne.KE6.cubicSubfield (Ω := Ω) r (n : ℕ)) :=
      Nat.finite_of_card_ne_zero (by
        rw [hk₃]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : r.Prime).ne_zero))
    obtain ⟨φ⟩ := nonempty_d4Layer_equiv_cat (K := CFSG.RankThree.PartOne.KE6.cubicSubfield
      (Ω := Ω) r (n : ℕ)) (Ω := Ω) (σ := σ₃) (Fr := Fr) (e := e12) Fact.out n.pos hk₃ he12 hσ₃
      hFr' (TauCeti.LieTypeIndex.valid_trialityD4 ⟨r, (n : ℕ), Fact.out, n.pos⟩)
    obtain ⟨φg, -⟩ := exists_d4Layer_equiv (K := CFSG.RankThree.PartOne.KE6.cubicSubfield
      (Ω := Ω) r (n : ℕ)) (Ω := Ω) (σ := σ₃) (Fr := Fr) (Fact.out : r.Prime) n.pos hk₃ he12
      hσ₃ hFr'
    refine ⟨⟨⟨r, (n : ℕ), Fact.out, n.pos⟩, ?_, rfl, TauCeti.LieTypeIndex.valid_trialityD4 _, ?_⟩, ?_⟩
    · rw [TauCeti.PrimePower.card_def]; exact hn.symm
    · exact ⟨((eY.trans hequiv).trans (d4ThetaFixedEquivLayer Fr e12)).trans φ⟩
    · intro y hy hyz
      set Ψ := (((eY.trans hequiv).trans (d4ThetaFixedEquivLayer Fr e12)).trans φg) with hΨ
      have hcen : Ψ ⟨y, hy⟩ ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4
          (CFSG.RankThree.PartOne.KE6.cubicSubfield (Ω := Ω) r (n : ℕ)) σ₃) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨y', rfl⟩ := Ψ.surjective z
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hyz y' y'.2)
      rw [center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ₃.injective)] at hcen
      have : Ψ ⟨y, hy⟩ = 1 := hcen
      have h1 : (⟨y, hy⟩ : ↥(Pk.comap (layerHom K Ω H))) = 1 := Ψ.injective (by rw [this, map_one])
      exact congrArg Subtype.val h1
  refine ⟨Pk.comap (layerHom K Ω H), ?_, ?_, ?_, ?_, hex.1, hex.2⟩
  · intro y hy
    have hyP : layerHom K Ω H y ∈ rootSpan Tag.E6 Ω (rootCharKernel a') := by
      have := hy.1
      rwa [hx'a, torusRootKernel_rootDiagUnit] at this
    have hc' := commute_rootDiagUnit_of_mem_rootSpan_kernel a' hyP
    have hex : layerHom K Ω H e = rootDiagUnit Tag.E6 a' := by
      rw [hlay, hxe]; exact hx'a
    rw [← hex] at hc'
    have : layerHom K Ω H (y * e) = layerHom K Ω H (e * y) := by
      rw [MonoidHom.map_mul (layerHom K Ω H) y e, MonoidHom.map_mul (layerHom K Ω H) e y]
      exact hc'.eq
    exact layerHom_injective H this
  · intro S hSroot hfix hLevi u hu hcomm
    have hιu : ι u ∈ rootSpan Tag.E6 Ω S :=
      map_baseChangeGL_rootSpan_le (algebraMap K Ω) S ⟨(u : ModGL Tag.E6 K), hu, rfl⟩
    set Q01 : ModGL Tag.E6 Ω := frameBlock ψΩ 0 Qs * frameBlock ψΩ 1 Qs with hQ01
    set P2 : ModGL Tag.E6 Ω := frameBlock ψΩ 2 Qs with hP2
    have hQhe : Qh = Q01 * P2 := rfl
    have hψε : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : Ω, (ε = 1 ∨ ε = -1) ∧ ∀ c : Ω,
        ((ψΩ i (CFSG.LieType.Steinberg.SL.x 2 Ω γ c) : adjointGroup Tag.E6 Ω) : ModGL Tag.E6 Ω) =
          pinnedX Tag.E6 Ω (e6A2Frame i γ) (ε * c) := by
      intro i γ hγ
      refine ⟨(e6A2Sign i γ : Ω), ?_, hψΩ i γ hγ⟩
      rcases e6A2Sign_eq i γ with h1 | h1 <;> rw [h1] <;> simp
    have hL0 : frameBlock ψΩ 0 Qs ∈ parabolicLevi Tag.E6 Ω
        (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
      parabolicLevi_mono Set.subset_union_left (range_le_parabolicLevi_E6 Ω ψΩ hψε 0 Qs)
    have hL1 : frameBlock ψΩ 1 Qs ∈ parabolicLevi Tag.E6 Ω
        (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
      parabolicLevi_mono Set.subset_union_right (range_le_parabolicLevi_E6 Ω ψΩ hψε 1 Qs)
    have hLQ : Q01 ∈ parabolicLevi Tag.E6 Ω (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
      mul_mem hL0 hL1
    have hv1S : Q01⁻¹ * ι u * Q01 ∈ rootSpan Tag.E6 Ω S := by
      have hn := hLevi Ω (inv_mem hLQ)
      have := (Subgroup.mem_normalizer_iff.1 hn (ι u)).1 hιu
      rwa [inv_inv] at this
    have hP2c : Commute P2 Δ := by
      have hΔ' : Δ = frameBlock ψΩ 0 (D ^ 1) * frameBlock ψΩ 1 (D ^ m) := by
        rw [hΔ, e6KerChar, rootDiagUnit_mul, ← hblock 0 1, ← hblock 1 m]
      rw [hΔ']
      exact (frameBlock_commute hΩcomm (i := 2) (j := 0) (by decide) Qs _).mul_right
        (frameBlock_commute hΩcomm (i := 2) (j := 1) (by decide) Qs _)
    have hQ01e : Q01⁻¹ * ι e * Q01 = Δ := by
      have h1 : Q01⁻¹ * ι e * Q01 = P2 * (Qh⁻¹ * ι e * Qh) * P2⁻¹ := by
        rw [hQhe]; group
      rw [h1, hΔe, hP2c.eq]; group
    have hcomm' : Commute (ι u) (ι e) := hcomm.map ι
    have hv1C : Commute (Q01⁻¹ * ι u * Q01) Δ := by
      show Q01⁻¹ * ι u * Q01 * Δ = Δ * (Q01⁻¹ * ι u * Q01)
      rw [← hQ01e]
      calc Q01⁻¹ * ι u * Q01 * (Q01⁻¹ * ι e * Q01) = Q01⁻¹ * (ι u * ι e) * Q01 := by group
        _ = Q01⁻¹ * (ι e * ι u) * Q01 := by rw [hcomm'.eq]
        _ = _ := by group
    have hv1K := hfix Ω (e6KerChar ζ q 1 m) _ hv1S
      (Subgroup.mem_centralizer_iff.2 fun d hd => by
        rw [Set.mem_singleton_iff] at hd
        subst hd
        exact hv1C.eq.symm)
    have hSub : rootCharKernel (e6KerChar ζ q 1 m) ∩ S ⊆ rootCharKernel (e6KerChar ζ q 1 m) :=
      Set.inter_subset_left
    have hP2K : P2 ∈ rootSpan Tag.E6 Ω (rootCharKernel (e6KerChar ζ q 1 m)) :=
      rootSpan_mono (by rw [hSig]; exact Set.subset_union_left)
        (frameBlock_mem_rootSpan_block hψΩ' 2 Qs)
    refine hmemY u (P2⁻¹ * (Q01⁻¹ * ι u * Q01) * P2) ?_ ?_
    · exact mul_mem (mul_mem (inv_mem hP2K) (rootSpan_mono hSub hv1K)) hP2K
    · rw [hQhe]; group
  · exact hmemY (ψ 2 g) (frameBlock ψΩ 2 D)
      (rootSpan_mono (by rw [hSig]; exact Set.subset_union_left)
        (frameBlock_mem_rootSpan_block hψΩ' 2 D))
      (by have := hconjB' 2 1; rwa [pow_one, pow_one] at this)
  · exact hmemY _ (rootDiagUnit Tag.E6 (e6KerChar ζ q 1 ((p - 1) * m)))
      (by rw [hSig]; exact e6D4_torus_mem_kernel hp hζ hpq s) (hΔgen ((p - 1) * m))
end Setup

end CFSG.HardMathSupport.Malle.SeitzCube
