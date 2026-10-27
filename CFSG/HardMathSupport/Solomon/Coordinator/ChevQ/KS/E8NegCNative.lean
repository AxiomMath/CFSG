module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCE6Iso
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCLayer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCCover
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest9

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8NegC

open Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Seitz CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)


set_option linter.unusedSectionVars false


section Layer

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem e6Layer_of_maps (hf : 1 ≤ f) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α ∈ parabolicRoots τ (e6Nodes τ))
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Finite P ∧ CFSG.IsQuasisimple P ∧
      ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (parabolicRoots τ (e6Nodes τ)),
        (∀ u ∈ P, y * u = u * y) → y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (rootSpan τ L (parabolicRoots τ (e6Nodes τ)) :
            Set (ModGL τ L)) := by
  have hw : MapsJ τ (e6Set τ) (weylQuotientHom τ L ⟨n, hn⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ, hact⟩ := exists_action hw
  have hπJ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, -, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπJ hπJ' hu hact
  have hstd : StdTwist6 n₁ π := ⟨hπ, hgen⟩
  have hP' : P = subsystemGroup τ L (e6Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hP, subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  obtain ⟨h1, h2, h3, -⟩ := layer_of_standard6 hf hstd hh hlang hP'
  refine ⟨h1, h2, fun y hy hc => ?_⟩
  rw [e6Nodes_eq_e6Set, ← subsystemGroup_eq_rootSpan] at hy ⊢
  exact h3 y hy hc

end Layer

section Lang

variable {L : Type} [Field L]

theorem torusGroup_inf_rootSpan_eq_e6 :
    torusGroup Tag.E8 L ⊓ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) =
      supportedTorus Tag.E8 L (e6Nodes Tag.E8) := by
  have hJ : subsystemGroup Tag.E8 L (e6Nodes Tag.E8) ⊓ torusGroup Tag.E8 L =
      supportedTorus Tag.E8 L (e6Nodes Tag.E8) :=
    subsystemGroup_inf_torusGroup_eq_supportedTorus _
  rw [subsystemGroup_eq_rootSpan] at hJ
  rw [inf_comm]
  exact hJ

theorem lang_torus_inf_rootSpan_e6 [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) {n : ModGL Tag.E8 L} (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hJ : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      weylQuotientHom Tag.E8 L ⟨n, hn⟩ • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :
    ∀ s ∈ torusGroup Tag.E8 L ⊓ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)),
      ∃ t ∈ torusGroup Tag.E8 L ⊓ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)),
        t⁻¹ * (n * Units.map (entrywiseHom Fr) t * n⁻¹) = s := by
  rw [torusGroup_inf_rootSpan_eq_e6]
  exact CFSG.HardMathSupport.Foote.Coordinator.exists_lang_supportedTorus_of_monomial hq hFr n hn hJ

end Lang

section Twist

variable {τ : Tag} {L : Type} [Field L]

theorem twist_mem_torusGroup [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) :
    n * Units.map (entrywiseHom Fr) h * n⁻¹ ∈ torusGroup τ L := by
  have h1 : Units.map (entrywiseHom Fr) h ∈ torusGroup τ L := by
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    have := units_map_entrywiseHom_rootDiagUnit_ringEquiv (τ := τ)
      (RingEquiv.ofBijective Fr hFrb) b
    have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at this
    rw [this]
    exact rootDiagUnit_mem_torusGroup _
  exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_torusGroup_of_mem_monomialSubgroup hn)
    _).1 h1

theorem twist_mem_rootSpan {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) {S : Set (Fin τ.rank → ℤ)}
    (hSr : ∀ α ∈ S, IsRoot τ α) (hS : ∀ β ∈ S, weylQuotientHom τ L ⟨n, hn⟩ • β ∈ S)
    {g : ModGL τ L} (hg : g ∈ rootSpan τ L S) :
    n * Units.map (entrywiseHom Fr) g * n⁻¹ ∈ rootSpan τ L S := by
  have h1 : Units.map (entrywiseHom Fr) g ∈ rootSpan τ L S := by
    have h := CFSG.RankThree.PartOne.KLR.map_entrywise_rootSpan (τ := τ)
      (RingEquiv.ofBijective Fr hFrb) S
    have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h
    rw [← h]
    exact ⟨g, hg, rfl⟩
  have hmap := map_conj_rootSpan_of_mem_monomialSubgroup hn (S := S) hSr
  have h3 : n * Units.map (entrywiseHom Fr) g * n⁻¹ ∈
      rootSpan τ L ((fun γ => weylQuotientHom τ L ⟨n, hn⟩ • γ) '' S) := by
    rw [← hmap]
    exact ⟨_, h1, rfl⟩
  exact rootSpan_mono (by rintro _ ⟨γ, hγ, rfl⟩; exact hS γ hγ) h3

theorem smul_mem_parabolicRoots_of_act_neg {J : Set (Fin τ.rank)} {w u : WeylGroup τ}
    (hu : u ∈ parabolicWeylGroup τ J)
    (hact : ∀ α ∈ parabolicRoots τ J, w • α = u • ((-1 : ℤ) • α)) :
    ∀ α ∈ parabolicRoots τ J, w • α ∈ parabolicRoots τ J := by
  intro α hα
  rw [hact α hα]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [neg_one_zsmul]
    exact IsRoot.smul (IsRoot.neg hα.1) u
  · rw [neg_one_zsmul, smul_apply_of_mem_parabolicWeylGroup hu _ hi]
    simp [hα.2 i hi]

end Twist

section Native

theorem card_conditions {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hq1 : 3 ∣ ℓ ^ f + 1)
    (hq28 : ¬ (ℓ = 2 ∧ (f = 1 ∨ f = 3))) :
    (ℓ ^ f) % 3 = 2 ∧ ℓ ^ f ≠ 2 ∧ ℓ ^ f ≠ 8 := by
  refine ⟨by omega, fun h => ?_, fun h => ?_⟩
  · have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1
      (h ▸ dvd_pow_self ℓ (by omega : f ≠ 0))
    subst hℓ2
    have : 2 ^ f = 2 ^ 1 := by rw [h, pow_one]
    exact hq28 ⟨rfl, Or.inl (Nat.pow_right_injective (le_refl 2) this)⟩
  · have h2 : 2 ∣ ℓ := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ ℓ ^ f by rw [h]; norm_num)
    have hℓ2 : ℓ = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h2).symm
    subst hℓ2
    have : 2 ^ f = 2 ^ 3 := by rw [h]; norm_num
    exact hq28 ⟨rfl, Or.inr (Nat.pow_right_injective (le_refl 2) this)⟩

theorem native_a2e6_line_le_hyperClosure (hD : QuasiHigh5E6Cover.TwE6ThreeOpenDiag)
    {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hq1 : 3 ∣ ℓ ^ f + 1) (hq28 : ¬ (ℓ = 2 ∧ (f = 1 ∨ f = 3)))
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (u : WeylGroup Tag.E8) (hu : u ∈ parabolicWeylGroup Tag.E8 (e6Nodes Tag.E8))
    (hact : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • α = u • ((-1 : ℤ) • α))
    {S₀ : Set (Fin Tag.E8.rank → ℤ)} (hS₀r : ∀ α ∈ S₀, IsRoot Tag.E8 α)
    (hS₀w : ∀ α ∈ S₀, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • α ∈ S₀)
    (hS₀o : ∀ α ∈ S₀, ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0)
    {G : Type} [Group G] (ψ : G →* ModGL Tag.E8 L) (hψ : Function.Injective ψ)
    {E : Subgroup G} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hψE : ∀ e ∈ E, ψ e ∈ torusGroup Tag.E8 L ∧
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ e) * n⁻¹ = ψ e)
    {y z : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hz : z ∈ E) (hzy : z ∉ Subgroup.zpowers y)
    (hψy : ∀ g ∈ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)),
      ψ y * g = g * ψ y)
    (hψz : ∀ g ∈ rootSpan Tag.E8 L S₀, ψ z * g = g * ψ z)
    (hψN : ∀ k : G, k * y = y * k →
      ψ k ∈ torusGroup Tag.E8 L ⊔
          rootSpan Tag.E8 L (S₀ ∪ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ∧
        n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ k) * n⁻¹ = ψ k)
    (hrat : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * n⁻¹ = x) →
        ⁅P, P⁆ = P → ∀ x ∈ P, ∃ g, ψ g = x) :
    Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ x, Fr x = x ^ ℓ ^ f := fun x => iterateFrobenius_def ℓ f x
  have hFrb : Function.Bijective Fr := ⟨Fr.injective, fun w => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq w (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  obtain ⟨hq3, hqne2, hqne8⟩ := card_conditions hℓ hf hq1 hq28
  let q : TauCeti.PrimePower := ⟨ℓ, f, hℓ, hf⟩
  have hqc : q.card = ℓ ^ f := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 q
  have hwS := smul_mem_parabolicRoots_of_act_neg hu hact
  set Γ : Subgroup (ModGL Tag.E8 L) :=
    rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) ⊓ twistedFixedPoints n Φ with hΓ
  obtain ⟨hPfin, hPq, hfree⟩ := e6Layer_of_maps hf hnm hwS Γ rfl
  haveI := hPfin
  have hu' : u ∈ parabolicWeylGroup Tag.E8 (e6Set Tag.E8) := by rwa [e6Nodes_eq_e6Set] at hu
  obtain ⟨e⟩ := nonempty_layer_quotient_equiv_cat hf hnm (mul_mem hu' w0E6_mem)
    (act_rho_of_act_neg hnm hact) Γ rfl hqc hv
  have hPQ : Γ ≤ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) := inf_le_left
  have hPfix : ∀ x ∈ Γ, n * Φ x * n⁻¹ = x := fun x hx => (Subgroup.mem_inf.1 hx).2
  have hPadj : Γ ≤ adjointGroup Tag.E8 L := hPQ.trans (rootSpan_le_adjointGroup L _)
  have hPperf : ⁅Γ, Γ⁆ = Γ := Subgroup.isPerfect_iff.1 hPq.1
  have hPperf' : commutator Γ = ⊤ := hPq.1.commutator_eq_top
  have hPψ : ∀ x ∈ Γ, ∃ g, ψ g = x := hrat Γ hPfin hPadj hPfix hPperf
  have hPnorm : ∀ e ∈ E, ∀ x ∈ Γ, ψ e * x * (ψ e)⁻¹ ∈ Γ := by
    intro e he x hx
    obtain ⟨heH, heθ⟩ := hψE e he
    have heθ' : ψ e ∈ twistedFixedPoints n Φ := heθ
    obtain ⟨hxQ, hxθ⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem heθ' hxθ) (inv_mem heθ')⟩
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
        (fun (α : Fin Tag.E8.rank → ℤ) (hα : α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) => hα.1)
        heH) x).1 hxQ
  have hPy : ∀ x ∈ Γ, ψ y * x = x * ψ y := fun x hx => hψy x (hPQ hx)
  have hlayer : ∀ g : G, ψ g ∈ Γ → g ∈ hyperClosure 3 ⊤ E :=
    layer_le_hyperClosure_of_gen ψ hψ hE hEc hy hy1 Γ hPψ hPy hPnorm fun hcard =>
      seitzHyperGamma_eq_top_twE6Cover hD hPperf' hv e (by rw [hqc]; exact hq3)
        (by rw [hqc]; exact hqne2) (by rw [hqc]; exact hqne8)
        (isElemAbelian_layerAction_range ψ hE hPnorm) hcard
  have hτ : Tag.E8 = Tag.D4 ∨ Tag.E8 = Tag.E6 ∨ Tag.E8 = Tag.E7 ∨ Tag.E8 = Tag.E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  have hJr : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8), IsRoot Tag.E8 α := fun α hα => hα.1
  have hcommQ := CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (L := L) hτ hS₀r hJr hS₀o
  have hθH : ∀ h ∈ torusGroup Tag.E8 L, n * Φ h * n⁻¹ ∈ torusGroup Tag.E8 L := fun h hh =>
    twist_mem_torusGroup hFrb hnm hh
  have hθS₀ : ∀ g ∈ rootSpan Tag.E8 L S₀, n * Φ g * n⁻¹ ∈ rootSpan Tag.E8 L S₀ := fun g hg =>
    twist_mem_rootSpan hFrb hnm hS₀r hS₀w hg
  have hθJ : ∀ g ∈ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)),
      n * Φ g * n⁻¹ ∈ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) := fun g hg =>
    twist_mem_rootSpan hFrb hnm hJr hwS hg
  have hHS₀ := CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (K := L) hS₀r
  refine SeitzExcOpenRest9Aux.centralizer_le_hyperClosure_of_layer_split ψ hψ hE hEc hy hy1 hz
    hzy Γ hPψ hPy hlayer ?_
  intro k hky
  obtain ⟨hkN, hkθ⟩ := hψN k hky
  obtain ⟨h, hh, z₀, hz₀, z₁, hz₁, hk⟩ :=
    CFSG.RankThree.PartOne.KE.exists_decomp_union hτ hS₀r hJr hS₀o hkN
  set θ : ModGL Tag.E8 L → ModGL Tag.E8 L := fun x => n * Φ x * n⁻¹ with hθdef
  have hθmul : ∀ a b, θ (a * b) = θ a * θ b := fun a b => by
    simp only [hθdef, map_mul]
    group
  have hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹ := fun a => by
    simp only [hθdef, map_inv]
    group
  set c : ModGL Tag.E8 L := h * z₀ with hcdef
  have hk' : ψ k = c * z₁ := by rw [hk]
  set d : ModGL Tag.E8 L := c⁻¹ * θ c with hddef
  have hd₁ : d = z₁ * (θ z₁)⁻¹ := by
    have h1 : θ c * θ z₁ = c * z₁ := by
      rw [← hθmul, ← hk']
      exact hkθ
    calc d = c⁻¹ * (θ c * θ z₁) * (θ z₁)⁻¹ := by rw [hddef]; group
      _ = c⁻¹ * (c * z₁) * (θ z₁)⁻¹ := by rw [h1]
      _ = z₁ * (θ z₁)⁻¹ := by group
  have hdQ : d ∈ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) := by
    rw [hd₁]
    exact mul_mem hz₁ (inv_mem (hθJ z₁ hz₁))
  have hcC : c ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L S₀ :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hz₀)
  have hθcC : θ c ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L S₀ := by
    rw [hcdef, hθmul]
    exact mul_mem (Subgroup.mem_sup_left (hθH h hh)) (Subgroup.mem_sup_right (hθS₀ z₀ hz₀))
  have hdC : d ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L S₀ := mul_mem (inv_mem hcC) hθcC
  have hdH : d ∈ torusGroup Tag.E8 L := by
    have hdC' : d ∈ ((torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L S₀ : Subgroup (ModGL Tag.E8 L)) :
        Set (ModGL Tag.E8 L)) := hdC
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHS₀] at hdC'
    obtain ⟨h', hh', q₀, hq₀, hdq⟩ := hdC'
    have hq₀' : q₀ = h'⁻¹ * d := by rw [← hdq]; group
    have hq₀N : q₀ ∈ torusGroup Tag.E8 L ⊔
        rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) := by
      rw [hq₀']
      exact mul_mem (Subgroup.mem_sup_left (inv_mem hh')) (Subgroup.mem_sup_right hdQ)
    have hq₀H := (hfree q₀ hq₀N fun x hx => hcommQ q₀ hq₀ x (hPQ hx)).1
    rw [← hdq]
    exact mul_mem hh' hq₀H
  obtain ⟨t, ht, hte⟩ := lang_torus_inf_rootSpan_e6 hq2 hFr hnm hwS d
    (Subgroup.mem_inf.2 ⟨hdH, hdQ⟩)
  obtain ⟨htH, htQ⟩ := Subgroup.mem_inf.1 ht
  have hte' : t⁻¹ * θ t = d := hte
  set c' : ModGL Tag.E8 L := c * t⁻¹ with hc'def
  set w₁ : ModGL Tag.E8 L := t * z₁ with hw₁def
  have hkc' : ψ k = c' * w₁ := by rw [hk', hc'def, hw₁def]; group
  have hθc' : θ c' = c' := by
    have hθc : θ c = c * d := by rw [hddef]; group
    rw [hc'def, hθmul, hθinv, hθc, ← hte']
    group
  have hw₁Q : w₁ ∈ rootSpan Tag.E8 L (parabolicRoots Tag.E8 (e6Nodes Tag.E8)) := mul_mem htQ hz₁
  have hθw₁ : θ w₁ = w₁ := by
    have h1 : θ c' * θ w₁ = c' * w₁ := by
      rw [← hθmul, ← hkc']
      exact hkθ
    rw [hθc'] at h1
    exact mul_left_cancel h1
  refine ⟨c', w₁, hkc', Subgroup.mem_inf.2 ⟨hw₁Q, hθw₁⟩, ?_⟩
  obtain ⟨hzH, -⟩ := hψE z hz
  have hzh : ψ z * h = h * ψ z := CFSG.RankThree.PartOne.KE.torusGroup_comm hzH hh
  have hzt : ψ z * t⁻¹ = t⁻¹ * ψ z :=
    CFSG.RankThree.PartOne.KE.torusGroup_comm hzH (inv_mem htH)
  have hzz₀ : ψ z * z₀ = z₀ * ψ z := hψz z₀ hz₀
  calc c' * ψ z = h * z₀ * (t⁻¹ * ψ z) := by rw [hc'def, hcdef]; group
    _ = h * z₀ * (ψ z * t⁻¹) := by rw [hzt]
    _ = h * (z₀ * ψ z) * t⁻¹ := by group
    _ = h * (ψ z * z₀) * t⁻¹ := by rw [hzz₀]
    _ = (h * ψ z) * z₀ * t⁻¹ := by group
    _ = (ψ z * h) * z₀ * t⁻¹ := by rw [hzh]
    _ = ψ z * c' := by rw [hc'def, hcdef]; group

end Native

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8NegC
