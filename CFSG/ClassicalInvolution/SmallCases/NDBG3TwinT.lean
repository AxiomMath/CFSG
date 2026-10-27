module

public import CFSG.ClassicalInvolution.SmallCases.NDBG3Outer
public import CFSG.ClassicalInvolution.ModelFacts.Orth15VertexTwin

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77.FrameVertex


theorem twinInnerAlpha_g2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) :
    TwinInnerAlpha p e .G2 0 := by
  intro H _ _ ψ R R' x x' hpair u hun hu hu2 hu1 hux
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  have hadm : Assembly.LowTwoRank.StatedLieAdmissible .G2 0 p e := ⟨Fact.out, he, rfl, by omega⟩
  obtain ⟨-, hZ, -, -⟩ := T3CII.T3U.g2d4_model_facts (p := p) (f := e) hp2 hq (Or.inl rfl)
    trivial hadm (Or.inl rfl)
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).1 (le_bot_iff.1 (hpair.ker.trans hZ.le))
  have hxx : x = x' := hinj hpair.same
  rw [← Subgroup.map_sup] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  have hcent : R ⊔ R' ≤ Subgroup.centralizer ({x} : Set _) := by
    refine sup_le (fun r hr => ?_) fun r hr => ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hxx]
      exact hpair.comm r hr x' hpair.hx'
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hpair.comm x hpair.hx r hr).symm
  have hxs : x * s = s * x := (Subgroup.mem_centralizer_singleton_iff.mp (hcent hs)).symm
  have h1 : toInducedAutOn ψ.range ⟨ψ s, hun⟩ = innerHom ψ s := rfl
  have h2 : toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ = innerHom ψ x := rfl
  have hx1 : ψ x ≠ 1 := fun h => hpair.hx1 (hinj (h.trans (map_one ψ).symm))
  have hx2 : ψ x * ψ x = 1 := by rw [← map_mul, hpair.hx2, map_one]
  have hcomm : ψ s * ψ x = ψ x * ψ s := by rw [← map_mul, ← map_mul, hxs]
  rw [h1, h2, ← inducedImage_closure_pair]
  refine T3CII.T3U.alphaOf_inducedImage_eq_bot_of_g2d4 (p := p) (f := e) hp2 hq (Or.inl rfl)
    trivial hadm (Or.inl rfl) ψ hpair.ker
    (Balance.Bootstrap.card_closure_pair_eq_four hu2 hx2 hu1 hx1 hux hcomm) (fun a ha => ?_)
    ((Subgroup.closure_le _).2 ?_)
  · refine Balance.Bootstrap.mul_self_eq_one_of_mem_closure ?_ ?_ ha
    · rintro z (rfl | rfl)
      · exact hu2
      · exact hx2
    · rintro z (rfl | rfl) w (rfl | rfl)
      · rfl
      · exact hcomm
      · exact hcomm.symm
      · rfl
  · rintro _ (rfl | rfl)
    · exact ⟨s, rfl⟩
    · exact ⟨x, rfl⟩

section Component

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinPair_of_twin_g2 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmega p f Φ)
    (D : OmegaLie p f Φ) (i : Fin D.card) (hG2 : D.tag i = .G2)
    {R R' : Subgroup (D.model i).K} (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hR' : R' ∈ fundamentalSubgroups (D.tag i) (D.model i).D) (hK : R.map (D.hom i) ∈ Φ)
    (hK'Φ : R'.map (D.hom i) ∈ Φ) {z : X} (hzK : IsUniqueInvolution (R.map (D.hom i)) z)
    (hzK' : IsUniqueInvolution (R'.map (D.hom i)) z)
    (hne : R.map (D.hom i) ≠ R'.map (D.hom i)) :
    R ≠ R' ∧ Commutes R R' ∧
      ∃ x ∈ R, ∃ x' ∈ R', x * x = 1 ∧ x ≠ 1 ∧ x' * x' = 1 ∧ x' ≠ 1 ∧ D.hom i x = z ∧
        D.hom i x' = z := by
  have hnA1 : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := fun h => by
    rw [hG2] at h
    exact absurd h.1 (by decide)
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => by
    rw [hG2] at h
    exact absurd h.1 (by decide)
  have hperf := Gaps.fundPerfect_modelUniv hp (D.isFundTag i) (D.admissible i) (by
    rw [hexp]
    omega)
  have hRp : R ≤ ⁅R, R⁆ := hperf R hR
  have hker := D.ker_le_center i
  have hex : oddCoreOf (R.map (D.hom i)) = ⊥ := oddCoreOf_eq_bot_of_exact hΦ.exact hK
  have hneR : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨hcomm, x, hx, x', hx', hψx, hψx', hx'1, -⟩ := ih8_twin_data hΦ.toMod hker hRp hK hK'Φ
    hne hzK hzK' hex
  have hinj := D.injOn_fund i hnA1 hR
  have hinj' := D.injOn_fund i hnA1 hR'
  have hx2 : x * x = 1 := hinj _ (R.mul_mem hx hx) (by rw [map_mul, hψx, hzK.sq])
  have hx'2 : x' * x' = 1 := hinj' _ (R'.mul_mem hx' hx') (by rw [map_mul, hψx', hzK'.sq])
  have hx1 : x ≠ 1 := fun h => hzK.ne_one (by rw [← hψx, h, map_one])
  exact ⟨hneR, hcomm, x, hx, x', hx', hx2, hx1, hx'2, hx'1, hψx, hψx'⟩

end Component

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem vertexTwin_g2 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    {M M' : Subgroup G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hmov : MovedByAll B c
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hG2 : D.tag j = .G2) :
    ∃ (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) (R R' : Subgroup (compModel D j).K)
      (x x' : (compModel D j).K),
      TwinPairOn (D.tag j) (compModel D j)
        (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j) R R' x x' ∧
      R.map (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j) =
        modOdd c (exactCore c M) ∧
      R'.map (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j) =
        modOdd c (exactCore c M') ∧
      secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j x =
        oddQuotMk c ⟨b, hbC⟩ := by
  classical
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  have hmem : ∀ N ∈ tqMembers Ω c, exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    fun N hN => ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hbB
  have hM'j := vertexTwin_mem hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hM' hM'b D j hmov
  obtain ⟨R, hR, hRM⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M hM) hMj
  obtain ⟨R', hR', hRM'⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M' hM') hM'j
  obtain ⟨hbY, hK, hK', hneK, hzK, hzK'⟩ := secFam_twin hp hq hΩ hc2 hM hM' hMb hM'b hne
  have hRφ := map_hom_eq_modOddIn hs' D j (hmem M hM) hRM
  have hR'φ := map_hom_eq_modOddIn hs' D j (hmem M' hM') hRM'
  have hΦ : HypOmega p f (secFam Ω c) := hypOmega_secFam hp hq hΩ hc2 hs' D
  have hKR : R.map (D.hom j) ∈ secFam Ω c := by rw [hRφ]; exact hK
  have hK'R' : R'.map (D.hom j) ∈ secFam Ω c := by rw [hR'φ]; exact hK'
  have hzKR : IsUniqueInvolution (R.map (D.hom j)) (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (exactFamily Ω c) {c})) ⟨b, hbY⟩) := by rw [hRφ]; exact hzK
  have hzK'R' : IsUniqueInvolution (R'.map (D.hom j)) (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(centralizingLayer (exactFamily Ω c) {c})) ⟨b, hbY⟩) := by
    rw [hR'φ]; exact hzK'
  have hneR : R.map (D.hom j) ≠ R'.map (D.hom j) := by rw [hRφ, hR'φ]; exact hneK
  obtain ⟨hneR, hcomm, x, hx, x', hx', hx2, hx1, hx'2, hx'1, hψx, hψx'⟩ :=
    twinPair_of_twin_g2 hp hq hΦ (LieSystemData.toOmegaLie D (omegaGen_secFam hs')) j hG2
      (R := R) (R' := R') hR hR' hKR hK'R' hzKR hzK'R' hneR
  have hψb : ∀ w : (compModel D j).K, D.hom j w = QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (exactFamily Ω c) {c})) ⟨b, hbY⟩ →
      secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j w =
        oddQuotMk c ⟨b, hbC⟩ := by
    intro w hw
    show sectionQuotientHom (normalizesLayer_exactFamily hΩ.conjInvariant) (D.hom j w) = _
    rw [hw]
    rfl
  exact ⟨hbC, R, R', x, x',
    { ker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j
      mem := hR
      mem' := hR'
      ne := hneR
      comm := hcomm
      hx := hx
      hx2 := hx2
      hx1 := hx1
      hx' := hx'
      hx'2 := hx'2
      hx'1 := hx'1
      same := (hψb x hψx).trans (hψb x' hψx').symm },
    hRM, hRM', hψb x hψx⟩

end Vertex

end CFSG.ClassicalInvolution.NDB.NDBG3
