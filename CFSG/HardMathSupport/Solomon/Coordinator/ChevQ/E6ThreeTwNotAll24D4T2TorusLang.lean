module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KE (d4Nodes)

section Abstract

variable {G : Type*} [Group G]

theorem d4t2tl_telescope (θ : G →* G) {S : Subgroup G}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hθ : ∀ x ∈ S, θ x ∈ S) {t₀ : G} (ht₀ : t₀ ∈ S)
    (j : ℕ) : ∃ P ∈ S, P⁻¹ * θ P = θ^[j] t₀ * t₀⁻¹ := by
  have hiter : ∀ j, θ^[j] t₀ ∈ S := by
    intro j
    induction j with
    | zero => exact ht₀
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hθ _ ih
  induction j with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ j ih =>
    obtain ⟨P, hP, hPe⟩ := ih
    refine ⟨P * θ^[j] t₀, mul_mem hP (hiter j), ?_⟩
    have hcm : t₀⁻¹ * θ^[j + 1] t₀ = θ^[j + 1] t₀ * t₀⁻¹ := by
      have h := hcomm _ (hiter (j + 1)) _ ht₀
      calc t₀⁻¹ * θ^[j + 1] t₀ = t₀⁻¹ * (θ^[j + 1] t₀ * t₀) * t₀⁻¹ := by group
        _ = t₀⁻¹ * (t₀ * θ^[j + 1] t₀) * t₀⁻¹ := by rw [h]
        _ = θ^[j + 1] t₀ * t₀⁻¹ := by group
    calc (P * θ^[j] t₀)⁻¹ * θ (P * θ^[j] t₀)
        = (θ^[j] t₀)⁻¹ * (P⁻¹ * θ P) * θ (θ^[j] t₀) := by rw [map_mul]; group
      _ = (θ^[j] t₀)⁻¹ * (θ^[j] t₀ * t₀⁻¹) * θ^[j + 1] t₀ := by
          rw [hPe, Function.iterate_succ_apply']
      _ = t₀⁻¹ * θ^[j + 1] t₀ := by group
      _ = θ^[j + 1] t₀ * t₀⁻¹ := hcm

theorem d4t2tl_lang_of_pow (θ : G →* G) {S : Subgroup G}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hθ : ∀ x ∈ S, θ x ∈ S) {k N : ℕ}
    (hpow : ∀ x ∈ S, θ^[k] x = x ^ (N + 1)) (hdiv : ∀ s ∈ S, ∃ t ∈ S, t ^ N = s) :
    ∀ s ∈ S, ∃ t ∈ S, t⁻¹ * θ t = s := by
  intro s hs
  obtain ⟨t₀, ht₀, rfl⟩ := hdiv s hs
  obtain ⟨P, hP, hPe⟩ := d4t2tl_telescope θ hcomm hθ ht₀ k
  exact ⟨P, hP, by rw [hPe, hpow t₀ ht₀, pow_succ, mul_inv_cancel_right]⟩

end Abstract

section Pow

set_option linter.unusedSectionVars false


theorem d4t2tl_perm_symm : e6Graph.symm = e6Graph := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.symm_apply_eq]
  exact (congrArg (fun p : Equiv.Perm (Fin Tag.E6.rank) => p i) e6Graph_mul_self).symm

@[expose] noncomputable def d4t2tlPsi (v : WeylGroup Tag.E6) :
    (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ) :=
  fun x => permLattice e6Graph.symm (v⁻¹ • x)

theorem d4t2tl_psi_sq (v : WeylGroup Tag.E6) (u : Fin Tag.E6.rank → ℤ) :
    (d4t2tlPsi v)^[2] u = (e6WeylTwist v⁻¹ * v⁻¹) • u := by
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ,
      permLattice e6Graph (permLattice e6Graph x) = x := fun x => by
    rw [← permLattice_mul, e6Graph_mul_self]
    rfl
  change permLattice e6Graph.symm (v⁻¹ • permLattice e6Graph.symm (v⁻¹ • u)) = _
  rw [d4t2tl_perm_symm, ← e6WeylTwist_smul, hσσ, mul_smul]

theorem d4t2tl_psi_iterate (v : WeylGroup Tag.E6) (u : Fin Tag.E6.rank → ℤ) :
    (d4t2tlPsi v)^[2 * Nat.card (WeylGroup Tag.E6)] u = u := by
  rw [Function.iterate_mul]
  have h2 : (d4t2tlPsi v)^[2] = fun u => (e6WeylTwist v⁻¹ * v⁻¹) • u :=
    funext (d4t2tl_psi_sq v)
  rw [h2, smul_iterate, pow_card_eq_one']
  exact one_smul _ u

variable {L : Type} [Field L]

@[expose] noncomputable def d4t2tlTuple (Fr : L →+* L) (v : WeylGroup Tag.E6)
    (b : Fin Tag.E6.rank → Lˣ) : Fin Tag.E6.rank → Lˣ :=
  weylTuple v fun i => Units.map Fr.toMonoidHom (b (e6Graph.symm i))

theorem d4t2tl_rootChar_tuple (Fr : L →+* L) (v : WeylGroup Tag.E6)
    (b : Fin Tag.E6.rank → Lˣ) (u : Fin Tag.E6.rank → ℤ) :
    rootChar (d4t2tlTuple Fr v b) u =
      Units.map Fr.toMonoidHom (rootChar b (d4t2tlPsi v u)) := by
  unfold d4t2tlTuple d4t2tlPsi
  rw [rootChar_weylTuple, rootChar_map_tuple (τ := Tag.E6) Fr (fun i => b (e6Graph.symm i)),
    rootChar_permLattice b e6Graph.symm]

theorem d4t2tl_rootChar_iterate (Fr : L →+* L) (v : WeylGroup Tag.E6)
    (a : Fin Tag.E6.rank → Lˣ) (k : ℕ) :
    ∀ u : Fin Tag.E6.rank → ℤ, rootChar ((d4t2tlTuple Fr v)^[k] a) u =
      (Units.map Fr.toMonoidHom)^[k] (rootChar a ((d4t2tlPsi v)^[k] u)) := by
  induction k with
  | zero => intro u; rfl
  | succ k ih =>
    intro u
    rw [Function.iterate_succ_apply', d4t2tl_rootChar_tuple, ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply]

theorem d4t2tl_unitsMap_iterate {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (k : ℕ)
    (c : Lˣ) : (Units.map Fr.toMonoidHom)^[k] c = c ^ (q ^ k) := by
  have h1 : ∀ x : Lˣ, Units.map Fr.toMonoidHom x = x ^ q := fun x =>
    Units.ext (by simp [hFr])
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, h1, ← pow_mul, pow_succ]

theorem d4t2tl_tuple_iterate {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup Tag.E6) (a : Fin Tag.E6.rank → Lˣ) :
    (d4t2tlTuple Fr v)^[2 * Nat.card (WeylGroup Tag.E6)] a =
      a ^ (q ^ (2 * Nat.card (WeylGroup Tag.E6))) := by
  funext i
  have h := d4t2tl_rootChar_iterate Fr v a (2 * Nat.card (WeylGroup Tag.E6)) (Pi.single i 1)
  rw [d4t2tl_psi_iterate, d4t2tl_unitsMap_iterate hFr, CTTorus.rootChar_single,
    CTTorus.rootChar_single] at h
  exact h

theorem d4t2tl_iterate_torus {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup Tag.E6) (θ : ModGL Tag.E6 L →* ModGL Tag.E6 L)
    (hθ : ∀ b : Fin Tag.E6.rank → Lˣ,
      θ (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 (d4t2tlTuple Fr v b))
    {x : ModGL Tag.E6 L} (hx : x ∈ torusGroup Tag.E6 L) :
    θ^[2 * Nat.card (WeylGroup Tag.E6)] x = x ^ (q ^ (2 * Nat.card (WeylGroup Tag.E6))) := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have key : ∀ k : ℕ, θ^[k] (rootDiagUnit Tag.E6 a) =
      rootDiagUnit Tag.E6 ((d4t2tlTuple Fr v)^[k] a) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hθ, Function.iterate_succ_apply']
  rw [key, d4t2tl_tuple_iterate hFr]
  exact (map_pow (rootDiagUnitHom Tag.E6 L) a _)

theorem d4t2tl_twFrob_tuple (Fr : L →+* L) (v : WeylGroup Tag.E6)
    (b : Fin Tag.E6.rank → Lˣ) :
    (twFrob TwistTag.E6 (canonicalRep (coxeterSystem Tag.E6) L v) Fr) (rootDiagUnit Tag.E6 b) =
      rootDiagUnit Tag.E6 (d4t2tlTuple Fr v b) :=
  twFrob_rootDiagUnit TwistTag.E6 Fr v b

end Pow

section Div

set_option linter.unusedSectionVars false


variable {L : Type} [Field L] [IsAlgClosed L]

theorem d4t2tl_div_supportedTorus (J : Set (Fin Tag.E6.rank)) {N : ℕ} (hN : 0 < N) :
    ∀ s ∈ supportedTorus Tag.E6 L J, ∃ t ∈ supportedTorus Tag.E6 L J, t ^ N = s := by
  rintro _ ⟨a, rfl⟩
  have hroot : ∀ j, ∃ u : Lˣ, u ^ N = a j := fun j => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((a j : Lˣ) : L) hN
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hx
      exact (a j).ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
  choose u hu using hroot
  refine ⟨supportedTorusHom Tag.E6 L J u, supportedTorusHom_mem J u, ?_⟩
  rw [← map_pow]
  congr 1
  funext j
  exact hu j

theorem d4t2tl_div_torus_inf_rootSpan (v : WeylGroup Tag.E6) {N : ℕ} (hN : 0 < N) :
    ∀ s ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L
        ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)),
      ∃ t ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L
        ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)), t ^ N = s := by
  intro s hs
  set n := canonicalRep (coxeterSystem Tag.E6) L v with hn
  have hnT : n ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer v
  have hspan := map_conj_rootSpan (L := L) v
    (S := parabolicRoots Tag.E6 (d4Nodes Tag.E6)) (fun γ hγ => hγ.1)
  have hs2 : s ∈ (rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6))).map
      (MulAut.conj n).toMonoidHom := by
    rw [hspan]
    exact hs.2
  obtain ⟨s', hs'U, hs's⟩ := hs2
  have hs'e : s' = n⁻¹ * s * n := by
    rw [← hs's]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hs'H : s' ∈ torusGroup Tag.E6 L := by
    rw [hs'e]
    refine ((Subgroup.mem_normalizer_iff.1 hnT (n⁻¹ * s * n)).2 ?_)
    rw [show n * (n⁻¹ * s * n) * n⁻¹ = s by group]
    exact hs.1
  have hmem : s' ∈ subsystemGroup Tag.E6 L (d4Nodes Tag.E6) ⊓ torusGroup Tag.E6 L :=
    ⟨by rw [subsystemGroup_eq_rootSpan]; exact hs'U, hs'H⟩
  rw [subsystemGroup_inf_torusGroup_eq_supportedTorus] at hmem
  obtain ⟨t', ht'J, ht'N⟩ := d4t2tl_div_supportedTorus (L := L) (d4Nodes Tag.E6) hN s' hmem
  have ht'U : t' ∈ rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
    rw [← subsystemGroup_eq_rootSpan]
    exact supportedTorus_le_subsystemGroup _ ht'J
  have ht'H : t' ∈ torusGroup Tag.E6 L := supportedTorus_le_torusGroup _ ht'J
  refine ⟨n * t' * n⁻¹, ⟨(Subgroup.mem_normalizer_iff.1 hnT t').1 ht'H, ?_⟩, ?_⟩
  · rw [← hspan]
    exact ⟨t', ht'U, rfl⟩
  · rw [conj_pow, ht'N, hs'e]
    group

end Div

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
