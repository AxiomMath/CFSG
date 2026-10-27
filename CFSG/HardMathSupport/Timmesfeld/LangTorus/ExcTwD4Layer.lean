module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.RankThree.PartOne.KGD.D4Twist

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KE6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints d4Nodes)


instance instE6SubTwE6 : E6Sub TwistTag.E6.tag := instE6SubE6

section Normal

variable {L : Type} [Field L]

theorem exists_scalars_twist {a : ModGL TwistTag.E6.tag L}
    (ha : a ∈ monomialSubgroup TwistTag.E6.tag L) {j j' : Fin TwistTag.E6.tag.rank}
    (hj : weylQuotientHom TwistTag.E6.tag L ⟨a, ha⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        Pi.single j' 1) :
    ∃ s : Lˣ, ∀ c : L,
      (a * diagramMap TwistTag.E6 L) * xUnit TwistTag.E6.tag L j c *
          (a * diagramMap TwistTag.E6 L)⁻¹ = xUnit TwistTag.E6.tag L j' (s * c) ∧
        (a * diagramMap TwistTag.E6 L) * yUnit TwistTag.E6.tag L j c *
          (a * diagramMap TwistTag.E6 L)⁻¹ = yUnit TwistTag.E6.tag L j' (((s⁻¹ : Lˣ) : L) * c) := by
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartOne.KGD.exists_conj_rootSL2_eq_twist (t := TwistTag.E6) ha
    (isRoot_single TwistTag.E6.tag j)
  rw [hj] at hs
  refine ⟨s, fun c => ⟨?_, ?_⟩⟩
  · have h := hs (uSL c)
    rw [rootSL2_single_apply', rootSL2_single_apply', simpleRootSL2_uSL] at h
    rw [h]
    exact (congrArg (simpleRootSL2 TwistTag.E6.tag L j') (conjSL_sl2Upper s c)).trans
      (simpleRootSL2_uSL j' _)
  · have h := hs (vSL c)
    rw [rootSL2_single_apply', rootSL2_single_apply', simpleRootSL2_vSL] at h
    rw [h]
    exact (congrArg (simpleRootSL2 TwistTag.E6.tag L j') (conjSL_sl2Lower s c)).trans
      (simpleRootSL2_vSL j' _)

theorem exists_normalized_twist [IsAlgClosed L] {n : ModGL TwistTag.E6.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {π : Equiv.Perm (Fin TwistTag.E6.tag.rank)} (hπ : ∀ i ∈ d4Set TwistTag.E6.tag, π i ∈ d4Set _)
    (hπ' : ∀ i ∈ d4Set TwistTag.E6.tag, π.symm i ∈ d4Set _)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Set _))
    (hact : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (π j) 1 : Fin TwistTag.E6.tag.rank → ℤ)) :
    ∃ q n₁ : ModGL TwistTag.E6.tag L, q ∈ subsystemGroup TwistTag.E6.tag L (d4Set _) ∧
      n * diagramMap TwistTag.E6 L = q * n₁ ∧ ∀ j ∈ d4Set TwistTag.E6.tag, ∀ c : L,
        n₁ * xUnit TwistTag.E6.tag L j c * n₁⁻¹ = xUnit TwistTag.E6.tag L (π j) c ∧
        n₁ * yUnit TwistTag.E6.tag L j c * n₁⁻¹ = yUnit TwistTag.E6.tag L (π j) c := by
  set w := weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ with hw
  set nu := canonicalRep (coxeterSystem TwistTag.E6.tag) L u with hnu
  have hnuQ : nu ∈ subsystemGroup TwistTag.E6.tag L (d4Set _) := canonicalRep_mem_subsystemGroup hu
  have hnuM : nu ∈ monomialSubgroup TwistTag.E6.tag L := canonicalRep_mem_monomialSubgroup L u
  set a := nu⁻¹ * n with ha_def
  have haM : a ∈ monomialSubgroup TwistTag.E6.tag L := mul_mem (inv_mem hnuM) hn
  have haw : weylQuotientHom TwistTag.E6.tag L ⟨a, haM⟩ = u⁻¹ * w := by
    have e : (⟨a, haM⟩ : monomialSubgroup TwistTag.E6.tag L) = (⟨nu, hnuM⟩)⁻¹ * ⟨n, hn⟩ := rfl
    rw [e, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep u)]
  have hsc : ∀ k : Fin Tag.D4.rank, ∃ r : Lˣ, ∀ c : L,
      (a * diagramMap TwistTag.E6 L) * xUnit TwistTag.E6.tag L (π.symm (d4Id k)) c *
          (a * diagramMap TwistTag.E6 L)⁻¹ = xUnit TwistTag.E6.tag L (d4Id k) (r * c) ∧
        (a * diagramMap TwistTag.E6 L) * yUnit TwistTag.E6.tag L (π.symm (d4Id k)) c *
          (a * diagramMap TwistTag.E6 L)⁻¹ =
            yUnit TwistTag.E6.tag L (d4Id k) (((r⁻¹ : Lˣ) : L) * c) := fun k => by
    refine exists_scalars_twist haM ?_
    rw [haw, mul_smul, hact _ (hπ' _ (d4Id_mem k)), inv_smul_smul, Equiv.apply_symm_apply]
  choose r hr using hsc
  obtain ⟨t, ht⟩ := exists_d4TorusWord_scalars (τ := TwistTag.E6.tag) (L := L) (fun k => (r k)⁻¹)
  have hTQ := d4TorusWord_mem_subsystemGroup (τ := TwistTag.E6.tag) (L := L) t
  refine ⟨nu * (d4TorusWord t : ModGL TwistTag.E6.tag L)⁻¹,
    d4TorusWord t * (a * diagramMap TwistTag.E6 L), mul_mem hnuQ (inv_mem hTQ), ?_, ?_⟩
  · rw [ha_def]
    group
  · intro j hj c
    obtain ⟨k, hk⟩ := exists_d4Id_eq (hπ j hj)
    have hjk : π.symm (d4Id (τ := TwistTag.E6.tag) k) = j := by rw [hk, Equiv.symm_apply_apply]
    obtain ⟨h1x, h1y⟩ := hr k c
    rw [hjk] at h1x h1y
    obtain ⟨h2x, -⟩ := ht k (r k * c)
    obtain ⟨-, h2y⟩ := ht k (((r k)⁻¹ : Lˣ) * c)
    have e1 : (((r k)⁻¹ : Lˣ) : L) * (((r k : Lˣ) : L) * c) = c := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have e2 : (((r k)⁻¹ : Lˣ)⁻¹ : Lˣ) * (((r k)⁻¹ : Lˣ) * c) = c := by
      rw [inv_inv, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    refine ⟨?_, ?_⟩
    · calc (d4TorusWord t * (a * diagramMap TwistTag.E6 L)) * xUnit TwistTag.E6.tag L j c *
            (d4TorusWord t * (a * diagramMap TwistTag.E6 L))⁻¹
          = d4TorusWord t * ((a * diagramMap TwistTag.E6 L) * xUnit TwistTag.E6.tag L j c *
              (a * diagramMap TwistTag.E6 L)⁻¹) * (d4TorusWord t : ModGL TwistTag.E6.tag L)⁻¹ := by
            group
        _ = d4TorusWord t * xUnit TwistTag.E6.tag L (d4Id k) (r k * c) *
              (d4TorusWord t : ModGL TwistTag.E6.tag L)⁻¹ := by rw [h1x]
        _ = xUnit TwistTag.E6.tag L (d4Id k) c := by rw [h2x, e1]
        _ = xUnit TwistTag.E6.tag L (π j) c := by rw [hk]
    · calc (d4TorusWord t * (a * diagramMap TwistTag.E6 L)) * yUnit TwistTag.E6.tag L j c *
            (d4TorusWord t * (a * diagramMap TwistTag.E6 L))⁻¹
          = d4TorusWord t * ((a * diagramMap TwistTag.E6 L) * yUnit TwistTag.E6.tag L j c *
              (a * diagramMap TwistTag.E6 L)⁻¹) * (d4TorusWord t : ModGL TwistTag.E6.tag L)⁻¹ := by
            group
        _ = d4TorusWord t * yUnit TwistTag.E6.tag L (d4Id k) (((r k)⁻¹ : Lˣ) * c) *
              (d4TorusWord t : ModGL TwistTag.E6.tag L)⁻¹ := by rw [h1y]
        _ = yUnit TwistTag.E6.tag L (d4Id k) c := by rw [h2y, e2]
        _ = yUnit TwistTag.E6.tag L (π j) c := by rw [hk]

theorem exists_conj_twistedFixed_twist [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {π : Equiv.Perm (Fin TwistTag.E6.tag.rank)} (hπ : ∀ i ∈ d4Set TwistTag.E6.tag, π i ∈ d4Set _)
    (hπ' : ∀ i ∈ d4Set TwistTag.E6.tag, π.symm i ∈ d4Set _)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Set _))
    (hact : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (π j) 1 : Fin TwistTag.E6.tag.rank → ℤ)) :
    ∃ n₁ h : ModGL TwistTag.E6.tag L, h ∈ subsystemGroup TwistTag.E6.tag L (d4Set _) ∧
      (∀ j ∈ d4Set TwistTag.E6.tag, ∀ c : L,
        n₁ * xUnit TwistTag.E6.tag L j c * n₁⁻¹ = xUnit TwistTag.E6.tag L (π j) c ∧
        n₁ * yUnit TwistTag.E6.tag L j c * n₁⁻¹ = yUnit TwistTag.E6.tag L (π j) c) ∧
      ∀ g : ModGL TwistTag.E6.tag L,
        (n * diagramMap TwistTag.E6 L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g *
            (n * diagramMap TwistTag.E6 L)⁻¹ = g ↔
          n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
            h * g * h⁻¹ := by
  obtain ⟨q, n₁, hq, hnq, hgen⟩ := exists_normalized_twist hn hπ hπ' hu hact
  have hA := mem_normalizer_subsystemGroup_of_conj hπ hπ' hgen
  obtain ⟨h, hh, hlang⟩ := ((supported_native_affine_realization_and_Lang TwistTag.E6.tag L
    (d4Set _)).2 ℓ f hf n₁ hA).2.2.2 q hq
  refine ⟨n₁, h, hh, hgen, fun g => ?_⟩
  have e1 : (n * diagramMap TwistTag.E6 L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g *
      (n * diagramMap TwistTag.E6 L)⁻¹ = q * frobTwistGL TwistTag.E6.tag L ℓ f n₁ g * q⁻¹ := by
    rw [hnq, frobTwistGL_apply]
    simp only [entrywiseFrobGL]
    group
  rw [e1, hlang g]
  change _ ↔ frobTwistGL TwistTag.E6.tag L ℓ f n₁ (h * g * h⁻¹) = h * g * h⁻¹
  generalize frobTwistGL TwistTag.E6.tag L ℓ f n₁ (h * g * h⁻¹) = X
  constructor
  · intro e
    rw [← e]
    group
  · intro e
    rw [e]
    group

end Normal

section Layer

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem twisted_triality_layer (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    Finite ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    obtain ⟨hfin, hqs, -, -⟩ := layer_of_standard hf hstd hh hlang rfl
    exact ⟨hfin, hqs⟩
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    obtain ⟨hfin, hqs, -, -⟩ := layer_of_standard hf hstd hh hlang rfl
    exact ⟨hfin, hqs⟩

@[expose] def e6Graph : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

@[expose] noncomputable def e6Diagram (L : Type) [Field L] : ModGL Tag.E6 L :=
  diagramMap TwistTag.E6 L

theorem twisted_triality_layer_E6 (hf : 1 ≤ f) {a b c : Fin Tag.E6.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes _),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    Finite ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes _)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
  twisted_triality_layer hf hab hbc hac ha hb hc hn hu hact

end Layer

end CFSG.HardMathSupport.Timmesfeld.LangTorus
