module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcTwBad
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedStd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcTwD4Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints D4TrialityLayer d4Nodes)


section Layer

variable {τ : Tag} {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem bad27_layer_swap (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) {a b k c : Fin τ.rank}
    (ha : a ∈ d4Set τ) (hb : b ∈ d4Set τ) (hk : k ∈ d4Set τ) (hc : c ∈ d4Set τ)
    (hab : τ.cartan a b = 0) (hak : τ.cartan a k = 0) (hbk : τ.cartan b k = 0)
    (hca : τ.cartan c a = -1) (hcb : τ.cartan c b = -1) (hck : τ.cartan c k = -1)
    (hπa : π a = b) (hπb : π b = a) (hπk : π k = k) (hπc : π c = c) :
    Bad27 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hB := bad27_swap hτ hf (d4Cfg_single hτ hab hak hbk hca hcb hck) (F₁ := stdF n₁ f)
    (stdF_a hgen ha hπa) (stdF_a hgen hb hπb) (stdF_a hgen hk hπk) (stdF_a hgen hc hπc)
  exact hB.mono (inf_le_inf (cfgGroup_single_le ha hb hk hc) (fixSub_stdF n₁ f).le)

theorem bad27_layer_cycle (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) {a b k c : Fin τ.rank}
    (ha : a ∈ d4Set τ) (hb : b ∈ d4Set τ) (hk : k ∈ d4Set τ) (hc : c ∈ d4Set τ)
    (hab : τ.cartan a b = 0) (hak : τ.cartan a k = 0) (hbk : τ.cartan b k = 0)
    (hca : τ.cartan c a = -1) (hcb : τ.cartan c b = -1) (hck : τ.cartan c k = -1)
    (hπa : π a = b) (hπb : π b = k) (hπk : π k = a) (hπc : π c = c) :
    Bad27 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hB := bad27_cycle hτ hf (d4Cfg_single hτ hab hak hbk hca hcb hck) (F₁ := stdF n₁ f)
    (stdF_a hgen ha hπa) (stdF_a hgen hb hπb) (stdF_a hgen hk hπk) (stdF_a hgen hc hπc)
  exact hB.mono (inf_le_inf (cfgGroup_single_le ha hb hk hc) (fixSub_stdF n₁ f).le)

end Layer

section D4Std

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem bad27_d4_std (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)} (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1)
    (hgen : ∀ j ∈ d4Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) :
    Bad27 (subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n₁ (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have m1 : e6Idx (τ := τ) 1 ∈ d4Set τ := e6Idx_mem_d4Set' 1 (by decide) (by decide)
  have m2 : e6Idx (τ := τ) 2 ∈ d4Set τ := e6Idx_mem_d4Set' 2 (by decide) (by decide)
  have m3 : e6Idx (τ := τ) 3 ∈ d4Set τ := e6Idx_mem_d4Set' 3 (by decide) (by decide)
  have m4 : e6Idx (τ := τ) 4 ∈ d4Set τ := e6Idx_mem_d4Set' 4 (by decide) (by decide)
  have n12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have n14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have n24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have n13 : e6Idx (τ := τ) 1 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have n23 : e6Idx (τ := τ) 2 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have n43 : e6Idx (τ := τ) 4 ≠ e6Idx 3 := e6Idx_ne (by decide)
  have c12 : τ.cartan (e6Idx 1) (e6Idx 2) = 0 := by rw [cartan_e6Idx]; decide
  have c21 : τ.cartan (e6Idx 2) (e6Idx 1) = 0 := by rw [cartan_e6Idx]; decide
  have c14 : τ.cartan (e6Idx 1) (e6Idx 4) = 0 := by rw [cartan_e6Idx]; decide
  have c41 : τ.cartan (e6Idx 4) (e6Idx 1) = 0 := by rw [cartan_e6Idx]; decide
  have c24 : τ.cartan (e6Idx 2) (e6Idx 4) = 0 := by rw [cartan_e6Idx]; decide
  have c42 : τ.cartan (e6Idx 4) (e6Idx 2) = 0 := by rw [cartan_e6Idx]; decide
  have c31 : τ.cartan (e6Idx 3) (e6Idx 1) = -1 := by rw [cartan_e6Idx]; decide
  have c32 : τ.cartan (e6Idx 3) (e6Idx 2) = -1 := by rw [cartan_e6Idx]; decide
  have c34 : τ.cartan (e6Idx 3) (e6Idx 4) = -1 := by rw [cartan_e6Idx]; decide
  rcases hleaf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hπ1
  · exact bad27_layer_swap hτ' hf hgen m1 m2 m4 m3 c12 c14 c24 c31 c32 c34
      (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _)
      (Equiv.swap_apply_of_ne_of_ne n14.symm n24.symm)
      (Equiv.swap_apply_of_ne_of_ne n13.symm n23.symm)
  · exact bad27_layer_swap hτ' hf hgen m1 m4 m2 m3 c14 c12 c42 c31 c34 c32
      (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _)
      (Equiv.swap_apply_of_ne_of_ne n12.symm n24)
      (Equiv.swap_apply_of_ne_of_ne n13.symm n43.symm)
  · exact bad27_layer_swap hτ' hf hgen m2 m4 m1 m3 c24 c21 c41 c32 c34 c31
      (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _)
      (Equiv.swap_apply_of_ne_of_ne n12 n14)
      (Equiv.swap_apply_of_ne_of_ne n23.symm n43.symm)
  · obtain ⟨e1, e2, e3⟩ := formPerm_three_vals n12 n24 n14
    refine bad27_layer_cycle hτ' hf hgen m1 m2 m4 m3 c12 c14 c24 c31 c32 c34 e1 e2 e3 ?_
    refine List.formPerm_apply_of_notMem ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨n13.symm, n23.symm, n43.symm⟩
  · obtain ⟨e1, e2, e3⟩ := formPerm_three_vals n14 n24.symm n12
    refine bad27_layer_cycle hτ' hf hgen m1 m4 m2 m3 c14 c12 c42 c31 c34 c32 e1 e2 e3 ?_
    refine List.formPerm_apply_of_notMem ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨n13.symm, n43.symm, n23.symm⟩

end D4Std

section Transport

variable {τ : Tag} {L : Type} [Field L]

theorem bad27_of_lang {Q : Subgroup (ModGL τ L)} {Φ : ModGL τ L →* ModGL τ L}
    {n n₁ h : ModGL τ L} (hh : h ∈ Q)
    (hlang : ∀ g : ModGL τ L, n * Φ g * n⁻¹ = g ↔ n₁ * Φ (h * g * h⁻¹) * n₁⁻¹ = h * g * h⁻¹)
    (hB : Bad27 (Q ⊓ twistedFixedPoints n₁ Φ)) : Bad27 (Q ⊓ twistedFixedPoints n Φ) := by
  refine (hB.map_conj h⁻¹).mono ?_
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨hsQ, hsF⟩ := Subgroup.mem_inf.1 hs
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hh) hsQ) hh, ?_⟩
  rw [mem_twistedFixedPoints, hlang]
  have e : h * (h⁻¹ * s * h) * h⁻¹ = s := by group
  rw [e]
  exact (mem_twistedFixedPoints).1 hsF

end Transport

section QB

@[expose] def QB27 {G : Type} [Group G] (P : Subgroup G) : Prop :=
  CFSG.IsQuasisimple ↥P ∧ Bad27 P

theorem QB27.map_conj {G : Type} [Group G] {P : Subgroup G} (h : QB27 P) (g : G) :
    QB27 (P.map (MulAut.conj g).toMonoidHom) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (P.equivMapOfInjective _ (MulAut.conj g).injective) h.1, h.2.map_conj g⟩

end QB

section Layer6

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem bad27_d4_layer (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) {π : Equiv.Perm (Fin τ.rank)} (hleaf : IsD4LeafPerm π)
    (hπ1 : π ≠ 1) {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) :
    Bad27 (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ := fun i hi => hleaf.mem_d4Set hi
  have hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ := fun i hi => hleaf.inv.mem_d4Set hi
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ •
      (Pi.single j 1 : Fin τ.rank → ℤ) = u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed (ℓ := 2) hf hn hπ hπ' hu hact'
  have hd4 : d4Nodes τ = d4Set τ := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  exact bad27_of_lang hh hlang (bad27_d4_std hτ hf hleaf hπ1 hgen)

end Layer6

section LayerTw

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem bad27_d4_layer_tw {f : ℕ} (hf : 1 ≤ f) {n : ModGL TwistTag.E6.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag L) {π : Equiv.Perm (Fin TwistTag.E6.tag.rank)}
    (hleaf : IsD4LeafPerm π) (hπ1 : π ≠ 1) {u : WeylGroup TwistTag.E6.tag}
    (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice π α) :
    Bad27 (rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
      twistedFixedPoints (n * diagramMap TwistTag.E6 L)
        (Units.map (entrywiseHom (iterateFrobenius L 2 f)))) := by
  have hπ : ∀ i ∈ d4Set TwistTag.E6.tag, π i ∈ d4Set TwistTag.E6.tag :=
    fun i hi => hleaf.mem_d4Set hi
  have hπ' : ∀ i ∈ d4Set TwistTag.E6.tag, π.symm i ∈ d4Set TwistTag.E6.tag :=
    fun i hi => hleaf.inv.mem_d4Set hi
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (π j) 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun j hj => by
    have := hact _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single π] at this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist (ℓ := 2) hf hn hπ hπ' hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  exact bad27_of_lang hh hlang
    (bad27_d4_std (τ := TwistTag.E6.tag) (Or.inl rfl) hf hleaf hπ1 hgen)

end LayerTw

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
