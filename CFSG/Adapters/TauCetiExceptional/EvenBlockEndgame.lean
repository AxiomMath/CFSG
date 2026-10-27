module

public import CFSG.Adapters.TauCetiExceptional.EvenTail
public import CFSG.Adapters.TauCetiExceptional.TwistedIsogeny

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell Twisted
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {L : Type} [Field L] {n m : ℕ}

@[expose] def ExclTwo
    (B : BlockCarrier τ L n m) : Prop :=
  ∀ (z : B.C) (π' : Equiv.Perm (Fin τ.rank)) (c : Fin τ.rank → L), (∀ j, c j ≠ 0) →
    (∀ i j, τ.cartan (π' i) (π' j) = τ.cartan i j) →
    (∀ j, B.mat z * B.E j * B.mat z⁻¹ = c j • B.E (π' j)) →
    (∀ j, B.mat z * B.F j * B.mat z⁻¹ = (c j)⁻¹ • B.F (π' j)) → π' = 1

variable (B : BlockCarrier τ L n m)

theorem π_mem_of_conj_two
    [IsAlgClosed L] {p : ℕ} [Fact p.Prime] [CharP L p] (hp : p = 2)
    (hτ : τ ≠ .G2) (hexcl : ExclTwo B)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (B.π z : Module.End L (RootModule τ L))) P = 0) (z : B.C)
    (E : Subfield L) [Finite E] {k : ℕ} (hE : Nat.card E = 2 ^ k) (hk : 3 ≤ k) (t : Eˣ)
    (ht : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ pairBound τ → t ^ m ≠ 1)
    (α : MulAut (adjointGroup τ E))
    (hα : ∀ x : adjointGroup τ E, baseChangeGL E.subtype (α x : ModGL τ E) =
      B.π z * baseChangeGL E.subtype (x : ModGL τ E) * (B.π z)⁻¹) :
    B.π z ∈ adjointGroup τ L := by
  subst hp
  have hHr : ∀ h ∈ B.π.range, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0 := by
    rintro _ ⟨w, rfl⟩ P hP
    exact hH w P hP
  have : CharP E 2 := Subfield.charP E 2
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  obtain ⟨c, β, hU, hV, hαβ⟩ :=
    (exceptional_ordinary_Sylow_opposition τ E 2 w₀ hw₀).2.2.2.2.2 α
  have hβ : β ∈ unipotentPairAut τ E := ⟨hU, hV⟩
  obtain ⟨π', hπ'⟩ := exists_perm_map_simple hβ
  choose prm hprm using fun i => exists_params_of_map_simple_of_charTwo (hπ' i).1 (hπ' i).2
  obtain ⟨c', hc'⟩ := B.adjointGroup_le_range
    (map_baseChangeGL_adjointGroup_le E.subtype ⟨(c : ModGL τ E), c.2, rfl⟩)
  have hαx : ∀ x : adjointGroup τ E, (α x : ModGL τ E) =
      (c : ModGL τ E) * (β x : ModGL τ E) * (c : ModGL τ E)⁻¹ := fun x => by
    rw [hαβ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
  have hz' : ∀ x : adjointGroup τ E, B.π (c'⁻¹ * z) * baseChangeGL E.subtype (x : ModGL τ E) *
      (B.π (c'⁻¹ * z))⁻¹ = baseChangeGL E.subtype (β x : ModGL τ E) := by
    intro x
    have e1 : baseChangeGL E.subtype (β x : ModGL τ E) =
        (baseChangeGL E.subtype (c : ModGL τ E))⁻¹ * baseChangeGL E.subtype (α x : ModGL τ E) *
          baseChangeGL E.subtype (c : ModGL τ E) := by
      rw [hαx x, map_mul, map_mul, map_inv]
      group
    rw [e1, hα x, map_mul, map_inv, hc']
    group
  have hu : ∀ i (c₀ : E), (c'⁻¹ * z) * B.u i c₀ * (c'⁻¹ * z)⁻¹ =
      B.u (π' i) (((prm i).1 * (prm i).2 c₀ : E) : L) := by
    intro i
    refine B.conj_eq_of_π_eq E (B.u i) (B.u (π' i)) (B.u_add i) (B.u_add (π' i)) _
      (fun c d => by rw [map_add, mul_add, Subfield.coe_add]) _ fun c₀ => ?_
    rw [map_mul, map_mul, map_inv, B.π_u, B.π_u]
    have e := hz' (adjX τ E i c₀)
    rw [(hprm i).1 c₀] at e
    simpa only [adjX, baseChangeGL_xUnit, Subfield.coe_subtype] using e
  have hv : ∀ i (c₀ : E), (c'⁻¹ * z) * B.v i c₀ * (c'⁻¹ * z)⁻¹ =
      B.v (π' i) (((((prm i).1⁻¹ : Eˣ) : E) * (prm i).2 c₀ : E) : L) := by
    intro i
    refine B.conj_eq_of_π_eq E (B.v i) (B.v (π' i)) (B.v_add i) (B.v_add (π' i)) _
      (fun c d => by rw [map_add, mul_add, Subfield.coe_add]) _ fun c₀ => ?_
    rw [map_mul, map_mul, map_inv, B.π_v, B.π_v]
    have e := hz' (adjY τ E i c₀)
    rw [(hprm i).2.1 c₀] at e
    simpa only [adjY, baseChangeGL_yUnit, Subfield.coe_subtype] using e
  have ha : ∀ i, (((prm i).1 : E) : L) ≠ 0 := fun i h0 =>
    (prm i).1.ne_zero (Subtype.ext (by rw [h0]; rfl))
  have hEq : ∀ i, B.mat (c'⁻¹ * z) * B.E i * B.mat (c'⁻¹ * z)⁻¹ =
      (((prm i).1 : E) : L) • B.E (π' i) := fun i =>
    B.conj_E_eq _ (by simpa only [OneMemClass.coe_one, map_one, mul_one] using hu i 1)
  have hFq : ∀ i, B.mat (c'⁻¹ * z) * B.F i * B.mat (c'⁻¹ * z)⁻¹ =
      (((prm i).1 : E) : L)⁻¹ • B.F (π' i) := by
    intro i
    refine B.conj_F_eq _ ?_
    have e := hv i 1
    rwa [OneMemClass.coe_one, map_one, mul_one, Units.val_inv_eq_inv_val, Subfield.coe_inv] at e
  have hdiag : ∀ i, B.mat (c'⁻¹ * z) * Matrix.diagonal (fun b => (B.wt b i : L)) *
      B.mat (c'⁻¹ * z)⁻¹ = Matrix.diagonal fun b => (B.wt b (π' i) : L) := fun i =>
    B.conj_diag_eq _ (ha i) (hEq i) (hFq i)
  have hπ1 : π' = 1 := hexcl _ π' (fun i => (((prm i).1 : E) : L)) ha
    (B.cartan_perm _ π' (fun i => (((prm i).1 : E) : L)) ha hdiag hEq) hEq hFq
  have hβ' : β ∈ rootPairAut τ E := mem_rootPairAut.2 fun i => by
    have h := hπ' i
    rw [hπ1, Equiv.Perm.one_apply] at h
    exact h
  obtain ⟨a, σ, hβx⟩ := BlockCarrier.exists_eq_diag_entrywise hβ'
  refine mem_adjointGroup_of_diag_entrywise_two hτ E hE hk σ t ht B.adjointGroup_le_range hHr
    ⟨z, rfl⟩ c a α hα fun x => ?_
  rw [hαx x, hβx x]
  simp only [mul_assoc]

theorem π_mem_adjointGroup_two
    [IsAlgClosed L] {p : ℕ} [Fact p.Prime] [CharP L p]
    [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L] (hp : p = 2) (hτ : τ ≠ .G2)
    (hexcl : ExclTwo B)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (B.π z : Module.End L (RootModule τ L))) P = 0) (z : B.C) :
    B.π z ∈ adjointGroup τ L := by
  have hHr : ∀ h ∈ B.π.range, ∀ P, VanishesOnRat τ P →
      evalMat (natMat τ L (h : Module.End L (RootModule τ L))) P = 0 := by
    rintro _ ⟨w, rfl⟩ P hP
    exact hH w P hP
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ :=
    exists_conj_mulAut_of_three_le (p := p) B.π.range B.adjointGroup_le_range hHr ⟨z, rfl⟩
  have : Finite (frobeniusFixedSubfield L p k) := finite_frobeniusFixedSubfield L p k (by omega)
  have hcard : Nat.card (frobeniusFixedSubfield L p k) = 2 ^ k := by
    rw [card_frobeniusFixedSubfield L p k (by omega), hp]
  exact π_mem_of_conj_two B hp hτ hexcl hH z _ hcard hk t ht α hα

section Twisted

variable {t : TwistTag} (B : BlockCarrier t.tag L n m) {p : ℕ} [Fact p.Prime] [IsAlgClosed L]
  [CharP L p] [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem π_comp_eq_twistHom_two
    (hp : p = 2) (hτ : t.tag ≠ .G2) (hexcl : ExclTwo B)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat t.tag P →
      evalMat (natMat t.tag L (B.π z : Module.End L (RootModule t.tag L))) P = 0)
    (F : B.C →* B.C) (Fr : L →+* L)
    (hFu : ∀ i c, F (B.u i c) = B.u (t.perm i) (Fr c))
    (hFv : ∀ i c, F (B.v i c) = B.v (t.perm i) (Fr c))
    (hFker : ∀ k, B.π k = 1 → B.π (F k) = 1) (g : B.C) :
    B.π (F g) = twistHom t L Fr (B.π g) := by
  obtain ⟨e, he, hπe⟩ :=
    B.adjointGroup_le_map_rootSubgroup (π_mem_adjointGroup_two B hp hτ hexcl hH g)
  have hk : B.π (e⁻¹ * g) = 1 := by rw [map_mul, map_inv, hπe, inv_mul_cancel]
  have hg : g = e * (e⁻¹ * g) := by group
  rw [hg, map_mul, map_mul, hFker _ hk, mul_one, B.π_comp_eq_of_mem_rootSubgroup F Fr hFu hFv he,
    map_mul, hk, mul_one]

theorem isTwistedIsogeny_two
    (hp : p = 2) (hτ : t.tag ≠ .G2) (hexcl : ExclTwo B)
    (hH : ∀ z : B.C, ∀ P, VanishesOnRat t.tag P →
      evalMat (natMat t.tag L (B.π z : Module.End L (RootModule t.tag L))) P = 0)
    (F : B.C →* B.C) (Fr : L →+* L)
    (hFu : ∀ i c, F (B.u i c) = B.u (t.perm i) (Fr c))
    (hFv : ∀ i c, F (B.v i c) = B.v (t.perm i) (Fr c))
    (hFker : ∀ k, B.π k = 1 → B.π (F k) = 1) :
    IsTwistedIsogeny t L Fr F B.π where
  mem := π_mem_adjointGroup_two B hp hτ hexcl hH
  surj _ hx := B.adjointGroup_le_range hx
  ker g hg := B.ker_center g hg
  comm := π_comp_eq_twistHom_two B hp hτ hexcl hH F Fr hFu hFv hFker

end Twisted

end CFSG.TauCetiBridge.Even
