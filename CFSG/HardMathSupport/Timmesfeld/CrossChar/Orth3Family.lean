module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthResidual
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Plane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Gen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthFamilyD

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank

section Model

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem isLocallyBalancedAbs_projOrth3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (hrig : ∀ A : Subgroup (ProjOrthDerived Q), IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∀ g : MulAut (ProjOrthDerived Q),
        (∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, g n = n) → g = 1)
    (hO : OutStructure.OutPChain p (ProjOrthDerived Q)) :
    IsLocallyBalancedAbs p 3 (ProjOrthDerived Q) := by
  intro D hD hcard H hH hDH
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj := conj_injective_of_center_eq_bot_orth hcenter
  obtain ⟨P, hPD, hPI, hPc⟩ := K133C.exists_inner_plane hp hO
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hD) hcard
  set E₁ : Subgroup (ProjOrthDerived Q) :=
    P.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) with hE₁
  have hmap : E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = P :=
    Subgroup.map_comap_eq_self hPI
  have hE₁el : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h2 : MulAut.conj (a : ProjOrthDerived Q) * MulAut.conj (b : ProjOrthDerived Q) =
          MulAut.conj (b : ProjOrthDerived Q) * MulAut.conj (a : ProjOrthDerived Q) :=
        congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hPD a.2⟩ ⟨_, hPD b.2⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h2
    · rw [map_pow, map_one]
      exact hD.2 _ (hPD hx)
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hPc]
  have hbot := localDeltaIn_eq_bot_projOrth3 hQ hT hp hp2 hK4 hpl E₁ hE₁el hE₁c
    (hrig E₁ hE₁el hE₁c) hH
  rw [hmap] at hbot
  exact le_bot_iff.1 ((localDeltaIn_antitone H hPD).trans hbot.le)


end Model

section B

@[expose] def regimeBOrth3Split (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r ∧ p = 3 ∧
    3 ∣ q.card - 1

open CFSG.RankThree.PartTwo.Census CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.KCOrthogonal in
theorem crossCharFamAt_B_orth3_split : CrossCharFamAt .B regimeBOrth3Split := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hq2, hr, rfl, hpq3⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.B r q, hv⟩ r q (Or.inl rfl)
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hpl : 3 ≠ ringChar F := by rw [hring]; exact hpq
  have h2 : (2 : F) ≠ 0 := by
    have : CharP F q.p := ringChar.of_eq hring
    intro h
    have : q.p ∣ 2 := (CharP.cast_eq_zero_iff F q.p 2).mp (by exact_mod_cast h)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard]
    have h1 : q.p ≤ q.p ^ q.exponent := Nat.le_self_pow q.exponent_pos.ne' _
    have h5 := q.prime_p.two_le
    have : q.p ≠ 3 := fun h => hpq h.symm
    omega
  have hpqF : 3 ∣ Nat.card F - 1 := by
    have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    rw [hcard, ← hqc]
    exact hpq3
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (n := r) (K := F) h2 hr
  let e₁ := Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq2 hr
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadOdd r F)
  let e : Cat ⟨.B r q, hv⟩ ≃* ProjOrthDerived (quadOdd r F) := e₁.trans e₂
  have hO : OutStructure.OutPChain 3 (ProjOrthDerived (quadOdd r F)) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_POmegaOdd_of_ne_two hp hp2
      (statedClassicalModel_typeB_odd r q hv hq2 hr e.symm)).toChain
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_projOrth3 hQ hT hp hp2 hK4 hpl
      (fun A hA hAc g hg => orth3_split_derived_rigid hQ hT hp hp2 hpqF A
        ⟨hA.1, hA.2⟩ hAc g hg) hO)

end B

end CFSG.HardMathSupport.Timmesfeld.CrossChar
