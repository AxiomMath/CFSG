module

public import CFSG.ClassicalInvolution.Asc77.AscS24FG0C
public import CFSG.ClassicalInvolution.AschTight.S19GC1
public import CFSG.ClassicalInvolution.AschTight.S19GC2
public import CFSG.ClassicalInvolution.AschTight.S19GCore

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open scoped MatrixGroups

section Iso

variable {K E : Type*} [Group K] [Group E]

theorem centralizer_map_mulEquiv (e : K ≃* E) (S : Subgroup K) :
    Subgroup.centralizer (S.map e.toMonoidHom : Set E) =
      (Subgroup.centralizer (S : Set K)).map e.toMonoidHom := by
  refine le_antisymm (fun x hx => ?_) (map_centralizer_le e.toMonoidHom S)
  refine ⟨e.symm x, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_, e.apply_symm_apply x⟩
  apply e.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact Subgroup.mem_centralizer_iff.mp hx (e s) ⟨s, hs, rfl⟩

theorem nonempty_centralizer_equiv {M : Type*} [Group M] (f : K →* E) (hf : Function.Bijective f)
    (S : Subgroup K) (g : K) (Φ' : M →* K) (hΦ' : Function.Injective Φ')
    (hC : Subgroup.centralizer (S : Set K) = Φ'.range) :
    Nonempty (↥(Subgroup.centralizer (((conjSub g S).map f : Subgroup E) : Set E)) ≃* M) := by
  set e : K ≃* E := (MulAut.conj g).trans (MulEquiv.ofBijective f hf) with he
  have hmap : (conjSub g S).map f = S.map e.toMonoidHom := by
    rw [conjSub, Subgroup.map_map]
    rfl
  have hinj : Function.Injective (e.toMonoidHom.comp Φ') := e.injective.comp hΦ'
  have hrange : Subgroup.centralizer (((conjSub g S).map f : Subgroup E) : Set E) =
      (e.toMonoidHom.comp Φ').range := by
    rw [hmap, centralizer_map_mulEquiv, hC, MonoidHom.map_range]
  exact ⟨(MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hinj).symm⟩

end Iso

section Models

variable {p : ℕ} [Fact p.Prime]

theorem nonempty_centralizer_equiv_g2 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {E : Type*} [Group E]
    (f : ↥(adjointGroup .G2 (GaloisField p e)) →* E) (hf : Function.Bijective f)
    {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e))) :
    Nonempty (↥(Subgroup.centralizer ((R.map f : Subgroup E) : Set E)) ≃*
      SL(2, GaloisField p e)) := by
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨i, g, rfl⟩ := exists_eq_conjSub_g2Chart hR
  obtain ⟨Φ', hΦ', hC⟩ := exists_centralizer_eq_g2 hodd i
  exact nonempty_centralizer_equiv f hf _ g Φ' hΦ' hC

theorem nonempty_centralizer_equiv_d4 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {E : Type*} [Group E]
    (f : ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) →* E)
    (hf : Function.Bijective f)
    {R : Subgroup ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4
      (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e))) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F),
      Nonempty (↥(Subgroup.centralizer ((R.map f : Subgroup E) : Set E)) ≃* SL(2, F)) := by
  obtain ⟨hσ3, hK1, hC₀, hgF, -, -⟩ := d4_model_data hp2 he
  obtain ⟨i, g₀, hRg⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨g, hg⟩ : ∃ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e), g = g₀ :=
    ⟨g₀, rfl⟩
  have hR' : R = conjSub g (CFSG.LieType.CurtisTits.rankOne
      (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
    rw [hg]
    exact hRg
  subst hR'
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = ng 0 := Fin.ext h0
    subst hi'
    rw [ModelFacts.rankOne_long_eq_range hσ3]
    exact ⟨GaloisField p (3 * e), inferInstance, Fintype.ofFinite _,
      nonempty_centralizer_equiv f hf _ g (slB _ hσ3) (slB_injective hσ3)
        (centralizer_range_slLong hσ3 hK1 hC₀ hgF)⟩
  · have hi' : i = ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3]
    exact ⟨↥(fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)), inferInstance,
      Fintype.ofFinite _, nonempty_centralizer_equiv f hf _ g _
        ((MulAut.conj _).injective.comp (slLong_injective hσ3))
        (centralizer_range_slShort hσ3 hK1 hC₀ hgF)⟩

end Models

theorem factFG0CCore :
    ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
      ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
        (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
          ((t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) →
          Nonempty (CFSG.ClassicalInvolution.Asc77.Ih8Model p e Ω t k e') →
          ∀ L ∈ Ω, ∃ (F : Type) (_ : Field F) (_ : Fintype F),
            Nonempty (↥(Subgroup.centralizer (L : Set E)) ≃* SL(2, F)) := by
  intro p e _ hp2 _ E _ _ _ Ω t k e' ht ⟨M⟩ L hL
  have he' : 1 ≤ e' := M.admissible.2.1
  have htag : t = .G2 ∨ t = .trialityD4 := by
    rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [Or.inl rfl, Or.inr rfl]
  obtain ⟨R, hRcls, rfl⟩ := (M.mem_iff L).mp hL
  have hRfund := M.cls_sub hRcls
  have hinj : Function.Injective M.ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact M.ker_le_center.trans (RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 htag k he').le
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨GaloisField p e', inferInstance, Fintype.ofFinite _,
      nonempty_centralizer_equiv_g2 hp2 he' M.ψ ⟨hinj, M.surj⟩ hRfund⟩
  · exact nonempty_centralizer_equiv_d4 hp2 he' M.ψ ⟨hinj, M.surj⟩ hRfund

theorem factFG0C : CFSG.ClassicalInvolution.Asc77.S24.FactFG0C :=
  factFG0CCore

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
