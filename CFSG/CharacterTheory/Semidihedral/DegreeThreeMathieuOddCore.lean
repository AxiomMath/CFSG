module

public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularity

public section

open scoped Nat

namespace CFSG.Semidihedral.DegreeThreeMathieuOddCore

open CFSG.Assembly.LowTwoRank
open CFSG.Wreathed.DegreeThreeModelFullCenter
open CFSG.Wreathed.OddUnitaryThreeCentralizerCore
open CFSG.ComponentClassification.CatalogueBUnitaryTwo
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry

theorem oddCore_map_centralizerEquiv {G X : Type} [Group G] [Group X] (e : G ≃* X) (t : G) :
    (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))).map
        (originalCentralizerEquiv e t).toMonoidHom =
      CFSG.oddCore (Subgroup.centralizer ({e t} : Set X)) := by
  rw [CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore,
    CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore]
  exact CFSG.pPrimeCore_map_iso 2 _

theorem oddCore_le_center_of_equiv {A B : Type} [Group A] [Group B] (θ : A ≃* B)
    (hmap : (CFSG.oddCore A).map θ.toMonoidHom = CFSG.oddCore B)
    (hB : CFSG.oddCore B ≤ Subgroup.center B) : CFSG.oddCore A ≤ Subgroup.center A := by
  intro g hg
  have hθ : θ g ∈ Subgroup.center B := hB (hmap ▸ Subgroup.mem_map_of_mem _ hg)
  rw [Subgroup.mem_center_iff] at hθ ⊢
  intro a
  apply θ.injective
  rw [map_mul, map_mul, hθ]

theorem isCyclic_oddCore_of_equiv {A B : Type} [Group A] [Group B] (θ : A ≃* B)
    (hmap : (CFSG.oddCore A).map θ.toMonoidHom = CFSG.oddCore B)
    (hB : IsCyclic (CFSG.oddCore B)) : IsCyclic (CFSG.oddCore A) := by
  let iso : CFSG.oddCore A ≃* CFSG.oddCore B :=
    ((CFSG.oddCore A).equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact isCyclic_of_surjective iso.symm.toMonoidHom iso.symm.surjective

theorem card_oddCore_of_equiv {A B : Type} [Group A] [Group B] (θ : A ≃* B)
    (hmap : (CFSG.oddCore A).map θ.toMonoidHom = CFSG.oddCore B) :
    Nat.card (CFSG.oddCore A) = Nat.card (CFSG.oddCore B) := by
  rw [← hmap]
  exact (Subgroup.card_map_of_injective θ.injective).symm

theorem oddCore_facts_of_equiv {G X : Type} [Group G] [Group X] (e : G ≃* X) (t : G) (k : ℕ)
    (hcen : CFSG.oddCore (Subgroup.centralizer ({e t} : Set X)) ≤
      Subgroup.center (Subgroup.centralizer ({e t} : Set X)))
    (hcyc : IsCyclic (CFSG.oddCore (Subgroup.centralizer ({e t} : Set X))))
    (hcard : Nat.card (CFSG.oddCore (Subgroup.centralizer ({e t} : Set X))) = k) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ≤
        Subgroup.center (Subgroup.centralizer ({t} : Set G)) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) = k := by
  have hmap := oddCore_map_centralizerEquiv e t
  exact ⟨oddCore_le_center_of_equiv _ hmap hcen, isCyclic_oddCore_of_equiv _ hmap hcyc,
    (card_oddCore_of_equiv _ hmap).trans hcard⟩

theorem linear_model_centralizer_oddCore {G : Type} [Group G] (p f : ℕ) (hp : p.Prime)
    (hpodd : p ≠ 2) (hf : 1 ≤ f) (hmodel : StatedClassicalModel G .PSL 3 p f) (t : G)
    (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ≤
        Subgroup.center (Subgroup.centralizer ({t} : Set G)) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) =
        ordCompl[2] (p ^ f - 1) / Nat.gcd 3 (p ^ f - 1) := by
  obtain ⟨_, F, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
  let e := eModel.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have ht' : orderOf (e t) = 2 := (orderOf_injective e.toMonoidHom e.injective t).trans ht
  have hF : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hpodd).pow
  have hq : 3 ≤ Nat.card F := by
    rw [hcard]
    have h3 : 3 ≤ p := by
      have := hp.two_le
      have hp2 : p ≠ 2 := hpodd
      omega
    calc 3 ≤ p := h3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcen, hcyc, hord, -⟩ :=
    CFSG.Wreathed.OddLinearThreeCentralizerCore.odd_linear_three_involution_centralizer_core F
      hF hq (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) le_rfl (e t) ht'
  have hD : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) =
      Nat.gcd 3 (p ^ f - 1) := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num), hcard]
  rw [hD, hcard] at hord
  exact oddCore_facts_of_equiv e t _ hcen hcyc hord

theorem card_scalarCenter {E V : Type} [Field E] [Finite E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (p f : ℕ) [Fact p.Prime] (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hdim : Module.finrank E V = 3) :
    Nat.card (scalarCenter h hdim) = Nat.gcd 3 (p ^ f + 1) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
  have hinj : Function.Injective (scalarSpecial h hdim) := by
    intro a b hab
    have h1 : scalarIsometry h a.val = scalarIsometry h b.val :=
      congrArg Subtype.val (congrArg Subtype.val hab) |> Subtype.ext
    exact Subtype.ext (scalarIsometry_injective h h1)
  rw [scalarCenter, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, cubicUnits,
    IsCyclic.card_powMonoidHom_ker, normOneUnits_card p f hE, Nat.gcd_comm]

theorem unitary_model_centralizer_oddCore {G : Type} [Group G] (p f : ℕ) (hp : p.Prime)
    (hpodd : p ≠ 2) (hmodel : StatedClassicalModel G .PSU 3 p f) (t : G)
    (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ≤
        Subgroup.center (Subgroup.centralizer ({t} : Set G)) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) =
        ordCompl[2] (p ^ f + 1) / Nat.gcd 3 (p ^ f + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, E, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
  let h := originalIdentityForm p f hcard
  let D := scalarCenter h (Module.finrank_fin_fun E)
  let : D.Normal := scalar_subgroup_normal h (Module.finrank_fin_fun E) D le_rfl
  let e : G ≃* specialIsometry h ⧸ D :=
    eModel.trans (originalIdentityProjectiveEquiv p f hcard).symm
  have ht' : orderOf (e t) = 2 := (orderOf_injective e.toMonoidHom e.injective t).trans ht
  obtain ⟨z, hz, hzt, hrest⟩ := odd_unitary_three_involution_centralizer_core p f
    (hp.odd_of_ne_two hpodd) hcard h (originalIdentityForm_isSymm p f hcard)
    (originalIdentityForm_nondegenerate p f hcard) (Module.finrank_fin_fun E) D le_rfl (e t) ht'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcen, hcyc, hord⟩ := hrest
  rw [card_scalarCenter p f hcard h (Module.finrank_fin_fun E)] at hord
  exact oddCore_facts_of_equiv e t _ hcen hcyc hord

theorem mathieu_model_centralizer_oddCore
    {G : Type} [Group G]
    (hmodel : Nonempty (G ≃* StatedM11)) (t : G) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  rw [CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore]
  exact (ProperSubgroupRegularity.stated_m11_involution_centralizer_card_and_core G hmodel t
    ht).2

theorem degree_three_and_Mathieu_model_centralizer_odd_core_central
    (G : Type) [Group G]
    (hG : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
      Nonempty (G ≃* StatedM11)) :
    (∀ t : G, orderOf t = 2 →
      CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ≤
        Subgroup.center (Subgroup.centralizer ({t} : Set G))) ∧
    (∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → StatedClassicalModel G .PSL 3 p f →
      ∀ t : G, orderOf t = 2 →
        IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) ∧
          Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) =
            ordCompl[2] (p ^ f - 1) / Nat.gcd 3 (p ^ f - 1)) ∧
    (∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → StatedClassicalModel G .PSU 3 p f →
      ∀ t : G, orderOf t = 2 →
        IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) ∧
          Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))) =
            ordCompl[2] (p ^ f + 1) / Nat.gcd 3 (p ^ f + 1)) ∧
    (Nonempty (G ≃* StatedM11) → ∀ t : G, orderOf t = 2 →
      CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) := by
  refine ⟨fun t ht => ?_, fun p f hp hpodd hf hmodel t ht =>
      (linear_model_centralizer_oddCore p f hp hpodd hf hmodel t ht).2,
    fun p f hp hpodd _ hmodel t ht =>
      (unitary_model_centralizer_oddCore p f hp hpodd hmodel t ht).2,
    fun hmodel t ht => mathieu_model_centralizer_oddCore hmodel t ht⟩
  rcases hG with ⟨p, f, hp, hpodd, hf, hmodel⟩ | ⟨p, f, hp, hpodd, -, hmodel⟩ | hmodel
  · exact (linear_model_centralizer_oddCore p f hp hpodd hf hmodel t ht).1
  · exact (unitary_model_centralizer_oddCore p f hp hpodd hmodel t ht).1
  · rw [mathieu_model_centralizer_oddCore hmodel t ht]
    exact bot_le

end CFSG.Semidihedral.DegreeThreeMathieuOddCore
