module

public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic

public noncomputable section
open WithConv
namespace CFSG.LieType.AlgebraicGroups.ScalarFiltration
universe u
variable {k : Type u} [Field k]
variable (H : Type u) [CommRing H] [HopfAlgebra k H]

theorem exists_simple_subcomodule (V : Type u) [AddCommGroup V] [Module k V]
    [TauCeti.Comodule k H V] [Module.Finite k V] [Nontrivial V] :
    ∃ N : TauCeti.Subcomodule k H V, N ≠ ⊥ ∧
      ∀ W : TauCeti.Subcomodule k H N, W = ⊥ ∨ W = ⊤ := by
  classical
  have hdim : StrictMono (fun N : TauCeti.Subcomodule k H V => Module.finrank k N.toSubmodule) := by
    intro A B hAB
    apply Submodule.finrank_lt_finrank_of_lt
    constructor
    · exact (TauCeti.Subcomodule.toSubmodule_le_toSubmodule).mpr hAB.le
    · intro hBA
      exact hAB.not_ge (TauCeti.Subcomodule.toSubmodule_le_toSubmodule.mp hBA)
  let : WellFoundedLT (TauCeti.Subcomodule k H V) := hdim.wellFoundedLT
  obtain ⟨N,hN⟩ := exists_minimal_of_wellFoundedLT
    (fun N : TauCeti.Subcomodule k H V => N ≠ ⊥) ⟨⊤, by
      intro h
      have h0 : (⊤ : Submodule k V) = ⊥ := by
        simpa using congrArg TauCeti.Subcomodule.toSubmodule h
      obtain ⟨v,hv⟩ := exists_ne (0 : V)
      have hv0 : v ∈ (⊥ : Submodule k V) := h0 ▸ Submodule.mem_top
      exact hv (by simpa using hv0)⟩
  refine ⟨N,hN.1,?_⟩
  intro W
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    let Z := W.map (TauCeti.Subcomodule.subtype N)
    have hZN : Z ≤ N := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := TauCeti.Subcomodule.mem_map.mp hv
      simp [w.property]
    have hZ0 : Z ≠ ⊥ := by
      intro hz
      obtain ⟨w,hw,hw0⟩ := TauCeti.Subcomodule.ne_bot_iff.mp hW
      have hwZ : (w : V) ∈ Z := by
        simpa using TauCeti.Subcomodule.mem_map_of_mem (TauCeti.Subcomodule.subtype N) hw
      rw [hz, TauCeti.Subcomodule.mem_bot] at hwZ
      exact hw0 (Subtype.ext hwZ)
    have hNZ : N ≤ Z := hN.2 hZ0 hZN
    apply TauCeti.Subcomodule.ext
    intro w
    constructor
    · intro _
      exact TauCeti.Subcomodule.mem_top _
    · intro _
      obtain ⟨v,hv,he⟩ := TauCeti.Subcomodule.mem_map.mp (hNZ w.property)
      have hvw : v = w := Subtype.ext (by simpa using he)
      exact hvw ▸ hv

theorem exists_scalar_filtration_of_family {ι : Type*} (p : ι → WithConv (H →ₐ[k] k))
    (hsimple : ∀ W : TauCeti.FGComoduleCat.{u,u,u} k H,
      (∀ N : TauCeti.Subcomodule k H W, N = ⊥ ∨ N = ⊤) →
      ∀ t : ι, ∃ c : k, ∀ v : W,
        TauCeti.Comodule.basePointsRepresentation W (p t) v = c • v)
    (V : Type u) [AddCommGroup V] [Module k V] [TauCeti.Comodule k H V]
    [Module.Finite k V] :
    ∃ (d : ℕ) (F : ℕ →o Submodule k V), F 0 = ⊥ ∧ F d = ⊤ ∧
      (∀ (g : WithConv (H →ₐ[k] k)) i, ∀ v ∈ F i,
        TauCeti.Comodule.basePointsRepresentation V g v ∈ F i) ∧
      ∀ t : ι, ∀ i, ∃ c : k, ∀ v ∈ F (i + 1),
        TauCeti.Comodule.basePointsRepresentation V (p t) v -
          c • v ∈ F i := by
  classical
  suffices h : ∀ n, ∀ (V : Type u) [AddCommGroup V] [Module k V] [TauCeti.Comodule k H V]
      [Module.Finite k V], Module.finrank k V = n →
      ∃ (d : ℕ) (F : ℕ →o Submodule k V), F 0 = ⊥ ∧ F d = ⊤ ∧
        (∀ (g : WithConv (H →ₐ[k] k)) i, ∀ v ∈ F i,
          TauCeti.Comodule.basePointsRepresentation V g v ∈ F i) ∧
        ∀ t : ι, ∀ i, ∃ c : k, ∀ v ∈ F (i + 1),
          TauCeti.Comodule.basePointsRepresentation V (p t) v -
            c • v ∈ F i from h (Module.finrank k V) V rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ _ hn
    by_cases hV : Subsingleton V
    · let := hV
      refine ⟨0, OrderHom.const _ ⊥, rfl, ?_, ?_, ?_⟩
      · ext v
        simp [Subsingleton.elim v 0]
      · intro g i v hv
        simp [Subsingleton.elim v 0]
      · intro t i
        refine ⟨1, fun v hv => ?_⟩
        simp [Subsingleton.elim v 0]
    · have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
      obtain ⟨N,hN0,hNsimple⟩ := exists_simple_subcomodule (k := k) H V
      have : Module.Finite k N := TauCeti.Subcomodule.finite N
      have : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
      have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr
        (fun h => hN0 ((TauCeti.Subcomodule.toSubmodule_eq_bot).mp h))
      have : Nontrivial N.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
        (fun h => hN0 ((TauCeti.Subcomodule.toSubmodule_eq_bot).mp h))
      let Q := V ⧸ N.toSubmodule
      let q : V →ₗ[k] Q := N.toSubmodule.mkQ
      have hlt : Module.finrank k Q < n := by
        have he := Submodule.finrank_quotient_add_finrank N.toSubmodule
        have hp := Module.finrank_pos (R := k) (M := N.toSubmodule)
        change Module.finrank k Q + Module.finrank k N.toSubmodule = Module.finrank k V at he
        rw [hn] at he
        omega
      obtain ⟨d,F,hF0,hFd,hstab,hscalar⟩ := ih (Module.finrank k Q) hlt Q rfl
      let F' : ℕ → Submodule k V := fun i => if i = 0 then ⊥ else (F (i - 1)).comap q
      have hmono : Monotone F' := by
        apply monotone_nat_of_le_succ
        intro i
        by_cases hi : i = 0
        · simp [F',hi]
        · simp only [F',hi,Nat.succ_ne_zero,if_false]
          exact Submodule.comap_mono ((F.monotone (by omega : i - 1 ≤ i)))
      let T : ℕ →o Submodule k V := ⟨F',hmono⟩
      refine ⟨d + 1,T,?_,?_,?_,?_⟩
      · simp [T,F']
      · simp [T,F',hFd]
      · intro g i v hv
        by_cases hi : i = 0
        · simp [T,F',hi] at hv ⊢
          simp [hv]
        · have hvQ : q v ∈ F (i - 1) := by simpa [T,F',hi] using hv
          have hact := hstab g (i - 1) (q v) hvQ
          have hqact := basePointsRepresentation_naturality (TauCeti.Subcomodule.mkQ N) g v
          simp only [TauCeti.Subcomodule.mkQ_apply] at hqact
          change q (TauCeti.Comodule.basePointsRepresentation V g v) =
            TauCeti.Comodule.basePointsRepresentation Q g (q v) at hqact
          change TauCeti.Comodule.basePointsRepresentation V g v ∈ F' i
          simp only [F', hi, if_false, Submodule.mem_comap]
          change q (TauCeti.Comodule.basePointsRepresentation V g v) ∈ F (i - 1)
          rw [hqact]
          exact hact
      · intro t i
        by_cases hi : i = 0
        · subst i
          obtain ⟨c,hc⟩ := hsimple (TauCeti.FGComoduleCat.of (R := k) (C := H) N) hNsimple t
          refine ⟨c,?_⟩
          intro v hv
          have hvN : v ∈ N.toSubmodule := by
            have hqv : q v = 0 := by simpa [T,F',hF0] using hv
            exact (TauCeti.Subcomodule.mkQ_eq_zero_iff N v).mp hqv
          have hcN := hc (⟨v,hvN⟩ : N)
          have hcoe := congrArg (fun x : N => (x : V)) hcN
          rw [basePointsRepresentation_subcomodule_apply] at hcoe
          have he : TauCeti.Comodule.basePointsRepresentation V
              (p t) v - c • v = 0 := sub_eq_zero.mpr hcoe
          simp [T,F',he]
        · obtain ⟨c,hc⟩ := hscalar t (i - 1)
          refine ⟨c,?_⟩
          intro v hv
          have hvQ : q v ∈ F i := by simpa [T,F'] using hv
          have hx := hc (q v)
            (by simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)] using hvQ)
          have hqact := basePointsRepresentation_naturality (TauCeti.Subcomodule.mkQ N)
            (p t) v
          simp only [TauCeti.Subcomodule.mkQ_apply] at hqact
          change q (TauCeti.Comodule.basePointsRepresentation V
              (p t) v) =
            TauCeti.Comodule.basePointsRepresentation Q (p t) (q v) at hqact
          change TauCeti.Comodule.basePointsRepresentation V
            (p t) v - c • v ∈ F' i
          simp only [F', hi, if_false, Submodule.mem_comap]
          change q (TauCeti.Comodule.basePointsRepresentation V
            (p t) v - c • v) ∈ F (i - 1)
          rw [map_sub,map_smul,hqact]
          exact hx

theorem exists_scalar_filtration
    (μ : H →ₐc[k] LaurentPolynomial k)
    (hsimple : ∀ W : TauCeti.FGComoduleCat.{u,u,u} k H,
      (∀ N : TauCeti.Subcomodule k H W, N = ⊥ ∨ N = ⊤) →
      ∀ t : kˣ, ∃ c : k, ∀ v : W,
        TauCeti.Comodule.basePointsRepresentation W (TauCeti.Cocharacter.pointsHom k μ t) v = c • v)
    (V : Type u) [AddCommGroup V] [Module k V] [TauCeti.Comodule k H V]
    [Module.Finite k V] :
    ∃ (d : ℕ) (F : ℕ →o Submodule k V), F 0 = ⊥ ∧ F d = ⊤ ∧
      (∀ (g : WithConv (H →ₐ[k] k)) i, ∀ v ∈ F i,
        TauCeti.Comodule.basePointsRepresentation V g v ∈ F i) ∧
      ∀ t : kˣ, ∀ i, ∃ c : k, ∀ v ∈ F (i + 1),
        TauCeti.Comodule.basePointsRepresentation V (TauCeti.Cocharacter.pointsHom k μ t) v -
          c • v ∈ F i :=
  exists_scalar_filtration_of_family H (TauCeti.Cocharacter.pointsHom k μ) hsimple V

end CFSG.LieType.AlgebraicGroups.ScalarFiltration
