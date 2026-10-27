module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RationalComponentEq
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepAComb
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Dichotomy
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.StdPos
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Straighten

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KE

section Roots


private theorem e6_exists_simple_iform_ne_zero : ∀ β ∈ rootFinset Tag.E6,
    ∃ i : Fin Tag.E6.rank, iform β (Pi.single i 1) ≠ 0 := by
  decide +kernel

private theorem e6_simple_path : ∀ i : Fin Tag.E6.rank, ∃ j : Fin Tag.E6.rank,
    iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) ≠ 0 ∧
      iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (Pi.single 3 1) ≠ 0 := by
  decide +kernel

theorem e6_mem_of_closed {O : Set (Fin Tag.E6.rank → ℤ)} (hne : O.Nonempty)
    (hO : ∀ γ ∈ O, IsRoot Tag.E6 γ)
    (hcl : ∀ γ ∈ O, ∀ β, IsRoot Tag.E6 β → iform γ β ≠ 0 → β ∈ O) :
    ∀ β, IsRoot Tag.E6 β → β ∈ O := by
  obtain ⟨γ₀, hγ₀⟩ := hne
  have hsimple : ∀ i : Fin Tag.E6.rank, IsRoot Tag.E6 (Pi.single i 1) :=
    fun i => isRoot_single Tag.E6 i
  obtain ⟨i₀, hi₀⟩ := e6_exists_simple_iform_ne_zero γ₀ (mem_rootFinset.2 (hO γ₀ hγ₀))
  have hα₀ : (Pi.single i₀ 1 : Fin Tag.E6.rank → ℤ) ∈ O := hcl γ₀ hγ₀ _ (hsimple i₀) hi₀
  have hcen : (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∈ O := by
    obtain ⟨j, hj1, hj2⟩ := e6_simple_path i₀
    exact hcl _ (hcl _ hα₀ _ (hsimple j) hj1) _ (hsimple 3) hj2
  have hall : ∀ k : Fin Tag.E6.rank, (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ O := by
    intro k
    obtain ⟨j, hj1, hj2⟩ := e6_simple_path k
    have hj : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ O :=
      hcl _ hcen _ (hsimple j) (by rwa [iform_comm])
    exact hcl _ hj _ (hsimple k) (by rwa [iform_comm])
  intro β hβ
  obtain ⟨k, hk⟩ := e6_exists_simple_iform_ne_zero β (mem_rootFinset.2 hβ)
  exact hcl _ (hall k) β hβ (by rwa [iform_comm])

end Roots

section Elements


theorem rationalComponent_le_rootSpan {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) :=
  fun _ hx => (Subgroup.commutator_le_self _ hx).1

theorem exists_rootDiagUnit_of_mem_torus_pow {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup Tag.E6 L p) {x : ModGL Tag.E6 L} (hx : x ∈ S.D.torus)
    (hx3 : x ^ 3 = 1) :
    ∃ a : Fin Tag.E6.rank → Lˣ, x = rootDiagUnit Tag.E6 a ∧ ∀ i, a i ^ 3 = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hx).1
  refine ⟨a, rfl, ?_⟩
  have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
    have e : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 L).map_pow a 3
    rw [e]
    exact hx3.trans rootDiagUnit_one.symm
  have h2 : a ^ 3 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
  exact fun i => congrFun h2 i

theorem pinnedX_mem_rootSpan {τ : Tag} {L : Type} [Field L] {S : Set (Fin τ.rank → ℤ)}
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ S) (c : L) : pinnedX τ L γ c ∈ rootSpan τ L S := by
  have h : pinnedX τ L γ c ∈ rootSubgroup τ L γ := mem_rootSubgroup.2 ⟨c, rfl⟩
  exact (le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup τ L α) γ hγ le_rfl) h

theorem rootChar_eq_one_of_commute_pinnedX
    {τ : Tag} {L : Type} [Field L] (b : Fin τ.rank → Lˣ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (h : Commute (rootDiagUnit τ b) (pinnedX τ L γ 1)) : rootChar b γ = 1 := by
  have h1 := rootDiagUnit_conj_pinnedX b hγ (1 : L)
  rw [h.eq, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective τ L γ h1
  rw [mul_one] at h2
  exact Units.ext h2.symm

private theorem not_commute_pinnedX_neg_E6
    {L : Type} [Field L] {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ¬ Commute (pinnedX Tag.E6 L β 1) (pinnedX Tag.E6 L (-β) 1) := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨ε₁, hε₁, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w (isRoot_single Tag.E6 i)
  obtain ⟨ε₂, hε₂, hY⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w (isRoot_neg_single Tag.E6 i)
  intro h
  have hε₁0 : ε₁ ≠ 0 := by rintro rfl; simp at hε₁
  have hε₂0 : ε₂ ≠ 0 := by rintro rfl; simp at hε₂
  set n := canonicalRep (coxeterSystem Tag.E6) L w
  have e1 : pinnedX Tag.E6 L (w • Pi.single i 1) 1 = n * xUnit Tag.E6 L i (ε₁ * 1) * n⁻¹ := by
    rw [← pinnedX_single, hX, ← mul_assoc, hε₁, one_mul]
  have e2 : pinnedX Tag.E6 L (-(w • Pi.single i 1)) 1 =
      n * yUnit Tag.E6 L i (ε₂ * 1) * n⁻¹ := by
    rw [← smul_neg, ← pinnedX_neg_single, hY, ← mul_assoc, hε₂, one_mul]
  rw [e1, e2] at h
  obtain ⟨h1, h2, -⟩ := opposite_simple_root_noncommutativity Tag.E6 L
  apply h2 i (ε₁ * 1) (ε₂ * 1) (by simpa using hε₁0) (by simpa using hε₂0)
  rw [← h1]
  have h' : (n * xUnit Tag.E6 L i (ε₁ * 1) * n⁻¹) * (n * yUnit Tag.E6 L i (ε₂ * 1) * n⁻¹) =
      (n * yUnit Tag.E6 L i (ε₂ * 1) * n⁻¹) * (n * xUnit Tag.E6 L i (ε₁ * 1) * n⁻¹) := h.eq
  have hc : xUnit Tag.E6 L i (ε₁ * 1) * yUnit Tag.E6 L i (ε₂ * 1) =
      yUnit Tag.E6 L i (ε₂ * 1) * xUnit Tag.E6 L i (ε₁ * 1) := by
    calc xUnit Tag.E6 L i (ε₁ * 1) * yUnit Tag.E6 L i (ε₂ * 1)
        = n⁻¹ * ((n * xUnit Tag.E6 L i (ε₁ * 1) * n⁻¹) *
            (n * yUnit Tag.E6 L i (ε₂ * 1) * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * yUnit Tag.E6 L i (ε₂ * 1) * n⁻¹) *
            (n * xUnit Tag.E6 L i (ε₁ * 1) * n⁻¹)) * n := by rw [h']
      _ = yUnit Tag.E6 L i (ε₂ * 1) * xUnit Tag.E6 L i (ε₁ * 1) := by group
  have hc' := congrArg Units.val hc
  rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit] at hc'
  rw [hc', sub_self, LinearMap.zero_apply]

end Elements

section Toral

variable
  {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)

private theorem four_le_pow_orbitLength (hq : 4 ≤ S.D.q) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
  hq.trans (Nat.le_self_pow (outer_componentOrbitLength_spec S hT i).1.ne' _)

theorem rootChar_eq_one_of_commute_rationalComponent (hq : 4 ≤ S.D.q)
    {a b : Fin Tag.E6.rank → Lˣ} (hTa : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTb : rootDiagUnit Tag.E6 b ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      Commute (rootDiagUnit Tag.E6 b) x) :
    ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1 := by
  have hc := commute_rootSpan_of_commute_component_anyT S (by decide) hTa i (by omega)
    (four_le_pow_orbitLength S hq hTa i) _ hcomm
  rintro _ ⟨k, δ, hδ, rfl⟩
  have hδk : δ ∈ kernelRoots (rootCharHom a) := hδ.1
  have h0 : rootChar b δ = 1 :=
    rootChar_eq_one_of_commute_pinnedX b hδk.1 (hc _ (pinnedX_mem_rootSpan hδ 1))
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hr : IsRoot Tag.E6 ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] δ) := by
      clear ih
      induction k with
      | zero => exact hδk.1
      | succ k ih' =>
        rw [Function.iterate_succ_apply']
        exact (S.frob.isRoot_iff _).2 ih'
    rw [Function.iterate_succ_apply', S.frob.rootChar_eq b hTb _ hr, ih, one_pow]

theorem rationalRoots_subset_of_eq (hq : 4 ≤ S.D.q) {a b : Fin Tag.E6.rank → Lˣ}
    (hTa : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hTb : rootDiagUnit Tag.E6 b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (j : KernelComponent (rootCharHom b))
    (hij : rationalComponent S.ρ S.Γ (rootCharHom a) i =
      rationalComponent S.ρ S.Γ (rootCharHom b) j)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      Commute (rootDiagUnit Tag.E6 b) x) :
    rationalRoots S.ρ (rootCharHom a) i ⊆ rationalRoots S.ρ (rootCharHom b) j := by
  classical
  intro γ hγ
  have hker_a := rho_mem_kernelRoots_of_mem_torus S hTa
  have hker_b := rho_mem_kernelRoots_of_mem_torus S hTb
  have hγk : γ ∈ kernelRoots (rootCharHom b) :=
    ⟨(rationalRoots_subset_kernelRoots hker_a i hγ).1,
      rootChar_eq_one_of_commute_rationalComponent S hq hTa hTb i hcomm γ hγ⟩
  by_contra hγj
  set c : KernelComponent (rootCharHom b) := ⟦⟨γ, hγk⟩⟧ with hc
  have hγc : γ ∈ rationalRoots S.ρ (rootCharHom b) c := ⟨0, γ, ⟨hγk, rfl⟩, rfl⟩
  have hne : rationalRoots S.ρ (rootCharHom b) c ≠ rationalRoots S.ρ (rootCharHom b) j :=
    fun h => hγj (h ▸ hγc)
  have hcom := commute_rootSpan_rationalRoots hker_b S.frob.iform_eq hne
  obtain ⟨k, δ, hδ, rfl⟩ := hγ
  have hδc : δ ∈ rationalRoots S.ρ (rootCharHom b) c :=
    rationalRoots_of_iterate_mem hker_b c k hγc
  have hX : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      Commute (pinnedX Tag.E6 L δ 1) x := by
    intro x hx
    rw [hij] at hx
    exact hcom _ (pinnedX_mem_rootSpan hδc 1) _ (rationalComponent_le_rootSpan S j hx)
  have hcX := commute_rootSpan_of_commute_component_anyT S (by decide) hTa i (by omega)
    (four_le_pow_orbitLength S hq hTa i) _ hX
  have hneg : -δ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem δ hδ
  exact not_commute_pinnedX_neg_E6 hδ.1.1 (hcX _ (pinnedX_mem_rootSpan hneg 1))

end Toral

section ToralMain

variable
  {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 3)

theorem false_of_common_component_of_le_torus_E6 (hq : 4 ≤ S.D.q)
    {D₁ : Subgroup (ModGL Tag.E6 L)} (hD₁ : D₁ ≤ S.D.torus) (hexp : ∀ x ∈ D₁, x ^ 3 = 1)
    (hc : Nat.card D₁ = 3 ^ 2) {J : Subgroup (ModGL Tag.E6 L)}
    (hJ : ∀ x ∈ D₁, x ≠ 1 → IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {x})) : False := by
  classical
  haveI : Finite D₁ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hrat : ∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 b ∈ D₁ →
      rootDiagUnit Tag.E6 b ≠ 1 →
      ∃ j : KernelComponent (rootCharHom b), J = rationalComponent S.ρ S.Γ (rootCharHom b) j := by
    intro b hb hb1
    obtain ⟨b', hbb', hb3⟩ := exists_rootDiagUnit_of_mem_torus_pow S (hD₁ hb) (hexp _ hb)
    obtain rfl := CFSG.LieType.Chevalley.rootDiagUnit_injective hbb'
    obtain ⟨j, hj, -⟩ := exists_eq_rationalComponent_of_isComponentOf S Nat.prime_three (hD₁ hb)
      hb3 hb1 (langSetup_hTame S (hD₁ hb) hb3 hb1) (hJ _ hb hb1)
    exact ⟨j, hj⟩
  have hJc : ∀ y ∈ D₁, ∀ x ∈ J, Commute y x := by
    intro y hy x hx
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Commute.one_left x
    · exact (Subgroup.mem_centralizer_singleton_iff.1 ((hJ y hy hy1).1 hx).2).symm
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ D₁, x ≠ 1 := by
    by_contra hno
    push Not at hno
    have hle : D₁ ≤ ⊥ := fun x hx => (Subgroup.mem_bot).2 (hno x hx)
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot, hc] at h1
    norm_num at h1
  obtain ⟨a₀, rfl, -⟩ := exists_rootDiagUnit_of_mem_torus_pow S (hD₁ hx₀) (hexp _ hx₀)
  obtain ⟨i₀, hi₀⟩ := hrat a₀ hx₀ hx₀1
  set O := rationalRoots S.ρ (rootCharHom a₀) i₀ with hO
  have hker₀ := rho_mem_kernelRoots_of_mem_torus S (hD₁ hx₀)
  have hOeq : ∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 b ∈ D₁ →
      ∀ j : KernelComponent (rootCharHom b), J = rationalComponent S.ρ S.Γ (rootCharHom b) j →
        rationalRoots S.ρ (rootCharHom b) j = O := by
    intro b hb j hj
    refine le_antisymm ?_ ?_
    · exact rationalRoots_subset_of_eq S hq (hD₁ hb) (hD₁ hx₀) j i₀ (hj.symm.trans hi₀)
        (fun x hx => hJc _ hx₀ x (hj ▸ hx))
    · exact rationalRoots_subset_of_eq S hq (hD₁ hx₀) (hD₁ hb) i₀ j (hi₀.symm.trans hj)
        (fun x hx => hJc _ hb x (hi₀ ▸ hx))
  have hOroot : ∀ γ ∈ O, IsRoot Tag.E6 γ := fun γ hγ =>
    (rationalRoots_subset_kernelRoots hker₀ i₀ hγ).1
  have hcl : ∀ γ ∈ O, ∀ β, IsRoot Tag.E6 β → iform γ β ≠ 0 → β ∈ O := by
    intro γ hγ β hβ hne
    obtain ⟨b, hb, hb1, hχ⟩ := exists_rootChar_eq_one_of_finite Nat.prime_three
      (fun x hx => (mem_twistedTorusOf.1 (hD₁ hx)).1) hexp (by rw [hc]; norm_num) β
    obtain ⟨j, hj⟩ := hrat b hb hb1
    rw [← hOeq b hb j hj] at hγ ⊢
    have hkerb := rho_mem_kernelRoots_of_mem_torus S (hD₁ hb)
    have hβk : β ∈ kernelRoots (rootCharHom b) := ⟨hβ, hχ⟩
    exact rationalRoots_closed hkerb S.frob.iform_eq j hγ hβk
      (mk_eq_of_iform_ne_zero (by rwa [iform_comm]))
  have hne : O.Nonempty := by
    obtain ⟨⟨γ, hγ⟩, hrep⟩ := Quotient.exists_rep i₀
    exact ⟨γ, 0, γ, ⟨hγ, hrep⟩, rfl⟩
  have hall := e6_mem_of_closed hne hOroot hcl
  apply hx₀1
  have ha₀ : a₀ = 1 := funext fun k => by
    have hk := (rationalRoots_subset_kernelRoots hker₀ i₀ (hall _ (isRoot_single Tag.E6 k))).2
    have hk' : rootChar a₀ (Pi.single k 1) = 1 := hk
    rw [CTTorus.rootChar_single] at hk'
    rw [hk', Pi.one_apply]
  rw [ha₀, rootDiagUnit_one]

end ToralMain

section HeisRoots


open CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4 CFSG.RankThree.Chevalley

private def d4VecList : List (Fin Tag.E6.rank → ℤ) :=
  [![0, -2, -1, -2, -1, 0], ![0, 0, -1, -2, -1, 0], ![0, 0, -1, 0, -1, 0], ![0, 0, -1, 0, 1, 0],
    ![0, 0, 1, 0, -1, 0], ![0, 0, 1, 0, 1, 0], ![0, 0, 1, 2, 1, 0], ![0, 2, 1, 2, 1, 0]]

private theorem d4VecList_reflect : ∀ γ ∈ rootFinset Tag.E6, γ 0 = 0 → γ 5 = 0 →
    ∀ v ∈ d4VecList, v - corootPair γ v • γ ∈ d4VecList := by
  decide +kernel

private theorem v₀_mem_d4VecList : (![0, 0, 1, 0, 1, 0] : Fin Tag.E6.rank → ℤ) ∈ d4VecList := by
  unfold d4VecList
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

private theorem d4VecList_wBeta :
    wordAct Tag.E6 d4TrialityWord ![0, 0, 1, 0, 1, 0] ∉ d4VecList ∧
      wordAct Tag.E6 d4TrialityWord (wordAct Tag.E6 d4TrialityWord ![0, 0, 1, 0, 1, 0]) ∉
        d4VecList := by
  decide +kernel

private theorem d4_exists_simple : ∀ γ ∈ rootFinset Tag.E6, γ 0 = 0 → γ 5 = 0 →
    ∃ j : Fin Tag.E6.rank, j ≠ 0 ∧ j ≠ 5 ∧ iform γ (Pi.single j 1) ≠ 0 := by
  decide +kernel

private theorem d4_simple_center : ∀ j : Fin Tag.E6.rank, j ≠ 0 → j ≠ 5 →
    iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ) (Pi.single 3 1) ≠ 0 := by
  decide +kernel

private theorem perm_three_ne : ∀ π : Equiv.Perm (Fin 3), π 0 ≠ 0 → π (π 0) ≠ 0 →
    ∀ j, π j ≠ j := by
  decide


private theorem kernelWeylGroup_stdChar_smul_mem_iff {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar stdChar)) :
    ∀ x : Fin Tag.E6.rank → ℤ, u • x ∈ d4VecList ↔ x ∈ d4VecList := by
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨w, i, hα, rfl⟩ := hg
    rw [conj_simple_eq_rootReflection]
    have hγ := mem_parabolicRoots_d4Support_iff'.1 (mem_kernelRoots_stdChar.1 hα)
    have hmap : ∀ y ∈ d4VecList, rootReflection (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) • y ∈
        d4VecList := fun y hy => by
      rw [rootReflection_smul hγ.1]
      exact d4VecList_reflect _ (mem_rootFinset.2 hγ.1) hγ.2.1 hγ.2.2 y hy
    intro x
    refine ⟨fun h => ?_, hmap x⟩
    have h2 := hmap _ h
    rwa [← mul_smul, rootReflection_mul_self hγ.1, one_smul] at h2
  | one => simp
  | mul g h _ _ hg hh => intro x; rw [mul_smul, hg, hh]
  | inv g _ hg => intro x; rw [← hg (g⁻¹ • x), smul_inv_smul]

private theorem mem_componentRoots_of_iform_ne_zero {L : Type} [Field L]
    {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)} {γ δ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) (hδ : δ ∈ kernelRoots (rootCharHom a))
    (h : iform γ δ ≠ 0) : δ ∈ componentRoots (rootCharHom a) i := by
  obtain ⟨hγk, hγi⟩ := hγ
  exact ⟨hδ, (mk_eq_of_iform_ne_zero (α := ⟨δ, hδ⟩) (β := ⟨γ, hγk⟩)
    (by rwa [iform_comm])).trans hγi⟩

theorem false_of_fix_componentRoots {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (ha3 : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1) (i : KernelComponent (rootCharHom a))
    (hfix : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ = γ) : False := by
  classical
  obtain ⟨⟨γ₀, hγ₀k⟩, hrep⟩ := Quotient.exists_rep i
  have hγ₀ : γ₀ ∈ componentRoots (rootCharHom a) i := ⟨hγ₀k, hrep⟩
  rcases heisClass_dichotomy a ha3 hw hsh with hA | hD
  ·
    obtain ⟨C, π, -, -, hCker, hCdisj, -, -, hπ0, hππ0, hCw⟩ := classA_components hA
    obtain ⟨j, hj⟩ := (hCker γ₀).1 hγ₀k
    have h1 := hCw j γ₀ hj
    rw [hfix γ₀ hγ₀] at h1
    exact (hCdisj (π j) j (perm_three_ne π hπ0 hππ0 j) γ₀ h1 γ₀ hj).1 rfl
  ·
    obtain ⟨s, hs, hw₀, hsh₀⟩ := stdPosition hD
    set w₀ := s * w * s⁻¹ with hw₀def
    have hker : ∀ j : Fin Tag.E6.rank, j ≠ 0 → j ≠ 5 →
        s⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots (rootCharHom a) := by
      intro j hj0 hj5
      have hr : IsRoot Tag.E6 (s⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :=
        IsRoot.smul (isRoot_single Tag.E6 j) s⁻¹
      refine ⟨hr, (hs _ hr).2 ?_⟩
      rw [smul_inv_smul, mem_parabolicRoots_d4Support_iff']
      exact ⟨isRoot_single Tag.E6 j, by simp [Pi.single_apply, hj0.symm],
        by simp [Pi.single_apply, hj5.symm]⟩
    have hsγ₀ := (hs γ₀ hγ₀k.1).1 hγ₀k.2
    rw [mem_parabolicRoots_d4Support_iff'] at hsγ₀
    obtain ⟨j₁, hj₁0, hj₁5, hj₁⟩ := d4_exists_simple _ (mem_rootFinset.2 hsγ₀.1) hsγ₀.2.1
      hsγ₀.2.2
    have hiform : ∀ x y : Fin Tag.E6.rank → ℤ, iform (s⁻¹ • x) (s⁻¹ • y) = iform x y :=
      fun x y => iform_smul s⁻¹ x y
    have hj₁i : s⁻¹ • (Pi.single j₁ 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i :=
      mem_componentRoots_of_iform_ne_zero hγ₀ (hker j₁ hj₁0 hj₁5) (by
        rw [← inv_smul_smul s γ₀, hiform]
        exact hj₁)
    have h30 : (3 : Fin Tag.E6.rank) ≠ 0 := by decide
    have h35 : (3 : Fin Tag.E6.rank) ≠ 5 := by decide
    have hcen : s⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      by_cases h3 : j₁ = 3
      · rw [← h3]
        exact hj₁i
      · exact mem_componentRoots_of_iform_ne_zero hj₁i (hker 3 h30 h35)
          (by rw [hiform]; exact d4_simple_center j₁ hj₁0 hj₁5)
    have hall : ∀ j : Fin Tag.E6.rank, j ≠ 0 → j ≠ 5 →
        s⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
      intro j hj0 hj5
      by_cases h3 : j = 3
      · rw [h3]
        exact hcen
      · exact mem_componentRoots_of_iform_ne_zero hcen (hker j hj0 hj5)
          (by rw [hiform, iform_comm]; exact d4_simple_center j hj0 hj5)
    have hw₀fix : ∀ j : Fin Tag.E6.rank, j ≠ 0 → j ≠ 5 →
        w₀ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 := by
      intro j hj0 hj5
      have h := hfix _ (hall j hj0 hj5)
      rw [hw₀def, mul_smul, mul_smul, h, smul_inv_smul]
    set v₀ : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 0, 1, 0] with hv₀
    have hv₀e : v₀ = Pi.single 2 1 + Pi.single 4 1 := by
      funext k
      fin_cases k <;> rfl
    have hv₀fix : w₀ • v₀ = v₀ := by
      rw [hv₀e, smul_add, hw₀fix 2 (by decide) (by decide), hw₀fix 4 (by decide) (by decide)]
    have hv₀mem : v₀ ∈ d4VecList := v₀_mem_d4VecList
    set c : ZMod 3 := triPairing stdChar (e6Shift w₀) / triPairing stdChar (e6Shift wBeta)
      with hc
    have hc0 : c ≠ 0 := div_ne_zero hsh₀ triPairing_e6Shift_wBeta
    set ε := c.val with hε
    have hε12 : ε = 1 ∨ ε = 2 := by
      have h1 : ε < 3 := ZMod.val_lt c
      have h2 : ε ≠ 0 := fun h => hc0 ((ZMod.val_eq_zero c).1 h)
      omega
    have hwβpow : wBeta ^ ε ∈ charStabilizer (triChar stdChar) :=
      pow_mem mem_charStabilizer_wBeta ε
    have hsh0 : triPairing stdChar (e6Shift (w₀ * (wBeta ^ ε)⁻¹)) = 0 := by
      have h1 := triPairing_e6Shift_mul hw₀ (wBeta ^ ε)⁻¹
      have h2 : triPairing stdChar (e6Shift (wBeta ^ ε)⁻¹) =
          -triPairing stdChar (e6Shift (wBeta ^ ε)) := by
        have := triPairing_e6Shift_mul hwβpow (wBeta ^ ε)⁻¹
        rw [mul_inv_cancel, e6Shift_one, triPairing_zero] at this
        linear_combination (-1 : ZMod 3) * this
      have h3 : triPairing stdChar (e6Shift (wBeta ^ ε)) =
          (ε : ZMod 3) * triPairing stdChar (e6Shift wBeta) :=
        pow_charStab_shift mem_charStabilizer_wBeta ε
      have h4 : (ε : ZMod 3) = c := ZMod.natCast_zmod_val c
      have h5 : c * triPairing stdChar (e6Shift wBeta) = triPairing stdChar (e6Shift w₀) :=
        div_mul_cancel₀ _ triPairing_e6Shift_wBeta
      rw [h1, h2, h3, h4, h5]
      ring
    have hu : w₀ * (wBeta ^ ε)⁻¹ ∈ kernelWeylGroup (triChar stdChar) :=
      e6Shift_mem_kernelWeylGroup stdChar (mul_mem hw₀ (inv_mem hwβpow)) hsh0
    have hmem : wBeta ^ ε • v₀ ∈ d4VecList := by
      have h := (kernelWeylGroup_stdChar_smul_mem_iff hu (wBeta ^ ε • v₀)).2
      rw [← mul_smul, inv_mul_cancel_right, hv₀fix] at h
      exact (kernelWeylGroup_stdChar_smul_mem_iff hu (wBeta ^ ε • v₀)).1 (by
        rw [← mul_smul, inv_mul_cancel_right, hv₀fix]
        exact hv₀mem)
    obtain ⟨hβ1, hβ2⟩ := d4VecList_wBeta
    rcases hε12 with h | h
    · rw [h, pow_one, wBeta, ← wordAct_eq_smul] at hmem
      exact hβ1 hmem
    · rw [h, pow_two, mul_smul, wBeta, ← wordAct_eq_smul, ← wordAct_eq_smul] at hmem
      exact hβ2 hmem

end HeisRoots

section HeisMain

variable
  {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 3)

theorem rootSpan_kernel_le_normalizer {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    rootSpan Tag.E6 L (rootCharKernel a) ≤
      Subgroup.normalizer (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) :
        Set (ModGL Tag.E6 L)) := by
  refine iSup₂_le fun γ hγ => ?_
  have hγk : γ ∈ kernelRoots (rootCharHom a) := hγ
  by_cases hγi : (⟦⟨γ, hγk⟩⟧ : KernelComponent (rootCharHom a)) = i
  · exact (le_iSup₂_of_le (f := fun α (_ : α ∈ componentRoots (rootCharHom a) i) =>
      rootSubgroup Tag.E6 L α) γ ⟨hγk, hγi⟩ le_rfl).trans Subgroup.le_normalizer
  · have h := (rootSubgroup_le_componentRootSpan L ⟨γ, hγk⟩).trans
      (componentRootSpan_le_centralizer L hγi)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hxc := Subgroup.mem_centralizer_iff.1 (h hx) g
    constructor
    · intro hg
      have e : x * g * x⁻¹ = g := by rw [← hxc hg, mul_inv_cancel_right]
      rw [e]
      exact hg
    · intro hg
      have hg' : x * g * x⁻¹ ∈ componentRootSpan L (rootCharHom a) i := hg
      have hc := Subgroup.mem_centralizer_iff.1 (h hx) _ hg'
      have e : g = x * g * x⁻¹ := by
        calc g = x⁻¹ * ((x * g * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * g * x⁻¹)) := by rw [hc]
          _ = x * g * x⁻¹ := by group
      rw [e]
      exact hg

theorem false_of_heisenberg_component_E6 (hq : 4 ≤ S.D.q) {a b : Fin Tag.E6.rank → Lˣ}
    {w : WeylGroup Tag.E6} (ha3 : ∀ i, a i ^ 3 = 1) (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1) {u : ModGL Tag.E6 L}
    (hu : u ∈ rootSpan Tag.E6 L (rootCharKernel a)) {J : Subgroup (ModGL Tag.E6 L)}
    (hJ : IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}))
    (hcomm : ∀ x ∈ J, Commute (u⁻¹ * (rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) L w) * u) x) : False := by
  obtain ⟨i, hi, -⟩ := exists_eq_rationalComponent_of_isComponentOf S Nat.prime_three hT ha3 h1
    (langSetup_hTame S hT ha3 h1) hJ
  have hc := commute_rootSpan_of_commute_component_anyT S (by decide) hT i (by omega)
    (four_le_pow_orbitLength S hq hT i) _ (fun x hx => hcomm x (hi ▸ hx))
  have hN := rootSpan_kernel_le_normalizer i (inv_mem hu)
  have hc₀ : ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
      Commute (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) g := by
    intro g hg
    have hg' : u⁻¹ * g * u⁻¹⁻¹ ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) :=
      (Subgroup.mem_normalizer_iff.1 hN g).1 hg
    rw [inv_inv] at hg'
    have h := (hc _ hg').eq
    show rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w * g =
      g * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w)
    calc rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w * g
        = u * ((u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u) *
            (u⁻¹ * g * u)) * u⁻¹ := by group
      _ = u * ((u⁻¹ * g * u) * (u⁻¹ * (rootDiagUnit Tag.E6 b *
            canonicalRep (coxeterSystem Tag.E6) L w) * u)) * u⁻¹ := by rw [h]
      _ = g * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) := by group
  refine false_of_fix_componentRoots ha3 hw hsh i fun γ hγ => ?_
  have hγr : IsRoot Tag.E6 γ := hγ.1.1
  obtain ⟨ε, -, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγr
  have h2 : rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w *
      pinnedX Tag.E6 L γ 1 *
        (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ =
      pinnedX Tag.E6 L (w • γ) ((rootChar b (w • γ) : L) * (ε * 1)) := by
    rw [mul_inv_rev, show rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w *
        pinnedX Tag.E6 L γ 1 * ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          (rootDiagUnit Tag.E6 b)⁻¹) = rootDiagUnit Tag.E6 b *
        (canonicalRep (coxeterSystem Tag.E6) L w * pinnedX Tag.E6 L γ 1 *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) * (rootDiagUnit Tag.E6 b)⁻¹ by group,
      hX, rootDiagUnit_conj_pinnedX b (IsRoot.smul hγr w)]
  have h3 : rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w *
      pinnedX Tag.E6 L γ 1 *
        (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ =
      pinnedX Tag.E6 L γ 1 := by
    rw [(hc₀ _ (pinnedX_mem_rootSpan hγ 1)).eq, mul_inv_cancel_right]
  have h4 : pinnedX Tag.E6 L γ 1 ∈ rootSubgroup Tag.E6 L (w • γ) := by
    rw [← h3, h2]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  exact (eq_of_pinnedX_one_mem_rootSubgroup hγr (IsRoot.smul hγr w) h4).symm

end HeisMain

end CFSG.HardMathSupport.Timmesfeld.LangTorus
