module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs

set_option linter.unusedSectionVars false

theorem map_eq_of_cube {X : Type} [Group X] (𝒞 : Set (Subgroup X))
    (hpair : ∀ J₁ ∈ 𝒞, ∀ J₂ ∈ 𝒞, ∀ J₃ ∈ 𝒞, J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃)
    (g : MulAut X) (hg3 : g ^ 3 = 1) (hmap : ∀ J ∈ 𝒞, J.map g.toMonoidHom ∈ 𝒞) :
    ∀ J ∈ 𝒞, J.map g.toMonoidHom = J := by
  intro J hJ
  have hinj : ∀ A B : Subgroup X, A.map g.toMonoidHom = B.map g.toMonoidHom → A = B :=
    fun A B h => Subgroup.map_injective g.injective h
  have hmap2 : ((J.map g.toMonoidHom).map g.toMonoidHom).map g.toMonoidHom = J := by
    rw [Subgroup.map_map, Subgroup.map_map]
    have : (g.toMonoidHom.comp g.toMonoidHom).comp g.toMonoidHom = MonoidHom.id X := by
      ext x
      have h := congrArg (fun φ : MulAut X => φ x) hg3
      simp only [pow_three', MulAut.mul_apply, MulAut.one_apply] at h
      exact h
    rw [this]
    exact Subgroup.map_id J
  rcases hpair J hJ (J.map g.toMonoidHom) (hmap J hJ)
    ((J.map g.toMonoidHom).map g.toMonoidHom) (hmap _ (hmap J hJ)) with h | h | h
  · exact h.symm
  ·
    have : J.map g.toMonoidHom = J := by
      calc J.map g.toMonoidHom = ((J.map g.toMonoidHom).map g.toMonoidHom).map g.toMonoidHom := by
            rw [← h]
        _ = J := hmap2
    exact this
  ·
    exact (hinj _ _ h).symm

theorem fixSubgroup_eq_fixedPoints {X : Type} [Group X] (f : MulAut X) :
    fixSubgroup f = fixedPoints (Subgroup.zpowers f) := by
  ext x
  rw [mem_fixSubgroup]
  constructor
  · intro hx
    have hle : Subgroup.zpowers f ≤ MulAction.stabilizer (MulAut X) x :=
      Subgroup.zpowers_le.2 hx
    intro φ hφ
    exact hle hφ
  · intro hx
    exact hx f (Subgroup.mem_zpowers f)

theorem isComponentOf_map_of_commute {X : Type} [Group X] (f g : MulAut X)
    (hfg : f * g = g * f) {J : Subgroup X}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    CFSG.Open.IsComponentOf (J.map g.toMonoidHom) (fixedPoints (Subgroup.zpowers f)) := by
  have hmap : (fixedPoints (Subgroup.zpowers f)).map g.toMonoidHom =
      fixedPoints (Subgroup.zpowers f) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ φ hφ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
      have hcomm : (f ^ k) * g = g * (f ^ k) := by
        have : Commute f g := hfg
        exact (this.zpow_left k).eq
      have h1 := hy (f ^ k) (Subgroup.zpow_mem_zpowers f k)
      calc (f ^ k) (g y) = (f ^ k * g) y := rfl
        _ = (g * f ^ k) y := by rw [hcomm]
        _ = g ((f ^ k) y) := rfl
        _ = g y := by rw [h1]
    · intro hx
      refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
      intro φ hφ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
      have hcomm : (f ^ k) * g = g * (f ^ k) := by
        have : Commute f g := hfg
        exact (this.zpow_left k).eq
      apply g.injective
      have h1 := hx (f ^ k) (Subgroup.zpow_mem_zpowers f k)
      calc g ((f ^ k) (g.symm x)) = (g * f ^ k) (g.symm x) := rfl
        _ = (f ^ k * g) (g.symm x) := by rw [hcomm]
        _ = (f ^ k) x := by rw [MulAut.mul_apply, g.apply_symm_apply]
        _ = g (g.symm x) := by rw [h1, g.apply_symm_apply]
  have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (g : X ≃* X) hJ
  rw [← hmap]
  exact h

section Classes


theorem kernel_classes_le_two {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1)
    (hbig : 18 < (kernelRoots (rootCharHom a)).ncard) :
    ∀ i j k : KernelComponent (rootCharHom a), i = j ∨ i = k ∨ j = k := by
  intro i j k
  by_contra hcon
  push Not at hcon
  obtain ⟨hij, hik, hjk⟩ := hcon
  have F := kac_facts h3 ha
  obtain ⟨hi6, hj6, hk6⟩ := F.three i j k hij hik hjk
  have hfin : ∀ c : KernelComponent (rootCharHom a),
      (componentRoots (rootCharHom a) c).ncard = 6 → (componentRoots (rootCharHom a) c).Finite :=
    fun c hc => Set.finite_of_ncard_ne_zero (by omega)
  have hsub : kernelRoots (rootCharHom a) ⊆
      componentRoots (rootCharHom a) i ∪ componentRoots (rootCharHom a) j ∪
        componentRoots (rootCharHom a) k := by
    intro α hα
    have hαc : α ∈ componentRoots (rootCharHom a) (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a)) :=
      ⟨hα, rfl⟩
    by_cases hci : (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a)) = i
    · rw [hci] at hαc
      exact Or.inl (Or.inl hαc)
    by_cases hcj : (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a)) = j
    · rw [hcj] at hαc
      exact Or.inl (Or.inr hαc)
    by_cases hck : (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a)) = k
    · rw [hck] at hαc
      exact Or.inr hαc
    exact (F.four i j k _ hij hik (Ne.symm hci) hjk (Ne.symm hcj) (Ne.symm hck)).elim
  have hfi := hfin i hi6
  have hfj := hfin j hj6
  have hfk := hfin k hk6
  have h1 : (kernelRoots (rootCharHom a)).ncard ≤
      (componentRoots (rootCharHom a) i ∪ componentRoots (rootCharHom a) j ∪
        componentRoots (rootCharHom a) k).ncard :=
    Set.ncard_le_ncard hsub ((hfi.union hfj).union hfk)
  have h2 := Set.ncard_union_le
    (componentRoots (rootCharHom a) i ∪ componentRoots (rootCharHom a) j)
    (componentRoots (rootCharHom a) k)
  have h3' := Set.ncard_union_le (componentRoots (rootCharHom a) i)
    (componentRoots (rootCharHom a) j)
  omega

end Classes

section Main


theorem components_pair_of_dim (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    (h : twistedE6InndiagGL K σ) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    (hdim : twE6MatFixDim K σ h ∈ ({28, 36, 46} : Set ℕ)) :
    ∀ J₁ J₂ J₃ : Subgroup (twistedE6RootGroup K σ),
      CFSG.Open.IsComponentOf J₁ (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
      CFSG.Open.IsComponentOf J₂ (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
      CFSG.Open.IsComponentOf J₃ (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
        J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [← hqf]; exact hKq
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := by intro c; rw [← hqf]; exact hσ c
  have hpℓ : 3 ≠ ringChar K := fun h' => hK3 h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp hf Nat.prime_three (by norm_num) hpℓ
  have hh3' : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  have hh1' : (h : ModGL TwistTag.E6.tag K) ≠ 1 := fun h' => hh1 (Subtype.ext h')
  obtain ⟨S, a, ι, -, hT, hap, h1, hinj, hrange, hconj, hg0⟩ :=
    exists_langSetup_conj_of_inndiag_twE6 hp hf hK' σ hσ' Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      monomialToralAt_E6_three (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) hh3' hh1'
  have hker := twE6MatFixDim_eq_of_conj σ h S.D.g0 a hg0
  have hbig : 18 < (kernelRoots (rootCharHom a)).ncard := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdim
    omega
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  have hcl := kernel_classes_le_two hL3 hap hbig
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hL3 (fun h => absurd h (by decide)) hT
    hap h1
  have hcomp : ∀ J : Subgroup (twistedE6RootGroup K σ),
      CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) →
      ∃ i : KernelComponent (rootCharHom a),
        J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro J hJ
    rw [← fixSubgroup_eq_fixedPoints] at hJ
    obtain ⟨i, -, hi⟩ := components_of_langSetup S Nat.prime_three ι hinj hrange
      (twistedE6InndiagConj K σ h) hconj hT hap h1 hTame hJ
    exact ⟨i, hi⟩
  intro J₁ J₂ J₃ h₁ h₂ h₃
  obtain ⟨i₁, hi₁⟩ := hcomp J₁ h₁
  obtain ⟨i₂, hi₂⟩ := hcomp J₂ h₂
  obtain ⟨i₃, hi₃⟩ := hcomp J₃ h₃
  have hmapinj : ∀ A B : Subgroup (twistedE6RootGroup K σ), A.map ι = B.map ι → A = B :=
    fun A B hAB => Subgroup.map_injective hinj hAB
  rcases hcl i₁ i₂ i₃ with e | e | e
  · exact Or.inl (hmapinj _ _ (by rw [hi₁, hi₂, e]))
  · exact Or.inr (Or.inl (hmapinj _ _ (by rw [hi₁, hi₃, e])))
  · exact Or.inr (Or.inr (hmapinj _ _ (by rw [hi₂, hi₃, e])))

theorem components_invariant_of_dim (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    (h : twistedE6InndiagGL K σ) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1)
    (hdim : twE6MatFixDim K σ h ∈ ({28, 36, 46} : Set ℕ))
    (g : MulAut (twistedE6RootGroup K σ)) (hg3 : g ^ 3 = 1)
    (hgf : twistedE6InndiagConj K σ h * g = g * twistedE6InndiagConj K σ h)
    (J : Subgroup (twistedE6RootGroup K σ))
    (hJ : CFSG.Open.IsComponentOf J
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    J.map g.toMonoidHom = J := by
  have hpair := components_pair_of_dim K σ q hK3 hσ hKq hq2 h hh1 hh3 hdim
  exact map_eq_of_cube
    {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))}
    (fun J₁ h₁ J₂ h₂ J₃ h₃ => hpair J₁ J₂ J₃ h₁ h₂ h₃) g hg3
    (fun J hJ' => isComponentOf_map_of_commute _ g hgf hJ') J hJ

theorem components_invariant_of_mem (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E)
    (h : twistedE6InndiagGL K σ) (hh : twistedE6InndiagConj K σ h = f) (hh1 : h ≠ 1)
    (hh3 : h ^ 3 = 1) (hdim : twE6MatFixDim K σ h ∈ ({28, 36, 46} : Set ℕ))
    (J : Subgroup (twistedE6RootGroup K σ))
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    ∀ g ∈ E, J.map g.toMonoidHom = J := by
  intro g hg
  subst hh
  exact components_invariant_of_dim K σ q hK3 hσ hKq hq2 h hh1 hh3 hdim g (hE.2 g hg)
    (congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hf⟩ ⟨g, hg⟩)) J hJ

end Main

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
