module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdClasses
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4LocalOne
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Std

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem isComponentOf_of_glaPComponent_of_core_eq_bot {G : Type*} [Group G] {p : ℕ}
    {X L : Subgroup G} (hX : GLAPPrimeCoreOf p X = ⊥) (hL : GLAPComponent p X L) :
    IsComponentOf L X := by
  have hcore : GLAPPrimeCore p ↥X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hX
  refine ⟨hL.1, hL.2.1, ?_⟩
  have hq := hL.2.2.1.2.2
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective (L.subgroupOf X) _ hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hL.1)) hq

section Model


theorem f4EightCompModel (hCore : F4LocalOneAux.F4EightOPrimeCore)
    (s : ↥(adjointGroup Tag.F4 (GaloisField 2 3))) (hs : orderOf s = 3) :
    (∀ J : Subgroup ↥(adjointGroup Tag.F4 (GaloisField 2 3)),
      GLAPComponent 3 (fixSubgroup (MulAut.conj s)) J →
        CFSG.Open.IsQuasisimple ↥J ∧ IsLieQuot ↥J KSF4Out.F4EightCompIndex) ∧
    ∀ J₁ J₂ J₃ : Subgroup ↥(adjointGroup Tag.F4 (GaloisField 2 3)),
      GLAPComponent 3 (fixSubgroup (MulAut.conj s)) J₁ →
      GLAPComponent 3 (fixSubgroup (MulAut.conj s)) J₂ →
      GLAPComponent 3 (fixSubgroup (MulAut.conj s)) J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃ := by
  classical
  have hcardK : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have hpK : ¬ 3 ∣ Nat.card (GaloisField 2 3) := by rw [hcardK]; norm_num
  obtain ⟨p₀, S, a, ι, hq, hT, hap, h1, hinj, hrange, -, hconj, hTame⟩ :=
    exists_langSetup_F4_of_orderOf_eq_three hpK s hs
  have hq8 : S.D.q = 8 := by rw [hq, hcardK]; norm_num
  have hpL : ((3 : ℕ) : AlgebraicClosure (GaloisField 2 3)) ≠ 0 :=
    LieSemisimple.natCast_ne_zero_algebraicClosure Nat.prime_three hpK
  haveI : CharP (AlgebraicClosure (GaloisField 2 3)) 2 := inferInstance
  obtain ⟨hgood, hcnt⟩ := f4_classes_good S hT hap h1 hq8 hpL hTame
  have hC : GLAPPrimeCoreOf 3 (fixSubgroup (MulAut.conj s)) = ⊥ := by
    rw [fixSubgroup_conj_eq]
    exact hCore (GaloisField 2 3) hcardK s hs
  have key : ∀ J, GLAPComponent 3 (fixSubgroup (MulAut.conj s)) J →
      ∃ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := fun J hJ =>
    LieComp.components_of_langSetup S Nat.prime_three ι hinj hrange (MulAut.conj s) hconj hT hap h1
      hTame (isComponentOf_of_glaPComponent_of_core_eq_bot hC hJ)
  refine ⟨fun J hJ => ?_, fun J₁ J₂ J₃ h₁ h₂ h₃ => ?_⟩
  · obtain ⟨i, -, hJi⟩ := key J hJ
    let e : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      (Subgroup.equivMapOfInjective J ι hinj).trans (MulEquiv.subgroupCongr hJi)
    exact ⟨(hgood i).1.of_mulEquiv e, Bal209F4Aux.isLieQuot_mulEquiv e.symm (hgood i).2⟩
  · obtain ⟨i₁, -, h1'⟩ := key J₁ h₁
    obtain ⟨i₂, -, h2'⟩ := key J₂ h₂
    obtain ⟨i₃, -, h3'⟩ := key J₃ h₃
    have hmap : ∀ {A B : Subgroup ↥(adjointGroup Tag.F4 (GaloisField 2 3))}, A.map ι = B.map ι →
        A = B := fun h => Subgroup.map_injective hinj h
    rcases hcnt i₁ i₂ i₃ with h | h | h
    · exact Or.inl (hmap (by rw [h1', h2', h]))
    · exact Or.inr (Or.inl (hmap (by rw [h1', h3', h])))
    · exact Or.inr (Or.inr (hmap (by rw [h2', h3', h])))

end Model

@[expose] def F4IsoStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → IsLieQuot Y IsF4EightIndex →
    Subgroup.center Y = ⊥ ∧ Nonempty (Y ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 3)))

theorem congr_conj_eq {S T : Type*} [Group S] [Group T] (e : S ≃* T) (x : S) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

section Transfer


theorem f4EightClass_of_core_iso (hCore : F4LocalOneAux.F4EightOPrimeCore)
    (hIso : F4IsoStatement) : KSF4Out.F4EightClass := by
  classical
  intro X _ _ K a hK hLie haN ha3 haC hinn
  obtain ⟨hZ, ⟨e⟩⟩ := hIso ↥K hK.2.2 hLie
  obtain ⟨k, hkK, hkc⟩ := hinn
  let kk : ↥K := ⟨k, hkK⟩
  have hac : a = k * (k⁻¹ * a) := by group
  have hα : K.normalizerMonoidHom ⟨a, haN⟩ = MulAut.conj kk := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have h1 : (K.normalizerMonoidHom ⟨a, haN⟩ y : X) = a * (y : X) * a⁻¹ := rfl
    have h2 : (MulAut.conj kk y : X) = k * (y : X) * k⁻¹ := rfl
    rw [h1, h2]
    have hcy : (k⁻¹ * a) * (y : X) = (y : X) * (k⁻¹ * a) :=
      (Subgroup.mem_centralizer_iff.1 hkc (y : X) y.2).symm
    calc a * (y : X) * a⁻¹ = (k * (k⁻¹ * a)) * (y : X) * (k * (k⁻¹ * a))⁻¹ := by rw [← hac]
      _ = k * ((k⁻¹ * a) * (y : X)) * (k⁻¹ * a)⁻¹ * k⁻¹ := by group
      _ = k * ((y : X) * (k⁻¹ * a)) * (k⁻¹ * a)⁻¹ * k⁻¹ := by rw [hcy]
      _ = k * (y : X) * k⁻¹ := by group
  set s := e kk with hsdef
  have hk1 : kk ≠ 1 := by
    intro h
    apply haC
    have hk1' : k = 1 := congrArg Subtype.val h
    have h' : k⁻¹ * a = a := by rw [hk1']; simp
    rw [← h']
    exact hkc
  have hkk3 : kk ^ 3 = 1 := by
    have hcc : ∀ y ∈ K, y * (k⁻¹ * a) = (k⁻¹ * a) * y := fun y hy =>
      Subgroup.mem_centralizer_iff.1 hkc y hy
    have hk3c : k ^ 3 * (k⁻¹ * a) ^ 3 = 1 := by
      have h1 : (k * (k⁻¹ * a)) ^ 3 = 1 := by rw [← hac]; exact ha3
      rwa [Commute.mul_pow (hcc k hkK)] at h1
    have hk3C : k ^ 3 ∈ Subgroup.centralizer (K : Set X) := by
      have hinv : k ^ 3 = ((k⁻¹ * a) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hk3c
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hinv]
      exact ((show Commute y (k⁻¹ * a) from hcc y hy).pow_right 3).inv_right.eq
    have hmem : kk ^ 3 ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hk3C (y : X) y.2
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hs3 : orderOf s = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [hsdef, ← map_pow, hkk3, map_one]
    · intro h
      exact hk1 (e.injective (by rw [← hsdef, h, map_one]))
  have htrans : ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      GLAPComponent 3 (fixSubgroup (MulAut.conj s)) ((J.subgroupOf K).map e.toMonoidHom) := by
    intro J hJ
    have h1 := CFSG.HardMathSupport.Dickson.I271.glaPComponent_fixSubgroup Nat.prime_three haN hJ
    rw [hα] at h1
    have h2 := glaPComponent_map_equiv e h1
    rwa [← CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr e (MulAut.conj kk),
      congr_conj_eq e kk] at h2
  obtain ⟨hgood, hcnt⟩ := f4EightCompModel hCore s hs3
  refine ⟨fun J hJ => ?_, fun J₁ J₂ J₃ h₁ h₂ h₃ => ?_⟩
  · have hJK : J ≤ K := hJ.1.trans inf_le_left
    obtain ⟨hq', hL'⟩ := hgood _ (htrans J hJ)
    let eJ : ↥J ≃* ↥((J.subgroupOf K).map e.toMonoidHom) :=
      (Subgroup.subgroupOfEquivOfLe hJK).symm.trans
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)
    exact ⟨CFSG.Open.IsQuasisimple.of_mulEquiv eJ hq', Bal209F4Aux.isLieQuot_mulEquiv eJ.symm hL'⟩
  · have hK1 : ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        J ≤ K := fun J hJ => hJ.1.trans inf_le_left
    have hinj : ∀ {A B : Subgroup X}, A ≤ K → B ≤ K →
        (A.subgroupOf K).map e.toMonoidHom = (B.subgroupOf K).map e.toMonoidHom → A = B := by
      intro A B hA hB h
      have h' := Subgroup.map_injective e.injective h
      have := (Subgroup.subgroupOf_inj).1 h'
      rwa [inf_of_le_left hA, inf_of_le_left hB] at this
    rcases hcnt _ _ _ (htrans J₁ h₁) (htrans J₂ h₂) (htrans J₃ h₃) with h | h | h
    · exact Or.inl (hinj (hK1 J₁ h₁) (hK1 J₂ h₂) h)
    · exact Or.inr (Or.inl (hinj (hK1 J₁ h₁) (hK1 J₃ h₃) h))
    · exact Or.inr (Or.inr (hinj (hK1 J₂ h₂) (hK1 J₃ h₃) h))

end Transfer

end KSF4Std

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
