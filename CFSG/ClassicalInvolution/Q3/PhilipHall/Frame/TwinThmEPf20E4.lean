module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf15Rigid

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitE4
open scoped commutatorElement

section E4t

@[expose] def E189E4Wt (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
    (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
    ∀ J ∈ CoreAssembly.conjClass K, ∀ t : M, IsUniqueInvolution J t → s * t = t * s →
      conjSub t K ≠ K → ∃ x : M, ∀ w ∈ conjSub x K ⊔ conjSub x (conjSub t K), w * (s * t) = (s * t) * w

@[expose] def E189E4ModelT : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (CFSG.Blueprint.LieModel M .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) →
      E189E4Wt M

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e189_twinE4_alt2' (hmodel : E189E4ModelT) (hΩ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hq8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2))
    (hgen : omegaGen Φ = ⊤) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hno : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → ¬ TightInO2 u) (hE : TwinE4 X)
    {K : Subgroup X} (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z)
    {J : Subgroup X} (hJ : J ∈ Φ) {t : X}
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∃ x : X, ∃ M' ∈ twinSet Φ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup X,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  obtain ⟨Q, hQ, f, hfs, hker, hM⟩ := hE
  set K' : Subgroup X := conjSub t K with hK'def
  have hK'Φ : K' ∈ Φ := hΩ.conjInvariant t K hK
  have hzK' : IsUniqueInvolution K' z := by
    have := hz.conj t
    rwa [show t * z * t⁻¹ = z by rw [← hzt]; group] at this
  have hK'tw : K' ∈ twinSet Φ K := ⟨hK'Φ, z, hz, hzK'⟩
  have hK'ne : K' ≠ K := hne
  have hN2 : IsPGroup 2 ↥f.ker := hker
  have hzN : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → u ∉ f.ker := fun J hJ u hu huN =>
    hno J hJ u hu ⟨f.ker, inferInstance, hN2, huN⟩
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => inf_eq_bot h2 hΩ hzN hJ
  have hNc : f.ker ≤ Subgroup.center X := center_of_meet hΩ h2 hgen hN2 hmeet
  have hc : CentQuotGen Φ f.ker := TwinDisc.ExitE4.centQuotGen hΩ h2 hNc hmeet
  set mk := QuotientGroup.mk' f.ker with hmk
  have hconj : ∀ g : X, ∀ L ∈ Φ, conjSub g L ∈ Φ := fun g L hL => hΩ.conjInvariant g L hL
  have hinj : ∀ L ∈ Φ, ∀ M ∈ Φ, L.map mk = M.map mk → L = M :=
    fun L hL M hM h => hc.eq_of_map L hL M hM h
  have hmem : ∀ M ∈ Φ, Set.InjOn mk (M : Set X) := by
    intro M hM a ha b hb hab
    have h1 : a⁻¹ * b ∈ f.ker := (QuotientGroup.eq).mp hab
    have h2' : a⁻¹ * b ∈ M ⊓ f.ker := ⟨M.mul_mem (M.inv_mem ha) hb, h1⟩
    rw [hmeet M hM, Subgroup.mem_bot] at h2'
    exact (inv_mul_eq_one.mp h2')
  let e : (X ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : CFSG.Blueprint.LieModel (X ⧸ f.ker) .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel (X ⧸ f.ker) .POmegaPlus 4 2 1 :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  have hnab := exists_noncomm hΩ h2 hK
  have hinvK : IsUniqueInvolution (K.map mk) (mk z) :=
    AscQuot.isUniqueInvolution_map_mk (hmeet K hK) hz
  have hinvK' : IsUniqueInvolution (K'.map mk) (mk z) :=
    AscQuot.isUniqueInvolution_map_mk (hmeet K' hK'tw.1) hzK'
  have hinvJ : IsUniqueInvolution (J.map mk) (mk t) :=
    AscQuot.isUniqueInvolution_map_mk (hmeet J hJ) ht
  have hq8K : Nonempty (↥(K.map mk) ≃* QuaternionGroup 2) := by
    obtain ⟨eK⟩ := hq8 K hK
    exact ⟨(AscQuot.quotRestrictEquiv (hmeet K hK)).symm.trans eK⟩
  have htw : ∀ c ∈ Subgroup.centralizer ({mk z} : Set (X ⧸ f.ker)),
      conjSub c (K.map mk) = K.map mk ∨
        ∀ x ∈ K.map mk, ∀ y ∈ conjSub c (K.map mk), x * y = y * x := by
    intro cb hcb
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective f.ker cb
    have hc' : mk c * mk z = mk z * mk c := Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hq : z⁻¹ * (c * z * c⁻¹) ∈ f.ker := by
      have h0 : mk (z⁻¹ * (c * z * c⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc', mul_inv_cancel_right, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have hcen : ∀ y : X, y * (z⁻¹ * (c * z * c⁻¹)) = (z⁻¹ * (c * z * c⁻¹)) * y :=
      Subgroup.mem_center_iff.mp (hNc hq)
    rcases twin_clause_central hΩ h2 hK hz hnab rfl hcen with h | h
    · left
      rw [← AscQuot.map_conjSub, h]
    · right
      rintro _ ⟨x, hx, rfl⟩ y hy
      rw [← AscQuot.map_conjSub] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, h x hx y' hy']
  have hK'ne' : K'.map mk ≠ K.map mk := fun h => hK'ne (hinj K' hK'tw.1 K hK h)
  have hcls : ∀ L ∈ Φ, L.map mk ∈ CoreAssembly.conjClass (K.map mk) := by
    intro L hL
    obtain ⟨g, rfl⟩ := htrans K hK L hL
    exact ⟨mk g, by rw [AscQuot.map_conjSub]⟩
  have hne' : conjSub (mk t) (K.map mk) ≠ K.map mk := by
    intro h
    apply hne
    refine hinj _ (hconj t K hK) K hK ?_
    rw [AscQuot.map_conjSub]
    exact h
  have hfin := hmodel (X ⧸ f.ker) hMq (K.map mk) (mk z) hq8K hinvK htw (J.map mk) (hcls J hJ) (mk t) hinvJ
    (by rw [← map_mul, ← map_mul, hzt]) hne'
  have hKt : K'.map mk = conjSub (mk t) (K.map mk) := by rw [hK'def, AscQuot.map_conjSub]
  obtain ⟨xb, hxb⟩ := hfin
  rw [← hKt] at hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective f.ker xb
  have hc1 : ∀ L ∈ Φ, (L = K ∨ L = K') → ∀ w ∈ conjSub x L, (z * t) * w = w * (z * t) := by
    intro L hL hLK w hw
    have hxL : conjSub x L ∈ Φ := hconj x L hL
    refine centralizes_of_image mk hconj hinj hmem hxL (a := z * t) ?_ w hw
    intro w' hw'
    have hmapw : mk w' ∈ conjSub (mk x) (K.map mk) ⊔ conjSub (mk x) (K'.map mk) := by
      rcases hLK with rfl | rfl
      · refine Subgroup.mem_sup_left ?_
        rw [← AscQuot.map_conjSub]
        exact Subgroup.mem_map_of_mem _ hw'
      · refine Subgroup.mem_sup_right ?_
        rw [← AscQuot.map_conjSub]
        exact Subgroup.mem_map_of_mem _ hw'
    have := hxb _ hmapw
    rw [map_mul]
    exact this.symm
  refine alt2_of_twin_centralizes hΩ h2 hK hz hK'tw hK'ne t (x := x) ?_
  intro w hw
  have hle : conjSub x K ⊔ conjSub x K' ≤ Subgroup.centralizer ({z * t} : Set X) := by
    refine sup_le (fun w hw => ?_) (fun w hw => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc1 K hK (Or.inl rfl) w hw).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc1 K' hK'tw.1 (Or.inr rfl) w hw).symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)


end E4t

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
