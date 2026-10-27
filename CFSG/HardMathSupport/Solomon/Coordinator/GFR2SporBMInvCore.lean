module

import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInv
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvGroup
import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns CFSG.HardMathSupport.Dickson.Sec6.BM

open scoped commutatorElement

theorem simple_normalizes_of_commuting_conj_dvd {G : Type} [Group G] [Finite G]
    {H J : Subgroup G} (hH : IsSimpleGroup ↥H) (m : ℕ)
    (hcomm : ∀ g₁ ∈ H, ∀ g₂ ∈ H, J.map (MulAut.conj g₁).toMonoidHom ≠
      J.map (MulAut.conj g₂).toMonoidHom → ∀ a ∈ J.map (MulAut.conj g₁).toMonoidHom,
      ∀ b ∈ J.map (MulAut.conj g₂).toMonoidHom, a * b = b * a)
    (hJ : m * Nat.card ↥(Subgroup.center ↥J) ≤ Nat.card ↥J)
    (hk : ∀ k : ℕ, m ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial) :
    ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨S, hS⟩ : ∃ S : Finset (Subgroup G),
      ∀ A, A ∈ S ↔ ∃ g : ↥H, J.map (MulAut.conj (g : G)).toMonoidHom = A :=
    ⟨Finset.univ.image fun g : ↥H => J.map (MulAut.conj (g : G)).toMonoidHom, fun A => by simp⟩
  have hpow : m ^ S.card ≤ Nat.card G := by
    refine (pow_card_le_card_iSup_of_commuting m S ?_ ?_).trans (Subgroup.card_le_card_group _)
    · intro A hA B hB hne a ha b hb
      obtain ⟨g₁, rfl⟩ := (hS A).1 hA
      obtain ⟨g₂, rfl⟩ := (hS B).1 hB
      exact hcomm g₁ g₁.2 g₂ g₂.2 hne a ha b hb
    · intro A hA
      obtain ⟨g, rfl⟩ := (hS A).1 hA
      rw [card_map_conj, card_center_map_conj]
      exact hJ
  letI : MulAction ↥H ↥S :=
    { smul := fun h A => ⟨A.1.map (MulAut.conj (h : G)).toMonoidHom, by
        obtain ⟨g, hg⟩ := (hS A.1).1 A.2
        exact (hS _).2 ⟨h * g, by rw [← hg]; exact map_conj_mul J h g⟩⟩
      one_smul := fun A => Subtype.ext (map_conj_one A.1)
      mul_smul := fun h₁ h₂ A => Subtype.ext (map_conj_mul A.1 h₁ h₂) }
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hH (MulAction.toPermHom ↥H ↥S).ker _
    with hbot | htop
  · have hdvd := Subgroup.card_dvd_of_injective _ ((MonoidHom.ker_eq_bot_iff _).1 hbot)
    rw [Nat.card_perm, Nat.card_eq_finsetCard] at hdvd
    exact absurd hdvd (hk S.card hpow)
  · intro h hh j hj
    have hJS : J ∈ S := (hS J).2 ⟨1, map_conj_one J⟩
    have hker : (⟨h, hh⟩ : ↥H) ∈ (MulAction.toPermHom ↥H ↥S).ker := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix : MulAction.toPermHom ↥H ↥S ⟨h, hh⟩ ⟨J, hJS⟩ = ⟨J, hJS⟩ :=
      congrArg (fun σ : Equiv.Perm ↥S => σ ⟨J, hJS⟩) (MonoidHom.mem_ker.1 hker)
    have hJ' : J.map (MulAut.conj h).toMonoidHom = J := congrArg Subtype.val hfix
    have hmem : h * j * h⁻¹ ∈ J.map (MulAut.conj h).toMonoidHom := by
      rw [mem_map_conj_iff, show h⁻¹ * (h * j * h⁻¹) * h = j by group]
      exact hj
    rwa [hJ'] at hmem

theorem false_of_inverted_component {G : Type} [Group G] [Finite G] {s α : G}
    (hα : α * α = 1) (hinv : α * s * α⁻¹ = s⁻¹)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥)
    {H : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hHα : ∀ h ∈ H, α * h = h * α) (hHs : ∀ h ∈ H, s * h = h * s)
    (hHn : ∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H)
    (hCQ : ∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1)
    (m : ℕ) (hbig : ∀ k : ℕ, m ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial)
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J)
    (hZ : m * Nat.card ↥(Subgroup.center ↥J) ≤ Nat.card ↥J)
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) (hdvd : ¬ Nat.card ↥H ∣ Nat.card ↥J ^ 2) : False := by
  set C := Subgroup.centralizer ({s} : Set G) with hCdef
  have hHC : ∀ g ∈ H, g ∈ C := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hHs g hg
  have hconjComp : ∀ g ∈ H, GLAPComponent 3 C (J.map (MulAut.conj g).toMonoidHom) := by
    intro g hg
    rw [map_conj_eq_gLBConj_inv]
    exact glaPComponent_gLBConj_of_mem hJ (C.inv_mem (hHC g hg))
  have hcomm_of_ne : ∀ {A B : Subgroup G}, GLAPComponent 3 C A → GLAPComponent 3 C B → A ≠ B →
      ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A B hA hB hne a ha b hb
    have hc := commutator_le_gLAPPrimeCore_of_ne (by norm_num) hA hB hne
    rw [hO] at hc
    have h1 : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := hc (Subgroup.commutator_mem_commutator ha hb)
    exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 h1)
  have hHJ : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J :=
    simple_normalizes_of_commuting_conj_dvd hH m
      (fun g₁ hg₁ g₂ hg₂ hne => hcomm_of_ne (hconjComp g₁ hg₁) (hconjComp g₂ hg₂) hne) hZ hbig
  have hcommα : J.map (MulAut.conj α).toMonoidHom = J ∨
      ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj α).toMonoidHom, a * b = b * a := by
    by_cases heq : J.map (MulAut.conj α).toMonoidHom = J
    · exact Or.inl heq
    · exact Or.inr (hcomm_of_ne hJ (glaPComponent_conj_inverter hα hinv hJ) (Ne.symm heq))
  have hJs : ∀ j ∈ J, s * j = j * s := fun j hj =>
    Subgroup.mem_centralizer_iff.1 (hJ.1 hj) s (Set.mem_singleton s)
  exact hdvd (lemmaInv_core hα hinv hH hHα hHn hCQ hJs hHJ hcommα hnab)

theorem glaPComponent_of_isComponentOf_of_core_eq_bot {G : Type} [Group G] [Finite G]
    {C J : Subgroup G} (hC : GLAPPrimeCoreOf 3 C = ⊥) (hJ : IsComponentOf J C) :
    GLAPComponent 3 C J := by
  have hcore : GLAPPrimeCore 3 ↥C = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hC
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  refine ⟨hJ.1, hJ.2.1, ⟨le_top, barX_isSubnormal_top 3 hJ.2.1, ?_⟩, ?_⟩
  · let e : ↥J ≃* ↥(barX 3 C J) :=
      (Subgroup.subgroupOfEquivOfLe hJ.1).symm.trans (Subgroup.equivMapOfInjective _ _ hinj)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hJ.2.2
  · intro J' hlt _ heq
    have h1 : J'.subgroupOf C = J.subgroupOf C := Subgroup.map_injective hinj heq
    have h2 : J' = J := by
      have := congrArg (Subgroup.map C.subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le (hlt.le.trans hJ.1),
        Subgroup.map_subgroupOf_eq_of_le hJ.1] at this
    exact hlt.ne h2

theorem bmInv_map_centralizer_singleton {S S' : Type*} [Group S] [Group S'] (φ : S ≃* S')
    (s : S) : (Subgroup.centralizer ({s} : Set S)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ s} : Set S') := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨φ.symm y, φ.injective ?_, φ.apply_symm_apply y⟩
    simpa [map_mul] using hy

theorem bmInv_isComponentOf_map {S S' : Type*} [Group S] [Group S'] (φ : S ≃* S') {s : S}
    {K : Subgroup S} (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set S))) :
    IsComponentOf (K.map φ.toMonoidHom) (Subgroup.centralizer ({φ s} : Set S')) := by
  rw [← bmInv_map_centralizer_singleton φ s]
  exact ⟨Subgroup.map_mono hK.1, hK.2.1.map φ.toMonoidHom,
    CFSG.Open.IsQuasisimple.of_mulEquiv (K.equivMapOfInjective _ φ.injective).symm hK.2.2⟩

theorem bmInv_hat_of_mulEquiv {X X' Q : Type*} [Group X] [Group X'] [Group Q] (e : X ≃* X')
    (h : commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* Q)) :
    commutator X' = ⊤ ∧ Nat.card (Subgroup.center X') = 3 ∧
      Nonempty ((X' ⧸ Subgroup.center X') ≃* Q) := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

theorem exists_noncomm_of_perfect_center_card_three {X : Type*} [Group X]
    (hperf : commutator X = ⊤) (hZ : Nat.card (Subgroup.center X) = 3) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hbot : commutator X = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [commutator]
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcon x y)
  have hZtop : Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact hcon y x
  rw [hZtop, Subgroup.card_top] at hZ
  have hsub : Subsingleton X := by
    refine ⟨fun a b => ?_⟩
    have h : ∀ z : X, z = 1 := fun z => by
      have hz : z ∈ commutator X := hperf ▸ Subgroup.mem_top z
      rw [hbot] at hz
      exact hz
    rw [h a, h b]
  have : Nat.card X = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
