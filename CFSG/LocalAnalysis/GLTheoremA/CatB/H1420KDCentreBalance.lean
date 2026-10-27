module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.BorelTitsConstrained
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294LayerLieQ
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDCentre

open CFSG.Open

section Balance

variable {G : Type*} [Group G]

private theorem kdc_subgroupOf_inf_centralizer {N : Subgroup G} {x : G} (hxN : x ∈ N) :
    (N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf N =
      Subgroup.centralizer ({(⟨x, hxN⟩ : ↥N)} : Set ↥N) := by
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨z.2, congrArg Subtype.val h⟩

theorem glaPLayer_inf_centralizer_eq_bot_of_core_layer [Finite G] {p : ℕ} (hp : p.Prime)
    {N : Subgroup G} (hO : GLAPPrimeCoreOf p N = ⊥) (hE : GLAPLayer p N = ⊥) {x : G}
    (hxN : x ∈ N) (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    GLAPLayer p (N ⊓ Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO' : CFSG.pPrimeCore p ↥N = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 hO
  have hE' : CFSG.pLayer ↥N p = ⊥ := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq_map hp] at hE
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 hE
  have hnc : ∀ K : Subgroup ↥N, ¬ CFSG.IsComponent K := by
    intro K hK
    have hKne : K ≠ ⊥ := by
      haveI := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      exact (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
    have hKR : ¬ K ≤ CFSG.pPrimeCore p ↥N := by
      rw [hO', le_bot_iff]
      exact hKne
    have hKL : K ≤ CFSG.pLayer ↥N p :=
      le_sSup (CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le p hK hKR)
    rw [hE', le_bot_iff] at hKL
    exact hKne hKL
  have hlayer : CFSG.layer ↥N = ⊥ := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_eq_bot.2 fun K hK => absurd hK (hnc K)
  obtain ⟨n, hn⟩ := hx
  have hx' : ∃ n : ℕ, (⟨x, hxN⟩ : ↥N) ^ p ^ n = 1 := ⟨n, Subtype.ext (by simpa using hn)⟩
  have key := CFSG.ComponentClassification.LBalance.pLayer_centralizer_le_layer hO' hx'
    fun K hK => absurd hK (hnc K)
  rw [hlayer, le_bot_iff] at key
  rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq,
    ← CFSG.ComponentClassification.LBalance.pLayer_nested_map p
      (N ⊓ Subgroup.centralizer ({x} : Set G)) N inf_le_left,
    kdc_subgroupOf_inf_centralizer hxN,
    CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map, key, Subgroup.map_bot]

end Balance

section BorelTits

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (isChevOfChar_of_characteristic glaPPrimeCoreOf_eq_bot_of_constrained
    glaPLayer_eq_bot_of_constrained)

variable {S : Type} [Group S]

private theorem kdc_center_eq_bot (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) :
    Subgroup.center S = ⊥ := by
  haveI := hs
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center S := by
      rw [h]
      exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.1 ha b).symm hab

private theorem kdc_conj_injective (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h1 : a * g * a⁻¹ = g := by
    have := congrArg (fun φ : MulAut S => φ g) (MonoidHom.mem_ker.1 ha)
    simpa [MulAut.conj_apply] using this
  calc g * a = a * g * a⁻¹ * a := by rw [h1]
    _ = a * g := by group

private theorem kdc_mul_conj_mul_inv (d : MulAut S) (s : S) :
    d * MulAut.conj s * d⁻¹ = MulAut.conj (d s) := by
  ext x
  simp [MulAut.conj_apply]

private theorem kdc_centralizer_range_conj (hZ : Subgroup.center S = ⊥) :
    Subgroup.centralizer
      (((MulAut.conj : S →* MulAut S).range : Subgroup (MulAut S)) : Set (MulAut S)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  ext s
  have h1 : MulAut.conj s * φ = φ * MulAut.conj s :=
    Subgroup.mem_centralizer_iff.1 hφ _ ⟨s, rfl⟩
  have h2 : MulAut.conj (φ s) = MulAut.conj s := by
    rw [← kdc_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
  rw [MulAut.one_apply]
  exact kdc_conj_injective hZ h2

theorem glaPPrimeCoreOf_glaPLayer_normalizer_conj_eq_bot
    (hL : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQConstrained 3) [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1.characteristic = 3) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) {u : S}
    (hu : orderOf u = 3) :
    GLAPPrimeCoreOf 3 (Subgroup.normalizer
        ((Subgroup.zpowers (MulAut.conj u) : Subgroup (MulAut S)) : Set (MulAut S))) = ⊥ ∧
      GLAPLayer 3 (Subgroup.normalizer
        ((Subgroup.zpowers (MulAut.conj u) : Subgroup (MulAut S)) : Set (MulAut S))) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective
  have hZ := kdc_center_eq_bot hs hnab
  have hinj := kdc_conj_injective hZ
  have hIn : ((MulAut.conj : S →* MulAut S).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
  haveI := hs
  have hIs : IsSimpleGroup ↥(MulAut.conj : S →* MulAut S).range :=
    (MonoidHom.ofInjective hinj).symm.isSimpleGroup
  have hIab : ∃ a b : ↥(MulAut.conj : S →* MulAut S).range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨MonoidHom.ofInjective hinj a, MonoidHom.ofInjective hinj b, fun h =>
      hab (by simpa using congrArg (MonoidHom.ofInjective hinj).symm h)⟩
  have hIc := isChevOfChar_of_characteristic hd ((MonoidHom.ofInjective hinj).symm.trans e)
  have hQI : Subgroup.zpowers (MulAut.conj u) ≤ (MulAut.conj : S →* MulAut S).range :=
    Subgroup.zpowers_le.2 ⟨u, rfl⟩
  have hu1 : MulAut.conj u ≠ 1 := by
    intro h
    have h1 : u = 1 := hinj (h.trans (map_one (MulAut.conj : S →* MulAut S)).symm)
    rw [h1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hQ1 : Subgroup.zpowers (MulAut.conj u) ≠ ⊥ := fun h0 =>
    hu1 (Subgroup.zpowers_eq_bot.1 h0)
  have hQp : IsPGroup 3 ↥(Subgroup.zpowers (MulAut.conj u)) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, orderOf_injective _ hinj u, hu, pow_one]⟩
  have hc := hL (MulAut S) _ hIn hIs hIab hIc (kdc_centralizer_range_conj hZ) _ hQI hQ1 hQp
  refine ⟨glaPPrimeCoreOf_eq_bot_of_constrained Nat.prime_three hc,
    glaPLayer_eq_bot_of_constrained Nat.prime_three le_rfl ?_ hc⟩
  rw [Subgroup.subgroupOf_self]
  infer_instance

end BorelTits

end CFSG.LocalAnalysis.GLTheoremA.KDCentre
