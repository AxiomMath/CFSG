module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
public import CFSG.Sporadic.Bridge.ONSurj
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.AGLEmbedding CFSG.Blueprint
open scoped commutatorElement

theorem sylow_hat_on {X Y : Type} [Group X] [Finite X] [Group Y]
    (hD : AbelianSylowDatum Y 3) (hcardY : Nat.card Y = 460815505920)
    (hperf : commutator X = ⊤)
    (hZ : Nat.card (Subgroup.center X) = 3) (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center X) (P : Sylow 3 X) :
    Nat.card (P : Subgroup X) = 3 ^ 5 ∧ (∀ g ∈ (P : Subgroup X), g ^ 3 = 1) ∧
      (∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), ⁅x, y⁆ ∈ Subgroup.center X) ∧
      (∀ x ∈ (P : Subgroup X), (∀ g ∈ (P : Subgroup X), g * x = x * g) →
        x ∈ Subgroup.center X) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Group.IsPerfect X := ⟨hperf⟩
  have hZ1 : Subgroup.center X ≠ ⊥ := by
    intro h
    rw [h] at hZ
    simp at hZ
  have hZp : IsPGroup 3 (Subgroup.center X) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have : Fact (Nat.Prime (Nat.card (Subgroup.center X))) := ⟨by rw [hZ]; exact hp⟩
  have hZc : IsCyclic (Subgroup.center X) := isCyclic_of_prime_card rfl
  have hZle : Subgroup.center X ≤ (P : Subgroup X) := IsPGroup.le_sylow_of_normal hZp P
  have hcardX : Nat.card X = 460815505920 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hker, hZ,
      hcardY]
  have hcardP : Nat.card (P : Subgroup X) = 3 ^ 5 := by
    rw [Sylow.card_eq_multiplicity, hcardX,
      show (460815505920 * 3 : ℕ) = 3 ^ 5 * 5689080320 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  obtain ⟨D, hn, hF, hN, hidx⟩ := hD
  have : Finite Y := Finite.of_surjective π hπ
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (D.card_span hp)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q (P.mapSurjective hπ)
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  set D' := D.map (MulAut.conj g).toMonoidHom hinj with hD'
  have hspan : D'.span ≤ (P : Subgroup X).map π := by
    have h2 := congrArg (fun S : Sylow 3 Y => (S : Subgroup Y)) hg
    simp only [Sylow.coe_mapSurjective] at h2
    rw [hD', ModuleSpec.map_span, ← h2, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hQ
  have hle : D'.span.comap π ≤ (P : Subgroup X) := by
    calc D'.span.comap π ≤ ((P : Subgroup X).map π).comap π := Subgroup.comap_mono hspan
      _ = (P : Subgroup X) ⊔ π.ker := Subgroup.comap_map_eq _ _
      _ = (P : Subgroup X) := by rw [hker, sup_eq_left]; exact hZle
  have hidx' : ¬ 3 ∣ (D'.span.comap π).index := by
    rwa [Subgroup.index_comap_of_surjective _ hπ, hD', ModuleSpec.map_span,
      Subgroup.index_map_of_bijective (MulAut.conj g).bijective]
  have heq : D'.span.comap π = (P : Subgroup X) :=
    (((P.isPGroup'.to_le hle).toSylow hidx').3 P.isPGroup' hle).symm
  have hN' : D'.Nondeg := hN
  have hF' : D'.NoFun := hF
  have hn' : D'.n ≤ 4 := hn
  have hc : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), ⁅x, y⁆ ∈ Subgroup.center X := by
    rw [← heq]
    exact fun x hx y hy => D'.commutator_mem_center π hker hx hy
  have hcen := D'.commute_or_mem_center_of_nondeg π hp (by norm_num) hπ hker hZp hZc hN'
  rw [heq] at hcen
  have hnc : ¬ ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x := by
    intro h
    apply hZ1
    have hZT' : Subgroup.center X ≤ ⁅(P : Subgroup X), (P : Subgroup X)⁆ := fun z hz => by
      obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
      exact center_le_commutator_of_isPerfect P hz ⟨k, congrArg Subtype.val hk⟩
    have hbot : ⁅(P : Subgroup X), (P : Subgroup X)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => h y hy x hx
    exact le_bot_iff.mp (hbot ▸ hZT')
  have hZT := hcen.resolve_left hnc
  refine ⟨hcardP, ?_, hc, fun x hx hxc => hZT x hx fun y hy => (hxc y hy).symm⟩
  obtain ⟨hexp, -⟩ := forall_pow_eq_one_and_card_le_of_cover hp hZ1 hZp hZc P hn'
    (by rw [← heq]; exact D'.card_comap π hp hπ hker)
    hc
    (by rw [← heq]; exact fun x hx y hy => D'.commutator_pow_eq_one π hker hx hy)
    (Or.inr hZT)
    (by rw [← heq]; exact D'.exists_pow_eq_pow_of_noFun π hp (by norm_num) hπ hker hZp hZc hF')
  exact hexp

theorem exists_surj_ker_center {X Y T : Type} [Group X] [Group Y] [Group T] (b : Y ≃* T)
    (e : X ⧸ Subgroup.center X ≃* T) :
    ∃ π : X →* Y, Function.Surjective π ∧ π.ker = Subgroup.center X := by
  let π : X →* Y :=
    b.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
  have hπ : ∀ x : X, π x = b.symm (e (QuotientGroup.mk x)) := fun _ => rfl
  refine ⟨π, fun y => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := e.surjective (b y)
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, by rw [hπ, hx, hq, MulEquiv.symm_apply_apply]⟩
  · ext x
    rw [MonoidHom.mem_ker, hπ, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]

theorem inputONSylow_holds :
    LocalBalance.Lemma59Ns.InputONSylow := by
  intro X _ _ hX P
  obtain ⟨hperf, hZ, ⟨e⟩⟩ := hX
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  have hD : AbelianSylowDatum (NativeSporadic.Carrier .ONan) 3 := abelianSylowDatum_ON_three
  have hcard : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  obtain ⟨π, hπ, hker⟩ := exists_surj_ker_center b' e
  exact sylow_hat_on hD hcard hperf hZ π hπ hker P

end CFSG.HardMathSupport.Solomon.Coordinator
