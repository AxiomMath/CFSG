module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7T
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CoreRows
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Transfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7S

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.Burgoyne.E2 CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p : ℕ} [Fact p.Prime]

theorem centModel_e7_twisted
    {f : ℕ} (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    {g : adjointGroup .E7 K} {a : Fin Tag.E7.rank → Kˣ}
    (hα : orderOf (MulAut.conj g * rootDiagAut .E7 K a) = 2)
    (hns : ∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) → ∀ ψ : MulAut (adjointGroup .E7 K),
      ψ * (MulAut.conj g * rootDiagAut .E7 K a) * ψ⁻¹ ≠
        rootDiagAut .E7 K (signMaskTuple .E7 K m)) :
    CentModel (fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a)) := by
  classical
  have hp : p.Prime := Fact.out
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  set L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨-, -, r, hr, hm, g₁, hg₁G, hconj, hcoc⟩ :=
    TwE7.exists_twisted_reduction hp2 hf hK L hα hns
  obtain ⟨hinj, -, -, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L
    (algebraMap K L)
  set R := fixedPointsIn (adjointGroup .E7 L) (frobTwistGL .E7 L p f 1) with hR
  set Ψ : adjointGroup .E7 K →* ModGL .E7 L :=
    (MulAut.conj g₁).toMonoidHom.comp (TwE7.embE7 L) with hΨ
  have hΨinj : Function.Injective Ψ :=
    (MulAut.conj g₁).injective.comp (hinj.comp Subtype.val_injective)
  have hH := TwE7.map_adjointGroup_eq_commutator L hp2 hK
  have hRR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hιH : ∀ c, TwE7.embE7 L c ∈ ⁅R, R⁆ := fun c => by
    rw [← hH]
    exact Subgroup.mem_map_of_mem _ c.2
  have hΨG : ∀ c, Ψ c ∈ adjointGroup .E7 L := fun c =>
    mul_mem (mul_mem hg₁G (mem_fixedPointsIn.1 (hRR (hιH c))).1) (inv_mem hg₁G)
  have hmemΨ : ∀ w, g₁⁻¹ * w * g₁ ∈ ⁅R, R⁆ → w ∈ Ψ.range := by
    intro w hw
    rw [← hH] at hw
    obtain ⟨c, hc, hcw⟩ := hw
    refine ⟨⟨c, hc⟩, ?_⟩
    change g₁ * baseChangeGL (algebraMap K L) c * g₁⁻¹ = w
    rw [hcw]
    group
  obtain ⟨D, -, u, -, hDe, hDχ, hDθ, hsub, hqs, hu, hCY, hYC⟩ := TwE7.exists_twisted_layer hp2
    hf hk hr (TwE7.e7Word2_1_mem_omegaWords hr hm) TwE7.e7Word2_1_ne_nil hg₁G hconj hcoc
  have hYΨ : (TwE7.twCent p L f (TwE7.liftElt (algebraMap K L) (g : ModGL .E7 K) a)).map
      (MulAut.conj g₁).toMonoidHom ≤ Ψ.range := by
    rintro _ ⟨y, hy, rfl⟩
    refine hmemΨ _ ?_
    change g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ ∈ _
    rw [show g₁⁻¹ * (g₁ * y * g₁⁻¹) * g₁ = y by group]
    exact (Subgroup.mem_inf.1 hy).1
  have hC'Ψ := hCY.trans hYΨ
  have htw : ∀ c, (MulAut.conj g * rootDiagAut .E7 K a) c = c ↔
      Ψ c ∈ (TwE7.twCent p L f (TwE7.liftElt (algebraMap K L) (g : ModGL .E7 K) a)).map
        (MulAut.conj g₁).toMonoidHom := by
    intro c
    have h := TwE7.map_fixedSubgroup_eq_twCent L hp2 hK g a
    constructor
    · intro hc
      refine ⟨TwE7.embE7 L c, ?_, rfl⟩
      rw [← h]
      exact ⟨c, hc, rfl⟩
    · rintro ⟨y, hy, hyc⟩
      rw [← h] at hy
      obtain ⟨c', hc', rfl⟩ := hy
      have : c' = c := hΨinj hyc
      rw [← this]
      exact hc'
  have hMG : torusGroup .E7 L ⊔ rootSpan .E7 L (kernelRoots (signMaskChar .E7 r.mask)) ≤
      adjointGroup .E7 L := sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _)
  have huG : u ∈ adjointGroup .E7 L := hMG hu
  set C' := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC'
  have hqC' : IsQuasisimple C' := LocalCores.isQuasisimple_of_mulEquiv
    (D.orbitGroup.equivMapOfInjective _ (MulAut.conj u).injective) hqs
  let eQ : C'.comap Ψ ≃* C' := ((C'.comap Ψ).equivMapOfInjective Ψ hΨinj).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hC'Ψ))
  have hC'norm : ∀ c, (MulAut.conj g * rootDiagAut .E7 K a) c = c →
      ∀ w ∈ C', Ψ c * w * (Ψ c)⁻¹ ∈ C' := by
    intro c hc w hw
    have h := Subgroup.mem_map_of_mem (MulAut.conj (Ψ c)).toMonoidHom hw
    rw [hYC (Ψ c) ((htw c).1 hc)] at h
    exact h
  set H := fixedSubgroup (MulAut.conj g * rootDiagAut .E7 K a) with hHdef
  have hQα : C'.comap Ψ ≤ H := fun c hc => (htw c).2 (hCY hc)
  have hQN : H ≤ normalizer ((C'.comap Ψ : Subgroup (adjointGroup .E7 K)) :
      Set (adjointGroup .E7 K)) := by
    intro c hc
    have hc' : (MulAut.conj g * rootDiagAut .E7 K a) c = c := hc
    rw [mem_normalizer_iff]
    intro q
    exact (TwE7.conj_mem_comap_iff (hC'norm c hc') (hC'norm c⁻¹ (by rw [map_inv, hc'])) q).symm
  have hQ : IsComponent ((C'.comap Ψ).subgroupOf H) :=
    ⟨(isQuasisimple_congr ((Subgroup.subgroupOfEquivOfLe hQα).trans eQ)).2 hqC',
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQα).2 hQN).isSubnormal⟩
  have hcC : ∀ y : H, (∀ s ∈ (C'.comap Ψ).subgroupOf H, s * y = y * s) →
      ∀ w ∈ D.orbitGroup, (u⁻¹ * Ψ y * u) * w = w * (u⁻¹ * Ψ y * u) := by
    intro y hy w hw
    obtain ⟨q, hq⟩ := hC'Ψ ⟨w, hw, rfl⟩
    have hq' : Ψ q ∈ C' := by
      rw [hq]
      exact ⟨w, hw, rfl⟩
    have h0 : q * (y : adjointGroup .E7 K) = (y : adjointGroup .E7 K) * q :=
      congrArg Subtype.val (hy ⟨q, hQα hq'⟩ (Subgroup.mem_subgroupOf.2 hq'))
    have h := congrArg Ψ h0
    rw [map_mul, map_mul, hq] at h
    change (u * w * u⁻¹) * Ψ y = Ψ y * (u * w * u⁻¹) at h
    calc u⁻¹ * Ψ y * u * w = u⁻¹ * (Ψ y * (u * w * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * w * u⁻¹) * Ψ y) * u := by rw [h]
      _ = w * (u⁻¹ * Ψ y * u) := by group
  have hG : ∀ y : H, u⁻¹ * Ψ y * u ∈ adjointGroup .E7 L := fun y =>
    mul_mem (mul_mem (inv_mem huG) (hΨG y)) huG
  obtain ⟨P, hd, huniq⟩ : ∃ P : (Fin (Tag.rank .E7) → Lˣ) → Prop,
      (∀ y : H, (∀ s ∈ (C'.comap Ψ).subgroupOf H, s * y = y * s) →
        ∃ b, u⁻¹ * Ψ y * u = rootDiagUnit .E7 b ∧ P b) ∧
      (∀ b b', P b → P b' → rootDiagUnit .E7 b * rootDiagUnit .E7 b = 1 →
        rootDiagUnit .E7 b' * rootDiagUnit .E7 b' = 1 → rootDiagUnit .E7 b ≠ 1 →
          rootDiagUnit .E7 b' ≠ 1 → rootDiagUnit .E7 b = rootDiagUnit .E7 b') := by
    have := hsub
    rcases hm with h2 | h3
    · refine ⟨fun b => ∀ j : Fin 7, j ≠ 1 → b (CatLeafProof.e7Node j) = 1, fun y hy =>
        eq_rootDiagUnit_of_commute_orbitGroup_two D (three_le_q D) (by rw [hDχ, h2]) hDθ (hG y)
          (hcC y hy), fun b b' hb hb' => ?_⟩
      have hconv : ∀ m : Fin (Tag.rank .E7) → Lˣ,
          (∀ j : Fin 7, j ≠ 1 → m (CatLeafProof.e7Node j) = 1) →
            ∀ j, j ≠ CatLeafProof.e7Node 1 → m j = 1 := fun m hm' j hj => by
        obtain ⟨j', rfl⟩ : ∃ j' : Fin 7, CatLeafProof.e7Node j' = j := ⟨j, rfl⟩
        exact hm' j' fun h => hj (by rw [h])
      exact rootDiagUnit_eq_of_single (hconv b hb) (hconv b' hb')
    · refine ⟨fun b => (∀ j : Fin 7, 2 ≤ j.val → b (CatLeafProof.e7Node j) = 1) ∧
        b (CatLeafProof.e7Node 0) * b (CatLeafProof.e7Node 1) = 1, fun y hy => ?_,
        fun b b' hb hb' => rootDiagUnit_eq_of_pair_e7 hb.1 hb.2 hb'.1 hb'.2⟩
      obtain ⟨b, hb, hb2, hb01⟩ := TwE7.eq_of_commute_orbitGroup_three D (three_le_q D)
        (by rw [hDχ, h3]) hDθ (hG y) (hcC y hy)
      exact ⟨b, hb, hb2, hb01⟩
  have hback : ∀ (y : H) (b : Fin (Tag.rank .E7) → Lˣ), u⁻¹ * Ψ y * u = rootDiagUnit .E7 b →
      Ψ y = u * rootDiagUnit .E7 b * u⁻¹ := fun y b hb => by
    rw [← hb]
    group
  refine ⟨Unit, fun _ => (C'.comap Ψ).subgroupOf H, fun _ => hQ,
    fun _ => Burgoyne.even_card_of_isQuasisimple hQ.1, fun y y' hy hy' => ?_,
    fun y y' hy hy' hy2 hy2' hy1 hy1' => ?_⟩
  · obtain ⟨b, hb, -⟩ := hd y (hy ())
    obtain ⟨b', hb', -⟩ := hd y' (hy' ())
    refine Subtype.ext (hΨinj ?_)
    change Ψ ((y : adjointGroup .E7 K) * y') = Ψ ((y' : adjointGroup .E7 K) * y)
    rw [map_mul, map_mul, hback y b hb, hback y' b' hb']
    have hc : rootDiagUnit .E7 b * rootDiagUnit .E7 b' =
        rootDiagUnit .E7 b' * rootDiagUnit .E7 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    calc u * rootDiagUnit .E7 b * u⁻¹ * (u * rootDiagUnit .E7 b' * u⁻¹) =
        u * (rootDiagUnit .E7 b * rootDiagUnit .E7 b') * u⁻¹ := by group
      _ = u * (rootDiagUnit .E7 b' * rootDiagUnit .E7 b) * u⁻¹ := by rw [hc]
      _ = u * rootDiagUnit .E7 b' * u⁻¹ * (u * rootDiagUnit .E7 b * u⁻¹) := by group
  · obtain ⟨b, hb, hPb⟩ := hd y (hy ())
    obtain ⟨b', hb', hPb'⟩ := hd y' (hy' ())
    have hsq : ∀ (x : H) (c : Fin (Tag.rank .E7) → Lˣ), u⁻¹ * Ψ x * u = rootDiagUnit .E7 c →
        x * x = 1 → rootDiagUnit .E7 c * rootDiagUnit .E7 c = 1 := by
      intro x c hc hx
      rw [← hc]
      have hΨx : Ψ (x : adjointGroup .E7 K) * Ψ x = 1 := by
        rw [← map_mul]
        exact (congrArg (fun t : H => Ψ (t : adjointGroup .E7 K)) hx).trans (map_one Ψ)
      calc u⁻¹ * Ψ x * u * (u⁻¹ * Ψ x * u) = u⁻¹ * (Ψ x * Ψ x) * u := by group
        _ = 1 := by rw [hΨx]; group
    have hne : ∀ (x : H) (c : Fin (Tag.rank .E7) → Lˣ), u⁻¹ * Ψ x * u = rootDiagUnit .E7 c →
        x ≠ 1 → rootDiagUnit .E7 c ≠ 1 := by
      intro x c hc hx h1
      apply hx
      have hΨx : Ψ (x : adjointGroup .E7 K) = 1 := by
        rw [hback x c hc, h1]
        group
      exact Subtype.ext (hΨinj (hΨx.trans (map_one Ψ).symm))
    have h := huniq b b' hPb hPb' (hsq y b hb hy2) (hsq y' b' hb' hy2') (hne y b hb hy1)
      (hne y' b' hb' hy1')
    refine Subtype.ext (hΨinj ?_)
    rw [hback y b hb, hback y' b' hb', h]

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
