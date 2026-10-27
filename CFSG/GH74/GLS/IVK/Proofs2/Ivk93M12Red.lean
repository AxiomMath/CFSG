module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93KindM12
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Shape
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Cls
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Lift
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
  CFSG.Blueprint

@[expose] def Ivk93M12J : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X), orderOf x = 2 → x ∈ generalizedFitting X →
    IsSimpleGroup ↥(generalizedFitting X) → (∃ a b : ↥(generalizedFitting X), a * b ≠ b * a) →
    GHList ↥(generalizedFitting X) →
    (∃ T : Sylow 2 X, ∀ t ∈ (T : Subgroup X), t * x = x * t) →
    ∀ (P : Type) [Group P] [Finite P] (zc : P), BarShape P zc →
      ∀ ρ : ↥(centralizer ({x} : Set X)) →* P, Function.Surjective ρ →
        (∀ y ∈ ρ.ker, Odd (orderOf y)) →
        ρ ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = zc →
          NativeSporadic.IsSporadic ↥(generalizedFitting X) .M12

theorem factorization_95040 : (95040 : ℕ).factorization 2 = 6 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have h : (95040 : ℕ) = 2 ^ 6 * 1485 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem card_S_m12 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.m12 S) : Nat.card ↥S = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hT'⟩ := exists_sylow_barIn hctx (le_refl (Cen z))
  have h1 := card_barIn_S hctx (le_refl (Cen z))
  rw [← hT'] at h1
  have h2 := Sylow.card_eq_multiplicity T'
  have hP : Nat.card (HBar (Cen z)) = 192 := (barShape_of_ctx hctx).card_eq
  rw [hP] at h2
  have h3 : (192 : ℕ).factorization 2 = 6 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    have h : (192 : ℕ) = 2 ^ 6 * 3 := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [h3] at h2
  rw [← h1, h2]
  norm_num


theorem ivk93KindM12_of_J
    (hJ : Ivk93M12J) : Ivk93KindM12 := by
  intro G _ _ z S hctx H hne hCH hV hs hn hPerf h2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hzH : z ∈ H := hCH (mem_Cen_self z)
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  have hzbT : mkH H ⟨z, hzH⟩ ∈ (T : Subgroup (HBar H)) := hT ▸ zbar_mem_barIn hctx hCH
  have hTc : ∀ t ∈ (T : Subgroup (HBar H)), t * mkH H ⟨z, hzH⟩ = mkH H ⟨z, hzH⟩ * t :=
    fun t ht => zbar_comm_barIn hctx hCH (hT ▸ ht)
  have hzb2 : orderOf (mkH H ⟨z, hzH⟩) = 2 := orderOf_mk_eq_two H hzH2
  have hcen := centralizer_mk_eq H hz2 hzH
  let e : ↥(centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H))) ≃* ↥(barIn H (Cen z)) :=
    MulEquiv.subgroupCongr hcen
  let ρ : ↥(centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H))) →* CentralizerBar z :=
    (cenToBar H hCH).comp e.toMonoidHom
  have hρsurj : Function.Surjective ρ := (cenToBar_surjective H hCH).comp e.surjective
  have hρodd : ∀ y ∈ ρ.ker, Odd (orderOf y) := by
    intro y hy
    have h1 := odd_orderOf_of_cenToBar_eq_one H hCH (e y) hy
    rwa [MulEquiv.orderOf_eq] at h1
  have hρx : ρ ⟨mkH H ⟨z, hzH⟩, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ =
      toBar z ⟨z, mem_Cen_self z⟩ := by
    have := cenToBar_cenMk H hCH ⟨z, mem_Cen_self z⟩
    exact this
  have hbar := barShape_of_ctx hctx
  have hzbJ : mkH H ⟨z, hzH⟩ ∈ generalizedFitting (HBar H) :=
    mem_fitting_of_barShape hzb2 hs hn T hTc hbar ρ hρsurj hρodd hρx
  have hGH := ghList_J hctx hne hs hn
  have hM12 := hJ (HBar H) (mkH H ⟨z, hzH⟩) hzb2 hzbJ hs hn hGH ⟨T, hTc⟩ _ _ hbar ρ hρsurj
    hρodd hρx
  obtain ⟨eJ⟩ := hM12
  have hJnorm : (generalizedFitting (HBar H)).Normal :=
    LocalCores.generalized_fitting_characteristic.2
  have hJcard : Nat.card ↥(generalizedFitting (HBar H)) = 95040 := by
    rw [Nat.card_congr eJ.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M12
  have hTJ : (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H) := by
    obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal T (N := generalizedFitting (HBar H))
    have hQc : Nat.card ↥(Q : Subgroup ↥(generalizedFitting (HBar H))) = 64 := by
      rw [Sylow.card_eq_multiplicity Q, hJcard, factorization_95040]; norm_num
    have hTc64 : Nat.card ↥(T : Subgroup (HBar H)) = 64 := by
      rw [hT, card_barIn_S hctx hCH, card_S_m12 hctx]
    have hinf : Nat.card ↥((T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H)) = 64 := by
      rw [hQ] at hQc
      rw [← hQc]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) ≤
          generalizedFitting (HBar H))).toEquiv).symm
    have heq : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinf, hTc64])
    rw [← heq]
    exact inf_le_right
  obtain ⟨x, hx2, hzx, hcl⟩ := (m12_data' hctx).two_classes
  have hS := (CFSG.ABGLocalTools.isSylowOf_iff).1 hctx.sylow_top
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let Sy : Sylow 2 G := hS.2.1.toSylow (fun hd => hidx hd)
  have hSy : (Sy : Subgroup G) = S := IsPGroup.toSylow_coe _ _
  have hpx : IsPGroup 2 (zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx2]; norm_num
  obtain ⟨Q, hQ⟩ := hpx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Sy Q
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  have hxS : g⁻¹ * x * g ∈ S := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    rw [← hSy]
    simpa using hxQ
  set x' : G := g⁻¹ * x * g with hx'
  have hconj : IsConj x x' := isConj_iff.2 ⟨g⁻¹, by rw [hx']; group⟩
  have hx'2 : orderOf x' = 2 := by rw [← hx2]; exact (hconj.orderOf_eq).symm
  have hzx' : ¬ IsConj z x' := fun h => hzx (h.trans hconj.symm)
  have hcl' : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x' u := by
    intro u hu
    rcases hcl u hu with h | h
    · exact Or.inl h
    · exact Or.inr (hconj.symm.trans h)
  have hx'H : x' ∈ H := hCH (hctx.S_le_Cen hxS)
  have hJcl : ∃ y : ↥(generalizedFitting (HBar H)), ∀ u : ↥(generalizedFitting (HBar H)),
      orderOf u = 2 →
      IsConj (⟨mkH H ⟨z, hzH⟩, hzbJ⟩ : ↥(generalizedFitting (HBar H))) u ∨ IsConj y u := by
    set a : ↥(generalizedFitting (HBar H)) := ⟨mkH H ⟨z, hzH⟩, hzbJ⟩ with ha
    have ha2 : orderOf a = 2 := by rw [ha, ← Subgroup.orderOf_coe]; exact hzb2
    by_cases hall : ∀ u : ↥(generalizedFitting (HBar H)), orderOf u = 2 → IsConj a u
    · exact ⟨a, fun u hu => Or.inl (hall u hu)⟩
    · push Not at hall
      obtain ⟨v, hv2, hav⟩ := hall
      refine ⟨v, fun u hu => ?_⟩
      have h3 := m12_three_involutions (eJ a) (eJ v) (eJ u)
        ((MulEquiv.orderOf_eq eJ a).trans ha2) ((MulEquiv.orderOf_eq eJ v).trans hv2)
        ((MulEquiv.orderOf_eq eJ u).trans hu)
      rcases h3 with h | h | h
      · exact absurd (isConj_of_equiv' eJ h) hav
      · exact Or.inl (isConj_of_equiv' eJ h)
      · exact Or.inr (isConj_of_equiv' eJ h)
  obtain ⟨y, hy⟩ := hJcl
  exact ⟨fus_of_J_two_classes hzH hx'H hz2 hx'2 hzx' hcl' T hTJ hzbJ hy, ⟨eJ⟩⟩


end CFSG.GH74.GLS.IVK.Proofs2
