module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Layer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

section Layer

variable {Q : Type*} [Group Q]

theorem gfr2_layer_le (H : Subgroup Q) : GLALayer H ≤ H :=
  sSup_le fun _ hK => hK.1

theorem gfr2_gLBConj_self {H : Subgroup Q} {g : Q} (hg : g ∈ H) : GLBConj g H = H := by
  ext z
  rw [mem_gLBConj]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg
    simpa [mul_assoc] using this
  · intro h
    exact H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)

theorem gfr2_isComponentOf_gLBConj {H K : Subgroup Q} (hK : IsComponentOf K H) {g : Q}
    (hg : g ∈ H) : IsComponentOf (GLBConj g K) H := by
  obtain ⟨hKH, hsn, hq⟩ := hK
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have h1 := H.mul_mem (H.mul_mem (H.inv_mem hg) (hKH (mem_gLBConj.1 hy))) hg
    simpa [mul_assoc] using h1
  · have h1 := isSubnormal_map' (MulAut.conj g⁻¹).toMonoidHom hsn
    have h2 : H.map (MulAut.conj g⁻¹).toMonoidHom = H := gfr2_gLBConj_self hg
    rw [h2] at h1
    exact h1
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective) hq

theorem gfr2_layer_subnormal (H : Subgroup Q) : IsSubnormal (GLALayer H) H := by
  have hle : GLALayer H ≤ H := gfr2_layer_le H
  have hconj : ∀ g ∈ H, GLBConj g (GLALayer H) ≤ GLALayer H := by
    intro g hg
    show (GLALayer H).map (MulAut.conj g⁻¹).toMonoidHom ≤ GLALayer H
    refine Subgroup.map_le_iff_le_comap.2 (sSup_le fun K hK => ?_)
    refine Subgroup.map_le_iff_le_comap.1 ?_
    exact le_sSup (gfr2_isComponentOf_gLBConj hK hg)
  have hN : H ≤ Subgroup.normalizer (GLALayer H : Set Q) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq]
    refine le_antisymm (hconj g hg) ?_
    have h1 := gLBConj_mono g (hconj g⁻¹ (H.inv_mem hg))
    rwa [gLBConj_gLBConj_inv] at h1
  exact IsSubnormal.step hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hN)
    (IsSubnormal.refl H)

end Layer

section Bridge

variable {G : Type*} [Group G] [Finite G]

theorem gfr2_central_of_subnormal {K J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hJK : J ≤ K) (hsn : IsSubnormal J K) (hne : J ≠ K) : ∀ x ∈ J, ∀ k ∈ K, x * k = k * x := by
  obtain ⟨N, hJN, hNK, hNne, hNn, -⟩ := isSubnormal_exists_normal hsn hne
  have := hNn
  rcases on25_normal_le_center_or_top hq (N.subgroupOf K) with hc | htop
  · intro x hx k hk
    have := Subgroup.mem_center_iff.1 (hc (show (⟨x, hNK (hJN hx)⟩ : ↥K) ∈ N.subgroupOf K from
      hJN hx)) ⟨k, hk⟩
    exact (congrArg Subtype.val this).symm
  · exfalso
    apply hNne
    refine le_antisymm hNK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ N.subgroupOf K := by rw [htop]; trivial
    exact this

theorem gfr2_false_of_subsingleton {X : Type*} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    (h : Subsingleton X) : False := by
  obtain ⟨-, hs⟩ := hq
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [Subsingleton.elim a b])

theorem gfr2_glaPComponent_of_layer {H J : Subgroup G} (hJ : IsComponentOf J (GLALayer H))
    (hq : CFSG.Open.IsQuasisimple (barOf 3 J)) : GLAPComponent 3 H J := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hJH : J ≤ H := hJ.1.trans (gfr2_layer_le H)
  have hsn : IsSubnormal J H := isSubnormal_trans' hJ.2.1 (gfr2_layer_subnormal H)
  refine ⟨hJH, hsn, ⟨le_top, barX_isSubnormal_top 3 hsn,
    (isQuasisimple_barX_iff hp hsn).2 hq⟩, ?_⟩
  intro J' hlt hJ'sn heq
  have hJ'J : J' ≤ J := hlt.le
  have hcov := (barX_eq_iff_cov hp hsn hJ'J).1 heq
  have hJ'sn' : IsSubnormal J' J := isSubnormal_of_le_of_le hJ'sn hJ'J hJH
  have hq0 : CFSG.Open.IsQuasisimple ↥J := hJ.2.2
  have hc1 : ∀ x ∈ J', ∀ k ∈ J, x * k = k * x :=
    gfr2_central_of_subnormal hq0 hJ'J hJ'sn' (ne_of_lt hlt)
  have hC : GLAPPrimeCore 3 ↥J ≤ Subgroup.center ↥J := by
    rcases on25_normal_le_center_or_top hq0 (GLAPPrimeCore 3 ↥J) with h | h
    · exact h
    · exfalso
      apply gfr2_false_of_subsingleton hq
      have : Subsingleton (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact this
  have hc2 : ∀ j ∈ J, ∀ k ∈ J, j * k = k * j := by
    intro j hj k hk
    obtain ⟨j', hj', hjc⟩ := hcov j hj
    obtain ⟨hjmem, hjcore⟩ := (mem_gLAPPrimeCoreOf_iff 3 J _).1 hjc
    have h1 : j'⁻¹ * j * k = k * (j'⁻¹ * j) := by
      have := Subgroup.mem_center_iff.1 (hC hjcore) ⟨k, hk⟩
      exact (congrArg Subtype.val this).symm
    have h2 : j' * k = k * j' := hc1 j' hj' k hk
    calc j * k = j' * (j'⁻¹ * j * k) := by group
      _ = j' * (k * (j'⁻¹ * j)) := by rw [h1]
      _ = (j' * k) * (j'⁻¹ * j) := by group
      _ = (k * j') * (j'⁻¹ * j) := by rw [h2]
      _ = k * j := by group
  apply gfr2_false_of_subsingleton hq
  have hsub : Subsingleton ↥J := by
    refine ⟨fun a b => ?_⟩
    have hcomm : ∀ x y : ↥J, x * y = y * x := fun x y => Subtype.ext (hc2 x x.2 y y.2)
    have hbot : (⁅(⊤ : Subgroup ↥J), ⊤⁆ : Subgroup ↥J) = ⊥ := by
      refine le_bot_iff.1 (Subgroup.commutator_le.2 fun x _ y _ => ?_)
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm x y)
    have htop : ∀ z : ↥J, z = 1 := by
      intro z
      have hz : z ∈ (⁅(⊤ : Subgroup ↥J), ⊤⁆ : Subgroup ↥J) := by
        have := hq0.1
        rw [show (⁅(⊤ : Subgroup ↥J), ⊤⁆ : Subgroup ↥J) = ⊤ from this]
        trivial
      rw [hbot] at hz
      exact hz
    rw [htop a, htop b]
  exact ⟨fun a b => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]⟩

end Bridge

end CFSG.HardMathSupport.Solomon.Coordinator
