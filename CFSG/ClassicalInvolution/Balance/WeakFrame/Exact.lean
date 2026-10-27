module

public import CFSG.ClassicalInvolution.Balance.WeakFrame.TwoBalanced

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

variable {F : Type*} [Field F] {G : Type*} [Group G]

section Member

variable {E K : Subgroup G}

theorem inSigma_oddCore_eq_bot (hK : InSigma F E K) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : componentClassificationOddCore ↥K = ⊥ := by
  have hfin := finite_of_odd_card hodd
  obtain ⟨φ, rfl, hD⟩ := hK
  let ε : SL(2, F) ≃* ↥φ.range := MonoidHom.ofInjective hD.inj
  refine le_bot_iff.mp (sSup_le fun N hN => ?_)
  exact (normal_odd_of_equiv_sl2 hodd (by omega) ε.symm N hN.1 hN.2).le

theorem inSigma_exists_chart (hK : InSigma F E K) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : ∃ φ : ↥K →* SL(2, F), IsChart F K φ ∧
    (∀ e ∈ E, ∃ g : GL (Fin 2) F, ∀ k k' : ↥K, (k' : G) = e * k * e⁻¹ →
      φ k' = slConjugation 2 F g (φ k)) ∧
    (∀ e ∈ E, (∀ k k' : ↥K, (k' : G) = e * k * e⁻¹ → φ k' = φ k) → e ∈ axisSub E K) := by
  have hO := inSigma_oddCore_eq_bot hK hodd h5
  obtain ⟨ψ, rfl, hD⟩ := hK
  let ε : SL(2, F) ≃* ↥ψ.range := MonoidHom.ofInjective hD.inj
  have hψ : ∀ k : ↥ψ.range, ψ (ε.symm k) = (k : G) := fun k => by
    have := MonoidHom.ofInjective_apply hD.inj (x := ε.symm k)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hinj : Function.Injective (ε.symm : ↥ψ.range →* SL(2, F)) := ε.symm.injective
  refine ⟨ε.symm.toMonoidHom, ⟨ε.symm.surjective, ?_⟩, ?_, ?_⟩
  · rw [hO]
    exact (MonoidHom.ker_eq_bot_iff _).mpr hinj
  · intro e he
    obtain ⟨g, hg⟩ := hD.diag e he
    refine ⟨g, fun k k' hk' => ?_⟩
    apply hD.inj
    show ψ (ε.symm k') = ψ (slConjugation 2 F g (ε.symm k))
    rw [← hg, hψ, hψ, hk']
  · intro e he htriv
    rw [mem_axisSub_iff]
    refine ⟨he, fun k hk => ?_⟩
    have hnorm : e * k * e⁻¹ ∈ ψ.range := by
      have := (InSigma.conjSub_le ⟨ψ, rfl, hD⟩ he) (conj_mem_conjSub hk)
      exact this
    have := htriv ⟨k, hk⟩ ⟨e * k * e⁻¹, hnorm⟩ rfl
    have h2 : (⟨e * k * e⁻¹, hnorm⟩ : ↥ψ.range) = ⟨k, hk⟩ :=
      hinj (by simpa using this)
    have h3 : e * k * e⁻¹ = k := congrArg Subtype.val h2
    calc k * e = (e * k * e⁻¹) * e := by rw [h3]
      _ = e * k := by group

theorem weakInSigma_of_inSigma (hK : InSigma F E K) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hsub : ∀ z, IsUniqueInvolution K z → IsSubnormal K (Subgroup.centralizer ({z} : Set G))) :
    WeakInSigma F E K := by
  have hfin := finite_of_odd_card hodd
  have hO := inSigma_oddCore_eq_bot hK hodd h5
  obtain ⟨φ, hφ, hdiag, hker⟩ := inSigma_exists_chart hK hodd h5
  obtain ⟨ψ, hψK, hD⟩ := hK
  have hU : IsUniqueInvolution K (ψ (-1)) := hψK ▸ hD.isUniqueInvolution hodd
  refine ⟨⟨ψ (-1), ?_, ?_⟩, ?_, ?_, ⟨φ, hφ, hdiag, hker⟩⟩
  · refine ⟨?_, hU.mem, ?_, hsub _ hU, ?_⟩
    · have := orderOf_injective ψ hD.inj (-1)
      rw [sl2_orderOf_neg_one hodd] at this
      exact this
    · have hKe : K ≃* SL(2, F) := by
        subst hψK
        exact (MonoidHom.ofInjective hD.inj).symm
      exact isPerfect_of_equiv_sl2 (by omega) hKe
    · have hKe : K ≃* SL(2, F) := by
        subst hψK
        exact (MonoidHom.ofInjective hD.inj).symm
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans hKe⟩
  · exact hD.neg_mem
  · intro e he k hk
    have := (InSigma.conjSub_le ⟨ψ, hψK, hD⟩ he) (conj_mem_conjSub hk)
    exact this
  · rw [← hψK]
    exact hD.index_two

theorem inSigma_of_weakInSigma [Finite G] {E K : Subgroup G} (hK : WeakInSigma F E K)
    (hE : ∀ x ∈ E, x * x = 1) (hodd : Odd (Nat.card F))
    (hex : componentClassificationOddCore ↥K = ⊥) :
    InSigma F E K := by
  obtain ⟨z, hz, hzE⟩ := hK.member
  obtain ⟨φ, hφ, hdiag, hker⟩ := hK.chart
  have hbij : Function.Bijective φ :=
    ⟨(MonoidHom.ker_eq_bot_iff φ).mp (by rw [hφ.ker_eq, hex]), hφ.surjective⟩
  let ε : ↥K ≃* SL(2, F) := MulEquiv.ofBijective φ hbij
  have hε : ∀ k : ↥K, ε k = φ k := fun _ => rfl
  let ψ : SL(2, F) →* G := K.subtype.comp ε.symm.toMonoidHom
  have hψ : ∀ s, ψ s = (ε.symm s : G) := fun _ => rfl
  have hψinj : Function.Injective ψ := K.subtype_injective.comp ε.symm.injective
  have hrange : ψ.range = K := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (ε.symm s).2
    · intro hx
      exact ⟨ε ⟨x, hx⟩, by rw [hψ]; simp⟩
  have hnorm : ∀ e ∈ E, ∀ k : ↥K, e * (k : G) * e⁻¹ ∈ K := fun e he k => hK.normalizes e he k k.2
  refine ⟨ψ, hrange, ⟨hψinj, fun x hx y hy => comm_of_sq_eq_one hE hx hy, hE, ?_, ?_, ?_⟩⟩
  · have hz1 := hφ.map_central hodd hz.isCentralInvolution
    have : ε.symm (-1) = ⟨z, hz.mem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact hz1.symm
    rw [hψ, this]
    exact hzE
  · intro e he
    obtain ⟨g, hg⟩ := hdiag e he
    refine ⟨g, fun s => ?_⟩
    have h1 := hg (ε.symm s) ⟨e * (ε.symm s : G) * e⁻¹, hnorm e he _⟩ rfl
    have h2 : ε.symm (slConjugation 2 F g s) = ⟨e * (ε.symm s : G) * e⁻¹, hnorm e he _⟩ := by
      rw [MulEquiv.symm_apply_eq, hε, h1, ← hε, MulEquiv.apply_symm_apply]
    rw [hψ, hψ, h2]
  · rw [hrange]
    exact hK.index_two

theorem isUniqueInvolution_iff_isCentralInvolution [Finite G] (hK : InSigma F E K)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) {z : G} :
    IsUniqueInvolution K z ↔ IsCentralInvolution K z := by
  constructor
  · intro h
    refine ⟨h.mem, h.ne_one, h.sq, fun k hk => ?_⟩
    have h1 := h.conj_eq (conjSub_eq_self_of_mem hk)
    calc z * k = (k * z * k⁻¹) * k := by rw [h1]
      _ = k * z := by group
  · intro hz
    obtain ⟨φ, hφ, -, -⟩ := inSigma_exists_chart hK hodd h5
    exact ⟨hz.mem, hz.ne_one, hz.sq, fun y hy hsq => hφ.eq_one_or_eq_of_sq hodd hz hy hsq⟩

end Member

section Frame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem weakPairingAdj_iff_pairingAdj [Finite G] (Fr : ToralFrame F Ω E S) {K L : Subgroup G}
    (hL : L ∈ S) : WeakPairingAdj E K L ↔ PairingAdj E K L := by
  constructor
  · rintro ⟨z, hz, hzn⟩
    exact ⟨z, (isUniqueInvolution_iff_isCentralInvolution (Fr.inSigma hL) Fr.odd Fr.five).mpr hz,
      hzn⟩
  · rintro ⟨z, hz, hzn⟩
    exact ⟨z, (isUniqueInvolution_iff_isCentralInvolution (Fr.inSigma hL) Fr.odd Fr.five).mp hz,
      hzn⟩

theorem wzSet_eq_zSet [Finite G] (Fr : ToralFrame F Ω E S) {S' : Set (Subgroup G)}
    (hS' : S' ⊆ S) : wzSet S' = zSet S' := by
  ext z
  constructor
  · rintro ⟨K, hK, hz⟩
    exact ⟨K, hK, (isUniqueInvolution_iff_isCentralInvolution (Fr.inSigma (hS' hK)) Fr.odd
      Fr.five).mpr hz⟩
  · rintro ⟨K, hK, hz⟩
    exact ⟨K, hK, (isUniqueInvolution_iff_isCentralInvolution (Fr.inSigma (hS' hK)) Fr.odd
      Fr.five).mp hz⟩

theorem toralFrame_weakPreFrame [Finite G] (Fr : ToralFrame F Ω E S)
    (hsub : ∀ K ∈ Ω, ∀ z, IsUniqueInvolution K z →
      IsSubnormal K (Subgroup.centralizer ({z} : Set G)))
    (hex : ∀ K ∈ Ω, componentClassificationOddCore ↥K = ⊥) : WeakPreFrame F Ω E S where
  odd := Fr.odd
  five := Fr.five
  inv := Fr.inv
  elem := Fr.elem
  eq_sigma := by
    rw [Fr.eq_sigma]
    ext K
    constructor
    · rintro ⟨hΩ, hIn⟩
      exact ⟨hΩ, weakInSigma_of_inSigma hIn Fr.odd Fr.five (hsub K hΩ)⟩
    · rintro ⟨hΩ, hW⟩
      exact ⟨hΩ, inSigma_of_weakInSigma hW Fr.elem Fr.odd (hex K hΩ)⟩
  gen := by
    rw [← Fr.gen, wzSet_eq_zSet Fr (subset_refl S)]
  card := Fr.card

theorem toralFrame_toWeakFrame [Finite G] (Fr : ToralFrame F Ω E S)
    (hsub : ∀ K ∈ Ω, ∀ z, IsUniqueInvolution K z →
      IsSubnormal K (Subgroup.centralizer ({z} : Set G)))
    (hex : ∀ K ∈ Ω, componentClassificationOddCore ↥K = ⊥) (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) : WeakToralFrame F Ω E S :=
  { toralFrame_weakPreFrame Fr hsub hex with
    sym := fun K hK L hL h =>
      (weakPairingAdj_iff_pairingAdj Fr hK).mpr
        (hsym K hK L hL ((weakPairingAdj_iff_pairingAdj Fr hL).mp h))
    conn := fun K L =>
      Relation.ReflTransGen.mono (fun _ L' h => (weakPairingAdj_iff_pairingAdj Fr L'.2).mpr h)
        K L (hconn K L) }

theorem weakZClosure_eq_zClosure [Finite G] (Fr : ToralFrame F Ω E S) (a : G) :
    weakZClosure E S a = zClosure E S a := by
  unfold weakZClosure zClosure
  rw [wzSet_eq_zSet Fr (fun K hK => hK.1)]

theorem mem_or_mem_or_mul_mem_zClosure' [Finite G] (Fr : ToralFrame F Ω E S)
    (hsub : ∀ K ∈ Ω, ∀ z, IsUniqueInvolution K z →
      IsSubnormal K (Subgroup.centralizer ({z} : Set G)))
    (hex : ∀ K ∈ Ω, componentClassificationOddCore ↥K = ⊥) (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) {a x y : G} (ha : a ∈ E) (hx : x ∈ E) (hy : y ∈ E) :
    x ∈ zClosure E S a ∨ y ∈ zClosure E S a ∨ x * y ∈ zClosure E S a := by
  have := mem_or_mem_or_mul_mem_weakZClosure (toralFrame_toWeakFrame Fr hsub hex hsym hconn)
    ha hx hy
  rwa [weakZClosure_eq_zClosure Fr] at this

theorem twoBalancedWrt_of_frame' [Finite G] (Fr : ToralFrame F Ω E S)
    (hsub : ∀ K ∈ Ω, ∀ z, IsUniqueInvolution K z →
      IsSubnormal K (Subgroup.centralizer ({z} : Set G)))
    (hex : ∀ K ∈ Ω, componentClassificationOddCore ↥K = ⊥) (hsym : PairingSymmetric E S)
    (hconn : PairingConnected E S) (hloc : ∀ a ∈ E, a ≠ 1 → ComponentBalanceAt Ω a) :
    TwoBalancedWrt E :=
  twoBalancedWrt_of_weakFrame (toralFrame_toWeakFrame Fr hsub hex hsym hconn) hloc

end Frame

end CFSG.ClassicalInvolution.Balance
