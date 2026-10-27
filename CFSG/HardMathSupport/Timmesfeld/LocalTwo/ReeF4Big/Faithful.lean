module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Layer
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Malle.LocalAction CFSG.HardMathSupport.Timmesfeld.CrossChar

section Cover

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ}

theorem exists_planeElt_kernel (hp : p.Prime) (hp2 : p ≠ 2) (P : ReePlane K a p)
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ rootFinset ReeTag.F4.tag) :
    ∃ z : (rootsOfUnity p (AlgebraicClosure K)) × (rootsOfUnity p (AlgebraicClosure K)),
      z ≠ 1 ∧ β ∈ rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ)
        (z.2 : (AlgebraicClosure K)ˣ) P.U) := by
  classical
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ξ, hξ⟩ := exists_primitive_root_two (L := AlgebraicClosure K) hp hp2
  have hF := P.hF1 β hβ
  set u₀ : ZMod p := ((∑ i, P.U 0 i * β i : ℤ) : ZMod p) with hu₀
  set u₁ : ZMod p := ((∑ i, P.U 1 i * β i : ℤ) : ZMod p) with hu₁
  have hne : u₀ ≠ 0 ∨ u₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hF hcon
  refine ⟨planeElt hξ u₁.val (-u₀).val, planeElt_ne_one hξ ?_, ?_⟩
  · rcases hne with h | h
    · right
      simpa using h
    · left
      simpa using h
  · refine ⟨mem_rootFinset.1 hβ, ?_⟩
    rw [show (expTuple ((planeElt hξ u₁.val (-u₀).val).1 : (AlgebraicClosure K)ˣ)
        ((planeElt hξ u₁.val (-u₀).val).2 : (AlgebraicClosure K)ˣ) P.U) =
        expTuple (ξ ^ u₁.val) (ξ ^ (-u₀).val) P.U from rfl]
    rw [rootChar_expTuple_pow_iff hξ, Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast,
      Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← hu₀, ← hu₁]
    ring

end Cover

section Inner

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ}

theorem inner_eq_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hp3 : 3 < p) (P : ReePlane K a p) (u : ReeTag.F4.reeGamma K a)
    (hcomm : ∀ z, u * P.Ψ z = P.Ψ z * u)
    (hfix : ∀ z, z ≠ 1 → rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ)
      (z.2 : (AlgebraicClosure K)ˣ) P.U) ≠ ∅ → ∀ A Sg, IsLayerDecomp P z A Sg →
        ∀ t ∈ Sg, u * t = t * u) : u = 1 := by
  classical
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hp2 : p ≠ 2 := by omega
  have key : ∀ z : (rootsOfUnity p (AlgebraicClosure K)) × (rootsOfUnity p (AlgebraicClosure K)),
      z ≠ 1 → rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ)
        (z.2 : (AlgebraicClosure K)ˣ) P.U) ≠ ∅ →
      ∃ c : Fin ReeTag.F4.tag.rank → (AlgebraicClosure K)ˣ,
        (∀ β ∈ rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ)
          (z.2 : (AlgebraicClosure K)ˣ) P.U), rootChar c β = 1) ∧
        rootDiagUnit ReeTag.F4.tag c = reeConj P.g₀ u := by
    intro z hz hne
    obtain ⟨A, Sg, hd⟩ := plane_layer hK hp (by omega) P hz hne
    have hd' := hd
    obtain ⟨hAmem, hcAS, -, hsup, -, hty⟩ := hd'
    have huC : u ∈ A ⊔ Sg := by
      rw [hsup, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm z
    obtain ⟨α, hαA, s, hsS, hαs⟩ := mem_sup_of_commute' hcAS huC
    have hsc : ∀ t ∈ Sg, s * t = t * s := by
      intro t ht
      have h1 := hfix z hz hne A Sg hd t ht
      have h2 := hcAS α hαA t ht
      rw [← hαs] at h1
      have h3 : α * (s * t) = α * (t * s) := by
        calc α * (s * t) = (α * s) * t := by rw [mul_assoc]
          _ = t * (α * s) := h1
          _ = (t * α) * s := by rw [mul_assoc]
          _ = (α * t) * s := by rw [← h2]
          _ = α * (t * s) := by rw [mul_assoc]
      exact mul_left_cancel h3
    have hs1 : s = 1 := by
      have hcen := (layerType_props ha hK hty).2.1
      have hes : (⟨s, hsS⟩ : Sg) ∈ Subgroup.center Sg := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hsc y y.2).symm
      rw [hcen, Subgroup.mem_bot] at hes
      exact congrArg Subtype.val hes
    have huA : u ∈ A := by
      rw [← hαs, hs1, mul_one]
      exact hαA
    obtain ⟨c, hc, hcu⟩ := mem_ZGrp.1 ((hAmem u).1 huA)
    exact ⟨c, hc, hcu⟩
  have hroot0 : (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ rootFinset ReeTag.F4.tag :=
    mem_rootFinset.2 (isRoot_single _ 0)
  obtain ⟨z₀, hz₀, hβ₀⟩ := exists_planeElt_kernel hp hp2 P hroot0
  obtain ⟨c₀, -, hc₀⟩ := key z₀ hz₀ (fun h => by
    have : (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) :=
      h ▸ hβ₀
    exact this)
  have hc1 : c₀ = 1 := by
    funext i
    have hroot : (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ rootFinset ReeTag.F4.tag :=
      mem_rootFinset.2 (isRoot_single _ i)
    obtain ⟨z, hz, hβ⟩ := exists_planeElt_kernel hp hp2 P hroot
    obtain ⟨c, hc, hcu⟩ := key z hz (fun h => by
      have : (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈
          (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := h ▸ hβ
      exact this)
    have hcc : c = c₀ := CFSG.LieType.Chevalley.rootDiagUnit_injective (hcu.trans hc₀.symm)
    subst hcc
    have h1 := hc _ hβ
    rw [CTTorus.rootChar_single] at h1
    exact h1
  apply reeConj_injective P.g₀
  rw [← hc₀, hc1, rootDiagUnit_one, map_one]

end Inner

section Outer

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem false_of_outer_prime_fix_gen (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (T : Subgroup (ReeTag.F4.reeGamma K a)) (hT : 2 ^ (2 * a + 1) - 1 ∣ Nat.card T) {r : ℕ}
    (hr : r.Prime) {h : MulAut (ReeTag.F4.reeGamma K a)} (hhr : h ^ r = 1)
    (hho : h ∉ innerAut (ReeTag.F4.reeGamma K a)) (hfix : ∀ t ∈ T, h t = t) : False := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hNFex, hNFuniq⟩ := reeGamma_normalForm ha hK
  obtain ⟨-, hone, hpow, -⟩ := reeGammaFieldAut_hom_facts (K := K) (a := a)
  obtain ⟨u, β, rfl⟩ := hNFex h
  have hβr : β ^ r = 1 := by
    obtain ⟨z, hz⟩ : ∃ z, (MulAut.conj u * ReeTag.F4.reeGammaFieldAut K a β) ^ r =
        MulAut.conj z * ReeTag.F4.reeGammaFieldAut K a β ^ r :=
      ⟨_, CFSG.RankThree.PartOne.KE.conj_mul_pow_aut u (ReeTag.F4.reeGammaFieldAut K a β) r⟩
    have h' : MulAut.conj 1 * ReeTag.F4.reeGammaFieldAut K a 1 =
        MulAut.conj z * ReeTag.F4.reeGammaFieldAut K a (β ^ r) := by
      rw [map_one, hone, one_mul, hpow, ← hz, hhr]
    exact (hNFuniq _ _ _ _ h').2.symm
  have hβ1 : β ≠ 1 := by
    rintro rfl
    exact hho ⟨u, by rw [hone, mul_one]⟩
  have hβ : orderOf β = r := orderOf_eq_prime hβr hβ1
  obtain ⟨σ₁, -, -, -, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) Nat.prime_two (by omega) hK
  have hrf : r ∣ 2 * a + 1 := by
    rw [← hβ, ← hcardAut]
    exact orderOf_dvd_natCard β
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hr β hβ _ hhr
    ⟨u, rfl⟩
  obtain ⟨b, hk, ψ, hbr, hψinj, hψfix, -⟩ := exists_reeGamma_fixSubfield_hom hK hr hr2 β hβ
  have hle : T.map ((MulAut.conj g)⁻¹).toMonoidHom ≤ ψ.range := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hfix t ht
    rw [hg] at h1
    have h2 : ReeTag.F4.reeGammaFieldAut K a β ((MulAut.conj g)⁻¹ t) = (MulAut.conj g)⁻¹ t := by
      apply (MulAut.conj g).injective
      have h1' : (MulAut.conj g) (ReeTag.F4.reeGammaFieldAut K a β ((MulAut.conj g)⁻¹ t)) = t := h1
      rw [h1', MulAut.apply_inv_self]
    exact (hψfix _).1 h2
  have hTcard : Nat.card T ∣ Nat.card ψ.range := by
    have h1 : Nat.card (T.map ((MulAut.conj g)⁻¹).toMonoidHom) = Nat.card T :=
      Subgroup.card_map_of_injective ((MulAut.conj g)⁻¹).injective
    rw [← h1]
    exact Subgroup.card_dvd_of_le hle
  have hψcard : Nat.card ψ.range = Nat.card (ReeTag.F4.reeGamma (fixSubfield β) b) :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hΓ₀ := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    b (fixSubfield β) hk).1
  have hQ : 2 ^ (2 * a + 1) = (2 ^ (2 * b + 1)) ^ r := by
    rw [← pow_mul, ← hbr]
  refine not_dvd_orderF_pow_sub_one (b := b) hr hr2 ?_
  have hdvd : Nat.card T ∣ Nat.card (ReeTag.F4.reeGamma (fixSubfield β) b) := hψcard ▸ hTcard
  have h2 := hT.trans hdvd
  rw [hΓ₀, hQ] at h2
  exact h2

end Outer

section Faithful

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ}

theorem faithful_std (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hp3 : 3 < p) (P : ReePlane K a p) (g : MulAut (ReeTag.F4.reeGamma K a))
    (hcomm : ∀ z, g * MulAut.conj (P.Ψ z) = MulAut.conj (P.Ψ z) * g)
    (hfix : ∀ z, z ≠ 1 → rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ)
      (z.2 : (AlgebraicClosure K)ˣ) P.U) ≠ ∅ → ∀ A Sg, IsLayerDecomp P z A Sg →
        ∀ t ∈ Sg, g t = t) : g = 1 := by
  classical
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hp2 : p ≠ 2 := by omega
  by_contra hg1
  have hn1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  have hnpos : 0 < orderOf g := orderOf_pos g
  have hr : (orderOf g).minFac.Prime := Nat.minFac_prime hn1
  have hrn : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
  set r := (orderOf g).minFac with hrdef
  set h := g ^ (orderOf g / r) with hhdef
  have hho : orderOf h = r := orderOf_pow_orderOf_div hnpos.ne' hrn
  have hhr : h ^ r = 1 := by
    rw [← hho]
    exact pow_orderOf_eq_one h
  have hhcomm : ∀ z, h * MulAut.conj (P.Ψ z) = MulAut.conj (P.Ψ z) * h := fun z =>
    ((Commute.pow_left (show Commute g (MulAut.conj (P.Ψ z)) from hcomm z) _).eq)
  have hhfix : ∀ z, z ≠ 1 → rootCharKernel (expTuple (z.1 : (AlgebraicClosure K)ˣ)
      (z.2 : (AlgebraicClosure K)ˣ) P.U) ≠ ∅ → ∀ A Sg, IsLayerDecomp P z A Sg →
        ∀ t ∈ Sg, h t = t := by
    intro z hz hne A Sg hd t ht
    have key : ∀ k : ℕ, (g ^ k) t = t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix z hz hne A Sg hd t ht, ih]
    exact key _
  by_cases hin : h ∈ innerAut (ReeTag.F4.reeGamma K a)
  · obtain ⟨u, hu⟩ := hin
    have hu1 : u = 1 := by
      refine inner_eq_one ha hK hp hp3 P u (fun z => ?_) (fun z hz hne A Sg hd t ht => ?_)
      · apply hinj
        rw [map_mul, map_mul, hu]
        exact hhcomm z
      · have h1 := hhfix z hz hne A Sg hd t ht
        rw [← hu] at h1
        have h2 : u * t * u⁻¹ = t := by simpa [MulAut.conj_apply] using h1
        calc u * t = (u * t * u⁻¹) * u := by group
          _ = t * u := by rw [h2]
    have h1 : h = 1 := by rw [← hu, hu1, map_one]
    rw [h1, orderOf_one] at hho
    exact hr.one_lt.ne hho
  ·
    have hroot0 : (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ rootFinset ReeTag.F4.tag :=
      mem_rootFinset.2 (isRoot_single _ 0)
    obtain ⟨z₀, hz₀, hβ₀⟩ := exists_planeElt_kernel hp hp2 P hroot0
    have hne : rootCharKernel (expTuple (z₀.1 : (AlgebraicClosure K)ˣ)
        (z₀.2 : (AlgebraicClosure K)ˣ) P.U) ≠ ∅ := fun h => by
      have : (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈
          (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := h ▸ hβ₀
      exact this
    obtain ⟨A, Sg, hd⟩ := plane_layer hK hp (by omega) P hz₀ hne
    obtain ⟨-, -, hdvd⟩ := layerType_props ha hK hd.2.2.2.2.2
    exact false_of_outer_prime_fix_gen ha hK Sg hdvd hr hhr hin (hhfix z₀ hz₀ hne A Sg hd)

end Faithful

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
