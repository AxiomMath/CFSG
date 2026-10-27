module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.LocalAnalysis.ComponentClassification.LocalBFailureTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayerTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionComponentTwoCore
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.ClassicalInvolution.LBalanceProof

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.LocalCores
  CFSG.GroupTheory Subgroup
open scoped commutatorElement

@[expose] def LBalanceAt (X : Type) [Group X] [Finite X] : Prop :=
  ∀ (A : Subgroup X), IsPGroup 2 A →
    ∀ K : Subgroup (centralizer (A : Set X)), IsPComponent 2 K →
      K.map (centralizer (A : Set X)).subtype ≤ pLayer X 2

theorem pLayer_eq_layer_of_pPrimeCore_eq_bot {G : Type} [Group G] [Finite G]
    (h : pPrimeCore 2 G = ⊥) : pLayer G 2 = layer G := by
  rw [LocalBFailure.pLayer_two_eq_twoLayer,
    TwoLayerTransport.eq_layer_of_corefree
      (by rw [← CatalogueBAlternating.primeCore_two_eq_oddCore]; exact h),
    CFSG.layer_eq_componentClassification]
theorem isPerfect_of_isPComponent {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsPComponent 2 K) : Group.IsPerfect K :=
  ⟨TwoComponents.perfect ((CatalogueBAlternating.pComponent_two_iff K).1 hK)⟩
theorem perfect_le_of_le_sup_solvable {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) [hP : Group.IsPerfect P]
    (N : Subgroup Y) [N.Normal] (S : Subgroup Y) [hS : Group.IsSolvable S]
    (h : P ≤ N ⊔ S) : P ≤ N := by
  have hmap : P.map (QuotientGroup.mk' N) ≤ S.map (QuotientGroup.mk' N) := by
    have h1 := Subgroup.map_mono (f := QuotientGroup.mk' N) h
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' N).ge,
      bot_sup_eq] at h1
  have hsolvS : Group.IsSolvable (S.map (QuotientGroup.mk' N)) := by
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp S.subtype).rangeRestrict :=
      MonoidHom.rangeRestrict_surjective _
    have h1 : Group.IsSolvable ((QuotientGroup.mk' N).comp S.subtype).range :=
      Group.isSolvable_of_surjective hsurj
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  have hperf : Group.IsPerfect (P.map (QuotientGroup.mk' N)) := Group.IsPerfect.map _
  have hsolv : Group.IsSolvable (P.map (QuotientGroup.mk' N)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hmap)
  have hbot : P.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra hne
    have : Nontrivial (P.map (QuotientGroup.mk' N)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable (G := P.map (QuotientGroup.mk' N)) hsolv
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot
theorem perfect_eq_bot_of_solvable_product {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) [hP : Group.IsPerfect P]
    (N : Subgroup Y) (hNP : N ≤ P) (hNn : (N.subgroupOf P).Normal) [hN : Group.IsSolvable N]
    (S : Subgroup Y) [hS : Group.IsSolvable S]
    (h : ∀ p ∈ P, ∃ s ∈ S, ∃ n ∈ N, p = s * n) : P = ⊥ := by
  have hN' : Group.IsSolvable (N.subgroupOf P) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNP).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNP).injective
  have hS' : Group.IsSolvable (S.subgroupOf P) := by
    have hinj : Function.Injective
        (((P.subtype.comp (S.subgroupOf P).subtype).codRestrict S (fun x => x.2)) :
          S.subgroupOf P →* S) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Group.isSolvable_of_isSolvable_injective hinj
  have hle : (⊤ : Subgroup P) ≤ N.subgroupOf P ⊔ S.subgroupOf P := by
    intro g _
    obtain ⟨s, hs, n, hn, hg⟩ := h g g.2
    have hsP : s ∈ P := by
      have : s = (g : Y) * n⁻¹ := by rw [hg]; group
      rw [this]
      exact P.mul_mem g.2 (P.inv_mem (hNP hn))
    have hgeq : g = ⟨s, hsP⟩ * ⟨n, hNP hn⟩ := Subtype.ext hg
    rw [hgeq, sup_comm]
    exact Subgroup.mul_mem_sup (show (⟨s, hsP⟩ : P) ∈ S.subgroupOf P from hs)
      (show (⟨n, hNP hn⟩ : P) ∈ N.subgroupOf P from hn)
  have hPb := @perfect_le_of_le_sup_solvable P _ _ (⊤ : Subgroup P) _ (N.subgroupOf P) hNn (S.subgroupOf P) hS' hle
  have heq : N.subgroupOf P = ⊤ := top_le_iff.1 hPb
  have hsolvP : Group.IsSolvable P := by
    rw [heq] at hN'
    exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P).toMonoidHom)
      Subgroup.topEquiv.surjective
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact Group.IsPerfect.not_isSolvable (G := P) hsolvP
theorem isSolvable_map_of_isSolvable {G G' : Type} [Group G] [Group G'] (f : G →* G') (S : Subgroup G)
    [Group.IsSolvable S] : Group.IsSolvable (S.map f) := by
  have hsurj : Function.Surjective (f.comp S.subtype).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have h1 : Group.IsSolvable (f.comp S.subtype).range := Group.isSolvable_of_surjective hsurj
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
section

variable {X : Type} [Group X] [Finite X]

theorem exists_centralizer_mul_of_commutator_le (K R M : Subgroup X) (hR : IsPGroup 2 R)
    (hMK : M ≤ K) (hMn : (M.subgroupOf K).Normal) (hModd : Odd (Nat.card M))
    (hRM : R ≤ normalizer (M : Set X)) (hcomm : ⁅K, R⁆ ≤ M) :
    ∀ k ∈ K, ∃ c ∈ K ⊓ centralizer (R : Set X), ∃ m ∈ M, k = c * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro k hk
  have hKM : K ≤ normalizer (M : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMK).1 hMn
  set G1 : Subgroup X := K ⊔ R with hG1
  have hKG1 : K ≤ G1 := le_sup_left
  have hRG1 : R ≤ G1 := le_sup_right
  have hMG1 : M ≤ G1 := hMK.trans hKG1
  have hG1M : G1 ≤ normalizer (M : Set X) := sup_le hKM hRM
  have hM'n : (M.subgroupOf G1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMG1).2 hG1M
  have hT : IsPGroup 2 (R.subgroupOf G1) := hR.comap_of_injective _ G1.subtype_injective
  have : Fact (IsPGroup 2 (R.subgroupOf G1)) := ⟨hT⟩
  have hcop : Nat.Coprime 2 (Nat.card (M.subgroupOf G1)) := by
    have h : Nat.card (M.subgroupOf G1) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMG1).toEquiv
    rw [h]
    exact Nat.coprime_two_left.2 hModd
  have hcent := centralizer_map_quotient_eq_map_centralizer 2 (R.subgroupOf G1)
    (M.subgroupOf G1) hM'n hcop
  let q := QuotientGroup.mk' (M.subgroupOf G1)
  let k' : G1 := ⟨k, hKG1 hk⟩
  have hk'mem : q k' ∈ centralizer (((R.subgroupOf G1).map q : Subgroup (G1 ⧸ M.subgroupOf G1)) :
      Set (G1 ⧸ M.subgroupOf G1)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hr' : (r : X) ∈ R := hr
    have := hcomm (commutator_mem_commutator (K.inv_mem hk) (R.inv_mem hr'))
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def, mul_assoc] using this
  rw [hcent] at hk'mem
  obtain ⟨c, hc, hcq⟩ := hk'mem
  have hcm : c⁻¹ * k' ∈ M.subgroupOf G1 := by
    have := (QuotientGroup.eq (s := M.subgroupOf G1)).1 hcq
    exact this
  have hcm' : (c : X)⁻¹ * k ∈ M := hcm
  refine ⟨(c : X), ⟨?_, ?_⟩, (c : X)⁻¹ * k, hcm', by group⟩
  · have : (c : X) = k * ((c : X)⁻¹ * k)⁻¹ := by group
    rw [this]
    exact K.mul_mem hk (K.inv_mem (hMK hcm'))
  · change (c : X) ∈ centralizer (R : Set X)
    rw [mem_centralizer_iff]
    intro r hr
    have hrc : (⟨r, hRG1 hr⟩ : G1) ∈ (R.subgroupOf G1) := hr
    have := mem_centralizer_iff.1 hc _ hrc
    have h2 := congrArg Subtype.val this
    exact h2
theorem exists_involution_centralizing_layer_sylow (hX : pPrimeCore 2 X = ⊥) (hne : (⊤ : Subgroup X) ≠ ⊥)
    (A : Subgroup X) (hA : IsPGroup 2 A) :
    ∃ z ∈ generalizedFitting X ⊓ centralizer (A : Set X), orderOf z = 2 ∧
      ∃ P : Sylow 2 (layer X),
        (P : Subgroup (layer X)).map (layer X).subtype ≤ centralizer ({z} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  have hFn : (fittingSubgroup X).Normal := (CFSG.LocalCores.fitting_nilpotent (G := X)).2.1
  have := CFSG.LocalCores.layer_characteristic (G := X)
  have hEn : (layer X).Normal := inferInstance
  have hFs : (generalizedFitting X).Normal := by
    simp only [CFSG.generalizedFitting.eq_sup]
    infer_instance
  have hFs_ne : generalizedFitting X ≠ ⊥ := by
    intro h
    apply hne
    have h1 := centralizer_generalizedFitting_le X
    rw [h] at h1
    have h2 : centralizer ((⊥ : Subgroup X) : Set X) = ⊤ := by
      ext g
      simp [mem_centralizer_iff]
    rw [h2] at h1
    exact le_bot_iff.1 h1
  have hev : Even (Nat.card (generalizedFitting X)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have := ComponentClassification.OddCore.maximal X (generalizedFitting X) hFs hodd
    rw [← CatalogueBAlternating.primeCore_two_eq_oddCore, hX] at this
    exact hFs_ne (le_bot_iff.1 this)
  obtain ⟨PF, hPF⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 2) Q
    (N := generalizedFitting X)
  have hne2 : (Q : Subgroup X) ⊓ generalizedFitting X ≠ ⊥ := by
    intro h
    have h1 : Nat.card (PF : Subgroup ↥(generalizedFitting X)) = 1 := by
      rw [hPF, h, Subgroup.bot_subgroupOf]
      exact Subgroup.card_bot
    rw [Sylow.card_eq_multiplicity PF] at h1
    have h2 : (Nat.card (generalizedFitting X)).factorization 2 = 0 := by
      have := Nat.pow_eq_one.1 h1
      simpa using this
    have h3 : 2 ∣ Nat.card (generalizedFitting X) := even_iff_two_dvd.1 hev
    have h4 : (Nat.card (generalizedFitting X)).factorization 2 ≠ 0 := by
      rw [Ne, Nat.factorization_eq_zero_iff]
      push Not
      exact ⟨Nat.prime_two, h3, Nat.card_pos.ne'⟩
    exact h4 h2
  have : Fact (IsPGroup 2 (Q : Subgroup X)) := ⟨Q.isPGroup'⟩
  have hN0n : ((generalizedFitting X).subgroupOf (Q : Subgroup X)).Normal :=
    Subgroup.normal_subgroupOf
  have hN0ne : (generalizedFitting X).subgroupOf (Q : Subgroup X) ≠ ⊥ := by
    intro h
    have := (Subgroup.subgroupOf_eq_bot.1 h).eq_bot
    exact hne2 (by rw [inf_comm]; exact this)
  have : Nontrivial ((generalizedFitting X).subgroupOf (Q : Subgroup X)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hN0ne
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal (p := 2)
    ((generalizedFitting X).subgroupOf (Q : Subgroup X))
  set g : X := ((x : (Q : Subgroup X)) : X) with hg
  have hgF : g ∈ generalizedFitting X := x.2
  have hg1 : g ≠ 1 := by
    intro h
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hgQ : ∀ q ∈ (Q : Subgroup X), g * q = q * g := by
    intro q hq
    have := Subgroup.mem_center_iff.1 hxc ⟨q, hq⟩
    exact congrArg Subtype.val this.symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).1 Q.isPGroup' (x : (Q : Subgroup X))
  have hk' : orderOf g = 2 ^ k := by
    rw [hg, Subgroup.orderOf_coe]
    exact hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk'
    exact hg1 (orderOf_eq_one_iff.1 hk')
  have hdvd : 2 ∣ orderOf g := by
    rw [hk']
    exact dvd_pow_self 2 hk1
  refine ⟨g ^ (orderOf g / 2), ⟨(generalizedFitting X).pow_mem hgF _, ?_⟩,
    orderOf_pow_orderOf_div (by rw [hk']; positivity) hdvd, ?_⟩
  · show g ^ (orderOf g / 2) ∈ centralizer (A : Set X)
    rw [mem_centralizer_iff]
    intro a ha
    have h1 : Commute a g := (hgQ a (hAQ ha)).symm
    exact (h1.pow_right _).eq
  · obtain ⟨PE, hPE⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 2) Q (N := layer X)
    refine ⟨PE, ?_⟩
    rw [hPE, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have h1 : Commute g y := hgQ y hy.1
    exact (h1.pow_left _).eq.symm
theorem pPrimeCore_layer_eq_bot (hX : pPrimeCore 2 X = ⊥) : pPrimeCore 2 (layer X) = ⊥ := by
  have := CFSG.LocalCores.layer_characteristic (G := X)
  have hEn : (layer X).Normal := inferInstance
  have hX' : Open.componentClassificationOddCore X = ⊥ := by
    rw [← CatalogueBAlternating.primeCore_two_eq_oddCore]
    exact hX
  have h := ComponentClassification.OddCore.normal_intersection X (layer X)
  rw [hX', inf_bot_eq, ← CatalogueBAlternating.primeCore_two_eq_oddCore] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (layer X).subtype_injective).1 h
theorem le_layer_of_perfect_of_le_generalizedFitting (P : Subgroup X) [Group.IsPerfect P]
    (hP : P ≤ generalizedFitting X) : P ≤ layer X := by
  have hFnil := (CFSG.LocalCores.fitting_nilpotent (G := X))
  have : Group.IsSolvable (fittingSubgroup X) := by
    have := hFnil.1
    infer_instance
  have := CFSG.LocalCores.layer_characteristic (G := X)
  exact perfect_le_of_le_sup_solvable P (layer X) (fittingSubgroup X) (by rw [sup_comm]; exact hP)
end

section

variable {H : Type} [Group H]

theorem twoComponent_centralizes_pCore [Finite H] {t : H} (ht : orderOf t = 2)
    (L : Subgroup (Subgroup.centralizer ({t} : Set H))) (hL : IsPComponent 2 L) :
    ⁅L.map (Subgroup.centralizer ({t} : Set H)).subtype, CFSG.pCore 2 H⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hQp : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hQC : ⁅L, (CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))⁆ = ⊥ := by
    have hp2 : IsPGroup 2 ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))) :=
      hQp.comap_of_injective _ (Subgroup.centralizer ({t} : Set H)).subtype_injective
    have hsolv : Group.IsSolvable
        ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))) := by
      have : Group.IsNilpotent
          ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))) := hp2.isNilpotent
      infer_instance
    have hnorm : ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))).Normal :=
      Subgroup.normal_subgroupOf
    exact TwoComponentCentralizers.commutes_with_normal_two L _
      ((CatalogueBAlternating.pComponent_two_iff L).1 hL) hp2
  have hodd : ∀ x ∈ L, ¬ 2 ∣ orderOf x → ∀ q ∈ CFSG.pCore 2 H,
      (x : H) * q * (x : H)⁻¹ = q := by
    intro x hxL hx q hq
    let A := Subgroup.zpowers (x : H)
    let B := Subgroup.zpowers t
    let α : A →* MulAut (CFSG.pCore 2 H) := MulAut.conjNormal.comp A.subtype
    let β : B →* MulAut (CFSG.pCore 2 H) := MulAut.conjNormal.comp B.subtype
    have hxt : (x : H) * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 x.2
    have hcomm : ∀ a b, α a * β b = β b * α a := by
      rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
      change MulAut.conjNormal (((x : H) ^ i)) * MulAut.conjNormal (t ^ j) =
        MulAut.conjNormal (t ^ j) * MulAut.conjNormal ((x : H) ^ i)
      rw [← map_mul, ← map_mul, ((Commute.zpow_zpow (hxt : Commute (x : H) t)) i j).eq]
    have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
      rintro ⟨a, i, rfl⟩ r hr
      have hrt : (r : H) ∈ Subgroup.centralizer ({t} : Set H) := by
        have := congrArg Subtype.val (hr ⟨t, Subgroup.mem_zpowers t⟩)
        rw [Subgroup.mem_centralizer_singleton_iff]
        change t * r * t⁻¹ = r at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      have hcx : (x : H) * r = r * x := by
        have hmem : (⟨r, hrt⟩ : Subgroup.centralizer ({t} : Set H)) ∈
            (CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H)) := r.2
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hQC hxL _ hmem
        exact (congrArg Subtype.val this).symm
      apply Subtype.ext
      change (x : H) ^ i * r * ((x : H) ^ i)⁻¹ = r
      rw [((Commute.zpow_left (hcx : Commute (x : H) r)) i).eq, mul_inv_cancel_right]
    have hA : ¬ 2 ∣ Nat.card A := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe]
      exact hx
    have hB : IsPGroup 2 B := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, ht, pow_one]⟩
    have h := thompson_A_times_B hQp hA hB α β hcomm hfix ⟨x, Subgroup.mem_zpowers _⟩
    have := congrArg (fun φ : MulAut (CFSG.pCore 2 H) => ((φ ⟨q, hq⟩ : CFSG.pCore 2 H) : H)) h
    simpa [α, MulAut.conjNormal_apply] using this
  let N : Subgroup L := ((Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)).comap
    (Subgroup.centralizer ({t} : Set H)).subtype).subgroupOf L
  have hNn : N.Normal := by
    have h1 : (Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)).Normal :=
      Subgroup.normal_centralizer
    have h2 : ((Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)).comap
        (Subgroup.centralizer ({t} : Set H)).subtype).Normal := h1.comap _
    exact Subgroup.normal_subgroupOf
  have hNmem : ∀ x : L, (∀ q ∈ CFSG.pCore 2 H,
      ((x : Subgroup.centralizer ({t} : Set H)) : H) * q *
        ((x : Subgroup.centralizer ({t} : Set H)) : H)⁻¹ = q) → x ∈ N := by
    intro x hx
    change ((x : Subgroup.centralizer ({t} : Set H)) : H) ∈
      Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := hx q hq
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hquot : IsPGroup 2 (L ⧸ N) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply hNmem
    have hord : orderOf (x ^ (2 ^ e)) = m := by
      rw [orderOf_pow' x (pow_ne_zero _ two_ne_zero), he, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (pow_pos two_pos e)]
    have hoddm : ¬ 2 ∣ orderOf (((x ^ (2 ^ e) : L) : Subgroup.centralizer ({t} : Set H))) := by
      rw [Subgroup.orderOf_coe, hord]
      exact hm.not_two_dvd_nat
    exact hodd _ (x ^ (2 ^ e)).2 hoddm
  have : Group.IsPerfect L := ⟨TwoComponents.perfect ((CatalogueBAlternating.pComponent_two_iff L).1 hL)⟩
  have htop := eq_top_of_quotient_isPGroup N hquot
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨y, hy, rfl⟩
  have hyN : (⟨y, hy⟩ : L) ∈ N := htop ▸ Subgroup.mem_top _
  exact hyN
end

theorem mul_mem_oddCore_map_of_mem_normalizer {H : Type} [Group H] [Finite H] (K : Subgroup H) (g : H)
    (hg : g ∈ normalizer (K : Set H)) :
    ∀ m ∈ (Open.componentClassificationOddCore K).map K.subtype,
      g * m * g⁻¹ ∈ (Open.componentClassificationOddCore K).map K.subtype := by
  rintro _ ⟨m0, hm0, rfl⟩
  let φ : MulAut K := normalizerConjHom K ⟨g, hg⟩
  have hchar := OddCore.characteristic K
  have h1 : φ m0 ∈ Open.componentClassificationOddCore K :=
    (Subgroup.characteristic_iff_map_le.1 hchar) φ ⟨m0, hm0, rfl⟩
  exact ⟨φ m0, h1, (coe_normalizerConjHom_apply K ⟨g, hg⟩ m0)⟩
end CFSG.ClassicalInvolution.LBalanceProof
