module

public import CFSG.LocalAnalysis.LargeEvenClassification.ElementaryLinear
public import CFSG.LocalAnalysis.LargeEvenClassification.CommutingElementaryProduct

public noncomputable section

namespace CFSG.LargeEvenClassification.Helpers

open CFSG.Open

universe u

theorem normalEight_square_zero_finrank_bound
    {K : Type*} [DivisionRing K] {M : Type*} [AddCommGroup M]
    [Module K M] [FiniteDimensional K M]
    (f : M →ₗ[K] M) (hsquare : f.comp f = 0) :
    Module.finrank K M ≤ 2 * Module.finrank K f.ker := by
  have hrange : f.range ≤ f.ker := by
    rintro x ⟨y, rfl⟩
    change f (f y) = 0
    exact LinearMap.congr_fun hsquare y
  have hmono := Submodule.finrank_mono hrange
  have hdimension := f.finrank_range_add_finrank_ker
  omega

theorem normalEight_involution_difference_square_zero
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (alpha : M →ₗ[ZMod 2] M) (hinvolution : alpha.comp alpha = LinearMap.id) :
    (alpha - LinearMap.id).comp (alpha - LinearMap.id) = 0 := by
  ext x
  have htwice : alpha (alpha x) = x := LinearMap.congr_fun hinvolution x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply, map_sub, htwice]
  calc
    x - alpha x - (alpha x - x) = (x + x) - (alpha x + alpha x) := by abel
    _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, sub_self]

theorem normalEight_involution_fixed_card
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (alpha : M →ₗ[ZMod 2] M) (hinvolution : alpha.comp alpha = LinearMap.id)
    (hcard : 8 ≤ Nat.card M) :
    4 ≤ Nat.card (alpha - LinearMap.id).ker := by
  have hMcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  have hKcard := Module.natCard_eq_pow_finrank
    (K := ZMod 2) (V := (alpha - LinearMap.id).ker)
  rw [Nat.card_zmod] at hMcard hKcard
  have hdimension : 3 ≤ Module.finrank (ZMod 2) M := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hMcard] using hcard
  have hbound := normalEight_square_zero_finrank_bound (alpha - LinearMap.id)
    (normalEight_involution_difference_square_zero alpha hinvolution)
  have hfixedDimension : 2 ≤ Module.finrank (ZMod 2) (alpha - LinearMap.id).ker := by
    omega
  rw [hKcard]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hfixedDimension

theorem normalEight_extend_four_with_involution
    {S : Type u} [Group S] [Finite S]
    (V : Subgroup S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (a : S) (ha : orderOf a = 2) (haV : a ∉ V)
    (hcentral : a ∈ Subgroup.centralizer (V : Set S)) :
    ∃ E : Subgroup S, V ≤ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      E ≤ Subgroup.centralizer (V : Set S) := by
  let T := Subgroup.zpowers a
  have hT : IsElemAbelian 2 T := by
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← ha]
    exact zpow_pow_orderOf
  have hTcard : Nat.card T = 2 := by rw [Nat.card_zpowers, ha]
  have hdisjoint : Disjoint V T := by
    have hdiv : Nat.card (V ⊓ T : Subgroup S) ∣ 2 := by
      simpa only [hTcard] using
        (Subgroup.card_dvd_of_le (inf_le_right : V ⊓ T ≤ T))
    have hsmall : Nat.card (V ⊓ T : Subgroup S) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | hequal
      · exact hone
      · have heq : V ⊓ T = T := Subgroup.eq_of_le_of_card_ge inf_le_right (by
          rw [hequal, hTcard])
        have hamem : a ∈ V ⊓ T := by
          rw [heq]
          exact Subgroup.mem_zpowers a
        exact False.elim (haV hamem.1)
    exact disjoint_iff.mpr (Subgroup.card_eq_one.mp hsmall)
  have hTC : T ≤ Subgroup.centralizer (V : Set S) :=
    Subgroup.zpowers_le.mpr hcentral
  have hcommutes : V ≤ Subgroup.centralizer (T : Set S) :=
    Subgroup.le_centralizer_iff.mp hTC
  obtain ⟨E, hVE, _, hE, hEcard, hEjoin⟩ :=
    commuting_disjoint_elementary_product (firstRank := 2) (secondRank := 1)
      V T hV hT (by simpa using hVcard) (by simpa using hTcard) hcommutes hdisjoint
  have hVC : V ≤ Subgroup.centralizer (V : Set S) := by
    let : IsMulCommutative V := hV.1
    exact Subgroup.le_centralizer V
  exact ⟨E, hVE, hE, by simpa using hEcard, hEjoin.trans (sup_le hVC hTC)⟩

theorem normalEight_four_line_complement
    {S : Type u} [Group S] [Finite S]
    (V D : Subgroup S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (hDV : D ≤ V) (hDcard : Nat.card D = 2) :
    ∃ t : S, t ∈ V ∧ t ∉ D ∧ V = D ⊔ Subgroup.zpowers t := by
  have hproper : ¬ V ≤ D := by
    intro hle
    have hbound := Subgroup.card_le_of_le hle
    rw [hVcard, hDcard] at hbound
    omega
  obtain ⟨t, htV, htD⟩ : ∃ t : S, t ∈ V ∧ t ∉ D := by
    by_contra hnone
    apply hproper
    intro t htV
    by_contra htD
    exact hnone ⟨t, htV, htD⟩
  let U := D ⊔ Subgroup.zpowers t
  have hUV : U ≤ V := sup_le hDV (Subgroup.zpowers_le.mpr htV)
  have hlarge : 2 < Nat.card U := by
    by_contra hsmall
    have hDU : D = U := Subgroup.eq_of_le_of_card_ge le_sup_left (by
      rw [hDcard]
      omega)
    have htU : t ∈ U := (le_sup_right : Subgroup.zpowers t ≤ U) (Subgroup.mem_zpowers t)
    exact htD (hDU ▸ htU)
  have hUgroup : IsPGroup 2 U := isPGroup_iff_pow_pow_eq_one.mpr (fun x => by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (x : S) ^ (2 ^ 1) = 1
    simpa only [pow_one] using hV.2 x (hUV x.property))
  obtain ⟨rank, hUcard⟩ := hUgroup.exists_card_eq
  have hrank : 2 ≤ rank := by
    have hbound : 2 ^ 1 < 2 ^ rank := by simpa only [pow_one, ← hUcard] using hlarge
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hbound
    omega
  have hUVeq : U = V := Subgroup.eq_of_le_of_card_ge hUV (by
    rw [hVcard, hUcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrank)
  exact ⟨t, htV, htD, hUVeq.symm⟩

theorem normalEight_normal_involution_centralizer_card
    {S : Type u} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hA : IsElemAbelian 2 A) (hAcard : 8 ≤ Nat.card A)
    (t : S) (ht : t ^ 2 = 1) :
    4 ≤ Nat.card (A ⊓ Subgroup.centralizer ({t} : Set S) : Subgroup S) := by
  let : CommGroup A := { A.toGroup with mul_comm := @mul_comm' A _ hA.1 }
  let : Module (ZMod 2) (Additive A) := elementaryZModModule (fun a => by
    apply Subtype.ext
    exact hA.2 a a.property)
  let alpha := (elementaryAutLinear (Elementary := A) 2 (MulAut.conjNormal t)).toLinearMap
  have hinvolution : alpha.comp alpha = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hpow : (MulAut.conjNormal (H := A) t) ^ 2 = 1 := by
      rw [← map_pow, ht, map_one]
    have hlinear : (elementaryAutLinear (Elementary := A) 2 (MulAut.conjNormal t)) ^ 2 = 1 := by
      rw [← map_pow, hpow, map_one]
    have hfixed : ((elementaryAutLinear (Elementary := A) 2 (MulAut.conjNormal t)) ^ 2) x = x := by
      rw [hlinear]
      rfl
    simpa only [alpha, LinearMap.comp_apply, LinearMap.id_apply,
      pow_two, LinearEquiv.mul_apply, LinearEquiv.coe_toLinearMap] using hfixed
  let F := A ⊓ Subgroup.centralizer ({t} : Set S)
  let injection : (alpha - LinearMap.id).ker → F := fun x =>
    ⟨x.val.toMul.val, x.val.toMul.property, by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      have hyEq : y = t := Set.mem_singleton_iff.mp hy
      subst y
      have hfixed : alpha x.val = x.val := sub_eq_zero.mp x.property
      have hconjugate := congrArg (fun a : Additive A => a.toMul.val) hfixed
      change t * x.val.toMul.val * t⁻¹ = x.val.toMul.val at hconjugate
      exact mul_inv_eq_iff_eq_mul.mp hconjugate⟩
  have hinjective : Function.Injective injection := by
    intro x y hxy
    have hval : x.val.toMul.val = y.val.toMul.val :=
      congrArg (fun a : F => a.val) hxy
    apply Subtype.ext
    exact Additive.ext (Subtype.ext hval)
  have hfixedCard := normalEight_involution_fixed_card alpha hinvolution
    (by
      rw [← Nat.card_congr (Additive.ofMul : A ≃ Additive A)]
      exact hAcard)
  exact hfixedCard.trans (Nat.card_le_card_of_injective injection hinjective)

theorem normal_elementary_rank_three_four_extension
    {S : Type u} [Group S] [Finite S] (htwo : IsPGroup 2 S)
    (A : Subgroup S) [A.Normal] (hA : IsElemAbelian 2 A) (hAcard : 8 ≤ Nat.card A)
    (V : Subgroup S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4) :
    ∃ E : Subgroup S, V ≤ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      E ≤ Subgroup.centralizer (V : Set S) := by
  classical
  let D := A ⊓ V
  have hdiv : Nat.card D ∣ 2 ^ 2 := by
    simpa only [hVcard, D, show 2 ^ 2 = 4 by norm_num] using
      (Subgroup.card_dvd_of_le (inf_le_right : D ≤ V))
  obtain ⟨d, hd, hDcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hcases : Nat.card D = 1 ∨ Nat.card D = 2 ∨ Nat.card D = 4 := by
    interval_cases d <;> simp_all
  have extend (a : S) (haA : a ∈ A) (haV : a ∉ V)
      (haC : a ∈ Subgroup.centralizer (V : Set S)) :
      ∃ E : Subgroup S, V ≤ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
        E ≤ Subgroup.centralizer (V : Set S) := by
    have haOrder : orderOf a = 2 := orderOf_eq_prime_iff.mpr ⟨hA.2 a haA, by
      intro haOne
      exact haV (haOne ▸ V.one_mem)⟩
    exact normalEight_extend_four_with_involution V hV hVcard a haOrder haV haC
  rcases hcases with hDone | hDtwo | hDfour
  · have hD : D = ⊥ := Subgroup.card_eq_one.mp hDone
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let action : V →* MulAut A := (MulAut.conjNormal (H := A)).comp V.subtype
    let : MulAction V A := MulAction.compHom A action
    have hdivA : 2 ∣ Nat.card A := by
      rcases (htwo.to_subgroup A).card_eq_or_dvd with hone | hdivA
      · omega
      · exact hdivA
    have honeFixed : (1 : A) ∈ MulAction.fixedPoints V A := by
      intro v
      exact map_one (action v)
    obtain ⟨a, haFixed, haNe⟩ :=
      (htwo.to_subgroup V).exists_fixed_point_of_prime_dvd_card_of_fixed_point A hdivA honeFixed
    have haV : (a : S) ∉ V := by
      intro haV
      have haD : (a : S) ∈ D := ⟨a.property, haV⟩
      have haOne : (a : S) = 1 := Subgroup.mem_bot.mp (hD ▸ haD)
      exact haNe (Subtype.ext haOne.symm)
    have haC : (a : S) ∈ Subgroup.centralizer (V : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro v hv
      have hconj := congrArg Subtype.val (haFixed ⟨v, hv⟩)
      change v * (a : S) * v⁻¹ = a at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj
    exact extend a a.property haV haC
  · obtain ⟨t, htV, _, hVgeneration⟩ :=
      normalEight_four_line_complement V D hV hVcard inf_le_right hDtwo
    let F := A ⊓ Subgroup.centralizer ({t} : Set S)
    have hFcard : 4 ≤ Nat.card F := normalEight_normal_involution_centralizer_card
      A hA hAcard t (hV.2 t htV)
    have hFC : F ≤ Subgroup.centralizer (V : Set S) := by
      apply Subgroup.le_centralizer_iff.mpr
      rw [hVgeneration]
      apply sup_le
      · intro d hd
        apply Subgroup.mem_centralizer_iff.mpr
        intro f hf
        exact congrArg Subtype.val (@mul_comm' A _ hA.1 ⟨f, hf.1⟩ ⟨d, hd.1⟩)
      · apply Subgroup.zpowers_le.mpr
        apply Subgroup.mem_centralizer_iff.mpr
        intro f hf
        exact (Subgroup.mem_centralizer_iff.mp hf.2 t (Set.mem_singleton t)).symm
    have hnotFV : ¬ F ≤ V := by
      intro hFV
      have hFD : F ≤ D := le_inf inf_le_left hFV
      have hbound := Subgroup.card_le_of_le hFD
      rw [hDtwo] at hbound
      omega
    obtain ⟨a, haF, haV⟩ : ∃ a : S, a ∈ F ∧ a ∉ V := by
      by_contra hnone
      apply hnotFV
      intro a haF
      by_contra haV
      exact hnone ⟨a, haF, haV⟩
    exact extend a haF.1 haV (hFC haF)
  · have hDV : D = V := Subgroup.eq_of_le_of_card_ge inf_le_right (by
      rw [hDfour, hVcard])
    have hVA : V ≤ A := hDV ▸ (inf_le_left : D ≤ A)
    have hnotAV : ¬ A ≤ V := by
      intro hAV
      have hbound := Subgroup.card_le_of_le hAV
      rw [hVcard] at hbound
      omega
    obtain ⟨a, haA, haV⟩ : ∃ a : S, a ∈ A ∧ a ∉ V := by
      by_contra hnone
      apply hnotAV
      intro a haA
      by_contra haV
      exact hnone ⟨a, haA, haV⟩
    have haC : a ∈ Subgroup.centralizer (V : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro v hv
      exact congrArg Subtype.val (@mul_comm' A _ hA.1 ⟨v, hVA hv⟩ ⟨a, haA⟩)
    exact extend a haA haV haC

theorem normal_elementary_rank_three_four_centralizer
    {S : Type u} [Group S] [Finite S] (htwo : IsPGroup 2 S)
    (A : Subgroup S) [A.Normal] (hA : IsElemAbelian 2 A) (hAcard : 8 ≤ Nat.card A)
    (V : Subgroup S) (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4) :
    3 ≤ CFSG.Open.twoRank (Subgroup.centralizer (V : Set S)) := by
  obtain ⟨E, _, hE, hEcard, hEC⟩ :=
    normal_elementary_rank_three_four_extension htwo A hA hAcard V hV hVcard
  let C := Subgroup.centralizer (V : Set S)
  let internal := E.subgroupOf C
  have hcomm : IsMulCommutative internal := by
    let : IsMulCommutative E := hE.1
    exact Subgroup.comap_injective_isMulCommutative E Subtype.val_injective
  have helementary : IsElemAbelian 2 internal := by
    refine ⟨hcomm, ?_⟩
    intro x hx
    apply Subtype.ext
    exact hE.2 x hx
  have hinternalCard : Nat.card internal = 2 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hEcard]
    norm_num
  unfold CFSG.Open.twoRank CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card C, ?_⟩
    rintro rank ⟨B, _, _, hBcard⟩
    exact rank_exponent_le_card (by decide : 1 < 2) B hBcard
  · exact ⟨internal, le_top, helementary, hinternalCard⟩

end CFSG.LargeEvenClassification.Helpers
