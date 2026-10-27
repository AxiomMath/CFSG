module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25U
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Main
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

namespace CFSG.ComponentClassification.Foote5.Asc25

open CFSG Subgroup CFSG.ABGLocalTools CFSG.GH74.Uniqueness.Bender CFSG.BenderSuzuki
  CFSG.EvenSporadicStandard.Finkelstein77

variable {G : Type} [Group G] [Finite G]

theorem injOn_of_odd_ker {M : Type} [Group M] [Finite M] {O : Subgroup M} [O.Normal]
    (hO : Odd (Nat.card O)) {Q : Subgroup M} (hQ : IsPGroup 2 Q) {a b : M} (ha : a ∈ Q)
    (hb : b ∈ Q) (hab : (QuotientGroup.mk' O) a = (QuotientGroup.mk' O) b) : a = b := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
  obtain ⟨k, hk⟩ := hQ ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb⟩
  have h1 : orderOf (a⁻¹ * b) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf (a⁻¹ * b) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hab
  have h3 : orderOf (a⁻¹ * b) = 1 := by
    have h4 := Nat.dvd_gcd h1 h2
    have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
    rwa [hcop.gcd_eq_one, Nat.dvd_one] at h4
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at h3
  exact h3

theorem false_of_psu3 {x : G} (hx : orderOf x = 4)
    (hwc : WeaklyClosedInNormalizer (zpowers x)) {D : Subgroup G} (hD4 : Nat.card D = 4)
    (hD𝒞 : ∀ d ∈ D, d ≠ 1 → IsConj (x ^ 2) d)
    (e₂ : ↥(normalClosure (D : Set G)) ⧸ Assembly.oddCore ↥(normalClosure (D : Set G)) ≃*
      Open.PSU3 2 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalClosure (D : Set G) with hM
  set O := Assembly.oddCore ↥M with hO
  have hOodd : Odd (Nat.card O) := DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hOchar : O.Characteristic := DisconnectedInvolutionGraph.Helpers.oddCore_characteristic
  set π : ↥M →* ↥M ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hDM : D ≤ M := subset_normalClosure
  have hD2 : ∀ d ∈ D, d * d = 1 := fun d hd => by
    by_cases hd1 : d = 1
    · rw [hd1, mul_one]
    · exact Lemma25Proof.sq_eq_one_of_isConj hx (hD𝒞 d hd hd1)
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : D = ⊥ := (eq_bot_iff_forall D).mpr h
    rw [hbot, card_bot] at hD4
    omega
  have hzM : x ^ 2 ∈ M := by
    obtain ⟨c, hc⟩ := isConj_iff.mp (hD𝒞 d₀ hd₀ hd₀1)
    have h1 := (normalClosure_normal (s := (D : Set G))).conj_mem d₀ (hDM hd₀) c⁻¹
    rwa [inv_inv, ← hc, show c⁻¹ * (c * x ^ 2 * c⁻¹) * c = x ^ 2 by group] at h1
  have hxp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨S, hS, hxS⟩ := FooteLit.exists_isSylowOf_ge_of_le (le_top : zpowers x ≤ ⊤) hxp
  have hxS' : x ∈ S := hxS (mem_zpowers x)
  have hP₀ : IsSylowOf 2 (S ⊓ M) M := hS.inf_of_le_normalizer le_top (normalizer_eq_top (H := M)).ge
  obtain ⟨Q₀, hQ₀⟩ := hP₀.exists_sylow_eq_subgroupOf
  have hmemQ : ∀ m : M, m ∈ (Q₀ : Subgroup M) ↔ (m : G) ∈ S := fun m => by
    rw [hQ₀, mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, m.2⟩⟩
  have hQp : IsPGroup 2 (Q₀ : Subgroup M) := Q₀.isPGroup'
  have hinj : ∀ a ∈ (Q₀ : Subgroup M), ∀ b ∈ (Q₀ : Subgroup M), π a = π b → a = b :=
    fun a ha b hb hab => injOn_of_odd_ker hOodd hQp ha hb hab
  set Pb : Sylow 2 (↥M ⧸ O) := Q₀.mapSurjective hπs with hPb
  have hPbc : (Pb : Subgroup (↥M ⧸ O)) = (Q₀ : Subgroup M).map π := Sylow.coe_mapSurjective hπs Q₀
  have hmodel : PSU3Model 2 = Open.PSU3 2 2 := by simp only [PSU3Model, Open.PSU3]
  have e : ↥M ⧸ O ≃* PSU3Model 2 := e₂.trans (MulEquiv.subgroupCongr hmodel.symm)
  have hB : BenderType (↥M ⧸ O) 2 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) :=
    .unitary 2 le_rfl e
  obtain ⟨w, hc⟩ := hB.exists_benderCore Pb
  have hmapO : O.map (MulAut.conjNormal x : MulAut M).toMonoidHom = O :=
    characteristic_iff_map_eq.mp hOchar _
  set α : MulAut (↥M ⧸ O) := QuotientGroup.congr O O (MulAut.conjNormal x) hmapO with hα
  have hα_apply : ∀ m : M, α (π m) = π (MulAut.conjNormal x m) := fun m =>
    QuotientGroup.congr_mk' O O _ hmapO m
  have hconjQ : ∀ q ∈ (Q₀ : Subgroup M), MulAut.conjNormal x q ∈ (Q₀ : Subgroup M) := by
    intro q hq
    rw [hmemQ, MulAut.conjNormal_apply]
    exact mul_mem (mul_mem hxS' ((hmemQ q).mp hq)) (inv_mem hxS')
  have hαP₁ : ∀ k ∈ (Pb : Subgroup (↥M ⧸ O)), α k ∈ (Pb : Subgroup (↥M ⧸ O)) := by
    intro k hk
    rw [hPbc] at hk ⊢
    obtain ⟨q, hq, rfl⟩ := hk
    exact ⟨_, hconjQ q hq, (hα_apply q).symm⟩
  have hmapP : (Pb : Subgroup (↥M ⧸ O)).map α.toMonoidHom = Pb :=
    eq_of_le_of_card_ge (map_le_iff_le_comap.mpr fun k hk => hαP₁ k hk)
      (card_map_of_injective α.injective).ge
  have hαP : ∀ k, α k ∈ (Pb : Subgroup (↥M ⧸ O)) ↔ k ∈ (Pb : Subgroup (↥M ⧸ O)) := by
    intro k
    refine ⟨fun h => ?_, hαP₁ k⟩
    rw [← hmapP] at h
    obtain ⟨k', hk', hkk'⟩ := h
    rwa [← α.injective hkk']
  set zb : ↥M ⧸ O := π ⟨x ^ 2, hzM⟩ with hzb
  have hzQ : (⟨x ^ 2, hzM⟩ : M) ∈ (Q₀ : Subgroup M) := (hmemQ _).mpr (pow_mem hxS' 2)
  have hzbP : zb ∈ (Pb : Subgroup (↥M ⧸ O)) := by rw [hPbc]; exact ⟨_, hzQ, rfl⟩
  have hx4 : x ^ 4 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hzb1 : zb ≠ 1 := by
    intro h
    have h1 := hinj _ hzQ 1 (one_mem _) (by rw [← hzb, h, map_one])
    have h2 : x ^ 2 = 1 := congrArg Subtype.val h1
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at this
    omega
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← map_mul]
    have : (⟨x ^ 2, hzM⟩ : M) * ⟨x ^ 2, hzM⟩ = 1 := by
      apply Subtype.ext
      change x ^ 2 * x ^ 2 = 1
      rw [← pow_add]
      exact hx4
    rw [this, map_one]
  have hzbZ : zb ∈ rootCenter (Pb : Subgroup (↥M ⧸ O)) :=
    hc.center_of_involution zb (le_borel _ hzbP) (orderOf_eq_prime (by rw [sq]; exact hzb2) hzb1)
  have hαz : α zb = zb := by
    rw [hzb, hα_apply]
    congr 1
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    group
  have hα2 : α * α = MulAut.conj zb := by
    ext k
    obtain ⟨m, rfl⟩ := hπs k
    rw [MulAut.mul_apply, hα_apply, hα_apply, MulAut.conj_apply, hzb, ← map_inv, ← map_mul,
      ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, coe_mul, coe_inv]
    rw [sq]
    group
  have hcent : ∀ t ∈ rootCenter (Pb : Subgroup (↥M ⧸ O)), α t = t := fun t ht =>
    centralizes_rootCenter e Pb hzbZ hzb1 α hαP hαz hα2 ht
  have hD'p : IsPGroup 2 (D.subgroupOf M) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv, hD4]
    norm_num
  obtain ⟨Q₁, hQ₁⟩ := hD'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) Q₁ Q₀
  have hgD : ∀ d (hd : d ∈ D), g * ⟨d, hDM hd⟩ * g⁻¹ ∈ (Q₀ : Subgroup M) := by
    intro d hd
    rw [← hg, Sylow.coe_subgroup_smul]
    have h1 : (⟨d, hDM hd⟩ : M) ∈ (Q₁ : Subgroup M) := hQ₁ (mem_subgroupOf.mpr hd)
    have h2 := smul_mem_pointwise_smul _ (MulAut.conj g) _ h1
    simpa [MulAut.smul_def] using h2
  set f : D →* ↥M ⧸ O :=
    π.comp ((MulAut.conj g).toMonoidHom.comp (Subgroup.inclusion hDM)) with hf
  have hf_apply : ∀ d : D, f d = π (g * ⟨d, hDM d.2⟩ * g⁻¹) := fun d => rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    rw [hf_apply, hf_apply] at hab
    have h1 := hinj _ (hgD a a.2) _ (hgD b b.2) hab
    have h2 : (⟨a, hDM a.2⟩ : M) = ⟨b, hDM b.2⟩ := by
      have := congrArg (fun y => g⁻¹ * y * g) h1
      simpa [mul_assoc] using this
    exact Subtype.ext (Subtype.mk.inj h2)
  have hfZ : f.range ≤ rootCenter (Pb : Subgroup (↥M ⧸ O)) := by
    rintro _ ⟨d, rfl⟩
    have hfP : f d ∈ (Pb : Subgroup (↥M ⧸ O)) := by
      rw [hf_apply, hPbc]
      exact ⟨_, hgD d d.2, rfl⟩
    by_cases hd1 : f d = 1
    · rw [hd1]
      exact one_mem _
    have hd2 : f d * f d = 1 := by
      rw [← map_mul]
      have : d * d = 1 := Subtype.ext (hD2 d d.2)
      rw [this, map_one]
    exact hc.center_of_involution _ (le_borel _ hfP) (orderOf_eq_prime (by rw [sq]; exact hd2) hd1)
  have hrange4 : Nat.card f.range = 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hD4]
  have hZ4 : Nat.card (rootCenter (Pb : Subgroup (↥M ⧸ O))) = 4 := by
    have := hc.card_center
    norm_num at this
    exact this
  have hrangeZ : f.range = rootCenter (Pb : Subgroup (↥M ⧸ O)) :=
    eq_of_le_of_card_ge hfZ (by rw [hZ4, hrange4])
  obtain ⟨tb, htbZ, htb1, htbz⟩ :
      ∃ tb ∈ rootCenter (Pb : Subgroup (↥M ⧸ O)), tb ≠ 1 ∧ tb ≠ zb := by
    by_contra h
    push Not at h
    have hsub : ((rootCenter (Pb : Subgroup (↥M ⧸ O)) : Subgroup _) : Set (↥M ⧸ O)) ⊆
        {1, zb} := by
      intro y hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr (h y hy hy1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, zb} : Set (↥M ⧸ O)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have h3 : Nat.card (rootCenter (Pb : Subgroup (↥M ⧸ O))) =
        ((rootCenter (Pb : Subgroup (↥M ⧸ O)) : Subgroup _) : Set (↥M ⧸ O)).ncard :=
      Nat.card_coe_set_eq _
    omega
  have htbR : tb ∈ f.range := by rw [hrangeZ]; exact htbZ
  obtain ⟨d, rfl⟩ := htbR
  have htQ : g * ⟨d, hDM d.2⟩ * g⁻¹ ∈ (Q₀ : Subgroup M) := hgD d d.2
  have hd1 : (d : G) ≠ 1 := by
    intro h
    apply htb1
    have : d = 1 := Subtype.ext h
    rw [this, map_one]
  have htC : IsConj (x ^ 2) (((g * ⟨d, hDM d.2⟩ * g⁻¹ : M)) : G) := by
    have := Lemma25Proof.isConj_conj (g : G) (hD𝒞 d d.2 hd1)
    simpa using this
  have htz : (((g * ⟨d, hDM d.2⟩ * g⁻¹ : M)) : G) ≠ x ^ 2 := by
    intro h
    apply htbz
    rw [hf_apply, hzb]
    congr 1
    exact Subtype.ext h
  refine htz (Lemma25Proof.eq_sq_of_commute hx hwc htC ?_)
  have h1 := hcent (f d) htbZ
  rw [hf_apply, hα_apply] at h1
  have h2 := hinj _ (hconjQ _ htQ) _ htQ h1
  have h3 : x * (((g * ⟨d, hDM d.2⟩ * g⁻¹ : M)) : G) * x⁻¹ =
      (((g * ⟨d, hDM d.2⟩ * g⁻¹ : M)) : G) := by
    have := congrArg Subtype.val h2
    rwa [MulAut.conjNormal_apply] at this
  calc (((g * ⟨d, hDM d.2⟩ * g⁻¹ : M)) : G) * x
      = x * (((g * ⟨d, hDM d.2⟩ * g⁻¹ : M)) : G) * x⁻¹ * x := by rw [h3]
    _ = x * (((g * ⟨d, hDM d.2⟩ * g⁻¹ : M)) : G) := by group

end CFSG.ComponentClassification.Foote5.Asc25
