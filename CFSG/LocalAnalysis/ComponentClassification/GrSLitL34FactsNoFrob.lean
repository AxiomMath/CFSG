module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsNoFrobGL
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourL34
public import Certificates.Certificate22214

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer

structure NoFrobParts : Prop where
  pow7 : x7Pow x7T 7 = idTab 42
  ne1 : x7T ≠ idTab 42
  orbit : ∀ u ∈ (orbitR r₁T).tabs.toList,
    comp 42 u (comp 42 (comp 42 x7T u) (x7Pow x7T 6)) ≠
      comp 42 (comp 42 (comp 42 x7T u) (x7Pow x7T 6)) u

theorem noFrobParts : NoFrobParts := by
  have h := Certificates.certificate22214
  simp only [noFrobOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun u hu => h3 u (show u ∈ noFrobOrbit from Array.mem_toList_iff.mp hu)⟩

@[expose] def x₇ : Equiv.Perm (Fin 42) := g₁ * g₂

theorem tabRep_x₇ : TabRep x7T x₇ := tabRep_g₁.comp tabRep_g₂

theorem tabRep_x7Pow : ∀ k, TabRep (x7Pow x7T k) (x₇ ^ k)
  | 0 => by rw [pow_zero]; exact TabRep.idTab
  | k + 1 => by rw [pow_succ]; exact (tabRep_x7Pow k).comp tabRep_x₇

theorem x₇_mem_S : x₇ ∈ S := S.mul_mem g₁_mem_S g₂_mem_S

theorem x₇_pow_seven : x₇ ^ 7 = 1 :=
  ((tabRep_x7Pow 7).eq_iff TabRep.idTab).1 noFrobParts.pow7

theorem orderOf_x₇ : orderOf x₇ = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine orderOf_eq_prime x₇_pow_seven fun h => noFrobParts.ne1 ?_
  exact (tabRep_x₇.eq_iff TabRep.idTab).2 h

theorem comm_conj_x₇_ne
    {t : Equiv.Perm (Fin 42)} (htS : t ∈ S) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    t * (x₇ * t * x₇⁻¹) ≠ x₇ * t * x₇⁻¹ * t := by
  have hord : orderOf (⟨t, S_le_R htS⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => ht1 (congrArg Subtype.val h)
    simp only [OneMemClass.coe_one, pow_two]
    exact ht2
  obtain ⟨u, hu, hut⟩ : ∃ u ∈ (orbitR r₁T).tabs.toList, TabRep u t := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
    · exact (conjClass₁.1 _).1 h
    · exact absurd htS (not_mem_S_of_isConj h not_mem_S_r₂)
    · exact absurd htS (not_mem_S_of_isConj h not_mem_S_r₃)
    · exact absurd htS (not_mem_S_of_isConj h not_mem_S_r₄)
  have hinv : x₇ ^ 6 = x₇⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, x₇_pow_seven])
  have hrep : TabRep (comp 42 (comp 42 x7T u) (x7Pow x7T 6)) (x₇ * t * x₇⁻¹) := by
    rw [← hinv]
    exact (tabRep_x₇.comp hut).comp (tabRep_x7Pow 6)
  intro h
  exact noFrobParts.orbit u hu (((hut.comp hrep).eq_iff (hrep.comp hut)).2 h)

theorem exists_mem_S_of_card_eight
    {V : Subgroup (Equiv.Perm (Fin 42))} (hVR : V ≤ R) (hV8 : Nat.card V = 8) :
    ∃ t ∈ V, t ∈ S ∧ t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : (S.subgroupOf R).Normal := S_normal
  let ψ : ↥V →* ↥R ⧸ S.subgroupOf R :=
    (QuotientGroup.mk' (S.subgroupOf R)).comp (Subgroup.inclusion hVR)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : Subgroup.inclusion hVR a ∈ S.subgroupOf R := (QuotientGroup.eq_one_iff _).mp ha
    rw [mem_subgroupOf] at h1
    exact Subtype.ext (hcon a a.2 h1)
  have hdvd := Subgroup.card_dvd_of_injective ψ hψ
  have hidx : (S.subgroupOf R).index = 12 := by
    have h := Subgroup.card_mul_index (S.subgroupOf R)
    rw [Nat.card_congr (subgroupOfEquivOfLe S_le_R).toEquiv, card_S, card_R] at h
    omega
  rw [hV8, show Nat.card (↥R ⧸ S.subgroupOf R) = (S.subgroupOf R).index from rfl, hidx] at hdvd
  norm_num at hdvd

theorem fpf_eight_false
    {V : Subgroup (Equiv.Perm (Fin 42))} (hVR : V ≤ R)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1) (hV8 : Nat.card V = 8)
    {ρ : Equiv.Perm (Fin 42)} (hρR : ρ ∈ R)
    (hρ : ρ ∈ normalizer (V : Set (Equiv.Perm (Fin 42)))) :
    ∃ v ∈ V, v ≠ 1 ∧ ρ * v = v * ρ := by
  by_contra hcon
  have hfix : ∀ v ∈ V, ρ * v = v * ρ → v = 1 := fun v hv hc => by
    by_contra h1
    exact hcon ⟨v, hv, h1, hc⟩
  have h7 := seven_dvd_orderOf_of_fpf hVc hV2 hV8 hρ hfix
  have hn0 : orderOf ρ ≠ 0 := (orderOf_pos ρ).ne'
  have hy7 : orderOf (ρ ^ (orderOf ρ / 7)) = 7 := by
    rw [orderOf_pow_of_dvd (fun h => hn0 (Nat.eq_zero_of_dvd_of_div_eq_zero h7 h))
      (Nat.div_dvd_of_dvd h7), Nat.div_div_self h7 hn0]
  have hyR : ρ ^ (orderOf ρ / 7) ∈ R := R.pow_mem hρR _
  have hyN : ρ ^ (orderOf ρ / 7) ∈ normalizer (V : Set (Equiv.Perm (Fin 42))) :=
    (normalizer _).pow_mem hρ _
  obtain ⟨c, hcR, m, hcm⟩ : ∃ c ∈ R, ∃ m : ℤ,
      (ρ ^ (orderOf ρ / 7)) ^ m = c * x₇ * c⁻¹ := by
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hsyl : ∀ g : R, orderOf g = 7 → ¬ 7 ∣ (zpowers g).index := by
      intro g hg
      have h := Subgroup.card_mul_index (zpowers g)
      rw [Nat.card_zpowers, hg, card_R] at h
      have h' : (zpowers g).index = 34560 := by omega
      rw [h']
      decide
    have hpg : ∀ g : R, orderOf g = 7 → IsPGroup 7 (zpowers g) := fun g hg =>
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
    have hxo : orderOf (⟨x₇, S_le_R x₇_mem_S⟩ : R) = 7 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_x₇
    have hyo : orderOf (⟨ρ ^ (orderOf ρ / 7), hyR⟩ : R) = 7 := by
      rw [← Subgroup.orderOf_coe]
      exact hy7
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥R) ((hpg _ hxo).toSylow (hsyl _ hxo))
      ((hpg _ hyo).toSylow (hsyl _ hyo))
    have hmem := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _
      (mem_zpowers (⟨x₇, S_le_R x₇_mem_S⟩ : R))
    have hmem' : MulAut.conj c • (⟨x₇, S_le_R x₇_mem_S⟩ : R) ∈
        zpowers (⟨ρ ^ (orderOf ρ / 7), hyR⟩ : R) := by
      have h1 : ((c • (hpg _ hxo).toSylow (hsyl _ hxo) : Sylow 7 R) : Subgroup R) =
          zpowers (⟨ρ ^ (orderOf ρ / 7), hyR⟩ : R) := by
        rw [hc]
        rfl
      rw [← h1, Sylow.coe_subgroup_smul]
      exact hmem
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hmem'
    refine ⟨c, c.2, m, ?_⟩
    have := congrArg Subtype.val hm
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hzN : c * x₇ * c⁻¹ ∈ normalizer (V : Set (Equiv.Perm (Fin 42))) := by
    rw [← hcm]
    exact (normalizer _).zpow_mem hyN m
  obtain ⟨t, htV, htS, ht1⟩ := exists_mem_S_of_card_eight hVR hV8
  have hzt : c * x₇ * c⁻¹ * t * (c * x₇ * c⁻¹)⁻¹ ∈ V := (mem_normalizer_iff.mp hzN t).mp htV
  have hcomm := hVc _ htV _ hzt
  have ht'S : c⁻¹ * t * c ∈ S := by
    have := conj_mem_S (R.inv_mem hcR) htS
    rwa [inv_inv] at this
  have ht'2 : c⁻¹ * t * c * (c⁻¹ * t * c) = 1 := by
    calc c⁻¹ * t * c * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c := by group
      _ = 1 := by rw [hV2 t htV]; group
  have ht'1 : c⁻¹ * t * c ≠ 1 := fun h => ht1 (by
    calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group)
  apply comm_conj_x₇_ne ht'S ht'2 ht'1
  calc c⁻¹ * t * c * (x₇ * (c⁻¹ * t * c) * x₇⁻¹) =
        c⁻¹ * (t * (c * x₇ * c⁻¹ * t * (c * x₇ * c⁻¹)⁻¹)) * c := by group
    _ = c⁻¹ * (c * x₇ * c⁻¹ * t * (c * x₇ * c⁻¹)⁻¹ * t) * c := by rw [hcomm]
    _ = x₇ * (c⁻¹ * t * c) * x₇⁻¹ * (c⁻¹ * t * c) := by group

theorem noFrobenius :
    ∀ (G : Type) [Group G] [Finite G] (J E : Subgroup G) (h : G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → E ≤ normalizer (J : Set G) → IsEightGroup E →
      E ⊓ coreActionKernel J = ⊥ → h ∈ normalizer (J : Set G) → h ∈ normalizer (E : Set G) →
      ∃ e ∈ E, e ≠ 1 ∧ h * e = e * h := by
  intro G _ _ J E h hJ hL hEN hE hEK hhN hhE
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL
  have hrel : ∀ g (hg : g ∈ normalizer (J : Set G)), ∃ ρ ∈ R,
      ∀ e, q (betaHat J hg e) = ρ * q e * ρ⁻¹ := fun g hg =>
    exists_realization q hqS hqsurj (betaHat J hg) (fun e => by
      rw [hqker]
      exact mulEquiv_mem_center_iff _ e)
  choose ρ hρR hρ using hrel
  have hcongr : ∀ {g k : G} (hg : g ∈ normalizer (J : Set G)) (hk : k ∈ normalizer (J : Set G)),
      g = k → ρ g hg = ρ k hk := by
    intro g k hg hk e
    subst e
    rfl
  have hmul : ∀ {g k : G} (hg : g ∈ normalizer (J : Set G)) (hk : k ∈ normalizer (J : Set G)),
      ρ (g * k) (mul_mem hg hk) = ρ k hk * ρ g hg := by
    intro g k hg hk
    refine realization_unique hqsurj (hρR _ _) (R.mul_mem (hρR k hk) (hρR g hg)) (hρ _ _) ?_
    intro e
    rw [betaHat_mul J hg hk, hρ k hk, hρ g hg]
    group
  have hone : ∀ {g : G} (hg : g ∈ normalizer (J : Set G)), g = 1 → ρ g hg = 1 := by
    intro g hg h1
    refine realization_unique hqsurj (hρR g hg) R.one_mem (hρ g hg) ?_
    intro e
    rw [betaHat_eq_self J hg h1]
    group
  have hinv : ∀ {g : G} (hg : g ∈ normalizer (J : Set G)), ρ g⁻¹ (inv_mem hg) = (ρ g hg)⁻¹ := by
    intro g hg
    have h1 := hmul hg (inv_mem hg)
    rw [hone _ (mul_inv_cancel g)] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hconj : ∀ {g k : G} (hg : g ∈ normalizer (J : Set G)) (hk : k ∈ normalizer (J : Set G)),
      ρ (g⁻¹ * k * g) (mul_mem (mul_mem (inv_mem hg) hk) hg) = ρ g hg * ρ k hk * (ρ g hg)⁻¹ := by
    intro g k hg hk
    rw [hmul (mul_mem (inv_mem hg) hk) hg, hmul (inv_mem hg) hk, hinv, mul_assoc]
  have hcore : ∀ {g : G} (hg : g ∈ normalizer (J : Set G)), g ∈ E → ρ g hg = 1 → g = 1 := by
    intro g hg hgE h1
    have hb := betaHat_eq_of_realization_one hJ hqsurj hqker hg (fun e => by rw [hρ g hg, h1])
    have hmem : g ∈ E ⊓ coreActionKernel J :=
      mem_inf.mpr ⟨hgE, mem_coreActionKernel_of_betaHat hg hb⟩
    rw [hEK, mem_bot] at hmem
    exact hmem
  have hinj : ∀ {a b : G} (ha : a ∈ E) (hb : b ∈ E), ρ a (hEN ha) = ρ b (hEN hb) → a = b := by
    intro a b ha hb hab
    have h2 := hmul (hEN hb) (inv_mem (hEN ha))
    rw [hinv (hEN ha), hab, inv_mul_cancel] at h2
    exact (mul_inv_eq_one.mp (hcore _ (E.mul_mem hb (E.inv_mem ha)) h2)).symm
  let V : Subgroup (Equiv.Perm (Fin 42)) :=
    { carrier := {x | ∃ e, ∃ he : e ∈ E, ρ e (hEN he) = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨b * a, E.mul_mem hb ha, hmul (hEN hb) (hEN ha)⟩
      one_mem' := ⟨1, E.one_mem, hone _ rfl⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, E.inv_mem ha, hinv (hEN ha)⟩ }
  have hmemV : ∀ x, x ∈ V ↔ ∃ e, ∃ he : e ∈ E, ρ e (hEN he) = x := fun x => Iff.rfl
  have hVR : V ≤ R := by
    rintro _ ⟨e, he, rfl⟩
    exact hρR _ _
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← hmul (hEN hb) (hEN ha), ← hmul (hEN ha) (hEN hb)]
    exact hcongr _ _ (hE.1.1 b hb a ha)
  have hV2 : ∀ a ∈ V, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hmul (hEN ha) (hEN ha)]
    exact hone _ (hE.1.2 a ha)
  have hV8 : Nat.card V = 8 := by
    rw [← hE.2]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun e : E => (⟨ρ e (hEN e.2), e, e.2, rfl⟩ : V))
      ⟨fun a b hab => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab)), ?_⟩)
    rintro ⟨_, e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩
  have hhE' : ∀ e ∈ E, h⁻¹ * e * h ∈ E := fun e he => by
    have := (mem_normalizer_iff.mp (inv_mem hhE) e).mp he
    rwa [inv_inv] at this
  have hρN : ρ h hhN ∈ normalizer (V : Set (Equiv.Perm (Fin 42))) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨h⁻¹ * e * h, hhE' e he, hconj hhN (hEN he)⟩
    · rintro ⟨e, he, hx⟩
      refine ⟨h * e * h⁻¹, (mem_normalizer_iff.mp hhE e).mp he, ?_⟩
      have h1 := hconj (inv_mem hhN) (hEN he)
      rw [hcongr _ (hEN ((mem_normalizer_iff.mp hhE e).mp he)) (by rw [inv_inv]), hinv hhN,
        inv_inv, hx] at h1
      rw [h1]
      group
  obtain ⟨v, hvV, hv1, hvc⟩ := fpf_eight_false hVR hVc hV2 hV8 (hρR h hhN) hρN
  obtain ⟨e, he, rfl⟩ := hvV
  refine ⟨e, he, fun h1 => hv1 (hone _ h1), ?_⟩
  have h1 := hconj hhN (hEN he)
  rw [hvc, mul_inv_cancel_right] at h1
  have h2 := hinj (hhE' e he) he h1
  calc h * e = h * (h⁻¹ * e * h) := by rw [h2]
    _ = e * h := by group

end CFSG.ComponentClassification.GrSLit.L34Facts
