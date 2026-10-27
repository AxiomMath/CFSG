module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

theorem normal_of_card_three_dihedral (n : ℕ) (B : Subgroup (DihedralGroup n))
    (hB : Nat.card B = 3) : B.Normal := by
  refine ⟨fun b hb g => ?_⟩
  by_cases hb1 : b = 1
  · simp [hb1, B.one_mem]
  · have hdvd : orderOf b ∣ 3 := by
      rw [← hB]
      exact Subgroup.orderOf_dvd_natCard B hb
    have ho : orderOf b = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hb1
      · exact h
    cases b with
    | r i =>
      cases g with
      | r j =>
        have : DihedralGroup.r j * DihedralGroup.r i * (DihedralGroup.r j)⁻¹ = DihedralGroup.r i := by
          simp [add_comm]
        rwa [this]
      | sr j =>
        have : DihedralGroup.sr j * DihedralGroup.r i * (DihedralGroup.sr j)⁻¹ =
            (DihedralGroup.r i)⁻¹ := by
          simp
        rw [this]
        exact B.inv_mem hb
    | sr i =>
      rw [DihedralGroup.orderOf_sr] at ho
      norm_num at ho

theorem perm4_normalizer (a g : Equiv.Perm (Fin 4)) (hsa : Equiv.Perm.sign a = 1)
    (hsg : Equiv.Perm.sign g = 1) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hg : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a ^ 2) : g = 1 ∨ g = a ∨ g = a ^ 2 := by
  revert a g
  decide +kernel

theorem a4_normalizer (a g : alternatingGroup (Fin 4)) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hg : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a ^ 2) : g = 1 ∨ g = a ∨ g = a ^ 2 := by
  have h := perm4_normalizer (a : Equiv.Perm (Fin 4)) g (Equiv.Perm.mem_alternatingGroup.mp a.2)
    (Equiv.Perm.mem_alternatingGroup.mp g.2)
    (by simpa using congrArg Subtype.val ha3)
    (fun h => ha1 (Subtype.ext h))
    (by
      rcases hg with h | h
      · left; simpa using congrArg Subtype.val h
      · right; simpa using congrArg Subtype.val h)
  rcases h with h | h | h
  · left; exact Subtype.ext h
  · right; left; exact Subtype.ext h
  · right; right; exact Subtype.ext (by simpa using h)

theorem s4_pow (g : Equiv.Perm (Fin 4)) : g ^ 4 = 1 ∨ g ^ 3 = 1 := by
  revert g
  decide +kernel

theorem normal_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {B : Subgroup G}
    (hB : (B.map e.toMonoidHom).Normal) : B.Normal := by
  have : B = (B.map e.toMonoidHom).comap e.toMonoidHom :=
    (Subgroup.comap_map_eq_self_of_injective e.injective B).symm
  rw [this]
  exact hB.comap _

theorem normal_of_card_dvd_six {G : Type*} [Group G] [Finite G] (hG : Nat.card G ∣ 6)
    (B : Subgroup G) (hB : Nat.card B = 3) : B.Normal := by
  have hmul : B.index * 3 = Nat.card G := by
    rw [← hB]
    exact B.index_mul_card
  have hd : B.index ∣ 2 := by
    have h6 : B.index * 3 ∣ 2 * 3 := by rw [hmul]; exact hG
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h6
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · rw [Subgroup.index_eq_one.mp h]
    exact Subgroup.normal_top
  · exact Subgroup.normal_of_index_eq_two h

theorem eq_zpowers_of_card_three {G : Type*} [Group G] [Finite G] {B : Subgroup G} (hB : Nat.card B = 3)
    {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) : B = Subgroup.zpowers a := by
  have hdvd : orderOf a ∣ 3 := by
    rw [← hB]
    exact Subgroup.orderOf_dvd_natCard B haB
  have ho : orderOf a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hle : Subgroup.zpowers a ≤ B := (Subgroup.zpowers_le).mpr haB
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, ho, hB]

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem psl2_dichotomy
    (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3) (h5 : 5 ≤ Nat.card F)
    {z g : ℕ} (hz3 : 3 ∣ z) (hg0 : 0 < g) (hg2 : g ≤ 2) (hzg : z * g = Nat.card F + 1)
    {A W : Subgroup (PSL2MatrixGroup F)} (hA : Nat.card A = 3) (hAW : A ≤ W)
    {x : PSL2MatrixGroup F} (hxW : x ∈ W) (hx : orderOf x = z)
    {s : PSL2MatrixGroup F} (hsW : s ∈ W)
    (hsN : s ∈ Subgroup.normalizer (A : Set (PSL2MatrixGroup F))) (hsA : s ∉ A) :
    W = ⊤ ∨ (A.subgroupOf W).Normal := by
  have hp : p.Prime := Fact.out
  have hxo : orderOf (⟨x, hxW⟩ : W) = z := (Subgroup.orderOf_coe ⟨x, hxW⟩).symm.trans hx
  have hf0 : f ≠ 0 := CFSG.BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hq1 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hzq : Nat.card F ≤ 2 * z + 1 := by
    have : z * g ≤ z * 2 := Nat.mul_le_mul_left z hg2
    omega
  have hKW : Nat.card W ∣ Nat.card (PSL2MatrixGroup F) := Subgroup.card_subgroup_dvd_card W
  have hA' : Nat.card (A.subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv]
    exact hA
  have hcommN : (∀ a b : W, a * b = b * a) → (A.subgroupOf W).Normal := by
    intro h
    refine ⟨fun n hn g => ?_⟩
    rw [show g * n * g⁻¹ = n by rw [h g n, mul_inv_cancel_right]]
    exact hn
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    rw [this, Subgroup.card_bot] at hA
    omega
  have hAz : A = Subgroup.zpowers a := eq_zpowers_of_card_three hA haA ha1
  have ho : orderOf a = 3 := by
    have hdvd : orderOf a ∣ 3 := by
      rw [← hA]
      exact Subgroup.orderOf_dvd_natCard A haA
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hsa : s * a * s⁻¹ ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp hsN a).mp haA
    exact this
  have hsa1 : s * a * s⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have : a = s⁻¹ * (s * a * s⁻¹) * s := by group
    rw [this, h]
    group
  have hsa2 : s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a ^ 2 := by
    rw [hAz] at hsa
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsa
    have hmod : a ^ (k % 3) = a ^ k := by
      have h := zpow_mod_orderOf a k
      rw [ho] at h
      simpa using h
    have hk0 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk0 with h | h | h
    · exfalso
      apply hsa1
      rw [← hk, ← hmod, h]
      simp
    · left
      rw [← hk, ← hmod, h]
      simp
    · right
      rw [← hk, ← hmod, h]
      simp [pow_two]
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield hF W with
    hE | ⟨z', -, -, hC⟩ | ⟨z', -, hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, -, htq, N, C, hN, hNe, hNcard, hCc, hCcard, hdisj, hsup⟩ | ⟨m, hm0, hmf, ⟨e⟩, -⟩ |
    ⟨m, hm0, hmf, ⟨e⟩, -⟩
  · exact Or.inr (hcommN fun a b => hE.is_comm.comm a b)
  · exact Or.inr (hcommN fun a b => hC.commGroup.mul_comm a b)
  ·
    right
    have hmapcard : Nat.card ((A.subgroupOf W).map e.toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective e.injective, hA']
    exact normal_of_equiv e (normal_of_card_three_dihedral z' _ hmapcard)
  ·
    exfalso
    have haW : a ∈ W := hAW haA
    have ha3 : a ^ 3 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ho] at this
    have h3 := a4_normalizer (e ⟨a, haW⟩) (e ⟨s, hsW⟩)
      (by rw [← map_pow]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext ha3))
      (fun h => ha1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))))
      (by
        rcases hsa2 with h | h
        · left
          rw [← map_inv, ← map_mul, ← map_mul]
          exact congrArg e (Subtype.ext h)
        · right
          rw [← map_pow, ← map_inv, ← map_mul, ← map_mul]
          exact congrArg e (Subtype.ext h))
    apply hsA
    rcases h3 with h | h | h
    · have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
      rw [show s = 1 from this]
      exact A.one_mem
    · have := congrArg Subtype.val (e.injective h)
      rw [show s = a from this]
      exact haA
    · have := congrArg Subtype.val (e.injective (h.trans (map_pow e _ 2).symm))
      rw [show s = a ^ 2 from this]
      exact A.pow_mem haA 2
  ·
    exfalso
    have hz34 : z ∣ 4 ∨ z ∣ 3 := by
      rcases s4_pow (e ⟨x, hxW⟩) with h | h
      · left
        have := orderOf_dvd_of_pow_eq_one h
        rwa [MulEquiv.orderOf_eq, hxo] at this
      · right
        have := orderOf_dvd_of_pow_eq_one h
        rwa [MulEquiv.orderOf_eq, hxo] at this
    have hz : z = 3 := by
      rcases hz34 with h | h
      · exact absurd (Nat.dvd_trans hz3 h) (by norm_num)
      · exact Nat.dvd_antisymm h hz3
    subst hz
    have hq5 : Nat.card F = 5 := by
      interval_cases g <;> omega
    have h25 : p ^ (2 * f) = 25 := by
      rw [pow_mul', ← hF, hq5]; norm_num
    rw [h25] at h16
    omega
  ·
    have h35 := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.orderOf_dvd_of_equiv_alternating_five
      e ⟨x, hxW⟩
    rw [hxo] at h35
    have hz3' : z = 3 := by
      rcases h35 with h | h | h
      · exact absurd (Nat.dvd_trans hz3 h) (by norm_num)
      · exact Nat.dvd_antisymm h hz3
      · exact absurd (Nat.dvd_trans hz3 h) (by norm_num)
    have hW60 : Nat.card W = 60 := by
      rw [Nat.card_congr e.toEquiv]
      exact MaxUp.card_alternatingFive'
    have hq5 : Nat.card F = 5 := by
      subst hz3'
      interval_cases g <;> omega
    have hp2 : p ≠ 2 := by
      intro hp2
      subst hp2
      have : 2 ∣ Nat.card F := hF ▸ dvd_pow_self 2 hf0
      omega
    have hcardPSL : Nat.card (PSL2MatrixGroup F) = 60 := by
      have := MaxUp.card_psl2_odd hF hp2
      rw [← hF, hq5] at this
      norm_num at this
      omega
    left
    exact Subgroup.eq_top_of_card_eq W (by rw [hW60, hcardPSL])
  ·
    exfalso
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      have hNb : N.map (QuotientGroup.mk' N) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      have hmapC : C.map (QuotientGroup.mk' N) = ⊤ := by
        have h1 := Subgroup.map_sup N C (QuotientGroup.mk' N)
        rw [hsup, hNb, bot_sup_eq,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
        exact h1.symm
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
      exact hmapC
    have hinj : Function.Injective ((QuotientGroup.mk' N).comp C.subtype) := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have hcN : (c : W) ∈ N := (QuotientGroup.eq_one_iff _).mp hc
      have : (c : W) ∈ N ⊓ C := ⟨hcN, c.2⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have hQcard : Nat.card (W ⧸ N) = t := by
      rw [← hCcard]
      exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm
    have hWcard : Nat.card W = p ^ m * t := by
      rw [← hNcard, ← hQcard, mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hzW : z ∣ p ^ m * t := by
      rw [← hWcard, ← hxo]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime z (p ^ m) := by
      refine Nat.Coprime.pow_right _ ?_
      refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_))
      intro hpz
      have h1 : p ∣ Nat.card F + 1 := hzg ▸ Dvd.dvd.mul_right hpz g
      have h2 : p ∣ Nat.card F := hF ▸ dvd_pow_self p hf0
      have := (Nat.dvd_add_right h2).mp h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hzt : z ∣ t := hcop.dvd_of_dvd_mul_left hzW
    have hzq1 : z ∣ Nat.card F - 1 := by
      have h := ‹t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2›
      rw [← hF] at h
      exact hzt.trans (h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    have hzq2 : z ∣ Nat.card F + 1 := hzg ▸ Dvd.intro g rfl
    have hz2 : z ∣ 2 := by
      have := Nat.dvd_sub hzq2 hzq1
      have e2 : Nat.card F + 1 - (Nat.card F - 1) = 2 := by omega
      rwa [e2] at this
    have := Nat.le_of_dvd (by norm_num) hz2
    have := Nat.le_of_dvd (by omega) hz3
    omega
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases h2 : p ^ m = 2
    · have hdvd : Nat.card W ∣ 6 := by
        rw [Nat.card_congr e.toEquiv]
        have := card_psl2_dvd (GaloisField p m)
        rw [hGF, h2] at this
        simpa using this
      exact Or.inr (normal_of_card_dvd_six hdvd _ hA')
    have ha := four_le_pow hp3 hm0 h2
    by_cases hmeq : m = f
    · obtain ⟨φ⟩ := nonempty_galoisField_ringHom hF hmf
      have hcardle : Nat.card F ≤ Nat.card (GaloisField p m) := by rw [hF, hGF, hmeq]
      have hbij := φ.injective.bijective_of_nat_card_le hcardle
      let ψ : F ≃+* GaloisField p m := (RingEquiv.ofBijective φ hbij).symm
      have hle : Nat.card (PSL2MatrixGroup F) ≤ Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_le_card_of_injective _ (psl2Map_injective ψ.toRingHom)
      left
      refine Subgroup.eq_top_of_card_eq W ?_
      refine le_antisymm (Nat.le_of_dvd Nat.card_pos hKW) ?_
      rw [Nat.card_congr e.toEquiv]
      exact hle
    · exfalso
      obtain ⟨k, hk⟩ := hmf
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k <;> simp_all
        · exact h
      have hf2 : 2 * m ≤ f := by nlinarith
      have hpow : (p ^ m) ^ 2 ≤ Nat.card F := by
        rw [hF, ← pow_mul, mul_comm]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
      have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le
        (GaloisField p m) (e ⟨x, hxW⟩)
      rw [MulEquiv.orderOf_eq, hxo, hGF] at hord
      exact false_of_subfield_bound ha hord hpow hzq
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hf2 : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    by_cases h2 : p ^ m = 2
    · have hdvd : Nat.card W ∣ 6 := by
        rw [Nat.card_congr e.toEquiv, MaxUp.card_pgl2_galoisField hm0, pow_mul' p 2 m, h2]
        norm_num
      exact Or.inr (normal_of_card_dvd_six hdvd _ hA')
    exfalso
    have ha := four_le_pow hp3 hm0 h2
    have hpow : (p ^ m) ^ 2 ≤ Nat.card F := by
      rw [hF, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
    have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le
      (GaloisField p m) (e ⟨x, hxW⟩)
    rw [MulEquiv.orderOf_eq, hxo, hGF] at hord
    exact false_of_subfield_bound ha hord hpow hzq

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
