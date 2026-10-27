module

public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Twin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Q3.Q3T6D CFSG.ClassicalInvolution.Asc77

section Plain

variable {H : Type} [Group H]

theorem conjOnNormalizerPsp_eq_conj {L : Subgroup H} (w : ↥(Subgroup.normalizer (L : Set H)))
    {d : H} (hd : d ∈ L) {e : H} (he : ∀ y ∈ L, e * y = y * e) (hwe : (w : H) = d * e) :
    conjOnNormalizer L w = MulAut.conj (⟨d, hd⟩ : ↥L) := by
  refine MulEquiv.ext fun y => Subtype.ext ?_
  have hey : e * (y : H) = y * e := he y y.2
  show (w : H) * y * (w : H)⁻¹ = d * y * d⁻¹
  rw [hwe, mul_inv_rev, mul_assoc d e, hey]
  group

end Plain

section Main


variable {G : Type} [Group G] [Finite G]

theorem inducedImagePsp_facts {A : Subgroup G} {s z₁ z₂ : G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAgen : A = Subgroup.closure {z₁, z₂, s})
    {L : Subgroup (OddQuot s)}
    (hL : ∀ d ∈ ({z₁, z₂, z₁ * z₂} : Set G), ∀ hdC : d ∈ Subgroup.centralizer ({s} : Set G),
      ∃ ℓ ∈ L, ∃ e : OddQuot s, (∀ y ∈ L, e * y = y * e) ∧ oddQuotMk s ⟨d, hdC⟩ = ℓ * e)
    (hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G)) (hz₁L : oddQuotMk s ⟨z₁, hz₁C⟩ ∈ L)
    (hmov : ∃ y ∈ L, oddQuotMk s ⟨z₁, hz₁C⟩ * y ≠ y * oddQuotMk s ⟨z₁, hz₁C⟩) :
    (∀ x ∈ inducedImage L (modOdd s A), x * x = 1) ∧
      (∃ x ∈ inducedImage L (modOdd s A), x ≠ 1) ∧
      ∀ x ∈ inducedImage L (modOdd s A),
        ((x : ↥(inducedAutOn L)) : MulAut ↥L) ∈ innSubgroup ↥L := by
  have hz₁A : z₁ ∈ A := hAgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hww : w * w = 1 := by
      apply Subtype.ext
      obtain ⟨k, hkA, hk⟩ := hw
      have hk' : oddQuotMk s k = (w : OddQuot s) := hk
      have hkk : k * k = 1 := Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hA hkA)
      show (w : OddQuot s) * w = 1
      rw [← hk', ← map_mul, hkk, map_one]
    rw [← map_mul, hww, map_one]
  · refine ⟨toInducedAutOn L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩,
      ⟨_, oddQuotMk_mem_modOdd hz₁A hz₁C, rfl⟩, fun h1 => ?_⟩
    obtain ⟨y, hyL, hy⟩ := hmov
    apply hy
    have h2 : conjOnNormalizer L ⟨oddQuotMk s ⟨z₁, hz₁C⟩, Subgroup.le_normalizer hz₁L⟩ = 1 :=
      congrArg Subtype.val h1
    have h3 := congrArg (fun τ : MulAut ↥L => ((τ ⟨y, hyL⟩ : ↥L) : OddQuot s)) h2
    change oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ = y at h3
    calc oddQuotMk s ⟨z₁, hz₁C⟩ * y
        = oddQuotMk s ⟨z₁, hz₁C⟩ * y * (oddQuotMk s ⟨z₁, hz₁C⟩)⁻¹ * oddQuotMk s ⟨z₁, hz₁C⟩ := by
          group
      _ = y * oddQuotMk s ⟨z₁, hz₁C⟩ := by rw [h3]
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : OddQuot s) ∈ modOdd s A := hw
    obtain ⟨d, hd, hdC, e, he, hwe⟩ := exists_mul_central_of_mem_modOdd hA hAgen hw'
    rcases hd with rfl | hd
    · have h1 := conjOnNormalizer_eq_conj w L.one_mem he
        (by rw [hwe, show oddQuotMk s ⟨1, hdC⟩ = 1 from map_one _])
      exact ⟨⟨1, L.one_mem⟩, h1.symm⟩
    · obtain ⟨ℓ, hℓ, e', he', hdℓ⟩ := hL d hd hdC
      have hwe' : (w : OddQuot s) = ℓ * (e' * e) := by rw [hwe, hdℓ, mul_assoc]
      have hcen : ∀ y ∈ L, (e' * e) * y = y * (e' * e) := fun y hy => by
        calc e' * e * y = e' * (e * y) := mul_assoc _ _ _
          _ = e' * (y * e) := by rw [← Subgroup.mem_center_iff.mp he y]
          _ = e' * y * e := (mul_assoc _ _ _).symm
          _ = y * e' * e := by rw [he' y hy]
          _ = y * (e' * e) := mul_assoc _ _ _
      exact ⟨⟨ℓ, hℓ⟩, (conjOnNormalizerPsp_eq_conj w hℓ hcen hwe').symm⟩

theorem hyp51At_of_pair_layers {Φ : Set (Subgroup G)} {c b b' d k y : G} {M M' B : Subgroup G}
    (hBelow : CIT3Below (Nat.card G)) (hΦ : SecData3 c Φ)
    (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) (hM : M ∈ Φ) (hM' : M' ∈ Φ)
    (hMb : IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M b)
    (hM'b : IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' b') (hbb' : b * b' = c)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hbB : b ∈ B) (hdB : d ∈ B) (hcB : c ∈ B)
    (hBgen : B = Subgroup.closure ({b, d, c} : Set G)) (hc1 : c ≠ 1) (hbc : b ≠ c)
    (hdky : d = k * y) (hy : y ∈ M ⊔ M') (hkC : k ∈ Subgroup.centralizer ({c} : Set G))
    (hk : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → ∀ x ∈ L,
      oddQuotMk c ⟨k, hkC⟩ * x = x * oddQuotMk c ⟨k, hkC⟩) :
    Asc77.Hyp51At B c := by
  classical
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hnc
  have hb1 : b ≠ 1 := fun h => by
    have := hMb.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hb'1 : b' ≠ 1 := fun h => by
    have := hM'b.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hb'B : b' ∈ B := by
    have : b' = b⁻¹ * c := by rw [← hbb']; group
    rw [this]
    exact B.mul_mem (B.inv_mem hbB) hcB
  have hb'c : b' ≠ c := fun h => hb1 (by
    rw [h] at hbb'
    exact mul_right_cancel (hbb'.trans (one_mul c).symm))
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := hMb.le hMb.mem
  have hb'C : b' ∈ Subgroup.centralizer ({c} : Set G) := hM'b.le hM'b.mem
  have hMC : M ≤ Subgroup.centralizer ({c} : Set G) := hMb.le
  have hM'C : M' ≤ Subgroup.centralizer ({c} : Set G) := hM'b.le
  have hdC : d ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hdB
  have hyC : y ∈ Subgroup.centralizer ({c} : Set G) := (sup_le hMC hM'C) hy
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.self_mem_centralizer_singleton c
  obtain ⟨j₁, hj₁⟩ := exists_modOdd_le_secComp hΦ D hM
  obtain ⟨j₂, hj₂⟩ := exists_modOdd_le_secComp hΦ D hM'
  have hb₁ : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c M := oddQuotMk_mem_modOdd hMb.mem hbC
  have hb₂ : oddQuotMk c ⟨b', hb'C⟩ ∈ modOdd c M' := oddQuotMk_mem_modOdd hM'b.mem hb'C
  have hm₁ : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      L = secComp hΦ D j₁ := fun L hL hm =>
    eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC (hj₁ hb₁) hL hm
  have hm₂ : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      L = secComp hΦ D j₂ := fun L hL hm =>
    eq_secComp_of_movedByAll hΦ D hB hcB hc1 hb'B hb'1 hb'c hb'C (hj₂ hb₂) hL hm
  refine ⟨fun L L' hL hL' hm hm' => (hm₁ L hL hm).trans (hm₁ L' hL' hm').symm,
    fun L hL hm => ?_⟩
  have hLj₁ := hm₁ L hL hm
  have hLj₂ := hm₂ L hL hm
  have hle₁ : modOdd c M ≤ L := hLj₁ ▸ hj₁
  have hle₂ : modOdd c M' ≤ L := hLj₂ ▸ hj₂
  have hmovb : ∃ y' ∈ L, oddQuotMk c ⟨b, hbC⟩ * y' ≠ y' * oddQuotMk c ⟨b, hbC⟩ :=
    hm _ (oddQuotMk_mem_modOdd hbB hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC)
  have hbL : oddQuotMk c ⟨b, hbC⟩ ∈ L := hle₁ hb₁
  have hb'L : oddQuotMk c ⟨b', hb'C⟩ ∈ L := hle₂ hb₂
  have hyL : oddQuotMk c ⟨y, hyC⟩ ∈ L :=
    (sup_le hle₁ hle₂) (oddQuotMk_mem_sup3 hMC hM'C hy hyC)
  have hkc : ∀ x ∈ L, oddQuotMk c ⟨k, hkC⟩ * x = x * oddQuotMk c ⟨k, hkC⟩ := hk L hL
  have hdk : oddQuotMk c ⟨d, hdC⟩ = oddQuotMk c ⟨y, hyC⟩ * oddQuotMk c ⟨k, hkC⟩ := by
    have e : (⟨d, hdC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = ⟨k, hkC⟩ * ⟨y, hyC⟩ :=
      Subtype.ext hdky
    rw [e, map_mul, hkc _ hyL]
  have hL3 : ∀ x ∈ ({b, d, b * d} : Set G), ∀ hxC : x ∈ Subgroup.centralizer ({c} : Set G),
      ∃ ℓ ∈ L, ∃ e : OddQuot c, (∀ y' ∈ L, e * y' = y' * e) ∧ oddQuotMk c ⟨x, hxC⟩ = ℓ * e := by
    intro x hx hxC
    rcases hx with hx | hx | hx
    · have e : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = ⟨b, hbC⟩ := Subtype.ext hx
      exact ⟨_, hbL, 1, fun y' _ => by rw [one_mul, mul_one], by rw [e, mul_one]⟩
    · have e : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = ⟨d, hdC⟩ := Subtype.ext hx
      exact ⟨_, hyL, _, hkc, by rw [e, hdk]⟩
    · have e : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = ⟨b, hbC⟩ * ⟨d, hdC⟩ :=
        Subtype.ext hx
      exact ⟨oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨y, hyC⟩, L.mul_mem hbL hyL, _, hkc,
        by rw [e, map_mul, hdk, mul_assoc]⟩
  obtain ⟨hsq, hne, hinn⟩ := inducedImagePsp_facts hB hBgen hL3 hbC hbL hmovb
  obtain ⟨hbL', K₀, hK₀⟩ := exists_classical_center hMb hbC hle₁ hmovb
  have hcl := exists_classical_inner_image hbB hbC hbL' hmovb ⟨K₀, hK₀⟩
  have hkind := kind_of_isComponent_secComp hΦ D (hLj₁ ▸ hL)
  subst hLj₁
  rcases hkind with ⟨t, n, ht, hadm, hc⟩ | hc
  · exact alphaOf_inducedImage_eq_bot_of_kind d4InnerAlphaThree_proved ⟨t, n, ht, hadm, hc⟩
      ((sectionQuotientHom (normalizesLayer_of_secData3 hΦ)).comp (D.hom j₁))
      (Q3CH.ker_comp_le_center D _ (sectionQuotientHom_injective _) j₁) (modOdd c B) hsq hne
      hinn hcl
  · exfalso
    let ψ := (sectionQuotientHom (normalizesLayer_of_secData3 hΦ)).comp (D.hom j₁)
    have hψ1 : ∃ x, ψ x ≠ 1 :=
      Q3CH.exists_comp_ne_one D _ (sectionQuotientHom_injective _) j₁
    obtain ⟨-, ⟨e⟩⟩ := range_m11 m11Facts hc ψ hψ1
    have hcL : oddQuotMk c ⟨c, hcC⟩ ∈ ψ.range := by
      have h1 : oddQuotMk c ⟨c, hcC⟩ = oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨b', hb'C⟩ := by
        rw [← map_mul]
        exact congrArg _ (Subtype.ext hbb'.symm)
      rw [h1]
      exact ψ.range.mul_mem hbL hb'L
    have hcen : (⟨oddQuotMk c ⟨c, hcC⟩, hcL⟩ : ↥ψ.range) = 1 := by
      have hz := oddQuotMk_mem_center_of_mem_zpowers (Subgroup.mem_zpowers c) hcC
      have h1 : e ⟨oddQuotMk c ⟨c, hcC⟩, hcL⟩ ∈
          Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 := by
        rw [Subgroup.mem_center_iff]
        intro m
        have h2 : (e.symm m) * (⟨oddQuotMk c ⟨c, hcC⟩, hcL⟩ : ↥ψ.range) =
            ⟨oddQuotMk c ⟨c, hcC⟩, hcL⟩ * (e.symm m) :=
          Subtype.ext (Subgroup.mem_center_iff.mp hz ((e.symm m : ↥ψ.range) : OddQuot c))
        have h3 := congrArg e h2
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
        exact h3
      rw [center_m11_eq_bot m11Facts] at h1
      exact e.injective ((Subgroup.mem_bot.mp h1).trans (map_one e).symm)
    have h1 : oddQuotMk c ⟨c, hcC⟩ = 1 := congrArg Subtype.val hcen
    have hcc : (⟨c, hcC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨c, hcC⟩ = 1 :=
      Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB hcB)
    exact hc1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hcc h1))

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
