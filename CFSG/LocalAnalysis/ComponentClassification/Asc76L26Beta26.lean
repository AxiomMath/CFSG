module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Beta26Core
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtension

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}

omit [Finite G] in
theorem isElemAbelian_map {A : Type*} [Group A] {E : Subgroup A} (hE : IsElemAbelian 2 E)
    (φ : A →* G) : IsElemAbelian 2 (E.map φ) := CFSG.SectionRank.isElemAbelian_map hE _

theorem exists_moved_conj (h : HypCore S 𝒯) (hne : (memberSet 𝒯).Nonempty) {x : G}
    (hxx : x * x = 1)
    (hsyl : IsSylowOf 2 (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)))
    (hCx : centralizer ({x} : Set G) ≤ fusionGen (memberSet 𝒯)) {k : G}
    (hk : k ∉ fusionGen (memberSet 𝒯)) (hxk : k * x * k⁻¹ ∈ fusionGen (memberSet 𝒯)) :
    ∃ g : G, g ∉ fusionGen (memberSet 𝒯) ∧ g⁻¹ * x * g ∈ S ∧
      S ⊓ centralizer ({g⁻¹ * x * g} : Set G) ≤ rightConjugate S g ∧
      centralizer ({g⁻¹ * x * g} : Set G) ≤ rightConjugate (fusionGen (memberSet 𝒯)) g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := fusionGen (memberSet 𝒯) with hHdef
  have hSH : S ≤ H := le_fusionGen h.closed (memberSet_subset h) hne
  have hd₀2 : (k * x * k⁻¹) * (k * x * k⁻¹) = 1 := by
    calc (k * x * k⁻¹) * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  obtain ⟨h₁, hh₁, hdS'⟩ := exists_conj_mem_of_le h.sylow hSH hxk
    (isPGroup_zpowers_of_mul_self hd₀2)
  set g₀ := k⁻¹ * h₁ with hg₀def
  have hg₀ : g₀ ∉ H := fun h' => hk (by
    have := H.mul_mem hh₁ (H.inv_mem h')
    rw [hg₀def] at this
    simpa using this)
  set d := g₀⁻¹ * x * g₀ with hddef
  have hdS : d ∈ S := by
    have : d = h₁⁻¹ * (k * x * k⁻¹) * h₁ := by rw [hddef, hg₀def]; group
    rw [this]
    exact hdS'
  have hCd : centralizer ({d} : Set G) = rightConjugate (centralizer ({x} : Set G)) g₀ :=
    (rightConjugate_centralizer_singleton x g₀).symm
  have hP₀ : IsSylowOf 2 (rightConjugate (S ⊓ centralizer ({x} : Set G)) g₀)
      (centralizer ({d} : Set G)) := by
    rw [hCd]
    apply isSylowOf_of_card (rightConjugate_mono hsyl.le g₀)
    rw [rightConjugate_card, hsyl.card_eq, rightConjugate_card]
  obtain ⟨c, hc, hcle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hP₀
    (h.sylow.isPGroup.to_le inf_le_left) (inf_le_right : S ⊓ centralizer ({d} : Set G) ≤ _)
  set g := g₀ * c⁻¹ with hgdef
  have hcd : c * d = d * c := mem_centralizer_singleton_iff.mp hc
  have hdg : g⁻¹ * x * g = d := by
    calc g⁻¹ * x * g = c * d * c⁻¹ := by rw [hgdef, hddef]; group
      _ = d := by rw [hcd]; group
  have hCS : S ⊓ centralizer ({d} : Set G) ≤ rightConjugate S g := by
    have := rightConjugate_mono hcle c⁻¹
    rw [rightConjugate_inv, rightConjugate_mul] at this
    exact this.trans (rightConjugate_mono inf_le_left g)
  have hCdH : centralizer ({d} : Set G) ≤ rightConjugate H g := by
    rw [← hdg, ← rightConjugate_centralizer_singleton]
    exact rightConjugate_mono hCx g
  have hg : g ∉ H := by
    intro hgH
    apply hg₀
    have hcH : c ∈ rightConjugate H g := hCdH hc
    rw [mem_rightConjugate_iff] at hcH
    have h2 : g₀ = (g * c * g⁻¹) * g := by rw [hgdef]; group
    rw [h2]
    exact H.mul_mem hcH hgH
  exact ⟨g, hg, hdg ▸ hdS, hdg ▸ hCS, hdg ▸ hCdH⟩

theorem false_of_beta26_pos (IH : Statement26 (Nat.card G - 1)) (h : HypCore S 𝒯)
    (hZ : ∀ c ∈ center G, orderOf c ≠ 2) {P : Subgroup G} (hP : P ∈ 𝒯) (hbig : IsBig P)
    (hconj : ∀ g : G, rightConjugate P g ≤ S → rightConjugate P g ∈ 𝒯) {a b : G}
    (haP : a ∈ P) (haZ : ∀ p ∈ P, p * a = a * p) (ha2 : orderOf a = 2) (hbS : b ∈ S) {w : G}
    (hbw : b = w⁻¹ * a * w) (hab : a * b = b * a) (hbP : b ∉ P)
    (hsyl : IsSylowOf 2 (S ⊓ centralizer ({a * b} : Set G)) (centralizer ({a * b} : Set G)))
    {k : G} (hk : k ∉ fusionGen (memberSet 𝒯))
    (hxk : k * (a * b) * k⁻¹ ∈ fusionGen (memberSet 𝒯)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := memberSet 𝒯 with hΓdef
  set H := fusionGen Γ with hHdef
  have hΓS : Γ ⊆ S := memberSet_subset h
  have hΓH : ∀ y ∈ Γ, ∀ g, y ∈ rightConjugate H g ↔ g ∈ H := fun y hy g =>
    mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS hy g
  have hPS : P ≤ S := h.le P hP
  have hP2 : IsPGroup 2 P := h.sylow.isPGroup.to_le hPS
  have ha1 : a ≠ 1 := fun h' => by rw [h', orderOf_one] at ha2; omega
  have haΓ : a ∈ Γ := mem_memberSet hP haP ha1
  have haa : a * a = 1 := by rw [← sq, ← ha2]; exact pow_orderOf_eq_one a
  have hbb : b * b = 1 := by
    rw [hbw]
    calc w⁻¹ * a * w * (w⁻¹ * a * w) = w⁻¹ * (a * a) * w := by group
      _ = 1 := by rw [haa]; group
  have hxx : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by rw [← mul_assoc, haa, one_mul, hbb]
  have hCx := beta1 IH h hZ hP hbig hconj haP haZ ha2 hbS hbw hab hbP
  obtain ⟨g, hg, hdS, hCdS, hCdH⟩ := exists_moved_conj h ⟨a, haΓ⟩ hxx hsyl hCx hk hxk
  set d := g⁻¹ * (a * b) * g with hddef
  have hdd : d * d = 1 := by
    calc d * d = g⁻¹ * (a * b * (a * b)) * g := by rw [hddef]; group
      _ = 1 := by rw [hxx]; group
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hd2 : IsPGroup 2 (zpowers d) := isPGroup_zpowers_of_mul_self hdd
  have hCΓ : ∀ y ∈ Γ, y * d ≠ d * y := fun y hy hyd =>
    hg ((hΓH y hy g).mp (hCdH (mem_centralizer_singleton_iff.mpr hyd)))
  obtain ⟨r₀, hr₀P, hr₀4⟩ := exists_orderOf_eq_four hP2 hbig.2
  have hr₀2 : r₀ ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hr₀4]; norm_num)
  have hPne : P ≠ ⊥ := fun h' => by
    have := h' ▸ hr₀P
    rw [mem_bot] at this
    rw [this, one_pow] at hr₀2
    exact hr₀2 rfl
  have hmemd : ∀ r ∈ P, d⁻¹ * r * d ∈ rightConjugate P d := fun r hr => by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hr
  have hPdS : rightConjugate P d ≤ S := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have := S.mul_mem (S.mul_mem (S.inv_mem hdS) (hPS hy)) hdS
    simpa [mul_assoc] using this
  have hPd𝒯 : rightConjugate P d ∈ 𝒯 := hconj d hPdS
  have hPdne : rightConjugate P d ≠ P := by
    intro heq
    obtain ⟨z, hzP, hz1, -, hzd⟩ := exists_center_commute hP2 hPne hd2
      ((rightConjugate_eq_self_iff P d).mp heq)
    exact hCΓ z (mem_memberSet hP hzP hz1) hzd
  have hcd := h.comm _ hPd𝒯 P hP hPdne
  have hcomm_d : ∀ r ∈ P, ∀ r' ∈ P, r * (d⁻¹ * r' * d) = (d⁻¹ * r' * d) * r := fun r hr r' hr' =>
    (commute_of_commutator_eq_bot hcd (hmemd r' hr') hr).symm
  have hinter : ∀ r ∈ P, d⁻¹ * r * d ∈ P → r = 1 := by
    set I := P ⊓ rightConjugate P d with hIdef
    have hI2 : IsPGroup 2 I := hP2.to_le inf_le_left
    have hdI : d ∈ normalizer (I : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, mem_rightConjugate_iff, mem_rightConjugate_iff]
      have e : d * (d * y * d⁻¹) * d⁻¹ = y := by
        rw [hdinv]
        calc d * (d * y * d) * d = (d * d) * y * (d * d) := by group
          _ = y := by rw [hdd, one_mul, mul_one]
      rw [e]
      exact And.comm
    intro r hr hrd
    by_contra hr1
    have hrI : r ∈ I :=
      mem_inf.mpr ⟨hr, by rw [mem_rightConjugate_iff, ← hdinv, inv_inv]; exact hrd⟩
    have hIne : I ≠ ⊥ := fun h' => hr1 (by rw [h', mem_bot] at hrI; exact hrI)
    obtain ⟨z, hzI, hz1, -, hzd⟩ := exists_center_commute hI2 hIne hd2 hdI
    exact hCΓ z (mem_memberSet hP (mem_inf.mp hzI).1 hz1) hzd
  let φ : P →* G := MonoidHom.mk' (fun r => (r : G) * (d⁻¹ * r * d)) (by
    intro r s
    simp only [Subgroup.coe_mul]
    have hc := hcomm_d s s.2 r r.2
    calc (r : G) * s * (d⁻¹ * (r * s) * d) = r * (s * (d⁻¹ * r * d)) * (d⁻¹ * s * d) := by
          group
      _ = r * ((d⁻¹ * r * d) * s) * (d⁻¹ * s * d) := by rw [hc]
      _ = r * (d⁻¹ * r * d) * (s * (d⁻¹ * s * d)) := by group)
  have hφ : ∀ r : P, φ r = (r : G) * (d⁻¹ * r * d) := fun _ => rfl
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker, hφ] at hr
    rw [mem_bot]
    have h1 : d⁻¹ * r * d = (r : G)⁻¹ := eq_inv_of_mul_eq_one_right hr
    exact Subtype.ext (hinter r r.2 (by rw [h1]; exact inv_mem r.2))
  set U := φ.range with hUdef
  have hUS : U ≤ S := by
    rintro _ ⟨r, rfl⟩
    rw [hφ]
    exact S.mul_mem (hPS r.2) (hPdS (hmemd r r.2))
  have hUd : U ≤ centralizer ({d} : Set G) := by
    rintro _ ⟨r, rfl⟩
    rw [hφ, mem_centralizer_singleton_iff]
    have hc' := hcomm_d r r.2 r r.2
    rw [hdinv] at hc' ⊢
    calc (r : G) * (d * r * d) * d = r * d * r * (d * d) := by group
      _ = (d * d) * (r * d * r) := by rw [hdd, one_mul, mul_one]
      _ = d * ((d * r * d) * r) := by group
      _ = d * (r * (d * r * d)) := by rw [← hc']
  have hUSg : U ≤ rightConjugate S g := (le_inf hUS hUd).trans hCdS
  have hPsS : ∀ s ∈ S, rightConjugate P s ≤ S := by
    intro s hs y hy
    rw [mem_rightConjugate_iff] at hy
    have := S.mul_mem (S.mul_mem (S.inv_mem hs) (hPS hy)) hs
    simpa [mul_assoc] using this
  have hzg : ∀ z ∈ rightConjugate P g, z ≠ 1 → z ∉ H := by
    intro z hzQ hz1 hzH
    rw [mem_rightConjugate_iff] at hzQ
    have hy1 : g * z * g⁻¹ ≠ 1 := fun h' => hz1 (by
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h']; group)
    have hyΓ : g * z * g⁻¹ ∈ Γ := mem_memberSet hP hzQ hy1
    apply hg
    have h3 := (hΓH _ hyΓ g⁻¹).mp (by rw [mem_rightConjugate_iff]; simpa [mul_assoc] using hzH)
    exact (H.inv_mem_iff).mp h3
  have hβ4 : ∀ W : Subgroup G, W ≤ U → Nat.card W = 4 → IsElemAbelian 2 W →
      (∀ w ∈ W, w ≠ 1 → centralizer ({w} : Set G) ≤ H) → False := by
    intro W hWU hW4 hWe hWC
    have hQ2 : IsPGroup 2 (rightConjugate P g) := hP2.map _
    have hrQ : g⁻¹ * r₀ * g ∈ rightConjugate P g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hr₀P
    have hr2 : (g⁻¹ * r₀ * g) ^ 2 ≠ 1 := by
      have hord : orderOf (g⁻¹ * r₀ * g) = 4 := by
        rw [show g⁻¹ * r₀ * g = MulAut.conj g⁻¹ r₀ by simp, MulEquiv.orderOf_eq]
        exact hr₀4
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
    have hcommQ : ∀ w ∈ W, w ∉ normalizer ((rightConjugate P g : Subgroup G) : Set G) →
        ∀ x ∈ rightConjugate P g, ∀ y ∈ rightConjugate (rightConjugate P g) w,
          x * y = y * x := by
      intro w hw hwN x hx y hy
      have hw' : g * w * g⁻¹ ∈ S := by
        have := hUSg (hWU hw)
        rwa [mem_rightConjugate_iff] at this
      have hQw : rightConjugate (rightConjugate P g) w =
          rightConjugate (rightConjugate P (g * w * g⁻¹)) g := by
        rw [rightConjugate_mul, rightConjugate_mul]
        congr 1
        group
      have hT' : rightConjugate P (g * w * g⁻¹) ∈ 𝒯 := hconj _ (hPsS _ hw')
      have hne : rightConjugate P (g * w * g⁻¹) ≠ P := by
        intro heq
        apply hwN
        rw [← rightConjugate_eq_self_iff, hQw, heq]
      have hcomm1 := h.comm _ hT' P hP hne
      rw [hQw, mem_rightConjugate_iff] at hy
      rw [mem_rightConjugate_iff] at hx
      have hc1 := commute_of_commutator_eq_bot hcomm1 hy hx
      have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
        calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * y * g⁻¹) := hc1
          _ = g * (x * y) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h2)).symm
    obtain ⟨z, hzQ, hz1, hzH⟩ :=
      exists_ne_one_mem_of_centralizers_le hQ2 hrQ hr2 hW4 hWe hcommQ hWC
    exact hzg z hzQ hz1 hzH
  have hfour : ∀ E : Subgroup G, E ≤ P → Nat.card E = 4 → IsElemAbelian 2 E →
      Nat.card ((E.subgroupOf P).map φ) = 4 ∧ IsElemAbelian 2 ((E.subgroupOf P).map φ) ∧
        (E.subgroupOf P).map φ ≤ U := by
    intro E hEP hE4 hEe
    refine ⟨?_, isElemAbelian_map (isElemAbelian_of_mulEquiv (subgroupOfEquivOfLe hEP).symm hEe) φ,
      map_le_range φ _⟩
    rw [card_map_of_injective hφinj, ← hE4]
    exact Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv
  have hCe : ∀ e : P, (∀ p ∈ P, p * e = e * p) → (e : G) ≠ 1 → (e : G) ^ 2 = 1 →
      centralizer ({φ e} : Set G) ≤ H := by
    intro e heZ he1 he2
    rw [hφ]
    exact beta1 IH h hZ hP hbig hconj e.2 heZ (orderOf_eq_prime he2 he1)
      (S.mul_mem (S.mul_mem (S.inv_mem hdS) (hPS e.2)) hdS) rfl (hcomm_d e e.2 e e.2)
      (fun h' => he1 (hinter e e.2 h'))
  by_cases hE : ∃ z ∈ P, (∀ p ∈ P, p * z = z * p) ∧ z * z = 1 ∧ z ≠ 1 ∧ z ≠ a
  ·
    obtain ⟨z, hzP, hzZ, hzz, hz1, hza⟩ := hE
    have hcz : Commute a z := hzZ a haP
    set E := commutingPairSubgroup a z haa hzz hcz with hEdef
    have hE4 : Nat.card E = 4 := by
      rw [commutingPairSubgroup_card ha1 hz1 (Ne.symm hza)]
      norm_num
    have hEP : E ≤ P := by
      intro e he
      rcases mem_commutingPairSubgroup.mp he with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact haP
      · exact hzP
      · exact P.mul_mem haP hzP
    have hEZ : ∀ e ∈ E, ∀ p ∈ P, p * e = e * p := by
      intro e he p hp
      rcases mem_commutingPairSubgroup.mp he with rfl | rfl | rfl | rfl
      · rw [mul_one, one_mul]
      · exact haZ p hp
      · exact hzZ p hp
      · calc p * (a * z) = (p * a) * z := by group
          _ = (a * p) * z := by rw [haZ p hp]
          _ = a * (p * z) := by group
          _ = a * (z * p) := by rw [hzZ p hp]
          _ = a * z * p := by group
    have hEe : IsElemAbelian 2 E := by
      refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => commutingPairSubgroup_sq hx⟩
      change (x : G) * y = y * x
      exact hEZ y y.2 x (hEP x.2)
    obtain ⟨hW4, hWe, hWU⟩ := hfour E hEP hE4 hEe
    apply hβ4 _ hWU hW4 hWe
    rintro _ ⟨e, he, rfl⟩ hw1
    have he' : (e : G) ∈ E := mem_subgroupOf.mp he
    have he1 : (e : G) ≠ 1 := fun h' => hw1 (by rw [show e = 1 from Subtype.ext h', map_one])
    exact hCe e (hEZ e he') he1 (commutingPairSubgroup_sq he')
  ·
    push Not at hE
    have hnshape : ∀ y : G, ¬ SylowShape (rightConjugate P y) := by
      intro y hshape
      have hshape₁ : SylowShape P := by
        have := hshape.rightConjugate y⁻¹
        rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
      obtain ⟨z₁, hz₁, z₂, hz₂, hz₁1, hz₂1, hz₁₂⟩ :=
        CFSG.ComponentClassification.AschbacherToolkit.BenderExt.ExtCore.exists_two_ne_one
          (Z := center P) (by have := hshape₁.card_center; omega)
      have hmem : ∀ z ∈ center P, (z : G) ∈ P ∧ (∀ p ∈ P, p * z = z * p) ∧
          (z : G) * z = 1 := by
        intro z hz
        refine ⟨z.2, fun p hp => ?_, ?_⟩
        · exact congrArg Subtype.val (mem_center_iff.mp hz ⟨p, hp⟩)
        · have := congrArg Subtype.val (hshape₁.center_sq z hz)
          simpa [sq] using this
      obtain ⟨hz₁P, hz₁Z, hz₁z⟩ := hmem z₁ hz₁
      obtain ⟨hz₂P, hz₂Z, hz₂z⟩ := hmem z₂ hz₂
      have e₁ := hE _ hz₁P hz₁Z hz₁z (fun h' => hz₁1 (Subtype.ext h'))
      have e₂ := hE _ hz₂P hz₂Z hz₂z (fun h' => hz₂1 (Subtype.ext h'))
      exact hz₁₂ (Subtype.ext (e₁.trans e₂.symm))
    have hII : ∀ y : G, rightConjugate P y ≤ S →
        rightConjugate P y = P ∨ rightConjugate P y = rightConjugate P d := by
      intro y hy
      by_contra hcon
      push Not at hcon
      obtain ⟨hne1, hne2⟩ := hcon
      have hR₂𝒯 : rightConjugate P y ∈ 𝒯 := hconj y hy
      have hc1 := h.comm _ hR₂𝒯 P hP hne1
      have hc2 := h.comm _ hR₂𝒯 _ hPd𝒯 hne2
      obtain ⟨E₀, hE₀P, hE₀4, hE₀e⟩ := exists_four_le hbig.1
      obtain ⟨hW4, hWe, hWU⟩ := hfour E₀ hE₀P hE₀4 hE₀e
      apply hβ4 _ hWU hW4 hWe
      rintro _ ⟨e, he, rfl⟩ hw1
      have hR₂w : rightConjugate P y ≤ centralizer ({φ e} : Set G) := by
        intro q hq
        rw [mem_centralizer_singleton_iff, hφ]
        have h1 : q * e = e * q := commute_of_commutator_eq_bot hc1 hq e.2
        have h2 : q * (d⁻¹ * e * d) = (d⁻¹ * e * d) * q :=
          commute_of_commutator_eq_bot hc2 hq (hmemd e e.2)
        calc q * ((e : G) * (d⁻¹ * e * d)) = (q * e) * (d⁻¹ * e * d) := by group
          _ = (e * q) * (d⁻¹ * e * d) := by rw [h1]
          _ = e * (q * (d⁻¹ * e * d)) := by group
          _ = e * ((d⁻¹ * e * d) * q) := by rw [h2]
          _ = (e : G) * (d⁻¹ * e * d) * q := by group
      have hwZ : φ e ∉ center G := by
        intro hc
        apply hZ _ hc
        refine orderOf_eq_prime ?_ hw1
        have he2 : e ^ 2 = 1 := Subtype.ext (by
          have := hE₀e.2 _ (mem_subgroupOf.mp he)
          simpa using this)
        rw [← map_pow, he2, map_one]
      have hconj₂ : ∀ g' : G, rightConjugate (rightConjugate P y) g' ≤ S →
          rightConjugate (rightConjugate P y) g' ∈ 𝒯 := fun g' hg' => by
        rw [rightConjugate_mul] at hg' ⊢
        exact hconj _ hg'
      obtain ⟨h₂, -, -, -, hcase⟩ :=
        cstep26 IH h hR₂𝒯 (hbig.rightConjugate y) hconj₂ hwZ hR₂w
      rcases hcase with hle | ⟨-, hshape⟩
      · exact hle
      · exfalso
        apply hnshape (y * h₂)
        rwa [← rightConjugate_mul]
    set Sq := Subgroup.closure ((fun r => r ^ 2) '' (P : Set G)) with hSqdef
    have hSqP : Sq ≤ P :=
      (Subgroup.closure_le P).mpr (by rintro _ ⟨r, hr, rfl⟩; exact pow_mem hr 2)
    have hSqconj : ∀ p ∈ P, ∀ y ∈ Sq, p * y * p⁻¹ ∈ Sq := by
      intro p hp y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        apply Subgroup.subset_closure
        refine ⟨p * r * p⁻¹, P.mul_mem (P.mul_mem hp hr) (P.inv_mem hp), ?_⟩
        simp only [sq]
        group
      | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
      | mul x y _ _ hx hy =>
        have : p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) := by group
        rw [this]
        exact mul_mem hx hy
      | inv x _ hx =>
        have : p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem hx
    have hSqN : P ≤ normalizer (Sq : Set G) := by
      intro p hp
      rw [mem_normalizer_iff]
      intro y
      constructor
      · exact hSqconj p hp y
      · intro hy
        have := hSqconj p⁻¹ (P.inv_mem hp) _ hy
        simpa [mul_assoc] using this
    have hSqne : Sq ≠ ⊥ := by
      intro h'
      have : r₀ ^ 2 ∈ Sq := Subgroup.subset_closure ⟨r₀, hr₀P, rfl⟩
      rw [h', mem_bot] at this
      exact hr₀2 this
    have hJ := inf_center_ne_bot_of_le hP2 hSqP hSqN hSqne
    obtain ⟨z, hzJ, hz2⟩ :=
      CFSG.ComponentClassification.AschbacherToolkit.BenderExt.ExtCore.exists_orderOf_eq_two
        hP2 (inf_le_left.trans hSqP) hJ
    have hzSq := (mem_inf.mp hzJ).1
    have hzP : z ∈ P := hSqP hzSq
    have hzZ : ∀ p ∈ P, p * z = z * p := fun p hp =>
      mem_centralizer_iff.mp (mem_inf.mp (mem_inf.mp hzJ).2).2 p hp
    have hzz : z * z = 1 := by rw [← sq, ← hz2]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := fun h' => by rw [h', orderOf_one] at hz2; omega
    have hza : z = a := hE z hzP hzZ hzz hz1
    have haSq : a ∈ Sq := hza ▸ hzSq
    have hsqN : ∀ u ∈ U, u ^ 2 ∈ normalizer ((rightConjugate P g : Subgroup G) : Set G) := by
      intro u hu
      have huS : g * u * g⁻¹ ∈ S := by
        have := hUSg hu
        rwa [mem_rightConjugate_iff] at this
      set s := g * u * g⁻¹ with hsdef
      have hs2N : s ^ 2 ∈ normalizer (P : Set G) := by
        rw [← rightConjugate_eq_self_iff]
        rcases hII s (hPsS s huS) with h1 | h1
        · rw [sq, ← rightConjugate_mul, h1, h1]
        · rcases hII (d * s) (hPsS _ (S.mul_mem hdS huS)) with h2 | h2
          · rw [sq, ← rightConjugate_mul, h1, rightConjugate_mul, h2]
          · exfalso
            apply hPdne
            have h3 : rightConjugate P (d * s) = rightConjugate P s := h2.trans h1.symm
            have h4 := congrArg (fun K => rightConjugate K s⁻¹) h3
            simp only [rightConjugate_mul, mul_inv_cancel_right, mul_inv_cancel,
              rightConjugate_one] at h4
            exact h4
      rw [← rightConjugate_eq_self_iff] at hs2N ⊢
      have e : u ^ 2 = g⁻¹ * s ^ 2 * g := by rw [hsdef, sq, sq]; group
      rw [e, rightConjugate_mul, show g * (g⁻¹ * s ^ 2 * g) = s ^ 2 * g by group,
        ← rightConjugate_mul, hs2N]
    have hφN : ∀ y (hy : y ∈ Sq), φ ⟨y, hSqP hy⟩ ∈
        normalizer ((rightConjugate P g : Subgroup G) : Set G) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        have : (⟨r ^ 2, hSqP (Subgroup.subset_closure ⟨r, hr, rfl⟩)⟩ : P) = (⟨r, hr⟩ : P) ^ 2 :=
          Subtype.ext (by simp)
        rw [this, map_pow]
        exact hsqN _ ⟨⟨r, hr⟩, rfl⟩
      | one =>
        have : (⟨1, hSqP (one_mem _)⟩ : P) = 1 := rfl
        rw [this, map_one]
        exact one_mem _
      | mul x y hx hy ihx ihy =>
        have : (⟨x * y, hSqP (mul_mem hx hy)⟩ : P) = ⟨x, hSqP hx⟩ * ⟨y, hSqP hy⟩ := rfl
        rw [this, map_mul]
        exact mul_mem ihx ihy
      | inv x hx ihx =>
        have : (⟨x⁻¹, hSqP (inv_mem hx)⟩ : P) = (⟨x, hSqP hx⟩ : P)⁻¹ := rfl
        rw [this, map_inv]
        exact inv_mem ihx
    have htN := hφN a haSq
    set t := φ ⟨a, hSqP haSq⟩ with htdef
    have htt : t * t = 1 := by
      rw [htdef, ← map_mul]
      have : (⟨a, hSqP haSq⟩ : P) * ⟨a, hSqP haSq⟩ = 1 := Subtype.ext haa
      rw [this, map_one]
    have hQ2 : IsPGroup 2 (rightConjugate P g) := hP2.map _
    have hQne : rightConjugate P g ≠ ⊥ := by
      intro h'
      have : g⁻¹ * r₀ * g ∈ rightConjugate P g := by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hr₀P
      rw [h', mem_bot] at this
      apply hr₀2
      have : r₀ = 1 := by
        have e : r₀ = g * (g⁻¹ * r₀ * g) * g⁻¹ := by group
        rw [e, this]
        group
      rw [this, one_pow]
    obtain ⟨z', hz'Q, hz'1, -, hz't⟩ :=
      exists_center_commute hQ2 hQne (isPGroup_zpowers_of_mul_self htt) htN
    have hCt : centralizer ({t} : Set G) ≤ H := by
      have := hCe ⟨a, hSqP haSq⟩ haZ ha1 (by rw [sq]; exact haa)
      exact this
    exact hzg z' hz'Q hz'1 (hCt (mem_centralizer_singleton_iff.mpr hz't))

theorem false_of_beta26 (IH : Statement26 (Nat.card G - 1)) (h : HypCore S 𝒯)
    (hZ : ∀ c ∈ center G, orderOf c ≠ 2) {P : Subgroup G} (hP : P ∈ 𝒯) (hbig : IsBig P)
    (hconj : ∀ g : G, rightConjugate P g ≤ S → rightConjugate P g ∈ 𝒯) {a b : G}
    (haP : a ∈ P) (haZ : ∀ p ∈ P, p * a = a * p) (ha2 : orderOf a = 2) (hbS : b ∈ S) {w : G}
    (hbw : b = w⁻¹ * a * w) (hab : a * b = b * a) (hba : b ≠ a) {k : G}
    (hk : k ∉ fusionGen (memberSet 𝒯))
    (hxk : k * (a * b) * k⁻¹ ∈ fusionGen (memberSet 𝒯)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := memberSet 𝒯 with hΓdef
  set H := fusionGen Γ with hHdef
  have hΓS : Γ ⊆ S := memberSet_subset h
  have ha1 : a ≠ 1 := fun h' => by rw [h', orderOf_one] at ha2; omega
  have haΓ : a ∈ Γ := mem_memberSet hP haP ha1
  have haa : a * a = 1 := by rw [← sq, ← ha2]; exact pow_orderOf_eq_one a
  have hbb : b * b = 1 := by
    rw [hbw]
    calc w⁻¹ * a * w * (w⁻¹ * a * w) = w⁻¹ * (a * a) * w := by group
      _ = 1 := by rw [haa]; group
  have hab1 : a * b ≠ 1 := fun h' => hba (by
    calc b = a * (a * b) := by rw [← mul_assoc, haa, one_mul]
      _ = a := by rw [h', mul_one])
  have hbP : b ∉ P := fun hbP => hk
    ((mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS
      (mem_memberSet hP (P.mul_mem haP hbP) hab1) k).mp
      (by rw [mem_rightConjugate_iff]; exact hxk))
  have hbΓ : b ∈ Γ := by
    have := h.closed a haΓ w (by rw [← hbw]; exact hbS)
    rwa [← hbw] at this
  have hbC : ∀ p ∈ P, p * b = b * p := by
    obtain ⟨-, T, hT, hbT⟩ := hbΓ
    have hTP : T ≠ P := fun h' => hbP (h' ▸ hbT)
    exact fun p hp => (commute_of_commutator_eq_bot (h.comm T hT P hP hTP) hbT hp).symm
  have hxx : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by rw [← mul_assoc, haa, one_mul, hbb]
  have hxZ : a * b ∉ center G := fun hc =>
    hZ _ hc (orderOf_eq_prime (by rw [sq]; exact hxx) hab1)
  have hPx : P ≤ centralizer ({a * b} : Set G) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    calc p * (a * b) = (p * a) * b := by group
      _ = (a * p) * b := by rw [haZ p hp]
      _ = a * (p * b) := by group
      _ = a * (b * p) := by rw [hbC p hp]
      _ = a * b * p := by group
  obtain ⟨h₀, hh₀, hAS, hsyl, -⟩ := cstep26 IH h hP hbig hconj hxZ hPx
  have hmemA : ∀ y ∈ S, y * (a * b) = (a * b) * y → h₀⁻¹ * y * h₀ ∈ S := by
    intro y hyS hyx
    apply hAS
    rw [mem_rightConjugate_iff]
    have : h₀ * (h₀⁻¹ * y * h₀) * h₀⁻¹ = y := by group
    rw [this]
    exact mem_inf.mpr ⟨hyS, mem_centralizer_singleton_iff.mpr hyx⟩
  have hP₁S : rightConjugate P h₀ ≤ S := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have := hmemA _ (h.le P hP hy) (mem_centralizer_singleton_iff.mp (hPx hy))
    simpa [mul_assoc] using this
  have hmemP₁ : ∀ y, h₀⁻¹ * y * h₀ ∈ rightConjugate P h₀ ↔ y ∈ P := fun y => by
    rw [mem_rightConjugate_iff]
    simp [mul_assoc]
  have hconj_comm : ∀ {u v : G}, u * v = v * u →
      (h₀⁻¹ * u * h₀) * (h₀⁻¹ * v * h₀) = (h₀⁻¹ * v * h₀) * (h₀⁻¹ * u * h₀) := by
    intro u v huv
    calc (h₀⁻¹ * u * h₀) * (h₀⁻¹ * v * h₀) = h₀⁻¹ * (u * v) * h₀ := by group
      _ = h₀⁻¹ * (v * u) * h₀ := by rw [huv]
      _ = (h₀⁻¹ * v * h₀) * (h₀⁻¹ * u * h₀) := by group
  have hab' : h₀⁻¹ * (a * b) * h₀ = (h₀⁻¹ * a * h₀) * (h₀⁻¹ * b * h₀) := by group
  have hk' : k * h₀ ∉ H := fun h' => hk (by
    have := H.mul_mem h' (H.inv_mem hh₀)
    rwa [mul_inv_cancel_right] at this)
  refine false_of_beta26_pos IH h hZ (hconj h₀ hP₁S) (hbig.rightConjugate h₀)
    (fun g' hg' => by
      rw [rightConjugate_mul] at hg' ⊢
      exact hconj _ hg')
    ((hmemP₁ a).mpr haP)
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ : ∃ q ∈ P, p = h₀⁻¹ * q * h₀ := by
        rw [mem_rightConjugate_iff] at hp
        exact ⟨_, hp, by group⟩
      exact hconj_comm (haZ q hq))
    (by rw [show h₀⁻¹ * a * h₀ = MulAut.conj h₀⁻¹ a by simp, MulEquiv.orderOf_eq]; exact ha2)
    (hmemA b hbS (by
      calc b * (a * b) = (b * a) * b := by group
        _ = (a * b) * b := by rw [hab]))
    (w := h₀⁻¹ * w * h₀) (by rw [hbw]; group) (hconj_comm hab)
    (fun h' => hbP ((hmemP₁ b).mp h')) (by rw [← hab']; exact hsyl) (k := k * h₀) hk' ?_
  rw [← hab']
  have : k * h₀ * (h₀⁻¹ * (a * b) * h₀) * (k * h₀)⁻¹ = k * (a * b) * k⁻¹ := by group
  rw [this]
  exact hxk

end CFSG.ComponentClassification.Asc76.L26
