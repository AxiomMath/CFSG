module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6SylowC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6QuasiC

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section General

variable {Γ : Type} [Group Γ]

theorem normalizer_le_normalizer_centralizer' (H : Subgroup Γ) :
    normalizer (H : Set Γ) ≤ normalizer (centralizer (H : Set Γ) : Set Γ) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  have h1 := centralizer_map_mulEquiv (MulAut.conj g) H
  rw [MulEquiv.toMonoidHom_eq_coe] at h1
  rw [← h1, hg]

theorem two_dvd_card_of_mem {S : Subgroup Γ} {v : Γ} (hv : v ∈ S) (hv1 : v ≠ 1) {a : ℕ}
    (hva : v ^ 2 ^ a = 1) : 2 ∣ Nat.card S := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hva)
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hi
    exact hv1 hi
  have h2 : orderOf v ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hv
  rw [hi] at h2
  exact (dvd_pow_self 2 hi0).trans h2

theorem mem_normalizer_of_mem_normalizer_centralizer [Finite Γ] {X : Subgroup Γ}
    (hX : Open.IsQuasisimple X)
    (hXN : centralizer (centralizer (X : Set Γ) : Set Γ) ≤ normalizer (X : Set Γ)) {g : Γ}
    (hg : g ∈ normalizer (centralizer (X : Set Γ) : Set Γ)) : g ∈ normalizer (X : Set Γ) := by
  have hperf : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hX.1)
  have := hX.2
  set Y := centralizer (X : Set Γ) with hYdef
  set X' := X.map (MulAut.conj g).toMonoidHom with hX'def
  have hXCY : X ≤ centralizer (Y : Set Γ) := fun x hx => mem_centralizer_iff.mpr fun y hy =>
    (mem_centralizer_iff.mp hy x hx).symm
  have hgCY : g ∈ normalizer (centralizer (Y : Set Γ) : Set Γ) :=
    normalizer_le_normalizer_centralizer' Y hg
  have h1 : X' ≤ normalizer (X : Set Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hXN ((mem_normalizer_iff.mp hgCY x).mp (hXCY hx))
  have h2 : X ≤ normalizer (X' : Set Γ) := by
    intro x hx
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ centralizer (Y : Set Γ) :=
      (mem_normalizer_iff.mp (inv_mem hgCY) x).mp (hXCY hx)
    rw [inv_inv] at hx'
    have hxN := hXN hx'
    rw [mem_normalizer_iff]
    intro y
    have e : g⁻¹ * (x * y * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [mem_map_conj_iff, mem_map_conj_iff, e]
    exact mem_normalizer_iff.mp hxN _
  set D := X ⊓ X' with hDdef
  have hXD : X ≤ normalizer (D : Set Γ) := fun x hx =>
    mem_normalizer_inf (le_normalizer hx) (h2 hx)
  set DX : Subgroup X := D.subgroupOf X
  have : DX.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXD
  set πX := QuotientGroup.mk' (center X)
  have hn : (DX.map πX).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (DX.map πX) with hb | ht
  ·
    exfalso
    have hDZ : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d := by
      intro d hd x hx
      have h3 : πX ⟨d, (mem_inf.mp hd).1⟩ ∈ DX.map πX := ⟨⟨d, (mem_inf.mp hd).1⟩, hd, rfl⟩
      rw [hb, mem_bot] at h3
      have h4 : (⟨d, (mem_inf.mp hd).1⟩ : X) ∈ center X := (QuotientGroup.eq_one_iff _).mp h3
      exact congrArg Subtype.val ((mem_center_iff.mp h4 ⟨x, hx⟩).symm)
    have hX'Y : X' ≤ Y := by
      intro y hy
      refine mem_centralizer_of_commutator_mem_center hperf (h1 hy) fun p hp q hq => ?_
      have hXm : y * p * y⁻¹ * p⁻¹ ∈ X :=
        mul_mem ((mem_normalizer_iff.mp (h1 hy) p).mp hp) (inv_mem hp)
      have hX'm : y * p * y⁻¹ * p⁻¹ ∈ X' := by
        have h3 : p * y⁻¹ * p⁻¹ ∈ X' := (mem_normalizer_iff.mp (h2 hp) y⁻¹).mp (inv_mem hy)
        have h4 := mul_mem hy h3
        simpa only [mul_assoc] using h4
      exact hDZ _ (mem_inf.mpr ⟨hXm, hX'm⟩) q hq
    have hXY : X ≤ Y := by
      intro x hx
      have h3 : g * x * g⁻¹ ∈ X' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
      have h4 := (mem_normalizer_iff.mp (inv_mem hg) (g * x * g⁻¹)).mp (hX'Y h3)
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at h4
    have hsub : ∀ a : X ⧸ center X, a = 1 := by
      intro a
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) a
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp (hXY x.2) y y.2)
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (X ⧸ center X)).exists_pair_ne
    exact hab ((hsub a).trans (hsub b).symm)
  ·
    have hdec : ∀ x ∈ X, ∃ d ∈ D, ∃ z ∈ X, (∀ w ∈ X, z * w = w * z) ∧ x = d * z := by
      intro x hx
      have h3 : πX ⟨x, hx⟩ ∈ DX.map πX := by rw [ht]; exact mem_top _
      obtain ⟨d, hd, hde⟩ := h3
      have hz : d⁻¹ * ⟨x, hx⟩ ∈ center X := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (QuotientGroup.mk d : X ⧸ center X) = QuotientGroup.mk ⟨x, hx⟩ := hde
        rw [this, inv_mul_cancel]
      refine ⟨d, hd, ((d⁻¹ * ⟨x, hx⟩ : X) : Γ), (d⁻¹ * ⟨x, hx⟩ : X).2, fun w hw => ?_, ?_⟩
      · exact congrArg Subtype.val (mem_center_iff.mp hz ⟨w, hw⟩).symm
      · simp
    have hXD' : X ≤ D := by
      rw [← hperf]
      refine commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨d, hd, z, hzX, hz, rfl⟩ := hdec x hx
      obtain ⟨d', hd', z', hz'X, hz', rfl⟩ := hdec y hy
      show d * z * (d' * z') * (d * z)⁻¹ * (d' * z')⁻¹ ∈ D
      rw [mul_commutator_mul_eq (hz d' (mem_inf.mp hd').1) (hz z' hz'X)
        (hz' _ (inv_mem (mem_inf.mp hd).1))]
      exact mul_mem (mul_mem (mul_mem hd hd') (inv_mem hd)) (inv_mem hd')
    have hXX' : X = X' := Subgroup.eq_of_le_of_card_ge (hXD'.trans inf_le_right) (by
      rw [hX'def, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective])
    rw [mem_normalizer_iff_map_conj_eq]
    exact hXX'.symm

end General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_mem_normalizer_oddQuotImageC {L K : Subgroup G} {n : centralizer (K : Set G)}
    (hn : (n : G) ∈ normalizer (L : Set G)) :
    QuotientGroup.mk' (standardComponentOddCore (centralizer (K : Set G))) n ∈
      normalizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K)) := by
  have hX₀G₁ : u3X₀ L K ≤ centralizer (K : Set G) := by
    refine (commutator_le).mpr fun x hx y hy => ?_
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).2 (mem_inf.mp hy).2)
      (inv_mem (mem_inf.mp hx).2)) (inv_mem (mem_inf.mp hy).2)
  have h1 : (n : G) ∈ normalizer (u3X₀ L K : Set G) := (mem_normalizer_u3X₀ hn n.2).1
  have h2 : n ∈ normalizer ((u3X₀ L K).subgroupOf (centralizer (K : Set G)) :
      Set (centralizer (K : Set G))) := by
    rw [← subgroupOf_normalizer_eq hX₀G₁]
    exact h1
  exact Subgroup.le_normalizer_map _ ⟨n, h2, rfl⟩

namespace Sec3

variable {L T : Subgroup G}

theorem centralizer_centralizer_le_normalizer
    (h3 : Sec3 G L T) {K : Subgroup G} (hKL : K ≤ L) :
    centralizer (u3X₀CentralizerC L K : Set (u3G₁Bar K)) ≤
      normalizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₁ := centralizer (K : Set G)
  set O := standardComponentOddCore G₁
  set π := QuotientGroup.mk' O
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  have hX₀L : u3X₀ L K ≤ L := by
    show ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆ ≤ L
    exact (commutator_le.mpr fun x hx y hy =>
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans inf_le_left
  have hT₀G₁ : T₀ ≤ G₁ := inf_le_right.trans (Subgroup.centralizer_le hKL)
  set T₀' : Subgroup G₁ := T₀.subgroupOf G₁ with hT₀'def
  have hT₀'2 : IsPGroup 2 T₀' := h3.isSylowOf_T₀.isPGroup.comap_subtype
  set NX := (normalizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K))).comap π
  have hT₀'NX : T₀' ≤ NX := fun t ht =>
    mk_mem_normalizer_oddQuotImageC
      (Subgroup.centralizer_le_normalizer _ (mem_inf.mp (mem_subgroupOf.mp ht)).2)
  have hONX : O ≤ NX := fun o ho => by
    have h1 : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    show π o ∈ normalizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K))
    rw [h1]
    exact one_mem _
  have hT₀'Y : ∀ t ∈ T₀', π t ∈ u3X₀CentralizerC L K := by
    intro t ht
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (mem_inf.mp (mem_subgroupOf.mp ht)).2 _ (hX₀L hx))
  intro w hw
  obtain ⟨w₁, rfl⟩ := QuotientGroup.mk'_surjective O w
  have hsyl : IsSylowOf 2 T₀' (O ⊔ T₀') := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hT₀'2, ?_⟩
    rw [relIndex_sup_eq_relIndex_of_normal]
    intro h2
    exact (Nat.not_even_iff_odd.mpr (odd_card_standardComponentOddCore'.of_dvd_nat
      (T₀'.relIndex_dvd_card O))) (even_iff_two_dvd.mpr h2)
  have hconj : T₀'.map (MulAut.conj w₁).toMonoidHom ≤ O ⊔ T₀' := by
    rintro _ ⟨t, ht, rfl⟩
    have hc : π t * π w₁ = π w₁ * π t := (mem_centralizer_iff.mp hw) _ (hT₀'Y t ht)
    have hO : w₁ * t * w₁⁻¹ * t⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 : π (w₁ * t * w₁⁻¹ * t⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
        group
      exact h1
    have e : w₁ * t * w₁⁻¹ = (w₁ * t * w₁⁻¹ * t⁻¹) * t := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e]
    exact mul_mem (mem_sup_left hO) (mem_sup_right ht)
  have hsyl' : IsSylowOf 2 (T₀'.map (MulAut.conj w₁).toMonoidHom) (O ⊔ T₀') := by
    refine isSylowOf_of_card hconj ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj w₁).toMonoidHom)
      (MulAut.conj w₁).injective, hsyl.card_eq]
  obtain ⟨k, hkH, hk⟩ := hsyl.exists_mem_conj hsyl'
  have hn : k⁻¹ * w₁ ∈ normalizer (T₀' : Set G₁) := by
    rw [mem_normalizer_iff]
    intro y
    have e : k⁻¹ * w₁ * y * (k⁻¹ * w₁)⁻¹ = k⁻¹ * (w₁ * y * w₁⁻¹) * k := by group
    have e2 : w₁⁻¹ * (w₁ * y * w₁⁻¹) * w₁ = y := by group
    rw [e, ← hk, mem_map_conj_iff, e2]
  have hnG : ((k⁻¹ * w₁ : G₁) : G) ∈ normalizer (T₀ : Set G) := by
    have h1 : k⁻¹ * w₁ ∈ (normalizer (T₀ : Set G)).subgroupOf G₁ := by
      rw [subgroupOf_normalizer_eq hT₀G₁]
      exact hn
    exact h1
  have h1 : π (k⁻¹ * w₁) ∈ normalizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K)) :=
    mk_mem_normalizer_oddQuotImageC (h3.normalizer_T₀_le hnG)
  have h2 : π k ∈ normalizer (oddQuotImageC K (u3X₀ L K) : Set (u3G₁Bar K)) :=
    sup_le hONX hT₀'NX hkH
  have e : π w₁ = π k * π (k⁻¹ * w₁) := by rw [map_mul, map_inv, mul_inv_cancel_left]
  rw [e]
  exact mul_mem h2 h1

end Sec3

theorem gms61TightC :
    GMS61TightC := by
  intro G _ _ L T K f hf he h3 hKL hKo hKH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := gms61QuasisimpleC G L T K f hf he h3 hKL hKo hKH
  obtain ⟨e⟩ := he
  set G₁ := centralizer (K : Set G)
  set O := standardComponentOddCore G₁
  set π := QuotientGroup.mk' O
  set Xb := oddQuotImageC K (u3X₀ L K)
  set Yb := u3X₀CentralizerC L K
  have hNN : normalizer (Yb : Set (u3G₁Bar K)) = normalizer (Xb : Set (u3G₁Bar K)) :=
    le_antisymm (fun g hg => mem_normalizer_of_mem_normalizer_centralizer hq
      (h3.centralizer_centralizer_le_normalizer hKL) hg)
      (normalizer_le_normalizer_centralizer' Xb)
  refine ⟨fun gb hgb => ?_, hNN⟩
  by_contra hodd
  apply hgb
  rw [hNN]
  have heven : 2 ∣ Nat.card (Yb ⊓ Yb.map (MulAut.conj gb).toMonoidHom : Subgroup (u3G₁Bar K)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨ub, hub⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hub2 : orderOf (ub : u3G₁Bar K) = 2 := by rw [Subgroup.orderOf_coe]; exact hub
  obtain ⟨hubY, hubY'⟩ := mem_inf.mp ub.2
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O gb
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective O (ub : u3G₁Bar K)
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  obtain ⟨u, hu⟩ : ∃ u, u = y ^ m := ⟨_, rfl⟩
  have hua : u ^ 2 ^ a = 1 := by rw [hu, ← pow_mul, mul_comm, ← hN, pow_orderOf_eq_one]
  have hπu : π u = ub := by
    obtain ⟨j, rfl⟩ := hm
    have hsq : (ub : u3G₁Bar K) ^ 2 = 1 := by rw [← hub2, pow_orderOf_eq_one]
    rw [hu, map_pow, hy, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hu1 : (u : G) ≠ 1 := by
    intro h
    have h1 : (ub : u3G₁Bar K) = 1 := by rw [← hπu, show u = 1 from Subtype.ext h, map_one]
    rw [h1, orderOf_one] at hub2
    norm_num at hub2
  have hua' : (u : G) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val hua
  have huŶ : (u : G) ∈ u3X₀CentralizerPre L K := ⟨u, by show π u ∈ Yb; rw [hπu]; exact hubY, rfl⟩
  have hu'Ŷ : ((g⁻¹ * u * g : G₁) : G) ∈ u3X₀CentralizerPre L K := by
    refine ⟨g⁻¹ * u * g, ?_, rfl⟩
    show π (g⁻¹ * u * g) ∈ Yb
    rw [map_mul, map_mul, map_inv, hπu]
    exact (mem_map_conj_iff Yb (π g) ub).mp hubY'
  have hzp : ∀ v : G, v ^ 2 ^ a = 1 → IsPGroup 2 (zpowers v) := by
    intro v hv
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hv)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have hua'' : ((g⁻¹ * u * g : G₁) : G) ^ 2 ^ a = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have e : (g : G)⁻¹ * u * g = (g : G)⁻¹ * u * (g : G)⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, hua', mul_one, mul_inv_cancel]
  have hsyl := h3.isSylowOf_T₀_centralizerPre hf e hKL hKo hKH
  obtain ⟨c, hcŶ, hc⟩ := exists_conj_le_of_isSylowOf hsyl ((zpowers_le).mpr huŶ) (hzp _ hua')
  obtain ⟨c', hc'Ŷ, hc'⟩ :=
    exists_conj_le_of_isSylowOf hsyl ((zpowers_le).mpr hu'Ŷ) (hzp _ hua'')
  have hv := hc _ (mem_zpowers _)
  have hw := hc' _ (mem_zpowers _)
  obtain ⟨c₁, hc₁, rfl⟩ := hcŶ
  obtain ⟨c₁', hc₁', rfl⟩ := hc'Ŷ
  have hv' : (c₁ : G) * u * (c₁ : G)⁻¹ ∈ T ⊓ centralizer (L : Set G) := hv
  have hw' : (c₁' : G) * ((g : G)⁻¹ * u * g) * (c₁' : G)⁻¹ ∈ T ⊓ centralizer (L : Set G) := hw
  obtain ⟨-, -, htight, hNC, -⟩ := h3.hyp.standard
  have hhN : ((c₁ * g * c₁'⁻¹ : G₁) : G) ∈ normalizer (L : Set G) := by
    rw [← hNC]
    by_contra hhN
    have hodd' := htight _ hhN
    have hvC : (c₁ : G) * u * (c₁ : G)⁻¹ ∈ centralizer (L : Set G) ⊓
        (centralizer (L : Set G)).map
          (MulAut.conj ((c₁ * g * c₁'⁻¹ : G₁) : G)).toMonoidHom := by
      refine mem_inf.mpr ⟨(mem_inf.mp hv').2, ?_⟩
      rw [mem_map_conj_iff]
      have e : ((c₁ * g * c₁'⁻¹ : G₁) : G)⁻¹ * ((c₁ : G) * u * (c₁ : G)⁻¹) *
          ((c₁ * g * c₁'⁻¹ : G₁) : G) = (c₁' : G) * ((g : G)⁻¹ * u * g) * (c₁' : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact (mem_inf.mp hw').2
    have hv1 : (c₁ : G) * u * (c₁ : G)⁻¹ ≠ 1 := by
      intro h1
      apply hu1
      calc (u : G) = (c₁ : G)⁻¹ * ((c₁ : G) * u * (c₁ : G)⁻¹) * c₁ := by group
        _ = 1 := by rw [h1]; group
    have hva : ((c₁ : G) * u * (c₁ : G)⁻¹) ^ 2 ^ a = 1 := by
      rw [conj_pow, hua', mul_one, mul_inv_cancel]
    exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr (two_dvd_card_of_mem hvC hv1 hva))
  have hhX := mk_mem_normalizer_oddQuotImageC (K := K) (L := L) (n := c₁ * g * c₁'⁻¹) hhN
  have hc₁N : π c₁ ∈ normalizer (Xb : Set (u3G₁Bar K)) := Subgroup.centralizer_le_normalizer _ hc₁
  have hc₁'N : π c₁' ∈ normalizer (Xb : Set (u3G₁Bar K)) :=
    Subgroup.centralizer_le_normalizer _ hc₁'
  have e : g = c₁⁻¹ * (c₁ * g * c₁'⁻¹) * c₁' := by group
  rw [e, map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (inv_mem hc₁N) hhX) hc₁'N

end CFSG.ComponentClassification.GMS78
