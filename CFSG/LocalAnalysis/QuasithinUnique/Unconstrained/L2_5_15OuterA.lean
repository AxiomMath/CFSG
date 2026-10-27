module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15OuterGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Common

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

omit [Finite G] in
theorem comm_of_mem_center {S : Subgroup G} {a b : G} (ha : a ∈ centerOf S) (hb : b ∈ S) :
    b * a = a * b :=
  Subgroup.mem_centralizer_iff.mp ha.2 b hb

theorem exists_outer_R (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G))
    (hout : ∃ s ∈ N.S, ¬ Ch1.InducesInner s N.K) :
    ∃ y₀ ∈ centSKz N.S N.K zK, ¬ Ch1.InducesInner y₀ N.K := by
  obtain ⟨s₀, hs₀, hs₀o⟩ := hout
  obtain ⟨s, hs', hc⟩ := exists_SK_mul_centralizes N h F hKt
    (⟨N.S_le_T hs₀, Subgroup.le_normalizer hs₀⟩ : s₀ ∈ T ⊓ Subgroup.normalizer (N.S : Set G))
  refine ⟨s⁻¹ * s₀, mem_centSKz_iff.mpr ⟨N.S.mul_mem (N.S.inv_mem (N.SK_le_S hs')) hs₀,
    fun v hv => (hc v hv).symm⟩, ?_⟩
  intro hin
  apply hs₀o
  have hsin : Ch1.InducesInner s N.K := Ch1.InducesInner.of_mem (N.SK_le_K hs')
  have := inducesInner_mul' hsin hin
  simpa using this

theorem outer_R_sq (h : Lv2513 N t zK) (F : K33Facts N.K) (L : L33Facts N.K) {r : G}
    (hr : r ∈ centSKz N.S N.K zK) (hout : ¬ Ch1.InducesInner r N.K) :
    ∃ c ∈ N.SC, r * r = c * zK := by
  have hf := h.facts2511
  have hKH := H_le_normalizer_K N h F
  have hK0 := N.K0_eq hKH
  have hzKK := zK_mem_K N h F
  rw [mem_centSKz_iff] at hr
  have hrN : r ∈ Subgroup.normalizer (N.K : Set G) := N.S_le_normalizer_K hKH hr.1
  have hz4 := L.z4 zK hzKK (zK_ne_one N hf) (by rw [sq]; exact zK_mul_self N hf) r hrN
    (fun v hv => (hr.2 v hv).symm) hout
  refine ⟨(r * r) * zK⁻¹, ⟨?_, ?_⟩, by group⟩
  · exact N.S.mul_mem (N.S.mul_mem hr.1 hr.1) (N.S.inv_mem (zK_mem_center N hf).1)
  · rw [hK0]
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have h1 := hz4 w hw
    calc w * (r * r * zK⁻¹) = (r * r) * ((r * r)⁻¹ * w * (r * r)) * zK⁻¹ := by group
      _ = (r * r) * (zK⁻¹ * w * zK) * zK⁻¹ := by rw [h1]
      _ = (r * r * zK⁻¹) * w := by group

theorem R_cover_four (h : Lv2513 N t zK) (F : K33Facts N.K) (L : L33Facts N.K) {y₀ : G}
    (hy₀R : y₀ ∈ centSKz N.S N.K zK) (hy₀o : ¬ Ch1.InducesInner y₀ N.K) :
    ∀ r ∈ centSKz N.S N.K zK,
      ∃ i : Fin 4, ∃ c ∈ N.SC, r = c * (![1, zK, y₀, y₀ * zK] i) := by
  intro r hr
  have hKH := H_le_normalizer_K N h F
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  by_cases hin : Ch1.InducesInner r N.K
  · obtain ⟨i, c, hc, hr'⟩ := inner_mem_R_cover N h F hr hin
    fin_cases i
    · exact ⟨0, c, hc, by simpa using hr'⟩
    · exact ⟨1, c, hc, by simpa using hr'⟩
  · have hy₀S : y₀ ∈ N.S := (mem_centSKz_iff.mp hy₀R).1
    have hy₀N : y₀ ∈ Subgroup.normalizer (N.K : Set G) := N.S_le_normalizer_K hKH hy₀S
    have hrN : r ∈ Subgroup.normalizer (N.K : Set G) :=
      N.S_le_normalizer_K hKH (mem_centSKz_iff.mp hr).1
    have hin' := inducesInner_inv_mul_of_not L.aut_card hZK hy₀N hrN hy₀o hin
    have hR' : y₀⁻¹ * r ∈ centSKz N.S N.K zK :=
      (centSKz N.S N.K zK).mul_mem ((centSKz N.S N.K zK).inv_mem hy₀R) hr
    obtain ⟨i, c, hc, hr'⟩ := inner_mem_R_cover N h F hR' hin'
    have hc' : y₀ * c * y₀⁻¹ ∈ N.SC :=
      (Subgroup.mem_normalizer_iff.mp (N.S_le_normalizer_SC hy₀S) c).mp hc
    have hr'' : r = y₀ * (c * (![1, zK] i)) := by
      rw [← hr']
      group
    fin_cases i
    · refine ⟨2, y₀ * c * y₀⁻¹, hc', ?_⟩
      simp only [Fin.zero_eta, Matrix.cons_val_zero] at hr''
      simp only [Matrix.cons_val]
      calc r = y₀ * (c * 1) := hr''
        _ = (y₀ * c * y₀⁻¹) * y₀ := by group
    · refine ⟨3, y₀ * c * y₀⁻¹, hc', ?_⟩
      simp only [Fin.mk_one, Matrix.cons_val_one] at hr''
      simp only [Matrix.cons_val]
      calc r = y₀ * (c * zK) := hr''
        _ = (y₀ * c * y₀⁻¹) * (y₀ * zK) := by group

theorem R_inner_cls (h : Lv2513 N t zK) (F : K33Facts N.K) (hSC : N.SC = Subgroup.zpowers t)
    {r : G} (hr : r ∈ centSKz N.S N.K zK) (hin : Ch1.InducesInner r N.K) :
    r ∈ centerOf N.S ∧ r * r = 1 := by
  obtain ⟨i, c, hc, rfl⟩ := inner_mem_R_cover N h F hr hin
  have hf := h.facts2511
  rw [hSC] at hc
  have ht2 := t_mul_self N hf
  have hz2 := zK_mul_self N hf
  have htZ := t_mem_center N hf
  have hzZ := zK_mem_center N hf
  have hcZ : c ∈ centerOf N.S := by
    rcases mem_zpowers_involution ht2 hc with h1 | h1
    · rw [h1]
      exact (centerOf N.S).one_mem
    · rw [h1]
      exact htZ
  have hcc : c * c = 1 := by
    rcases mem_zpowers_involution ht2 hc with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      exact ht2
  have hgZ : ∀ j : Fin 2, (![1, zK] j) ∈ centerOf N.S := by
    rw [Fin.forall_fin_two]
    exact ⟨by simp, by simpa using hzZ⟩
  have hgg : ∀ j : Fin 2, (![1, zK] j) * (![1, zK] j) = 1 := by
    rw [Fin.forall_fin_two]
    exact ⟨by simp, by simpa using hz2⟩
  refine ⟨(centerOf N.S).mul_mem hcZ (hgZ i), ?_⟩
  have hcomm : c * (![1, zK] i) = (![1, zK] i) * c :=
    (comm_of_mem_center hcZ (hgZ i).1).symm
  calc c * (![1, zK] i) * (c * (![1, zK] i))
      = c * ((![1, zK] i) * c) * (![1, zK] i) := by group
    _ = c * (c * (![1, zK] i)) * (![1, zK] i) := by rw [← hcomm]
    _ = (c * c) * ((![1, zK] i) * (![1, zK] i)) := by group
    _ = 1 := by rw [hcc, hgg i, one_mul]

theorem R_outer_cls (h : Lv2513 N t zK) (F : K33Facts N.K) (L : L33Facts N.K)
    (hSC : N.SC = Subgroup.zpowers t) {r : G} (hr : r ∈ centSKz N.S N.K zK)
    (hout : ¬ Ch1.InducesInner r N.K) : r * r = zK ∨ r * r = t * zK := by
  obtain ⟨c, hc, hrr⟩ := outer_R_sq N h F L hr hout
  rw [hSC] at hc
  rcases mem_zpowers_involution (t_mul_self N h.facts2511) hc with h1 | h1
  · left
    rw [h1, one_mul] at hrr
    exact hrr
  · right
    rw [h1] at hrr
    exact hrr

theorem SC_eq_zpowers_of_outer (h : Lv2513 N t zK) (F : K33Facts N.K) (L : L33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G))
    (hout : ∃ s ∈ N.S, ¬ Ch1.InducesInner s N.K) {x' : G}
    (hx'P : x' ∈ T ⊓ Subgroup.normalizer (N.S : Set G)) (hx'S : x' ∉ N.S) (hx'2 : x' ^ 2 ∈ N.S)
    (hx'c : ∀ v ∈ threeCoreCent N.K zK, x' * v = v * x') : N.SC = Subgroup.zpowers t := by
  have hf := h.facts2511
  have hKH := H_le_normalizer_K N h F
  have hzKK := zK_mem_K N h F
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  obtain ⟨hRle, hcard, hcomm⟩ := SC_sup_conjugate N h F hx'P hx'S hx'2 hx'c
  obtain ⟨y₀, hy₀R, hy₀o⟩ := exists_outer_R N h F hKt hout
  have hy₀S : y₀ ∈ N.S := (mem_centSKz_iff.mp hy₀R).1
  have hzR : zK ∈ centSKz N.S N.K zK :=
    mem_centSKz_iff.mpr ⟨(zK_mem_center N hf).1, fun v hv => threeCoreCent_comm hv⟩
  have hg : ∀ i : Fin 4, (![1, zK, y₀, y₀ * zK] i) ∈ centSKz N.S N.K zK := by
    intro i
    fin_cases i
    · exact (centSKz N.S N.K zK).one_mem
    · exact hzR
    · exact hy₀R
    · exact (centSKz N.S N.K zK).mul_mem hy₀R hzR
  have hbound : Nat.card ↥(centSKz N.S N.K zK) ≤ 4 * Nat.card N.SC :=
    card_le_mul_of_cover (le_sup_left.trans hRle) _ hg (R_cover_four N h F L hy₀R hy₀o)
  have hsq : Nat.card N.SC * Nat.card N.SC ≤ Nat.card ↥(centSKz N.S N.K zK) := by
    rw [← hcard]
    exact Subgroup.card_le_of_le hRle
  have hSC4 : Nat.card N.SC ≤ 4 := Nat.le_of_mul_le_mul_right (hsq.trans hbound) Nat.card_pos
  have hSCne4 : Nat.card N.SC ≠ 4 := by
    intro h4
    have hReq : N.SC ⊔ CFSG.conjugate N.SC x' = centSKz N.S N.K zK := by
      apply Subgroup.eq_of_le_of_card_ge hRle
      rw [hcard, h4]
      rw [h4] at hbound
      exact hbound
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcommSC : IsMulCommutative ↥N.SC :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)
    have hSCcomm : ∀ a ∈ N.SC, ∀ b ∈ N.SC, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : N.SC) ⟨b, hb⟩)
    have hy₀c : ∀ c ∈ N.SC, c * y₀ = y₀ * c := by
      intro c hc
      have hy : y₀ ∈ N.SC ⊔ CFSG.conjugate N.SC x' := hReq ▸ hy₀R
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := mem_sup_of_commute hcomm hy
      calc c * (c₁ * c₂) = (c * c₁) * c₂ := by group
        _ = (c₁ * c) * c₂ := by rw [hSCcomm c hc c₁ hc₁]
        _ = c₁ * (c * c₂) := by group
        _ = c₁ * (c₂ * c) := by rw [hcomm c hc c₂ hc₂]
        _ = (c₁ * c₂) * c := by group
    have hSCk : ∀ c ∈ N.SC, ∀ k ∈ N.SK, k * c = c * k := fun c hc k hk =>
      Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hc) k (N.K_le_K0 (N.SK_le_K hk))
    have hSCS : ∀ c ∈ N.SC, ∀ s ∈ N.S, c * s = s * c := by
      intro c hc s hs'
      by_cases hin : Ch1.InducesInner s N.K
      · obtain ⟨c', hc', k, hk, rfl⟩ := inner_mem_SC_mul_SK N h F hs' hin
        calc c * (c' * k) = (c * c') * k := by group
          _ = (c' * c) * k := by rw [hSCcomm c hc c' hc']
          _ = c' * (c * k) := by group
          _ = c' * (k * c) := by rw [hSCk c hc k hk]
          _ = (c' * k) * c := by group
      · have hsN : s ∈ Subgroup.normalizer (N.K : Set G) := N.S_le_normalizer_K hKH hs'
        have hy₀N : y₀ ∈ Subgroup.normalizer (N.K : Set G) := N.S_le_normalizer_K hKH hy₀S
        have hin' := inducesInner_inv_mul_of_not L.aut_card hZK hy₀N hsN hy₀o hin
        obtain ⟨c', hc', k, hk, hck⟩ :=
          inner_mem_SC_mul_SK N h F (N.S.mul_mem (N.S.inv_mem hy₀S) hs') hin'
        have hs_eq : s = y₀ * (c' * k) := by rw [← hck]; group
        rw [hs_eq]
        calc c * (y₀ * (c' * k)) = (c * y₀) * (c' * k) := by group
          _ = (y₀ * c) * (c' * k) := by rw [hy₀c c hc]
          _ = y₀ * ((c * c') * k) := by group
          _ = y₀ * ((c' * c) * k) := by rw [hSCcomm c hc c' hc']
          _ = y₀ * (c' * (c * k)) := by group
          _ = y₀ * (c' * (k * c)) := by rw [hSCk c hc k hk]
          _ = (y₀ * (c' * k)) * c := by group
    have hSCZ : N.SC ≤ centerOf N.S := fun c hc =>
      ⟨N.SC_le_S hc, Subgroup.mem_centralizer_iff.mpr fun s hs' => (hSCS c hc s hs').symm⟩
    have hSCeqZ : N.SC = centerOf N.S :=
      Subgroup.eq_of_le_of_card_ge hSCZ (by rw [hf.centerS_E4.2, h4])
    have hzSC : zK ∈ N.SC := hSCeqZ ▸ zK_mem_center N hf
    have hzcomm := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hzSC)
    exact zK_ne_one N hf (hZK zK hzKK fun y hy => (hzcomm y (N.K_le_K0 hy)).symm)
  obtain ⟨n, hn⟩ := (N.tuple.sylow.isPGroup.to_le N.SC_le_S).exists_card_eq
  have hSC2 : Nat.card N.SC ≤ 2 := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have h2 : 2 ^ n ≤ 2 := by
        interval_cases n <;> norm_num
      omega
    · have h4 : 4 ≤ 2 ^ n :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
      omega
  exact SC_eq_zpowers N hf hSC2

end Config

end CFSG.QuasithinUnique.Unc25K1
