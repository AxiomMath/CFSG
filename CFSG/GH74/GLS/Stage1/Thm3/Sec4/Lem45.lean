module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Lem44
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

theorem mem_normalizer_cj' {K : Subgroup G} {g w : G}
    (hw : g * w * g⁻¹ ∈ normalizer (K : Set G)) : w ∈ normalizer (cj K g : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hw ⊢
  intro x
  have h1 := hw (g * x * g⁻¹)
  simp only [mem_cj]
  have e2 : g * (w * x * w⁻¹) * g⁻¹ = g * w * g⁻¹ * (g * x * g⁻¹) * (g * w * g⁻¹)⁻¹ := by group
  rw [e2]
  exact h1

theorem cj_cj_of_conj (K : Subgroup G) (g z : G) :
    cj (cj K g) z = cj (cj K (g * z * g⁻¹)) g := by
  rw [cj_cj, cj_cj]; congr 1; group

namespace M4

variable [Finite G]

omit [Finite G] in
theorem K_ne (h : M4 O FA SD z S K₁ K₂) : K₁ ≠ K₂ := by
  intro hne
  obtain ⟨a, ha, b, hb, hab⟩ := h.nonab K₁ (Or.inl rfl)
  have hb' : b ∈ K₂ := hne ▸ hb
  exact hab ((h.cs₁ hb').2.2 a ha)

theorem Q_norm_S (h : M4 O FA SD z S K₁ K₂) {c n : G} (hc : c ∈ S) (hn : n ∈ Qm O S K₁ K₂) :
    c * n * c⁻¹ ∈ Qm O S K₁ K₂ := by
  have hnE : n ∈ Em O z K₁ K₂ := ⟨hn.2, h.S_syl.1 hn.1⟩
  have h1 := h.E_norm (h.S_syl.1 hc) hnE
  have hnS : n ∈ S := hn.1
  have h2 : c * n * c⁻¹ ∈ S := mul_mem (mul_mem hc hnS) (inv_mem hc)
  exact ⟨h2, h1.1⟩

theorem prod_facts (h : M4 O FA SD z S K₁ K₂) {u₁ u₂ : G} (hu₁S : u₁ ∈ S) (hu₂S : u₂ ∈ S)
    (hu₁K : u₁ ∈ K₁) (hu₂K : u₂ ∈ K₂) (hsq₁ : u₁ * u₁ = z) (hsq₂ : u₂ * u₂ = z) :
    (u₁ * u₂) * (u₁ * u₂) = 1 ∧ u₁ * u₂ ≠ 1 ∧ u₁ * u₂ ≠ z := by
  have hcomm : u₁ * u₂ = u₂ * u₁ := h.comm_of_S hu₁K hu₂K hu₁S hu₂S
  refine ⟨?_, ?_, ?_⟩
  · calc u₁ * u₂ * (u₁ * u₂) = (u₁ * u₁) * (u₂ * u₂) := by
          rw [mul_assoc, ← mul_assoc u₂ u₁ u₂, ← hcomm]; group
      _ = 1 := by rw [hsq₁, hsq₂, h.z_sq]
  · intro h1
    have h2 : u₁ = u₂⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hx : u₁ ∈ K₂ := by rw [h2]; exact inv_mem hu₂K
    have := h.sq_of_inter hu₁S hu₁K hx
    rw [hsq₁] at this
    exact h.z_ne this
  · intro h1
    have h2 : u₂ = u₁⁻¹ * z := by
      calc u₂ = u₁⁻¹ * (u₁ * u₂) := by group
        _ = u₁⁻¹ * z := by rw [h1]
    have hx : u₂ ∈ K₁ := by
      rw [h2]; exact mul_mem (inv_mem hu₁K) (h.z_mem_comp (Or.inl rfl))
    have := h.sq_of_inter hu₂S hx hu₂K
    rw [hsq₂] at this
    exact h.z_ne this

end M4

namespace M45

open M4

variable [Finite G]

omit [Finite G] in
theorem c_part (h : M45 O FA SD z S K₁ K₂) {t g : G} (hg : g⁻¹ * z * g = t)
    (htC : t ∈ centralizer ({z} : Set G)) (hI : Intch t K₁ K₂) : Intch (g * z * g⁻¹) K₁ K₂ := by
  obtain ⟨hw₀z, -⟩ := conj_data hg htC
  have hw₀C : g * z * g⁻¹ ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hw₀z
  rcases h.perm _ hw₀C with ⟨h1, h2⟩ | hI'
  · exfalso
    have hn : g * z * g⁻¹ ∈ normalizer (K₁ : Set G) := cj_eq_iff_normalizer.1 h1
    have hzn : z ∈ normalizer (cj K₁ g : Set G) := mem_normalizer_cj' hn
    have htn := h.rec2 t g hg htC K₁ K₁ (Or.inl rfl) (Or.inl rfl) hzn
    have := cj_eq_iff_normalizer.2 htn
    rw [hI.1] at this
    exact h.K_ne this.symm
  · exact hI'

omit [Finite G] in
theorem no_sqrt (h : M45 O FA SD z S K₁ K₂) {t g : G} (hg : g⁻¹ * z * g = t)
    (htC : t ∈ centralizer ({z} : Set G)) (hI : Intch t K₁ K₂) {y : G}
    (hy : y ∈ centralizer ({t} : Set G)) : y * y ≠ z := by
  intro hyz
  have hI' := h.c_part hg htC hI
  have hy' : g * y * g⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    have e1 : z = g * t * g⁻¹ := by rw [← hg]; group
    calc g * y * g⁻¹ * z = g * (y * t) * g⁻¹ := by rw [e1]; group
      _ = g * (t * y) * g⁻¹ := by rw [hyt]
      _ = z * (g * y * g⁻¹) := by rw [e1]; group
  have hsq : (g * y * g⁻¹) * (g * y * g⁻¹) = g * z * g⁻¹ := by
    rw [← hyz]; group
  rcases h.perm _ hy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have : cj K₁ (g * z * g⁻¹) = K₁ := by
      rw [← hsq, ← cj_cj, h1, h1]
    rw [hI'.1] at this
    exact h.K_ne this.symm
  · have : cj K₁ (g * z * g⁻¹) = K₁ := by
      rw [← hsq, ← cj_cj, h1, h2]
    rw [hI'.1] at this
    exact h.K_ne this.symm

theorem lemma45 (h : M45 O FA SD z S K₁ K₂) (hA : H4A O z S K₁ K₂) {t : G} (htS : t ∈ S)
    (htz : IsConj z t) (htne : t ≠ z) (hI : Intch t K₁ K₂) :
    Qm O S K₁ K₂ = zpowers z ∧
      (∀ u ∈ Pm S K₁ K₂, orderOf u = 2 → u ≠ z → IsConj (t * z) u) ∧ ¬ IsConj z (t * z) := by
  obtain ⟨c0, hc0⟩ := isConj_iff.1 htz
  have ht2 : t * t = 1 := by
    rw [← hc0]
    calc c0 * z * c0⁻¹ * (c0 * z * c0⁻¹) = c0 * (z * z) * c0⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have ht1 : t ≠ 1 := by
    intro h1
    apply h.z_ne
    have : c0 * z * c0⁻¹ = 1 := by rw [hc0, h1]
    calc z = c0⁻¹ * (c0 * z * c0⁻¹) * c0 := by group
      _ = 1 := by rw [this]; group
  have htC : t ∈ centralizer ({z} : Set G) := h.S_syl.1 htS
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzt : z * t = t * z := (centralizer_comm htC).symm
  have htnot := h.not_mem_ZsK' ht2 ht1 htne
  have hP₁pg : IsPGroup 2 ↥(S ⊓ K₁) := h.S_pgroup.to_inf_left
  have hex : ∃ y ∈ S ⊓ K₁, y ∉ zpowers z := by
    by_contra hne
    push Not at hne
    have hle : S ⊓ K₁ ≤ zpowers z := fun y hy => hne y hy
    have h1 := Subgroup.card_le_of_le hle
    rw [card_zpowers_of_sq h.z_sq h.z_ne] at h1
    have h2 := (h.zs K₁ (Or.inl rfl)).2
    omega
  obtain ⟨y, hy, hyz⟩ := hex
  obtain ⟨u₁, hu₁mem, hu₁2⟩ := exists_sq_eq_of_unique_inv hP₁pg
    (fun x hx hx2 => h.inv_comp (Or.inl rfl) hx.2 hx2) hy hyz
  have hu₁S : u₁ ∈ S := hu₁mem.1
  have hu₁K : u₁ ∈ K₁ := hu₁mem.2
  have hu₁P : u₁ ∈ Pm S K₁ K₂ := ⟨hu₁S, mem_sup_left hu₁K⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u₂, u₂ = t * u₁ * t := ⟨_, rfl⟩
  have hu₂K : u₂ ∈ K₂ := by
    have : u₁ ∈ cj K₂ t := by rw [hI.2]; exact hu₁K
    have h1 := mem_cj.1 this
    rw [hu₂]; simpa [htinv] using h1
  have hu₂S : u₂ ∈ S := by rw [hu₂]; exact mul_mem (mul_mem htS hu₁S) htS
  have hu₂P : u₂ ∈ Pm S K₁ K₂ := ⟨hu₂S, mem_sup_right hu₂K⟩
  have hu₂2 : u₂ * u₂ = z := by
    rw [hu₂]
    calc t * u₁ * t * (t * u₁ * t) = t * (u₁ * (t * t) * u₁) * t := by group
      _ = t * (u₁ * u₁) * t := by rw [ht2]; group
      _ = t * z * t := by rw [hu₁2]
      _ = z * t * t := by rw [← hzt]
      _ = z := by rw [mul_assoc, ht2, mul_one]
  have hcomm : u₁ * u₂ = u₂ * u₁ := h.comm_of_S hu₁K hu₂K hu₁S hu₂S
  obtain ⟨hu2, hu1, huz⟩ := h.prod_facts hu₁S hu₂S hu₁K hu₂K hu₁2 hu₂2
  obtain ⟨u, hu⟩ : ∃ u, u = u₁ * u₂ := ⟨_, rfl⟩
  rw [← hu] at hu2 hu1 huz
  have huP : u ∈ Pm S K₁ K₂ := by rw [hu]; exact mul_mem hu₁P hu₂P
  have htu₂ : t * u₂ = u₁ * t := by
    rw [hu₂]
    calc t * (t * u₁ * t) = (t * t) * u₁ * t := by group
      _ = u₁ * t := by rw [ht2, one_mul]
  have htu : u₁⁻¹ * (t * u) * u₁ = t * z := by
    rw [hu]
    calc u₁⁻¹ * (t * (u₁ * u₂)) * u₁ = u₁⁻¹ * (t * (u₂ * u₁)) * u₁ := by rw [hcomm]
      _ = u₁⁻¹ * ((t * u₂) * u₁) * u₁ := by group
      _ = u₁⁻¹ * ((u₁ * t) * u₁) * u₁ := by rw [htu₂]
      _ = t * (u₁ * u₁) := by group
      _ = t * z := by rw [hu₁2]
  have hfbal := h.fbal hA t htS htz htne hI u₁ hu₁K hu₁S hu₁2
  rw [← hu₂, ← hu] at hfbal
  have hu_tz : IsConj u (t * z) :=
    hfbal.trans (isConj_iff.2 ⟨u₁⁻¹, by simpa using htu⟩)
  have part1a : ∀ u' ∈ Pm S K₁ K₂, orderOf u' = 2 → u' ≠ z → IsConj (t * z) u' := by
    intro u' hu' ho hne
    obtain ⟨hu'2, hu'1⟩ := orderOf_two_iff.1 ho
    obtain ⟨k, -, hk⟩ := h.f31a u' u hu'.2 huP.2 hu'2 hu2 hu'1 hu1 hne huz
    have hc : IsConj u' u := isConj_iff.2 ⟨k, hk⟩
    exact hu_tz.symm.trans hc.symm
  have part1b : ¬ IsConj z (t * z) := by
    intro hzc
    have hzu : IsConj z u := hzc.trans hu_tz.symm
    exact huz (hA u ((le_sup_left : Pm S K₁ K₂ ≤ Rm O S K₁ K₂) huP) hzu)
  refine ⟨?_, part1a, part1b⟩
  apply le_antisymm ?_ (zpowers_le.2 h.z_mem_Q)
  by_contra hQ
  have hex' : ∃ q ∈ Qm O S K₁ K₂, q ∉ zpowers z := by
    by_contra hne
    push Not at hne
    exact hQ (fun q hq => hne q hq)
  obtain ⟨g, hg⟩ := exists_conj_inv htz
  have hnosq : ∀ y ∈ centralizer ({t} : Set G), y * y ≠ z := fun y hy => h.no_sqrt hg htC hI hy
  have hD₁ := h.hc t htC htz htnot K₁ (Or.inl rfl)
  have hCQ : Qm O S K₁ K₂ ⊓ centralizer ({t} : Set G) ≤ zpowers z := by
    intro y hy
    by_contra hyz'
    have hpg : IsPGroup 2 ↥(Qm O S K₁ K₂ ⊓ centralizer ({t} : Set G)) :=
      (h.S_pgroup.to_inf_left (K := secCent (K₁ ⊔ K₂) (O (K₁ ⊔ K₂)))).to_inf_left
    have huniq : ∀ x ∈ Qm O S K₁ K₂ ⊓ centralizer ({t} : Set G), x * x = 1 → x = 1 ∨ x = z :=
      fun x hx hx2 => h.unique_inv_D htC (Or.inl rfl) hD₁ (h.Q_mem_secCent_comp hx.1 (Or.inl rfl))
        (centralizer_comm (h.Q_le_C hx.1)) (Subgroup.mem_centralizer_singleton_iff.1 hx.2) hx2
    obtain ⟨w, hw, hw2⟩ := exists_sq_eq_of_unique_inv hpg huniq hy hyz'
    exact hnosq w hw.2 hw2
  have hDS : Qm O S K₁ K₂ ⊔ zpowers t ≤ S := sup_le Q_le_S (zpowers_le.2 htS)
  have hDpg : IsPGroup 2 ↥(Qm O S K₁ K₂ ⊔ zpowers t) := h.S_pgroup.to_le hDS
  have hQn : ∀ c ∈ S, c ∈ normalizer (Qm O S K₁ K₂ : Set G) := fun c hc =>
    mem_normalizer_of_both (fun n hn => h.Q_norm_S hc hn) (fun n hn => by
      have := h.Q_norm_S (inv_mem hc) hn
      simpa using this)
  have hDn : ∀ d ∈ Qm O S K₁ K₂ ⊔ zpowers t, ∀ n ∈ Qm O S K₁ K₂,
      d * n * d⁻¹ ∈ Qm O S K₁ K₂ := by
    intro d hd n hn
    have hle : Qm O S K₁ K₂ ⊔ zpowers t ≤ normalizer (Qm O S K₁ K₂ : Set G) :=
      sup_le Subgroup.le_normalizer (zpowers_le.2 (hQn t htS))
    have := (Subgroup.mem_normalizer_iff.1 (hle hd) n).1 hn
    exact this
  have hMc : ∀ m ∈ zpowers z, ∀ d ∈ Qm O S K₁ K₂ ⊔ zpowers t, m * d = d * m := by
    intro m hm d hd
    have hdC : d ∈ centralizer ({z} : Set G) := h.S_syl.1 (hDS hd)
    rcases (mem_zpowers_of_sq h.z_sq).1 hm with rfl | rfl
    · simp
    · exact (centralizer_comm hdC).symm
  obtain ⟨y, hyQ, hyz2, hyc⟩ := exists_mem_comm_mod hDpg le_sup_left hMc hDn hex'
  have hytz : y * t * y⁻¹ * t⁻¹ ∈ zpowers z := hyc t (mem_sup_right (Subgroup.mem_zpowers t))
  rcases (mem_zpowers_of_sq h.z_sq).1 hytz with h1 | h1
  · apply hyz2
    apply hCQ
    refine ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc y * t = (y * t * y⁻¹ * t⁻¹) * (t * y) := by group
      _ = t * y := by rw [h1, one_mul]
  · have h2 : y * t * y⁻¹ = z * t := by
      rw [htinv] at h1
      calc y * t * y⁻¹ = (y * t * y⁻¹ * t) * t⁻¹ := by group
        _ = z * t := by rw [h1, htinv]
    have hconj : IsConj t (z * t) := isConj_iff.2 ⟨y, h2⟩
    apply part1b
    rw [← hzt]
    exact htz.trans hconj

end M45

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
