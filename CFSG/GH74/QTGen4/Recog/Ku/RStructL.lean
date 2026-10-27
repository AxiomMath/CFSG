module

public import CFSG.GH74.QTGen4.Recog.Ku.RStructC
public import CFSG.GH74.QTGen4.Recog.Ku.RStructJ

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem isElemAbelian_of_sq {E : Subgroup G} (hE : ∀ x ∈ E, x * x = 1) : IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => by rw [pow_two]; exact hE x hx⟩
  apply Subtype.ext
  have ha := hE a a.2
  have hb := hE b b.2
  have hab := hE (a * b) (mul_mem a.2 b.2)
  have h1 : ((a : G) * b)⁻¹ = (a : G) * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
  exact h1.symm

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem le_of_E_data (h : KuHyp G T M H P z) {E E' : Subgroup G}
    (hE : E ≤ kuR T M ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧ E ⊓ pCoreOf 2 M = kuV2 T M)
    (hE' : E' ≤ kuR T M ∧ IsElemAbelian 2 E' ∧ Nat.card E' = 16 ∧
      E' ⊓ pCoreOf 2 M = kuV2 T M) : E' ≤ E := by
  have hsup := h.E_sup_pCore hE
  obtain ⟨hER, hEel, -, hEV⟩ := hE
  obtain ⟨hER', hEel', -, hEV'⟩ := hE'
  have hVR : pCoreOf 2 M ≤ kuR T M := h.pCore_le_kuR
  have hV2E : kuV2 T M ≤ E := by
    rw [← hEV]; exact inf_le_left
  intro x hx'
  by_cases hxV : x ∈ pCoreOf 2 M
  · have : x ∈ kuV2 T M := by rw [← hEV']; exact ⟨hx', hxV⟩
    exact hV2E this
  · have hxR : x ∈ kuR T M := hER' hx'
    have hxx : x * x = 1 := by have := hEel'.2 x hx'; rwa [pow_two] at this
    have hxmem : x ∈ E ⊔ pCoreOf 2 M := by rw [hsup]; exact hxR
    have hnorm : E ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := fun e he =>
      h.kuR_normalizer (hER he)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right E _ hnorm] at hxmem
    obtain ⟨e, he, v, hv, rfl⟩ := hxmem
    have hee : e * e = 1 := by have := hEel.2 e he; rwa [pow_two] at this
    have heV : e ∉ pCoreOf 2 M := fun hh => hxV (mul_mem hh hv)
    have hev : e⁻¹ * (e * v) ∈ pCoreOf 2 M := by simpa using hv
    have := h.invol_coset_subset (hER he) heV hee hxx hev
    have hvE : e⁻¹ * (e * v) ∈ E := hV2E this
    have e1 : e * v = e * (e⁻¹ * (e * v)) := by group
    show e * v ∈ E
    rw [e1]
    exact mul_mem he hvE

theorem E_unique (h : KuHyp G T M H P z) {E E' : Subgroup G}
    (hE : E ≤ kuR T M ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧ E ⊓ pCoreOf 2 M = kuV2 T M)
    (hE' : E' ≤ kuR T M ∧ IsElemAbelian 2 E' ∧ Nat.card E' = 16 ∧
      E' ⊓ pCoreOf 2 M = kuV2 T M) : E = E' :=
  le_antisymm (h.le_of_E_data hE' hE) (h.le_of_E_data hE hE')

omit [Finite G] in
theorem kuR_le_normalizer_kuV2 (h : KuHyp G T M H P z) {r : G} (hr : r ∈ kuR T M) :
    r ∈ Subgroup.normalizer (kuV2 T M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have key : ∀ w ∈ kuV2 T M, r * w * r⁻¹ = w := fun w hw => by
    rw [← h.kuV2_comm hw hr]; group
  constructor
  · intro hv; rw [key v hv]; exact hv
  · intro hv
    have hc := h.kuV2_comm hv hr
    have e1 : r * v = r * (r * v * r⁻¹) := by
      calc r * v = (r * v * r⁻¹) * r := by group
        _ = r * (r * v * r⁻¹) := hc
    have e2 : v = r * v * r⁻¹ := mul_left_cancel e1
    rw [e2]; exact hv

theorem conj_mem_kuR_of_mem (h : KuHyp G T M H P z) {g : G}
    (hg : g ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) {r : G} (hr : r ∈ kuR T M) :
    g * r * g⁻¹ ∈ kuR T M := by
  obtain ⟨hgM, hgN⟩ := hg
  set R' : Subgroup G := (kuR T M).map (MulAut.conj g).toMonoidHom with hR'
  set B : Subgroup G := oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G) with hB
  have hRB : kuR T M ≤ B := fun r hr =>
    ⟨(show r ∈ kuR T M from hr).2, h.kuR_le_normalizer_kuV2 hr⟩
  have hR'B : R' ≤ B := by
    rintro x ⟨r, hr, rfl⟩
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (h.M_le_normalizer_oTwoUpper hgM) r).mp
        (show r ∈ kuR T M from hr).2
      simpa using this
    · have : (MulAut.conj g).toMonoidHom r = g * r * g⁻¹ := rfl
      rw [this]
      exact mul_mem (mul_mem hgN (h.kuR_le_normalizer_kuV2 hr)) (Subgroup.inv_mem _ hgN)
  have hBN : B ≤ Subgroup.normalizer (kuR T M : Set G) := fun x hx => h.normalizer_kuR_of_X hx
  have hcardR : Nat.card (kuR T M) = 2 ^ 6 := by rw [h.card_kuR]; norm_num
  have hcardR' : Nat.card R' = 2 ^ 6 := by
    rw [hR', Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_kuR]; norm_num
  have hpR : IsPGroup 2 (kuR T M) := IsPGroup.of_card hcardR
  have hpR' : IsPGroup 2 R' := IsPGroup.of_card hcardR'
  have hK : IsPGroup 2 (kuR T M ⊔ R' : Subgroup G) :=
    hpR.to_sup_of_normal_left' hpR' (fun x hx => hBN (hR'B hx))
  have hKB : (kuR T M ⊔ R' : Subgroup G) ≤ B := sup_le hRB hR'B
  have hdvd : Nat.card (kuR T M ⊔ R' : Subgroup G) ∣ 192 := by
    have := Subgroup.card_dvd_of_le hKB
    rwa [hB, h.card_L_inf_normalizer_kuV2] at this
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hn6 : n ≤ 6 := by
    by_contra hc
    push Not at hc
    have h1 : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 hc
    rw [← hn] at h1
    have := h1.trans hdvd
    omega
  have hle : Nat.card (kuR T M ⊔ R' : Subgroup G) ≤ Nat.card (kuR T M) := by
    rw [hn, hcardR]; exact Nat.pow_le_pow_right (by norm_num) hn6
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : kuR T M ≤ kuR T M ⊔ R') hle
  have : g * r * g⁻¹ ∈ R' := ⟨r, hr, rfl⟩
  rw [heq]
  exact Subgroup.mem_sup_right this

theorem M_inf_normalizer_V2_le_normalizer_E (h : KuHyp G T M H P z) {E : Subgroup G}
    (hE : E ≤ kuR T M ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧ E ⊓ pCoreOf 2 M = kuV2 T M) :
    M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  intro g hg
  obtain ⟨hER, hEel, hEc, hEV⟩ := hE
  obtain ⟨hgM, hgN⟩ := hg
  have hgV : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := h.mem_normalizer_V_of_mem_M hgM
  set E' : Subgroup G := E.map (MulAut.conj g).toMonoidHom with hE'
  have hconj : ∀ x, (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := fun x => rfl
  have hE'R : E' ≤ kuR T M := by
    rintro x ⟨e, he, rfl⟩
    rw [hconj]
    exact h.conj_mem_kuR_of_mem ⟨hgM, hgN⟩ (hER he)
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    rintro x ⟨e, he, rfl⟩
    rw [hconj]
    have hee : e * e = 1 := by have := hEel.2 e he; rwa [pow_two] at this
    calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [hee]; group
  have hE'c : Nat.card E' = 16 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]
  have hE'V : E' ⊓ pCoreOf 2 M = kuV2 T M := by
    ext x
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hxV⟩
      rw [hconj] at hxV ⊢
      have heV : e ∈ pCoreOf 2 M := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) (g * e * g⁻¹)).mp hxV
        have e0 : g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e := by group
        rwa [e0] at this
      have : e ∈ kuV2 T M := by rw [← hEV]; exact ⟨he, heV⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN e).mp this
    · intro hx
      have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ kuV2 T M :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx
      have hxE : g⁻¹ * x * g⁻¹⁻¹ ∈ E := by
        have : g⁻¹ * x * g⁻¹⁻¹ ∈ E ⊓ pCoreOf 2 M := by rw [hEV]; exact hx'
        exact this.1
      refine ⟨⟨_, hxE, ?_⟩, hx.1⟩
      rw [hconj]; group
  have huniq := h.E_unique ⟨hER, hEel, hEc, hEV⟩
    ⟨hE'R, isElemAbelian_of_sq hE'sq, hE'c, hE'V⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [huniq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [huniq] at hx
    obtain ⟨e, he, hex⟩ := hx
    rw [hconj] at hex
    have : e = x := by
      have h2 : g * e * g⁻¹ = g * x * g⁻¹ := hex
      have := mul_right_cancel h2
      exact mul_left_cancel this
    rw [← this]; exact he

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
