module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Facts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Q

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem LocalSetting.centralizer_le_of_good {p : ℕ} {M V : Subgroup G} (hp : p.Prime)
    (hS : LocalSetting p M V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (h : 2 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G))) :
    centralizer ({v} : Set G) ≤ M := by
  have hv2 : v ^ 2 = 1 := hS.elemAbelian.2 v hv
  have hnorm : normalizer ((zpowers v : Subgroup G) : Set G) = centralizer ({v} : Set G) :=
    normalizer_zpowers_eq_centralizer_of_sq_eq_one hv2
  have hX1 : zpowers v ≠ ⊥ := fun hbot => hv1 (zpowers_eq_bot.mp hbot)
  have h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer ((zpowers v : Subgroup G) : Set G)) := by
    rw [hnorm]; exact h
  exact hnorm ▸ hS.u2 _ hX1 (isPGroup_two_zpowers_of_sq_eq_one hv2) h2

theorem LocalSetting.hr_of_facts {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop}
    (hp : p.Prime) (hS : LocalSetting p M V) (hF : U4LocalFacts p n M L V sing) :
    ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ M → 2 ^ (4 * n) ≤ U.relIndex V := by
  intro U hUV hUM
  refine hF.ts_index U hUV (fun w hw hw1 => ?_)
  by_contra hns
  apply hUM
  have hcw := hS.centralizer_le_of_good hp (hUV hw) hw1 (hF.nonsing_good w (hUV hw) hw1 hns)
  exact le_trans (centralizer_le (Set.singleton_subset_iff.mpr hw)) hcw

theorem LocalSetting.not_inf_centralizer_le {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop}
    (hS : LocalSetting p M V) (hF : U4LocalFacts p n M L V sing) {g : G} (hg : g ∉ M)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) : ¬ M ⊓ centralizer ({u} : Set G) ≤ cj g M := by
  intro hle
  refine hS.spe g hg (dvd_trans (hF.p_dvd u hu hu1) ?_)
  exact Subgroup.card_dvd_of_le (le_inf inf_le_left hle)


omit [Finite G] in
theorem cj_ne_of_not_mem {M : Subgroup G} (hM : normalizer (M : Set G) = M) {g : G} (hg : g ∉ M) :
    cj g M ≠ M := by
  intro h
  apply hg
  rw [← hM, mem_normalizer_iff]
  intro x
  have h1 : g * x * g⁻¹ ∈ cj g M ↔ x ∈ M := by
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [mem_cj_iff, e]
  rw [← h1, h]

theorem not_inf_centralizer_le_of_dvd {p : ℕ} {M M' : Subgroup G} {u : G}
    (hspe : ¬ p ∣ Nat.card ↥(M ⊓ M'))
    (hdvd : p ∣ Nat.card ↥(M ⊓ centralizer ({u} : Set G))) :
    ¬ M ⊓ centralizer ({u} : Set G) ≤ M' := by
  intro hle
  exact hspe (dvd_trans hdvd (Subgroup.card_dvd_of_le (le_inf inf_le_left hle)))

theorem not_inf_centralizer_le_of_dvd' {p : ℕ} {M M' : Subgroup G} {u : G}
    (hspe : ¬ p ∣ Nat.card ↥(M ⊓ M'))
    (hdvd : p ∣ Nat.card ↥(M' ⊓ centralizer ({u} : Set G))) :
    ¬ M' ⊓ centralizer ({u} : Set G) ≤ M := by
  intro hle
  exact hspe (dvd_trans hdvd (Subgroup.card_dvd_of_le (le_inf hle inf_le_left)))

theorem qProp_base {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop} {g : G} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : U4LocalFacts p n M L V sing)
    (hSg : LocalSetting p (cj g M) (cj g V))
    (hFg : U4LocalFacts p n (cj g M) (cj g L) (cj g V) (fun x => sing (g⁻¹ * x * g)))
    (hg : g ∉ M) (hAM : cj g V ≤ M) :
    ∀ B : Subgroup G, B ≤ cj g V → B.relIndex (cj g V) < 2 ^ (2 * n) →
      V ⊓ centralizer (B : Set G) ≤ centralizer ((cj g V : Subgroup G) : Set G) := by
  have hmono : 2 ^ (2 * n) ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine lemmaQ (k := 2 * n) (M := M) (M' := cj g M) hS.elemAbelian.2 hAM
    (le_of_eq hS.normalizer_eq.symm) (le_of_eq hSg.normalizer_eq.symm)
    (cj_ne_of_not_mem hS.self_normalizing hg) ?_ ?_ ?_
  · intro u hu hu1 hle
    exact absurd hle (hS.not_inf_centralizer_le hF hg hu hu1)
  · intro U' hU' hcU'
    exact le_trans hmono (hSg.hr_of_facts hp hFg U' hU' hcU')
  · intro t ht ht2 a ha hat _
    refine hFg.inv_index t ht ht2 ?_
    intro htc
    apply hat
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_iff.mp htc a ha

theorem qProp_mirror {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop} {g : G} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : U4LocalFacts p n M L V sing)
    (hSg : LocalSetting p (cj g M) (cj g V))
    (hFg : U4LocalFacts p n (cj g M) (cj g L) (cj g V) (fun x => sing (g⁻¹ * x * g)))
    (hg : g ∉ M) (hVM' : V ≤ cj g M) :
    ∀ B : Subgroup G, B ≤ V → B.relIndex V < 2 ^ (2 * n) →
      cj g V ⊓ centralizer (B : Set G) ≤ centralizer (V : Set G) := by
  have hmono : 2 ^ (2 * n) ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine lemmaQ (k := 2 * n) (M := cj g M) (M' := M) hSg.elemAbelian.2 hVM'
    (le_of_eq hSg.normalizer_eq.symm) (le_of_eq hS.normalizer_eq.symm)
    (cj_ne_of_not_mem hS.self_normalizing hg).symm ?_ ?_ ?_
  · intro u hu hu1 hle
    exact absurd hle (not_inf_centralizer_le_of_dvd' (hS.spe g hg) (hFg.p_dvd u hu hu1))
  · intro U' hU' hcU'
    exact le_trans hmono (hS.hr_of_facts hp hF U' hU' hcU')
  · intro t ht ht2 a ha hat _
    refine hF.inv_index t ht ht2 ?_
    intro htc
    apply hat
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_iff.mp htc a ha


theorem unitary_caseII {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop} {g : G} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : U4LocalFacts p n M L V sing)
    (hSg : LocalSetting p (cj g M) (cj g V))
    (hFg : U4LocalFacts p n (cj g M) (cj g L) (cj g V) (fun x => sing (g⁻¹ * x * g)))
    (hAM : cj g V ≤ M) (hAL : cj g V ≤ L ⊔ (M ⊓ centralizer (V : Set G)))
    (hVM' : ¬ V ≤ cj g M) : False := by
  have hAab : IsElemAbelian 2 (cj g V) := hSg.elemAbelian
  have hr' := hSg.hr_of_facts hp hFg
  set B₀ : Subgroup G := cj g V ⊓ (M ⊓ centralizer (V : Set G)) with hB₀
  have hVB0 : V ≤ centralizer (B₀ : Set G) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro b hb
    exact (mem_centralizer_iff.mp hb.2.2 v hv).symm
  have hB0 : 2 ^ (4 * n) ≤ B₀.relIndex (cj g V) :=
    hr' B₀ inf_le_left (fun hle => hVM' (hVB0.trans hle))
  have heq : B₀.relIndex (cj g V) = 2 ^ (4 * n) :=
    le_antisymm (hF.rank_le (cj g V) hAM hAab hAL) hB0
  apply hVM'
  refine hF.generation (cj g V) hAM hAab hAL heq (cj g M) ?_
  intro a haA haC x hx
  have hBaA : B₀ ⊔ zpowers a ≤ cj g V :=
    sup_le inf_le_left ((zpowers_le).mpr haA)
  have hB0Ba : B₀ ≤ B₀ ⊔ zpowers a := le_sup_left
  have hpos : 0 < (B₀ ⊔ zpowers a).relIndex (cj g V) :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (B₀ ⊔ zpowers a).subgroupOf (cj g V)))
  have hpos0 : 0 < B₀.relIndex (cj g V) :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := B₀.subgroupOf (cj g V)))
  have hdvd : (B₀ ⊔ zpowers a).relIndex (cj g V) ∣ B₀.relIndex (cj g V) :=
    relIndex_dvd_of_le_left (cj g V) hB0Ba
  have hne : (B₀ ⊔ zpowers a).relIndex (cj g V) ≠ B₀.relIndex (cj g V) := by
    intro heq'
    have hmul := relIndex_mul_relIndex B₀ (B₀ ⊔ zpowers a) (cj g V) hB0Ba hBaA
    have h1 : B₀.relIndex (B₀ ⊔ zpowers a) = 1 := by
      rw [heq'] at hmul
      exact Nat.eq_of_mul_eq_mul_right hpos0 (by rw [hmul, one_mul])
    have h2 : B₀ ⊔ zpowers a ≤ B₀ := relIndex_eq_one.mp h1
    have haB0 : a ∈ B₀ := h2 (Subgroup.mem_sup_right (mem_zpowers a))
    exact haC haB0.2
  have hlt : (B₀ ⊔ zpowers a).relIndex (cj g V) < 2 ^ (4 * n) := by
    rw [← heq]
    exact lt_of_le_of_ne (Nat.le_of_dvd hpos0 hdvd) hne
  have hCle : centralizer ((B₀ ⊔ zpowers a : Subgroup G) : Set G) ≤ cj g M := by
    by_contra hcon
    exact absurd (hr' _ hBaA hcon) (not_le.mpr hlt)
  refine hCle ?_
  rw [mem_centralizer_iff]
  intro h hh
  have hle : B₀ ⊔ zpowers a ≤ centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · intro b hb
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp hb.2.2 x hx.1).symm
    · rw [zpowers_le, mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.mp hx.2).symm
  have := hle hh
  rw [mem_centralizer_singleton_iff] at this
  exact this


omit [Finite G] in
theorem commutator_le_inf_of_normalizer {A V : Subgroup G} (hAV : A ≤ normalizer (V : Set G))
    (hVA : V ≤ normalizer (A : Set G)) : ⁅A, V⁆ ≤ V ⊓ A := by
  rw [le_inf_iff]
  constructor
  · rw [commutator_le]
    intro a ha v hv
    have h1 : a * v * a⁻¹ ∈ V := (mem_normalizer_iff.mp (hAV ha) v).mp hv
    have h2 : a * v * a⁻¹ * v⁻¹ ∈ V := V.mul_mem h1 (V.inv_mem hv)
    simpa [commutatorElement_def] using h2
  · rw [commutator_le]
    intro a ha v hv
    have h1 : v * a⁻¹ * v⁻¹ ∈ A := (mem_normalizer_iff.mp (hVA hv) a⁻¹).mp (A.inv_mem ha)
    have h2 : a * (v * a⁻¹ * v⁻¹) ∈ A := A.mul_mem ha h1
    simpa [commutatorElement_def, mul_assoc] using h2

theorem unitary_caseI {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop} {g : G} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : U4LocalFacts p n M L V sing)
    (hSg : LocalSetting p (cj g M) (cj g V))
    (hFg : U4LocalFacts p n (cj g M) (cj g L) (cj g V) (fun x => sing (g⁻¹ * x * g)))
    (hg : g ∉ M) (hAM : cj g V ≤ M) (hAL : cj g V ≤ L ⊔ (M ⊓ centralizer (V : Set G)))
    (hnc : ¬ cj g V ≤ centralizer (V : Set G)) (hVM' : V ≤ cj g M) : False := by
  have hVab : IsElemAbelian 2 V := hS.elemAbelian
  have hAab : IsElemAbelian 2 (cj g V) := hSg.elemAbelian
  have hVnc : ¬ V ≤ centralizer ((cj g V : Subgroup G) : Set G) := fun h =>
    hnc (Subgroup.le_centralizer_iff.mp h)
  have hQ := qProp_base hp hn hS hF hSg hFg hg hAM
  have hQ' := qProp_mirror hp hn hS hF hSg hFg hg hVM'
  have hVL' : V ≤ cj g L ⊔ (cj g M ⊓ centralizer ((cj g V : Subgroup G) : Set G)) :=
    hFg.Q_le V hVM' hVab hVnc hQ'
  have hcomm : ⁅cj g V, V⁆ ≤ V ⊓ cj g V :=
    commutator_le_inf_of_normalizer (hAM.trans (le_of_eq hS.normalizer_eq.symm))
      (hVM'.trans (le_of_eq hSg.normalizer_eq.symm))
  have hTS : ∀ u ∈ ⁅cj g V, V⁆, u ≠ 1 → sing u := by
    intro u hu hu1
    by_contra hns
    have huVA := hcomm hu
    have hcu : centralizer ({u} : Set G) ≤ M :=
      hS.centralizer_le_of_good hp huVA.1 hu1 (hF.nonsing_good u huVA.1 hu1 hns)
    exact not_inf_centralizer_le_of_dvd' (hS.spe g hg) (hFg.p_dvd u huVA.2 hu1)
      (le_trans inf_le_right hcu)
  have hTS' : ∀ u ∈ ⁅V, cj g V⁆, u ≠ 1 → sing (g⁻¹ * u * g) := by
    intro u hu hu1
    by_contra hns
    have huVA := hcomm (by rwa [Subgroup.commutator_comm] at hu)
    have hcu : centralizer ({u} : Set G) ≤ cj g M :=
      hSg.centralizer_le_of_good hp huVA.2 hu1 (hFg.nonsing_good u huVA.2 hu1 hns)
    exact not_inf_centralizer_le_of_dvd (hS.spe g hg) (hF.p_dvd u huVA.1 hu1)
      (le_trans inf_le_right hcu)
  have hVB0 : V ≤ centralizer ((cj g V ⊓ (M ⊓ centralizer (V : Set G)) : Subgroup G) : Set G) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro b hb
    exact (mem_centralizer_iff.mp hb.2.2 v hv).symm
  have hAB0 : cj g V ≤
      centralizer ((V ⊓ (cj g M ⊓ centralizer ((cj g V : Subgroup G) : Set G)) : Subgroup G) : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact (mem_centralizer_iff.mp hb.2.2 a ha).symm
  have h2n : 2 ^ (2 * n) ≤ (cj g V ⊓ (M ⊓ centralizer (V : Set G))).relIndex (cj g V) := by
    by_contra hlt
    exact hVnc fun v hv => hQ _ inf_le_left (not_le.mp hlt) ⟨hv, hVB0 hv⟩
  have h2n' : 2 ^ (2 * n) ≤
      (V ⊓ (cj g M ⊓ centralizer ((cj g V : Subgroup G) : Set G))).relIndex V := by
    by_contra hlt
    exact hnc fun a ha => hQ' _ inf_le_left (not_le.mp hlt) ⟨ha, hAB0 ha⟩
  obtain ⟨h5a, h5b⟩ := hF.ts_plane (cj g V) hAM hAab hAL h2n hTS
  obtain ⟨h6a, h6b⟩ := hFg.ts_plane V hVM' hVab hVL' h2n' hTS'
  have hAC : cj g V ⊓ (M ⊓ centralizer (V : Set G)) = cj g V ⊓ centralizer (V : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hAM h.1, h.2⟩⟩
  have hcardAC : Nat.card ↥(cj g V ⊓ (M ⊓ centralizer (V : Set G))) = 2 ^ (4 * n) := by
    rw [hAC, ← h6a]
    exact h6b
  have hrel : (cj g V ⊓ (M ⊓ centralizer (V : Set G))).relIndex (cj g V) = 2 ^ (4 * n) := by
    have h := Subgroup.relIndex_mul_card (H := cj g V ⊓ (M ⊓ centralizer (V : Set G)))
      (K := cj g V)
    rw [inf_of_le_left (inf_le_left : cj g V ⊓ (M ⊓ centralizer (V : Set G)) ≤ cj g V),
      hcardAC, hFg.card_V] at h
    have h8 : 2 ^ (8 * n) = 2 ^ (4 * n) * 2 ^ (4 * n) := by
      rw [← pow_add]; congr 1; omega
    rw [h8] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  obtain ⟨B, hBA, hB0B, hBcard, hBeq⟩ :=
    hF.transvection (cj g V) hAM hAab hAL hrel hTS
  have hYle : V ⊓ centralizer (B : Set G) ≤ cj g M := inf_le_left.trans hVM'
  have hYL : V ⊓ centralizer (B : Set G) ≤
      cj g L ⊔ (cj g M ⊓ centralizer ((cj g V : Subgroup G) : Set G)) := inf_le_left.trans hVL'
  obtain ⟨j, hj⟩ := hFg.dim_F _ hYle hYL
  rw [← hBeq, hBcard, hcardAC] at hj
  have hpow : 2 ^ n * 2 ^ (4 * n) = 2 ^ (2 * n * j) := hj
  rw [← pow_add] at hpow
  have hexp := Nat.pow_right_injective (le_refl 2) hpow
  have hn5 : n * 5 = n * (2 * j) := by nlinarith
  have := Nat.eq_of_mul_eq_mul_left (by omega) hn5
  omega

theorem unitary_commute {p n : ℕ} {M L V : Subgroup G} {sing : G → Prop} {g : G} (hp : p.Prime)
    (hn : 1 ≤ n) (hS : LocalSetting p M V) (hF : U4LocalFacts p n M L V sing)
    (hSg : LocalSetting p (cj g M) (cj g V))
    (hFg : U4LocalFacts p n (cj g M) (cj g L) (cj g V) (fun x => sing (g⁻¹ * x * g)))
    (hg : g ∉ M) (hAM : cj g V ≤ M) : cj g V ≤ centralizer (V : Set G) := by
  by_contra hnc
  have hQ := qProp_base hp hn hS hF hSg hFg hg hAM
  have hAL : cj g V ≤ L ⊔ (M ⊓ centralizer (V : Set G)) :=
    hF.Q_le (cj g V) hAM hSg.elemAbelian hnc hQ
  by_cases hVM' : V ≤ cj g M
  · exact unitary_caseI hp hn hS hF hSg hFg hg hAM hAL hnc hVM'
  · exact unitary_caseII hp hn hS hF hSg hFg hAM hAL hVM'

end CFSG.LocalAnalysis.RankThreeUC
