module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParF5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParO
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma s888parm_zpow_eq_one_or_self {G : Type} [Group G] {a : G} (ha : a * a = 1)
    {x : G} (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : a ^ (2 : ℕ) = 1 := by rwa [pow_two]
  rw [zpow_eq_zpow_emod' k h2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; show a ^ (k % 2) = 1; rw [hk]; simp
  · right; show a ^ (k % 2) = a; rw [hk]; simp

private lemma s888parm_w2_apply {G : Type} [Group G] {z n q : G} (hz2 : z * z = 1)
    (hqz : q * z = z * q) (hnz : n * z = z * n)
    (hcomm : n * q * n⁻¹ * q⁻¹ ∈ Subgroup.zpowers z) :
    n⁻¹ * q * n = q ∨ n⁻¹ * q * n = q * z := by
  rcases s888parm_zpow_eq_one_or_self hz2 hcomm with h1 | hz
  · left
    have h2 : n * q * n⁻¹ = q := by
      have h := congrArg (fun y => y * q) h1
      simpa [mul_assoc] using h
    have h3 : q * n = n * q := by
      have h := congrArg (fun y => y * n) h2
      exact (by simpa [mul_assoc] using h : n * q = q * n).symm
    calc n⁻¹ * q * n = n⁻¹ * (q * n) := by group
      _ = n⁻¹ * (n * q) := by rw [h3]
      _ = q := by group
  · right
    have h2 : n * q * n⁻¹ = z * q := by
      have h := congrArg (fun y => y * q) hz
      simpa [mul_assoc] using h
    have h3 : n * q * n⁻¹ = q * z := by rw [h2, hqz]
    have hq' : q = (n⁻¹ * q * n) * z := by
      calc q = n⁻¹ * (n * q * n⁻¹) * n := by group
        _ = n⁻¹ * (q * z) * n := by rw [h3]
        _ = n⁻¹ * q * (z * n) := by group
        _ = n⁻¹ * q * (n * z) := by rw [← hnz]
        _ = (n⁻¹ * q * n) * z := by group
    have hfin : q * z = n⁻¹ * q * n := by
      have h := congrArg (fun y => y * z) hq'
      rw [mul_assoc, hz2, mul_one] at h
      exact h
    exact hfin.symm

private lemma s888parm_xor_congr {a b c d : Prop} (h1 : a ↔ c) (h2 : b ↔ d) :
    (Xor' a b ↔ Xor' c d) := by
  change Xor a b ↔ Xor c d
  rw [xor_iff_not_iff, xor_iff_not_iff]
  exact not_congr (iff_congr h1 h2)

private lemma s888parm_xor_comm {a b : Prop} : (Xor' a b ↔ Xor' b a) := by
  change Xor a b ↔ Xor b a
  rw [_root_.xor_comm]

private lemma s888parm_out_corr {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}
    (hq : Sec5B517Quad K z) {l : Fin 4} {r w : G} (hr : r ∈ K 2) (hl : l ≠ 2)
    (hwK : CFSG.conjugate (K l) w = K l) :
    (∃ k ∈ K l, (w * r)⁻¹ * k * (w * r) * k⁻¹ ∉ twoCoreIn (K l)) ↔
      (∃ k ∈ K l, w⁻¹ * k * w * k⁻¹ ∉ twoCoreIn (K l)) := by
  have hbody : ∀ k ∈ K l, ((w * r)⁻¹ * k * (w * r) * k⁻¹ ∉ twoCoreIn (K l)) ↔
      (w⁻¹ * k * w * k⁻¹ ∉ twoCoreIn (K l)) := by
    intro k hk
    have hconj : (w * r)⁻¹ * k * (w * r) = w⁻¹ * k * w := by
      have hkw : w⁻¹ * k * w ∈ K l := sec5b_mem_of_conjugate_eq' hwK hk
      have hrkw : r * (w⁻¹ * k * w) = (w⁻¹ * k * w) * r :=
        hq.comm 2 l hl.symm r hr (w⁻¹ * k * w) hkw
      calc (w * r)⁻¹ * k * (w * r) = r⁻¹ * (w⁻¹ * k * w) * r := by group
        _ = r⁻¹ * ((w⁻¹ * k * w) * r) := by group
        _ = r⁻¹ * (r * (w⁻¹ * k * w)) := by rw [← hrkw]
        _ = w⁻¹ * k * w := by group
    rw [hconj]
  constructor
  · rintro ⟨k, hk, hk'⟩
    exact ⟨k, hk, (hbody k hk).mp hk'⟩
  · rintro ⟨k, hk, hk'⟩
    exact ⟨k, hk, (hbody k hk).mpr hk'⟩

private lemma s888parm_sup01_le_centralizer_y {G : Type} [Group G] {K : Fin 4 → Subgroup G}
    {z : G} (hq : Sec5B517Quad K z) {a₁ b₁ : G} (ha₁ : a₁ ∈ K 2) (hb₁ : b₁ ∈ K 3) :
    K 0 ⊔ K 1 ≤ centralizer ({a₁ * b₁} : Set G) := by
  apply sup_le
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * (a₁ * b₁) = (k * a₁) * b₁ := by group
      _ = (a₁ * k) * b₁ := by rw [hq.comm 0 2 (by decide) k hk a₁ ha₁]
      _ = a₁ * (k * b₁) := by group
      _ = a₁ * (b₁ * k) := by rw [hq.comm 0 3 (by decide) k hk b₁ hb₁]
      _ = (a₁ * b₁) * k := by group
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * (a₁ * b₁) = (k * a₁) * b₁ := by group
      _ = (a₁ * k) * b₁ := by rw [hq.comm 1 2 (by decide) k hk a₁ ha₁]
      _ = a₁ * (k * b₁) := by group
      _ = a₁ * (b₁ * k) := by rw [hq.comm 1 3 (by decide) k hk b₁ hb₁]
      _ = (a₁ * b₁) * k := by group

theorem par_even_of_xor_iff (P : Fin 4 → Prop) (hP : Xor' (P 0) (P 1) ↔ Xor' (P 2) (P 3)) :
    Even (Nat.card {i : Fin 4 // P i}) := by
  classical
  have hcard : Nat.card {i : Fin 4 // P i} =
      (if P 0 then 1 else 0) + (if P 1 then 1 else 0) +
        (if P 2 then 1 else 0) + (if P 3 then 1 else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp; omega
  rw [hcard]
  by_cases h0 : P 0 <;> by_cases h1 : P 1 <;> by_cases h2 : P 2 <;> by_cases h3 : P 3 <;>
    simp_all [Xor'] <;> norm_num

theorem asc82Lemma518Parity_of (h514 : Asc82Lemma514) (h515b : Asc82Lemma515b)
    (h515c : Asc82Lemma515c) (hF2 : Asc82FactPocketsTwo) (h52a : Asc82Lemma52a)
    (h37 : Asc82Lemma37) (hF5 : Asc82FactOm6Par) : Asc82Lemma518Parity := by
  classical
  intro G _ _ t L S z r B A K₁ K₂ h c w hwN hwK hw2
  let K : Fin 4 → Subgroup G := Kfam5 K₁ K₂ h
  have hq : Sec5B517Quad K z := sec5b517_quad h514 c
  show Even (Nat.card {i : Fin 4 // ParNt K z w i})
  apply par_even_of_xor_iff (fun i => ParNt K z w i)
  have hwz : w * z = z * w := by
    have hmem : w * z * w⁻¹ ∈ K 0 :=
      (sec5b_mem_conjugate_iff (H := K 0) (g := w) (x := z)).mp
        (by rw [hwK 0]; exact hq.z_mem 0)
    have hsq : (w * z * w⁻¹) * (w * z * w⁻¹) = 1 := by
      rw [show (w * z * w⁻¹) * (w * z * w⁻¹) = w * (z * z) * w⁻¹ by group, hq.z_sq]
      group
    rcases hq.eq_of_sq hmem hsq with h1 | hz
    · exfalso
      have hz1 : z = 1 := by
        have h := congrArg (fun y => w⁻¹ * y * w) h1
        simpa [mul_assoc] using h
      exact hq.z_ne hz1
    · have h := congrArg (fun y => y * w) hz
      simpa [mul_assoc] using h
  have hw2' : ∀ i, ∀ q ∈ K i, q ^ 4 = 1 →
      (w * w)⁻¹ * q * (w * w) = q ∨ (w * w)⁻¹ * q * (w * w) = q * z := by
    intro i q hqK hq4
    obtain ⟨_, hw2z, _, hw2comm⟩ := hw2
    have hqQ : q ∈ Qsub K₁ K₂ h := by
      rw [sec5b517_Qsub_eq, hq.core_eq]
      exact Sec5B517Q8.mem_of_mem hq hqK hq4
    exact s888parm_w2_apply hq.z_sq (hq.z_comm hqK).symm
      (Subgroup.mem_centralizer_singleton_iff.mp hw2z) (hw2comm q hqQ)
  obtain ⟨a₀, ha₀K, ha₀2, hwa⟩ := par_exists_fixed_class hq 2 hwz (hwK 2) (hw2' 2)
  obtain ⟨b₀, hb₀K, hb₀2, hwb⟩ := par_exists_fixed_class hq 3 hwz (hwK 3) (hw2' 3)
  obtain ⟨a₁, ha₁K, ha₁2, ha₁ne, ha₁ne'⟩ := par_exists_other_sq hq 2 ha₀K ha₀2
  obtain ⟨b₁, hb₁K, hb₁2, hb₁ne, hb₁ne'⟩ := par_exists_other_sq hq 3 hb₀K hb₀2
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  obtain ⟨r, hrK, hr4, hcorr⟩ :=
    par_exists_corr hq (i := 2) (j := 3) h23 ha₀K hb₀K ha₀2 hb₀2 hwa hwb
  let g : G := w * r
  let t' : G := a₀ * b₀
  have hcorr' : g⁻¹ * t' * g = t' := hcorr
  have hgt' : g * t' = t' * g := by
    have h1 : t' * g = g * t' := by
      calc t' * g = g * (g⁻¹ * t' * g) := by group
        _ = g * t' := by rw [hcorr']
    exact h1.symm
  obtain ⟨S'', r'', B'', A'', P₁, P₂, h'', c'', hpockets⟩ :=
    par_exists_ctx h514 h515b h515c hF2 c ha₀K hb₀K ha₀2 hb₀2
  let L' : Subgroup G := layerC5 t'
  let D : Subgroup G := centralizer (L' : Set G)
  have ht'props := par_t_props hq h23 ha₀K hb₀K ha₀2 hb₀2
  have ht'pair : t' ∈ Sec5B517Q8.pair hq 2 3 := ht'props.1
  have ht'D : t' ∈ D := par_t_mem_centralizer c''
  have hD : ∀ x ∈ Sec5B517Q8.pair hq 2 3, x * t' = t' * x → x ∈ D → x = 1 ∨ x = t' :=
    par_inf_cent_le h52a h37 c'' hq h23 ht'pair
  have hg_norm : g ∈ normalizer (L' : Set G) := by
    rw [← sec5b513_conjugate_eq_iff]
    exact sec5_conj_L h52a c'' (Subgroup.mem_centralizer_singleton_iff.mpr hgt')
  have hgK : ∀ l, CFSG.conjugate (K l) g = K l := by
    intro l
    exact par_conj_mul hq (j := 2) hrK hwK l
  let y : G := a₁ * b₁
  have hyprops := par_y_props hq h23 ha₀K hb₀K ha₁K hb₁K ha₀2 hb₀2 ha₁2 hb₁2
    ha₁ne ha₁ne' hb₁ne hb₁ne'
  have hyt' : y * t' = t' * y := hyprops.2.2.2.1
  have hy_sq : y * y = 1 := hyprops.2.2.1
  have hy_norm : y ∈ normalizer (L' : Set G) := by
    rw [← sec5b513_conjugate_eq_iff]
    exact sec5_conj_L h52a c'' (Subgroup.mem_centralizer_singleton_iff.mpr hyt')
  have hy2 : y * y ∈ D := by rw [hy_sq]; exact D.one_mem
  have hyne : y ∉ D := by
    intro hyD
    rcases hD y hyprops.1 hyt' hyD with h1 | ht
    · exact hyprops.2.2.2.2.1 h1
    · exact hyprops.2.2.2.2.2.1 ht
  have hzt' : z * t' = t' * z := by
    dsimp only [t']
    calc z * (a₀ * b₀) = (z * a₀) * b₀ := by group
      _ = (a₀ * z) * b₀ := by rw [hq.z_comm ha₀K]
      _ = a₀ * (z * b₀) := by group
      _ = a₀ * (b₀ * z) := by rw [hq.z_comm hb₀K]
      _ = (a₀ * b₀) * z := by group
  have hyz_comm : (y * z) * t' = t' * (y * z) := by
    calc (y * z) * t' = y * (z * t') := by group
      _ = y * (t' * z) := by rw [hzt']
      _ = (y * t') * z := by group
      _ = (t' * y) * z := by rw [hyt']
      _ = t' * (y * z) := by group
  have hyzne : y * z ∉ D := by
    intro hyzD
    rcases hD (y * z) hyprops.2.1 hyz_comm hyzD with h1 | ht
    · exact hyprops.2.2.2.2.2.2.1 h1
    · exact hyprops.2.2.2.2.2.2.2 ht
  have hgz : g * z = z * g := by
    have hrz : r * z = z * r := (hq.z_comm hrK).symm
    dsimp only [g]
    rw [mul_assoc, hrz, ← mul_assoc, hwz]
    group
  have ha₀' : g⁻¹ * a₀ * g ∈ K 2 := sec5b_mem_of_conjugate_eq' (hgK 2) ha₀K
  have hb₀' : g⁻¹ * b₀ * g ∈ K 3 := sec5b_mem_of_conjugate_eq' (hgK 3) hb₀K
  have hg₀ : g⁻¹ * a₀ * g = a₀ ∨ g⁻¹ * a₀ * g = a₀ * z := by
    have h : a₀ * b₀ = (g⁻¹ * a₀ * g) * (g⁻¹ * b₀ * g) := by
      calc a₀ * b₀ = g⁻¹ * (a₀ * b₀) * g := hcorr.symm
        _ = (g⁻¹ * a₀ * g) * (g⁻¹ * b₀ * g) := by dsimp only [g]; group
    exact par_mul_cancel hq (i := 2) (j := 3) h23 ha₀K ha₀' hb₀K hb₀' h
  have hg₀' : g⁻¹ * b₀ * g = b₀ ∨ g⁻¹ * b₀ * g = b₀ * z := by
    have h : b₀ * a₀ = (g⁻¹ * b₀ * g) * (g⁻¹ * a₀ * g) := by
      calc b₀ * a₀ = a₀ * b₀ := (hq.comm 2 3 h23 a₀ ha₀K b₀ hb₀K).symm
        _ = g⁻¹ * (a₀ * b₀) * g := hcorr.symm
        _ = (g⁻¹ * b₀ * g) * (g⁻¹ * a₀ * g) := by
              rw [hq.comm 2 3 h23 a₀ ha₀K b₀ hb₀K]
              dsimp only [g]; group
    exact par_mul_cancel hq (i := 3) (j := 2) h23.symm hb₀K hb₀' ha₀K ha₀' h
  have hsup01 : K 0 ⊔ K 1 ≤ centralizer ({y} : Set G) :=
    s888parm_sup01_le_centralizer_y hq ha₁K hb₁K
  have hF5_result :
      (Xor' (∃ k ∈ K 0, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn (K 0))
        (∃ k ∈ K 1, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn (K 1))) ↔
      (y⁻¹ * (g⁻¹ * y * g) ∉ D ∧ (y * z)⁻¹ * (g⁻¹ * y * g) ∉ D) := by
    rcases hpockets with ⟨hP1, hP2⟩ | ⟨hP1, hP2⟩
    · subst P₁; subst P₂
      exact hF5 G L' z K₁ K₂ c''.toSec5Setting.isOm6Z2 (sec5b517_oddCore_bot c'')
        c''.pocket.1 c''.pocket₁ c''.pocket₂ c''.ne c''.comm c''.prod
        g y hg_norm (hgK 0) (hgK 1) hy_norm hsup01 hy2 hyne hyzne
    · subst P₁; subst P₂
      have hycent : K₂ ⊔ K₁ ≤ centralizer ({y} : Set G) := by
        rw [sup_comm]; exact hsup01
      have hres := hF5 G L' z K₂ K₁ c''.toSec5Setting.isOm6Z2 (sec5b517_oddCore_bot c'')
        c''.pocket.1 c''.pocket₁ c''.pocket₂ c''.ne c''.comm c''.prod
        g y hg_norm (hgK 1) (hgK 0) hy_norm hycent hy2 hyne hyzne
      exact s888parm_xor_comm.trans hres
  have step1 : (Xor' (ParNt K z w 0) (ParNt K z w 1)) ↔
      (Xor' (∃ k ∈ K 0, w⁻¹ * k * w * k⁻¹ ∉ twoCoreIn (K 0))
        (∃ k ∈ K 1, w⁻¹ * k * w * k⁻¹ ∉ twoCoreIn (K 1))) :=
    s888parm_xor_congr (par_outer_iff hq 0 hwz (hwK 0) (hw2' 0)).symm
      (par_outer_iff hq 1 hwz (hwK 1) (hw2' 1)).symm
  have step2 : (Xor' (∃ k ∈ K 0, w⁻¹ * k * w * k⁻¹ ∉ twoCoreIn (K 0))
        (∃ k ∈ K 1, w⁻¹ * k * w * k⁻¹ ∉ twoCoreIn (K 1))) ↔
      (Xor' (∃ k ∈ K 0, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn (K 0))
        (∃ k ∈ K 1, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn (K 1))) :=
    s888parm_xor_congr
      (s888parm_out_corr hq hrK (by decide : (0 : Fin 4) ≠ 2) (hwK 0)).symm
      (s888parm_out_corr hq hrK (by decide : (1 : Fin 4) ≠ 2) (hwK 1)).symm
  have step4 : (y⁻¹ * (g⁻¹ * y * g) ∉ D ∧ (y * z)⁻¹ * (g⁻¹ * y * g) ∉ D) ↔
      (Xor' (ParNt K z g 2) (ParNt K z g 3)) :=
    par_xor_iff hq h23 D ha₀K hb₀K ha₁K hb₁K ha₀2 hb₀2 ha₁2 hb₁2 ha₁ne ha₁ne'
      hb₁ne hb₁ne' hgz (hgK 2) (hgK 3) hg₀ hg₀' ht'D hD
  have step5 : (Xor' (ParNt K z g 2) (ParNt K z g 3)) ↔
      (Xor' (ParNt K z w 2) (ParNt K z w 3)) :=
    s888parm_xor_congr (par_nt_corr_iff hq hrK hr4 hwK 2)
      (par_nt_corr_iff hq hrK hr4 hwK 3)
  exact step1.trans (step2.trans (hF5_result.trans (step4.trans step5)))

end CFSG.OddStandard.SmallF3.Omega
