module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD14

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

structure ZJClass (T : H → Prop) (Q : Subgroup H) (t τ l : H) : Prop where
  conj : ∀ u g : H, T u → T (g * u * g⁻¹)
  invol : ∀ u : H, T u → u * u = 1 ∧ u ≠ 1
  not_Q : ∀ q ∈ Q, ¬ T q
  not_Qtau : ∀ q ∈ Q, ¬ T (q * τ)
  not_l : ¬ T l
  not_ltau : ¬ T (l * τ)
  not_lttau : ¬ T (l * t * τ)

private lemma z4j_prod_inv {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (ha : a * a = 1) (hb : b * b = 1) : (a * b) * (a * b) = 1 := by
  have h1 := hab.mul_pow 2
  simp only [pow_two] at h1
  rw [h1, ha, hb, mul_one]

private lemma z4j_conj_form {G : Type*} [Group G] {x m : G} (hx : x * x = 1) :
    x * (x * m * x⁻¹) = m * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  calc x * (x * m * x⁻¹) = (x * x) * m * x⁻¹ := by group
    _ = 1 * m * x⁻¹ := by rw [hx]
    _ = m * x⁻¹ := by rw [one_mul]
    _ = m * x := by rw [hxi]

private lemma z4j_E_le_centralizer_lt (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) :
    closure ({t, τ, l} : Set H) ≤ centralizer ({l * t} : Set H) := by
  refine (Subgroup.closure_le (centralizer ({l * t} : Set H))).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg | hg
  · rw [hg]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc (l * t) * t = l * (t * t) := by rw [mul_assoc]
      _ = l := by rw [h.t_sq, mul_one]
      _ = t * (l * t) := by rw [← mul_assoc, h.t_l, mul_assoc, h.t_sq, mul_one]
  · rw [hg]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc (l * t) * τ = l * (t * τ) := by rw [mul_assoc]
      _ = l * (τ * t) := by rw [h.t_tau]
      _ = (l * τ) * t := by rw [← mul_assoc]
      _ = (τ * l) * t := by rw [← h.tau_l]
      _ = τ * (l * t) := by rw [mul_assoc]
  · rw [hg]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc (l * t) * l = l * (t * l) := by rw [mul_assoc]
      _ = l * (l * t) := by rw [h.t_l]

private lemma z4j_conj_conj_self {G : Type*} [Group G] {g x : G} (hg : g * g = 1) :
    g * (g * x * g⁻¹) * g⁻¹ = x := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [hgi]
  calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
    _ = x := by rw [hg]; group

private lemma z4j_form_mem {Mc : Subgroup H} (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂)
    {g m e : H}
    (hm : m ∈ Mc) (heE : e ∈ closure ({t, τ, l} : Set H))
    (heC : e ∈ centralizer ({l * t} : Set H))
    (hgC : g ∈ centralizer ({l * t} : Set H)) (hge : g = m * e) :
    g ∈ (Mc ⊓ centralizer ({l * t} : Set H)) ⊔ closure ({t, τ, l} : Set H) := by
  have hmC : m ∈ centralizer ({l * t} : Set H) := by
    have hm_eq : m = g * e⁻¹ := by rw [hge]; group
    rw [hm_eq]
    exact (centralizer ({l * t} : Set H)).mul_mem hgC
      ((centralizer ({l * t} : Set H)).inv_mem heC)
  have hmK : m ∈ Mc ⊓ centralizer ({l * t} : Set H) := Subgroup.mem_inf.mpr ⟨hm, hmC⟩
  rw [hge]
  exact Subgroup.mul_mem_sup hmK heE

private lemma z4j_gen_normalizes_K {Mc : Subgroup H} {g : H} (hg2 : g * g = 1)
    (hgMc : ∀ y ∈ Mc, g * y * g⁻¹ ∈ Mc) (hgσ : g * (l * t) = (l * t) * g) :
    g ∈ Subgroup.normalizer (Mc ⊓ centralizer ({l * t} : Set H) : Set H) := by
  have hfwd : ∀ x, x ∈ (Mc ⊓ centralizer ({l * t} : Set H) : Subgroup H) →
      g * x * g⁻¹ ∈ (Mc ⊓ centralizer ({l * t} : Set H) : Subgroup H) := by
    intro x hx
    obtain ⟨hxMc, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hgMc x hxMc, ?_⟩
    have hgC : g ∈ centralizer ({l * t} : Set H) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgσ
    exact (centralizer ({l * t} : Set H)).mul_mem
      ((centralizer ({l * t} : Set H)).mul_mem hgC hxC)
      ((centralizer ({l * t} : Set H)).inv_mem hgC)
  rw [Subgroup.mem_set_normalizer_iff]
  intro x; constructor
  · exact hfwd x
  · intro hx
    have h2 := hfwd (g * x * g⁻¹) hx
    rwa [z4j_conj_conj_self hg2] at h2

private lemma z4j_E_le_normalizer_K (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂)
    {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) {Mc : Subgroup H}
    (hMc : IsZJMc ρ Q Mh Mc) :
    closure ({t, τ, l} : Set H) ≤
      Subgroup.normalizer (Mc ⊓ centralizer ({l * t} : Set H) : Set H) := by
  have hEσ := z4j_E_le_centralizer_lt h
  refine (Subgroup.closure_le
    (Subgroup.normalizer (Mc ⊓ centralizer ({l * t} : Set H) : Set H))).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg | hg
  · rw [hg]
    exact z4j_gen_normalizes_K h.t_sq (fun y hy => h.Mc_conj_t hMh hMc hy)
      (Subgroup.mem_centralizer_singleton_iff.mp (hEσ (Subgroup.subset_closure (by simp))))
  · rw [hg]
    exact z4j_gen_normalizes_K h.tau_sq (fun y hy => h.Mc_conj_tau hMh hMc hy)
      (Subgroup.mem_centralizer_singleton_iff.mp (hEσ (Subgroup.subset_closure (by simp))))
  · rw [hg]
    exact z4j_gen_normalizes_K h.l_sq (fun y hy => h.Mc_conj_l hMh hMc hy)
      (Subgroup.mem_centralizer_singleton_iff.mp (hEσ (Subgroup.subset_closure (by simp))))

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem card_cent_Vh_lt :
    Nat.card ↥(zjVh Mc t τ l ⊓ centralizer ({l * t} : Set H)) = 128 := by
  let E : Subgroup H := closure ({t, τ, l} : Set H)
  let K : Subgroup H := Mc ⊓ centralizer ({l * t} : Set H)
  let D : Subgroup H := zjVh Mc t τ l ⊓ centralizer ({l * t} : Set H)
  have hEσ : E ≤ centralizer ({l * t} : Set H) := z4j_E_le_centralizer_lt h
  have hEMc : E ≤ Subgroup.normalizer (Mc : Set H) := E_le_normalizer_Mc h hMh hMc
  have hEbot : Mc ⊓ E = ⊥ := Mc_inf_E h hMh hMc
  have hEnormK : E ≤ Subgroup.normalizer (K : Set H) := z4j_E_le_normalizer_K h hMh hMc
  have hKbot : K ⊓ E = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨hxK, hxE⟩ := Subgroup.mem_inf.mp hx
    have hxMc : x ∈ Mc := (Subgroup.mem_inf.mp hxK).1
    have hxME : x ∈ Mc ⊓ E := Subgroup.mem_inf.mpr ⟨hxMc, hxE⟩
    rwa [hEbot] at hxME
  have hEVh : E ≤ zjVh Mc t τ l := by rw [zjVh]; exact le_sup_right
  have hD : D = K ⊔ E := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgV, hgC⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨m, hm, hdisj⟩ := (h.mem_Vh_iff hMh hMc).mp hgV
      have htE : t ∈ E := Subgroup.subset_closure (by simp)
      have hτE : τ ∈ E := Subgroup.subset_closure (by simp)
      have hlE : l ∈ E := Subgroup.subset_closure (by simp)
      have hmem := fun (e : H) (heE : e ∈ E)
          (heC : e ∈ centralizer ({l * t} : Set H)) (hge : g = m * e) =>
        z4j_form_mem h hm heE heC hgC hge
      rcases hdisj with hg1 | hg1 | hg1 | hg1 | hg1 | hg1 | hg1 | hg1
      · exact hmem 1 (Subgroup.one_mem E) (Subgroup.one_mem _) (by rw [hg1]; group)
      · exact hmem t htE (hEσ htE) hg1
      · exact hmem τ hτE (hEσ hτE) hg1
      · exact hmem (t * τ) (E.mul_mem htE hτE) (hEσ (E.mul_mem htE hτE)) hg1
      · exact hmem l hlE (hEσ hlE) hg1
      · exact hmem (t * l) (E.mul_mem htE hlE) (hEσ (E.mul_mem htE hlE)) hg1
      · exact hmem (τ * l) (E.mul_mem hτE hlE) (hEσ (E.mul_mem hτE hlE)) hg1
      · exact hmem (t * τ * l) (E.mul_mem (E.mul_mem htE hτE) hlE)
          (hEσ (E.mul_mem (E.mul_mem htE hτE) hlE)) hg1
    · apply sup_le
      · intro k hk
        obtain ⟨hkMc, hkC⟩ := Subgroup.mem_inf.mp hk
        exact Subgroup.mem_inf.mpr ⟨Mc_le_zjVh Mc t τ l hkMc, hkC⟩
      · intro e he
        exact Subgroup.mem_inf.mpr ⟨hEVh he, hEσ he⟩
  have hcardD : Nat.card D = Nat.card K * Nat.card E := by
    rw [hD]
    exact card_sup_of_le_normalizer hEnormK hKbot
  have hcardE : Nat.card E = 8 := by
    have hs : Mc ⊔ E = zjVh Mc t τ l := by rw [zjVh]
    have h1 : Nat.card Mc * Nat.card E = 2048 := by
      rw [← card_sup_of_le_normalizer hEMc hEbot, hs, h.card_Vh hMh hMc]
    have hcardMc : Nat.card Mc = 256 := h.card_Mc hMh hMc
    have h2 : 256 * Nat.card E = 256 * 8 := by
      rw [← hcardMc, h1, hcardMc]
    exact Nat.mul_left_cancel (by norm_num) h2
  have hcardK : Nat.card K = 16 := (h.Mc_fusion_lt hMh hMc).2
  show Nat.card D = 128
  rw [hcardD, hcardK, hcardE]

theorem T_invol_coset {T : H → Prop} (hT : ZJClass T Q t τ l) {s : H}
    (hs : s ∈ zjVh Mc t τ l) (hs2 : s * s = 1) (hTs : T s)
    (hsK : s ∉ Mc ⊔ closure ({t, τ} : Set H)) : ∃ w ∈ Mc, s = w * (l * t) * w⁻¹ := by
  obtain ⟨m, hm, hdisj⟩ := (h.mem_Vh_iff hMh hMc).mp hs
  have ht_in : t ∈ Mc ⊔ closure ({t, τ} : Set H) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hτ_in : τ ∈ Mc ⊔ closure ({t, τ} : Set H) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hm_in : m ∈ Mc ⊔ closure ({t, τ} : Set H) := Subgroup.mem_sup_left hm
  have hlt_sq : (l * t) * (l * t) = 1 := z4j_prod_inv h.t_l.symm h.l_sq h.t_sq
  have hlτ_sq : (l * τ) * (l * τ) = 1 := z4j_prod_inv h.tau_l.symm h.l_sq h.tau_sq
  have htt_sq : (t * τ) * (t * τ) = 1 := z4j_prod_inv h.t_tau h.t_sq h.tau_sq
  have hcomm_l_tt : l * (t * τ) = (t * τ) * l := by
    calc l * (t * τ) = (l * t) * τ := by rw [← mul_assoc]
      _ = (t * l) * τ := by rw [h.t_l]
      _ = t * (l * τ) := by rw [mul_assoc]
      _ = t * (τ * l) := by rw [h.tau_l]
      _ = (t * τ) * l := by rw [← mul_assoc]
  have hltt_sq : (l * t * τ) * (l * t * τ) = 1 := by
    have hcomm_lt_τ : (l * t) * τ = τ * (l * t) := by
      calc (l * t) * τ = l * (t * τ) := by rw [mul_assoc]
        _ = l * (τ * t) := by rw [h.t_tau]
        _ = (l * τ) * t := by rw [← mul_assoc]
        _ = (τ * l) * t := by rw [← h.tau_l]
        _ = τ * (l * t) := by rw [mul_assoc]
    exact z4j_prod_inv hcomm_lt_τ hlt_sq h.tau_sq
  rcases hdisj with hg | hg | hg | hg | hg | hg | hg | hg
  · exact absurd (hg ▸ hm_in) hsK
  · exact absurd (hg ▸ (Mc ⊔ closure ({t, τ} : Set H)).mul_mem hm_in ht_in) hsK
  · exact absurd (hg ▸ (Mc ⊔ closure ({t, τ} : Set H)).mul_mem hm_in hτ_in) hsK
  · exact absurd (hg ▸ (Mc ⊔ closure ({t, τ} : Set H)).mul_mem hm_in
      ((Mc ⊔ closure ({t, τ} : Set H)).mul_mem ht_in hτ_in)) hsK
  · set m' : H := l * m * l⁻¹ with hm'def
    have hm' : m' ∈ Mc := by rw [hm'def]; exact h.Mc_conj_l hMh hMc hm
    have hs_eq : s = l * m' := by
      rw [hm'def, z4j_conj_form h.l_sq]
      exact hg
    have hs2' : l * m' * (l * m') = 1 := by rw [← hs_eq]; exact hs2
    obtain ⟨w, hw, hweq⟩ := (h.Mc_fusion_l hMh hMc).1 m' hm' hs2'
    exact (hT.not_l (by
      have h1 := hT.conj s w⁻¹ hTs
      rwa [show w⁻¹ * s * w⁻¹⁻¹ = l by rw [hs_eq, hweq]; group] at h1)).elim
  · set m' : H := (l * t) * m * (l * t)⁻¹ with hm'def
    have hm' : m' ∈ Mc := by
      rw [hm'def, show (l * t) * m * (l * t)⁻¹ = l * (t * m * t⁻¹) * l⁻¹ by group]
      exact h.Mc_conj_l hMh hMc (h.Mc_conj_t hMh hMc hm)
    have hs_eq : s = (l * t) * m' := by
      rw [hm'def, z4j_conj_form hlt_sq, h.t_l.symm]
      exact hg
    have hs2' : l * t * m' * (l * t * m') = 1 := by rw [← hs_eq]; exact hs2
    obtain ⟨w, hw, hweq⟩ := (h.Mc_fusion_lt hMh hMc).1 m' hm' hs2'
    exact ⟨w, hw, by rw [hs_eq, hweq]⟩
  · set m' : H := (l * τ) * m * (l * τ)⁻¹ with hm'def
    have hm' : m' ∈ Mc := by
      rw [hm'def, show (l * τ) * m * (l * τ)⁻¹ = l * (τ * m * τ⁻¹) * l⁻¹ by group]
      exact h.Mc_conj_l hMh hMc (h.Mc_conj_tau hMh hMc hm)
    have hs_eq : s = (l * τ) * m' := by
      rw [hm'def, z4j_conj_form hlτ_sq, h.tau_l.symm]
      exact hg
    have hs2' : l * τ * m' * (l * τ * m') = 1 := by rw [← hs_eq]; exact hs2
    obtain ⟨w, hw, hweq⟩ := (h.Mc_fusion_ltau hMh hMc).1 m' hm' hs2'
    exact (hT.not_ltau (by
      have h1 := hT.conj s w⁻¹ hTs
      rwa [show w⁻¹ * s * w⁻¹⁻¹ = l * τ by rw [hs_eq, hweq]; group] at h1)).elim
  · set m' : H := (l * t * τ) * m * (l * t * τ)⁻¹ with hm'def
    have hm' : m' ∈ Mc := by
      rw [hm'def, show (l * t * τ) * m * (l * t * τ)⁻¹ =
        l * (t * (τ * m * τ⁻¹) * t⁻¹) * l⁻¹ by group]
      exact h.Mc_conj_l hMh hMc (h.Mc_conj_t hMh hMc (h.Mc_conj_tau hMh hMc hm))
    have hperm : l * t * τ = t * τ * l := by
      calc l * t * τ = l * (t * τ) := by rw [mul_assoc]
        _ = (t * τ) * l := hcomm_l_tt
    have hs_eq : s = (l * t * τ) * m' := by
      rw [hm'def, z4j_conj_form hltt_sq, hperm]
      exact hg
    have hs2' : l * t * τ * m' * (l * t * τ * m') = 1 := by rw [← hs_eq]; exact hs2
    obtain ⟨w, hw, hweq⟩ := (h.Mc_fusion_lttau hMh hMc).1 m' hm' hs2'
    exact (hT.not_lttau (by
      have h1 := hT.conj s w⁻¹ hTs
      rwa [show w⁻¹ * s * w⁻¹⁻¹ = l * t * τ by rw [hs_eq, hweq]; group] at h1)).elim

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
