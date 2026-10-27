module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611C

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem Zg_decomp {α : G} (hα : AlphaSpec S z t α) {c : G}
    (hc : c ∈ (zpowers α ⊔ zpowers t : Subgroup G)) :
    ∃ c' ∈ zpowers α, ∃ c'' ∈ zpowers (α * t), c = c' * c'' := by
  rcases (h.mem_Zg hα).1 hc with h1 | h1 | h1 | h1
  · exact ⟨1, one_mem _, 1, one_mem _, by rw [h1, mul_one]⟩
  · exact ⟨α, mem_zpowers α, α * t, mem_zpowers _, by rw [h1, ← mul_assoc, hα.sq, one_mul]⟩
  · exact ⟨α, mem_zpowers α, 1, one_mem _, by rw [h1, mul_one]⟩
  · exact ⟨1, one_mem _, α * t, mem_zpowers _, by rw [h1, one_mul]⟩

theorem W1_inf_W2 {α : G} (hα : AlphaSpec S z t α) {q : G}
    (h1 : q ∈ Wsub h hα (zpowers α)) (h2 : q ∈ Wsub h hα (zpowers (α * t))) :
    q ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  have hcomm : ∀ e ∈ E, q * e = e * q := by
    intro e he
    apply cmt_eq_one_iff.1
    rcases mem_zpowers_sq_eq_one hα.sq (h1.2 e he) with h3 | h3
    · exact h3
    · exfalso
      rcases mem_zpowers_sq_eq_one (h.zinv_alpha_t hα).sq (h2.2 e he) with h4 | h4
      · rw [h3] at h4
        exact hα.ne_one h4
      · rw [h3] at h4
        exact h.t_ne (mul_eq_left.1 h4.symm)
  exact (h.mem_Zg hα).2 (h.QF_cent_E hα h1.1 hcomm)

theorem Zg_mem_Wsub {α : G} (hα : AlphaSpec S z t α) (A : Subgroup G) {a : G}
    (ha : a ∈ (zpowers α ⊔ zpowers t : Subgroup G)) : a ∈ Wsub h hα A :=
  ⟨(h.Zg_cent_Q hα ha).1, fun e he => by
    rw [cmt_eq_one_iff.2 (h.Zg_comm_E hα ha he)]
    exact A.one_mem⟩

theorem eq_mod_Zg_of_gen {α : G} (hα : AlphaSpec S z t α) {s : Set G}
    (hE : Subgroup.closure s = E) {q q' : G} (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hq' : q' ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hgen : ∀ g ∈ s, q * g * q⁻¹ * g⁻¹ = q' * g * q'⁻¹ * g⁻¹) :
    q⁻¹ * q' ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
  have hall : ∀ e ∈ E, q * e * q⁻¹ * e⁻¹ = q' * e * q'⁻¹ * e⁻¹ := by
    refine eq_on_closure hE (f := fun e => q * e * q⁻¹ * e⁻¹) (f' := fun e => q' * e * q'⁻¹ * e⁻¹)
      ?_ ?_ hgen
    · intro e he e' he'
      exact h.cmt_mul_right hα hq (h.E_le_Qs hα he) (h.E_le_Qs hα he')
    · intro e he e' he'
      exact h.cmt_mul_right hα hq' (h.E_le_Qs hα he) (h.E_le_Qs hα he')
  have hcomm : ∀ e ∈ E, (q⁻¹ * q') * e = e * (q⁻¹ * q') := by
    intro e he
    apply cmt_eq_one_iff.1
    rw [h.cmt_mul_left hα (inv_mem hq) hq' (h.E_le_Qs hα he),
      h.cmt_inv_left hα hq (h.E_le_Qs hα he), hall e he, inv_mul_cancel]
  exact (h.mem_Zg hα).2 (h.QF_cent_E hα (mul_mem (inv_mem hq) hq') hcomm)

theorem Qs_eq_W1_W2 {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t) {q : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    ∃ w₁ ∈ Wsub h hα (zpowers α), ∃ w₂ ∈ Wsub h hα (zpowers (α * t)), q = w₁ * w₂ := by
  obtain ⟨a, b, c, d, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  have ha : a ∈ E := hgen a (by simp)
  have hb : b ∈ E := hgen b (by simp)
  have hc : c ∈ E := hgen c (by simp)
  have hd : d ∈ E := hgen d (by simp)
  obtain ⟨a₁, ha₁, a₂, ha₂, hca⟩ := h.Zg_decomp hα (h.cmt_mem hα hq (h.E_le_Qs hα ha))
  obtain ⟨b₁, hb₁, b₂, hb₂, hcb⟩ := h.Zg_decomp hα (h.cmt_mem hα hq (h.E_le_Qs hα hb))
  obtain ⟨c₁, hc₁, c₂, hc₂, hcc⟩ := h.Zg_decomp hα (h.cmt_mem hα hq (h.E_le_Qs hα hc))
  obtain ⟨d₁, hd₁, d₂, hd₂, hcd⟩ := h.Zg_decomp hα (h.cmt_mem hα hq (h.E_le_Qs hα hd))
  have hzp1 : zpowers α ≤ (zpowers α ⊔ zpowers t : Subgroup G) := le_sup_left
  have hzp2 : zpowers (α * t) ≤ (zpowers α ⊔ zpowers t : Subgroup G) :=
    zpowers_le.2 (mul_mem (h.alpha_mem_Zg hα) (h.t_mem_Zg hα))
  obtain ⟨w₁, hw₁Q, e1, e2, e3, e4⟩ := h.Phi4_surj hα hE ha hb hc hd a₁ b₁ c₁ d₁ (hzp1 ha₁)
    (hzp1 hb₁) (hzp1 hc₁) (hzp1 hd₁)
  obtain ⟨w₂, hw₂Q, f1, f2, f3, f4⟩ := h.Phi4_surj hα hE ha hb hc hd a₂ b₂ c₂ d₂ (hzp2 ha₂)
    (hzp2 hb₂) (hzp2 hc₂) (hzp2 hd₂)
  have hmul : ∀ (A : Subgroup G) (w : G) (hw : w ∈ Fsub h hα ⊓ centralizer ({α} : Set G)),
      (w * a * w⁻¹ * a⁻¹ ∈ A) → (w * b * w⁻¹ * b⁻¹ ∈ A) → (w * c * w⁻¹ * c⁻¹ ∈ A) →
      (w * d * w⁻¹ * d⁻¹ ∈ A) → w ∈ Wsub h hα A := by
    intro A w hw h1 h2 h3 h4
    refine ⟨hw, mem_on_closure (E := E) (s := ({a, b, c, d} : Set G)) hE
      (f := fun e => w * e * w⁻¹ * e⁻¹) ?_ ?_⟩
    · intro e he e' he'
      exact h.cmt_mul_right hα hw (h.E_le_Qs hα he) (h.E_le_Qs hα he')
    · intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl | rfl
      exacts [h1, h2, h3, h4]
  have hw₁ : w₁ ∈ Wsub h hα (zpowers α) :=
    hmul _ w₁ hw₁Q (by rw [e1]; exact ha₁) (by rw [e2]; exact hb₁) (by rw [e3]; exact hc₁)
      (by rw [e4]; exact hd₁)
  have hw₂ : w₂ ∈ Wsub h hα (zpowers (α * t)) :=
    hmul _ w₂ hw₂Q (by rw [f1]; exact ha₂) (by rw [f2]; exact hb₂) (by rw [f3]; exact hc₂)
      (by rw [f4]; exact hd₂)
  have hu : (w₁ * w₂)⁻¹ * q ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    refine h.eq_mod_Zg_of_gen hα hE (mul_mem hw₁Q hw₂Q) hq ?_
    intro g hg
    have hgE : g ∈ E := hgen g hg
    rw [h.cmt_mul_left hα hw₁Q hw₂Q (h.E_le_Qs hα hgE)]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [e1, f1, hca]
    · rw [e2, f2, hcb]
    · rw [e3, f3, hcc]
    · rw [e4, f4, hcd]
  have hu2 : ((w₁ * w₂)⁻¹ * q) * w₂ = w₂ * ((w₁ * w₂)⁻¹ * q) := (h.Zg_cent_Q hα hu).2 w₂ hw₂Q
  refine ⟨w₁ * ((w₁ * w₂)⁻¹ * q), mul_mem hw₁ (h.Zg_mem_Wsub hα _ hu), w₂, hw₂, ?_⟩
  calc q = w₁ * (w₂ * ((w₁ * w₂)⁻¹ * q)) := by group
    _ = w₁ * (((w₁ * w₂)⁻¹ * q) * w₂) := by rw [hu2]
    _ = w₁ * ((w₁ * w₂)⁻¹ * q) * w₂ := by group

theorem conj_z_W1 {α : G} (hα : AlphaSpec S z t α) {w : G} (hw : w ∈ Wsub h hα (zpowers α)) :
    z * w * z⁻¹ ∈ Wsub h hα (zpowers (α * t)) := by
  refine ⟨h.z_norm_Qs hα hw.1, fun e he => ?_⟩
  rw [h.chi_conj_z he]
  rcases mem_zpowers_sq_eq_one hα.sq (hw.2 e he) with h1 | h1
  · rw [h1]; simp
  · rw [h1, h.z_conj_alpha hα]; exact mem_zpowers _

theorem conj_z_W2 {α : G} (hα : AlphaSpec S z t α) {w : G}
    (hw : w ∈ Wsub h hα (zpowers (α * t))) : z * w * z⁻¹ ∈ Wsub h hα (zpowers α) := by
  refine ⟨h.z_norm_Qs hα hw.1, fun e he => ?_⟩
  rw [h.chi_conj_z he]
  rcases mem_zpowers_sq_eq_one (h.zinv_alpha_t hα).sq (hw.2 e he) with h1 | h1
  · rw [h1]; simp
  · rw [h1]
    have : z * (α * t) * z⁻¹ = α := by
      calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
        _ = α * t * t := by rw [h.z_conj_alpha hα, h.z_conj_t]
        _ = α := by rw [mul_assoc, h.t_sq, mul_one]
    rw [this]
    exact mem_zpowers α

theorem W_norm_Wsub {α : G} (hα : AlphaSpec S z t α) {A : Subgroup G} {b w : G}
    (hb : b ∈ L ⊓ centralizer ({t} : Set G)) (hw : w ∈ Wsub h hα A) :
    b * w * b⁻¹ ∈ Wsub h hα A := by
  refine ⟨h.W_norm_Qs hα hb hw.1, fun e he => ?_⟩
  have he' : b⁻¹ * e * b ∈ E := by
    have := h.W_norm_E (inv_mem hb) he
    simpa using this
  rw [h.chi_conj_W hα hb hw.1 he]
  exact hw.2 _ he'

theorem exists_fixed_lift {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t) {b d : G}
    (hb : b ∈ B) (hb3 : orderOf b = 3) (hd : d ∈ E) (hbd : b * d * b⁻¹ = d) :
    ∃ g, IsLift h hα α d g ∧ g * b = b * g := by
  obtain ⟨a₁, a₂, a₃, a₄, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a₁, a₂, a₃, a₄} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  obtain ⟨w, hw⟩ := h.exists_isLift hα (h.zinv_alpha hα) hE (hgen a₁ (by simp))
    (hgen a₂ (by simp)) (hgen a₃ (by simp)) (hgen a₄ (by simp)) hd
  have hbW : b ∈ L ⊓ centralizer ({t} : Set G) := h.B_le_W hb
  have h1 := h.isLift_conj_W hα hbW hd hw
  rw [hbd] at h1
  have hu := h.isLift_unique hα hw h1
  have hbu : b * (w⁻¹ * (b * w * b⁻¹)) = (w⁻¹ * (b * w * b⁻¹)) * b := h.W_cent_Z hα hbW hu
  have hu2 : (w⁻¹ * (b * w * b⁻¹)) * (w⁻¹ * (b * w * b⁻¹)) = 1 := h.Zg_sq hα hu
  set u := w⁻¹ * (b * w * b⁻¹) with hu_def
  have hwb : b * w * b⁻¹ = w * u := by rw [hu_def]; group
  have hbu' : b * u * b⁻¹ = u := by rw [hbu]; group
  have hb3' : b * (b * b) = 1 := by
    have : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
    rwa [pow_three] at this
  have e2 : b * (b * w * b⁻¹) * b⁻¹ = w * u * u := by
    calc b * (b * w * b⁻¹) * b⁻¹ = b * (w * u) * b⁻¹ := by rw [hwb]
      _ = (b * w * b⁻¹) * (b * u * b⁻¹) := by group
      _ = w * u * u := by rw [hwb, hbu']
  have e3 : b * (b * (b * w * b⁻¹) * b⁻¹) * b⁻¹ = w * u * u * u := by
    calc b * (b * (b * w * b⁻¹) * b⁻¹) * b⁻¹ = b * (w * u * u) * b⁻¹ := by rw [e2]
      _ = (b * w * b⁻¹) * (b * u * b⁻¹) * (b * u * b⁻¹) := by group
      _ = w * u * u * u := by rw [hwb, hbu']
  have e4 : b * (b * (b * w * b⁻¹) * b⁻¹) * b⁻¹ = w := by
    calc b * (b * (b * w * b⁻¹) * b⁻¹) * b⁻¹ = (b * (b * b)) * w * (b * (b * b))⁻¹ := by group
      _ = w := by rw [hb3']; group
  have hu1 : u = 1 := by
    have h5 : w * u * u * u = w := by rw [← e3, e4]
    have h6 : u * u * u = 1 := by
      have : w * (u * u * u) = w * 1 := by
        calc w * (u * u * u) = w * u * u * u := by group
          _ = w := h5
          _ = w * 1 := by rw [mul_one]
      exact mul_left_cancel this
    calc u = (u * u) * u := by rw [hu2, one_mul]
      _ = 1 := h6
  refine ⟨w, hw, ?_⟩
  have : b * w * b⁻¹ = w := by rw [hwb, hu1, mul_one]
  calc w * b = (b * w * b⁻¹) * b := by rw [this]
    _ = b * w := by group

theorem rel_d_t {α : G} (hα : AlphaSpec S z t α) {x w : G} (hx : x ∈ E)
    (hw : IsLift h hα α x w) :
    ∃ a : G, (a = 1 ∨ a = t) ∧ x = w * (z * w * z⁻¹) * a ∧
      w * (z * w * z⁻¹) = (z * w * z⁻¹) * w := by
  obtain ⟨a, ha, hxa, hcom⟩ := h.rel_d hα hx hw
  have hzx : z * x * z⁻¹ = x := by
    have := h.S_comm_E z h.zS x hx
    calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [this]
      _ = x := by group
  have hz2' : z * (z * w * z⁻¹) * z⁻¹ = w := by
    calc z * (z * w * z⁻¹) * z⁻¹ = (z * z) * w * (z * z)⁻¹ := by group
      _ = w := by rw [h.z_sq]; group
  have e1 : z * x * z⁻¹ = (z * w * z⁻¹) * w * (z * a * z⁻¹) := by
    calc z * x * z⁻¹ = z * (w * (z * w * z⁻¹) * a) * z⁻¹ := by rw [← hxa]
      _ = (z * w * z⁻¹) * (z * (z * w * z⁻¹) * z⁻¹) * (z * a * z⁻¹) := by group
      _ = (z * w * z⁻¹) * w * (z * a * z⁻¹) := by rw [hz2']
  have hτ : z * a * z⁻¹ = a := by
    have e2 : (z * w * z⁻¹) * w * a = (z * w * z⁻¹) * w * (z * a * z⁻¹) := by
      calc (z * w * z⁻¹) * w * a = w * (z * w * z⁻¹) * a := by rw [← hcom]
        _ = x := hxa.symm
        _ = z * x * z⁻¹ := hzx.symm
        _ = (z * w * z⁻¹) * w * (z * a * z⁻¹) := e1
    exact (mul_left_cancel e2).symm
  refine ⟨a, ?_, hxa, hcom⟩
  rcases (h.mem_Zg hα).1 ha with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rw [h1, h.z_conj_alpha hα] at hτ
    exact h.t_ne (mul_eq_left.1 hτ)
  · exfalso
    rw [h1] at hτ
    have : z * (α * t) * z⁻¹ = α := by
      calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
        _ = α * t * t := by rw [h.z_conj_alpha hα, h.z_conj_t]
        _ = α := by rw [mul_assoc, h.t_sq, mul_one]
    rw [this] at hτ
    exact h.t_ne (mul_eq_left.1 hτ.symm)

theorem Q_norm_Wsub {α : G} (hα : AlphaSpec S z t α) {A : Subgroup G} {q w : G}
    (hq : q ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) (hw : w ∈ Wsub h hα A) :
    q * w * q⁻¹ ∈ Wsub h hα A := by
  have hc := h.cmt_mem hα hq hw.1
  have : q * w * q⁻¹ = (q * w * q⁻¹ * w⁻¹) * w := by group
  rw [this]
  exact mul_mem (h.Zg_mem_Wsub hα _ hc) hw

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
