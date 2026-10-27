module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep1

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

omit [Finite G] in
theorem comm_conj {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (g : G) :
    ∀ a ∈ conjSubgroup A g, ∀ b ∈ conjSubgroup B g, a * b = b * a := by
  intro a ha b hb
  rw [mem_conjSubgroup_iff] at ha hb
  have := h _ ha _ hb
  have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := this
      _ = g * (b * a) * g⁻¹ := by group
  simpa using h2

omit [Finite G] in
theorem commute_of_mul_commute {a r v : G} (h : Commute (a * r) v) (hr : Commute r v) :
    Commute a v := by
  have := h.mul_left hr.inv_left
  simpa using this

omit [Finite G] in
theorem commute_right_of_mul {a r v : G} (h : Commute (a * r) v) (ha : Commute a v) :
    Commute r v := by
  have e : r = a⁻¹ * (a * r) := by group
  rw [e]
  exact ha.inv_left.mul_left h

namespace Dbl

variable (D : Dbl T M H S L n t)
include D

theorem mem_baumD_iff {f : G} : f ∈ baumD S L ↔ f ∈ baum S ∧ (∀ l ∈ L, l * f = f * l) ∧
    (∀ l ∈ conjSubgroup L t, l * f = f * l) := by
  show f ∈ baum S ⊓ centralizer ((conjJoin S L : Subgroup G) : Set G) ↔ _
  rw [D.hjoin]
  constructor
  · rintro ⟨hB, hC⟩
    refine ⟨hB, fun l hl => ?_, fun l hl => ?_⟩
    · exact Subgroup.mem_centralizer_iff.1 hC l (Subgroup.mem_sup_left hl)
    · exact Subgroup.mem_centralizer_iff.1 hC l (Subgroup.mem_sup_right hl)
  · rintro ⟨hB, h1, h2⟩
    exact ⟨hB, C56.mem_centralizer_sup h1 h2⟩

theorem U_cases₂ {g : G} (hg : g ∈ S) :
    (conjSubgroup (blockU L) g = blockU L ∧
        conjSubgroup (conjSubgroup (blockU L) t) g = conjSubgroup (blockU L) t) ∨
      (conjSubgroup (blockU L) g = conjSubgroup (blockU L) t ∧
        conjSubgroup (conjSubgroup (blockU L) t) g = blockU L) := by
  have e1 := blockU_conjR L t
  rcases D.conjR_L₂_cases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨?_, ?_⟩
    · have h3 := blockU_conjR L g
      rw [h1] at h3
      exact h3.symm
    · have h3 := blockU_conjR (conjR L t) g
      rw [h2, e1] at h3
      exact h3.symm
  · right
    refine ⟨?_, ?_⟩
    · have h3 := blockU_conjR L g
      rw [h1, e1] at h3
      exact h3.symm
    · have h3 := blockU_conjR (conjR L t) g
      rw [h2, e1] at h3
      exact h3.symm

theorem conj_U_sup {g : G} (hg : g ∈ S) :
    conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) g =
      blockU L ⊔ conjSubgroup (blockU L) t := by
  rw [C5.conjSubgroup_sup]
  rcases D.U_cases₂ hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

end Dbl

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem comm_U₁x_U₂x : ∀ y ∈ conjSubgroup (blockU L) x, ∀ a ∈ conjSubgroup (conjSubgroup (blockU L) t) x,
    y * a = a * y := by
  have h : ∀ u ∈ blockU L, ∀ v ∈ conjSubgroup (blockU L) t, u * v = v * u :=
    fun u hu v hv => P.D.comm_elem u (P.U₁_le_L hu) v (P.U₂_le_L₂ hv)
  exact comm_conj h x

theorem a_decomp {a : G} (ha : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x) :
    ∃ u' ∈ W, ∃ d' ∈ baum S ⊓ centralizer (blockU L : Set G) ⊓ centralizer (L : Set G),
      a = u' * d' := by
  have kf := P.kf₁
  have haQ : a ∈ baum S ⊓ centralizer (blockU L : Set G) := P.U₂x_le_Q₁ ha
  have ha' : a ∈ blockU L ⊔
      (baum S ⊓ centralizer (blockU L : Set G) ⊓ centralizer (L : Set G)) := by
    rw [← kf.Q_eq]; exact haQ
  have hcomm₁ : ∀ u ∈ blockU L, ∀ d ∈ (baum S ⊓ centralizer (blockU L : Set G) ⊓
      centralizer (L : Set G)), u * d = d * u :=
    fun u hu d hd => Subgroup.mem_centralizer_iff.1 hd.2 u (P.U₁_le_L hu)
  obtain ⟨u', hu', d', hd', hae⟩ := mem_sup_of_commute hcomm₁ ha'
  refine ⟨u', ?_, d', hd', hae⟩
  rw [← kf.infC]
  refine ⟨hu', Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hd'X : d' ∈ centralizer (conjSubgroup (blockU L) x : Set G) := by
    have h1 : d' ∈ conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x :=
      kf.D_le ⟨hd'.1, hd'.2⟩
    rw [kf.Qx] at h1
    exact h1.2
  have hyd : y * d' = d' * y := Subgroup.mem_centralizer_iff.1 hd'X y hy
  have hya : y * (u' * d') = (u' * d') * y := by
    rw [← hae]; exact P.comm_U₁x_U₂x y hy a ha
  have : (y * u') * d' = (u' * y) * d' := by
    calc (y * u') * d' = y * (u' * d') := by group
      _ = (u' * d') * y := hya
      _ = u' * (d' * y) := by group
      _ = u' * (y * d') := by rw [hyd]
      _ = (u' * y) * d' := by group
  exact mul_right_cancel this

theorem B_decomp {b : G} (hb : b ∈ baum S) :
    ∃ x₁ ∈ conjSubgroup (blockU L) x, ∃ u₁ ∈ blockU L,
      ∃ a ∈ conjSubgroup (conjSubgroup (blockU L) t) x, ∃ u₂ ∈ conjSubgroup (blockU L) t,
        ∃ e ∈ W, ∃ f ∈ baumD S L, b = x₁ * (u₁ * (a * (u₂ * (e * f)))) := by
  have kf₁ := P.kf₁
  have kf₂ := P.kf₂
  have hb₁ : b ∈ conjSubgroup (blockU L) x ⊔ (baum S ⊓ centralizer (blockU L : Set G)) := by
    rw [kf₁.supQ]; exact hb
  obtain ⟨x₁, hx₁, q₁, hq₁, rfl⟩ := mem_sup_of_le_normalizer
    (fun g hg => P.loc.rk.B_le_normQ (kf₁.Ux_le_B hg)) hb₁
  have hq₁' : q₁ ∈ blockU L ⊔
      (baum S ⊓ centralizer (blockU L : Set G) ⊓ centralizer (L : Set G)) := by
    rw [← kf₁.Q_eq]; exact hq₁
  have hcomm₁ : ∀ u ∈ blockU L, ∀ d ∈ (baum S ⊓ centralizer (blockU L : Set G) ⊓
      centralizer (L : Set G)), u * d = d * u :=
    fun u hu d hd => Subgroup.mem_centralizer_iff.1 hd.2 u (P.U₁_le_L hu)
  obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ := mem_sup_of_commute hcomm₁ hq₁'
  have hd₁B : d₁ ∈ baum S := hd₁.1.1
  have hb₂ : d₁ ∈ conjSubgroup (conjSubgroup (blockU L) t) x ⊔
      conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := by
    rw [kf₂.supQ]; exact hd₁B
  obtain ⟨a, ha, q₂, hq₂, rfl⟩ := mem_sup_of_le_normalizer
    (fun g hg => P.loc₂.rk.B_le_normQ (kf₂.Ux_le_B hg)) hb₂
  have hq₂' : q₂ ∈ conjSubgroup (blockU L) t ⊔
      (conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t ⊓
        centralizer (conjSubgroup L t : Set G)) := by
    rw [← kf₂.Q_eq]; exact hq₂
  have hcomm₂ : ∀ u ∈ conjSubgroup (blockU L) t, ∀ d ∈ (conjSubgroup (baum S ⊓
      centralizer (blockU L : Set G)) t ⊓ centralizer (conjSubgroup L t : Set G)), u * d = d * u :=
    fun u hu d hd => Subgroup.mem_centralizer_iff.1 hd.2 u (P.U₂_le_L₂ hu)
  obtain ⟨u₂, hu₂, d₂, hd₂, rfl⟩ := mem_sup_of_commute hcomm₂ hq₂'
  obtain ⟨u', hu'W, d', hd', hadec⟩ := P.a_decomp ha
  have hu'U : u' ∈ blockU L := P.loc.rk.W_le_U hu'W
  have hu'L : u' ∈ L := P.U₁_le_L hu'U
  have hu₂L₂ : u₂ ∈ conjSubgroup L t := P.U₂_le_L₂ hu₂
  have hc_u'u₂ : u' * u₂ = u₂ * u' := P.D.comm_elem u' hu'L u₂ hu₂L₂
  have hc_u'd' : u' * d' = d' * u' := Subgroup.mem_centralizer_iff.1 hd'.2 u' hu'L
  have hf_eq : u₂⁻¹ * (d'⁻¹ * (a * (u₂ * d₂))) = u' * d₂ := by
    have e1 : d'⁻¹ * (u' * d') = u' := by rw [hc_u'd']; group
    have e2 : u₂⁻¹ * u' = u' * u₂⁻¹ := by
      calc u₂⁻¹ * u' = u₂⁻¹ * (u' * u₂) * u₂⁻¹ := by group
        _ = u₂⁻¹ * (u₂ * u') * u₂⁻¹ := by rw [hc_u'u₂]
        _ = u' * u₂⁻¹ := by group
    rw [hadec]
    calc u₂⁻¹ * (d'⁻¹ * ((u' * d') * (u₂ * d₂))) = u₂⁻¹ * ((d'⁻¹ * (u' * d')) * (u₂ * d₂)) := by
          group
      _ = u₂⁻¹ * (u' * (u₂ * d₂)) := by rw [e1]
      _ = (u₂⁻¹ * u') * (u₂ * d₂) := by group
      _ = (u' * u₂⁻¹) * (u₂ * d₂) := by rw [e2]
      _ = u' * d₂ := by group
  refine ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, u'⁻¹, W.inv_mem hu'W, u' * d₂, ?_, ?_⟩
  · rw [P.D.mem_baumD_iff]
    refine ⟨(baum S).mul_mem (P.loc.rk.U_le_B hu'U) (P.loc₂.rk.Q_le_B hd₂.1), ?_, ?_⟩
    ·
      rw [← hf_eq]
      have hCL : ∀ y ∈ L, ∀ z ∈ centralizer (L : Set G), y * z = z * y :=
        fun y hy z hz => Subgroup.mem_centralizer_iff.1 hz y hy
      intro l hl
      have hm : u₂⁻¹ * (d'⁻¹ * (a * (u₂ * d₂))) ∈ centralizer (L : Set G) := by
        refine (centralizer (L : Set G)).mul_mem ((centralizer (L : Set G)).inv_mem ?_)
          ((centralizer (L : Set G)).mul_mem ((centralizer (L : Set G)).inv_mem hd'.2) hd₁.2)
        exact Subgroup.mem_centralizer_iff.mpr fun v hv => P.D.comm_elem v hv u₂ hu₂L₂
      exact Subgroup.mem_centralizer_iff.1 hm l hl
    · intro l hl
      have hu'C : u' ∈ centralizer (conjSubgroup L t : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun v hv => (P.D.comm_elem u' hu'L v hv).symm
      have hm : u' * d₂ ∈ centralizer (conjSubgroup L t : Set G) :=
        (centralizer _).mul_mem hu'C hd₂.2
      exact Subgroup.mem_centralizer_iff.1 hm l hl
  · rw [inv_mul_cancel_left]

theorem D_comm_X {f : G} (hf : f ∈ baumD S L) :
    (∀ v ∈ conjSubgroup (blockU L) x, v * f = f * v) ∧
      (∀ v ∈ conjSubgroup (conjSubgroup (blockU L) t) x, v * f = f * v) := by
  obtain ⟨hfB, hfL, hfL₂⟩ := P.D.mem_baumD_iff.1 hf
  have kf₁ := P.kf₁
  have kf₂ := P.kf₂
  refine ⟨?_, ?_⟩
  · have hQ : f ∈ baum S ⊓ centralizer (blockU L : Set G) ⊓ centralizer (L : Set G) :=
      ⟨⟨hfB, Subgroup.mem_centralizer_iff.mpr fun v hv => hfL v (P.U₁_le_L hv)⟩,
        Subgroup.mem_centralizer_iff.mpr hfL⟩
    have h1 : f ∈ conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x := kf₁.D_le hQ
    rw [kf₁.Qx] at h1
    exact fun v hv => Subgroup.mem_centralizer_iff.1 h1.2 v hv
  · have hQ : f ∈ conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t ⊓
        centralizer (conjSubgroup L t : Set G) := by
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr hfL₂⟩
      rw [P.loc₂.rk.Q_eq]
      exact ⟨hfB, Subgroup.mem_centralizer_iff.mpr fun v hv => hfL₂ v (P.U₂_le_L₂ hv)⟩
    have h1 := kf₂.D_le hQ
    rw [kf₂.Qx] at h1
    exact fun v hv => Subgroup.mem_centralizer_iff.1 h1.2 v hv

theorem W_le_X : W ≤ conjSubgroup (blockU L) x := by
  have := P.kf₁.infU
  intro w hw
  rw [← this] at hw
  exact hw.2

theorem W₂_le_Y : conjSubgroup W t ≤ conjSubgroup (conjSubgroup (blockU L) t) x := by
  have := P.kf₂.infU
  intro w hw
  rw [← this] at hw
  exact hw.2

theorem B_decomp_C {b : G} (hb : b ∈ baum S) (h1 : ∀ v ∈ blockU L, v * b = b * v)
    (h2 : ∀ v ∈ conjSubgroup (blockU L) t, v * b = b * v) :
    ∃ x₁ ∈ W, ∃ u₁ ∈ blockU L, ∃ a ∈ conjSubgroup W t,
      ∃ u₂ ∈ conjSubgroup (blockU L) t, ∃ e ∈ W, ∃ f ∈ baumD S L,
        b = x₁ * (u₁ * (a * (u₂ * (e * f)))) := by
  obtain ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, e, he, f, hf, rfl⟩ := P.B_decomp hb
  have kf₁ := P.kf₁
  have kf₂ := P.kf₂
  have hU₁ab : ∀ u ∈ blockU L, ∀ v ∈ blockU L, u * v = v * u := P.loc.rk.U_comm
  have hU₂ab : ∀ u ∈ conjSubgroup (blockU L) t, ∀ v ∈ conjSubgroup (blockU L) t, u * v = v * u :=
    P.loc₂.rk.U_comm
  have hWU : ∀ w ∈ W, w ∈ blockU L := fun w hw => P.loc.rk.W_le_U hw
  have hfD := P.D.mem_baumD_iff.1 hf
  have hx₁W : x₁ ∈ W := by
    have hr : ∀ v ∈ blockU L,
        Commute (u₁ * (a * (u₂ * (e * f)))) v := by
      intro v hv
      refine Commute.mul_left (hU₁ab u₁ hu₁ v hv) (Commute.mul_left ?_ (Commute.mul_left ?_
        (Commute.mul_left (hU₁ab e (hWU e he) v hv) ?_)))
      · exact (Subgroup.mem_centralizer_iff.1 (P.U₂x_le_Q₁ ha).2 v hv).symm
      · exact (P.D.comm_elem v (P.U₁_le_L hv) u₂ (P.U₂_le_L₂ hu₂)).symm
      · exact (hfD.2.1 v (P.U₁_le_L hv)).symm
    have hc : ∀ v ∈ blockU L, Commute x₁ v := fun v hv =>
      commute_of_mul_commute (a := x₁) (r := u₁ * (a * (u₂ * (e * f)))) (v := v)
        (h1 v hv).symm (hr v hv)
    have hxQ : x₁ ∈ baum S ⊓ centralizer (blockU L : Set G) :=
      ⟨kf₁.Ux_le_B hx₁, Subgroup.mem_centralizer_iff.mpr fun v hv => (hc v hv).symm⟩
    have : x₁ ∈ conjSubgroup (blockU L) x ⊓ (baum S ⊓ centralizer (blockU L : Set G)) :=
      ⟨hx₁, hxQ⟩
    rwa [kf₁.infQ] at this
  have haW : a ∈ conjSubgroup W t := by
    have hr : ∀ v ∈ conjSubgroup (blockU L) t, Commute (u₂ * (e * f)) v := by
      intro v hv
      refine Commute.mul_left (hU₂ab u₂ hu₂ v hv) (Commute.mul_left ?_ ?_)
      · exact (P.D.comm_elem e (P.U₁_le_L (hWU e he)) v (P.U₂_le_L₂ hv))
      · exact (hfD.2.2 v (P.U₂_le_L₂ hv)).symm
    have hc1 : ∀ v ∈ conjSubgroup (blockU L) t, Commute (x₁ * u₁) v := by
      intro v hv
      refine Commute.mul_left ?_ ?_
      · have := Subgroup.mem_centralizer_iff.1 (by
          have := P.Ux_le_Q₂ hx₁
          rw [P.loc₂.rk.Q_eq] at this
          exact this.2) v hv
        exact this.symm
      · exact P.D.comm_elem u₁ (P.U₁_le_L hu₁) v (P.U₂_le_L₂ hv)
    have hc : ∀ v ∈ conjSubgroup (blockU L) t, Commute a v := by
      intro v hv
      have h3 : Commute (a * (u₂ * (e * f))) v := by
        have hb' : Commute ((x₁ * u₁) * (a * (u₂ * (e * f)))) v := by
          have h5 : Commute (x₁ * (u₁ * (a * (u₂ * (e * f))))) v := (h2 v hv).symm
          have hassoc : x₁ * (u₁ * (a * (u₂ * (e * f)))) =
              (x₁ * u₁) * (a * (u₂ * (e * f))) := by group
          rwa [hassoc] at h5
        exact commute_right_of_mul hb' (hc1 v hv)
      exact commute_of_mul_commute h3 (hr v hv)
    have haQ : a ∈ baum S ⊓ centralizer (conjSubgroup (blockU L) t : Set G) :=
      ⟨kf₂.Ux_le_B ha, Subgroup.mem_centralizer_iff.mpr fun v hv => (hc v hv).symm⟩
    have : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x ⊓
        conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := by
      refine ⟨ha, ?_⟩
      rw [P.loc₂.rk.Q_eq]
      exact haQ
    rwa [kf₂.infQ] at this
  exact ⟨x₁, hx₁W, u₁, hu₁, a, haW, u₂, hu₂, e, he, f, hf, rfl⟩

theorem B_decomp_N0 {b : G} (hb : b ∈ baum S) (h1 : ∀ v ∈ blockU L, v * b = b * v)
    (h2 : ∀ v ∈ conjSubgroup (blockU L) t, v * b = b * v)
    (h3 : ∀ v ∈ conjSubgroup (blockU L) x, v * b = b * v)
    (h4 : ∀ v ∈ conjSubgroup (conjSubgroup (blockU L) t) x, v * b = b * v) :
    b ∈ baumD S L ⊔ (W ⊔ conjSubgroup W t) := by
  obtain ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, e, he, f, hf, rfl⟩ := P.B_decomp_C hb h1 h2
  have kf₁ := P.kf₁
  have kf₂ := P.kf₂
  have hXab : ∀ u ∈ conjSubgroup (blockU L) x, ∀ v ∈ conjSubgroup (blockU L) x, u * v = v * u :=
    P.loc.rk.conj_comm x
  have hYab : ∀ u ∈ conjSubgroup (conjSubgroup (blockU L) t) x,
      ∀ v ∈ conjSubgroup (conjSubgroup (blockU L) t) x, u * v = v * u := P.loc₂.rk.conj_comm x
  have hWU : ∀ w ∈ W, w ∈ blockU L := fun w hw => P.loc.rk.W_le_U hw
  have hW₂U₂ : ∀ w ∈ conjSubgroup W t, w ∈ conjSubgroup (blockU L) t := fun w hw =>
    conjSubgroup_mono P.loc.rk.W_le_U t hw
  have hfD := P.D.mem_baumD_iff.1 hf
  have hfX := P.D_comm_X hf
  have hu₁W : u₁ ∈ W := by
    have hc : ∀ v ∈ conjSubgroup (blockU L) x, Commute u₁ v := by
      intro v hv
      have hr : Commute (a * (u₂ * (e * f))) v := by
        refine Commute.mul_left ?_ (Commute.mul_left ?_ (Commute.mul_left ?_ ?_))
        · exact (P.comm_U₁x_U₂x v hv a (P.W₂_le_Y ha)).symm
        · have := P.Ux_le_Q₂ hv
          rw [P.loc₂.rk.Q_eq] at this
          exact (Subgroup.mem_centralizer_iff.1 this.2 u₂ hu₂)
        · exact (hXab e (P.W_le_X he) v hv)
        · exact (hfX.1 v hv).symm
      have hxc : Commute x₁ v := hXab x₁ (P.W_le_X hx₁) v hv
      have hb' : Commute (x₁ * (u₁ * (a * (u₂ * (e * f))))) v := (h3 v hv).symm
      have hz : Commute (u₁ * (a * (u₂ * (e * f)))) v := commute_right_of_mul hb' hxc
      exact commute_of_mul_commute hz hr
    rw [← kf₁.infC]
    exact ⟨hu₁, Subgroup.mem_centralizer_iff.mpr fun v hv => (hc v hv).symm⟩
  have hu₂W : u₂ ∈ conjSubgroup W t := by
    have hc : ∀ v ∈ conjSubgroup (conjSubgroup (blockU L) t) x, Commute u₂ v := by
      intro v hv
      have hvQ : v ∈ baum S ⊓ centralizer (blockU L : Set G) := P.U₂x_le_Q₁ hv
      have hl : Commute (x₁ * (u₁ * a)) v := by
        refine Commute.mul_left ?_ (Commute.mul_left ?_ ?_)
        · exact (P.comm_U₁x_U₂x x₁ (P.W_le_X hx₁) v hv)
        · exact (Subgroup.mem_centralizer_iff.1 hvQ.2 u₁ hu₁)
        · exact hYab a (P.W₂_le_Y ha) v hv
      have hr : Commute (e * f) v := by
        refine Commute.mul_left ?_ ?_
        · exact (Subgroup.mem_centralizer_iff.1 hvQ.2 e (hWU e he))
        · exact (hfX.2 v hv).symm
      have hb' : Commute ((x₁ * (u₁ * a)) * (u₂ * (e * f))) v := by
        have h5 : Commute (x₁ * (u₁ * (a * (u₂ * (e * f))))) v := (h4 v hv).symm
        have hassoc : x₁ * (u₁ * (a * (u₂ * (e * f)))) =
            (x₁ * (u₁ * a)) * (u₂ * (e * f)) := by group
        rwa [hassoc] at h5
      have hz : Commute (u₂ * (e * f)) v := commute_right_of_mul hb' hl
      exact commute_of_mul_commute hz hr
    rw [← kf₂.infC]
    exact ⟨hu₂, Subgroup.mem_centralizer_iff.mpr fun v hv => (hc v hv).symm⟩
  have hJ : ∀ g ∈ W, g ∈ baumD S L ⊔ (W ⊔ conjSubgroup W t) := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_sup_left hg)
  have hJ₂ : ∀ g ∈ conjSubgroup W t, g ∈ baumD S L ⊔ (W ⊔ conjSubgroup W t) := fun g hg =>
    Subgroup.mem_sup_right (Subgroup.mem_sup_right hg)
  refine Subgroup.mul_mem _ (hJ _ hx₁) (Subgroup.mul_mem _ (hJ _ hu₁W)
    (Subgroup.mul_mem _ (hJ₂ _ ha) (Subgroup.mul_mem _ (hJ₂ _ hu₂W)
      (Subgroup.mul_mem _ (hJ _ he) (Subgroup.mem_sup_left hf)))))

end Setup

end CFSG.QuasithinUnique.AppE
