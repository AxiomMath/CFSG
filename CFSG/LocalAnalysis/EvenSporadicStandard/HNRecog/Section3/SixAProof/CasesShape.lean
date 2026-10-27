module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Psi
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.ModelShapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

private theorem sixA_mul_b_comm_iff {t g b : G} (hb : g * b = b * g) :
    t * b * g = g * (t * b) ↔ t * g = g * t := by
  constructor
  · intro h
    have h' : (t * g) * b = (g * t) * b := by
      calc (t * g) * b = t * (g * b) := mul_assoc _ _ _
        _ = t * (b * g) := by rw [hb]
        _ = (t * b) * g := (mul_assoc _ _ _).symm
        _ = g * (t * b) := h
        _ = (g * t) * b := (mul_assoc _ _ _).symm
    exact mul_right_cancel h'
  · intro h
    calc (t * b) * g = t * (b * g) := mul_assoc _ _ _
      _ = t * (g * b) := by rw [← hb]
      _ = (t * g) * b := (mul_assoc _ _ _).symm
      _ = (g * t) * b := by rw [h]
      _ = g * (t * b) := mul_assoc _ _ _

private theorem sixA_sigma_mul_comm_iff (h : IsF5Type a z) (hx : x ∈ orb6A a a)
    (ψ : SixAIso a x) {g : G} (hgy : g ∈ Gxy a (x * (a * x) ^ 3)) :
    sixASigma * ψ.f g = ψ.f g * sixASigma ↔ g ∈ Gx x := by
  have hby : (a * x) ^ 3 ∈ Gxy a (x * (a * x) ^ 3) := sixA_b_mem_Gxy_y h hx
  have hga : g ∈ Gx a := (mem_Gxy.1 hgy).1
  have h1 : sixASigma * ψ.f g = ψ.f g * sixASigma ↔
      g * (a * x) ^ 3 = (a * x) ^ 3 * g := by
    rw [← ψ.f_b h hx, ← ψ.f_mul hby hgy, ← ψ.f_mul hgy hby]
    exact (ψ.f_inj (mul_mem hby hgy) (mul_mem hgy hby)).trans eq_comm
  rw [h1]
  constructor
  · intro hc
    exact (mem_Gxy.1 ((sixA_mem_Gxy_iff h hx).2 ⟨hgy, hc⟩)).2
  · intro hgx
    exact ((sixA_mem_Gxy_iff h hx).1 (mem_Gxy.2 ⟨hga, hgx⟩)).2

private theorem sixA_t_mul_comm_iff (ψ : SixAIso a x) {g t : G}
    (hgy : g ∈ Gxy a (x * (a * x) ^ 3)) (hty : t ∈ Gxy a (x * (a * x) ^ 3)) :
    ψ.f t * ψ.f g = ψ.f g * ψ.f t ↔ g ∈ Gx t := by
  rw [mem_Gx, ← ψ.f_mul hty hgy, ← ψ.f_mul hgy hty]
  exact ψ.f_inj (mul_mem hty hgy) (mul_mem hgy hty)

theorem sixA_Gxyz_mul_b (h : IsF5Type a z) (hx : x ∈ orb6A a a) (t : G) :
    Gxyz a t x = Gxyz a (t * (a * x) ^ 3) x := by
  ext g
  rw [mem_Gxyz, mem_Gxyz]
  constructor
  · rintro ⟨ha, ht, hx'⟩
    refine ⟨ha, ?_, hx'⟩
    rw [mem_Gx] at ht ⊢
    exact (sixA_mul_b_comm_iff (sixA_comm_b_of_mem (mem_Gxy.2 ⟨ha, hx'⟩))).2 ht
  · rintro ⟨ha, ht, hx'⟩
    refine ⟨ha, ?_, hx'⟩
    rw [mem_Gx] at ht ⊢
    exact (sixA_mul_b_comm_iff (sixA_comm_b_of_mem (mem_Gxy.2 ⟨ha, hx'⟩))).1 ht

theorem sixA_Gxyz_equiv (h : IsF5Type a z) (hx : x ∈ orb6A a a) (ψ : SixAIso a x) {t : G}
    (ht : t ∈ Gxy a x) :
    Nonempty (↥(Gxyz a t x) ≃* ↥(Subgroup.centralizer ({sixASigma, ψ.f t} : Set (Sym 7)))) := by
  have hle : Gxyz a t x ≤ Gxy a (x * (a * x) ^ 3) := by
    intro g hg
    rw [mem_Gxyz] at hg
    exact sixA_Gxy_le a x (mem_Gxy.2 ⟨hg.1, hg.2.2⟩)
  have hty : t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x ht
  have hiff : ∀ g : ↥(Gxy a (x * (a * x) ^ 3)),
      ψ.e g ∈ Subgroup.centralizer ({sixASigma, ψ.f t} : Set (Sym 7)) ↔
        g ∈ (Gxyz a t x).subgroupOf (Gxy a (x * (a * x) ^ 3)) := by
    intro g
    have hgy : (g : G) ∈ Gxy a (x * (a * x) ^ 3) := g.2
    have hfg : ψ.e g = ψ.f (g : G) := (ψ.f_apply g.2).symm
    rw [Subgroup.mem_subgroupOf, hfg, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    rw [sixA_sigma_mul_comm_iff h hx ψ hgy, sixA_t_mul_comm_iff ψ hgy hty, mem_Gxyz]
    exact ⟨fun ⟨hx', ht'⟩ => ⟨(mem_Gxy.1 hgy).1, ht', hx'⟩,
      fun ⟨_, ht', hx'⟩ => ⟨hx', ht'⟩⟩
  obtain ⟨eDC⟩ := sixA_restrict_equiv ψ.e.toMonoidHom ψ.e.injective
    (D := (Gxyz a t x).subgroupOf (Gxy a (x * (a * x) ^ 3)))
    (C := Subgroup.centralizer ({sixASigma, ψ.f t} : Set (Sym 7)))
    (fun c _ => by obtain ⟨d, hd⟩ := ψ.e.surjective c; exact ⟨d, hd⟩) hiff
  exact ⟨(Subgroup.subgroupOfEquivOfLe hle).symm.trans eDC⟩

theorem sixA_shape_B (h : IsF5Type a z) (hx : x ∈ orb6A a a) (ψ : SixAIso a x) {t : G}
    (ht : t ∈ Gxy a x) (hB : sixAIsB (ψ.f t)) : IsShapeZ2TimesD8 ↥(Gxyz a t x) := by
  obtain ⟨e1⟩ := sixA_Gxyz_equiv h hx ψ ht
  obtain ⟨e2⟩ := sixA_model_shape_B (ψ.f_mem_cent h hx ht) hB
  exact ⟨e1.trans e2⟩

theorem sixA_shape_A (h : IsF5Type a z) (hx : x ∈ orb6A a a) (ψ : SixAIso a x) {t : G}
    (ht : t ∈ Gxy a x) (hA : sixAIsA (ψ.f t)) : IsShapeTwoTwoTimesS3 ↥(Gxyz a t x) := by
  obtain ⟨e1⟩ := sixA_Gxyz_equiv h hx ψ ht
  obtain ⟨e2⟩ := sixA_model_shape_A (ψ.f_mem_cent h hx ht) hA
  exact ⟨e1.trans e2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
