module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.AutXCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Ext2A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Ext2BB

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

private theorem Gx_inf_mul_self {H : Type} [Group H] {x t : H} (hx2 : x * x = 1) :
    Gx x ⊓ Gx (x * t) = Gx x ⊓ Gx t := by
  have ht_eq : x * (x * t) = t := by rw [← mul_assoc, hx2, one_mul]
  ext g
  simp only [Subgroup.mem_inf, mem_Gx]
  constructor
  · rintro ⟨hgx, hgxt⟩
    refine ⟨hgx, ?_⟩
    calc t * g = x * (x * t) * g := by rw [ht_eq]
      _ = x * ((x * t) * g) := by rw [mul_assoc]
      _ = x * (g * (x * t)) := by rw [hgxt]
      _ = (x * g) * (x * t) := by rw [← mul_assoc]
      _ = (g * x) * (x * t) := by rw [hgx]
      _ = g * (x * (x * t)) := by rw [mul_assoc]
      _ = g * t := by rw [ht_eq]
  · rintro ⟨hgx, hgt⟩
    refine ⟨hgx, ?_⟩
    calc (x * t) * g = x * (t * g) := by rw [mul_assoc]
      _ = x * (g * t) := by rw [hgt]
      _ = (x * g) * t := by rw [← mul_assoc]
      _ = (g * x) * t := by rw [hgx]
      _ = g * (x * t) := by rw [mul_assoc]

private theorem isConj_z_mul_of_orb2B {w d : G} (h : F5Std a z)
    (hw : w ∈ orb2AB a z a) (hd1 : d ∈ orb2A a a) (hd2 : d ∈ orb2B a z (a * w)) :
    IsConj z (d * w) := by
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
    simpa [pow_two] using h2
  have haw : a * (a * w) = w := by rw [← mul_assoc, ha2, one_mul]
  have hb : a * w ∈ orb2B a z a := ⟨hw.2, by rw [haw]; exact hw.1⟩
  have hwG : w ∈ Gx a := h.mem_Gx_of_orb2AB (IsConj.refl a) hw
  have hawb : a * w = w * a := mem_Gx.mp hwG
  have had : a * d = d * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hd1.1) (Or.inl hd1.2)
  have hbd : (a * w) * d = d * (a * w) :=
    h.mul_comm (Or.inl hb.1) (Or.inl hd2.1) (Or.inr hd2.2)
  have hwd : w * d = d * w := by
    calc w * d = (a * (a * w)) * d := congrArg (fun t => t * d) haw.symm
      _ = a * ((a * w) * d) := by rw [mul_assoc]
      _ = a * (d * (a * w)) := by rw [hbd]
      _ = (a * d) * (a * w) := by rw [← mul_assoc]
      _ = (d * a) * (a * w) := by rw [had]
      _ = d * (a * (a * w)) := by rw [mul_assoc]
      _ = d * w := congrArg (fun t => d * t) haw
  have hw2 : w * w = 1 := by
    have h2 : w ^ 2 = 1 := by
      rw [← h.orderOf_eq_two (Or.inr hw.1)]; exact pow_orderOf_eq_one w
    simpa [pow_two] using h2
  have hd2' : d * d = 1 := by
    have h2 : d ^ 2 = 1 := by
      rw [← h.orderOf_eq_two (Or.inl hd1.1)]; exact pow_orderOf_eq_one d
    simpa [pow_two] using h2
  have hwd2 : (w * d) ^ 2 = 1 := by
    rw [pow_two]
    calc (w * d) * (w * d) = w * (d * (w * d)) := mul_assoc w d (w * d)
      _ = w * ((d * w) * d) := congrArg (fun t => w * t) (mul_assoc d w d).symm
      _ = w * ((w * d) * d) := congrArg (fun t => w * (t * d)) hwd.symm
      _ = w * (w * (d * d)) := congrArg (fun t => w * t) (mul_assoc w d d)
      _ = (w * w) * (d * d) := (mul_assoc w w (d * d)).symm
      _ = 1 := by rw [hw2, hd2', mul_one]
  have hne : w * d ≠ 1 := by
    intro h1
    have hwd_eq : w = d := by
      have h2 : d = w⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2, inv_eq_of_mul_eq_one_right hw2]
    exact not_isConj_of_isF5Type h.iface h.typ (hd1.1.trans ((hwd_eq ▸ hw.1).symm))
  have hord : orderOf (w * d) = 2 := orderOf_eq_prime hwd2 hne
  rcases h.loc.gzClass.self.inv_two (w * d) hord with hA | hZ
  · exfalso
    have hdQ : d ∈ Qz w := mem_Qz_of_isConj_mul h hw.1 hd1.1 hA
    have haQ : a ∈ Qz w :=
      mem_Qz_of_isConj_mul h hw.1 (IsConj.refl a) (by rw [← hawb]; exact hw.2)
    have hnot : a * d ∉ Qz w := by
      refine not_mem_Qz_of_isConj_mul h hw.1 hd1.2 ?_
      rw [show w * (a * d) = (a * w) * d by rw [← mul_assoc, ← hawb]]
      exact hd2.2
    exact hnot ((Qz w).mul_mem haQ hdQ)
  · rwa [show d * w = w * d from hwd.symm]

theorem exists_iso_2B (h : F5Std a z) (h' : F5Std a' z') {α : G → G'}
    (hα : IsIsoOn (Gx a) (Gx a') α) {b : G} (hb : b ∈ orb2B a z a) :
    ∃ β : G → G', IsIsoOn (Gx b) (Gx (α b)) β ∧ ∀ x ∈ Gxy a b, β x = α x := by
  obtain ⟨c, hc1, hc2⟩ := exists_orb2A_inter_orb2A h hb
  have hbc : b * c = c * b :=
    h.mul_comm (Or.inl hb.1) (Or.inl hc1.1) (Or.inl hc2.2)
  have hab : a * b = b * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hb.1) (Or.inr hb.2)
  have hac : a * c = c * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hc1.1) (Or.inl hc1.2)
  obtain ⟨β₁, hβ₁, hβ₁α⟩ := exists_iso_2A h h' hα hc1
  have hαa : α a = a' := iso_apply_self h h' hα
  have hFc : F5Std c z := h.of_isConj hc1.1 (IsConj.refl z)
  have hFc' : F5Std (α c) z' := h'.of_isConj (typing_2A h h' hα hc1).1 (IsConj.refl z')
  have hbc_orb : b ∈ orb2A c c :=
    ⟨hc1.1.symm.trans hb.1, by rw [← hbc]; exact hc1.1.symm.trans hc2.2⟩
  obtain ⟨β₂, hβ₂, hβ₂β₁⟩ := exists_iso_2A hFc hFc' hβ₁ hbc_orb
  have hbGxyac : b ∈ Gxy a c :=
    mem_Gxy.mpr ⟨mem_Gx.mpr hab, mem_Gx.mpr hbc.symm⟩
  have hβ₁b : β₁ b = α b := hβ₁α b hbGxyac
  have hβ₂' : IsIsoOn (Gx b) (Gx (α b)) β₂ := by rw [← hβ₁b]; exact hβ₂
  have haGxycb : a ∈ Gxy c b :=
    mem_Gxy.mpr ⟨mem_Gx.mpr hac.symm, mem_Gx.mpr hab.symm⟩
  have haGxyac : a ∈ Gxy a c := mem_Gxy.mpr ⟨self_mem_Gx a, mem_Gx.mpr hac.symm⟩
  have hβ₂a : β₂ a = a' := by
    rw [hβ₂β₁ a haGxycb, hβ₁α a haGxyac, hαa]
  have hbGa : b ∈ Gx a := mem_Gx.mpr hab
  have haGb : a ∈ Gx b := mem_Gx.mpr hab.symm
  have h₁ : IsIsoOn (Gxy a b) (Gxy a' (α b)) α := by
    simpa only [Gxy_eq_inf] using hα.restrict_cent hbGa
  have h₂ : IsIsoOn (Gxy a b) (Gxy a' (α b)) β₂ := by
    have h := hβ₂'.restrict_cent haGb
    rw [hβ₂a, inf_comm (Gx b) (Gx a), inf_comm (Gx (α b)) (Gx a')] at h
    rwa [← Gxy_eq_inf a b, ← Gxy_eq_inf a' (α b)] at h
  have hS : ∀ x ∈ Gxyz a b c, α x = β₂ x := by
    intro x hx
    obtain ⟨hxa, hxb, hxc⟩ := mem_Gxyz.mp hx
    exact (hβ₁α x (mem_Gxy.mpr ⟨hxa, hxc⟩)).symm.trans
      (hβ₂β₁ x (mem_Gxy.mpr ⟨hxc, hxb⟩)).symm
  rcases aut_X_cent_iso h hb ⟨hc1, Or.inl hc2⟩ h₁ h₂ hS with hcase | hcase
  · exact ⟨β₂, hβ₂', fun x hx => (hcase x hx).symm⟩
  · refine ⟨fun x => β₂ (c * x * c⁻¹), ?_, ?_⟩
    · exact (isIsoOn_conj (K := Gx b) (mem_Gx.mpr hbc)).comp hβ₂'
    · intro x hx
      exact (hcase x hx).symm

theorem exists_iso_2AB (h : F5Std a z) (h' : F5Std a' z') {α : G → G'}
    (hα : IsIsoOn (Gx a) (Gx a') α) {w : G} (hw : w ∈ orb2AB a z a) :
    ∃ β : G → G', IsIsoOn (Gx w) (Gx (α w)) β ∧ ∀ x ∈ Gxy a w, β x = α x := by
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
    simpa [pow_two] using h2
  have ha'2 : a' * a' = 1 := by
    have h2 : a' ^ 2 = 1 := by rw [← h'.typ.orderOf_a]; exact pow_orderOf_eq_one a'
    simpa [pow_two] using h2
  have haw : a * (a * w) = w := by rw [← mul_assoc, ha2, one_mul]
  have hb : a * w ∈ orb2B a z a := ⟨hw.2, by rw [haw]; exact hw.1⟩
  have hwG : w ∈ Gx a := h.mem_Gx_of_orb2AB (IsConj.refl a) hw
  have hawb : a * w = w * a := mem_Gx.mp hwG
  have hGxy : Gxy a w = Gxy a (a * w) := by
    rw [Gxy_eq_inf a w, Gxy_eq_inf a (a * w)]
    exact (Gx_inf_mul_self (x := a) (t := w) ha2).symm
  obtain ⟨d, hd1, hd2⟩ := exists_orb2A_inter_orb2B h hb
  have had : a * d = d * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hd1.1) (Or.inl hd1.2)
  have hbd : (a * w) * d = d * (a * w) :=
    h.mul_comm (Or.inl hb.1) (Or.inl hd2.1) (Or.inr hd2.2)
  have hwd : w * d = d * w := by
    calc w * d = (a * (a * w)) * d := congrArg (fun t => t * d) haw.symm
      _ = a * ((a * w) * d) := by rw [mul_assoc]
      _ = a * (d * (a * w)) := by rw [hbd]
      _ = (a * d) * (a * w) := by rw [← mul_assoc]
      _ = (d * a) * (a * w) := by rw [had]
      _ = d * (a * (a * w)) := by rw [mul_assoc]
      _ = d * w := congrArg (fun t => d * t) haw
  have hdGxw : d ∈ Gx w := mem_Gx.mpr hwd
  obtain ⟨β₁, hβ₁, hβ₁α⟩ := exists_iso_2A h h' hα hd1
  have hFd : F5Std d z := h.of_isConj hd1.1 (IsConj.refl z)
  have hFd' : F5Std (α d) z' := h'.of_isConj (typing_2A h h' hα hd1).1 (IsConj.refl z')
  have hdw : w ∈ orb2BB d z d := ⟨hw.1, isConj_z_mul_of_orb2B h hw hd1 hd2⟩
  obtain ⟨γ₁, hγ₁, hγ₁β₁⟩ := exists_iso_2BB hFd hFd' hβ₁ hdw
  have hwGxyd : w ∈ Gxy a d := mem_Gxy.mpr ⟨hwG, mem_Gx.mpr hwd.symm⟩
  have hβ₁w : β₁ w = α w := hβ₁α w hwGxyd
  have hγ₁' : IsIsoOn (Gx w) (Gx (α w)) γ₁ := by rw [← hβ₁w]; exact hγ₁
  have haGxw : a ∈ Gx w := mem_Gx.mpr hawb.symm
  have haGxad : a ∈ Gxy a d := mem_Gxy.mpr ⟨self_mem_Gx a, mem_Gx.mpr had.symm⟩
  have haGxydw : a ∈ Gxy d w := mem_Gxy.mpr ⟨mem_Gx.mpr had.symm, haGxw⟩
  have hγ₁a : γ₁ a = a' := by
    rw [hγ₁β₁ a haGxydw, hβ₁α a haGxad, iso_apply_self h h' hα]
  have hbGxa : a * w ∈ Gx a := (Gx a).mul_mem (self_mem_Gx a) hwG
  have h₁ : IsIsoOn (Gxy a (a * w)) (Gxy a' (α w)) α := by
    have hαw : α (a * w) = a' * α w := by
      rw [hα.map_mul a (self_mem_Gx a) w hwG, iso_apply_self h h' hα]
    have h := hα.restrict_cent hbGxa
    rw [hαw, Gx_inf_mul_self (x := a') (t := α w) ha'2] at h
    rwa [← Gxy_eq_inf a (a * w), ← Gxy_eq_inf a' (α w)] at h
  have h₂ : IsIsoOn (Gxy a (a * w)) (Gxy a' (α w)) γ₁ := by
    have h := hγ₁'.restrict_cent haGxw
    rw [hγ₁a, inf_comm (Gx w) (Gx a), inf_comm (Gx (α w)) (Gx a')] at h
    rwa [← Gxy_eq_inf a w, hGxy, ← Gxy_eq_inf a' (α w)] at h
  have hS : ∀ x ∈ Gxyz a (a * w) d, α x = γ₁ x := by
    intro x hx
    obtain ⟨hxa, hxaw, hxd⟩ := mem_Gxyz.mp hx
    have hxw : x ∈ Gx w := by
      have h1 : x ∈ Gx a ⊓ Gx (a * w) := Subgroup.mem_inf.mpr ⟨hxa, hxaw⟩
      rw [Gx_inf_mul_self (x := a) (t := w) ha2] at h1
      exact (Subgroup.mem_inf.mp h1).2
    exact (hβ₁α x (mem_Gxy.mpr ⟨hxa, hxd⟩)).symm.trans
      (hγ₁β₁ x (mem_Gxy.mpr ⟨hxd, hxw⟩)).symm
  rcases aut_X_cent_iso h hb ⟨hd1, Or.inr hd2⟩ h₁ h₂ hS with hcase | hcase
  · refine ⟨γ₁, hγ₁', ?_⟩
    intro x hx
    rw [hGxy] at hx
    exact (hcase x hx).symm
  · refine ⟨fun x => γ₁ (d * x * d⁻¹), ?_, ?_⟩
    · exact (isIsoOn_conj (K := Gx w) hdGxw).comp hγ₁'
    · intro x hx
      rw [hGxy] at hx
      exact (hcase x hx).symm

end CFSG.EvenSporadicStandard.HNRecog.Section4
