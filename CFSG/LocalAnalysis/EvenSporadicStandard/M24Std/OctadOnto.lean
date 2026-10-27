module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.AutCount

public section

namespace CFSG.EvenSporadicStandard.M24Std.Octad

open Subgroup

variable {G : Type} [Group G] [Finite G] {L B : Subgroup G} {z : G}

theorem card_egV_le (hs : LocalSetting G L z) (hBL : B ≤ L) :
    Nat.card (egV B z) ≤ Nat.card B + Nat.card B := by
  let f : B ⊕ B → egV B z := Sum.elim (fun b => ⟨b, B_le_egV b.2⟩)
    (fun b => ⟨b * z, mul_mem (B_le_egV b.2) z_mem_egV⟩)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨b, hb, h | h⟩ := (mem_egV_iff hs hBL).1 hx
    · exact ⟨Sum.inl ⟨b, hb⟩, Subtype.ext h.symm⟩
    · exact ⟨Sum.inr ⟨b, hb⟩, Subtype.ext h.symm⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_sum] at this

theorem card_egM_ge (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) :
    Nat.card B * Nat.card (egNL L B) + Nat.card B * Nat.card (egNL L B) ≤
      Nat.card (egM B z) := by
  choose nb hnbM hnb using fun b : B => exists_conj_eq hs hBL hb hcase b.2
  have hzM : z ∈ egM B z := z_mem_egM hs hBL
  have hHM := egNL_le_egM hs hBL (z := z)
  let g : B × egNL L B → G → G := fun q c => nb q.1 * q.2 * c
  have hg : ∀ q c, c ∈ egM B z → g q c ∈ egM B z := fun q c hc =>
    mul_mem (mul_mem (hnbM q.1) (hHM q.2.2)) hc
  have hconj : ∀ q c, c * z = z * c → g q c * z * (g q c)⁻¹ = z * q.1 := by
    intro q c hc
    have hzh := z_comm hs (mem_inf.1 q.2.2).2
    calc g q c * z * (g q c)⁻¹
        = nb q.1 * q.2 * (c * z) * c⁻¹ * (q.2 : G)⁻¹ * (nb q.1)⁻¹ := by simp only [g]; group
      _ = nb q.1 * ((q.2 : G) * z) * (q.2 : G)⁻¹ * (nb q.1)⁻¹ := by rw [hc]; group
      _ = nb q.1 * z * (nb q.1)⁻¹ := by rw [← hzh]; group
      _ = z * q.1 := hnb q.1
  have key : ∀ q q' c c', c * z = z * c → c' * z = z * c' → g q c = g q' c' →
      q.1 = q'.1 ∧ (q.2 : G) * c = q'.2 * c' := by
    intro q q' c c' hc hc' e
    have h1 := hconj q c hc
    rw [e, hconj q' c' hc'] at h1
    have hb1 : q.1 = q'.1 := Subtype.ext (mul_left_cancel h1).symm
    refine ⟨hb1, ?_⟩
    simp only [g, hb1, mul_assoc] at e
    exact mul_left_cancel e
  let f : (B × egNL L B) ⊕ (B × egNL L B) → egM B z :=
    Sum.elim (fun q => ⟨g q 1, hg q 1 (one_mem _)⟩) (fun q => ⟨g q z, hg q z hzM⟩)
  have h1z : (1 : G) * z = z * 1 := by group
  have hzz : z * z = z * z := rfl
  have hf : Function.Injective f := by
    rintro (q | q) (q' | q') e
    · obtain ⟨h1, h2⟩ := key q q' 1 1 h1z h1z (congrArg Subtype.val e)
      rw [mul_one, mul_one] at h2
      exact congrArg Sum.inl (Prod.ext h1 (Subtype.ext h2))
    · exfalso
      obtain ⟨-, h2⟩ := key q q' 1 z h1z hzz (congrArg Subtype.val e)
      apply z_not_mem_L hs
      rw [mul_one] at h2
      have e' : z = (q'.2 : G)⁻¹ * q.2 := by rw [h2]; group
      rw [e']
      exact mul_mem (inv_mem (mem_inf.1 q'.2.2).2) (mem_inf.1 q.2.2).2
    · exfalso
      obtain ⟨-, h2⟩ := key q q' z 1 hzz h1z (congrArg Subtype.val e)
      apply z_not_mem_L hs
      rw [mul_one] at h2
      have e' : z = (q.2 : G)⁻¹ * q'.2 := by rw [← h2]; group
      rw [e']
      exact mul_mem (inv_mem (mem_inf.1 q.2.2).2) (mem_inf.1 q'.2.2).2
    · obtain ⟨h1, h2⟩ := key q q' z z hzz hzz (congrArg Subtype.val e)
      exact congrArg Sum.inr (Prod.ext h1 (Subtype.ext (mul_right_cancel h2)))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_sum, Nat.card_prod] at this

theorem card_egM_le (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) (hΛ : egLam B z ≤ egV B z) :
    Nat.card (egM B z) ≤ (Nat.card B + Nat.card B) * 20160 := by
  have hMN := egM_le_normalizer hs hBL hb hcase
  let ρ : egM B z →* MulAut B := B.normalizerMonoidHom.comp (inclusion hMN)
  have hker : Nat.card ρ.ker ≤ Nat.card B + Nat.card B := by
    refine le_trans ?_ (card_egV_le hs hBL)
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : egM B z) : G), hΛ (mem_inf.2 ⟨(x : egM B z).2, ?_⟩)⟩) ?_
    · have h2 : inclusion hMN (x : egM B z) ∈ B.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact MonoidHom.mem_ker.1 x.2
      rw [normalizerMonoidHom_ker, mem_subgroupOf, coe_inclusion] at h2
      exact h2
    · intro x y hxy
      have h : ((x : egM B z) : G) = ((y : egM B z) : G) := by
        simpa using congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
  have hrange : Nat.card ρ.range ≤ 20160 := by
    have h20 : Nat.card (MulAut B) = 20160 :=
      M23Std.card_mulEquiv_eq_of_elemAb16 (F := B)
        (fun x y => Subtype.ext (hb.elem.1 x x.2 y y.2)) (fun x => Subtype.ext (hb.elem.2 x x.2))
        hb.card_B
    have : Finite (MulAut B) := Nat.finite_of_card_ne_zero (by rw [h20]; norm_num)
    rw [← h20]
    exact Nat.card_le_card_of_injective _ Subtype.coe_injective
  have := Subgroup.card_ker_mul_card_range ρ
  rw [← this]
  exact Nat.mul_le_mul hker hrange

theorem exists_phiB_ne_one (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) : ∃ t ∈ egLam B z, phiB z t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hΛ : egLam B z ≤ egV B z := fun t ht =>
    mem_egV_of_comm hs hBL hb ht ((phiB_eq_one_iff hs).1 (hcon t ht))
  have h1 := card_egM_ge hs hBL hb hcase
  have h2 := card_egM_le hs hBL hb hcase hΛ
  have h3 := hb.big_N
  rw [hb.card_B] at h1 h2
  omega

theorem exists_phiB_eq (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) {b : G} (hbB : b ∈ B) :
    ∃ t ∈ egLam B z, phiB z t = b := by
  by_cases hb1 : b = 1
  · exact ⟨1, one_mem _, by rw [hb1]; exact (phiB_eq_one_iff hs).2 (by group)⟩
  obtain ⟨t, ht, ht1⟩ := exists_phiB_ne_one hs hBL hb hcase
  obtain ⟨h, hh, hhb⟩ := hb.trans _ (phiB_mem hs hBL (mem_egLam.1 ht).1) b hbB ht1 hb1
  exact ⟨h * t * h⁻¹, conj_mem_egLam hs hBL hh ht, by rw [phiB_conj hs (mem_inf.1 hh).2, hhb]⟩

end CFSG.EvenSporadicStandard.M24Std.Octad
