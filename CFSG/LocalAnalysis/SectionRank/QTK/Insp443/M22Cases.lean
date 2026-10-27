module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.Quasithin.Vol2.KGFactC31M22

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M22

theorem KConfig.m22_cases
    {L V MK : Subgroup G₀} (h : KConfig G₀ L V MK) :
    ∃ g : G₀,
      (V = (eSub basis_hex).map (MulAut.conj g).toMonoidHom ∧
        L = Mhex.map (MulAut.conj g).toMonoidHom) ∨
      (V = (eSub basis_duad).map (MulAut.conj g).toMonoidHom ∧
        L = Mduad.map (MulAut.conj g).toMonoidHom) ∨
      (V = (eSub basis_e8).map (MulAut.conj g).toMonoidHom ∧
        L = (eNorm basis_e8).map (MulAut.conj g).toMonoidHom) := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := h.elemAbelian.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := fun j => by
    have hm : y ^ j * t * y⁻¹ ^ j ∈ V := by
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) j) t).mp ht
    have := h.elemAbelian.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    simpa using congrArg Subtype.val this
  have hpd : p ∣ 443520 := by
    by_contra hpd
    have h1 : y = 1 := eq_one_of_pow_of_not_dvd hp
      (by rwa [CFSG.Sporadic.Mathieu.card_M22]) ⟨k, hyk⟩
    apply hyt
    rw [h1, one_mul, inv_one, mul_one]
  have key : ∀ (x : G₀), orderOf x = p → ¬ p ∣ 443520 / p → ∃ (g y₁ t₁ : G₀),
      y₁ ∈ Subgroup.zpowers x ∧ y₁ * t₁ * y₁⁻¹ ≠ t₁ ∧ orderOf t₁ = 2 ∧
        (∀ j : ℕ, t₁ * (y₁ ^ j * t₁ * y₁⁻¹ ^ j) = y₁ ^ j * t₁ * y₁⁻¹ ^ j * t₁) ∧
        orbSub y t = (orbSub y₁ t₁).map (MulAut.conj g).toMonoidHom := by
    intro x hx hpi
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hP, hPi⟩ := sylow_of_order hx hpi
    obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi ⟨k, hyk⟩
    let f : G₀ →* G₀ := (MulAut.conj g).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj g).injective
    have hconj : ∀ z : G₀, f (g⁻¹ * z * g) = z := fun z => by
      change (MulAut.conj g).toMonoidHom (g⁻¹ * z * g) = z
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hfy : f (g⁻¹ * y * g) = y := hconj y
    have hft : f (g⁻¹ * t * g) = t := hconj t
    generalize g⁻¹ * y * g = y₁ at hg hfy
    generalize g⁻¹ * t * g = t₁ at hft
    refine ⟨g, y₁, t₁, hg, fun h => hyt ?_, ?_, fun j => hf ?_, ?_⟩
    · have := congrArg f h
      rwa [map_mul, map_mul, map_inv, hfy, hft] at this
    · rw [← ht2, ← hft, orderOf_injective f hf]
    · simp only [map_mul, map_pow, map_inv, hfy, hft]
      exact hcommA j
    · rw [orbSub_map, hfy, hft]
  rcases prime_dvd_m22 hp hp5 hpd with rfl | rfl | rfl
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x5 orderOf_x5 (by norm_num)
    rcases orbSub_cases5 hg hord hmv (fun j _ => hcm j) with hcase | hcase | hcase
    · rw [hcase] at hU
      have hd : RefData ((eSub basis_duad).map (MulAut.conj g).toMonoidHom)
          (Mduad.map (MulAut.conj g).toMonoidHom) :=
        RefData.map_mulEquiv refData_duad (MulAut.conj g)
      obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
      exact ⟨g, Or.inr (Or.inl ⟨hV, hL⟩)⟩
    · rw [hcase] at hU
      have hd : RefData ((eSub basis_hex).map (MulAut.conj g).toMonoidHom)
          (Mhex.map (MulAut.conj g).toMonoidHom) :=
        RefData.map_mulEquiv refData_hex (MulAut.conj g)
      obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
      exact ⟨g, Or.inl ⟨hV, hL⟩⟩
    · rw [hcase, Subgroup.map_map] at hU
      have hcomp : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj cHex).toMonoidHom) =
          (MulAut.conj (g * cHex)).toMonoidHom := by
        ext z
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hcomp] at hU
      have hd : RefData ((eSub basis_hex).map (MulAut.conj (g * cHex)).toMonoidHom)
          (Mhex.map (MulAut.conj (g * cHex)).toMonoidHom) :=
        RefData.map_mulEquiv refData_hex (MulAut.conj (g * cHex))
      obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
      exact ⟨g * cHex, Or.inl ⟨hV, hL⟩⟩
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x7 orderOf_x7 (by norm_num)
    rw [orbSub_cases7 hg hord hmv (fun j _ => hcm j)] at hU
    have hd : RefData ((eSub basis_e8).map (MulAut.conj g).toMonoidHom)
        ((eNorm basis_e8).map (MulAut.conj g).toMonoidHom) :=
      RefData.map_mulEquiv refData_e8 (MulAut.conj g)
    obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
    exact ⟨g, Or.inr (Or.inr ⟨hV, hL⟩)⟩
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, -⟩ := key x11 orderOf_x11 (by norm_num)
    exact (not_bad11 hg hord hmv fun j _ => hcm j).elim

end CFSG.SectionRank.QTK.Insp443

end
