module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

abbrev Y9 (h : Hyp59 H) : Subgroup H := centralizer ({h.a} : Set H) ⊓ coreActionKernel h.J

theorem P_le_Y9 (h : Hyp59 H) : h.P ≤ Y9 h := fun _ hx =>
  mem_inf.mpr ⟨(mem_inf.mp (h.S_le (mem_inf.mp hx).1)).1, (mem_inf.mp hx).2⟩

theorem centralizer_le_normalizer_J (H₁ : h.L81Hyp) :
    centralizer ({h.a} : Set H) ≤ normalizer (h.J : Set H) := by
  intro g hg
  have := H₁.J_normal
  rw [normal_subgroupOf_iff h.J_le] at this
  exact Eight2.mem_normalizer_of_conj_mem_fin fun x hx => this x g hx hg

theorem P_sylow_Y9 (H₁ : h.L81Hyp) :
    ∃ R : Sylow 2 ↥(Y9 h), (R : Subgroup _) = h.P.subgroupOf (Y9 h) := by
  have hJN := H₁.centralizer_le_normalizer_J
  have hMK : centralizer ({h.a} : Set H) ≤ normalizer ((Y9 h : Subgroup H) : Set H) :=
    fun g hg => mem_normalizer_inf (le_normalizer hg)
      (Eight2.mem_normalizer_of_conj_mem_fin fun x hx =>
        UnbalancedLayer.conj_mem_coreActionKernel (hJN hg) hx)
  obtain ⟨R, hR⟩ := exists_sylow_inf_of_le_normalizer (inf_le_left : Y9 h ≤ _) hMK
    (fun x hx => (mem_inf.mp (h.S_le hx)).1) H₁.S_sylow_C
  refine ⟨R, ?_⟩
  rw [hR]
  congr 1
  ext x
  simp only [mem_inf]
  constructor
  · rintro ⟨hxS, -, hxK⟩
    exact ⟨hxS, hxK⟩
  · rintro ⟨hxS, hxK⟩
    exact ⟨hxS, (mem_inf.mp (h.S_le hxS)).1, hxK⟩

namespace Data

variable {H₁ : h.L81Hyp} (d : Data H₁)

theorem hasNormalPComplement_kernel {v : H} (hst : d.Stage7 v) :
    HasNormalPComplement 2 ↥(Y9 h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPY := P_le_Y9 h
  have hbP : d.b ∈ h.P := (h.B_le (d.B_eq ▸ mem_zpowers d.b : d.b ∈ h.B))
  have hP2 : IsPGroup 2 h.P := h.isPGroup_S.to_le inf_le_left
  have hp4 : 4 ≤ orderOf d.p := by
    have h1 := d.card_P
    have h2 := H₁.eight_le
    omega
  have hbb : d.b * d.b = 1 := by
    rw [← pow_two, ← d.b_ord, pow_orderOf_eq_one]
  set p' : ↥(Y9 h) := ⟨d.p, hPY d.p_mem⟩ with hp'
  set b' : ↥(Y9 h) := ⟨d.b, hPY hbP⟩ with hb'
  have hop : orderOf p' = orderOf d.p := Subgroup.orderOf_mk _ _
  have D : Nine81.DihData (h.P.subgroupOf (Y9 h)) p' b' :=
    { hp := mem_subgroupOf.mpr d.p_mem
      hb := mem_subgroupOf.mpr hbP
      hcard := by
        rw [hop, Nat.card_congr (subgroupOfEquivOfLe hPY).toEquiv]
        exact d.card_P
      hbp := by
        intro hb
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb
        have hk' : d.p ^ k = d.b := by simpa [hp', hb'] using congrArg Subtype.val hk
        have h1 := hst.dihedral
        rw [← hk', show d.p ^ k * d.p * (d.p ^ k)⁻¹ = d.p by group] at h1
        have h2 : d.p ^ 2 = 1 := by
          calc d.p ^ 2 = d.p * d.p := pow_two _
            _ = d.p * d.p⁻¹ := by rw [← h1]
            _ = 1 := mul_inv_cancel _
        have := orderOf_le_of_pow_eq_one (by norm_num) h2
        omega
      hb2 := Subtype.ext hbb
      hrel := Subtype.ext hst.dihedral
      hp4 := by rw [hop]; exact hp4
      hpow := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨d.p, d.p_mem⟩
        exact ⟨n, by rw [hop, ← Subgroup.orderOf_mk d.p d.p_mem]; exact hn⟩ }
  refine Nine81.hasNormalPComplement_of_dihedral D (P_sylow_Y9 H₁) fun x => ?_
  have hpa : p' ^ (orderOf p' / 2) = ⟨h.a, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
      h.a_mem_coreActionKernel⟩⟩ := Subtype.ext (by rw [hop]; simpa [hp'] using d.p_a)
  rw [hpa]
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).1)

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
