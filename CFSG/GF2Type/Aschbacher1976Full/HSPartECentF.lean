module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartEBasis
public import CFSG.GF2Type.Aschbacher1976Full.HSEmbedFacts
public import CFSG.GF2Type.Aschbacher1976Full.WidthForm
public import CFSG.GF2Type.Aschbacher1976Full.WidthTI

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartE

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem cbit_eq_zero_iff (x t : G) : Width.cbit z x t = 0 ↔ t * x = x * t := by
  unfold Width.cbit
  split_ifs with h
  · simp only [true_iff]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  · simp only [one_ne_zero, false_iff]
    intro h'
    exact h (commutatorElement_eq_one_iff_mul_comm.mpr h'.symm)

theorem exists_comm_one_not_comm_two (hset : HSSetting G z) (hV : HSV z T V) {t₁ t₂ : G}
    (hb : IsBasis z V t₁ t₂) : ∃ x ∈ Fz z, t₁ * x = x * t₁ ∧ t₂ * x ≠ x * t₂ := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have hF := Embed.cdata_Fz hD hz
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hyF, hy2⟩ := exists_noncomm_F hset hV hb.mem₂ hb.not_mem₂
  have hy1 : t₁ * y ≠ y * t₁ := fun h => hy2 (hcon y hyF h)
  have ht₁F : t₁ ∈ Fz z := hV.le_F hb.mem₁
  have ht₂F : t₂ ∈ Fz z := hV.le_F hb.mem₂
  have hyA : Width.cbit z y t₁ = 1 := by
    rcases Width.zmod2_cases (Width.cbit z y t₁) with h | h
    · exact absurd ((cbit_eq_zero_iff y t₁).mp h) hy1
    · exact h
  have hyB : Width.cbit z y t₂ = 1 := by
    rcases Width.zmod2_cases (Width.cbit z y t₂) with h | h
    · exact absurd ((cbit_eq_zero_iff y t₂).mp h) hy2
    · exact h
  have key : ∀ x ∈ Fz z, Width.cbit z x t₁ = Width.cbit z x t₂ := by
    intro x hx
    have hxyA := Width.cbit_mul_left hF hx hyF ht₁F
    have hxyB := Width.cbit_mul_left hF hx hyF ht₂F
    rw [hyA] at hxyA
    rw [hyB] at hxyB
    rcases Width.zmod2_cases (Width.cbit z x t₁) with h1 | h1
    · have h2 : Width.cbit z x t₂ = 0 := (cbit_eq_zero_iff (z := z) x t₂).mpr
        (hcon x hx ((cbit_eq_zero_iff x t₁).mp h1))
      rw [h1, h2]
    · have h3 : Width.cbit z (x * y) t₁ = 0 := by rw [hxyA, h1]; decide
      have h4 := (cbit_eq_zero_iff (z := z) (x * y) t₂).mpr (hcon (x * y) ((Fz z).mul_mem hx hyF)
        ((cbit_eq_zero_iff (x * y) t₁).mp h3))
      rw [hxyB] at h4
      rcases Width.zmod2_cases (Width.cbit z x t₂) with h5 | h5
      · rw [h5] at h4
        exact absurd h4 (by decide)
      · rw [h1, h5]
  have hcomm : ∀ x ∈ Fz z, t₁ * t₂ * x = x * (t₁ * t₂) := by
    intro x hx
    have h1 := Width.cbit_mul_right hF hx ht₁F ht₂F
    rw [key x hx] at h1
    have h2 : Width.cbit z x (t₁ * t₂) = 0 := by
      rw [h1]
      rcases Width.zmod2_cases (Width.cbit z x t₂) with h | h <;> rw [h] <;> decide
    exact (cbit_eq_zero_iff x (t₁ * t₂)).mp h2
  obtain ⟨f, hfF, hf⟩ := exists_noncomm_F hset hV (V.mul_mem hb.mem₁ hb.mem₂) hb.not_mem₃
  exact hf (hcomm f hfF)

theorem card_inf_centralizer_le (hset : HSSetting G z) (hV : HSV z T V) :
    Nat.card ↥(Fz z ⊓ Subgroup.centralizer (V : Set G)) ≤ 16 := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have hFcard : Nat.card (Fz z) = 64 := (Width.card_Fz hD hz).trans (by norm_num)
  obtain ⟨t₁, t₂, hb⟩ := exists_basis hz hV
  obtain ⟨f₁, hf₁F, hf₁⟩ := exists_noncomm_F hset hV hb.mem₁ hb.not_mem₁
  obtain ⟨x, hxF, hx1, hx2⟩ := exists_comm_one_not_comm_two hset hV hb
  have e := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer ({t₂} : Set G))
    (Subgroup.centralizer ({t₁} : Set G)) (Fz z)
  have hr1 : (Subgroup.centralizer ({t₁} : Set G)).relIndex (Fz z) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    exact hf₁ (Subgroup.mem_centralizer_singleton_iff.mp (hle hf₁F)).symm
  have hr2 : (Subgroup.centralizer ({t₂} : Set G)).relIndex
      (Subgroup.centralizer ({t₁} : Set G) ⊓ Fz z) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    have hxm : x ∈ Subgroup.centralizer ({t₁} : Set G) ⊓ Fz z :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hx1.symm, hxF⟩
    exact hx2 (Subgroup.mem_centralizer_singleton_iff.mp (hle hxm)).symm
  have hr10 : (Subgroup.centralizer ({t₁} : Set G)).relIndex (Fz z) ≠ 0 :=
    ne_zero_of_dvd_ne_zero Nat.card_pos.ne' (Subgroup.relIndex_dvd_card _ _)
  have hr20 : (Subgroup.centralizer ({t₂} : Set G)).relIndex
      (Subgroup.centralizer ({t₁} : Set G) ⊓ Fz z) ≠ 0 :=
    ne_zero_of_dvd_ne_zero Nat.card_pos.ne' (Subgroup.relIndex_dvd_card _ _)
  have h4 : 4 ≤ (Subgroup.centralizer ({t₂} : Set G) ⊓
      Subgroup.centralizer ({t₁} : Set G)).relIndex (Fz z) := by
    rw [← e]
    have ha : 2 ≤ (Subgroup.centralizer ({t₂} : Set G)).relIndex
      (Subgroup.centralizer ({t₁} : Set G) ⊓ Fz z) := by omega
    have hb' : 2 ≤ (Subgroup.centralizer ({t₁} : Set G)).relIndex (Fz z) := by omega
    exact (Nat.mul_le_mul ha hb')
  have h5 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({t₂} : Set G) ⊓
      Subgroup.centralizer ({t₁} : Set G)) (Fz z)
  have hle : Fz z ⊓ Subgroup.centralizer (V : Set G) ≤
      (Subgroup.centralizer ({t₂} : Set G) ⊓ Subgroup.centralizer ({t₁} : Set G)) ⊓ Fz z := by
    intro y hy
    refine ⟨⟨?_, ?_⟩, hy.1⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hy.2) t₂ hb.mem₂).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hy.2) t₁ hb.mem₁).symm
  have h6 := Subgroup.card_le_of_le hle
  rw [hFcard] at h5
  nlinarith

theorem sixteen_le_card_sup {Z A : Subgroup G} (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hV : HSV z T V) : 16 ≤ Nat.card ↥(Z ⊔ V) := by
  obtain ⟨k, hkZ, -, -, hk2⟩ := Width.exists_gen_Z hD hz
  have hle : V ≤ Z ⊔ V := le_sup_right
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hne : V ≠ Z ⊔ V := by
    intro h
    have hkV : k ∈ V := h ▸ Subgroup.mem_sup_left hkZ
    have := hsAut_mul_self hV hkV
    rw [← pow_two, hk2] at this
    exact hz1 this
  have hm1 : m ≠ 1 := by
    intro h
    apply hne
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hm, h, mul_one]
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    exact Nat.card_pos.ne' hm
  rw [hm, hV.card_eq]
  omega

theorem inf_centralizer_eq_sup (hset : HSSetting G z) (hV : HSV z T V) {Z A : Subgroup G}
    (hD : Width.Z4Data z 2 Z A) :
    Fz z ⊓ Subgroup.centralizer (V : Set G) = Z ⊔ V := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hZF : Z ≤ Fz z := hD.sup_eq ▸ le_sup_left
  have hle : Z ⊔ V ≤ Fz z ⊓ Subgroup.centralizer (V : Set G) := by
    refine sup_le ?_ ?_
    · refine le_inf hZF fun c hc => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Width.Z_comm_F hD hc (hV.le_F hv)).symm
    · refine le_inf hV.le_F fun a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hsAut_mul_comm hV hv ha
  exact (Subgroup.eq_of_le_of_card_ge hle
    ((card_inf_centralizer_le hset hV).trans (sixteen_le_card_sup hD hz hV))).symm

end CFSG.GF2Type.Aschbacher1976Full.HS.PartE
