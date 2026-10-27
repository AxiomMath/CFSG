module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartEBasis
public import CFSG.GF2Type.Aschbacher1976Full.HSEmbedFacts
public import CFSG.GF2Type.Aschbacher1976Full.WidthForm

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.TransY

open CFSG CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {V : Subgroup G}

structure ElemV (z : G) (V : Subgroup G) : Prop where
  comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  sq : ∀ a ∈ V, a * a = 1
  card_eq : Nat.card V = 8
  le_F : V ≤ Fz z
  z_mem : z ∈ V

theorem ElemV.exists_not_mem_zpowers (hz : orderOf z = 2) (hV : ElemV z V) :
    ∃ v ∈ V, v ∉ Subgroup.zpowers z := by
  by_contra h
  have hle : V ≤ Subgroup.zpowers z := fun v hv => not_not.mp fun hn => h ⟨v, hv, hn⟩
  have := Subgroup.card_le_of_le hle
  rw [hV.card_eq, Nat.card_zpowers, hz] at this
  omega

theorem ElemV.exists_basis (hz : orderOf z = 2) (hV : ElemV z V) :
    ∃ t₁ t₂ : G, PartE.IsBasis z V t₁ t₂ := by
  classical
  obtain ⟨t₁, ht₁V, ht₁z⟩ := hV.exists_not_mem_zpowers hz
  obtain ⟨t₂, ht₂V, ht₂⟩ : ∃ t₂ ∈ V, t₂ ∉ (↑({1, z, t₁, z * t₁} : Finset G) : Set G) := by
    by_contra hcon
    push Not at hcon
    have hsub : (V : Set G) ⊆ (↑({1, z, t₁, z * t₁} : Finset G) : Set G) := hcon
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : (V : Set G).ncard = 8 := by
      rw [← Nat.card_coe_set_eq]
      exact hV.card_eq
    have h3 := Finset.card_le_four (a := (1 : G)) (b := z) (c := t₁) (d := z * t₁)
    omega
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] at ht₂
  obtain ⟨h2one, h2z, h2t, h2zt⟩ := ht₂
  have hsq : ∀ {a : G}, a ∈ V → a * a = 1 := fun ha => hV.sq _ ha
  refine ⟨t₁, t₂, ht₁V, ht₂V, ht₁z, ?_, ?_⟩
  · intro hmem
    rcases Width.mem_zpowers_involution hz hmem with h | h
    · exact h2one h
    · exact h2z h
  · intro hmem
    rcases Width.mem_zpowers_involution hz hmem with h | h
    · apply h2t
      have := hsq ht₁V
      calc t₂ = t₁ * (t₁ * t₂) := by rw [← mul_assoc, this, one_mul]
        _ = t₁ := by rw [h, mul_one]
    · apply h2zt
      have := hsq ht₁V
      calc t₂ = t₁ * (t₁ * t₂) := by rw [← mul_assoc, this, one_mul]
        _ = t₁ * z := by rw [h]
        _ = z * t₁ := hV.comm _ ht₁V _ hV.z_mem

theorem ElemV.exists_noncomm_F (hset : HSSetting G z) (hV : ElemV z V) {t : G} (htV : t ∈ V)
    (htz : t ∉ Subgroup.zpowers z) : ∃ f ∈ Fz z, t * f ≠ f * t := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have ht1 := (PartE.ne_one_ne_z_of_not_mem htz).1
  by_contra hcon
  push Not at hcon
  have htZ : t ∈ Z := Width.mem_Z_of_comm hD hz (hV.le_F htV) fun b hb =>
    hcon b (hD.sup_eq ▸ Subgroup.mem_sup_right hb)
  have htsq : t ^ 2 = 1 := by rw [pow_two]; exact hV.sq t htV
  exact htz (Width.involution_eq hD hz htZ htsq ht1 ▸ Subgroup.mem_zpowers z)

theorem cbit_eq_zero_iff (x t : G) : Width.cbit z x t = 0 ↔ t * x = x * t := by
  unfold Width.cbit
  split_ifs with h
  · simp only [true_iff]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  · simp only [one_ne_zero, false_iff]
    intro h'
    exact h (commutatorElement_eq_one_iff_mul_comm.mpr h'.symm)

theorem ElemV.exists_comm_one_not_comm_two (hset : HSSetting G z) (hV : ElemV z V) {t₁ t₂ : G}
    (hb : PartE.IsBasis z V t₁ t₂) : ∃ x ∈ Fz z, t₁ * x = x * t₁ ∧ t₂ * x ≠ x * t₂ := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have hF := Embed.cdata_Fz hD hz
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hyF, hy2⟩ := hV.exists_noncomm_F hset hb.mem₂ hb.not_mem₂
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
  obtain ⟨f, hfF, hf⟩ := hV.exists_noncomm_F hset (V.mul_mem hb.mem₁ hb.mem₂) hb.not_mem₃
  exact hf (hcomm f hfF)

theorem ElemV.card_inf_centralizer_le (hset : HSSetting G z) (hV : ElemV z V) :
    Nat.card ↥(Fz z ⊓ Subgroup.centralizer (V : Set G)) ≤ 16 := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have hFcard : Nat.card (Fz z) = 64 := (Width.card_Fz hD hz).trans (by norm_num)
  obtain ⟨t₁, t₂, hb⟩ := hV.exists_basis hz
  obtain ⟨f₁, hf₁F, hf₁⟩ := hV.exists_noncomm_F hset hb.mem₁ hb.not_mem₁
  obtain ⟨x, hxF, hx1, hx2⟩ := hV.exists_comm_one_not_comm_two hset hb
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

end CFSG.GF2Type.Aschbacher1976Full.HS.TransY
