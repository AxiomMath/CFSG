module

public import Certificates.Certificate133001
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.EvenSmallLie.OmegaEight

theorem exists_conj_mem_of_card {J : Type*} [Group J] [Finite J] {R : Subgroup J}
    (hR : Nat.card R = 3 ^ (Nat.card J).factorization 3) {a : J} (ha : a ^ 3 = 1) :
    ∃ g : J, g⁻¹ * a * g ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH : IsPGroup 3 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ha
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J (Sylow.ofCard R hR) P
  have haP : a ∈ (P : Subgroup J) := hP (Subgroup.mem_zpowers a)
  rw [← hg, Sylow.coe_subgroup_smul] at haP
  have h2 := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 haP
  refine ⟨g, ?_⟩
  have h3 : (MulAut.conj g)⁻¹ • a = g⁻¹ * a * g := by simp
  rw [h3] at h2
  exact h2

theorem exists_nonabelian_three_cent_of_outer
    {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT) (ha3 : a ^ 3 = 1)
    (hao : a ∉ omegaT) :
    ∃ E : Subgroup (Equiv.Perm (Fin 360)), E ≤ omegaT ∧ (∀ e ∈ E, a * e = e * a) ∧
      IsPGroup 3 E ∧ ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
  obtain ⟨Q, R, hQω, hRA, hQ243, hR729, hmain⟩ := triCheck_sound triData
    Certificates.certificate133001 omegaT autT (fun l hl => gen_mem_omegaT hl)
    (fun l hl => gen_mem_autT hl)
  have hcardA : Nat.card autT = 3 ^ 6 * 1433600 := by rw [card_autT]; norm_num
  have hfact : (Nat.card autT).factorization 3 = 6 := by
    rw [hcardA]
    exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 6 (by norm_num)
  have hR' : Nat.card (R.subgroupOf autT) = 3 ^ (Nat.card autT).factorization 3 := by
    rw [CFSG.RankThree.PartTwo.Sec4.Item434SporE81.card_subgroupOf_of_le hRA, hR729, hfact]
    norm_num
  have ha3' : (⟨a, ha⟩ : autT) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card hR' ha3'
  have hgR : (g : Equiv.Perm (Fin 360))⁻¹ * a * g ∈ R := by
    have := (Subgroup.mem_subgroupOf).1 hg
    simpa using this
  have hr3 : ((g : Equiv.Perm (Fin 360))⁻¹ * a * g) ^ 3 = 1 := by
    have := conj_pow (a := (g : Equiv.Perm (Fin 360))⁻¹) (b := a) (i := 3)
    simp only [inv_inv] at this
    rw [this, ha3]
    group
  rcases hmain _ hgR hr3 with hrQ | ⟨h, y, z, hh, hy, hz, hyz, hcy, hcz⟩
  · exfalso
    apply hao
    have hrω : (g : Equiv.Perm (Fin 360))⁻¹ * a * g ∈ omegaT := hQω hrQ
    have h1 := (conj_mem_omegaT (a := (g : Equiv.Perm (Fin 360))) g.2
      (g := (g : Equiv.Perm (Fin 360))⁻¹ * a * g)).1 hrω
    simpa [mul_assoc] using h1
  ·
    set k : Equiv.Perm (Fin 360) := h * (g : Equiv.Perm (Fin 360))⁻¹ with hk
    have hkA : k ∈ autT := autT.mul_mem hh (autT.inv_mem g.2)
    have hkc : k * a * k⁻¹ = h * ((g : Equiv.Perm (Fin 360))⁻¹ * a * g) * h⁻¹ := by
      rw [hk]
      group
    have hconj : ∀ w ∈ omegaT, k⁻¹ * w * k⁻¹⁻¹ ∈ omegaT := fun w hw =>
      (conj_mem_omegaT (a := k⁻¹) (autT.inv_mem hkA)).1 hw
    have hQω' : ∀ w ∈ Q, k⁻¹ * w * k⁻¹⁻¹ ∈ omegaT := fun w hw => hconj w (hQω hw)
    set y' := k⁻¹ * y * k⁻¹⁻¹ with hy'
    set z' := k⁻¹ * z * k⁻¹⁻¹ with hz'
    have hcomm : ∀ w : Equiv.Perm (Fin 360),
        h * ((g : Equiv.Perm (Fin 360))⁻¹ * a * g) * h⁻¹ * w =
          w * (h * ((g : Equiv.Perm (Fin 360))⁻¹ * a * g) * h⁻¹) →
        a * (k⁻¹ * w * k⁻¹⁻¹) = k⁻¹ * w * k⁻¹⁻¹ * a := by
      intro w hw
      rw [← hkc] at hw
      have : k⁻¹ * (k * a * k⁻¹ * w) * k⁻¹⁻¹ = k⁻¹ * (w * (k * a * k⁻¹)) * k⁻¹⁻¹ := by rw [hw]
      simpa [mul_assoc] using this
    have hay : a * y' = y' * a := hcomm y hcy
    have haz : a * z' = z' * a := hcomm z hcz
    set Q' : Subgroup (Equiv.Perm (Fin 360)) := Q.map (MulAut.conj k⁻¹).toMonoidHom with hQ'
    have hQ'card : Nat.card Q' = 3 ^ 5 := by
      rw [hQ', Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hQ243]
      norm_num
    have hQ'p : IsPGroup 3 Q' := IsPGroup.of_card hQ'card
    have hy'Q : y' ∈ Q' := ⟨y, hy, by simp [hy']⟩
    have hz'Q : z' ∈ Q' := ⟨z, hz, by simp [hz']⟩
    have hQ'ω : Q' ≤ omegaT := by
      rintro _ ⟨w, hw, rfl⟩
      simpa [MulAut.conj_apply] using hQω' w hw
    set E : Subgroup (Equiv.Perm (Fin 360)) := Subgroup.closure {y', z'} with hE
    have hEQ' : E ≤ Q' := by
      rw [hE, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hy'Q
      · exact hz'Q
    refine ⟨E, hEQ'.trans hQ'ω, ?_, hQ'p.to_le hEQ', y', Subgroup.subset_closure (by simp),
      z', Subgroup.subset_closure (by simp), ?_⟩
    · intro e he
      have hle : E ≤ Subgroup.centralizer {a} := by
        rw [hE, Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          exact hay.symm
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          exact haz.symm
      have := Subgroup.mem_centralizer_singleton_iff.1 (hle he)
      exact this.symm
    · intro hcomm'
      apply hyz
      have h1 : k⁻¹ * (y * z) * k⁻¹⁻¹ = k⁻¹ * (z * y) * k⁻¹⁻¹ := by
        have : y' * z' = z' * y' := hcomm'
        simpa [hy', hz', mul_assoc] using this
      have h2 := mul_left_cancel (mul_right_cancel h1)
      exact h2

end CFSG.HardMathSupport.Curtis.Coordinator
