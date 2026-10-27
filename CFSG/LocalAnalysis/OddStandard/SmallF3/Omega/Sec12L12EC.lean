module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

private theorem weight_two_even (w : Fin 5 → ZMod 2) (hw : vecWeight w = 2) : IsEvenVec w := by
  revert w
  unfold vecWeight IsEvenVec
  decide +kernel

private theorem isEvenVec_permVec_five :
    ∀ (σ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2), IsEvenVec v → IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec
  decide +kernel

private theorem exists_alt_permVec_add_weight_two (w : Fin 5 → ZMod 2) (hw : vecWeight w = 2) :
    ∃ σ ∈ alternatingGroup (Fin 5), ∃ u : Fin 5 → ZMod 2,
      IsEvenVec u ∧ permVec σ u + u = w := by
  revert w
  unfold vecWeight IsEvenVec permVec
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem weight_four_eq_sum_weight_two (w : Fin 5 → ZMod 2) (hw : vecWeight w = 4) :
    ∃ x y : Fin 5 → ZMod 2, vecWeight x = 2 ∧ vecWeight y = 2 ∧ w = x + y := by
  revert w
  unfold vecWeight
  decide +kernel

private theorem sec12E_f_inv (F : Sec12Frame t L S) {p : G} (hp : p ∈ secCMB t S L) :
    sec12f t p⁻¹ = (sec12f t p)⁻¹ := by
  have hp1 : p⁻¹ ∈ secCMB t S L := (secCMB t S L).inv_mem hp
  have h1 : sec12f t p * sec12f t p⁻¹ = 1 := by
    have hmul := sec12E_f_mul F hp hp1
    rw [mul_inv_cancel] at hmul
    simpa [sec12f] using hmul.symm
  exact eq_inv_of_mul_eq_one_right h1

private theorem sec12E_phi_weight_two_mem (F : Sec12Frame t L S) {φ : (Fin 5 → ZMod 2) → G}
    (hML : secM t S L ⊓ L = L ⊓ normalizer (secB S L : Set G))
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L)
      (L ⊓ normalizer (secB S L : Set G)) (alternatingGroup (Fin 5)))
    {w : Fin 5 → ZMod 2} (hw : vecWeight w = 2) :
    φ w ∈ ⁅secM t S L ⊓ L, secB S L⁆ := by
  obtain ⟨σ, hσ, u, hu, hσu⟩ := exists_alt_permVec_add_weight_two w hw
  obtain ⟨h, hhH, hh⟩ := hperm.2.2.2.2 σ hσ
  have hhML : h ∈ secM t S L ⊓ L := by rw [hML]; exact hhH
  have huB : φ u ∈ secB S L := (hperm.2.2.1 (φ u)).2 ⟨u, hu, rfl⟩
  have hcomm : ⁅h, φ u⁆ ∈ ⁅secM t S L ⊓ L, secB S L⁆ :=
    Subgroup.commutator_mem_commutator hhML huB
  have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h00 : φ 0 = φ 0 * φ 0 := by simpa using hperm.1 0 0 h0ev h0ev
  have hφ0 : φ 0 = 1 := mul_eq_left.mp h00.symm
  have huu : u + u = 0 := by
    funext i
    simpa using CharTwo.add_self_eq_zero (u i)
  have hu2 : φ u * φ u = 1 := by
    have h := hperm.1 u u hu hu
    rw [huu, hφ0] at h
    exact h.symm
  have hinv : (φ u)⁻¹ = φ u := inv_eq_of_mul_eq_one_right hu2
  have hσeven : IsEvenVec (permVec σ u) := isEvenVec_permVec_five σ u hu
  have hval : ⁅h, φ u⁆ = φ w := by
    rw [commutatorElement_def, hh u hu, hinv, ← hperm.1 (permVec σ u) u hσeven hu, hσu]
  rw [← hval]
  exact hcomm

theorem sec12E_A_le_X (F : Sec12Frame t L S) : secA t S L ≤ secXR t S L := by
  rw [secXR, le_inf_iff]
  refine ⟨sec12E_A_le_P F, ?_⟩
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (Subgroup.mem_centralizer_iff.mp (sec12E_R_le_C F hr) a ha).symm

theorem sec12E_X_normal (F : Sec12Frame t L S) {m x : G} (hm : m ∈ secM t S L)
    (hx : x ∈ secXR t S L) : m * x * m⁻¹ ∈ secXR t S L := by
  rw [secXR, Subgroup.mem_inf] at hx ⊢
  refine ⟨sec12E_P_normal F hm hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro r hr
  have hm' : m⁻¹ ∈ secM t S L := (secM t S L).inv_mem hm
  have hr' : m⁻¹ * r * m ∈ secR t := by
    simpa using sec12E_R_normal F hm' hr
  have hxr : (m⁻¹ * r * m) * x = x * (m⁻¹ * r * m) := hx.2 _ hr'
  calc r * (m * x * m⁻¹) = m * ((m⁻¹ * r * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * r * m)) * m⁻¹ := by rw [hxr]
    _ = (m * x * m⁻¹) * r := by group

theorem sec12E_comm_mem_X (F : Sec12Frame t L S) {y p : G} (hy : y ∈ secM t S L ⊓ L)
    (hp : p ∈ secCMB t S L) : y * p * y⁻¹ * p⁻¹ ∈ secXR t S L := by
  have hyM : y ∈ secM t S L := hy.1
  have hyL : y ∈ L := hy.2
  have hpM : p ∈ secM t S L := by
    have h : p ∈ secCMB t S L := hp
    rw [secCMB] at h
    exact (Subgroup.mem_inf.mp h).1
  rw [secXR, Subgroup.mem_inf]
  refine ⟨(secCMB t S L).mul_mem (sec12E_P_normal F hyM hp) ((secCMB t S L).inv_mem hp), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  set r1 : G := p⁻¹ * r * p with hr1def
  have hr1 : r1 = p⁻¹ * r * p := hr1def
  have hpMinv : p⁻¹ ∈ secM t S L := (secM t S L).inv_mem hpM
  have hr1mem : r1 ∈ secR t := by
    rw [hr1]
    simpa using sec12E_R_normal F hpMinv hr
  have hyr1 : y * r1 = r1 * y :=
    (Subgroup.mem_centralizer_iff.mp (F.rcent hr1mem)) y hyL
  have hyr : y * r = r * y := (Subgroup.mem_centralizer_iff.mp (F.rcent hr)) y hyL
  have hpr1 : p * r1 = r * p := by rw [hr1]; group
  have h1 : p⁻¹ * r = r1 * p⁻¹ := by rw [hr1]; group
  have h2 : y⁻¹ * r1 = r1 * y⁻¹ := by
    have hyr1c : Commute y r1 := hyr1
    exact hyr1c.inv_left
  calc r * (y * p * y⁻¹ * p⁻¹)
      = r * y * p * y⁻¹ * p⁻¹ := by group
    _ = y * r * p * y⁻¹ * p⁻¹ := by rw [hyr.symm]
    _ = y * (p * r1) * y⁻¹ * p⁻¹ := by rw [hpr1]; group
    _ = y * p * (r1 * y⁻¹) * p⁻¹ := by group
    _ = y * p * (y⁻¹ * r1) * p⁻¹ := by rw [h2]
    _ = y * p * y⁻¹ * (r1 * p⁻¹) := by group
    _ = y * p * y⁻¹ * (p⁻¹ * r) := by rw [h1]
    _ = (y * p * y⁻¹ * p⁻¹) * r := by group

theorem sec12E_B_le_comm (F : Sec12Frame t L S) :
    secB S L ≤ ⁅secM t S L ⊓ L, secB S L⁆ := by
  obtain ⟨-, -, -, -, hML, φ, hperm, -⟩ := F.bdata
  intro b hb
  obtain ⟨v, hv, rfl⟩ := (hperm.2.2.1 b).1 hb
  have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h00 : φ 0 = φ 0 * φ 0 := by simpa using hperm.1 0 0 h0ev h0ev
  have hφ0 : φ 0 = 1 := mul_eq_left.mp h00.symm
  rcases even_weight_cases_five v hv with h0 | h2 | h4
  · rw [h0, hφ0]
    exact Subgroup.one_mem _
  · exact sec12E_phi_weight_two_mem F hML hperm h2
  · obtain ⟨x, y, hx2, hy2, hw⟩ := weight_four_eq_sum_weight_two v h4
    have hxN : φ x ∈ ⁅secM t S L ⊓ L, secB S L⁆ :=
      sec12E_phi_weight_two_mem F hML hperm hx2
    have hyN : φ y ∈ ⁅secM t S L ⊓ L, secB S L⁆ :=
      sec12E_phi_weight_two_mem F hML hperm hy2
    have hxy : φ v = φ x * φ y := by
      rw [hw, hperm.1 x y (weight_two_even x hx2) (weight_two_even y hy2)]
    rw [hxy]
    exact Subgroup.mul_mem _ hxN hyN

theorem sec12E_f_surj_X (F : Sec12Frame t L S) {b : G} (hb : b ∈ secB S L) :
    ∃ x ∈ secXR t S L, sec12f t x = b := by
  let Φ : Subgroup G :=
    { carrier := {b : G | b ∈ secB S L ∧ ∃ x ∈ secXR t S L, sec12f t x = b}
      one_mem' := ⟨(secB S L).one_mem, 1, (secXR t S L).one_mem, by simp [sec12f]⟩
      mul_mem' := by
        rintro a b ⟨haB, x, hxX, hxa⟩ ⟨hbB, y, hyX, hyb⟩
        refine ⟨(secB S L).mul_mem haB hbB, x * y, (secXR t S L).mul_mem hxX hyX, ?_⟩
        rw [sec12E_f_mul F hxX.1 hyX.1, hxa, hyb]
      inv_mem' := by
        rintro a ⟨haB, x, hxX, hxa⟩
        refine ⟨(secB S L).inv_mem haB, x⁻¹, (secXR t S L).inv_mem hxX, ?_⟩
        rw [sec12E_f_inv F hxX.1, hxa] }
  have hcomm_le : ⁅secM t S L ⊓ L, secB S L⁆ ≤ Φ := by
    rw [Subgroup.commutator_le]
    intro y hy b hb
    obtain ⟨p, hpP, rfl⟩ := sec12E_f_surj F hb
    have hb0 : sec12f t p ∈ secB S L := sec12E_f_mem F hpP
    have hcommB : ⁅y, sec12f t p⁆ ∈ secB S L := by
      rw [commutatorElement_def]
      exact (secB S L).mul_mem (F.normB y hy.1 (sec12f t p) hb0) ((secB S L).inv_mem hb0)
    have hxmem : y * p * y⁻¹ * p⁻¹ ∈ secXR t S L := sec12E_comm_mem_X F hy hpP
    have hxP : y * p * y⁻¹ ∈ secCMB t S L := sec12E_P_normal F hy.1 hpP
    have hpinvP : p⁻¹ ∈ secCMB t S L := (secCMB t S L).inv_mem hpP
    have hyt : y * t = t * y := Subgroup.mem_centralizer_iff.mp F.htC y hy.2
    have hfinv : sec12f t p⁻¹ = (sec12f t p)⁻¹ := sec12E_f_inv F hpP
    have hval : sec12f t (y * p * y⁻¹ * p⁻¹) = ⁅y, sec12f t p⁆ := by
      rw [sec12E_f_mul F hxP hpinvP, sec12E_f_conj hyt p, hfinv, commutatorElement_def]
    exact ⟨hcommB, y * p * y⁻¹ * p⁻¹, hxmem, hval⟩
  have hbΦ : b ∈ Φ := hcomm_le (sec12E_B_le_comm F hb)
  exact hbΦ.2

theorem sec12E_P_eq_RX (F : Sec12Frame t L S) {p : G} (hp : p ∈ secCMB t S L) :
    ∃ r ∈ secR t, ∃ x ∈ secXR t S L, p = r * x := by
  obtain ⟨x, hxX, hx⟩ := sec12E_f_surj_X F (sec12E_f_mem F hp)
  have hxP : x ∈ secCMB t S L := hxX.1
  have hxinvP : x⁻¹ ∈ secCMB t S L := (secCMB t S L).inv_mem hxP
  have hpxinvP : p * x⁻¹ ∈ secCMB t S L := (secCMB t S L).mul_mem hp hxinvP
  have hfx : sec12f t (p * x⁻¹) = 1 := by
    rw [sec12E_f_mul F hp hxinvP, sec12E_f_inv F hxP, hx, mul_inv_cancel]
  have hc : p * x⁻¹ ∈ centralizer (secA t S L : Set G) := (sec12E_f_eq_one F hpxinvP).1 hfx
  obtain ⟨a, haA, r, hrR, har⟩ := sec12E_C_decomp F hc
  refine ⟨r, hrR, a * x, (secXR t S L).mul_mem ((sec12E_A_le_X F) haA) hxX, ?_⟩
  have hra : a * r = r * a :=
    Subgroup.mem_centralizer_iff.mp (sec12E_R_le_C F hrR) a haA
  calc p = (p * x⁻¹) * x := by group
    _ = (a * r) * x := by rw [har]
    _ = r * (a * x) := by rw [hra]; group

end CFSG.OddStandard.SmallF3.Omega
