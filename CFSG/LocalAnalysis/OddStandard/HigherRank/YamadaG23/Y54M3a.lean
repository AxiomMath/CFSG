module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54MDef
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Sq
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5FrameB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y54_phi_one_aux {c : Ctx5 G L} : f3phi c.s 1 = 1 := by
  unfold f3phi
  group

private theorem y54_phi_inv_aux {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {y : G}
    (hy : y ∈ f4Y c.s) : f3phi c.s y⁻¹ = (f3phi c.s y)⁻¹ := by
  have hmul := y54_phi_mul hH y hy y⁻¹ ((f4Y c.s).inv_mem hy)
  have h : f3phi c.s y * f3phi c.s y⁻¹ = 1 := by
    rw [← hmul, mul_inv_cancel, y54_phi_one_aux]
  exact eq_inv_of_mul_eq_one_right h

theorem y54_N_eq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ f4N s, ∃ n₁ ∈ normIn L s.fr.F, ∃ x ∈ f4X0 s, n = n₁ * x := by
  intro n hn
  obtain ⟨hnH, hnN⟩ := Subgroup.mem_inf.mp hn
  obtain ⟨n₁, hn₁, hsurj⟩ :=
    y54_aut_surj hH ((s.fr.F).normalizerMonoidHom ⟨n, hnN⟩)
  refine ⟨n₁, hn₁, n₁⁻¹ * n, ?_, by group⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact s.H.mul_mem (s.H.inv_mem (s3_L_le_H s hH.hS (Subgroup.mem_inf.mp hn₁).1)) hnH
  · rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hαf : ((((s.fr.F).normalizerMonoidHom ⟨n, hnN⟩) ⟨f, hf⟩ : ↥s.fr.F) : G) =
        n * f * n⁻¹ := by
      simpa using Subgroup.normalizerMonoidHom_apply_apply_coe (H := s.fr.F) ⟨n, hnN⟩ ⟨f, hf⟩
    have hconj : (n₁⁻¹ * n) * f * (n₁⁻¹ * n)⁻¹ = f := by
      have h := hsurj ⟨f, hf⟩
      rw [hαf] at h
      calc (n₁⁻¹ * n) * f * (n₁⁻¹ * n)⁻¹ = n₁⁻¹ * (n * f * n⁻¹) * n₁ := by group
        _ = n₁⁻¹ * (n₁ * f * n₁⁻¹) * n₁ := by rw [h]
        _ = f := by group
    calc f * (n₁⁻¹ * n) = ((n₁⁻¹ * n) * f * (n₁⁻¹ * n)⁻¹) * (n₁⁻¹ * n) := by rw [hconj]
      _ = (n₁⁻¹ * n) * f := by group

theorem y54_comm_F {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ⁅s.fr.F, normIn L s.fr.F⁆ = s.fr.F := by
  set K : Subgroup G := ⁅s.fr.F, normIn L s.fr.F⁆ with hKdef
  have hKF : K ≤ s.fr.F := by
    rw [hKdef, Subgroup.commutator_le]
    intro f hf b hb
    have hbN : b ∈ Subgroup.normalizer (s.fr.F : Set G) := (Subgroup.mem_inf.mp hb).2
    have hbf : b * f⁻¹ * b⁻¹ ∈ s.fr.F :=
      (Subgroup.mem_normalizer_iff.mp hbN f⁻¹).mp (s.fr.F.inv_mem hf)
    rw [show ⁅f, b⁆ = f * (b * f⁻¹ * b⁻¹) by rw [commutatorElement_def]; group]
    exact s.fr.F.mul_mem hf hbf
  have hKinv : ∀ b ∈ normIn L s.fr.F, ∀ k ∈ K, b * k * b⁻¹ ∈ K := by
    intro b hb k hk
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := by
      rw [hKdef]
      exact Subgroup.normalizer_commutator_ge_right (H₁ := s.fr.F)
        (H₂ := normIn L s.fr.F) hb
    exact (Subgroup.mem_normalizer_iff.mp hbN k).mp hk
  have hne : K ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hwV, hzV, hw1, hz1, hwz, _, _, _, _⟩ := f3_V_elems hH
    have hwF : w ∈ s.fr.F := y5_V_le_F hH hwV
    have hzF : s.fr.z ∈ s.fr.F := y5_V_le_F hH hzV
    have hbot' : ⁅s.fr.F, normIn L s.fr.F⁆ = ⊥ := by rw [← hKdef]; exact hbot
    have hcen : s.fr.F ≤ Subgroup.centralizer (normIn L s.fr.F : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot'
    obtain ⟨b, hb, hbz⟩ := y54_trans1 hH s.fr.z hzF w hwF hz1 hw1
    have hcomm : b * s.fr.z = s.fr.z * b :=
      Subgroup.mem_centralizer_iff.mp (hcen hzF) b hb
    have hfix : b * s.fr.z * b⁻¹ = s.fr.z := by rw [hcomm]; group
    rw [hfix] at hbz
    exact hwz hbz.symm
  apply le_antisymm hKF
  intro f hf
  by_cases hf1 : f = 1
  · rw [hf1]; exact K.one_mem
  · have hnt : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
    obtain ⟨a, haK, ha1⟩ := (Subgroup.nontrivial_iff_exists_ne_one K).mp hnt
    obtain ⟨b, hb, hba⟩ := y54_trans1 hH a (hKF haK) f hf ha1 hf1
    rw [← hba]
    exact hKinv b hb a haK

theorem y54_M_normal {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : ∀ y ∈ f4Y c.s, ∀ m ∈ M, y * m * y⁻¹ ∈ M := by
  intro y hy m hm
  have hmY : m ∈ f4Y c.s := hM.2.1 hm
  have hcomm : ⁅y, m⁆ ∈ c.s.fr.F := y54_Y_comm c hH y hy m hmY
  have heq : y * m * y⁻¹ = ⁅y, m⁆ * m := by rw [commutatorElement_def]; group
  rw [heq]
  exact M.mul_mem (hM.1 hcomm) hm

private theorem y54_M_le_normalizer {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : f4Y c.s ≤ Subgroup.normalizer (M : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact fun hm => y54_M_normal hH hM y hy m hm
  · intro hm
    have h := y54_M_normal hH hM y⁻¹ ((f4Y c.s).inv_mem hy) (y * m * y⁻¹) hm
    rwa [show y⁻¹ * (y * m * y⁻¹) * (y⁻¹)⁻¹ = m by group] at h

theorem y54_Y_decomp {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : ∀ y ∈ f4Y c.s, ∃ m ∈ M, ∃ x ∈ f4X0 c.s, y = m * x := by
  intro y hy
  have hMY : M ≤ f4Y c.s := hM.2.1
  have hX0Y : f4X0 c.s ≤ f4Y c.s := y54_X0_le_Y hH
  have hYnormM : f4Y c.s ≤ Subgroup.normalizer (M : Set G) := y54_M_le_normalizer hH hM
  have hYnormX0 : f4Y c.s ≤ Subgroup.normalizer (f4X0 c.s : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => y54_Y_norm_X0 hH y hy x hx
    · intro hx
      have h := y54_Y_norm_X0 hH y⁻¹ ((f4Y c.s).inv_mem hy) (y * x * y⁻¹) hx
      rwa [show y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x by group] at h
  haveI : ((f4X0 c.s).subgroupOf (f4Y c.s)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYnormX0
  have hsup : (M.subgroupOf (f4Y c.s)) ⊔ ((f4X0 c.s).subgroupOf (f4Y c.s)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMY hX0Y, hM.2.2.2.2, Subgroup.subgroupOf_self]
  obtain ⟨m, hm, x, hx, hmx⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := M.subgroupOf (f4Y c.s))
      (t := (f4X0 c.s).subgroupOf (f4Y c.s))
      (x := (⟨y, hy⟩ : ↥(f4Y c.s)))).mp (by rw [hsup]; exact trivial)
  exact ⟨(m : G), (Subgroup.mem_subgroupOf.mp hm), (x : G), (Subgroup.mem_subgroupOf.mp hx),
    (congrArg Subtype.val hmx).symm⟩

theorem y54_phi_M {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : ∀ f ∈ c.s.fr.F, ∃ m ∈ M, f3phi c.s m = f := by
  intro f hf
  obtain ⟨y, hy, hyφ⟩ := y54_phi_surj hH f hf
  obtain ⟨m, hmM, x, hx, hy_eq⟩ := y54_Y_decomp hH hM y hy
  refine ⟨m, hmM, ?_⟩
  have hmY : m ∈ f4Y c.s := hM.2.1 hmM
  have hxY : x ∈ f4Y c.s := y54_X0_le_Y hH hx
  have hmul := y54_phi_mul hH m hmY x hxY
  have hx1 : f3phi c.s x = 1 := (y54_phi_eq_one hH x hxY).mpr hx
  have h : f3phi c.s y = f3phi c.s m := by rw [hy_eq, hmul, hx1, mul_one]
  rw [← h, hyφ]

theorem y54_M_inf_ker {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : ∀ m ∈ M, f3phi c.s m = 1 → m ∈ c.s.fr.F := by
  intro m hmM hφ
  have hmY : m ∈ f4Y c.s := hM.2.1 hmM
  have hmX0 : m ∈ f4X0 c.s := (y54_phi_eq_one hH m hmY).mp hφ
  rw [← hM.2.2.2.1]
  exact ⟨hmM, hmX0⟩

private theorem y54_phi_commutator {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) {m : G} (hm : m ∈ M) {n : G}
    (hn : n ∈ normIn L c.s.fr.F) : f3phi c.s ⁅m, n⁆ = ⁅f3phi c.s m, n⁆ := by
  have hmY : m ∈ f4Y c.s := hM.2.1 hm
  have hnN : n ∈ f4N c.s := y54_NL_le_N hH hn
  have htY : n * m⁻¹ * n⁻¹ ∈ f4Y c.s :=
    y54_N_norm_Y hH n hnN m⁻¹ ((f4Y c.s).inv_mem hmY)
  have hsplit : ⁅m, n⁆ = m * (n * m⁻¹ * n⁻¹) := by rw [commutatorElement_def]; group
  have hmul := y54_phi_mul hH m hmY (n * m⁻¹ * n⁻¹) htY
  have hconj := y54_phi_conj hH n hnN m⁻¹
  have hinv : f3phi c.s m⁻¹ = (f3phi c.s m)⁻¹ := y54_phi_inv_aux hH hmY
  rw [hsplit, hmul, hconj, hinv, commutatorElement_def]
  group

theorem y54_M_comm_eq {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : ⁅M, normIn L c.s.fr.F⁆ ⊔ c.s.fr.F = M := by
  set K' : Subgroup G := ⁅M, normIn L c.s.fr.F⁆ ⊔ c.s.fr.F with hK'def
  have hMY : M ≤ f4Y c.s := hM.2.1
  have hKM : K' ≤ M := by
    rw [hK'def]
    refine sup_le ?_ hM.1
    rw [Subgroup.commutator_le]
    intro m hm n hn
    have hninv : n * m⁻¹ * n⁻¹ ∈ M := hM.2.2.1 n hn m⁻¹ (M.inv_mem hm)
    rw [show ⁅m, n⁆ = m * (n * m⁻¹ * n⁻¹) by rw [commutatorElement_def]; group]
    exact M.mul_mem hm hninv
  have hgen : ∀ f ∈ c.s.fr.F, ∃ k ∈ K', f3phi c.s k = f := by
    intro f hf
    rw [← y54_comm_F hH, Subgroup.commutator_def] at hf
    refine Subgroup.closure_induction (p := fun x _ => ∃ k ∈ K', f3phi c.s k = x)
      (mem := ?_) (one := ?_) (mul := ?_) (inv := ?_) hf
    · intro x hx
      obtain ⟨a, haF, b, hbN, rfl⟩ := hx
      obtain ⟨m, hmM, hmφ⟩ := y54_phi_M hH hM a haF
      refine ⟨⁅m, b⁆, ?_, ?_⟩
      · rw [hK'def]
        exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hmM hbN)
      · rw [y54_phi_commutator hH hM hmM hbN, hmφ]
    · refine ⟨1, K'.one_mem, ?_⟩
      exact y54_phi_one_aux
    · intro x y hx hy ihx ihy
      obtain ⟨k₁, hk₁, hk₁φ⟩ := ihx
      obtain ⟨k₂, hk₂, hk₂φ⟩ := ihy
      refine ⟨k₁ * k₂, K'.mul_mem hk₁ hk₂, ?_⟩
      rw [y54_phi_mul hH k₁ (hMY (hKM hk₁)) k₂ (hMY (hKM hk₂)), hk₁φ, hk₂φ]
    · intro x hx ihx
      obtain ⟨k, hk, hkφ⟩ := ihx
      refine ⟨k⁻¹, K'.inv_mem hk, ?_⟩
      rw [y54_phi_inv_aux hH (hMY (hKM hk)), hkφ]
  refine le_antisymm hKM ?_
  intro m hm
  have hmY : m ∈ f4Y c.s := hMY hm
  obtain ⟨k, hkK, hkφ⟩ := hgen (f3phi c.s m) (y54_phi_mem hH m hmY)
  have hkM : k ∈ M := hKM hkK
  have hkY : k ∈ f4Y c.s := hMY hkM
  have hkmM : k⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hkM) hm
  have hphi1 : f3phi c.s (k⁻¹ * m) = 1 := by
    rw [y54_phi_mul hH k⁻¹ ((f4Y c.s).inv_mem hkY) m hmY,
      y54_phi_inv_aux hH hkY, hkφ, inv_mul_cancel]
  have hFmem : k⁻¹ * m ∈ c.s.fr.F := y54_M_inf_ker hH hM (k⁻¹ * m) hkmM hphi1
  have hmK' : k * (k⁻¹ * m) ∈ K' :=
    K'.mul_mem hkK (by rw [hK'def]; exact Subgroup.mem_sup_right hFmem)
  rwa [show k * (k⁻¹ * m) = m by group] at hmK'

theorem y54_YN_le {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : ⁅f4Y c.s, f4N c.s⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro y hy n hn
  obtain ⟨n₁, hn₁, x, hx, rfl⟩ := y54_N_eq hH n hn
  have hxY : x ∈ f4Y c.s := y54_X0_le_Y hH hx
  have hcomm_yx : ⁅y, x⁆ ∈ c.s.fr.F := y54_Y_comm c hH y hy x hxY
  have hcomm_yn₁ : ⁅y, n₁⁆ ∈ M := by
    obtain ⟨m, hmM, x', hx', hy_eq⟩ := y54_Y_decomp hH hM y hy
    have hm₁M : n₁ * m * n₁⁻¹ ∈ M := hM.2.2.1 n₁ hn₁ m hmM
    have hfF : ⁅n₁, x'⁆ ∈ c.s.fr.F := y54_NL_X0 hH n₁ hn₁ x' hx'
    have hfx : n₁ * x' * n₁⁻¹ = ⁅n₁, x'⁆ * x' := by rw [commutatorElement_def]; group
    have hny : n₁ * y * n₁⁻¹ = (n₁ * m * n₁⁻¹) * (⁅n₁, x'⁆ * x') := by
      rw [hy_eq]
      calc n₁ * (m * x') * n₁⁻¹ = (n₁ * m * n₁⁻¹) * (n₁ * x' * n₁⁻¹) := by group
        _ = (n₁ * m * n₁⁻¹) * (⁅n₁, x'⁆ * x') := by rw [hfx]
    have hcomm_ny : ⁅n₁, y⁆ ∈ M := by
      have heq : ⁅n₁, y⁆ = (n₁ * m * n₁⁻¹) * ⁅n₁, x'⁆ * m⁻¹ := by
        rw [commutatorElement_def, hny, hy_eq]; group
      rw [heq]
      exact M.mul_mem (M.mul_mem hm₁M (hM.1 hfF)) (M.inv_mem hmM)
    have hinv := M.inv_mem hcomm_ny
    rwa [commutatorElement_inv] at hinv
  have hn₁F : n₁ * ⁅y, x⁆ * n₁⁻¹ ∈ c.s.fr.F :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hn₁).2 ⁅y, x⁆).mp hcomm_yx
  have hsplit : ⁅y, n₁ * x⁆ = ⁅y, n₁⁆ * (n₁ * ⁅y, x⁆ * n₁⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hsplit]
  exact M.mul_mem hcomm_yn₁ (hM.1 hn₁F)

theorem y54_M_le_YN {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : M ≤ ⁅f4Y c.s, f4N c.s⁆ ⊔ c.s.fr.F := by
  have h1 : ⁅M, normIn L c.s.fr.F⁆ ≤ ⁅f4Y c.s, f4N c.s⁆ :=
    Subgroup.commutator_mono hM.2.1 (y54_NL_le_N hH)
  rw [← y54_M_comm_eq hH hM]
  exact sup_le (h1.trans le_sup_left) le_sup_right

end CFSG.OddStandard.HigherRank.YamadaG23
