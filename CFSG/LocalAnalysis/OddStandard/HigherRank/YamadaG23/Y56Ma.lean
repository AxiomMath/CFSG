module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Aut2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Sq

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y56_phi_one_aux {c : Ctx5 G L} : f3phi c.s 1 = 1 := by
  unfold f3phi
  group

private theorem y56_phi_inv_aux {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {y : G}
    (hy : y ∈ e4Y c.s) : f3phi c.s y⁻¹ = (f3phi c.s y)⁻¹ := by
  have hmul := y56_phi_mul hH y hy y⁻¹ ((e4Y c.s).inv_mem hy)
  have h : f3phi c.s y * f3phi c.s y⁻¹ = 1 := by
    rw [← hmul, mul_inv_cancel, y56_phi_one_aux]
  exact eq_inv_of_mul_eq_one_right h

theorem y56_M_normal {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : ∀ y ∈ e4Y c.s, ∀ m ∈ M, y * m * y⁻¹ ∈ M := by
  intro y hy m hm
  have hmY : m ∈ e4Y c.s := hM.2.1 hm
  have hcomm : ⁅y, m⁆ ∈ e4Q c.s := y56_Y_comm c hH y hy m hmY
  have heq : y * m * y⁻¹ = ⁅y, m⁆ * m := by rw [commutatorElement_def]; group
  rw [heq]
  exact M.mul_mem (hM.1 hcomm) hm

private theorem y56_M_le_normalizer {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : e4Y c.s ≤ Subgroup.normalizer (M : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact fun hm => y56_M_normal hH hM y hy m hm
  · intro hm
    have h := y56_M_normal hH hM y⁻¹ ((e4Y c.s).inv_mem hy) (y * m * y⁻¹) hm
    rwa [show y⁻¹ * (y * m * y⁻¹) * (y⁻¹)⁻¹ = m by group] at h

theorem y56_Y_decomp {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : ∀ y ∈ e4Y c.s, ∃ m ∈ M, ∃ x ∈ e4X0 c.s, y = m * x := by
  intro y hy
  have hMY : M ≤ e4Y c.s := hM.2.1
  have hX0Y : e4X0 c.s ≤ e4Y c.s := y56_X0_le_Y hH
  have hYnormM : e4Y c.s ≤ Subgroup.normalizer (M : Set G) := y56_M_le_normalizer hH hM
  have hYnormX0 : e4Y c.s ≤ Subgroup.normalizer (e4X0 c.s : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => y56_Y_norm_X0 hH y hy x hx
    · intro hx
      have h := y56_Y_norm_X0 hH y⁻¹ ((e4Y c.s).inv_mem hy) (y * x * y⁻¹) hx
      rwa [show y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x by group] at h
  haveI : ((e4X0 c.s).subgroupOf (e4Y c.s)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYnormX0
  have hsup : (M.subgroupOf (e4Y c.s)) ⊔ ((e4X0 c.s).subgroupOf (e4Y c.s)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMY hX0Y, hM.2.2.2.2.1, Subgroup.subgroupOf_self]
  obtain ⟨m, hm, x, hx, hmx⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := M.subgroupOf (e4Y c.s))
      (t := (e4X0 c.s).subgroupOf (e4Y c.s))
      (x := (⟨y, hy⟩ : ↥(e4Y c.s)))).mp (by rw [hsup]; exact trivial)
  exact ⟨(m : G), (Subgroup.mem_subgroupOf.mp hm), (x : G), (Subgroup.mem_subgroupOf.mp hx),
    (congrArg Subtype.val hmx).symm⟩

theorem y56_phi_M {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : ∀ f ∈ c.s.fr.E, ∃ m ∈ M, f3phi c.s m = f := by
  intro f hf
  obtain ⟨y, hy, hyφ⟩ := y56_phi_surj c hH f hf
  obtain ⟨m, hmM, x, hx, hy_eq⟩ := y56_Y_decomp hH hM y hy
  refine ⟨m, hmM, ?_⟩
  have hmY : m ∈ e4Y c.s := hM.2.1 hmM
  have hxY : x ∈ e4Y c.s := y56_X0_le_Y hH hx
  have hmul := y56_phi_mul hH m hmY x hxY
  have hx1 : f3phi c.s x = 1 := (y56_phi_eq_one hH x hxY).mpr hx
  have h : f3phi c.s y = f3phi c.s m := by rw [hy_eq, hmul, hx1, mul_one]
  rw [← h, hyφ]

theorem y56_M_inf_ker {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : ∀ m ∈ M, f3phi c.s m = 1 → m ∈ e4Q c.s := by
  intro m hmM hφ
  have hmY : m ∈ e4Y c.s := hM.2.1 hmM
  have hmX0 : m ∈ e4X0 c.s := (y56_phi_eq_one hH m hmY).mp hφ
  rw [← hM.2.2.2.1]
  exact ⟨hmM, hmX0⟩

private theorem y56_phi_commutator {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) {m : G} (hm : m ∈ M) {n : G}
    (hn : n ∈ normIn L c.s.fr.E) : f3phi c.s ⁅m, n⁆ = ⁅f3phi c.s m, n⁆ := by
  have hmY : m ∈ e4Y c.s := hM.2.1 hm
  have hnN : n ∈ e4N c.s := y56_NL_le_N hH hn
  have htY : n * m⁻¹ * n⁻¹ ∈ e4Y c.s :=
    y56_N_norm_Y hH n hnN m⁻¹ ((e4Y c.s).inv_mem hmY)
  have hsplit : ⁅m, n⁆ = m * (n * m⁻¹ * n⁻¹) := by rw [commutatorElement_def]; group
  have hmul := y56_phi_mul hH m hmY (n * m⁻¹ * n⁻¹) htY
  have hconj := y56_phi_conj hH n hnN m⁻¹
  have hinv : f3phi c.s m⁻¹ = (f3phi c.s m)⁻¹ := y56_phi_inv_aux hH hmY
  rw [hsplit, hmul, hconj, hinv, commutatorElement_def]
  group

theorem y56_M_comm_eq {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : ⁅M, normIn L c.s.fr.E⁆ ⊔ e4Q c.s = M := by
  set K' : Subgroup G := ⁅M, normIn L c.s.fr.E⁆ ⊔ e4Q c.s with hK'def
  have hMY : M ≤ e4Y c.s := hM.2.1
  have hKM : K' ≤ M := by
    rw [hK'def]
    refine sup_le ?_ hM.1
    rw [Subgroup.commutator_le]
    intro m hm n hn
    have hninv : n * m⁻¹ * n⁻¹ ∈ M := hM.2.2.1 n hn m⁻¹ (M.inv_mem hm)
    rw [show ⁅m, n⁆ = m * (n * m⁻¹ * n⁻¹) by rw [commutatorElement_def]; group]
    exact M.mul_mem hm hninv
  have hgen : ∀ f ∈ c.s.fr.E, ∃ k ∈ K', f3phi c.s k = f := by
    intro f hf
    rw [← y56_comm_E hH, Subgroup.commutator_def] at hf
    refine Subgroup.closure_induction (p := fun x _ => ∃ k ∈ K', f3phi c.s k = x)
      (mem := ?_) (one := ?_) (mul := ?_) (inv := ?_) hf
    · intro x hx
      obtain ⟨a, haF, b, hbN, rfl⟩ := hx
      obtain ⟨m, hmM, hmφ⟩ := y56_phi_M hH hM a haF
      refine ⟨⁅m, b⁆, ?_, ?_⟩
      · rw [hK'def]
        exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hmM hbN)
      · rw [y56_phi_commutator hH hM hmM hbN, hmφ]
    · refine ⟨1, K'.one_mem, ?_⟩
      exact y56_phi_one_aux
    · intro x y hx hy ihx ihy
      obtain ⟨k₁, hk₁, hk₁φ⟩ := ihx
      obtain ⟨k₂, hk₂, hk₂φ⟩ := ihy
      refine ⟨k₁ * k₂, K'.mul_mem hk₁ hk₂, ?_⟩
      rw [y56_phi_mul hH k₁ (hMY (hKM hk₁)) k₂ (hMY (hKM hk₂)), hk₁φ, hk₂φ]
    · intro x hx ihx
      obtain ⟨k, hk, hkφ⟩ := ihx
      refine ⟨k⁻¹, K'.inv_mem hk, ?_⟩
      rw [y56_phi_inv_aux hH (hMY (hKM hk)), hkφ]
  refine le_antisymm hKM ?_
  intro m hm
  have hmY : m ∈ e4Y c.s := hMY hm
  obtain ⟨k, hkK, hkφ⟩ := hgen (f3phi c.s m) (y56_phi_mem hH m hmY)
  have hkM : k ∈ M := hKM hkK
  have hkY : k ∈ e4Y c.s := hMY hkM
  have hkmM : k⁻¹ * m ∈ M := M.mul_mem (M.inv_mem hkM) hm
  have hphi1 : f3phi c.s (k⁻¹ * m) = 1 := by
    rw [y56_phi_mul hH k⁻¹ ((e4Y c.s).inv_mem hkY) m hmY,
      y56_phi_inv_aux hH hkY, hkφ, inv_mul_cancel]
  have hQmem : k⁻¹ * m ∈ e4Q c.s := y56_M_inf_ker hH hM (k⁻¹ * m) hkmM hphi1
  have hmK' : k * (k⁻¹ * m) ∈ K' :=
    K'.mul_mem hkK (by rw [hK'def]; exact Subgroup.mem_sup_right hQmem)
  rwa [show k * (k⁻¹ * m) = m by group] at hmK'

theorem y56_YN_le {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : ⁅e4Y c.s, e4N c.s⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro y hy n hn
  obtain ⟨n₁, hn₁, x, hx, rfl⟩ := y56_N_eq hH n hn
  have hxY : x ∈ e4Y c.s := y56_X0_le_Y hH hx
  have hQx : ⁅y, x⁆ ∈ e4Q c.s := y56_Y_comm c hH y hy x hxY
  have hterm : n₁ * ⁅y, x⁆ * n₁⁻¹ ∈ M := hM.2.2.1 n₁ hn₁ ⁅y, x⁆ (hM.1 hQx)
  have hcomm_yn₁ : ⁅y, n₁⁆ ∈ M := by
    obtain ⟨m, hmM, x', hx', hy_eq⟩ := y56_Y_decomp hH hM y hy
    have hm₁M : n₁ * m * n₁⁻¹ ∈ M := hM.2.2.1 n₁ hn₁ m hmM
    have hfM : ⁅n₁, x'⁆ ∈ M := hM.1 (Subgroup.mem_sup_left (y56_NL_X0 hH n₁ hn₁ x' hx'))
    have hfx : n₁ * x' * n₁⁻¹ = ⁅n₁, x'⁆ * x' := by rw [commutatorElement_def]; group
    have hny : n₁ * y * n₁⁻¹ = (n₁ * m * n₁⁻¹) * (⁅n₁, x'⁆ * x') := by
      rw [hy_eq]
      calc n₁ * (m * x') * n₁⁻¹ = (n₁ * m * n₁⁻¹) * (n₁ * x' * n₁⁻¹) := by group
        _ = (n₁ * m * n₁⁻¹) * (⁅n₁, x'⁆ * x') := by rw [hfx]
    have hcomm_ny : ⁅n₁, y⁆ ∈ M := by
      have heq : ⁅n₁, y⁆ = (n₁ * m * n₁⁻¹) * ⁅n₁, x'⁆ * m⁻¹ := by
        rw [commutatorElement_def, hny, hy_eq]; group
      rw [heq]
      exact M.mul_mem (M.mul_mem hm₁M hfM) (M.inv_mem hmM)
    have hinv := M.inv_mem hcomm_ny
    rwa [commutatorElement_inv] at hinv
  have hsplit : ⁅y, n₁ * x⁆ = ⁅y, n₁⁆ * (n₁ * ⁅y, x⁆ * n₁⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hsplit]
  exact M.mul_mem hcomm_yn₁ hterm

theorem y56_M_le_YN {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : M ≤ ⁅e4Y c.s, e4N c.s⁆ ⊔ e4Q c.s := by
  have h1 : ⁅M, normIn L c.s.fr.E⁆ ≤ ⁅e4Y c.s, e4N c.s⁆ :=
    Subgroup.commutator_mono hM.2.1 (y56_NL_le_N hH)
  rw [← y56_M_comm_eq hH hM]
  exact sup_le (h1.trans le_sup_left) le_sup_right

end CFSG.OddStandard.HigherRank.YamadaG23
