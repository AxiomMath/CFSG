module

public import CFSG.ClassicalInvolution.Q3.Q3T6BExact
public import CFSG.ClassicalInvolution.Q3.Q3T6BFixSub

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem Mem3.eq_one_or_eq_of_central {X : Subgroup F} {x : F} (hX : Mem3 X x) (hex : ExAt x)
    {a : F} (haX : a ∈ X) (hc : ∀ b ∈ X, a * b = b * a) : a = 1 ∨ a = x := by
  have hO : oddCoreOf X = ⊥ := Mem3.oddCoreOf_eq_bot hX hex
  have hc' : ∀ u ∈ X, ⁅a, u⁆ ∈ oddCoreOf X := fun u hu => by
    rw [hO, Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc u hu)
  rcases (hX.mem_center_oddQuot_iff _).mp (mk_mem_center_of_forall haX hc') with h1 | h1
  · left
    rw [QuotientGroup.eq_one_iff] at h1
    have : a ∈ oddCoreOf X := mem_oddCoreOf_iff.mpr ⟨haX, h1⟩
    rw [hO, Subgroup.mem_bot] at this
    exact this
  · right
    rw [QuotientGroup.eq] at h1
    have hmem : a⁻¹ * x ∈ oddCoreOf X :=
      mem_oddCoreOf_iff.mpr ⟨X.mul_mem (X.inv_mem haX) hX.mem, h1⟩
    rw [hO, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hmem

@[expose] def diagHom (Q : Subgroup F) (u : F) (hc : ∀ a ∈ Q, ∀ b ∈ conjSub u Q, a * b = b * a) :
    ↥Q →* F where
  toFun a := diag u (a : F)
  map_one' := by simp [diag]
  map_mul' a b := diag_mul_of_comm hc a.2 b.2

@[expose] def diagGroupOf {X : Subgroup F} {x y : F} (hs : Swap X x y) (hex : ExAt x) :
    Subgroup F :=
  (diagHom X y (hs.comm_twin hex)).range

section Diag

variable {X : Subgroup F} {x y : F} (hs : Swap X x y) (hex : ExAt x)

include hs hex

theorem mem_diagGroupOf_iff {c : F} : c ∈ diagGroupOf hs hex ↔ ∃ q ∈ X, c = diag y q := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩

theorem diag_mem_diagGroupOf {q : F} (hq : q ∈ X) : diag y q ∈ diagGroupOf hs hex :=
  (mem_diagGroupOf_iff hs hex).mpr ⟨q, hq, rfl⟩

theorem diag_mul_of_mem {a b : F} (ha : a ∈ X) (hb : b ∈ X) :
    diag y (a * b) = diag y a * diag y b :=
  diag_mul_of_comm (hs.comm_twin hex) ha hb

theorem diag_conj_of_mem {a b : F} (ha : a ∈ X) (hb : b ∈ X) :
    diag y (a * b * a⁻¹) = diag y a * diag y b * (diag y a)⁻¹ := by
  have h1 : diag y (a * b * a⁻¹) * diag y a = diag y a * diag y b := by
    rw [← diag_mul_of_mem hs hex (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) ha,
      ← diag_mul_of_mem hs hex ha hb]
    congr 1
    group
  calc diag y (a * b * a⁻¹) = (diag y a * diag y b) * (diag y a)⁻¹ := by
        rw [← h1]
        group
    _ = diag y a * diag y b * (diag y a)⁻¹ := rfl

theorem diag_comm_xy {q : F} (hq : q ∈ X) :
    diag y q * x = x * diag y q ∧ diag y q * y = y * diag y q :=
  diag_comm_both hs hex hq

theorem diagGroupOf_comm_x {k : F} (hk : k ∈ diagGroupOf hs hex) : k * x = x * k := by
  obtain ⟨q, hq, rfl⟩ := (mem_diagGroupOf_iff hs hex).mp hk
  exact (diag_comm_xy hs hex hq).1

theorem diagGroupOf_comm_y {k : F} (hk : k ∈ diagGroupOf hs hex) : k * y = y * k := by
  obtain ⟨q, hq, rfl⟩ := (mem_diagGroupOf_iff hs hex).mp hk
  exact (diag_comm_xy hs hex hq).2

theorem diagGroupOf_le_closure_odd :
    diagGroupOf hs hex ≤ Subgroup.closure {g : F | g ∈ diagGroupOf hs hex ∧ Odd (orderOf g)} := by
  intro k hk
  obtain ⟨q, hq, rfl⟩ := (mem_diagGroupOf_iff hs hex).mp hk
  have h1 := diag_mem_closure_odd hs hex hq
  refine (Subgroup.closure_mono ?_) h1
  rintro d ⟨s, hsX, p, k, hp, hp2, hsp, rfl⟩
  exact ⟨diag_mem_diagGroupOf hs hex hsX, odd_orderOf_diag (hs.comm_twin hex) hsX hp hp2 hsp⟩

theorem diag_eq_one {a : F} (ha : a ∈ X) (h : diag y a = 1) : a = 1 ∨ a = x := by
  have hc := hs.comm_twin hex
  have h1 : y * a * y⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_right h
  have h2 : a⁻¹ ∈ conjSub y X := by
    rw [← h1]
    exact conj_mem_conjSub ha
  rcases Mem3.eq_one_or_eq_of_central hs.member hex (X.inv_mem ha)
      (fun b hb => (hc b hb _ h2).symm) with h3 | h3
  · left
    exact inv_eq_one.mp h3
  · right
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hs.member.mul_self
    have := congrArg (fun t => t⁻¹) h3
    simpa [hxi] using this

theorem fixed_decomp {d : F} (hd : d ∈ X ⊔ conjSub y X) (hdy : d * y = y * d) :
    ∃ c ∈ X, d = diag y c ∨ d = diag y c * x := by
  have hc := hs.comm_twin hex
  have hne : X ≠ conjSub y X := fun h => hs.moves h.symm
  have hXN : X ≤ Subgroup.normalizer (conjSub y X : Set F) :=
    (hs.member.twin_facts hs.twin hne).2.1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X (conjSub y X) hXN] at hd
  obtain ⟨a, ha, b, hb, rfl⟩ := hd
  have hyi : y⁻¹ = y := hs.inv_eq
  have hb0 : y * b * y⁻¹ ∈ X := by
    have := mem_conjSub_iff.mp hb
    rw [hyi] at this
    rw [hyi]
    exact this
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : F, b₀ = y * b * y⁻¹ := ⟨_, rfl⟩
  rw [← hb₀] at hb0
  have hbb : b = y * b₀ * y⁻¹ := by
    rw [hb₀]
    calc b = (y * y) * b * (y * y) := by rw [hs.sq]; group
      _ = y * (y * b * y⁻¹) * y⁻¹ := by rw [hyi]; group
  have hdiag : b₀ * b = diag y b₀ := by
    unfold diag
    rw [← hbb]
  have ha' : y * a * y⁻¹ ∈ conjSub y X := conj_mem_conjSub ha
  have hfix : a * b = (y * a * y⁻¹) * b₀ := by
    have h1 : y * (a * b) * y⁻¹ = a * b := by
      calc y * (a * b) * y⁻¹ = (a * b * y) * y⁻¹ := by rw [← hdy]
        _ = a * b := by group
    calc a * b = y * (a * b) * y⁻¹ := h1.symm
      _ = (y * a * y⁻¹) * b₀ := by rw [hb₀]; group
  have hcomm : (y * a * y⁻¹) * b₀ = b₀ * (y * a * y⁻¹) := (hc b₀ hb0 _ ha').symm
  have hw : b₀⁻¹ * a = (y * a * y⁻¹) * b⁻¹ := by
    have : a * b = b₀ * (y * a * y⁻¹) := hfix.trans hcomm
    calc b₀⁻¹ * a = b₀⁻¹ * (a * b) * b⁻¹ := by group
      _ = b₀⁻¹ * (b₀ * (y * a * y⁻¹)) * b⁻¹ := by rw [this]
      _ = (y * a * y⁻¹) * b⁻¹ := by group
  have hwX : b₀⁻¹ * a ∈ X := X.mul_mem (X.inv_mem hb0) ha
  have hwX' : b₀⁻¹ * a ∈ conjSub y X := by
    rw [hw]
    exact (conjSub y X).mul_mem ha' ((conjSub y X).inv_mem hb)
  rcases Mem3.eq_one_or_eq_of_central hs.member hex hwX (fun b' hb' => (hc b' hb' _ hwX').symm)
    with h1 | h1
  · refine ⟨b₀, hb0, Or.inl ?_⟩
    have ha₀ : a = b₀ := by
      have := congrArg (fun t => b₀ * t) h1
      simpa using this
    rw [ha₀]
    exact hdiag
  · refine ⟨b₀, hb0, Or.inr ?_⟩
    have hax : a = b₀ * x := by
      have := congrArg (fun t => b₀ * t) h1
      simpa using this
    have hxb : b * x = x * b := hs.twin.mul_comm_of_mem hb
    rw [hax]
    calc b₀ * x * b = b₀ * (x * b) := by group
      _ = b₀ * (b * x) := by rw [hxb]
      _ = (b₀ * b) * x := by group
      _ = diag y b₀ * x := by rw [hdiag]

theorem isSubnormal_diagGroupOf :
    IsSubnormal (diagGroupOf hs hex)
      (Subgroup.centralizer ({x} : Set F) ⊓ Subgroup.centralizer ({y} : Set F)) := by
  set E : Subgroup F := twinProd (Subgroup.zpowers y) X with hE
  have hy2 : y * y = 1 := hs.sq
  have hyx : y * x = x * y := hs.comm
  have hzK : ∀ k ∈ Subgroup.zpowers y, k * x = x * k := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact Commute.zpow_left (show Commute y x from hyx) n
  have hEsub : IsSubnormal E (Subgroup.centralizer ({x} : Set F)) :=
    isSubnormal_twinProd hs.member.subnormal hzK
  have hyE : y ∈ Subgroup.normalizer (E : Set F) :=
    K_le_normalizer_twinProd (Subgroup.mem_zpowers y)
  have hyCx : y ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({x} : Set F) : Subgroup F) : Set F) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hyx)
  have hfix := isSubnormal_inf_centralizer_of_normalizes hEsub hyE hyCx
  have hpow : ∀ n : ℤ, y ^ n = 1 ∨ y ^ n = y := by
    intro n
    rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, hy2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hy2, one_zpow, one_mul]
  have hEle : E ≤ X ⊔ conjSub y X := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨k, hk, rfl⟩ := hL
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rcases hpow n with h | h
    · rw [h, conjSub_one]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  have hXE : X ≤ E := le_twinProd ⟨1, Subgroup.one_mem _, (conjSub_one X).symm⟩
  have hX'E : conjSub y X ≤ E := le_twinProd ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hΔE : diagGroupOf hs hex ≤ E := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := (mem_diagGroupOf_iff hs hex).mp hk
    exact E.mul_mem (hXE hq) (hX'E (conj_mem_conjSub hq))
  have hΔD : diagGroupOf hs hex ≤ E ⊓ Subgroup.centralizer ({y} : Set F) := fun k hk =>
    ⟨hΔE hk, Subgroup.mem_centralizer_singleton_iff.mpr (diagGroupOf_comm_y hs hex hk)⟩
  have hnorm : ((diagGroupOf hs hex).subgroupOf
      (E ⊓ Subgroup.centralizer ({y} : Set F))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΔD]
    intro k d hk hd
    obtain ⟨c, hcX, hc | hc⟩ := fixed_decomp hs hex (hEle hd.1)
      (Subgroup.mem_centralizer_singleton_iff.mp hd.2)
    · rw [hc]
      exact (diagGroupOf hs hex).mul_mem
        ((diagGroupOf hs hex).mul_mem (diag_mem_diagGroupOf hs hex hcX) hk)
        ((diagGroupOf hs hex).inv_mem (diag_mem_diagGroupOf hs hex hcX))
    · rw [hc]
      have hkx : k * x = x * k := diagGroupOf_comm_x hs hex hk
      have e1 : diag y c * x * k * (diag y c * x)⁻¹ = diag y c * k * (diag y c)⁻¹ := by
        calc diag y c * x * k * (diag y c * x)⁻¹ = diag y c * (x * k * x⁻¹) * (diag y c)⁻¹ := by
              group
          _ = diag y c * k * (diag y c)⁻¹ := by rw [← hkx]; group
      rw [e1]
      exact (diagGroupOf hs hex).mul_mem
        ((diagGroupOf hs hex).mul_mem (diag_mem_diagGroupOf hs hex hcX) hk)
        ((diagGroupOf hs hex).inv_mem (diag_mem_diagGroupOf hs hex hcX))
  exact isSubnormal_trans (isSubnormal_of_normal_subgroupOf hΔD hnorm) hfix

end Diag

end CFSG.ClassicalInvolution.Q3.Q3T6B
