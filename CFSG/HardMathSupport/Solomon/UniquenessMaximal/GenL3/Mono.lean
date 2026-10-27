module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.SylowIndex
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.HardMathSupport.Timmesfeld.LinearRank CFSG.SectionRank.OddCover Matrix Equiv

variable {F : Type} [Field F]

theorem exists_conj_into_mono [Finite F] (hF3 : 3 ∣ Nat.card Fˣ) (U : Subgroup (GL (Fin 3) F))
    (hU : IsPGroup 3 (U.map (QuotientGroup.mk' (Subgroup.center (GL (Fin 3) F))))) :
    ∃ m : GL (Fin 3) F, ∀ g ∈ U, m * g * m⁻¹ ∈ (monoHom 3 F).range := by
  obtain ⟨x, hx⟩ := exists_conj_le_of_not_dvd_index Nat.prime_three (monoImage 3 F)
    (not_dvd_index_monoImage Nat.prime_three (by norm_num) hF3) _ hU
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨m, fun g hg => ?_⟩
  have h1 := hx (QuotientGroup.mk' _ g) (Subgroup.mem_map_of_mem _ hg)
  obtain ⟨y, hy⟩ := h1
  have hy' : (QuotientGroup.mk' (Subgroup.center (GL (Fin 3) F)) (monoHom 3 F y)) =
      QuotientGroup.mk' _ (m * g * m⁻¹) := by
    change projMono 3 F y = _
    rw [hy]
    rfl
  have hz : (monoHom 3 F y)⁻¹ * (m * g * m⁻¹) ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center (GL (Fin 3) F)), MonoidHom.mem_ker, map_mul,
      map_inv, hy', inv_mul_cancel]
  have hzr := center_le_range_monoHom hz
  have : m * g * m⁻¹ = monoHom 3 F y * ((monoHom 3 F y)⁻¹ * (m * g * m⁻¹)) := by group
  rw [this]
  exact Subgroup.mul_mem _ ⟨y, rfl⟩ hzr

open Equiv in
theorem perm_cube_cases : ∀ c : Perm (Fin 3), c ^ 3 = 1 → c ≠ 1 →
    (c 0 = 1 ∧ c 1 = 2 ∧ c 2 = 0) ∨ (c 0 = 2 ∧ c 1 = 0 ∧ c 2 = 1) := by decide

open Equiv in
theorem perm_cube_card : Fintype.card {σ : Perm (Fin 3) // σ ^ 3 = 1} = 3 := by decide

open Equiv in
theorem perm_const_of_fixed {c : Perm (Fin 3)} (h3 : c ^ 3 = 1) (h1 : c ≠ 1)
    {d : Fin 3 → Fˣ} (hd : ∀ i, d (c.symm i) = d i) : ∀ i j, d i = d j := by
  have h0 := hd 0
  have h1' := hd 1
  have h2 := hd 2
  rcases perm_cube_cases c h3 h1 with ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩
  · have e0 : c.symm 1 = 0 := by rw [Equiv.symm_apply_eq]; exact a0.symm
    have e1 : c.symm 2 = 1 := by rw [Equiv.symm_apply_eq]; exact a1.symm
    have e2 : c.symm 0 = 2 := by rw [Equiv.symm_apply_eq]; exact a2.symm
    rw [e2] at h0
    rw [e0] at h1'
    rw [e1] at h2
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  · have e0 : c.symm 2 = 0 := by rw [Equiv.symm_apply_eq]; exact a0.symm
    have e1 : c.symm 0 = 1 := by rw [Equiv.symm_apply_eq]; exact a1.symm
    have e2 : c.symm 1 = 2 := by rw [Equiv.symm_apply_eq]; exact a2.symm
    rw [e1] at h0
    rw [e2] at h1'
    rw [e0] at h2
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all

theorem mono_diag_of_comm [Finite F] (U : Subgroup (GL (Fin 3) F))
    (hM : U ≤ (monoHom 3 F).range)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hexp : ∀ g ∈ U, g ^ 3 ∈ Subgroup.center (GL (Fin 3) F))
    (hUcard : Nat.card U = 9 * Nat.card (Subgroup.center (GL (Fin 3) F))) :
    ∀ g ∈ U, ∃ d : Fin 3 → Fˣ, g = diagHom 3 d := by
  classical
  set Z := Subgroup.center (GL (Fin 3) F) with hZdef
  have hinj : Function.Injective (monoHom 3 F) := monoHom_injective
  set B : Subgroup (MonoGroup 3 F) := U.comap (monoHom 3 F) with hB
  set π : MonoGroup 3 F →* Perm (Fin 3) := SemidirectProduct.rightHom with hπ
  have hcube : ∀ x ∈ B, (π x) ^ 3 = 1 := by
    intro x hx
    have h1 : monoHom 3 F (x ^ 3) ∈ Z := by rw [map_pow]; exact hexp _ hx
    obtain ⟨c, hc⟩ := mem_center_iff.1 h1
    have := right_eq_one_of_scalar hc
    rw [← map_pow, hπ, SemidirectProduct.rightHom_eq_right]
    exact this
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm _ ha _ hb
  have hBU : Nat.card B = Nat.card U := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : B => (⟨monoHom 3 F x, x.2⟩ : U)) ⟨?_, ?_⟩)
    · intro a b h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · intro u
      obtain ⟨x, hx⟩ := hM u.2
      exact ⟨⟨x, by rw [hB, Subgroup.mem_comap, hx]; exact u.2⟩, Subtype.ext hx⟩
  set ρ : B →* Perm (Fin 3) := SemidirectProduct.rightHom.comp B.subtype with hρ
  have hρx : ∀ x : B, ρ x = (x : MonoGroup 3 F).right := fun x => rfl
  have hall1 : ∀ x : B, ρ x = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x0, hx0⟩ := hcon
    have hx03 : (ρ x0) ^ 3 = 1 := hcube _ x0.2
    have hkerZ : ∀ k : ρ.ker, monoHom 3 F (k : B) ∈ Z := by
      intro k
      have hk1 : ((k : B) : MonoGroup 3 F).right = 1 := by
        have := k.2
        rw [MonoidHom.mem_ker, hρx] at this
        exact this
      have hcm := hBcomm _ (k : B).2 _ x0.2
      have hl := congrArg SemidirectProduct.left hcm
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, hk1] at hl
      have hfix : permAct 3 F (x0 : MonoGroup 3 F).right ((k : MonoGroup 3 F).left) =
          (k : MonoGroup 3 F).left := by
        have : (k : MonoGroup 3 F).left * (x0 : MonoGroup 3 F).left =
            (x0 : MonoGroup 3 F).left *
              permAct 3 F (x0 : MonoGroup 3 F).right ((k : MonoGroup 3 F).left) := by
          simpa using hl
        rw [mul_comm] at this
        exact (mul_left_cancel this).symm
      have hconst := perm_const_of_fixed (c := (x0 : MonoGroup 3 F).right) hx03 hx0
        (d := (k : MonoGroup 3 F).left) (fun i => by
          have := congrFun hfix i
          rw [permAct_apply] at this
          exact this)
      have hmk : monoHom 3 F (k : B) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ((k : MonoGroup 3 F).left 0) := by
        rw [monoHom_apply, hk1, map_one, mul_one, ← diagHom_const]
        congr 1
        funext i
        exact hconst i 0
      rw [hmk]
      rw [hZdef, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have hker : Nat.card ρ.ker ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun k : ρ.ker => (⟨monoHom 3 F (k : B), hkerZ k⟩ : Z)) ?_
      intro a b hab
      have := hinj (congrArg Subtype.val hab)
      exact Subtype.ext (Subtype.ext this)
    have hrange : Nat.card ρ.range ≤ 3 := by
      have h3 : Nat.card {σ : Perm (Fin 3) // σ ^ 3 = 1} = 3 := by
        rw [Nat.card_eq_fintype_card]; exact perm_cube_card
      have hmem : ∀ σ : ρ.range, σ.1 ^ 3 = 1 := by
        intro σ
        obtain ⟨y, hy⟩ := σ.2
        rw [← hy]
        exact hcube _ y.2
      refine le_trans (Nat.card_le_card_of_injective
        (fun σ : ρ.range => (⟨σ.1, hmem σ⟩ : {σ : Perm (Fin 3) // σ ^ 3 = 1})) ?_) h3.le
      intro a b hab
      exact Subtype.ext (Subtype.mk.inj hab)
    have hmul := Subgroup.card_ker_mul_card_range ρ
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    nlinarith
  intro g hg
  obtain ⟨x, hx⟩ := hM hg
  have hxB : x ∈ B := by rw [hB, Subgroup.mem_comap, hx]; exact hg
  have hr : x.right = 1 := hall1 ⟨x, hxB⟩
  refine ⟨x.left, ?_⟩
  rw [← hx, monoHom_apply, hr, map_one, mul_one]

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
