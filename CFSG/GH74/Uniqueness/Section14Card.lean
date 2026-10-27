module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Uniqueness.Section12Transport
public import CFSG.GH74.Uniqueness.Section14Aut
public import CFSG.GH74.Uniqueness.Theorem4

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section General

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem inf_centralizer_eq_bot_of_center (L : Subgroup X) (hc : center ↥L = ⊥) :
    L ⊓ centralizer (L : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
  have h1 : (⟨x, hxL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hxC) g g.2)
  rw [hc, mem_bot] at h1
  rw [mem_bot]
  exact congrArg Subtype.val h1

omit [Finite X] in
theorem card_range_conj_of_center (L : Subgroup X) (hc : center ↥L = ⊥) :
    Nat.card (MulAut.conj : ↥L →* MulAut ↥L).range = Nat.card L := by
  have hinj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : l ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut ↥L => σ g) hl
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hc, mem_bot] at h1
    exact h1
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

omit [Finite X] in
theorem card_normalizer_eq_mul (L : Subgroup X) (hc : center ↥L = ⊥) :
    ∃ d : ℕ, Nat.card (normalizer (L : Set X)) =
      Nat.card (centralizer (L : Set X)) * Nat.card L * d ∧
      d ∣ (MulAut.conj : ↥L →* MulAut ↥L).range.index := by
  set N := normalizer (L : Set X) with hN
  set I := (MulAut.conj : ↥L →* MulAut ↥L).range with hI
  have : I.Normal := Bender.normal_range_conj ↥L
  have h1 := card_eq_card_inf_centralizer_mul L N le_rfl
  have hJN : centralizer (L : Set X) ⊓ N = centralizer (L : Set X) :=
    inf_eq_left.mpr (centralizer_le_normalizer _)
  set R := (N.subgroupOf N).map (conjAut L) with hR
  have hIR : I ≤ R := by
    rintro _ ⟨l, rfl⟩
    refine ⟨⟨l, le_normalizer l.2⟩, ?_, ?_⟩
    · simp
    · exact conjAut_of_mem L l.2
  refine ⟨I.relIndex R, ?_, relIndex_dvd_index_of_normal I R⟩
  rw [h1, hJN, mul_assoc]
  congr 1
  have h2 := Subgroup.relIndex_mul_card I R
  rw [inf_eq_left.mpr hIR, card_range_conj_of_center L hc] at h2
  rw [← h2, mul_comm]

omit [Finite X] in
theorem card_eq_mul_of_le_normalizer (L D : Subgroup X) (hc : center ↥L = ⊥)
    (hDN : D ≤ normalizer (L : Set X)) (hJD : centralizer (L : Set X) ≤ D) :
    ∃ d : ℕ, Nat.card D = Nat.card (centralizer (L : Set X)) * Nat.card ↥(D ⊓ L) * d ∧
      d ∣ (MulAut.conj : ↥L →* MulAut ↥L).range.index := by
  set N := normalizer (L : Set X) with hN
  set I := (MulAut.conj : ↥L →* MulAut ↥L).range with hI
  have : I.Normal := Bender.normal_range_conj ↥L
  have hDLN : D ⊓ L ≤ N := inf_le_left.trans hDN
  have h1 := card_eq_card_inf_centralizer_mul L D hDN
  have h2 := card_eq_card_inf_centralizer_mul L (D ⊓ L) hDLN
  have hJD' : centralizer (L : Set X) ⊓ D = centralizer (L : Set X) := inf_eq_left.mpr hJD
  have hJDL : centralizer (L : Set X) ⊓ (D ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have := inf_centralizer_eq_bot_of_center L hc
    rw [← this]
    exact mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).2).2, (mem_inf.mp hx).1⟩
  rw [hJDL, card_bot, one_mul] at h2
  set ψD := (D.subgroupOf N).map (conjAut L) with hψD
  set ψDL := ((D ⊓ L).subgroupOf N).map (conjAut L) with hψDL
  have hinf : I ⊓ ψD = ψDL := by
    ext σ
    constructor
    · rintro ⟨⟨l, rfl⟩, g, hg, hgσ⟩
      have hgD : (g : X) ∈ D := mem_subgroupOf.mp hg
      have hJ := mul_inv_mem_centralizer_of_conjAut_eq L g l hgσ
      have hlD : (l : X) ∈ D := by
        have := D.mul_mem (D.inv_mem (hJD hJ)) hgD
        simpa using this
      refine ⟨⟨l, le_normalizer l.2⟩, mem_subgroupOf.mpr (mem_inf.mpr ⟨hlD, l.2⟩), ?_⟩
      exact conjAut_of_mem L l.2
    · rintro ⟨g, hg, rfl⟩
      have hgDL := mem_inf.mp (mem_subgroupOf.mp hg)
      refine ⟨⟨⟨g, hgDL.2⟩, ?_⟩, g, mem_subgroupOf.mpr hgDL.1, rfl⟩
      exact (conjAut_of_mem L hgDL.2).symm
  refine ⟨I.relIndex ψD, ?_, relIndex_dvd_index_of_normal I ψD⟩
  rw [h1, hJD', mul_assoc]
  congr 1
  have h3 := Subgroup.relIndex_mul_card I ψD
  rw [hinf, ← h2] at h3
  rw [← h3, mul_comm]

end General

section Orbit

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.card_M_eq
    (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) :
    Nat.card M = ((omega M).ncard - 1) * Nat.card ↥(M ⊓ conjugate M t) := by
  have hD := S.theorem4.1
  have hβ : conjugate M t ∈ omega M := ⟨t, rfl⟩
  have hβM : conjugate M t ≠ M := by
    intro h
    apply htM
    have h1 := (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M) (u := t)).mp h
    exact h1
  let β : omega M := ⟨conjugate M t, hβ⟩
  have hstab : MulAction.stabilizer (↥M) β = (conjugate M t).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf]
    constructor
    · intro hm
      have h1 : conjugate (conjugate M t) (m : X)⁻¹ = conjugate M t :=
        congrArg Subtype.val hm
      have h2 := (S.prodDisc.conjugate_eq_iff_mem hβ).mp h1
      simpa using (conjugate M t).inv_mem h2
    · intro hm
      apply Subtype.ext
      change conjugate (conjugate M t) (m : X)⁻¹ = conjugate M t
      exact (S.prodDisc.conjugate_eq_iff_mem hβ).mpr ((conjugate M t).inv_mem hm)
  have horbit : MulAction.orbit (↥M) β = {γ : omega M | (γ : Subgroup X) ≠ M} := by
    ext γ
    constructor
    · rintro ⟨m, rfl⟩
      change conjugate (conjugate M t) (m : X)⁻¹ ≠ M
      intro h
      apply hβM
      have hmM : conjugate M (m : X)⁻¹⁻¹ = M :=
        (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (by simp)
      calc conjugate M t = conjugate (conjugate (conjugate M t) (m : X)⁻¹) (m : X)⁻¹⁻¹ := by
            rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
        _ = conjugate M (m : X)⁻¹⁻¹ := by rw [h]
        _ = M := hmM
    · intro hγ
      obtain ⟨m, hm, hmγ⟩ :=
        S.prodDisc.exists_mem_conjugate_of_doublyTransitive hD hβ γ.2 hβM hγ
      refine ⟨⟨m⁻¹, M.inv_mem hm⟩, Subtype.ext ?_⟩
      change conjugate (conjugate M t) (m⁻¹)⁻¹ = γ
      rw [inv_inv]
      exact hmγ
  have hcard_orbit : (MulAction.orbit (↥M) β).ncard = (omega M).ncard - 1 := by
    rw [horbit]
    have e : {γ : omega M | (γ : Subgroup X) ≠ M} = (Set.univ : Set (omega M)) \
        {⟨M, self_mem_omega M⟩} := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      constructor
      · intro h1 h2
        exact h1 (congrArg Subtype.val h2)
      · intro h1 h2
        exact h1 (Subtype.ext h2)
    rw [e, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      Nat.card_coe_set_eq]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (↥M) β)
  rw [MulAction.index_stabilizer, hcard_orbit, hstab] at h1
  have h2 : Nat.card ((conjugate M t).subgroupOf M) = Nat.card ↥(M ⊓ conjugate M t) := by
    rw [← inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  rw [← h1, mul_comm]

end Orbit

section Sec14Card

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

theorem out_L {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2) :
    (MulAut.conj : ↥c.L →* MulAut ↥c.L).range.index ∣ n ∧
      Odd (MulAut.conj : ↥c.L →* MulAut ↥c.L).range.index := by
  obtain ⟨-, h1, h2⟩ := h.bender.outer_suzuki
  exact ⟨h1, h2⟩

theorem card_D {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2) :
    ∃ d : ℕ, Nat.card c.D = (2 ^ n - 1) * Nat.card (centralizer (c.L : Set X)) * d ∧
      d ∣ n ∧ Odd d := by
  have hDN : c.D ≤ normalizer (c.L : Set X) := by
    intro d hd
    have : d ∈ ((normalizer (c.L : Set X) : Subgroup X) : Set X) := by
      rw [h.normalizer_eq]
      exact ⟨1, c.L.one_mem, d, hd, one_mul d⟩
    exact this
  obtain ⟨d, hd, hdvd⟩ := card_eq_mul_of_le_normalizer c.L c.D h.center_eq_bot hDN
    h.centralizer_le
  obtain ⟨hout, hodd⟩ := out_L h
  refine ⟨d, ?_, hdvd.trans hout, Odd.of_dvd_nat hodd hdvd⟩
  rw [hd, h.k_card]
  ring

theorem card_normalizer_L {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2) :
    ∃ d : ℕ, Nat.card (normalizer (c.L : Set X)) =
      Nat.card (centralizer (c.L : Set X)) * Nat.card c.L * d ∧ d ∣ n ∧ Odd d := by
  obtain ⟨d, hd, hdvd⟩ := card_normalizer_eq_mul c.L h.center_eq_bot
  obtain ⟨hout, hodd⟩ := out_L h
  exact ⟨d, hd, hdvd.trans hout, Odd.of_dvd_nat hodd hdvd⟩

theorem card_M
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) {c : Ctx12 Z M} {n : ℕ}
    (h : LData c n 2) :
    Nat.card M = 2 ^ (3 * n) * (2 ^ (2 * n) - 2 ^ n + 1) * Nat.card c.D := by
  have hΩ : (omega M).ncard + (2 ^ n) ^ 4 = (2 ^ n) ^ 5 + (2 ^ n) ^ 3 + 1 := by
    rcases h12.l1210 c n 2 h with ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨h1, -⟩
    · omega
    · exact h2
    · omega
  rw [S.card_M_eq c.htM]
  have hQ : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  set Q := 2 ^ n with hQdef
  have e3 : 2 ^ (3 * n) = Q ^ 3 := by rw [hQdef, ← pow_mul, mul_comm]
  have e2 : 2 ^ (2 * n) = Q ^ 2 := by rw [hQdef, ← pow_mul, mul_comm]
  rw [e3, e2]
  congr 1
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hA : 1 ≤ (omega M).ncard := by nlinarith [pow_le_pow_left₀ (Nat.zero_le Q) hQ2 2]
  zify [hQ2, hA]
  have h' : ((omega M).ncard : ℤ) + (Q : ℤ) ^ 4 = (Q : ℤ) ^ 5 + (Q : ℤ) ^ 3 + 1 := by
    exact_mod_cast hΩ
  linear_combination h'

end Sec14

end Sec14Card

end CFSG.GH74.Uniqueness
