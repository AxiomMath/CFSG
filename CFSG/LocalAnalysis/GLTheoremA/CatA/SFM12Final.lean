module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Iso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open CFSG.Open
open scoped commutatorElement

theorem comm_mul_central_left {G : Type} [Group G] {K : Subgroup G} {x y z : G}
    (hz : ∀ k ∈ K, z * k = k * z) (hy : y ∈ K) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hzy := hz y hy
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzy]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_mul_central_right {G : Type} [Group G] {K : Subgroup G} {x y z : G}
    (hz : ∀ k ∈ K, z * k = k * z) (hx : x ∈ K) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hzx : z * x⁻¹ = x⁻¹ * z := hz x⁻¹ (K.inv_mem hx)
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem quasisimple_le_of_normal {G : Type} [Group G] {K J : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple K) (hJK : J ≤ K) (hJq : CFSG.Open.IsQuasisimple J)
    (hJn : ∀ j ∈ K, ∀ m ∈ J, j * m * j⁻¹ ∈ J) : K ≤ J := by
  rcases quasisimple_dichot hK (M := J) hJK hJn with hcen | hdec
  · exfalso
    apply not_all_commute_of_quasisimple hJq
    intro x y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcen x x.2 y (hJK y.2)
  · have hcomm : ∀ a b : K, ⁅(a : G), (b : G)⁆ ∈ J := by
      intro a b
      obtain ⟨m, hm, z, hz, hzc, ha⟩ := hdec a a.2
      obtain ⟨m', hm', z', hz', hzc', hb⟩ := hdec b b.2
      have e : ⁅(a : G), (b : G)⁆ = ⁅m * z, m' * z'⁆ := by rw [ha, hb]
      rw [e, comm_mul_central_right hzc' (K.mul_mem (hJK hm) hz),
        comm_mul_central_left hzc (hJK hm')]
      rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem hm hm') (J.inv_mem hm)) (J.inv_mem hm')
    have hle : commutator K ≤ J.subgroupOf K := by
      unfold commutator
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_subgroupOf]
      have := hcomm a b
      rw [commutatorElement_def] at this ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    rw [hK.1] at hle
    intro x hx
    exact Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_top (⟨x, hx⟩ : K)))

theorem mem_Eset' {F : Type} [Field F] [DecidableEq F] (d : Fin 6 → F) (l0 : F) (k : Fin 6) :
    k ∈ Eset d l0 ↔ d k = l0 := by
  simp [Eset]

theorem core_diag {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Finite F]
    {d : Fin 6 → F} (hF : Nat.card F = (2 ^ 2) ^ 2)
    {g : ↥(StatedSU 6 (2 ^ 2) F)} (hgd : (g : GL (Fin 6) F).val = Matrix.diagonal d)
    (hd5 : ∀ k, d k ^ 5 = 1) (hg1 : g ≠ 1) {J : Subgroup ↥(StatedSU 6 (2 ^ 2) F)}
    (hJq : CFSG.Open.IsQuasisimple J) (hJC : J ≤ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)))
    (hnorm : ∀ c ∈ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)), ∀ j ∈ J,
      c * j * c⁻¹ ∈ J)
    (h41 : 41 ∣ Nat.card J) : g ∈ J := by
  have hCg : Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)) = Cg d := centralizer_eq_Cg hgd
  rw [hCg] at hJC hnorm
  obtain ⟨l0, hl0⟩ := exists_block hF hJq hJC hnorm
  have hF16 : Nat.card F = 16 := by rw [hF]; norm_num
  have hdet : (g : GL (Fin 6) F).val.det = 1 := ((mem_SU_iff hF (g : GL (Fin 6) F)).1 g.2).1
  have hdetd : ∏ k, d k = 1 := by
    rw [← Matrix.det_diagonal, ← hgd]
    exact hdet
  have hcard_le : (Eset d l0).card ≤ 6 := by
    have := Finset.card_le_univ (Eset d l0)
    simpa using this
  rcases (show (Eset d l0).card ≤ 4 ∨ (Eset d l0).card = 5 ∨ (Eset d l0).card = 6 by omega) with h4 | h5 | h6
  ·
    exfalso
    have h1 : 41 ∣ Nat.card ↥(Ug d l0) := h41.trans (Subgroup.card_dvd_of_le hl0)
    exact not_dvd41_card_GL hF16 h4 (h1.trans (card_Ug_dvd_GL d l0))
  ·
    have hC : (Eset d l0).card + (Finset.univ.filter fun k : Fin 6 => ¬ d k = l0).card = 6 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 6)))
        (fun k : Fin 6 => d k = l0)
      simpa using this
    have hC1 : (Finset.univ.filter fun k : Fin 6 => ¬ d k = l0).card = 1 := by omega
    obtain ⟨k0, hk0⟩ := Finset.card_eq_one.1 hC1
    have hl5 : l0 ^ 5 = 1 := by
      have hpos : 0 < (Eset d l0).card := by omega
      obtain ⟨k, hk⟩ := Finset.card_pos.1 hpos
      have hkl : d k = l0 := (mem_Eset' d l0 k).1 hk
      rw [← hkl]
      exact hd5 k
    have hprod : ∏ k, d k = l0 ^ 5 * d k0 := by
      rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin 6)) (fun k => d k = l0)]
      have e1 : ∏ k ∈ Finset.univ.filter (fun k => d k = l0), d k = l0 ^ 5 := by
        rw [Finset.prod_congr rfl (fun k hk => (mem_Eset' d l0 k).1 hk), Finset.prod_const, h5]
      have e2 : ∏ k ∈ Finset.univ.filter (fun k => ¬ d k = l0), d k = d k0 := by
        rw [hk0, Finset.prod_singleton]
      rw [e1, e2]
    have hd0 : d k0 = 1 := by
      rw [hprod, hl5, one_mul] at hdetd
      exact hdetd
    have hd1 : ∀ k, ¬ d k = l0 → d k = 1 := by
      intro k hk
      have hkC : k ∈ Finset.univ.filter fun k : Fin 6 => ¬ d k = l0 := by simpa using hk
      rw [hk0, Finset.mem_singleton] at hkC
      rw [hkC, hd0]
    have hgU : g ∈ Ug d l0 := by
      refine ⟨?_, ?_⟩
      · intro m
        have hcomm : Matrix.diagonal d * (g : GL (Fin 6) F).val = (g : GL (Fin 6) F).val * Matrix.diagonal d := by
          rw [← hgd]
        exact (commute_diag_iff d _).1 hcomm m
      · show ((g : GL (Fin 6) F).val) * (1 - eigP d l0) = 1 - eigP d l0
        rw [hgd]
        ext i j
        by_cases hij : i = j
        · subst hij
          by_cases hi : d i = l0
          · simp [eigP, Matrix.diagonal_mul, hi]
          · simp [eigP, Matrix.diagonal_mul, hi, hd1 i hi]
        · simp [eigP, Matrix.diagonal_mul, Matrix.diagonal_apply, hij]
    have hUgC : Ug d l0 ≤ Cg d := fun x hx => hx.1
    have hUq : CFSG.Open.IsQuasisimple ↥(Ug d l0) := isQuasisimple_Ug d l0 hF (by omega)
    have hle : Ug d l0 ≤ J :=
      quasisimple_le_of_normal hUq hl0 hJq (fun j hj m hm => hnorm j (hUgC hj) m hm)
    exact hle hgU
  ·
    exfalso
    apply hg1
    have hall : ∀ k, d k = l0 := by
      have huniv := Finset.eq_univ_of_card (Eset d l0) (by simpa using h6)
      intro k
      have hk : k ∈ Eset d l0 := by rw [huniv]; exact Finset.mem_univ k
      exact (mem_Eset' d l0 k).1 hk
    have hl6 : l0 ^ 6 = 1 := by
      have : ∏ k, d k = l0 ^ 6 := by
        rw [Finset.prod_congr rfl (fun k _ => hall k), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      rw [← this]
      exact hdetd
    have hl5 : l0 ^ 5 = 1 := by rw [← hall 0]; exact hd5 0
    have hl1 : l0 = 1 := by
      have h : l0 ^ 6 = l0 ^ 5 * l0 := pow_succ l0 5
      rw [hl6, hl5, one_mul] at h
      exact h.symm
    have hd1 : d = fun _ => (1 : F) := funext fun k => by rw [hall k, hl1]
    apply Subtype.ext
    apply Units.ext
    show (g : GL (Fin 6) F).val = 1
    rw [hgd, hd1]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem mem_conj_map' {G : Type} [Group G] (K : Subgroup G) (P x : G) :
    x ∈ K.map (MulAut.conj P).toMonoidHom ↔ P⁻¹ * x * P ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e : P⁻¹ * (P * k * P⁻¹) * P = k := by group
    show P⁻¹ * (P * k * P⁻¹) * P ∈ K
    rw [e]
    exact hk
  · intro h
    refine ⟨P⁻¹ * x * P, h, ?_⟩
    show P * (P⁻¹ * x * P) * P⁻¹ = x
    group

@[expose] def UnitaryDiagFact : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] [CharP F 2] [Finite F], Nat.card F = (2 ^ 2) ^ 2 →
    ∀ g : ↥(StatedSU 6 (2 ^ 2) F), g ^ 5 = 1 →
      ∃ P : ↥(StatedSU 6 (2 ^ 2) F), ∃ d : Fin 6 → F,
        ((P * g * P⁻¹ : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F).val = Matrix.diagonal d

theorem core_general {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Finite F]
    (hF : Nat.card F = (2 ^ 2) ^ 2)
    (hdiag : ∀ g : ↥(StatedSU 6 (2 ^ 2) F), g ^ 5 = 1 → ∃ P : ↥(StatedSU 6 (2 ^ 2) F),
      ∃ d : Fin 6 → F, ((P * g * P⁻¹ : ↥(StatedSU 6 (2 ^ 2) F)) : GL (Fin 6) F).val = Matrix.diagonal d)
    {g : ↥(StatedSU 6 (2 ^ 2) F)} (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1)
    {K : Subgroup ↥(StatedSU 6 (2 ^ 2) F)} (hKq : CFSG.Open.IsQuasisimple K)
    (hKC : K ≤ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)))
    (hnorm : ∀ c ∈ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)), ∀ j ∈ K,
      c * j * c⁻¹ ∈ K)
    (h41 : 41 ∣ Nat.card K) : g ∈ K := by
  obtain ⟨P, d, hPd⟩ := hdiag g hg5
  have hcentr : ∀ (h x : ↥(StatedSU 6 (2 ^ 2) F)),
      x ∈ Subgroup.centralizer ({h} : Set ↥(StatedSU 6 (2 ^ 2) F)) ↔ h * x = x * h := by
    intro h x
    rw [Subgroup.mem_centralizer_iff]
    simp
  have hg'5 : (P * g * P⁻¹) ^ 5 = 1 := by
    have h1 : (MulAut.conj P g) ^ 5 = 1 := by rw [← map_pow, hg5, map_one]
    simpa [MulAut.conj_apply] using h1
  have hg'1 : P * g * P⁻¹ ≠ 1 := by
    intro h
    apply hg1
    have h2 : P * g = P := by
      have := congrArg (· * P) h
      simpa [mul_assoc] using this
    exact mul_left_cancel (h2.trans (mul_one P).symm)
  have hd5 : ∀ k, d k ^ 5 = 1 := by
    have h5 := congrArg (fun x : ↥(StatedSU 6 (2 ^ 2) F) => ((x : GL (Fin 6) F).val)) hg'5
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hPd, Units.val_one, one_pow] at h5
    intro k
    have h6 := congrFun (congrFun h5 k) k
    rw [Matrix.diagonal_pow] at h6
    simpa [Matrix.diagonal_apply] using h6
  have hK'q : CFSG.Open.IsQuasisimple (K.map (MulAut.conj P).toMonoidHom) :=
    hKq.of_mulEquiv (Subgroup.equivMapOfInjective K _ (MulAut.conj P).injective).symm
  have h41' : 41 ∣ Nat.card (K.map (MulAut.conj P).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj P).injective]
    exact h41
  have hK'C : K.map (MulAut.conj P).toMonoidHom ≤
      Subgroup.centralizer ({P * g * P⁻¹} : Set ↥(StatedSU 6 (2 ^ 2) F)) := by
    intro x hx
    rw [mem_conj_map'] at hx
    rw [hcentr]
    have hx' : x = P * (P⁻¹ * x * P) * P⁻¹ := by group
    rw [hx']
    have hk := hKC hx
    rw [hcentr] at hk
    calc P * g * P⁻¹ * (P * (P⁻¹ * x * P) * P⁻¹)
        = P * (g * (P⁻¹ * x * P)) * P⁻¹ := by group
      _ = P * ((P⁻¹ * x * P) * g) * P⁻¹ := by rw [hk]
      _ = P * (P⁻¹ * x * P) * P⁻¹ * (P * g * P⁻¹) := by group
  have hnorm' : ∀ c ∈ Subgroup.centralizer ({P * g * P⁻¹} : Set ↥(StatedSU 6 (2 ^ 2) F)),
      ∀ j ∈ K.map (MulAut.conj P).toMonoidHom, c * j * c⁻¹ ∈ K.map (MulAut.conj P).toMonoidHom := by
    intro c hc j hj
    rw [hcentr] at hc
    rw [mem_conj_map'] at hj ⊢
    have hc0 : P⁻¹ * c * P ∈ Subgroup.centralizer ({g} : Set ↥(StatedSU 6 (2 ^ 2) F)) := by
      rw [hcentr]
      have h1 : c * (P * g * P⁻¹) = (P * g * P⁻¹) * c := hc.symm
      calc g * (P⁻¹ * c * P) = P⁻¹ * (P * g * P⁻¹) * c * P := by group
        _ = P⁻¹ * (c * (P * g * P⁻¹)) * P := by rw [h1]; group
        _ = P⁻¹ * c * P * g := by group
    have e : P⁻¹ * (c * j * c⁻¹) * P = (P⁻¹ * c * P) * (P⁻¹ * j * P) * (P⁻¹ * c * P)⁻¹ := by group
    rw [e]
    exact hnorm _ hc0 _ hj
  have hmem' : P * g * P⁻¹ ∈ K.map (MulAut.conj P).toMonoidHom :=
    core_diag hF hPd hd5 hg'1 hK'q hK'C hnorm' h41'
  rw [mem_conj_map'] at hmem'
  have e : P⁻¹ * (P * g * P⁻¹) * P = g := by group
  rw [e] at hmem'
  exact hmem'

end CFSG.LocalAnalysis.GLTheoremA.SFM12
