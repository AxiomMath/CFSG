module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bR23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Transport
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.LocalAnalysis.GLTheoremA.CatB CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.Fischer Matrix

namespace U52E81

theorem card_units_F4 : Nat.card F4ˣ = 3 := by
  rw [Nat.card_units, hF4card]
  norm_num

theorem unit_cube (u : F4ˣ) : u ^ 3 = 1 := by
  have := pow_card_eq_one' (G := F4ˣ) (x := u)
  rwa [card_units_F4] at this

@[expose] def diagG : (Fin 5 → F4ˣ) →* GL (Fin 5) F4 where
  toFun d := ⟨diagonal fun i => (d i : F4), diagonal fun i => ((d i)⁻¹ : F4ˣ), by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => Units.mul_inv _), by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => Units.inv_mul _)⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    change diagonal (fun i => ((a * b) i : F4)) = diagonal (fun i => (a i : F4)) *
      diagonal (fun i => (b i : F4))
    rw [diagonal_mul_diagonal]
    rfl)

theorem coe_diagG (d : Fin 5 → F4ˣ) :
    ((diagG d : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) = diagonal fun i => (d i : F4) :=
  rfl

@[expose] def entries : (Fin 4 → F4ˣ) →* (Fin 5 → F4ˣ) where
  toFun s := ![s 0, s 1, s 2, s 3, (s 0 * s 1 * s 2 * s 3)⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' s t := by
    funext i
    fin_cases i <;> simp [mul_inv, mul_comm, mul_left_comm, mul_assoc]

@[expose] def diag5 : (Fin 4 → F4ˣ) →* GL (Fin 5) F4 := diagG.comp entries

theorem diag5_mem (s : Fin 4 → F4ˣ) : diag5 s ∈ StatedSU 5 (2 ^ 1) F4 := by
  rw [mem_M5_iff]
  have hc : ((diag5 s : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
      diagonal fun i => (entries s i : F4) := rfl
  refine ⟨?_, ?_⟩
  · rw [hc, det_diagonal, ← Units.coe_prod]
    have : ∏ i, entries s i = 1 := by
      simp [Fin.prod_univ_five, entries]
    rw [this, Units.val_one]
  · rw [hc, diagonal_map (f := fun x : F4 => x ^ 2 ^ 1) sq_zero_one.1, diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    refine congrArg diagonal (funext fun i => ?_)
    have h3 := unit_cube (entries s i)
    have h4 : ((entries s i : F4ˣ) : F4) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    rw [← h4]
    ring

@[expose] noncomputable def psi : (Fin 4 → F4ˣ) →* M5 :=
  MonoidHom.codRestrict diag5 (StatedSU 5 (2 ^ 1) F4) diag5_mem

theorem psi_injective : Function.Injective psi := by
  intro s t h
  have h1 : diag5 s = diag5 t := congrArg Subtype.val h
  funext i
  have h2 := congrArg (fun A : GL (Fin 5) F4 => (A : Matrix (Fin 5) (Fin 5) F4) i.castSucc i.castSucc) h1
  simp only [diag5, MonoidHom.comp_apply, coe_diagG, diagonal_apply_eq] at h2
  apply Units.ext
  have : ((entries s i.castSucc : F4ˣ) : F4) = ((entries t i.castSucc : F4ˣ) : F4) := h2
  fin_cases i <;> simpa [entries] using this

@[expose] noncomputable def E81 : Subgroup M5 := psi.range

theorem E81_isElemAbelian : IsElemAbelian 3 E81 := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : M5) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨v, rfl⟩ := hx
    rw [← map_pow]
    have : v ^ 3 = 1 := funext fun i => unit_cube (v i)
    rw [this, map_one]

theorem card_E81 : Nat.card E81 = 3 ^ 4 := by
  rw [E81, ← Nat.card_congr (MonoidHom.ofInjective psi_injective).toEquiv, Nat.card_fun, card_units_F4,
    Nat.card_fin]

end U52E81

theorem exists_e81_of_catalog_u52 {S : Type} [Group S] (h : catalogIs S S9.isU5two) :
    ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  obtain ⟨e⟩ := bridge_u5two_stated h
  refine ⟨U52E81.E81.map e.symm.toMonoidHom, ?_, ?_⟩
  · exact S9.l94t_isElemAbelian_map _ U52E81.E81_isElemAbelian
  · rw [Subgroup.card_map_of_injective e.symm.injective, U52E81.card_E81]

theorem card_mulAut_u52 {S : Type} [Group S] (h : catalogIs S S9.isU5two) :
    Nat.card (MulAut S) = 13685760 * 2 := by
  obtain ⟨e⟩ := bridge_u5two h
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.card_mulAut_SU52,
    (CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.card_SU52).1]

section Prime3

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_u52 (hR : Rank23At Y) {K B : Subgroup Y} (h : KHyp 3 K B)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < 3 ^ 3)
    (hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU5two) : False := by
  have hlist : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isList94 := by
    obtain ⟨i, hi, e⟩ := hcat
    exact ⟨i, Or.inr (Or.inr (Or.inr hi)), e⟩
  obtain ⟨hZP, hZ, hRb⟩ := rank23_data hR h hlist
  have hout := forall_cube_inner_of_catalog h hZP hcat fun S _ hS => not_three_dvd_outer_u5two hS
  have hin := hin_of_cube_inner h hout
  have hcatK : catalogIs ↥K S9.isU5two := ys03_catalogIs_of_mulEquiv (mulEquivQuotCenter hZ).symm hcat
  obtain ⟨E₀, hE₀el, hE₀c⟩ := exists_e81_of_catalog_u52 hcatK
  refine false_of_inner h hZ hin hRb ⟨E₀.map K.subtype, Subgroup.map_subtype_le E₀,
    S9.l94t_isElemAbelian_map _ hE₀el, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, hE₀c]
  norm_num

end Prime3

theorem kDescFam_u52 (hR : ∀ (Y : Type) [Group Y] [Finite Y], Rank23At Y) (p : ℕ) :
    KDescFam p fU52 := by
  intro hp hp2 Y _ _ K B h hc hcB
  have hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU5two := hc
  by_cases hp3 : p = 3
  · subst hp3
    exact (false_of_u52 (hR Y) h hcB hcat).elim
  · refine (false_of_not_sq_dvd hp h hcB (MulEquiv.refl _) fun hdvd => ?_).elim
    rw [card_mulAut_u52 hcat] at hdvd
    exact not_sq_dvd_of_dvd_smooth_mul (a := 11) (b := 5) (M := 5 * 11) hp hp2 hp3
      (squarefree_prime_mul (by norm_num) (by norm_num) (by norm_num)) (by norm_num) hdvd

end CFSG.LocalAnalysis.GLTheoremA
