module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y01
public import CFSG.ClassicalInvolution.Asc77.AscB3C2
public import CFSG.ClassicalInvolution.Asc77.AscB3CG
public import CFSG.ClassicalInvolution.Q3.Q3WAPow

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.B3C
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped commutatorElement MatrixGroups

section Model

variable {F : Type} [Field F]

theorem R0_map_conj_blk (A B : SL(2, F)) :
    (R0 F).map (MulAut.conj (blk F A B)).toMonoidHom = R0 F := by
  have key : ∀ (A B : SL(2, F)) (x : StatedSp 2 F), x ∈ R0 F →
      blk F A B * x * (blk F A B)⁻¹ ∈ R0 F := by
    intro A B x hx
    obtain ⟨y, rfl⟩ := hx
    have h : blk F A B * longBlock F 2 0 y * (blk F A B)⁻¹ = longBlock F 2 0 (A * y * A⁻¹) := by
      have hcomm : longBlock F 2 1 B * longBlock F 2 0 y = longBlock F 2 0 y * longBlock F 2 1 B :=
        (longBlock_comm y B).symm
      calc blk F A B * longBlock F 2 0 y * (blk F A B)⁻¹
          = longBlock F 2 0 A * (longBlock F 2 1 B * longBlock F 2 0 y) *
              (longBlock F 2 1 B)⁻¹ * (longBlock F 2 0 A)⁻¹ := by
            simp only [blk, mul_inv_rev, mul_assoc]
        _ = longBlock F 2 0 A * (longBlock F 2 0 y * longBlock F 2 1 B) *
              (longBlock F 2 1 B)⁻¹ * (longBlock F 2 0 A)⁻¹ := by rw [hcomm]
        _ = longBlock F 2 0 (A * y * A⁻¹) := by
            simp only [map_mul, map_inv]
            group
    rw [h]
    exact ⟨_, rfl⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact key A B y hy
  · intro hx
    refine ⟨(blk F A B)⁻¹ * x * ((blk F A B)⁻¹)⁻¹, ?_, ?_⟩
    · have := key A⁻¹ B⁻¹ x hx
      rwa [← blk_inv] at this
    · show blk F A B * ((blk F A B)⁻¹ * x * ((blk F A B)⁻¹)⁻¹) * (blk F A B)⁻¹ = x
      group

theorem twin_plane0_eq (h2 : (2 : F) ≠ 0) {R : Subgroup (StatedSp 2 F)} {g c x : StatedSp 2 F}
    (hRg : R = (R0 F).map (MulAut.conj g).toMonoidHom) (hxR : x ∈ R) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hxc : x = c * x0 F * c⁻¹) : R = (R0 F).map (MulAut.conj c).toMonoidHom := by
  have hxg : x = g * x0 F * g⁻¹ := T7L.eq_conj_longInv h2 (k := 0) (hRg ▸ hxR) hx2 hx1
  have hIs : IsLongRootSp2 R x := ⟨0, g, hRg, hxg⟩
  have hIs' : IsLongRootSp2 ((R0 F).map (MulAut.conj c).toMonoidHom) x :=
    hxc ▸ (isLongRootSp2_standard (K := F) (n := 2) 0).conj c
  rw [hIs.eq_longRootGroup h2, hIs'.eq_longRootGroup h2]

theorem sp4_adapted_core_tw3 [Finite F] (h2 : (2 : F) ≠ 0) {c e : StatedSp 2 F}
    {Rp Rq : Subgroup (StatedSp 2 F)} (hRp : Rp = (R0' F).map (MulAut.conj c).toMonoidHom)
    (hRq : Rq = (R0 F).map (MulAut.conj c).toMonoidHom) (he : e = c * u0 F * c⁻¹) :
    ∃ c' : StatedSp 2 F, Rp = (longBlock F 2 1).range.map (MulAut.conj c'⁻¹).toMonoidHom ∧
      Rq = (longBlock F 2 0).range.map (MulAut.conj c'⁻¹).toMonoidHom ∧
      (twShort h2).range.map (MulAut.conj c'⁻¹).toMonoidHom ≤
        Subgroup.centralizer ({e} : Set (StatedSp 2 F)) := by
  obtain ⟨A₀, hA₀⟩ := ModelFacts.Orth15.InnerL4.exists_conj_r0 h2 (rho0 h2) (rho0_sq h2)
  obtain ⟨A₁, hA₁⟩ := ModelFacts.Orth15.InnerL4.exists_conj_r0 h2 (rho1 h2) (rho1_sq h2)
  set d : StatedSp 2 F := blk F A₀ A₁ with hd
  have hconj : (MulAut.conj (c * d⁻¹)).toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp (MulAut.conj d⁻¹).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have h1 : (d * c⁻¹)⁻¹ = c * d⁻¹ := by group
  refine ⟨d * c⁻¹, ?_, ?_, ?_⟩
  · have hmap : (longBlock F 2 1).range.map (MulAut.conj (d * c⁻¹)⁻¹).toMonoidHom =
        (R0' F).map (MulAut.conj c).toMonoidHom := by
      rw [h1, hconj, ← Subgroup.map_map]
      show ((R0' F).map (MulAut.conj d⁻¹).toMonoidHom).map _ = _
      rw [hd, blk_inv, T7Z.R0'_map_conj_blk]
    rw [hRp, hmap]
  · have hmap : (longBlock F 2 0).range.map (MulAut.conj (d * c⁻¹)⁻¹).toMonoidHom =
        (R0 F).map (MulAut.conj c).toMonoidHom := by
      rw [h1, hconj, ← Subgroup.map_map]
      show ((R0 F).map (MulAut.conj d⁻¹).toMonoidHom).map _ = _
      rw [hd, blk_inv, R0_map_conj_blk]
    rw [hRq, hmap]
  · rintro _ ⟨_, ⟨A', rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    set s : StatedSp 2 F := twShort h2 A' with hs
    set u' : StatedSp 2 F := blk F (rho0 h2) (rho1 h2) with hu'
    have hdu : d * u0 F * d⁻¹ = u' := by
      rw [hd, hu', u0_eq_blk, blk_inv, blk_mul, blk_mul, ← hA₀, ← hA₁]
    have h1' : d * u0 F = u' * d := by rw [← hdu]; group
    have h2'' : d⁻¹ * u' = u0 F * d⁻¹ := by rw [← hdu]; group
    have hcs : s * u' = u' * s := twShort_comm_dB h2 A'
    have hy : (MulAut.conj (d * c⁻¹)⁻¹).toMonoidHom s = c * d⁻¹ * s * d * c⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hy, he]
    calc c * d⁻¹ * s * d * c⁻¹ * (c * u0 F * c⁻¹)
        = c * d⁻¹ * s * (d * u0 F) * c⁻¹ := by group
      _ = c * d⁻¹ * s * (u' * d) * c⁻¹ := by rw [h1']
      _ = c * d⁻¹ * (s * u') * d * c⁻¹ := by group
      _ = c * d⁻¹ * (u' * s) * d * c⁻¹ := by rw [hcs]
      _ = c * (d⁻¹ * u') * s * d * c⁻¹ := by group
      _ = c * (u0 F * d⁻¹) * s * d * c⁻¹ := by rw [h2'']
      _ = c * u0 F * c⁻¹ * (c * d⁻¹ * s * d * c⁻¹) := by group


theorem sp4_adapted_tw3 [Finite F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    {a b : StatedSp 2 F} (ha : a ∈ R) (haa : a * a = x) (hb : b ∈ R') (hbb : b * b = x')
    (hab : a * b = b * a) :
    ∃ (c : StatedSp 2 F) (Rp Rq : Subgroup (StatedSp 2 F)),
      ((Rp = R ∧ Rq = R') ∨ (Rp = R' ∧ Rq = R)) ∧
      Rp = (longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom ∧
      Rq = (longBlock F 2 0).range.map (MulAut.conj c⁻¹).toMonoidHom ∧
      (twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom ≤
        Subgroup.centralizer ({a * b} : Set (StatedSp 2 F)) := by
  obtain ⟨g, k, hRg, hR'g⟩ := ModelFacts.Orth15.OuterSp4.twin_std_sp h2 hR hR' hne hxR hx2 hx1
    hx'R' hx'2 hx'1 hc
  fin_cases k
  · obtain ⟨c, hxc, habc⟩ := T7L.exists_conj_x0_u0_sp h2 hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 ha
      haa hb hbb
    have hp := T7Z.twin_plane1_eq h2 hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 hxc
    have hq := twin_plane0_eq h2 hRg hxR hx2 hx1 hxc
    obtain ⟨c', h1, h2', h3⟩ := sp4_adapted_core_tw3 h2 hp hq habc
    exact ⟨c', R', R, Or.inr ⟨rfl, rfl⟩, h1, h2', h3⟩
  · obtain ⟨c, hxc, habc⟩ := T7L.exists_conj_x0_u0_sp h2 hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hb
      hbb ha haa
    have hp := T7Z.twin_plane1_eq h2 hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hxc
    have hq := twin_plane0_eq h2 hR'g hx'R' hx'2 hx'1 hxc
    obtain ⟨c', h1, h2', h3⟩ := sp4_adapted_core_tw3 h2 hp hq (hab ▸ habc)
    exact ⟨c', R, R', Or.inl ⟨rfl, rfl⟩, h1, h2', h3⟩


theorem sq_eq_one_of_mem_center3 [Finite F] (hF : Nat.card F = 3) {n : StatedSp 2 F}
    (hn : n ∈ Subgroup.center (StatedSp 2 F)) : n * n = 1 := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hn
  obtain ⟨r, hr⟩ := hn
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card Fˣ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  have hr2 : r * r = 1 := by
    have := pow_card_eq_one' (G := Fˣ) (x := r)
    rwa [hcard, pow_two] at this
  have h1 : ((n * n : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [Subgroup.coe_mul, ← hr, ← map_mul, hr2, map_one]
  exact Subtype.ext h1

theorem not_three_dvd_orderOf_center3 [Finite F] (hF : Nat.card F = 3) {n : StatedSp 2 F}
    (hn : n ∈ Subgroup.center (StatedSp 2 F)) : ¬ 3 ∣ orderOf n := by
  intro h
  have h1 : orderOf n ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact sq_eq_one_of_mem_center3 hF hn)
  have := Nat.le_of_dvd (by norm_num) (h.trans h1)
  omega

theorem pow3_of_isLongRootSp2 [Finite F] (hF : Nat.card F = 3) {L : Subgroup (StatedSp 2 F)}
    {i : StatedSp 2 F} (h : IsLongRootSp2 L i) : Q3W.Pow3 L := by
  obtain ⟨k, g, rfl, -⟩ := h
  exact Q3W.Pow3.map _ (Q3W.pow3_range_sl2 hF (longBlock F 2 k))


theorem ySide_core_tw3 [Finite F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) = 0) (hF : Nat.card F = 3)
    {G : Type} [Group G] (ψ : StatedSp 2 F →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {c : StatedSp 2 F}
    {Rp Rq : Subgroup (StatedSp 2 F)}
    (hpl : Rp = (longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom)
    (hql : Rq = (longBlock F 2 0).range.map (MulAut.conj c⁻¹).toMonoidHom)
    (hinj : ∀ y ∈ Rp, ψ y = 1 → y = 1) {e : StatedSp 2 F}
    (hS : (twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({e} : Set (StatedSp 2 F))) :
    SymplecticPhanPair F h2 ψ.range (Rp.map ψ)
      (((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ) ∧
    ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ ≤
      Subgroup.centralizer ({ψ e} : Set G) ∧
    Q3W.Pow3 (((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ) ∧
    ψ.range ≤ Rp.map ψ ⊔ ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ ∧
    ∃ w ∈ ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ,
      conjSub w (Rp.map ψ) = Rq.map ψ := by
  have hmem : ∀ A : SL(2, F), c⁻¹ * longBlock F 2 1 A * c ∈ Rp := by
    intro A
    rw [hpl]
    exact ⟨longBlock F 2 1 A, ⟨A, rfl⟩, by simp⟩
  refine ⟨⟨ψ, c, rfl, hker, ?_, ?_, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro A B hAB
    have h1 : ψ ((c⁻¹ * longBlock F 2 1 A * c)⁻¹ * (c⁻¹ * longBlock F 2 1 B * c)) = 1 := by
      rw [map_mul, map_inv]
      have : ψ (c⁻¹ * longBlock F 2 1 A * c) = ψ (c⁻¹ * longBlock F 2 1 B * c) := by
        simpa [MonoidHom.comp_apply] using hAB
      rw [this, inv_mul_cancel]
    have h2' := hinj _ (Rp.mul_mem (Rp.inv_mem (hmem A)) (hmem B)) h1
    have h3' : c⁻¹ * longBlock F 2 1 A * c = c⁻¹ * longBlock F 2 1 B * c := inv_mul_eq_one.mp h2'
    exact longBlock_injective (1 : Fin 2) (by simpa using h3')
  · exact congrArg (Subgroup.map ψ) hpl.symm
  · rintro _ ⟨s, hs, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' := congrArg ψ h
    simpa only [map_mul] using h'
  · have hφ : ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom).map ψ =
        (ψ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (twShort h2))).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp]
    rw [hφ]
    exact Q3W.pow3_range_sl2 hF _
  · have htop : ((twShort h2).range.map (MulAut.conj c⁻¹).toMonoidHom) ⊔ Rp = ⊤ := by
      rw [hpl, ← Subgroup.map_sup, twShort_sup_longBlock h2, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (MulAut.conj c⁻¹).surjective
    rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup, sup_comm]
  · set s : StatedSp 2 F := swapElt3 h2 h3 with hs
    set w' : StatedSp 2 F := (MulAut.conj c⁻¹).toMonoidHom s with hw'
    refine ⟨ψ w', Subgroup.mem_map_of_mem ψ (Subgroup.mem_map_of_mem _ ⟨swapMat3 h3, rfl⟩), ?_⟩
    have hψ : (MulAut.conj (ψ w')).toMonoidHom.comp ψ =
        ψ.comp (MulAut.conj w').toMonoidHom := by
      ext y
      simp [MulAut.conj_apply, map_mul, map_inv]
    have hcomp : (MulAut.conj w').toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom =
        (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom := by
      ext y
      simp [hw', MulAut.conj_apply, mul_assoc]
    have hRq : Rp.map (MulAut.conj w').toMonoidHom = Rq := by
      rw [hpl, hql, Subgroup.map_map, hcomp, ← Subgroup.map_map, hs, swapElt3_conj h2 h3]
    unfold conjSub
    rw [Subgroup.map_map, hψ, ← Subgroup.map_map, hRq]

end Model


section Layer

variable {G : Type} [Group G]



theorem ySide_model_tw3 {Φ : Set (Subgroup G)} (P : T7Z.ModelLayer .PSp 2 3 1 Φ)
    {J J' : Subgroup G} {t a b : G} (hJ : J ∈ Φ) (hJ' : J' ∈ Φ)
    (eJ : Nonempty (↥J ≃* SL(2, GaloisField 3 1)))
    (eJ' : Nonempty (↥J' ≃* SL(2, GaloisField 3 1))) (hne : J ≠ J')
    (hcomm : Commutes J J') (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t)
    (ha : a ∈ J) (hb : b ∈ J') (haa : a * a = t) (hbb : b * b = t) :
    ∃ J₁ J₂ K₃ : Subgroup G, ((J₁ = J ∧ J₂ = J') ∨ (J₁ = J' ∧ J₂ = J)) ∧
      SymplecticPhanPair (GaloisField 3 1) (ModelFacts.two_ne_zero_galoisField 1 (by norm_num))
        (omegaGen Φ) J₁ K₃ ∧
      K₃ ≤ Subgroup.centralizer ({a * b} : Set G) ∧ Q3W.Pow3 K₃ ∧ omegaGen Φ ≤ J₁ ⊔ K₃ ∧
      K₃ ≤ omegaGen Φ ∧ ∃ w ∈ K₃, conjSub w J₁ = J₂ := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  have h3 : (3 : GaloisField 3 1) = 0 := by
    have := CharP.cast_eq_zero (GaloisField 3 1) 3
    exact_mod_cast this
  have hadm : StatedLieAdmissible .PSp 2 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 hp2
  have hfin : Finite (modelUniv .PSp 2 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (by trivial) hadm
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund J hJ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund J' hJ'
  have hi₁ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ hJR eJ
  have hi₂ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ' hJ'R eJ'
  have hlong : ∀ R : Subgroup (modelUniv .PSp 2 3 1 Fact.out).K,
      R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Fact.out).D →
        ∃ i, IsLongRootSp2 (K := GaloisField 3 1) (n := 2) R i :=
    fun R hR => (ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).1 hR
  have hpow : Q3W.Pow3 RJ := by
    obtain ⟨i, hi⟩ := hlong RJ hRJ
    exact pow3_of_isLongRootSp2 hF hi
  have hcop : ∀ n ∈ P.ψ.ker, ¬ 3 ∣ orderOf n :=
    fun n hn => not_three_dvd_orderOf_center3 hF (P.ker_le hn)
  obtain ⟨a₀, ha₀, hψa⟩ := (hJR ▸ ha : a ∈ RJ.map P.ψ)
  obtain ⟨b₀, hb₀, hψb⟩ := (hJ'R ▸ hb : b ∈ RJ'.map P.ψ)
  have hcomm' : Commutes RJ RJ' := by
    intro x hx y hy
    refine (Q3W.commutes_of_map_commute_exponent3 P.ψ P.ker_le hcop (A := RJ') (L := RJ) hpow
      ?_ y hy x hx).symm
    intro a' ha' l hl
    have := hcomm (P.ψ l) (hJR ▸ ⟨l, hl, rfl⟩) (P.ψ a') (hJ'R ▸ ⟨a', ha', rfl⟩)
    exact this.symm
  have hxR : a₀ * a₀ ∈ RJ := RJ.mul_mem ha₀ ha₀
  have hx'R : b₀ * b₀ ∈ RJ' := RJ'.mul_mem hb₀ hb₀
  have hψx : P.ψ (a₀ * a₀) = t := by rw [map_mul, hψa, haa]
  have hψx' : P.ψ (b₀ * b₀) = t := by rw [map_mul, hψb, hbb]
  have hx2 : (a₀ * a₀) * (a₀ * a₀) = 1 := hi₁ _ (RJ.mul_mem hxR hxR) (by
    rw [map_mul, hψx, htJ.sq])
  have hx'2 : (b₀ * b₀) * (b₀ * b₀) = 1 := hi₂ _ (RJ'.mul_mem hx'R hx'R) (by
    rw [map_mul, hψx', htJ'.sq])
  have hx1 : a₀ * a₀ ≠ 1 := fun h => htJ.ne_one (by rw [← hψx, h, map_one])
  have hx'1 : b₀ * b₀ ≠ 1 := fun h => htJ'.ne_one (by rw [← hψx', h, map_one])
  have hc : (b₀ * b₀) * (a₀ * a₀)⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField 3 1)) := by
    refine P.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψx, hψx', mul_inv_cancel]
  have hne' : RJ ≠ RJ' := by
    intro h
    apply hne
    rw [hJR, hJ'R, h]
  obtain ⟨c, Rp, Rq, hRpq, hpl, hql, hS⟩ := sp4_adapted_tw3 h2 (hlong RJ hRJ) (hlong RJ' hRJ') hne'
    hxR hx2 hx1 hx'R hx'2 hx'1 hc ha₀ rfl hb₀ rfl (hcomm' a₀ ha₀ b₀ hb₀)
  have hinj : ∀ y ∈ Rp, P.ψ y = 1 → y = 1 := by
    rcases hRpq with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      exact hi₁
    · rw [h]
      exact hi₂
  obtain ⟨hpair, hcent, hperfK, hgen, hw⟩ :=
    ySide_core_tw3 h2 h3 hF P.ψ P.ker_le hpl hql hinj hS
  have hψe : P.ψ (a₀ * b₀) = a * b := by rw [map_mul, hψa, hψb]
  refine ⟨Rp.map P.ψ, Rq.map P.ψ, _, ?_, ?_, ?_, hperfK, ?_, ?_, ?_⟩
  · rcases hRpq with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · left
      rw [h1, h2', hJR, hJ'R]
      exact ⟨rfl, rfl⟩
    · right
      rw [h1, h2', hJR, hJ'R]
      exact ⟨rfl, rfl⟩
  · rw [← P.range_eq]
    exact hpair
  · rw [← hψe]
    exact hcent
  · rw [← P.range_eq]
    exact hgen
  · rw [← P.range_eq]
    exact Subgroup.map_le_range _ _
  · exact hw

end Layer

end CFSG.ClassicalInvolution.Q3.Q3T7S23
