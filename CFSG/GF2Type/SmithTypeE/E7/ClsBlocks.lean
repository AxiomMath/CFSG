module

public import CFSG.GF2Type.SmithTypeE.E7.UwRankGeom

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod
open scoped Matrix

theorem zmod2_add_self_eq_zero : ∀ a : ZMod 2, a + a = 0 := by decide

theorem V12_add_self_eq_zero (w : V12) : w + w = 0 :=
  Prod.ext (funext fun i => zmod2_add_self_eq_zero _) (funext fun i => zmod2_add_self_eq_zero _)

theorem q12_eq_dot (x : V12) : q12 x = x.1 ⬝ᵥ x.2 := rfl

theorem dotProduct_mulVec_self_of_isAlt {N : M6} (hN : IsAlt N) (x : Fin 6 → ZMod 2) :
    x ⬝ᵥ (N *ᵥ x) = 0 := by
  have hsym : ∀ i j, N i j = N j i := fun i j => by
    have h := congrFun (congrFun hN.1 j) i
    simpa [Matrix.transpose_apply] using h
  have hrw : x ⬝ᵥ (N *ᵥ x) = ∑ p : Fin 6 × Fin 6, x p.1 * (N p.1 p.2 * x p.2) := by
    rw [Fintype.sum_prod_type]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hrw]
  refine Finset.sum_ninvolution Prod.swap (fun p => ?_) (fun p hp hsp => ?_)
    (fun p => Finset.mem_univ _) (fun p => Prod.swap_swap p)
  · obtain ⟨i, j⟩ := p
    show x i * (N i j * x j) + x j * (N j i * x i) = 0
    rw [← hsym i j]
    have h : x j * (N i j * x i) = x i * (N i j * x j) := by ring
    rw [h, zmod2_add_self_eq_zero]
  · obtain ⟨i, j⟩ := p
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hsp
    obtain ⟨rfl, -⟩ := hsp
    simp [hN.2] at hp

section Blocks

@[expose] def kNlin (N : M6) : V12 →ₗ[ZMod 2] V12 :=
  LinearMap.prod (LinearMap.fst (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2))
    (LinearMap.snd (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2) +
      Matrix.toLin' N ∘ₗ LinearMap.fst (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2))

theorem kNlin_apply (N : M6) (v : V12) : kNlin N v = (v.1, v.2 + N *ᵥ v.1) := rfl

theorem kNlin_kNlin (N : M6) (v : V12) : kNlin N (kNlin N v) = v := by
  obtain ⟨x, y⟩ := v
  have h2 : ∀ w : Fin 6 → ZMod 2, w + w = 0 := fun w => funext fun i => zmod2_add_self_eq_zero _
  simp only [kNlin_apply, add_assoc, h2, add_zero]

@[expose] noncomputable def kN (N : M6) : V12 ≃ₗ[ZMod 2] V12 :=
  LinearEquiv.ofInvolutive (kNlin N) (fun v => kNlin_kNlin N v)

theorem kN_apply (N : M6) (v : V12) : kN N v = (v.1, v.2 + N *ᵥ v.1) := rfl

theorem kN_zero : kN 0 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [kN_apply, Matrix.zero_mulVec, add_zero]
  rfl

theorem kN_add (N N' : M6) : kN N * kN N' = kN (N + N') := by
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply, kN_apply, Matrix.add_mulVec]
  congr 1
  abel

@[expose] noncomputable def sA (A : GL6) : V12 ≃ₗ[ZMod 2] V12 where
  toFun v := (((A⁻¹ : GL6) : M6)ᵀ *ᵥ v.1, (A : M6) *ᵥ v.2)
  invFun v := ((A : M6)ᵀ *ᵥ v.1, ((A⁻¹ : GL6) : M6) *ᵥ v.2)
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Matrix.mulVec_add]
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, Matrix.mulVec_smul, RingHom.id_apply]
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.one_mulVec, Prod.mk.eta]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.one_mulVec, Prod.mk.eta]

theorem sA_apply (A : GL6) (v : V12) :
    sA A v = (((A⁻¹ : GL6) : M6)ᵀ *ᵥ v.1, (A : M6) *ᵥ v.2) := rfl

theorem sA_symm_apply (A : GL6) (v : V12) :
    (sA A).symm v = ((A : M6)ᵀ *ᵥ v.1, ((A⁻¹ : GL6) : M6) *ᵥ v.2) := rfl

theorem sA_iso (A : GL6) (v : V12) : q12 (sA A v) = q12 v := by
  show (((A⁻¹ : GL6) : M6)ᵀ *ᵥ v.1) ⬝ᵥ ((A : M6) *ᵥ v.2) = v.1 ⬝ᵥ v.2
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Units.inv_mul,
    Matrix.vecMul_one]

theorem kN_iso {N : M6} (hN : IsAlt N) (v : V12) : q12 (kN N v) = q12 v := by
  show v.1 ⬝ᵥ (v.2 + N *ᵥ v.1) = v.1 ⬝ᵥ v.2
  rw [dotProduct_add, dotProduct_mulVec_self_of_isAlt hN, add_zero]

theorem eq_sA_kN {σ : V12 ≃ₗ[ZMod 2] V12} (hσ : ∀ x, q12 (σ x) = q12 x)
    (hF : ∀ y, (σ (0, y)).1 = 0) {A : GL6} (hA : (A : M6) = Ablk σ) :
    IsAlt (((A⁻¹ : GL6) : M6) * Sblk σ) ∧
      σ = sA A * kN (((A⁻¹ : GL6) : M6) * Sblk σ) := by
  obtain ⟨τ, hτ⟩ : ∃ τ : V12 ≃ₗ[ZMod 2] V12, ∀ v, τ v = (sA A).symm (σ v) :=
    ⟨σ.trans (sA A).symm, fun v => rfl⟩
  have hsτ : ∀ v, sA A (τ v) = σ v := fun v => by rw [hτ v, LinearEquiv.apply_symm_apply]
  have hτiso : ∀ x, q12 (τ x) = q12 x := fun x => by
    have h := sA_iso A (τ x)
    rw [hsτ x, hσ x] at h
    exact h.symm
  have hτF : FixesF τ := fun y => by
    rw [hτ, apply_F σ hF y, ← hA, sA_symm_apply]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  obtain ⟨N', hN'⟩ : ∃ N' : M6, ∀ x, (τ (x, 0)).2 = N' *ᵥ x :=
    ⟨LinearMap.toMatrix' (Mlin τ), fun x => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hNent : ∀ i j, N' i j = ent τ i j := by
    intro i j
    show N' i j = (τ (Pi.single j 1, 0)).2 i
    rw [hN' (Pi.single j 1), Matrix.mulVec_single_one]
    rfl
  have hN'alt : IsAlt N' := by
    refine ⟨Matrix.ext fun i j => ?_, fun i => ?_⟩
    · rw [Matrix.transpose_apply, hNent, hNent]
      exact (ent_comm hτiso hτF i j).symm
    · rw [hNent]
      exact ent_diag hτiso hτF i
  have hτk : ∀ v : V12, τ v = kN N' v := by
    rintro ⟨a, b⟩
    rw [fix_apply hτiso hτF a b, kN_apply, hN' a]
  have hσk : ∀ v, σ v = sA A (kN N' v) := fun v => by rw [← hτk v, hsτ v]
  have hSx : ∀ x : Fin 6 → ZMod 2, Sblk σ *ᵥ x = (A : M6) *ᵥ (N' *ᵥ x) := fun x => by
    rw [Sblk_mulVec, hσk (x, 0)]
    simp [sA_apply, kN_apply]
  have hS : Sblk σ = (A : M6) * N' := by
    ext i j
    have h := congrFun (hSx (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h
  have hN'eq : ((A⁻¹ : GL6) : M6) * Sblk σ = N' := by
    rw [hS, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨by rw [hN'eq]; exact hN'alt, ?_⟩
  rw [hN'eq]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply]
  exact hσk v

end Blocks

@[expose] def Wp : Submodule (ZMod 2) V12 where
  carrier := {v | (∀ i : Fin 6, i ≠ 5 → v.1 i = 0) ∧ v.2 5 = 0}
  add_mem' := fun {a b} ha hb => ⟨fun i hi => by simp [ha.1 i hi, hb.1 i hi], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨fun _ _ => rfl, rfl⟩
  smul_mem' := fun c v hv => ⟨fun i hi => by simp [hv.1 i hi], by simp [hv.2]⟩

@[expose] def Cc : Submodule (ZMod 2) V12 where
  carrier := {v | (∀ i : Fin 6, i ≠ 5 → v.1 i = 0) ∧ v.1 5 = v.2 5}
  add_mem' := fun {a b} ha hb => ⟨fun i hi => by simp [ha.1 i hi, hb.1 i hi], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨fun _ _ => rfl, rfl⟩
  smul_mem' := fun c v hv => ⟨fun i hi => by simp [hv.1 i hi], by simp [hv.2]⟩

section Cert

@[expose] def UFix (Y : Submodule (ZMod 2) V12) : Subgroup TD6 where
  carrier := {g | ∀ y ∈ Y, sig g y = y}
  mul_mem' := fun {a b} ha hb y hy => by
    rw [sig_mul, LinearEquiv.mul_apply, hb y hy, ha y hy]
  one_mem' := fun y _ => by rw [sig_one]; rfl
  inv_mem' := fun {a} ha y hy => by
    have h1 : sig a⁻¹ * sig a = 1 := by rw [← sig_mul, inv_mul_cancel, sig_one]
    have := congrArg (fun f : V12 ≃ₗ[ZMod 2] V12 => f y) h1
    simp only [LinearEquiv.mul_apply, ha y hy] at this
    exact this

theorem mem_UFix {Y : Submodule (ZMod 2) V12} {g : TD6} :
    g ∈ UFix Y ↔ ∀ y ∈ Y, sig g y = y := Iff.rfl

theorem sig_inv_apply_apply (c : TD6) (y : V12) : sig c⁻¹ (sig c y) = y := by
  have h := congrArg (fun g : TD6 => sig g y) (inv_mul_cancel c)
  simp only [sig_mul, LinearEquiv.mul_apply, sig_one, LinearEquiv.coe_one, id_eq] at h
  exact h

theorem isElementaryAbelian_UFix (Y : Submodule (ZMod 2) V12)
    (hY : ∀ v : V12, (∀ y ∈ Y, B12 v y = 0) → v ∈ Y) :
    CFSG.IsElementaryAbelian 2 (UFix Y) := by
  have hmove : ∀ g ∈ UFix Y, ∀ v : V12, sig g v + v ∈ Y := by
    intro g hg v
    apply hY
    intro y hy
    have h1 : B12 (sig g v) y = B12 v y := by
      have h := B12_of_isometry (iso_sig g) v y
      rwa [mem_UFix.mp hg y hy] at h
    rw [B12_add_left, h1, zmod2_add_self_eq_zero]
  have hkey : ∀ g ∈ UFix Y, ∀ h ∈ UFix Y, ∀ v : V12,
      sig g (sig h v) = sig g v + sig h v + v := by
    intro g hg h hh v
    have e : v + (sig h v + v) = sig h v := by
      rw [add_comm (sig h v) v, ← add_assoc, V12_add_self_eq_zero, zero_add]
    have hgd : sig g (sig h v + v) = sig h v + v := mem_UFix.mp hg _ (hmove h hh v)
    calc sig g (sig h v) = sig g (v + (sig h v + v)) := by rw [e]
      _ = sig g v + sig g (sig h v + v) := by rw [map_add]
      _ = sig g v + (sig h v + v) := by rw [hgd]
      _ = sig g v + sig h v + v := by rw [add_assoc]
  have hcomm : ∀ g ∈ UFix Y, ∀ h ∈ UFix Y, ∀ v : V12, sig g (sig h v) = sig h (sig g v) := by
    intro g hg h hh v
    rw [hkey g hg h hh v, hkey h hh g hg v]
    abel
  have hmul_comm : ∀ g ∈ UFix Y, ∀ h ∈ UFix Y, g * h = h * g := by
    intro g hg h hh
    apply sig_injective
    refine LinearEquiv.ext fun v => ?_
    rw [sig_mul, sig_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hcomm g hg h hh v
  have hsq : ∀ g ∈ UFix Y, g * g = 1 := by
    intro g hg
    apply sig_injective
    refine LinearEquiv.ext fun v => ?_
    rw [sig_mul, sig_one, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, hkey g hg g hg v,
      V12_add_self_eq_zero, zero_add]
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hmul_comm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_ }
  apply Subtype.ext
  show (g : TD6) ^ 2 = 1
  rw [pow_two]
  exact hsq g g.2

theorem card_UFix_le (Y : Submodule (ZMod 2) V12)
    (hY : ∀ v : V12, (∀ y ∈ Y, B12 v y = 0) → v ∈ Y) : Nat.card (UFix Y) ≤ 2 ^ 15 :=
  card_le_of_isElementaryAbelian_TD6 (UFix Y) (isElementaryAbelian_UFix Y hY)

theorem map_UFix (c : TD6) (Y : Submodule (ZMod 2) V12) :
    (UFix Y).map (MulAut.conj c).toMonoidHom = UFix (Y.map (sig c).toLinearMap) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩ y' hy'
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hy'
    show sig (c * h * c⁻¹) (sig c y) = sig c y
    rw [sig_mul, sig_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, sig_inv_apply_apply,
      mem_UFix.mp hh y hy]
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, ?_⟩
    · intro y hy
      show sig (c⁻¹ * g * c) y = y
      rw [sig_mul, sig_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        mem_UFix.mp hg (sig c y) (Submodule.mem_map_of_mem hy), sig_inv_apply_apply]
    · show c * (c⁻¹ * g * c) * c⁻¹ = g
      group

theorem sig_tvP (p : Fin 365211) : sig ⟨tvP p, tvP_mem p⟩ = siegelK p.val := by
  have hsym : omegaTD6.symm ⟨tvP p, tvP_mem p⟩ = ⟨siegelK p.val, siegelK_mem_omega p.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (omegaTD6_siegelK p).symm
  show (omegaTD6.symm ⟨tvP p, tvP_mem p⟩).1 = siegelK p.val
  rw [hsym]

theorem exists_line_siegel {u w : V12} (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w)
    (h : TsPair u w) : ∃ p : Fin 365211, lineSet p.val = lineOfPair u w ∧
      sig ⟨tvP p, tvP_mem p⟩ = siegelEquiv u w := by
  obtain ⟨hq1, hq2, hb⟩ := h
  obtain ⟨x, hx⟩ : ∃ x, x = enc12 u := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = enc12 w := ⟨_, rfl⟩
  have hxu : dec12 x = u := by rw [hx, dec12_enc12]
  have hyw : dec12 y = w := by rw [hy, dec12_enc12]
  have hx4 : x < 4096 := by rw [hx]; exact enc12_lt u
  have hy4 : y < 4096 := by rw [hy]; exact enc12_lt w
  have hx0 : x ≠ 0 := fun h0 => hu (by rw [← hxu, h0, dec12_zero])
  have hy0 : y ≠ 0 := fun h0 => hw (by rw [← hyw, h0, dec12_zero])
  have hqx : qf x = false := bit_inj (qf x) false (by rw [← q12_dec12, hxu, hq1]; rfl)
  have hqy : qf y = false := bit_inj (qf y) false (by rw [← q12_dec12, hyw, hq2]; rfl)
  have hxy : x ≠ y := fun h0 => huw (by rw [← hxu, ← hyw, h0])
  have hb' : bf x y = false := bit_inj (bf x y) false (by rw [← B12_dec12, hxu, hyw, hb]; rfl)
  obtain ⟨hlt, hset⟩ := lineSet_lineIdx3 hx4 hy4 hx0 hy0 hqx hqy hxy hb'
  obtain ⟨p, hpv⟩ : ∃ p : Fin 365211, p.val = lineIdx3 x y (x ^^^ y) := ⟨⟨_, hlt⟩, rfl⟩
  have hset' : lineSet p.val = lineOfPair u w := by rw [hpv, hset, hxu, hyw]
  refine ⟨p, hset', ?_⟩
  rw [sig_tvP]
  obtain ⟨hu', hw', huw'⟩ := linePair_ne p.2
  exact (siegelEquiv_eq_of_lineOfPair_eq ⟨hq1, hq2, hb⟩ (tsPair_linePair p.2) hu hw huw hu' hw'
    huw' hset'.symm).symm

theorem tsPair_F {i j : Fin 6} (hij : i ≠ j) :
    TsPair ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2))
      ((0 : Fin 6 → ZMod 2), (Pi.single j 1 : Fin 6 → ZMod 2)) := by
  refine ⟨by simp [q12_eq_dot], by simp [q12_eq_dot], ?_⟩
  simp [B12]

theorem F_single_ne_zero (i : Fin 6) :
    ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2)) ≠ 0 := by
  intro h
  have := congrArg (fun v : V12 => v.2 i) h
  simp at this

theorem F_single_ne {i j : Fin 6} (hij : i ≠ j) :
    ((0 : Fin 6 → ZMod 2), (Pi.single j 1 : Fin 6 → ZMod 2)) ≠
      ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2)) := by
  intro h
  have := congrArg (fun v : V12 => v.2 i) h
  simp [Pi.single_apply, hij] at this

theorem E_single_ne_zero (j : Fin 6) :
    ((Pi.single j 1 : Fin 6 → ZMod 2), (0 : Fin 6 → ZMod 2)) ≠ 0 := by
  intro h
  have := congrArg (fun v : V12 => v.1 j) h
  simp at this

@[expose] def altE (i j : Fin 6) : M6 := Matrix.single i j 1 + Matrix.single j i 1

theorem B12_F_right (x y : Fin 6 → ZMod 2) (j : Fin 6) :
    B12 (x, y) (0, Pi.single j 1) = x j := by
  simp [B12, Pi.single_apply]

theorem altE_mulVec_apply (i j : Fin 6) (x : Fin 6 → ZMod 2) (k : Fin 6) :
    (altE i j *ᵥ x) k = (if k = i then x j else 0) + (if k = j then x i else 0) := by
  simp only [altE, Matrix.add_mulVec, Pi.add_apply]
  rw [Matrix.single_mulVec, Matrix.single_mulVec]
  simp [Function.update_apply]

theorem altE_mulVec {i j : Fin 6} (hij : i ≠ j) (x : Fin 6 → ZMod 2) :
    altE i j *ᵥ x = x j • Pi.single i 1 + x i • Pi.single j 1 := by
  funext k
  rw [altE_mulVec_apply]
  rcases eq_or_ne k i with rfl | hki <;> rcases eq_or_ne k j with rfl | hkj <;>
    simp_all [Pi.single_apply, hij, hij.symm]

theorem kN_altE {i j : Fin 6} (hij : i ≠ j) :
    kN (altE i j) = siegelEquiv (0, Pi.single i 1) (0, Pi.single j 1) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, y⟩ := v
  rw [siegelEquiv_apply (tsPair_F hij), kN_apply]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [B12_F_right, altE_mulVec hij, Prod.snd_add, Prod.smul_snd, add_assoc]

theorem exists_K0_kN_altE {i j : Fin 6} (hij : i ≠ j) : ∃ g ∈ K0, sig g = kN (altE i j) := by
  obtain ⟨p, hp, hsig⟩ := exists_line_siegel (F_single_ne_zero i) (F_single_ne_zero j)
    (F_single_ne hij.symm) (tsPair_F hij)
  refine ⟨⟨tvP p, tvP_mem p⟩, tvP_mem_K0 ?_, ?_⟩
  · intro x hx
    rw [hp] at hx
    simp only [lineOfPair, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_F_iff.mpr (by simp)
    · exact mem_F_iff.mpr (by simp)
    · exact mem_F_iff.mpr (by simp)
  · rw [hsig, kN_altE hij]

theorem ite_mul_ite_aux (a b i j : Fin 6) :
    (if j = b then (1 : ZMod 2) else 0) * (if a = i then 1 else 0) =
      if i = a ∧ j = b then 1 else 0 := by
  by_cases h1 : j = b <;> by_cases h2 : a = i
  · subst h2
    subst h1
    simp
  · have h3 : ¬ (i = a ∧ j = b) := fun h => h2 h.1.symm
    have h4 : i ≠ a := fun h => h2 h.symm
    simp [h1, h2, h3, h4]
  · have h3 : ¬ (i = a ∧ j = b) := fun h => h1 h.2
    simp [h1, h2, h3]
  · have h3 : ¬ (i = a ∧ j = b) := fun h => h1 h.2
    simp [h1, h2, h3]

theorem single_mul_single_eq_zero {i j : Fin 6} (hij : i ≠ j) (k : Fin 6) :
    (Pi.single j 1 : Fin 6 → ZMod 2) k * (Pi.single i 1 : Fin 6 → ZMod 2) k = 0 := by
  by_cases hk : k = j
  · subst hk
    simp [Pi.single_apply, hij.symm]
  · simp [Pi.single_apply, hk]

theorem tsPair_levi {i j : Fin 6} (hij : i ≠ j) :
    TsPair ((Pi.single j 1 : Fin 6 → ZMod 2), (0 : Fin 6 → ZMod 2))
      ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2)) := by
  refine ⟨by simp [q12_eq_dot], by simp [q12_eq_dot], ?_⟩
  simp [B12, single_mul_single_eq_zero hij]

theorem Ablk_siegel_levi {i j : Fin 6} (hij : i ≠ j) :
    Ablk (siegelEquiv ((Pi.single j 1 : Fin 6 → ZMod 2), (0 : Fin 6 → ZMod 2))
      ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2))) =
      Matrix.transvection i j 1 := by
  have hts := tsPair_levi hij
  ext a b
  rw [Ablk_apply, siegelEquiv_apply hts]
  have hB1 : B12 ((0 : Fin 6 → ZMod 2), (Pi.single b 1 : Fin 6 → ZMod 2))
      ((0 : Fin 6 → ZMod 2), (Pi.single i 1 : Fin 6 → ZMod 2)) = 0 := by
    simp [B12]
  have hB2 : B12 ((0 : Fin 6 → ZMod 2), (Pi.single b 1 : Fin 6 → ZMod 2))
      ((Pi.single j 1 : Fin 6 → ZMod 2), (0 : Fin 6 → ZMod 2)) =
        (Pi.single b 1 : Fin 6 → ZMod 2) j := by
    simp only [B12, Prod.fst, Prod.snd, Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add,
      Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero]
    by_cases h : b = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hB1, hB2]
  simp only [zero_smul, add_zero, zero_add, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Pi.single_apply]
  rw [ite_mul_ite_aux]

theorem mem_Stab0_of_invol {g : TD6} (hF : ∀ y, (sig g (0, y)).1 = 0)
    (hinv : ∀ v, sig g (sig g v) = v) : g ∈ Stab0 := by
  rw [mem_Stab0]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ planeSub 0 := hx
    rw [mem_F_iff] at hx'
    have hx0 : x = (0, x.2) := Prod.ext hx' rfl
    rw [mem_F_iff]
    show (sig g x).1 = 0
    rw [hx0]
    exact hF _
  · intro x hx
    have hx' : x ∈ planeSub 0 := hx
    rw [mem_F_iff] at hx'
    have hx0 : x = (0, x.2) := Prod.ext hx' rfl
    refine ⟨sig g x, ?_, hinv x⟩
    show sig g x ∈ planeSub 0
    rw [mem_F_iff]
    show (sig g x).1 = 0
    rw [hx0]
    exact hF _

theorem exists_stab0_levi {i j : Fin 6} (hij : i ≠ j) :
    ∃ g ∈ Stab0, Ablk (sig g) = Matrix.transvection i j 1 := by
  have hts := tsPair_levi hij
  have huw : (Pi.single j 1, (0 : Fin 6 → ZMod 2)) ≠ ((0 : Fin 6 → ZMod 2), Pi.single i 1) := by
    intro h
    have := congrArg (fun v : V12 => v.1 j) h
    simp at this
  obtain ⟨p, -, hsig⟩ := exists_line_siegel (E_single_ne_zero j) (F_single_ne_zero i) huw hts
  have hinv : ∀ v, sig ⟨tvP p, tvP_mem p⟩ (sig ⟨tvP p, tvP_mem p⟩ v) = v := by
    intro v
    rw [hsig]
    have h := congrArg (fun f : V12 ≃ₗ[ZMod 2] V12 => f v) (siegelEquiv_mul_self hts)
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] using h
  have hF : ∀ y, (sig ⟨tvP p, tvP_mem p⟩ (0, y)).1 = 0 := by
    intro y
    rw [hsig, siegelEquiv_apply hts]
    simp [B12]
  refine ⟨⟨tvP p, tvP_mem p⟩, mem_Stab0_of_invol hF hinv, ?_⟩
  rw [hsig, Ablk_siegel_levi hij]

theorem exists_mem_stab0_Ablk_eq (A : GL6) : ∃ g ∈ Stab0, Ablk (sig g) = A := by
  have key : ∀ M : M6, Matrix.det M ≠ 0 → ∃ g ∈ Stab0, Ablk (sig g) = M := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M : M6 => ∃ g ∈ Stab0, Ablk (sig g) = M) M hM ?_ ?_ ?_
    · intro D hD
      have hD1 : D = 1 := by
        funext i
        rw [Matrix.det_diagonal] at hD
        have hi := Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
        exact (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hi
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hD1, Matrix.diagonal_one', sig_one, Ablk_one]
    · intro t
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) t.c with hc | hc
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [sig_one, Ablk_one]
        show (1 : M6) = Matrix.transvection t.i t.j t.c
        rw [hc, Matrix.transvection_zero]
      · obtain ⟨g, hg, hgt⟩ := exists_stab0_levi t.hij
        refine ⟨g, hg, ?_⟩
        show Ablk (sig g) = Matrix.transvection t.i t.j t.c
        rw [hgt, hc]
    · intro B C _ _ hB hC
      obtain ⟨g, hg, hgB⟩ := hB
      obtain ⟨h, hh, hhC⟩ := hC
      refine ⟨g * h, Subgroup.mul_mem _ hg hh, ?_⟩
      rw [sig_mul, Ablk_mul _ _ (stab_F hh), hgB, hhC]
  have hdet : Matrix.det (A : M6) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  exact key _ hdet

theorem sum_altE_apply (s : Finset (Fin 6 × Fin 6)) (i j : Fin 6) :
    (∑ p ∈ s, altE p.1 p.2) i j =
      (if (i, j) ∈ s then 1 else 0) + (if (j, i) ∈ s then 1 else 0) := by
  rw [Matrix.sum_apply]
  simp only [altE, Matrix.add_apply, Matrix.single_apply, Finset.sum_add_distrib]
  congr 1
  · have hc : ∀ p : Fin 6 × Fin 6, (p.1 = i ∧ p.2 = j) ↔ p = (i, j) := fun p => by
      simp [Prod.ext_iff]
    simp only [hc, Finset.sum_ite_eq']
  · have hc : ∀ p : Fin 6 × Fin 6, (p.2 = i ∧ p.1 = j) ↔ p = (j, i) := fun p => by
      simp [Prod.ext_iff, and_comm]
    simp only [hc, Finset.sum_ite_eq']

theorem ent_kN (N : M6) (i j : Fin 6) : ent (kN N) i j = N i j := by
  show (kN N ((Pi.single j 1 : Fin 6 → ZMod 2), (0 : Fin 6 → ZMod 2))).2 i = N i j
  rw [kN_apply]
  simp [Matrix.mulVec_single_one]

theorem exists_K0_sig_sum (s : Finset (Fin 6 × Fin 6)) (hs : ∀ p ∈ s, p.1 < p.2) :
    ∃ g ∈ K0, sig g = kN (∑ p ∈ s, altE p.1 p.2) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, by rw [Finset.sum_empty, kN_zero, sig_one]⟩
  | @insert p s hp ih =>
    obtain ⟨g, hg, hgs⟩ := ih fun q hq => hs q (Finset.mem_insert_of_mem hq)
    obtain ⟨h, hh, hhp⟩ := exists_K0_kN_altE (ne_of_lt (hs p (Finset.mem_insert_self p s)))
    refine ⟨g * h, Subgroup.mul_mem _ hg hh, ?_⟩
    rw [sig_mul, hgs, hhp, kN_add, Finset.sum_insert hp, add_comm]

theorem exists_K0_ent (c : {p : Fin 6 × Fin 6 // p.1 < p.2} → ZMod 2) :
    ∃ g ∈ K0, ∀ p : {p : Fin 6 × Fin 6 // p.1 < p.2}, ent (sig g) p.1.1 p.1.2 = c p := by
  obtain ⟨c', hc'⟩ : ∃ c' : Fin 6 × Fin 6 → ZMod 2,
      ∀ p : Fin 6 × Fin 6, c' p = if h : p.1 < p.2 then c ⟨p, h⟩ else 0 :=
    ⟨fun p => if h : p.1 < p.2 then c ⟨p, h⟩ else 0, fun p => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin 6 × Fin 6), s = Finset.univ.filter (fun p => c' p = 1) :=
    ⟨_, rfl⟩
  have hmem : ∀ q, q ∈ s ↔ c' q = 1 := fun q => by
    rw [hs, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hlt : ∀ p ∈ s, p.1 < p.2 := by
    intro p hp
    rw [hmem] at hp
    by_contra hlt
    rw [hc', dif_neg hlt] at hp
    exact zero_ne_one hp
  obtain ⟨g, hg, hgs⟩ := exists_K0_sig_sum s hlt
  refine ⟨g, hg, fun p => ?_⟩
  have h1 : c' (p.1.1, p.1.2) = c p := by
    rw [hc']
    exact dif_pos p.2
  have h2 : c' (p.1.2, p.1.1) = 0 := by
    rw [hc']
    exact dif_neg (not_lt.mpr (le_of_lt p.2))
  rw [hgs, ent_kN, sum_altE_apply]
  simp only [hmem, h1, h2]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (c p) with h | h <;> simp [h]

theorem card_upPair_fun :
    Nat.card ({p : Fin 6 × Fin 6 // p.1 < p.2} → ZMod 2) = 2 ^ 15 := by
  rw [Nat.card_fun, Nat.card_zmod]
  have : Nat.card {p : Fin 6 × Fin 6 // p.1 < p.2} = 15 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [this]

theorem card_K0 : Nat.card K0 = 2 ^ 15 := by
  refine le_antisymm card_K0_le ?_
  have hsurj : Function.Surjective
      (fun g : K0 => fun p : {p : Fin 6 × Fin 6 // p.1 < p.2} => ent (sig g.1) p.1.1 p.1.2) := by
    intro c
    obtain ⟨g, hg, hgc⟩ := exists_K0_ent c
    exact ⟨⟨g, hg⟩, funext hgc⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [card_upPair_fun] at h

end Cert

end CFSG.GF2Type.SmithTypeE.E7
