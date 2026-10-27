module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {F : Type} [Field F]

@[expose] def preGL (W : Subgroup (StatedProj (StatedSp 2 F))) :
    Subgroup (GL (Fin 2 ⊕ Fin 2) F) :=
  (W.comap (proj 2 F)).map (StatedSp 2 F).subtype

@[expose] def IsPElt (p : ℕ) (W : Subgroup (StatedProj (StatedSp 2 F)))
    (x : GL (Fin 2 ⊕ Fin 2) F) : Prop :=
  x ∈ preGL W ∧ ∃ n : ℕ, x ^ p ^ n = 1

@[expose] def fixSp (p : ℕ) (W : Subgroup (StatedProj (StatedSp 2 F))) :
    Submodule F (Fin 2 ⊕ Fin 2 → F) where
  carrier := {v | ∀ x, IsPElt p W x →
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v = v}
  zero_mem' := fun x _ => mulVec_zero _
  add_mem' := fun ha hb x hx => by rw [mulVec_add, ha x hx, hb x hx]
  smul_mem' := fun c v hv x hx => by rw [mulVec_smul, hv x hx]

@[expose] def comSp (p : ℕ) (W : Subgroup (StatedProj (StatedSp 2 F))) :
    Submodule F (Fin 2 ⊕ Fin 2 → F) :=
  Submodule.span F {w | ∃ x v, IsPElt p W x ∧
    w = (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v}

variable {p : ℕ} {W : Subgroup (StatedProj (StatedSp 2 F))}

theorem isPElt_conj {A : GL (Fin 2 ⊕ Fin 2) F}
    (hA : A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set _))
    {x : GL (Fin 2 ⊕ Fin 2) F} (hx : IsPElt p W x) : IsPElt p W (A * x * A⁻¹) := by
  obtain ⟨hxW, n, hn⟩ := hx
  exact ⟨(Subgroup.mem_normalizer_iff.mp hA x).mp hxW, n, by rw [conj_pow, hn]; group⟩

theorem mulVec_mem_fixSp {A : GL (Fin 2 ⊕ Fin 2) F}
    (hA : A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set _))
    {v : Fin 2 ⊕ Fin 2 → F} (hv : v ∈ fixSp p W) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ fixSp p W := by
  intro x hx
  have h1 := hv _ (isPElt_conj (inv_mem hA) hx)
  rw [inv_inv] at h1
  have e : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (A : Matrix _ _ F) =
      (A : Matrix _ _ F) * ((A⁻¹ * x * A : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) := by
    rw [← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [mulVec_mulVec, e, ← mulVec_mulVec, h1]

theorem mulVec_mem_comSp {A : GL (Fin 2 ⊕ Fin 2) F}
    (hA : A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set _))
    {v : Fin 2 ⊕ Fin 2 → F} (hv : v ∈ comSp p W) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ comSp p W := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, u, hx, rfl⟩ := hw
    refine Submodule.subset_span ⟨A * x * A⁻¹, (A : Matrix _ _ F) *ᵥ u, isPElt_conj hA hx, ?_⟩
    rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel_right]
  | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ c ha

theorem pairedSympForm_fixSp_comSp {u v : Fin 2 ⊕ Fin 2 → F} (hu : u ∈ fixSp p W)
    (hv : v ∈ comSp p W) : pairedSympForm F 2 u v = 0 := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, rfl⟩ := hw
    have hux := hu x hx
    obtain ⟨s, -, rfl⟩ := hx.1
    have hux' : ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ u =
      u := hux
    have hs := pairedSympForm_mulVec s u y
    rw [hux'] at hs
    show pairedSympForm F 2 u
      (((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ y - y) = 0
    rw [map_sub, hs, sub_self]
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

variable [Finite F]

variable [Fact p.Prime] [CharP F p]

omit [Finite F] in
theorem spScalars_mul_self {s : StatedSp 2 F} (hs : s ∈ spScalars 2 F) : s * s = 1 := by
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hs :)
  have hsp := SymplecticTorusWeyl.mem_statedSp_iff.mp s.2
  have hc2 : (c : F) * c = 1 := by
    have := congrFun (congrFun hsp (Sum.inl 0)) (Sum.inr 0)
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at this
    simpa [Matrix.scalar_apply] using this
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
  simp [Matrix.scalar_apply, hc2]

omit [CharP F p] in
theorem isNilpotent_comap (hWp : IsPGroup p ↥W) : Group.IsNilpotent ↥(W.comap (proj 2 F)) := by
  have : Group.IsNilpotent ↥W := hWp.isNilpotent
  let f : ↥(W.comap (proj 2 F)) →* ↥W :=
    ((proj 2 F).comp (W.comap (proj 2 F)).subtype).codRestrict W fun x => x.2
  refine Subgroup.isNilpotent_of_ker_le_center f fun x hx => ?_
  have hx1 : proj 2 F (x : StatedSp 2 F) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hxs : (x : StatedSp 2 F) ∈ spScalars 2 F := by rw [← ker_proj]; exact hx1
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hxs :)
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  exact ((Matrix.scalar_commute (c : F) (fun _ => Commute.all _ _) _).eq).symm

theorem exists_ne_zero_mem (hp2 : p ≠ 2) (hW : W ≠ ⊥) (hWp : IsPGroup p ↥W) :
    ∃ v ∈ fixSp p W ⊓ comSp p W, v ≠ 0 := by
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  obtain ⟨g, hg⟩ := proj_surjective (w : StatedProj (StatedSp 2 F))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWp
  have hwn : (w : StatedProj (StatedSp 2 F)) ^ p ^ n = 1 := by
    have : w ^ Nat.card ↥W = 1 := pow_card_eq_one'
    rw [hn] at this
    exact congrArg Subtype.val this
  set x : GL (Fin 2 ⊕ Fin 2) F := ((g * g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) with hxdef
  have hgW : proj 2 F g ∈ W := hg ▸ w.2
  have hxW : x ∈ preGL W := ⟨g * g, by
    show proj 2 F (g * g) ∈ W
    rw [map_mul]; exact mul_mem hgW hgW, rfl⟩
  have hgs : g ^ p ^ n ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_pow, hg, hwn]
  have hxp : x ^ p ^ n = 1 := by
    have h1 : (g * g) ^ p ^ n = 1 := by
      rw [(Commute.refl g).mul_pow, spScalars_mul_self hgs]
    rw [hxdef, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hx1 : x ≠ 1 := by
    intro h
    have hgg : g * g = 1 := Subtype.ext h
    have hww : (w : StatedProj (StatedSp 2 F)) * w = 1 := by
      rw [← hg, ← map_mul, hgg, map_one]
    have hd2 : orderOf (w : StatedProj (StatedSp 2 F)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hww)
    have hdp : orderOf (w : StatedProj (StatedSp 2 F)) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hwn
    have hcop : Nat.Coprime 2 (p ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hdp
    exact hw1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hD : ∃ v, (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx1
    apply Units.ext
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simp only [Pi.sub_apply, mulVec_single_one, Pi.zero_apply, sub_eq_zero, Matrix.col_apply]
      at this
    rw [Units.val_one, Matrix.one_apply, this, Pi.single_apply]
  obtain ⟨v₀, hv₀⟩ := hD
  have hv₀D : (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v₀ - v₀ ∈ comSp p W :=
    Submodule.subset_span ⟨x, v₀, ⟨hxW, n, hxp⟩, rfl⟩
  have : Nontrivial ↥(comSp p W) := ⟨⟨⟨_, hv₀D⟩, 0, fun h => hv₀ (congrArg Subtype.val h)⟩⟩
  have hnil := isNilpotent_comap hWp
  obtain ⟨S⟩ : Nonempty (Sylow p ↥(W.comap (proj 2 F))) := inferInstance
  have hHD : ∀ h : ↥(W.comap (proj 2 F)), ∀ v ∈ comSp p W,
      Matrix.mulVecLin (((h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) v ∈ comSp p W :=
    fun h v hv => mulVec_mem_comSp (Subgroup.le_normalizer ⟨h.1, h.2, rfl⟩) hv
  let ρ : ↥(W.comap (proj 2 F)) →* Module.End F ↥(comSp p W) :=
    { toFun := fun h => (Matrix.mulVecLin (((h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)).restrict (hHD h)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [mulVec_mulVec] }
  obtain ⟨⟨v, hvD⟩, hv0, hvfix⟩ :=
    CFSG.LieType.BorelTits.exists_fixed_ne_zero ρ p (S : Subgroup _) S.isPGroup'
  refine ⟨v, ⟨fun y hy => ?_, hvD⟩, fun h => hv0 (Subtype.ext h)⟩
  obtain ⟨⟨t, ht, rfl⟩, m, hm⟩ := hy
  have htS : (⟨t, ht⟩ : ↥(W.comap (proj 2 F))) ∈ S := by
    refine mem_sylow_of_normal S ⟨m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hm
  exact congrArg Subtype.val (hvfix _ htS)

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
