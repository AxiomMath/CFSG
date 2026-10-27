module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Hyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma ffOutFFE8Dim_mul_comm_of_mem {hQ : Q.Nondegenerate} {E : Subgroup (OGroup Q)}
    {t ν : OGroup Q} (h : FFE8VData hQ E t ν) {a b : OGroup Q} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  have hcomm : (⟨a, ha⟩ : ↥E) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    h.elemAb.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val hcomm

private lemma ffOutFFE8Dim_conj_mem {hQ : Q.Nondegenerate} {E : Subgroup (OGroup Q)}
    {t ν : OGroup Q} (h : FFE8VData hQ E t ν) {e : OGroup Q} (he : e ∈ E) :
    ν * e * ν⁻¹ ∈ E :=
  ((Subgroup.mem_normalizer_iff (H := E)).mp h.nu_norm e).mp he

private lemma ffOutFFE8Dim_conj_inv_mem {hQ : Q.Nondegenerate} {E : Subgroup (OGroup Q)}
    {t ν : OGroup Q} (h : FFE8VData hQ E t ν) {e : OGroup Q} (he : e ∈ E) :
    ν⁻¹ * e * ν ∈ E :=
  ((Subgroup.mem_normalizer_iff'' (H := E)).mp h.nu_norm e).mp he

private lemma ffOutFFE8Dim_mul_comm_three {hQ : Q.Nondegenerate} {E : Subgroup (OGroup Q)}
    {t ν : OGroup Q} (h : FFE8VData hQ E t ν) {a b c : OGroup Q} (ha : a ∈ E) (hb : b ∈ E)
    (hc : c ∈ E) : a * b * c = c * a * b := by
  have hbc : b * c = c * b := ffOutFFE8Dim_mul_comm_of_mem h hb hc
  have hac : a * c = c * a := ffOutFFE8Dim_mul_comm_of_mem h ha hc
  calc a * b * c = a * (b * c) := mul_assoc _ _ _
    _ = a * (c * b) := by rw [hbc]
    _ = (a * c) * b := (mul_assoc _ _ _).symm
    _ = (c * a) * b := by rw [hac]
    _ = c * a * b := rfl

theorem ffE8Dim_nu_comm_t (hQ : Q.Nondegenerate) {E : Subgroup (OGroup Q)} {t ν : OGroup Q}
    (h : FFE8VData hQ E t ν) : ν * t = t * ν := by
  classical
  haveI hEfin : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [h.elemAb.2]; norm_num)
  haveI hEft : Fintype ↥E := Fintype.ofFinite ↥E
  let α := {x : ↥E // x ≠ 1}
  haveI : Fintype α := Fintype.ofFinite α
  have hcardα : Fintype.card α = 7 := by
    show Fintype.card {x : ↥E // x ≠ 1} = 7
    rw [Fintype.card_subtype_compl (fun x : ↥E => x = 1),
      Fintype.card_subtype_eq (1 : ↥E), ← Nat.card_eq_fintype_card, h.elemAb.2]
    norm_num
  have hconj : ∀ x ∈ E, ν * x * ν⁻¹ ∈ E := fun x hx => ffOutFFE8Dim_conj_mem h hx
  have hconj' : ∀ x ∈ E, ν⁻¹ * x * ν ∈ E := fun x hx => ffOutFFE8Dim_conj_inv_mem h hx
  let f : α → α := fun x =>
    ⟨⟨ν * (x.1 : OGroup Q) * ν⁻¹, hconj x.1 x.1.2⟩, by
      intro hx
      apply x.2
      apply Subtype.ext
      have hx' : ν * (x.1 : OGroup Q) * ν⁻¹ = 1 := by
        simpa using congrArg Subtype.val hx
      calc (x.1 : OGroup Q) = ν⁻¹ * (ν * (x.1 : OGroup Q) * ν⁻¹) * ν := by group
        _ = ν⁻¹ * 1 * ν := by rw [hx']
        _ = 1 := by group⟩
  let finv : α → α := fun x =>
    ⟨⟨ν⁻¹ * (x.1 : OGroup Q) * ν, hconj' x.1 x.1.2⟩, by
      intro hx
      apply x.2
      apply Subtype.ext
      have hx' : ν⁻¹ * (x.1 : OGroup Q) * ν = 1 := by
        simpa using congrArg Subtype.val hx
      calc (x.1 : OGroup Q) = ν * (ν⁻¹ * (x.1 : OGroup Q) * ν) * ν⁻¹ := by group
        _ = ν * 1 * ν⁻¹ := by rw [hx']
        _ = 1 := by group⟩
  have hleft : Function.LeftInverse finv f := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show ν⁻¹ * (ν * (x.1 : OGroup Q) * ν⁻¹) * ν = (x.1 : OGroup Q)
    group
  have hright : Function.RightInverse finv f := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show ν * (ν⁻¹ * (x.1 : OGroup Q) * ν) * ν⁻¹ = (x.1 : OGroup Q)
    group
  let σ : Equiv.Perm α := ⟨f, finv, hleft, hright⟩
  have hf3 : ∀ x : α, f (f (f x)) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have h3 : ν * ν * ν = 1 := (pow_three' ν).symm.trans h.nu_cube
    show ν * (ν * (ν * (x.1 : OGroup Q) * ν⁻¹) * ν⁻¹) * ν⁻¹ = (x.1 : OGroup Q)
    calc ν * (ν * (ν * (x.1 : OGroup Q) * ν⁻¹) * ν⁻¹) * ν⁻¹
        = (ν * ν * ν) * (x.1 : OGroup Q) * (ν * ν * ν)⁻¹ := by group
      _ = (x.1 : OGroup Q) := by rw [h3]; group
  have hσ3 : σ ^ 3 = 1 := by
    apply Equiv.ext
    intro x
    exact hf3 x
  have hσ3' : σ ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hσ3
  have hnot : ¬ 3 ∣ Fintype.card α := by rw [hcardα]; norm_num
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hnot hσ3'
  have hfixE : (σ a).1 = a.1 := congrArg Subtype.val ha
  have hfix : ν * (a.1 : OGroup Q) * ν⁻¹ = (a.1 : OGroup Q) := congrArg Subtype.val hfixE
  have hcomm_a : ν * (a.1 : OGroup Q) = (a.1 : OGroup Q) * ν := by
    calc ν * (a.1 : OGroup Q) = ν * (a.1 : OGroup Q) * ν⁻¹ * ν := by group
      _ = (a.1 : OGroup Q) * ν := by rw [hfix]
  rcases h.nu_fix (a.1 : OGroup Q) a.1.2 hcomm_a with h1 | ht
  · exact absurd (Subtype.ext h1) a.2
  · rw [ht] at hcomm_a
    exact hcomm_a

theorem ffE8Dim_fix (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {E : Subgroup (OGroup Q)} {t ν : OGroup Q} (h : FFE8VData hQ E t ν) :
    ∀ e ∈ E, ∀ v ∈ fixSp t, (e : V ≃ₗ[ZMod 3] V) v = v := by
  intro e he v hv
  have hvv : (t : V ≃ₗ[ZMod 3] V) v = v := mem_fixSp_iff.mp hv
  have he2 : e * e = 1 := by rw [← pow_two]; exact h.elemAb.1.2 e he
  have het : e * t = t * e := ffOutFFE8Dim_mul_comm_of_mem h he h.t_mem
  have heP : ∀ w ∈ fixSp t, (e : V ≃ₗ[ZMod 3] V) w ∈ fixSp t := by
    intro w hw
    rw [mem_fixSp_iff]
    have hw' : (t : V ≃ₗ[ZMod 3] V) w = w := mem_fixSp_iff.mp hw
    calc (t : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) w)
        = ((t : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V)) w :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = (↑(t * e) : V ≃ₗ[ZMod 3] V) w := by rw [Subgroup.coe_mul]
      _ = (↑(e * t) : V ≃ₗ[ZMod 3] V) w := by rw [← het]
      _ = ((e : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V)) w := by rw [Subgroup.coe_mul]
      _ = (e : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) w) := LinearEquiv.mul_apply _ _ _
      _ = (e : V ≃ₗ[ZMod 3] V) w := by rw [hw']
  have hνt : ν * t = t * ν := ffE8Dim_nu_comm_t hQ h
  have hνP : ∀ w ∈ fixSp t, (ν : V ≃ₗ[ZMod 3] V) w ∈ fixSp t := by
    intro w hw
    rw [mem_fixSp_iff]
    have hw' : (t : V ≃ₗ[ZMod 3] V) w = w := mem_fixSp_iff.mp hw
    calc (t : V ≃ₗ[ZMod 3] V) ((ν : V ≃ₗ[ZMod 3] V) w)
        = ((t : V ≃ₗ[ZMod 3] V) * (ν : V ≃ₗ[ZMod 3] V)) w :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = (↑(t * ν) : V ≃ₗ[ZMod 3] V) w := by rw [Subgroup.coe_mul]
      _ = (↑(ν * t) : V ≃ₗ[ZMod 3] V) w := by rw [← hνt]
      _ = ((ν : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V)) w := by rw [Subgroup.coe_mul]
      _ = (ν : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) w) := LinearEquiv.mul_apply _ _ _
      _ = (ν : V ≃ₗ[ZMod 3] V) w := by rw [hw']
  have hνinv_t : ν⁻¹ * t = t * ν⁻¹ := by
    calc ν⁻¹ * t = ν⁻¹ * (t * ν) * ν⁻¹ := by group
      _ = ν⁻¹ * (ν * t) * ν⁻¹ := by rw [← hνt]
      _ = t * ν⁻¹ := by group
  have hνinvP : ∀ w ∈ fixSp t, (ν⁻¹ : V ≃ₗ[ZMod 3] V) w ∈ fixSp t := by
    intro w hw
    rw [mem_fixSp_iff]
    have hw' : (t : V ≃ₗ[ZMod 3] V) w = w := mem_fixSp_iff.mp hw
    have hcoe : (ν⁻¹ : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) =
        (t : V ≃ₗ[ZMod 3] V) * (ν⁻¹ : V ≃ₗ[ZMod 3] V) := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hνinv_t
    calc (t : V ≃ₗ[ZMod 3] V) ((ν⁻¹ : V ≃ₗ[ZMod 3] V) w)
        = ((t : V ≃ₗ[ZMod 3] V) * (ν⁻¹ : V ≃ₗ[ZMod 3] V)) w :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = ((ν⁻¹ : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V)) w := by rw [← hcoe]
      _ = (ν⁻¹ : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) w) := LinearEquiv.mul_apply _ _ _
      _ = (ν⁻¹ : V ≃ₗ[ZMod 3] V) w := by rw [hw']
  set e₁ : OGroup Q := ν * e * ν⁻¹ with he₁
  set e₂ : OGroup Q := ν * e₁ * ν⁻¹ with he₂
  have he₁E : e₁ ∈ E := by rw [he₁]; exact ffOutFFE8Dim_conj_mem h he
  have he₂E : e₂ ∈ E := by rw [he₂]; exact ffOutFFE8Dim_conj_mem h he₁E
  have he₁P : ∀ w ∈ fixSp t, (e₁ : V ≃ₗ[ZMod 3] V) w = (e : V ≃ₗ[ZMod 3] V) w := by
    intro w hw
    have hνinvw : (ν⁻¹ : V ≃ₗ[ZMod 3] V) w ∈ fixSp t := hνinvP w hw
    have hcomm := ffE8Hyp_comm hQ hdim hsgn h.t_sq h.t_dim h.t_sign hνP heP
      ((ν⁻¹ : V ≃ₗ[ZMod 3] V) w) hνinvw
    rw [he₁]
    calc ((ν * e * ν⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) w
        = (ν : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) ((ν⁻¹ : V ≃ₗ[ZMod 3] V) w)) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
            LinearEquiv.mul_apply]
      _ = (e : V ≃ₗ[ZMod 3] V) ((ν : V ≃ₗ[ZMod 3] V) ((ν⁻¹ : V ≃ₗ[ZMod 3] V) w)) := hcomm
      _ = (e : V ≃ₗ[ZMod 3] V) w := by simp
  have he₂P : ∀ w ∈ fixSp t, (e₂ : V ≃ₗ[ZMod 3] V) w = (e₁ : V ≃ₗ[ZMod 3] V) w := by
    intro w hw
    have hνinvw : (ν⁻¹ : V ≃ₗ[ZMod 3] V) w ∈ fixSp t := hνinvP w hw
    have he₁Pmem : ∀ u ∈ fixSp t, (e₁ : V ≃ₗ[ZMod 3] V) u ∈ fixSp t := by
      intro u hu
      rw [he₁P u hu]
      exact heP u hu
    have hcomm := ffE8Hyp_comm hQ hdim hsgn h.t_sq h.t_dim h.t_sign hνP he₁Pmem
      ((ν⁻¹ : V ≃ₗ[ZMod 3] V) w) hνinvw
    rw [he₂]
    calc ((ν * e₁ * ν⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) w
        = (ν : V ≃ₗ[ZMod 3] V) ((e₁ : V ≃ₗ[ZMod 3] V) ((ν⁻¹ : V ≃ₗ[ZMod 3] V) w)) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
            LinearEquiv.mul_apply]
      _ = (e₁ : V ≃ₗ[ZMod 3] V) ((ν : V ≃ₗ[ZMod 3] V) ((ν⁻¹ : V ≃ₗ[ZMod 3] V) w)) := hcomm
      _ = (e₁ : V ≃ₗ[ZMod 3] V) w := by simp
  set N : OGroup Q := e * e₁ * e₂ with hN
  have hNE : N ∈ E := by rw [hN]; exact E.mul_mem (E.mul_mem he he₁E) he₂E
  have he₂conj : ν * e₂ * ν⁻¹ = e := by
    rw [he₂, he₁]
    have h3 : ν * ν * ν = 1 := (pow_three' ν).symm.trans h.nu_cube
    calc ν * (ν * (ν * e * ν⁻¹) * ν⁻¹) * ν⁻¹
        = (ν * ν * ν) * e * (ν * ν * ν)⁻¹ := by group
      _ = e := by rw [h3]; group
  have hNconj : ν * N * ν⁻¹ = N := by
    rw [hN]
    calc ν * (e * e₁ * e₂) * ν⁻¹
        = (ν * e * ν⁻¹) * (ν * e₁ * ν⁻¹) * (ν * e₂ * ν⁻¹) := by group
      _ = e₁ * e₂ * (ν * e₂ * ν⁻¹) := by rw [← he₁, ← he₂]
      _ = e₁ * e₂ * e := by rw [he₂conj]
      _ = e * e₁ * e₂ := ffOutFFE8Dim_mul_comm_three h he₁E he₂E he
  have hNuN : ν * N = N * ν := by
    calc ν * N = ν * N * ν⁻¹ * ν := by group
      _ = N * ν := by rw [hNconj]
  have hNv : (N : V ≃ₗ[ZMod 3] V) v = v := by
    rcases h.nu_fix N hNE hNuN with hN1 | hNt
    · rw [hN1]; simp
    · rw [hNt, hvv]
  have hee : ∀ w : V, (e : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) w) = w := by
    intro w
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, he2]
    simp
  have hNcoe : (N : V ≃ₗ[ZMod 3] V) =
      (e : V ≃ₗ[ZMod 3] V) * (e₁ : V ≃ₗ[ZMod 3] V) * (e₂ : V ≃ₗ[ZMod 3] V) := by
    rw [hN, Subgroup.coe_mul, Subgroup.coe_mul]
  have hN_eq_e : (N : V ≃ₗ[ZMod 3] V) v = (e : V ≃ₗ[ZMod 3] V) v := by
    rw [hNcoe, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [he₂P v hv, he₁P v hv, he₁P ((e : V ≃ₗ[ZMod 3] V) v) (heP v hv)]
    exact hee ((e : V ≃ₗ[ZMod 3] V) v)
  rw [← hN_eq_e]
  exact hNv

theorem ffE8Dim_commSp_le (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {E : Subgroup (OGroup Q)} {t ν : OGroup Q} (h : FFE8VData hQ E t ν)
    {e : OGroup Q} (he : e ∈ E) : commSp e ≤ commSp t := by
  intro w hw
  obtain ⟨u, hu⟩ := (CFSG.RankThree.OrthogonalInvolutions.mem_commSpace).mp hw
  have hu_top : u ∈ fixSp t ⊔ commSp t := by
    rw [(isCompl_fixSp_commSp h.t_sq).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u₁, hu₁, u₂, hu₂, hu_eq⟩ := Submodule.mem_sup.mp hu_top
  rw [← hu_eq] at hu
  have heu₁ : (e : V ≃ₗ[ZMod 3] V) u₁ = u₁ := ffE8Dim_fix hQ hdim hsgn h e he u₁ hu₁
  have het : e * t = t * e := ffOutFFE8Dim_mul_comm_of_mem h he h.t_mem
  have heu₂ : (e : V ≃ₗ[ZMod 3] V) u₂ ∈ commSp t := by
    rw [mem_commSp_iff h.t_sq]
    have hu₂' : (t : V ≃ₗ[ZMod 3] V) u₂ = -u₂ := (mem_commSp_iff h.t_sq).mp hu₂
    calc (t : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) u₂)
        = ((t : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V)) u₂ :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = (↑(t * e) : V ≃ₗ[ZMod 3] V) u₂ := by rw [Subgroup.coe_mul]
      _ = (↑(e * t) : V ≃ₗ[ZMod 3] V) u₂ := by rw [← het]
      _ = ((e : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V)) u₂ := by rw [Subgroup.coe_mul]
      _ = (e : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) u₂) := LinearEquiv.mul_apply _ _ _
      _ = (e : V ≃ₗ[ZMod 3] V) (-u₂) := by rw [hu₂']
      _ = -(e : V ≃ₗ[ZMod 3] V) u₂ := by simp
  rw [← hu, map_add, heu₁]
  have hmem : (u₁ + (e : V ≃ₗ[ZMod 3] V) u₂) - (u₁ + u₂) =
      (e : V ≃ₗ[ZMod 3] V) u₂ - u₂ := by abel
  rw [hmem]
  exact Submodule.sub_mem _ heu₂ hu₂

theorem ffE8Dim_invDim (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {E : Subgroup (OGroup Q)} {t ν : OGroup Q} (h : FFE8VData hQ E t ν)
    {e : OGroup Q} (he : e ∈ E) (he1 : e ≠ 1) (het : e ≠ t) : invDim e = 2 := by
  have he2 : e * e = 1 := by rw [← pow_two]; exact h.elemAb.1.2 e he
  have ht4 : Module.finrank (ZMod 3) (commSp t) = 4 := by simpa [invDim] using h.t_dim
  have hle_dim : invDim e ≤ 4 := by
    have hmono := Submodule.finrank_mono (ffE8Dim_commSp_le hQ hdim hsgn h he)
    rw [ht4] at hmono
    simpa [invDim] using hmono
  have hne0 : invDim e ≠ 0 := by
    intro h0
    exact he1 ((invDim_eq_zero_iff he2).mp h0)
  have hne4 : invDim e ≠ 4 := by
    intro h4
    have hfe : Module.finrank (ZMod 3) (commSp e) = 4 := by simpa [invDim] using h4
    have heq : commSp e = commSp t :=
      Submodule.eq_of_le_of_finrank_eq (ffE8Dim_commSp_le hQ hdim hsgn h he)
        (by rw [hfe, ht4])
    exact het (eq_of_commSp_eq hQ he2 h.t_sq heq)
  have hev : Even (invDim e) :=
    ((involution_mem_omegaGroup_iff hQ he2).mp (h.le_omega he)).1
  obtain ⟨k, hk⟩ := hev
  omega

end CFSG.OddStandard.SmallF3.Omega
