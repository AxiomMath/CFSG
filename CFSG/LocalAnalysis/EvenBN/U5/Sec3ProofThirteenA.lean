module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBFactors
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Torus

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section S313aGeneric

open scoped Matrix

theorem s313a_sq_eq_one_of_fixed {k : Type*} [Field k] (h2 : (2 : k) = 0)
    (M : SL(2, k)) {v : Fin 2 → k} (hv : v ≠ 0)
    (hM : (M : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v) :
    M * M = 1 := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) k).det = 1 := M.2
  have hker : ((M : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hM, Matrix.one_mulVec, sub_self]
  have hd0 : ((M : Matrix (Fin 2) (Fin 2) k) - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hker⟩
  rw [Matrix.det_fin_two] at hd0 hdet
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
    Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true, sub_zero,
    zero_sub] at hd0
  set a := (M : Matrix (Fin 2) (Fin 2) k) 0 0 with ha
  set b := (M : Matrix (Fin 2) (Fin 2) k) 0 1 with hb
  set c := (M : Matrix (Fin 2) (Fin 2) k) 1 0 with hc
  set d := (M : Matrix (Fin 2) (Fin 2) k) 1 1 with hd
  have had : a + d = 0 := by linear_combination (hdet - hd0) + h2
  have hda : d = a := by linear_combination had - a * h2
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination hdet - a * hda + (b * c) * h2
  · linear_combination b * had
  · linear_combination c * had
  · linear_combination hdet + d * hda + (b * c) * h2

theorem s313a_eq_one_of_odd_fixed {G : Type*} [Group G] {k : Type*} [Field k] (h2 : (2 : k) = 0)
    {Y : Subgroup G} (φ : Y ≃* SL(2, k)) {θ : (Fin 2 → k) → G}
    (hθ : Timmesfeld.ARS.IsNaturalModule φ θ) {y : G} (hy : y ∈ Y)
    (hodd : Odd (orderOf y)) {u : G} (hu : u ∈ Set.range θ) (hfix : y * u * y⁻¹ = u) :
    y = 1 ∨ u = 1 := by
  obtain ⟨v, rfl⟩ := hu
  by_cases hv : v = 0
  · right
    subst hv
    have := hθ.map_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  · left
    have h1 := hθ.map_mulVec ⟨y, hy⟩ v
    simp only at h1
    rw [hfix] at h1
    have h3 := hθ.injective h1
    have h4 := s313a_sq_eq_one_of_fixed h2 (φ ⟨y, hy⟩) hv h3
    rw [← map_mul] at h4
    have h5 : (⟨y, hy⟩ : Y) * ⟨y, hy⟩ = 1 := φ.injective (by rw [h4, map_one])
    have h6 : y * y = 1 := congrArg Subtype.val h5
    have h7 : y ^ 2 = 1 := by rw [sq]; exact h6
    have h8 := orderOf_dvd_of_pow_eq_one h7
    rcases (Nat.dvd_prime Nat.prime_two).1 h8 with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at hodd
      exact absurd hodd (by decide)

def s313a_fixModSubgroup {G : Type*} [Group G] (F W : Subgroup G) (x : G) : Subgroup G where
  carrier := {s | s ∈ normalizer (F : Set G) ∧ s ∈ normalizer (W : Set G) ∧
    x⁻¹ * (s * x * s⁻¹) ∈ W}
  mul_mem' := by
    rintro s s' ⟨hsF, hsW, hs⟩ ⟨hs'F, hs'W, hs'⟩
    refine ⟨mul_mem hsF hs'F, mul_mem hsW hs'W, ?_⟩
    have e : x⁻¹ * (s * s' * x * (s * s')⁻¹) =
        (x⁻¹ * (s * x * s⁻¹)) * (s * (x⁻¹ * (s' * x * s'⁻¹)) * s⁻¹) := by group
    rw [e]
    exact mul_mem hs ((mem_normalizer_iff.1 hsW _).1 hs')
  one_mem' := ⟨one_mem _, one_mem _, by simp⟩
  inv_mem' := by
    rintro s ⟨hsF, hsW, hs⟩
    refine ⟨inv_mem hsF, inv_mem hsW, ?_⟩
    have h1 := (mem_normalizer_iff.1 (inv_mem hsW) _).1 (inv_mem hs)
    have e : x⁻¹ * (s⁻¹ * x * s⁻¹⁻¹) = s⁻¹ * (x⁻¹ * (s * x * s⁻¹))⁻¹ * s⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem s313a_normal_subgroupOf_of_comm {G : Type*} [Group G] {F W : Subgroup G} (hWF : W ≤ F)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) : (W.subgroupOf F).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have : ((g * n * g⁻¹ : F) : G) = (n : G) := by
    push_cast
    rw [hFcomm (g : G) g.2 (n : G) n.2]
    group
  rw [this]
  exact hn

theorem s313a_mem_of_fixed_mod {G : Type*} [Group G] [Finite G] {F W : Subgroup G} (hWF : W ≤ F)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) {n : ℕ} (hF : Nat.card F = 2 ^ n) {j : G}
    (hjF : j ∈ normalizer (F : Set G)) (hjW : j ∈ normalizer (W : Set G))
    (hodd : Odd (orderOf j)) (hfree : ∀ c ∈ F, j * c * j⁻¹ = c → c = 1)
    {x : G} (hxF : x ∈ F) (hx : x⁻¹ * (j * x * j⁻¹) ∈ W) : x ∈ W := by
  have hFW : F ≤ normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWF).1 (s313a_normal_subgroupOf_of_comm hWF hFcomm)
  have hsolv : Group.IsSolvable F := by
    refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    exact hFcomm (a : G) a.2 (b : G) b.2
  have hjH : j ∈ s313a_fixModSubgroup F W x := ⟨hjF, hjW, hx⟩
  have hle := Subgroup.zpowers_le.2 hjH
  have hcop : (Nat.card (zpowers j)).Coprime (Nat.card F) := by
    rw [Nat.card_zpowers, hF]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hodd)
  obtain ⟨c, hc, w, hw, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hWF hFW
    (Subgroup.zpowers_le.2 hjF) (Subgroup.zpowers_le.2 hjW) hsolv hcop hxF
    (fun s hs => (hle hs).2.2)
  have hcj : j * c * j⁻¹ = c := by
    have := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 j (Subgroup.mem_zpowers j)
    rw [this]; group
  have hc1 : c = 1 := hfree c (Subgroup.mem_inf.1 hc).1 hcj
  rw [hc1, one_mul]
  exact hw

theorem s313a_exists_conj_mul_inv_mem {G : Type*} [Group G] [Finite G] {F W J : Subgroup G}
    (hWF : W ≤ F) (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hJF : J ≤ normalizer (F : Set G)) (hJW : J ≤ normalizer (W : Set G))
    (hfree : ∀ j ∈ J, j ≠ 1 → ∀ x ∈ F, x⁻¹ * (j * x * j⁻¹) ∈ W → x ∈ W)
    (hcard : ∀ [(W.subgroupOf F).Normal], Nat.card J + 1 = Nat.card (F ⧸ W.subgroupOf F))
    {x : G} (hxF : x ∈ F) (hxW : x ∉ W) {y : G} (hyF : y ∈ F) (hyW : y ∉ W) :
    ∃ j ∈ J, (j * x * j⁻¹) * y⁻¹ ∈ W := by
  classical
  haveI hN : (W.subgroupOf F).Normal := s313a_normal_subgroupOf_of_comm hWF hFcomm
  have hcard' := @hcard hN
  let Φ : J → {z : F ⧸ W.subgroupOf F // z ≠ 1} := fun j =>
    ⟨(QuotientGroup.mk (⟨j * x * j⁻¹, (mem_normalizer_iff.1 (hJF j.2) x).1 hxF⟩ : F) :
        F ⧸ W.subgroupOf F), by
      intro h
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h
      have h' : (j : G) * x * (j : G)⁻¹ ∈ W := h
      exact hxW ((mem_normalizer_iff.1 (hJW j.2) x).2 h')⟩
  have hinj : Function.Injective Φ := by
    intro j j' hjj'
    have h1 := congrArg Subtype.val hjj'
    simp only [Φ] at h1
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    have h1' : ((j : G) * x * (j : G)⁻¹)⁻¹ * ((j' : G) * x * (j' : G)⁻¹) ∈ W := by
      simpa using h1
    by_contra hne
    have hi : (j : G)⁻¹ * (j' : G) ≠ 1 := by
      intro h
      exact hne (Subtype.ext (by rw [inv_mul_eq_one] at h; exact h))
    refine hxW (hfree ((j : G)⁻¹ * (j' : G)) (J.mul_mem (J.inv_mem j.2) j'.2) hi x hxF ?_)
    have h2 := (mem_normalizer_iff.1 (hJW (J.inv_mem j.2)) _).1 h1'
    have e : (j : G)⁻¹ * (((j : G) * x * (j : G)⁻¹)⁻¹ * ((j' : G) * x * (j' : G)⁻¹)) *
        ((j : G)⁻¹)⁻¹ = x⁻¹ * (((j : G)⁻¹ * (j' : G)) * x * ((j : G)⁻¹ * (j' : G))⁻¹) := by group
    rwa [e] at h2
  have hΩ : Nat.card {z : F ⧸ W.subgroupOf F // z ≠ 1} = Nat.card J := by
    have : Fintype (F ⧸ W.subgroupOf F) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun z : F ⧸ W.subgroupOf F => z = 1),
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
    omega
  have hbij := hinj.bijective_of_nat_card_le hΩ.le
  have hyx : (QuotientGroup.mk (⟨y, hyF⟩ : F) : F ⧸ W.subgroupOf F) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    exact hyW h
  obtain ⟨j, hj⟩ := hbij.2 ⟨_, hyx⟩
  refine ⟨j, j.2, ?_⟩
  have h1 := congrArg Subtype.val hj
  simp only [Φ] at h1
  rw [QuotientGroup.eq, mem_subgroupOf] at h1
  have h1' : ((j : G) * x * (j : G)⁻¹)⁻¹ * y ∈ W := by simpa using h1
  have hjx : (j : G) * x * (j : G)⁻¹ ∈ F := (mem_normalizer_iff.1 (hJF j.2) x).1 hxF
  have h2 := inv_mem h1'
  rw [show (((j : G) * x * (j : G)⁻¹)⁻¹ * y)⁻¹ = y⁻¹ * ((j : G) * x * (j : G)⁻¹) by group,
    hFcomm y⁻¹ (F.inv_mem hyF) _ hjx] at h2
  exact h2

theorem s313a_torus_le_normalizer_ofSL {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k]
    {Y : Subgroup G} (φ : Y ≃* SL(2, k)) :
    Prelim.ofSL φ (Common.torusSL k) ≤
      normalizer ((Prelim.ofSL φ (Timmesfeld.upperUnipotent k) : Subgroup G) : Set G) := by
  intro j hj
  have hjY : j ∈ Y := Prelim.ofSL_le φ _ hj
  have hg : φ ⟨j, hjY⟩ ∈ Common.torusSL k := (Prelim.coe_mem_ofSL_iff φ ⟨j, hjY⟩).1 hj
  obtain ⟨μ, hμ⟩ := Common.mem_torusSL_iff.1 hg
  have hg10 : ((φ ⟨j, hjY⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rw [← hμ, Common.coe_diagSL]
    simp
  have hN := Prelim.map_conj_upperUnipotent_of_eq_zero hg10
  refine mem_normalizer_fintype fun q hq => ?_
  have hqY : q ∈ Y := Prelim.ofSL_le φ _ hq
  have hq' : φ ⟨q, hqY⟩ ∈ Timmesfeld.upperUnipotent k := (Prelim.coe_mem_ofSL_iff φ ⟨q, hqY⟩).1 hq
  have hjqY : j * q * j⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hjY hqY) (Y.inv_mem hjY)
  have := (Prelim.coe_mem_ofSL_iff (S := Timmesfeld.upperUnipotent k) φ
    (⟨j, hjY⟩ * ⟨q, hqY⟩ * ⟨j, hjY⟩⁻¹)).2 (by
      rw [map_mul, map_mul, map_inv]
      rw [← hN]
      exact ⟨_, hq', rfl⟩)
  simpa using this

theorem s313a_exists_J {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {m : ℕ}
    (hkm : Nat.card k = 2 ^ m) (hm : 1 ≤ m) {Y : Subgroup G} (φ : Y ≃* SL(2, k))
    {Q₀ : Subgroup G} (hQ₀ : IsSylowOf 2 Q₀ Y) :
    ∃ J : Subgroup G, J ≤ Y ∧ J ≤ normalizer (Q₀ : Set G) ∧ Nat.card J = Nat.card k - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyY, hy⟩ := Prelim.exists_conj_of_isSylowOf
    (Prelim.isSylowOf_ofSL_upperUnipotent hkm hm φ) hQ₀
  refine ⟨(Prelim.ofSL φ (Common.torusSL k)).map (MulAut.conj y).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Y.mul_mem (Y.mul_mem hyY (Prelim.ofSL_le φ _ hz)) (Y.inv_mem hyY)
  · rintro _ ⟨z, hz, rfl⟩
    have hzN := s313a_torus_le_normalizer_ofSL φ hz
    refine mem_normalizer_fintype fun q hq => ?_
    rw [hy] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    rw [hy]
    refine ⟨z * q' * z⁻¹, (mem_normalizer_iff.1 hzN q').1 hq', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Prelim.card_map_conj, Prelim.card_ofSL, Common.card_torusSL]

theorem s313a_mem_normalizer_Z₂ {G : Type*} [Group G] [Finite G] {S : Subgroup G} {g : G}
    (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (((Subgroup.upperCentralSeries ↥S 2).map S.subtype : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun z hz => ?_
  obtain ⟨s, hs, rfl⟩ := hz
  set α : MulAut S := S.normalizerMonoidHom ⟨g, hg⟩ with hα
  have hchar : (Subgroup.upperCentralSeries ↥S 2).comap α.toMonoidHom = Subgroup.upperCentralSeries ↥S 2 :=
    (inferInstance : (Subgroup.upperCentralSeries ↥S 2).Characteristic).fixed α
  have hs' : α s ∈ Subgroup.upperCentralSeries ↥S 2 := by
    have : s ∈ (Subgroup.upperCentralSeries ↥S 2).comap α.toMonoidHom := by rw [hchar]; exact hs
    exact this
  refine ⟨α s, hs', ?_⟩
  simp [hα]

end S313aGeneric

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

section S313a

variable (hp : d.CaseHyp) (k12 : d.Know12) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k12 hS hP

theorem s313a_L₁_eq : d.L₁ = d.D ⊔ d.M₁ := k12.s9_3.1

theorem s313a_M₁_le_L₁ : d.M₁ ≤ d.L₁ := (s313a_L₁_eq hp k12 hS hP) ▸ le_sup_right

theorem s313a_centerIn_D : CFSG.centerIn d.D = d.F := (k12.s9_2 S hS hP).2.2.2.1

theorem s313a_F_le_D : d.F ≤ d.D := by
  rw [← s313a_centerIn_D hp k12 hS hP]
  exact inf_le_left

theorem s313a_D_le_centralizer_F : d.D ≤ centralizer (d.F : Set G) := by
  rw [← s313a_centerIn_D hp k12 hS hP]
  intro x hx
  exact mem_centralizer_iff.2 fun z hz =>
    (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 x hx).symm

theorem s313a_mul_self_mem_F : ∀ x ∈ d.D, x * x ∈ d.F := (k12.s9_2 S hS hP).2.2.2.2

theorem s313a_L₁_le_normalizer_F : d.L₁ ≤ normalizer (d.F : Set G) := by
  rw [← s313a_centerIn_D hp k12 hS hP]
  exact hp.hyp.L₁_le_normalizer_D.trans (normalizer_le_normalizer_centerIn _)

theorem s313a_S_eq : S = d.E ⊔ d.D := (k12.s9_1 S hS hP).1

theorem s313a_D_le_S : d.D ≤ S := (s313a_S_eq hp k12 hS hP).symm ▸ le_sup_right

theorem s313a_t_mem_normalizer_S : d.t ∈ normalizer (S : Set G) := by
  rw [s313a_S_eq hp k12 hS hP]
  exact Common.mem_normalizer_sup (hp.hyp.t_mem_normalizer_E_caseB hp.gms)
    hp.hyp.t_mem_normalizer_D

theorem s313a_W_le_F : d.W ≤ d.F := by
  have h1 := (k12.s10_1 S hS hP).2.2.1.1
  calc d.W ≤ d.W ⊔ (S ⊓ centralizer (d.I₆ : Set G)) := le_sup_left
    _ = d.F := h1.symm

theorem s313a_isSylowOf_S_M₁ : IsSylowOf 2 (S ⊓ d.M₁) d.M₁ := (k12.s10_2 S hS hP).1.2

theorem s313a_S_eq_D_sup : S = d.D ⊔ (S ⊓ d.M₁) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12⟩ := k12.s10_1 S hS hP
  rw [← (k12.s10_2 S hS hP).1.1]
  exact h12.1

theorem s313a_mem_normalizer_W {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (d.W : Set G) := by
  have := s313a_mem_normalizer_Z₂ hg
  rwa [(k12.s9_2 S hS hP).2.1] at this

section S313aPsi

variable {k : Type} [Field k] [Fintype k] (ψ : d.M₁ ≃* SL(2, k) × SL(2, k))
include hp k12 hS hP

theorem s313a_X_le_L₁ : Common.prodFactorOne ψ ≤ d.L₁ :=
  (Common.prodFactorOne_le ψ).trans (s313a_M₁_le_L₁ hp k12 hS hP)

theorem s313a_X_le_Kc : Common.prodFactorOne ψ ≤ d.Kc (Common.prodFactorOne ψ) := by
  rw [d.Kc_eq_normalClosureIn]
  exact le_normalClosureIn (s313a_X_le_L₁ hp k12 hS hP ψ)

theorem s313a_X_le_normalizer_D : Common.prodFactorOne ψ ≤ normalizer (d.D : Set G) :=
  (s313a_X_le_L₁ hp k12 hS hP ψ).trans hp.hyp.L₁_le_normalizer_D

theorem s313a_L₁_le_normalizer_D_sup_X :
    d.L₁ ≤ normalizer ((d.D ⊔ Common.prodFactorOne ψ : Subgroup G) : Set G) := by
  rw [s313a_L₁_eq hp k12 hS hP]
  refine sup_le (fun x hx => le_normalizer (mem_sup_left hx)) fun m hm => ?_
  exact Common.mem_normalizer_sup (hp.hyp.L₁_le_normalizer_D
    (s313a_M₁_le_L₁ hp k12 hS hP hm)) (Common.le_normalizer_prodFactorOne ψ hm)

theorem s313a_Kc_le_D_sup_X : d.Kc (Common.prodFactorOne ψ) ≤ d.D ⊔ Common.prodFactorOne ψ := by
  rw [d.Kc_eq_normalClosureIn]
  exact normalClosureIn_le le_sup_right (s313a_L₁_le_normalizer_D_sup_X hp k12 hS hP ψ)

theorem s313a_Uc_eq :
    d.Uc S (Common.prodFactorOne ψ) = d.D ⊔ (Common.prodFactorOne ψ ⊓ S) := by
  have e : d.D ⊔ d.Kc (Common.prodFactorOne ψ) = d.D ⊔ Common.prodFactorOne ψ :=
    le_antisymm (sup_le le_sup_left (s313a_Kc_le_D_sup_X hp k12 hS hP ψ))
      (sup_le_sup_left (s313a_X_le_Kc hp k12 hS hP ψ) _)
  rw [Uc, e, inf_comm]
  exact sup_inf_eq_of_le (s313a_D_le_S hp k12 hS hP) (s313a_X_le_normalizer_D hp k12 hS hP ψ)

theorem s313a_commutatorElement_mem_F {a b : G} (ha : a ∈ d.D) (hb : b ∈ d.D) :
    a * b * a⁻¹ * b⁻¹ ∈ d.F := by
  have h1 := s313a_mul_self_mem_F hp k12 hS hP _ (mul_mem ha hb)
  have h2 := s313a_mul_self_mem_F hp k12 hS hP _ ha
  have h3 := s313a_mul_self_mem_F hp k12 hS hP _ hb
  have hcomm : Commute b (a * a)⁻¹ :=
    (Commute.inv_right (mem_centralizer_iff.1 (s313a_D_le_centralizer_F hp k12 hS hP hb) _ h2).symm)
  have e : a * b * a⁻¹ * b⁻¹ = (a * b) * (a * b) * ((a * a)⁻¹ * (b * b)⁻¹) := by
    calc a * b * a⁻¹ * b⁻¹ = a * b * a * ((a * a)⁻¹ * b) * (b * b)⁻¹ := by group
      _ = a * b * a * (b * (a * a)⁻¹) * (b * b)⁻¹ := by rw [hcomm.eq]
      _ = (a * b) * (a * b) * ((a * a)⁻¹ * (b * b)⁻¹) := by group
  rw [e]
  exact mul_mem h1 (mul_mem (inv_mem h2) (inv_mem h3))

theorem s313a_eq_one_of_mem_X (hk : Fintype.card k = (2 ^ f) ^ 2) {x : G}
    (hx : x ∈ Common.prodFactorOne ψ)
    (htriv : ∀ a ∈ d.D, a⁻¹ * (x * a * x⁻¹) ∈ d.F) : x = 1 := by
  obtain ⟨-, -, hN⟩ := k12.s12 k inferInstance inferInstance hk ψ
  exact hN.eq_one (Subgroup.mem_inf.2 ⟨Common.prodFactorOne_le ψ hx,
    s313a_X_le_Kc hp k12 hS hP ψ hx⟩) fun a ha => htriv a (Subgroup.mem_inf.1 ha).2

theorem s313a_centerIn_Uc (hk : Fintype.card k = (2 ^ f) ^ 2) :
    CFSG.centerIn (d.Uc S (Common.prodFactorOne ψ)) =
      d.F ⊓ centralizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G) := by
  rw [s313a_Uc_eq hp k12 hS hP ψ]
  apply le_antisymm
  · rintro z ⟨hzU, hzc⟩
    obtain ⟨e, he, x, hx, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer
        (inf_le_left.trans (s313a_X_le_normalizer_D hp k12 hS hP ψ)) hzU
    have hcD : ∀ a ∈ d.D, a * (e * x) = (e * x) * a := fun a ha =>
      mem_centralizer_iff.1 hzc a (mem_sup_left ha)
    have hx1 : x = 1 := by
      refine s313a_eq_one_of_mem_X hp k12 hS hP ψ hk (Subgroup.mem_inf.1 hx).1 fun a ha => ?_
      have e1 : x * a * x⁻¹ = e⁻¹ * a * e := by
        calc x * a * x⁻¹ = e⁻¹ * ((e * x) * a) * (e * x)⁻¹ * e := by group
          _ = e⁻¹ * (a * (e * x)) * (e * x)⁻¹ * e := by rw [← hcD a ha]
          _ = e⁻¹ * a * e := by group
      rw [e1]
      have := s313a_commutatorElement_mem_F hp k12 hS hP (inv_mem ha) (inv_mem he)
      rw [inv_inv, inv_inv] at this
      simpa only [mul_assoc] using this
    subst hx1
    simp only [mul_one] at hcD hzc ⊢
    refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_iff.1 hzc y (mem_sup_right hy)⟩
    rw [← s313a_centerIn_D hp k12 hS hP]
    exact ⟨he, mem_centralizer_iff.2 fun a ha => by simpa using hcD a ha⟩
  · rintro z ⟨hzF, hzc⟩
    refine ⟨mem_sup_left (s313a_F_le_D hp k12 hS hP hzF), mem_centralizer_iff.2 fun y hy => ?_⟩
    have hle : d.D ⊔ (Common.prodFactorOne ψ ⊓ S) ≤ centralizer ({z} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (s313a_D_le_centralizer_F hp k12 hS hP ha) z hzF).symm)
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzc a ha))
    exact mem_centralizer_singleton_iff.1 (hle hy)

theorem s313a_two_eq_zero (hk : Fintype.card k = (2 ^ f) ^ 2) : (2 : k) = 0 := by
  have hd := hp.hyp
  refine GMSK.two_eq_zero_of_card (n := 2 * f) (by have := hd.two_le; omega) ?_
  rw [hk, ← pow_mul, mul_comm]

theorem s313a_four_le_card (hk : Fintype.card k = (2 ^ f) ^ 2) : 4 ≤ Fintype.card k := by
  have hd := hp.hyp
  have h1 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hd.two_le
  rw [hk]
  nlinarith

theorem s313a_isSimpleGroup_X (hk : Fintype.card k = (2 ^ f) ^ 2) :
    IsSimpleGroup (Common.prodFactorOne ψ) := by
  haveI : IsSimpleGroup SL(2, k) := GMSK.sl2_isSimpleGroup (s313a_two_eq_zero hp k12 hS hP hk)
    (s313a_four_le_card hp k12 hS hP hk)
  exact (Common.prodFactorOneEquiv ψ).isSimpleGroup

theorem s313a_exists_mul_ne_X :
    ∃ x y : Common.prodFactorOne ψ, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
  exact ⟨(Common.prodFactorOneEquiv ψ).symm x, (Common.prodFactorOneEquiv ψ).symm y,
    fun e => hxy (by simpa using congrArg (Common.prodFactorOneEquiv ψ) e)⟩

theorem s313a_map_conj_t_X (hk : Fintype.card k = (2 ^ f) ^ 2) :
    (Common.prodFactorOne ψ).map (MulAut.conj d.t).toMonoidHom = Common.prodFactorTwo ψ := by
  have hd := hp.hyp
  have ht : d.t ∈ normalizer (d.M₁ : Set G) := hd.t_mem_normalizer_M₁
  set X := Common.prodFactorOne ψ with hX
  set Y := Common.prodFactorTwo ψ with hY
  set Z := X.map (MulAut.conj d.t).toMonoidHom with hZ
  have hXM : X ≤ d.M₁ := Common.prodFactorOne_le ψ
  have hYM : Y ≤ d.M₁ := Common.prodFactorTwo_le ψ
  have hMX : d.M₁ ≤ normalizer (X : Set G) := Common.le_normalizer_prodFactorOne ψ
  have hZM : Z ≤ d.M₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 ht x).1 (hXM hx)
  have hMZ : d.M₁ ≤ normalizer (Z : Set G) := by
    intro m hm
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := hz
    have hm' : d.t⁻¹ * m * d.t⁻¹⁻¹ ∈ d.M₁ := (mem_normalizer_iff.1 (inv_mem ht) m).1 hm
    have h1 := (mem_normalizer_iff.1 (hMX hm') x).1 hx
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hXs := s313a_isSimpleGroup_X hp k12 hS hP ψ hk
  have hZs : IsSimpleGroup Z :=
    (Subgroup.equivMapOfInjective X (MulAut.conj d.t).toMonoidHom (MulAut.conj d.t).injective).symm.isSimpleGroup
  have hcardZ : Nat.card Z = Nat.card X := Prelim.card_map_conj X d.t
  have hcardXY : Nat.card X = Nat.card Y := by
    rw [Nat.card_congr (Common.prodFactorOneEquiv ψ).toEquiv,
      Nat.card_congr (Common.prodFactorTwoEquiv ψ).toEquiv]
  have hZX : Z ≠ X := by
    intro hZX
    obtain ⟨-, h2, -⟩ := k12.s12 k inferInstance inferInstance hk ψ
    have hXF : X ≤ d.F := by
      have hXK : X ≤ d.F ⊔ d.Kc X := (s313a_X_le_Kc hp k12 hS hP ψ).trans le_sup_right
      have hXKt : X ≤ d.F ⊔ (d.Kc X).map (MulAut.conj d.t).toMonoidHom :=
        calc X = Z := hZX.symm
          _ ≤ (d.Kc X).map (MulAut.conj d.t).toMonoidHom :=
            map_mono (s313a_X_le_Kc hp k12 hS hP ψ)
          _ ≤ d.F ⊔ (d.Kc X).map (MulAut.conj d.t).toMonoidHom := le_sup_right
      exact h2 ▸ le_inf hXK hXKt
    obtain ⟨x, y, hxy⟩ := s313a_exists_mul_ne_X hp k12 hS hP ψ
    exact hxy (Subtype.ext (Prelim.mul_comm_of_mem (hd.isElementaryAbelian_F hp.gms)
      (hXF x.2) (hXF y.2)))
  have hnorm : (X.subgroupOf Z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.1 (hMX (hZM g.2)) (n : G)).1 hn
    simpa using this
  have hZXbot : X ⊓ Z = ⊥ := by
    rcases hZs.eq_bot_or_eq_top_of_normal (X.subgroupOf Z) with h1 | h1
    · have := Subgroup.subgroupOf_eq_bot.1 h1
      exact disjoint_iff.1 this
    · exfalso
      have hle : Z ≤ X := Subgroup.subgroupOf_eq_top.1 h1
      exact hZX (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ]))
  have hcomm : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z := by
    intro z hz x hx
    have h1 : z * x * z⁻¹ ∈ X := (mem_normalizer_iff.1 (hMX (hZM hz)) x).1 hx
    have h2 : x * z⁻¹ * x⁻¹ ∈ Z := (mem_normalizer_iff.1 (hMZ (hXM hx)) z⁻¹).1 (inv_mem hz)
    have hc1 : z * x * z⁻¹ * x⁻¹ ∈ X := mul_mem h1 (inv_mem hx)
    have hc2 : z * x * z⁻¹ * x⁻¹ ∈ Z := by
      have := mul_mem hz h2
      simpa [mul_assoc] using this
    have hc : z * x * z⁻¹ * x⁻¹ ∈ X ⊓ Z := Subgroup.mem_inf.2 ⟨hc1, hc2⟩
    rw [hZXbot, Subgroup.mem_bot] at hc
    have := congrArg (· * x) hc
    simp only [one_mul, inv_mul_cancel_right] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hZY : Z ≤ Y := by
    intro z hz
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := Common.exists_mul_of_mem ψ (hZM hz)
    have hxc : ∀ x ∈ X, x₁ * x = x * x₁ := by
      intro x hx
      have h1 := hcomm _ hz x hx
      have h2 : y₁ * x = x * y₁ := mem_centralizer_iff.1
        (Common.prodFactorOne_le_centralizer ψ hx) y₁ hy₁
      have : x₁ * x * y₁ = x * x₁ * y₁ := by
        calc x₁ * x * y₁ = x₁ * (x * y₁) := by group
          _ = x₁ * (y₁ * x) := by rw [h2]
          _ = x₁ * y₁ * x := by group
          _ = x * (x₁ * y₁) := h1
          _ = x * x₁ * y₁ := by group
      exact mul_right_cancel this
    have hcen : (⟨x₁, hx₁⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxc g g.2).symm
    have hx1 : x₁ = 1 := by
      rcases hXs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
      · rw [h1, Subgroup.mem_bot] at hcen
        exact congrArg Subtype.val hcen
      · exfalso
        obtain ⟨a, b, hab⟩ := s313a_exists_mul_ne_X hp k12 hS hP ψ
        have : a ∈ Subgroup.center X := by rw [h1]; trivial
        exact hab (Subgroup.mem_center_iff.1 this b).symm
    rw [hx1, one_mul]
    exact hy₁
  exact Subgroup.eq_of_le_of_card_ge hZY (by rw [hcardZ, hcardXY])

theorem s313a_isSylowOf_X_inf_S :
    IsSylowOf 2 (Common.prodFactorOne ψ ⊓ S) (Common.prodFactorOne ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (s313a_isSylowOf_S_M₁ hp k12 hS hP).inf_of_le_normalizer
    (Common.prodFactorOne_le ψ) (Common.le_normalizer_prodFactorOne ψ)
  rwa [inf_assoc, inf_eq_right.2 (Common.prodFactorOne_le ψ), inf_comm] at h1

theorem s313a_isSylowOf_Y_inf_S :
    IsSylowOf 2 (Common.prodFactorTwo ψ ⊓ S) (Common.prodFactorTwo ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (s313a_isSylowOf_S_M₁ hp k12 hS hP).inf_of_le_normalizer
    (Common.prodFactorTwo_le ψ) (Common.le_normalizer_prodFactorTwo ψ)
  rwa [inf_assoc, inf_eq_right.2 (Common.prodFactorTwo_le ψ), inf_comm] at h1

theorem s313a_map_conj_t_X_inf_S (hk : Fintype.card k = (2 ^ f) ^ 2) :
    (Common.prodFactorOne ψ ⊓ S).map (MulAut.conj d.t).toMonoidHom =
      Common.prodFactorTwo ψ ⊓ S := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective,
    s313a_map_conj_t_X hp k12 hS hP ψ hk,
    map_conj_eq_of_mem_normalizer (s313a_t_mem_normalizer_S hp k12 hS hP)]

theorem s313a_card_F_Y_eq (hk : Fintype.card k = (2 ^ f) ^ 2) :
    Nat.card (d.F ⊓ centralizer ((Common.prodFactorTwo ψ ⊓ S : Subgroup G) : Set G) :
      Subgroup G) =
    Nat.card (d.F ⊓ centralizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G) :
      Subgroup G) := by
  rw [← s313a_map_conj_t_X_inf_S hp k12 hS hP ψ hk,
    Prelim.inf_centralizer_map_conj hp.hyp.t_mem_normalizer_F, Prelim.card_map_conj]

theorem s313a_M₁_le_normalizer_F : d.M₁ ≤ normalizer (d.F : Set G) :=
  (s313a_M₁_le_L₁ hp k12 hS hP).trans (s313a_L₁_le_normalizer_F hp k12 hS hP)

theorem s313a_F_inf_centralizer_X_inf_centralizer_Y :
    d.F ⊓ centralizer (Common.prodFactorOne ψ : Set G) ⊓
      centralizer (Common.prodFactorTwo ψ : Set G) = ⊥ := by
  rw [eq_bot_iff, ← hp.hyp.F_inf_centralizer_N₁ hp.gms]
  rintro z ⟨⟨hzF, hzX⟩, hzY⟩
  refine Subgroup.mem_inf.2 ⟨hzF, ?_⟩
  have hz : z ∈ centralizer ((Common.prodFactorOne ψ ⊔ Common.prodFactorTwo ψ : Subgroup G) :
      Set G) := by
    rw [Prelim.centralizer_sup_eq]
    exact Subgroup.mem_inf.2 ⟨hzX, hzY⟩
  rw [Common.prodFactorOne_sup_prodFactorTwo] at hz
  exact centralizer_le (SetLike.coe_subset_coe.2 d.N₁_le_M₁) hz

theorem s313a_pair (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hle : Nat.card (CFSG.centerIn (d.Uc S (Common.prodFactorOne ψ))) ≤ (2 ^ f) ^ 4) :
    ∃ P' : Subgroup G, P' ≤ Common.prodFactorOne ψ ∧
      (d.F ⊓ centralizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G)) ⊔
          (d.F ⊓ centralizer (P' : Set G)) = d.F ∧
      (d.F ⊓ centralizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G)) ⊓
          (d.F ⊓ centralizer (P' : Set G)) = ⊥ ∧
      (∃ θ : (Fin 2 → k) → G, Timmesfeld.ARS.IsNaturalModule (Common.prodFactorTwoEquiv ψ) θ ∧
        Set.range θ =
          ↑(d.F ⊓ centralizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G))) ∧
      ∃ θ : (Fin 2 → k) → G, Timmesfeld.ARS.IsNaturalModule (Common.prodFactorTwoEquiv ψ) θ ∧
        Set.range θ = ↑(d.F ⊓ centralizer (P' : Set G)) := by
  have hd := hp.hyp
  have hf2 := hd.two_le
  have hkm : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  obtain ⟨P', hP', hPP'⟩ := exists_isSylowOf_ne hkm (by omega : 1 ≤ 2 * f)
    (Common.prodFactorOneEquiv ψ) (Common.prodFactorOne ψ ⊓ S)
  obtain ⟨Q', hQ', hQQ'⟩ := exists_isSylowOf_ne hkm (by omega : 1 ≤ 2 * f)
    (Common.prodFactorTwoEquiv ψ) (Common.prodFactorTwo ψ ⊓ S)
  have hcomm : ∀ x ∈ Common.prodFactorOne ψ, ∀ y ∈ Common.prodFactorTwo ψ, x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1 (Common.prodFactorOne_le_centralizer ψ hx) y hy).symm
  have hXF : Common.prodFactorOne ψ ≤ normalizer (d.F : Set G) :=
    (Common.prodFactorOne_le ψ).trans (s313a_M₁_le_normalizer_F hp k12 hS hP)
  have hYF : Common.prodFactorTwo ψ ≤ normalizer (d.F : Set G) :=
    (Common.prodFactorTwo_le ψ).trans (s313a_M₁_le_normalizer_F hp k12 hS hP)
  have hcardF : Nat.card d.F = 2 ^ (4 * (2 * f)) := by
    rw [hd.card_F hp.gms, ← pow_mul]
    congr 1
    ring
  have hle' : Nat.card (d.F ⊓ centralizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G) :
      Subgroup G) ≤ 2 ^ (2 * (2 * f)) := by
    rw [← s313a_centerIn_Uc hp k12 hS hP ψ hk]
    calc _ ≤ (2 ^ f) ^ 4 := hle
      _ = 2 ^ (2 * (2 * f)) := by rw [← pow_mul]; congr 1; ring
  have key := sl2_pair_module_small hkm (by omega : 2 ≤ 2 * f) (by omega : 2 * f ≠ 3)
    (hd.isElementaryAbelian_F hp.gms) hcardF (Common.prodFactorOneEquiv ψ)
    (Common.prodFactorTwoEquiv ψ) hXF hYF hcomm
    (s313a_F_inf_centralizer_X_inf_centralizer_Y hp k12 hS hP ψ)
    (s313a_isSylowOf_X_inf_S hp k12 hS hP ψ) hP' hPP'
    (s313a_isSylowOf_Y_inf_S hp k12 hS hP ψ) hQ' hQQ'
    (s313a_card_F_Y_eq hp k12 hS hP ψ hk).symm hle'
  obtain ⟨-, hUU', hUU, -, -, -, -, ⟨θ, hθ, hθr⟩, ⟨θ', hθ', hθ'r⟩⟩ := key
  exact ⟨P', hP'.le, hUU', hUU, ⟨θ, hθ, hθr⟩, ⟨θ', hθ', hθ'r⟩⟩

theorem s313a_free (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hle : Nat.card (CFSG.centerIn (d.Uc S (Common.prodFactorOne ψ))) ≤ (2 ^ f) ^ 4) {j : G}
    (hjY : j ∈ Common.prodFactorTwo ψ) (hodd : Odd (orderOf j)) (hj1 : j ≠ 1) {c : G}
    (hc : c ∈ d.F) (hfix : j * c * j⁻¹ = c) : c = 1 := by
  obtain ⟨P', hP'X, hsup, hinf, ⟨θ, hθ, hθr⟩, ⟨θ', hθ', hθ'r⟩⟩ :=
    s313a_pair hp k12 hS hP ψ hk hle
  set U := d.F ⊓ centralizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G) with hU
  set U' := d.F ⊓ centralizer (P' : Set G) with hU'
  have h2 := s313a_two_eq_zero hp k12 hS hP hk
  have hFcomm : ∀ {v w : G}, v ∈ d.F → w ∈ d.F → v * w = w * v := fun {v w} hv hw =>
    Prelim.mul_comm_of_mem (hp.hyp.isElementaryAbelian_F hp.gms) hv hw
  have hUc : ∀ x ∈ U, ∀ y ∈ U', x * y = y * x := fun x hx y hy => hFcomm hx.1 hy.1
  have hcsup : c ∈ ((U ⊔ U' : Subgroup G) : Set G) := by rw [hsup]; exact hc
  rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U U' hUc).2] at hcsup
  obtain ⟨u, hu, u', hu', hcu⟩ := hcsup
  have hcu' : c = u * u' := hcu.symm
  subst hcu'
  have hYF : Common.prodFactorTwo ψ ≤ normalizer (d.F : Set G) :=
    (Common.prodFactorTwo_le ψ).trans (s313a_M₁_le_normalizer_F hp k12 hS hP)
  have hYU : Common.prodFactorTwo ψ ≤ normalizer (U : Set G) :=
    Prelim.le_normalizer_inf_centralizer hYF
      ((Common.prodFactorTwo_le_centralizer ψ).trans
        (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)))
  have hYU' : Common.prodFactorTwo ψ ≤ normalizer (U' : Set G) :=
    Prelim.le_normalizer_inf_centralizer hYF
      ((Common.prodFactorTwo_le_centralizer ψ).trans
        (centralizer_le (SetLike.coe_subset_coe.2 hP'X)))
  have ha : j * u * j⁻¹ ∈ U := (mem_normalizer_iff.1 (hYU hjY) u).1 hu
  have hb : j * u' * j⁻¹ ∈ U' := (mem_normalizer_iff.1 (hYU' hjY) u').1 hu'
  have hab : (j * u * j⁻¹) * (j * u' * j⁻¹) = u * u' := by
    rw [← hfix]; group
  have e1 : u⁻¹ * (j * u * j⁻¹) = u' * (j * u' * j⁻¹)⁻¹ := by
    calc u⁻¹ * (j * u * j⁻¹) = u⁻¹ * ((j * u * j⁻¹) * (j * u' * j⁻¹)) * (j * u' * j⁻¹)⁻¹ := by
          group
      _ = u⁻¹ * (u * u') * (j * u' * j⁻¹)⁻¹ := by rw [hab]
      _ = u' * (j * u' * j⁻¹)⁻¹ := by group
  have hmem : u⁻¹ * (j * u * j⁻¹) ∈ U ⊓ U' :=
    Subgroup.mem_inf.2 ⟨U.mul_mem (U.inv_mem hu) ha, e1 ▸ U'.mul_mem hu' (U'.inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hu1 : u = 1 := by
    rcases s313a_eq_one_of_odd_fixed h2 (Common.prodFactorTwoEquiv ψ) hθ hjY hodd
      (by rw [hθr]; exact hu) hmem.symm with h | h
    · exact absurd h hj1
    · exact h
  have hb' : j * u' * j⁻¹ = u' := by
    have : u * (j * u' * j⁻¹) = u * u' := by
      have h := hab
      rw [← hmem] at h
      exact h
    exact mul_left_cancel this
  have hu'1 : u' = 1 := by
    rcases s313a_eq_one_of_odd_fixed h2 (Common.prodFactorTwoEquiv ψ) hθ' hjY hodd
      (by rw [hθ'r]; exact hu') hb' with h | h
    · exact absurd h hj1
    · exact h
  rw [hu1, hu'1, one_mul]

theorem s313a_S_inf_M₁_eq :
    S ⊓ d.M₁ = (Common.prodFactorOne ψ ⊓ S) ⊔ (Common.prodFactorTwo ψ ⊓ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := s313a_isSylowOf_X_inf_S hp k12 hS hP ψ
  have hY := s313a_isSylowOf_Y_inf_S hp k12 hS hP ψ
  have hM := s313a_isSylowOf_S_M₁ hp k12 hS hP
  have hcomm : ∀ x ∈ Common.prodFactorOne ψ ⊓ S, ∀ y ∈ Common.prodFactorTwo ψ ⊓ S, x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1
      (Common.prodFactorOne_le_centralizer ψ (Subgroup.mem_inf.1 hx).1) y
      (Subgroup.mem_inf.1 hy).1).symm
  have hcommXY : ∀ x ∈ Common.prodFactorOne ψ, ∀ y ∈ Common.prodFactorTwo ψ, x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1 (Common.prodFactorOne_le_centralizer ψ hx) y hy).symm
  have hbot : (Common.prodFactorOne ψ ⊓ S) ⊓ (Common.prodFactorTwo ψ ⊓ S) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have : z ∈ Common.prodFactorOne ψ ⊓ Common.prodFactorTwo ψ :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).2).1⟩
    rwa [Common.prodFactorOne_inf_prodFactorTwo] at this
  have hc1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hbot, Subgroup.card_bot, mul_one] at hc1
  have hc2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Common.prodFactorOne ψ)
    (Common.prodFactorTwo ψ) hcommXY).1
  rw [Common.prodFactorOne_inf_prodFactorTwo, Subgroup.card_bot, mul_one,
    Common.prodFactorOne_sup_prodFactorTwo] at hc2
  have hle : (Common.prodFactorOne ψ ⊓ S) ⊔ (Common.prodFactorTwo ψ ⊓ S) ≤ S ⊓ d.M₁ :=
    sup_le (fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
        Common.prodFactorOne_le ψ (Subgroup.mem_inf.1 hx).1⟩)
      (fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
        Common.prodFactorTwo_le ψ (Subgroup.mem_inf.1 hx).1⟩)
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hc1, hM.card_eq, hX.card_eq, hY.card_eq, ← pow_add, hc2,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp

theorem s313a_J (hk : Fintype.card k = (2 ^ f) ^ 2) :
    ∃ J : Subgroup G, J ≤ Common.prodFactorTwo ψ ∧ J ≤ normalizer (S : Set G) ∧
      Odd (Nat.card J) ∧ Nat.card J + 1 = Nat.card k := by
  have hd := hp.hyp
  have hf2 := hd.two_le
  have hkm : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  obtain ⟨J, hJY, hJQ, hJc⟩ := s313a_exists_J hkm (by omega : 1 ≤ 2 * f)
    (Common.prodFactorTwoEquiv ψ) (s313a_isSylowOf_Y_inf_S hp k12 hS hP ψ)
  have hpos : 0 < 2 ^ (2 * f) := by positivity
  have hk2 : 2 ≤ 2 ^ (2 * f) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨J, hJY, ?_, ?_, ?_⟩
  · intro j hj
    have hjY := hJY hj
    have hjQ := hJQ hj
    have hD : j ∈ normalizer (d.D : Set G) := hd.L₁_le_normalizer_D
      ((s313a_M₁_le_L₁ hp k12 hS hP) (Common.prodFactorTwo_le ψ hjY))
    have hP₀ : j ∈ normalizer ((Common.prodFactorOne ψ ⊓ S : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _
        (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)
          (Common.prodFactorTwo_le_centralizer ψ hjY))
    have := Common.mem_normalizer_sup hD (Common.mem_normalizer_sup hP₀ hjQ)
    rw [← s313a_S_inf_M₁_eq hp k12 hS hP ψ, ← s313a_S_eq_D_sup hp k12 hS hP] at this
    exact this
  · rw [hJc, hkm]
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ (2 * f) = 2 * m := ⟨2 ^ (2 * f - 1), by
      rw [← pow_succ']; congr 1; omega⟩
    exact ⟨m - 1, by omega⟩
  · rw [hJc, hkm]
    omega

end S313aPsi

end S313a

theorem sec313Trans_of_hyp (hp : d.CaseHyp) (k : d.Know12) : d.Sec313Trans := by
  intro S hS hP κ _ _ hk ψ hle
  have hd := hp.hyp
  have hf2 := hd.two_le
  obtain ⟨J, hJY, hJS, hJodd, hJcard⟩ := s313a_J hp k hS hP ψ hk
  have hFN : d.M₁ ≤ normalizer (d.F : Set G) := s313a_M₁_le_normalizer_F hp k hS hP
  have hJF : J ≤ normalizer (d.F : Set G) :=
    hJY.trans ((Common.prodFactorTwo_le ψ).trans hFN)
  have hJW : J ≤ normalizer (d.W : Set G) := fun j hj =>
    s313a_mem_normalizer_W hp k hS hP (hJS hj)
  refine ⟨J, hJodd, le_inf (le_inf hJS hJF) hJW, ?_⟩
  have hWF : d.W ≤ d.F := s313a_W_le_F hp k hS hP
  have hFcomm : ∀ a ∈ d.F, ∀ b ∈ d.F, a * b = b * a := fun a ha b hb =>
    Prelim.mul_comm_of_mem (hd.isElementaryAbelian_F hp.gms) ha hb
  have hFcard : Nat.card d.F = 2 ^ (f * 8) := by
    rw [hd.card_F hp.gms, ← pow_mul]
  have hfree : ∀ j ∈ J, j ≠ 1 → ∀ x ∈ d.F, x⁻¹ * (j * x * j⁻¹) ∈ d.W → x ∈ d.W := by
    intro j hj hj1 x hxF hx
    have hodd : Odd (orderOf j) := by
      refine Odd.of_dvd_nat hJodd ?_
      rw [← Subgroup.orderOf_mk j hj]
      exact orderOf_dvd_natCard _
    exact s313a_mem_of_fixed_mod hWF hFcomm hFcard (hJF hj) (hJW hj) hodd
      (fun c hc hfix => s313a_free hp k hS hP ψ hk hle (hJY hj) hodd hj1 hc hfix) hxF hx
  refine fun x hx hxW y hy hyW => s313a_exists_conj_mul_inv_mem hWF hFcomm hJF hJW hfree ?_ hx hxW hy hyW
  intro hN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.W.subgroupOf d.F)
  rw [hd.card_F hp.gms, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWF).toEquiv,
    hd.card_W hp.gms] at h1
  have h2 : Nat.card (d.F ⧸ d.W.subgroupOf d.F) = (2 ^ f) ^ 2 := by
    have hpos : 0 < (2 ^ f) ^ 6 := by positivity
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [← h1]
    ring
  rw [h2, ← hk, ← Nat.card_eq_fintype_card] at *
  omega

end Data

namespace CaseBParts

theorem sec313Trans : Sec313TransStatement :=
  fun _ _ _ _ _ _ _ _ hp k => Data.sec313Trans_of_hyp hp k

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
