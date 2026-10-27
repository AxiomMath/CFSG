module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensus
public import CFSG.RankThree.PartOne.SPOR.OuterLy

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ly

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem mul_conj_mul_inv (β : MulAut G) (g : G) :
    β * MulAut.conj g * β⁻¹ = MulAut.conj (β g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem commutatorElement_conj (β : MulAut G) (g : G) :
    ⁅β, MulAut.conj g⁆ = MulAut.conj (β g * g⁻¹) := by
  rw [commutatorElement_def, mul_conj_mul_inv, map_mul, map_inv]

theorem conj_injective_of_center (hc : center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro x y hxy
  have hmem : y⁻¹ * x ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut G => φ g) hxy
    simp only [MulAut.conj_apply] at h
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * y * y⁻¹ * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * y * y⁻¹ * x := by rw [h]
      _ = y⁻¹ * x * g := by group
  rw [hc, mem_bot] at hmem
  calc x = y * (y⁻¹ * x) := by group
    _ = y := by rw [hmem, mul_one]

theorem autModel_mulAut {X₀ : Type*} [Group X₀] (e : G ≃* X₀) (hc : center G = ⊥) :
    AutModel X₀ (MulAut G) (inner G) := by
  have hinj := conj_injective_of_center hc
  set φ : G ≃* inner G := MonoidHom.ofInjective hinj with hφ
  have hφv : ∀ g : G, ((φ g : inner G) : MulAut G) = MulAut.conj g := fun g => rfl
  refine ⟨inner_normal G, ?_, ⟨φ.symm.trans e⟩, fun α => ?_⟩
  · rw [eq_bot_iff]
    intro β hβ
    rw [mem_bot]
    ext g
    have hc' := mem_centralizer_iff.mp hβ (MulAut.conj g) ⟨g, rfl⟩
    have h1 : β * MulAut.conj g * β⁻¹ = MulAut.conj g := by
      rw [← hc']
      group
    rw [mul_conj_mul_inv] at h1
    exact hinj h1
  · refine ⟨(φ.trans α).trans φ.symm, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := φ.surjective x
    have hβg : φ (((φ.trans α).trans φ.symm) g) = α (φ g) := by
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [← hβg, hφv, hφv, mul_conj_mul_inv]

theorem displacement_normal (f : G →* G) :
    (Subgroup.closure {d : G | ∃ c, d = f c * c⁻¹}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    have h : g * (f c * c⁻¹) * g⁻¹ = (f g * g⁻¹)⁻¹ * (f (g * c) * (g * c)⁻¹) := by
      rw [map_mul]
      group
    rw [h]
    exact mul_mem (inv_mem (Subgroup.subset_closure ⟨g, rfl⟩))
      (Subgroup.subset_closure ⟨g * c, rfl⟩)
  | one => simp
  | mul x y _ _ hx hy =>
    have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [h]
    exact mul_mem hx hy
  | inv x _ hx =>
    have h : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem hx

end General

section Quasisimple

variable {T : Type*} [Group T] {z : T} {C : Subgroup T}

theorem apply_mem_of_fix (hC : C = centralizer {z}) {β : MulAut T} (hβ : β z = z) {c : T}
    (hc : c ∈ C) : β c ∈ C := by
  rw [hC, mem_centralizer_singleton_iff] at hc ⊢
  rw [← hβ, ← map_mul, ← map_mul, hc]

@[expose] noncomputable def restrictCent (hC : C = centralizer {z}) (β : MulAut T)
    (hβ : β z = z) : ↥C →* ↥C where
  toFun c := ⟨β c, apply_mem_of_fix hC hβ c.2⟩
  map_one' := Subtype.ext (map_one β)
  map_mul' x y := Subtype.ext (map_mul β (x : T) (y : T))

theorem closure_displacement_eq_top (hC : C = centralizer {z})
    (hq : CFSG.Open.IsQuasisimple ↥C)
    (hfix : ∀ α : MulAut T, (∀ c ∈ C, α c = c) → α = 1 ∨ α = MulAut.conj z)
    {β : MulAut T} (hβ : β z = z) (hβz : β ∉ zpowers (MulAut.conj z)) :
    Subgroup.closure {d : ↥C | ∃ c, d = restrictCent hC β hβ c * c⁻¹} = ⊤ := by
  have : Group.IsPerfect ↥C := ⟨hq.1⟩
  have := displacement_normal (restrictCent hC β hβ)
  rcases Quasisimple.normal_le_center_or_eq_top hq
      (Subgroup.closure {d : ↥C | ∃ c, d = restrictCent hC β hβ c * c⁻¹}) with h | h
  · exfalso
    have hcen : ∀ c : ↥C, c⁻¹ * restrictCent hC β hβ c ∈ center ↥C := by
      intro c
      have h1 := h (Subgroup.subset_closure ⟨c, rfl⟩)
      have h2 : c⁻¹ * restrictCent hC β hβ c = c⁻¹ * (restrictCent hC β hβ c * c⁻¹) * c := by
        group
      rw [h2]
      have hn := (inferInstance : (center ↥C).Normal).conj_mem _ h1 c⁻¹
      rwa [inv_inv] at hn
    have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement _ hcen
    have hβfix : ∀ c ∈ C, β c = c := by
      intro c hc
      have := congrArg (fun f : ↥C →* ↥C => ((f ⟨c, hc⟩ : ↥C) : T)) hid
      simpa [restrictCent] using this
    rcases hfix β hβfix with h1 | h1
    · exact hβz (h1 ▸ one_mem _)
    · exact hβz (h1 ▸ mem_zpowers _)
  · exact h

variable [Finite T]

theorem yWitness_of_mem_quasisimple (hc : center T = ⊥) (hz : orderOf z = 2)
    (hC : C = centralizer {z}) (hq : CFSG.Open.IsQuasisimple ↥C)
    (hfix : ∀ α : MulAut T, (∀ c ∈ C, α c = c) → α = 1 ∨ α = MulAut.conj z)
    (h4 : ∃ y : ↥C, 4 ∣ orderOf y) {E : Subgroup (MulAut T)} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (hzE : MulAut.conj z ∈ E) : YWitness (inner T) E := by
  have hinj := conj_injective_of_center hc
  have : Finite (MulAut T) :=
    Finite.of_injective (fun f : MulAut T => (f : T → T)) DFunLike.coe_injective
  set ι := MulAut.conj z with hι
  have hord : orderOf ι = 2 := by rw [hι, orderOf_injective _ hinj, hz]
  have hι1 : ι ≠ 1 := fun h => by rw [h, orderOf_one] at hord; exact absurd hord (by norm_num)
  obtain ⟨β, hβE, hβz⟩ : ∃ β ∈ E, β ∉ zpowers ι := by
    by_contra hcon
    push Not at hcon
    have hcard := card_le_of_le (show E ≤ zpowers ι from hcon)
    rw [Nat.card_zpowers, hord] at hcard
    omega
  have hcomm : β * ι = ι * β :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨β, hβE⟩ ⟨ι, hzE⟩)
  have hβfix : β z = z := by
    apply hinj
    rw [← mul_conj_mul_inv]
    change β * ι * β⁻¹ = ι
    rw [hcomm, mul_inv_cancel_right]
  set ψ := (MulAut.conj (G := T)).comp C.subtype with hψ
  have hΓ : ∀ c ∈ C, MulAut.conj c ∈ gammaE (inner T) E := by
    intro c hc
    have hle : centDer (inner T) ι ≤ gammaE (inner T) E :=
      le_iSup₂_of_le ι hzE (le_iSup_of_le hι1 le_rfl)
    refine hle ?_
    have hc' : (⟨c, hc⟩ : ↥C) ∈ commutator ↥C := by rw [hq.1]; trivial
    rw [_root_.commutator_def] at hc'
    have hmap : ψ ⟨c, hc⟩ ∈ Subgroup.map ψ ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ :=
      mem_map_of_mem ψ hc'
    rw [map_commutator] at hmap
    show ψ ⟨c, hc⟩ ∈ ⁅inner T ⊓ centralizer {ι}, inner T ⊓ centralizer {ι}⁆
    refine commutator_mono ?_ ?_ hmap <;>
    · rintro _ ⟨d, -, rfl⟩
      refine mem_inf.mpr ⟨⟨(d : T), rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hd : (d : T) * z = z * d :=
        mem_centralizer_singleton_iff.mp (hC.le d.2)
      show MulAut.conj (d : T) * MulAut.conj z = MulAut.conj z * MulAut.conj (d : T)
      rw [← map_mul, ← map_mul, hd]
  have hD : Subgroup.closure {d : ↥C | ∃ c, d = restrictCent hC β hβfix c * c⁻¹} ≤
      (nE (inner T) E).comap ψ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    show ψ (restrictCent hC β hβfix c * c⁻¹) ∈ nE (inner T) E
    have he : ψ (restrictCent hC β hβfix c * c⁻¹) = ⁅β, MulAut.conj (c : T)⁆ := by
      rw [commutatorElement_conj]
      rfl
    rw [he]
    exact commutator_mem_commutator hβE (hΓ c c.2)
  rw [closure_displacement_eq_top hC hq hfix hβfix hβz] at hD
  obtain ⟨y, hy⟩ := h4
  have hψinj : Function.Injective ψ := hinj.comp C.subtype_injective
  exact Or.inl ⟨ψ y, hD (mem_top y), by rwa [orderOf_injective ψ hψinj]⟩

theorem yCensus_inner_of_quasisimple (hc : center T = ⊥) (hout : Nat.card (Outer T) ∣ 2)
    (hz : orderOf z = 2) (hfus : ∀ t : T, orderOf t = 2 → ∃ x : T, x * z * x⁻¹ = t)
    (hC : C = centralizer {z}) (hq : CFSG.Open.IsQuasisimple ↥C)
    (hfix : ∀ α : MulAut T, (∀ c ∈ C, α c = c) → α = 1 ∨ α = MulAut.conj z)
    (h4 : ∃ y : ↥C, 4 ∣ orderOf y) : YCensus (inner T) (fun _ => False) := by
  intro E hE hE4 _
  have hinj := conj_injective_of_center hc
  set X := inner T
  obtain ⟨e, heE, heX, he1⟩ : ∃ e ∈ E, e ∈ X ∧ e ≠ 1 := by
    have hidx : X.relIndex E ∣ 2 := (relIndex_dvd_index_of_normal X E).trans hout
    have hmul := (X.subgroupOf E).card_mul_index
    rw [show (X.subgroupOf E).index = X.relIndex E from rfl] at hmul
    have hle : X.relIndex E ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    have hcard : 1 < Nat.card (X.subgroupOf E) := by
      by_contra hcon
      push Not at hcon
      have : Nat.card E ≤ 2 := by
        calc Nat.card E = Nat.card (X.subgroupOf E) * X.relIndex E := hmul.symm
          _ ≤ 1 * 2 := Nat.mul_le_mul hcon hle
          _ = 2 := by norm_num
      omega
    obtain ⟨x, hx⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot _).mp hcard)
    exact ⟨x.1.1, x.1.2, (mem_subgroupOf).mp x.2, fun h => hx (Subtype.ext (Subtype.ext h))⟩
  obtain ⟨j, rfl⟩ := (MonoidHom.mem_range).mp
    (show e ∈ (MulAut.conj (G := T)).range from heX)
  have hj1 : j ≠ 1 := fun h => he1 (by rw [h, map_one])
  have hj2 : orderOf j = 2 := by
    have h2 : (MulAut.conj j) ^ 2 = 1 := hE.2 _ heE
    rw [← map_pow] at h2
    have hj2' : j ^ 2 = 1 := hinj (by rw [h2, map_one])
    exact orderOf_eq_prime hj2' hj1
  obtain ⟨x, hx⟩ := hfus j hj2
  set w := (MulAut.conj x)⁻¹
  set σ := MulAut.conj w
  have hzE : MulAut.conj z ∈ E.map σ.toMonoidHom := by
    refine ⟨MulAut.conj j, heE, ?_⟩
    show w * MulAut.conj j * w⁻¹ = MulAut.conj z
    rw [mul_conj_mul_inv]
    congr 1
    simp only [w, MulAut.conj_inv_apply, ← hx]
    group
  have hw := yWitness_of_mem_quasisimple hc hz hC hq hfix h4
    (isElemAbelian_map hE σ.toMonoidHom) (by rwa [card_map_of_injective σ.injective]) hzE
  rwa [← map_conj_eq_of_normal (inner_normal T) w,
    yWitness_map_iff σ.toMonoidHom σ.injective] at hw

end Quasisimple

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

theorem card_J : Nat.card ↥J = 51765179004000000 := by
  rw [← Nat.card_congr lyEquivJ.toEquiv]
  exact card_Ly'

theorem center_J : center ↥J = ⊥ := by
  have : IsSimpleGroup ↥J := isSimpleGroup_J
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥J) with h | h
  · exact h
  · exfalso
    let _ : CommGroup ↥J :=
      { (inferInstance : Group ↥J) with
        mul_comm := fun a b => mem_center_iff.mp (h ▸ mem_top b) a }
    have hp := IsSimpleGroup.prime_card (α := ↥J)
    rw [card_J] at hp
    exact absurd hp (by norm_num)

theorem lyAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Ly) (MulAut ↥J) (inner ↥J) :=
  autModel_mulAut (G := ↥J) (X₀ := Blueprint.NativeSporadic.Carrier .Ly) lyEquivJ.symm center_J

instance finite_mulAut_J : Finite (MulAut ↥J) :=
  Finite.of_injective (fun f : MulAut ↥J => (f : ↥J → ↥J)) DFunLike.coe_injective

@[expose] noncomputable def lyCenterQuotEquiv :
    ↥lyC ⧸ center ↥lyC ≃* alternatingGroup (Fin 11) :=
  (QuotientGroup.quotientMulEquivOfEq center_lyC).trans lyCoverEquiv

theorem isQuasisimple_C :
    CFSG.Open.IsQuasisimple ↥lyC := by
  have : IsSimpleGroup (alternatingGroup (Fin 11)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨commutator_lyC, lyCenterQuotEquiv.isSimpleGroup⟩

@[expose] def sigma4 : alternatingGroup (Fin 11) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

theorem orderOf_sigma4 : orderOf sigma4 = 4 := by
  have h1 : ¬ sigma4 ^ 2 ^ 1 = 1 := by
    intro h
    have := congrArg (fun p : alternatingGroup (Fin 11) => (p : Equiv.Perm (Fin 11)) 0) h
    revert this
    decide
  have h2 : sigma4 ^ 2 ^ (1 + 1) = 1 := by
    apply Subtype.ext
    decide
  exact orderOf_eq_prime_pow h1 h2

theorem exists_four_dvd_orderOf_C :
    ∃ y : ↥lyC, 4 ∣ orderOf y := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center ↥lyC) (lyCenterQuotEquiv.symm sigma4)
  refine ⟨y, ?_⟩
  have h := orderOf_map_dvd (lyCenterQuotEquiv.toMonoidHom.comp (QuotientGroup.mk' _)) y
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hy,
    MulEquiv.apply_symm_apply, orderOf_sigma4] at h
  exact h

theorem ly_yCensus :
    YCensus (inner ↥J) (fun _ => False) :=
  yCensus_inner_of_quasisimple (T := ↥J) (z := lyz) (C := lyC) center_J
    CFSG.RankThree.PartOne.SPOR.card_outer_J_dvd' orderOf_a
    (involution_centralizer_fusion_generator).2 lyC_eq_centralizer isQuasisimple_C
    (fun _ h => fixes_C_cases h) exists_four_dvd_orderOf_C

theorem sporadicCaseOdd_Ly
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Ly :=
  sporadicCaseOdd_of_yCensus h32 h33 lyAutModel ly_yCensus

end CFSG.ComponentClassification.RankTwoSporadic.Ly
