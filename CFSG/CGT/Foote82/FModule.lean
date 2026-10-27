module

public import CFSG.CGT.Foote82.TildeULin
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.CGT.Foote82.FPrimeDefs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

private theorem normal_le_center_or_eq_top {Q : Type*} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q) (N : Subgroup Q) [hN : N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hs⟩ := hq
  have hnormal : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hker : N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker :=
      Subgroup.map_eq_bot_iff _ |>.mp hbot
    simpa only [QuotientGroup.ker_mk'] using hker
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hderived
    exact top_unique hderived

private theorem le_ker_of_ne_top {J T : Type*} [Group J] [Group T]
    (hq : CFSG.Open.IsQuasisimple (J ⧸ CFSG.pCore 2 J))
    (hres : ∀ (N : Subgroup J) [N.Normal], IsPGroup 2 (J ⧸ N) → N = ⊤)
    (α : J →* T) (hα : Function.Surjective α) (hP : CFSG.pCore 2 J ≤ α.ker)
    (hZ : Subgroup.center T = ⊥) (C : Subgroup J) [C.Normal] (hC : C ≠ ⊤) : C ≤ α.ker := by
  haveI hCn : (C.map (QuotientGroup.mk' (CFSG.pCore 2 J))).Normal :=
    Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  rcases normal_le_center_or_eq_top hq (C.map (QuotientGroup.mk' (CFSG.pCore 2 J))) with h | h
  · intro c hc
    have hc' : QuotientGroup.mk' (CFSG.pCore 2 J) c ∈ Subgroup.center (J ⧸ CFSG.pCore 2 J) :=
      h (Subgroup.mem_map_of_mem _ hc)
    have hcen : α c ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨y, rfl⟩ := hα t
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 J) (y * c) =
          QuotientGroup.mk' (CFSG.pCore 2 J) (c * y) := by
        rw [map_mul, map_mul]
        exact (Subgroup.mem_center_iff.mp hc' _)
      have h2 : (y * c)⁻¹ * (c * y) ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp h1
      have h3 := hP h2
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul] at h3
      exact h3
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hcen
  · exfalso
    apply hC
    have hsup : C ⊔ CFSG.pCore 2 J = ⊤ := by
      have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 J)) C
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    refine hres C ?_
    refine IsPGroup.of_surjective (CFSG.pCore_isPGroup (p := 2) (G := J))
      ((QuotientGroup.mk' C).comp (CFSG.pCore 2 J).subtype) ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C q
    have hx : x ∈ C ⊔ CFSG.pCore 2 J := hsup ▸ Subgroup.mem_top x
    obtain ⟨c, hc, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨p, hp⟩, ?_⟩
    have hc1 : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, hc1, one_mul]

private theorem matrix_faithful {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι (ZMod 2))
    (h : ∀ a : ι → ZMod 2, a = (g : Matrix ι ι (ZMod 2)) *ᵥ a) : g = 1 := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [Units.val_one, Matrix.one_mulVec]
  exact (h v).symm

private theorem isElementaryAbelian_tildeU {J : Subgroup G} (hJ : IsFooteBlock J J) :
    CFSG.IsElementaryAbelian 2 (tildeU J) := by
  have hcomm : ∀ a b : tildeU J, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have := IsFooteBlock.commutator_mem_blockZ hJ (u := (b : G)⁻¹) (v := (a : G)⁻¹)
          ((blockU J).inv_mem b.2) ((blockU J).inv_mem a.2)
        simpa [commutatorElement_def, mul_assoc] using this
  refine { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact IsFooteBlock.sq_mem_blockZ hJ a.2

namespace TildeULin

variable {J₁ J₂ X : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (lin : TildeULin J₂ X V)

private structure Ctx (J₁ J₂ X : Subgroup G) : Prop where
  h1 : IsFooteBlock J₁ J₁
  h2 : IsFooteBlock J₂ J₂
  le : J₁ ≤ J₂
  leX : J₁ ≤ X
  hU : blockU J₁ = ⁅blockQ J₂, J₁⁆

private theorem Ctx.blockU_le (c : Ctx J₁ J₂ X) : blockU J₁ ≤ blockU J₂ :=
  TildeULin.blockU_le_blockU c.le c.hU

private theorem conj_mem_blockU_of_mem {A : Subgroup G} {x : G} (hx : x ∈ A) {w : G}
    (hw : w ∈ blockU A) : x * w * x⁻¹ ∈ blockU A :=
  (Subgroup.mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_right (blockQ A) A hx) w).mp hw

private noncomputable def ρ₁ (hJ₁X : J₁ ≤ X) : ↥J₁ →* GLV V :=
  lin.ρ.comp (Subgroup.inclusion hJ₁X)

private theorem mem_img_iff (hJ₁X : J₁ ≤ X) (k : GLV V) :
    k ∈ lin.img J₁ ↔ ∃ j : ↥J₁, lin.ρ (Subgroup.inclusion hJ₁X j) = k := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Subgroup.inclusion hJ₁X j, j.2, rfl⟩

private noncomputable def ρ₁' (hJ₁X : J₁ ≤ X) : ↥J₁ →* ↥(lin.img J₁) :=
  (lin.ρ₁ hJ₁X).codRestrict (lin.img J₁) fun j => (lin.mem_img_iff hJ₁X _).mpr ⟨j, rfl⟩

private theorem ρ₁'_surjective (hJ₁X : J₁ ≤ X) : Function.Surjective (lin.ρ₁' hJ₁X) := by
  rintro ⟨k, hk⟩
  obtain ⟨j, rfl⟩ := (lin.mem_img_iff hJ₁X k).mp hk
  exact ⟨j, rfl⟩

private theorem ker_ρ₁' (hJ₁X : J₁ ≤ X) : (lin.ρ₁' hJ₁X).ker = (lin.ρ₁ hJ₁X).ker :=
  MonoidHom.ker_codRestrict _ _ _

private theorem ker_ρ₁_ne_top (hJ₁X : J₁ ≤ X) (hirr : HasIrrTildeV (lin.img J₁)) :
    (lin.ρ₁ hJ₁X).ker ≠ ⊤ := by
  intro htop
  have hcomm : commSpace (lin.img J₁) ⊤ = ⊥ := by
    refine Submodule.span_eq_bot.mpr ?_
    rintro w ⟨k, hk, u, -, rfl⟩
    obtain ⟨j, rfl⟩ := (lin.mem_img_iff hJ₁X k).mp hk
    have hj : j ∈ (lin.ρ₁ hJ₁X).ker := htop ▸ Subgroup.mem_top j
    have h1 : lin.ρ (Subgroup.inclusion hJ₁X j) = 1 := hj
    rw [h1]
    simp
  have hlt := hirr.1
  rw [hcomm] at hlt
  exact not_lt_bot hlt

private theorem vec_mem_commSpace (c : Ctx J₁ J₂ X) (u : ↥(blockU J₂)) (hu : (u : G) ∈ blockU J₁) :
    lin.vec u ∈ commSpace (lin.img J₁) ⊤ := by
  rw [lin.commSpace_img_eq c.h2 c.h1 c.leX c.le c.hU]
  exact Submodule.subset_span ⟨u, hu, rfl⟩

private theorem exists_vec_eq (c : Ctx J₁ J₂ X) (w : V) (hw : w ∈ commSpace (lin.img J₁) ⊤) :
    ∃ u : ↥(blockU J₂), (u : G) ∈ blockU J₁ ∧ lin.vec u = w := by
  rw [lin.commSpace_img_eq c.h2 c.h1 c.leX c.le c.hU] at hw
  exact (lin.mem_vecImg_iff c.blockU_le w).mp hw

private theorem vec_one : lin.vec (1 : ↥(blockU J₂)) = 0 := by
  show Multiplicative.toAdd (lin.π 1) = 0
  rw [map_one]
  rfl

private theorem mem_blockZ_iff (c : Ctx J₁ J₂ X) (u : ↥(blockU J₂)) (hu : (u : G) ∈ blockU J₁) :
    (u : G) ∈ blockZ J₁ ↔ lin.vec u ∈ fixedSpace (lin.img J₁) := by
  rw [← lin.vec_mem_tildeVBot_iff c.h2 c.h1 c.leX c.le c.hU u hu]
  exact ⟨fun h => h.1, fun h => ⟨h, lin.vec_mem_commSpace c u hu⟩⟩

private noncomputable def uHom (c : Ctx J₁ J₂ X) :
    ↥(blockU J₁) →* Multiplicative ↥(commSpace (lin.img J₁) ⊤) where
  toFun u := Multiplicative.ofAdd
    ⟨lin.vec (Subgroup.inclusion c.blockU_le u), lin.vec_mem_commSpace c _ u.2⟩
  map_one' := by
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    exact lin.vec_one
  map_mul' u v := by
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    exact lin.vec_mul (Subgroup.inclusion c.blockU_le u) (Subgroup.inclusion c.blockU_le v)

private theorem uHom_apply (c : Ctx J₁ J₂ X) (u : ↥(blockU J₁)) :
    ((Multiplicative.toAdd (lin.uHom c u) : ↥(commSpace (lin.img J₁) ⊤)) : V) =
      lin.vec (Subgroup.inclusion c.blockU_le u) := rfl

private theorem uHom_surjective (c : Ctx J₁ J₂ X) : Function.Surjective (lin.uHom c) := by
  intro w
  obtain ⟨u, hu, hw⟩ := lin.exists_vec_eq c (Multiplicative.toAdd w : ↥(commSpace (lin.img J₁) ⊤))
    (Multiplicative.toAdd w).2
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hw

private theorem mem_blockZ_of_uHom_eq_one (c : Ctx J₁ J₂ X) (u : ↥(blockU J₁))
    (hu : lin.uHom c u = 1) : (u : G) ∈ blockZ J₁ := by
  have h0 : lin.vec (Subgroup.inclusion c.blockU_le u) = 0 :=
    congrArg (fun w => ((Multiplicative.toAdd w : ↥(commSpace (lin.img J₁) ⊤)) : V)) hu
  exact (lin.mem_blockZ_iff c (Subgroup.inclusion c.blockU_le u) u.2).mpr
    (by rw [h0]; exact Submodule.zero_mem _)

private theorem tildeVWitness_of_blockWitness (c : Ctx J₁ J₂ X) {T M : Type} [Group T]
    [AddGroup M] (R : T → M → M → Prop) (α : ↥J₁ →* T) (hα : Function.Surjective α)
    (hαk : (lin.ρ₁ c.leX).ker ≤ α.ker) (β : ↥(blockU J₁) →* Multiplicative M)
    (hβ : Function.Surjective β) (hβk : β.ker = (blockZ J₁).subgroupOf (blockU J₁))
    (hR : ∀ (ℓ : ↥J₁) (u v : ↥(blockU J₁)), (v : G) = ℓ * u * (ℓ : G)⁻¹ →
      R (α ℓ) (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v))) :
    TildeVWitness (lin.img J₁) T M R := by
  obtain ⟨α', hα'⟩ : ∃ α' : ↥(lin.img J₁) →* T, ∀ j, α' (lin.ρ₁' c.leX j) = α j :=
    ⟨(lin.ρ₁' c.leX).liftOfSurjective (lin.ρ₁'_surjective c.leX) ⟨α, by
      rw [lin.ker_ρ₁']
      exact hαk⟩, fun j => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ j⟩
  have hker : (lin.uHom c).ker ≤ β.ker := by
    intro u hu
    rw [hβk, Subgroup.mem_subgroupOf]
    exact lin.mem_blockZ_of_uHom_eq_one c u hu
  obtain ⟨β', hβ'⟩ : ∃ β' : Multiplicative ↥(commSpace (lin.img J₁) ⊤) →* Multiplicative M,
      ∀ u, β' (lin.uHom c u) = β u :=
    ⟨(lin.uHom c).liftOfSurjective (lin.uHom_surjective c) ⟨β, hker⟩,
      fun u => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u⟩
  refine ⟨α', ?_, AddMonoidHom.toMultiplicative.symm β', ?_, ?_, ?_⟩
  · intro t
    obtain ⟨j, rfl⟩ := hα t
    exact ⟨lin.ρ₁' c.leX j, hα' j⟩
  · intro a
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd a)
    refine ⟨Multiplicative.toAdd (lin.uHom c u), ?_⟩
    show Multiplicative.toAdd (β' (Multiplicative.ofAdd (Multiplicative.toAdd (lin.uHom c u)))) = a
    rw [ofAdd_toAdd, hβ', hu]
    rfl
  · ext w
    obtain ⟨u, hu⟩ := lin.uHom_surjective c (Multiplicative.ofAdd w)
    have hw : (w : V) = lin.vec (Subgroup.inclusion c.blockU_le u) := by
      have := lin.uHom_apply c u
      rw [hu] at this
      exact this
    have hβw : (AddMonoidHom.toMultiplicative.symm β' w) = Multiplicative.toAdd (β u) := by
      show Multiplicative.toAdd (β' (Multiplicative.ofAdd w)) = _
      rw [← hu, hβ']
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      Submodule.subtype_apply]
    have hZ : (u : G) ∈ blockZ J₁ ↔
        lin.vec (Subgroup.inclusion c.blockU_le u) ∈ fixedSpace (lin.img J₁) :=
      lin.mem_blockZ_iff c (Subgroup.inclusion c.blockU_le u) u.2
    rw [hβw, hw, toAdd_eq_zero, ← hZ, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  · intro ℓ w w' hww'
    obtain ⟨j, rfl⟩ := lin.ρ₁'_surjective c.leX ℓ
    obtain ⟨u, hu⟩ := lin.uHom_surjective c (Multiplicative.ofAdd w)
    obtain ⟨u', hu'⟩ := lin.uHom_surjective c (Multiplicative.ofAdd w')
    set v : ↥(blockU J₁) :=
      ⟨(j : G) * (u : G) * (j : G)⁻¹, conj_mem_blockU_of_mem j.2 u.2⟩ with hv
    have hw : (w : V) = lin.vec (Subgroup.inclusion c.blockU_le u) := by
      have := lin.uHom_apply c u
      rw [hu] at this
      exact this
    have hw' : (w' : V) = lin.vec (Subgroup.inclusion c.blockU_le u') := by
      have := lin.uHom_apply c u'
      rw [hu'] at this
      exact this
    have hρ : lin.ρ (Subgroup.inclusion c.leX j) (lin.vec (Subgroup.inclusion c.blockU_le u)) =
        lin.vec (Subgroup.inclusion c.blockU_le v) :=
      lin.ρ_vec _ _ _ rfl
    have hvec : lin.uHom c u' = lin.uHom c v := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      rw [lin.uHom_apply, lin.uHom_apply, ← hw', ← hρ, hww', ← hw]
      rfl
    have hβv : β u' = β v := by
      rw [← hβ', ← hβ', hvec]
    have hβw : (AddMonoidHom.toMultiplicative.symm β' w) = Multiplicative.toAdd (β u) := by
      show Multiplicative.toAdd (β' (Multiplicative.ofAdd w)) = _
      rw [← hu, hβ']
    have hβw' : (AddMonoidHom.toMultiplicative.symm β' w') = Multiplicative.toAdd (β u') := by
      show Multiplicative.toAdd (β' (Multiplicative.ofAdd w')) = _
      rw [← hu', hβ']
    rw [hα', hβw, hβw', hβv]
    exact hR j u v rfl

private theorem exists_surjective_of_ker_le (c : Ctx J₁ J₂ X) {T : Type} [Group T]
    (α : ↥J₁ →* T) (hα : Function.Surjective α) (hαk : (lin.ρ₁ c.leX).ker ≤ α.ker) :
    ∃ α' : ↥(lin.img J₁) →* T, Function.Surjective α' := by
  refine ⟨(lin.ρ₁' c.leX).liftOfSurjective (lin.ρ₁'_surjective c.leX) ⟨α, by
      rw [lin.ker_ρ₁']
      exact hαk⟩, fun t => ?_⟩
  obtain ⟨j, rfl⟩ := hα t
  exact ⟨lin.ρ₁' c.leX j, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ j⟩

private theorem ker_le_of_blockWitness (c : Ctx J₁ J₂ X) {T M : Type} [Group T] [AddGroup M]
    (R : T → M → M → Prop) (hfaith : ∀ g : T, (∀ a : M, R g a a) → g = 1)
    (α : ↥J₁ →* T) (β : ↥(blockU J₁) →* Multiplicative M) (hβ : Function.Surjective β)
    (hβk : β.ker = (blockZ J₁).subgroupOf (blockU J₁))
    (hR : ∀ (ℓ : ↥J₁) (u v : ↥(blockU J₁)), (v : G) = ℓ * u * (ℓ : G)⁻¹ →
      R (α ℓ) (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v))) :
    (lin.ρ₁ c.leX).ker ≤ α.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  apply hfaith
  intro a
  obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd a)
  set v : ↥(blockU J₁) := ⟨(x : G) * (u : G) * (x : G)⁻¹, conj_mem_blockU_of_mem x.2 u.2⟩ with hv
  have hρx : lin.ρ (Subgroup.inclusion c.leX x) = 1 := hx
  have h := lin.commutator_mem_blockZ_of_ρ_eq_one c.h2 c.h1 c.leX c.le c.hU
    (Subgroup.inclusion c.leX x) x.2 hρx (u : G) u.2
  have hmem : v * u⁻¹ ∈ β.ker := by
    rw [hβk, Subgroup.mem_subgroupOf]
    exact h
  have hβvu : β v = β u := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hmem
    exact hmem
  have := hR x u v rfl
  rwa [hβvu, hu, toAdd_ofAdd] at this

private theorem ker_le_of_center_bot (c : Ctx J₁ J₂ X) (hirr : HasIrrTildeV (lin.img J₁))
    {T : Type} [Group T] (α : ↥J₁ →* T) (hα : Function.Surjective α)
    (hP : CFSG.pCore 2 ↥J₁ ≤ α.ker) (hZ : Subgroup.center T = ⊥) :
    (lin.ρ₁ c.leX).ker ≤ α.ker :=
  le_ker_of_ne_top c.h1.quasisimple (fun N _ h => c.h1.residual N h) α hα hP hZ _
    (lin.ker_ρ₁_ne_top c.leX hirr)

private theorem finrank_tildeV_img (c : Ctx J₁ J₂ X) {k : ℕ}
    (hk : CFSG.pRank 2 (tildeU J₁) = k) :
    Module.finrank (ZMod 2) (TildeV (lin.img J₁)) = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isElementaryAbelian_tildeU c.h1
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 (tildeU J₁)).exists_card_eq
  have hnk : n = k := (CFSG.pRank_eq_of_card_eq_pow one_lt_two hn).symm.trans hk
  let q : Submodule (ZMod 2) ↥(commSpace (lin.img J₁) ⊤) :=
    (fixedSpace (lin.img J₁)).comap (commSpace (lin.img J₁) ⊤).subtype
  let Θ : ↥(blockU J₁) →* Multiplicative (TildeV (lin.img J₁)) :=
    (AddMonoidHom.toMultiplicative (Submodule.mkQ q).toAddMonoidHom).comp (lin.uHom c)
  have hΘs : Function.Surjective Θ := by
    intro y
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective q (Multiplicative.toAdd y)
    obtain ⟨u, hu⟩ := lin.uHom_surjective c (Multiplicative.ofAdd w)
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    show (Submodule.mkQ q) (Multiplicative.toAdd (lin.uHom c u)) = _
    rw [hu, toAdd_ofAdd, hw]
  have hΘk : Θ.ker = (blockZ J₁).subgroupOf (blockU J₁) := by
    ext u
    have hZ : (u : G) ∈ blockZ J₁ ↔
        lin.vec (Subgroup.inclusion c.blockU_le u) ∈ fixedSpace (lin.img J₁) :=
      lin.mem_blockZ_iff c (Subgroup.inclusion c.blockU_le u) u.2
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hZ]
    show Multiplicative.ofAdd (Submodule.mkQ q (Multiplicative.toAdd (lin.uHom c u))) = 1 ↔ _
    rw [ofAdd_eq_one, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    rfl
  have hcard := card_tildeU_eq_of_surjective Θ hΘs hΘk
  have h2 : Nat.card (TildeV (lin.img J₁)) =
      2 ^ Module.finrank (ZMod 2) (TildeV (lin.img J₁)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hn, h2] at hcard
  rw [← hnk]
  exact (Nat.pow_right_injective le_rfl hcard).symm

theorem isAltNaturalModule_img (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂)
    (hJ₁J₂ : J₁ ≤ J₂) (hJ₁X : J₁ ≤ X) (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆) {n : ℕ} (hn : 6 ≤ n)
    (hA : IsAltNaturalType J₁ n) : IsAltNaturalModule (lin.img J₁) n := by
  have c : Ctx J₁ J₂ X := ⟨h1, h2, hJ₁J₂, hJ₁X, hU⟩
  have hirr : HasIrrTildeV (lin.img J₁) := lin.hasIrrTildeV_img h2 h1 hJ₁X hJ₁J₂ hU
  obtain ⟨α, hα, hαk, β, hβ, hβk, hR⟩ := hA
  have hker := lin.ker_le_of_center_bot c hirr α hα hαk.ge
    (alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ n)))
  exact lin.tildeVWitness_of_blockWitness c
    (fun (σ : alternatingGroup (Fin n)) (a b : altHeart n) =>
      ∀ x : evenWeight n, a = (x : altHeart n) →
        b = (evenWeightPerm (σ : Equiv.Perm (Fin n)) x : altHeart n))
    α hα hker β hβ hβk hR

theorem isA7FourModule_img (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂)
    (hJ₁J₂ : J₁ ≤ J₂) (hJ₁X : J₁ ≤ X) (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆)
    (hA : IsA7FourType J₁) : IsA7FourModule (lin.img J₁) := by
  have c : Ctx J₁ J₂ X := ⟨h1, h2, hJ₁J₂, hJ₁X, hU⟩
  have hirr : HasIrrTildeV (lin.img J₁) := lin.hasIrrTildeV_img h2 h1 hJ₁X hJ₁J₂ hU
  obtain ⟨⟨α, hα, hαk⟩, hr⟩ := hA
  have hker := lin.ker_le_of_center_bot c hirr α hα hαk.ge
    (alternatingGroup.center_eq_bot (by simp))
  exact ⟨lin.exists_surjective_of_ker_le c α hα hker, lin.finrank_tildeV_img c hr⟩

theorem isOmegaPlusModule_img (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂)
    (hJ₁J₂ : J₁ ≤ J₂) (hJ₁X : J₁ ≤ X) (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆) {m : ℕ}
    (hA : IsOmegaPlusType J₁ m) : IsOmegaPlusModule (lin.img J₁) m := by
  have c : Ctx J₁ J₂ X := ⟨h1, h2, hJ₁J₂, hJ₁X, hU⟩
  obtain ⟨α, hα, hαk, β, hβ, hβk, hR⟩ := hA
  let R : ↥(omegaPlusTwo m) → (Fin m ⊕ Fin m → ZMod 2) → (Fin m ⊕ Fin m → ZMod 2) → Prop :=
    fun g a b => b = ((g : GL (Fin m ⊕ Fin m) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) *ᵥ a
  have hker := lin.ker_le_of_blockWitness c R
    (fun g hg => Subtype.ext (matrix_faithful _ fun a => hg a)) α β hβ hβk hR
  exact lin.tildeVWitness_of_blockWitness c R α hα hker β hβ hβk hR

theorem isOmegaMinusModule_img (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂)
    (hJ₁J₂ : J₁ ≤ J₂) (hJ₁X : J₁ ≤ X) (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆) {m : ℕ}
    (hA : IsOmegaMinusType J₁ m) : IsOmegaMinusModule (lin.img J₁) m := by
  have c : Ctx J₁ J₂ X := ⟨h1, h2, hJ₁J₂, hJ₁X, hU⟩
  obtain ⟨α, hα, hαk, β, hβ, hβk, hR⟩ := hA
  let R : ↥(omegaMinusTwo m) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →
      (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) → Prop :=
    fun g a b => b = ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a
  have hker := lin.ker_le_of_blockWitness c R
    (fun g hg => Subtype.ext (matrix_faithful _ fun a => hg a)) α β hβ hβk hR
  exact lin.tildeVWitness_of_blockWitness c R α hα hker β hβ hβk hR

theorem isA6Z3Module_img (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂)
    (hJ₁J₂ : J₁ ≤ J₂) (hJ₁X : J₁ ≤ X) (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆)
    (hA : IsA6Z3Type J₁) : IsA6Z3Module (lin.img J₁) := by
  have c : Ctx J₁ J₂ X := ⟨h1, h2, hJ₁J₂, hJ₁X, hU⟩
  have hirr : HasIrrTildeV (lin.img J₁) := lin.hasIrrTildeV_img h2 h1 hJ₁X hJ₁J₂ hU
  obtain ⟨⟨α, hα, hP, -⟩, hr⟩ := hA
  have hker := lin.ker_le_of_center_bot c hirr α hα hP
    (alternatingGroup.center_eq_bot (by simp))
  exact ⟨lin.exists_surjective_of_ker_le c α hα hker, lin.finrank_tildeV_img c hr⟩

theorem isFPrimeModule_img (h1 : IsFooteBlock J₁ J₁) (h2 : IsFooteBlock J₂ J₂)
    (hJ₁J₂ : J₁ ≤ J₂) (hJ₁X : J₁ ≤ X) (hU : blockU J₁ = ⁅blockQ J₂, J₁⁆)
    (hF : IsFPrimeType J₁) : IsFPrimeModule (lin.img J₁) := by
  rcases hF with ⟨n, hn, hA⟩ | hA | hA | hA | hA | hA
  · exact Or.inl ⟨n, hn, lin.isAltNaturalModule_img h1 h2 hJ₁J₂ hJ₁X hU hn hA⟩
  · exact Or.inr (Or.inl (lin.isA7FourModule_img h1 h2 hJ₁J₂ hJ₁X hU hA))
  · exact Or.inr (Or.inr (Or.inl (lin.isOmegaPlusModule_img h1 h2 hJ₁J₂ hJ₁X hU hA)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (lin.isOmegaMinusModule_img h1 h2 hJ₁J₂ hJ₁X hU hA))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (lin.isOmegaMinusModule_img h1 h2 hJ₁J₂ hJ₁X hU hA)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (lin.isA6Z3Module_img h1 h2 hJ₁J₂ hJ₁X hU hA)))))

end TildeULin

end CFSG.CGT.Foote82
