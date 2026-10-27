module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndUnitaryTools
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint
open scoped Pointwise MatrixGroups

section Generic

variable {G : Type} [Group G]

structure IsCentralPair (R M : Subgroup G) (t : G) : Prop where
  normal : R ≤ normalizer (M : Set G)
  normal' : R ≤ normalizer (conjR M t : Set G)
  sup_eq : M ⊔ conjR M t = R
  comm : ⁅M, conjR M t⁆ = ⊥
  odd : Odd (Nat.card (M ⊓ conjR M t : Subgroup G))

theorem conjR_conjR_of_sq {X : Subgroup G} {t : G} (ht : t * t = 1) :
    conjR (conjR X t) t = X := by
  rw [← conjR_mul, ht, conjR_one]

theorem IsCentralPair.swap {R M : Subgroup G} {t : G} (ht : t * t = 1)
    (hp : IsCentralPair R M t) : IsCentralPair R (conjR M t) t where
  normal := hp.normal'
  normal' := by rw [conjR_conjR_of_sq ht]; exact hp.normal
  sup_eq := by rw [conjR_conjR_of_sq ht, sup_comm]; exact hp.sup_eq
  comm := by rw [conjR_conjR_of_sq ht, commutator_comm]; exact hp.comm
  odd := by rw [conjR_conjR_of_sq ht, inf_comm]; exact hp.odd

theorem IsCentralPair.le {R M : Subgroup G} {t : G} (hp : IsCentralPair R M t) : M ≤ R :=
  hp.sup_eq ▸ le_sup_left

theorem IsCentralPair.le' {R M : Subgroup G} {t : G} (hp : IsCentralPair R M t) :
    conjR M t ≤ R :=
  hp.sup_eq ▸ le_sup_right

theorem conj_mem_conjR_of_sq {M : Subgroup G} {t : G} (ht : t * t = 1) {m : G} (hm : m ∈ M) :
    t * m * t⁻¹ ∈ conjR M t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [mem_conjR, hti]
  have : t * (t * m * t) * t = m := by
    rw [show t * (t * m * t) * t = (t * t) * m * (t * t) by group, ht, one_mul, mul_one]
  rw [this]
  exact hm

theorem conj_mem_of_mem_conjR {M : Subgroup G} {t m : G} (hm : m ∈ conjR M t) :
    t * m * t⁻¹ ∈ M :=
  mem_conjR.mp hm

@[expose] def rootPair (U M : Subgroup G) (w : G) : Subgroup G := (U ⊓ M) ⊔ conjR (U ⊓ M) w

theorem rootPair_le {U M : Subgroup G} {w : G} (hw : w ∈ normalizer (M : Set G)) :
    rootPair U M w ≤ M :=
  sup_le inf_le_right ((conjR_mono (inf_le_right : U ⊓ M ≤ M) w).trans (conjR_eq_self hw).le)

theorem rootPair_le_sup {U M : Subgroup G} {w : G} : rootPair U M w ≤ U ⊔ conjR U w :=
  sup_le (inf_le_left.trans le_sup_left) ((conjR_mono inf_le_left w).trans le_sup_right)

theorem conjR_rootPair_self {U M : Subgroup G} {w : G} (hw : w * w = 1) :
    conjR (rootPair U M w) w = rootPair U M w := by
  rw [rootPair, conjR_sup, ← conjR_mul, hw, conjR_one, sup_comm]

theorem conjR_rootPair {U M : Subgroup G} {t w : G} (htU : t ∈ normalizer (U : Set G))
    (htw : t * w = w * t) : conjR (rootPair U M w) t = rootPair U (conjR M t) w := by
  have h1 : conjR (U ⊓ M) t = U ⊓ conjR M t := by rw [conjR_inf, conjR_eq_self htU]
  rw [rootPair, rootPair, conjR_sup, ← conjR_mul, ← htw, conjR_mul, h1]

theorem sup_conjR_eq_rootPair {U M : Subgroup G} {t w : G} (htU : t ∈ normalizer (U : Set G))
    (htw : t * w = w * t) (hU : U = (U ⊓ M) ⊔ (U ⊓ conjR M t)) :
    U ⊔ conjR U w = rootPair U M w ⊔ conjR (rootPair U M w) t := by
  rw [conjR_rootPair htU htw, rootPair, rootPair, sup_sup_sup_comm, ← conjR_sup, ← hU]

theorem conj_mul_conj_eq {t w : G} (htw : t * w = w * t) (x : G) :
    w⁻¹ * x * w * (t * (w⁻¹ * x * w) * t⁻¹) = w⁻¹ * (x * (t * x * t⁻¹)) * w := by
  have h1 : w * t = t * w := htw.symm
  have h2 : w * t⁻¹ = t⁻¹ * w := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← htw, ← mul_assoc, inv_mul_cancel, one_mul]
  calc w⁻¹ * x * w * (t * (w⁻¹ * x * w) * t⁻¹)
      = w⁻¹ * x * (w * t) * w⁻¹ * x * (w * t⁻¹) := by group
    _ = w⁻¹ * x * (t * w) * w⁻¹ * x * (t⁻¹ * w) := by rw [h1, h2]
    _ = w⁻¹ * (x * (t * x * t⁻¹)) * w := by group

theorem isSimpleGroup_of_lieModel_PSU_four {Q : Type} [Group Q] (hQ : LieModel Q .PSU 4 2 1) :
    IsSimpleGroup Q :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hQ

theorem le_rootPair_sup {U M M' : Subgroup G} {w : G} (hU : U = (U ⊓ M) ⊔ (U ⊓ M')) :
    U ≤ rootPair U M w ⊔ M' :=
  calc U = (U ⊓ M) ⊔ (U ⊓ M') := hU
    _ ≤ rootPair U M w ⊔ M' := sup_le_sup le_sup_left inf_le_right

theorem mem_sup_of_mem_gen {X Z M' : Subgroup G} {w : G} (hw : w ∈ X ⊔ conjR X w)
    (hX : X ≤ Z ⊔ M') (hZ : conjR Z w = Z) (hM' : conjR M' w = M') : w ∈ Z ⊔ M' := by
  have : conjR X w ≤ Z ⊔ M' := by
    have := conjR_mono hX w
    rwa [conjR_sup, hZ, hM'] at this
  exact sup_le hX this hw

theorem conjR_bot (g : G) : conjR (⊥ : Subgroup G) g = ⊥ := map_bot _

end Generic

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {d : YamadaData G}

namespace YamadaSection4

variable (h : YamadaSection4 F d)
include h

theorem t_P₁ : d.t ∈ normalizer (d.P₁ : Set G) :=
  YamadaEnd.mem_normalizer_inf h.t_P (mem_normalizer_conjR h.t_P (t_comm_of_mem_H h.u₁_H))

theorem t_Uc : d.t ∈ normalizer (d.Uc : Set G) :=
  YamadaEnd.mem_normalizer_inf h.t_P₁ (mem_normalizer_conjR h.t_P₁
    (t_comm_of_mem_H (mul_mem (mul_mem h.w₂_H h.w₃_H) h.w₂_H)))

theorem t_Yc : d.t ∈ normalizer (d.Yc : Set G) :=
  mem_normalizer_sup h.t_Uc (mem_normalizer_conjR h.t_Uc (t_comm_of_mem_H h.w₃_H))

theorem Ua_decomp {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) :
    d.Ua = (d.Ua ⊓ M) ⊔ (d.Ua ⊓ conjR M d.t) :=
  h.P₂_decomp hp.normal hp.normal' hp.sup_eq hp.comm hp.odd
    (mul_mem (h.K₂_le_L₂ h.w₁_K₂) (h.K₂_le_L₂ h.w₂_K₂))

theorem Ub_decomp₂ {M : Subgroup G} (hp : IsCentralPair d.L₂ M d.t) :
    d.Ub = (d.Ub ⊓ M) ⊔ (d.Ub ⊓ conjR M d.t) :=
  h.P₂_decomp hp.normal hp.normal' hp.sup_eq hp.comm hp.odd
    (mul_mem (h.K₂_le_L₂ h.w₂_K₂) (h.K₂_le_L₂ h.w₁_K₂))

theorem P₁_decomp {M : Subgroup G} (hp : IsCentralPair d.L₁ M d.t) {g : G} (hg : g ∈ d.L₁) :
    d.P₁ ⊓ conjR d.P₁ g =
      ((d.P₁ ⊓ conjR d.P₁ g) ⊓ M) ⊔ ((d.P₁ ⊓ conjR d.P₁ g) ⊓ conjR M d.t) :=
  inf_conjR_decomp hp.comm hp.odd (hp.sup_eq.symm ▸ h.P₁_facts.2.2) (hp.sup_eq.symm ▸ hp.normal)
    (hp.sup_eq.symm ▸ hp.normal') (hp.normal hg) (hp.normal' hg)

theorem Ub_decomp₁ {M : Subgroup G} (hp : IsCentralPair d.L₁ M d.t) :
    d.Ub = (d.Ub ⊓ M) ⊔ (d.Ub ⊓ conjR M d.t) := by
  have := h.P₁_decomp hp h.w₃w₂w₃_L₁
  rwa [h.P₁_cbc] at this

theorem Uc_decomp {M : Subgroup G} (hp : IsCentralPair d.L₁ M d.t) :
    d.Uc = (d.Uc ⊓ M) ⊔ (d.Uc ⊓ conjR M d.t) :=
  h.P₁_decomp hp h.w₂w₃w₂_L₁

theorem L₁_components (hU : ∃ M : Subgroup G, d.D₁ ≤ M ∧ M ≤ d.N₁ ∧ d.N₁ = M ⊔ conjR M d.t ∧
      ⁅M, conjR M d.t⁆ ≤ d.D₁ ∧ M ⊓ conjR M d.t = d.D₁ ∧
      ∃ _ : (d.D₁.subgroupOf M).Normal, LieModel (M ⧸ d.D₁.subgroupOf M) .PSU 4 2 1) :
    ∃ M : Subgroup G, IsCentralPair d.L₁ M d.t ∧ M ⊓ conjR M d.t = ⊥ ∧ IsSimpleGroup M := by
  obtain ⟨Mt, hDM, hMN, hN, hcomm, hinf, hnorm, hlie⟩ := hU
  obtain ⟨hn₁, hconj, hn₂, hsup, hc, hXD, hXinf⟩ := components_of (L := d.L₁) h.t_sq hDM hMN hN
    hcomm inf_le_left h.N₁_eq h.L₁_facts.2 h.N₁_norm h.t_L₁ h.t_D₁
  have hbot : (d.L₁ ⊓ Mt) ⊓ (d.L₁ ⊓ conjR Mt d.t) = ⊥ := by
    have h1 : (d.L₁ ⊓ Mt) ⊓ (d.L₁ ⊓ conjR Mt d.t) ≤ d.D₁ :=
      le_sup_left.trans (hXD.trans hinf.le)
    have h2 := le_inf (le_refl ((d.L₁ ⊓ Mt) ⊓ (d.L₁ ⊓ conjR Mt d.t))) h1
    rwa [hXinf, le_bot_iff] at h2
  refine ⟨d.L₁ ⊓ Mt, ⟨hn₁, hconj ▸ hn₂, hconj ▸ hsup, hconj ▸ hc, ?_⟩, hconj ▸ hbot, ?_⟩
  · rw [hconj, hbot, card_bot]
    exact odd_one
  · obtain ⟨e⟩ := nonempty_quotientEquiv hDM (hMN.trans h.N₁_eq.le) h.L₁_facts.2
      (inf_le_left.trans h.N₁_norm)
    have := isSimpleGroup_of_lieModel_PSU_four hlie
    exact e.isSimpleGroup

theorem rootPair_Ub_quasisimple {M : Subgroup G} (hp : IsCentralPair d.L₁ M d.t)
    (hbot : M ⊓ conjR M d.t = ⊥) : CFSG.Open.IsQuasisimple (rootPair d.Ub M d.w₂) := by
  have hMC : M ≤ centralizer (conjR M d.t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hp.comm
  have hcomm : ∀ u ∈ M, ∀ v ∈ M, v * (d.t * u * d.t⁻¹) = d.t * u * d.t⁻¹ * v :=
    fun u hu v hv => (mem_centralizer_iff.mp (hMC hv) _ (conj_mem_conjR_of_sq h.t_sq hu)).symm
  have hw₂M : d.w₂ ∈ normalizer (M : Set G) := hp.normal (h.K₁_le_L₁ h.w₂_K₁)
  have hZM : rootPair d.Ub M d.w₂ ≤ M := rootPair_le hw₂M
  have htw : d.t * d.w₂ = d.w₂ * d.t := t_comm_of_mem_H h.w₂_H
  have hX₂ : ∀ v ∈ d.Ub ⊓ M, v * (d.t * v * d.t⁻¹) ∈ d.X₂ := fun v hv => by
    rw [← h.Ub_inf_H]
    exact ⟨mul_mem hv.1 ((mem_normalizer_iff.mp h.t_Ub v).mp hv.1),
      diagHom_mem_centralizer hcomm h.t_sq ⟨v, hv.2⟩⟩
  let ψ : rootPair d.Ub M d.w₂ →* G := (diagHom M d.t hcomm).comp (inclusion hZM)
  have hψ : ∀ z, ψ z = (z : G) * (d.t * z * d.t⁻¹) := fun z => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hψ] at hz
    have h1 : d.t * z * d.t⁻¹ = (z : G)⁻¹ := eq_inv_of_mul_eq_one_right hz
    have h2 : (z : G)⁻¹ ∈ M ⊓ conjR M d.t :=
      ⟨M.inv_mem (hZM z.2), h1 ▸ conj_mem_conjR_of_sq h.t_sq (hZM z.2)⟩
    rw [hbot, mem_bot, inv_eq_one] at h2
    exact Subtype.ext h2
  refine isQuasisimple_of_injective ψ hinj (le_antisymm ?_ ?_) h.X₂_quasisimple
  ·
    have key : rootPair d.Ub M d.w₂ ≤
        ((d.X₂ ⊔ conjR d.X₂ d.w₂).comap (diagHom M d.t hcomm)).map M.subtype := by
      refine sup_le (fun v hv => ⟨⟨v, hv.2⟩, mem_sup_left (hX₂ v hv), rfl⟩) ?_
      intro x hx
      have hy : d.w₂ * x * d.w₂⁻¹ ∈ d.Ub ⊓ M := mem_conjR.mp hx
      have hxM : x ∈ M := hZM (mem_sup_right hx)
      have hxy : x = d.w₂⁻¹ * (d.w₂ * x * d.w₂⁻¹) * d.w₂ := by group
      refine ⟨⟨x, hxM⟩, ?_, rfl⟩
      change (diagHom M d.t hcomm) ⟨x, hxM⟩ ∈ d.X₂ ⊔ conjR d.X₂ d.w₂
      rw [diagHom_apply]
      refine mem_sup_right (mem_conjR.mpr ?_)
      change d.w₂ * (x * (d.t * x * d.t⁻¹)) * d.w₂⁻¹ ∈ d.X₂
      rw [hxy, conj_mul_conj_eq htw]
      convert hX₂ _ hy using 1
      group
    rintro _ ⟨z, rfl⟩
    obtain ⟨m, hm, hmz⟩ := key z.2
    rw [hψ, ← hmz]
    exact hm
  ·
    have hX₂le : d.X₂ ≤ ψ.range := by
      intro x hx
      rw [← h.Ub_inf_H] at hx
      obtain ⟨hxU, hxH⟩ := hx
      have hmul : x ∈ ((d.Ub ⊓ M : Subgroup G) : Set G) *
          ((d.Ub ⊓ conjR M d.t : Subgroup G) : Set G) := by
        rw [← coe_sup_eq_mul hp.comm inf_le_right inf_le_right, ← h.Ub_decomp₁ hp]
        exact hxU
      obtain ⟨y, hy, z, hz, rfl⟩ := hmul
      have hc1 : y * z * d.t = d.t * (y * z) := mem_centralizer_singleton_iff.mp hxH
      have hfix : d.t * (y * z) * d.t⁻¹ = y * z := by rw [← hc1, mul_inv_cancel_right]
      have hty : d.t * y * d.t⁻¹ ∈ conjR M d.t := conj_mem_conjR_of_sq h.t_sq hy.2
      have htz : d.t * z * d.t⁻¹ ∈ M := conj_mem_of_mem_conjR hz.2
      have hcomm' : d.t * z * d.t⁻¹ * (d.t * y * d.t⁻¹) =
          d.t * y * d.t⁻¹ * (d.t * z * d.t⁻¹) :=
        (mem_centralizer_iff.mp (hMC htz) _ hty).symm
      have heq : d.t * z * d.t⁻¹ * (d.t * y * d.t⁻¹) = y * z := by
        rw [hcomm', ← hfix]
        group
      have hmem : y⁻¹ * (d.t * z * d.t⁻¹) ∈ M ⊓ conjR M d.t := by
        refine ⟨M.mul_mem (M.inv_mem hy.2) htz, ?_⟩
        have : y⁻¹ * (d.t * z * d.t⁻¹) = z * (d.t * y * d.t⁻¹)⁻¹ := by
          calc y⁻¹ * (d.t * z * d.t⁻¹)
              = y⁻¹ * (d.t * z * d.t⁻¹ * (d.t * y * d.t⁻¹)) * (d.t * y * d.t⁻¹)⁻¹ := by group
            _ = y⁻¹ * (y * z) * (d.t * y * d.t⁻¹)⁻¹ := by rw [heq]
            _ = z * (d.t * y * d.t⁻¹)⁻¹ := by group
        rw [this]
        exact (conjR M d.t).mul_mem hz.2 ((conjR M d.t).inv_mem hty)
      rw [hbot, mem_bot] at hmem
      have h3 : y = d.t * z * d.t⁻¹ := inv_mul_eq_one.mp hmem
      have hzy : z = d.t * y * d.t⁻¹ := by
        rw [h3, h.t_inv]
        calc z = (d.t * d.t) * z * (d.t * d.t) := by rw [h.t_sq, one_mul, mul_one]
          _ = d.t * (d.t * z * d.t) * d.t := by group
      refine ⟨⟨y, mem_sup_left hy⟩, ?_⟩
      rw [hψ, hzy]
    have hX₂w : conjR d.X₂ d.w₂ ≤ ψ.range := by
      intro x hx
      obtain ⟨z, hz⟩ := hX₂le (mem_conjR.mp hx)
      have hzw : d.w₂⁻¹ * z * d.w₂ ∈ rootPair d.Ub M d.w₂ := by
        have := conj_mem_conjR (g := d.w₂) z.2
        rwa [conjR_rootPair_self h.w₂_sq] at this
      refine ⟨⟨_, hzw⟩, ?_⟩
      rw [hψ]
      change d.w₂⁻¹ * z * d.w₂ * (d.t * (d.w₂⁻¹ * z * d.w₂) * d.t⁻¹) = x
      rw [conj_mul_conj_eq htw]
      rw [hψ] at hz
      rw [hz]
      group
    exact sup_le hX₂le hX₂w

theorem exists_M₂ {M₁ : Subgroup G} (hp₁ : IsCentralPair d.L₁ M₁ d.t)
    (hbot : M₁ ⊓ conjR M₁ d.t = ⊥) :
    ∃ M : Subgroup G, IsCentralPair d.L₂ M d.t ∧ ⁅M, M⁆ = M ∧
      rootPair d.Ub M₁ d.w₂ ≤ rootPair d.Ub M d.w₂ := by
  obtain ⟨M, hn, hn', hsup, hc, hodd, θ, hθ, -⟩ := h.L₂_components
  have hp : IsCentralPair d.L₂ M d.t := ⟨hn, hn', hsup, hc, hodd⟩
  have hperf : ⁅M, M⁆ = M := by
    have : Group.IsPerfect SL(3, F) := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le
      (by norm_num)
    have : Group.IsPerfect M := Group.IsPerfect.ofSurjective hθ
    exact YamadaEnd.commutator_eq_self_of_isPerfect this
  have htw : d.t * d.w₂ = d.w₂ * d.t := t_comm_of_mem_H h.w₂_H
  have hYb : d.Yb = rootPair d.Ub M d.w₂ ⊔ conjR (rootPair d.Ub M d.w₂) d.t :=
    sup_conjR_eq_rootPair h.t_Ub htw (h.Ub_decomp₂ hp)
  have hYb' : d.Yb = rootPair d.Ub M₁ d.w₂ ⊔ conjR (rootPair d.Ub M₁ d.w₂) d.t :=
    sup_conjR_eq_rootPair h.t_Ub htw (h.Ub_decomp₁ hp₁)
  have hZM : rootPair d.Ub M d.w₂ ≤ M := rootPair_le (hn (h.K₂_le_L₂ h.w₂_K₂))
  have hZc : ⁅rootPair d.Ub M d.w₂, conjR (rootPair d.Ub M d.w₂) d.t⁆ = ⊥ :=
    le_bot_iff.mp (hc ▸ commutator_mono hZM (conjR_mono hZM d.t))
  have hZ'M : rootPair d.Ub M₁ d.w₂ ≤ M₁ := rootPair_le (hp₁.normal (h.K₁_le_L₁ h.w₂_K₁))
  have hM₁C : conjR M₁ d.t ≤ centralizer (M₁ : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp (by rw [commutator_comm]; exact hp₁.comm)
  have hZ'N : d.Yb ≤ normalizer (rootPair d.Ub M₁ d.w₂ : Set G) := by
    rw [hYb']
    exact sup_le le_normalizer (((conjR_mono hZ'M d.t).trans (hM₁C.trans
      (centralizer_le hZ'M))).trans (centralizer_le_normalizer _))
  rcases le_or_le_of_quasisimple (h.rootPair_Ub_quasisimple hp₁ hbot) hZc
      (hYb ▸ hYb' ▸ le_sup_left) (hYb ▸ hZ'N) with hle | hle
  · exact ⟨M, hp, hperf, hle⟩
  · refine ⟨conjR M d.t, hp.swap h.t_sq, by rw [← conjR_commutator, hperf], ?_⟩
    rwa [← conjR_rootPair h.t_Ub htw]

theorem M₂_le {M₁ M : Subgroup G} (hp₁ : IsCentralPair d.L₁ M₁ d.t)
    (hp : IsCentralPair d.L₂ M d.t) (hperf : ⁅M, M⁆ = M)
    (hZ : rootPair d.Ub M₁ d.w₂ ≤ rootPair d.Ub M d.w₂) :
    M ≤ rootPair d.Ua M d.w₁ ⊔ rootPair d.Ub M₁ d.w₂ := by
  have hw₁ := h.K₂_le_L₂ h.w₁_K₂
  have hw₂ := h.K₂_le_L₂ h.w₂_K₂
  have htw : d.t * d.w₂ = d.w₂ * d.t := t_comm_of_mem_H h.w₂_H
  have hMC : M ≤ centralizer (conjR M d.t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hp.comm
  have hcomm : ∀ u ∈ M, ∀ v ∈ M, v * (d.t * u * d.t⁻¹) = d.t * u * d.t⁻¹ * v :=
    fun u hu v hv => (mem_centralizer_iff.mp (hMC hv) _ (conj_mem_conjR_of_sq h.t_sq hu)).symm
  have hZaM : rootPair d.Ua M d.w₁ ≤ M := rootPair_le (hp.normal hw₁)
  have hZ'M : rootPair d.Ub M₁ d.w₂ ≤ M := hZ.trans (rootPair_le (hp.normal hw₂))
  have hZ't : conjR (rootPair d.Ub M₁ d.w₂) d.t ≤ conjR M d.t := conjR_mono hZ'M d.t
  have hX₁ : d.X₁ ≤ rootPair d.Ua M d.w₁ ⊔ conjR M d.t :=
    (h.Ua_inf_H ▸ inf_le_left).trans (le_rootPair_sup (h.Ua_decomp hp))
  have hX₂ : d.X₂ ≤ rootPair d.Ub M₁ d.w₂ ⊔ conjR M d.t := by
    have hUb : d.Ub ≤ rootPair d.Ub M₁ d.w₂ ⊔ conjR (rootPair d.Ub M₁ d.w₂) d.t :=
      le_sup_left.trans (sup_conjR_eq_rootPair h.t_Ub htw (h.Ub_decomp₁ hp₁)).le
    exact (h.Ub_inf_H ▸ inf_le_left).trans (hUb.trans (sup_le_sup_left hZ't _))
  have hK : d.K₂ ≤ (rootPair d.Ua M d.w₁ ⊔ rootPair d.Ub M₁ d.w₂) ⊔ conjR M d.t := by
    rw [h.K₂_gen]
    have h1 : rootPair d.Ua M d.w₁ ⊔ conjR M d.t ≤
        (rootPair d.Ua M d.w₁ ⊔ rootPair d.Ub M₁ d.w₂) ⊔ conjR M d.t :=
      sup_le_sup_right le_sup_left _
    have h2 : rootPair d.Ub M₁ d.w₂ ⊔ conjR M d.t ≤
        (rootPair d.Ua M d.w₁ ⊔ rootPair d.Ub M₁ d.w₂) ⊔ conjR M d.t :=
      sup_le_sup_right le_sup_right _
    refine sup_le (sup_le (sup_le (hX₁.trans h1) (hX₂.trans h2)) ?_) ?_
    · rw [zpowers_le]
      exact h1 (mem_sup_of_mem_gen h.w₁_gen hX₁ (conjR_rootPair_self h.w₁_sq)
        (conjR_eq_self (hp.normal' hw₁)))
    · rw [zpowers_le]
      exact h2 (mem_sup_of_mem_gen h.w₂_gen hX₂ (conjR_rootPair_self h.w₂_sq)
        (conjR_eq_self (hp.normal' hw₂)))
  refine le_of_mul_conj_mem_of_perfect hp.comm (sup_le hZaM hZ'M) hperf
    (fun m hm => conj_mem_conjR_of_sq h.t_sq hm) fun m hm => hK ?_
  rw [← h.L₂_facts.1]
  exact ⟨mul_mem (hp.le hm) (hp.le' (conj_mem_conjR_of_sq h.t_sq hm)),
    diagHom_mem_centralizer hcomm h.t_sq ⟨m, hm⟩⟩

theorem M₁_le {M₁ : Subgroup G} (hp₁ : IsCentralPair d.L₁ M₁ d.t)
    (hbot : M₁ ⊓ conjR M₁ d.t = ⊥) :
    M₁ ≤ rootPair d.Ub M₁ d.w₂ ⊔ rootPair d.Uc M₁ d.w₃ := by
  have hw₂ := h.K₁_le_L₁ h.w₂_K₁
  have hw₃ := h.K₁_le_L₁ h.w₃_K₁
  have hMC : M₁ ≤ centralizer (conjR M₁ d.t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hp₁.comm
  have hcomm : ∀ u ∈ M₁, ∀ v ∈ M₁, v * (d.t * u * d.t⁻¹) = d.t * u * d.t⁻¹ * v :=
    fun u hu v hv => (mem_centralizer_iff.mp (hMC hv) _ (conj_mem_conjR_of_sq h.t_sq hu)).symm
  have hX₂ : d.X₂ ≤ rootPair d.Ub M₁ d.w₂ ⊔ conjR M₁ d.t :=
    (h.Ub_inf_H ▸ inf_le_left).trans (le_rootPair_sup (h.Ub_decomp₁ hp₁))
  have hX₃ : d.X₃ ≤ rootPair d.Uc M₁ d.w₃ ⊔ conjR M₁ d.t :=
    (h.Uc_inf_H ▸ inf_le_left).trans (le_rootPair_sup (h.Uc_decomp hp₁))
  have hK : d.K₁ ≤ (rootPair d.Ub M₁ d.w₂ ⊔ rootPair d.Uc M₁ d.w₃) ⊔ conjR M₁ d.t := by
    rw [h.K₁_gen]
    have h1 : rootPair d.Ub M₁ d.w₂ ⊔ conjR M₁ d.t ≤
        (rootPair d.Ub M₁ d.w₂ ⊔ rootPair d.Uc M₁ d.w₃) ⊔ conjR M₁ d.t :=
      sup_le_sup_right le_sup_left _
    have h2 : rootPair d.Uc M₁ d.w₃ ⊔ conjR M₁ d.t ≤
        (rootPair d.Ub M₁ d.w₂ ⊔ rootPair d.Uc M₁ d.w₃) ⊔ conjR M₁ d.t :=
      sup_le_sup_right le_sup_right _
    refine sup_le (sup_le (sup_le (hX₂.trans h1) (hX₃.trans h2)) ?_) ?_
    · rw [zpowers_le]
      exact h1 (mem_sup_of_mem_gen h.w₂_gen hX₂ (conjR_rootPair_self h.w₂_sq)
        (conjR_eq_self (hp₁.normal' hw₂)))
    · rw [zpowers_le]
      exact h2 (mem_sup_of_mem_gen h.w₃_gen hX₃ (conjR_rootPair_self h.w₃_sq)
        (conjR_eq_self (hp₁.normal' hw₃)))
  refine le_of_mul_conj_mem_of_inf_eq_bot hp₁.comm
    (sup_le (rootPair_le (hp₁.normal hw₂)) (rootPair_le (hp₁.normal hw₃))) hbot
    (fun m hm => conj_mem_conjR_of_sq h.t_sq hm) fun m hm => hK ?_
  rw [← h.L₁_facts.1]
  exact ⟨mul_mem (hp₁.le hm) (hp₁.le' (conj_mem_conjR_of_sq h.t_sq hm)),
    diagHom_mem_centralizer hcomm h.t_sq ⟨m, hm⟩⟩

theorem commutator_M₂_M₁ {M₁ M : Subgroup G} (hp₁ : IsCentralPair d.L₁ M₁ d.t)
    (hp : IsCentralPair d.L₂ M d.t) (hZ : rootPair d.Ub M₁ d.w₂ ≤ rootPair d.Ub M d.w₂)
    (hM : M ≤ rootPair d.Ua M d.w₁ ⊔ rootPair d.Ub M₁ d.w₂)
    (hM₁ : M₁ ≤ rootPair d.Ub M₁ d.w₂ ⊔ rootPair d.Uc M₁ d.w₃) :
    ⁅M, conjR M₁ d.t⁆ = ⊥ := by
  have hZaM : rootPair d.Ua M d.w₁ ≤ M := rootPair_le (hp.normal (h.K₂_le_L₂ h.w₁_K₂))
  have hZ'M₁ : rootPair d.Ub M₁ d.w₂ ≤ M₁ := rootPair_le (hp₁.normal (h.K₁_le_L₁ h.w₂_K₁))
  have hZcM₁ : rootPair d.Uc M₁ d.w₃ ≤ M₁ := rootPair_le (hp₁.normal (h.K₁_le_L₁ h.w₃_K₁))
  have hZ'M : conjR (rootPair d.Ub M₁ d.w₂) d.t ≤ conjR M d.t :=
    conjR_mono (hZ.trans (rootPair_le (hp.normal (h.K₂_le_L₂ h.w₂_K₂)))) d.t
  have hMC : M ≤ centralizer (conjR M d.t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hp.comm
  have hM₁C : M₁ ≤ centralizer (conjR M₁ d.t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hp₁.comm
  have hYC : d.Ya ≤ centralizer (d.Yc : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp h.commutator_Ya_Yc
  have hZct : conjR (rootPair d.Uc M₁ d.w₃) d.t ≤ d.Yc :=
    (conjR_mono (rootPair_le_sup : rootPair d.Uc M₁ d.w₃ ≤ d.Yc) d.t).trans
      (conjR_eq_self h.t_Yc).le
  have hM₁t : conjR M₁ d.t ≤
      conjR (rootPair d.Ub M₁ d.w₂) d.t ⊔ conjR (rootPair d.Uc M₁ d.w₃) d.t := by
    rw [← conjR_sup]
    exact conjR_mono hM₁ d.t
  have hZa : rootPair d.Ua M d.w₁ ≤ centralizer ((conjR (rootPair d.Ub M₁ d.w₂) d.t ⊔
      conjR (rootPair d.Uc M₁ d.w₃) d.t : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le (hZ'M.trans ((le_centralizer_iff.mp hMC).trans (centralizer_le hZaM))) ?_
    exact hZct.trans ((le_centralizer_iff.mp hYC).trans
      (centralizer_le (rootPair_le_sup : rootPair d.Ua M d.w₁ ≤ d.Ya)))
  have hZ' : rootPair d.Ub M₁ d.w₂ ≤ centralizer ((conjR (rootPair d.Ub M₁ d.w₂) d.t ⊔
      conjR (rootPair d.Uc M₁ d.w₃) d.t : Subgroup G) : Set G) :=
    hZ'M₁.trans (hM₁C.trans (centralizer_le
      (sup_le (conjR_mono hZ'M₁ d.t) (conjR_mono hZcM₁ d.t))))
  rw [commutator_eq_bot_iff_le_centralizer]
  exact hM.trans ((sup_le hZa hZ').trans (centralizer_le hM₁t))

theorem G₀_eq_L₁_sup_L₂ : d.G₀ = d.L₁ ⊔ d.L₂ := by
  have hYc : d.Yc ≤ d.L₁ := by
    have hUc : d.Uc ≤ d.L₁ := inf_le_left.trans h.P₁_facts.2.2.le
    have hc : conjR d.L₁ d.w₃ = d.L₁ := conjR_eq_self (le_normalizer (h.K₁_le_L₁ h.w₃_K₁))
    exact sup_le hUc (hc ▸ conjR_mono hUc _)
  refine le_antisymm (sup_le (h.Ya_Yb_eq.le.trans le_sup_right) (hYc.trans le_sup_left)) ?_
  exact sup_le ((inf_le_left : d.L₁ ≤ d.N₁).trans (le_sup_left.trans h.G₀_eq.ge))
    (h.Ya_Yb_eq.ge.trans (le_sup_left : d.Ya ⊔ d.Yb ≤ d.G₀))

theorem unitaryCase_of
    {G₁ : Subgroup G} (hperf : ⁅G₁, G₁⁆ = G₁)
    (hc : ⁅G₁, conjR G₁ d.t⁆ = ⊥) (hG₀ : d.G₀ = G₁ ⊔ conjR G₁ d.t) :
    UnitaryCase d.G₀ d.t := by
  have hGC : G₁ ≤ centralizer (conjR G₁ d.t : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp hc
  have hGC' : conjR G₁ d.t ≤ centralizer (G₁ : Set G) := le_centralizer_iff.mp hGC
  have hcomm : ∀ u ∈ G₁, ∀ v ∈ G₁, v * (d.t * u * d.t⁻¹) = d.t * u * d.t⁻¹ * v :=
    fun u hu v hv => (mem_centralizer_iff.mp (hGC hv) _ (conj_mem_conjR_of_sq h.t_sq hu)).symm
  have htop : commutator G₁ = ⊤ := commutator_eq_top_of_commutator_eq hperf
  have : Group.IsPerfect G₁ := Group.isPerfect_def.2 htop
  have hΔH : (diagHom G₁ d.t hcomm).range ≤ d.H := by
    rintro _ ⟨x, rfl⟩
    exact diagHom_mem_centralizer hcomm h.t_sq x
  have hΔperf : ⁅(diagHom G₁ d.t hcomm).range, (diagHom G₁ d.t hcomm).range⁆ =
      (diagHom G₁ d.t hcomm).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, htop]
  have hΔL : (diagHom G₁ d.t hcomm).range ≤ d.L := le_of_perfect h.setting.standard
    h.center_eq h.lie h.order_t h.t_mem h.kernel hΔH hΔperf
  have hLΔ : d.L ≤ (diagHom G₁ d.t hcomm).range :=
    le_range_diagHom hc (fun a ha => conj_mem_conjR_of_sq h.t_sq ha)
      (fun a ha => conj_mem_of_mem_conjR ha) hcomm (hG₀ ▸ h.L_le_G₀) h.L_le_H
      (commutator_eq_self_of_quasisimple h.setting.standard.1)
  let q : G₁ →* d.L := (diagHom G₁ d.t hcomm).codRestrict d.L fun x => hΔL ⟨x, rfl⟩
  have hq : Function.Surjective q := by
    rintro ⟨l, hl⟩
    obtain ⟨x, hx⟩ := hLΔ hl
    exact ⟨x, Subtype.ext hx⟩
  have hkerG : ∀ x : G₁, x ∈ q.ker → (x : G) ∈ conjR G₁ d.t := by
    intro x hx
    rw [MonoidHom.ker_codRestrict, MonoidHom.mem_ker, diagHom_apply] at hx
    have h1 : d.t * x * d.t⁻¹ = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right hx
    have := conj_mem_conjR_of_sq h.t_sq x.2
    rw [h1] at this
    simpa using (conjR G₁ d.t).inv_mem this
  have hker : q.ker ≤ center G₁ := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hGC' (hkerG x hx)) y y.2)
  have hcen : center G₁ ≤ q.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : q z ∈ center d.L := by
      rw [mem_center_iff]
      intro l
      obtain ⟨y, rfl⟩ := hq l
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
    rw [h.center_eq, mem_bot] at this
    exact this
  have hZeq : center G₁ = q.ker := le_antisymm hcen hker
  have hLie : LieModel d.L .PSU 6 2 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq h.center_eq).trans QuotientGroup.quotientBot) h.lie
  have hdvd : Nat.card q.ker ∣ 3 * 2 ^ 2 := card_ker_dvd_twelve hLie q hq hker
  have hodd : Odd (Nat.card q.ker) := by
    have hle : q.ker.map G₁.subtype ≤ centralizer (d.G₀ : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hG₀]
      exact mem_centralizer_sup (fun a ha => mem_centralizer_iff.mp (hGC' (hkerG x hx)) a ha)
        (fun b hb => mem_centralizer_iff.mp (hGC x.2) b hb)
    have h1 := card_dvd_of_le hle
    rw [card_map_of_injective G₁.subtype_injective] at h1
    exact Odd.of_dvd_nat h.odd_centralizer_G₀ h1
  have h3 : Nat.card (center G₁) ∣ 3 := by
    rw [hZeq]
    exact ((Nat.coprime_two_right.2 hodd).pow_right 2).dvd_of_dvd_mul_right hdvd
  have hZmap : center d.L = (center G₁).map q := by
    rw [h.center_eq, eq_comm, eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact mem_bot.mpr (MonoidHom.mem_ker.mp (hcen hz))
  let e := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective q hq hker hZmap
  have hlie₁ : LieModel (G₁ ⧸ center G₁) .PSU 6 2 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h.lie
  have hqs : CFSG.Open.IsQuasisimple G₁ := by
    have : IsSimpleGroup (d.L ⧸ center d.L) := h.setting.standard.1.2
    exact ⟨htop, e.isSimpleGroup⟩
  have hconjeq : conjR G₁ d.t = G₁.map (MulAut.conj d.t).toMonoidHom := by
    rw [conjR, h.t_inv]
  refine ⟨G₁, by rw [← hconjeq]; exact hG₀, by rw [← hconjeq]; exact hc, ?_, hqs, hlie₁, h3⟩
  intro heq
  rw [← hconjeq] at heq
  rw [heq, hperf] at hc
  have hL : d.L ≤ ⊥ := by
    have := h.L_le_G₀
    rwa [hG₀, heq, hc, sup_bot_eq] at this
  exact not_le_centralizer_self_of_quasisimple h.setting.standard.1 (hL.trans bot_le)

theorem unitaryCase
    (hU : ∃ M : Subgroup G, d.D₁ ≤ M ∧ M ≤ d.N₁ ∧ d.N₁ = M ⊔ conjR M d.t ∧
      ⁅M, conjR M d.t⁆ ≤ d.D₁ ∧ M ⊓ conjR M d.t = d.D₁ ∧
      ∃ _ : (d.D₁.subgroupOf M).Normal, LieModel (M ⧸ d.D₁.subgroupOf M) .PSU 4 2 1) :
    UnitaryCase d.G₀ d.t := by
  obtain ⟨M₁, hp₁, hbot, hsimple⟩ := h.L₁_components hU
  obtain ⟨M, hp, hperf, hZ⟩ := h.exists_M₂ hp₁ hbot
  have hM := h.M₂_le hp₁ hp hperf hZ
  have hM₁ := h.M₁_le hp₁ hbot
  have hc := h.commutator_M₂_M₁ hp₁ hp hZ hM hM₁
  have hM₁perf : ⁅M₁, M₁⁆ = M₁ := by
    have hq := h.rootPair_Ub_quasisimple hp₁ hbot
    have hZ'M₁ : rootPair d.Ub M₁ d.w₂ ≤ M₁ := rootPair_le (hp₁.normal (h.K₁_le_L₁ h.w₂_K₁))
    exact commutator_eq_self_of_isSimpleGroup fun hab =>
      not_le_centralizer_self_of_quasisimple hq (hZ'M₁.trans (hab.trans (centralizer_le hZ'M₁)))
  have hperf₁ : ⁅M₁ ⊔ M, M₁ ⊔ M⁆ = M₁ ⊔ M := by
    refine le_antisymm (commutator_le_self _) (sup_le ?_ ?_)
    · calc M₁ = ⁅M₁, M₁⁆ := hM₁perf.symm
        _ ≤ ⁅M₁ ⊔ M, M₁ ⊔ M⁆ := commutator_mono le_sup_left le_sup_left
    · calc M = ⁅M, M⁆ := hperf.symm
        _ ≤ ⁅M₁ ⊔ M, M₁ ⊔ M⁆ := commutator_mono le_sup_right le_sup_right
  have hc' : ⁅conjR M d.t, M₁⁆ = ⊥ := by
    have : conjR ⁅M, conjR M₁ d.t⁆ d.t = conjR ⊥ d.t := by rw [hc]
    rwa [conjR_commutator, conjR_conjR_of_sq h.t_sq, conjR_bot] at this
  have hcomm₁ : ⁅M₁ ⊔ M, conjR (M₁ ⊔ M) d.t⁆ = ⊥ := by
    rw [conjR_sup, commutator_eq_bot_iff_le_centralizer]
    refine sup_le ?_ ?_
    · rw [le_centralizer_iff]
      exact sup_le (le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hp₁.comm))
        ((commutator_eq_bot_iff_le_centralizer).mp hc')
    · rw [le_centralizer_iff]
      exact sup_le (le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hc))
        (le_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer).mp hp.comm))
  have hG₀ : d.G₀ = (M₁ ⊔ M) ⊔ conjR (M₁ ⊔ M) d.t := by
    rw [h.G₀_eq_L₁_sup_L₂, ← hp₁.sup_eq, ← hp.sup_eq, conjR_sup, sup_sup_sup_comm]
  exact h.unitaryCase_of hperf₁ hcomm₁ hG₀

end YamadaSection4

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
