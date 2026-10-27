module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Skeleton
public import CFSG.LieType.ChevTwo.OppCl.Defs
import CFSG.LieType.ChevTwo.OppCl.ToolkitAsmNorm
import CFSG.LieType.ChevTwo.OppCl.ToolkitAsmFix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.OppCl

section Template

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]

@[expose] def RigidProp (P : Equiv.Perm V → Prop) (ρ : H →* Module.End F V)
    (𝔉 : Subgroup H → ℕ → Submodule F V) (p : ℕ) : Prop :=
  ∀ Rh : Subgroup (Equiv.Perm V), Rh ≤ semilinGroup F V → (∀ r ∈ Rh, P r) → IsPGroup p Rh →
    (∀ r ∈ Rh, NormH ρ r) → ∀ Q : Subgroup H, IsPGroup 2 Q → flagKernel ρ (𝔉 Q) ≠ ⊥ →
      (∀ x ∈ flagKernel ρ (𝔉 Q), CommR ρ Rh x) → ∀ r ∈ Rh, ∃ c : F, ∀ v, r v = c • v

theorem lt_inf_normalizer_of_lt' {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Y W : Subgroup G} (hW : IsPGroup p ↥W) (hYW : Y < W) :
    Y < W ⊓ Subgroup.normalizer (Y : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent ↥W := hW.isNilpotent
  have hle : Y ≤ W := hYW.le
  have hlt : Y.subgroupOf W < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd hYW (not_lt_of_ge h)
  have h2 := Group.normalizerCondition_of_isNilpotent (G := ↥W) (Y.subgroupOf W) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hle] at h2
  obtain ⟨x, hx1, hx2⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp h2).2
  refine lt_of_le_of_ne (le_inf hle Subgroup.le_normalizer) ?_
  intro heq
  apply hx2
  have hxm : (x : G) ∈ W ⊓ Subgroup.normalizer (Y : Set G) := ⟨x.2, hx1⟩
  rw [← heq] at hxm
  exact hxm

theorem eq_of_inf_normalizer_le' {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Y W : Subgroup G} (hW : IsPGroup p ↥W) (hYW : Y ≤ W)
    (h : W ⊓ Subgroup.normalizer (Y : Set G) ≤ Y) : Y = W := by
  by_contra hne
  exact absurd h (not_le_of_gt (lt_inf_normalizer_of_lt' hp hW (lt_of_le_of_ne hYW hne)))

theorem mulAut_pow_apply_of_fixes {S : Type*} [Group S] (β : MulAut S) {R : Set S}
    (h : ∀ r ∈ R, β r = r) (k : ℕ) : ∀ r ∈ R, (β ^ k) r = r := by
  induction k with
  | zero => intro r _; simp
  | succ k ih => intro r hr; rw [pow_succ, MulAut.mul_apply, h r hr, ih r hr]

theorem mulAut_zpowers_apply_of_fixes {S : Type*} [Group S] (β : MulAut S) {R : Set S}
    (h : ∀ r ∈ R, β r = r) : ∀ γ ∈ Subgroup.zpowers β, ∀ r ∈ R, γ r = r := by
  have hinv : ∀ r ∈ R, β⁻¹ r = r := fun r hr => by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact (h r hr).symm
  rintro γ ⟨k, rfl⟩ r hr
  show (β ^ k) r = r
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, MulAut.mul_apply, h r hr]; exact ih
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply, hinv r hr]; exact ih

end Template

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H] [Finite H]

theorem radRigid_of_rigid (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZo : Nat.Coprime (Nat.card Z) 2) (P : Equiv.Perm V → Prop) (ρ : H →* Module.End F V)
    (hρ : Function.Injective ρ) (𝔉 : Subgroup H → ℕ → Submodule F V)
    (h0 : ∀ Q : Subgroup H, IsPGroup 2 Q → 𝔉 Q 0 = ⊥)
    (htop : ∀ Q : Subgroup H, IsPGroup 2 Q → ∃ m, 𝔉 Q m = ⊤)
    (hnorm : ∀ Q : Subgroup H, IsPGroup 2 Q → Subgroup.normalizer (Q : Set H) ≤ flagStab ρ (𝔉 Q))
    (hker : ∀ Q : Subgroup H, IsPGroup 2 Q → Q ≤ flagKernel ρ (𝔉 Q))
    (hlift : AutLift P (QuotientGroup.mk' Z) ρ)
    (hrigid : ∀ p : ℕ, p.Prime → p ≠ 2 → RigidProp P ρ 𝔉 p) : RadRigid 2 (H ⧸ Z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro R hR α hfix hord
  by_contra hα1
  have hord1 : orderOf α ≠ 1 := fun h => hα1 (orderOf_eq_one_iff.mp h)
  have hord0 : orderOf α ≠ 0 := by
    intro h
    rw [h] at hord
    simp at hord
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpd
    exact absurd ((Nat.Coprime.symm hord).eq_one_of_dvd hpd) (by norm_num)
  haveI : Fact p.Prime := ⟨hp⟩
  set β : MulAut (H ⧸ Z) := α ^ (orderOf α / p) with hβdef
  have hβord : orderOf β = p := orderOf_pow_orderOf_div hord0 hpd
  have hβfix : ∀ r ∈ (R : Set (H ⧸ Z)), β r = r :=
    mulAut_pow_apply_of_fixes α (fun r hr => hfix r hr) _
  have hβ1 : β ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hβord
    exact hp.one_lt.ne hβord
  have hRβp : IsPGroup p (Subgroup.zpowers β) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one, Nat.card_zpowers, hβord]
  have hRβfix := mulAut_zpowers_apply_of_fixes β hβfix
  obtain ⟨Rh, hRhs, hRhP, hRhp, hRhN, hRhA, hRhB⟩ := hlift p hp hp2 (Subgroup.zpowers β) hRβp
  obtain ⟨Qt, hQt2, hQtmap⟩ := exists_isPGroup_map_eq (r := 2) Z hR.2.1
  have hRQt : ∀ γ ∈ Subgroup.zpowers β, (Qt.map (QuotientGroup.mk' Z)).map γ.toMonoidHom =
      Qt.map (QuotientGroup.mk' Z) := by
    intro γ hγ
    rw [hQtmap]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hRβfix γ hγ x hx
      simp only [MulEquiv.coe_toMonoidHom]
      rw [this]
      exact hx
    · intro hy
      exact ⟨y, hy, hRβfix γ hγ y hy⟩
  have hNQ : ∀ r ∈ Rh, NormQ ρ r Qt := fun r hr => by
    obtain ⟨γ, hγR, hind⟩ := hRhB r hr
    exact CFSG.LieType.ChevTwo.OppCl.TK.normQ_of_induces Z hZc hZo hρ hQt2 hRQt hγR hind
  obtain ⟨m, hm⟩ := htop Qt hQt2
  have hKF2 : IsPGroup 2 (flagKernel ρ (𝔉 Qt)) := isPGroup_flagKernel ρ 2 hρ (h0 Qt hQt2) hm
  have hQtKF : Qt ≤ flagKernel ρ (𝔉 Qt) := hker Qt hQt2
  have hNnorm : Subgroup.normalizer (Qt : Set H) =
      (Subgroup.normalizer (R : Set (H ⧸ Z))).comap (QuotientGroup.mk' Z) := by
    rw [normalizer_eq_comap_normalizer_map Z hZc hZo hQt2, hQtmap]
  have hcore : pCoreOf 2 (Subgroup.normalizer (Qt : Set H)) ≤ Qt := by
    intro x hx
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (Subgroup.normalizer (Qt : Set H))) ⟨x, hx⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : QuotientGroup.mk' Z x ∈
        (pCoreOf 2 (Subgroup.normalizer (Qt : Set H))).map (QuotientGroup.mk' Z) := ⟨x, hx, rfl⟩
    have h2 := map_pCoreOf_le (QuotientGroup.mk' Z) _ h1
    have h3 : (Subgroup.normalizer (Qt : Set H)).map (QuotientGroup.mk' Z) =
        Subgroup.normalizer (R : Set (H ⧸ Z)) := by
      rw [hNnorm, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]
    rw [h3, hR.2.2.1, ← hQtmap] at h2
    exact mem_of_mk_mem_map Z hZc hZo hQt2 h2 hxn
  have hbase : flagKernel ρ (𝔉 Qt) ⊓ Subgroup.normalizer (Qt : Set H) ≤ Qt := by
    refine le_trans ?_ hcore
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hKF2.to_le inf_le_left)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hgs : g ∈ flagStab ρ (𝔉 Qt) := hnorm Qt hQt2 hg
    have hgK := flagStab_le_normalizer_flagKernel ρ (𝔉 Qt) hgs
    have key : ∀ g ∈ Subgroup.normalizer (Qt : Set H), ∀ n ∈ flagKernel ρ (𝔉 Qt) ⊓
        Subgroup.normalizer (Qt : Set H), g * n * g⁻¹ ∈ flagKernel ρ (𝔉 Qt) ⊓
          Subgroup.normalizer (Qt : Set H) := by
      intro g hg n hn
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (flagStab_le_normalizer_flagKernel ρ (𝔉 Qt)
          (hnorm Qt hQt2 hg)) n).mp hn1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hn2) (Subgroup.inv_mem _ hg)
    intro n
    refine ⟨fun hn => key g hg n hn, fun hn => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hn
    simpa [mul_assoc] using this
  have hKFeq : flagKernel ρ (𝔉 Qt) = Qt :=
    (eq_of_inf_normalizer_le' Nat.prime_two hKF2 hQtKF hbase).symm
  have hQt0 : Qt ≠ ⊥ := by
    rintro rfl
    apply hR.1
    rw [← hQtmap, Subgroup.map_bot]
  have hcomm : ∀ x ∈ flagKernel ρ (𝔉 Qt), CommR ρ Rh x := by
    intro x hx
    rw [hKFeq] at hx
    refine CFSG.LieType.ChevTwo.OppCl.TK.commR_of_fixed Z hZo hρ hQt2 hRhB hNQ hx ?_
    intro γ hγ
    exact hRβfix γ hγ _ (hQtmap ▸ Subgroup.mem_map_of_mem _ hx)
  obtain ⟨r, hrRh, hrind⟩ := hRhA β (Subgroup.mem_zpowers β)
  obtain ⟨c, hc⟩ := hrigid p hp hp2 Rh hRhs hRhP hRhp hRhN Qt hQt2 (by rw [hKFeq]; exact hQt0)
    hcomm r hrRh
  apply hβ1
  have hc0 : c ≠ 0 := by
    intro hc0
    have hsub : Subsingleton V := ⟨fun u v => r.injective (by rw [hc u, hc v, hc0, zero_smul, zero_smul])⟩
    have hHsub : ∀ h : H, h = 1 := fun h =>
      hρ (LinearMap.ext fun v => Subsingleton.elim _ _)
    apply hR.1
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Z y
    rw [hHsub h]
    simp
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Z y
  obtain ⟨h', hh', hβh⟩ := hrind.1 h
  have hρeq : ρ h = ρ h' := by
    ext v
    have := hh' v
    rw [hc, hc, map_smul] at this
    exact smul_right_injective V hc0 this
  have : h = h' := hρ hρeq
  rw [MulAut.one_apply, hβh, this]

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
