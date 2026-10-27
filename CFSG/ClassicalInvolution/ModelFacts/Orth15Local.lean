module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Alpha
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
variable {X : Type} [Group X]

variable (Q) in
@[expose] def KerScalar (e : ↥(elementaryGroup Q) →* X) : Prop :=
  ∀ g : ↥(elementaryGroup Q), e g = 1 → (g : V ≃ₗ[F] V) ∈ scalars F V

section Bridge

variable (e : ↥(elementaryGroup Q) →* X)

def img (H : Subgroup (V ≃ₗ[F] V)) : Subgroup X :=
  (H.subgroupOf (elementaryGroup Q)).map e

theorem mem_img_iff {H : Subgroup (V ≃ₗ[F] V)} {x : X} :
    x ∈ img e H ↔ ∃ g : ↥(elementaryGroup Q), (g : V ≃ₗ[F] V) ∈ H ∧ e g = x := by
  unfold img
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨g, hg, hx⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg, hx⟩,
    fun ⟨g, hg, hx⟩ => ⟨g, Subgroup.mem_subgroupOf.mpr hg, hx⟩⟩

theorem img_mono {H H' : Subgroup (V ≃ₗ[F] V)} (h : H ≤ H') : img e H ≤ img e H' := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hx
  exact (mem_img_iff e).mpr ⟨g, h hg, rfl⟩

theorem img_le_range (H : Subgroup (V ≃ₗ[F] V)) : img e H ≤ e.range := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := (mem_img_iff e).mp hx
  exact ⟨g, rfl⟩

theorem mem_range_iff {x : X} : x ∈ e.range ↔ ∃ g : ↥(elementaryGroup Q), e g = x := Iff.rfl

theorem exists_rel_of_commute (hker : KerScalar Q e) {g a : ↥(elementaryGroup Q)}
    (h : e g * e a = e a * e g) :
    ∃ c : F, ∀ x, (g : V ≃ₗ[F] V) ((a : V ≃ₗ[F] V) x) =
      c • (a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) x) := by
  have h1 : e (g * a * g⁻¹ * a⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨c, hc⟩ := mem_scalars.mp (hker _ h1)
  refine ⟨c, fun x => ?_⟩
  have := hc ((a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) x))
  simpa using this

theorem commute_of_e_commute (hker : KerScalar Q e) {g h : ↥(elementaryGroup Q)}
    {T : Submodule F V} (hgT : ∀ x, x ∈ T ↔ (g : V ≃ₗ[F] V) x ∈ T)
    (hh : (h : V ≃ₗ[F] V) ∈ elemOn Q T) (hz : ∃ z : V, z ≠ 0 ∧ ∀ x ∈ T, polar Q z x = 0)
    (hc : e g * e h = e h * e g) : (g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) =
      (h : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
  have h1 : e (g * h * g⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  obtain ⟨c, hc'⟩ := mem_scalars.mp (hker _ h1)
  obtain ⟨z, hz0, hzT⟩ := hz
  have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q g.2
  have hhfix := (support_of_mem_elemOn hh).2
  have hhz : (h : V ≃ₗ[F] V) z = z := hhfix z hzT
  have hhz' : (h : V ≃ₗ[F] V)⁻¹ z = z := by
    apply (h : V ≃ₗ[F] V).injective
    rw [LinearEquiv.apply_inv_apply', hhz]
  have hgz : ∀ x ∈ T, polar Q ((g : V ≃ₗ[F] V)⁻¹ z) x = 0 := by
    intro x hx
    rw [← polar_map_of_mem hgO ((g : V ≃ₗ[F] V)⁻¹ z) x, LinearEquiv.apply_inv_apply']
    exact hzT _ ((hgT x).mp hx)
  have hgz' : (h : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V)⁻¹ z) = (g : V ≃ₗ[F] V)⁻¹ z := hhfix _ hgz
  have h2 := hc' z
  have h3 : ((g * h * g⁻¹ * h⁻¹ : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) z = z := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
    rw [hhz', hgz', LinearEquiv.apply_inv_apply']
  rw [h3] at h2
  have hc1 : c = 1 := by
    have : (c - 1) • z = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)
  have h4 : (g * h * g⁻¹ * h⁻¹ : ↥(elementaryGroup Q)) = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hc' v, hc1, one_smul]
    rfl
  have h5 : g * h = h * g := by
    rw [mul_inv_eq_one.symm] at h4
    exact (mul_inv_eq_one.mp (by simpa [mul_assoc] using h4))
  exact congrArg Subtype.val h5

theorem rel_pow {g a : V ≃ₗ[F] V} {c : F} (hc : ∀ x, g (a x) = c • a (g x)) (k : ℕ) :
    ∀ x, (g ^ k) (a x) = c ^ k • a ((g ^ k) x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', LinearEquiv.mul_apply, ih x, map_smul, hc, smul_smul, LinearEquiv.mul_apply,
      pow_succ]

end Bridge

section Local

variable (e : ↥(elementaryGroup Q) →* X)

structure LocalData (e : ↥(elementaryGroup Q) →* X) (a : ↥(elementaryGroup Q))
    (S T : Submodule F V) : Prop where
  split : SplitInv Q S T (a : V ≃ₗ[F] V)
  ker : KerScalar Q e
  S_ne : S ≠ ⊥
  T_ne : T ≠ ⊥

variable {e} {a : ↥(elementaryGroup Q)} {S T : Submodule F V}

theorem LocalData.nontrivial (D : LocalData e a S T) : Nontrivial V := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot D.S_ne
  exact ⟨⟨x, 0, hx0⟩⟩

theorem LocalData.ne_one (h2 : (2 : F) ≠ 0) (D : LocalData e a S T) : e a ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := mem_scalars.mp (D.ker a h1)
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot D.S_ne
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot D.T_ne
  have h3 : (c + 1) • s = 0 := by
    rw [add_smul, one_smul, ← hc s]
    rw [D.split.negS s hs, neg_add_cancel]
  have h4 : (c - 1) • t = 0 := by
    rw [sub_smul, one_smul, ← hc t, D.split.fixT t ht, sub_self]
  have hc1 : c = -1 := eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h3).resolve_right hs0)
  have hc2 : c = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right ht0)
  rw [hc1] at hc2
  have : (2 : F) = 0 := by linear_combination -hc2
  exact h2 this

theorem LocalData.exists_perp_right (D : LocalData e a S T) :
    ∃ z : V, z ≠ 0 ∧ ∀ x ∈ S, polar Q z x = 0 := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot D.T_ne
  exact ⟨z, hz0, fun x hx => by rw [polar_comm]; exact D.split.orth x hx z hz⟩

theorem LocalData.exists_perp_left (D : LocalData e a S T) :
    ∃ z : V, z ≠ 0 ∧ ∀ x ∈ T, polar Q z x = 0 := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot D.S_ne
  exact ⟨z, hz0, fun x hx => D.split.orth z hz x hx⟩

theorem join_le_centralizer (D : LocalData e a S T) :
    elemOn Q S ⊔ elemOn Q T ≤ Subgroup.centralizer ({(a : V ≃ₗ[F] V)} : Set (V ≃ₗ[F] V)) := by
  refine sup_le (fun y hy => ?_) (fun y hy => ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (D.split.commute_of_mem_elemOn_left hy).symm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (D.split.commute_of_mem_elemOn_right hy).symm

theorem img_join_le_centralizer (D : LocalData e a S T) :
    img e (elemOn Q S ⊔ elemOn Q T) ≤ Subgroup.centralizer ({e a} : Set X) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (join_le_centralizer D hg)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h1

theorem conj_mem_img (h2 : (2 : F) ≠ 0) (D : LocalData e a S T) {x : X}
    (hx : x ∈ e.range ⊓ Subgroup.centralizer ({e a} : Set X)) {p : X}
    (hp : p ∈ img e (elemOn Q S ⊔ elemOn Q T)) :
    x * p * x⁻¹ ∈ img e (elemOn Q S ⊔ elemOn Q T) := by
  have := D.nontrivial
  obtain ⟨g, rfl⟩ := hx.1
  obtain ⟨y, hy, rfl⟩ := (mem_img_iff e).mp hp
  have hxc : e a * e g = e g * e a := (Subgroup.mem_centralizer_iff.mp hx.2) (e a) rfl
  obtain ⟨c, hc⟩ := exists_rel_of_commute e D.ker hxc.symm
  have hgO := elementaryGroup_le_orthogonalGroup Q g.2
  have h3 := D.split.conj_mem_join h2 hgO hc hy
  refine (mem_img_iff e).mpr ⟨g * y * g⁻¹, ?_, ?_⟩
  · simpa using h3
  · simp

theorem rel_one_of_odd (h2 : (2 : F) ≠ 0) (D : LocalData e a S T) {N : Subgroup X}
    (hodd : Odd (Nat.card N)) {g : ↥(elementaryGroup Q)} (hg : e g ∈ N)
    (hgc : e g * e a = e a * e g) :
    ∀ x, (g : V ≃ₗ[F] V) ((a : V ≃ₗ[F] V) x) = (a : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) x) := by
  have := D.nontrivial
  obtain ⟨c, hc⟩ := exists_rel_of_commute e D.ker hgc
  rcases D.split.sign_of_rel hc with rfl | rfl
  · intro x
    rw [hc x, one_smul]
  · exfalso
    set m := orderOf (e g) with hm
    have hmodd : Odd m := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hg)
    have hgm : e (g ^ m) = 1 := by rw [map_pow, hm, pow_orderOf_eq_one]
    obtain ⟨d, hd⟩ := mem_scalars.mp (D.ker _ hgm)
    have hcoe : ((g ^ m : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) = (g : V ≃ₗ[F] V) ^ m :=
      Subgroup.coe_pow _ _ _
    have hpow := rel_pow hc m
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hax : (a : V ≃ₗ[F] V) x ≠ 0 := fun h0 => hx ((a : V ≃ₗ[F] V).injective (by
      rw [h0, map_zero]))
    have h1 := hpow x
    rw [← hcoe, hd, hd, map_smul, Odd.neg_one_pow hmodd] at h1
    have h3 : (d + d) • (a : V ≃ₗ[F] V) x = 0 := by
      rw [add_smul]
      nth_rewrite 1 [h1]
      rw [neg_one_smul, neg_add_cancel]
    have h4 : d = 0 := by
      have h5 : (2 * d) • (a : V ≃ₗ[F] V) x = 0 := by rw [two_mul]; exact h3
      have := (smul_eq_zero.mp h5).resolve_right hax
      exact (mul_eq_zero.mp this).resolve_left h2
    have h6 := hd x
    rw [h4, zero_smul] at h6
    exact hx (((g ^ m : ↥(elementaryGroup Q)) : V ≃ₗ[F] V).injective (by rw [h6, map_zero]))

section Layers

theorem isQuasisimple_img (hker : KerScalar Q e) {H : Subgroup (V ≃ₗ[F] V)}
    (hHE : H ≤ elementaryGroup Q) (hq : CFSG.Open.IsQuasisimple ↥H)
    (hinj : ∀ g ∈ H, g ∈ scalars F V → g = 1) : CFSG.Open.IsQuasisimple ↥(img e H) := by
  set K : Subgroup ↥(elementaryGroup Q) := H.subgroupOf (elementaryGroup Q) with hK
  have hinj' : Function.Injective (e.domRestrict K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : e (g : ↥(elementaryGroup Q)) = 1 := hg
    have h2 := hker _ h1
    have h3 : ((g : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) = 1 :=
      hinj _ (Subgroup.mem_subgroupOf.mp g.2) h2
    exact Subtype.ext (Subtype.ext h3)
  have e1 : ↥H ≃* ↥K := (Subgroup.subgroupOfEquivOfLe hHE).symm
  have e2 : ↥K ≃* ↥((e.domRestrict K).range) := MonoidHom.ofInjective hinj'
  have e3 : ↥((e.domRestrict K).range) ≃* ↥(img e H) :=
    MulEquiv.subgroupCongr (by rw [MonoidHom.domRestrict_range]; rfl)
  exact CFSG.ClassicalInvolution.Balance.StrongBalance.Orth.isQuasisimple_of_mulEquiv_open
    (e1.trans (e2.trans e3)) hq

theorem eq_one_of_scalar_of_mem_elemOn (D : LocalData e a S T) {g : V ≃ₗ[F] V}
    (hg : g ∈ elemOn Q S) (hs : g ∈ scalars F V) : g = 1 := by
  obtain ⟨z, hz0, hz⟩ := D.exists_perp_right
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have h1 : g z = z := (support_of_mem_elemOn hg).2 z hz
  have hc1 : c = 1 := by
    rw [hc z] at h1
    have : (c - 1) • z = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)
  refine LinearEquiv.ext fun v => ?_
  rw [hc v, hc1, one_smul]
  rfl

theorem eq_one_of_scalar_of_mem_elemOn' (D : LocalData e a S T) {g : V ≃ₗ[F] V}
    (hg : g ∈ elemOn Q T) (hs : g ∈ scalars F V) : g = 1 := by
  obtain ⟨z, hz0, hz⟩ := D.exists_perp_left
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have h1 : g z = z := (support_of_mem_elemOn hg).2 z hz
  have hc1 : c = 1 := by
    rw [hc z] at h1
    have : (c - 1) • z = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)
  refine LinearEquiv.ext fun v => ?_
  rw [hc v, hc1, one_smul]
  rfl

theorem conj_mem_join_of_normalized (horth : ∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0)
    {H : Subgroup (V ≃ₗ[F] V)} (hHle : H ≤ elemOn Q S)
    (hHn : ∀ g ∈ elemOn Q S, ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    {g : V ≃ₗ[F] V} (hg : g ∈ elemOn Q S ⊔ elemOn Q T) {h : V ≃ₗ[F] V} (hh : h ∈ H) :
    g * h * g⁻¹ ∈ H := by
  have hS : elemOn Q S ≤ Subgroup.normalizer (H : Set (V ≃ₗ[F] V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hHn g hg h hh, fun hh => ?_⟩
    have := hHn g⁻¹ (inv_mem hg) _ hh
    simpa [mul_assoc] using this
  have hc : ∀ g ∈ elemOn Q T, ∀ k ∈ H, g * k * g⁻¹ = k := by
    intro g hg k hk
    have := commute_elemOn_elemOn (Q := Q) (S := S) (T := T)
      horth (hHle hk) hg
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hT : elemOn Q T ≤ Subgroup.normalizer (H : Set (V ≃ₗ[F] V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hc g hg h hh]
      exact hh
    · intro hh
      have h1 := hc g⁻¹ (inv_mem hg) _ hh
      have h2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [h2] at h1
      rw [h1]
      exact hh
  have : elemOn Q S ⊔ elemOn Q T ≤ Subgroup.normalizer (H : Set (V ≃ₗ[F] V)) := sup_le hS hT
  exact (Subgroup.mem_normalizer_iff.mp (this hg) h).mp hh

theorem exists_layers_img (D : LocalData e a S T) (layS : LayerGenOn Q S)
    (layT : LayerGenOn Q T) :
    ∃ 𝓗 : Set (Subgroup X),
      (∀ H ∈ 𝓗, H ≤ img e (elemOn Q S ⊔ elemOn Q T) ∧ CFSG.Open.IsQuasisimple ↥H ∧
        ∀ p ∈ img e (elemOn Q S ⊔ elemOn Q T), ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧
      img e (elemOn Q S ⊔ elemOn Q T) ≤ ⨆ H ∈ 𝓗, H := by
  obtain ⟨𝓗S, hS, hSc⟩ := layS
  obtain ⟨𝓗T, hT, hTc⟩ := layT
  have horth : ∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0 := fun x hx y hy => D.split.orth x hx y hy
  have horth' : ∀ x ∈ T, ∀ y ∈ S, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]; exact horth y hy x hx
  refine ⟨(fun H => img e H) '' (𝓗S ∪ 𝓗T), ?_, ?_⟩
  · rintro _ ⟨H, hH, rfl⟩
    rcases hH with hH | hH
    · obtain ⟨hHle, hHq, hHn⟩ := hS H hH
      have hHE : H ≤ elementaryGroup Q := hHle.trans elemOn_le_elementaryGroup
      refine ⟨img_mono e (hHle.trans le_sup_left), isQuasisimple_img D.ker hHE hHq
        (fun g hg hs => eq_one_of_scalar_of_mem_elemOn D (hHle hg) hs), ?_⟩
      intro p hp k hk
      obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hp
      obtain ⟨k', hk', rfl⟩ := (mem_img_iff e).mp hk
      refine (mem_img_iff e).mpr ⟨g * k' * g⁻¹, ?_, by simp⟩
      simpa using conj_mem_join_of_normalized horth hHle hHn hg hk'
    · obtain ⟨hHle, hHq, hHn⟩ := hT H hH
      have hHE : H ≤ elementaryGroup Q := hHle.trans elemOn_le_elementaryGroup
      refine ⟨img_mono e (hHle.trans le_sup_right), isQuasisimple_img D.ker hHE hHq
        (fun g hg hs => eq_one_of_scalar_of_mem_elemOn' D (hHle hg) hs), ?_⟩
      intro p hp k hk
      obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hp
      obtain ⟨k', hk', rfl⟩ := (mem_img_iff e).mp hk
      refine (mem_img_iff e).mpr ⟨g * k' * g⁻¹, ?_, by simp⟩
      rw [sup_comm] at hg
      simpa using conj_mem_join_of_normalized horth' hHle hHn hg hk'
  · set M : Subgroup X := ⨆ Hb ∈ (fun H => img e H) '' (𝓗S ∪ 𝓗T), Hb with hM
    set K : Subgroup (V ≃ₗ[F] V) := (M.comap e).map (elementaryGroup Q).subtype with hK
    have hlay : ∀ H ∈ 𝓗S ∪ 𝓗T, H ≤ elementaryGroup Q → H ≤ K := by
      intro H hH hHE h hh
      refine ⟨⟨h, hHE hh⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact (le_iSup₂ (f := fun (Hb : Subgroup X) (_ : Hb ∈ (fun H => img e H) '' (𝓗S ∪ 𝓗T)) => Hb)
        (img e H) ⟨H, hH, rfl⟩) ((mem_img_iff e).mpr ⟨⟨h, hHE hh⟩, hh, rfl⟩)
    have hSK : elemOn Q S ≤ K := by
      refine hSc.trans (iSup₂_le fun H hH => hlay H (Or.inl hH) ?_)
      exact (hS H hH).1.trans elemOn_le_elementaryGroup
    have hTK : elemOn Q T ≤ K := by
      refine hTc.trans (iSup₂_le fun H hH => hlay H (Or.inr hH) ?_)
      exact (hT H hH).1.trans elemOn_le_elementaryGroup
    intro x hx
    obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hx
    obtain ⟨g', hg', hg'g⟩ := sup_le hSK hTK hg
    have : g' = g := Subtype.ext hg'g
    subst this
    exact hg'

theorem img_join_perfect (D : LocalData e a S T) (layS : LayerGenOn Q S)
    (layT : LayerGenOn Q T) :
    img e (elemOn Q S ⊔ elemOn Q T) ≤
      ⁅img e (elemOn Q S ⊔ elemOn Q T), img e (elemOn Q S ⊔ elemOn Q T)⁆ := by
  obtain ⟨𝓗, hH, hP⟩ := exists_layers_img D layS layT
  refine hP.trans (iSup₂_le fun H hH' => ?_)
  obtain ⟨hHle, hHq, -⟩ := hH H hH'
  rw [← CFSG.ClassicalInvolution.ModelFacts.Orth15.commutator_self_of_perfect hHq.1]
  exact Subgroup.commutator_mono hHle hHle

theorem commutator_img_eq_bot [Finite X] (h2 : (2 : F) ≠ 0) (D : LocalData e a S T)
    (layS : LayerGenOn Q S) (layT : LayerGenOn Q T) {N : Subgroup X}
    (hNle : N ≤ e.range ⊓ Subgroup.centralizer ({e a} : Set X))
    (hNnorm : ∀ x ∈ e.range ⊓ Subgroup.centralizer ({e a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : ⁅N, img e (elemOn Q S ⊔ elemOn Q T)⁆ = ⊥ := by
  obtain ⟨𝓗, hH, hP⟩ := exists_layers_img D layS layT
  refine commutator_eq_bot_of_layers (img e (elemOn Q S ⊔ elemOn Q T)) N 𝓗 hH hP ?_ ?_ hodd
  · intro p hp o ho
    exact hNnorm p ⟨img_le_range e _ hp, img_join_le_centralizer D hp⟩ o ho
  · intro o ho p hp
    exact conj_mem_img h2 D (hNle ho) hp

theorem preserves_of_odd (h2 : (2 : F) ≠ 0) (D : LocalData e a S T) {N : Subgroup X}
    (hNle : N ≤ e.range ⊓ Subgroup.centralizer ({e a} : Set X)) (hodd : Odd (Nat.card N))
    {g : ↥(elementaryGroup Q)} (hg : e g ∈ N) :
    (∀ x, x ∈ S ↔ (g : V ≃ₗ[F] V) x ∈ S) ∧ ∀ x, x ∈ T ↔ (g : V ≃ₗ[F] V) x ∈ T := by
  have hgc : e g * e a = e a * e g :=
    ((Subgroup.mem_centralizer_iff.mp (hNle hg).2) (e a) rfl).symm
  exact D.split.preserves_of_comm h2 (rel_one_of_odd h2 D hodd hg hgc)

theorem commute_join_of_odd [Finite X] (h2 : (2 : F) ≠ 0) (D : LocalData e a S T)
    (layS : LayerGenOn Q S) (layT : LayerGenOn Q T) {N : Subgroup X}
    (hNle : N ≤ e.range ⊓ Subgroup.centralizer ({e a} : Set X))
    (hNnorm : ∀ x ∈ e.range ⊓ Subgroup.centralizer ({e a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {g : ↥(elementaryGroup Q)} (hg : e g ∈ N)
    {y : V ≃ₗ[F] V} (hy : y ∈ elemOn Q S ⊔ elemOn Q T) :
    (g : V ≃ₗ[F] V) * y = y * g := by
  have hNP := commutator_img_eq_bot h2 D layS layT hNle hNnorm hodd
  obtain ⟨hgS, hgT⟩ := preserves_of_odd h2 D hNle hodd hg
  have key : elemOn Q S ⊔ elemOn Q T ≤ Subgroup.centralizer ({(g : V ≃ₗ[F] V)} :
      Set (V ≃ₗ[F] V)) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · have yE : y ∈ elementaryGroup Q := elemOn_le_elementaryGroup hy
      have hmem : e ⟨y, yE⟩ ∈ img e (elemOn Q S ⊔ elemOn Q T) :=
        (mem_img_iff e).mpr ⟨⟨y, yE⟩, Subgroup.mem_sup_left hy, rfl⟩
      have hc := comm_of_commutator_eq_bot hNP hg hmem
      have := commute_of_e_commute e D.ker hgS hy D.exists_perp_right hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact this.symm
    · have yE : y ∈ elementaryGroup Q := elemOn_le_elementaryGroup hy
      have hmem : e ⟨y, yE⟩ ∈ img e (elemOn Q S ⊔ elemOn Q T) :=
        (mem_img_iff e).mpr ⟨⟨y, yE⟩, Subgroup.mem_sup_right hy, rfl⟩
      have hc := comm_of_commutator_eq_bot hNP hg hmem
      have := commute_of_e_commute e D.ker hgT hy D.exists_perp_left hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact this.symm
  have := Subgroup.mem_centralizer_singleton_iff.mp (key hy)
  exact this.symm

variable [Finite F] [FiniteDimensional F V]

theorem exists_smul_left_of_odd [Finite X] (hodd' : Odd (Nat.card F)) (D : LocalData e a S T)
    (layS : LayerGenOn Q S) (layT : LayerGenOn Q T) {N : Subgroup X}
    (hNle : N ≤ e.range ⊓ Subgroup.centralizer ({e a} : Set X))
    (hNnorm : ∀ x ∈ e.range ⊓ Subgroup.centralizer ({e a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {g : ↥(elementaryGroup Q)} (hg : e g ∈ N)
    (h3 : 3 ≤ Module.finrank F S) : ∃ c : F, ∀ x ∈ S, (g : V ≃ₗ[F] V) x = c • x := by
  have h2 := two_ne_zero_of_odd_card hodd'
  exact exists_smul_of_commute_elemOn hodd' D.split.ndS h3
    (elementaryGroup_le_orthogonalGroup Q g.2) (preserves_of_odd h2 D hNle hodd hg).1
    (fun h hh => commute_join_of_odd h2 D layS layT hNle hNnorm hodd hg (Subgroup.mem_sup_left hh))

theorem exists_smul_right_of_odd [Finite X] (hodd' : Odd (Nat.card F)) (D : LocalData e a S T)
    (layS : LayerGenOn Q S) (layT : LayerGenOn Q T) {N : Subgroup X}
    (hNle : N ≤ e.range ⊓ Subgroup.centralizer ({e a} : Set X))
    (hNnorm : ∀ x ∈ e.range ⊓ Subgroup.centralizer ({e a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {g : ↥(elementaryGroup Q)} (hg : e g ∈ N)
    (h3 : 3 ≤ Module.finrank F T) : ∃ c : F, ∀ x ∈ T, (g : V ≃ₗ[F] V) x = c • x := by
  have h2 := two_ne_zero_of_odd_card hodd'
  exact exists_smul_of_commute_elemOn hodd' D.split.ndT h3
    (elementaryGroup_le_orthogonalGroup Q g.2) (preserves_of_odd h2 D hNle hodd hg).2
    (fun h hh => commute_join_of_odd h2 D layS layT hNle hNnorm hodd hg (Subgroup.mem_sup_right hh))

omit [Finite F] [FiniteDimensional F V] in
theorem commute_of_scalar_on_T {S T : Submodule F V} (hdec : ∀ x : V, ∃ s ∈ S, ∃ t ∈ T, x = s + t)
    {g b : V ≃ₗ[F] V} (hgS : ∀ x ∈ S, g x ∈ S) {c : F} (hgT : ∀ x ∈ T, g x = c • x)
    (hbS : ∀ x ∈ S, b x = x) (hbT : ∀ x ∈ T, b x ∈ T) : g * b = b * g := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := hdec x
  simp only [LinearEquiv.mul_apply, map_add, hbS s hs, hgT t ht, hbS _ (hgS s hs), map_smul,
    hgT _ (hbT t ht)]


end Layers

end Local

end CFSG.ClassicalInvolution.ModelFacts.Orth15
