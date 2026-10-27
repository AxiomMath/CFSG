module

public import CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoLeviCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoTailMaps

public noncomputable section

namespace CFSG.LieType.Chevalley.TwistedE6FieldTwoCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.RelativeRoots CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover
  CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open Subgroup
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem exists_mul_eq_of_mem_sup {H N : Subgroup G} (h : H ≤ normalizer (N : Set G)) {x : G}
    (hx : x ∈ H ⊔ N) : ∃ a ∈ H, ∃ b ∈ N, a * b = x := by
  let M : Subgroup G :=
    { carrier := {g | ∃ a ∈ H, ∃ b ∈ N, a * b = g}
      one_mem' := ⟨1, H.one_mem, 1, N.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, H.mul_mem ha₁ ha₂, a₂⁻¹ * b₁ * a₂ * b₂, N.mul_mem ?_ hb₂, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (h (H.inv_mem ha₂)) b₁).1 hb₁
        rwa [inv_inv] at this
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, H.inv_mem ha, a * b⁻¹ * a⁻¹,
          (Subgroup.mem_normalizer_iff.1 (h ha) b⁻¹).1 (N.inv_mem hb), by group⟩ }
  exact (sup_le (fun a ha => ⟨a, ha, 1, N.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, H.one_mem, b, hb, one_mul b⟩) : H ⊔ N ≤ M) hx

theorem le_normalizer_of_commute {H N : Subgroup G} (h : ∀ a ∈ H, ∀ b ∈ N, a * b = b * a) :
    H ≤ normalizer (N : Set G) := fun a ha => Subgroup.mem_normalizer_iff.2 fun b => by
  constructor
  · intro hb
    rw [h a ha b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have e : a * b * a⁻¹ = b :=
      mul_left_cancel ((h a ha _ hb).trans (by group))
    rwa [e] at hb

theorem card_sup_le_of_le_normalizer [Finite G] {H N : Subgroup G}
    (h : H ≤ normalizer (N : Set G)) : Nat.card ↥(H ⊔ N) ≤ Nat.card H * Nat.card N := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun p : H × N => (⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩ : ↥(H ⊔ N))) fun x => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_eq_of_mem_sup h x.2
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem card_iSup_le_prod {τ : Tag} [Finite G] (Y : (Fin τ.rank → ℤ) → Subgroup G)
    (L : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → Set (Fin τ.rank → ℤ))
    (hL : ∀ α β, IsRoot τ α → 0 < height α → IsRoot τ β → 0 < height β → α ≠ β →
      ∀ γ ∈ L α β, height α < height γ)
    (hrel : ∀ α β, IsRoot τ α → 0 < height α → IsRoot τ β → 0 < height β → α ≠ β →
      ∀ a ∈ Y α, ∀ b ∈ Y β, ⁅a, b⁆ ∈ ⨆ γ ∈ L α β, Y γ) :
    ∀ T : Finset (Fin τ.rank → ℤ), (∀ α ∈ T, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ T, ∀ β ∈ T, α ≠ β → ∀ γ ∈ L α β, γ ∈ T) →
      Nat.card ↥(⨆ α ∈ T, Y α) ≤ ∏ α ∈ T, Nat.card (Y α) := by
  classical
  intro T
  induction T using Finset.induction_on_min_value height with
  | empty =>
    intro _ _
    simp
  | insert a s has hmin ih =>
    intro hT hcl
    have ha := hT a (Finset.mem_insert_self _ _)
    have hT_s : ∀ α ∈ s, IsRoot τ α ∧ 0 < height α := fun α hα =>
      hT α (Finset.mem_insert_of_mem hα)
    have hcl_s : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → ∀ γ ∈ L α β, γ ∈ s := by
      intro α hα β hβ hne γ hγ
      rcases Finset.mem_insert.mp (hcl α (Finset.mem_insert_of_mem hα) β
        (Finset.mem_insert_of_mem hβ) hne γ hγ) with h' | h'
      · exfalso
        have h1 := hmin α hα
        have h2 := hL α β (hT_s α hα).1 (hT_s α hα).2 (hT_s β hβ).1 (hT_s β hβ).2 hne γ hγ
        rw [h'] at h2
        omega
      · exact h'
    have ih' := ih hT_s hcl_s
    set N := ⨆ α ∈ s, Y α with hN
    have hconj : ∀ y ∈ Y a, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
      intro y hy x hx
      have hle : N ≤ N.comap (MulAut.conj y).toMonoidHom := by
        refine iSup₂_le fun β hβ b hb => ?_
        change y * b * y⁻¹ ∈ N
        have hne : a ≠ β := fun h => has (h ▸ hβ)
        rw [show y * b * y⁻¹ = ⁅y, b⁆ * b by simp only [commutatorElement_def]; group]
        refine N.mul_mem ?_ ((le_iSup₂ (f := fun α (_ : α ∈ s) => Y α) β hβ) hb)
        refine (iSup₂_le fun γ hγ => ?_ : (⨆ γ ∈ L a β, Y γ) ≤ N)
          (hrel a β ha.1 ha.2 (hT_s β hβ).1 (hT_s β hβ).2 hne y hy b hb)
        rcases Finset.mem_insert.mp (hcl a (Finset.mem_insert_self _ _) β
          (Finset.mem_insert_of_mem hβ) hne γ hγ) with h' | h'
        · exfalso
          have h2 := hL a β ha.1 ha.2 (hT_s β hβ).1 (hT_s β hβ).2 hne γ hγ
          rw [h'] at h2
          omega
        · exact le_iSup₂ (f := fun α (_ : α ∈ s) => Y α) γ h'
      exact hle hx
    have hnorm : Y a ≤ normalizer (N : Set G) := fun y hy =>
      Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hconj y hy x hx, fun hx => by
        have h1 := hconj y⁻¹ (inv_mem hy) _ hx
        rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at h1⟩
    rw [Finset.iSup_insert, Finset.prod_insert has]
    exact (card_sup_le_of_le_normalizer hnorm).trans (Nat.mul_le_mul_left _ ih')

end General

theorem relRootGroup_le_stdGroup
    (r : Fin Tag.F4.rank → ℤ) : relRootGroup r ≤ stdGroup := by
  rw [← stdFixedGroup_eq_stdGroup]
  exact inf_le_right

abbrev relG
    (r : Fin Tag.F4.rank → ℤ) : Subgroup stdGroup :=
  (relRootGroup r).comap stdGroup.subtype

theorem card_relG
    (r : Fin Tag.F4.rank → ℤ) : Nat.card (relG r) = Nat.card (relRootGroup r) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (relRootGroup_le_stdGroup r)).toEquiv

theorem relRootGroup_eq_bot
    {r : Fin Tag.F4.rank → ℤ} (hr : ¬ IsRoot .F4 r) :
    relRootGroup r = ⊥ := by
  have h : relFibre r = ∅ := Set.eq_empty_of_forall_notMem fun β hβ =>
    hr (hβ.2 ▸ isRoot_relProj hβ.1)
  simp [relRootGroup, h, rootSpan]

theorem eq_one_of_mem_relG
    {r : Fin Tag.F4.rank → ℤ} (hr : ¬ IsRoot .F4 r) {g : stdGroup}
    (hg : g ∈ relG r) : g = 1 := by
  exact Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 (relRootGroup_eq_bot hr) _ hg)

theorem relSpan_empty
    : relSpan (∅ : Set (Fin Tag.F4.rank → ℤ)) = ⊥ := by
  simp [relSpan]

theorem relSpan_singleton
    (γ : Fin Tag.F4.rank → ℤ) : relSpan {γ} = relRootGroup γ := by
  simp [relSpan]

theorem relSpan_pair
    (γ δ : Fin Tag.F4.rank → ℤ) :
    relSpan {γ, δ} = relRootGroup γ ⊔ relRootGroup δ := by
  simp [relSpan, iSup_or, iSup_sup_eq]

theorem relSupport_eq_empty
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (hne : r ≠ s) (hne' : r ≠ -s) (hip : 0 ≤ f4Ip r s)
    (horth : ¬ (f4Len r = 1 ∧ f4Len s = 1 ∧ f4Ip r s = 0)) : relSupport r s = ∅ := by
  have hpos := f4Len_pos hr
  refine (relSupport_cases hr hs hne hne').2.2.2 ?_ ?_ ?_
  · rintro (⟨-, h⟩ | h)
    · change 2 * f4Ip r s = -f4Len r at h
      linarith
    · exact horth h
  · rintro ⟨-, -, h⟩
    change f4Ip r s = -1 at h
    linarith
  · rintro ⟨-, -, h⟩
    change f4Ip r s = -1 at h
    linarith

theorem commute_of_relSupport_eq_empty
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r)
    (hs : IsRoot .F4 s) (hne : r ≠ s) (hne' : r ≠ -s) (h : relSupport r s = ∅) :
    ∀ a ∈ relRootGroup r, ∀ b ∈ relRootGroup s, a * b = b * a := by
  intro a ha b hb
  have hc := commutator_relRootGroup_le hr hs hne hne' (Subgroup.commutator_mem_commutator ha hb)
  rw [h, relSpan_empty, Subgroup.mem_bot] at hc
  exact commutatorElement_eq_one_iff_mul_comm.1 hc

section Lifts

variable
    {E : Type*} [Group E] [Finite E] {η : E →* stdGroup} (hη : Function.Surjective η)
  (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker)

include hη hC h2 in
theorem exists_lift_mul_self_relG
    {r : Fin Tag.F4.rank → ℤ} {g : stdGroup} (hg : g ∈ relG r) :
    ∃ y, η y = g ∧ y * y = 1 := by
  by_cases hr : IsRoot .F4 r
  · obtain ⟨F, hFmap, hFker, -⟩ := exists_split_relRootGroup η hη hC h2 hr
    obtain ⟨f, hf, rfl⟩ : g ∈ F.map η := by rw [hFmap]; exact hg
    refine ⟨f, rfl, ?_⟩
    have h1 : f * f ∈ F ⊓ η.ker := Subgroup.mem_inf.2 ⟨F.mul_mem hf hf, by
      rw [MonoidHom.mem_ker, map_mul]
      exact Subtype.ext ((relRootGroup_elementary hr).2 _ hg)⟩
    rw [hFker] at h1
    exact Subgroup.mem_bot.1 h1
  · rw [eq_one_of_mem_relG hr hg]
    exact ⟨1, map_one η, mul_one 1⟩

include hη hC h2 in
theorem liftsCommute_relG_self
    {r : Fin Tag.F4.rank → ℤ} {u v : stdGroup} (hu : u ∈ relG r)
    (hv : v ∈ relG r) : LiftsCommute η u v := by
  intro a b ha hb
  by_cases hr : IsRoot .F4 r
  · obtain ⟨n, hn, hle, -⟩ := exists_conj_levi_root hr
    exact commute_preimage_of_le_leviConj η hη hC h2 hn hle hle (relRootGroup_elementary hr).1 a
      (by rw [Subgroup.mem_comap, ha]; exact hu) b (by rw [Subgroup.mem_comap, hb]; exact hv)
  · rw [eq_one_of_mem_relG hr hu] at ha
    exact (Subgroup.mem_center_iff.1 (hC ha) b).symm

include hη hC h2 in
theorem liftsCommute_of_levi
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (htype : (f4Len r = 2 ∧ f4Len s = 2) ∨ f4Len r ≠ f4Len s ∨
      (f4Len r = 1 ∧ f4Len s = 1 ∧ f4Ip r s = 0))
    (hcomm : ∀ a ∈ relRootGroup r, ∀ b ∈ relRootGroup s, a * b = b * a) {u v : stdGroup}
    (hu : u ∈ relG r) (hv : v ∈ relG s) : LiftsCommute η u v := by
  obtain ⟨n, hn, hrn, hsn⟩ := exists_conj_levi_pair hr hs htype
  intro a b ha hb
  exact commute_preimage_of_le_leviConj η hη hC h2 hn hrn hsn hcomm a
    (by rw [Subgroup.mem_comap, ha]; exact hu) b (by rw [Subgroup.mem_comap, hb]; exact hv)

theorem f4Euclid_vL1 : f4Euclid vL1 = Pi.single 0 1 - Pi.single 1 1 := by
  decide +kernel

theorem f4Euclid_vE2 : f4Euclid vE2 = Pi.single 1 1 := by
  decide +kernel

theorem f4Euclid_vS1 : f4Euclid vS1 = Pi.single 0 1 := by
  decide +kernel

theorem f4Euclid_vE12 : f4Euclid vE12 = Pi.single 0 1 + Pi.single 1 1 := by
  decide +kernel

include hη hC h2 in
theorem liftsCommute_shortAcute_rep
    {u v : stdGroup} (hu : u ∈ relG vS1) (hv : v ∈ relG vS2) :
    LiftsCommute η u v := by
  have hra : IsRoot .F4 vL1 := isRoot_of_ofFn (by decide +kernel)
  have hrb : IsRoot .F4 vE2 := isRoot_of_ofFn (by decide +kernel)
  have hru : IsRoot .F4 vS1 := isRoot_of_ofFn (by decide +kernel)
  have hrv : IsRoot .F4 vS2 := isRoot_of_ofFn (by decide +kernel)
  have hrd : IsRoot .F4 vE12 := isRoot_of_ofFn (by decide +kernel)
  have hav := commute_of_relSupport_eq_empty hra hrv (by decide) (by decide)
    (relSupport_eq_empty hra hrv (by decide) (by decide) (by decide +kernel) (by decide +kernel))
  have hbv := commute_of_relSupport_eq_empty hrb hrv (by decide) (by decide)
    (relSupport_eq_empty hrb hrv (by decide) (by decide) (by decide +kernel) (by decide +kernel))
  have hdv := commute_of_relSupport_eq_empty hrd hrv (by decide) (by decide)
    (relSupport_eq_empty hrd hrv (by decide) (by decide) (by decide +kernel) (by decide +kernel))
  obtain ⟨x, hxR, hx1⟩ : ∃ x ∈ relRootGroup vL1, x ≠ 1 := by
    have hcard : Nat.card (relRootGroup vL1) = 2 := by
      have hl : f4Euclid vL1 ⬝ᵥ f4Euclid vL1 = 2 := by decide +kernel
      rw [card_relRootGroup hra, hl]
      simp
    have : Finite (relRootGroup vL1) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have : Nontrivial (relRootGroup vL1) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
    obtain ⟨⟨x, hx⟩, hne⟩ := exists_ne (1 : relRootGroup vL1)
    exact ⟨x, hx, fun h => hne (Subtype.ext h)⟩
  obtain ⟨φ, hφ⟩ := exists_tail_commutator_equiv_euclid (i := 0) (j := 1) (by decide) hra hrb
    f4Euclid_vL1 f4Euclid_vE2 f4Euclid_vS1 f4Euclid_vE12 hxR hx1
  intro x' z hx' hz
  set w₀ := φ.symm ⟨(u : ModGL Tag.E6 K), hu⟩ with hw₀
  have hφw : ((φ w₀ : relRootGroup vS1) : ModGL TwistTag.E6.tag K) = (u : ModGL Tag.E6 K) := by
    rw [hw₀, MulEquiv.apply_symm_apply]
  have hdd := hφ w₀
  set dd := ((φ w₀ : relRootGroup vS1) : ModGL TwistTag.E6.tag K)⁻¹ *
    ⁅x, (w₀ : ModGL TwistTag.E6.tag K)⁆ with hdddef
  set X : stdGroup := ⟨x, relRootGroup_le_stdGroup _ hxR⟩ with hX
  set W : stdGroup := ⟨(w₀ : ModGL TwistTag.E6.tag K), relRootGroup_le_stdGroup _ w₀.2⟩ with hW
  set Dg : stdGroup := ⟨dd, relRootGroup_le_stdGroup _ hdd⟩ with hDg
  obtain ⟨Xl, hXl⟩ := hη X
  obtain ⟨Wl, hWl⟩ := hη W
  obtain ⟨Dl, hDl⟩ := hη Dg
  set M := ⁅Xl, Wl⁆ * Dl⁻¹ with hMdef
  have hM : η M = u := by
    rw [hMdef, map_mul, map_inv, map_commutatorElement, hXl, hWl, hDl]
    apply Subtype.ext
    have key : ∀ c t : ModGL TwistTag.E6.tag K, c * (t⁻¹ * c)⁻¹ = t := fun c t => by group
    have e : (((⁅X, W⁆ * Dg⁻¹ : stdGroup) : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) =
        ⁅x, (w₀ : ModGL TwistTag.E6.tag K)⁆ * dd⁻¹ := rfl
    rw [e, hdddef, key, hφw]
  have hzX : η z * η Xl = η Xl * η z := by
    rw [hz, hXl]
    exact Subtype.ext (hav x hxR _ hv).symm
  have hzW : η z * η Wl = η Wl * η z := by
    rw [hz, hWl]
    exact Subtype.ext (hbv _ w₀.2 _ hv).symm
  have hcXW : z * ⁅Xl, Wl⁆ * z⁻¹ = ⁅Xl, Wl⁆ := by
    rw [conjugate_commutatorElement]
    refine commutatorElement_lift_eq hC ?_ ?_
    · rw [map_mul, map_mul, map_inv, hzX, mul_inv_cancel_right]
    · rw [map_mul, map_mul, map_inv, hzW, mul_inv_cancel_right]
  have hzD : Dl * z = z * Dl := liftsCommute_of_levi hη hC h2 hrd hrv
    (Or.inr (Or.inl (by decide +kernel))) hdv (u := Dg) (v := v) hdd hv Dl z hDl hz
  have hMz : M * z = z * M := by
    have h1 : z * ⁅Xl, Wl⁆ = ⁅Xl, Wl⁆ * z := by
      calc z * ⁅Xl, Wl⁆ = z * ⁅Xl, Wl⁆ * z⁻¹ * z := by group
        _ = ⁅Xl, Wl⁆ * z := by rw [hcXW]
    have h2' : z * Dl⁻¹ = Dl⁻¹ * z := by
      calc z * Dl⁻¹ = Dl⁻¹ * (Dl * z) * Dl⁻¹ := by group
        _ = Dl⁻¹ * (z * Dl) * Dl⁻¹ := by rw [hzD]
        _ = Dl⁻¹ * z := by group
    calc M * z = ⁅Xl, Wl⁆ * (Dl⁻¹ * z) := by rw [hMdef, mul_assoc]
      _ = ⁅Xl, Wl⁆ * (z * Dl⁻¹) := by rw [h2']
      _ = (⁅Xl, Wl⁆ * z) * Dl⁻¹ := by group
      _ = (z * ⁅Xl, Wl⁆) * Dl⁻¹ := by rw [h1]
      _ = z * M := by rw [hMdef, mul_assoc]
  have hc : M⁻¹ * x' ∈ center E :=
    hC (by rw [MonoidHom.mem_ker, map_mul, map_inv, hM, hx', inv_mul_cancel])
  have hcz := Subgroup.mem_center_iff.1 hc z
  calc x' * z = M * ((M⁻¹ * x') * z) := by group
    _ = M * (z * (M⁻¹ * x')) := by rw [hcz]
    _ = (M * z) * (M⁻¹ * x') := by group
    _ = (z * M) * (M⁻¹ * x') := by rw [hMz]
    _ = z * x' := by group

include hη hC h2 in
theorem liftsCommute_shortAcute
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r)
    (hs : IsRoot .F4 s) (hlr : f4Len r = 1) (hls : f4Len s = 1) (hip : f4Ip r s = 1 / 2)
    {u v : stdGroup} (hu : u ∈ relG r) (hv : v ∈ relG s) : LiftsCommute η u v := by
  have hru : IsRoot .F4 vS1 := isRoot_of_ofFn (by decide +kernel)
  have hrv : IsRoot .F4 vS2 := isRoot_of_ofFn (by decide +kernel)
  have hp := rootPair_of_ip hr hs (by rw [hip, hlr]; norm_num) (by rw [hip, hlr]; norm_num)
  have e1 : f4Len vS1 = 1 := by decide +kernel
  have e2 : f4Len vS2 = 1 := by decide +kernel
  have e3 : f4Ip vS1 vS2 = 1 / 2 := by decide +kernel
  obtain ⟨w, hwr, hws, w', hw', hn, hmap⟩ := exists_pair_conj hru hrv hr hs (by decide)
    (by decide) hp.2.2.1 hp.2.2.2 (e1.trans hlr.symm) (e2.trans hls.symm) (e3.trans hip.symm)
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K w' with hndef
  have hu' : ((u : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) ∈
      (relRootGroup vS1).map (MulAut.conj n).toMonoidHom := by
    rw [hmap, hwr]
    exact hu
  have hv' : ((v : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) ∈
      (relRootGroup vS2).map (MulAut.conj n).toMonoidHom := by
    rw [hmap, hws]
    exact hv
  obtain ⟨u₀, hu₀, hu₀u⟩ := hu'
  obtain ⟨v₀, hv₀, hv₀v⟩ := hv'
  set g : stdGroup := ⟨n, hn⟩ with hg
  have hueq : u = g * ⟨u₀, relRootGroup_le_stdGroup _ hu₀⟩ * g⁻¹ := Subtype.ext hu₀u.symm
  have hveq : v = g * ⟨v₀, relRootGroup_le_stdGroup _ hv₀⟩ * g⁻¹ := Subtype.ext hv₀v.symm
  rw [hueq, hveq]
  exact (liftsCommute_shortAcute_rep hη hC h2 hu₀ hv₀).conj hη g

end Lifts

theorem f4_short_ip_cases : ∀ k k' : Fin 48, f4Len (Tag.F4.rootCertificate.root k) = 1 →
    f4Len (Tag.F4.rootCertificate.root k') = 1 →
    Tag.F4.rootCertificate.root k ≠ Tag.F4.rootCertificate.root k' →
    Tag.F4.rootCertificate.root k ≠ -Tag.F4.rootCertificate.root k' →
    f4Ip (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') ∈
      ({-1 / 2, 0, 1 / 2} : Finset ℚ) := by
  decide +kernel

theorem short_ip_cases
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (hlr : f4Len r = 1) (hls : f4Len s = 1) (hne : r ≠ s) (hne' : r ≠ -s) :
    f4Ip r s = -1 / 2 ∨ f4Ip r s = 0 ∨ f4Ip r s = 1 / 2 := by
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.mp hr
  obtain ⟨k', rfl⟩ := isRoot_f4_iff.mp hs
  have h := f4_short_ip_cases k k' hlr hls hne hne'
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  exact h

section Commuting

variable
    {E : Type*} [Group E] [Finite E] {η : E →* stdGroup} (hη : Function.Surjective η)
  (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker)

include hη hC h2 in
theorem liftsCommute_of_relSupport_eq_empty
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r)
    (hs : IsRoot .F4 s) (hne : r ≠ s) (hne' : r ≠ -s) (h : relSupport r s = ∅) {u v : stdGroup}
    (hu : u ∈ relG r) (hv : v ∈ relG s) : LiftsCommute η u v := by
  have hcomm := commute_of_relSupport_eq_empty hr hs hne hne' h
  have hcases := relSupport_cases hr hs hne hne'
  rcases f4Len_of_isRoot hr with hlr | hlr <;> rcases f4Len_of_isRoot hs with hls | hls
  · rcases short_ip_cases hr hs hlr hls hne hne' with hip | hip | hip
    · exfalso
      have h1 := hcases.1 (Or.inl ⟨hlr.trans hls.symm, by
        change 2 * f4Ip r s = -f4Len r
        rw [hip, hlr]
        norm_num⟩)
      exact Set.singleton_ne_empty _ (h1.symm.trans h)
    · exfalso
      exact Set.singleton_ne_empty _ ((hcases.1 (Or.inr ⟨hlr, hls, hip⟩)).symm.trans h)
    · exact liftsCommute_shortAcute hη hC h2 hr hs hlr hls hip hu hv
  · exact liftsCommute_of_levi hη hC h2 hr hs (Or.inr (Or.inl (by rw [hlr, hls]; norm_num)))
      hcomm hu hv
  · exact liftsCommute_of_levi hη hC h2 hr hs (Or.inr (Or.inl (by rw [hlr, hls]; norm_num)))
      hcomm hu hv
  · exact liftsCommute_of_levi hη hC h2 hr hs (Or.inl ⟨hlr, hls⟩) hcomm hu hv

variable
    (y : (Fin Tag.F4.rank → ℤ) → stdGroup → E)
  (hy : ∀ r g, g ∈ relG r → η (y r g) = g) (hy2 : ∀ r g, g ∈ relG r → y r g * y r g = 1)

include hη hC h2 hy hy2 in
theorem exists_commutator_mixed
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (hβ : IsRoot .F4 β) (hlα : f4Len α = 2) (hlβ : f4Len β = 1) (hip : f4Ip α β = -1)
    {g h : stdGroup} (hg : g ∈ relG α) (hh : h ∈ relG β) :
    ∃ k₁ ∈ relG (α + β), ∃ k₂ ∈ relG (α + 2 • β),
      ⁅y α g, y β h⁆ * (y (α + β) k₁ * y (α + 2 • β) k₂)⁻¹ ∈ kerSq η hC := by
  have hp : RootPair α β := rootPair_of_len_ne hα hβ (by rw [hlα, hlβ]; norm_num)
  have hsupp := (relSupport_cases hα hβ hp.2.2.1 hp.2.2.2).2.1 ⟨hlα, hlβ, hip⟩
  have hr1 : IsRoot .F4 (α + β) := by
    have h1 : α + β ∈ relSupport α β := by rw [hsupp]; exact Or.inl rfl
    exact h1.1
  have hr2 : IsRoot .F4 (α + 2 • β) := by
    have h1 : α + 2 • β ∈ relSupport α β := by rw [hsupp]; exact Or.inr rfl
    exact h1.1
  have hαα : f4Ip α α = 2 := hlα
  have hββ : f4Ip β β = 1 := hlβ
  have hl1 : f4Len (α + β) = 1 := by
    rw [f4Len_add, hlα, hlβ, hip]
    norm_num
  have hl2 : f4Len (α + 2 • β) = 2 := by
    rw [f4Len_add, hlα, f4Ip_two_nsmul_right, hip, show f4Len (2 • β) = 4 * f4Len β by
      simp only [f4Len, f4Ip_two_nsmul_left, f4Ip_two_nsmul_right]
      change 2 * (2 * f4Ip β β) = 4 * f4Ip β β
      ring, hlβ]
    norm_num
  have hi1 : f4Ip α (α + β) = 1 := by
    rw [f4Ip_add_right, hip, hαα]
    norm_num
  have hi2 : f4Ip α (α + 2 • β) = 0 := by
    rw [f4Ip_add_right, f4Ip_two_nsmul_right, hip, hαα]
    norm_num
  have hi3 : f4Ip (α + β) (α + 2 • β) = 1 := by
    rw [f4Ip_add_left, f4Ip_add_right, f4Ip_add_right, f4Ip_two_nsmul_right,
      f4Ip_two_nsmul_right, hip, f4Ip_comm β α, hip, hαα, hββ]
    norm_num
  have hp1 : RootPair α (α + β) :=
    rootPair_of_ip hα hr1 (by rw [hi1, hlα]; norm_num) (by rw [hi1, hlα]; norm_num)
  have hp2 : RootPair α (α + 2 • β) :=
    rootPair_of_ip hα hr2 (by rw [hi2, hlα]; norm_num) (by rw [hi2, hlα]; norm_num)
  have hp3 : RootPair (α + β) (α + 2 • β) :=
    rootPair_of_len_ne hr1 hr2 (by rw [hl1, hl2]; norm_num)
  have he1 := relSupport_eq_empty hα hr1 hp1.2.2.1 hp1.2.2.2 (by rw [hi1]; norm_num)
    (by rintro ⟨h', -, -⟩; rw [hlα] at h'; norm_num at h')
  have he2 := relSupport_eq_empty hα hr2 hp2.2.2.1 hp2.2.2.2 (by rw [hi2])
    (by rintro ⟨h', -, -⟩; rw [hlα] at h'; norm_num at h')
  have he3 := relSupport_eq_empty hr1 hr2 hp3.2.2.1 hp3.2.2.2 (by rw [hi3]; norm_num)
    (by rintro ⟨-, h', -⟩; rw [hl2] at h'; norm_num at h')
  have hc := commutator_relRootGroup_le hα hβ hp.2.2.1 hp.2.2.2
    (Subgroup.commutator_mem_commutator hg hh)
  rw [hsupp, relSpan_pair] at hc
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := exists_mul_eq_of_mem_sup
    (le_normalizer_of_commute (commute_of_relSupport_eq_empty hr1 hr2 hp3.2.2.1 hp3.2.2.2 he3)) hc
  set K₁ : stdGroup := ⟨k₁, relRootGroup_le_stdGroup _ hk₁⟩ with hK₁
  set K₂ : stdGroup := ⟨k₂, relRootGroup_le_stdGroup _ hk₂⟩ with hK₂
  have hgh : ⁅g, h⁆ = K₁ * K₂ := Subtype.ext hk.symm
  refine ⟨K₁, hk₁, K₂, hk₂, ?_⟩
  exact commutatorElement_mul_inv_mem_kerSq_of_mul hC (hy α g hg) (hy β h hh) (hy _ K₁ hk₁)
    (hy _ K₂ hk₂) (hy2 α g hg) (hy2 _ K₁ hk₁) (hy2 _ K₂ hk₂) hgh
    (liftsCommute_of_relSupport_eq_empty hη hC h2 hα hr1 hp1.2.2.1 hp1.2.2.2 he1 hg hk₁)
    (liftsCommute_of_relSupport_eq_empty hη hC h2 hα hr2 hp2.2.2.1 hp2.2.2.2 he2 hg hk₂)
    (liftsCommute_of_relSupport_eq_empty hη hC h2 hr1 hr2 hp3.2.2.1 hp3.2.2.2 he3 hk₁ hk₂)

include hη hC h2 hy hy2 in
theorem exists_commutator_lift_mem
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β) {g h : stdGroup} (hg : g ∈ relG α)
    (hh : h ∈ relG β) :
    ∃ z ∈ Subgroup.closure {x | ∃ γ ∈ relSupport α β, ∃ k ∈ relG γ, y γ k = x},
      ⁅y α g, y β h⁆ * z⁻¹ ∈ kerSq η hC := by
  have hcases := relSupport_cases hα hβ hne hne'
  have hmem : ∀ {γ : Fin Tag.F4.rank → ℤ} {k : stdGroup}, γ ∈ relSupport α β → k ∈ relG γ →
      y γ k ∈ Subgroup.closure {x | ∃ γ ∈ relSupport α β, ∃ k ∈ relG γ, y γ k = x} :=
    fun hγ hk => Subgroup.subset_closure ⟨_, hγ, _, hk, rfl⟩
  by_cases c1 : (f4Euclid α ⬝ᵥ f4Euclid α = f4Euclid β ⬝ᵥ f4Euclid β ∧
        2 * (f4Euclid α ⬝ᵥ f4Euclid β) = -(f4Euclid α ⬝ᵥ f4Euclid α)) ∨
      (f4Euclid α ⬝ᵥ f4Euclid α = 1 ∧ f4Euclid β ⬝ᵥ f4Euclid β = 1 ∧
        f4Euclid α ⬝ᵥ f4Euclid β = 0)
  ·
    have hsupp := hcases.1 c1
    have hγ : α + β ∈ relSupport α β := by rw [hsupp]; rfl
    have hr1 : IsRoot .F4 (α + β) := hγ.1
    have hc := commutator_relRootGroup_le hα hβ hne hne'
      (Subgroup.commutator_mem_commutator hg hh)
    rw [hsupp, relSpan_singleton] at hc
    have hk : ⁅g, h⁆ ∈ relG (α + β) := hc
    have hpos := f4Len_pos hα
    have hip : 0 < f4Ip (α + β) α := by
      rw [f4Ip_add_left, f4Ip_comm β α]
      rcases c1 with ⟨-, h'⟩ | ⟨h', -, h''⟩
      · change 2 * f4Ip α β = -f4Len α at h'
        change 0 < f4Len α + f4Ip α β
        linarith
      · change 0 < f4Euclid α ⬝ᵥ f4Euclid α + f4Euclid α ⬝ᵥ f4Euclid β
        rw [h'', h']
        norm_num
    have hp1 : RootPair (α + β) α := by
      refine ⟨hr1, hα, fun e => ?_, fun e => ?_⟩
      · have : β = 0 := by
          have := congrArg (· - α) e
          simpa using this
        exact hβ.ne_zero this
      · have e' : f4Ip (α + β) α = -f4Len α := by
          rw [e]
          simp only [f4Ip, f4Len, f4Euclid_neg, neg_dotProduct]
        linarith
    have he := relSupport_eq_empty hr1 hα hp1.2.2.1 hp1.2.2.2 hip.le
      (by rintro ⟨-, -, h'⟩; linarith)
    exact ⟨y (α + β) ⁅g, h⁆, hmem hγ hk, commutatorElement_mul_inv_mem_kerSq hC (hy α g hg)
      (hy β h hh) (hy _ _ hk) (hy2 α g hg) (hy2 _ _ hk) rfl
      (liftsCommute_of_relSupport_eq_empty hη hC h2 hr1 hα hp1.2.2.1 hp1.2.2.2 he hk hg)⟩
  by_cases c2 : f4Euclid α ⬝ᵥ f4Euclid α = 2 ∧ f4Euclid β ⬝ᵥ f4Euclid β = 1 ∧
      f4Euclid α ⬝ᵥ f4Euclid β = -1
  ·
    have hsupp := hcases.2.1 c2
    obtain ⟨k₁, hk₁, k₂, hk₂, hrel⟩ :=
      exists_commutator_mixed hη hC h2 y hy hy2 hα hβ c2.1 c2.2.1 c2.2.2 hg hh
    exact ⟨_, mul_mem (hmem (by rw [hsupp]; exact Or.inl rfl) hk₁)
      (hmem (by rw [hsupp]; exact Or.inr rfl) hk₂), hrel⟩
  by_cases c3 : f4Euclid α ⬝ᵥ f4Euclid α = 1 ∧ f4Euclid β ⬝ᵥ f4Euclid β = 2 ∧
      f4Euclid α ⬝ᵥ f4Euclid β = -1
  ·
    have hsupp := hcases.2.2.1 c3
    obtain ⟨k₁, hk₁, k₂, hk₂, hrel⟩ := exists_commutator_mixed hη hC h2 y hy hy2 hβ hα c3.2.1
      c3.1 (by rw [f4Ip_comm]; exact c3.2.2) hh hg
    set w := y (β + α) k₁ * y (β + 2 • α) k₂ with hw
    have hwmem : w ∈ Subgroup.closure {x | ∃ γ ∈ relSupport α β, ∃ k ∈ relG γ, y γ k = x} :=
      mul_mem (hmem (by rw [hsupp]; exact Or.inl (add_comm β α)) hk₁)
        (hmem (by rw [hsupp]; exact Or.inr (add_comm β (2 • α))) hk₂)
    refine ⟨w⁻¹, inv_mem hwmem, ?_⟩
    have hcen : ⁅y β h, y α g⁆ * w⁻¹ ∈ center E := kerSq_le_center hC hrel
    have e2 := conj_eq_of_mem_center' (inv_mem hcen) w⁻¹
    have e : ⁅y α g, y β h⁆ * w⁻¹⁻¹ = (⁅y β h, y α g⁆ * w⁻¹)⁻¹ := by
      rw [← commutatorElement_inv]
      calc ⁅y β h, y α g⁆⁻¹ * w⁻¹⁻¹ = w⁻¹ * (⁅y β h, y α g⁆ * w⁻¹)⁻¹ * w⁻¹⁻¹ := by group
        _ = (⁅y β h, y α g⁆ * w⁻¹)⁻¹ := e2
    rw [e]
    exact inv_mem hrel
  ·
    have hsupp := hcases.2.2.2 c1 c2 c3
    have hcomm := commute_of_relSupport_eq_empty hα hβ hne hne' hsupp
    refine ⟨1, one_mem _, ?_⟩
    rw [inv_one, mul_one]
    exact commutatorElement_mem_kerSq_of_commute hC
      (by rw [hy α g hg, hy β h hh]; exact Subtype.ext (hcomm _ hg _ hh))
      (by rw [hy α g hg]; exact Subtype.ext ((relRootGroup_elementary hα).2 _ hg))

end Commuting

end CFSG.LieType.Chevalley.TwistedE6FieldTwoCover
