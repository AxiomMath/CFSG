module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step47Img
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Cert
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Tab
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step46
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Chain

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic HeSylow Q47 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native
open Matrix
open scoped MatrixGroups

namespace Q47

theorem perm_inv_apply_self (f : Equiv.Perm (Fin 64)) (x : Fin 64) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem perm_apply_inv_self (f : Equiv.Perm (Fin 64)) (x : Fin 64) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem q47Check_parts (h : q47Check = true) :
    transCheckO = true ∧ nondegCheck = true ∧ refCheck = true ∧ tableCheck = true := by
  simp only [q47Check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

theorem modelFacts16 :
    ModelFacts 16 heSyl16 heSylQ16 heSylE16 heSylF16 heSylZ16 q47Rep16 heSyl16 q47D16 q47Eb16
      q47Fb16 q47KE16 q47KF16 q47C16 := by
  have h := q47_check
  simp only [q47Check, Bool.and_eq_true] at h
  obtain ⟨hX, hQ, hE, hF, -, hvz, -⟩ := sylCheck16_parts (sylCheck16_of he_sylowCheck)
  exact modelFacts_of h.1.1.1.1.1 h.1.1.1.2 hX hQ hE hF hvz h.1.2

theorem modelFacts32 :
    ModelFacts 32 GrSLit.HeldFix.hfT0Tabs32.toList heAutQ32 heAutE32 heAutF32 heAutZ32 q47Rep32
      q47NE32 q47D32 q47Eb32 q47Fb32 q47KE32 q47KF32 q47C32 := by
  have h := q47_check
  simp only [q47Check, Bool.and_eq_true] at h
  obtain ⟨hX, hQ, hE, hF, -, hvz, -⟩ := heAutSylowCheck_parts he_autSylowCheck
  exact modelFacts_of h.1.1.1.1.1 h.1.1.1.2 hX hQ hE hF hvz h.2

theorem trans_wOne (hq : refCheck = true) : ∀ a ∈ wOne, a ≠ 0 → ∀ b ∈ wOne, b ≠ 0 →
    ∃ σ ∈ ystar, σ a = b := by
  intro a ha ha0 b hb hb0
  obtain ⟨σ₁, h₁, e₁⟩ := exists_ystar_wOne hq ha ha0
  obtain ⟨σ₂, h₂, e₂⟩ := exists_ystar_wOne hq hb hb0
  refine ⟨σ₂ * σ₁⁻¹, mul_mem h₂ (inv_mem h₁), ?_⟩
  rw [Equiv.Perm.mul_apply, ← e₁, perm_inv_apply_self, e₂]

theorem trans_wTwo (hq : refCheck = true) : ∀ a ∈ wTwo, a ≠ 0 → ∀ b ∈ wTwo, b ≠ 0 →
    ∃ σ ∈ ystar, σ a = b := by
  intro a ha ha0 b hb hb0
  obtain ⟨σ₁, h₁, e₁⟩ := exists_ystar_wTwo hq ha ha0
  obtain ⟨σ₂, h₂, e₂⟩ := exists_ystar_wTwo hq hb hb0
  refine ⟨σ₂ * σ₁⁻¹, mul_mem h₂ (inv_mem h₁), ?_⟩
  rw [Equiv.Perm.mul_apply, ← e₁, perm_inv_apply_self, e₂]

theorem exists_xr_wOne_wTwo (hq : refCheck = true) (v : Fin 64) :
    ∃ a ∈ wOne, ∃ b ∈ wTwo, xr a b = v := by
  have hW1 := tSub_wOne hq
  have hW2 := tSub_wTwo hq
  let φ : ↥wOne × ↥wTwo → Fin 64 := fun p => xr p.1 p.2
  have hinj : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h' : xr a b = xr a' b' := h
    have e : xr a a' = xr b b' := Fin.ext (by
      have h'' := congrArg Fin.val h'
      simp only [xr_val] at h'' ⊢
      have e1 : a.val ^^^ a'.val = (a.val ^^^ b.val) ^^^ (b.val ^^^ a'.val) := by
        rw [Nat.xor_assoc, ← Nat.xor_assoc b.val b.val a'.val, Nat.xor_self, Nat.zero_xor]
      rw [e1, h'', Nat.xor_comm b.val a'.val, ← Nat.xor_assoc, Nat.xor_assoc a'.val,
        Nat.xor_comm b'.val a'.val, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_comm])
    have h1 : xr a a' ∈ wOne := hW1.xr_mem _ ha _ ha'
    have h2 : xr a a' ∈ wTwo := e ▸ hW2.xr_mem _ hb _ hb'
    have h0 := eq_zero_of_mem_both hq h1 h2
    have haa : a = a' := by rw [← xr_xr_cancel a a', h0, xr_comm, xr_zero]
    have hbb : b = b' := by rw [← xr_xr_cancel b b', ← e, h0, xr_comm, xr_zero]
    subst haa
    subst hbb
    rfl
  have hcard : Nat.card (Fin 64) ≤ Nat.card (↥wOne × ↥wTwo) := by
    rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq, ncard_ptSet hW1.eight,
      ncard_ptSet hW2.eight]
    simp
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩ := (hinj.bijective_of_nat_card_le hcard).2 v
  exact ⟨a, ha, b, hb, hab⟩

theorem exists_hom_of_range {H M : Type*} [Group H] [Group M]
    {K : Subgroup (Equiv.Perm (Fin 64))} (e : ↥K ≃* M) (α : H →* Equiv.Perm (Fin 64))
    (hα : α.range = K) : ∃ φ : H →* M, Function.Surjective φ ∧ φ.ker = α.ker := by
  have hmem : ∀ x, α x ∈ K := fun x => hα ▸ ⟨x, rfl⟩
  refine ⟨e.toMonoidHom.comp (α.codRestrict K hmem), fun m => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective m
    have hy : (y : Equiv.Perm (Fin 64)) ∈ α.range := hα.symm ▸ y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    exact Subtype.ext hx
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    exact Subtype.ext_iff

theorem map_conj_map_conj_inv (K : Subgroup (Equiv.Perm (Fin 64))) (c₀ : Equiv.Perm (Fin 64)) :
    (K.map (MulAut.conj c₀).toMonoidHom).map (MulAut.conj c₀⁻¹).toMonoidHom = K := by
  rw [Subgroup.map_map]
  have e : (MulAut.conj c₀⁻¹).toMonoidHom.comp (MulAut.conj c₀).toMonoidHom =
      MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [e, Subgroup.map_id]

theorem ker_conj_comp {H : Type*} [Group H] (α : H →* Equiv.Perm (Fin 64))
    (c₀ : Equiv.Perm (Fin 64)) : ((MulAut.conj c₀⁻¹).toMonoidHom.comp α).ker = α.ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem isSubsp_image {c₀ : Equiv.Perm (Fin 64)} (hc₀ : c₀ ∈ oV) {Wa : Array ℕ} (hW : TSub Wa) :
    VCode.IsSubsp (⇑c₀ '' ptSet Wa) where
  zero := ⟨0, hW.zero, (mem_oV.mp hc₀).map_zero⟩
  xr_mem := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨xr a b, hW.xr_mem a ha b hb, (mem_oV.mp hc₀).1 a b⟩

end Q47

section Preim

variable {G : Type} [Group G] [Finite G]

theorem preim_facts {Q Y : Subgroup G} {z : G} {c : VCode Q z}
    {hs : VCode.Std Q z} (hYN : Y ≤ normalizer (Q : Set G)) {c₀ : Equiv.Perm (Fin 64)}
    (hc₀ : c₀ ∈ oV) (hYimg : c.img hs Y = ystar.map (MulAut.conj c₀).toMonoidHom)
    {Wa : Array ℕ} (hW : TSub Wa) (hstab : ystar ≤ setStab (ptSet Wa))
    (htr : ∀ a ∈ ptSet Wa, a ≠ 0 → ∀ b ∈ ptSet Wa, b ≠ 0 → ∃ σ ∈ ystar, σ a = b) :
    c.preim hs (isSubsp_image hc₀ hW) ≤ Q ∧
      IsElemAbelian 2 (c.preim hs (isSubsp_image hc₀ hW)) ∧
      Nat.card (c.preim hs (isSubsp_image hc₀ hW)) = 16 ∧
      Y ≤ normalizer (c.preim hs (isSubsp_image hc₀ hW) : Set G) ∧
      ∀ W : Subgroup G, zpowers z ≤ W → W ≤ c.preim hs (isSubsp_image hc₀ hW) →
        Y ≤ normalizer (W : Set G) → W = zpowers z ∨ W = c.preim hs (isSubsp_image hc₀ hW) := by
  have hiso := mem_oV.mp hc₀
  have hact : ∀ y (hy : y ∈ Y), ∃ σ ∈ ystar, ∀ a, c.rho hs ⟨y, hYN hy⟩ (c₀ a) = c₀ (σ a) := by
    intro y hy
    have hmem : c.rho hs ⟨y, hYN hy⟩ ∈ ystar.map (MulAut.conj c₀).toMonoidHom :=
      hYimg ▸ VCode.mem_img_of_mem hy (hYN hy)
    obtain ⟨σ, hσ, he⟩ := hmem
    refine ⟨σ, hσ, fun a => ?_⟩
    rw [← he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Equiv.Perm.mul_apply,
      perm_inv_apply_self]
  refine ⟨VCode.preim_le hs _, VCode.isElemAbelian_preim hs _ ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hiso.2]
    exact hW.sing a ha
  · rw [VCode.card_preim hs, Set.ncard_image_of_injective _ c₀.injective, ncard_ptSet hW.eight]
  · intro y hy
    obtain ⟨σ, hσ, he⟩ := hact y hy
    refine VCode.mem_normalizer_preim hs _ ⟨y, hYN hy⟩ ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [he]
    refine ⟨σ a, ?_, rfl⟩
    have h1 := mem_setStab.mp (hstab hσ)
    rw [← h1]
    exact ⟨a, ha, rfl⟩
  · intro W hzW hWV hYW
    by_cases hall : ∀ x ∈ W, x ∈ zpowers z
    · exact Or.inl (le_antisymm hall hzW)
    · right
      push Not at hall
      obtain ⟨x, hxW, hxz⟩ := hall
      have hxV := hWV hxW
      obtain ⟨a, ha, hax⟩ := hxV.2
      have ha0 : a ≠ 0 := by
        rintro rfl
        apply hxz
        rw [← VCode.code_eq_zero_iff hs hxV.1, ← hax, hiso.map_zero]
      refine le_antisymm hWV (fun y hyV => ?_)
      obtain ⟨b, hb, hby⟩ := hyV.2
      by_cases hb0 : b = 0
      · subst hb0
        exact hzW ((VCode.code_eq_zero_iff hs hyV.1).1 (by rw [← hby, hiso.map_zero]))
      · obtain ⟨σ, hσ, hσab⟩ := htr a ha ha0 b hb hb0
        have hmem : (MulAut.conj c₀).toMonoidHom σ ∈ c.img hs Y := hYimg ▸ ⟨σ, hσ, rfl⟩
        obtain ⟨m, hmY, hme⟩ := hmem
        have hmW : (m : G) * x * (m : G)⁻¹ ∈ W :=
          (mem_normalizer_iff.mp (hYW (mem_subgroupOf.mp hmY)) x).mp hxW
        refine VCode.mem_of_code_eq (c := c) hs hzW hyV.1 hmW (VCode.conj_mem_Q m.2 hxV.1) ?_
        rw [VCode.code_conj hs m.2 hxV.1, ← VCode.rho_apply (hs := hs), hme, ← hax, ← hby]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Equiv.Perm.mul_apply,
          perm_inv_apply_self, hσab]

end Preim

section Img

variable {G : Type} [Group G] [Finite G]

theorem ystar_le_range_le_nstar (hT : transCheckO = true) (hq : refCheck = true)
    {Q Y : Subgroup G} {z : G} (c : VCode Q z) (hs : VCode.Std Q z) {c₀ : Equiv.Perm (Fin 64)}
    (hc₀ : c₀ ∈ oV) (hYimg : c.img hs Y = ystar.map (MulAut.conj c₀).toMonoidHom)
    (h12 : ¬ 2 ^ 12 ∣ Nat.card (normalizer (Q : Set G))) :
    ystar ≤ ((MulAut.conj c₀⁻¹).toMonoidHom.comp (c.rho hs)).range ∧
      ((MulAut.conj c₀⁻¹).toMonoidHom.comp (c.rho hs)).range ≤ nstar := by
  set α := (MulAut.conj c₀⁻¹).toMonoidHom.comp (c.rho hs) with hα
  have hHO : α.range ≤ oV := by
    rintro _ ⟨x, rfl⟩
    simp only [hα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hc₀) (VCode.rho_mem_oV hs x)) hc₀
  have hYH : ystar ≤ α.range := by
    intro σ hσ
    have hmem : (MulAut.conj c₀).toMonoidHom σ ∈ c.img hs Y := hYimg ▸ ⟨σ, hσ, rfl⟩
    obtain ⟨m, -, hme⟩ := hmem
    refine ⟨m, ?_⟩
    simp only [hα, MonoidHom.comp_apply, hme, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h32 : ¬ 32 ∣ Nat.card α.range := by
    intro h32
    have hc := card_eq_card_ker_mul α.rangeRestrict α.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict] at hc
    have hQk : Q.subgroupOf (normalizer (Q : Set G)) ≤ α.ker := fun x hx => by
      have h1 : c.rho hs x = 1 := VCode.rho_eq_one_of_mem hs x (mem_sup_left hx)
      rw [MonoidHom.mem_ker, hα, MonoidHom.comp_apply, h1, map_one]
    have h128 : 128 ∣ Nat.card α.ker := by
      have := Subgroup.card_dvd_of_le hQk
      rwa [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, hs.card] at this
    apply h12
    rw [hc, show 2 ^ 12 = 128 * 32 by norm_num]
    exact Nat.mul_dvd_mul h128 h32
  exact ⟨hYH, le_nstar_of_le hT hq hHO hYH h32⟩

theorem step47_of_img (hT : transCheckO = true) (hq : refCheck = true) (hb : tableCheck = true)
    (hnd : nondegCheck = true) {Q Y : Subgroup G} {z : G} (c : VCode Q z) (hs : VCode.Std Q z)
    (hcent : centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)))
    (hQY : Q ≤ Y) (hYN : Y ≤ normalizer (Q : Set G)) {c₀ : Equiv.Perm (Fin 64)} (hc₀ : c₀ ∈ oV)
    (hYimg : c.img hs Y = ystar.map (MulAut.conj c₀).toMonoidHom)
    (h12 : ¬ 2 ^ 12 ∣ Nat.card (normalizer (Q : Set G))) :
    (Q ≤ Y ∧ ∃ φ : ↥Y →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf Y) ∧
      (∃ V₁ V₂ : Subgroup G, V₁ ≤ Q ∧ V₂ ≤ Q ∧ IsElemAbelian 2 V₁ ∧ IsElemAbelian 2 V₂ ∧
        Nat.card V₁ = 16 ∧ Nat.card V₂ = 16 ∧ V₁ ⊓ V₂ = zpowers z ∧ V₁ ⊔ V₂ = Q ∧
        Y ≤ normalizer (V₁ : Set G) ∧ Y ≤ normalizer (V₂ : Set G) ∧
        ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)), ∀ W : Subgroup G, zpowers z ≤ W → W ≤ V →
          Y ≤ normalizer (W : Set G) → W = zpowers z ∨ W = V) ∧
      ((∃ φ : ↥(normalizer (Q : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
          φ.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf
            (normalizer (Q : Set G))) ∨
        ∃ φ : ↥(normalizer (Q : Set G)) →* ProjGenLinGroup (Fin 2) (ZMod 7),
          Function.Surjective φ ∧
          φ.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf
            (normalizer (Q : Set G))) := by
  refine ⟨⟨hQY, ?_⟩, ?_, ?_⟩
  ·
    set α := (MulAut.conj c₀⁻¹).toMonoidHom.comp ((c.rho hs).comp (inclusion hYN)) with hα
    have hrange : α.range = ystar := by
      rw [hα, MonoidHom.range_comp, VCode.range_comp_inclusion, hYimg, map_conj_map_conj_inv]
    obtain ⟨φ, hφ, hker⟩ := exists_hom_of_range (ystarEquiv hq hb) α hrange
    refine ⟨φ, hφ, ?_⟩
    rw [hker, hα, ker_conj_comp]
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mem_subgroupOf]
    exact VCode.rho_eq_one_iff hs hnd hcent _
  ·
    have hW1 := tSub_wOne hq
    have hW2 := tSub_wTwo hq
    obtain ⟨h1Q, h1e, h1c, h1N, h1irr⟩ := preim_facts hYN hc₀ hYimg hW1
      ((ystar_le_setStab hq).trans inf_le_left) (trans_wOne hq)
    obtain ⟨h2Q, h2e, h2c, h2N, h2irr⟩ := preim_facts hYN hc₀ hYimg hW2
      ((ystar_le_setStab hq).trans inf_le_right) (trans_wTwo hq)
    refine ⟨_, _, h1Q, h2Q, h1e, h2e, h1c, h2c, VCode.preim_inf hs _ _ ?_,
      VCode.preim_sup hs _ _ ?_, h1N, h2N, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hba : b = a := c₀.injective hab
      subst hba
      rw [eq_zero_of_mem_both hq ha hb]
      exact (mem_oV.mp hc₀).map_zero
    · intro v
      obtain ⟨a, ha, b, hb, hab⟩ := exists_xr_wOne_wTwo hq (c₀⁻¹ v)
      refine ⟨c₀ a, ⟨a, ha, rfl⟩, c₀ b, ⟨b, hb, rfl⟩, ?_⟩
      rw [← (mem_oV.mp hc₀).1, hab, perm_apply_inv_self]
    · intro V hV W hzW hWV hYW
      rcases hV with rfl | hV
      · exact h1irr W hzW hWV hYW
      · rw [Set.mem_singleton_iff] at hV
        subst hV
        exact h2irr W hzW hWV hYW
  ·
    obtain ⟨hYH, hHN⟩ := ystar_le_range_le_nstar hT hq c hs hc₀ hYimg h12
    set α := (MulAut.conj c₀⁻¹).toMonoidHom.comp (c.rho hs) with hα
    have hker : α.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf
        (normalizer (Q : Set G)) := by
      rw [hα, ker_conj_comp, VCode.ker_rho hs hnd hcent]
    have hd1 := Subgroup.card_dvd_of_le hHN
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hYH
    rw [card_nstar hq] at hd1
    rw [card_ystar hq] at hm
    have hle := Nat.le_of_dvd (by norm_num) hd1
    have hpos : 0 < Nat.card α.range := Nat.card_pos
    have hm2 : m = 1 ∨ m = 2 := by omega
    rcases hm2 with rfl | rfl
    · left
      have hr : α.range = ystar :=
        (Subgroup.eq_of_le_of_card_ge hYH (by rw [hm, card_ystar hq])).symm
      obtain ⟨φ, hφ, hk⟩ := exists_hom_of_range (ystarEquiv hq hb) α hr
      exact ⟨φ, hφ, hk.trans hker⟩
    · right
      have hr : α.range = nstar :=
        Subgroup.eq_of_le_of_card_ge hHN (by rw [hm, card_nstar hq])
      obtain ⟨φ, hφ, hk⟩ := exists_hom_of_range (nstarEquiv hq hb) α hr
      exact ⟨φ, hφ, hk.trans hker⟩

end Img

section Setting

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem std_of_sec4Q (hQ : Sec4Q G A R g E F S₁ Q z) : VCode.Std Q z where
  z_mem := hQ.z_mem_Q
  z_comm x hx := mem_centralizer_iff.mp hQ.z_mem_centerIn_Q.2 x hx
  z_sq := by rw [← pow_two, ← hQ.order_z, pow_orderOf_eq_one]
  z_ne := hQ.z_ne_one
  card := by rw [hQ.card]; norm_num
  comm x hx y hy := hQ.commutator_mem hx hy
  norm_cent := hQ.normalizer_le_centralizer

theorem le_normalizer_of_uniq (hQ : Sec4Q G A R g E F S₁ Q z)
    (huniq : ∀ Q' : Subgroup G, Q' ≤ S₁ → Nat.card Q' = 2 ^ 7 → (∀ x ∈ Q', x ^ 2 ∈ zpowers z) →
      (∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → Q' = Q) :
    S₁ ≤ normalizer (Q : Set G) := by
  intro s hs
  have hsC : s ∈ centralizer ({z} : Set G) := hQ.le_centralizer hs
  have hS : Q.map (MulAut.conj s).toMonoidHom ≤ S₁ := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact S₁.mul_mem (S₁.mul_mem hs (hQ.le hq)) (S₁.inv_mem hs)
  have hcard : Nat.card (Q.map (MulAut.conj s).toMonoidHom) = 2 ^ 7 := by
    rw [card_map_of_injective (MulAut.conj s).injective, hQ.card]
  have heq := huniq _ hS hcard (by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow]
    exact conj_mem_zpowers hsC (sq_mem_zpowers_of_sec4Q hQ hq)) (by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h := conj_mem_zpowers hsC (hQ.commutator_mem hq hv)
    convert h using 1
    group)
  exact mem_normalizer_iff_map_conj_eq.mpr heq

theorem centralizer_le_sup (hQ : Sec4Q G A R g E F S₁ Q z) (hS₁N : S₁ ≤ normalizer (Q : Set G))
    (hcS : ∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z) :
    centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : centralizer (Q : Set G) ≤ normalizer (Q : Set G) := centralizer_le_normalizer _
  have hNC : normalizer (Q : Set G) ≤ normalizer (centralizer (Q : Set G) : Set G) := by
    intro n hn
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : n⁻¹ * q * n ∈ Q := by
      have := (mem_normalizer_iff.mp (inv_mem hn) q).mp hq
      simpa using this
    have hc := mem_centralizer_iff.mp hx _ hq'
    calc q * (n * x * n⁻¹) = n * ((n⁻¹ * q * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * q * n)) * n⁻¹ := by rw [hc]
      _ = n * x * n⁻¹ * q := by group
  have hS : IsSylowOf 2 S₁ (normalizer (Q : Set G)) := hQ.sylow.of_le hS₁N le_top
  have hSC := hS.inf_of_le_normalizer hCN hNC
  have hzS : z ∈ S₁ := hQ.le hQ.z_mem_Q
  have hzC : zpowers z ≤ centralizer (Q : Set G) := zpowers_le.mpr hQ.z_mem_centerIn_Q.2
  have hSz : S₁ ⊓ centralizer (Q : Set G) = zpowers z :=
    le_antisymm (fun x hx => hcS x hx.1 fun y hy => (mem_centralizer_iff.mp hx.2 y hy).symm)
      (le_inf (zpowers_le.mpr hzS) hzC)
  rw [hSz] at hSC
  have hodd : Odd ((zpowers z).relIndex (centralizer (Q : Set G))) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (isSylowOf_iff.mp hSC).2.2)
  have hzcC : zpowers z ≤ centralizer (centralizer (Q : Set G) : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.mp hx z hQ.z_mem_Q).symm
  have heq := eq_sup_oddCoreIn_of_central hSC.isPGroup hzC hzcC hodd
  have hOC : AS76b.oddCoreIn (centralizer (Q : Set G)) ≤
      AS76b.oddCoreIn (normalizer (Q : Set G)) :=
    Asc76.Sec5.le_oddCoreIn ((AS76b.oddCoreIn_le _).trans hCN)
      (fun n hn => AS76b.normalizer_le_normalizer_oddCoreIn _ (hNC hn))
      (AS76b.odd_card_oddCoreIn _)
  rw [heq]
  exact sup_le_sup (zpowers_le.mpr hQ.z_mem_Q) hOC

theorem not_dvd_card_normalizer (hQ : Sec4Q G A R g E F S₁ Q z) :
    ¬ 2 ^ 12 ∣ Nat.card (normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁card : Nat.card S₁ ≤ 2 ^ 11 := by
    rcases hQ.quot with ⟨φ, hφ, hker⟩ | ⟨φ, hφ, hker⟩ <;>
      rw [card_eq_card_ker_mul φ hφ, hker, Nat.card_congr (subgroupOfEquivOfLe hQ.le).toEquiv,
        hQ.card, DihedralGroup.nat_card] <;> norm_num
  intro h
  have h1 : 2 ^ 12 ∣ Nat.card G := h.trans (Subgroup.card_subgroup_dvd_card _)
  have h2 := hQ.sylow.card_eq
  rw [card_top] at h2
  have h3 : 12 ≤ (Nat.card G).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
  have h4 : 2 ^ 12 ≤ Nat.card S₁ := by
    rw [h2]
    exact Nat.pow_le_pow_right (by norm_num) h3
  omega

end Setting

section OfModel

variable {G : Type} [Group G] {Q : Subgroup G} {z : G} {n : ℕ}
  {Xm : Subgroup (Equiv.Perm (Fin n))} {Qg reps : List (Array ℕ)} {zg : Array ℕ}

@[expose] noncomputable def VCode.ofModel (fN : ↥Xm →* ↥(normalizer (Q : Set G)))
    (hf : Function.Injective ((normalizer (Q : Set G)).subtype.comp fN))
    (hR : RepFacts n Qg reps zg) (hQX : grpN n Qg ≤ Xm)
    (hQQ : trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Qg) = Q)
    (hzX : permOfArr n zg ∈ Xm) (hzf : z = (fN ⟨permOfArr n zg, hzX⟩ : G)) : VCode Q z where
  rep v := (fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G)
  rep_mem v := by
    have h := (apply_mem_trS_iff (x := ⟨repV n reps v, hQX (hR.mem v)⟩) hf).mpr (hR.mem v)
    rw [hQQ] at h
    exact h
  rep_zero := by
    have e : (⟨repV n reps 0, hQX (hR.mem 0)⟩ : ↥Xm) = 1 := Subtype.ext hR.zero
    show (fN ⟨repV n reps 0, hQX (hR.mem 0)⟩ : G) = 1
    rw [e, map_one]
    rfl
  rep_mul u v := by
    show (fN ⟨repV n reps u, hQX (hR.mem u)⟩ : G) * (fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G) =
        (fN ⟨repV n reps (xr u v), hQX (hR.mem _)⟩ : G) ∨
      (fN ⟨repV n reps u, hQX (hR.mem u)⟩ : G) * (fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G) =
        (fN ⟨repV n reps (xr u v), hQX (hR.mem _)⟩ : G) * z
    rw [← Subgroup.coe_mul, ← map_mul]
    rcases hR.mul u v with h | h
    · left
      have e : (⟨repV n reps u, hQX (hR.mem u)⟩ : ↥Xm) * ⟨repV n reps v, hQX (hR.mem v)⟩ =
          ⟨repV n reps (xr u v), hQX (hR.mem _)⟩ := Subtype.ext h
      rw [e]
    · right
      have e : (⟨repV n reps u, hQX (hR.mem u)⟩ : ↥Xm) * ⟨repV n reps v, hQX (hR.mem v)⟩ =
          ⟨repV n reps (xr u v), hQX (hR.mem _)⟩ * ⟨permOfArr n zg, hzX⟩ := Subtype.ext h
      rw [e, map_mul, Subgroup.coe_mul, ← hzf]
  cover x hx := by
    rw [← hQQ] at hx
    obtain ⟨y, hy, rfl⟩ := mem_trS.mp hx
    obtain ⟨v, hv | hv⟩ := hR.cover y hy
    · refine ⟨v, Or.inl ?_⟩
      show (fN y : G) = (fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G)
      rw [show y = ⟨repV n reps v, hQX (hR.mem v)⟩ from Subtype.ext hv]
    · refine ⟨v, Or.inr ?_⟩
      show (fN y : G) = (fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G) * z
      rw [hzf, ← Subgroup.coe_mul, ← map_mul,
        show y = ⟨repV n reps v, hQX (hR.mem v)⟩ * ⟨permOfArr n zg, hzX⟩ from Subtype.ext hv]
  sq v := by
    show ((fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G) * (fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G) =
        1 ∧ qv v = 0) ∨
      ((fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G) * (fN ⟨repV n reps v, hQX (hR.mem v)⟩ : G) =
        z ∧ qv v = 1)
    rw [← Subgroup.coe_mul, ← map_mul]
    rcases hR.sq v with ⟨h, hq⟩ | ⟨h, hq⟩
    · refine Or.inl ⟨?_, hq⟩
      have e : (⟨repV n reps v, hQX (hR.mem v)⟩ : ↥Xm) * ⟨repV n reps v, hQX (hR.mem v)⟩ = 1 :=
        Subtype.ext h
      rw [e, map_one]
      rfl
    · refine Or.inr ⟨?_, hq⟩
      have e : (⟨repV n reps v, hQX (hR.mem v)⟩ : ↥Xm) * ⟨repV n reps v, hQX (hR.mem v)⟩ =
          ⟨permOfArr n zg, hzX⟩ := Subtype.ext h
      rw [e, ← hzf]

theorem exists_fN {S₁ : Subgroup G} (hS₁N : S₁ ≤ normalizer (Q : Set G)) (θ : ↥Xm ≃* ↥S₁) :
    ∃ fN : ↥Xm →* ↥(normalizer (Q : Set G)),
      Function.Injective ((normalizer (Q : Set G)).subtype.comp fN) ∧
      ((normalizer (Q : Set G)).subtype.comp fN).range = S₁ := by
  refine ⟨(S₁.subtype.comp θ.toMonoidHom).codRestrict _ fun x => hS₁N (θ x).2,
    fun a b h => θ.injective (Subtype.ext h), ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (θ x).2
  · intro hy
    refine ⟨θ.symm ⟨y, hy⟩, ?_⟩
    show ((θ (θ.symm ⟨y, hy⟩) : ↥S₁) : G) = y
    rw [MulEquiv.apply_symm_apply]

end OfModel

section Proof

variable {G : Type} [Group G] [Finite G]

theorem trS_le_normalizer {H : Type} [Group H] {X : Subgroup H} {f : ↥X →* G}
    (hf : Function.Injective f) {K L : Subgroup H} (hKL : K ≤ normalizer (L : Set H)) :
    trS f K ≤ normalizer (trS f L : Set G) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_trS.mp hy
  refine mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨u, hu, rfl⟩ := mem_trS.mp hw
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← map_inv, ← map_mul, ← map_mul, apply_mem_trS_iff hf]
  exact (mem_normalizer_iff.mp (hKL hx) u).mp hu

theorem exists_idx_of {KE KF : List (List (Array ℕ))} {A B : Subgroup (Equiv.Perm (Fin 64))}
    (hA : A = grpN 64 KE[0]! ∨ A = grpN 64 KE[1]!) (hB : B = grpN 64 KF[0]! ∨ B = grpN 64 KF[1]!) :
    ∃ i < 2, ∃ j < 2, A ⊔ B = grpN 64 (KE[i]! ++ KF[j]!) := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact ⟨0, by norm_num, 0, by norm_num, (grpN_append _ _ _).symm⟩
  · exact ⟨0, by norm_num, 1, by norm_num, (grpN_append _ _ _).symm⟩
  · exact ⟨1, by norm_num, 0, by norm_num, (grpN_append _ _ _).symm⟩
  · exact ⟨1, by norm_num, 1, by norm_num, (grpN_append _ _ _).symm⟩

theorem transport_QZ {n : ℕ} {Xg Qg Eg Fg : List (Array ℕ)} {zg : Array ℕ}
    {U : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    (hm : SylModel (grpN n Xg) (grpN n Qg) (grpN n Eg) (grpN n Fg) U (permOfArr n zg) k)
    {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G} {z : G} (hQ : Sec4Q G A R g E F S₁ Q z)
    (fN : ↥(grpN n Xg) →* ↥(normalizer (Q : Set G)))
    (hf : Function.Injective ((normalizer (Q : Set G)).subtype.comp fN))
    (hfr : ((normalizer (Q : Set G)).subtype.comp fN).range = S₁) :
    trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Qg) = Q ∧
      z = (fN ⟨permOfArr n zg, hm.z_mem⟩ : G) ∧
      ((E = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Eg) ∧
          F = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Fg)) ∨
        (E = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Fg) ∧
          F = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Eg))) := by
  have hset := hQ.setting
  have hmf := hm.map _ hf
  rw [hfr] at hmf
  refine ⟨hQ.unique _ hmf.QX hmf.extraspecial hmf.cardQ (by rw [hmf.center_Q, hmf.center_X]),
    ?_, ?_⟩
  · have hz : z ∈
        zpowers (((normalizer (Q : Set G)).subtype.comp fN) ⟨permOfArr n zg, hm.z_mem⟩) := by
      rw [← hmf.center_X, hQ.center_S₁]
      exact mem_zpowers z
    rcases eq_one_or_eq_of_mem_zpowers hmf.order_z hz with h | h
    · exact absurd h hQ.z_ne_one
    · exact h
  · have hEF := sup_le_of_isSylowOf_normalizer hset hQ.sylowN
    have hE := hmf.uniqE E (le_sup_left.trans hEF) hset.frame.elemE
      (by rw [hset.frame.cardE]; norm_num)
    have hF := hmf.uniqE F (le_sup_right.trans hEF) hset.frame.elemF
      (by rw [hset.frame.cardF]; norm_num)
    rcases hE with hE | hE <;> rcases hF with hF | hF
    · exact absurd (hE.trans hF.symm) hset.frame.ne
    · exact Or.inl ⟨hE, hF⟩
    · exact Or.inr ⟨hE, hF⟩
    · exact absurd (hE.trans hF.symm) hset.frame.ne

theorem img_Y_eq (hnd : nondegCheck = true) {n : ℕ} {Xg Qg Eg Fg : List (Array ℕ)}
    {zg : Array ℕ} {reps NE D Eb Fb : List (Array ℕ)} {KE KF : List (List (Array ℕ))}
    {C : List (Array ℕ)} {U : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    (hMF : ModelFacts n Xg Qg Eg Fg zg reps NE D Eb Fb KE KF C)
    (hm : SylModel (grpN n Xg) (grpN n Qg) (grpN n Eg) (grpN n Fg) U (permOfArr n zg) k)
    {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G} {z : G} (hQ : Sec4Q G A R g E F S₁ Q z)
    (fN : ↥(grpN n Xg) →* ↥(normalizer (Q : Set G)))
    (hf : Function.Injective ((normalizer (Q : Set G)).subtype.comp fN))
    (hfr : ((normalizer (Q : Set G)).subtype.comp fN).range = S₁)
    (hcS : ∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z)
    (huniq : ∀ Q' : Subgroup G, Q' ≤ S₁ → Nat.card Q' = 2 ^ 7 → (∀ x ∈ Q', x ^ 2 ∈ zpowers z) →
      (∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → Q' = Q)
    (h46 : ∀ X : Subgroup G, X = E ∨ X = F → X ≤ iX z X ∧ Nat.card (iX z X) = 3072 ∧
      iX z X ≤ normalizer (Q : Set G) ∧
      ∀ c ∈ iX z X, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3)
    (hQQ : trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Qg) = Q)
    (hzf : z = (fN ⟨permOfArr n zg, hm.z_mem⟩ : G))
    (hEF : (E = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Eg) ∧
          F = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Fg)) ∨
        (E = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Fg) ∧
          F = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n Eg))) :
    ∃ i < 2, ∃ j < 2,
      (VCode.ofModel fN hf hMF.rep hm.QX hQQ hm.z_mem hzf).img (std_of_sec4Q hQ)
        (iX z E ⊔ iX z F) = grpN 64 (KE[i]! ++ KF[j]!) := by
  have hs := std_of_sec4Q hQ
  have hS₁N := le_normalizer_of_uniq hQ huniq
  have hcent := centralizer_le_sup hQ hS₁N hcS
  set c := VCode.ofModel fN hf hMF.rep hm.QX hQQ hm.z_mem hzf with hc
  have hrepX : ∀ v, repV n reps v ∈ grpN n Xg := fun v => hm.QX (hMF.rep.mem v)
  have himg : ∀ {gs ds : List (Array ℕ)}, grpN n gs ≤ grpN n Xg →
      (gs.length = ds.length ∧ ∀ k < gs.length, validA 64 ds[k]! = true ∧
        ActsBy n reps zg (permOfArr n gs[k]!) (permOfArr 64 ds[k]!)) →
      c.img hs (trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n gs)) = grpN 64 ds :=
    fun hgX hact => by
      rw [VCode.img_trS]
      exact VCode.map_grpN_eq hrepX (fun v => rfl) hm.z_mem hzf hgX hact
  have himE := himg hm.EX hMF.actE
  have himF := himg hm.FX hMF.actF
  have himP := himg hMF.ne_le hMF.actD
  have hPcard : Nat.card (trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n NE)) =
      2 ^ 10 := by
    rw [card_trS hf hMF.ne_le, hMF.ne_card]
    norm_num
  have hPS : trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n NE) ≤ S₁ :=
    hfr ▸ trS_le_range _
  have hPE := trS_le_normalizer hf hMF.ne_normE
  have hPF := trS_le_normalizer hf hMF.ne_normF
  have hIX : ∀ X : Subgroup G, (X = E ∨ X = F) → ∀ {Xb K0 K1 : List (Array ℕ)},
      c.img hs X = grpN 64 Xb →
      trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n NE) ≤ normalizer (X : Set G) →
      (∀ K : Subgroup (Equiv.Perm (Fin 64)), K ≤ oV → Nat.card K = 24 → grpN 64 D ≤ K →
        K ≤ normalizer (grpN 64 Xb : Set (Equiv.Perm (Fin 64))) →
          K = grpN 64 K0 ∨ K = grpN 64 K1) →
      c.img hs (iX z X) = grpN 64 K0 ∨ c.img hs (iX z X) = grpN 64 K1 := by
    intro X hX Xb K0 K1 hXimg hPX hcand
    obtain ⟨-, hcard, hIN, h3⟩ := h46 X hX
    have hQN : Q ≤ normalizer (X : Set G) := by
      rcases hX with rfl | rfl
      exacts [hQ.normE, hQ.normF]
    have hQI : Q ≤ iX z X := le_oUpper_of_card (le_inf hQ.Q_le_centralizer hQN) hQ.card
    have hPI := le_oUpper_of_card (le_inf (hPS.trans hQ.le_centralizer) hPX) hPcard
    exact VCode.img_iX_eq hnd hcent hQI hIN ((iX_le z X).trans inf_le_right) hcard h3 hPI himP
      hXimg hcand
  rw [VCode.img_sup (h46 E (Or.inl rfl)).2.2.1 (h46 F (Or.inr rfl)).2.2.1]
  rcases hEF with ⟨hE, hF⟩ | ⟨hE, hF⟩
  · have h1 := hIX E (Or.inl rfl) (by rw [hE]; exact himE) (by rw [hE]; exact hPE) hMF.candE
    have h2 := hIX F (Or.inr rfl) (by rw [hF]; exact himF) (by rw [hF]; exact hPF) hMF.candF
    exact exists_idx_of h1 h2
  · have h1 := hIX E (Or.inl rfl) (by rw [hE]; exact himF) (by rw [hE]; exact hPF) hMF.candF
    have h2 := hIX F (Or.inr rfl) (by rw [hF]; exact himE) (by rw [hF]; exact hPE) hMF.candE
    rw [sup_comm]
    exact exists_idx_of h2 h1

theorem exists_img_Y_conj (hnd : nondegCheck = true) {n : ℕ} {Xg Qg Eg Fg : List (Array ℕ)}
    {zg : Array ℕ} {reps NE D Eb Fb : List (Array ℕ)} {KE KF : List (List (Array ℕ))}
    {C : List (Array ℕ)} {U : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    (hMF : ModelFacts n Xg Qg Eg Fg zg reps NE D Eb Fb KE KF C)
    (hm : SylModel (grpN n Xg) (grpN n Qg) (grpN n Eg) (grpN n Fg) U (permOfArr n zg) k)
    {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G} {z : G} (hQ : Sec4Q G A R g E F S₁ Q z)
    (fN : ↥(grpN n Xg) →* ↥(normalizer (Q : Set G)))
    (hf : Function.Injective ((normalizer (Q : Set G)).subtype.comp fN))
    (hfr : ((normalizer (Q : Set G)).subtype.comp fN).range = S₁)
    (hcS : ∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z)
    (huniq : ∀ Q' : Subgroup G, Q' ≤ S₁ → Nat.card Q' = 2 ^ 7 → (∀ x ∈ Q', x ^ 2 ∈ zpowers z) →
      (∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → Q' = Q)
    (h46 : ∀ X : Subgroup G, X = E ∨ X = F → X ≤ iX z X ∧ Nat.card (iX z X) = 3072 ∧
      iX z X ≤ normalizer (Q : Set G) ∧
      ∀ c ∈ iX z X, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3) :
    ∃ (c : VCode Q z) (c₀ : Equiv.Perm (Fin 64)), c₀ ∈ oV ∧
      c.img (std_of_sec4Q hQ) (iX z E ⊔ iX z F) = ystar.map (MulAut.conj c₀).toMonoidHom := by
  obtain ⟨hQQ, hzf, hEF⟩ := transport_QZ hm hQ fN hf hfr
  obtain ⟨i, hi, j, hj, hY⟩ := img_Y_eq hnd hMF hm hQ fN hf hfr hcS huniq h46 hQQ hzf hEF
  obtain ⟨hc₀, hconj⟩ := hMF.conj i hi j hj
  exact ⟨_, _, hc₀, hY.trans hconj.symm⟩

theorem card_S4Z2 : Nat.card (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) = 48 := by
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin,
    Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)), Fintype.card_multiplicative,
    ZMod.card]
  rfl

end Proof

theorem step47_img_Y
    (h44 : Step44ii) (hNX : Sec4NXModel) {G : Type} [Group G] [Finite G]
    {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G} {z : G}
    (hQ : Sec4Q G A R g E F S₁ Q z) :
    ∃ (c : VCode Q z) (c₀ : Equiv.Perm (Fin 64)), c₀ ∈ oV ∧
      c.img (std_of_sec4Q hQ) (iX z E ⊔ iX z F) = ystar.map (MulAut.conj c₀).toMonoidHom ∧
      centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)) := by
  obtain ⟨-, hnd, -, -⟩ := q47Check_parts q47_check
  obtain ⟨-, -, hcS, huniq⟩ := sec4Q_qe h44 hQ
  have h46 : ∀ X : Subgroup G, X = E ∨ X = F → X ≤ iX z X ∧ Nat.card (iX z X) = 3072 ∧
      iX z X ≤ normalizer (Q : Set G) ∧
      ∀ c ∈ iX z X, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3 := by
    intro X hX
    obtain ⟨hXI, ⟨φ, hφ, hker⟩, -, -, hIN, -, h3⟩ := step46_X h44 hNX hQ hX
    refine ⟨hXI, ?_, hIN, h3⟩
    have hX64 : Nat.card X = 64 := by
      rcases hX with rfl | rfl
      exacts [hQ.setting.frame.cardE, hQ.setting.frame.cardF]
    rw [card_eq_card_ker_mul φ hφ, hker, Nat.card_congr (subgroupOfEquivOfLe hXI).toEquiv, hX64,
      card_S4Z2]
  have hS₁N := le_normalizer_of_uniq hQ huniq
  have hcent := centralizer_le_sup hQ hS₁N hcS
  rcases h44 G A R g E F hQ.setting S₁ hQ.sylowN with ⟨-, P, ⟨e⟩⟩ |
    ⟨-, H, _, _, K, hKn, hK, hi, hC, P, ⟨e⟩⟩
  · obtain ⟨e0⟩ := nonempty_sylow_he_equiv P
    obtain ⟨fN, hf, hfr⟩ := exists_fN hS₁N (e.trans e0).symm
    obtain ⟨c, c₀, hc₀, hY⟩ :=
      exists_img_Y_conj hnd modelFacts16 sylModel16 hQ fN hf hfr hcS huniq h46
    exact ⟨c, c₀, hc₀, hY, hcent⟩
  · obtain ⟨e0⟩ := nonempty_sylow_aut_equiv hKn hK hi hC P
    obtain ⟨fN, hf, hfr⟩ := exists_fN hS₁N (e.trans e0).symm
    obtain ⟨c, c₀, hc₀, hY⟩ :=
      exists_img_Y_conj hnd modelFacts32 sylModel32 hQ fN hf hfr hcS huniq h46
    exact ⟨c, c₀, hc₀, hY, hcent⟩

theorem iX_sup_le_normalizer
    (h44 : Step44ii) (hNX : Sec4NXModel) {G : Type} [Group G] [Finite G]
    {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G} {z : G}
    (hQ : Sec4Q G A R g E F S₁ Q z) : iX z E ⊔ iX z F ≤ normalizer (Q : Set G) :=
  sup_le (step46_X h44 hNX hQ (X := E) (Or.inl rfl)).2.2.2.2.1
    (step46_X h44 hNX hQ (X := F) (Or.inr rfl)).2.2.2.2.1

theorem step47_rho_nstar
    (h44 : Step44ii) (hNX : Sec4NXModel) {G : Type} [Group G] [Finite G]
    {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G} {z : G}
    (hQ : Sec4Q G A R g E F S₁ Q z) :
    ∃ (c : VCode Q z) (hs : VCode.Std Q z), ∃ c₀ ∈ oV,
      (∀ n : ↥(normalizer (Q : Set G)), c₀⁻¹ * c.rho hs n * c₀ ∈ nstar) ∧
      centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)) := by
  obtain ⟨hT, -, hq, -⟩ := q47Check_parts q47_check
  obtain ⟨c, c₀, hc₀, hY, hcent⟩ := step47_img_Y h44 hNX hQ
  have hN := (ystar_le_range_le_nstar hT hq c (std_of_sec4Q hQ) hc₀ hY
    (not_dvd_card_normalizer hQ)).2
  refine ⟨c, std_of_sec4Q hQ, c₀, hc₀, fun n => ?_, hcent⟩
  have h := hN ⟨n, rfl⟩
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h

theorem step47_of
    (h44 : Step44ii) (hNX : Sec4NXModel) : Step47 := by
  intro G _ _ A R g E F S₁ Q z hQ
  obtain ⟨hT, hnd, hq, hb⟩ := q47Check_parts q47_check
  obtain ⟨c, c₀, hc₀, hY, hcent⟩ := step47_img_Y h44 hNX hQ
  have hQY : Q ≤ iX z E ⊔ iX z F :=
    (le_oUpper_of_card (le_inf hQ.Q_le_centralizer hQ.normE) hQ.card).trans le_sup_left
  exact step47_of_img hT hq hb hnd c (std_of_sec4Q hQ) hcent hQY
    (iX_sup_le_normalizer h44 hNX hQ) hc₀ hY (not_dvd_card_normalizer hQ)

end CFSG.ComponentClassification.AS81
