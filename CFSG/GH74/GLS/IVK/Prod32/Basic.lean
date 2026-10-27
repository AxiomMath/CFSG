module

public import CFSG.GH74.GLS.IVK.Statements.Sec32
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31g
public import CFSG.RankThree.PartOne.S10.ComponentOrbitSemisimpleLocalRankWitness

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section A0
variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}

omit [Finite H] in
theorem mem_sup_of_comm {K₁ K₂ : Subgroup H} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (x : H) :
    x ∈ K₁ ⊔ K₂ ↔ ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b := by
  constructor
  · intro hx
    let S : Subgroup H :=
      { carrier := {x | ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b}
        one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [← hc a' ha' b hb]
            _ = a * a' * (b * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
          have := hc a ha b⁻¹ (K₂.inv_mem hb)
          calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
            _ = a⁻¹ * b⁻¹ := by
              have h1 : a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
              rw [h1, ← hc a ha b hb, mul_inv_rev] }
    have hle : K₁ ⊔ K₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, K₂.one_mem, by simp⟩)
      (fun b hb => ⟨1, K₁.one_mem, b, hb, by simp⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem Setting.normal (hS : Setting H K₁ K₂ z) : (K₁ ⊔ K₂).Normal := by
  rw [← hS.fstar]; exact (CFSG.LocalCores.generalized_fitting_characteristic).2

theorem Setting.centralizer_le (hS : Setting H K₁ K₂ z) :
    centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) ≤ K₁ ⊔ K₂ := by
  rw [← hS.fstar]; exact CFSG.centralizer_generalizedFitting_le H

omit [Finite H] in
theorem quasisimple_of_type {K : Subgroup H}
    (h : HasSL2Model ↥K (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt ↥K 7) :
    CFSG.IsQuasisimple ↥K := by
  rcases h with ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩ | h
  · have := CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' (K := F) (by omega)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e.trans (specialLinearGroupEquivStatedSL 2 F).symm).symm this
  · exact h.1

theorem Setting.quasisimple₁ (hS : Setting H K₁ K₂ z) : CFSG.IsQuasisimple ↥K₁ :=
  quasisimple_of_type hS.type₁

omit [Finite H] in
theorem exists_center_ne_one_of_type {K : Subgroup H}
    (h : HasSL2Model ↥K (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt ↥K 7) :
    ∃ w ∈ Subgroup.center ↥K, w ≠ 1 := by
  rcases h with ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩ | h
  · set e' := e.trans (specialLinearGroupEquivStatedSL 2 F).symm with he'
    have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
    refine ⟨e'.symm (CFSG.Semidihedral.OddFieldSL2.minusIdentity F), ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      apply e'.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.mp
        (CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F) (e' g)
    · intro h1
      have h3 := CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F h2
      have : CFSG.Semidihedral.OddFieldSL2.minusIdentity F = 1 := by
        have := congrArg e' h1
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      rw [this, orderOf_one] at h3
      omega
  · have h2 : Nat.card (Subgroup.center ↥K) = 2 := h.2.1
    have hne : Subgroup.center ↥K ≠ ⊥ := fun hb => by
      rw [hb, Subgroup.card_bot] at h2; omega
    obtain ⟨w, hw⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨w, w.2, fun h => hw (Subtype.ext h)⟩

omit [Finite H] in
theorem eq_one_or_eq_of_mem_zpowers {z g : H} (hz : orderOf z = 2) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul]; simp [hz2]
  · right; rw [zpow_add, zpow_mul]; simp [hz2]

theorem Setting.inter_le (hS : Setting H K₁ K₂ z) : K₁ ⊓ K₂ ≤ zpowers z := by
  intro x hx
  have h1 : ∀ y ∈ K₁ ⊔ K₂, y * x = x * y := by
    intro y hy
    have hle : K₁ ⊔ K₂ ≤ centralizer ({x} : Set H) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hS.comm y hy x hx.2)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hS.comm x hx.1 y hy).symm
    have := hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  rw [← hS.zK]
  exact Subgroup.mem_map.2 ⟨⟨x, Subgroup.mem_sup_left hx.1⟩, by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h1 g g.2), rfl⟩

theorem Setting.center_mem₁ (hS : Setting H K₁ K₂ z) {w : ↥K₁} (hw : w ∈ Subgroup.center ↥K₁) :
    (w : H) ∈ zpowers z := by
  rw [← hS.zK]
  refine Subgroup.mem_map.2 ⟨⟨(w : H), Subgroup.mem_sup_left w.2⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', hg'⟩ := g
  have : g' ∈ K₁ ⊔ K₂ := hg'
  have hle : K₁ ⊔ K₂ ≤ centralizer ({(w : H)} : Set H) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.mp hw ⟨y, hy⟩
      exact congrArg Subtype.val this
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hS.comm w w.2 y hy).symm
  have h2 := hle hg'
  rw [Subgroup.mem_centralizer_singleton_iff] at h2
  exact Subtype.ext h2

theorem Setting.z_mem₁ (hS : Setting H K₁ K₂ z) : z ∈ K₁ := by
  obtain ⟨w, hw, hw1⟩ := exists_center_ne_one_of_type hS.type₁
  have hwK : (w : H) ∈ zpowers z := hS.center_mem₁ hw
  rcases eq_one_or_eq_of_mem_zpowers hS.z_ord hwK with h | h
  · exact absurd (Subtype.ext h) hw1
  · rw [← h]; exact w.2

theorem Setting.symm (hS : Setting H K₁ K₂ z) : Setting H K₂ K₁ z where
  fstar := by rw [sup_comm]; exact hS.fstar
  comm a ha b hb := (hS.comm b hb a ha).symm
  type₁ := hS.type₂
  type₂ := hS.type₁
  z_ord := hS.z_ord
  zK := by rw [sup_comm]; exact hS.zK

theorem Setting.z_mem₂ (hS : Setting H K₁ K₂ z) : z ∈ K₂ := hS.symm.z_mem₁

theorem Setting.inter (hS : Setting H K₁ K₂ z) : K₁ ⊓ K₂ = zpowers z :=
  le_antisymm hS.inter_le (Subgroup.zpowers_le.mpr ⟨hS.z_mem₁, hS.z_mem₂⟩)

theorem Setting.ne (hS : Setting H K₁ K₂ z) : K₁ ≠ K₂ := by
  intro h
  have hq := hS.quasisimple₁
  have hc : ∀ a b : ↥K₁, a * b = b * a := fun a b =>
    Subtype.ext (hS.comm a a.2 b (h ▸ b.2))
  have : Group.IsSolvable ↥K₁ := Group.isSolvable_of_comm hc
  have : Nontrivial ↥K₁ := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect ↥K₁ := hq.1
  exact Group.IsPerfect.not_isSolvable ↥K₁ inferInstance

theorem Setting.le_normalizer₁ (hS : Setting H K₁ K₂ z) : K₂ ≤ normalizer (K₁ : Set H) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have h1 : y * u * y⁻¹ = u := by
      have := hS.comm u hu y hy
      rw [← this]; group
    rw [h1]; exact hu
  · intro hu
    have h2 : y⁻¹ * (y * u * y⁻¹) * y = y * u * y⁻¹ := by
      have := hS.comm (y * u * y⁻¹) hu y⁻¹ (inv_mem hy)
      rw [← this]; group
    have h3 : y⁻¹ * (y * u * y⁻¹) * y = u := by group
    rw [← h3, h2]; exact hu

theorem Setting.normal_subgroupOf₁ (hS : Setting H K₁ K₂ z) :
    (K₁.subgroupOf (K₁ ⊔ K₂)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer hS.le_normalizer₁

theorem Setting.isSubnormal₁ (hS : Setting H K₁ K₂ z) : K₁.IsSubnormal :=
  Subgroup.IsSubnormal.trans (le_sup_left : K₁ ≤ K₁ ⊔ K₂)
    hS.normal_subgroupOf₁.isSubnormal hS.normal.isSubnormal

theorem Setting.isComponent₁ (hS : Setting H K₁ K₂ z) : CFSG.IsComponent K₁ :=
  ⟨hS.quasisimple₁, hS.isSubnormal₁⟩

theorem Setting.isComponent₂ (hS : Setting H K₁ K₂ z) : CFSG.IsComponent K₂ :=
  hS.symm.isComponent₁

theorem Setting.conj_dichotomy (hS : Setting H K₁ K₂ z) (g : H) :
    K₁.map (MulAut.conj g).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  classical
  let A : Bool → Subgroup H := fun b => if b then K₁ else K₂
  have hA : ∀ b, CFSG.IsComponent (A b) := by
    intro b; cases b
    · exact hS.isComponent₂
    · exact hS.isComponent₁
  have hsup : (⨆ b, A b) = K₁ ⊔ K₂ := by
    rw [iSup_bool_eq]
    simp [A]
  have hL : CFSG.IsComponent (K₁.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hS.isComponent₁
  have hLle : K₁.map (MulAut.conj g).toMonoidHom ≤ ⨆ b, A b := by
    rw [hsup]
    rintro _ ⟨y, hy, rfl⟩
    exact hS.normal.conj_mem y (Subgroup.mem_sup_left hy) g
  obtain ⟨b, hb⟩ := CFSG.RankThree.PartOne.SemisimpleSection.exists_eq_subgroupOf_of_isComponent_iSup A hA
    (CFSG.LocalCores.component_overgroup hL hLle)
  have hAle : A b ≤ ⨆ b, A b := le_iSup A b
  have hEq : K₁.map (MulAut.conj g).toMonoidHom = A b := by
    have := Subgroup.subgroupOf_inj.mp hb
    rwa [inf_eq_left.mpr hLle, inf_eq_left.mpr hAle] at this
  cases b
  · right; exact hEq
  · left; exact hEq

theorem Setting.index_le_two (hS : Setting H K₁ K₂ z) : (normalizer (K₁ : Set H)).index ≤ 2 :=
  CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.index_le_two_of_dichotomy hS.conj_dichotomy

theorem Setting.normalizer₁₂ (hS : Setting H K₁ K₂ z) {x : H} (hx : x ∈ normalizer (K₁ : Set H)) :
    x ∈ normalizer (K₂ : Set H) := by
  rw [CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.mem_normalizer_iff_conj_eq] at hx ⊢
  rcases hS.symm.conj_dichotomy x with h | h
  · exact h
  · exfalso
    apply hS.ne
    apply Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
    rw [hx]; exact h.symm

theorem Setting.normalizer_eq (hS : Setting H K₁ K₂ z) :
    normalizer (K₁ : Set H) = normalizer (K₂ : Set H) := by
  ext x
  exact ⟨fun h => hS.normalizer₁₂ h, fun h => hS.symm.normalizer₁₂ h⟩

theorem Setting.swap (hS : Setting H K₁ K₂ z) {x : H} (hx : x ∉ normalizer (K₁ : Set H)) :
    K₁.map (MulAut.conj x).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj x).toMonoidHom = K₁ := by
  refine ⟨?_, ?_⟩
  · rcases hS.conj_dichotomy x with h | h
    · exact absurd ((CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.mem_normalizer_iff_conj_eq K₁ x).mpr h) hx
    · exact h
  · rcases hS.symm.conj_dichotomy x with h | h
    · exact absurd (hS.normalizer_eq ▸
        ((CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.mem_normalizer_iff_conj_eq K₂ x).mpr h)) hx
    · exact h

theorem Setting.conj_mem₂ (hS : Setting H K₁ K₂ z) {x : H} (hx : x ∈ normalizer (K₁ : Set H))
    {y : H} (hy : y ∈ K₂) : x * y * x⁻¹ ∈ K₂ :=
  (Subgroup.mem_normalizer_iff.mp (hS.normalizer₁₂ hx) y).mp hy

theorem Setting.conj_mem_swap₁ (hS : Setting H K₁ K₂ z) {x : H} (hx : x ∉ normalizer (K₁ : Set H))
    {y : H} (hy : y ∈ K₁) : x * y * x⁻¹ ∈ K₂ := by
  have := hS.swap hx
  rw [← this.1]
  exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩

theorem Setting.conj_mem_swap₂ (hS : Setting H K₁ K₂ z) {x : H} (hx : x ∉ normalizer (K₁ : Set H))
    {y : H} (hy : y ∈ K₂) : x * y * x⁻¹ ∈ K₁ := by
  have := hS.swap hx
  rw [← this.2]
  exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩

section HypLemmas

theorem Hyp.z_central (h : Hyp H K₁ K₂ z T a) (g : H) : g * z * g⁻¹ = z := by
  have hS := h.setting
  have hzK : z ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left hS.z_mem₁
  have hzc : ∀ m ∈ K₁ ⊔ K₂, m * z = z * m := by
    have : z ∈ (Subgroup.center ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype := by
      rw [hS.zK]; exact Subgroup.mem_zpowers z
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 this
    intro m hm
    have h3 := Subgroup.mem_center_iff.mp hc ⟨m, hm⟩
    have h2 := congrArg Subtype.val h3
    have hcz' : (c : H) = z := hcz
    simp only [Subgroup.coe_mul] at h2
    rw [hcz'] at h2
    exact h2
  have hmem : g * z * g⁻¹ ∈ (Subgroup.center ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype := by
    refine Subgroup.mem_map.2 ⟨⟨g * z * g⁻¹, hS.normal.conj_mem z hzK g⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    show (k : H) * (g * z * g⁻¹) = (g * z * g⁻¹) * k
    have hk' : g⁻¹ * (k : H) * g ∈ K₁ ⊔ K₂ := by
      have := hS.normal.conj_mem (k : H) k.2 g⁻¹
      simpa using this
    have h1 := hzc _ hk'
    calc (k : H) * (g * z * g⁻¹) = g * ((g⁻¹ * (k : H) * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * (k : H) * g)) * g⁻¹ := by rw [h1]
      _ = (g * z * g⁻¹) * k := by group
  rw [hS.zK] at hmem
  rcases eq_one_or_eq_of_mem_zpowers hS.z_ord hmem with h1 | h1
  · exfalso
    have hz1 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have h2 := hS.z_ord
    rw [hz1, orderOf_one] at h2
    omega
  · exact h1

theorem Hyp.z_mem (h : Hyp H K₁ K₂ z T a) : z ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.setting
  obtain ⟨hTle, hTp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h.sylow
  have hdvd' : ¬ 2 ∣ T.index := by
    rwa [Subgroup.relIndex_top_right] at hdvd
  let S : Sylow 2 H := hTp.toSylow hdvd'
  have hN : (zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * z ^ k * g⁻¹ = z ^ k := by
      have h1 := h.z_central g
      calc g * z ^ k * g⁻¹ = (g * z * g⁻¹) ^ k := by rw [conj_zpow]
        _ = z ^ k := by rw [h1]
    rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hS.z_ord]; norm_num)
  have := hp.le_sylow_of_normal S
  have hSeq : (S : Subgroup H) = T := IsPGroup.toSylow_coe hTp hdvd'
  rw [hSeq] at this
  exact this (Subgroup.mem_zpowers z)

theorem Hyp.sylow₁ (h : Hyp H K₁ K₂ z T a) : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₁) K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.setting
  have h1 := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer h.sylow (le_top : K₁ ⊔ K₂ ≤ ⊤)
    (by
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro u
      exact ⟨fun hu => hS.normal.conj_mem u hu x, fun hu => by
        have := hS.normal.conj_mem _ hu x⁻¹
        simpa [mul_assoc] using this⟩)
  have h2 := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer h1 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)
    (fun x hx => by
      have : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set H) :=
        sup_le Subgroup.le_normalizer hS.le_normalizer₁
      exact this hx)
  rwa [inf_assoc, inf_eq_right.mpr (le_sup_left : K₁ ≤ K₁ ⊔ K₂)] at h2

end HypLemmas

end A0
end CFSG.GH74.GLS.IVK.Prod3
