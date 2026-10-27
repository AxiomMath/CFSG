module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Unpack

variable {A : Type} [Group A] [Finite A]

structure CellData (zb : A) (p : ℕ) (X : Subgroup A) : Prop where
  z2 : zb * zb = 1
  A4 : Sig4A zb (⊤ : Subgroup A) p X
  op : pCore p A = ⊥
  gen : layer A ⊔ X ⊔ zpowers zb = ⊤
  quasi : IsQuasisimple ↥(layer A)
  Zcore : center ↥(layer A) = pCore 2 ↥(layer A)
  nc : ¬ ⁅layer A, X⁆ ≤ (center ↥(layer A)).map (layer A).subtype

end Unpack

theorem CellData.of_ctx {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀} [H₁.Normal] {hz : z ∈ H₀}
    {p : ℕ} {X : Subgroup (Sec H₀ H₁)} (hsig : Sig4B G z H₀ H₁ hz p X)
    (hyp : Hyp42 (zSec z H₀ hz H₁) X) : CellData (zSec z H₀ hz H₁) p X where
  z2 := by
    have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hctx.central.1, pow_two] at this
    have h1 : (⟨z, hz⟩ : ↥H₀) * ⟨z, hz⟩ = 1 := Subtype.ext hzz
    show QuotientGroup.mk (⟨z, hz⟩ : ↥H₀) * QuotientGroup.mk (⟨z, hz⟩ : ↥H₀) = 1
    rw [← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one]
  A4 := hsig.A
  op := hsig.op
  gen := hyp.1
  quasi := hyp.2.1
  Zcore := hyp.2.2.1
  nc := hyp.2.2.2

section Reductions

variable {A : Type} [Group A] [Finite A]

theorem layer_normal : (layer A).Normal := by
  have hc : (layer A).Characteristic := LocalCores.layer_characteristic
  infer_instance

theorem CellData.exists_not_commute {zb : A} {p : ℕ} {X : Subgroup A} (h : CellData zb p X) :
    ∃ k ∈ layer A, zb * k ≠ k * zb := by
  classical
  by_contra hcon0
  have hcon : ∀ k ∈ layer A, zb * k = k * zb := fun k hk =>
    by_contra fun hne => hcon0 ⟨k, hk, hne⟩
  apply h.nc
  have hKn : (layer A).Normal := layer_normal
  have hKN : ∀ k ∈ layer A, k ∈ normalizer (X : Set A) := fun k hk =>
    h.A4.inv k (Subgroup.mem_top k)
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcon k hk).symm)
  set R : Subgroup ↥(layer A) := X.subgroupOf (layer A) with hR
  have hRn : R.Normal := by
    refine ⟨fun r hr g => ?_⟩
    rw [hR, Subgroup.mem_subgroupOf] at hr ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hKN g.1 g.2) r.1).mp hr
    simpa using this
  have hRc : R ≤ center ↥(layer A) := by
    rcases LocalCores.quasisimple_normal_subgroups h.quasi hRn with htop | hz
    · exfalso
      have hKX : ∀ k : ↥(layer A), (k : A) ∈ X := fun k => by
        have : k ∈ R := htop ▸ Subgroup.mem_top k
        exact Subgroup.mem_subgroupOf.mp this
      have hpK : IsPGroup p ↥(layer A) := by
        intro k
        obtain ⟨m, hm⟩ := h.A4.pgroup ⟨(k : A), hKX k⟩
        refine ⟨m, Subtype.ext ?_⟩
        have := congrArg Subtype.val hm
        simpa using this
      have : Fact p.Prime := ⟨h.A4.prime⟩
      have : Nontrivial (↥(layer A) ⧸ center ↥(layer A)) := h.quasi.2.1.toNontrivial
      have : Nontrivial ↥(layer A) := (QuotientGroup.mk'_surjective (center ↥(layer A))).nontrivial
      have : Group.IsPerfect ↥(layer A) := h.quasi.1
      exact Group.IsPerfect.not_isNilpotent _ hpK.isNilpotent
    · exact hz
  rw [Subgroup.commutator_le]
  intro k hk x hx
  have hkX : ⁅k, x⁆ ∈ X := by
    have h1 : k * x * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hKN k hk) x).mp hx
    exact X.mul_mem h1 (X.inv_mem hx)
  have hkK : ⁅k, x⁆ ∈ layer A := by
    have h1 : x * k⁻¹ * x⁻¹ ∈ layer A := hKn.conj_mem k⁻¹ ((layer A).inv_mem hk) x
    have : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact (layer A).mul_mem hk h1
  have hmem : (⟨⁅k, x⁆, hkK⟩ : ↥(layer A)) ∈ R := Subgroup.mem_subgroupOf.mpr hkX
  exact ⟨_, hRc hmem, rfl⟩

noncomputable def layerAut (zb : A) : MulAut ↥(layer A) :=
  haveI : (layer A).Normal := layer_normal
  MulAut.conjNormal zb

theorem coe_layerAut (zb : A) (x : ↥(layer A)) : ((layerAut zb x : ↥(layer A)) : A) = zb * x * zb⁻¹ := by
  have : (layer A).Normal := layer_normal
  exact MulAut.conjNormal_apply zb x

theorem layerAut_layerAut {zb : A} (hz2 : zb * zb = 1) (x : ↥(layer A)) :
    layerAut zb (layerAut zb x) = x := by
  apply Subtype.ext
  rw [coe_layerAut, coe_layerAut]
  have hzi : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hz2
  rw [hzi]
  calc zb * (zb * (x : A) * zb) * zb = (zb * zb) * (x : A) * (zb * zb) := by group
    _ = x := by rw [hz2]; group

end Reductions

section Induced

theorem exists_induced {L P : Type} [Group L] [Group P] (a : MulAut L) (ha : ∀ x, a (a x) = x)
    (e : (L ⧸ center L) ≃* P) :
    ∃ (π : L →* P) (α : MulAut P), Function.Surjective π ∧ π.ker = center L ∧
      (∀ x, π (a x) = α (π x)) ∧ ∀ s, α (α s) = s := by
  set π : L →* P := e.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set α : MulAut P := e.symm.trans ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient a).trans e)
    with hαdef
  have hcomm : ∀ x, π (a x) = α (π x) := fun x => by
    rw [hαdef, hπdef, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  refine ⟨π, α, hπ, hker, hcomm, fun s => ?_⟩
  obtain ⟨x, rfl⟩ := hπ s
  rw [← hcomm, ← hcomm, ha]

end Induced

section Lift

variable {A : Type} [Group A] [Finite A]

@[expose] def CentSection (zb : A) (T : Type) [Group T] : Prop :=
  ∃ (U : Subgroup A) (f : ↥U →* T), U ≤ centralizer ({zb} : Set A) ∧ Function.Surjective f

theorem centSection_of_fixed_perfect {zb : A} {P : Type} [Group P] {π : ↥(layer A) →* P}
    (hπ : Function.Surjective π) (hker : π.ker ≤ center ↥(layer A)) {α : MulAut P}
    (hcomm : ∀ x, π (layerAut zb x) = α (π x)) (Q : Subgroup P) [Group.IsPerfect Q]
    (hQ : ∀ s ∈ Q, α s = s) {T : Type} [Group T] (c : ↥Q →* T) (hc : Function.Surjective c) :
    CentSection zb T := by
  obtain ⟨-, hmap, hfix⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.fixedPerfectLift hπ hker hcomm Q hQ
  set D : Subgroup ↥(layer A) := ⁅Q.comap π, Q.comap π⁆ with hD
  set U : Subgroup A := D.map (layer A).subtype with hU
  have hUc : U ≤ centralizer ({zb} : Set A) := by
    rintro _ ⟨x, hx, rfl⟩
    have h2 := congrArg Subtype.val (hfix x hx)
    rw [coe_layerAut] at h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((mul_inv_eq_iff_eq_mul).mp h2).symm
  let e : ↥D ≃* ↥U := D.equivMapOfInjective (layer A).subtype (layer A).subtype_injective
  have hDQ : ∀ x : ↥D, π x.1 ∈ Q := fun x => by
    have : π x.1 ∈ D.map π := Subgroup.mem_map_of_mem π x.2
    rw [hmap] at this
    exact this
  let g : ↥D →* ↥Q := (π.comp D.subtype).codRestrict Q hDQ
  have hg : Function.Surjective g := by
    intro y
    have hy : (y : P) ∈ D.map π := by rw [hmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨U, (c.comp g).comp e.symm.toMonoidHom, hUc, (hc.comp hg).comp e.symm.surjective⟩

theorem exists_mul_of_mem_sup_of_comm' {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        have e := hc h₂ hh₂ k₁ hk₁
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [← e]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        have e := hc h hh k hk
        calc (h * k)⁻¹ = k⁻¹ * h⁻¹ := by group
          _ = h⁻¹ * k⁻¹ := by
            have : k * h = h * k := e.symm
            calc k⁻¹ * h⁻¹ = (h * k)⁻¹ := by group
              _ = (k * h)⁻¹ := by rw [this]
              _ = h⁻¹ * k⁻¹ := by group }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
  exact hle hx

open scoped IsMulCommutative in
theorem gen4_kill (hA : Gen4 A) {zb : A} (hz2 : zb * zb = 1) (hzK : zb ∉ layer A)
    {P : Type} [Group P] {π : ↥(layer A) →* P} (hπ : Function.Surjective π)
    (hker : π.ker = center ↥(layer A)) {α : MulAut P}
    (hcomm : ∀ x, π (layerAut zb x) = α (π x)) (E : Subgroup P)
    (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEcard : 2 ^ 4 ≤ Nat.card ↥E) (hEfix : ∀ e ∈ E, α e = e) : False := by
  classical
  have hKn : (layer A).Normal := layer_normal
  set N : Subgroup A := (center ↥(layer A)).map (layer A).subtype with hN
  have hNK : N ≤ layer A := Subgroup.map_subtype_le _
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hn
    have hc' : c ∈ center ↥(layer A) := hc
    refine ⟨⟨g * (c : A) * g⁻¹, hKn.conj_mem _ c.2 g⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    apply Subtype.ext
    have h1 := Subgroup.mem_center_iff.mp hc'
      (⟨g⁻¹ * (y : A) * g, by simpa using hKn.conj_mem _ y.2 g⁻¹⟩ : ↥(layer A))
    have h2 := congrArg Subtype.val h1
    change g⁻¹ * (y : A) * g * (c : A) = (c : A) * (g⁻¹ * (y : A) * g) at h2
    change (y : A) * (g * (c : A) * g⁻¹) = g * (c : A) * g⁻¹ * (y : A)
    calc (y : A) * (g * (c : A) * g⁻¹) = g * (g⁻¹ * (y : A) * g * (c : A)) * g⁻¹ := by group
      _ = g * ((c : A) * (g⁻¹ * (y : A) * g)) * g⁻¹ := by rw [h2]
      _ = g * (c : A) * g⁻¹ * (y : A) := by group
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  have hG4 : Gen4 (A ⧸ N) := Gen4.quotient N hA
  set Et : Subgroup ↥(layer A) := E.comap π with hEt
  let θ : ↥Et →* A ⧸ N := q.comp ((layer A).subtype.comp Et.subtype)
  let ψ : ↥Et →* ↥E := π.subgroupComap E
  have hψ : Function.Surjective ψ := π.subgroupComap_surjective E hπ
  have hkerθψ : θ.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : θ x = 1 ↔ (x.1 : A) ∈ N := by
      change q ((x.1 : ↥(layer A)) : A) = 1 ↔ _
      exact QuotientGroup.eq_one_iff _
    have h2 : (x.1 : A) ∈ N ↔ x.1 ∈ center ↥(layer A) := by
      constructor
      · rintro ⟨c, hc, hcx⟩
        have : c = x.1 := Subtype.ext hcx
        exact this ▸ hc
      · intro hx
        exact ⟨x.1, hx, rfl⟩
    have h3 : ψ x = 1 ↔ π x.1 = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1, h2, h3, ← hker, MonoidHom.mem_ker]
  have hcardH : Nat.card θ.range = Nat.card ↥E := by
    have h1 := Subgroup.card_ker_mul_card_range θ
    have h2 := Subgroup.card_ker_mul_card_range ψ
    rw [← hkerθψ, ← h1] at h2
    have hrange : Nat.card ψ.range = Nat.card ↥E := by
      rw [MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top]
    rw [hrange] at h2
    have hpos : 0 < Nat.card θ.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h2.symm
  set H₁ : Subgroup (A ⧸ N) := θ.range with hH₁
  have hqz : q zb ∉ H₁ := by
    rintro ⟨x, hx⟩
    have h1 : (q ((x.1 : ↥(layer A)) : A)) = q zb := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 : ((x.1 : ↥(layer A)) : A)⁻¹ * zb ∈ layer A := hNK h1
    apply hzK
    have h3 : zb = ((x.1 : ↥(layer A)) : A) * (((x.1 : ↥(layer A)) : A)⁻¹ * zb) := by group
    rw [h3]
    exact (layer A).mul_mem x.1.2 h2
  have hH₁c : ∀ a ∈ H₁, ∀ b ∈ H₁, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    show q ((x.1 : ↥(layer A)) : A) * q ((y.1 : ↥(layer A)) : A) = q ((y.1 : ↥(layer A)) : A) * q ((x.1 : ↥(layer A)) : A)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hc : π ((x.1 * y.1)⁻¹ * (y.1 * x.1)) = 1 := by
      have := hEc _ x.2 _ y.2
      simp only [map_mul, map_inv]
      rw [this]
      group
    have : (x.1 * y.1)⁻¹ * (y.1 * x.1) ∈ center ↥(layer A) := hker ▸ hc
    exact ⟨_, this, by simp⟩
  have hH₁2 : ∀ a ∈ H₁, a * a = 1 := by
    rintro _ ⟨x, rfl⟩
    show q ((x.1 : ↥(layer A)) : A) * q ((x.1 : ↥(layer A)) : A) = 1
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hc : π (x.1 * x.1) = 1 := by
      rw [map_mul]
      exact hE2 _ x.2
    have : x.1 * x.1 ∈ center ↥(layer A) := hker ▸ hc
    exact ⟨_, this, rfl⟩
  have hzq2 : q zb * q zb = 1 := by rw [← map_mul, hz2, map_one]
  have hzH : ∀ a ∈ H₁, q zb * a = a * q zb := by
    rintro _ ⟨x, rfl⟩
    show q zb * q ((x.1 : ↥(layer A)) : A) = q ((x.1 : ↥(layer A)) : A) * q zb
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hc : π ((x.1 : ↥(layer A))⁻¹ * layerAut zb x.1) = 1 := by
      rw [map_mul, map_inv, hcomm, hEfix _ x.2, inv_mul_cancel]
    have hcen : (x.1 : ↥(layer A))⁻¹ * layerAut zb x.1 ∈ center ↥(layer A) := hker ▸ hc
    refine ⟨_, hcen, ?_⟩
    have hzi : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hz2
    simp only [Subgroup.coe_subtype, coe_mul, coe_inv, coe_layerAut, mul_inv_rev, hzi, mul_assoc]
  set V : Subgroup (A ⧸ N) := H₁ ⊔ zpowers (q zb) with hV
  have hcommV : ∀ a ∈ H₁, ∀ b ∈ zpowers (q zb), a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (Commute.symm (hzH a ha)) n)).eq
  have hVel : CFSG.Open.IsElemAbelian 2 V := by
    have hmem : ∀ v ∈ V, ∃ a ∈ H₁, ∃ b ∈ zpowers (q zb), v = a * b := fun v hv =>
      exists_mul_of_mem_sup_of_comm' hcommV hv
    have hz : ∀ b ∈ zpowers (q zb), ∀ n ∈ H₁, b * n = n * b := fun b hb n hn =>
      (hcommV n hn b hb).symm
    have hbb : ∀ b ∈ zpowers (q zb), b * b = 1 := by
      intro b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [← zpow_add, show (2 * m + 2 * m : ℤ) = 2 * (2 * m) by ring, zpow_mul]
        have : q zb ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzq2
        rw [this, one_zpow]
      · rw [← zpow_add, show (2 * m + 1 + (2 * m + 1) : ℤ) = 2 * (2 * m + 1) by ring, zpow_mul]
        have : q zb ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzq2
        rw [this, one_zpow]
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun v hv => ?_⟩
    · obtain ⟨a₁, ha₁, b₁, hb₁, h₁⟩ := hmem a.1 a.2
      obtain ⟨a₂, ha₂, b₂, hb₂, h₂⟩ := hmem b.1 b.2
      apply Subtype.ext
      show (a : A ⧸ N) * b = b * a
      rw [h₁, h₂]
      have e1 := hH₁c a₁ ha₁ a₂ ha₂
      have e2 := hcommV a₁ ha₁ b₂ hb₂
      have e3 := hcommV a₂ ha₂ b₁ hb₁
      have e4 : b₁ * b₂ = b₂ * b₁ := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb₁
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb₂
        exact ((Commute.refl (q zb)).zpow_zpow n m).eq
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [← e3]
        _ = a₁ * a₂ * (b₁ * b₂) := by group
        _ = a₂ * a₁ * (b₂ * b₁) := by rw [e1, e4]
        _ = a₂ * (a₁ * b₂) * b₁ := by group
        _ = a₂ * (b₂ * a₁) * b₁ := by rw [e2]
        _ = a₂ * b₂ * (a₁ * b₁) := by group
    · obtain ⟨a₁, ha₁, b₁, hb₁, h₁⟩ := hmem v hv
      show v ^ 2 = 1
      rw [h₁, pow_two]
      have e3 := hcommV a₁ ha₁ b₁ hb₁
      calc a₁ * b₁ * (a₁ * b₁) = a₁ * (b₁ * a₁) * b₁ := by group
        _ = a₁ * (a₁ * b₁) * b₁ := by rw [← e3]
        _ = (a₁ * a₁) * (b₁ * b₁) := by group
        _ = 1 := by rw [hH₁2 a₁ ha₁, hbb b₁ hb₁, one_mul]
  have hVcard : Nat.card V ≤ 2 ^ 4 := hG4.card_le_of_elementary V hVel
  have hle : H₁ ≤ V := le_sup_left
  have hlt : H₁ ≠ V := by
    intro h
    apply hqz
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hdvd : Nat.card H₁ ∣ Nat.card V := Subgroup.card_dvd_of_le hle
  obtain ⟨c, hc⟩ := hdvd
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hlt
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, mul_one])
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : Nat.card V = 0 := by rw [hc, mul_zero]
    exact Nat.card_pos.ne' this
  have hH₁card : 2 ^ 4 ≤ Nat.card H₁ := hcardH ▸ hEcard
  have : 2 * Nat.card H₁ ≤ Nat.card V := by
    rw [hc, mul_comm 2]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

end Lift



section Bad

theorem CentSection.isSection {A : Type} [Group A] {zb : A} {T : Type} [Group T]
    (h : CentSection zb T) : IsSection T ↥(centralizer ({zb} : Set A)) := by
  obtain ⟨U, f, hU, hf⟩ := h
  exact ⟨U.subgroupOf (centralizer ({zb} : Set A)),
    f.comp (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom,
    hf.comp (Subgroup.subgroupOfEquivOfLe hU).surjective⟩

theorem not_isL2_of_involved {T : Type} [Group T] [Finite T] {p0 : ℕ} [Fact p0.Prime] (hp0 : p0 ≠ 2)
    (hinv : CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p0) T) :
    ¬ IVK.IsL2 T (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, hq, ⟨e⟩⟩
  have hL2 : IVK.L2Field F := ⟨hq.1, by omega⟩
  have hD := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
    (IVK.isOddPrimePower_of_L2Field hL2)
  have hT : CFSG.GorensteinWalter.HasDihedralSylowTwo T :=
    IVK.hasDihedralSylowTwo_of_equiv (e.trans (IVK.L2.equivPSL F)).symm hD
  exact CFSG.GorensteinWalter.qdSL_not_involved_of_hasDihedralSylowTwo hT hp0 hinv

theorem not_kindFactor {k : Kind} {T : Type} [Group T] [Finite T] {p0 : ℕ} [Fact p0.Prime]
    (hp0 : p0 ≠ 2)
    (hinv : CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p0) T)
    (hord : ¬ Nat.card T ∣ Nat.factorial 11) : ¬ KindFactor k T := by
  intro h
  cases k with
  | g2 => exact not_isL2_of_involved hp0 hinv h
  | psp4 => exact not_isL2_of_involved hp0 hinv h
  | l4 ε => exact not_isL2_of_involved hp0 hinv h
  | m12 => exact h
  | mcl => exact hord ((KindFactor.all h).card_dvd (Or.inl rfl))
  | ly => exact hord ((KindFactor.all h).card_dvd (Or.inr rfl))

end Bad

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
