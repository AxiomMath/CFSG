module

public import CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape
public import CFSG.GH74.Generic.BProg.B2.GenLocG2Basic
public import CFSG.GH74.Generic.BProg.B2.GenLocRee
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Exc
import CFSG.GH74.Generic.BProg.B2.GenLocG2SL2
public import CFSG.GH74.Generic.BProg.B2.PumpupTableExc

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape
open scoped MatrixGroups commutatorElement

namespace GenLocG2Outer

section Res
variable {J : Type} [Group J]

theorem mem_cent_of_fix (σ : J ≃* J) {v : J} (hv : σ v = v) {x : J} (hx : x ∈ centralizer ({v} : Set J)) :
    σ x ∈ centralizer ({v} : Set J) := by
  rw [mem_centralizer_singleton_iff] at hx ⊢
  calc σ x * v = σ x * σ v := by rw [hv]
    _ = σ (x * v) := (map_mul σ x v).symm
    _ = σ (v * x) := by rw [hx]
    _ = σ v * σ x := map_mul σ v x
    _ = v * σ x := by rw [hv]

@[expose] def resAut (σ : MulAut J) (v : J) (hv : σ v = v) : MulAut ↥(centralizer ({v} : Set J)) where
  toFun x := ⟨σ (x : J), mem_cent_of_fix σ hv x.2⟩
  invFun x := ⟨σ.symm (x : J), mem_cent_of_fix σ.symm (σ.symm_apply_eq.2 hv.symm) x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : J))
  right_inv x := Subtype.ext (σ.apply_symm_apply (x : J))
  map_mul' x y := Subtype.ext (map_mul σ (x : J) (y : J))

theorem resAut_apply (σ : MulAut J) (v : J) (hv : σ v = v) (x : ↥(centralizer ({v} : Set J))) :
    ((resAut σ v hv x : ↥(centralizer ({v} : Set J))) : J) = σ (x : J) := rfl

theorem resAut_resAut (σ : MulAut J) (hσ : σ * σ = 1) (v : J) (hv : σ v = v)
    (x : ↥(centralizer ({v} : Set J))) : resAut σ v hv (resAut σ v hv x) = x := by
  apply Subtype.ext
  rw [resAut_apply, resAut_apply]
  have := congrArg (fun φ : MulAut J => φ (x : J)) hσ
  simpa using this

end Res

section Dichotomy

variable {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

omit [Finite Y] in
theorem I₁_ne_I₂ (hq₁ : CFSG.IsQuasisimple ↥S.I₁) : S.I₁ ≠ S.I₂ := by
  intro h
  have hab : ∀ a ∈ S.I₁, ∀ b ∈ S.I₁, a * b = b * a := fun a ha b hb => S.comm a ha b (h ▸ hb)
  have hperf : ⁅S.I₁, S.I₁⁆ = S.I₁ := Subgroup.isPerfect_iff.mp hq₁.1
  have hbot : ⁅S.I₁, S.I₁⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hab a ha b hb)
  rw [hbot] at hperf
  have := S.z_mem₁
  rw [← hperf] at this
  exact S.z_ne (Subgroup.mem_bot.1 this)

theorem stable_or_swap (hq₁ : CFSG.IsQuasisimple ↥S.I₁) (hq₂ : CFSG.IsQuasisimple ↥S.I₂)
    (τ : MulAut Y) :
    ((∀ x ∈ S.I₁, τ x ∈ S.I₁) ∧ (∀ y ∈ S.I₂, τ y ∈ S.I₂)) ∨
      ((∀ x ∈ S.I₁, τ x ∈ S.I₂) ∧ (∀ y ∈ S.I₂, τ y ∈ S.I₁)) := by
  have hc₁ : CFSG.IsComponent S.I₁ := ⟨hq₁, S.normal₁.isSubnormal⟩
  have hc₂ : CFSG.IsComponent S.I₂ := ⟨hq₂, S.normal₂.isSubnormal⟩
  have k₁ := CFSG.GH74.Generic.BProg.B2.PumpupTableExc.isComponent_eq_I S (Or.inl hq₁) (Or.inl hq₂)
    (CFSG.LocalCores.isComponent_map_mulEquiv τ hc₁)
  have k₂ := CFSG.GH74.Generic.BProg.B2.PumpupTableExc.isComponent_eq_I S (Or.inl hq₁) (Or.inl hq₂)
    (CFSG.LocalCores.isComponent_map_mulEquiv τ hc₂)
  have hne := I₁_ne_I₂ S hq₁
  have mem : ∀ {K L : Subgroup Y}, K.map τ.toMonoidHom = L → ∀ x ∈ K, τ x ∈ L := by
    intro K L h x hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  rcases k₁ with h1 | h1 <;> rcases k₂ with h2 | h2
  · exact absurd (Subgroup.map_injective τ.injective (h2.trans h1.symm)).symm hne
  · exact Or.inl ⟨mem h1, mem h2⟩
  · exact Or.inr ⟨mem h1, mem h2⟩
  · exact absurd (Subgroup.map_injective τ.injective (h1.trans h2.symm)) hne

end Dichotomy

section Datum


variable {J : Type} [Group J] {f : ℕ}

theorem g2_outer_fixed_datum (hf : 3 ≤ f) (hodd : Odd f) (hJ : LieModel J .G2 0 3 f)
    {σ : MulAut J} (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : J →* MulAut J).range) :
    ∀ u : ↥(fixedIn J (Subgroup.zpowers σ)), orderOf u = 2 → GenLocRee.ReeDatum u f := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_of_lieModel hJ
  have : CharP F CFSG.LieType.Ree.ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hcard
  have : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.LieType.Ree.ReeTag.G2.tag F) :=
    CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨Ψ⟩ := GenLocG2Basic.nonempty_fixedIn_zpowers_equiv e σ
  have hα2 : (MulAut.congr e σ) ^ 2 = 1 := by rw [sq, ← map_mul, hσ, map_one]
  have hnot : MulAut.congr e σ ∉ (MulAut.conj : CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.G2g F →*
      MulAut (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.G2g F)).range :=
    fun h => hout ((GenLocG2Basic.congr_mem_range_conj_iff e σ).1 h)
  rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional
      (by omega) hcard hα2 with
    ⟨g, a, hαg⟩ | ⟨e', he', hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, hαb⟩
  · exact absurd (CFSG.GH74.GLS.IVK.Proofs2.ivk93res_inner_of_diag hαg) hnot
  · exfalso
    have h3 : 3 ^ f = 3 ^ (2 * e') := by rw [← hcard, hKe, ← pow_mul, mul_comm]
    have h4 : f = 2 * e' := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
    obtain ⟨k, hk⟩ := hodd
    omega
  · have hb : 1 ≤ b := by omega
    have hK' : Nat.card F = 3 ^ (2 * b + 1) := hfb ▸ hcard
    have hα' : (MulAut.conj g * CFSG.LieType.Ree.ReeTag.G2.finiteReeAut F b) ^ 2 = 1 := hαb ▸ hα2
    obtain ⟨Ψ'⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.g2_ree_fixed_equiv hK' hα'
    have hfix := congrArg CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub hαb
    let Θ := Ψ.trans ((MulEquiv.subgroupCongr hfix).trans Ψ')
    intro u hu
    have hu' : orderOf (Θ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hd := (GenLocRee.reeGamma_datum hb hK' (Θ u) hu').map_equiv Θ.symm
    rw [MulEquiv.symm_apply_apply] at hd
    rw [hfb]
    exact hd

end Datum

theorem psl2_card_facts {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 f)) * 2 =
        3 ^ f * ((3 ^ f) ^ 2 - 1) ∧
      2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 f)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 f) = 3 ^ f := GaloisField.card 3 f (by omega)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 f)) :=
    ⟨3, f, Nat.prime_three, by decide, hf, hK⟩
  have hc := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 f) hodd
  rw [hK] at hc
  have h9 : (3 ^ f) ^ 2 = 9 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hmod : 9 ^ f ≡ 1 [MOD 8] := by
    have := Nat.ModEq.pow f (show 9 ≡ 1 [MOD 8] by decide)
    simpa using this
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 hmod.symm
  rw [h9, hk] at hc
  have hc' : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 f)) =
      3 ^ f * (4 * k) := by
    rw [hc, show 3 ^ f * (8 * k) = 2 * (3 ^ f * (4 * k)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hc', h9, hk]; ring
  · rw [hc']; exact ⟨3 ^ f * (2 * k), by ring⟩

theorem isQuasisimple_I₁ {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    (S : Shape Y F₁ F₂) (h4 : 4 ≤ Nat.card F₁) : CFSG.IsQuasisimple ↥S.I₁ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4)

theorem isQuasisimple_I₂ {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₂]
    (S : Shape Y F₁ F₂) (h4 : 4 ≤ Nat.card F₂) : CFSG.IsQuasisimple ↥S.I₂ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₂.symm (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4)


section StableJ


variable {J : Type} [Group J] [Finite J] {f : ℕ}

theorem false_of_stable_J (hf : 3 ≤ f) (hodd : Odd f) (hJ : LieModel J .G2 0 3 f)
    {σ : MulAut J} (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : J →* MulAut J).range)
    {v : J} (hv2 : orderOf v = 2) (hσv : σ v = v)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3 ^ f)
    (S : Shape ↥(centralizer ({v} : Set J)) F F) (hSz : (S.z : J) = v)
    (hst₁ : ∀ x ∈ S.I₁, resAut σ v hσv x ∈ S.I₁) (hst₂ : ∀ y ∈ S.I₂, resAut σ v hσv y ∈ S.I₂) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq₁ := isQuasisimple_I₁ S h4
  set J₀ := fixedIn J (Subgroup.zpowers σ) with hJ₀
  have hvJ₀ : v ∈ J₀ := (GenLocG2Basic.mem_fixedIn_zpowers σ v).2 hσv
  set u : ↥J₀ := ⟨v, hvJ₀⟩ with hu
  have hu2 : orderOf u = 2 := by rw [hu, Subgroup.orderOf_mk]; exact hv2
  obtain ⟨F0, hF0c, huF0, hcent0, ⟨iso⟩⟩ :=
    g2_outer_fixed_datum hf hodd hJ hσ hout u hu2
  set Φ' : Subgroup J := F0.map J₀.subtype with hΦ'
  have hΦ'C : Φ' ≤ centralizer ({v} : Set J) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hF0c hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  set Φ : Subgroup ↥(centralizer ({v} : Set J)) := Φ'.subgroupOf (centralizer ({v} : Set J)) with hΦ
  have isoΦ : ↥Φ ≃* PSL(2, GaloisField 3 f) :=
    (Subgroup.subgroupOfEquivOfLe hΦ'C).trans
      ((F0.equivMapOfInjective J₀.subtype J₀.subtype_injective).symm.trans iso)
  have hPSLsimple : IsSimpleGroup (PSL(2, GaloisField 3 f)) := by
    have h4' : 4 ≤ Nat.card (GaloisField 3 f) := by
      rw [GaloisField.card 3 f (by omega)]
      calc 4 ≤ 3 ^ 3 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4'
  have hPSLperf : Group.IsPerfect (PSL(2, GaloisField 3 f)) := by
    refine CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three _ ?_
    rw [GaloisField.card 3 f (by omega)]
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hΦsimple : IsSimpleGroup ↥Φ := isoΦ.isSimpleGroup
  have hΦperf : Group.IsPerfect ↥Φ := by
    have : Group.IsPerfect (PSL(2, GaloisField 3 f)) := hPSLperf
    exact Group.IsPerfect.ofSurjective (f := isoΦ.symm.toMonoidHom) isoΦ.symm.surjective
  obtain ⟨hcardΦ, hevenΦ⟩ := psl2_card_facts (f := f) (by omega)
  have hΦcard : Nat.card ↥Φ = Nat.card (PSL(2, GaloisField 3 f)) := Nat.card_congr isoΦ.toEquiv
  have hI₁card : Nat.card ↥S.I₁ = 3 ^ f * ((3 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr S.e₁.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hF]
  have hzΦ : S.z ∉ Φ := by
    intro h
    obtain ⟨x, hx, hxz⟩ := (show (S.z : J) ∈ Φ' from h)
    apply huF0
    have : x = u := Subtype.ext (hxz.trans hSz)
    rwa [← this]
  have hΦfix : ∀ a ∈ Φ, resAut σ v hσv a = a := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := (show (a : J) ∈ Φ' from ha)
    have hσx : σ (x : J) = x := (GenLocG2Basic.mem_fixedIn_zpowers σ x).1 x.2
    apply Subtype.ext
    rw [resAut_apply]
    have : (x : J) = (a : J) := hxa
    rw [← this, hσx]
  have hcard : Nat.card ↥S.I₁ = 2 * Nat.card ↥Φ := by
    rw [hI₁card, hΦcard, ← hcardΦ, mul_comm]
  have hΦeven : 2 ∣ Nat.card ↥Φ := hΦcard ▸ hevenΦ
  have hcent : ∀ y : ↥(centralizer ({v} : Set J)), resAut σ v hσv y = y →
      y ∈ zpowers S.z ⊔ Φ := by
    intro y hy
    have hσy : σ (y : J) = y := by
      have := congrArg Subtype.val hy
      rwa [resAut_apply] at this
    have hgc : (⟨(y : J), (GenLocG2Basic.mem_fixedIn_zpowers σ _).2 hσy⟩ : ↥J₀) ∈
        centralizer ({u} : Set ↥J₀) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [hcent0] at hgc
    have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ F0, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hbu : Commute b u := Subgroup.mem_centralizer_singleton_iff.1 (hF0c hb)
      exact (hbu.zpow_right k).symm.eq
    obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_sup_of_commute hcomm hgc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hbΦ' : (b : J) ∈ Φ' := ⟨b, hb, rfl⟩
    have hbC : (b : J) ∈ centralizer ({v} : Set J) := hΦ'C hbΦ'
    have hyeq : y = S.z ^ k * ⟨(b : J), hbC⟩ := by
      apply Subtype.ext
      have h1 : ((u ^ k * b : ↥J₀) : J) = (y : J) := congrArg Subtype.val hab
      rw [← h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow, hSz]
      rfl
    rw [hyeq]
    exact mul_mem (Subgroup.mem_sup_left (zpow_mem (Subgroup.mem_zpowers S.z) k))
      (Subgroup.mem_sup_right (show (⟨(b : J), hbC⟩ : ↥(centralizer ({v} : Set J))) ∈ Φ from hbΦ'))
  exact false_of_stable S hq₁ (resAut σ v hσv) hst₁ hst₂ Φ hΦfix hΦsimple hΦperf hΦeven hzΦ
    hcard hcent

end StableJ

section Aut
variable {J : Type} [Group J]

theorem mem_fixedIn_pair {x y : MulAut J} {g : J} (hx : x g = g) (hy : y g = g) :
    g ∈ fixedIn J (zpowers x ⊔ zpowers y) := by
  intro φ hφ
  have hle : zpowers x ⊔ zpowers y ≤ MulAction.stabilizer (MulAut J) g :=
    sup_le (zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hx))
      (zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hy))
  simpa using MulAction.mem_stabilizer_iff.1 (hle hφ)

theorem aut_mul_conj (σ : MulAut J) (b : J) :
    σ * MulAut.conj b = MulAut.conj (σ b) * σ := by
  ext x
  simp [MulAut.conj_apply]

theorem pRank_le_three {H : Type} [Group H] [Finite H] (hH : Nat.card H ≤ 8) : pRank 2 H ≤ 3 := by
  refine csSup_le' ?_
  rintro r ⟨A, -, hA⟩
  have h1 := Subgroup.card_le_card_group A
  rw [hA] at h1
  by_contra h
  push Not at h
  have h2 : 2 ^ 4 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem card_inn_sup_le [Finite J] (V₀ : Subgroup J) (hV4 : Nat.card ↥V₀ = 4) (σ : MulAut J)
    (hσ : σ * σ = 1) (hfix : ∀ v ∈ V₀, σ v = v) :
    Nat.card ↥(V₀.map (MulAut.conj : J →* MulAut J) ⊔ zpowers σ) ≤ 8 := by
  have hcomm : ∀ a ∈ V₀.map (MulAut.conj : J →* MulAut J), ∀ s ∈ zpowers σ, a * s = s * a := by
    rintro _ ⟨b, hb, rfl⟩ s hs
    have hc : σ * MulAut.conj b = MulAut.conj b * σ := by rw [aut_mul_conj, hfix b hb]
    rcases mem_zpowers_of_sq hσ hs with rfl | rfl
    · simp
    · exact hc.symm
  let F : ↥V₀ × Fin 2 → ↥(V₀.map (MulAut.conj : J →* MulAut J) ⊔ zpowers σ) := fun p =>
    ⟨MulAut.conj (p.1 : J) * σ ^ (p.2 : ℕ), mul_mem
      (mem_sup_left (mem_map_of_mem _ p.1.2))
      (pow_mem (mem_sup_right (mem_zpowers σ)) _)⟩
  have hsurj : Function.Surjective F := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, s, hs, rfl⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_sup_of_commute hcomm hd
    obtain ⟨b, hb, rfl⟩ := ha
    rcases mem_zpowers_of_sq hσ hs with rfl | rfl
    · exact ⟨(⟨b, hb⟩, 0), Subtype.ext (by simp [F])⟩
    · exact ⟨(⟨b, hb⟩, 1), Subtype.ext (by simp [F])⟩
  have := Nat.card_le_card_of_surjective F hsurj
  rw [Nat.card_prod, hV4, Nat.card_fin] at this
  omega

end Aut

section Nonab
variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

theorem I₁_nonabelian (hq₁ : CFSG.IsQuasisimple ↥S.I₁) : ∃ a ∈ S.I₁, ∃ b ∈ S.I₁, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hperf : ⁅S.I₁, S.I₁⁆ = S.I₁ := Subgroup.isPerfect_iff.mp hq₁.1
  have hbot : ⁅S.I₁, S.I₁⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcon a ha b hb)
  rw [hbot] at hperf
  have := S.z_mem₁
  rw [← hperf] at this
  exact S.z_ne (Subgroup.mem_bot.1 this)

end Nonab

section Rank2

variable {J : Type} [Group J] [Finite J]

theorem fixedIn_pair_le {D : Subgroup (MulAut J)} (hD3 : pRank 2 ↥D ≤ 3) {x y : MulAut J}
    (hxD : x ∈ D) (hyD : y ∈ D) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x ≠ y) (hc : x * y = y * x) : fixedIn J (zpowers x ⊔ zpowers y) ≤ gammaSub J D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  obtain ⟨hcl, hEA, hcard⟩ := CFSG.GH74.Generic.BProg.B1.PilotS5.closure_pair_facts hxo hyo hc hxy
  have hle : zpowers x ⊔ zpowers y ≤ D := sup_le (zpowers_le.2 hxD) (zpowers_le.2 hyD)
  have hrank : pRank 2 ↥D - 1 ≤ pRank 2 ↥(zpowers x ⊔ zpowers y) := by
    have h2 : pRank 2 ↥(zpowers x ⊔ zpowers y) = 2 := by
      rw [← hcl]
      exact CFSG.pRank_eq_of_card_eq_pow one_lt_two (by rw [hcard]; norm_num)
    omega
  exact le_iSup₂_of_le (zpowers x ⊔ zpowers y) hle (le_iSup_of_le hrank le_rfl)

end Rank2

section Center

variable {J : Type} [Group J]

theorem g2_center_trivial_of_shape (hJs : IsSimpleGroup J) {v : J}
    {F : Type} [Field F] (S : Shape ↥(centralizer ({v} : Set J)) F F)
    (hq₁ : CFSG.IsQuasisimple ↥S.I₁) : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
  intro z hz
  have hcen : Subgroup.center J = ⊥ := by
    rcases hJs.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := I₁_nonabelian S hq₁
      apply hab
      apply Subtype.ext
      have : ((a : ↥(centralizer ({v} : Set J))) : J) ∈ Subgroup.center J := by rw [h]; trivial
      have h' := (Subgroup.mem_center_iff.1 this) (b : J)
      simpa using h'.symm
  have : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g => hz g
  rw [hcen] at this
  exact Subgroup.mem_bot.1 this

end Center

section Main


variable {J : Type} [Group J] [Finite J] {f : ℕ}

theorem g2_centralizer_le_gammaSub_outer_of_L3
    (hL3 : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 ^ f →
      ∀ A B : SL(2, F), orderOf A = 4 → orderOf B = 4 → IsConj A B)
    (hf : 3 ≤ f) (hodd : Odd f) (hJ : LieModel J .G2 0 3 f)
    {σ : MulAut J} (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : J →* MulAut J).range)
    {V₀ : Subgroup J} (hV : CFSG.IsElementaryAbelian 2 ↥V₀) (hV4 : Nat.card ↥V₀ = 4)
    (hfix : ∀ v ∈ V₀, σ v = v) {v : J} (hv : v ∈ V₀) (hv1 : v ≠ 1) :
    centralizer ({v} : Set J) ≤
      gammaSub J (V₀.map (MulAut.conj : J →* MulAut J) ⊔ Subgroup.zpowers σ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut J) := MulEquiv.finite_left
  obtain ⟨hab, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hV
  have hv2 : orderOf v = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hsq v hv) hv1
  obtain ⟨w, hw, hw1, hwv⟩ : ∃ w ∈ V₀, w ≠ 1 ∧ w ≠ v := by
    obtain ⟨t, ht, u, hu, ht1, hu1, htu⟩ := GenLocBasic.exists_two_ne_one (B := V₀) (by omega)
    by_cases htv : t = v
    · exact ⟨u, hu, hu1, fun h => htu (htv ▸ h.symm)⟩
    · exact ⟨t, ht, ht1, htv⟩
  obtain ⟨F, _, _, S, hF, hSz⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 Nat.prime_three (by norm_num) hJ v hv2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 ≤ 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq₁ := isQuasisimple_I₁ S h4
  have hq₂ := isQuasisimple_I₂ S h4
  have hJs : IsSimpleGroup J :=
    (CFSG.LieType.Simplicity.fam_g2_simplicity J 3 f
      (CFSG.GH74.GLS.IVK.chevalleyExceptionalModel_of_lieModel_G2 hJ)).2
  have hZ := g2_center_trivial_of_shape hJs S hq₁
  have hinj : Function.Injective (MulAut.conj : J →* MulAut J) :=
    GenLocBasic.conj_injective_of_center_trivial hZ
  have hDfin : Finite (MulAut J) := inferInstance
  have hD3 : pRank 2 ↥(V₀.map (MulAut.conj : J →* MulAut J) ⊔ zpowers σ) ≤ 3 :=
    pRank_le_three (card_inn_sup_le V₀ hV4 σ hσ hfix)
  have hconj2 : ∀ b ∈ V₀, MulAut.conj b * MulAut.conj b = (1 : MulAut J) := fun b hb => by
    rw [← map_mul, hsq b hb, map_one]
  have hconj1 : ∀ b ∈ V₀, b ≠ 1 → (MulAut.conj b : MulAut J) ≠ 1 := fun b hb hb1 h =>
    hb1 (hinj (h.trans (map_one _).symm))
  have hσ1 : σ ≠ 1 := fun h => hout ⟨1, by rw [h, map_one]⟩
  have hσconj : ∀ b ∈ V₀, σ * MulAut.conj b = MulAut.conj b * σ := fun b hb => by
    rw [aut_mul_conj, hfix b hb]
  have hDc : ∀ b ∈ V₀, (MulAut.conj b : MulAut J) ∈
      V₀.map (MulAut.conj : J →* MulAut J) ⊔ zpowers σ := fun b hb =>
    mem_sup_left (mem_map_of_mem _ hb)
  have hDσ : σ ∈ V₀.map (MulAut.conj : J →* MulAut J) ⊔ zpowers σ :=
    mem_sup_right (mem_zpowers σ)
  have hcomm_conj : ∀ a ∈ V₀, ∀ b ∈ V₀, (MulAut.conj a : MulAut J) * MulAut.conj b =
      MulAut.conj b * MulAut.conj a := fun a ha b hb => by
    rw [← map_mul, ← map_mul, hab a ha b hb]
  have P1 := fixedIn_pair_le hD3 (hDc v hv) hDσ (hconj2 v hv) hσ (hconj1 v hv hv1) hσ1
    (fun h => hout ⟨v, h⟩) (hσconj v hv).symm
  have hy2 : (MulAut.conj w * σ) * (MulAut.conj w * σ) = (1 : MulAut J) := by
    calc (MulAut.conj w * σ) * (MulAut.conj w * σ)
        = MulAut.conj w * (σ * MulAut.conj w) * σ := by simp only [mul_assoc]
      _ = MulAut.conj w * (MulAut.conj w * σ) * σ := by rw [hσconj w hw]
      _ = (MulAut.conj w * MulAut.conj w) * (σ * σ) := by simp only [mul_assoc]
      _ = 1 := by rw [hconj2 w hw, hσ, one_mul]
  have hy1 : (MulAut.conj w * σ : MulAut J) ≠ 1 := by
    intro h
    apply hout
    refine ⟨w⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hyx : (MulAut.conj v : MulAut J) ≠ MulAut.conj w * σ := by
    intro h
    apply hout
    refine ⟨w⁻¹ * v, ?_⟩
    rw [map_mul, map_inv, h]
    group
  have hcy : (MulAut.conj v : MulAut J) * (MulAut.conj w * σ) = (MulAut.conj w * σ) * MulAut.conj v := by
    calc MulAut.conj v * (MulAut.conj w * σ) = (MulAut.conj v * MulAut.conj w) * σ := by
          simp only [mul_assoc]
      _ = (MulAut.conj w * MulAut.conj v) * σ := by rw [hcomm_conj v hv w hw]
      _ = MulAut.conj w * (MulAut.conj v * σ) := by simp only [mul_assoc]
      _ = MulAut.conj w * (σ * MulAut.conj v) := by rw [hσconj v hv]
      _ = (MulAut.conj w * σ) * MulAut.conj v := by simp only [mul_assoc]
  have P2 := fixedIn_pair_le hD3 (hDc v hv) (mul_mem (hDc w hw) hDσ) (hconj2 v hv) hy2
    (hconj1 v hv hv1) hy1 hyx hcy
  have P3 := fixedIn_pair_le hD3 (hDc v hv) (hDc w hw) (hconj2 v hv) (hconj2 w hw)
    (hconj1 v hv hv1) (hconj1 w hw hw1) (fun h => hwv (hinj h).symm) (hcomm_conj v hv w hw)
  have hσv : σ v = v := hfix v hv
  have hwC : w ∈ centralizer ({v} : Set J) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hab w hw v hv)
  have hconjC : ∀ y : ↥(centralizer ({v} : Set J)), (MulAut.conj v : MulAut J) (y : J) = y := by
    intro y
    have := Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact this.symm
  rcases stable_or_swap S hq₁ hq₂ (resAut σ v hσv) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (false_of_stable_J hf hodd hJ hσ hout hv2 hσv hF S hSz h1 h2).elim
  · have hwz : (⟨w, hwC⟩ : ↥(centralizer ({v} : Set J))) ∉ zpowers S.z := by
      intro hmem
      rcases mem_zpowers_of_sq S.z_sq hmem with h | h
      · exact hw1 (congrArg Subtype.val h)
      · exact hwv ((congrArg Subtype.val h).trans hSz)
    obtain ⟨G1, hG1⟩ : ∃ G1 : Subgroup ↥(centralizer ({v} : Set J)), G1 =
        (fixedIn J (zpowers (MulAut.conj v) ⊔ zpowers σ)).comap (centralizer ({v} : Set J)).subtype :=
      ⟨_, rfl⟩
    obtain ⟨G2, hG2⟩ : ∃ G2 : Subgroup ↥(centralizer ({v} : Set J)), G2 =
        (fixedIn J (zpowers (MulAut.conj v) ⊔ zpowers (MulAut.conj w * σ))).comap
          (centralizer ({v} : Set J)).subtype := ⟨_, rfl⟩
    obtain ⟨G3, hG3⟩ : ∃ G3 : Subgroup ↥(centralizer ({v} : Set J)), G3 =
        (fixedIn J (zpowers (MulAut.conj v) ⊔ zpowers (MulAut.conj w))).comap
          (centralizer ({v} : Set J)).subtype := ⟨_, rfl⟩
    have hT := twist_gen S (hL3 F hF) (hL3 F hF) hq₁ hq₂ (resAut σ v hσv) h1 h2
      (resAut_resAut σ hσ v hσv) (w := ⟨w, hwC⟩) (Subtype.ext (hsq w hw))
      (Subtype.ext (hfix w hw)) hwz (G1 := G1) (G2 := G2) (G3 := G3)
      (fun y hy => hG1 ▸ mem_fixedIn_pair (hconjC y) (by
        have := congrArg Subtype.val hy
        rwa [resAut_apply] at this))
      (fun y hy => hG2 ▸ mem_fixedIn_pair (hconjC y) (by
        have := congrArg Subtype.val hy
        simpa [resAut_apply, MulAut.conj_apply] using this))
      (fun y hy => hG3 ▸ mem_fixedIn_pair (hconjC y) (by
        have := congrArg Subtype.val hy
        simp only [Subgroup.coe_mul] at this
        rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
        exact this))
    intro g hg
    have hg' : (⟨g, hg⟩ : ↥(centralizer ({v} : Set J))) ∈ G1 ⊔ G2 ⊔ G3 := by rw [hT]; trivial
    have hmap := Subgroup.mem_map_of_mem (centralizer ({v} : Set J)).subtype hg'
    rw [Subgroup.map_sup, Subgroup.map_sup] at hmap
    refine (sup_le (sup_le ?_ ?_) ?_ : _ ≤ gammaSub J _) hmap
    · rw [hG1]; exact (Subgroup.map_comap_le _ _).trans P1
    · rw [hG2]; exact (Subgroup.map_comap_le _ _).trans P2
    · rw [hG3]; exact (Subgroup.map_comap_le _ _).trans P3


theorem _root_.CFSG.GH74.Generic.BProg.B2.g2_centralizer_le_gammaSub_outer
    (hf : 3 ≤ f) (hodd : Odd f) (hJ : LieModel J .G2 0 3 f)
    {σ : MulAut J} (hσ : σ * σ = 1) (hout : σ ∉ (MulAut.conj : J →* MulAut J).range)
    {V₀ : Subgroup J} (hV : CFSG.IsElementaryAbelian 2 ↥V₀) (hV4 : Nat.card ↥V₀ = 4)
    (hfix : ∀ v ∈ V₀, σ v = v) {v : J} (hv : v ∈ V₀) (hv1 : v ≠ 1) :
    centralizer ({v} : Set J) ≤
      gammaSub J (V₀.map (MulAut.conj : J →* MulAut J) ⊔ Subgroup.zpowers σ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact g2_centralizer_le_gammaSub_outer_of_L3
    (fun F _ _ hF A B hA hB => sl2_order_four_isConj hF (by norm_num) hA hB) hf hodd hJ hσ hout
    hV hV4 hfix hv hv1

end Main

end GenLocG2Outer

end CFSG.GH74.Generic.BProg.B2
