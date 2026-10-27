module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcLines
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement Matrix

section Group

variable {G : Type*} [Group G]

theorem tw_mem_sylow_of_commute {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G} {k : ℕ}
    (hx : x ^ p ^ k = 1) (hc : ∀ s ∈ (P : Subgroup G), s * x = x * s) :
    x ∈ (P : Subgroup G) := by
  have hz : IsPGroup p (Subgroup.zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx
  have hnorm : (P : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro s hs
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
    exact ((Commute.zpow_right (show Commute s x from hc s hs) i).eq).symm
  have hQ : IsPGroup p ((P : Subgroup G) ⊔ Subgroup.zpowers x : Subgroup G) :=
    P.isPGroup'.to_sup_of_normal_right' hz hnorm
  have hQeq : ((P : Subgroup G) ⊔ Subgroup.zpowers x : Subgroup G) = (P : Subgroup G) :=
    P.is_maximal' hQ le_sup_left
  rw [← hQeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem tw_pow_eq_one_of_card_eq_prime {p : ℕ} {A : Subgroup G} (hA : Nat.card A = p) {x : G}
    (hx : x ∈ A) : x ^ p = 1 := by
  have := pow_card_eq_one' (G := A) (x := ⟨x, hx⟩)
  rw [hA] at this
  exact congrArg Subtype.val this

theorem tw_commutator_mem_normalizer {S : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (S : Set G)) (hb : b ∈ Subgroup.normalizer (S : Set G)) :
    ⁅a, b⁆ ∈ Subgroup.normalizer (S : Set G) := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem exists_tw_dc_moves_line {p : ℕ} [Fact p.Prime] {Γ S A : Subgroup G} (hAS : A ≤ S)
    (hA : Nat.card A = p) {c₁ c₂ c₃ c₄ : G}
    (h₁ : c₁ ∈ Subgroup.normalizer (S : Set G)) (h₂ : c₂ ∈ Subgroup.normalizer (S : Set G))
    (h₃ : c₃ ∈ Subgroup.normalizer (S : Set G)) (h₄ : c₄ ∈ Subgroup.normalizer (S : Set G))
    (hΓ₁ : ⁅c₁, c₂⁆ ∈ Γ) (hΓ₂ : ⁅c₃, c₄⁆ ∈ Γ)
    (hfpf : ∀ x ∈ S, x ^ p = 1 → ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆ * x * ⁅⁅c₁, c₂⁆, ⁅c₃, c₄⁆⁆⁻¹ = x → x = 1) :
    ∃ n : G, n ∈ Γ ∧ n ∈ Subgroup.normalizer (S : Set G) ∧
      A.map (MulAut.conj n).toMonoidHom ≠ A := by
  have hmove := exists_not_normalizes_of_doubleCommutator_fpf (p := p) (E := A) (A := A) le_rfl hA
    (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (c₄ := c₄)
    (fun x hx hxu => hfpf x (hAS hx) (tw_pow_eq_one_of_card_eq_prime hA hx) hxu)
  rcases hmove with h | h
  · exact ⟨⁅c₁, c₂⁆, hΓ₁, tw_commutator_mem_normalizer h₁ h₂, h⟩
  · exact ⟨⁅c₃, c₄⁆, hΓ₂, tw_commutator_mem_normalizer h₃ h₄, h⟩

theorem exists_tw_sc_moves_line {p : ℕ} [Fact p.Prime] {Γ S A : Subgroup G} (hAS : A ≤ S)
    (hA : Nat.card A = p) {c₁ c₂ : G} (hΓ₁ : c₁ ∈ Γ) (hΓ₂ : c₂ ∈ Γ)
    (h₁ : c₁ ∈ Subgroup.normalizer (S : Set G)) (h₂ : c₂ ∈ Subgroup.normalizer (S : Set G))
    (hfpf : ∀ x ∈ S, x ^ p = 1 → ⁅c₁, c₂⁆ * x * ⁅c₁, c₂⁆⁻¹ = x → x = 1) :
    ∃ n : G, n ∈ Γ ∧ n ∈ Subgroup.normalizer (S : Set G) ∧
      A.map (MulAut.conj n).toMonoidHom ≠ A := by
  have hmove := exists_not_normalizes_of_commutator_fpf (p := p) (E := A) (A := A) le_rfl hA
    (c₁ := c₁) (c₂ := c₂)
    (fun x hx hxu => hfpf x (hAS hx) (tw_pow_eq_one_of_card_eq_prime hA hx) hxu)
  rcases hmove with h | h
  · exact ⟨c₁, hΓ₁, h₁, h⟩
  · exact ⟨c₂, hΓ₂, h₂, h⟩

theorem exists_mem_normalizer_move_of_ambient' {Γ : Subgroup G} {S₀ A : Subgroup Γ} {n : G}
    (hnΓ : n ∈ Γ) (hn : n ∈ Subgroup.normalizer ((S₀.map Γ.subtype : Subgroup G) : Set G))
    (hmove : (A.map Γ.subtype).map (MulAut.conj n).toMonoidHom ≠ A.map Γ.subtype) :
    ∃ m ∈ Subgroup.normalizer (S₀ : Set Γ), A.map (MulAut.conj m).toMonoidHom ≠ A := by
  refine ⟨⟨n, hnΓ⟩, ?_, fun heq => hmove ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 hn (x : G)
    have e1 : (x ∈ S₀) ↔ ((x : G) ∈ S₀.map Γ.subtype) :=
      (Subgroup.mem_map_iff_mem Γ.subtype_injective).symm
    have e2 : (⟨n, hnΓ⟩ * x * ⟨n, hnΓ⟩⁻¹ ∈ S₀) ↔
        (((⟨n, hnΓ⟩ * x * ⟨n, hnΓ⟩⁻¹ : Γ) : G) ∈ S₀.map Γ.subtype) :=
      (Subgroup.mem_map_iff_mem Γ.subtype_injective).symm
    rw [e1, e2]
    exact h1
  · ext g
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have : (⟨n, hnΓ⟩ * a * ⟨n, hnΓ⟩⁻¹ : Γ) ∈ A.map (MulAut.conj (⟨n, hnΓ⟩ : Γ)).toMonoidHom :=
        ⟨a, ha, by simp [MulAut.conj_apply]⟩
      rw [heq] at this
      exact ⟨_, this, by simp⟩
    · rintro ⟨a, ha, rfl⟩
      have hn' : (⟨n, hnΓ⟩⁻¹ * a * ⟨n, hnΓ⟩ : Γ) ∈ A := by
        have : a ∈ A.map (MulAut.conj (⟨n, hnΓ⟩ : Γ)).toMonoidHom := by rw [heq]; exact ha
        obtain ⟨b, hb, hba⟩ := this
        have : b = ⟨n, hnΓ⟩⁻¹ * a * ⟨n, hnΓ⟩ := by
          rw [← hba]; simp [MulAut.conj_apply, mul_assoc]
        rw [← this]; exact hb
      refine ⟨_, ⟨(⟨n, hnΓ⟩⁻¹ * a * ⟨n, hnΓ⟩ : Γ), hn', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

end Group

section Model

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
  (D : LangDatum τ L)

theorem tw_mem_model {y : ModGL τ L} (hy : y ∈ monomialSubgroup τ L)
    (hf : D.n * D.Φ y * D.n⁻¹ = y) : y ∈ D.model :=
  ⟨monomialSubgroup_le_adjointGroup' hy, hf⟩

theorem tw_Γ_le_model : D.Γ ≤ D.model := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem tw_model_conj_mem_Γ {y g : ModGL τ L} (hy : y ∈ D.model) (hg : g ∈ D.Γ) :
    y * g * y⁻¹ ∈ D.Γ := by
  have hgM : g ∈ D.model := tw_Γ_le_model D hg
  have h := (commutator_subgroupOf_normal D.model).conj_mem ⟨g, hgM⟩
    (Subgroup.mem_subgroupOf.2 hg) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem tw_commutator_mem_Γ {y₁ y₂ : ModGL τ L} (h₁ : y₁ ∈ D.model) (h₂ : y₂ ∈ D.model) :
    ⁅y₁, y₂⁆ ∈ D.Γ :=
  Subgroup.commutator_mem_commutator h₁ h₂

theorem tw_conj_mem_torus {y t : ModGL τ L} (hy : y ∈ monomialSubgroup τ L)
    (hf : D.n * D.Φ y * D.n⁻¹ = y) (ht : t ∈ D.torus) : y * t * y⁻¹ ∈ D.torus := by
  obtain ⟨ht1, ht2⟩ := mem_twistedTorusOf.1 ht
  refine mem_twistedTorusOf.2 ⟨?_, ?_⟩
  · have htm : t ∈ monomialSubgroup τ L := torusGroup_le_monomialSubgroup' ht1
    have h := (inferInstance :
      ((torusGroup τ L).subgroupOf (monomialSubgroup τ L)).Normal).conj_mem
      ⟨t, htm⟩ (Subgroup.mem_subgroupOf.2 ht1) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 h
  · have e : D.n * D.Φ (y * t * y⁻¹) * D.n⁻¹ =
        (D.n * D.Φ y * D.n⁻¹) * (D.n * D.Φ t * D.n⁻¹) * (D.n * D.Φ y * D.n⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e, hf, ht2]

variable {p : ℕ} [Fact p.Prime]

theorem tw_conj_mem_sylow (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {y : ModGL τ L}
    (hy : y ∈ monomialSubgroup τ L) (hf : D.n * D.Φ y * D.n⁻¹ = y) {s : ModGL τ L}
    (hs : s ∈ (S₀ : Subgroup D.Γ).map D.Γ.subtype) :
    y * s * y⁻¹ ∈ (S₀ : Subgroup D.Γ).map D.Γ.subtype := by
  obtain ⟨s', hs'S, rfl⟩ := hs
  have hyM : y ∈ D.model := tw_mem_model D hy hf
  have hs'T : (s' : ModGL τ L) ∈ D.torus := Subgroup.mem_subgroupOf.1 (hS₀ hs'S)
  have hzT : y * (s' : ModGL τ L) * y⁻¹ ∈ D.torus := tw_conj_mem_torus D hy hf hs'T
  have hzΓ : y * (s' : ModGL τ L) * y⁻¹ ∈ D.Γ := tw_model_conj_mem_Γ D hyM s'.2
  set z : D.Γ := ⟨y * (s' : ModGL τ L) * y⁻¹, hzΓ⟩ with hz
  obtain ⟨k, hk⟩ := S₀.isPGroup' ⟨s', hs'S⟩
  have hs'k : (s' : ModGL τ L) ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using congrArg Subtype.val this
  have hzk : z ^ p ^ k = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hz]
    rw [conj_pow, hs'k]
    simp
  have hcomm : ∀ t ∈ (S₀ : Subgroup D.Γ), t * z = z * t := by
    intro t ht
    have htT : (t : ModGL τ L) ∈ D.torus := Subgroup.mem_subgroupOf.1 (hS₀ ht)
    apply Subtype.ext
    exact torusGroup_mul_comm (mem_twistedTorusOf.1 htT).1 (mem_twistedTorusOf.1 hzT).1
  exact ⟨z, tw_mem_sylow_of_commute S₀ hzk hcomm, rfl⟩

theorem tw_mem_normalizer_sylow (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {y : ModGL τ L}
    (hy : y ∈ monomialSubgroup τ L) (hf : D.n * D.Φ y * D.n⁻¹ = y) :
    y ∈ Subgroup.normalizer (((S₀ : Subgroup D.Γ).map D.Γ.subtype : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := by
  have hyinv : y⁻¹ ∈ monomialSubgroup τ L := inv_mem hy
  have hfinv : D.n * D.Φ y⁻¹ * D.n⁻¹ = y⁻¹ := by
    rw [map_inv]
    calc D.n * (D.Φ y)⁻¹ * D.n⁻¹ = (D.n * D.Φ y * D.n⁻¹)⁻¹ := by group
      _ = y⁻¹ := by rw [hf]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => tw_conj_mem_sylow D S₀ hS₀ hy hf hx, fun hx => ?_⟩
  have h := tw_conj_mem_sylow D S₀ hS₀ hyinv hfinv hx
  simpa [mul_assoc] using h

end Model

section Engine

variable {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L]
  (D : LangDatum t.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
  (hΦ : D.Φ = twistHom t L Fr) {w : WeylGroup t.tag}
  (hn : D.n = canonicalRep (coxeterSystem t.tag) L w)
  {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ} (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x)
  {N : ℕ} (hN0 : N ≠ 0) (hpow : M ^ N = 1)

include hq hFr hΦ hn hv hN0 hpow in
theorem tw_exists_lift {u : WeylGroup t.tag} (hu : w * weylTwist t u = u * w) :
    ∃ y : ModGL t.tag L, y ∈ monomialSubgroup t.tag L ∧ D.n * D.Φ y * D.n⁻¹ = y ∧
      TwActsAs y u := by
  obtain ⟨t₁, ht₁, hf⟩ := exists_twFrob_lift Fr hq hFr w hv hN0 hpow hu
  refine ⟨t₁ * canonicalRep (coxeterSystem t.tag) L u, lift_mem_monomialSubgroup ht₁ u, ?_,
    twActsAs_lift ht₁ u⟩
  rw [hn, hΦ]
  exact hf

include hΦ hn hv in
theorem tw_eq_one_of_fixed {u : WeylGroup t.tag} {p : ℕ}
    (hfpf : ∀ β ∈ fixedCharTuples M Fr, (∀ i, β i ^ p = 1) → weylTuple u β = β → β = 1)
    {y x : ModGL t.tag L} (hy : TwActsAs y u) (hx : x ∈ D.torus) (hxp : x ^ p = 1)
    (hfix : y * x * y⁻¹ = x) : x = 1 := by
  have h := twistedTorusOf_twistHom_eq_map t Fr w M hv
  have hx' : x ∈ twistedTorusOf (canonicalRep (coxeterSystem t.tag) L w) (twistHom t L Fr) := by
    have : x ∈ twistedTorusOf D.n D.Φ := hx
    rwa [hn, hΦ] at this
  rw [h] at hx'
  obtain ⟨β, hβ, rfl⟩ := hx'
  have hinj : ∀ γ : Fin t.tag.rank → Lˣ, rootDiagUnit t.tag γ = 1 → γ = 1 := fun γ h =>
    CFSG.LieType.Chevalley.rootDiagUnit_injective (h.trans (rootDiagUnit_one (K := L)).symm)
  have hβ' : rootDiagUnit t.tag β ^ p = 1 := hxp
  have hβp : ∀ i, β i ^ p = 1 := by
    have hpow : rootDiagUnit t.tag (β ^ p) = rootDiagUnit t.tag β ^ p :=
      map_pow (rootDiagUnitHom t.tag L) β p
    have : β ^ p = 1 := hinj _ (hpow.trans hβ')
    intro i
    exact congrFun this i
  have hfix' : weylTuple u β = β := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := t.tag) (K := L)
    rw [← hy β]
    exact hfix
  have := hfpf β hβ hβp hfix'
  rw [this]
  exact map_one _

include hq hFr hΦ hn hv hN0 hpow in
theorem normalizerMovesLines_of_tw_dc {p : ℕ} [Fact p.Prime] (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {a b c d : WeylGroup t.tag}
    (ha : w * weylTwist t a = a * w) (hb : w * weylTwist t b = b * w)
    (hc : w * weylTwist t c = c * w) (hd : w * weylTwist t d = d * w)
    (hfpf : ∀ β ∈ fixedCharTuples M Fr, (∀ i, β i ^ p = 1) →
      weylTuple ⁅⁅a, b⁆, ⁅c, d⁆⁆ β = β → β = 1) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  obtain ⟨ya, hma, hfa, hca⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow ha
  obtain ⟨yb, hmb, hfb, hcb⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow hb
  obtain ⟨yc, hmc, hfc, hcc⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow hc
  obtain ⟨yd, hmd, hfd, hcd⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow hd
  intro A hA hAcard
  have hA' : A.map D.Γ.subtype ≤ (S₀ : Subgroup D.Γ).map D.Γ.subtype := Subgroup.map_mono hA
  have hA'card : Nat.card (A.map D.Γ.subtype) = p := by
    rw [Subgroup.card_map_of_injective D.Γ.subtype_injective, hAcard]
  have hact : TwActsAs ⁅⁅ya, yb⁆, ⁅yc, yd⁆⁆ ⁅⁅a, b⁆, ⁅c, d⁆⁆ :=
    (hca.commutator hcb).commutator (hcc.commutator hcd)
  obtain ⟨m, hmΓ, hmN, hmove⟩ := exists_tw_dc_moves_line (Γ := D.Γ) hA' hA'card
    (tw_mem_normalizer_sylow D S₀ hS₀ hma hfa) (tw_mem_normalizer_sylow D S₀ hS₀ hmb hfb)
    (tw_mem_normalizer_sylow D S₀ hS₀ hmc hfc) (tw_mem_normalizer_sylow D S₀ hS₀ hmd hfd)
    (tw_commutator_mem_Γ D (tw_mem_model D hma hfa) (tw_mem_model D hmb hfb))
    (tw_commutator_mem_Γ D (tw_mem_model D hmc hfc) (tw_mem_model D hmd hfd))
    (fun x hx hxp hfix => by
      obtain ⟨x', hx'S, rfl⟩ := hx
      exact tw_eq_one_of_fixed D hΦ hn hv hfpf hact (Subgroup.mem_subgroupOf.1 (hS₀ hx'S)) hxp hfix)
  exact exists_mem_normalizer_move_of_ambient' hmΓ hmN hmove

include hq hFr hΦ hn hv hN0 hpow in
theorem normalizerMovesLines_of_tw_sc {p : ℕ} [Fact p.Prime] (hMΓ : D.model ≤ D.Γ)
    (S₀ : Sylow p D.Γ) (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ)
    {a b : WeylGroup t.tag} (ha : w * weylTwist t a = a * w) (hb : w * weylTwist t b = b * w)
    (hfpf : ∀ β ∈ fixedCharTuples M Fr, (∀ i, β i ^ p = 1) → weylTuple ⁅a, b⁆ β = β → β = 1) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  obtain ⟨ya, hma, hfa, hca⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow ha
  obtain ⟨yb, hmb, hfb, hcb⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow hb
  intro A hA hAcard
  have hA' : A.map D.Γ.subtype ≤ (S₀ : Subgroup D.Γ).map D.Γ.subtype := Subgroup.map_mono hA
  have hA'card : Nat.card (A.map D.Γ.subtype) = p := by
    rw [Subgroup.card_map_of_injective D.Γ.subtype_injective, hAcard]
  have hact : TwActsAs ⁅ya, yb⁆ ⁅a, b⁆ := hca.commutator hcb
  obtain ⟨m, hmΓ, hmN, hmove⟩ := exists_tw_sc_moves_line (Γ := D.Γ) hA' hA'card
    (hMΓ (tw_mem_model D hma hfa)) (hMΓ (tw_mem_model D hmb hfb))
    (tw_mem_normalizer_sylow D S₀ hS₀ hma hfa) (tw_mem_normalizer_sylow D S₀ hS₀ hmb hfb)
    (fun x hx hxp hfix => by
      obtain ⟨x', hx'S, rfl⟩ := hx
      exact tw_eq_one_of_fixed D hΦ hn hv hfpf hact (Subgroup.mem_subgroupOf.1 (hS₀ hx'S)) hxp hfix)
  exact exists_mem_normalizer_move_of_ambient' hmΓ hmN hmove

end Engine

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
