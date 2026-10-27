module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosuresExact
import CFSG.LocalAnalysis.SteinbergSFOneAxisInvolutionExclusion
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCQuotientCoset
import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries
import CFSG.LocalAnalysis.SteinbergSFOneAxisWeakClosure
import CFSG.LocalAnalysis.SteinbergSFOneAxisHeisenberg
import CFSG.GroupTheory.SteinbergCBFTHall

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialSlice

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.ComponentInitial (sectionRightConj sectionRightConj_mk
  elementary_quotient_involution_coset_conjugacy coe_closure_range_inv_mul_apply)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐖'[" i "]" =>
  (𝐖[i].map (MulAut.conj 𝐰[Axis.swap i]⁻¹).toMonoidHom : Subgroup G)
local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀" => (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G)

section GenericCoset

variable {G' : Type*} [Group G'] [Finite G']

theorem exists_conj_of_mem_coset_generic {V E : Subgroup G'} (hEV : E ≤ V)
    (hEn : V ≤ normalizer (E : Set G')) (hEsq : ∀ x ∈ E, x * x = 1)
    (hVsq : ∀ v ∈ V, v * v ∈ E) (hVc : ∀ v ∈ V, ∀ w ∈ V, v⁻¹ * w⁻¹ * v * w ∈ E)
    {t : G'} (ht : orderOf t = 2) (htV : t ∈ normalizer (V : Set G'))
    (htE : t ∈ normalizer (E : Set G')) (htV' : t ∉ V)
    (hfix : ∀ v ∈ V, t⁻¹ * v⁻¹ * t * v ∈ E → ∃ y ∈ V, (y⁻¹ * (t⁻¹ * y * t))⁻¹ * v ∈ E)
    (hD : ∀ d ∈ E ⊓ centralizer ({t} : Set G'), ∃ x ∈ E, t * d = x⁻¹ * t * x)
    {y : G'} (hy : ∃ v ∈ V, y = t * v) (hy2 : orderOf y = 2) : ∃ s ∈ V, y = s⁻¹ * t * s := by
  have : (E.subgroupOf V).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (hEn g.2) _).mp hx⟩
  have : IsElementaryAbelian 2 E := isElementaryAbelian_of_mul_self hEsq
  have hQ : IsElementaryAbelian 2 (V ⧸ E.subgroupOf V) :=
    { is_comm := ⟨fun a b => by
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have e : (((v * w)⁻¹ * (w * v) : V) : G') = (w : G')⁻¹ * (v : G')⁻¹ * w * v := by
          simp only [coe_mul, coe_inv]
          group
        rw [e]
        exact hVc w w.2 v v.2⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_pow, sq]
        exact hVsq v v.2 }
  set α := sectionRightConj htV htE with hα
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hfr : {u | α u = u} = Set.range fun u : V ⧸ E.subgroupOf V => u⁻¹ * α u := by
    apply le_antisymm
    · rintro q hq
      obtain ⟨⟨v, hv⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hvt := (CFSG.LocalAnalysis.ComponentInitial.sectionRightConj_mk_eq_iff htV htE
        ⟨v, hv⟩).mp hq
      obtain ⟨z, hzV, hzv⟩ := hfix v hv hvt
      have hz' : t⁻¹ * z * t ∈ V := by
        have := (mem_normalizer_iff.mp (inv_mem htV) z).mp hzV
        rwa [inv_inv] at this
      refine ⟨QuotientGroup.mk ⟨z, hzV⟩, ?_⟩
      change (QuotientGroup.mk ⟨z, hzV⟩ : V ⧸ E.subgroupOf V)⁻¹ * α (QuotientGroup.mk ⟨z, hzV⟩) =
        QuotientGroup.mk ⟨v, hv⟩
      rw [hα, sectionRightConj_mk htV htE ⟨z, hzV⟩ ⟨t⁻¹ * z * t, hz'⟩ rfl,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      simpa only [coe_mul, coe_inv] using hzv
    · rintro _ ⟨q, rfl⟩
      change α (q⁻¹ * α q) = q⁻¹ * α q
      have hinv : ∀ r : V ⧸ E.subgroupOf V, r⁻¹ = r := fun r =>
        inv_eq_of_mul_eq_one_right
          (CFSG.LocalAnalysis.ComponentInitial.mul_self_eq_one_of_isElementaryAbelian_two r)
      rw [map_mul, map_inv, Common.sectionRightConj_sectionRightConj _ _ ht2, hinv, hinv,
        mul_comm' (α q) q]
  rw [← coe_closure_range_inv_mul_apply] at hfr
  have hres := (elementary_quotient_involution_coset_conjugacy hEV ht htV htE htV' hfr).1
  have hmem : y ∈ {x : G' | (∃ v ∈ V, x = t * v) ∧ orderOf x = 2} := ⟨hy, hy2⟩
  rw [hres] at hmem
  obtain ⟨v, hv, d, hd, hyd⟩ := hmem
  obtain ⟨x, hx, hxd⟩ := hD d hd
  refine ⟨x * v, mul_mem (hEV hx) hv, ?_⟩
  rw [hyd, hxd]
  group

omit [Finite G'] in
theorem kappa_comm_t {X : Subgroup G'} (hXsq : ∀ x ∈ X, x * x = 1) {t : G'} (htt : t * t = 1)
    (htX : t ∈ normalizer (X : Set G')) {x : G'} (hx : x ∈ X) :
    t⁻¹ * (x⁻¹ * t * x) * t = t * (t⁻¹ * (x⁻¹ * t * x)) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hXsq x hx)
  have hy : t * x * t ∈ X := by
    have := (mem_normalizer_iff.mp htX x).mp hx
    rwa [hti] at this
  have hc : x * (t * x * t) = (t * x * t) * x := comm_of_mul_self hXsq hx hy
  rw [hti, hxi]
  calc t * (x * t * x) * t = t * (x * (t * x * t)) := by group
    _ = t * ((t * x * t) * x) := by rw [hc]
    _ = t * (t * (x * t * x)) := by group

omit [Finite G'] in
theorem conj_mem_of_sup {H₁ H₂ M : Subgroup G'} {g : G'} (h₁ : ∀ x ∈ H₁, g * x * g⁻¹ ∈ M)
    (h₂ : ∀ x ∈ H₂, g * x * g⁻¹ ∈ M) {x : G'} (hx : x ∈ H₁ ⊔ H₂) : g * x * g⁻¹ ∈ M := by
  have hle : H₁ ⊔ H₂ ≤ M.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun y hy => by simpa using h₁ y hy) fun y hy => by simpa using h₂ y hy
  simpa using hle hx

omit [Finite G'] in
theorem pCore_map_subtype_congr {H H' : Subgroup G'} (e : H = H') :
    (CFSG.pCore 2 H).map H.subtype = (CFSG.pCore 2 H').map H'.subtype := by
  subst e
  rfl

theorem pCore_normalizer_map_conj (g : G') (B : Subgroup G') :
    ((CFSG.pCore 2 (normalizer (B : Set G'))).map (normalizer (B : Set G')).subtype).map
      (MulAut.conj g).toMonoidHom =
    (CFSG.pCore 2 (normalizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup G') : Set G'))).map
      (normalizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup G') : Set G')).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 ↥((MulAut.conj g).toMonoidHom.ker ⊓ normalizer (B : Set G')) := by
    have hk : (MulAut.conj g).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective
    rw [hk, bot_inf_eq]
    exact IsPGroup.of_bot
  rw [CFSG.GroupTheory.FT63ChII.map_pCore_map_subtype _ _ hker]
  exact pCore_map_subtype_congr (Subgroup.map_equiv_normalizer_eq B (MulAut.conj g))

end GenericCoset

theorem conj_not_mem_S (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (g : G) : g⁻¹ * t * g ∉ 𝐒 := by
  intro hx
  set x := g⁻¹ * t * g with hxdef
  have hx2 : x * x = 1 := by
    rw [hxdef, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, h.setup.t_mul_t]
    group
  have hxF : ∀ f ∈ 𝐅, f * x = x * f := fun f hf => (F_comm_S h hbt hf hx).symm
  have hxN : zpowers x ≤ normalizer (𝐅 : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_of_conj_le fun f hf => ?_
    rw [show x * f * x⁻¹ = f by rw [← hxF f hf, mul_inv_cancel_right]]
    exact hf
  set E : Subgroup G := 𝐅 ⊔ zpowers x with hE
  have hEsq : ∀ y ∈ E, y * y = 1 := by
    intro y hy
    rw [hE, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hxN] at hy
    obtain ⟨f, hf, c, hc, rfl⟩ := hy
    have hc' : c = 1 ∨ c = x := by
      obtain ⟨j, rfl⟩ := hc
      exact zpow_eq_one_or_eq hx2 j
    rcases hc' with rfl | rfl
    · simp only [mul_one]
      exact F_mul_self h hbt hf
    · rw [show f * x * (f * x) = f * (x * f) * x by group, ← hxF f hf,
        show f * (f * x) * x = (f * f) * (x * x) by group, F_mul_self h hbt hf, hx2, one_mul]
  have hEel : IsElementaryAbelian 2 E := isElementaryAbelian_of_mul_self hEsq
  set E' : Subgroup G := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'el : IsElementaryAbelian 2 E' := OneAxisWeakClosure.elemAb_map hEel _
  have htE' : t ∈ E' := ⟨x, mem_sup_right (mem_zpowers x), by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxdef]
    group⟩
  have hE'C : E' ≤ 𝐂 := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact comm_of_mul_self (fun z hz => OneAxisWeakClosure.elemAb_mul_self hE'el hz) hy htE'
  have hrank := (OneAxisInvolutionExclusion.rank_le_of_le_centralizer h.setup hE'C hE'el).2
  rw [hE', card_map_of_injective (MulAut.conj g).injective] at hrank
  have hFE : Nat.card 𝐅 ≤ Nat.card E := card_le_of_le le_sup_left
  rw [card_F h, h.setup.card_K, ← pow_mul] at hFE
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hFE.trans hrank)
  have := h.setup.two_le
  omega

theorem exists_conj_of_mem_A (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) {d : G}
    (hd : d ∈ 𝐗[i] ⊓ 𝐂) : ∃ x ∈ 𝐗[i], t * d = x⁻¹ * t * x := by
  have htX := t_mem_normalizer_X h i
  have hU : ∀ x ∈ 𝐗[i], t⁻¹ * (x⁻¹ * t * x) ∈ 𝐀[i] := by
    intro x hx
    rw [← X_inf_C h i]
    have hx' : t⁻¹ * x⁻¹ * t ∈ 𝐗[i] := by
      have := (mem_normalizer_iff.mp (inv_mem htX) x⁻¹).mp (inv_mem hx)
      rwa [inv_inv] at this
    have hcX : t⁻¹ * (x⁻¹ * t * x) ∈ 𝐗[i] := by
      rw [show t⁻¹ * (x⁻¹ * t * x) = (t⁻¹ * x⁻¹ * t) * x by group]
      exact mul_mem hx' hx
    exact ⟨hcX, mem_centralizer_singleton_iff.mpr
      (kappa_comm_t (fun _ hy => X_mul_self h hbt i hy) h.setup.t_mul_t htX hx)⟩
  have hcard : Nat.card 𝐗[i] = Nat.card 𝐀[i] * Nat.card (𝐂 ⊓ 𝐗[i] : Subgroup G) := by
    rw [inf_comm 𝐂 𝐗[i], X_inf_C h i, card_X h i, card_pull, card_rootA, ← pow_add]
  have hdA : d ∈ 𝐀[i] := (X_inf_C h i) ▸ hd
  obtain ⟨x, hx, hxd⟩ := exists_conj_eq_of_card hU hcard hdA
  exact ⟨x, hx, by rw [← hxd]; group⟩

theorem mem_U_of_comm_mem (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) {x w₀ : G} (hx : x ∈ 𝐗[i])
    (hw₀ : w₀ ∈ 𝐖[i])
    (hvt : t⁻¹ * (x * (𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap]))⁻¹ * t *
      (x * (𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap])) ∈ 𝐗[i]) : w₀ ∈ 𝐔[i] := by
  have htX := t_mem_normalizer_X h i
  have hconj : (MulAut.conj 𝐰[i.swap]⁻¹).toMonoidHom w₀ = 𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap] := by
    simp
  have hw'W : 𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap] ∈ 𝐖'[i] := ⟨w₀, hw₀, hconj⟩
  have hw'N : 𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap] ∈ normalizer (𝐗[i] : Set G) :=
    S_le_normalizer_X h hbt i (X_le_S i.swap (W'_le_X i hw'W))
  set v := 𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap] with hv
  have hc₁ : t⁻¹ * x⁻¹ * t * x ∈ 𝐗[i] := by
    have hx' : t⁻¹ * x⁻¹ * t ∈ 𝐗[i] := by
      have := (mem_normalizer_iff.mp (inv_mem htX) x⁻¹).mp (inv_mem hx)
      rwa [inv_inv] at this
    exact mul_mem hx' hx
  have hw't : t⁻¹ * v⁻¹ * t * v ∈ 𝐗[i] := by
    have e : t⁻¹ * v⁻¹ * t * v = (t⁻¹ * (x * v)⁻¹ * t * (x * v)) *
        (v⁻¹ * (t⁻¹ * x⁻¹ * t * x) * v)⁻¹ := by group
    rw [e]
    refine mul_mem hvt (inv_mem ?_)
    have := (mem_normalizer_iff.mp (inv_mem hw'N) _).mp hc₁
    rwa [inv_inv] at this
  have e2 : t⁻¹ * v⁻¹ * t * v = 𝐰[i.swap]⁻¹ * (t⁻¹ * (w₀⁻¹ * t * w₀)) * 𝐰[i.swap] := by
    have e := comm_W'_eq h i w₀
    calc t⁻¹ * v⁻¹ * t * v = (v⁻¹ * (t⁻¹ * v * t))⁻¹ := by group
      _ = _ := by rw [hv, e]; group
  rw [e2] at hw't
  have hκU : t⁻¹ * (w₀⁻¹ * t * w₀) ∈ 𝐔[i] := kappa_mem_U h i (mem_inf.mp (W_le_Fi h i hw₀)).2
  have hκL : 𝐰[i.swap]⁻¹ * (t⁻¹ * (w₀⁻¹ * t * w₀)) * 𝐰[i.swap] ∈ L :=
    mul_mem (mul_mem (inv_mem (w_mem_L _)) (pull_le φ _ hκU)) (w_mem_L _)
  have hA : 𝐰[i.swap]⁻¹ * (t⁻¹ * (w₀⁻¹ * t * w₀)) * 𝐰[i.swap] ∈ 𝐀[i] := by
    rw [← X_inf_C h i]
    exact ⟨hw't, h.setup.L_le hκL⟩
  have hw₀C : w₀ ∈ 𝐂 := kappa_eq_one_iff.mp (eq_one_of_conj_U_mem_A i hκU hA)
  rw [← W_inf_C h i]
  exact ⟨hw₀, hw₀C⟩

theorem exists_comm_of_fixed (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) {v : G} (hv : v ∈ 𝐒)
    (hvt : t⁻¹ * v⁻¹ * t * v ∈ 𝐗[i]) : ∃ y ∈ 𝐒, (y⁻¹ * (t⁻¹ * y * t))⁻¹ * v ∈ 𝐗[i] := by
  obtain ⟨x, hx, w', hw', rfl⟩ := exists_X_mul_W' h hbt i hv
  obtain ⟨w₀, hw₀, rfl⟩ := hw'
  have hconj : ∀ z : G, (MulAut.conj 𝐰[i.swap]⁻¹).toMonoidHom z = 𝐰[i.swap]⁻¹ * z * 𝐰[i.swap] :=
    fun z => by simp
  rw [hconj] at hvt ⊢
  have hw₀U := mem_U_of_comm_mem h hbt i hx hw₀ hvt
  have hw'W : 𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap] ∈ 𝐖'[i] := ⟨w₀, hw₀, hconj w₀⟩
  have hw'N : 𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap] ∈ normalizer (𝐗[i] : Set G) :=
    S_le_normalizer_X h hbt i (X_le_S i.swap (W'_le_X i hw'W))
  obtain ⟨y₀, hy₀, hy₀κ⟩ := exists_kappa_eq_W h i (inv_mem hw₀U)
  have hyW : 𝐰[i.swap]⁻¹ * y₀ * 𝐰[i.swap] ∈ 𝐖'[i] := ⟨y₀, hy₀, hconj y₀⟩
  refine ⟨_, X_le_S i.swap (W'_le_X i hyW), ?_⟩
  rw [comm_W'_eq h i y₀, hy₀κ, inv_inv]
  have hx' : (𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap])⁻¹ * x * (𝐰[i.swap]⁻¹ * w₀ * 𝐰[i.swap]) ∈ 𝐗[i] := by
    have := (mem_normalizer_iff.mp (inv_mem hw'N) _).mp hx
    rwa [inv_inv] at this
  rw [← mul_assoc]
  exact hx'

theorem comm_mem_X (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {v w : G} (hv : v ∈ 𝐒) (hw : w ∈ 𝐒) : v⁻¹ * w⁻¹ * v * w ∈ 𝐗[i] := by
  have := commutator_mem h hbt (inv_mem hv) (inv_mem hw)
  rw [inv_inv, inv_inv] at this
  exact mem_sup_left this

theorem exists_conj_of_mem_coset (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {y : G} (hy : ∃ v ∈ 𝐒, y = t * v)
    (hy2 : orderOf y = 2) : ∃ s ∈ 𝐒, y = s⁻¹ * t * s := by
  refine exists_conj_of_mem_coset_generic (V := 𝐒) (E := 𝐗[Axis.one]) (t := t) ?_ ?_ ?_ ?_ ?_
    h.setup.order_t ?_ ?_ ?_ ?_ ?_ hy hy2
  · exact X_le_S Axis.one
  · exact S_le_normalizer_X h hbt Axis.one
  · exact fun _ hx => X_mul_self h hbt Axis.one hx
  · exact fun _ hv => mul_self_mem_X h hbt Axis.one hv
  · exact fun _ hv _ hw => comm_mem_X h hbt Axis.one hv hw
  · exact T_le_normalizer_S h hbt (t_mem_T h)
  · exact t_mem_normalizer_X h Axis.one
  · intro htS
    exact t_not_mem_S h hbt htS
  · exact fun _ hv hvt => exists_comm_of_fixed h hbt Axis.one hv hvt
  · intro d hd
    exact exists_conj_of_mem_A h hbt Axis.one hd

omit [Finite G] [Finite K] in
theorem weyl_conj_rootU_mem_antiUnipotent (i : Axis) {u : antiSp K}
    (hu : u ∈ rootU K i) : weylElt K i.swap * u * weylElt K i.swap ∈ antiUnipotent K := by
  cases i
  · obtain ⟨b, rfl⟩ := hu
    change weylElt K Axis.two * uElt 0 b 0 0 * weylElt K Axis.two ∈ antiUnipotent K
    rw [weyl_two_conj_uElt]
    exact ⟨b, 0, 0, 0, rfl⟩
  · obtain ⟨c, rfl⟩ := hu
    change weylElt K Axis.one * uElt 0 0 c 0 * weylElt K Axis.one ∈ antiUnipotent K
    rw [weyl_one_conj_uElt]
    exact ⟨0, 0, 0, c, rfl⟩

omit [Finite G] [Finite K] in
theorem conj_U_mem_P (i : Axis) {u : G} (hu : u ∈ 𝐔[i]) :
    𝐰[i.swap]⁻¹ * u * 𝐰[i.swap] ∈ 𝐏 := by
  obtain ⟨huL, hu'⟩ := mem_pull.mp hu
  rw [conj_w_eq i huL, symm_mem_pull]
  exact weyl_conj_rootU_mem_antiUnipotent i hu'

theorem S_inf_C (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    𝐒 ⊓ 𝐂 = 𝐏 := by
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ ((pull_le φ _).trans h.setup.L_le))
  · obtain ⟨hxS, hxC⟩ := mem_inf.mp hx
    obtain ⟨x₁, hx₁, w', hw', hxe⟩ := exists_X_mul_W' h hbt Axis.one hxS
    obtain ⟨w₀, hw₀, rfl⟩ := hw'
    have hconj : (MulAut.conj 𝐰[Axis.one.swap]⁻¹).toMonoidHom w₀ =
        𝐰[Axis.one.swap]⁻¹ * w₀ * 𝐰[Axis.one.swap] := by simp
    rw [hconj] at hxe
    have hvt : t⁻¹ * (x₁ * (𝐰[Axis.one.swap]⁻¹ * w₀ * 𝐰[Axis.one.swap]))⁻¹ * t *
        (x₁ * (𝐰[Axis.one.swap]⁻¹ * w₀ * 𝐰[Axis.one.swap])) ∈ 𝐗[Axis.one] := by
      rw [← hxe]
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp hxC
      rw [show t⁻¹ * x⁻¹ * t * x = t⁻¹ * x⁻¹ * (t * x) by group, ← hxt]
      rw [show t⁻¹ * x⁻¹ * (x * t) = 1 by group]
      exact one_mem _
    have hw₀U := mem_U_of_comm_mem h hbt Axis.one hx₁ hw₀ hvt
    have hvP := conj_U_mem_P Axis.one hw₀U
    have hvC : 𝐰[Axis.one.swap]⁻¹ * w₀ * 𝐰[Axis.one.swap] ∈ 𝐂 :=
      ((pull_le φ _).trans h.setup.L_le) hvP
    have hx₁C : x₁ ∈ 𝐂 := by
      have := mul_mem hxC (inv_mem hvC)
      rwa [hxe, mul_inv_cancel_right] at this
    have hx₁A : x₁ ∈ 𝐀[Axis.one] := by
      rw [← X_inf_C h Axis.one]
      exact ⟨hx₁, hx₁C⟩
    rw [hxe]
    exact mul_mem (pull_mono φ (rootA_le_antiUnipotent Axis.one) hx₁A) hvP
  · rw [P_eq_A_sup_A]
    exact sup_le ((A_le_X h Axis.one).trans (X_le_S Axis.one))
      ((A_le_X h Axis.two).trans (X_le_S Axis.two))

theorem T_inf_C (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) :
    𝐓₀ ⊓ 𝐂 = 𝐐 := by
  have hPS : 𝐏 ≤ 𝐒 := by
    rw [← S_inf_C h hbt]
    exact inf_le_left
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le (hPS.trans (S_le_T h))
    (zpowers_le.mpr (t_mem_T h))) h.setup.Q_le_C)
  obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← S_mul_t h hbt] at hxT
  obtain ⟨s, hs, c, hc, rfl⟩ := hxT
  have hcC : c ∈ 𝐂 := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl) hc
  have hsC : s ∈ 𝐂 := by
    have := mul_mem hxC (inv_mem hcC)
    rwa [mul_inv_cancel_right] at this
  have hsP : s ∈ 𝐏 := by
    rw [← S_inf_C h hbt]
    exact ⟨hs, hsC⟩
  exact mul_mem (mem_sup_left hsP) (mem_sup_right hc)

local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)

theorem normalizer_Q_le_T (h : FCHyp L K n φ t) :
    normalizer (𝐐 : Set G) ≤ normalizer (𝐓₀ : Set G) := by
  intro g hg
  have hconj : ∀ y : G, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun y => by simp
  have hQ : ∀ y ∈ 𝐐, g * y * g⁻¹ ∈ 𝐓₀ := fun y hy =>
    mem_sup_left (mem_sup_left ((mem_normalizer_iff.mp hg y).mp hy))
  have hE : ∀ j : Axis, ∀ y ∈ 𝐄[j], g * y * g⁻¹ ∈ 𝐓₀ := by
    intro j y hy
    have hy' : g * y * g⁻¹ ∈ (𝐄[j]).map (MulAut.conj g).toMonoidHom := ⟨y, hy, hconj y⟩
    rw [pCore_normalizer_map_conj g 𝐁[j]] at hy'
    rcases h.map_B hg j with hk | hk
    · rw [pCore_map_subtype_congr (congrArg (fun B : Subgroup G => normalizer (B : Set G)) hk)]
        at hy'
      exact mem_sup_left (mem_sup_right hy')
    · rw [pCore_map_subtype_congr (congrArg (fun B : Subgroup G => normalizer (B : Set G)) hk)]
        at hy'
      exact mem_sup_right (mem_sup_right hy')
  exact mem_normalizer_of_conj_le fun x hx => conj_mem_of_sup
    (fun y hy => conj_mem_of_sup hQ (hE Axis.one) hy)
    (fun y hy => conj_mem_of_sup hQ (hE Axis.two) hy) hx

theorem mem_normalizer_X_of_mem_normalizer_U (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) {u : G} (huC : u ∈ 𝐂)
    (huU : u ∈ normalizer (𝐔[i] : Set G)) : u ∈ normalizer (𝐗[i] : Set G) := by
  have hV : u ∈ normalizer ((zpowers t ⊔ 𝐔[i] : Subgroup G) : Set G) :=
    (h.twoCore.mem_normalizer_zpowers_sup_iff huC (pull_le φ _)).mpr huU
  have hD : u ∈ normalizer (𝐃[i] : Set G) := OneAxisHeisenberg.le_normalizer_pCore_map hV
  have hB : u ∈ normalizer (𝐁[i] : Set G) := by
    rw [← h.D_inf_C i]
    exact inf_normalizer_le_normalizer_inf ⟨hD, le_normalizer huC⟩
  exact N_le_normalizer_X h hbt i hB

end BothTrivialSlice

end CFSG.LocalAnalysis.EvenBN.Sp4
