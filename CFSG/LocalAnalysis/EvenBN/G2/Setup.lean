module

public import CFSG.LocalAnalysis.EvenBN.G2.AutomorphismsTable
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Assembly.Reduction
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped commutatorElement Pointwise

theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {a b c d : G}
    (hcb : c * b = b * c) (hcd : c * d = d * c) (hda : d * a = a * d) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hda' : d * a⁻¹ = a⁻¹ * d := (Commute.inv_right (hda : Commute d a)).eq
  calc ⁅a * c, b * d⁆ = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (c * d) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hcb]; group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by rw [hcd]; group
    _ = ⁅a, b⁆ := by rw [hda', commutatorElement_def]; group

theorem isElementaryAbelian_of_isElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : CFSG.IsElementaryAbelian 2 E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE

theorem isElemAbelian_range {G M : Type*} [Group G] [Group M] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) (ψ : E →* M) : IsElemAbelian 2 ψ.range := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨z, hz⟩ := b.2
    refine Subtype.ext ?_
    change (a : M) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm' x z]
  · obtain ⟨x, rfl⟩ := hy
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 _ x.2)
    rw [this, map_one]

theorem isMulCommutative_sup {G : Type*} [Group G] {A B : Subgroup G} [IsMulCommutative A]
    [IsMulCommutative B] (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsMulCommutative (A ⊔ B : Subgroup G) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure fun x hx y hy _ => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  · exact hAB x hx y hy
  · exact (hAB y hy x hx).symm
  · exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)

theorem card_le_two_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (h : ∀ x : H, x ^ 2 = 1) : Nat.card H ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_of_forall_pow_eq_one h)

theorem ringEquiv_mul_comm {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  obtain ⟨s, -, rfl⟩ := exists_eq_frobeniusEquiv_pow hK hn σ
  obtain ⟨u, -, rfl⟩ := exists_eq_frobeniusEquiv_pow hK hn τ
  rw [← pow_add, ← pow_add, add_comm]

namespace Model

section Facts

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem commutatorElement_mem_inner {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (α β : MulAut (adjointGroup .G2 K)) : ⁅α, β⁆ ∈ inner (adjointGroup .G2 K) := by
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form hn K hK
  have h : ⁅α, β⁆ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ringEquiv_mul_comm hK (by omega) _ _
  rw [hker] at h
  exact h

theorem exists_leviB_conj_mem_U {y : ModGL .G2 K} (hy : y ∈ Y K)
    (hy1 : y ≠ 1) :
    ∃ l ∈ leviB K, l⁻¹ * y * l ∈ U K := by
  obtain ⟨ρ, hrange, -, -, -, hconj⟩ := natural_Y (K := K)
  obtain ⟨E, F, rfl⟩ := mem_Y.1 hy
  obtain ⟨M, hM⟩ : ∃ M : SL2 K,
      Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) K) ![1, 0] = ![F, E] := by
    by_cases hF : F = 0
    · have hE : E ≠ 0 := by
        rintro rfl
        subst hF
        exact hy1 g2N_zero
      refine ⟨⟨!![0, E⁻¹; E, 0], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_two_of, mul_zero, inv_mul_cancel₀ hE, zero_sub, CharTwo.neg_eq]
      · ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, hF]
    · refine ⟨⟨!![F, 0; E, F⁻¹], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hF, zero_mul, sub_zero]
      · ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  refine ⟨ρ M, hrange ▸ ⟨M, rfl⟩, ?_⟩
  have h1 := hconj M ![1, 0]
  rw [hM] at h1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  rw [← h1, show (ρ M)⁻¹ * (ρ M * g2N 0 0 0 0 0 1 * (ρ M)⁻¹) * ρ M = g2N 0 0 0 0 0 1 by group]
  exact g2N_mem_U_iff.2 ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem D_sup_leviA_le_centralizer_U :
    Model.D K ⊔ leviA K ≤ centralizer (U K : Set (ModGL .G2 K)) := by
  have h := (even_G2_highest_long_root_centralizer K).2.2.2.1
  rw [show Model.D K ⊔ leviA K = g2LongRadical K ⊔ g2RankOne K g2ir from rfl, ← h]
  exact centralizer_pinnedX_c_le

end Facts

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Facts

variable
  [Finite K] [CharP K 2]

theorem isSylowOf_S [Finite G] : IsSylowOf 2 d.S L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) card_posUnipotent
  have hcard := Sylow.card_eq_multiplicity (hUp.toSylow hUi)
  rw [IsPGroup.toSylow_coe] at hcard
  refine isSylowOf_of_card (d.image_le _) ?_
  rw [G2Data.S, d.card_image (Model.S_le_adjointGroup K),
    ← Nat.card_congr (subgroupOfEquivOfLe (Model.S_le_adjointGroup K)).toEquiv, hcard,
    Nat.card_congr d.equiv.toEquiv]

theorem exists_conj_mem_U_of_mem_Y {y : G} (hy : y ∈ d.Y)
    (hy1 : y ≠ 1) :
    ∃ l ∈ L, l⁻¹ * y * l ∈ d.U := by
  obtain ⟨y₀, hy₀, rfl⟩ := d.mem_image.1 hy
  have hy₀1 : (y₀ : ModGL .G2 K) ≠ 1 := fun h1 =>
    hy1 (by rw [show y₀ = 1 from Subtype.ext h1, map_one])
  obtain ⟨l, hl, hly⟩ := Model.exists_leviB_conj_mem_U hy₀ hy₀1
  have hlA : l ∈ adjointGroup .G2 K := Model.leviB_le_adjointGroup K hl
  refine ⟨d.emb ⟨l, hlA⟩, d.emb_mem _, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  exact d.emb_mem_image (by simpa using hly)

theorem D_sup_leviA_le_centralizer_U :
    d.D ⊔ d.leviA ≤ centralizer (d.U : Set G) := by
  have h1 := d.image_inf_centralizer (Model.D K ⊔ Model.leviA K) (Model.U_le_adjointGroup K)
  rw [inf_eq_left.2 Model.D_sup_leviA_le_centralizer_U,
    d.image_sup Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K)] at h1
  rw [G2Data.D, G2Data.leviA, G2Data.U, h1]
  exact inf_le_right

omit [Finite K] in
theorem le_W_or_le_X_of_le_F {E : Subgroup G} (hEF : E ≤ d.F)
    (hE : CFSG.IsElementaryAbelian 2 E) : E ≤ d.W ∨ E ≤ d.X := by
  have hEL : E ≤ L := hEF.trans (d.image_le _)
  have hE₀F : d.preimage E ≤ Model.F K := by
    rw [← d.image_le_image_iff (d.preimage_le E), d.image_preimage hEL]
    exact hEF
  have hE₀ : CFSG.IsElementaryAbelian 2 (d.preimage E) := by
    rw [← d.isElementaryAbelian_image_iff (d.preimage_le E), d.image_preimage hEL]
    exact hE
  rcases Model.twoElementaryProduct_F.le_or_le hE₀F with h1 | h1
  · left
    rw [← d.image_preimage hEL]
    exact d.image_mono h1
  · right
    rw [← d.image_preimage hEL]
    exact d.image_mono h1

theorem map_conj_W_ne_X {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) {x : G} (hx : x ∈ normalizer (L : Set G)) :
    d.W.map (MulAut.conj x).toMonoidHom ≠ d.X := by
  intro hWX
  obtain ⟨g, k, -, hgk⟩ := Model.exists_eq_conj_mul_fieldAut_pow hK hn (d.act ⟨x, hx⟩)
  have hle : (Model.W K).map (MulAut.conj (g : ModGL .G2 K)).toMonoidHom ≤ Model.X K := by
    rintro _ ⟨w₁, hw₁, rfl⟩
    have hw₁' : w₁ ∈ (Model.W K).map
        (Units.map (entrywiseHom (frobeniusEquiv K 2 ^ k).toRingHom)) := by
      rw [Model.map_entrywise_W]
      exact hw₁
    obtain ⟨w₀, hw₀, rfl⟩ := hw₁'
    have hw₀A : w₀ ∈ adjointGroup .G2 K := Model.W_le_adjointGroup hw₀
    have h1 : x * d.emb ⟨w₀, hw₀A⟩ * x⁻¹ ∈ d.X := by
      rw [← hWX]
      exact ⟨_, d.emb_mem_image hw₀, rfl⟩
    rw [← d.emb_act_apply ⟨x, hx⟩, hgk] at h1
    have h2 := d.emb_mem_image_iff.1 h1
    rw [Model.coe_conj_mul_fieldAut_pow_apply] at h2
    exact h2
  have heq : (Model.W K).map (MulAut.conj (g : ModGL .G2 K)).toMonoidHom = Model.X K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj, Model.card_W, Model.card_X])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn
  obtain ⟨-, -, hXW, -⟩ := Model.yamada_3_17_1 hK4
  refine hXW _ (inv_mem g.2) (le_antisymm (fun y hy => ?_) fun y hy => ?_)
  · rw [mem_map_conj_iff, inv_inv, ← heq, mem_map_conj_iff] at hy
    simpa [mul_assoc] using hy
  · rw [mem_map_conj_iff, inv_inv, ← heq, mem_map_conj_iff]
    simpa [mul_assoc] using hy

end Facts

end G2Data

structure Setup (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  std : standardComponentIsStandard L
  core : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥
  cyc : ∀ S : Sylow 2 (centralizer (L : Set G)),
    IsCyclic (S : Subgroup (centralizer (L : Set G)))
  center_eq : center L = ⊥
  two_le : 2 ≤ f
  model : LieModel L .G2 0 2 f
  ht : orderOf t = 2
  htL : t ∈ centralizer (L : Set G)

theorem exists_setup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {L : Subgroup G} (hL : standardComponentIsStandard L) (hZ : center L = ⊥)
    (hcore : ∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (hcyc : ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {f : ℕ} (hf : 2 ≤ f) (hm : LieModel L .G2 0 2 f) : ∃ t : G, Setup G L f t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hL.2.1)
  exact ⟨u, ‹IsSimpleGroup G›, hnonab, hK, hL, hcore, hcyc, hZ, hf, hm,
    by rw [orderOf_coe]; exact hu, u.2⟩

@[expose] noncomputable def yamadaR
    {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K) (t : G) :
    Subgroup G :=
  d.S ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_data
    (h : Setup G L f t) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (G2Data L K) :=
  G2Data.exists_of_lieModel h.model

theorem four_le (h : Setup G L f t) : 4 ≤ 2 ^ f :=
  (Nat.pow_le_pow_right two_pos h.two_le).trans_eq' (by norm_num)

theorem not_normal (h : Setup G L f t) : ¬ L.Normal := fun hN => by
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hb | htop
  · have hnt := h.std.1.2.toNontrivial
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine hab (congrArg _ (Subtype.ext ?_))
    rw [(Subgroup.eq_bot_iff_forall L).1 hb _ a'.2, (Subgroup.eq_bot_iff_forall L).1 hb _ b'.2]
  · have hC : centralizer (L : Set G) = ⊥ := by
      rw [htop, coe_top, centralizer_univ]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
      · exact hc
      · exfalso
        obtain ⟨a, b, hab⟩ := h.nonab
        exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm
    have heven := h.std.2.1
    rw [hC, Subgroup.card_bot] at heven
    exact Nat.not_even_one heven

theorem inf_centralizer_eq_bot (h : Setup G L f t) : L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [h.center_eq, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

theorem t_ne_one (h : Setup G L f t) : t ≠ 1 := fun h1 => by
  have := h.ht
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t_mul_t (h : Setup G L f t) : t * t = 1 := by
  rw [← sq, ← h.ht, pow_orderOf_eq_one]

theorem t_not_mem_L (h : Setup G L f t) : t ∉ L := fun htL => by
  have : t ∈ L ⊓ centralizer (L : Set G) := ⟨htL, h.htL⟩
  rw [h.inf_centralizer_eq_bot, mem_bot] at this
  exact h.t_ne_one this

theorem card_zpowers_t (h : Setup G L f t) : Nat.card (zpowers t) = 2 := by
  rw [Nat.card_zpowers, h.ht]

theorem zpowers_inf_L (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L) : zpowers t ⊓ E = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxE⟩
  rw [mem_bot]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
  have hk : t ^ k = t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.ht]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hk, h0, zpow_zero]
  · rw [hk, h1, zpow_one] at hxE
    exact absurd (hEL hxE) h.t_not_mem_L

theorem commutator_L (h : Setup G L f t) : ⁅L, L⁆ = L := by
  have h1 : commutator L = ⊤ := h.std.1.1
  have h2 := congrArg (Subgroup.map L.subtype) h1
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

theorem centralizer_le_normalizer (h : Setup G L f t) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  (ComponentInitial.standard_involution_centralizer_normality h.std h.htL h.ht).1

theorem L_le_centralizer (h : Setup G L f t) : L ≤ centralizer ({t} : Set G) :=
  (ComponentInitial.standard_involution_centralizer_normality h.std h.htL h.ht).2.1

theorem t_mem_centralizer (_h : Setup G L f t) : t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem kernel (h : Setup G L f t) :
    IsCyclic (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      (∀ x ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), orderOf x = 2 → x = t) ∧
      ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (centralizer ({t} : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (L : Set G) := ⟨t, h.htL⟩ with htc
  have htc2 : orderOf tc = 2 := by rw [← orderOf_coe]; exact h.ht
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htc2, pow_one])
  obtain ⟨S, hSt⟩ := hz.exists_le_sylow
  have htS : tc ∈ S := hSt (mem_zpowers _)
  have hSc := h.cyc S
  obtain ⟨-, huniq, -, -, -, -, hR, hRn, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      h.std S hSc htS htc2 (h.core t h.ht)
  have hR' : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) =
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := hR
  rw [hR']
  refine ⟨isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _),
    S.isPGroup'.map _, ?_, hRn⟩
  rintro _ ⟨y, hy, rfl⟩ hy2
  rw [Subgroup.subtype_apply, orderOf_coe] at hy2
  exact congrArg Subtype.val (huniq y hy hy2)

theorem t_mem_kernel (h : Setup G L f t) :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
  ⟨h.htL, h.t_mem_centralizer⟩

theorem kernel_comm (h : Setup G L f t) {c d : G}
    (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
    (hd : d ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : c * d = d * c := by
  have := h.kernel.1
  exact congrArg Subtype.val (mul_comm' (⟨c, hc⟩ :
    (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G)) ⟨d, hd⟩)

theorem isElemAbelian_sup_zpowers (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L)
    (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E ⊔ zpowers t) ∧ Nat.card (E ⊔ zpowers t : Subgroup G) = 2 * Nat.card E := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL x (hEL hx) : Commute x t) k).eq
  have : CFSG.IsElementaryAbelian 2 E := isElementaryAbelian_of_isElemAbelian hE
  have : CFSG.IsElementaryAbelian 2 (zpowers t) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact h.t_mul_t)
  have hEt : zpowers t ≤ centralizer (E : Set G) := by
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy
  refine ⟨isElemAbelian_of_isElementaryAbelian
    (CFSG.IsElementaryAbelian.sup_of_le_centralizer hEt), ?_⟩
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (zpowers t) hcomm).1
  rw [inf_comm, h.zpowers_inf_L hEL, Subgroup.card_bot, mul_one, h.card_zpowers_t] at hc
  rw [hc, mul_comm]

section Act

variable {K : Type} [Field K]

@[expose] noncomputable def act (h : Setup G L f t) (d : G2Data L K) :
    centralizer ({t} : Set G) →* MulAut (adjointGroup .G2 K) :=
  d.act.comp (inclusion h.centralizer_le_normalizer)

theorem act_apply (h : Setup G L f t) (d : G2Data L K) (x : centralizer ({t} : Set G)) :
    h.act d x = d.act ⟨x, h.centralizer_le_normalizer x.2⟩ :=
  rfl

theorem act_eq_one_iff (h : Setup G L f t) (d : G2Data L K) (x : centralizer ({t} : Set G)) :
    h.act d x = 1 ↔ (x : G) ∈ centralizer (L : Set G) :=
  d.act_eq_one_iff _

theorem coe_sup_kernel (_h : Setup G L f t) :
    ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) : Set G) =
      (L : Set G) * ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :
        Set G) :=
  (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L _
    fun l hl _ hc => mem_centralizer_iff.1 (mem_inf.1 hc).1 l hl).2

theorem act_mem_inner_iff (h : Setup G L f t) (d : G2Data L K) (x : centralizer ({t} : Set G)) :
    h.act d x ∈ inner (adjointGroup .G2 K) ↔
      (x : G) ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  rw [act_apply, d.act_mem_inner_iff]
  refine ⟨fun hx => ?_, fun hx => (sup_le_sup_left (inf_le_left : centralizer (L : Set G) ⊓
    centralizer ({t} : Set G) ≤ centralizer (L : Set G)) L) hx⟩
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L (centralizer (L : Set G))
    fun l hl c hc => mem_centralizer_iff.1 hc l hl).2
  have hx' : (x : G) ∈ ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨l, hl, c, hc, hlc⟩ := hx'
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (h.L_le_centralizer hl)) x.2
    rwa [← hlc, inv_mul_cancel_left] at this
  rw [← hlc]
  exact mul_mem (mem_sup_left hl) (mem_sup_right ⟨hc, hcC⟩)

theorem act_emb (h : Setup G L f t) (d : G2Data L K) (g : adjointGroup .G2 K) :
    h.act d ⟨d.emb g, h.L_le_centralizer (d.emb_mem g)⟩ = MulAut.conj g :=
  d.act_emb g

end Act

section Perfect

theorem perfect_le (h : Setup G L f t) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ centralizer ({t} : Set G)) : P ≤ L := by
  obtain ⟨K, _, _, _, hK, ⟨d⟩⟩ := G2Data.exists_of_lieModel h.model
  have hdec : ∀ p ∈ P, p ∈ (L : Set G) *
      ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    intro p hp
    have hT : ⁅P, P⁆ ≤ ((inner (adjointGroup .G2 K)).comap (h.act d)).map
        (centralizer ({t} : Set G)).subtype := by
      rw [commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, hPC ha⟩ : centralizer ({t} : Set G)), ⟨b, hPC hb⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, map_commutatorElement]
      exact Model.commutatorElement_mem_inner hK h.two_le _ _
    rw [← hP] at hp
    obtain ⟨x, hx, rfl⟩ := hT hp
    rw [← h.coe_sup_kernel]
    exact (h.act_mem_inner_iff d x).1 hx
  rw [← hP, commutator_le]
  intro a ha b hb
  obtain ⟨l, hl, c, hc, rfl⟩ := hdec a ha
  obtain ⟨l', hl', c', hc', rfl⟩ := hdec b hb
  rw [commutatorElement_mul_mul_of_commute (mem_centralizer_iff.1 hc.1 l' hl').symm
    (h.kernel_comm hc hc') (mem_centralizer_iff.1 hc'.1 l hl).symm]
  have hll := commutator_mem_commutator hl hl'
  rwa [h.commutator_L] at hll

end Perfect

section YamadaR

variable {K : Type} [Field K]

theorem S_le_centralizer (h : Setup G L f t) (d : G2Data L K) : d.S ≤ centralizer ({t} : Set G) :=
  (d.image_le _).trans h.L_le_centralizer

theorem yamadaR_le_centralizer (h : Setup G L f t) (d : G2Data L K) :
    yamadaR d t ≤ centralizer ({t} : Set G) :=
  sup_le (h.S_le_centralizer d) inf_le_right

omit [Finite G] in
theorem S_commute_kernel (d : G2Data L K) (t : G) :
    ∀ x ∈ d.S, ∀ y ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), x * y = y * x :=
  fun x hx _ hy => mem_centralizer_iff.1 (mem_inf.1 hy).1 x (d.image_le _ hx)

theorem card_yamadaR (h : Setup G L f t) (d : G2Data L K) :
    Nat.card (yamadaR d t) =
      Nat.card d.S *
        Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ (S_commute_kernel d t)).1
  have hinf : d.S ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf (d.image_le _) inf_le_left).trans h.inf_centralizer_eq_bot.le)
  rwa [hinf, Subgroup.card_bot, mul_one] at hc

end YamadaR

section Yamada42

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem isSylowOf_yamadaR (h : Setup G L f t) (d : G2Data L K) :
    IsSylowOf 2 (yamadaR d t) (L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardLT : Nat.card (L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :
      Subgroup G) = Nat.card L *
        Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L
      (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
      fun l hl _ hc => mem_centralizer_iff.1 (mem_inf.1 hc).1 l hl).1
    have hinf : L ⊓ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf le_rfl inf_le_left).trans h.inf_centralizer_eq_bot.le)
    rwa [hinf, Subgroup.card_bot, mul_one] at hc
  have hT : Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) =
      2 ^ (Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :
        Subgroup G)).factorization 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h.kernel.2.1
    rw [hn, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  refine isSylowOf_of_card (sup_le_sup_right (d.image_le _) _) ?_
  rw [h.card_yamadaR d, d.isSylowOf_S.card_eq, hcardLT,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add, ← hT]

theorem card_le_of_isElemAbelian (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {E : Subgroup G} (hEC : E ≤ centralizer ({t} : Set G)) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 * Nat.card ((h.act d).comp (inclusion hEC)).range ∧
      Nat.card ((h.act d).comp (inclusion hEC)).range ≤ Nat.card K ^ 3 := by
  set ψ := (h.act d).comp (inclusion hEC) with hψ
  have hker : Nat.card ψ.ker ≤ 2 := by
    have := h.kernel.1
    let κ : ψ.ker →* (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
      (E.subtype.comp ψ.ker.subtype).codRestrict _ fun x =>
        ⟨(h.act_eq_one_iff d _).1 (MonoidHom.mem_ker.1 x.2), hEC (x : E).2⟩
    have hκ : Function.Injective κ := by
      intro x y hxy
      have h1 := congrArg
        (fun z : (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have : IsCyclic ψ.ker := isCyclic_of_injective κ hκ
    exact card_le_two_of_isCyclic fun x => Subtype.ext (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
      exact hE.2 _ (x : E).2))
  refine ⟨?_, (Model.card_le_of_isElemAbelian hK h.two_le (isElemAbelian_range hE ψ)).1⟩
  rw [← Subgroup.card_ker_mul_card_range ψ]
  exact Nat.mul_le_mul_right _ hker

theorem isElemAbelian_W_sup_zpowers (h : Setup G L f t) (d : G2Data L K) :
    IsElemAbelian 2 (d.W ⊔ zpowers t) ∧
      Nat.card (d.W ⊔ zpowers t : Subgroup G) = 2 * Nat.card K ^ 3 := by
  obtain ⟨hE, hcard⟩ := h.isElemAbelian_sup_zpowers (E := d.W) (d.image_le _)
    (isElemAbelian_of_isElementaryAbelian d.isElementaryAbelian.2.2.2)
  exact ⟨hE, by rw [hcard, d.cards.2.2.2.1]⟩

omit [Finite K] in
theorem W_sup_zpowers_le_yamadaR (h : Setup G L f t) (d : G2Data L K) :
    d.W ⊔ zpowers t ≤ yamadaR d t := by
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -, -⟩ := d.inclusions
  exact sup_le_sup (hWF.trans (hFD.trans hDS)) ((zpowers_le).2 h.t_mem_kernel)

theorem pRank_centralizer (h : Setup G L f t) :
    CFSG.Open.pRank 2 (centralizer ({t} : Set G)) = 3 * f + 1 := by
  obtain ⟨K, _, _, _, hK, ⟨d⟩⟩ := G2Data.exists_of_lieModel h.model
  have hq : 2 * Nat.card K ^ 3 = 2 ^ (3 * f + 1) := by
    rw [hK, ← pow_mul, pow_succ, mul_comm, mul_comm f 3]
  apply le_antisymm
  · refine SectionRank.pRank_le one_lt_two fun E hEC hE => ?_
    obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hK hEC hE
    rw [← hq]
    exact h1.trans (Nat.mul_le_mul_left 2 h2)
  · obtain ⟨hE, hcard⟩ := h.isElemAbelian_W_sup_zpowers d
    exact SectionRank.le_pRank one_lt_two
      ((h.W_sup_zpowers_le_yamadaR d).trans (h.yamadaR_le_centralizer d)) hE (hcard.trans hq)

theorem pRank_eq (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) {Q : Subgroup G}
    (hQC : Q ≤ centralizer ({t} : Set G)) (hRQ : yamadaR d t ≤ Q) :
    CFSG.Open.pRank 2 Q = 3 * f + 1 := by
  apply le_antisymm
  · rw [← h.pRank_centralizer]
    exact SectionRank.pRank_mono one_lt_two hQC
  · obtain ⟨hE, hcard⟩ := h.isElemAbelian_W_sup_zpowers d
    refine SectionRank.le_pRank one_lt_two ((h.W_sup_zpowers_le_yamadaR d).trans hRQ) hE ?_
    rw [hcard, hK, ← pow_mul, pow_succ, mul_comm, mul_comm f 3]

theorem rankThompson_eq (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQC : Q ≤ centralizer ({t} : Set G))
    (hRQ : yamadaR d t ≤ Q) : rankThompson Q = yamadaR d t := by
  have hrQ := h.pRank_eq d hK hQC hRQ
  have hf1 : 1 ≤ f := by have := h.two_le; omega
  apply le_antisymm
  · set ψQ := (h.act d).comp (inclusion hQC) with hψQ
    have hQ' : IsPGroup 2 ψQ.range := hQ2.of_surjective ψQ.rangeRestrict ψQ.rangeRestrict_surjective
    have hSQ' : Model.inn (Model.S K) ≤ ψQ.range := by
      intro α hα
      obtain ⟨g, hg, rfl⟩ := Model.mem_inn.1 hα
      exact ⟨⟨d.emb g, hRQ (mem_sup_left (d.emb_mem_image hg))⟩, h.act_emb d g⟩
    refine iSup₂_le fun V ⟨hVQ, hV, hrV⟩ => ?_
    have hVC := hVQ.trans hQC
    set ψV := (h.act d).comp (inclusion hVC) with hψV
    have hV'Q' : ψV.range ≤ ψQ.range := by
      rintro _ ⟨v, rfl⟩
      exact ⟨⟨v, hVQ v.2⟩, rfl⟩
    have hV' : IsMulCommutative ψV.range := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨z, hz⟩ := b.2
      change (a : MulAut (adjointGroup .G2 K)) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm' x z]
    have hrV' : 3 * f ≤ CFSG.Open.pRank 2 ψV.range := by
      obtain ⟨E, hEV, hE, hcardE⟩ := SectionRank.exists_pRank one_lt_two V
      rw [hrV, hrQ] at hcardE
      have hEC := hEV.trans hVC
      obtain ⟨h1, h2⟩ := h.card_le_of_isElemAbelian d hK hEC hE
      have hcard' : Nat.card ((h.act d).comp (inclusion hEC)).range = 2 ^ (3 * f) := by
        apply le_antisymm
        · rw [hK, ← pow_mul, mul_comm] at h2
          exact h2
        · rw [hcardE, pow_succ, mul_comm] at h1
          exact Nat.le_of_mul_le_mul_left h1 two_pos
      refine SectionRank.le_pRank one_lt_two ?_ (isElemAbelian_range hE _) hcard'
      rintro _ ⟨e, rfl⟩
      exact ⟨⟨e, hEV e.2⟩, rfl⟩
    have key := (Model.yamada_3_21 hK h.two_le hQ' hSQ').1 _ hV'Q' hV' hrV'
    intro v hv
    obtain ⟨g, hg, hge⟩ := Model.mem_inn.1 (key ⟨⟨v, hv⟩, rfl⟩)
    have hgC := h.L_le_centralizer (d.emb_mem g)
    have hge' : h.act d ⟨v, hVC hv⟩ = MulAut.conj g := hge.symm
    have hc : (d.emb g)⁻¹ * v ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
      refine mem_inf.2 ⟨(h.act_eq_one_iff d ⟨_, mul_mem (inv_mem hgC) (hVC hv)⟩).1 ?_,
        mul_mem (inv_mem hgC) (hVC hv)⟩
      have e : (⟨(d.emb g)⁻¹ * v, mul_mem (inv_mem hgC) (hVC hv)⟩ :
          centralizer ({t} : Set G)) = (⟨d.emb g, hgC⟩ : centralizer ({t} : Set G))⁻¹ *
            ⟨v, hVC hv⟩ := rfl
      rw [e, map_mul, map_inv, h.act_emb d g, hge', inv_mul_cancel]
    rw [show v = d.emb g * ((d.emb g)⁻¹ * v) by group]
    exact mul_mem (mem_sup_left (d.emb_mem_image hg)) (mem_sup_right hc)
  · have := h.kernel.1
    have hfam : ∀ A : Subgroup G, A ≤ d.S → IsMulCommutative A →
        CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 d.S →
        A ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) ≤ rankThompson Q := by
      intro A hAS hA hrA
      have hAQ : A ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) ≤ Q :=
        (sup_le_sup_right hAS _).trans hRQ
      refine le_iSup₂_of_le (A ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)))
        ⟨hAQ, isMulCommutative_sup fun a ha c hc => S_commute_kernel d t a (hAS ha) c hc, ?_⟩ le_rfl
      refine le_antisymm (SectionRank.pRank_mono one_lt_two hAQ) ?_
      obtain ⟨E, hEA, hE, hcardE⟩ := SectionRank.exists_pRank one_lt_two A
      rw [hrA, (d.pRank_S hK hf1).1] at hcardE
      obtain ⟨hE', hcard⟩ := h.isElemAbelian_sup_zpowers (hEA.trans (hAS.trans (d.image_le _))) hE
      refine hrQ ▸ SectionRank.le_pRank one_lt_two
        (sup_le_sup hEA ((zpowers_le).2 h.t_mem_kernel)) hE' ?_
      rw [hcard, hcardE, ← pow_succ']
    have hS : d.S ≤ rankThompson Q := by
      rw [← d.rankThompson_S hK hf1]
      exact iSup₂_le fun A ⟨hAS, hA, hrA⟩ => le_sup_left.trans (hfam A hAS hA hrA)
    obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -, -⟩ := d.inclusions
    have hWS : d.W ≤ d.S := hWF.trans (hFD.trans hDS)
    have hW := d.isElementaryAbelian.2.2.2
    have hrW : CFSG.Open.pRank 2 d.W = CFSG.Open.pRank 2 d.S := by
      rw [(d.pRank_S hK hf1).1]
      exact d.pRank_eq_of_le hK hf1 le_rfl (hWS.trans (d.image_le _))
        (isElemAbelian_of_isElementaryAbelian hW) d.cards.2.2.2.1
    exact sup_le hS (le_sup_right.trans (hfam d.W hWS hW.toIsMulCommutative hrW))

theorem conj_not_mem_Y (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (g : G) :
    g * t * g⁻¹ ∉ d.Y := by
  intro hy
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hy1 : g * t * g⁻¹ ≠ 1 := fun h1 => h.t_ne_one (by
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1)
  obtain ⟨l, -, hu⟩ := d.exists_conj_mem_U_of_mem_Y hy hy1
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  set m := g⁻¹ * l with hm
  set u := l⁻¹ * (g * t * g⁻¹) * l with hu'
  have htu : m * u * m⁻¹ = t := by
    rw [hm, hu']
    group
  have hperf : ⁅d.D ⊔ d.leviA, d.D ⊔ d.leviA⁆ = d.D ⊔ d.leviA := (d.yamada_3_13_4_G hK4).2.1
  have hcent := d.D_sup_leviA_le_centralizer_U
  have huP : u ∈ d.D ⊔ d.leviA := mem_sup_left (hFD (hXF (hYX (hUY hu))))
  have hPC : (d.D ⊔ d.leviA).map (MulAut.conj m).toMonoidHom ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    have hpu : u * p = p * u := mem_centralizer_iff.1 (hcent hp) u hu
    rw [mem_centralizer_singleton_iff, ← htu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * p * m⁻¹ * (m * u * m⁻¹) = m * (p * u) * m⁻¹ := by group
      _ = m * (u * p) * m⁻¹ := by rw [hpu]
      _ = m * u * m⁻¹ * (m * p * m⁻¹) := by group
  have hPL := h.perfect_le (by rw [← map_commutator, hperf]) hPC
  exact h.t_not_mem_L (hPL ⟨u, huP, htu⟩)

theorem normalizer_S_le_normalizer_W (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (d.W : Set G) := by
  rintro x ⟨hxC, hxS⟩
  have hxN := h.centralizer_le_normalizer hxC
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hSx : d.S.map (MulAut.conj x).toMonoidHom = d.S := by
    ext y
    rw [mem_map_conj_iff]
    constructor
    · intro hy
      have := (mem_normalizer_iff.1 hxS (x⁻¹ * y * x)).1 hy
      rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at this
    · intro hy
      have := (mem_normalizer_iff.1 hxS (x⁻¹ * y * x)).2
      rw [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at this
      exact this hy
  have hFx : d.F.map (MulAut.conj x).toMonoidHom = d.F := by
    rw [← (d.yamada_3_12_commutators hK4).2.2.1, map_commutator, hSx]
  obtain ⟨-, -, -, -, hWF, -⟩ := d.inclusions
  have hWxF : d.W.map (MulAut.conj x).toMonoidHom ≤ d.F := by
    rw [← hFx]
    exact map_mono hWF
  have hcard : Nat.card d.W ≤ Nat.card (d.W.map (MulAut.conj x).toMonoidHom) := by
    rw [card_map_conj]
  rcases d.le_W_or_le_X_of_le_F hWxF (isElementaryAbelian_map_conj d.isElementaryAbelian.2.2.2 x)
    with h1 | h1
  · have heq := Subgroup.eq_of_le_of_card_ge h1 hcard
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← heq]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← heq, mem_map_conj_iff] at hy
      simpa [mul_assoc] using hy
  · exact absurd (Subgroup.eq_of_le_of_card_ge h1 (by
      rw [card_map_conj, d.cards.2.2.2.1, d.cards.2.2.1])) (d.map_conj_W_ne_X hK h.two_le hxN)

end Yamada42

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
