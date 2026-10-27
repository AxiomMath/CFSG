module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderHypIIQuot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSylow
public import Certificates.Certificate113
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderHypII
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.StronglyEmbedded

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ABGLocalTools

section Basic

variable {G : Type*} [Group G]

theorem tightlyEmbedded_subgroupOf_top_iff (Q : Subgroup G) :
    TightlyEmbedded (Q.subgroupOf ⊤) ↔ TightlyEmbedded Q :=
  StandardSubgroupAPI.tightlyEmbedded_subgroupOf_top_iff Q

theorem commutator_eq_top_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : commutator Y = ⊤) : commutator X = ⊤ := by
  have : Group.IsPerfect Y := (Group.isPerfect_def).2 hY
  exact (Group.isPerfect_def).1 (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective)

theorem map_center_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (center X).map e.toMonoidHom = center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e w * e x = e x * e w
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hx w)]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro z
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, (mem_center_iff.mp hy (e z))]

end Basic

theorem hypII_of_sup_eq_top {A : Type*} [Group A]
    (h : ∀ (H : Type) [Group H] [Finite H] (B T : Subgroup H), T ⊔ B = ⊤ →
      Nonempty (B ≃* A) → NoncyclicFaithful T B → SylowInTightTwoNilpotent T B →
        T ≤ B ⊔ centralizer (B : Set H)) :
    HypII A := by
  intro H _ _ B T ⟨eB⟩ hTF hTX
  obtain ⟨hTe, hT4, hTN, hTC⟩ := hTF
  obtain ⟨X, hXP, hTsyl, hX2, htight⟩ := hTX
  set P := T ⊔ B with hP
  have hBP : B ≤ P := le_sup_right
  have hTP : T ≤ P := le_sup_left
  set B₁ := B.subgroupOf P
  set T₁ := T.subgroupOf P
  set X₁ := X.subgroupOf P
  have hsup : T₁ ⊔ B₁ = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTP, map_subgroupOf_eq_of_le hBP, ← hP,
      ← MonoidHom.range_eq_map, range_subtype]
  have hTX : T ≤ X := hTsyl.le
  have hres := h P B₁ T₁ hsup ⟨(subgroupOfEquivOfLe hBP).trans eB⟩
    ⟨Asc76X.isElemAbelian_of_mulEquiv (subgroupOfEquivOfLe hTP).symm hTe,
      by rwa [Nat.card_congr (subgroupOfEquivOfLe hTP).toEquiv],
      fun t ht => by
        rw [mem_normalizer_iff]
        intro x
        exact mem_normalizer_iff.mp (hTN ht) x,
      by
        rw [eq_bot_iff]
        rintro t ⟨ht, htc⟩
        have : (t : H) ∈ T ⊓ centralizer (B : Set H) := by
          refine ⟨ht, mem_centralizer_iff.mpr fun b hb => ?_⟩
          have := mem_centralizer_iff.mp htc ⟨b, hBP hb⟩ (mem_subgroupOf.mpr hb)
          exact congrArg Subtype.val this
        rw [hTC] at this
        exact mem_bot.mpr (Subtype.ext (mem_bot.mp this))⟩
    ⟨X₁, by rw [hsup]; exact le_top,
      by
        rw [Asc76X.isSylowOf_iff_card] at hTsyl ⊢
        refine ⟨fun x hx => hTsyl.1 hx, ?_⟩
        rw [Nat.card_congr (subgroupOfEquivOfLe hTP).toEquiv,
          Nat.card_congr (subgroupOfEquivOfLe hXP).toEquiv]
        exact hTsyl.2,
      by
        obtain ⟨N, hNX, hNn, hNodd, k, hk⟩ := hX2
        refine ⟨N.subgroupOf P, fun x hx => hNX hx, ?_, ?_, k, ?_⟩
        · rw [normal_subgroupOf_iff (fun x hx => hNX hx : N.subgroupOf P ≤ X.subgroupOf P)]
          intro n x hn hx
          rw [mem_subgroupOf] at hn hx ⊢
          simp only [coe_mul, coe_inv]
          exact ((normal_subgroupOf_iff hNX).mp hNn) _ _ hn hx
        · rwa [Nat.card_congr (subgroupOfEquivOfLe (hNX.trans hXP)).toEquiv]
        · rw [relIndex_subgroupOf hXP]
          exact hk,
      by
        rw [hsup, tightlyEmbedded_subgroupOf_top_iff]
        exact htight⟩
  intro t ht
  have hmem := hres (mem_subgroupOf.mpr ht : (⟨t, hTP ht⟩ : P) ∈ T₁)
  have hmap : (B₁ ⊔ centralizer (B₁ : Set P)).map P.subtype ≤ B ⊔ centralizer (B : Set H) := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBP]
    refine sup_le_sup_left ?_ _
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc ⟨b, hBP hb⟩ (mem_subgroupOf.mpr hb))
  exact hmap ⟨_, hmem, rfl⟩

section Quotient

variable {H : Type} [Group H] [Finite H]

abbrev centerIn (B : Subgroup H) : Subgroup H := (center B).map B.subtype

omit [Finite H] in
theorem centerIn_le (B : Subgroup H) : centerIn B ≤ B := map_subtype_le _

omit [Finite H] in
theorem centerIn_le_centralizer (B : Subgroup H) : centerIn B ≤ centralizer (B : Set H) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val ((mem_center_iff.mp hz ⟨b, hb⟩))

omit [Finite H] in
theorem centerIn_normal {B : Subgroup H} (hB : normalizer (B : Set H) = ⊤) :
    (centerIn B).Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨z, hz', rfl⟩ := hz
  have hg : g ∈ normalizer (B : Set H) := hB ▸ mem_top g
  have hgz : g * z * g⁻¹ ∈ B := (mem_normalizer_iff.mp hg z).mp z.2
  refine ⟨⟨g * z * g⁻¹, hgz⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_center_iff]
  intro b
  apply Subtype.ext
  have hb : g⁻¹ * b * g ∈ B := by
    have := (mem_normalizer_iff.mp (inv_mem hg) b).mp b.2
    rwa [inv_inv] at this
  have hc := congrArg Subtype.val (mem_center_iff.mp hz' ⟨g⁻¹ * b * g, hb⟩)
  simp only [coe_mul] at hc ⊢
  calc (b : H) * (g * z * g⁻¹) = g * ((g⁻¹ * b * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * b * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * b := by group

omit [Finite H] in
theorem mem_centralizer_of_map {B : Subgroup H} (hBp : commutator B = ⊤) [hN : (centerIn B).Normal]
    {g : H} (hg : g ∈ normalizer (B : Set H))
    (hc : QuotientGroup.mk' (centerIn B) g ∈ centralizer ((B.map (QuotientGroup.mk' (centerIn B)) :
      Subgroup (H ⧸ centerIn B)) : Set (H ⧸ centerIn B))) :
    g ∈ centralizer (B : Set H) := by
  refine RankTwoSporadic.mem_centralizer_of_displacement hBp hg fun a ha => ?_
  apply centerIn_le_centralizer
  rw [← QuotientGroup.ker_mk' (centerIn B), MonoidHom.mem_ker]
  have h := mem_centralizer_iff.mp hc _ ⟨a, ha, rfl⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h]
  group

end Quotient

theorem hypII_of_odd_center {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤)
    (hodd : Odd (Nat.card (center A))) (h : HypII (A ⧸ center A)) : HypII A := by
  apply hypII_of_sup_eq_top
  intro H _ _ B T hTB ⟨eB⟩ hTF hTX
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTe, hT4, hTN, hTC⟩ := hTF
  obtain ⟨X, hXP, hTsyl, hX2, htight⟩ := hTX
  have hBp : commutator B = ⊤ := commutator_eq_top_of_mulEquiv eB hA
  have hNB : normalizer (B : Set H) = ⊤ := by
    rw [eq_top_iff, ← hTB]
    exact sup_le hTN le_normalizer
  have hBn : B.Normal := normalizer_eq_top_iff.mp hNB
  have : (centerIn B).Normal := centerIn_normal hNB
  set Z := centerIn B with hZdef
  set π := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hcB : Nat.card (center B) = Nat.card (center A) := by
    rw [← map_center_mulEquiv eB, card_map_of_injective eB.injective]
  have hk : Odd (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk', hZdef, centerIn, card_map_of_injective B.subtype_injective, hcB]
    exact hodd
  have hTp : IsPGroup 2 T := fun g => ⟨1, Subtype.ext (by simpa using hTe.2 g g.2)⟩
  let ψ : B →* H ⧸ Z := π.comp B.subtype
  have hψr : ψ.range = B.map π := by rw [MonoidHom.range_comp, range_subtype]
  have hψk : ψ.ker = center B := by
    ext x
    rw [MonoidHom.mem_ker]
    change π (x : H) = 1 ↔ _
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZdef, centerIn]
    constructor
    · rintro ⟨z, hz, hzx⟩
      rwa [← B.subtype_injective hzx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  let e₁ : B ⧸ center B ≃* ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivRange ψ)
  let e₂ : B ⧸ center B ≃* A ⧸ center A :=
    QuotientGroup.congr (center B) (center A) eB (map_center_mulEquiv eB)
  let eB' : (B.map π : Subgroup (H ⧸ Z)) ≃* A ⧸ center A :=
    ((MulEquiv.subgroupCongr hψr).symm.trans e₁.symm).trans e₂
  have hBn' : (B.map π).Normal := hBn.map π hπs
  have hX : TightlyEmbedded X := by
    rwa [hTB, tightlyEmbedded_subgroupOf_top_iff] at htight
  have hres := h (H ⧸ Z) (B.map π) (T.map π) ⟨eB'⟩
    ⟨isElemAbelian_map π hTe, by rwa [card_map_of_isPGroup π hk hTp],
      fun _ _ => by
        rw [normalizer_eq_top_iff.mpr hBn']
        exact mem_top _,
      by
        rw [eq_bot_iff]
        rintro _ ⟨⟨t, ht, rfl⟩, htc⟩
        have htC := mem_centralizer_of_map hBp (hNB ▸ mem_top t) htc
        have : t ∈ T ⊓ centralizer (B : Set H) := ⟨ht, htC⟩
        rw [hTC, mem_bot] at this
        rw [this, map_one]
        exact one_mem _⟩
    ⟨X.map π, by rw [← Subgroup.map_sup]; exact map_mono hXP, isSylowOf_map_of_odd_ker π hk hTsyl,
      by
        have := isTwoNilpotent_range hX2 (π.comp X.subtype)
        rwa [MonoidHom.range_comp, range_subtype] at this,
      by
        rw [← Subgroup.map_sup, hTB, map_top_of_surjective π hπs, tightlyEmbedded_subgroupOf_top_iff]
        exact tightlyEmbedded_map_of_odd_ker π hπs hk hX⟩
  intro t ht
  have hmem : π t ∈ ((B.map π ⊔ centralizer ((B.map π : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) :
      Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) := hres ⟨t, ht, rfl⟩
  rw [normal_mul] at hmem
  obtain ⟨_, ⟨b, hb, rfl⟩, c', hc', hbc⟩ := Set.mem_mul.mp hmem
  have hc'' : c' = π (b⁻¹ * t) := by
    rw [map_mul, map_inv, ← hbc, inv_mul_cancel_left]
  have hg : b⁻¹ * t ∈ centralizer (B : Set H) :=
    mem_centralizer_of_map hBp (hNB ▸ mem_top _) (hc'' ▸ hc')
  have := mul_mem_sup hb hg
  rwa [mul_inv_cancel_left] at this

@[expose] def SuzukiInvolutoryInner : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (Y : Type) [Group Y], (Y ≃* Sz a) → ∀ α : MulAut Y, α * α = 1 →
    ∃ y : Y, α = MulAut.conj y

theorem hypII_of_suzuki_cover (hSz : SuzukiInvolutoryInner) {A : Type}
    [Group A] [Finite A] (hA : commutator A = ⊤) {a : ℕ}
    (ha : 1 ≤ a) (e : A ⧸ center A ≃* Sz a) : HypII A := by
  intro H _ _ B T ⟨eB⟩ hTF _
  classical
  obtain ⟨hTe, -, hTN, -⟩ := hTF
  have hBp : commutator B = ⊤ := commutator_eq_top_of_mulEquiv eB hA
  intro t ht
  set α : MulAut B := B.normalizerMonoidHom ⟨t, hTN ht⟩ with hα
  have hα2 : α * α = 1 := by
    have h1 : (⟨t, hTN ht⟩ : normalizer (B : Set H)) * ⟨t, hTN ht⟩ = 1 :=
      Subtype.ext (by simpa [sq] using hTe.2 t ht)
    rw [hα, ← map_mul, h1, map_one]
  let ᾱ : MulAut (B ⧸ center B) := QuotientGroup.congr (center B) (center B) α
    (map_center_mulEquiv α)
  have hᾱ : ∀ x : B, ᾱ (x : B ⧸ center B) = ((α x : B) : B ⧸ center B) := fun _ => rfl
  have hᾱ2 : ᾱ * ᾱ = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, hᾱ, hᾱ, ← MulAut.mul_apply, hα2, MulAut.one_apply, MulAut.one_apply]
  let eQ : B ⧸ center B ≃* Sz a :=
    (QuotientGroup.congr (center B) (center A) eB (map_center_mulEquiv eB)).trans e
  obtain ⟨yb, hyb⟩ :=
    hSz a ha _ eQ ᾱ hᾱ2
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hg : (y : H)⁻¹ * t ∈ centralizer (B : Set H) := by
    refine RankTwoSporadic.mem_centralizer_of_displacement hBp
      (mul_mem (inv_mem (le_normalizer y.2)) (hTN ht)) fun z hz => ?_
    have h1 := DFunLike.congr_fun hyb ((⟨z, hz⟩ : B) : B ⧸ center B)
    rw [hᾱ, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    set w : B := (y * ⟨z, hz⟩ * y⁻¹)⁻¹ * α ⟨z, hz⟩ with hw
    have h1' : w ∈ center B := by
      have := inv_mem h1
      rwa [mul_inv_rev, inv_inv] at this
    have hwc : (w : H) ∈ centralizer (B : Set H) := centerIn_le_centralizer B ⟨w, h1', rfl⟩
    have hαz : ((α ⟨z, hz⟩ : B) : H) = t * z * t⁻¹ := rfl
    have hwy : (y : H)⁻¹ * w * y = w := by
      have := mem_centralizer_iff.mp hwc y y.2
      rw [mul_assoc, ← this, inv_mul_cancel_left]
    have hkey : z⁻¹ * ((y : H)⁻¹ * t * z * ((y : H)⁻¹ * t)⁻¹) = (y : H)⁻¹ * w * y := by
      rw [hw, coe_mul, coe_inv, hαz, coe_mul, coe_mul, coe_inv]
      group
    rw [hkey, hwy]
    exact hwc
  have := mul_mem_sup y.2 hg
  rwa [mul_inv_cancel_left] at this

end CFSG.ComponentClassification.RankTwoBender
