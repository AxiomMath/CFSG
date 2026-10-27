module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Stmts
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011BarIso
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage2.Local.P34
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_conjugate_iff)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (F20_conj_mem F20_le_OddCore)

@[expose] def Ctx2011 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) : Prop :=
  Fail20 G z k S (Cen z) ∧ TypeCl z k S

structure JSetup20 {G : Type} [Group G] [Finite G] (z : G) (S : Subgroup G) (g : G) : Prop where
  comp : IsPComponent 2 ((J0 z g).subgroupOf (H0 z g))
  simple : IsSimpleGroup (HBar (J0 z g))
  nonab : ∃ a b : HBar (J0 z g), a * b ≠ b * a
  layer_le : Em (Cen z) ≤ J0 z g
  z_mem : z ∈ J0 z g
  t_mem : zc z g ∈ J0 z g
  central : IsCentralInvolution (mkH (J0 z g) ⟨z, z_mem⟩)
  cfg : ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (K₁ K₂ : Subgroup G),
    Stage1Pair G z S q L₁ L₂ → CompData z K₁ K₂ L₁ L₂ →
      IVK.Proofs2.Ivk93Cfg (mkH (J0 z g) ⟨z, z_mem⟩) q (barIn (J0 z g) K₁) (barIn (J0 z g) K₂)

@[expose] def Adapter20_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx2011 G z k S →
    ∀ g : G, Case20A z S g → JSetup20 z S g

@[expose] def SylowIn20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx2011 G z k S →
    ∀ g : G, Case20A z S g → JSetup20 z S g →
      ∃ S₀ : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S₀ (Cen z) ∧ S₀ ≤ J0 z g ∧ zc z g ∈ S₀

@[expose] def Coprime20b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx2011 G z k S →
    ∀ g : G, Case20A z S g → JSetup20 z S g →
      ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(F20 z) → ¬ r ∣ Nat.card ↥⁅pPrimeCoreOf 2 (J0 z g), J0 z g⁆

@[expose] def CentS20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx2011 G z k S →
    ∀ g : G, Case20A z S g → JSetup20 z S g → S ≤ J0 z g →
      (∀ s ∈ S, ∀ f ∈ F20 z ⊓ pPrimeCoreOf 2 (H0 z g), s * f = f * s) ∧
      ∀ j ∈ J0 z g, ∃ d ∈ J0 z g, (∀ f ∈ F20 z ⊓ pPrimeCoreOf 2 (H0 z g), d * f = f * d) ∧
        j * d⁻¹ ∈ pPrimeCoreOf 2 (J0 z g)

@[expose] def YStep20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx2011 G z k S →
    ∀ g : G, Case20A z S g → JSetup20 z S g → S ≤ J0 z g →
      ∃ y ∈ S, orderOf y = 2 ∧ y ≠ z ∧ y ∈ S1 S z ∧
        ∃ j ∈ J0 z g, y * (j⁻¹ * z * j)⁻¹ ∈ pPrimeCoreOf 2 (J0 z g)

@[expose] def CentA20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx2011 G z k S →
    ∀ g : G, Case20A z S g → JSetup20 z S g → S ≤ J0 z g →
      ∀ y ∈ S, y ∈ S1 S z → orderOf y = 2 → (∀ f ∈ F0 z g, y * f = f * y) →
        F20 z ⊓ pPrimeCoreOf 2 (H0 z g) ≤ F0 z g → ∀ a ∈ OddCore z, a * y = y * a

section Conj

variable {G : Type} [Group G]

theorem zc_mul (z g c : G) : zc z (g * c) = c⁻¹ * zc z g * c := by
  simp only [zc]; group

theorem mem_Ag_mul (z g c : G) {x : G} : x ∈ Ag z (g * c) ↔ c * x * c⁻¹ ∈ Ag z g := by
  unfold Ag
  rw [bar_mem_conjugate_iff, bar_mem_conjugate_iff]
  have e : g * c * x * (g * c)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ := by group
  rw [e]

theorem F0_mul (z g : G) {c : G} (hc : c ∈ Cen z) : F0 z (g * c) = cmap c⁻¹ (F0 z g) := by
  ext x
  rw [mem_cmap, inv_inv]
  constructor
  · rintro ⟨hxF, hxA⟩
    have hF : c * x * c⁻¹ ∈ F20 z := F20_conj_mem z hc hxF
    exact ⟨hF, (mem_Ag_mul z g c).1 hxA⟩
  · rintro ⟨hxF, hxA⟩
    have hF : x ∈ F20 z := by
      have := F20_conj_mem z ((Cen z).inv_mem hc) hxF
      have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rwa [e] at this
    exact ⟨hF, (mem_Ag_mul z g c).2 hxA⟩

theorem normalizer_cmap (c : G) (F : Subgroup G) :
    normalizer ((cmap c F : Subgroup G) : Set G) = cmap c (normalizer (F : Set G)) := by
  ext x
  rw [Subgroup.mem_normalizer_iff, mem_cmap, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (c * y * c⁻¹)
    rw [mem_cmap, mem_cmap] at this
    have e1 : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    have e2 : c⁻¹ * (x * (c * y * c⁻¹) * x⁻¹) * c = (c⁻¹ * x * c) * y * (c⁻¹ * x * c)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro h y
    rw [mem_cmap, mem_cmap]
    have := h (c⁻¹ * y * c)
    have e2 : c⁻¹ * (x * y * x⁻¹) * c = (c⁻¹ * x * c) * (c⁻¹ * y * c) * (c⁻¹ * x * c)⁻¹ := by group
    rw [e2]
    exact this

theorem H0_mul (z g : G) {c : G} (hc : c ∈ Cen z) : H0 z (g * c) = cmap c⁻¹ (H0 z g) := by
  unfold H0
  rw [F0_mul z g hc, normalizer_cmap]

theorem J0_mul [Finite G] (z g : G) {c : G} (hc : c ∈ Cen z) : J0 z (g * c) = cmap c⁻¹ (J0 z g) := by
  unfold J0
  rw [H0_mul z g hc, pLayerOf_cmap]

theorem card_F0_mul (z g : G) {c : G} (hc : c ∈ Cen z) :
    Nat.card ↥(F0 z (g * c)) = Nat.card ↥(F0 z g) := by
  rw [F0_mul z g hc]
  exact Nat.card_congr ((MulAut.conj c⁻¹).subgroupMap (F0 z g)).toEquiv.symm

end Conj

section Dev

variable {G : Type} [Group G] [Finite G]

open CFSG.ABGLocalTools in
theorem exists_conj_sylowOf {K P₁ P₂ : Subgroup G} (h₁ : IsSylowOf 2 P₁ K) (h₂ : IsSylowOf 2 P₂ K) :
    ∃ c ∈ K, ∀ x, x ∈ P₂ ↔ c⁻¹ * x * c ∈ P₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₁, hQ₁⟩ := h₁.exists_sylow_eq_subgroupOf
  obtain ⟨Q₂, hQ₂⟩ := h₂.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K Q₁ Q₂
  refine ⟨g, g.2, fun x => ?_⟩
  by_cases hx : x ∈ K
  · have h1 : (⟨x, hx⟩ : ↥K) ∈ (Q₂ : Subgroup ↥K) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (Q₁ : Subgroup ↥K) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥K) ∈ (Q₂ : Subgroup ↥K) ↔ x ∈ P₂ := by
      rw [hQ₂]; exact Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (Q₁ : Subgroup ↥K) ↔ (g : G)⁻¹ * x * g ∈ P₁ := by
      rw [hQ₁]; exact Subgroup.mem_subgroupOf (H := P₁) (K := K) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxP₂ : x ∉ P₂ := fun h => hx (h₂.le h)
    have hxP₁ : (g : G)⁻¹ * x * g ∉ P₁ := fun h => hx (by
      have := K.mul_mem (K.mul_mem g.2 (h₁.le h)) (K.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxP₂, fun h => absurd h hxP₁⟩

open CFSG.ABGLocalTools in
theorem exists_g_conj {z : G} {S S₀ : Subgroup G} (hS : IsSylowOf 2 S (Cen z)) (hS₀ : IsSylowOf 2 S₀ (Cen z))
    {g : G} (hg : Case20A z S g) (hS₀J : S₀ ≤ J0 z g) (htS₀ : zc z g ∈ S₀) :
    ∃ g' : G, Case20A z S g' ∧ Nat.card ↥(F0 z g') = Nat.card ↥(F0 z g) ∧ S ≤ J0 z g' := by
  obtain ⟨c, hcC, hc⟩ := exists_conj_sylowOf hS hS₀
  have hzc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  refine ⟨g * c, ⟨?_, ?_, ?_⟩, card_F0_mul z g hcC, ?_⟩
  · rw [zc_mul]; exact (hc _).1 htS₀
  · intro hmem
    apply hg.t_ne
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcomm : c * z ^ n = z ^ n * c := by
      have : Commute c z := hzc
      exact (this.zpow_right n).eq
    have e : zc z g = c * zc z (g * c) * c⁻¹ := by rw [zc_mul]; group
    rw [e, ← hn]
    have : c * z ^ n * c⁻¹ = z ^ n := by rw [hcomm]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers z n
  · have h1 : F0 z (g * c) ≠ ⊥ := by
      rw [F0_mul z g hcC]
      intro h
      apply hg.inter
      exact (Subgroup.map_eq_bot_iff_of_injective (F0 z g) (f := (MulAut.conj c⁻¹).toMonoidHom)
        (MulAut.conj c⁻¹).injective).1 h
    exact h1
  · intro x hx
    rw [J0_mul z g hcC, mem_cmap, inv_inv]
    apply hS₀J
    exact (hc _).2 (by have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
                       rw [e]; exact hx)

end Dev

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem F0_le_F1 (z g : G) : F0 z g ≤ F20 z ⊓ pPrimeCoreOf 2 (H0 z g) := by
  refine le_inf inf_le_left ?_
  have hFH : F0 z g ≤ H0 z g := Subgroup.le_normalizer
  have hodd : Nat.Coprime 2 (Nat.card ↥(F0 z g)) := by
    have h1 : Nat.card ↥(F0 z g) ∣ Nat.card ↥(OddCore z) :=
      Subgroup.card_dvd_of_le (inf_le_left.trans (F20_le_OddCore z))
    have h2 : Nat.Coprime 2 (Nat.card ↥(OddCore z)) :=
      CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 2 (Cen z)
    exact Nat.Coprime.coprime_dvd_right h1 h2
  exact CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf hFH le_rfl hodd

omit [Finite G] in
theorem eq_one_or_eq_of_zpowers {z y : G} (hz2 : z * z = 1) (h : y ∈ zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  have hsq : z ^ 2 = 1 := by rw [sq]; exact hz2
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [← Int.emod_add_mul_ediv n 2, h0, zero_add, zpow_mul]
    simp [hsq]
  · right
    rw [← Int.emod_add_mul_ediv n 2, h1, zpow_add, zpow_mul]
    simp [hsq]

end Assembly

section Pkg

variable {G : Type} [Group G] [Finite G]

open CFSG.ABGLocalTools in
theorem pkg2010_of_parts (hAd : Adapter20_9) (hSyl : SylowIn20) (hCS : CentS20) (hY : YStep20)
    (hCA : CentA20) : Pkg2010 := by
  intro G _ _ z k S M hF hMC hT g₀ hg₀
  subst hMC
  have hctx : Stage2Ctx G z k S := hF.ctx.ctx17.ctx
  have hC : Ctx2011 G z k S := ⟨hF, hT⟩
  have hSyl2 : IsSylowOf 2 S (Cen z) := hctx.sylow
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hctx.orderOf_z, pow_two] at this
  have : Nonempty {g : G // Case20A z S g} := ⟨⟨g₀, hg₀⟩⟩
  obtain ⟨⟨g₁, hg₁⟩, hmax⟩ := Finite.exists_max (fun x : {g : G // Case20A z S g} => Nat.card ↥(F0 z x.1))
  have hJ₁ := hAd G z k S hC g₁ hg₁
  obtain ⟨S₀, hS₀, hS₀J, htS₀⟩ := hSyl G z k S hC g₁ hg₁ hJ₁
  obtain ⟨g₂, hg₂, hcard, hSJ₂⟩ := exists_g_conj hSyl2 hS₀ hg₁ hS₀J htS₀
  have hmax₂ : ∀ g' : G, Case20A z S g' → Nat.card ↥(F0 z g') ≤ Nat.card ↥(F0 z g₂) := fun g' hg' => by
    rw [hcard]; exact hmax ⟨g', hg'⟩
  have hJ₂ := hAd G z k S hC g₂ hg₂
  obtain ⟨hCS1, hCS2⟩ := hCS G z k S hC g₂ hg₂ hJ₂ hSJ₂
  obtain ⟨y, hyS, hy2, hyz, hyS1, j, hjJ, hjy⟩ := hY G z k S hC g₂ hg₂ hJ₂ hSJ₂
  obtain ⟨d, hdJ, hdF, hjd⟩ := hCS2 j hjJ
  set F₁ : Subgroup G := F20 z ⊓ pPrimeCoreOf 2 (H0 z g₂) with hF₁def
  set J₂ : Subgroup G := J0 z g₂ with hJ₂def
  set D : Subgroup G := J₂ ⊓ centralizer (F₁ : Set G) with hDdef
  have hmemD : ∀ x ∈ J₂, (∀ f ∈ F₁, x * f = f * x) → x ∈ D := fun x hx hxf =>
    ⟨hx, Subgroup.mem_centralizer_iff.2 fun f hf => (hxf f hf).symm⟩
  have hzJ : z ∈ J₂ := hJ₂.z_mem
  have hzF : ∀ f ∈ F₁, z * f = f * z := fun f hf =>
    (Subgroup.mem_centralizer_singleton_iff.1 (oddCore_le_Cen z (F20_le_OddCore z hf.1) :) ).symm
  set N : Subgroup G := pPrimeCoreOf 2 J₂ with hNdef
  set z' : G := d⁻¹ * z * d with hz'
  have hdD : d ∈ D := hmemD d hdJ hdF
  have hz'J : z' ∈ J₂ := J₂.mul_mem (J₂.mul_mem (J₂.inv_mem hdJ) hzJ) hdJ
  have hz'F : ∀ f ∈ F₁, z' * f = f * z' := by
    intro f hf
    have hcz : Commute z f := hzF f hf
    have hcd : Commute d f := hdF f hf
    exact (((hcd.inv_left).mul_left hcz).mul_left hcd).eq
  have hz'D : z' ∈ D := hmemD z' hz'J hz'F
  have hyJ : y ∈ J₂ := hSJ₂ hyS
  have hyD : y ∈ D := hmemD y hyJ (fun f hf => hCS1 y hyS f hf)
  have hyz'N : y * z'⁻¹ ∈ N := by
    set n : G := j * d⁻¹ with hn
    have hnN : n ∈ N := hjd
    have hjn : j = n * d := by simp only [hn]; group
    have e1 : (j⁻¹ * z * j) * z'⁻¹ = d⁻¹ * (n⁻¹ * (z * n * z⁻¹)) * d := by
      rw [hjn]; simp only [hz']; group
    have e2 : y * z'⁻¹ = (y * (j⁻¹ * z * j)⁻¹) * ((j⁻¹ * z * j) * z'⁻¹) := by group
    rw [e2, e1]
    refine N.mul_mem hjy ?_
    have h3 : n⁻¹ * (z * n * z⁻¹) ∈ N := N.mul_mem (N.inv_mem hnN) (pPrimeCoreOf_conj_mem hzJ hnN)
    have h4 := pPrimeCoreOf_conj_mem (J := J₂) (J₂.inv_mem hdJ) h3
    simpa using h4
  have hyz'ND : y * z'⁻¹ ∈ pPrimeCoreOf 2 D := by
    have hle : N ⊓ D ≤ pPrimeCoreOf 2 D := by
      refine CFSG.RankThree.PartTwo.Sec14.le_pPrimeCoreOf inf_le_right ?_ ?_
      · intro x hx
        have hxJ : x ∈ J₂ := hx.1
        rw [Subgroup.mem_normalizer_iff]
        intro m
        constructor
        · intro hm
          exact ⟨pPrimeCoreOf_conj_mem hxJ hm.1, D.mul_mem (D.mul_mem hx hm.2) (D.inv_mem hx)⟩
        · intro hm
          have h1 := pPrimeCoreOf_conj_mem (J := J₂) (J₂.inv_mem hxJ) hm.1
          have h2 := D.mul_mem (D.mul_mem (D.inv_mem hx) hm.2) hx
          have e : x⁻¹ * (x * m * x⁻¹) * x⁻¹⁻¹ = m := by group
          have e' : x⁻¹ * (x * m * x⁻¹) * x = m := by group
          rw [e] at h1
          rw [e'] at h2
          exact ⟨h1, h2⟩
      · have h1 : Nat.card ↥(N ⊓ D) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le inf_le_left
        have h2 : Nat.Coprime 2 (Nat.card ↥N) := by
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 2 J₂
        exact Nat.Coprime.coprime_dvd_right h1 h2
    exact hle ⟨hyz'N, D.mul_mem hyD (D.inv_mem hz'D)⟩
  have hord' : orderOf z' = 2 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj d⁻¹) z
    rw [MulAut.conj_apply] at h1
    have e : d⁻¹ * z * d⁻¹⁻¹ = z' := by simp only [hz', inv_inv]
    rw [e] at h1
    rw [h1]; exact hctx.orderOf_z
  have hzD : orderOf (⟨z', hz'D⟩ : ↥D) = 2 := by
    rw [← hord']; exact (Subgroup.orderOf_coe (⟨z', hz'D⟩ : ↥D)).symm
  have huD : orderOf (⟨y, hyD⟩ : ↥D) = 2 := by
    rw [← hy2]; exact (Subgroup.orderOf_coe (⟨y, hyD⟩ : ↥D)).symm
  have hmk : mkH D ⟨y, hyD⟩ = mkH D ⟨z', hz'D⟩ := by
    obtain ⟨x', hx', hxe⟩ := hyz'ND
    have hx'e : x' = (⟨y, hyD⟩ : ↥D) * (⟨z', hz'D⟩ : ↥D)⁻¹ := Subtype.ext hxe
    have h1 : mkH D ((⟨y, hyD⟩ : ↥D) * (⟨z', hz'D⟩ : ↥D)⁻¹) = 1 := by
      rw [← hx'e]; exact (mkH_eq_one_iff D).2 hx'
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.1 h1
  obtain ⟨p, hpO, hpe⟩ := exists_mem_core_conj D hzD huD hmk
  set h : G := d * (p : G) with hhdef
  have hpD : (p : G) ∈ D := p.2
  have hhD : h ∈ D := D.mul_mem hdD hpD
  have hyh : y = (p : G)⁻¹ * z' * p := by
    have := congrArg Subtype.val hpe
    simpa using this
  have hzh : zc z h = y := by
    simp only [zc, hhdef, hyh, hz']; group
  have hhF : ∀ f ∈ F₁, h * f = f * h := fun f hf =>
    (Subgroup.mem_centralizer_iff.1 hhD.2 f hf).symm
  have hF₁h : F₁ ≤ F0 z h := by
    intro f hf
    have hAg : f ∈ Ag z h := by
      unfold Ag
      refine bar_mem_conjugate_iff.2 ?_
      have : h * f * h⁻¹ = f := by rw [hhF f hf]; group
      rw [this]
      exact F20_le_OddCore z hf.1
    exact ⟨hf.1, hAg⟩
  have hcaseh : Case20A z S h := by
    refine ⟨by rw [hzh]; exact hyS, ?_, ?_⟩
    · rw [hzh]
      intro hmem
      rcases eq_one_or_eq_of_zpowers hz2 hmem with h1 | h1
      · rw [h1, orderOf_one] at hy2; omega
      · exact hyz h1
    · intro hbot
      have h1 : F₁ ≤ ⊥ := (hF₁h.trans (le_of_eq hbot))
      exact hg₂.inter (le_bot_iff.1 ((F0_le_F1 z g₂).trans h1))
  have hF0le : F0 z g₂ ≤ F0 z h := (F0_le_F1 z g₂).trans hF₁h
  have hEq : F0 z g₂ = F0 z h := Subgroup.eq_of_le_of_card_ge hF0le (hmax₂ h hcaseh)
  have hF₁eq : F₁ ≤ F0 z g₂ := fun f hf => by rw [hEq]; exact hF₁h hf
  have hA : ∀ a ∈ OddCore z, a * y = y * a := by
    refine hCA G z k S hC g₂ hg₂ hJ₂ hSJ₂ y hyS hyS1 hy2 ?_ hF₁eq
    intro f hf
    have hfh : f ∈ F0 z h := by rw [← hEq]; exact hf
    have hmem : h * f * h⁻¹ ∈ OddCore z := by
      have h2 : f ∈ Ag z h := hfh.2
      unfold Ag at h2
      exact bar_mem_conjugate_iff.1 h2
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (oddCore_le_Cen z hmem)
    have e : f * zc z h = zc z h * f := by
      simp only [zc]
      calc f * (h⁻¹ * z * h) = h⁻¹ * ((h * f * h⁻¹) * z) * h := by group
        _ = h⁻¹ * (z * (h * f * h⁻¹)) * h := by rw [hc]
        _ = h⁻¹ * z * h * f := by group
    rw [hzh] at e
    exact e.symm
  have hH : H0 z h = H0 z g₂ := by unfold H0; rw [← hEq]
  have hJ' : J0 z h = J0 z g₂ := by unfold J0; rw [hH]
  have key : ∀ (H H' J J' : Subgroup G), H = H' → J = J' →
      IsSimpleGroup ↥(barIn H J) → IsSimpleGroup ↥(barIn H' J') := by
    intro H H' J J' h1 h2
    subst h1; subst h2
    exact id
  refine ⟨h, hcaseh, by rw [hzh]; exact hy2, by rw [hzh]; exact hyS1,
    fun a ha => by rw [hzh]; exact hA a ha, ?_, ?_⟩
  · rw [hH]; exact hSJ₂.trans (J0_le_H0 z g₂)
  · exact key _ _ _ _ hH.symm hJ'.symm (simple_barIn_of_simple (J0_le_H0 z g₂) (fun h hh j hj => J0_conj_mem z g₂ hh hj) hJ₂.simple)

end Pkg

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
