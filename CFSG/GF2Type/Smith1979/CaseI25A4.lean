module

public import CFSG.GF2Type.Smith1979.CaseI25A3
public import CFSG.GF2Type.Smith1979.CaseI25A4Abs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def Kbar (S : Setting G) (g : G) (t : S.O) : Subgroup S.O :=
  Subgroup.closure {z | ∃ x ∈ Delta S g t, ∃ y ∈ Delta S g t, z = x * y}

@[expose] noncomputable def conjLbar (S : Setting G) (g : G) : NLbar S g →* MulAut (S.Lbar g) :=
  (S.Lbar g).normalizerMonoidHom.comp
    (Subgroup.inclusion (inf_le_right : NLbar S g ≤ normalizer (S.Lbar g : Set S.O)))

theorem coe_conjLbar (S : Setting G) (g : G) (n : NLbar S g) (l : S.Lbar g) :
    ((conjLbar S g n l : S.Lbar g) : S.O) = (n : S.O) * l * (n : S.O)⁻¹ := rfl

theorem Kbar_le_Lbar {t : S.O} (ht : t ∈ S.Lbar g) : Kbar S g t ≤ S.Lbar g := by
  refine (closure_le _).mpr ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact mul_mem (delta_subset_Lbar ht hx) (delta_subset_Lbar ht hy)

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
  {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
  (hpol : Q.polarBilin = beta H C ht ht1 hVQ) (hX : RmodN S g t = omegaGroup Q hQ)
  (hE : LmodN S g t = pointRadical Q (aV ht))
  (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
include hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing

theorem invariant_functional_of_form (hΔ : (Delta S g t).ncard = 6) :
    (∀ l : List (Delta S g t), l.Nodup →
      ((l.map (fun x : Delta S g t => (x : S.O))).prod = 1 ↔ l = [] ∨ l.length = 6)) ∧
    ∃ f : S.Lbar g →* Multiplicative (ZMod 2),
      (∀ x (hx : x ∈ Delta S g t), f ⟨x, delta_subset_Lbar ht hx⟩ = Multiplicative.ofAdd 1) ∧
      (∀ (n : NLbar S g) (l : S.Lbar g), f (conjLbar S g n l) = f l) ∧
      f.ker.map (S.Lbar g).subtype = Kbar S g t ∧ f.ker.index = 2 ∧
      (⟨t, ht⟩ : S.Lbar g) ∉ f.ker ∧
      (∀ z ∈ Kbar S g t, z ≠ 1 → ∃ x ∈ Delta S g t, ∃ y ∈ Delta S g t, x ≠ y ∧ z = x * y) ∧
      (∀ a ∈ Kbar S g t, a ≠ 1 → ∀ b ∈ Kbar S g t, b ≠ 1 →
        ∃ n ∈ NLbar S g, n * a * n⁻¹ = b) ∧
      (∀ M : Subgroup S.O, M ≤ S.Lbar g → (∀ n ∈ NLbar S g, ∀ m ∈ M, n * m * n⁻¹ ∈ M) →
        M ≠ ⊥ → M ≠ S.Lbar g → M = Kbar S g t) := by
  classical
  have hcl := closure_Delta_of_form hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  have halt := alt_le_image_of_form hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  have hw : S.width = 6 := by
    rw [width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ, h6]
  have hcomm : ∀ a b : S.Lbar g, a * b = b * a := fun a b =>
    Subtype.ext (Lbar_comm S H.conj_mem a.2 b.2)
  have hsq : ∀ a : S.Lbar g, a * a = 1 := fun a =>
    Subtype.ext (mul_self_of_mem_Lbar S H.conj_mem a.2)
  have hcard : Nat.card (S.Lbar g) = 2 ^ 5 := by rw [C.card_Lbar, hw]
  have hι : Fintype.card (Delta S g t) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hΔ
  let d : Delta S g t → S.Lbar g := fun x => ⟨x, delta_subset_Lbar ht x.2⟩
  have himg : (S.Lbar g).subtype '' Set.range d = Delta S g t := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact y.2
    · intro hx
      exact ⟨d ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hgen : Subgroup.closure (Set.range d) = ⊤ := by
    rw [eq_top_iff]
    intro l _
    have h1 : (l : S.O) ∈ Subgroup.closure (Delta S g t) := by
      rw [hcl]
      exact l.2
    rw [← himg, ← MonoidHom.map_closure] at h1
    obtain ⟨y, hy, hyl⟩ := h1
    have : y = l := Subtype.ext hyl
    rw [← this]
    exact hy
  let Γ : Set (S.Lbar g ≃* S.Lbar g) := Set.range (fun n : NLbar S g => conjLbar S g n)
  have hΓ : ∀ φ ∈ Γ, ∃ σ : Equiv.Perm (Delta S g t), ∀ i, φ (d i) = d (σ i) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨permDelta S g t n, fun i => Subtype.ext rfl⟩
  have hΓalt : ∀ σ ∈ alternatingGroup (Delta S g t),
      ∃ φ ∈ Γ, ∀ i, φ (d i) = d (σ i) := by
    intro σ hσ
    obtain ⟨n, rfl⟩ := halt hσ
    exact ⟨conjLbar S g n, ⟨n, rfl⟩, fun i => Subtype.ext rfl⟩
  obtain ⟨hrel, f, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ :=
    sixGenerators hcomm hsq hcard hι d hgen Γ hΓ hΓalt
  have hKmap : f.ker.map (S.Lbar g).subtype = Kbar S g t := by
    rw [hf3, MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, j, rfl⟩, rfl⟩
      exact ⟨i, i.2, j, j.2, rfl⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨d ⟨x, hx⟩ * d ⟨y, hy⟩, ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl⟩, rfl⟩
  have hmemK : ∀ a ∈ Kbar S g t, ∃ a' ∈ f.ker, ((a' : S.Lbar g) : S.O) = a := by
    intro a ha
    rw [← hKmap] at ha
    exact ha
  have hprod : ∀ l : List (Delta S g t),
      (((l.map d).prod : S.Lbar g) : S.O) = (l.map (fun x : Delta S g t => (x : S.O))).prod := by
    intro l
    have := map_list_prod (S.Lbar g).subtype (l.map d)
    rw [List.map_map] at this
    exact this
  refine ⟨fun l hl => ?_, f, fun x hx => hf1 ⟨x, hx⟩, fun n l => hf2 _ ⟨n, rfl⟩ l, hKmap, hf4,
    ?_, ?_, ?_, ?_⟩
  · rw [← hprod, ← (hrel l hl)]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · intro h
    rw [MonoidHom.mem_ker, hf1 ⟨t, mem_Delta_self S g t⟩] at h
    exact absurd h (by decide)
  · intro z hz hz1
    obtain ⟨z', hz', rfl⟩ := hmemK z hz
    obtain ⟨i, j, hij, rfl⟩ := hf5 z' hz' (fun h => hz1 (by rw [h]; rfl))
    exact ⟨i, i.2, j, j.2, fun h => hij (Subtype.ext h), rfl⟩
  · intro a ha ha1 b hb hb1
    obtain ⟨a', ha', rfl⟩ := hmemK a ha
    obtain ⟨b', hb', rfl⟩ := hmemK b hb
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hf6 a' ha' (fun h => ha1 (by rw [h]; rfl)) b' hb'
      (fun h => hb1 (by rw [h]; rfl))
    exact ⟨n, n.2, congrArg Subtype.val hn⟩
  · intro M hML hMinv hM0 hMtop
    have hM'inv : ∀ φ ∈ Γ, ∀ m ∈ M.subgroupOf (S.Lbar g), φ m ∈ M.subgroupOf (S.Lbar g) := by
      rintro _ ⟨n, rfl⟩ m hm
      exact hMinv n n.2 m hm
    have hM'0 : M.subgroupOf (S.Lbar g) ≠ ⊥ := by
      intro h
      apply hM0
      rw [eq_bot_iff]
      intro m hm
      have : (⟨m, hML hm⟩ : S.Lbar g) ∈ M.subgroupOf (S.Lbar g) := hm
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hM'top : M.subgroupOf (S.Lbar g) ≠ ⊤ := by
      intro h
      apply hMtop
      refine le_antisymm hML fun l hl => ?_
      have : (⟨l, hl⟩ : S.Lbar g) ∈ M.subgroupOf (S.Lbar g) := by
        rw [h]
        exact mem_top _
      exact this
    have := hf7 (M.subgroupOf (S.Lbar g)) hM'inv hM'0 hM'top
    rw [← hKmap, ← this, Subgroup.map_subgroupOf_eq_of_le hML]

end Context

section NoForm

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem invariant_functional (hΔ : (Delta S g t).ncard = 6) :
    (∀ l : List (Delta S g t), l.Nodup →
      ((l.map (fun x : Delta S g t => (x : S.O))).prod = 1 ↔ l = [] ∨ l.length = 6)) ∧
    ∃ f : S.Lbar g →* Multiplicative (ZMod 2),
      (∀ x (hx : x ∈ Delta S g t), f ⟨x, delta_subset_Lbar ht hx⟩ = Multiplicative.ofAdd 1) ∧
      (∀ (n : NLbar S g) (l : S.Lbar g), f (conjLbar S g n l) = f l) ∧
      f.ker.map (S.Lbar g).subtype = Kbar S g t ∧ f.ker.index = 2 ∧
      (⟨t, ht⟩ : S.Lbar g) ∉ f.ker ∧
      (∀ z ∈ Kbar S g t, z ≠ 1 → ∃ x ∈ Delta S g t, ∃ y ∈ Delta S g t, x ≠ y ∧ z = x * y) ∧
      (∀ a ∈ Kbar S g t, a ≠ 1 → ∀ b ∈ Kbar S g t, b ≠ 1 →
        ∃ n ∈ NLbar S g, n * a * n⁻¹ = b) ∧
      (∀ M : Subgroup S.O, M ≤ S.Lbar g → (∀ n ∈ NLbar S g, ∀ m ∈ M, n * m * n⁻¹ ∈ M) →
        M ≠ ⊥ → M ≠ S.Lbar g → M = Kbar S g t) := by
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := hΩ.exists_form
  exact invariant_functional_of_form hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ

theorem relIndex_Kbar (hΔ : (Delta S g t).ncard = 6) :
    (Kbar S g t).relIndex (S.Lbar g) = 2 ∧ t ∉ Kbar S g t := by
  obtain ⟨-, f, -, -, hKmap, hidx, hnot, -⟩ :=
    invariant_functional hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine ⟨?_, fun htK => hnot ?_⟩
  · have : (Kbar S g t).subgroupOf (S.Lbar g) = f.ker := by
      rw [← hKmap]
      exact Subgroup.comap_map_eq_self_of_injective (S.Lbar g).subtype_injective f.ker
    rw [Subgroup.relIndex, this]
    exact hidx
  · rw [← hKmap] at htK
    obtain ⟨y, hy, hyt⟩ := htK
    have : y = ⟨t, ht⟩ := Subtype.ext hyt
    rw [← this]
    exact hy

theorem card_Kbar (hΔ : (Delta S g t).ncard = 6) : Nat.card (Kbar S g t) = 2 ^ 4 := by
  have hw : S.width = 6 := by
    rw [width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ, h6]
  have h1 := (relIndex_Kbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ).1
  have h2 := Subgroup.relIndex_mul_card (H := Kbar S g t) (K := S.Lbar g)
  rw [inf_of_le_left (Kbar_le_Lbar ht), h1, C.card_Lbar, hw] at h2
  omega

theorem conj_mem_Kbar (hΔ : (Delta S g t).ncard = 6) {n k : S.O} (hn : n ∈ NLbar S g)
    (hk : k ∈ Kbar S g t) : n * k * n⁻¹ ∈ Kbar S g t := by
  obtain ⟨-, f, -, hf2, hKmap, -⟩ := invariant_functional hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  rw [← hKmap] at hk ⊢
  obtain ⟨k', hk', rfl⟩ := hk
  refine ⟨conjLbar S g ⟨n, hn⟩ k', ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, hf2 ⟨n, hn⟩ k']
  exact hk'

theorem Kbar_eq_commutator (hΔ : (Delta S g t).ncard = 6) :
    Kbar S g t = ⁅S.Lbar g, NLbar S g⁆ := by
  obtain ⟨-, f, hf1, hf2, hKmap, -⟩ := invariant_functional hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine le_antisymm ((closure_le _).mpr ?_) (Subgroup.commutator_le.mpr ?_)
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := hy
    have hmt : m * t * m⁻¹ ∈ S.Lbar g := delta_subset_Lbar ht ⟨m, hm, rfl⟩
    have hkt : k * t * k⁻¹ ∈ S.Lbar g := delta_subset_Lbar ht ⟨k, hk, rfl⟩
    have hsq : (m * t * m⁻¹) * (m * t * m⁻¹) = 1 := mul_self_of_mem_Lbar S H.conj_mem hmt
    have hc : (m * t * m⁻¹) * (k * t * k⁻¹) = (k * t * k⁻¹) * (m * t * m⁻¹) :=
      Lbar_comm S H.conj_mem hmt hkt
    have hnm : (k * m⁻¹) * (m * t * m⁻¹) * (k * m⁻¹)⁻¹ = k * t * k⁻¹ := by group
    have hcomm : ⁅k * m⁻¹, m * t * m⁻¹⁆ = (m * t * m⁻¹) * (k * t * k⁻¹) := by
      rw [commutatorElement_def, hnm]
      have hinv : (m * t * m⁻¹)⁻¹ = m * t * m⁻¹ := inv_eq_of_mul_eq_one_right hsq
      rw [hinv, hc]
    rw [← hcomm]
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (mul_mem hk (inv_mem hm)) hmt
  · intro l hl n hn
    have hnl : n * l⁻¹ * n⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hn.2 l⁻¹).mp (inv_mem hl)
    have hmem : ⁅l, n⁆ ∈ S.Lbar g := by
      have : ⁅l, n⁆ = l * (n * l⁻¹ * n⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem hl hnl
    rw [← hKmap]
    refine ⟨⟨⁅l, n⁆, hmem⟩, ?_, rfl⟩
    have e : (⟨⁅l, n⁆, hmem⟩ : S.Lbar g) =
        ⟨l, hl⟩ * (conjLbar S g ⟨n, hn⟩ ⟨l, hl⟩)⁻¹ := by
      refine Subtype.ext ?_
      change ⁅l, n⁆ = l * (n * l * n⁻¹)⁻¹
      rw [commutatorElement_def]
      group
    rw [SetLike.mem_coe, MonoidHom.mem_ker, e, map_mul, map_inv, hf2, mul_inv_cancel]

end NoForm

end Case25

end CFSG.GF2Type.Smith1979
