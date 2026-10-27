module

public import CFSG.GH74.GLS.SP.Local.SPLSL2Input
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups

namespace SL2Transport

theorem mem_normalizer_map_iff {S G : Type*} [Group S] [Group G] {ι : S →* G}
    (hι : Function.Injective ι) (H : Subgroup S) (y : S) :
    ι y ∈ normalizer ((H.map ι : Subgroup G) : Set G) ↔ y ∈ normalizer (H : Set S) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro hy s
    have h := hy (ι s)
    have h2 : ι y * ι s * (ι y)⁻¹ = ι (y * s * y⁻¹) := by simp
    rw [h2, Subgroup.mem_map_iff_mem hι, Subgroup.mem_map_iff_mem hι] at h
    exact h
  · intro hy g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨y * s * y⁻¹, (hy s).1 hs, by simp⟩
    · rintro ⟨t, ht, hte⟩
      refine ⟨y⁻¹ * t * y, ?_, ?_⟩
      · have ht' : t ∈ H := ht
        show y⁻¹ * t * y ∈ H
        rw [hy]
        have e : y * (y⁻¹ * t * y) * y⁻¹ = t := by group
        rw [e]
        exact ht'
      · have : g = (ι y)⁻¹ * (ι y * g * (ι y)⁻¹) * ι y := by group
        rw [this, ← hte]
        simp

theorem normalizer_zpowers_inf_range {S G : Type*} [Group S] [Group G] {ι : S →* G}
    (hι : Function.Injective ι) (h : S) :
    normalizer ((zpowers (ι h) : Subgroup G) : Set G) ⊓ ι.range =
      (normalizer ((zpowers h : Subgroup S) : Set S)).map ι := by
  ext x
  constructor
  · rintro ⟨hx, y, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [← MonoidHom.map_zpowers] at hx
    exact (mem_normalizer_map_iff hι _ y).1 hx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y, rfl⟩
    rw [← MonoidHom.map_zpowers]
    exact (mem_normalizer_map_iff hι _ y).2 hy

theorem relIndex_zpowers_inf_map {S G : Type*} [Group S] [Group G] {ι : S →* G}
    (hι : Function.Injective ι) (h : S) (B : Subgroup S) :
    (zpowers (ι h) ⊓ B.map ι).relIndex (zpowers (ι h)) =
      (zpowers h ⊓ B).relIndex (zpowers h) := by
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_inf_eq _ _ _ hι,
    Subgroup.relIndex_map_map_of_injective _ _ hι]

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {K Φ : Subgroup G}
    (hΦK : ∀ f ∈ Φ, ∀ x ∈ K, f * x * f⁻¹ ∈ K) : Φ ≤ normalizer (K : Set G) := by
  intro f hf
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hΦK f hf x, fun hx => ?_⟩
  have := hΦK f⁻¹ (Φ.inv_mem hf) _ hx
  simpa [mul_assoc] using this

theorem exists_autSubgroup {G : Type*} [Group G] (K Φ : Subgroup G) {S : Type*} [Group S]
    (ε : ↥K ≃* S) (hΦK : ∀ f ∈ Φ, ∀ x ∈ K, f * x * f⁻¹ ∈ K) :
    ∃ Φ' : Subgroup (MulAut S),
      (∀ f ∈ Φ, ∃ φ ∈ Φ', ∀ s : S,
        ((ε.symm (φ s) : ↥K) : G) = f * ((ε.symm s : ↥K) : G) * f⁻¹) ∧
      (∀ φ ∈ Φ', ∃ f ∈ Φ, orderOf φ ∣ orderOf f ∧ ∀ s : S,
        ((ε.symm (φ s) : ↥K) : G) = f * ((ε.symm s : ↥K) : G) * f⁻¹) := by
  have hle : Φ ≤ normalizer (K : Set G) := le_normalizer_of_conj_mem hΦK
  let ρ : ↥Φ →* MulAut S :=
    (MulAut.congr ε).toMonoidHom.comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hle))
  have key : ∀ (f : ↥Φ) (s : S),
      ((ε.symm (ρ f s) : ↥K) : G) = (f : G) * ((ε.symm s : ↥K) : G) * (f : G)⁻¹ := by
    intro f s
    simp [ρ, MulAut.congr_apply]
  refine ⟨ρ.range, ?_, ?_⟩
  · intro f hf
    exact ⟨ρ ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩, fun s => key ⟨f, hf⟩ s⟩
  · rintro φ ⟨f, rfl⟩
    refine ⟨f, f.2, ?_, key f⟩
    calc orderOf (ρ f) ∣ orderOf f := orderOf_map_dvd ρ f
      _ = orderOf (f : G) := (Subgroup.orderOf_coe f).symm

theorem sq_eq_gen_of_center {G : Type*} [Group G] (K : Subgroup G) {F : Type} [Field F]
    (ε : ↥K ≃* SL(2, F)) {z : G} (hz : (center ↥K).map K.subtype = zpowers z)
    {w : SL(2, F)} (hwc : w * w ∈ center SL(2, F)) (hw1 : w * w ≠ 1) :
    ((ε.symm w : ↥K) : G) * ((ε.symm w : ↥K) : G) = z := by
  set c : ↥K := ε.symm (w * w) with hc
  have hcw : (c : G) = ((ε.symm w : ↥K) : G) * ((ε.symm w : ↥K) : G) := by
    rw [hc, map_mul]; rfl
  rw [← hcw]
  have hcc : c ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply ε.injective
    simp only [map_mul, hc, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp hwc) (ε g)
  have hc1 : c ≠ 1 := fun h => hw1 (by simpa [hc] using congrArg ε h)
  have h3 :=
    (Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F _).mp hwc
  have hZ : ∀ x ∈ (center ↥K).map K.subtype, x = 1 ∨ x = (c : G) := by
    rintro x ⟨c₁, hc₁, rfl⟩
    have h1 : ε c₁ ∈ center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply ε.symm.injective
      simp only [map_mul, MulEquiv.symm_apply_apply]
      exact (Subgroup.mem_center_iff.mp hc₁) (ε.symm g)
    have h2 :=
      (Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F _).mp h1
    rcases h2 with h2 | h2
    · left
      have : c₁ = 1 := ε.injective (by rw [h2, map_one])
      simp [this]
    · right
      have : c₁ = c := by
        apply ε.injective
        rw [hc, MulEquiv.apply_symm_apply, h2]
        rcases h3 with h3 | h3
        · exact absurd h3 hw1
        · exact h3.symm
      rw [this]
      rfl
  have hzZ : z ∈ (center ↥K).map K.subtype := by rw [hz]; exact mem_zpowers z
  have hcZ : (c : G) ∈ (center ↥K).map K.subtype := ⟨c, hcc, rfl⟩
  rcases hZ z hzZ with h | h
  · exfalso
    rw [hz, h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hcZ
    exact hc1 (Subtype.ext hcZ)
  · exact h.symm

end SL2Transport

theorem sl2OddAutTorus_of_SL2 (h1 : SL2OddAutTorusSL2 1) (h3 : SL2OddAutTorusSL2 3) :
    SL2OddAutTorus := by
  intro G _ _ K q hmod hodd h5 z hz Q Φ hΦK hΦQ hΦodd
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hmod
  have hFq' : Nat.card F = q := hFq
  have hoddF : Odd (Nat.card F) := by rw [hFq']; exact hodd
  have h5F : 5 ≤ Nat.card F := by rw [hFq']; exact h5
  have hmod4 : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    obtain ⟨k, hk⟩ := hoddF
    omega
  let ε : ↥K ≃* SL(2, F) :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  let ι : SL(2, F) →* G := K.subtype.comp ε.symm.toMonoidHom
  have hι : Function.Injective ι := K.subtype_injective.comp ε.symm.injective
  have hιapp : ∀ s, ι s = ((ε.symm s : ↥K) : G) := fun s => rfl
  have hιrange : ι.range = K := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (ε.symm s).2
    · intro hx
      exact ⟨ε ⟨x, hx⟩, by simp [hιapp]⟩
  let Q' : Sylow 2 SL(2, F) := Sylow.mapSurjective (f := ε.toMonoidHom) ε.surjective Q
  have hQ' : (Q' : Subgroup SL(2, F)) = (Q : Subgroup ↥K).map ε.toMonoidHom := rfl
  obtain ⟨Φ', hΦ'1, hΦ'2⟩ := SL2Transport.exists_autSubgroup K Φ ε hΦK
  have hcent : ∀ φ ∈ Φ', ∀ x ∈ (Q' : Subgroup SL(2, F)), φ x = x := by
    intro φ hφ x hx
    obtain ⟨f, hf, -, hfs⟩ := hΦ'2 φ hφ
    rw [hQ'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change φ (ε y) = ε y
    have h1 : ε.symm (φ (ε y)) = y := by
      apply Subtype.ext
      have hc : f * (y : G) = (y : G) * f := hΦQ f hf (y : G) ⟨y, hy, rfl⟩
      rw [hfs (ε y), MulEquiv.symm_apply_apply, hc, mul_inv_cancel_right]
    calc φ (ε y) = ε (ε.symm (φ (ε y))) := (ε.apply_symm_apply _).symm
      _ = ε y := by rw [h1]
  have hodd' : ∀ φ ∈ Φ', Odd (orderOf φ) := by
    intro φ hφ
    obtain ⟨f, hf, hdvd, -⟩ := hΦ'2 φ hφ
    exact Odd.of_dvd_nat (hΦodd f hf) hdvd
  obtain ⟨h', w', hord, hwQ, hww, hww1, hinv, hnorm, hrel, hΦ'⟩ :=
    hmod4.elim (fun h4 => h1 F hoddF h5F h4 Q' Φ' hcent hodd')
      (fun h4 => h3 F hoddF h5F h4 Q' Φ' hcent hodd')
  refine ⟨ι h', ι w', (ε.symm h').2, ?_, ?_,
    SL2Transport.sq_eq_gen_of_center K ε hz hww hww1, ?_, ?_, ?_, ?_⟩
  · rw [hQ'] at hwQ
    obtain ⟨y, hy, rfl⟩ := hwQ
    exact ⟨y, hy, by simp [hιapp]⟩
  · rw [orderOf_injective ι hι, hord, hFq']
  · intro k hk
    rw [← MonoidHom.map_zpowers] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    have h2 : w' * k' * w'⁻¹ = k'⁻¹ := hinv k' hk'
    calc ι w' * ι k' * (ι w')⁻¹ = ι (w' * k' * w'⁻¹) := by simp
      _ = ι k'⁻¹ := by rw [h2]
      _ = (ι k')⁻¹ := map_inv ι k'
  · have h2 := SL2Transport.normalizer_zpowers_inf_range hι h'
    rw [hιrange] at h2
    rw [h2, hnorm, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  · have hB : (Q' : Subgroup SL(2, F)).map ι = (Q : Subgroup ↥K).map K.subtype := by
      rw [hQ', Subgroup.map_map]
      congr 1
      ext x
      simp [hιapp]
    rw [← hB, SL2Transport.relIndex_zpowers_inf_map hι h']
    exact hrel
  · intro f hf k hk
    rw [← MonoidHom.map_zpowers] at hk ⊢
    obtain ⟨k', hk', rfl⟩ := hk
    obtain ⟨φ, hφ, hφs⟩ := hΦ'1 f hf
    exact ⟨φ k', hΦ' φ hφ k' hk', hφs k'⟩

end CFSG.GH74.GLS.SP.Local
