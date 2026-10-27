module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

@[expose] def WeakTI {G : Type*} [Group G] (R : Subgroup G) : Prop :=
  ∀ g x : G, x ∈ R → x ≠ 1 → g⁻¹ * x * g ∈ R → g ∈ normalizer (R : Set G)

theorem weakTI_of_inf_eq_bot {G : Type*} [Group G] {R : Subgroup G}
    (h : ∀ g : G, g ∉ normalizer (R : Set G) → R ⊓ R.map (MulAut.conj g).toMonoidHom = ⊥) :
    WeakTI R := by
  intro g x hx hx1 hxg
  by_contra hg
  have h1 := h g hg
  have hmem : x ∈ R ⊓ R.map (MulAut.conj g).toMonoidHom := by
    refine ⟨hx, ?_⟩
    refine ⟨g⁻¹ * x * g, hxg, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  rw [h1, Subgroup.mem_bot] at hmem
  exact hx1 hmem

theorem WeakTI.map {G H : Type*} [Group G] [Group H] {R : Subgroup G} (h : WeakTI R)
    (e : G ≃* H) : WeakTI (R.map e.toMonoidHom) := by
  intro g' x' hx' hx1 hxg
  obtain ⟨x, hxR, rfl⟩ := Subgroup.mem_map.1 hx'
  obtain ⟨y, hyR, hy⟩ := Subgroup.mem_map.1 hxg
  have hx1' : x ≠ 1 := fun h1 => hx1 (by simp [h1])
  have hconj : (e.symm g')⁻¹ * x * e.symm g' ∈ R := by
    have : (e.symm g')⁻¹ * x * e.symm g' = y := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hy.symm
    rw [this]
    exact hyR
  have hN := h (e.symm g') x hxR hx1' hconj
  have hmem : g' ∈ (normalizer (R : Set G)).map e.toMonoidHom :=
    ⟨e.symm g', hN, by simp⟩
  exact Subgroup.le_normalizer_map e.toMonoidHom hmem

theorem WeakTI.conj {G : Type*} [Group G] {R : Subgroup G} (h : WeakTI R) (g : G) :
    WeakTI (R.map (MulAut.conj g).toMonoidHom) :=
  h.map (MulAut.conj g)

theorem centralizes_of_weakTI {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {R B Y : Subgroup G} (hR : IsPGroup p R) (hRTI : WeakTI R) (hBR : B ≤ R)
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hY : ¬ p ∣ Nat.card Y)
    (hBY : B ≤ normalizer (Y : Set G)) : B ≤ centralizer (Y : Set G) := by
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp B Y (fun b => Subtype.ext (hB.2 b b.2)) hBc hY hBY
  have hYN : Y ≤ normalizer (R : Set G) := by
    calc Y = ⨆ (b : B) (_ : b ≠ 1), Y ⊓ centralizer ({(b : G)} : Set G) := hgen
      _ ≤ normalizer (R : Set G) := by
        refine iSup₂_le fun b hb y hy => ?_
        obtain ⟨hyY, hyC⟩ := hy
        have hbR : (b : G) ∈ R := hBR b.2
        have hb1 : (b : G) ≠ 1 := fun h1 => hb (Subtype.ext h1)
        have hyC' : y ∈ centralizer ({(b : G)} : Set G) := hyC
        have hcomm : (b : G) * y = y * (b : G) :=
          Subgroup.mem_centralizer_iff.1 hyC' (b : G) (Set.mem_singleton _)
        refine hRTI y (b : G) hbR hb1 ?_
        have : y⁻¹ * (b : G) * y = b := by
          rw [mul_assoc, hcomm]; group
        rw [this]
        exact hbR
  intro β hβ
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hβR : β ∈ R := hBR hβ
  have hyN := hYN hy
  have hcR : y * β * y⁻¹ * β⁻¹ ∈ R := by
    have h1 : y * β * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hyN β).1 hβR
    exact R.mul_mem h1 (R.inv_mem hβR)
  have hcY : y * β * y⁻¹ * β⁻¹ ∈ Y := by
    have hβ' := (Subgroup.mem_normalizer_iff.1 (hBY hβ) y⁻¹).1 (Y.inv_mem hy)
    have : y * β * y⁻¹ * β⁻¹ = y * (β * y⁻¹ * β⁻¹) := by group
    rw [this]
    exact Y.mul_mem hy hβ'
  have hc1 : y * β * y⁻¹ * β⁻¹ = 1 := by
    obtain ⟨k, hk⟩ := hR ⟨_, hcR⟩
    have hk' : (y * β * y⁻¹ * β⁻¹) ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hord1 : orderOf (y * β * y⁻¹ * β⁻¹) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hord2 : orderOf (y * β * y⁻¹ * β⁻¹) ∣ Nat.card Y := by
      have := Subgroup.orderOf_dvd_natCard Y hcY
      simpa using this
    have hcop : Nat.Coprime (p ^ k) (Nat.card Y) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hY)
    have : orderOf (y * β * y⁻¹ * β⁻¹) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
    exact orderOf_eq_one_iff.1 this
  calc y * β = (y * β * y⁻¹ * β⁻¹) * β * y := by group
    _ = β * y := by rw [hc1]; group

theorem centralizes_of_sylow_weakTI {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (R₀ : Sylow p G) (hR₀ : WeakTI (R₀ : Subgroup G)) {B Y : Subgroup G}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hY : ¬ p ∣ Nat.card Y)
    (hBY : B ≤ normalizer (Y : Set G)) : B ≤ centralizer (Y : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := fun b => ⟨1, by simpa using Subtype.ext (hB.2 b b.2)⟩
  obtain ⟨R, hBR⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R₀ R
  have hRe : (R : Subgroup G) = (R₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  exact centralizes_of_weakTI hp R.isPGroup' (by rw [hRe]; exact hR₀.conj g) hBR hB hBc hY hBY

theorem centralizes_of_equiv_weakTI {G X : Type*} [Group G] [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (ι : X ≃* G) {R : Subgroup X}
    (hR : Nat.card R = p ^ (Nat.card X).factorization p) (hTI : WeakTI R) {B Y : Subgroup G}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hY : ¬ p ∣ Nat.card Y)
    (hBY : B ≤ normalizer (Y : Set G)) : B ≤ centralizer (Y : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite G := Finite.of_equiv X ι.toEquiv
  have hcardG : Nat.card G = Nat.card X := (Nat.card_congr ι.toEquiv).symm
  have hRmap : Nat.card (R.map ι.toMonoidHom) = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective ι.injective, hR, hcardG]
  let R₀ : Sylow p G := Sylow.ofCard (R.map ι.toMonoidHom) hRmap
  have hR₀ : WeakTI (R₀ : Subgroup G) := by
    rw [Sylow.coe_ofCard]
    exact hTI.map ι
  exact centralizes_of_sylow_weakTI hp R₀ hR₀ hB hBc hY hBY

end CFSG.LocalAnalysis.RankFourTheoremC
