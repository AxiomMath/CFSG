module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Uniq
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Ind
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Ru


theorem exists_eq_conj_of_ru {X : Type*} [Group X] (e : X ≃* NativeSporadic.Ru)
    (φ : MulAut X) : ∃ x : X, φ = MulAut.conj x := by
  set ψ := e.trans CFSG.Sporadic.RuSchreier.ruEquivP with hψ
  obtain ⟨g, hg⟩ := CFSG.Sporadic.RuSchreier.mulAut_inner (MulAut.congr ψ φ)
  refine ⟨ψ.symm g, ?_⟩
  ext x
  have h := congrArg (fun α : MulAut _ => α (ψ x)) hg
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h
  apply ψ.injective
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h

end Ru

theorem center_eq_bot_of_ru
    {X : Type*} [Group X]
    (e : X ≃* NativeSporadic.Ru) : center X = ⊥ := by
  set ψ := e.trans CFSG.Sporadic.RuSchreier.ruEquivP with hψ
  rw [eq_bot_iff]
  intro x hx
  have hψx : ψ x ∈ center CFSG.Sporadic.RuSchreier.ruP := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hx y)]
  rw [CFSG.Sporadic.RuSchreier.center_ruP, mem_bot] at hψx
  rw [mem_bot]
  exact ψ.injective (by rw [hψx, map_one])


variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_left_of_mul_of_pow_two {A C : Subgroup G} (hAC : A ⊓ C = ⊥)
    (hC : Odd (Nat.card C)) {a c : G} (ha : a ∈ A) (hc : c ∈ C) (hca : a * c = c * a) {k : ℕ}
    (hk : (a * c) ^ 2 ^ k = 1) : a * c ∈ A := by
  have hcomm : Commute a c := hca
  rw [hcomm.mul_pow] at hk
  have hck : c ^ 2 ^ k ∈ A ⊓ C := by
    refine mem_inf.mpr ⟨?_, pow_mem hc _⟩
    have : c ^ 2 ^ k = (a ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hk
    rw [this]
    exact inv_mem (pow_mem ha _)
  rw [hAC, mem_bot] at hck
  have hodd : Odd (orderOf c) := hC.of_dvd_nat (Subgroup.orderOf_dvd_natCard C hc)
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
  have h2 : orderOf c = 1 :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd h1
  rw [orderOf_eq_one_iff.mp h2, mul_one]
  exact ha

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer' {X : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (X : Set G)) (hc : c ∈ centralizer (X : Set G)) :
    n * c * n⁻¹ ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have hx' : n⁻¹ * x * n ∈ X := by
    have := (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
    simpa using this
  have h1 := mem_centralizer_iff.mp hc _ hx'
  calc x * (n * c * n⁻¹) = n * ((n⁻¹ * x * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * x := by group

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer_b1 (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (centralizer (X : Set G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact conj_mem_centralizer_of_mem_normalizer' hn
  · intro hc
    have h1 := conj_mem_centralizer_of_mem_normalizer' (inv_mem hn) hc
    simpa [mul_assoc] using h1

namespace Sec3

structure B1Frame (L T L₀ : Subgroup G) : Prop where
  ru : Nonempty (L₀ ≃* NativeSporadic.Ru)
  le : L ≤ L₀
  T_le : T ≤ L₀
  centralizer_eq : centralizer (L₀ : Set G) = AS76b.oddCoreIn (centralizer (L : Set G))
  inf_eq : L₀ ⊓ AS76b.oddCoreIn (centralizer (L : Set G)) = ⊥
  normalizer_eq : normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) =
    L₀ ⊔ AS76b.oddCoreIn (centralizer (L : Set G))
  normalizer_eq' : normalizer (L₀ : Set G) =
    normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G)

end Sec3

@[expose] def B1Stage3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T L₀ : Subgroup G), SzMinCounter G L 1 → Sec3 G L T →
    Foundation → Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 →
    AS76b.oddCoreIn (centralizer (L : Set G)) ≠ ⊥ → Sec3.B1Frame L T L₀ →
    ∀ f ∈ gmsA L T, f ≠ 1 → AS76b.oddCoreIn (centralizer ({f} : Set G)) = ⊥ →
      centralizer ({f} : Set G) ≤ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G)

namespace SzMinCounter

variable {L T : Subgroup G}

theorem centralizer_le_normalizer_oddCoreIn
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1) :
    centralizer ({t} : Set G) ≤ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) := by
  have hstd := hM.hyp.standard
  have hKt := AS76b.tightlyEmbedded_centralizer hstd
  have hT₀el := h3.isElemAbelian_T₀ hF
  intro y hy
  have hzK : zpowers t ≤ centralizer (L : Set G) := zpowers_le.mpr (mem_inf.mp ht).2
  have hev : Even (Nat.card (zpowers t)) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hT₀el.2 t ht) ht1]
    exact even_two
  refine AS76b.normalizer_le_normalizer_oddCoreIn _
    (AS76b.Lemma37.normalizer_le_of_le_of_even hKt hzK hev ?_)
  have hc : Commute y t := mem_centralizer_singleton_iff.mp hy
  refine mem_normalizer_of_conj_mem_of_finite fun z hz => ?_
  obtain ⟨k, rfl⟩ := hz
  refine ⟨k, ?_⟩
  simp only
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]

theorem exists_b1Frame
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hW : AS76b.oddCoreIn (centralizer (L : Set G)) ≠ ⊥) :
    ∃ L₀ : Subgroup G, Sec3.B1Frame L T L₀ := by
  classical
  set K := centralizer (L : Set G) with hKdef
  set W := AS76b.oddCoreIn K with hWdef
  set N₀ := normalizer (W : Set G) with hN₀def
  have hstd := hM.hyp.standard
  have hKt := AS76b.tightlyEmbedded_centralizer hstd
  have hNK : normalizer (K : Set G) = normalizer (L : Set G) :=
    AS76b.normalizer_centralizer_eq hstd
  have hWodd : Odd (Nat.card W) := AS76b.odd_card_oddCoreIn K
  have hN₀ : N₀ ≠ ⊤ := by
    intro htop
    have hn : W.Normal := normalizer_eq_top_iff.mp htop
    have h1 := RankTwoSporadic.le_standardComponentOddCore hn hWodd
    rw [hM.hyp.oddCore, le_bot_iff] at h1
    exact hW h1
  have hLW : L ≤ centralizer (W : Set G) := fun l hl => mem_centralizer_iff.mpr fun w hw =>
    (mem_centralizer_iff.mp (AS76b.oddCoreIn_le K hw) l hl).symm
  have hLN : L ≤ N₀ := hLW.trans (centralizer_le_normalizer _)
  have hKN : K ≤ N₀ := AS76b.le_normalizer_oddCoreIn K
  have hMN : normalizer (L : Set G) ≤ N₀ := hNK ▸ AS76b.normalizer_le_normalizer_oddCoreIn K
  have hnn := hM.not_normal_normalizer_oddCoreIn h3 hF hZ h4
  obtain ⟨e⟩ := hM.nonempty_closureIn_mulEquiv_ru hN₀ hLN hKN hnn
  set L₀ := (rankTwoX (L.subgroupOf N₀)).map N₀.subtype with hL₀def
  refine ⟨L₀, ?_⟩
  have hL₀N : L₀ ≤ N₀ := map_subtype_le _
  have hL₀n : N₀ ≤ normalizer (L₀ : Set G) := by
    have : (rankTwoX (L.subgroupOf N₀)).Normal := normalClosure_normal
    exact AS76b.le_normalizer_map_subtype_of_normal N₀ _
  have hLL₀ : L ≤ L₀ := fun l hl =>
    ⟨⟨l, hLN hl⟩, subset_normalClosure (mem_subgroupOf.mpr hl), rfl⟩
  have hL₀W : L₀ ≤ centralizer (W : Set G) := by
    have hn : ((centralizer (W : Set G)).subgroupOf N₀).Normal :=
      (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer W)).mpr
        (normalizer_le_normalizer_centralizer_b1 W)
    have h1 : rankTwoX (L.subgroupOf N₀) ≤ (centralizer (W : Set G)).subgroupOf N₀ :=
      normalClosure_le_normal fun x hx => mem_subgroupOf.mpr (hLW (mem_subgroupOf.mp hx))
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp (h1 hx)
  have hZ₀ : center L₀ = ⊥ := center_eq_bot_of_ru e
  have hcen : ∀ x ∈ L₀, x ∈ centralizer (L₀ : Set G) → x = 1 := by
    intro x hx hxc
    have : (⟨x, hx⟩ : L₀) ∈ center L₀ := mem_center_iff.mpr fun y =>
      Subtype.ext (mem_centralizer_iff.mp hxc y y.2)
    rw [hZ₀, mem_bot] at this
    exact congrArg Subtype.val this
  have hWC : W ≤ centralizer (L₀ : Set G) := fun w hw => mem_centralizer_iff.mpr fun x hx =>
    (mem_centralizer_iff.mp (hL₀W hx) w hw).symm
  have hinf : L₀ ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (mem_bot).mpr (hcen x (mem_inf.mp hx).1 (hWC (mem_inf.mp hx).2))
  have hdecomp : ∀ n ∈ normalizer (L₀ : Set G), ∃ l ∈ L₀, l⁻¹ * n ∈ centralizer (L₀ : Set G) := by
    intro n hn
    obtain ⟨l, hl⟩ := exists_eq_conj_of_ru e (L₀.normalizerMonoidHom ⟨n, hn⟩)
    refine ⟨l, l.2, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have h1 := congrArg (fun φ : MulAut L₀ => ((φ ⟨x, hx⟩ : L₀) : G)) hl
    simp only [normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply, coe_mul, coe_inv] at h1
    calc x * ((l : G)⁻¹ * n) = (l : G)⁻¹ * (l * x * (l : G)⁻¹) * n := by group
      _ = (l : G)⁻¹ * (n * x * n⁻¹) * n := by rw [h1]
      _ = (l : G)⁻¹ * n * x := by group
  obtain ⟨g, hgV, hgL⟩ := hM.exists_mem_normalizer_gmsV_not_mem h3 hF hZ
  have hgN : g ∈ N₀ := hM.normalizer_gmsV_le h3 hF hZ h4 hgV
  have hgK : g ∉ normalizer (K : Set G) := hNK ▸ hgL
  have hCK : centralizer (L₀ : Set G) ≤ K ⊓ rightConjugate K g := by
    intro c hc
    refine mem_inf.mpr ⟨centralizer_le hLL₀ hc, ?_⟩
    rw [mem_rightConjugate_iff, mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L₀ := by
      have := (mem_normalizer_iff.mp (hL₀n (inv_mem hgN)) l).mp (hLL₀ hl)
      simpa using this
    have h1 := mem_centralizer_iff.mp hc _ hl'
    calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * l := by group
  have hCodd : Odd (Nat.card (centralizer (L₀ : Set G))) :=
    (hKt.2 g hgK).of_dvd_nat (Subgroup.card_dvd_of_le hCK)
  have hVN : gmsV L T ≤ N₀ :=
    (sup_le (inf_le_left.trans inf_le_left) inf_le_left : gmsV L T ≤ T).trans
      (h3.sylow.le.trans hMN)
  have hCeq : centralizer (L₀ : Set G) = W := by
    refine le_antisymm ?_ hWC
    refine hM.le_oddCoreIn_of_le_normalizer_gmsV h3 hF hZ h4 hCodd fun v hv => ?_
    exact normalizer_le_normalizer_centralizer_b1 L₀ (hL₀n (hVN hv))
  have hNL₀ : normalizer (L₀ : Set G) ≤ L₀ ⊔ W := by
    intro n hn
    obtain ⟨l, hl, hln⟩ := hdecomp n hn
    rw [hCeq] at hln
    have := mul_mem_sup hl hln
    rwa [mul_inv_cancel_left] at this
  have hsupN : L₀ ⊔ W ≤ N₀ := sup_le hL₀N le_normalizer
  refine ⟨⟨e⟩, hLL₀, ?_, hCeq, hinf, ?_, ?_⟩
  ·
    intro t ht
    have htN : t ∈ normalizer (L₀ : Set G) := hL₀n (hMN (h3.sylow.le ht))
    obtain ⟨l, hl, hln⟩ := hdecomp t htN
    rw [hCeq] at hln
    obtain ⟨k, hk⟩ := h3.sylow.isPGroup ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc : l * (l⁻¹ * t) = (l⁻¹ * t) * l :=
      mem_centralizer_iff.mp (hWC hln) l hl
    have h1 := mem_left_of_mul_of_pow_two hinf hWodd hl hln hc
      (by rw [mul_inv_cancel_left]; exact htk)
    rwa [mul_inv_cancel_left] at h1
  · exact le_antisymm (hL₀n.trans hNL₀) hsupN
  · exact le_antisymm (hNL₀.trans hsupN) hL₀n

end SzMinCounter

end CFSG.ComponentClassification.GMS78
