module

public import CFSG.LocalAnalysis.GH72.Sec5C13Basic
public import CFSG.LocalAnalysis.GH72.Sec5C12

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement MatrixGroups

section General

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_le_sup {p : ℕ} [Fact p.Prime] {S B K O : Subgroup G}
    (hS : IsSylowOf p S B) (hBK : B ≤ K) (hK : K ≤ O ⊔ B) (hBO : B ≤ normalizer (O : Set G))
    (hO : ¬ p ∣ Nat.card O) : IsSylowOf p S K := by
  rw [isSylowOf_iff] at hS ⊢
  obtain ⟨hSB, hSp, hidx⟩ := hS
  refine ⟨hSB.trans hBK, hSp, ?_⟩
  rw [← relIndex_mul_relIndex S B K hSB hBK]
  have h1 : ¬ p ∣ B.relIndex K := by
    intro h
    have h2 : B.relIndex K ∣ B.relIndex (O ⊔ B) :=
      Dvd.intro _ (relIndex_mul_relIndex B K (O ⊔ B) hBK hK)
    rw [CFSG.ABGTheoremB.relIndex_sup_eq_relIndex_of_le_normalizer hBO] at h2
    exact hO ((h.trans h2).trans (index_dvd_card _))
  exact (Fact.out : p.Prime).not_dvd_mul hidx h1

theorem isSylowOf_bar_of_isSylowOf {p : ℕ} [Fact p.Prime] {H T K : Subgroup G}
    (hT : IsSylowOf p T K) (hKH : K ≤ H) : IsSylowOf p (bar H T) (bar H K) := by
  have hTH : T ≤ H := hT.le.trans hKH
  have e1 : (T.subgroupOf H).map H.subtype = T := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hTH]
  have e2 : (K.subgroupOf H).map H.subtype = K := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hKH]
  have h1 : IsSylowOf p (T.subgroupOf H) (K.subgroupOf H) :=
    (isSylowOf_map_subtype_iff H).mp (by rw [e1, e2]; exact hT)
  exact isSylowOf_map_hom h1 _

theorem card_eq_eight_of_isSylowOf_aSeven {X : Type} [Group X]
    [Finite X] {J S : Subgroup X} (e : J ≃* alternatingGroup (Fin 7)) (hS : IsSylowOf 2 S J) :
    Nat.card S = 8 := by
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨φ, hφ⟩ := CFSG.ABGDGroups.exists_mulEquiv_aSeven_map_sylow_eq e Q
  rw [card_map_of_injective J.subtype_injective, ← CFSG.ABGDGroups.card_a7S, ← hφ,
    card_map_of_injective φ.injective]

omit [Finite G] in
theorem le_normalizer_of_card_eq_eight {X T : Subgroup G} (hXT : X ≤ T) (hX : IsKleinFour X)
    (hT : Nat.card T = 8) : T ≤ normalizer (X : Set G) := by
  have hidx : (X.subgroupOf T).index = 2 := by
    have h := (X.subgroupOf T).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hXT).toEquiv, hX.card_four, hT] at h
    omega
  have := Subgroup.normal_of_index_eq_two hidx
  exact (normal_subgroupOf_iff_le_normalizer hXT).mp inferInstance

omit [Finite G] in
theorem conj_mem_normalizer_map_conj {R : Subgroup G} {s : G} (hs : s ∈ normalizer (R : Set G))
    (c : G) : c * s * c⁻¹ ∈ normalizer ((R.map (MulAut.conj c).toMonoidHom : Subgroup G) :
      Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have e : ∀ a b : G, (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := fun a b => by
    ext y
    simp [mul_assoc]
  change (R.map (MulAut.conj c).toMonoidHom).map (MulAut.conj (c * s * c⁻¹)).toMonoidHom = _
  rw [map_map, e, show c * s * c⁻¹ * c = c * s by group, ← e, ← map_map,
    map_conj_eq_of_mem_normalizer hs]

omit [Finite G] in
theorem inf_eq_bot_of_isPGroup_two {S K : Subgroup G} (hS : IsPGroup 2 S) (hK : Odd (Nat.card K)) :
    S ⊓ K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (hS.to_le (inf_le_left : S ⊓ K ≤ S)).card_eq_or_dvd with h | h
  · exact card_eq_one.mp h
  · exact absurd (h.trans (card_dvd_of_le inf_le_right)) hK.not_two_dvd_nat

end General

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

theorem covers_centralizer_V_inf_W {L : Type} [Group L] [IsSimpleGroup L]
    (f : ρ.N₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = (O ρ.N).subgroupOf ρ.N₀) {W : Subgroup G}
    (hWK : W ≤ 𝔨.K₁ ⊓ ρ.N₀) (hXW : ρ.X ≤ W) (hWcov : Covers W ρ.N₀ (O ρ.N)) :
    Covers (centralizer (𝔨.V : Set G) ⊓ W) ρ.N₀ (O ρ.N) := by
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_isKleinFour ρ.isKleinFour_X
  have hXO : ρ.X ⊓ O ρ.N = ⊥ := inf_eq_bot_of_isKleinFour ρ.isKleinFour_X (card_O_odd _)
  refine covers_of_isSimpleGroup f hf hker hWcov ρ.N₀_le_normalizer_O_N ?_
    ⟨⟨⟨𝔨.X_le_centralizer_V hx, hXW hx⟩, hXW hx⟩, (hWK (hXW hx)).2⟩ ?_
  · intro g hg
    have hgK : g ∈ normalizer (𝔨.V : Set G) :=
      𝔨.K_eq_normalizer_V ▸ 𝔨.K₁_le_K (hWK hg.1).1
    exact inf_normalizer_le_normalizer_inf
      ⟨normalizer_le_normalizer_centralizer _ hgK, le_normalizer hg.1⟩
  · intro hxO
    have : x ∈ ρ.X ⊓ O ρ.N := ⟨hx, hxO⟩
    rw [hXO, mem_bot] at this
    exact hx1 this

theorem covers_normalizer_inf_centralizer_T₂ (hPM : 𝔨.P ≤ ρ.M) {T₂ : Subgroup G}
    (hT₂ : IsPGroup 2 T₂) (hT₂X : T₂ ≤ normalizer (ρ.X : Set G))
    (hT₂R : T₂ ≤ normalizer ((𝔨.P ⊓ O ρ.M : Subgroup G) : Set G))
    (hTM₀ : ⁅T₂, ρ.M₀⁆ ≤ O ρ.M) :
    Covers (normalizer ((𝔨.P ⊓ O ρ.M ⊓ centralizer (T₂ : Set G) : Subgroup G) : Set G))
      ρ.M₀ (O ρ.M) := by
  set R₀ : Subgroup G := 𝔨.P ⊓ O ρ.M with hR₀def
  have hR₀ : IsSylowOf p R₀ (O ρ.M) :=
    isSylowOf_inf_O_of_isMaxInvIn 𝔨.hp ρ.isPGroup_A
      ((ρ.A_le_centralizer_of_le ρ.X_le_A).trans le_normalizer) (𝔨.hP.of_le hPM le_top)
  have hOMn : ρ.M ≤ normalizer (O ρ.M : Set G) := le_normalizer_O _
  set O' : Subgroup G := O ρ.M ⊓ normalizer (R₀ : Set G) with hO'def
  have hO'odd : Odd (Nat.card O') := (card_O_odd _).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hT₂O' : T₂ ≤ normalizer (O' : Set G) := fun t ht =>
    inf_normalizer_le_normalizer_inf
      ⟨ρ.normalizer_X_le_normalizer_O_M (hT₂X ht), le_normalizer (hT₂R ht)⟩
  apply covers_of_forall
  intro m hm
  have hmM : m ∈ ρ.M := ρ.M₀_le hm
  have hm' : m ∈ ((O ρ.M ⊔ (ρ.M ⊓ normalizer (R₀ : Set G)) : Subgroup G) : Set G) :=
    le_O_sup_inf_normalizer_of_isSylowOf 𝔨.hp hR₀ hmM
  rw [coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hOMn)] at hm'
  obtain ⟨o₁, ho₁', n, hn', rfl⟩ := Set.mem_mul.mp hm'
  have ho₁ : o₁ ∈ O ρ.M := ho₁'
  have hn : n ∈ ρ.M ⊓ normalizer (R₀ : Set G) := hn'
  have hOM₀ : O ρ.M ≤ ρ.M₀ := le_sup_right
  have hnM₀ : n ∈ ρ.M₀ := by
    have := ρ.M₀.mul_mem (ρ.M₀.inv_mem (hOM₀ ho₁)) hm
    simpa using this
  have hnT : T₂.map (MulAut.conj n).toMonoidHom ≤ O' ⊔ T₂ := by
    rintro _ ⟨t, ht, rfl⟩
    have hc1 : ⁅n, t⁆ ∈ O ρ.M := by
      have h1 : ⁅t, n⁆ ∈ O ρ.M := hTM₀ (commutator_mem_commutator ht hnM₀)
      rw [← commutatorElement_inv]
      exact (O ρ.M).inv_mem h1
    have hc2 : ⁅n, t⁆ ∈ normalizer (R₀ : Set G) := by
      have hn2 : n ∈ normalizer (R₀ : Set G) := hn.2
      have ht2 : t ∈ normalizer (R₀ : Set G) := hT₂R ht
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hn2 ht2) (inv_mem hn2)) (inv_mem ht2)
    have hc : ⁅n, t⁆ ∈ O' := ⟨hc1, hc2⟩
    have e : (MulAut.conj n).toMonoidHom t = ⁅n, t⁆ * t := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact mul_mem (mem_sup_left hc) (mem_sup_right ht)
  obtain ⟨o, ho, hon⟩ := exists_mul_mem_normalizer_of_map_conj_le hT₂ hO'odd hT₂O' hnT
  refine ⟨o * n, ⟨?_, ρ.M₀.mul_mem (hOM₀ ho.1) hnM₀⟩,
    (o * n)⁻¹ * (o₁ * n), ?_, by group⟩
  · have ho2 : o ∈ normalizer (R₀ : Set G) := ho.2
    have hn2 : n ∈ normalizer (R₀ : Set G) := hn.2
    exact inf_normalizer_le_normalizer_inf
      ⟨mul_mem ho2 hn2, normalizer_le_normalizer_centralizer _ hon⟩
  · have e : (o * n)⁻¹ * (o₁ * n) = n⁻¹ * (o⁻¹ * o₁) * n := by group
    rw [e]
    have hn1 : n ∈ ρ.M := hn.1
    have ho1 : o ∈ O ρ.M := ho.1
    have h1 := (mem_normalizer_iff.mp (hOMn (inv_mem hn1)) (o⁻¹ * o₁)).mp
      (mul_mem (inv_mem ho1) ho₁)
    simpa using h1

theorem exists_T₂ {W : Subgroup G} (hWK : W ≤ 𝔨.K₁ ⊓ ρ.N₀)
    (hXW : ρ.X ≤ W) (hWn : (bar 𝔨.K₁ W).Normal) (e : bar 𝔨.K₁ W ≃* alternatingGroup (Fin 7))
    (hcov : Covers (centralizer (𝔨.V : Set G) ⊓ W) ρ.N₀ (O ρ.N))
    (hPK₁ : 𝔨.P ≤ 𝔨.K₁) (hPM : 𝔨.P ≤ ρ.M) :
    ∃ T₂ : Subgroup G, IsSylowOf 2 T₂ ρ.N₀ ∧ ρ.X ≤ T₂ ∧ T₂ ≤ 𝔨.K₁ ∧
      T₂ ≤ centralizer (𝔨.V : Set G) ∧
      T₂ ≤ normalizer ((𝔨.P ⊓ O ρ.M : Subgroup G) : Set G) ∧ Nat.card T₂ = 8 ∧
      IsSylowOf 2 (bar 𝔨.K₁ T₂) (bar 𝔨.K₁ W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨𝔨.hp⟩
  have hWK₁ : W ≤ 𝔨.K₁ := hWK.trans inf_le_left
  have hWN₀ : W ≤ ρ.N₀ := hWK.trans inf_le_right
  set B₀ : Subgroup G := centralizer (𝔨.V : Set G) ⊓ W with hB₀def
  have hXB₀ : ρ.X ≤ B₀ := le_inf 𝔨.X_le_centralizer_V hXW
  obtain ⟨S, hS⟩ := (ρ.isPGroup_two_X.comap_subtype (K := B₀)).exists_le_sylow
  set S'' : Subgroup G := (S : Subgroup B₀).map B₀.subtype with hS''def
  have hS''B₀ : IsSylowOf 2 S'' B₀ := ⟨S, rfl⟩
  have hXS'' : ρ.X ≤ S'' := fun x hx => ⟨⟨x, hXB₀ hx⟩, hS hx, rfl⟩
  have hB₀N₀ : B₀ ≤ ρ.N₀ := inf_le_right.trans hWN₀
  have hN₀B₀ : ρ.N₀ ≤ O ρ.N ⊔ B₀ := fun n hn => by
    have h1 := (sup_le_sup_right (inf_le_left : B₀ ⊓ ρ.N₀ ≤ B₀) _) (hcov hn)
    rwa [sup_comm] at h1
  have hS''N₀ : IsSylowOf 2 S'' ρ.N₀ :=
    isSylowOf_of_le_sup hS''B₀ hB₀N₀ hN₀B₀ (hB₀N₀.trans ρ.N₀_le_normalizer_O_N)
      (card_O_odd _).not_two_dvd_nat
  have hS''W : S'' ≤ W := hS''B₀.le.trans inf_le_right
  have hS''K₁ : S'' ≤ 𝔨.K₁ := hS''W.trans hWK₁
  have hS''V : S'' ≤ centralizer (𝔨.V : Set G) := hS''B₀.le.trans inf_le_left
  have hS''Wb : IsSylowOf 2 (bar 𝔨.K₁ S'') (bar 𝔨.K₁ W) :=
    isSylowOf_bar_of_isSylowOf (hS''N₀.of_le hS''W hWN₀) hWK₁
  have hS''O : S'' ⊓ O 𝔨.K₁ = ⊥ := inf_eq_bot_of_isPGroup_two hS''B₀.isPGroup (card_O_odd _)
  have hS''8 : Nat.card S'' = 8 := by
    have h2 := card_eq_eight_of_isSylowOf_aSeven e hS''Wb
    rwa [card_bar_of_inf_eq_bot hS''K₁ hS''O] at h2
  have hS''X : S'' ≤ normalizer (ρ.X : Set G) :=
    le_normalizer_of_card_eq_eight hXS'' ρ.isKleinFour_X hS''8
  have hYS'' : ρ.Y ≤ normalizer (S'' : Set G) := by
    have h1 : S'' ≤ centralizer (ρ.Y : Set G) := hS''N₀.le.trans ρ.N₀_le
    exact (le_centralizer_iff.mp h1).trans (centralizer_le_normalizer _)
  have hŜ : IsPGroup 2 (S'' ⊔ ρ.Y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hS''B₀.isPGroup ρ.isPGroup_two_Y hYS''
  set Γ : Subgroup G := O ρ.M ⊓ 𝔨.K₁ with hΓdef
  have hΓodd : Odd (Nat.card Γ) := (card_O_odd _).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hYM : ρ.Y ≤ ρ.M := ρ.Y_le_A.trans (ρ.A_le_centralizer_of_le ρ.X_le_A)
  have hŜΓ : S'' ⊔ ρ.Y ≤ normalizer (Γ : Set G) := by
    refine sup_le (fun s hs => inf_normalizer_le_normalizer_inf
      ⟨ρ.normalizer_X_le_normalizer_O_M (hS''X hs), le_normalizer (hS''K₁ hs)⟩)
      (fun y hy => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_O _ (hYM hy), le_normalizer (𝔨.Y_le_K₁ hy)⟩)
  have hR₀O : IsSylowOf p (𝔨.P ⊓ O ρ.M) (O ρ.M) :=
    isSylowOf_inf_O_of_isMaxInvIn 𝔨.hp ρ.isPGroup_A
      ((ρ.A_le_centralizer_of_le ρ.X_le_A).trans le_normalizer) (𝔨.hP.of_le hPM le_top)
  have hR₀Γ : IsSylowOf p (𝔨.P ⊓ O ρ.M) Γ :=
    hR₀O.of_le (le_inf inf_le_right (inf_le_left.trans hPK₁)) inf_le_left
  obtain ⟨R₁, hR₁, hŜR₁⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_odd 𝔨.hp hŜ hŜΓ hΓodd
  have hAŜ : A ≤ S'' ⊔ ρ.Y := ρ.X_sup_Y.ge.trans (sup_le_sup_right hXS'' _)
  have hAR₀ : A ≤ normalizer ((𝔨.P ⊓ O ρ.M : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf
      ⟨𝔨.A_le_normalizer_P ha, le_normalizer_O _ (ρ.A_le_centralizer_of_le ρ.X_le_A ha)⟩
  obtain ⟨c, ⟨hcΓ, hcA⟩, hc⟩ := CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_odd
    𝔨.hp ρ.isPGroup_A (hAŜ.trans hŜΓ) hΓodd hR₁ hR₀Γ (hAŜ.trans hŜR₁) hAR₀
  have hcK₁ : c ∈ 𝔨.K₁ := hcΓ.2
  have hcY : c ∈ centralizer (ρ.Y : Set G) := centralizer_le (fun y hy => ρ.Y_le_A hy) hcA
  have hcX : c ∈ centralizer (ρ.X : Set G) := centralizer_le (fun x hx => ρ.X_le_A hx) hcA
  have hT₂K₁ : S''.map (MulAut.conj c).toMonoidHom ≤ 𝔨.K₁ := by
    rw [← map_conj_eq_of_mem_normalizer (le_normalizer hcK₁)]
    exact map_mono hS''K₁
  refine ⟨S''.map (MulAut.conj c).toMonoidHom, ?_, ?_, hT₂K₁, ?_, ?_, ?_, ?_⟩
  · have hcN₀ : c ∈ normalizer (ρ.N₀ : Set G) :=
      ρ.normalizer_Y_le_normalizer_N₀ (centralizer_le_normalizer _ hcY)
    have := isSylowOf_map_hom hS''N₀ (MulAut.conj c).toMonoidHom
    rwa [map_conj_eq_of_mem_normalizer hcN₀] at this
  · rw [← map_conj_eq_of_mem_normalizer (centralizer_le_normalizer _ hcX)]
    exact map_mono hXS''
  · have hcV : c ∈ normalizer (centralizer (𝔨.V : Set G) : Set G) :=
      normalizer_le_normalizer_centralizer _ (𝔨.K_eq_normalizer_V ▸ 𝔨.K₁_le_K hcK₁)
    rw [← map_conj_eq_of_mem_normalizer hcV]
    exact map_mono hS''V
  · rintro _ ⟨s, hs, rfl⟩
    rw [← hc]
    exact conj_mem_normalizer_map_conj (hŜR₁ (mem_sup_left hs)) c
  · rw [card_map_of_injective (MulAut.conj c).injective, hS''8]
  ·
    have hle : bar 𝔨.K₁ (S''.map (MulAut.conj c).toMonoidHom) ≤ bar 𝔨.K₁ W := by
      rintro _ ⟨⟨y, hyK₁⟩, hy, rfl⟩
      obtain ⟨s, hs, hsy⟩ := hy
      have hsK₁ : s ∈ 𝔨.K₁ := hS''K₁ hs
      have e1 : (⟨y, hyK₁⟩ : 𝔨.K₁) = ⟨c, hcK₁⟩ * ⟨s, hsK₁⟩ * (⟨c, hcK₁⟩ : 𝔨.K₁)⁻¹ :=
        Subtype.ext hsy.symm
      rw [e1, map_mul, map_mul, map_inv]
      exact hWn.conj_mem _ (mk_mem_bar hsK₁ (hS''W hs)) _
    have hcard : Nat.card (bar 𝔨.K₁ (S''.map (MulAut.conj c).toMonoidHom)) = 8 := by
      rw [card_bar_of_inf_eq_bot hT₂K₁
        (inf_eq_bot_of_isPGroup_two (hS''B₀.isPGroup.map _) (card_O_odd _)),
        card_map_of_injective (MulAut.conj c).injective, hS''8]
    exact isSylowOf_of_card hle (by
      rw [hcard, ← hS''Wb.card_eq, card_bar_of_inf_eq_bot hS''K₁ hS''O, hS''8])

end Sec5KConfig

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔠 : Sec5ConfigR ρ p)

theorem V_inf_O_M_ne_bot
    (h57 : ∀ y ∈ ρ.Y, y ≠ 1 → ¬ 𝔠.V ≤ C y)
    (hPM : 𝔠.P ≤ ρ.M) : 𝔠.V ⊓ O ρ.M ≠ ⊥ := by
  intro hbot
  have hYM₀ := 𝔠.Y_le_M₀
  obtain ⟨L, _, f, hf, hker, hL⟩ := 𝔠.quotIs_M₀
  have hcovM : Covers ρ.M ρ.M₀ (O ρ.M) := fun m hm =>
    mem_sup_left ⟨ρ.M₀_le hm, hm⟩
  have hOM₀ : O ρ.M ≤ ρ.M₀ := le_sup_right
  have hOH : O ρ.M ⊓ ρ.M₀ = ρ.M ⊓ ρ.M₀ ⊓ O ρ.M := by
    rw [inf_eq_left.mpr hOM₀, inf_eq_right.mpr ρ.M₀_le, inf_eq_right.mpr hOM₀]
  obtain ⟨eJ⟩ := nonempty_bar_mulEquiv f hf hker hcovM ρ.M₀_le_normalizer_O_M hOH
  have hJ5 : IsL2OrA7 (bar ρ.M ρ.M₀) 5 := isL2OrA7_of_mulEquiv eJ hL
  have hMM₀ : ρ.M ≤ normalizer (ρ.M₀ : Set G) :=
    ρ.M_le_normalizer_X.trans ρ.normalizer_X_le_normalizer_M₀
  have hJn : (bar ρ.M ρ.M₀).Normal :=
    bar_normal ((normal_subgroupOf_iff_le_normalizer ρ.M₀_le).mpr hMM₀)
  have hYM : ρ.Y ≤ ρ.M := ρ.Y_le_A.trans (ρ.A_le_centralizer_of_le ρ.X_le_A)
  have hYK : IsKleinFour (bar ρ.M ρ.Y) := isKleinFour_bar_of_le hYM ρ.isKleinFour_Y
  have hPJ : bar ρ.M 𝔠.P ≤ normalizer (bar ρ.M ρ.M₀ : Set (Bar ρ.M)) := by
    rw [normalizer_eq_top_iff.mpr hJn]
    exact le_top
  have hPodd : Odd (Nat.card (bar ρ.M 𝔠.P)) :=
    odd_card_bar (CFSG.GH72.odd_card_of_isPGroup 𝔠.hp 𝔠.hp2 𝔠.isPGroup_P)
  have hYP : bar ρ.M ρ.Y ≤ normalizer (bar ρ.M 𝔠.P : Set (Bar ρ.M)) :=
    bar_le_normalizer (ρ.Y_le_A.trans 𝔠.A_le_normalizer_P)
  obtain ⟨a, ha, ha1, hPa⟩ :=
    exists_le_centralizer_of_odd_of_le_normalizer hJ5 hYK (bar_mono hYM₀) hPJ hPodd hYP
  obtain ⟨y, hyY, rfl⟩ := mem_bar_iff.mp ha
  have hy1 : (y : G) ≠ 1 := fun h => ha1 (by rw [show y = 1 from Subtype.ext h]; rfl)
  apply h57 y hyY hy1
  intro v hv
  have hvP : v ∈ 𝔠.P := (inf_le_left.trans inf_le_left : 𝔠.V ≤ 𝔠.P) hv
  have hvM : v ∈ ρ.M := hPM hvP
  have hc := mem_centralizer_singleton_iff.mp (hPa (mk_mem_bar hvM hvP))
  have hO : v * y * v⁻¹ * y⁻¹ ∈ O ρ.M := by
    have h1 : (QuotientGroup.mk (⟨v, hvM⟩ * y * (⟨v, hvM⟩ : ρ.M)⁻¹ * y⁻¹) : Bar ρ.M) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      calc (QuotientGroup.mk ⟨v, hvM⟩ : Bar ρ.M) * QuotientGroup.mk y *
            (QuotientGroup.mk ⟨v, hvM⟩)⁻¹ * (QuotientGroup.mk y)⁻¹
          = QuotientGroup.mk y * QuotientGroup.mk ⟨v, hvM⟩ * (QuotientGroup.mk ⟨v, hvM⟩)⁻¹ *
            (QuotientGroup.mk y)⁻¹ := by rw [hc]
        _ = 1 := by group
    exact (mk_eq_one_iff _).mp h1
  have hyV : (y : G) ∈ normalizer (𝔠.V : Set G) := 𝔠.A_le_normalizer_V (ρ.Y_le_A hyY)
  have hV : v * y * v⁻¹ * y⁻¹ ∈ 𝔠.V := by
    have h1 : (y : G) * v⁻¹ * (y : G)⁻¹ ∈ 𝔠.V := (mem_normalizer_iff.mp hyV v⁻¹).mp (inv_mem hv)
    have := mul_mem hv h1
    simpa [mul_assoc] using this
  have h1 : v * y * v⁻¹ * y⁻¹ = 1 := by
    have : v * y * v⁻¹ * y⁻¹ ∈ 𝔠.V ⊓ O ρ.M := ⟨hV, hO⟩
    rwa [hbot, mem_bot] at this
  rw [mem_centralizer_singleton_iff]
  have := congrArg (· * (y * v)) h1
  simpa [mul_assoc] using this

theorem lemma_5_13_of
    (h58 : 𝔠.R = 𝔠.U)
    (h48 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₁ ρ.N₀ ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (A : Set G)) ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (ρ.S₁ : Set G)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → O2 (C y) = (O2 ρ.N ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (ρ.N₀ ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h57 : ∀ y ∈ ρ.Y, y ≠ 1 → ¬ 𝔠.V ≤ C y)
    (h59 : ∃ W : Subgroup G, 𝔠.Q = (𝔠.R ⊓ 𝔠.Q) ⊔ W ∧ IsCyclic W ∧
      A ≤ normalizer (W : Set G) ∧ W ≤ 𝔠.K₁ ⊓ centralizer (𝔠.V : Set G) ∧ ⁅ρ.X, W⁆ = W)
    (h59E : ∃ E : Subgroup G, E ≤ 𝔠.R ⊓ 𝔠.Q ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3)
    (h59cyc : IsCyclic (⁅𝔠.Pstar, ρ.X⁆ : Subgroup G))
    (h315 : (∃ H₁ : Subgroup (Bar (C ρ.z₁)), bar (C ρ.z₁) ρ.S₁ ⊓ H₁ = ⊥ ∧
        bar (C ρ.z₁) ρ.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C ρ.z₁) ρ.S₁ : Set (Bar (C ρ.z₁))) ∧
        bar (C ρ.z₁) ρ.S₂ ≤ ⁅H₁, H₁⁆ ∧
        (IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C ρ.z₁))) 5 ∨ ⁅H₁, H₁⁆ = bar (C ρ.z₁) ρ.S₂)) ∧
      (∃ K₁ : Subgroup (Bar (C ρ.z₂)), bar (C ρ.z₂) ρ.S₂ ⊓ K₁ = ⊥ ∧
        bar (C ρ.z₂) ρ.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C ρ.z₂) ρ.S₂ : Set (Bar (C ρ.z₂))) ∧
        bar (C ρ.z₂) ρ.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C ρ.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C ρ.z₂) ρ.S₁)))
    (h7 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => Nonempty (L ≃* alternatingGroup (Fin 7)))) :
    ∃ H, ρ.IsCovering p H := by
  obtain ⟨W, hW⟩ := h59
  by_cases hcase : 𝔠.Q ⊓ 𝔠.U ≤ 𝔠.V ∨ W ≠ ⊥
  · exact 𝔠.lemma_5_12_of h58 h59E h59cyc W hW hcase
  have hW1 : W = ⊥ := by
    by_contra h
    exact hcase (Or.inr h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := 𝔠.hp
  have hp2 := 𝔠.hp2
  obtain ⟨hPP, hPUW⟩ := 𝔠.lemma_5_11_of h58 W hW
  have hPU : 𝔠.P = 𝔠.U := by rw [hPUW, hW1, sup_bot_eq]
  have hPM : 𝔠.P ≤ ρ.M := hPU.le.trans 𝔠.U_le_centralizer_X
  have hPK : 𝔠.P ≤ 𝔠.K := hPP.le.trans inf_le_right
  have hPK₁ : 𝔠.P ≤ 𝔠.K₁ := hPP.le.trans 𝔠.Pstar_le_K₁
  have hXN₀ := 𝔠.X_le_N₀
  obtain ⟨WK, hWK, hXWK, hWKcov, hK₁WK, hWKn, hWKO, -⟩ := 𝔠.exists_W
  have hWKK₁ : WK ≤ 𝔠.K₁ := hWK.trans inf_le_left
  obtain ⟨L, _, f, hf, hker, ⟨e7⟩⟩ := h7
  obtain ⟨eJ⟩ := 𝔠.nonempty_bar_W_mulEquiv f hf hker hWK hWKcov hWKO
  have e := eJ.trans e7
  have : IsSimpleGroup L := isSimpleGroup_of_isL2OrA7 le_rfl (Or.inl ⟨e7⟩ : IsL2OrA7 L 5)
  have hcovW := 𝔠.covers_centralizer_V_inf_W f hf hker hWK hXWK hWKcov
  have hJn : (bar 𝔠.K₁ WK).Normal := 𝔠.bar_W_normal hWKK₁ hWKn
  have hXJ : bar 𝔠.K₁ ρ.X ≤ bar 𝔠.K₁ WK := bar_mono hXWK
  have hXb := 𝔠.isKleinFour_bar_X
  have hUbJ : bar 𝔠.K₁ 𝔠.U ≤ normalizer (bar 𝔠.K₁ WK : Set (Bar 𝔠.K₁)) := by
    rw [normalizer_eq_top_iff.mpr hJn]
    exact le_top
  have hUb : IsPGroup p (bar 𝔠.K₁ 𝔠.U) := isPGroup_bar_of_isPGroup (𝔠.isPGroup_P.to_le hPU.ge)
  have hUbodd : Odd (Nat.card (bar 𝔠.K₁ 𝔠.U)) := CFSG.GH72.odd_card_of_isPGroup hp hp2 hUb
  have hJU : bar 𝔠.K₁ WK ⊔ bar 𝔠.K₁ 𝔠.U = bar 𝔠.K₁ WK ⊔ bar 𝔠.K₁ 𝔠.Pstar := by
    rw [← hPU, hPP]
  have hJUn : (bar 𝔠.K₁ WK ⊔ bar 𝔠.K₁ 𝔠.U).Normal := hJU ▸ 𝔠.bar_W_sup_Pstar_normal hWKK₁ hK₁WK
  have hZJ : center (bar 𝔠.K₁ WK) = ⊥ :=
    center_eq_bot_of_isL2OrA7 (Or.inl ⟨e⟩ : IsL2OrA7 (bar 𝔠.K₁ WK) 5)
  have hfaith := sup_inf_centralizer_eq_bot hJn hJUn hZJ hUbJ hUbodd 𝔠.oddCore_bar_K₁
  obtain ⟨hUbJ', -⟩ :=
    le_and_card_dvd_three_of_aSeven e hXb hXJ hUbJ hUbodd 𝔠.bar_U_le_centralizer_bar_X hfaith
  have hVs1 := 𝔠.V_inf_O_M_ne_bot h57 hPM
  obtain ⟨T₂, hT₂syl, hXT₂, hT₂K₁, hT₂V, hT₂R, hT₂8, hT₂J⟩ :=
    𝔠.exists_T₂ hWK hXWK hJn e hcovW hPK₁ hPM
  have hT₂X := le_normalizer_of_card_eq_eight hXT₂ ρ.isKleinFour_X hT₂8
  have hS₁8 : Nat.card ρ.S₁ = 8 := by rw [h48.2.1.card_eq, ← hT₂syl.card_eq, hT₂8]
  have hS₁X := le_normalizer_of_card_eq_eight (inf_le_right : ρ.X ≤ ρ.S₁) ρ.isKleinFour_X hS₁8
  have hTM₀ := ρ.commutator_le_O_M_of_isSylowOf h315.1 h48.2.1 hS₁X hT₂syl hT₂X
  have hVP : 𝔠.V ≤ 𝔠.P := inf_le_left.trans inf_le_left
  have hVs : 𝔠.V ⊓ O ρ.M = 𝔠.P ⊓ O ρ.M ⊓ centralizer (T₂ : Set G) := by
    apply le_antisymm
    · intro v hv
      exact ⟨⟨hVP hv.1, hv.2⟩, (le_centralizer_iff.mp hT₂V) hv.1⟩
    · intro x hx
      refine ⟨?_, hx.1.2⟩
      have hxU : x ∈ 𝔠.U := hPU ▸ hx.1.1
      have hbot : bar 𝔠.K₁ (𝔠.U ⊓ centralizer (T₂ : Set G)) = ⊥ :=
        eq_bot_of_isSylowOf_le_centralizer_aSeven e hT₂J ((bar_mono inf_le_left).trans hUbJ')
          (odd_card_bar ((CFSG.GH72.odd_card_of_isPGroup hp hp2 𝔠.isPGroup_P).of_dvd_nat
            (card_dvd_of_le (inf_le_left.trans hPU.ge))))
          (bar_le_centralizer (le_centralizer_iff.mp inf_le_right))
      have hxO : x ∈ O 𝔠.K₁ := bar_eq_bot_iff.mp hbot ⟨⟨hxU, hx.2⟩, 𝔠.U_le_K₁ hxU⟩
      rw [← 𝔠.V_eq]
      exact ⟨⟨hx.1.1, hPK hx.1.1⟩, hxO⟩
  have hVsp : IsPGroup p (𝔠.V ⊓ O ρ.M : Subgroup G) :=
    𝔠.isPGroup_P.to_le (inf_le_left.trans hVP)
  have hAVs : A ≤ normalizer ((𝔠.V ⊓ O ρ.M : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf
      ⟨𝔠.A_le_normalizer_V ha, le_normalizer_O _ (ρ.A_le_centralizer_of_le ρ.X_le_A ha)⟩
  have hPVs : 𝔠.P ≤ normalizer ((𝔠.V ⊓ O ρ.M : Subgroup G) : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf
      ⟨𝔠.K_eq_normalizer_V ▸ hPK hg, le_normalizer_O _ (hPM hg)⟩
  refine ⟨normalizer ((𝔠.V ⊓ O ρ.M : Subgroup G) : Set G),
    ⟨⟨_, hVs1, hVsp, rfl⟩, hAVs, 𝔠.P, 𝔠.hP, hPVs⟩, ?_, ?_⟩
  · rw [hVs]
    exact 𝔠.covers_normalizer_inf_centralizer_T₂ hPM hT₂syl.isPGroup hT₂X hT₂R hTM₀
  · refine (𝔠.covers_centralizer_V 𝔠.quotIs_N₀ hXN₀).mono fun g hg => ?_
    apply centralizer_le_normalizer
    exact centralizer_le (fun x hx => (inf_le_left : 𝔠.V ⊓ O ρ.M ≤ 𝔠.V) hx) hg.1

end Sec5ConfigR

end CFSG.GH72
