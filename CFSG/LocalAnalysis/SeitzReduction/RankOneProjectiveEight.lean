module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneDegreeEightD8
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.SeitzReduction.RankOne

open Equiv Subgroup DegreeEight

private theorem projEight_mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {g : G} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hg x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  have : y = x := by
    have h1 := congrArg (fun z => g⁻¹ * z * g) hyx
    simpa [mul_assoc] using h1
  exact this ▸ hy

theorem card_le_mul_card_inf_centralizer_of_conj_mem {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (w : G) (I : Set G) (hI : ∀ s ∈ S, s * w * s⁻¹ ∈ I) :
    Nat.card S ≤ Nat.card I * Nat.card (S ⊓ centralizer ({w} : Set G) : Subgroup G) := by
  classical
  set C : Subgroup S := (centralizer ({w} : Set G)).subgroupOf S with hC
  have h1 := card_eq_card_quotient_mul_card_subgroup C
  have hCc : Nat.card C = Nat.card (S ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    rw [hC, ← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmemC : ∀ a b : S, (a : G)⁻¹ * b * w = w * ((a : G)⁻¹ * b) ↔ a⁻¹ * b ∈ C := by
    intro a b
    rw [hC, mem_subgroupOf, mem_centralizer_singleton_iff]
    simp only [coe_mul, coe_inv]
  have hwd : ∀ a b : S, a⁻¹ * b ∈ C →
      (a : G) * w * (a : G)⁻¹ = (b : G) * w * (b : G)⁻¹ := by
    intro a b hab
    have hab' := (hmemC a b).mpr hab
    calc (a : G) * w * (a : G)⁻¹
        = a * (w * ((a : G)⁻¹ * b)) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ := by group
      _ = a * ((a : G)⁻¹ * b * w) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ := by rw [hab']
      _ = (b : G) * w * (b : G)⁻¹ := by group
  let g : S → I := fun s => ⟨(s : G) * w * (s : G)⁻¹, hI s s.2⟩
  let f : S ⧸ C → I := fun q => Quotient.liftOn' q g (fun a b hab => by
    apply Subtype.ext
    exact hwd a b (QuotientGroup.leftRel_apply.mp hab))
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    have h2 : (a : G) * w * (a : G)⁻¹ = (b : G) * w * (b : G)⁻¹ := congrArg Subtype.val hxy
    rw [QuotientGroup.eq, ← hmemC]
    calc (a : G)⁻¹ * b * w = (a : G)⁻¹ * ((b : G) * w * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * ((a : G) * w * (a : G)⁻¹) * b := by rw [h2]
      _ = w * ((a : G)⁻¹ * b) := by group
  have h3 : Nat.card (S ⧸ C) ≤ Nat.card I := Nat.card_le_card_of_injective f hf
  rw [h1, hCc]
  exact Nat.mul_le_mul_right _ h3

section Abstract

variable {D : Type} [Group D] [Finite D]

theorem exists_normal_index_two_of_projective_eight {U V : Subgroup D} {t : D}
    (hV2 : IsPGroup 2 V) (hUV : U ≤ V) (htV : t ∈ V) (htU : t ∉ U) (htt : t * t = 1)
    (hVU : ∀ v ∈ V, v ∉ U → t * v ∈ U) (hsqV : ∀ v ∈ V, v * v ∈ U)
    (hUn : normalizer (V : Set D) ≤ normalizer (U : Set D))
    (π : normalizer (V : Set D) →* Perm (Option (ZMod 7)))
    (hrange : π.range = natPSL)
    (hker : ∀ x : normalizer (V : Set D), π x = 1 ↔ (x : D) ∈ V)
    (hfix : ∀ x : normalizer (V : Set D), ∀ v ∈ V, v ∉ U → (x : D) * v = v * x →
      ∃ z, π x z = z)
    (hconjU : ∀ g : D, g⁻¹ * t * g ∉ U)
    (hconjtU : ∀ u ∈ U, ∃ g : D, g⁻¹ * t * g = t * u)
    (hinv : ∀ w : normalizer (V : Set D), π w ∈ d8 → (w : D) ∉ V → (w : D) * w = 1 →
      ∀ g : D, g⁻¹ * t * g ≠ w) :
    ∃ M : Subgroup D, M.Normal ∧ M.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVN : V ≤ normalizer (V : Set D) := le_normalizer
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hmemrange : ∀ x : normalizer (V : Set D), π x ∈ natPSL := fun x => by
    rw [← hrange]; exact ⟨x, rfl⟩
  have hFP : ∀ x : normalizer (V : Set D), π x ∈ d8 → ∀ v ∈ V, v ∉ U →
      (x : D) * v = v * x → (x : D) ∈ V := by
    intro x hx v hv hvU hxv
    obtain ⟨z, hz⟩ := hfix x v hv hvU hxv
    exact (hker x).mp (eq_one_of_mem_natPSL_of_fix (hmemrange x) hz (pow_four_of_mem_d8 hx))
  have hconjVU : ∀ g ∈ normalizer (V : Set D), ∀ v ∈ V, g * v * g⁻¹ * v ∈ U := by
    intro g hg v hv
    have hgU := hUn hg
    have hgv : g * v * g⁻¹ ∈ V := (mem_normalizer_iff.mp hg v).mp hv
    by_cases hvU : v ∈ U
    · exact mul_mem ((mem_normalizer_iff.mp hgU v).mp hvU) hvU
    · have hgvU : g * v * g⁻¹ ∉ U := fun h => hvU ((mem_normalizer_iff.mp hgU v).mpr h)
      have h1 := hVU _ hgv hgvU
      have h2 := hVU v hv hvU
      have htU' : t * (t * (g * v * g⁻¹)) * t⁻¹ ∈ U :=
        (mem_normalizer_iff.mp (hUn (hVN htV)) _).mp h1
      have h3 : g * v * g⁻¹ * v = t * (t * (g * v * g⁻¹)) * t⁻¹ * (t * v) := by
        rw [htinv]
        calc g * v * g⁻¹ * v = (t * t) * (g * v * g⁻¹) * (t * t) * v := by rw [htt]; group
          _ = t * (t * (g * v * g⁻¹)) * t * (t * v) := by group
      rw [h3]
      exact mul_mem htU' h2
  set S₁ : Subgroup D := (d8.comap π).map (normalizer (V : Set D)).subtype with hS₁def
  have hmemS : ∀ x : D, x ∈ S₁ ↔ ∃ h : x ∈ normalizer (V : Set D), π ⟨x, h⟩ ∈ d8 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  have hVS : V ≤ S₁ := by
    intro v hv
    rw [hmemS]
    refine ⟨hVN hv, ?_⟩
    rw [(hker ⟨v, hVN hv⟩).mpr hv]
    exact one_mem _
  have hS₁2 : IsPGroup 2 S₁ := by
    intro x
    obtain ⟨hxN, hxd⟩ := (hmemS x).mp x.2
    have h4 : π ⟨(x : D), hxN⟩ ^ 4 = 1 := pow_four_of_mem_d8 hxd
    have hx4V : (x : D) ^ 4 ∈ V := by
      have h5 := (hker (⟨(x : D), hxN⟩ ^ 4)).mp (by rw [map_pow, h4])
      simpa using h5
    obtain ⟨k, hk⟩ := hV2 ⟨(x : D) ^ 4, hx4V⟩
    have hk' : ((x : D) ^ 4) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k + 2, Subtype.ext ?_⟩
    have h6 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by ring
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [h6, pow_mul, hk']
  have hC : ∀ x ∈ S₁, ∀ g : D, g⁻¹ * t * g = x → t * x ∈ U := by
    intro x hx g hgx
    obtain ⟨hxN, hxd⟩ := (hmemS x).mp hx
    by_cases hxV : x ∈ V
    · by_cases hxU : x ∈ U
      · exact absurd (hgx ▸ hxU) (hconjU g)
      · exact hVU x hxV hxU
    · exfalso
      have hxx : x * x = 1 := by
        rw [← hgx]
        calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [htt]; group
      exact hinv ⟨x, hxN⟩ hxd hxV hxx g hgx
  obtain ⟨T, hST⟩ := hS₁2.exists_le_sylow
  have hSeq : S₁ = (T : Subgroup D) := by
    by_contra hne
    set I := S₁.subgroupOf (T : Subgroup D) with hI
    have hIlt : I < ⊤ := by
      refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hST fun x hx => ?_)
      have : (⟨x, hx⟩ : (T : Subgroup D)) ∈ I := by
        rw [htop]
        trivial
      exact mem_subgroupOf.mp this
    have : Group.IsNilpotent (T : Subgroup D) := T.isPGroup'.isNilpotent
    have hlt := Group.normalizerCondition_of_isNilpotent (G := (T : Subgroup D)) I hIlt
    obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
    have hzN : (x : D) ∈ normalizer (S₁ : Set D) := by
      have : x ∈ (normalizer (S₁ : Set D)).subgroupOf (T : Subgroup D) := by
        rw [subgroupOf_normalizer_eq hST]; exact hxN
      exact mem_subgroupOf.mp this
    have hzS : (x : D) ∉ S₁ := fun h => hxI (mem_subgroupOf.mpr h)
    set z : D := (x : D) with hz
    have hztU : ∀ u ∈ U, t * (z * (t * u) * z⁻¹) ∈ U := by
      intro u hu
      obtain ⟨g, hg⟩ := hconjtU u hu
      have hmem : z * (t * u) * z⁻¹ ∈ S₁ :=
        (mem_normalizer_iff.mp hzN _).mp (hVS (mul_mem htV (hUV hu)))
      refine hC _ hmem (g * z⁻¹) ?_
      rw [← hg]
      group
    have hzV : z ∈ normalizer (V : Set D) := by
      apply projEight_mem_normalizer_of_conj_mem
      have hcase : ∀ u ∈ U, z * (t * u) * z⁻¹ ∈ V := fun u hu => by
        have h1 := hztU u hu
        have h2 : z * (t * u) * z⁻¹ = t * (t * (z * (t * u) * z⁻¹)) := by
          rw [← mul_assoc t t, htt, one_mul]
        rw [h2]
        exact mul_mem htV (hUV h1)
      intro v hv
      by_cases hvU : v ∈ U
      · have h1 := hcase 1 (one_mem U)
        have h2 := hcase v hvU
        rw [mul_one] at h1
        have h3 : z * v * z⁻¹ = (z * t * z⁻¹) * (z * (t * v) * z⁻¹) := by
          calc z * v * z⁻¹ = z * ((t * t) * v) * z⁻¹ := by rw [htt, one_mul]
            _ = (z * t * z⁻¹) * (z * (t * v) * z⁻¹) := by group
        rw [h3]
        exact mul_mem h1 h2
      · have h1 := hcase (t * v) (hVU v hv hvU)
        have h2 : t * (t * v) = v := by rw [← mul_assoc t t, htt, one_mul]
        rwa [h2] at h1
    have hπzN : π ⟨z, hzV⟩ ∈ normalizer (d8 : Set (Perm (Option (ZMod 7)))) := by
      apply projEight_mem_normalizer_of_conj_mem
      intro δ hδ
      have hδr : δ ∈ π.range := by rw [hrange]; exact d8_le_natPSL hδ
      obtain ⟨y, rfl⟩ := hδr
      have hyS : (y : D) ∈ S₁ := (hmemS y).mpr ⟨y.2, hδ⟩
      have hzy : z * y * z⁻¹ ∈ S₁ := (mem_normalizer_iff.mp hzN _).mp hyS
      obtain ⟨hzyN, hzyd⟩ := (hmemS _).mp hzy
      have heq : (⟨z * y * z⁻¹, hzyN⟩ : normalizer (V : Set D)) =
          ⟨z, hzV⟩ * y * ⟨z, hzV⟩⁻¹ := rfl
      rw [heq, map_mul, map_mul, map_inv] at hzyd
      exact hzyd
    have hz2 : ∃ k : ℕ, π ⟨z, hzV⟩ ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := T.isPGroup' x
      refine ⟨k, ?_⟩
      have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [← map_pow]
      have : (⟨z, hzV⟩ : normalizer (V : Set D)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    exact hzS ((hmemS z).mpr ⟨hzV, mem_d8_of_normalizes (hmemrange _) hz2 hπzN⟩)
  have hidx : ¬ 2 ∣ S₁.index := by
    rw [hSeq]
    exact Sylow.not_dvd_index T
  have hrho : d8Rho ∈ π.range := by rw [hrange]; exact d8Rho_mem_natPSL
  obtain ⟨x₀, hx₀⟩ := hrho
  have hx₀S : (x₀ : D) ∈ S₁ := (hmemS _).mpr ⟨x₀.2, by
    have : (⟨(x₀ : D), x₀.2⟩ : normalizer (V : Set D)) = x₀ := rfl
    rw [this, hx₀]; exact d8Rho_mem_d8⟩
  set y₀ : D := (x₀ : D) * x₀ with hy₀
  have hy₀U : y₀ ∈ normalizer (U : Set D) := hUn (mul_mem x₀.2 x₀.2)
  set H₀ : Subgroup D := zpowers y₀ ⊔ U with hH₀
  have hmemH₀ : ∀ h ∈ H₀, ∃ k : ℤ, ∃ u ∈ U, y₀ ^ k * u = h := by
    intro h hh
    have hh' : h ∈ ((zpowers y₀ ⊔ U : Subgroup D) : Set D) := hh
    rw [coe_mul_of_left_le_normalizer_right (zpowers y₀) U (zpowers_le.mpr hy₀U)] at hh'
    obtain ⟨a, ha, u, hu, rfl⟩ := hh'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact ⟨k, u, hu, rfl⟩
  have hUH : U ≤ H₀ := le_sup_right
  have hyH : y₀ ∈ H₀ := mem_sup_left (mem_zpowers y₀)
  have htH : t ∉ H₀ := by
    intro htH
    obtain ⟨k, u, hu, hk⟩ := hmemH₀ t htH
    have hyk : y₀ ^ k = t * u⁻¹ := by rw [← hk]; group
    have hykV : y₀ ^ k ∈ V := hyk ▸ mul_mem htV (hUV (inv_mem hu))
    have hykU : y₀ ^ k ∉ U := fun h => htU (by rw [← hk]; exact mul_mem h hu)
    have hcomm : (x₀ : D) * y₀ ^ k = y₀ ^ k * x₀ := by
      have h1 : Commute (x₀ : D) y₀ := (Commute.refl _).mul_right (Commute.refl _)
      exact (h1.zpow_right k).eq
    have hx₀V := hFP x₀ (by rw [hx₀]; exact d8Rho_mem_d8) _ hykV hykU hcomm
    have h1 := (hker x₀).mpr hx₀V
    rw [hx₀] at h1
    exact d8Rho_ne_one h1
  have hsq : ∀ x ∈ S₁, x * x ∈ H₀ := by
    intro x hx
    obtain ⟨hxN, hxd⟩ := (hmemS x).mp hx
    rcases d8_cases hxd with h | h | h
    · have hxxV : x * x ∈ V := by
        have h1 := (hker (⟨x, hxN⟩ * ⟨x, hxN⟩)).mp (by rw [map_mul]; exact h)
        simpa using h1
      by_cases hxV : x ∈ V
      · exact hUH (hsqV x hxV)
      · by_contra hxxH
        have hxxU : x * x ∉ U := fun h' => hxxH (hUH h')
        exact hxV (hFP ⟨x, hxN⟩ hxd (x * x) hxxV hxxU (by group))
    · set v : D := (x₀ : D)⁻¹ * x with hv
      have hvV : v ∈ V := by
        have h1 := (hker (x₀⁻¹ * ⟨x, hxN⟩)).mp (by rw [map_mul, map_inv, hx₀, h, inv_mul_cancel])
        simpa [hv] using h1
      have h1 := hconjVU (x₀ : D)⁻¹ (inv_mem x₀.2) v hvV
      have h2 : x * x = y₀ * ((x₀ : D)⁻¹ * v * (x₀ : D)⁻¹⁻¹ * v) := by
        rw [hv, hy₀]; group
      rw [h2]
      exact mul_mem hyH (hUH h1)
    · set v : D := (x₀ : D) * x with hv
      have hvV : v ∈ V := by
        have h1 := (hker (x₀ * ⟨x, hxN⟩)).mp
          (by rw [map_mul, hx₀, h, d8RhoInv_eq, mul_inv_cancel])
        simpa [hv] using h1
      have h1 := hconjVU (x₀ : D) x₀.2 v hvV
      have h2 : x * x = y₀⁻¹ * ((x₀ : D) * v * (x₀ : D)⁻¹ * v) := by
        rw [hv, hy₀]; group
      rw [h2]
      exact mul_mem (inv_mem hyH) (hUH h1)
  have hH₀S : H₀ ≤ S₁ := sup_le (zpowers_le.mpr (mul_mem hx₀S hx₀S)) (hUV.trans hVS)
  have : Finite (Subgroup D) :=
    Finite.of_injective (fun K : Subgroup D => (K : Set D)) SetLike.coe_injective
  set 𝒮 : Set (Subgroup D) := {K | H₀ ≤ K ∧ K ≤ S₁ ∧ t ∉ K} with h𝒮
  obtain ⟨M, ⟨hHM, hMS, htM⟩, hmax⟩ := (Set.toFinite 𝒮).exists_maximal ⟨H₀, le_rfl, hH₀S, htH⟩
  have hMn : ∀ s ∈ S₁, ∀ m ∈ M, s * m * s⁻¹ ∈ M := by
    intro s hs m hm
    have h1 : s * m * s⁻¹ = (s * m) * (s * m) * m⁻¹ * (s⁻¹ * s⁻¹) := by group
    rw [h1]
    exact mul_mem (mul_mem (hHM (hsq _ (mul_mem hs (hMS hm)))) (inv_mem hm))
      (hHM (hsq _ (inv_mem hs)))
  have hbt : ∀ b ∈ S₁, b ∉ M → b * t ∈ M := by
    intro b hb hbM
    have hbN : zpowers b ≤ normalizer (M : Set D) :=
      zpowers_le.mpr (projEight_mem_normalizer_of_conj_mem (hMn b hb))
    have htM' : t ∈ zpowers b ⊔ M := by
      by_contra htM'
      have hle : M ≤ zpowers b ⊔ M := le_sup_right
      have hmem : zpowers b ⊔ M ∈ 𝒮 := ⟨hHM.trans hle, sup_le (zpowers_le.mpr hb) hMS, htM'⟩
      exact hbM (hmax hmem hle (mem_sup_left (mem_zpowers b)))
    have h1 : t ∈ ((zpowers b ⊔ M : Subgroup D) : Set D) := htM'
    rw [coe_mul_of_left_le_normalizer_right (zpowers b) M hbN] at h1
    obtain ⟨a, ha, m, hm, ham⟩ := h1
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    have hbb : b ^ (2 : ℤ) ∈ M := by
      rw [zpow_two]; exact hHM (hsq b hb)
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exfalso
      apply htM
      have ham' : (b ^ (2 : ℤ)) ^ j * m = t := by
        rw [← zpow_mul]; exact ham
      rw [← ham']
      exact mul_mem (zpow_mem hbb j) hm
    · have hc : (b ^ (2 : ℤ)) ^ j ∈ M := zpow_mem hbb j
      have ham' : (b ^ (2 : ℤ)) ^ j * b * m = t := by
        rw [← zpow_mul, ← zpow_add_one]; exact ham
      have hb' : b = ((b ^ (2 : ℤ)) ^ j)⁻¹ * t * m⁻¹ := by rw [← ham']; group
      have htm : t * m⁻¹ * t⁻¹ ∈ M := hMn t (hVS htV) m⁻¹ (inv_mem hm)
      have h2 : b * t = ((b ^ (2 : ℤ)) ^ j)⁻¹ * (t * m⁻¹ * t⁻¹) := by
        conv_lhs => rw [hb']
        rw [htinv]; group
      rw [h2]
      exact mul_mem (inv_mem hc) htm
  have hMidx : M.relIndex S₁ = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨t, hVS htV, fun b hb => ?_⟩
    by_cases hbM : b ∈ M
    · refine Or.inr ⟨hbM, fun hbt' => htM ?_⟩
      have h1 : t = b⁻¹ * (b * t) := by group
      rw [h1]
      exact mul_mem (inv_mem hbM) hbt'
    · exact Or.inl ⟨hbt b hb hbM, hbM⟩
  have hconj : ∀ g : D, g⁻¹ * t * g ∉ M := by
    intro g hg
    have h1 := hC _ (hMS hg) g rfl
    apply htM
    have h2 : t = (t * (g⁻¹ * t * g)) * (g⁻¹ * t * g)⁻¹ := by group
    rw [h2]
    exact mul_mem (hHM (hUH h1)) (inv_mem hg)
  have hmin : ∀ y ∈ S₁, y ∉ M → orderOf t ≤ orderOf y := fun y _ hyM =>
    Endings.orderOf_le_of_ne_one htt fun h => hyM (h ▸ one_mem M)
  exact CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hS₁2 hidx hMS hMidx (hVS htV)
    htM hmin hconj

theorem exists_normal_index_two_of_projective_eight_layer {U V W : Subgroup D} {t : D}
    (hV2 : IsPGroup 2 V) (hUV : U ≤ V) (htV : t ∈ V) (htU : t ∉ U) (htt : t * t = 1)
    (hVU : ∀ v ∈ V, v ∉ U → t * v ∈ U) (hsqV : ∀ v ∈ V, v * v ∈ U)
    (hUn : normalizer (V : Set D) ≤ normalizer (U : Set D))
    (π : normalizer (V : Set D) →* Perm (Option (ZMod 7)))
    (hrange : π.range = natPSL)
    (hker : ∀ x : normalizer (V : Set D), π x = 1 ↔ (x : D) ∈ V)
    (hfix : ∀ x : normalizer (V : Set D), ∀ v ∈ V, v ∉ U → (x : D) * v = v * x →
      ∃ z, π x z = z)
    (hconjU : ∀ g : D, g⁻¹ * t * g ∉ U)
    (hconjtU : ∀ u ∈ U, ∃ g : D, g⁻¹ * t * g = t * u)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hsqW : ∀ u ∈ U, u * u ∈ W) (hinvW : ∀ u ∈ U, u * u = 1 → u ∈ W)
    (hlayer : ∀ w : normalizer (V : Set D), (w : D) ∉ V →
      ∃ u ∈ U, (w : D) * u * (w : D)⁻¹ * u⁻¹ ∉ W)
    (hCt : ∀ x : D, x * t = t * x → (∃ k : ℕ, x ^ 2 ^ k = 1) → x * x = 1) :
    ∃ M : Subgroup D, M.Normal ∧ M.index = 2 := by
  refine exists_normal_index_two_of_projective_eight hV2 hUV htV htU htt hVU hsqV hUn π hrange
    hker hfix hconjU hconjtU ?_
  intro w _ hwV hww g hgw
  obtain ⟨u, hu, hwu⟩ := hlayer w hwV
  have hwU : (w : D) * u * (w : D)⁻¹ ∈ U := (mem_normalizer_iff.mp (hUn w.2) u).mp hu
  set c : D := u * ((w : D) * u * (w : D)⁻¹) with hc
  have hcU : c ∈ U := mul_mem hu hwU
  have hcw : (w : D) * c = c * w := by
    have h1 : (w : D) * c * (w : D)⁻¹ = ((w : D) * u * (w : D)⁻¹) * u := by
      rw [hc]
      calc (w : D) * (u * ((w : D) * u * (w : D)⁻¹)) * (w : D)⁻¹
          = ((w : D) * u * (w : D)⁻¹) * (((w : D) * w) * u * ((w : D) * w)⁻¹) := by group
        _ = ((w : D) * u * (w : D)⁻¹) * u := by rw [hww]; group
    have h2 : (w : D) * c * (w : D)⁻¹ = c := by
      rw [h1, hc, hUab _ hwU u hu]
    calc (w : D) * c = (w : D) * c * (w : D)⁻¹ * w := by group
      _ = c * w := by rw [h2]
  have hcW : c ∉ W := by
    intro hcW
    apply hwu
    have h1 : (w : D) * u * (w : D)⁻¹ * u⁻¹ = c * (u * u)⁻¹ := by
      have h2 := hUab u hu ((w : D) * u * (w : D)⁻¹) hwU
      rw [hc, h2]
      group
    rw [h1]
    exact mul_mem hcW (inv_mem (hsqW u hu))
  have hcc : c * c ≠ 1 := fun h => hcW (hinvW c hcU h)
  have hc2 : ∃ k : ℕ, c ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hV2 ⟨c, hUV hcU⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hgc : (g * c * g⁻¹) * t = t * (g * c * g⁻¹) := by
    rw [← hgw] at hcw
    calc g * c * g⁻¹ * t = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by rw [hcw]
      _ = t * (g * c * g⁻¹) := by group
  have hgc2 : ∃ k : ℕ, (g * c * g⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hc2
    exact ⟨k, by rw [conj_pow, hk]; group⟩
  have h1 := hCt _ hgc hgc2
  apply hcc
  calc c * c = g⁻¹ * ((g * c * g⁻¹) * (g * c * g⁻¹)) * g := by group
    _ = 1 := by rw [h1]; group

end Abstract

end CFSG.SeitzReduction.RankOne
