module

public import CFSG.LocalAnalysis.GH72.Sec4Conj
public import CFSG.LocalAnalysis.GH72.Coprime
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial

public section

namespace CFSG.GH72

open Subgroup

namespace G5d

section OddCores

variable {G : Type*} [Group G]

theorem le_O_of_le_normalizer {D H : Subgroup G} (hDH : D ≤ H)
    (hHD : H ≤ normalizer (D : Set G)) (hD : Odd (Nat.card D)) : D ≤ O H := by
  have hn : (D.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hDH).mpr hHD
  have hodd : Odd (Nat.card (D.subgroupOf H)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]
  have hle := ABGLocalTools.le_oddCore_of_normal hn hodd
  intro d hd
  exact ⟨⟨d, hDH hd⟩, hle hd, rfl⟩

theorem O_inf_le_O_of_le [Finite G] {H K : Subgroup G} (hHK : H ≤ K) : O K ⊓ H ≤ O H := by
  refine le_O_of_le_normalizer inf_le_right ?_ ?_
  · intro h hh
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer_O K (hHK hh), le_normalizer hh⟩
  · exact (card_O_odd K).of_dvd_nat (card_dvd_of_le inf_le_left)

end OddCores

section Coprime

variable {G : Type*} [Group G]

theorem mem_sup_of_le_normalizer {N H : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) {g : G}
    (hg : g ∈ N ⊔ H) : ∃ n ∈ N, ∃ h ∈ H, n * h = g := by
  have hg' : g ∈ ((N ⊔ H : Subgroup G) : Set G) := hg
  rw [coe_mul_of_right_le_normalizer_left N H hHN] at hg'
  obtain ⟨n, hn, h, hh, rfl⟩ := hg'
  exact ⟨n, hn, h, hh, rfl⟩

theorem mem_sup_of_le_normalizer' {N H : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) {g : G}
    (hg : g ∈ H ⊔ N) : ∃ h ∈ H, ∃ n ∈ N, h * n = g := by
  have hg' : g ∈ ((H ⊔ N : Subgroup G) : Set G) := hg
  rw [coe_mul_of_left_le_normalizer_right H N hHN] at hg'
  obtain ⟨h, hh, n, hn, rfl⟩ := hg'
  exact ⟨h, hh, n, hn, rfl⟩

variable [Finite G]

theorem exists_fixed_mem_coset_of_isPGroup {X D : Subgroup G} (hX : IsPGroup 2 X) (hD : Odd (Nat.card D))
    (hXD : X ≤ normalizer (D : Set G)) {n : G} (hn : ∀ x ∈ X, x * n * x⁻¹ * n⁻¹ ∈ D) :
    ∃ d ∈ D, ∀ x ∈ X, x * (d * n) * x⁻¹ = d * n := by
  classical
  have hmem : ∀ x ∈ X, ∀ c : G, c * n⁻¹ ∈ D → x * c * x⁻¹ * n⁻¹ ∈ D := by
    intro x hx c hc
    have h1 : x * c * x⁻¹ * n⁻¹ = (x * (c * n⁻¹) * x⁻¹) * (x * n * x⁻¹ * n⁻¹) := by group
    rw [h1]
    exact D.mul_mem ((mem_normalizer_iff.mp (hXD hx) _).mp hc) (hn x hx)
  set Ω : Set G := {c | c * n⁻¹ ∈ D}
  let inst : MulAction X Ω :=
    { smul := fun x c => ⟨(x : G) * c * (x : G)⁻¹, hmem x x.2 c c.2⟩
      one_smul := fun c => Subtype.ext (by
        change (1 : G) * (c : G) * (1 : G)⁻¹ = c
        group)
      mul_smul := fun x y c => Subtype.ext (by
        change ((x * y : X) : G) * (c : G) * ((x * y : X) : G)⁻¹ =
          (x : G) * ((y : G) * (c : G) * (y : G)⁻¹) * (x : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card Ω = Nat.card D := by
    refine Nat.card_congr ⟨fun c => ⟨c * n⁻¹, c.2⟩, fun d => ⟨d * n, ?_⟩, ?_, ?_⟩
    · change (d : G) * n * n⁻¹ ∈ D
      simp
    · intro c
      apply Subtype.ext
      simp
    · intro d
      apply Subtype.ext
      simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hX.card_modEq_card_fixedPoints Ω
  rw [hcard] at hmod
  have hfix : Nat.card (MulAction.fixedPoints X Ω) ≠ 0 := by
    intro h0
    rw [h0, Nat.ModEq, Nat.zero_mod] at hmod
    exact Nat.odd_iff.mp hD |>.symm.trans hmod |> absurd <| by norm_num
  obtain ⟨⟨c, hc⟩, hcf⟩ := (Nat.card_ne_zero.mp hfix).1.some
  refine ⟨c * n⁻¹, hc, fun x hx => ?_⟩
  have := congrArg Subtype.val (hcf ⟨x, hx⟩)
  change (x : G) * c * (x : G)⁻¹ = c at this
  simpa [mul_assoc] using this

theorem exists_mul_of_eq_O_sup {K N X : Subgroup G} (hX : IsPGroup 2 X) (hXK : X ≤ K)
    (hXN : X ≤ normalizer (N : Set G)) (hNK : N ≤ K) (hK : K = O K ⊔ N) {k : G}
    (hk : k ∈ K ⊓ centralizer (X : Set G)) :
    ∃ o ∈ O K ⊓ centralizer (X : Set G), ∃ n ∈ N ⊓ centralizer (X : Set G), o * n = k := by
  obtain ⟨hkK, hkX⟩ := hk
  have hON : N ≤ normalizer (O K : Set G) := hNK.trans (le_normalizer_O K)
  have hk' : k ∈ O K ⊔ N := hK ▸ hkK
  obtain ⟨o, ho, m, hm, rfl⟩ := mem_sup_of_le_normalizer hON hk'
  set D : Subgroup G := O K ⊓ N
  have hDodd : Odd (Nat.card D) := (card_O_odd K).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hXD : X ≤ normalizer (D : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer_O K (hXK hx), hXN hx⟩
  have hcomm : ∀ x ∈ X, x * (o * m) * x⁻¹ = o * m := fun x hx =>
    (mem_centralizer_iff.mp hkX x hx).symm ▸ by group
  have hstab : ∀ x ∈ X, x * m * x⁻¹ * m⁻¹ ∈ D := by
    intro x hx
    refine ⟨?_, ?_⟩
    ·
      have h1 : x * m * x⁻¹ * m⁻¹ = (x * o * x⁻¹)⁻¹ * (x * (o * m) * x⁻¹) * m⁻¹ := by group
      rw [h1, hcomm x hx, show (x * o * x⁻¹)⁻¹ * (o * m) * m⁻¹ = (x * o * x⁻¹)⁻¹ * o by group]
      exact (O K).mul_mem ((O K).inv_mem
        ((mem_normalizer_iff.mp (le_normalizer_O K (hXK hx)) o).mp ho)) ho
    · exact N.mul_mem ((mem_normalizer_iff.mp (hXN hx) m).mp hm) (N.inv_mem hm)
  obtain ⟨d, ⟨hdO, hdN⟩, hfix⟩ := exists_fixed_mem_coset_of_isPGroup hX hDodd hXD hstab
  have hdm : d * m ∈ N ⊓ centralizer (X : Set G) := by
    refine ⟨N.mul_mem hdN hm, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := hfix x hx
    calc x * (d * m) = x * (d * m) * x⁻¹ * x := by group
      _ = d * m * x := by rw [this]
  have hod : o * d⁻¹ ∈ O K ⊓ centralizer (X : Set G) := by
    refine ⟨(O K).mul_mem ho ((O K).inv_mem hdO), mem_centralizer_iff.mpr fun x hx => ?_⟩
    have h1 := hcomm x hx
    have h2 := hfix x hx
    have h3 : x * (o * d⁻¹) * x⁻¹ = o * d⁻¹ := by
      calc x * (o * d⁻¹) * x⁻¹ = (x * (o * m) * x⁻¹) * (x * (d * m) * x⁻¹)⁻¹ := by group
        _ = o * d⁻¹ := by rw [h1, h2]; group
    calc x * (o * d⁻¹) = x * (o * d⁻¹) * x⁻¹ * x := by group
      _ = o * d⁻¹ * x := by rw [h3]
  exact ⟨o * d⁻¹, hod, d * m, hdm, by group⟩

theorem covers_of_eq_O_sup {K N X M₀ M : Subgroup G} (hX : IsPGroup 2 X) (hXK : X ≤ K)
    (hXN : X ≤ normalizer (N : Set G)) (hNK : N ≤ K) (hK : K = O K ⊔ N)
    (hM : M = centralizer (X : Set G)) (hM₀M : M₀ ≤ M) (hOM₀ : O M ≤ M₀)
    (hOKM : O K ⊓ M ≤ O M) (hcov : Covers K M₀ (O M)) : Covers N M₀ (O M) := by
  intro m hm
  have hOMn : M₀ ≤ normalizer (O M : Set G) := hM₀M.trans (le_normalizer_O M)
  obtain ⟨k, ⟨hkK, hkM₀⟩, o, ho, rfl⟩ :=
    mem_sup_of_le_normalizer' (inf_le_right.trans hOMn) (hcov hm)
  obtain ⟨o', ⟨ho'K, ho'X⟩, n', ⟨hn'N, hn'X⟩, rfl⟩ :=
    exists_mul_of_eq_O_sup hX hXK hXN hNK hK ⟨hkK, hM ▸ hM₀M hkM₀⟩
  have ho'M : o' ∈ O M := hOKM ⟨ho'K, hM ▸ ho'X⟩
  have hn'M₀ : n' ∈ M₀ := by
    have : n' = o'⁻¹ * (o' * n') := by group
    rw [this]
    exact M₀.mul_mem (M₀.inv_mem (hOM₀ ho'M)) hkM₀
  have hconj : n'⁻¹ * o' * n' ∈ O M :=
    (mem_normalizer_iff.mp (hOMn (M₀.inv_mem hn'M₀)) o').mp ho'M |> fun h => by
      simpa [mul_assoc] using h
  have : o' * n' * o = n' * ((n'⁻¹ * o' * n') * o) := by group
  rw [this]
  exact mul_mem_sup ⟨hn'N, hn'M₀⟩ ((O M).mul_mem hconj ho)

end Coprime

section MaxInv

variable {G : Type*} [Group G] [Finite G]

theorem exists_isMaxInvIn_ge {p : ℕ} {A H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup p Q)
    (hAQ : A ≤ normalizer (Q : Set G)) : ∃ P, IsMaxInvIn p A H P ∧ Q ≤ P := by
  set 𝒮 : Set (Subgroup G) :=
    {P | P ≤ H ∧ IsPGroup p P ∧ A ≤ normalizer (P : Set G) ∧ Q ≤ P}
  obtain ⟨P, hQP, hP⟩ := (Set.toFinite 𝒮).exists_le_maximal
    (show Q ∈ 𝒮 from ⟨hQH, hQ, hAQ, le_rfl⟩)
  obtain ⟨⟨hPH, hPp, hAP, -⟩, hmax⟩ := hP
  refine ⟨P, ⟨hPH, hPp, hAP, fun R hRH hR hAR hPR => ?_⟩, hQP⟩
  exact le_antisymm (hmax ⟨hRH, hR, hAR, hQP.trans hPR⟩ hPR) hPR

end MaxInv

section Frattini

variable {G : Type*} [Group G] [Finite G]

theorem eq_sup_inf_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {K O T : Subgroup G}
    (hOK : O ≤ K) (hKO : K ≤ normalizer (O : Set G)) (hT : ABGLocalTools.IsSylowOf p T O) :
    K = O ⊔ (K ⊓ normalizer (T : Set G)) := by
  refine le_antisymm (fun k hk => ?_) (sup_le hOK inf_le_left)
  have hTk : T.map (MulAut.conj k).toMonoidHom ≤ O := by
    rw [← mem_normalizer_iff_map_conj_eq.mp (hKO hk)]
    exact map_mono hT.le
  obtain ⟨c, hcO, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hT hTk
    (hT.isPGroup.map (MulAut.conj k).toMonoidHom)
  rw [G4b.map_conj_map_conj] at hc
  have heq : T.map (MulAut.conj (c * k)).toMonoidHom = T :=
    eq_of_le_of_card_ge hc (by rw [card_map_of_injective (MulAut.conj (c * k)).injective])
  have hck : c * k ∈ K ⊓ normalizer (T : Set G) :=
    ⟨K.mul_mem (hOK hcO) hk, mem_normalizer_iff_map_conj_eq.mpr heq⟩
  have : k = c⁻¹ * (c * k) := by group
  rw [this]
  exact mul_mem_sup (O.inv_mem hcO) hck

theorem exists_pLocal_covers_of_pConstrainedWrt {G : Type} [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {A Z W M₀ : Subgroup G} {x : G} (hA2 : IsPGroup 2 A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hZA : Z ≤ A) (hxZ : x ∈ Z)
    (hM₀ : M₀ ≤ centralizer (Z : Set G)) (hOM₀ : O (centralizer (Z : Set G)) ≤ M₀)
    (h : Sec4Setting.PConstrainedWrt q A (C x) W) :
    ∃ H : Subgroup G, CFSG.IsPLocal q H ∧ A ≤ H ∧
      Covers H M₀ (O (centralizer (Z : Set G))) ∧ Sec4Setting.PConstrainedWrt q A H W := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨T, hT, hAT, hWT⟩ := h
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    refine hWT fun w _ => mem_centralizer_iff.mpr fun t ht => ?_
    rw [SetLike.mem_coe, mem_bot] at ht
    rw [ht, one_mul, mul_one]
  have hTodd : Odd (Nat.card T) := by
    obtain ⟨n, hn⟩ := hT.isPGroup.exists_card_eq
    rw [hn]
    exact (hq.odd_of_ne_two hq2).pow
  refine ⟨normalizer (T : Set G), ⟨T, hT1, hT.isPGroup, rfl⟩, hAT, ?_, ?_⟩
  ·
    have hZ2 : IsPGroup 2 Z := hA2.to_le hZA
    have hZK : Z ≤ C x := fun z hz =>
      mem_centralizer_singleton_iff.mpr (hAc z (hZA hz) x (hZA hxZ))
    have hZN : Z ≤ normalizer ((C x ⊓ normalizer (T : Set G) : Subgroup G) : Set G) :=
      fun z hz => inf_normalizer_le_normalizer_inf
        ⟨le_normalizer (hZK hz), le_normalizer (hAT (hZA hz))⟩
    have hFr : C x = O (C x) ⊔ (C x ⊓ normalizer (T : Set G)) :=
      eq_sup_inf_normalizer_of_isSylowOf (map_subtype_le _) (le_normalizer_O _) hT
    have hMK : centralizer (Z : Set G) ≤ C x :=
      centralizer_le (Set.singleton_subset_iff.mpr hxZ)
    have hcov : Covers (C x) M₀ (O (centralizer (Z : Set G))) :=
      fun m hm => mem_sup_left ⟨hMK (hM₀ hm), hm⟩
    have h := covers_of_eq_O_sup hZ2 hZK hZN inf_le_left hFr rfl hM₀ hOM₀
      (O_inf_le_O_of_le hMK) hcov
    unfold Covers at h ⊢
    exact h.trans (sup_le_sup_right (inf_le_inf_right _ inf_le_right) _)
  ·
    have hTO : T ≤ O (normalizer (T : Set G)) := le_O_of_le_normalizer le_normalizer le_rfl hTodd
    obtain ⟨P', hP', hTP'⟩ := exists_isMaxInvIn_ge (A := A) (H := normalizer (T : Set G))
      le_normalizer hT.isPGroup hAT
    refine ⟨P' ⊓ O (normalizer (T : Set G)),
      isSylowOf_inf_O_of_isMaxInvIn hq hA2 (hAT.trans le_normalizer) hP', fun a ha =>
        inf_normalizer_le_normalizer_inf ⟨hP'.2.2.1 ha, le_normalizer_O _ (hAT ha)⟩, ?_⟩
    intro hW
    exact hWT (hW.trans (centralizer_le (le_inf hTP' hTO)))

end Frattini


theorem isPGroup_of_isE16 {G : Type*} [Group G] {A : Subgroup G} (hA : IsE16 A) : IsPGroup 2 A :=
  IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)

section Sec4

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem M₀_le (A : Subgroup G) : 𝔖.M₀ A ≤ 𝔖.M A :=
  sup_le (commutator_le.mpr fun _ ha _ hb => (𝔖.M A).mul_mem ((𝔖.M A).mul_mem
    ((𝔖.M A).mul_mem (map_subtype_le _ ha) (map_subtype_le _ hb))
    ((𝔖.M A).inv_mem (map_subtype_le _ ha))) ((𝔖.M A).inv_mem (map_subtype_le _ hb)))
    (map_subtype_le _)

theorem N₀_le (A : Subgroup G) : 𝔖.N₀ A ≤ 𝔖.N A :=
  sup_le (commutator_le.mpr fun _ ha _ hb => (𝔖.N A).mul_mem ((𝔖.N A).mul_mem
    ((𝔖.N A).mul_mem (map_subtype_le _ ha) (map_subtype_le _ hb))
    ((𝔖.N A).inv_mem (map_subtype_le _ ha))) ((𝔖.N A).inv_mem (map_subtype_le _ hb)))
    (map_subtype_le _)

theorem O_M_le_M₀ (A : Subgroup G) : O (𝔖.M A) ≤ 𝔖.M₀ A := le_sup_right

theorem O_N_le_N₀ (A : Subgroup G) : O (𝔖.N A) ≤ 𝔖.N₀ A := le_sup_right

include 𝔖 in
theorem oddCore_eq_bot : CFSG.oddCore G = ⊥ := 𝔖.mc.hyp.1

private theorem odd_card_of_isPGroup' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : IsPGroup p P) : Odd (Nat.card P) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

include 𝔖 in
theorem ne_top_of_isPLocal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hH : CFSG.IsPLocal p H) : H ≠ ⊤ := by
  obtain ⟨R, hR1, hRp, rfl⟩ := hH
  intro htop
  have hRn : R.Normal := normalizer_eq_top_iff.mp htop
  have hle := ABGLocalTools.le_oddCore_of_normal hRn (odd_card_of_isPGroup' hp hp2 hRp)
  rw [oddCore_eq_bot 𝔖, le_bot_iff] at hle
  exact hR1 hle

variable {A : Subgroup G}

theorem not_mem_Y_of_mem_X {x : G} (hx : x ∈ 𝔖.X A) (hx1 : x ≠ 1) : x ∉ 𝔖.Y A := by
  intro hy
  have : x ∈ 𝔖.X A ⊓ 𝔖.Y A := ⟨hx, hy⟩
  rw [G4b.X_inf_Y, mem_bot] at this
  exact hx1 this

theorem not_mem_X_of_mem_Y {y : G} (hy : y ∈ 𝔖.Y A) (hy1 : y ≠ 1) : y ∉ 𝔖.X A :=
  fun hx => not_mem_Y_of_mem_X 𝔖 hx hy1 hy

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem normalizer_le_normalizer_O_M :
    normalizer (A : Set G) ≤ normalizer (O (𝔖.M A) : Set G) := fun _ hn =>
  ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image _
    (G4b.normalizer_le_normalizer_M 𝔖 hAS hA hn)

theorem normalizer_le_normalizer_O_N :
    normalizer (A : Set G) ≤ normalizer (O (𝔖.N A) : Set G) := fun _ hn =>
  ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image _
    (G4b.normalizer_le_normalizer_N 𝔖 hAS hA hn)

end Sec4

theorem covers_map_conj {G : Type*} [Group G] {H M₀ OM : Subgroup G} (h : Covers H M₀ OM)
    (g : G) : Covers (H.map (MulAut.conj g).toMonoidHom) (M₀.map (MulAut.conj g).toMonoidHom)
      (OM.map (MulAut.conj g).toMonoidHom) := by
  have h' := map_mono (f := (MulAut.conj g).toMonoidHom) h
  rwa [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj g).injective] at h'

end G5d

end CFSG.GH72
