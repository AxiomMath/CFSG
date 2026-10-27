module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48OrbitOne
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Cases
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48TwoSmall
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Lines

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section ThreeA

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.le_normalizer_RPi (c : Sp48Ctx P M H R X U A L) :
    R ≤ Subgroup.normalizer ((R ⊓ piOf M H L : Subgroup G) : Set G) := fun _ hr =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hr,
    (c.h3.mem_Pi' c.hB3 c.block).1 (c.h3.le_inf hr)⟩

theorem Sp48Ctx.false_of_line (c : Sp48Ctx P M H R X U A L)
    (hA : (R ⊓ piOf M H L : Subgroup G) = A) {S : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hS : S ≤ barM M A) (hS3 : Nat.card S = 3) (hSX : ¬ S ≤ barM M X)
    (T : Fin 3 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hT : ∀ j, T j ≤ barM M A)
    (hperm : ∀ (u : G) (huM : u ∈ M), u ∈ U → ∃ j,
      S.map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, huM⟩)).toMonoidHom = T j) :
    False := by
  have h3 := c.h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := c.data.A_le.trans h3.le_M
  have hA3 : IsPGroup 3 A := h3.isPGroup_R.to_le c.data.A_le
  obtain ⟨x, hxS, hxX⟩ := Set.not_subset.mp hSX
  obtain ⟨⟨a, haM⟩, ha, rfl⟩ := hS hxS
  have haA : a ∈ A := Subgroup.mem_subgroupOf.mp ha
  have haX : a ∉ X := fun h => hxX (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h))
  set x := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, haM⟩ with hx
  have hx1 : x ≠ 1 := fun h => hxX (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := by
    have := Subgroup.orderOf_dvd_natCard S hxS
    rw [hS3] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hSz : S = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxS)
      (by rw [hS3, Nat.card_zpowers, orderOf_eq_prime hx3 hx1])).symm
  set W : Fin 3 → Subgroup G := fun j => A ⊓ preM M (T j) with hW
  obtain ⟨u, huU, hu⟩ := c.data.orbit_nine a haA haX W
  have huR : u ∈ R := c.data.U_le huU
  have huM : u ∈ M := h3.le_M huR
  obtain ⟨j, hj⟩ := hperm u huM huU
  apply hu j
  have huN : u ∈ Subgroup.normalizer (A : Set G) := hA ▸ c.le_normalizer_RPi huR
  have hZA : (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≤ A := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp huN]
    exact Subgroup.map_mono (Subgroup.zpowers_le.mpr haA)
  have hbarZ : barM M ((Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom) = T j := by
    rw [barM_map_conj huM, barM_zpowers haM, ← hx, ← hSz, hj]
  have hbarW : barM M (W j) = T j := barM_inf_preM (hT j)
  have hWA : W j ≤ A := inf_le_left
  exact le_antisymm
    (le_of_barM_le_of_isPGroup Nat.prime_three (by norm_num) hAM hA3 hZA hWA
      (hbarZ.trans hbarW.symm).le)
    (le_of_barM_le_of_isPGroup Nat.prime_three (by norm_num) hAM hA3 hWA hZA
      (hbarW.trans hbarZ.symm).le)

theorem Sp48Ctx.eq_A (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ H ⊓ M) (hk₂ : k₂ ∈ H ⊓ M) (h01 : blkOf M L 1 ≠ blkOf M L k₁)
    (h02 : blkOf M L 1 ≠ blkOf M L k₂) (h12 : blkOf M L k₁ ≠ blkOf M L k₂) :
    (R ⊓ piOf M H L : Subgroup G) = A := by
  have h27 := c.cube_dvd SL hk₁ hk₂ h01 h02 h12
  rw [hs] at h27
  have hnU := c.not_U_le SL hs
  rcases (c.data.Pi_cases c.hB3 c.block).2 with h1 | h1 | h1 | h1
  · have h1' : (R ⊓ piOf M H L : Subgroup G) = X := h1
    rw [h1', c.data.card_X] at h27
    norm_num at h27
  · exact h1
  · exact absurd (le_of_eq (h1 : (R ⊓ piOf M H L : Subgroup G) = U).symm) hnU
  · exfalso
    apply hnU
    have h1' : (R ⊓ piOf M H L : Subgroup G) = R := h1
    rw [h1']
    exact c.data.U_le

end ThreeA

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section ThreeSmall

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X U A L : Subgroup G}

theorem Sp48Ctx.false_of_three_small (c : Sp48Ctx P M H R X U A L)
    (SL : Sylow 3 (blockParabolic M (pCoreOf 2 H) L))
    (hs : Nat.card (SL : Subgroup (blockParabolic M (pCoreOf 2 H) L)) = 3) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ H ⊓ M) (hk₂ : k₂ ∈ H ⊓ M) (h01 : blkOf M L 1 ≠ blkOf M L k₁)
    (h02 : blkOf M L 1 ≠ blkOf M L k₂) (h12 : blkOf M L k₁ ≠ blkOf M L k₂)
    (h3' : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁ ∨
      blkOf M L k = blkOf M L k₂) : False := by
  have h3 := c.h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := c.eq_A SL hs hk₁ hk₂ h01 h02 h12
  rw [blkOf_one] at h01 h02
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set B₀ := barM M L with hB₀
  set B₁ := blkOf M L k₁ with hB₁
  set B₂ := blkOf M L k₂ with hB₂
  have hAM : A ≤ M := c.data.A_le.trans h3.le_M
  have hA3 : IsPGroup 3 A := h3.isPGroup_R.to_le c.data.A_le
  set Ab := barM M A with hAb
  have hAPi : A ≤ piOf M H L := hA ▸ inf_le_right
  have hAbPi : Ab ≤ barM M (piOf M H L) := Subgroup.map_mono (Subgroup.comap_mono hAPi)
  have hAb3 : IsPGroup 3 Ab := (hA3.comap_subtype (K := M)).map _
  have hAbcard : Nat.card Ab = 27 := by
    rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) hAM hA3, c.data.card_A]
    norm_num
  have hAbel := isElemAbelian_barM (M := M) c.data.elem_A
  have hAbcomm : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x := by
    intro x hx y hy
    have : IsMulCommutative Ab := hAbel.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Ab) ⟨y, hy⟩)
  have hr : ∀ k ∈ H ⊓ M, (Subgroup.centralizer (blkOf M L k : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex
      Ab ≤ 3 := fun k hk => by
    have := c.relIndex_dvd hAbPi hAb3 hk SL
    rw [hs] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hr0 : (Subgroup.centralizer (B₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex Ab ≤ 3 := by
    have := hr 1 (H ⊓ M).one_mem
    rwa [blkOf_one] at this
  have hr1 := hr k₁ hk₁
  have hr2 := hr k₂ hk₂
  have hbot : ∀ q ∈ Ab, q ∈ Subgroup.centralizer (B₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      q ∈ Subgroup.centralizer (B₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      q ∈ Subgroup.centralizer (B₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → q = 1 :=
    fun q hq h0 h1 h2 => c.eq_one (hAbPi hq) (hAb3.to_le (Subgroup.zpowers_le.mpr hq))
      fun k hk => by rcases h3' k hk with e | e | e <;> rw [e] <;> assumption
  have hcardS : ∀ D D' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), D.relIndex Ab ≤ 3 →
      D'.relIndex Ab ≤ 3 → 3 ≤ Nat.card ((D ⊓ D') ⊓ Ab : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro D D' hD hD'
    have hrel : (D ⊓ D').relIndex Ab ≤ 9 :=
      Subgroup.relIndex_inf_le.trans (by nlinarith)
    have hmul := (((D ⊓ D') ⊓ Ab).subgroupOf Ab).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (D ⊓ D') ⊓ Ab ≤ Ab)).toEquiv, hAbcard] at hmul
    have he : (((D ⊓ D') ⊓ Ab).subgroupOf Ab).index = (D ⊓ D').relIndex Ab :=
      Subgroup.inf_relIndex_right (D ⊓ D') Ab
    rw [he] at hmul
    by_contra hlt
    have := Nat.mul_le_mul (show Nat.card ((D ⊓ D') ⊓ Ab : Subgroup _) ≤ 2 by omega) hrel
    omega
  set S₀ := lineOf Ab B₁ B₂ with hS₀
  set S₁ := lineOf Ab B₀ B₂ with hS₁
  set S₂ := lineOf Ab B₀ B₁ with hS₂
  have hS01 : S₀ ⊓ S₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro q ⟨⟨⟨hq1, hq2⟩, hqA⟩, ⟨⟨hq0, -⟩, -⟩⟩
    exact Subgroup.mem_bot.mpr (hbot q hqA hq0 hq1 hq2)
  have hc01 := card_sup_of_commute (A := S₀) (B := S₁)
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hAbcomm y hy.2 x hx.2) hS01
  have hS012 : (S₀ ⊔ S₁) ⊓ S₂ = ⊥ := by
    have hle : S₀ ⊔ S₁ ≤ Subgroup.centralizer (B₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓ Ab :=
      sup_le (le_inf (fun q hq => hq.1.2) inf_le_right) (le_inf (fun q hq => hq.1.2) inf_le_right)
    rw [eq_bot_iff]
    rintro q ⟨hq01, ⟨⟨hq0, hq1⟩, -⟩⟩
    obtain ⟨hq2, hqA⟩ := hle hq01
    exact Subgroup.mem_bot.mpr (hbot q hqA hq0 hq1 hq2)
  have hc012 := card_sup_of_commute (A := S₀ ⊔ S₁) (B := S₂)
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hAbcomm y hy.2 x
      ((sup_le (inf_le_right : S₀ ≤ Ab) (inf_le_right : S₁ ≤ Ab)) hx)) hS012
  have hle27 : Nat.card (S₀ ⊔ S₁ ⊔ S₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ 27 :=
    hAbcard ▸ Subgroup.card_le_of_le (sup_le (sup_le inf_le_right inf_le_right) inf_le_right)
  rw [hc012, hc01] at hle27
  have hS0c : 3 ≤ Nat.card S₀ := hcardS _ _ hr1 hr2
  have hS1c : 3 ≤ Nat.card S₁ := hcardS _ _ hr0 hr2
  have hS2c : 3 ≤ Nat.card S₂ := hcardS _ _ hr0 hr1
  have e0 : Nat.card S₀ = 3 := by nlinarith
  have e1 : Nat.card S₁ = 3 := by nlinarith
  have e2 : Nat.card S₂ = 3 := by nlinarith
  have hXM : X ≤ M := c.data.surv.le_R.trans h3.le_M
  have hXb : Nat.card (barM M X) = 9 := by
    rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) hXM
      (h3.isPGroup_R.to_le c.data.surv.le_R), c.data.card_X]
    norm_num
  have hperm : ∀ S : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), (S = S₀ ∨ S = S₁ ∨ S = S₂) →
      ∀ (u : G) (huM : u ∈ M), u ∈ U → ∃ j : Fin 3,
        S.map (MulAut.conj (mk ⟨u, huM⟩)).toMonoidHom = ![S₀, S₁, S₂] j := by
    intro S hS u huM huU
    have huR : u ∈ R := c.data.U_le huU
    have huK : u ∈ H ⊓ M := h3.le_inf huR
    set g := mk ⟨u, huM⟩ with hg
    have huN : u ∈ Subgroup.normalizer (A : Set G) := hA ▸ c.le_normalizer_RPi huR
    have hAu : A.map (MulAut.conj u).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp huN
    have hAbg : Ab.map (MulAut.conj g).toMonoidHom = Ab := by
      rw [hAb, ← barM_map_conj huM, hAu]
    have hBg : ∀ k ∈ H ⊓ M, (blkOf M L k).map (MulAut.conj g).toMonoidHom = blkOf M L (u * k) :=
      fun k _ => (blkOf_mul M L huM k).symm
    have hB0g : B₀.map (MulAut.conj g).toMonoidHom = blkOf M L u := by
      rw [hB₀, ← blkOf_one, hBg 1 (H ⊓ M).one_mem, mul_one]
    have hinj : ∀ Y Z : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Y ≠ Z →
        Y.map (MulAut.conj g).toMonoidHom ≠ Z.map (MulAut.conj g).toMonoidHom :=
      fun Y Z h e => h (Subgroup.map_injective (MulAut.conj g).injective e)
    have hm0 := hB0g ▸ h3' u huK
    have hm1 := (hBg k₁ hk₁) ▸ h3' (u * k₁) ((H ⊓ M).mul_mem huK hk₁)
    have hm2 := (hBg k₂ hk₂) ▸ h3' (u * k₂) ((H ⊓ M).mul_mem huK hk₂)
    rcases hS with rfl | rfl | rfl
    · rw [lineOf_map_conj, hAbg]
      rcases lineOf_cases Ab B₀ B₁ B₂ hm1 hm2 (hinj _ _ h12) with h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
    · rw [lineOf_map_conj, hAbg]
      rcases lineOf_cases Ab B₀ B₁ B₂ hm0 hm2 (hinj _ _ h02) with h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
    · rw [lineOf_map_conj, hAbg]
      rcases lineOf_cases Ab B₀ B₁ B₂ hm0 hm1 (hinj _ _ h01) with h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hT : ∀ j, (![S₀, S₁, S₂] : Fin 3 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) j ≤ Ab := by
    intro j
    fin_cases j <;> exact inf_le_right
  by_cases hX0 : S₀ ≤ barM M X
  · by_cases hX1 : S₁ ≤ barM M X
    · by_cases hX2 : S₂ ≤ barM M X
      · have := Subgroup.card_le_of_le (sup_le (sup_le hX0 hX1) hX2)
        rw [hc012, hc01, e0, e1, e2, hXb] at this
        norm_num at this
      · exact c.false_of_line hA inf_le_right e2 hX2 _ hT (hperm S₂ (Or.inr (Or.inr rfl)))
    · exact c.false_of_line hA inf_le_right e1 hX1 _ hT (hperm S₁ (Or.inr (Or.inl rfl)))
  · exact c.false_of_line hA inf_le_right e0 hX0 _ hT (hperm S₀ (Or.inl rfl))

end ThreeSmall

end CFSG.AGLEmbedding
