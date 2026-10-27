module

public import CFSG.LieType.Chevalley.E6EvenRootTorusCentralizer
public import CFSG.LieType.Chevalley.SignKernelComponentBorel

public noncomputable section

namespace CFSG.LieType.Chevalley.E6EvenRootTorus

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.Chevalley.E6GraphRootSL2
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section SL2

variable {F : Type} [Field F]

theorem mul_apply_two (A B : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_mul_SL2 (A B : SL2 F) :
    ((A * B : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem entries_of_mul_self (h2 : (2 : F) = 0) {Y : SL2 F} (hY : Y * Y = 1) :
    (Y : Matrix (Fin 2) (Fin 2) F) 1 1 = (Y : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (Y : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 +
        (Y : Matrix (Fin 2) (Fin 2) F) 0 1 * (Y : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have hM : (Y : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) = 1 :=
    congrArg Subtype.val hY
  have e00 := congrFun (congrFun hM 0) 0
  have e11 := congrFun (congrFun hM 1) 1
  rw [mul_apply_two, one_apply_eq] at e00 e11
  have hdet := det_entries Y
  set a := (Y : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (Y : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (Y : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (Y : Matrix (Fin 2) (Fin 2) F) 1 1
  have hsq : (d - a) ^ 2 = 0 := by linear_combination e00 + e11 - 2 * hdet - 2 * b * c * h2
  refine ⟨sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq), ?_⟩
  linear_combination e00

theorem HSL_inv (t : Fˣ) : (HSL t)⁻¹ = HSL t⁻¹ := by
  refine E6GraphRootSL2.SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [coe_HSL, adjugate_fin_two]

theorem entries_conj_HSL (t : Fˣ) (Y : SL2 F) :
    ((HSL t * Y * (HSL t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (Y : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      ((HSL t * Y * (HSL t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        (t : F) ^ 2 * (Y : Matrix (Fin 2) (Fin 2) F) 0 1 ∧
      ((HSL t * Y * (HSL t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
        ((t⁻¹ : Fˣ) : F) ^ 2 * (Y : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
      ((HSL t * Y * (HSL t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        (Y : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  have ht : (t : F) * ((t⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [HSL_inv, coe_mul_SL2, coe_mul_SL2, coe_HSL, coe_HSL]
  simp only [mul_apply_two, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, zero_mul, mul_zero, add_zero, zero_add, inv_inv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (Y : Matrix (Fin 2) (Fin 2) F) 0 0 * ht
  · ring
  · ring
  · linear_combination (Y : Matrix (Fin 2) (Fin 2) F) 1 1 * ht

theorem le_or_le_of_normalized_SL2 (h2 : (2 : F) = 0) {t : Fˣ} (ht : t ≠ 1)
    {S : Subgroup (SL2 F)} (hS2 : ∀ Y ∈ S, Y * Y = 1)
    (hSH : ∀ Y ∈ S, HSL t * Y * (HSL t)⁻¹ ∈ S) :
    (∀ Y ∈ S, ∃ s, Y = uSL s) ∨ (∀ Y ∈ S, ∃ s, Y = vSL s) := by
  have htF : (t : F) * ((t⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have htri : ∀ Y ∈ S, (Y : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∨
      (Y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro Y hY
    by_contra hcon
    rw [not_or] at hcon
    have hYZ := hS2 _ (mul_mem hY (hSH Y hY))
    obtain ⟨hd, -⟩ := entries_of_mul_self h2 (hS2 Y hY)
    obtain ⟨hd', -⟩ := entries_of_mul_self h2 hYZ
    obtain ⟨z00, z01, z10, z11⟩ := entries_conj_HSL t Y
    rw [coe_mul_SL2, mul_apply_two, mul_apply_two, z00, z01, z10, z11, hd] at hd'
    have hbc : (Y : Matrix (Fin 2) (Fin 2) F) 0 1 * (Y : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 :=
      mul_ne_zero hcon.1 hcon.2
    have h4 : ((t : F) ^ 2 - ((t⁻¹ : Fˣ) : F) ^ 2) *
        ((Y : Matrix (Fin 2) (Fin 2) F) 0 1 * (Y : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 := by
      linear_combination hd'
    have h5 := (mul_eq_zero.1 h4).resolve_right hbc
    have h7 : (t : F) ^ 4 = 1 := by
      linear_combination (t : F) ^ 2 * h5 + (((t⁻¹ : Fˣ) : F) * (t : F) + 1) * htF
    have h6 : ((t : F) - 1) ^ 4 = 0 := by
      linear_combination h7 + (-(2 : F) * (t : F) ^ 3 + 3 * (t : F) ^ 2 - 2 * (t : F) + 1) * h2
    apply ht
    exact Units.ext (by
      simpa [sub_eq_zero] using pow_eq_zero_iff (n := 4) (by norm_num) |>.1 h6)
  have hdiag : ∀ Y ∈ S,
      (Y : Matrix (Fin 2) (Fin 2) F) 0 1 * (Y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
        (Y : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (Y : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    intro Y hY h0
    obtain ⟨hd, hsq⟩ := entries_of_mul_self h2 (hS2 Y hY)
    rw [h0, add_zero] at hsq
    have ha : (Y : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      have : ((Y : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 = 0 := by
        linear_combination hsq + (1 - (Y : Matrix (Fin 2) (Fin 2) F) 0 0) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    exact ⟨ha, hd.trans ha⟩
  have hu : ∀ Y ∈ S, (Y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      Y = uSL ((Y : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    intro Y hY h10
    obtain ⟨ha, hd⟩ := hdiag Y hY (by rw [h10, mul_zero])
    refine E6GraphRootSL2.SL2_ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_uSL, ha, hd, h10]
  have hv : ∀ Y ∈ S, (Y : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 →
      Y = vSL ((Y : Matrix (Fin 2) (Fin 2) F) 1 0) := by
    intro Y hY h01
    obtain ⟨ha, hd⟩ := hdiag Y hY (by rw [h01, zero_mul])
    refine E6GraphRootSL2.SL2_ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [coe_vSL, ha, hd, h01]
  by_cases hex : ∃ Y ∈ S, (Y : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0
  · left
    obtain ⟨Y₁, hY₁, hb⟩ := hex
    have hc₁ := (htri Y₁ hY₁).resolve_left hb
    intro Y hY
    refine ⟨_, hu Y hY ?_⟩
    by_contra hc
    have hc' := (htri Y hY).resolve_right hc
    have e₁ := hu Y₁ hY₁ hc₁
    have e := hv Y hY hc'
    have h01 : ((Y₁ * Y : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        (Y₁ : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      rw [coe_mul_SL2, mul_apply_two]
      conv_lhs => rw [e₁, e]
      simp [coe_uSL, coe_vSL]
    have h10 : ((Y₁ * Y : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
        (Y : Matrix (Fin 2) (Fin 2) F) 1 0 := by
      rw [coe_mul_SL2, mul_apply_two]
      conv_lhs => rw [e₁, e]
      simp [coe_uSL, coe_vSL]
    rcases htri _ (mul_mem hY₁ hY) with h | h
    · rw [h01] at h
      exact hb h
    · rw [h10] at h
      exact hc h
  · right
    push Not at hex
    exact fun Y hY => ⟨_, hv Y hY (hex Y hY)⟩

theorem WSL_mul_HSL_mul_inv (t : Fˣ) : WSL * HSL t * WSL⁻¹ = HSL t⁻¹ := by
  refine E6GraphRootSL2.SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [coe_WSL, coe_HSL, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

variable {K : Type} [Field K]

theorem pinnedX_mul_self
    (h2 : (2 : K) = 0) (β : Fin TwistTag.E6.tag.rank → ℤ) (c : K) :
    pinnedX TwistTag.E6.tag K β c * pinnedX TwistTag.E6.tag K β c = 1 := by
  rw [← pinnedX_add, ← two_mul, h2, zero_mul, pinnedX_zero]

theorem le_or_le_of_normalized
    (h2 : (2 : K) = 0) {t : Kˣ} (ht : t ≠ 1)
    {S : Subgroup (ModGL TwistTag.E6.tag K)} (hSX : S ≤ thetaRankOneGroup (RingHom.id K))
    (hS2 : ∀ s ∈ S, s * s = 1)
    (hSH : ∀ s ∈ S, thetaTorusHom K t * s * (thetaTorusHom K t)⁻¹ ∈ S) :
    S ≤ rootSubgroup TwistTag.E6.tag K e6HighestRoot ∨
      S ≤ rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) := by
  have hinj := thetaSL2_injective (E := K) h2
  have hX : ∀ s ∈ S, ∃ Y : SL2 K, thetaSL2 K Y = s := fun s hs => by
    have h := hSX hs
    rw [thetaRankOneGroup_eq_range h2] at h
    obtain ⟨Y, hY⟩ := h
    exact ⟨SpecialLinearGroup.map (RingHom.id K) Y, hY⟩
  have key := le_or_le_of_normalized_SL2 (S := S.comap (thetaSL2 K)) h2 ht
    (fun Y hY => hinj (by rw [map_mul, map_one]; exact hS2 _ hY))
    (fun Y hY => by
      rw [mem_comap, map_mul, map_mul, map_inv, ← thetaTorusHom_eq_thetaSL2]
      exact hSH _ hY)
  rcases key with h | h
  · left
    intro s hs
    obtain ⟨Y, rfl⟩ := hX s hs
    obtain ⟨b, rfl⟩ := h Y hs
    rw [thetaSL2_uSL h2]
    exact mem_rootSubgroup.2 ⟨b, rfl⟩
  · right
    intro s hs
    obtain ⟨Y, rfl⟩ := hX s hs
    obtain ⟨c, rfl⟩ := h Y hs
    rw [thetaSL2_vSL h2]
    exact mem_rootSubgroup.2 ⟨c, rfl⟩

section Generic

theorem eq_bot_of_isPGroup_two {L : Type*} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hodd : Odd (Nat.card (center L))) {M : Subgroup L}
    (hM : M.Normal) (h2 : IsPGroup 2 M) : M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf, hsimple⟩ := hq
  have hπ : Function.Surjective (QuotientGroup.mk' (center L)) := QuotientGroup.mk'_surjective _
  have := hM.map (QuotientGroup.mk' (center L)) hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (center L))) with
    h | h
  · have hMZ : M ≤ center L := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    have hdvd := Subgroup.card_dvd_of_le hMZ
    rw [hn] at hdvd
    rcases n with _ | n
    · exact Subgroup.eq_bot_of_card_eq M (by rw [hn, pow_zero])
    · exact absurd (Odd.of_dvd_nat hodd hdvd)
        (by rw [pow_succ]; exact Nat.not_odd_iff_even.2 (even_two.mul_left _))
  ·
    exfalso
    have hP : IsPGroup 2 (L ⧸ center L) := by
      have h3 := h2.map (QuotientGroup.mk' (center L))
      rw [h] at h3
      exact h3.of_equiv Subgroup.topEquiv
    have : Group.IsPerfect L := ⟨hperf⟩
    exact Group.IsPerfect.not_isNilpotent (L ⧸ center L) hP.isNilpotent

theorem eq_one_of_pow_two_pow_eq_one {M : Type*} [Group M] {H : Subgroup M}
    (hH : Odd (Nat.card H)) {h : M} (hh : h ∈ H) {n : ℕ} (hn : h ^ 2 ^ n = 1) : h = 1 := by
  have h1 : orderOf (⟨h, hh⟩ : H) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hn))
  have h3 : orderOf (⟨h, hh⟩ : H) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    rcases j with _ | j
    · simpa using hj
    · have h2 := orderOf_dvd_natCard (⟨h, hh⟩ : H)
      rw [hj] at h2
      exact absurd (Odd.of_dvd_nat hH h2)
        (by rw [pow_succ]; exact Nat.not_odd_iff_even.2 (even_two.mul_left _))
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

variable {C : Type*} [Group C] [Finite C]

theorem map_eq_of_le (β : MulAut C) {S : Subgroup C} (hS : ∀ x ∈ S, β x ∈ S) :
    S.map β.toMonoidHom = S :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 fun x hx => hS x hx)
    (Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective).ge

theorem symm_mem (β : MulAut C) {S : Subgroup C} (hS : ∀ x ∈ S, β x ∈ S) {y : C} (hy : y ∈ S) :
    β.symm y ∈ S := by
  rw [← map_eq_of_le β hS] at hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
  simpa using hz

theorem map_mem_normalizer (β : MulAut C) {S : Subgroup C} (hS : ∀ x ∈ S, β x ∈ S) {y : C}
    (hy : y ∈ normalizer (S : Set C)) : β y ∈ normalizer (S : Set C) := by
  rw [← map_eq_of_le β hS, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.mem_map_of_mem _ hy

end Generic

theorem map_mem_of_factor {M : Type*} [Group M] {G N Q L H : Subgroup M} (hNG : N ≤ G)
    (hNsup : Q ⊔ (L ⊔ H) = N) (hQn : N ≤ normalizer (Q : Set M))
    (huniq : ∀ g ∈ N, ∃! t : M × M × M,
      t.1 ∈ Q ∧ t.2.1 ∈ L ∧ t.2.2 ∈ H ∧ g = t.1 * (t.2.1 * t.2.2))
    (hLH : ∀ l ∈ L, ∀ h ∈ H, l * h = h * l) (hQ2 : IsPGroup 2 Q) (hH : Odd (Nat.card H))
    (hL : ∀ S : Subgroup M, S ≤ L → IsPGroup 2 S → L ≤ normalizer (S : Set M) → S = ⊥)
    (β : MulAut G) (hβ : ∀ y : G, (y : M) ∈ N → (β y : M) ∈ N)
    (hβ' : ∀ y : G, (y : M) ∈ N → (β.symm y : M) ∈ N) {x : G} (hx : (x : M) ∈ Q) :
    (β x : M) ∈ Q := by
  have hQN : Q ≤ N := le_sup_left.trans hNsup.le
  have hLN : L ≤ N := (le_sup_left.trans le_sup_right).trans hNsup.le
  obtain ⟨𝒬, h𝒬⟩ : ∃ 𝒬 : Subgroup M, 𝒬 = (Q.subgroupOf G).map (G.subtype.comp β.toMonoidHom) :=
    ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ 𝒬 ↔ ∃ y : G, (y : M) ∈ Q ∧ (β y : M) = z := fun z => by
    rw [h𝒬]
    exact Iff.rfl
  have h𝒬N : 𝒬 ≤ N := fun z hz => by
    obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
    exact hβ y (hQN hy)
  have h𝒬2 : IsPGroup 2 𝒬 := h𝒬 ▸ (hQ2.comap_subtype (K := G)).map _
  have hN𝒬 : N ≤ normalizer (𝒬 : Set M) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer h𝒬N).1 ?_
    refine (Subgroup.normal_subgroupOf_iff h𝒬N).2 fun z n hz hn => ?_
    obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
    have hm : ((β.symm ⟨n, hNG hn⟩ : G) : M) ∈ N := hβ' ⟨n, hNG hn⟩ hn
    refine (hmem _).2 ⟨β.symm ⟨n, hNG hn⟩ * y * (β.symm ⟨n, hNG hn⟩)⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mem_normalizer_iff.1 (hQn hm) y).1 hy
    · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv]
  have h𝒮2 : IsPGroup 2 (𝒬 ⊔ Q : Subgroup M) :=
    IsPGroup.to_sup_of_normal_right' h𝒬2 hQ2 (h𝒬N.trans hQn)
  have hN𝒮 : N ≤ normalizer ((𝒬 ⊔ Q : Subgroup M) : Set M) :=
    (le_inf hN𝒬 hQn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hLH1 : ∀ t ∈ L, t ∈ H → t = 1 := by
    intro t htL htH
    have e := (huniq t (hLN htL)).unique (y₁ := (1, t, 1)) (y₂ := (1, 1, t))
      ⟨one_mem _, htL, one_mem _, by rw [mul_one, one_mul]⟩
      ⟨one_mem _, one_mem _, htH, by rw [one_mul, one_mul]⟩
    exact congrArg (fun p : M × M × M => p.2.1) e
  have hβx : (β x : M) ∈ 𝒬 := (hmem _).2 ⟨x, hx, rfl⟩
  obtain ⟨⟨q, l, h⟩, ⟨hq, hl, hh, he⟩, -⟩ := huniq _ (h𝒬N hβx)
  dsimp only at hq hl hh he
  have hlh : l * h ∈ (𝒬 ⊔ Q : Subgroup M) := by
    have e : l * h = q⁻¹ * (β x : M) := by rw [he]; group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right (inv_mem hq)) (Subgroup.mem_sup_left hβx)
  obtain ⟨n, hn⟩ := h𝒮2 ⟨l * h, hlh⟩
  have hn' : (l * h) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  rw [Commute.mul_pow (hLH l hl h hh)] at hn'
  have hh1 : h = 1 := by
    refine eq_one_of_pow_two_pow_eq_one hH hh (n := n) (hLH1 (h ^ 2 ^ n) ?_ (pow_mem hh _))
    rw [eq_inv_of_mul_eq_one_right hn']
    exact inv_mem (pow_mem hl _)
  subst hh1
  rw [mul_one] at hlh he
  have hbot := hL ((𝒬 ⊔ Q) ⊓ L) inf_le_right (h𝒮2.to_le inf_le_left)
    ((le_inf (hLN.trans hN𝒮) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
  have hl1 : l ∈ ((𝒬 ⊔ Q) ⊓ L : Subgroup M) := Subgroup.mem_inf.2 ⟨hlh, hl⟩
  rw [hbot, Subgroup.mem_bot] at hl1
  rw [he, hl1, mul_one]
  exact hq

variable {k : Type} [Field k]

theorem thetaRootGroup_id :
    thetaRootGroup (RingHom.id k) = rootSubgroup TwistTag.E6.tag k e6HighestRoot := by
  ext g
  rw [mem_thetaRootGroup, mem_rootSubgroup]
  exact Iff.rfl

theorem eq_bot_of_le_subsystemGroup
    [Finite k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (S : Subgroup (ModGL TwistTag.E6.tag k))
    (hSL : S ≤ subsystemGroup TwistTag.E6.tag k setA) (hS2 : IsPGroup 2 S)
    (hSn : subsystemGroup TwistTag.E6.tag k setA ≤
      normalizer (S : Set (ModGL TwistTag.E6.tag k))) :
    S = ⊥ := by
  obtain ⟨-, hq, hodd, -⟩ := subsystemGroup_facts hf hk
  have hLG : subsystemGroup TwistTag.E6.tag k setA ≤ adjointGroup TwistTag.E6.tag k :=
    subsystemGroup_le_adjointGroup
  have hbot := eq_bot_of_isPGroup_two hq hodd
    (M := (S.subgroupOf (adjointGroup TwistTag.E6.tag k)).subgroupOf
      ((subsystemGroup TwistTag.E6.tag k setA).subgroupOf (adjointGroup TwistTag.E6.tag k)))
    ⟨fun n hn g => (mem_normalizer_iff.1 (hSn g.2) _).1 hn⟩
    ((hS2.comap_subtype (K := adjointGroup TwistTag.E6.tag k)).comap_subtype
      (K := (subsystemGroup TwistTag.E6.tag k setA).subgroupOf (adjointGroup TwistTag.E6.tag k)))
  rw [eq_bot_iff]
  intro s hs
  have hsL := hSL hs
  have h := (Subgroup.eq_bot_iff_forall _).1 hbot ⟨⟨s, hLG hsL⟩, hsL⟩ hs
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (congrArg Subtype.val h))

theorem map_mem_parabolicRadical
    [Finite k] [CharP k 2] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (β : MulAut (adjointGroup TwistTag.E6.tag k))
    (hβ : ∀ x : adjointGroup TwistTag.E6.tag k,
      (x : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot →
        (β x : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot)
    {x : adjointGroup TwistTag.E6.tag k}
    (hx : (x : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA) :
    (β x : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA := by
  have h2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  set E := GaloisField 2 (2 * f)
  have hE : Nat.card E = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hE
  let _ : Algebra k E := ι.toAlgebra
  obtain ⟨⟨-, hNsup, hQnorm, huniq, hLH, -⟩, -⟩ :=
    even_E6_graph_highest_root_normalizer f hf k E hk hE (iterateFrobenius E 2 f)
      (fun c => iterateFrobenius_def (p := 2) f c)
  rw [thetaRootGroup_id] at hNsup hQnorm huniq
  have hRG : rootSubgroup TwistTag.E6.tag k e6HighestRoot ≤ adjointGroup TwistTag.E6.tag k :=
    rootSubgroup_le_adjointGroup _
  have hLG : subsystemGroup TwistTag.E6.tag k setA ≤ adjointGroup TwistTag.E6.tag k :=
    subsystemGroup_le_adjointGroup
  have hR : ∀ y ∈ (rootSubgroup TwistTag.E6.tag k e6HighestRoot).subgroupOf
      (adjointGroup TwistTag.E6.tag k), β y ∈ (rootSubgroup TwistTag.E6.tag k
        e6HighestRoot).subgroupOf (adjointGroup TwistTag.E6.tag k) := fun y hy => hβ y hy
  have hN : ∀ γ : MulAut (adjointGroup TwistTag.E6.tag k),
      (∀ y ∈ (rootSubgroup TwistTag.E6.tag k e6HighestRoot).subgroupOf
        (adjointGroup TwistTag.E6.tag k), γ y ∈ (rootSubgroup TwistTag.E6.tag k
          e6HighestRoot).subgroupOf (adjointGroup TwistTag.E6.tag k)) →
      ∀ y : adjointGroup TwistTag.E6.tag k, (y : ModGL TwistTag.E6.tag k) ∈
        normalizer (rootSubgroup TwistTag.E6.tag k e6HighestRoot :
          Set (ModGL TwistTag.E6.tag k)) ⊓ adjointGroup TwistTag.E6.tag k →
      (γ y : ModGL TwistTag.E6.tag k) ∈
        normalizer (rootSubgroup TwistTag.E6.tag k e6HighestRoot :
          Set (ModGL TwistTag.E6.tag k)) ⊓ adjointGroup TwistTag.E6.tag k := by
    intro γ hγ y hy
    refine mem_inf.2 ⟨?_, (γ y).2⟩
    have hy' : y ∈ normalizer (((rootSubgroup TwistTag.E6.tag k e6HighestRoot).subgroupOf
        (adjointGroup TwistTag.E6.tag k) : Subgroup (adjointGroup TwistTag.E6.tag k)) :
          Set (adjointGroup TwistTag.E6.tag k)) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hRG]
      exact (mem_inf.1 hy).1
    have h := map_mem_normalizer γ hγ hy'
    rw [← Subgroup.subgroupOf_normalizer_eq hRG] at h
    exact h
  have hQ2 : IsPGroup 2 (parabolicRadical TwistTag.E6.tag k setA ⊓
      adjointGroup TwistTag.E6.tag k : Subgroup (ModGL TwistTag.E6.tag k)) :=
    (isPGroup_posUnipotent (K := k) 2 TwistTag.E6.tag).to_le
      (inf_le_left.trans (parabolicRadical_le_posUnipotent setA))
  have hH : Odd (Nat.card (thetaTorus (RingHom.id k))) := by
    rw [card_thetaTorus h2, Nat.card_units, hk]
    exact odd_two_pow_sub_one hf
  have hQN : parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ≤
      normalizer (rootSubgroup TwistTag.E6.tag k e6HighestRoot :
        Set (ModGL TwistTag.E6.tag k)) ⊓ adjointGroup TwistTag.E6.tag k :=
    le_sup_left.trans hNsup.le
  have h := map_mem_of_factor inf_le_right hNsup
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQN).1 hQnorm) huniq hLH hQ2 hH
    (fun S hSL hS2 hSn => eq_bot_of_le_subsystemGroup hf hk S (hSL.trans inf_le_left) hS2
      ((le_inf le_rfl hLG).trans hSn))
    β (hN β hR) (hN β.symm fun y hy => symm_mem β hR hy) (x := x) (mem_inf.2 ⟨hx, x.2⟩)
  exact (mem_inf.1 h).1

theorem sTheta_inv : sTheta⁻¹ = sTheta := by
  show (wTheta * simple TwistTag.E6.tag (e6Idx 0) * wTheta⁻¹)⁻¹ =
    wTheta * simple TwistTag.E6.tag (e6Idx 0) * wTheta⁻¹
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, simple_inv, mul_assoc]

theorem sTheta_smul_theta :
    sTheta • e6HighestRoot = -e6HighestRoot := by
  rw [sTheta_smul]
  decide +kernel

theorem sTheta_root_check :
    ∀ n < TwistTag.E6.tag.rootCertificate.roots.length,
    TwistTag.E6.tag.rootCertificate.root n (e6Idx 1) ≠ 0 →
      (height (TwistTag.E6.tag.rootCertificate.root n) < 0 →
        0 < height (sTheta • TwistTag.E6.tag.rootCertificate.root n) ∧
          (sTheta • TwistTag.E6.tag.rootCertificate.root n) (e6Idx 1) ≠ 0) ∧
      (0 < height (TwistTag.E6.tag.rootCertificate.root n) →
        height (sTheta • TwistTag.E6.tag.rootCertificate.root n) < 0) := by
  simp only [sTheta_smul]
  decide +kernel

theorem sTheta_smul_of_isRoot
    {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (h1 : γ (e6Idx 1) ≠ 0) :
    (height γ < 0 → 0 < height (sTheta • γ) ∧ (sTheta • γ) (e6Idx 1) ≠ 0) ∧
      (0 < height γ → height (sTheta • γ) < 0) := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  exact sTheta_root_check n hn h1

theorem mem_parabolicRoots_of {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (h0 : γ (e6Idx 1) = 0) :
    γ ∈ parabolicRoots TwistTag.E6.tag setA := by
  refine ⟨hγ, fun i hi => ?_⟩
  have : i = e6Idx 1 := by
    by_contra hne
    exact hi hne
  rw [this]
  exact h0

theorem mem_parabolicRadicalRoots_of {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ) (h1 : γ (e6Idx 1) ≠ 0) :
    γ ∈ parabolicRadicalRoots TwistTag.E6.tag setA :=
  ⟨⟨hγ, hpos⟩, fun h => h1 (h.1.2 (e6Idx 1) fun h' => h' rfl)⟩

theorem ne_zero_of_mem_parabolicRadicalRoots {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : δ ∈ parabolicRadicalRoots TwistTag.E6.tag setA) : δ (e6Idx 1) ≠ 0 := fun h0 =>
  hδ.2 ⟨mem_parabolicRoots_of hδ.1.1 h0, hδ.1⟩

theorem conj_mem_rootSubgroup
    {g : ModGL TwistTag.E6.tag k}
    (hg : g ∈ monomialSubgroup TwistTag.E6.tag k) {w : WeylGroup TwistTag.E6.tag}
    (hgw : MapsRootLines g w) {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    {x : ModGL TwistTag.E6.tag k} (hx : x ∈ rootSubgroup TwistTag.E6.tag k γ) :
    g * x * g⁻¹ ∈ rootSubgroup TwistTag.E6.tag k (w • γ) := by
  have h := conj_mem_rootSpan_of_mapsRootLines hg hgw (S := {γ})
    (fun α hα => by rw [Set.mem_singleton_iff.1 hα]; exact hγ) (by rwa [rootSpan_singleton])
  rwa [Set.image_singleton, rootSpan_singleton] at h

theorem map_mem_rootSpan_of_forall
    {τ : Tag} (α : MulAut (adjointGroup τ k))
    {S : Set (Fin τ.rank → ℤ)} {T : Subgroup (ModGL τ k)}
    (h : ∀ γ ∈ S, ∀ y : adjointGroup τ k, (y : ModGL τ k) ∈ rootSubgroup τ k γ →
      (α y : ModGL τ k) ∈ T)
    {y : adjointGroup τ k} (hy : (y : ModGL τ k) ∈ rootSpan τ k S) : (α y : ModGL τ k) ∈ T := by
  have hle : rootSpan τ k S ≤ ((T.subgroupOf (adjointGroup τ k)).comap α.toMonoidHom).map
      (adjointGroup τ k).subtype := iSup₂_le fun γ hγ g hg =>
    ⟨⟨g, rootSubgroup_le_adjointGroup γ hg⟩, h γ hγ _ hg, rfl⟩
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hle hy)
  obtain rfl : z = y := Subtype.ext hzy
  exact hz

theorem nTheta_mem_adjointGroup
    (h2 : (2 : k) = 0) :
    E6GraphLevi.thetaSL2 k WSL ∈ adjointGroup TwistTag.E6.tag k :=
  E6GraphRadical.thetaRankOneGroup_le_adjointGroup (RingHom.id k)
    (nTheta_mem_thetaRankOneGroup h2)

theorem map_mem_posUnipotent
    (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hL : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ subsystemGroup TwistTag.E6.tag k setA → α y = y)
    (hQ : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA →
        (α y : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA)
    {y : adjointGroup TwistTag.E6.tag k}
    (hy : (y : ModGL TwistTag.E6.tag k) ∈ posUnipotent TwistTag.E6.tag k) :
    (α y : ModGL TwistTag.E6.tag k) ∈ posUnipotent TwistTag.E6.tag k := by
  refine map_mem_rootSpan_of_forall α (fun γ hγ z hz => ?_) hy
  by_cases h1 : γ (e6Idx 1) = 0
  · rw [hL z (rootSubgroup_le_subsystemGroup (mem_parabolicRoots_of hγ.1 h1) hz)]
    exact (le_iSup₂_of_le γ hγ le_rfl :
      rootSubgroup TwistTag.E6.tag k γ ≤ posUnipotent TwistTag.E6.tag k) hz
  · exact parabolicRadical_le_posUnipotent setA (hQ z ((le_iSup₂_of_le γ
      (mem_parabolicRadicalRoots_of hγ.1 hγ.2 h1) le_rfl : rootSubgroup TwistTag.E6.tag k γ ≤
        parabolicRadical TwistTag.E6.tag k setA) hz))

theorem map_mem_negUnipotent
    (h2 : (2 : k) = 0) (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hL : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ subsystemGroup TwistTag.E6.tag k setA → α y = y)
    (hQ : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA →
        (((⟨_, nTheta_mem_adjointGroup h2⟩ : adjointGroup TwistTag.E6.tag k)⁻¹ *
          α (⟨_, nTheta_mem_adjointGroup h2⟩ * y *
            (⟨_, nTheta_mem_adjointGroup h2⟩ : adjointGroup TwistTag.E6.tag k)⁻¹) *
          ⟨_, nTheta_mem_adjointGroup h2⟩ : adjointGroup TwistTag.E6.tag k) :
            ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA)
    {y : adjointGroup TwistTag.E6.tag k}
    (hy : (y : ModGL TwistTag.E6.tag k) ∈ negUnipotent TwistTag.E6.tag k) :
    (α y : ModGL TwistTag.E6.tag k) ∈ negUnipotent TwistTag.E6.tag k := by
  set n : adjointGroup TwistTag.E6.tag k := ⟨_, nTheta_mem_adjointGroup h2⟩ with hn
  have hnmon := nTheta_mem_monomialSubgroup (K := k) h2
  have hnmaps := mapsRootLines_nTheta (K := k) h2
  refine map_mem_rootSpan_of_forall α (fun γ hγ z hz => ?_) hy
  by_cases h1 : γ (e6Idx 1) = 0
  · rw [hL z (rootSubgroup_le_subsystemGroup (mem_parabolicRoots_of hγ.1 h1) hz)]
    exact (le_iSup₂_of_le γ hγ le_rfl :
      rootSubgroup TwistTag.E6.tag k γ ≤ negUnipotent TwistTag.E6.tag k) hz
  · obtain ⟨hδpos, hδ1⟩ := (sTheta_smul_of_isRoot hγ.1 h1).1 hγ.2
    have hw : ((n⁻¹ * z * n : adjointGroup TwistTag.E6.tag k) : ModGL TwistTag.E6.tag k) ∈
        parabolicRadical TwistTag.E6.tag k setA := by
      have h3 := conj_mem_rootSubgroup (inv_mem hnmon) hnmaps.inv hγ.1 hz
      rw [inv_inv, sTheta_inv] at h3
      exact (le_iSup₂_of_le _ (mem_parabolicRadicalRoots_of (IsRoot.smul hγ.1 sTheta) hδpos hδ1)
        le_rfl : rootSubgroup TwistTag.E6.tag k (sTheta • γ) ≤
          parabolicRadical TwistTag.E6.tag k setA) h3
    have h4 := hQ _ hw
    have e : n * (n⁻¹ * z * n) * n⁻¹ = z := by group
    rw [e] at h4
    have h5 := conj_mem_rootSpan_of_mapsRootLines hnmon hnmaps
      (S := parabolicRadicalRoots TwistTag.E6.tag setA) (fun δ hδ => hδ.1.1) h4
    have e' : α z = n * (n⁻¹ * α z * n) * n⁻¹ := by group
    rw [e']
    refine rootSpan_mono ?_ h5
    rintro _ ⟨δ, hδ, rfl⟩
    exact ⟨IsRoot.smul hδ.1.1 _, (sTheta_smul_of_isRoot hδ.1.1
      (ne_zero_of_mem_parabolicRadicalRoots hδ)).2 hδ.1.2⟩

theorem exists_eq_conj_of_mem_unipotentPairAut
    [Finite k]
    {α : MulAut (adjointGroup TwistTag.E6.tag k)} (hα : α ∈ unipotentPairAut TwistTag.E6.tag k)
    (hx : ∀ i, i ≠ e6Idx 1 → ∀ c : k,
      α (adjX TwistTag.E6.tag k i c) = adjX TwistTag.E6.tag k i c) :
    ∃ c : kˣ, ∀ y : adjointGroup TwistTag.E6.tag k,
      (α y : ModGL TwistTag.E6.tag k) = thetaTorusHom k c * y * (thetaTorusHom k c)⁻¹ := by
  obtain ⟨a, σ, ε, rfl⟩ := exists_exactNormalAut_eq (τ := TwistTag.E6.tag) (Or.inl rfl) hα
  have hε : (ε : ℕ) = 0 := by
    have h := hx (e6Idx 0) (by decide) 1
    rw [exactNormalAut_adjX, map_one, mul_one] at h
    have h' : pinnedX TwistTag.E6.tag k (Pi.single (exactPerm TwistTag.E6.tag ε (e6Idx 0)) 1)
        (a (exactPerm TwistTag.E6.tag ε (e6Idx 0)) : k) =
          pinnedX TwistTag.E6.tag k (Pi.single (e6Idx 0) 1) 1 := by
      rw [pinnedX_single, pinnedX_single]
      exact congrArg Subtype.val h
    have hroot := eq_of_pinnedX_eq_pinnedX_of_pos (isRoot_single _ _) (isRoot_single _ _)
      (by decide) one_ne_zero h'
    have hidx : exactPerm TwistTag.E6.tag ε (e6Idx 0) = e6Idx 0 := by
      by_contra hne
      have h0 := congrFun hroot (e6Idx 0)
      rw [Pi.single_eq_of_ne (Ne.symm hne), Pi.single_eq_same] at h0
      exact zero_ne_one h0
    have h0 : exactPerm Tag.E6 ((0 : Fin 2) : ℕ) ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
      show (TwistTag.E6.perm ^ (0 : ℕ) : Equiv.Perm (Fin Tag.E6.rank)) ⟨0, by decide⟩ =
        ⟨0, by decide⟩
      rw [pow_zero]
      rfl
    exact congrArg Fin.val (exactPerm_E6_injective ε 0 (hidx.trans h0.symm))
  have hπ : ∀ i, exactPerm TwistTag.E6.tag (ε : ℕ) i = i := fun i => by
    rw [hε]
    show (TwistTag.E6.perm ^ (0 : ℕ) : Equiv.Perm (Fin Tag.E6.rank)) i = i
    rw [pow_zero]
    rfl
  have hai : ∀ i, i ≠ e6Idx 1 → ∀ c : k, (a i : k) * σ c = c := by
    intro i hi c
    have h := hx i hi c
    rw [exactNormalAut_adjX, hπ] at h
    have h' : pinnedX TwistTag.E6.tag k (Pi.single i 1) ((a i : k) * σ c) =
        pinnedX TwistTag.E6.tag k (Pi.single i 1) c := by
      rw [pinnedX_single, pinnedX_single]
      exact congrArg Subtype.val h
    exact pinnedX_injective _ _ _ h'
  have ha1 : ∀ i, i ≠ e6Idx 1 → a i = 1 := fun i hi => Units.ext (by simpa using hai i hi 1)
  have hσ : σ = RingEquiv.refl k := RingEquiv.ext fun c => by
    have h := hai (e6Idx 0) (by decide) c
    rw [ha1 _ (by decide), Units.val_one, one_mul] at h
    exact h
  subst hσ
  refine ⟨a (e6Idx 1), fun y => ?_⟩
  have ha : a = Pi.mulSingle (e6Idx 1) (a (e6Idx 1)) := funext fun j => by
    by_cases hj : j = e6Idx 1
    · subst hj
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj, ha1 j hj]
  have hd : rootDiagUnit TwistTag.E6.tag a = thetaTorusHom k (a (e6Idx 1)) := by
    conv_lhs => rw [ha]
    rfl
  have hQ0 : exactQ TwistTag.E6.tag k (ε : ℕ) = 1 := by
    rw [hε]
    exact pow_zero _
  have hmap : Units.map (entrywiseHom (RingEquiv.refl k).toRingHom) (y : ModGL TwistTag.E6.tag k) =
      y := by
    rw [RingEquiv.toRingHom_refl']
    exact Units.ext (entrywise_id _)
  rw [coe_exactNormalAut, hQ0, hmap, hd, mul_one, inv_one, mul_one]

theorem exists_eq_conj_thetaTorusHom
    [Finite k] [CharP k 2] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hL : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ subsystemGroup TwistTag.E6.tag k setA → α y = y)
    (hU : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot →
        (α y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot)
    (hV : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k (-e6HighestRoot) →
        (α y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k (-e6HighestRoot)) :
    ∃ c : kˣ, ∀ y : adjointGroup TwistTag.E6.tag k,
      (α y : ModGL TwistTag.E6.tag k) = thetaTorusHom k c * y * (thetaTorusHom k c)⁻¹ := by
  have h2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  set n : adjointGroup TwistTag.E6.tag k := ⟨_, nTheta_mem_adjointGroup h2⟩ with hn
  have hnmon := nTheta_mem_monomialSubgroup (K := k) h2
  have hnmaps := mapsRootLines_nTheta (K := k) h2
  have hs : sTheta⁻¹ • (-e6HighestRoot) = e6HighestRoot :=
    inv_smul_eq_iff.2 sTheta_smul_theta.symm
  have hα' : ∀ y, ((MulAut.conj n)⁻¹ * α * MulAut.conj n) y = n⁻¹ * α (n * y * n⁻¹) * n :=
    fun y => by rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hU' : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot →
        (((MulAut.conj n)⁻¹ * α * MulAut.conj n) y : ModGL TwistTag.E6.tag k) ∈
          rootSubgroup TwistTag.E6.tag k e6HighestRoot := by
    intro y hy
    have h1 : ((n * y * n⁻¹ : adjointGroup TwistTag.E6.tag k) : ModGL TwistTag.E6.tag k) ∈
        rootSubgroup TwistTag.E6.tag k (-e6HighestRoot) := by
      have h := conj_mem_rootSubgroup hnmon hnmaps isRoot_e6HighestRoot hy
      rwa [sTheta_smul_theta] at h
    have h3 := conj_mem_rootSubgroup (inv_mem hnmon) hnmaps.inv (IsRoot.neg isRoot_e6HighestRoot)
      (hV _ h1)
    rw [hs, inv_inv] at h3
    rw [hα']
    exact h3
  have hQ : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA →
        (α y : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA :=
    fun y hy => map_mem_parabolicRadical hf hk α hU hy
  have hQ' : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA →
        ((n⁻¹ * α (n * y * n⁻¹) * n : adjointGroup TwistTag.E6.tag k) :
          ModGL TwistTag.E6.tag k) ∈ parabolicRadical TwistTag.E6.tag k setA := fun y hy => by
    rw [← hα']
    exact map_mem_parabolicRadical hf hk _ hU' hy
  have hmem : α ∈ unipotentPairAut TwistTag.E6.tag k :=
    ⟨map_eq_of_le α fun y hy => map_mem_posUnipotent α hL hQ hy,
      map_eq_of_le α fun y hy => map_mem_negUnipotent h2 α hL hQ' hy⟩
  exact exists_eq_conj_of_mem_unipotentPairAut hmem fun i hi c =>
    hL _ (xUnit_mem_subsystemGroup (show i ∈ setA from hi) c)

theorem nTheta_conj_thetaTorusHom
    (t : kˣ) :
    E6GraphLevi.thetaSL2 k WSL * thetaTorusHom k t * (E6GraphLevi.thetaSL2 k WSL)⁻¹ =
      (thetaTorusHom k t)⁻¹ := by
  simp only [thetaTorusHom_eq_thetaSL2, ← map_inv, ← map_mul, WSL_mul_HSL_mul_inv, HSL_inv]

theorem negRootSubgroup_le_thetaRankOneGroup :
    rootSubgroup TwistTag.E6.tag k (-e6HighestRoot) ≤ thetaRankOneGroup (RingHom.id k) := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  exact Subgroup.mem_sup_right ((mem_thetaNegRootGroup (RingHom.id k)).2 ⟨c, rfl⟩)

theorem exists_units_ne_one [Finite k] {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f) :
    ∃ t : kˣ, t ≠ 1 := by
  by_contra h
  push Not at h
  have h1 : Nat.card kˣ = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
  rw [Nat.card_units, hk] at h1
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem thetaTorusHom_mem_thetaTorus
    (t : kˣ) :
    thetaTorusHom k t ∈ thetaTorus (RingHom.id k) :=
  ⟨t, by rw [MonoidHom.comp_apply]; exact congrArg _ (Units.ext rfl)⟩

theorem thetaTorusHom_mem_adjointGroup
    (h2 : (2 : k) = 0) (t : kˣ) :
    thetaTorusHom k t ∈ adjointGroup TwistTag.E6.tag k :=
  E6GraphRadical.thetaRankOneGroup_le_adjointGroup (RingHom.id k)
    (thetaTorus_le_thetaRankOneGroup h2 (thetaTorusHom_mem_thetaTorus t))

theorem pinnedX_theta_mul_ne
    (h2 : (2 : k) = 0) :
    pinnedX TwistTag.E6.tag k e6HighestRoot 1 * pinnedX TwistTag.E6.tag k (-e6HighestRoot) 1 ≠
      pinnedX TwistTag.E6.tag k (-e6HighestRoot) 1 *
        pinnedX TwistTag.E6.tag k e6HighestRoot 1 := by
  rw [← thetaSL2_uSL h2, ← thetaSL2_vSL h2, ← map_mul, ← map_mul]
  intro h
  have h' := congrArg (fun B : SL2 k => (B : Matrix (Fin 2) (Fin 2) k) 0 0)
    (thetaSL2_injective h2 h)
  have e1 : ((uSL (1 : k) * vSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    rw [coe_mul_SL2, mul_apply_two, coe_uSL, coe_vSL]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      mul_one]
    linear_combination h2
  have e2 : ((vSL (1 : k) * uSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    rw [coe_mul_SL2, mul_apply_two, coe_uSL, coe_vSL]
    simp
  exact zero_ne_one (e1.symm.trans (h'.trans e2))

theorem not_map_le_of_map_le
    (h2 : (2 : k) = 0)
    (α : MulAut (adjointGroup TwistTag.E6.tag k)) {ρ : Fin TwistTag.E6.tag.rank → ℤ}
    (h₁ : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot →
        (α y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k ρ)
    (h₂ : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k (-e6HighestRoot) →
        (α y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k ρ) : False := by
  obtain ⟨a, ha⟩ : ∃ a : adjointGroup TwistTag.E6.tag k,
      (a : ModGL TwistTag.E6.tag k) = pinnedX TwistTag.E6.tag k e6HighestRoot 1 :=
    ⟨⟨_, pinnedX_mem_adjointGroup _ _⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : adjointGroup TwistTag.E6.tag k,
      (b : ModGL TwistTag.E6.tag k) = pinnedX TwistTag.E6.tag k (-e6HighestRoot) 1 :=
    ⟨⟨_, pinnedX_mem_adjointGroup _ _⟩, rfl⟩
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (h₁ a (mem_rootSubgroup.2 ⟨1, ha.symm⟩))
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 (h₂ b (mem_rootSubgroup.2 ⟨1, hb.symm⟩))
  have hcomm : α (a * b) = α (b * a) := by
    rw [map_mul, map_mul]
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hd, ← pinnedX_add, ← pinnedX_add, add_comm])
  have h := congrArg Subtype.val (α.injective hcomm)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb] at h
  exact pinnedX_theta_mul_ne h2 h

theorem map_mem_thetaRankOneGroup
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hL : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ subsystemGroup TwistTag.E6.tag k setA → α y = y)
    {y : adjointGroup TwistTag.E6.tag k}
    (hy : (y : ModGL TwistTag.E6.tag k) ∈ thetaRankOneGroup (RingHom.id k)) :
    (α y : ModGL TwistTag.E6.tag k) ∈ thetaRankOneGroup (RingHom.id k) := by
  rw [← centralizer_subsystemGroup hf hk]
  refine mem_inf.2 ⟨(α y).2, mem_centralizer_iff.2 fun l hl => ?_⟩
  have hyc := mem_centralizer_iff.1 (thetaRankOneGroup_le_centralizer (by omega) hk hy) l hl
  have e : (⟨l, subsystemGroup_le_adjointGroup hl⟩ : adjointGroup TwistTag.E6.tag k) * y =
      y * ⟨l, subsystemGroup_le_adjointGroup hl⟩ := Subtype.ext hyc
  have e' := congrArg α e
  rw [map_mul, map_mul, hL ⟨l, subsystemGroup_le_adjointGroup hl⟩ hl] at e'
  exact congrArg Subtype.val e'

theorem map_rootSubgroup_le_or_le
    [Finite k] {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hH : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ thetaTorus (RingHom.id k) → α y = y)
    (hL : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ subsystemGroup TwistTag.E6.tag k setA → α y = y)
    {ρ : Fin TwistTag.E6.tag.rank → ℤ} (hρ : IsRoot TwistTag.E6.tag ρ)
    (hρX : rootSubgroup TwistTag.E6.tag k ρ ≤ thetaRankOneGroup (RingHom.id k)) :
    (∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k ρ →
        (α y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot) ∨
    (∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k ρ →
        (α y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k (-e6HighestRoot)) := by
  have h2 : (2 : k) = 0 := two_eq_zero_of_card (by omega) hk
  obtain ⟨t, ht⟩ := exists_units_ne_one hf hk
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (ModGL TwistTag.E6.tag k),
      S = ((rootSubgroup TwistTag.E6.tag k ρ).subgroupOf (adjointGroup TwistTag.E6.tag k)).map
        ((adjointGroup TwistTag.E6.tag k).subtype.comp α.toMonoidHom) := ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ S ↔ ∃ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k ρ ∧
        (α y : ModGL TwistTag.E6.tag k) = z := fun z => by
    rw [hS]
    exact Iff.rfl
  have hhG := thetaTorusHom_mem_adjointGroup h2 t
  have hle := le_or_le_of_normalized h2 ht (S := S)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
      exact map_mem_thetaRankOneGroup hf hk α hL (hρX hy))
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
      obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hy
      have hyy : y * y = 1 :=
        Subtype.ext (by rw [Subgroup.coe_mul, ← hc, pinnedX_mul_self h2]; rfl)
      rw [← Subgroup.coe_mul, ← map_mul, hyy, map_one]
      rfl)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := (hmem z).1 hz
      have hαh : α ⟨_, hhG⟩ = ⟨_, hhG⟩ := hH ⟨_, hhG⟩ (thetaTorusHom_mem_thetaTorus t)
      refine (hmem _).2 ⟨⟨_, hhG⟩ * y * (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k)⁻¹, ?_, ?_⟩
      · exact (mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup hρ
          (thetaTorus_le_torusGroup _ (thetaTorusHom_mem_thetaTorus t))) _).1 hy
      · rw [map_mul, map_mul, map_inv, hαh]
        rfl)
  rcases hle with h | h
  · exact Or.inl fun y hy => h ((hmem _).2 ⟨y, hy, rfl⟩)
  · exact Or.inr fun y hy => h ((hmem _).2 ⟨y, hy, rfl⟩)

theorem eq_one_of_fix
    [Finite k] [CharP k 2] {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag k))
    (hα : ∃ n : ℕ, α ^ 2 ^ n = 1)
    (hH : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ thetaTorus (RingHom.id k) → α y = y)
    (hL : ∀ y : adjointGroup TwistTag.E6.tag k,
      (y : ModGL TwistTag.E6.tag k) ∈ subsystemGroup TwistTag.E6.tag k setA → α y = y) :
    α = 1 := by
  have hf1 : 1 ≤ f := by omega
  have h2 : (2 : k) = 0 := two_eq_zero_of_card hf1 hk
  have hHodd : Odd (Nat.card (thetaTorus (RingHom.id k))) := by
    rw [card_thetaTorus h2, Nat.card_units, hk]
    exact odd_two_pow_sub_one hf1
  have hθ : IsRoot TwistTag.E6.tag e6HighestRoot := isRoot_e6HighestRoot
  rcases map_rootSubgroup_le_or_le hf hk α hH hL hθ
      (rootSubgroup_le_thetaRankOneGroup (K := k)) with hU | hU <;>
    rcases map_rootSubgroup_le_or_le hf hk α hH hL (IsRoot.neg hθ)
      (negRootSubgroup_le_thetaRankOneGroup (k := k)) with hV | hV
  · exact (not_map_le_of_map_le h2 α hU hV).elim
  ·
    obtain ⟨c, hc⟩ := exists_eq_conj_thetaTorusHom hf1 hk α hL hU hV
    have hhG := thetaTorusHom_mem_adjointGroup h2 c
    have hαh : α = MulAut.conj (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) :=
      MulEquiv.ext fun y => Subtype.ext (hc y)
    obtain ⟨n, hn⟩ := hα
    rw [hαh, ← map_pow] at hn
    have hz : (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) ^ 2 ^ n ∈
        center (adjointGroup TwistTag.E6.tag k) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have e := congrArg (fun β : MulAut (adjointGroup TwistTag.E6.tag k) => β z) hn
      simp only [MulAut.conj_apply, MulAut.one_apply] at e
      calc z * (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) ^ 2 ^ n =
          (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) ^ 2 ^ n * z *
            ((⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) ^ 2 ^ n)⁻¹ *
              (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) ^ 2 ^ n := by rw [e]
        _ = (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) ^ 2 ^ n * z := by group
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
    have h1 : thetaTorusHom k c = 1 :=
      eq_one_of_pow_two_pow_eq_one hHodd (thetaTorusHom_mem_thetaTorus c) (n := n)
        (by simpa using congrArg Subtype.val hz)
    have h1' : (⟨_, hhG⟩ : adjointGroup TwistTag.E6.tag k) = 1 := Subtype.ext h1
    rw [hαh, h1', map_one]
  ·
    exfalso
    obtain ⟨n, hn⟩ : ∃ n : adjointGroup TwistTag.E6.tag k,
        (n : ModGL TwistTag.E6.tag k) = E6GraphLevi.thetaSL2 k WSL :=
      ⟨⟨_, nTheta_mem_adjointGroup h2⟩, rfl⟩
    have hnmon := nTheta_mem_monomialSubgroup (K := k) h2
    have hnmaps := mapsRootLines_nTheta (K := k) h2
    have hnC := thetaRankOneGroup_le_centralizer hf1 hk (nTheta_mem_thetaRankOneGroup (K := k) h2)
    have hβy : ∀ y, (MulAut.conj n * α) y = n * α y * n⁻¹ := fun y => by
      rw [MulAut.mul_apply, MulAut.conj_apply]
    have hβL : ∀ y : adjointGroup TwistTag.E6.tag k,
        (y : ModGL TwistTag.E6.tag k) ∈ subsystemGroup TwistTag.E6.tag k setA →
          (MulAut.conj n * α) y = y := fun y hy => by
      rw [hβy, hL y hy]
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn,
        ← mem_centralizer_iff.1 hnC _ hy, mul_inv_cancel_right]
    have hβU : ∀ y : adjointGroup TwistTag.E6.tag k,
        (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot →
          ((MulAut.conj n * α) y : ModGL TwistTag.E6.tag k) ∈
            rootSubgroup TwistTag.E6.tag k e6HighestRoot := fun y hy => by
      have h := conj_mem_rootSubgroup hnmon hnmaps (IsRoot.neg hθ) (hU y hy)
      rw [smul_neg, sTheta_smul_theta, neg_neg] at h
      rw [hβy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn]
      exact h
    have hβV : ∀ y : adjointGroup TwistTag.E6.tag k,
        (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k (-e6HighestRoot) →
          ((MulAut.conj n * α) y : ModGL TwistTag.E6.tag k) ∈
            rootSubgroup TwistTag.E6.tag k (-e6HighestRoot) := fun y hy => by
      have h := conj_mem_rootSubgroup hnmon hnmaps hθ (hV y hy)
      rw [sTheta_smul_theta] at h
      rw [hβy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn]
      exact h
    obtain ⟨c, hc⟩ := exists_eq_conj_thetaTorusHom hf1 hk _ hβL hβU hβV
    obtain ⟨t, ht⟩ := exists_units_ne_one hf hk
    have htG := thetaTorusHom_mem_adjointGroup h2 t
    have e1 : (((MulAut.conj n * α) ⟨_, htG⟩ : adjointGroup TwistTag.E6.tag k) :
        ModGL TwistTag.E6.tag k) = (thetaTorusHom k t)⁻¹ := by
      rw [hβy, hH ⟨_, htG⟩ (thetaTorusHom_mem_thetaTorus t), Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hn]
      exact nTheta_conj_thetaTorusHom t
    have e2 : (((MulAut.conj n * α) ⟨_, htG⟩ : adjointGroup TwistTag.E6.tag k) :
        ModGL TwistTag.E6.tag k) = thetaTorusHom k t := by
      rw [hc]
      change thetaTorusHom k c * thetaTorusHom k t * (thetaTorusHom k c)⁻¹ = thetaTorusHom k t
      rw [← map_mul, mul_comm c t, map_mul, mul_inv_cancel_right]
    have e4 : thetaTorusHom k t = (thetaTorusHom k t)⁻¹ := e2.symm.trans e1
    have e3 : thetaTorusHom k (t ^ 2) = thetaTorusHom k 1 := by
      rw [map_pow, pow_two, map_one]
      nth_rw 2 [e4]
      exact mul_inv_cancel _
    exact RootTorus.sq_ne_one_of_two h2 ht (thetaTorusHom_injective h2 e3)
  · exact (not_map_le_of_map_le h2 α hU hV).elim

end CFSG.LieType.Chevalley.E6EvenRootTorus
