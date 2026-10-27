module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma isPGroup_of_isElemAbelian' {p : ℕ} {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) : IsPGroup p A := by
  intro x
  exact ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA.2 (x : G) x.2)⟩

private lemma isElemAbelian_of_le' {p : ℕ} {E E₀ : Subgroup G}
    (hE₀ : CFSG.Open.IsElemAbelian p E₀) (hEE₀ : E ≤ E₀) :
    CFSG.Open.IsElemAbelian p E := by
  refine ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_,
    fun x hx => hE₀.2 x (hEE₀ hx)⟩
  haveI : IsMulCommutative ↥E₀ := hE₀.1
  exact congrArg (Subtype.val : ↥E₀ → G) (mul_comm' (⟨(x : G), hEE₀ x.2⟩ : ↥E₀)
    (⟨(y : G), hEE₀ y.2⟩ : ↥E₀))

private lemma tau_mul_base_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    tau * (x₁ * x₂) ∉ ctxP t tau x₁ x₂ rho := by
  intro h
  have hx12 : x₁ * x₂ ∈ ctxP t tau x₁ x₂ rho :=
    l17_Q_le_P hc (hc.base_le_Q (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))))
  have htau : tau ∈ ctxP t tau x₁ x₂ rho := by
    have hmem : (tau * (x₁ * x₂)) * (x₁ * x₂)⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
      (ctxP t tau x₁ x₂ rho).mul_mem h ((ctxP t tau x₁ x₂ rho).inv_mem hx12)
    rwa [show (tau * (x₁ * x₂)) * (x₁ * x₂)⁻¹ = tau by group] at hmem
  exact l17_tau_not_mem_P hc htau

private lemma ttau_mul_base_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t * tau * (x₁ * x₂) ∉ ctxP t tau x₁ x₂ rho := by
  intro h
  have hx12 : x₁ * x₂ ∈ ctxP t tau x₁ x₂ rho :=
    l17_Q_le_P hc (hc.base_le_Q (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))))
  have httau : t * tau ∈ ctxP t tau x₁ x₂ rho := by
    have hmem : (t * tau * (x₁ * x₂)) * (x₁ * x₂)⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
      (ctxP t tau x₁ x₂ rho).mul_mem h ((ctxP t tau x₁ x₂ rho).inv_mem hx12)
    rwa [show (t * tau * (x₁ * x₂)) * (x₁ * x₂)⁻¹ = t * tau by group] at hmem
  exact l17_ttau_not_mem_P hc httau

theorem l17_card_W_le (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {W : Subgroup G}
    (hWP : W ≤ ctxP t tau x₁ x₂ rho) (hWe : CFSG.Open.IsElemAbelian 2 W)
    (hWS : NormalIn W S) : Nat.card W ≤ 4 := by
  by_contra hle
  have hlt : 4 < Nat.card W := Nat.lt_of_not_le hle
  have hW2 : IsPGroup 2 W := isPGroup_of_isElemAbelian' hWe
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hW2.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    have hk2 : k ≤ 2 := by omega
    interval_cases k <;> rw [hk] at hlt <;> norm_num at hlt
  rcases eq_or_lt_of_le hk3 with hk3' | hk4
  · have hW8 : Nat.card W = 8 := by rw [hk, ← hk3']; norm_num
    rcases hc.toCtx11.toCtx10.l46 W hWS hWe hW8 with h | h | h | h | h
    · have htW : t ∈ W := by rw [h]; exact Subgroup.subset_closure (by simp)
      exact l17_t_not_mem_P hc (hWP htW)
    · have htauW : tau ∈ W := by rw [h]; exact Subgroup.subset_closure (by simp)
      exact l17_tau_not_mem_P hc (hWP htauW)
    · have httauW : t * tau ∈ W := by rw [h]; exact Subgroup.subset_closure (by simp)
      exact l17_ttau_not_mem_P hc (hWP httauW)
    · have hgW : tau * (x₁ * x₂) ∈ W := by
        rw [h]; exact Subgroup.subset_closure (by simp)
      exact tau_mul_base_not_mem_P hc (hWP hgW)
    · have hgW : t * tau * (x₁ * x₂) ∈ W := by
        rw [h]; exact Subgroup.subset_closure (by simp)
      exact ttau_mul_base_not_mem_P hc (hWP hgW)
  · have hk4' : 4 ≤ k := by omega
    have hcard16 : 16 ≤ Nat.card W := by
      rw [hk]
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4'
    obtain ⟨Y', hY'W, hY'e, hY'card⟩ := exists_isElemAbelian_card_sixteen hWe hcard16
    have hY'S : Y' ≤ S := hY'W.trans hWS.1
    have hY'16 : IsE16In S Y' := ⟨hY'S, hY'e, hY'card⟩
    have htY' : t ∈ Y' :=
      (hc.toCtx11.toCtx10.l47.1 Y' hY'16).2.1 (Subgroup.subset_closure (by simp))
    exact l17_t_not_mem_P hc (hWP (hY'W htY'))

private def OmegaP (t tau x₁ x₂ rho : G) : Subgroup G :=
  closure {g : G | g ∈ ctxP t tau x₁ x₂ rho ∧ g ^ 2 = 1}

private lemma mem_OmegaP_iff (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) (x : G) :
    x ∈ OmegaP t tau x₁ x₂ rho ↔ x ∈ ctxP t tau x₁ x₂ rho ∧ x ^ 2 = 1 := by
  unfold OmegaP
  exact mem_closure_sq_one_iff (l17_P_comm hc) x

private lemma OmegaP_eq_ctxYq (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    OmegaP t tau x₁ x₂ rho = ctxYq t tau x₁ x₂ rho := by
  have hPcomm : ∀ a ∈ ctxP t tau x₁ x₂ rho, ∀ b ∈ ctxP t tau x₁ x₂ rho,
      a * b = b * a := l17_P_comm hc
  have hmem : ∀ x : G, x ∈ OmegaP t tau x₁ x₂ rho ↔
      x ∈ ctxP t tau x₁ x₂ rho ∧ x ^ 2 = 1 := fun x => mem_OmegaP_iff hc x
  have hYΩ : ctxYq t tau x₁ x₂ rho ≤ OmegaP t tau x₁ x₂ rho := by
    intro y hy
    exact (hmem y).mpr ⟨l17_Q_le_P hc.toCtx13 (ctxYq_le_ctxQ hy),
      ((mem_ctxYq_iff hc.q_iso y).mp hy).2⟩
  have hΩe : CFSG.Open.IsElemAbelian 2 (OmegaP t tau x₁ x₂ rho) := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      exact hPcomm a.1 ((hmem a.1).mp a.2).1 b.1 ((hmem b.1).mp b.2).1
    · intro a ha
      exact ((hmem a).mp ha).2
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htΩ : ∀ a ∈ OmegaP t tau x₁ x₂ rho,
      t * a * t⁻¹ ∈ OmegaP t tau x₁ x₂ rho := by
    intro a ha
    obtain ⟨haP, ha2⟩ := (hmem a).mp ha
    have htK : t ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).1
    refine (hmem (t * a * t⁻¹)).mpr
      ⟨(l17_P_normal hc.toCtx13).2 t htK a haP, ?_⟩
    rw [conj_pow, ha2]
    group
  have hbound : Nat.card (OmegaP t tau x₁ x₂ rho) ≤ 16 := by
    have h := card_le_sq_card_centralizer hΩe ht2 htΩ
    have hWle4 :
        Nat.card ↥(OmegaP t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G)) ≤ 4 := by
      refine l17_card_W_le hc.toCtx13 ?_ ?_ ?_
      · intro w hw
        exact ((hmem w).mp (Subgroup.mem_inf.mp hw).1).1
      · exact isElemAbelian_of_le' hΩe inf_le_left
      · refine ⟨?_, ?_⟩
        · have hle : OmegaP t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) ≤
              𝒮 ⊓ centralizer ({t} : Set G) := by
            refine le_inf ?_ inf_le_right
            intro w hw
            exact l17_P_le_sylow hc ((hmem w).mp (Subgroup.mem_inf.mp hw).1).1
          rwa [c17_cent_eq hc.toCtx13.toCtx11.toCtx10 hc.sylow.2.1
            (l17_le_sylow hc).2.2.1] at hle
        · intro g hg k hk
          obtain ⟨hkΩ, hkC⟩ := Subgroup.mem_inf.mp hk
          obtain ⟨hkP, hk2⟩ := (hmem k).mp hkΩ
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have hgK : g ∈ ctxK t tau x₁ x₂ rho :=
              hc.sylow.1 ((l17_le_sylow hc).2.2.1 hg)
            refine (hmem (g * k * g⁻¹)).mpr
              ⟨(l17_P_normal hc.toCtx13).2 g hgK k hkP, ?_⟩
            rw [conj_pow, hk2]
            group
          · rw [Subgroup.mem_centralizer_singleton_iff]
            have hgt : g * t = t * g := S4A.mem_invCent_iff.mp (hc.le_invCent hg)
            have hkt : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
            have hginv : g⁻¹ * t = t * g⁻¹ := by
              calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
                _ = g⁻¹ * (g * t) * g⁻¹ := by rw [← hgt]
                _ = t * g⁻¹ := by group
            calc (g * k * g⁻¹) * t = g * k * (g⁻¹ * t) := by group
              _ = g * k * (t * g⁻¹) := by rw [hginv]
              _ = g * (k * t) * g⁻¹ := by group
              _ = g * (t * k) * g⁻¹ := by rw [hkt]
              _ = (g * t) * k * g⁻¹ := by group
              _ = (t * g) * k * g⁻¹ := by rw [hgt]
              _ = t * (g * k * g⁻¹) := by group
    calc Nat.card (OmegaP t tau x₁ x₂ rho)
        ≤ Nat.card ↥(OmegaP t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G)) ^ 2 := h
      _ ≤ 4 ^ 2 := Nat.pow_le_pow_left hWle4 2
      _ = 16 := by norm_num
  have hcardY := card_ctxYq hc.q_iso
  have hΩcard : Nat.card (OmegaP t tau x₁ x₂ rho) = 16 := by
    apply le_antisymm hbound
    calc (16 : ℕ) = Nat.card (ctxYq t tau x₁ x₂ rho) := hcardY.symm
      _ ≤ Nat.card (OmegaP t tau x₁ x₂ rho) := Subgroup.card_le_of_le hYΩ
  exact (Subgroup.eq_of_le_of_card_ge hYΩ (by rw [hΩcard, hcardY])).symm

theorem l17_omega (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, x ^ 2 = 1 → x ∈ ctxYq t tau x₁ x₂ rho := by
  intro x hxP hx2
  rw [← OmegaP_eq_ctxYq hc]
  exact (mem_OmegaP_iff hc x).mpr ⟨hxP, hx2⟩

theorem l17_sq_surj (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∃ p ∈ ctxP t tau x₁ x₂ rho, p ^ 2 = a := by
  intro a ha
  let P : Subgroup G := ctxP t tau x₁ x₂ rho
  let f : ↥P →* ↥P := MonoidHom.mk' (fun x => x ^ 2) (fun x y => by
    apply Subtype.ext
    show ((x : G) * (y : G)) ^ 2 = (x : G) ^ 2 * (y : G) ^ 2
    exact Commute.mul_pow (l17_P_comm hc x.1 x.2 y.1 y.2) 2)
  have hf : ∀ x : ↥P, ((f x : ↥P) : G) = (x : G) ^ 2 := fun x => rfl
  have hker_eq : f.ker = (ctxYq t tau x₁ x₂ rho).subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← OmegaP_eq_ctxYq hc]
      refine (mem_OmegaP_iff hc (x : G)).mpr ⟨x.2, ?_⟩
      rw [← hf x]
      exact congrArg Subtype.val hx
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      apply Subtype.ext
      rw [hf x]
      rw [← OmegaP_eq_ctxYq hc] at hx
      exact ((mem_OmegaP_iff hc (x : G)).mp hx).2
  have hkercard : Nat.card f.ker = 16 := by
    rw [hker_eq]
    change Nat.card ((ctxYq t tau x₁ x₂ rho).subgroupOf
      (ctxP t tau x₁ x₂ rho)) = 16
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (ctxYq_le_ctxQ.trans (l17_Q_le_P hc.toCtx13))).toEquiv]
    exact card_ctxYq hc.q_iso
  have hPcard : Nat.card ↥P = 2 ^ 8 := by
    change Nat.card ↥(ctxP t tau x₁ x₂ rho) = 2 ^ 8
    exact (l17_card_P hc).1
  have hrangecard : Nat.card f.range = 16 := by
    set n : ℕ := Nat.card f.range with hn
    have hmul : Nat.card f.ker * n = Nat.card ↥P := by
      rw [hn]
      exact Subgroup.card_ker_mul_card_range f
    rw [hkercard, hPcard] at hmul
    norm_num at hmul
    have hmul' : 16 * n = 16 * 16 := by rw [hmul]
    exact Nat.mul_left_cancel (by norm_num : 0 < 16) hmul'
  let Im : Subgroup G := f.range.map P.subtype
  have hImY : Im ≤ ctxYq t tau x₁ x₂ rho := by
    rintro b ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := hy
    rw [← OmegaP_eq_ctxYq hc]
    refine (mem_OmegaP_iff hc ((x ^ 2 : ↥P) : G)).mpr ⟨(x ^ 2).2, ?_⟩
    calc (((x ^ 2 : ↥P) : G)) ^ 2 = ((x : G) ^ 2) ^ 2 := by
          rw [show (((x ^ 2 : ↥P) : G)) = (x : G) ^ 2 from rfl]
      _ = (x : G) ^ 4 := by rw [← pow_mul]
      _ = 1 := l17_exp_four hc (x : G) x.2
  have hImcard : Nat.card Im = 16 := by
    change Nat.card (f.range.map P.subtype) = 16
    rw [Subgroup.card_map_of_injective (K := f.range) P.subtype_injective, hrangecard]
  have hIm_eq : Im = ctxYq t tau x₁ x₂ rho :=
    Subgroup.eq_of_le_of_card_ge hImY (by rw [hImcard, card_ctxYq hc.q_iso])
  have haIm : a ∈ Im := by rwa [hIm_eq]
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp haIm
  obtain ⟨x, rfl⟩ := hy
  refine ⟨(x : G), x.2, ?_⟩
  calc (x : G) ^ 2 = ((f x : ↥P) : G) := (hf x).symm
    _ = a := hya

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
