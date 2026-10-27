module

public import CFSG.LocalAnalysis.GH72.G3b
public import CFSG.LocalAnalysis.GH72.DDSubgroups
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6
  (mem_sup_iff_of_le_normalizer le_normalizer_of_comm card_sup_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn)

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem lemma_3_13 (𝔖 : Sec3Setting G) (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) (H : Subgroup G)
    (hH : O2 H = H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ H) ⊔ (𝔖.S₂ ⊓ H)) H) :
    (𝔖.S₁ ⊓ H = ⊥ ∨ IsDih (𝔖.S₁ ⊓ H)) ∧ (𝔖.S₂ ⊓ H = ⊥ ∨ IsDih (𝔖.S₂ ⊓ H)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R₁ : Subgroup G := 𝔖.S₁ ⊓ H with hR₁
  set R₂ : Subgroup G := 𝔖.S₂ ⊓ H with hR₂
  set R : Subgroup G := R₁ ⊔ R₂ with hR
  have hR₁le : R₁ ≤ 𝔖.S₁ := by
    rw [hR₁]
    exact (inf_le_left : 𝔖.S₁ ⊓ H ≤ 𝔖.S₁)
  have hR₂le : R₂ ≤ 𝔖.S₂ := by
    rw [hR₂]
    exact (inf_le_left : 𝔖.S₂ ⊓ H ≤ 𝔖.S₂)
  have hRleH : R ≤ H := hsyl.le
  have hR2 : IsPGroup 2 R := hsyl.isPGroup
  have hRidx : ¬ 2 ∣ R.relIndex H := (CFSG.ABGLocalTools.isSylowOf_iff.mp hsyl).2.2
  have hRleS : R ≤ 𝔖.S := by
    rw [hR, ← 𝔖.decomp.sup_eq]
    exact sup_le (hR₁le.trans le_sup_left) (hR₂le.trans le_sup_right)
  have hdisj : R₁ ⊓ R₂ = ⊥ := by
    rw [hR₁, hR₂]
    have h : (𝔖.S₁ ⊓ H) ⊓ (𝔖.S₂ ⊓ H) = (𝔖.S₁ ⊓ 𝔖.S₂) ⊓ H := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [h, 𝔖.decomp.inf_eq, bot_inf_eq]
  have hD₁ : IsDih 𝔖.S₁ := 𝔖.decomp.dih₁
  have hD₂ : IsDih 𝔖.S₂ := isDih_of_isDihNonab 𝔖.decomp.dih₂
  have hcomm₁₂ : ∀ x ∈ 𝔖.S₁, ∀ y ∈ 𝔖.S₂, x * y = y * x := fun x hx y hy =>
    𝔖.decomp.comm hx hy
  have hnoIdx : ∀ N : Subgroup H, N.Normal → N.index ≠ 2 := by
    intro N hN hN2
    have hmem : N ∈ {M : Subgroup H | M.Normal ∧ ∃ n : ℕ, M.index = 2 ^ n} :=
      ⟨hN, ⟨1, by rw [hN2]; norm_num⟩⟩
    have hle : O2 H ≤ N.map H.subtype := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨y, sInf_le hmem hy, rfl⟩
    have hHle : H ≤ N.map H.subtype := by
      intro x hx
      exact hle (hH.symm ▸ hx)
    have heq : N.map H.subtype = H := le_antisymm (Subgroup.map_subtype_le N) hHle
    have hcard : Nat.card H = Nat.card N := by
      calc Nat.card H = Nat.card (N.map H.subtype) :=
            (Nat.card_congr (MulEquiv.subgroupCongr heq).toEquiv).symm
        _ = Nat.card N := Subgroup.card_subtype H N
    have h1 : Nat.card N * N.index = Nat.card H := Subgroup.card_mul_index N
    rw [hN2] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    omega
  have h12₁ : ∀ (T : Subgroup G) (g : G), T ≤ 𝔖.S₁ →
      T.map (MulAut.conj g).toMonoidHom ≤ 𝔖.S →
      ∀ t ∈ T, orderOf t = 2 → g * t * g⁻¹ ∈ 𝔖.S₁ :=
    fun T g hT hmap t ht ht2 => (lemma_3_12 𝔖 hpf T g hmap).1 hT t ht ht2
  have h12₂ : ∀ (T : Subgroup G) (g : G), T ≤ 𝔖.S₂ →
      T.map (MulAut.conj g).toMonoidHom ≤ 𝔖.S →
      ∀ t ∈ T, orderOf t = 2 → g * t * g⁻¹ ∈ 𝔖.S₂ :=
    fun T g hT hmap t ht ht2 => (lemma_3_12 𝔖 hpf T g hmap).2 hT t ht ht2
  have cycleContra : ∀ (A B SA SB : Subgroup G), IsDih SA → A ≤ SA → B ≤ SB →
      (∀ x ∈ A, ∀ y ∈ B, x * y = y * x) → A ⊓ B = ⊥ → SA ⊓ SB = ⊥ → A ⊔ B = R →
      (∀ (T : Subgroup G) (g : G), T ≤ SA →
        T.map (MulAut.conj g).toMonoidHom ≤ 𝔖.S →
        ∀ t ∈ T, orderOf t = 2 → g * t * g⁻¹ ∈ SA) →
      IsCyclic A → A ≠ ⊥ → False := by
    intro A B SA SB hDA hAsa hBsb hcomm hAB hSAB hsup h12 hcyc hne
    obtain ⟨a, hagen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp hcyc
    have haA : a ∈ A := by rw [← hagen]; exact Subgroup.mem_zpowers a
    have hA2 : IsPGroup 2 A := hDA.isPGroup.to_le hAsa
    obtain ⟨n, hn⟩ := hA2.exists_card_eq
    have haord : orderOf a = 2 ^ n := by
      rw [← Nat.card_zpowers, hagen, hn]
    have hn1 : 1 ≤ n := by
      by_contra h
      have hn0 : n = 0 := by omega
      have h1 : Nat.card (Subgroup.zpowers a) = 1 := by rw [hagen, hn, hn0, pow_zero]
      apply hne
      rw [← hagen]
      exact Subgroup.card_eq_one.mp h1
    set m : ℕ := n - 1 with hm
    have hmn : n = m + 1 := by omega
    have haord' : orderOf a = 2 ^ (m + 1) := by rw [haord, hmn]
    have hcarda : Nat.card (Subgroup.zpowers a) = 2 ^ (m + 1) := by
      rw [Nat.card_zpowers, haord']
    have hcarda2 : Nat.card (Subgroup.zpowers (a ^ 2)) = 2 ^ m := by
      rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num)]
      · rw [haord', pow_succ]
        exact Nat.mul_div_cancel _ (by norm_num)
      · rw [haord']
        exact Nat.pow_dvd_pow 2 (Nat.succ_le_succ (Nat.zero_le m))
    set T : Subgroup G := Subgroup.zpowers (a ^ 2) ⊔ B with hT
    have ha2A : a ^ 2 ∈ A := A.pow_mem haA 2
    have hzpowA : Subgroup.zpowers (a ^ 2) ≤ A := Subgroup.zpowers_le.mpr ha2A
    have hTleR : T ≤ R := by
      rw [hT, ← hsup]
      exact sup_le (hzpowA.trans le_sup_left) le_sup_right
    have hTleS : T ≤ 𝔖.S := hTleR.trans hRleS
    have hTcard : Nat.card T = Nat.card (Subgroup.zpowers (a ^ 2)) * Nat.card B := by
      rw [hT]
      exact card_sup_of_le_normalizer
        (le_normalizer_of_comm (fun x hx y hy => hcomm x (hzpowA hx) y hy))
        (by
          apply le_antisymm _ bot_le
          intro x hx
          rw [Subgroup.mem_inf] at hx
          rw [← hSAB]
          exact Subgroup.mem_inf.mpr ⟨hAsa (hzpowA hx.1), hBsb hx.2⟩)
    have hRcard : Nat.card R = Nat.card (Subgroup.zpowers a) * Nat.card B := by
      rw [← hsup, ← hagen]
      exact card_sup_of_le_normalizer
        (le_normalizer_of_comm (fun x hx y hy => hcomm x (hagen ▸ hx) y hy))
        (by rw [hagen]; exact hAB)
    have hTrel : T.relIndex R = 2 := by
      have h1 := Subgroup.relIndex_mul_card T R
      rw [inf_of_le_left hTleR] at h1
      rw [hRcard, hTcard, hcarda, hcarda2] at h1
      rw [show 2 ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring] at h1
      have hpos : 0 < 2 ^ m * Nat.card B :=
        Nat.mul_pos (pow_pos (by norm_num) m) Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [h1]
      ring
    have haT : a ∉ T := by
      intro ha
      have hTR : T = R := by
        apply le_antisymm hTleR
        rw [← hsup]
        have hAT : A ≤ T := by
          rw [← hagen]
          exact Subgroup.zpowers_le.mpr ha
        exact sup_le hAT le_sup_right
      have h1 : T.relIndex R = 1 := by rw [hTR, Subgroup.relIndex_self]
      omega
    have hTpow : ∀ y ∈ T, y ^ (2 ^ m) ∈ B := by
      intro y hy
      rw [hT] at hy
      obtain ⟨u, hu, v, hv, hyuv⟩ :=
        (mem_sup_iff_of_le_normalizer (H := Subgroup.zpowers (a ^ 2)) (K := B)
          (le_normalizer_of_comm (fun x hx y hy => hcomm x (hzpowA hx) y hy))).mp hy
      have huA : u ∈ A := hzpowA hu
      have huPow : u ^ (2 ^ m) = 1 := by
        rw [← hcarda2]
        exact orderOf_dvd_iff_pow_eq_one.mp
          (Subgroup.orderOf_dvd_natCard (Subgroup.zpowers (a ^ 2)) hu)
      have hcommuv : Commute u v := hcomm u huA v hv
      rw [hyuv, hcommuv.mul_pow, huPow, one_mul]
      exact B.pow_mem hv (2 ^ m)
    have hpowNe : ∀ u ∈ A, u ∉ Subgroup.zpowers (a ^ 2) → u ^ (2 ^ m) ≠ 1 := by
      intro u huA huNot hup
      let uA : A := ⟨u, huA⟩
      let aA : A := ⟨a, haA⟩
      have hsqcard : Nat.card (Subgroup.zpowers (aA ^ 2)) = 2 ^ m := by
        have hmap : (Subgroup.zpowers (aA ^ 2)).map A.subtype = Subgroup.zpowers (a ^ 2) := by
          rw [MonoidHom.map_zpowers]
          rfl
        calc Nat.card (Subgroup.zpowers (aA ^ 2))
            = Nat.card ((Subgroup.zpowers (aA ^ 2)).map A.subtype) :=
              (Subgroup.card_subtype A _).symm
          _ = Nat.card (Subgroup.zpowers (a ^ 2)) := by rw [hmap]
          _ = 2 ^ m := hcarda2
      have hUA : Subgroup.zpowers uA ≤ Subgroup.zpowers (aA ^ 2) := by
        rw [IsCyclic.subgroup_le_iff_card_dvd]
        rw [Nat.card_zpowers, hsqcard]
        exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [uA] using hup)
      have hmemA : uA ∈ Subgroup.zpowers (aA ^ 2) := hUA (Subgroup.mem_zpowers uA)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemA
      apply huNot
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg (Subgroup.subtype A) hk
      simpa [uA, aA] using this
    have hminG : ∀ y ∈ R, y ∉ T → orderOf a ≤ orderOf y := by
      intro y hyR hyT
      have hyAB : y ∈ A ⊔ B := hsup.symm ▸ hyR
      obtain ⟨u, huA, v, hvB, hyuv⟩ :=
        (mem_sup_iff_of_le_normalizer (H := A) (K := B)
          (le_normalizer_of_comm hcomm)).mp hyAB
      have huNotSq : u ∉ Subgroup.zpowers (a ^ 2) := by
        intro huSq
        apply hyT
        rw [hT, hyuv]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huSq) (Subgroup.mem_sup_right hvB)
      have hyPow : y ^ (2 ^ m) ≠ 1 := by
        intro hyp
        have hcommuv : Commute u v := hcomm u huA v hvB
        have hpow : (u * v) ^ (2 ^ m) = u ^ (2 ^ m) * v ^ (2 ^ m) :=
          hcommuv.mul_pow (2 ^ m)
        have huB : u ^ (2 ^ m) ∈ B := by
          have h1 : u ^ (2 ^ m) = (v ^ (2 ^ m))⁻¹ := by
            rw [hyuv, hpow] at hyp
            exact eq_inv_of_mul_eq_one_left hyp
          rw [h1]
          exact B.inv_mem (B.pow_mem hvB (2 ^ m))
        have huA' : u ^ (2 ^ m) ∈ A := A.pow_mem huA (2 ^ m)
        have hbot : u ^ (2 ^ m) ∈ (⊥ : Subgroup G) := by
          rw [← hAB]
          exact Subgroup.mem_inf.mpr ⟨huA', huB⟩
        exact hpowNe u huA huNotSq (Subgroup.mem_bot.mp hbot)
      by_contra hle
      rw [haord'] at hle
      obtain ⟨d, hd⟩ := hR2.exists_orderOf_eq_pow (⟨y, hyR⟩ : R)
      have hd' : orderOf y = 2 ^ d := by
        rw [Subgroup.orderOf_coe (⟨y, hyR⟩ : R)]
        exact hd
      have hdlt : d < m + 1 := by
        rw [hd'] at hle
        by_contra h
        exact hle (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hdvd : orderOf y ∣ 2 ^ m := by
        rw [hd']
        exact Nat.pow_dvd_pow 2 (by omega)
      exact hyPow (orderOf_dvd_iff_pow_eq_one.mp hdvd)
    have haH : a ∈ H := hRleH (hsup ▸ Subgroup.mem_sup_left haA)
    have hRsubP : IsPGroup 2 (R.subgroupOf H) := hR2.comap_subtype
    have hRsubIdx : ¬ 2 ∣ (R.subgroupOf H).index := hRidx
    have hTsubLe : T.subgroupOf H ≤ R.subgroupOf H := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hTleR (Subgroup.mem_subgroupOf.mp hx))
    have hTsubIdx : (T.subgroupOf H).relIndex (R.subgroupOf H) = 2 :=
      (Subgroup.relIndex_subgroupOf (H := T) (K := R) (L := H) hRleH).trans hTrel
    have haTsub : (⟨a, haH⟩ : H) ∉ T.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact haT
    have hminH : ∀ y ∈ R.subgroupOf H, y ∉ T.subgroupOf H →
        orderOf (⟨a, haH⟩ : H) ≤ orderOf y := by
      intro y hyR hyT
      have hyR' : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hyR
      have hyT' : (y : G) ∉ T := fun h => hyT (Subgroup.mem_subgroupOf.mpr h)
      have h1 := hminG (y : G) hyR' hyT'
      rw [← Subgroup.orderOf_coe (⟨a, haH⟩ : H), ← Subgroup.orderOf_coe y]
      exact h1
    have hxord : orderOf (a ^ 2 ^ m) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity)]
      · rw [haord', pow_succ, mul_comm]
        exact Nat.mul_div_cancel _ (by positivity)
      · rw [haord']
        exact Nat.pow_dvd_pow 2 (Nat.le_succ m)
    have hex : ∃ g : H, g⁻¹ * (⟨a, haH⟩ : H) * g ∈ T.subgroupOf H := by
      by_contra hconj
      have hconj' : ∀ g : H, g⁻¹ * (⟨a, haH⟩ : H) * g ∉ T.subgroupOf H := not_exists.mp hconj
      obtain ⟨N, hN, hNidx⟩ :=
        CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
          (G := H) (T := R.subgroupOf H) (U := T.subgroupOf H)
          hRsubP hRsubIdx hTsubLe hTsubIdx
          (Subgroup.mem_subgroupOf.mpr (hsup ▸ Subgroup.mem_sup_left haA)) haTsub hminH hconj'
      exact hnoIdx N hN hNidx
    obtain ⟨gh, hghT⟩ := hex
    let hG : G := (gh : G)⁻¹
    have hyT : hG * a * hG⁻¹ ∈ T := by
      have h := Subgroup.mem_subgroupOf.mp hghT
      simpa [hG] using h
    have hyPowB : (hG * a * hG⁻¹) ^ (2 ^ m) ∈ B := hTpow _ hyT
    have hxSA : hG * (a ^ (2 ^ m)) * hG⁻¹ ∈ SA := by
      have hAsa' : Subgroup.zpowers a ≤ SA := by rwa [hagen]
      have hmap : (Subgroup.zpowers a).map (MulAut.conj hG).toMonoidHom ≤ 𝔖.S := by
        rw [MonoidHom.map_zpowers]
        apply Subgroup.zpowers_le.mpr
        have hconj : (MulAut.conj hG).toMonoidHom a = hG * a * hG⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hconj]
        exact hTleS hyT
      exact h12 (Subgroup.zpowers a) hG hAsa' hmap (a ^ (2 ^ m))
        (Subgroup.npow_mem_zpowers a (2 ^ m)) hxord
    have hxSB : hG * (a ^ (2 ^ m)) * hG⁻¹ ∈ SB := by
      apply hBsb
      rw [show hG * (a ^ (2 ^ m)) * hG⁻¹ = (hG * a * hG⁻¹) ^ (2 ^ m) by
        rw [conj_pow]]
      exact hyPowB
    have hxord' : orderOf (hG * (a ^ (2 ^ m)) * hG⁻¹) = 2 := by
      have h1 := orderOf_injective (MulAut.conj hG).toMonoidHom (MulAut.conj hG).injective
        (a ^ (2 ^ m))
      rw [hxord] at h1
      rw [show (MulAut.conj hG).toMonoidHom (a ^ (2 ^ m)) = hG * (a ^ (2 ^ m)) * hG⁻¹ by
        simp [MulAut.conj_apply]] at h1
      exact h1
    have hbot : hG * (a ^ (2 ^ m)) * hG⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hSAB]
      exact Subgroup.mem_inf.mpr ⟨hxSA, hxSB⟩
    rw [Subgroup.mem_bot.mp hbot] at hxord'
    exact absurd hxord' (by norm_num)
  have hR₁class : R₁ = ⊥ ∨ IsDih R₁ := by
    by_cases hfour : ∃ V : Subgroup G, IsFourIn 𝔖.S₁ V ∧ V ≤ R₁
    · obtain ⟨V, hV, hVR⟩ := hfour
      exact Or.inr (IsDih.of_le hD₁ hR₁le hV hVR)
    · have hcyc : IsCyclic R₁ :=
        IsDih.isCyclic_of_le hD₁ hR₁le (fun V hV hVR => hfour ⟨V, hV, hVR⟩)
      by_cases hbot : R₁ = ⊥
      · exact Or.inl hbot
      · exact False.elim (cycleContra R₁ R₂ 𝔖.S₁ 𝔖.S₂ hD₁ hR₁le hR₂le
          (fun x hx y hy => hcomm₁₂ x (hR₁le hx) y (hR₂le hy))
          hdisj 𝔖.decomp.inf_eq hR.symm h12₁ hcyc hbot)
  have hR₂class : R₂ = ⊥ ∨ IsDih R₂ := by
    by_cases hfour : ∃ V : Subgroup G, IsFourIn 𝔖.S₂ V ∧ V ≤ R₂
    · obtain ⟨V, hV, hVR⟩ := hfour
      exact Or.inr (IsDih.of_le hD₂ hR₂le hV hVR)
    · have hcyc : IsCyclic R₂ :=
        IsDih.isCyclic_of_le hD₂ hR₂le (fun V hV hVR => hfour ⟨V, hV, hVR⟩)
      by_cases hbot : R₂ = ⊥
      · exact Or.inl hbot
      · exact False.elim (cycleContra R₂ R₁ 𝔖.S₂ 𝔖.S₁ hD₂ hR₂le hR₁le
          (fun x hx y hy => (hcomm₁₂ y (hR₁le hy) x (hR₂le hx)).symm)
          (by rw [inf_comm, hdisj]) (by rw [inf_comm, 𝔖.decomp.inf_eq])
          (by rw [sup_comm, ← hR]) h12₂ hcyc hbot)
  exact ⟨hR₁class, hR₂class⟩

end Sec3Setting

end CFSG.GH72
