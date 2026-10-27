module

public import CFSG.CGT.Hall82.DBasic
public import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeTri
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G} {rep : Fin 64 → G}

private noncomputable def repM (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (v : Fin 64) : ↥M :=
  ⟨rep v, S.le (CFSG.LieType.BorelTits.pCoreOf_le 2 L (S.blockU_le_blockQ (hc.mem v)))⟩

private lemma repM_zero (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    repM S hc 0 = 1 :=
  Subtype.ext hc.rep_zero

private lemma repM_mul (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (v w : Fin 64) :
    repM S hc (xorF v w) = repM S hc v * repM S hc w :=
  Subtype.ext (hc.add v w)

private lemma repM_inj (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    Function.Injective (repM S hc) :=
  fun a b h => hc.inj (congrArg Subtype.val h)

private lemma conj_repM (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) (v : Fin 64) :
    m * repM S hc v * m⁻¹ = repM S hc (S.psiM hc m v) :=
  Subtype.ext (S.rep_psiM hc m v).symm

private lemma psiM_repM (S : Setting G M L)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (v : Fin 64) :
    S.psiM hc (repM S hc v) = 1 :=
  (S.psiM_eq_one_iff_mem_blockU hc hC1 (repM S hc v)).mpr (hc.mem v)

private lemma exists_theta (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    ∃ θ : ↥M, θ ^ 3 = 1 ∧ θ ≠ 1 ∧ S.psiM hc θ = heZeta := by
  have hω : heZeta ∈ S.psiSub hc L := by
    rw [S.psiSub_L hF hc]
    exact hF.zeta_mem
  rw [mem_psiSub S hc S.le] at hω
  obtain ⟨l, hlL, hlM, hlψ⟩ := hω
  let m₀ : ↥M := ⟨l, hlM⟩
  have hψm₀ : S.psiM hc m₀ = heZeta := hlψ
  have h3mem : ((m₀ ^ 3 : ↥M) : G) ∈ blockU L := by
    refine (S.psiM_eq_one_iff_mem_blockU hc hC1 (m₀ ^ 3)).mp ?_
    rw [map_pow, hψm₀, hD.zeta_pow]
  have h6 : m₀ ^ 6 = 1 := by
    have hsq : (m₀ ^ 3) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using S.blockU_sq h3mem
    calc m₀ ^ 6 = m₀ ^ (3 * 2) := by norm_num
      _ = (m₀ ^ 3) ^ 2 := pow_mul m₀ 3 2
      _ = 1 := hsq
  have hθ3 : (m₀ ^ 4) ^ 3 = 1 := by
    calc (m₀ ^ 4) ^ 3 = m₀ ^ (4 * 3) := (pow_mul m₀ 4 3).symm
      _ = m₀ ^ (6 * 2) := by norm_num
      _ = (m₀ ^ 6) ^ 2 := pow_mul m₀ 6 2
      _ = 1 := by rw [h6, one_pow]
  have hθne : m₀ ^ 4 ≠ 1 := by
    intro h
    have hψ : S.psiM hc (m₀ ^ 4) = 1 := by rw [h, map_one]
    rw [map_pow, hψm₀] at hψ
    have hω1 : heZeta = 1 := by
      calc heZeta = heZeta ^ 4 := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hD.zeta_pow, one_mul, pow_one]
        _ = 1 := hψ
    exact hD.zeta_ne hω1
  have hψθ : S.psiM hc (m₀ ^ 4) = heZeta := by
    rw [map_pow, hψm₀]
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hD.zeta_pow, one_mul, pow_one]
  exact ⟨m₀ ^ 4, hθ3, hθne, hψθ⟩

private lemma zeta_pow_add (hF : ModelFacts) (hD : DModelFacts) (j : ℕ) (v w : Fin 64) :
    (heZeta ^ j) (xorF v w) = xorF ((heZeta ^ j) v) ((heZeta ^ j) w) :=
  hD.lin (heZeta ^ j) (hF.le (hexaL.pow_mem hF.zeta_mem j)) v w

private lemma zeta_pow_fix (hD : DModelFacts) (j : ℕ) (hj : j = 1 ∨ j = 2) (v : Fin 64) :
    (heZeta ^ j) v = v → v = 0 := by
  rcases hj with rfl | rfl
  · exact hD.zeta_fix v
  · intro h
    have h3 : (heZeta ^ 3) v = (heZeta ^ 1) v := by
      calc (heZeta ^ 3) v = (heZeta * heZeta ^ 2) v := by
            rw [show heZeta ^ 3 = heZeta * heZeta ^ 2 by
              rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ']]
        _ = heZeta ((heZeta ^ 2) v) := Equiv.Perm.mul_apply _ _ _
        _ = heZeta v := congrArg heZeta h
        _ = (heZeta ^ 1) v := by rw [pow_one]
    rw [hD.zeta_pow, pow_one, Equiv.Perm.one_apply] at h3
    exact hD.zeta_fix v h3.symm

private lemma bijective_xor_zeta (hF : ModelFacts) (hD : DModelFacts) (j : ℕ)
    (hj : j = 1 ∨ j = 2) :
    Function.Bijective (fun a : Fin 64 => xorF a ((heZeta ^ j) a)) := by
  have hf_add : ∀ v w, (fun a : Fin 64 => xorF a ((heZeta ^ j) a)) (xorF v w) =
      xorF ((fun a : Fin 64 => xorF a ((heZeta ^ j) a)) v)
        ((fun a : Fin 64 => xorF a ((heZeta ^ j) a)) w) := by
    intro v w
    show xorF (xorF v w) ((heZeta ^ j) (xorF v w)) =
      xorF (xorF v ((heZeta ^ j) v)) (xorF w ((heZeta ^ j) w))
    rw [zeta_pow_add hF hD j v w]
    calc xorF (xorF v w) (xorF ((heZeta ^ j) v) ((heZeta ^ j) w))
        = xorF v (xorF w (xorF ((heZeta ^ j) v) ((heZeta ^ j) w))) :=
          xorF_assoc v w _
      _ = xorF v (xorF ((heZeta ^ j) v) (xorF w ((heZeta ^ j) w))) := by
          rw [← xorF_assoc w ((heZeta ^ j) v) ((heZeta ^ j) w),
            xorF_comm w ((heZeta ^ j) v),
            xorF_assoc ((heZeta ^ j) v) w ((heZeta ^ j) w)]
      _ = xorF (xorF v ((heZeta ^ j) v)) (xorF w ((heZeta ^ j) w)) :=
          (xorF_assoc v ((heZeta ^ j) v) _).symm
  have hker : ∀ c, (fun a : Fin 64 => xorF a ((heZeta ^ j) a)) c = 0 → c = 0 := by
    intro c hc0
    have hval : c.val ^^^ ((heZeta ^ j) c).val = 0 := by
      rw [← val_xorF]
      exact congrArg Fin.val hc0
    have hfix : (heZeta ^ j) c = c := Fin.ext (Nat.xor_eq_zero_iff.mp hval).symm
    exact zeta_pow_fix hD j hj c hfix
  have hinj : Function.Injective (fun a : Fin 64 => xorF a ((heZeta ^ j) a)) := by
    intro a b hab
    have h0 : (fun a : Fin 64 => xorF a ((heZeta ^ j) a)) (xorF a b) = 0 := by
      calc (fun a : Fin 64 => xorF a ((heZeta ^ j) a)) (xorF a b)
          = xorF ((fun a : Fin 64 => xorF a ((heZeta ^ j) a)) a)
              ((fun a : Fin 64 => xorF a ((heZeta ^ j) a)) b) := hf_add a b
        _ = xorF ((fun a : Fin 64 => xorF a ((heZeta ^ j) a)) b)
              ((fun a : Fin 64 => xorF a ((heZeta ^ j) a)) b) := by rw [hab]
        _ = 0 := xorF_self _
    have h := hker (xorF a b) h0
    have hval : a.val ^^^ b.val = 0 := by
      rw [← val_xorF]
      exact congrArg Fin.val h
    exact Fin.ext (Nat.xor_eq_zero_iff.mp hval)
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

private lemma conj_rep_pow_theta (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (θ : ↥M)
    (hψθ : S.psiM hc θ = heZeta) (j : ℕ) (a : Fin 64) :
    repM S hc a * θ ^ j * (repM S hc a)⁻¹ =
      repM S hc (xorF a ((heZeta ^ j) a)) * θ ^ j := by
  have hψj : S.psiM hc (θ ^ j) = heZeta ^ j := by rw [map_pow, hψθ]
  apply Subtype.ext
  have hconj : (θ : G) ^ j * rep a * ((θ : G) ^ j)⁻¹ = rep ((heZeta ^ j) a) := by
    simpa [hψj] using (S.rep_psiM hc (θ ^ j) a).symm
  have hu : (rep a)⁻¹ = rep a := inv_eq_of_mul_eq_one_right (by
    have h := hc.add a a
    rw [xorF_self, hc.rep_zero] at h
    exact h.symm)
  calc (repM S hc a * θ ^ j * (repM S hc a)⁻¹ : ↥M)
      = rep a * (θ : G) ^ j * (rep a)⁻¹ := rfl
    _ = rep a * ((θ : G) ^ j * rep a) := by rw [hu]; group
    _ = rep a * (rep ((heZeta ^ j) a) * (θ : G) ^ j) := by
        rw [← hconj]
        group
    _ = rep (xorF a ((heZeta ^ j) a)) * (θ : G) ^ j := by rw [hc.add]; group
    _ = (repM S hc (xorF a ((heZeta ^ j) a)) * θ ^ j : ↥M) := rfl

private lemma zeta_sq_ne (hD : DModelFacts) : heZeta ^ 2 ≠ heZeta := by
  intro h
  have h1 : heZeta = 1 := by
    conv_lhs => rw [show heZeta = heZeta ^ 2 * heZeta⁻¹ by
      rw [pow_two]
      group]
    rw [h]
    group
  exact hD.zeta_ne h1

private lemma mem_zpowers_three {H : Type*} [Group H] {x y : H}
    (h3 : x ^ 3 = 1) (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hk, zpow_eq_zpow_emod' k h3]
  rw [show ((3 : ℕ) : ℤ) = 3 by norm_num]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero]
    exact Or.inl rfl
  · rw [h, zpow_one]
    exact Or.inr (Or.inl rfl)
  · rw [h]
    right; right
    exact zpow_natCast x 2

private lemma exists_decomp (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) (θ : ↥M)
    (hψθ : S.psiM hc θ = heZeta) (m : ↥M) :
    ∃ a : Fin 64, ∃ k : ↥M,
      k ∈ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M) ∧
        m = repM S hc a * k := by
  classical
  let y : ↥M := m * θ * m⁻¹
  have hψy : S.psiM hc y = heZeta ∨ S.psiM hc y = heZeta ^ 2 := by
    have h := hD.zeta_conj (S.psiM hc m) (S.psiM_mem_hexaM hc m)
    simpa [y, map_mul, map_inv, hψθ] using h
  rcases hψy with hω | hω2
  ·
    let v : G := ((y * θ⁻¹ : ↥M) : G)
    have hv : v ∈ blockU L := by
      refine (S.psiM_eq_one_iff_mem_blockU hc hC1 (y * θ⁻¹)).mp ?_
      rw [map_mul, map_inv, hω, hψθ]
      group
    obtain ⟨b, hb⟩ := hc.surj v hv
    have hy_eq : y = repM S hc b * θ := by
      apply Subtype.ext
      change (y : G) = rep b * (θ : G)
      calc (y : G) = (((y * θ⁻¹) * θ : ↥M) : G) := by
            rw [show (y * θ⁻¹) * θ = y from by group]
        _ = ((y * θ⁻¹ : ↥M) : G) * (θ : G) := Subgroup.coe_mul M _ _
        _ = rep b * (θ : G) := by
          rw [show ((y * θ⁻¹ : ↥M) : G) = v from rfl, ← hb]
    obtain ⟨a, ha⟩ := (bijective_xor_zeta hF hD 1 (Or.inl rfl)).2 b
    have hconj := conj_rep_pow_theta S hc θ hψθ 1 a
    rw [pow_one] at hconj
    have hfa : xorF a ((heZeta ^ 1) a) = b := ha
    rw [hfa] at hconj
    let k : ↥M := (repM S hc a)⁻¹ * m
    have hm : m = repM S hc a * k := by
      change m = repM S hc a * ((repM S hc a)⁻¹ * m)
      group
    have hkθ : k * θ * k⁻¹ = θ := by
      change ((repM S hc a)⁻¹ * m) * θ * ((repM S hc a)⁻¹ * m)⁻¹ = θ
      calc (repM S hc a)⁻¹ * m * θ * ((repM S hc a)⁻¹ * m)⁻¹
          = (repM S hc a)⁻¹ * (m * θ * m⁻¹) * repM S hc a := by group
        _ = (repM S hc a)⁻¹ * (repM S hc a * θ * (repM S hc a)⁻¹) * repM S hc a := by
            rw [show m * θ * m⁻¹ = y from rfl, hy_eq, hconj]
        _ = θ := by group
    have hkK : k ∈ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M) :=
      CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem (x := θ) (g := k) (by
        rw [hkθ]
        exact Subgroup.mem_zpowers θ)
    exact ⟨a, k, hkK, hm⟩
  ·
    let v : G := ((y * (θ ^ 2)⁻¹ : ↥M) : G)
    have hv : v ∈ blockU L := by
      refine (S.psiM_eq_one_iff_mem_blockU hc hC1 (y * (θ ^ 2)⁻¹)).mp ?_
      rw [map_mul, map_inv, hω2, map_pow, hψθ]
      group
    obtain ⟨b, hb⟩ := hc.surj v hv
    have hy_eq : y = repM S hc b * θ ^ 2 := by
      apply Subtype.ext
      change (y : G) = rep b * ((θ : G) ^ 2)
      calc (y : G) = (((y * (θ ^ 2)⁻¹) * θ ^ 2 : ↥M) : G) := by
            rw [show (y * (θ ^ 2)⁻¹) * θ ^ 2 = y from by group]
        _ = ((y * (θ ^ 2)⁻¹ : ↥M) : G) * ((θ : G) ^ 2) := by
            rw [Subgroup.coe_mul, Subgroup.coe_pow]
        _ = rep b * ((θ : G) ^ 2) := by
          rw [show ((y * (θ ^ 2)⁻¹ : ↥M) : G) = v from rfl, ← hb]
    obtain ⟨a, ha⟩ := (bijective_xor_zeta hF hD 2 (Or.inr rfl)).2 b
    have hconj := conj_rep_pow_theta S hc θ hψθ 2 a
    have hfa : xorF a ((heZeta ^ 2) a) = b := ha
    rw [hfa] at hconj
    let k : ↥M := (repM S hc a)⁻¹ * m
    have hm : m = repM S hc a * k := by
      change m = repM S hc a * ((repM S hc a)⁻¹ * m)
      group
    have hkθ : k * θ * k⁻¹ = θ ^ 2 := by
      change ((repM S hc a)⁻¹ * m) * θ * ((repM S hc a)⁻¹ * m)⁻¹ = θ ^ 2
      calc (repM S hc a)⁻¹ * m * θ * ((repM S hc a)⁻¹ * m)⁻¹
          = (repM S hc a)⁻¹ * (m * θ * m⁻¹) * repM S hc a := by group
        _ = (repM S hc a)⁻¹ * (repM S hc a * θ ^ 2 * (repM S hc a)⁻¹) * repM S hc a := by
            rw [show m * θ * m⁻¹ = y from rfl, hy_eq, hconj]
        _ = θ ^ 2 := by group
    have hkK : k ∈ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M) :=
      CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem (x := θ) (g := k) (by
        rw [hkθ]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers θ) 2)
    exact ⟨a, k, hkK, hm⟩

private lemma inf_subgroupOf_normalizer_zpowers_eq_bot (S : Setting G M L)
    (hD : DModelFacts) (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) (θ : ↥M)
    (hθ3 : θ ^ 3 = 1) (hθne : θ ≠ 1) (hψθ : S.psiM hc θ = heZeta) :
    (blockU L).subgroupOf M ⊓ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M) = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨hkV, hkK⟩ := Subgroup.mem_inf.mp hk
  have hk_mem_zp : k * θ * k⁻¹ ∈ Subgroup.zpowers θ :=
    (Subgroup.mem_normalizer_iff.mp hkK θ).mp (Subgroup.mem_zpowers θ)
  have hψk : S.psiM hc k = 1 :=
    (S.psiM_eq_one_iff_mem_blockU hc hC1 k).mpr (Subgroup.mem_subgroupOf.mp hkV)
  have hψconj : S.psiM hc (k * θ * k⁻¹) = heZeta := by
    rw [map_mul, map_mul, map_inv, hψθ, hψk]
    group
  rcases mem_zpowers_three hθ3 hk_mem_zp with hk1 | hkθ | hkθ2
  · exfalso
    rw [hk1, map_one] at hψconj
    exact hD.zeta_ne hψconj.symm
  · obtain ⟨v, hv⟩ := hc.surj (k : G) (Subgroup.mem_subgroupOf.mp hkV)
    have hk_eq : k = repM S hc v := Subtype.ext hv.symm
    have hconj := conj_rep_pow_theta S hc θ hψθ 1 v
    simp only [pow_one] at hconj
    have hkconj : repM S hc v * θ * (repM S hc v)⁻¹ = θ := by
      rw [← hk_eq]
      exact hkθ
    rw [hconj] at hkconj
    have hrep1 : repM S hc (xorF v (heZeta v)) = 1 := by
      calc repM S hc (xorF v (heZeta v))
          = repM S hc (xorF v (heZeta v)) * θ * θ⁻¹ := by group
        _ = θ * θ⁻¹ := by rw [hkconj]
        _ = 1 := by group
    have hrep : rep (xorF v (heZeta v)) = 1 := congrArg Subtype.val hrep1
    have hf0 : xorF v (heZeta v) = 0 := hc.inj (hrep.trans hc.rep_zero.symm)
    have hval : v.val ^^^ (heZeta v).val = 0 := by
      rw [← val_xorF]
      exact congrArg Fin.val hf0
    have hωv : heZeta v = v := Fin.ext (Nat.xor_eq_zero_iff.mp hval).symm
    have hv0 : v = 0 := hD.zeta_fix v hωv
    rw [hk_eq, hv0, repM_zero]
    exact Subgroup.mem_bot.mpr rfl
  · exfalso
    have hψ2 : S.psiM hc (k * θ * k⁻¹) = heZeta ^ 2 := by
      rw [hkθ2, map_pow, hψθ]
    rw [hψ2] at hψconj
    exact zeta_sq_ne hD hψconj

private lemma decomp_unique (S : Setting G M L) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) (θ : ↥M)
    (hθ3 : θ ^ 3 = 1) (hθne : θ ≠ 1) (hψθ : S.psiM hc θ = heZeta)
    {a a' : Fin 64} {k k' : ↥M}
    (hk : k ∈ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M))
    (hk' : k' ∈ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M))
    (h : repM S hc a * k = repM S hc a' * k') : a = a' := by
  have hK := inf_subgroupOf_normalizer_zpowers_eq_bot S hD hc hC1 θ hθ3 hθne hψθ
  have hVa : repM S hc a ∈ (blockU L).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (hc.mem a)
  have hVa' : repM S hc a' ∈ (blockU L).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (hc.mem a')
  have hV : (repM S hc a')⁻¹ * repM S hc a ∈ (blockU L).subgroupOf M :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hVa') hVa
  have heq : (repM S hc a')⁻¹ * repM S hc a = k' * k⁻¹ := by
    calc (repM S hc a')⁻¹ * repM S hc a
        = (repM S hc a')⁻¹ * (repM S hc a * k) * k⁻¹ := by group
      _ = (repM S hc a')⁻¹ * (repM S hc a' * k') * k⁻¹ := by rw [h]
      _ = k' * k⁻¹ := by group
  have hKm : k' * k⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M) :=
    Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk)
  have hbot : (repM S hc a')⁻¹ * repM S hc a = 1 := by
    have hmem : (repM S hc a')⁻¹ * repM S hc a ∈
        (blockU L).subgroupOf M ⊓ Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M) :=
      Subgroup.mem_inf.mpr ⟨hV, by rw [heq]; exact hKm⟩
    rwa [hK, Subgroup.mem_bot] at hmem
  have hrep : repM S hc a = repM S hc a' := by
    calc repM S hc a = repM S hc a' * ((repM S hc a')⁻¹ * repM S hc a) := by group
      _ = repM S hc a' * 1 := by rw [hbot]
      _ = repM S hc a' := by group
  exact repM_inj S hc hrep

theorem exists_split (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    ∃ Φ : ↥M →* Equiv.Perm (Fin 64), Function.Injective Φ ∧
      (∀ m : ↥M, ∃ a : Fin 64, Φ m = transl a * S.psiM hc m) ∧
      ∀ (m : ↥M) (b : Fin 64), (m : G) = rep b → Φ m = transl b := by
  classical
  obtain ⟨θ, hθ3, hθne, hψθ⟩ := exists_theta S hF hD hc hC1
  let K : Subgroup ↥M := Subgroup.normalizer (Subgroup.zpowers θ : Set ↥M)
  have hKbot : (blockU L).subgroupOf M ⊓ K = ⊥ :=
    inf_subgroupOf_normalizer_zpowers_eq_bot S hD hc hC1 θ hθ3 hθne hψθ
  choose a k hkK hdec using fun m : ↥M => exists_decomp S hF hD hc hC1 θ hψθ m
  have hψk : ∀ m : ↥M, S.psiM hc (k m) = S.psiM hc m := by
    intro m
    have h := congrArg (S.psiM hc) (hdec m)
    rw [map_mul, psiM_repM S hC1 hc, one_mul] at h
    exact h.symm
  let Φ : ↥M →* Equiv.Perm (Fin 64) :=
    { toFun := fun m => transl (a m) * S.psiM hc m
      map_one' := by
        have hψk1 : S.psiM hc (k 1) = 1 := by
          have h := congrArg (S.psiM hc) (hdec 1)
          rw [map_one, map_mul, psiM_repM S hC1 hc, one_mul] at h
          exact h.symm
        have hk1V : k 1 ∈ (blockU L).subgroupOf M :=
          Subgroup.mem_subgroupOf.mpr ((S.psiM_eq_one_iff_mem_blockU hc hC1 (k 1)).mp hψk1)
        have hk1 : k 1 = 1 := by
          have hmem : k 1 ∈ (blockU L).subgroupOf M ⊓ K :=
            Subgroup.mem_inf.mpr ⟨hk1V, hkK 1⟩
          rwa [hKbot, Subgroup.mem_bot] at hmem
        have hrep1 : repM S hc (a 1) = 1 := by
          have h := hdec 1
          rw [hk1, mul_one] at h
          exact h.symm
        have ha1 : a 1 = 0 := by
          have hval : rep (a 1) = 1 := congrArg Subtype.val hrep1
          exact hc.inj (hval.trans hc.rep_zero.symm)
        change transl (a 1) * S.psiM hc 1 = 1
        rw [ha1, map_one, transl_zero, one_mul]
      map_mul' := by
        intro m m'
        change transl (a (m * m')) * S.psiM hc (m * m') =
          (transl (a m) * S.psiM hc m) * (transl (a m') * S.psiM hc m')
        have hdecomp : m * m' =
            repM S hc (xorF (a m) (S.psiM hc m (a m'))) * (k m * k m') := by
          calc m * m' = (repM S hc (a m) * k m) * (repM S hc (a m') * k m') := by
                conv_lhs => rw [hdec m, hdec m']
            _ = repM S hc (a m) * (k m * repM S hc (a m') * (k m)⁻¹) * (k m * k m') := by
                group
            _ = repM S hc (a m) * repM S hc (S.psiM hc (k m) (a m')) * (k m * k m') := by
                rw [conj_repM S hc (k m) (a m')]
            _ = repM S hc (a m) * repM S hc (S.psiM hc m (a m')) * (k m * k m') := by
                rw [hψk m]
            _ = repM S hc (xorF (a m) (S.psiM hc m (a m'))) * (k m * k m') := by
                rw [← repM_mul S hc]
        have ha_eq : a (m * m') = xorF (a m) (S.psiM hc m (a m')) := by
          refine decomp_unique S hD hc hC1 θ hθ3 hθne hψθ (hkK (m * m'))
            (Subgroup.mul_mem _ (hkK m) (hkK m')) ?_
          calc repM S hc (a (m * m')) * k (m * m') = m * m' := (hdec (m * m')).symm
            _ = repM S hc (xorF (a m) (S.psiM hc m (a m'))) * (k m * k m') := hdecomp
        have hconj : S.psiM hc m * transl (a m') * (S.psiM hc m)⁻¹ =
            transl (S.psiM hc m (a m')) :=
          mul_transl_mul_inv (psiM_xorF S hc m) (a m')
        calc transl (a (m * m')) * S.psiM hc (m * m')
            = transl (xorF (a m) (S.psiM hc m (a m'))) *
                (S.psiM hc m * S.psiM hc m') := by rw [ha_eq, map_mul]
          _ = transl (a m) * transl (S.psiM hc m (a m')) *
                (S.psiM hc m * S.psiM hc m') := by rw [transl_xorF]
          _ = transl (a m) * (S.psiM hc m * transl (a m') * (S.psiM hc m)⁻¹) *
                (S.psiM hc m * S.psiM hc m') := by rw [hconj]
          _ = (transl (a m) * S.psiM hc m) * (transl (a m') * S.psiM hc m') := by
              group }
  refine ⟨Φ, ?_, ⟨fun m => ⟨a m, rfl⟩, ?_⟩⟩
  · intro m m' hΦ
    have hker : ∀ x : ↥M, Φ x = 1 → x = 1 := by
      intro x hx
      have h0 : (transl (a x) * S.psiM hc x) 0 = 0 := by
        rw [show transl (a x) * S.psiM hc x = Φ x from rfl, hx]
        rfl
      rw [Equiv.Perm.mul_apply, hF.apply_zero (S.psiM hc x) (S.psiM_mem_hexaM hc x),
        transl_apply, zero_xorF] at h0
      have hψx : S.psiM hc x = 1 := by
        have h : transl (a x) * S.psiM hc x = 1 := by
          rw [show transl (a x) * S.psiM hc x = Φ x from rfl]
          exact hx
        rw [h0, transl_zero, one_mul] at h
        exact h
      have hxV : x ∈ (blockU L).subgroupOf M :=
        Subgroup.mem_subgroupOf.mpr ((S.psiM_eq_one_iff_mem_blockU hc hC1 x).mp hψx)
      have hxK : x ∈ K := by
        have h := hdec x
        rw [h0, repM_zero, one_mul] at h
        rw [h]
        exact hkK x
      have hmem : x ∈ (blockU L).subgroupOf M ⊓ K := Subgroup.mem_inf.mpr ⟨hxV, hxK⟩
      rwa [hKbot, Subgroup.mem_bot] at hmem
    have h1 : Φ (m * m'⁻¹) = 1 := by
      rw [map_mul, map_inv, hΦ, mul_inv_cancel]
    have h2 : m * m'⁻¹ = 1 := hker (m * m'⁻¹) h1
    calc m = m * m'⁻¹ * m' := by group
      _ = 1 * m' := by rw [h2]
      _ = m' := by group
  · intro m b hmb
    have hm_eq : m = repM S hc b := Subtype.ext hmb
    have ha : a m = b := by
      refine decomp_unique S hD hc hC1 θ hθ3 hθne hψθ (hkK m) (Subgroup.one_mem _) ?_
      calc repM S hc (a m) * k m = m := (hdec m).symm
        _ = repM S hc b * 1 := by rw [hm_eq, mul_one]
    change transl (a m) * S.psiM hc m = transl b
    rw [ha, show S.psiM hc m = 1 by rw [hm_eq, psiM_repM S hC1 hc], mul_one]

theorem exists_split_mem (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    ∃ Φ : ↥M →* Equiv.Perm (Fin 64), Function.Injective Φ ∧
      (∀ m : ↥M, ∃ a : Fin 64, Φ m = transl a * S.psiM hc m) ∧
      (∀ (m : ↥M) (b : Fin 64), (m : G) = rep b → Φ m = transl b) ∧
      ∀ (b : Fin 64) (m : ↥M), ∃ m' : ↥M,
        Φ m' = transl b * S.psiM hc m ∧ S.psiM hc m' = S.psiM hc m := by
  obtain ⟨Φ, hinj, hform, hrep⟩ := exists_split S hF hD hc hC1
  refine ⟨Φ, hinj, hform, hrep, ?_⟩
  intro b m
  obtain ⟨a, ha⟩ := hform m
  let c : Fin 64 := xorF b a
  have hc_eq : xorF c a = b := by
    show xorF (xorF b a) a = b
    rw [xorF_assoc, xorF_self, xorF_zero]
  refine ⟨repM S hc c * m, ?_, ?_⟩
  · rw [map_mul, hrep (repM S hc c) c rfl, ha, ← mul_assoc, ← transl_xorF, hc_eq]
  · rw [map_mul, psiM_repM S hC1 hc, one_mul]

end CFSG.CGT.Hall82.Setting
