module

public import CFSG.CGT.Hall82.Transfer
public import CFSG.CGT.Hall82.Complement

public section

namespace CFSG.CGT.Hall82

theorem pow_two_eq_one_of_card_eq_two {G : Type} [Group G] {W : Subgroup G}
    (h : Nat.card W = 2) {w : G} (hw : w ∈ W) : w ^ 2 = 1 := by
  have h1 := pow_card_eq_one' (G := ↥W) (x := ⟨w, hw⟩)
  rw [h] at h1
  simpa using congrArg (fun z : ↥W => (z : G)) h1

theorem mem_zpowers_iff_of_mul_self {G : Type} [Group G] {x y : G} (hx : x * x = 1) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      change x ^ ((2 : ℤ) * m) = 1
      rw [zpow_mul, h2, one_zpow]
    · right
      change x ^ ((2 : ℤ) * m + 1) = x
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  · intro h
    rcases h with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers x

theorem card_sup_eq_two_mul_card_of_card_inf {G : Type} [Group G] [Finite G]
    {H J K V : Subgroup G} (hK : K ≤ Subgroup.normalizer (J : Set G))
    (hinf : K ⊓ J = V) (hsup : K ⊔ J = H) (hJV : Nat.card J = 2 * Nat.card V) :
    Nat.card H = 2 * Nat.card K := by
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := K) (K := J) hK
  rw [hsup, hinf, hJV] at h
  have h' : Nat.card H * Nat.card V = (2 * Nat.card K) * Nat.card V := by
    calc Nat.card H * Nat.card V = Nat.card K * (2 * Nat.card V) := h
      _ = (2 * Nat.card K) * Nat.card V := by ring
  exact Nat.mul_right_cancel Nat.card_pos h'

theorem relIndex_eq_two_of_card_eq_two_mul {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hKH : K ≤ H) (h : Nat.card H = 2 * Nat.card K) :
    K.relIndex H = 2 := by
  have h1 := Subgroup.relIndex_mul_card K H
  rw [inf_eq_left.mpr hKH, h] at h1
  exact Nat.mul_right_cancel Nat.card_pos h1

theorem card_eq_two_mul_card_of_relIndex_eq_two {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hKH : K ≤ H) (h : K.relIndex H = 2) :
    Nat.card H = 2 * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card K H
  rw [inf_eq_left.mpr hKH, h] at h1
  exact h1.symm

theorem card_sup_zpowers_of_not_mem_of_sq_eq_one {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {x : G} (hxK : x ∉ K) (hx2 : x * x = 1)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(K ⊔ Subgroup.zpowers x) = 2 * Nat.card K := by
  have hx1 : x ≠ 1 := fun h => hxK (h ▸ K.one_mem)
  have hzp : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := Subgroup.zpowers x) (K := K) hzp
  have hinf : Subgroup.zpowers x ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyz, hyK⟩ := Subgroup.mem_inf.mp hy
    rcases (mem_zpowers_iff_of_mul_self hx2).mp hyz with h1 | hx
    · rw [h1]
      exact Subgroup.one_mem ⊥
    · exact absurd (hx ▸ hyK) hxK
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1] at h
  rwa [sup_comm] at h

end CFSG.CGT.Hall82

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem centralizer_eq_pCoreOf_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2) :
    Subgroup.centralizer (L : Set G) =
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  change C = W
  have hcardW : Nat.card W = 2 := hcard
  obtain ⟨w, hwne, hwuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).mp hcardW
  apply le_antisymm
  · intro k hk
    have hkM : k ∈ M := S.centralizer_le hk
    have hconj : k * (w : G) * k⁻¹ ∈ W := S.conj_mem_pCoreOf_centralizer hkM w.2
    have hconj_ne : k * (w : G) * k⁻¹ ≠ 1 := by
      intro h1
      apply hwne
      apply Subtype.ext
      calc (w : G) = k⁻¹ * (k * (w : G) * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; simp
    have heq : (⟨k * (w : G) * k⁻¹, hconj⟩ : ↥W) = w :=
      hwuniq _ (fun h => hconj_ne (congrArg Subtype.val h))
    have hcommw : k * (w : G) = (w : G) * k := by
      have h := congrArg Subtype.val heq
      simp only [Subgroup.coe_mk] at h
      calc k * (w : G) = (k * (w : G) * k⁻¹) * k := by group
        _ = (w : G) * k := by rw [h]
    have hcommall : ∀ y ∈ W, k * y = y * k := by
      intro y hy
      by_cases hy1 : y = 1
      · subst y
        simp
      · have hyw : (⟨y, hy⟩ : ↥W) = w := hwuniq _ (by simpa using hy1)
        have hyG : y = (w : G) := congrArg Subtype.val hyw
        rw [hyG]
        exact hcommw
    exact S.mem_pCoreOf_of_commute hF hc hk hcommall
  · exact CFSG.LieType.BorelTits.pCoreOf_le 2 C

theorem inf_centralizer_blockU_eq_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC : Subgroup.centralizer (L : Set G) =
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    M ⊓ Subgroup.centralizer (blockU L : Set G) = CFSG.Open.pCoreOf 2 M := by
  rw [S.centralizer_blockU_eq]
  have hV : blockU L ≤ M :=
    (S.blockU_le_blockQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans S.le
  have hC' : Subgroup.centralizer (L : Set G) ≤ M := S.centralizer_le
  rw [inf_eq_right.mpr (sup_le hV hC'), hC, S.pCoreOf_eq hF hc]

theorem sq_eq_one_of_mem_pCoreOf_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {j : G} (hj : j ∈ CFSG.Open.pCoreOf 2 M) : j * j = 1 := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (S.exists_mul_of_mem_pCoreOf hF hc).mp hj
  have hv2 : v * v = 1 := by rw [← pow_two]; exact S.blockU_sq hv
  have hw2 : w * w = 1 := by
    rw [← pow_two]
    exact pow_two_eq_one_of_card_eq_two hcard hw
  have hcomm : v * w = w * v := S.commute_blockU_pCoreOf_centralizer hv hw
  calc (v * w) * (v * w) = v * (w * v) * w := by group
    _ = v * (v * w) * w := by rw [hcomm]
    _ = (v * v) * (w * w) := by group
    _ = 1 := by rw [hv2, hw2, one_mul]

theorem commute_of_mem_pCoreOf_centralizer_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {a b : G}
    (ha : a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hb : b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    a * b = b * a := by
  obtain ⟨w, -, hwuniq⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))))).mp
      hcard
  have hmem : ∀ x ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      x = 1 ∨ x = (w : G) := by
    intro x hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    · right
      have hxw : (⟨x, hx⟩ : ↥(CFSG.Open.pCoreOf 2
          (Subgroup.centralizer (L : Set G)))) = w := hwuniq _ (by simpa using h1)
      exact congrArg Subtype.val hxw
  rcases hmem a ha with rfl | rfl <;> rcases hmem b hb with rfl | rfl <;> simp

theorem commute_of_mem_pCoreOf_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {a b : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (hb : b ∈ CFSG.Open.pCoreOf 2 M) :
    a * b = b * a :=
  S.commute_of_mem_pCoreOf hF hc
    (fun x hx y hy => S.commute_of_mem_pCoreOf_centralizer_of_card_eq_two hF hc hcard hx hy)
    ha hb

theorem sq_eq_one_of_mem_conjSubgroup_pCoreOf_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {g x : G}
    (hx : x ∈ CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g) : x * x = 1 := by
  rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
  have h := S.sq_eq_one_of_mem_pCoreOf_of_card_eq_two hF hc hcard hx
  have h2 : g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g = x * x := by group
  have h3 : g⁻¹ * (1 : G) * g = 1 := by simp
  have := congrArg (fun z => g⁻¹ * z * g) h
  rwa [h2, h3] at this

theorem commute_of_mem_conjSubgroup_pCoreOf_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {g a b : G}
    (ha : a ∈ CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g)
    (hb : b ∈ CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g) :
    a * b = b * a := by
  rw [CFSG.Quasithin.mem_conjSubgroup_iff] at ha hb
  have hab := S.commute_of_mem_pCoreOf_of_card_eq_two hF hc hcard ha hb
  have h2 : g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g = a * b := by group
  have h3 : g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g = b * a := by group
  have := congrArg (fun z => g⁻¹ * z * g) hab
  rwa [h2, h3] at this

theorem conj_eq_self_of_mem_pCoreOf_centralizer_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {m : G} (hm : m ∈ M)
    {w : G} (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    m * w * m⁻¹ = w := by
  obtain ⟨w0, -, hw0uniq⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))))).mp
      hcard
  have hconj : m * w * m⁻¹ ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) :=
    S.conj_mem_pCoreOf_centralizer hm hw
  by_cases hw1 : w = 1
  · subst w
    simp
  · have hw_eq : (⟨w, hw⟩ : ↥(CFSG.Open.pCoreOf 2
        (Subgroup.centralizer (L : Set G)))) = w0 := hw0uniq _ (by simpa using hw1)
    have hconj_eq : (⟨m * w * m⁻¹, hconj⟩ : ↥(CFSG.Open.pCoreOf 2
        (Subgroup.centralizer (L : Set G)))) = w0 := by
      apply hw0uniq
      intro h
      apply hw1
      have hG : m * w * m⁻¹ = 1 := congrArg Subtype.val h
      calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
        _ = m⁻¹ * 1 * m := by rw [hG]
        _ = 1 := by simp
    have hwG : w = (w0 : G) := congrArg Subtype.val hw_eq
    have hconjG : m * w * m⁻¹ = (w0 : G) := congrArg Subtype.val hconj_eq
    exact hconjG.trans hwG.symm

theorem card_pCoreOf_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2) :
    Nat.card (CFSG.Open.pCoreOf 2 M) = 2 * Nat.card (blockU L) := by
  rw [S.card_pCoreOf hF hc, S.card_blockU, hcard]

theorem pCoreOf_le_M1 (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    CFSG.Open.pCoreOf 2 M ≤ S.M1 hc := by
  rw [S.M1_eq hF hc, S.pCoreOf_eq hF hc]
  exact sup_le
    ((S.blockU_le_blockQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans le_sup_left)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Subgroup.centralizer (L : Set G))).trans
      le_sup_right)

@[expose] noncomputable def piM1 (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    ↥(S.M1 hc) →* ↥hexaL :=
  ((S.psiM hc).comp (Subgroup.inclusion (S.M1_le hc))).codRestrict hexaL
    (fun x => by
      obtain ⟨hxM, hxψ⟩ := (S.mem_M1 hc).mp x.2
      have hsame : (⟨(x : G), S.M1_le hc x.2⟩ : ↥M) = ⟨(x : G), hxM⟩ := Subtype.ext rfl
      change S.psiM hc ⟨(x : G), S.M1_le hc x.2⟩ ∈ hexaL
      rwa [hsame])

theorem piM1_apply (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (x : ↥(S.M1 hc)) :
    (S.piM1 hc x : Equiv.Perm (Fin 64)) =
      S.psiM hc ⟨(x : G), S.M1_le hc x.2⟩ := rfl

theorem piM1_surjective (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    Function.Surjective (S.piM1 hc) := by
  intro y
  have hy : (y : Equiv.Perm (Fin 64)) ∈ S.psiSub hc L := by
    rw [S.psiSub_L hF hc]
    exact y.2
  rw [mem_psiSub S hc S.le] at hy
  obtain ⟨l, hlL, hlM, hψl⟩ := hy
  have hlM1 : l ∈ S.M1 hc := by
    refine (S.mem_M1 hc).mpr ⟨hlM, ?_⟩
    rw [hψl]
    exact y.2
  refine ⟨⟨l, hlM1⟩, ?_⟩
  apply Subtype.ext
  rw [piM1_apply]
  have hsame : (⟨l, S.M1_le hc hlM1⟩ : ↥M) = ⟨l, hlM⟩ := Subtype.ext rfl
  rw [hsame, hψl]

theorem piM1_ker (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC : Subgroup.centralizer (L : Set G) =
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    (S.piM1 hc).ker = (CFSG.Open.pCoreOf 2 M).subgroupOf (S.M1 hc) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hxval : S.psiM hc ⟨(x : G), S.M1_le hc x.2⟩ = 1 := by
      have h := congrArg (fun z : ↥hexaL => (z : Equiv.Perm (Fin 64))) hx
      rw [piM1_apply] at h
      simpa using h
    have hxCV : (x : G) ∈ Subgroup.centralizer (blockU L : Set G) :=
      (S.psiM_eq_one_iff hc ⟨(x : G), S.M1_le hc x.2⟩).mp hxval
    have hxM : (x : G) ∈ M := S.M1_le hc x.2
    have hmem : (x : G) ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hxM, hxCV⟩
    rwa [S.inf_centralizer_blockU_eq_pCoreOf hF hc hC] at hmem
  · intro hxJ
    have hxCV : (x : G) ∈ Subgroup.centralizer (blockU L : Set G) :=
      S.pCoreOf_le_centralizer hF hc hxJ
    have hxval : S.psiM hc ⟨(x : G), S.M1_le hc x.2⟩ = 1 :=
      (S.psiM_eq_one_iff hc ⟨(x : G), S.M1_le hc x.2⟩).mpr hxCV
    apply Subtype.ext
    rw [piM1_apply, hxval]
    rfl

theorem exists_compl_or_forall_mem_mod_M1 (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    (hC : Subgroup.centralizer (L : Set G) =
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    (∃ K : Subgroup G, blockU L ≤ K ∧ K ≤ S.M1 hc ∧
        K ⊓ CFSG.Open.pCoreOf 2 M = blockU L ∧
        K ⊔ CFSG.Open.pCoreOf 2 M = S.M1 hc) ∨
      ∀ h ∈ S.M1 hc, h * h ∈ blockU L → h ∈ CFSG.Open.pCoreOf 2 M := by
  classical
  let V : Subgroup G := blockU L
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  let H : Subgroup G := S.M1 hc
  have hVJ : V ≤ J := S.blockU_le_pCoreOf
  have hJH : J ≤ H := S.pCoreOf_le_M1 hF hc
  have hVn : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V :=
    fun h hh v hv => S.conj_mem_blockU (S.M1_le hc hh) hv
  have hJc : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ * j⁻¹ ∈ V := by
    intro h hh j hj
    obtain ⟨v, hv, w, hw, rfl⟩ := (S.exists_mul_of_mem_pCoreOf hF hc).mp hj
    have hhM : h ∈ M := S.M1_le hc hh
    have hconjV : h * v * h⁻¹ ∈ V := S.conj_mem_blockU hhM hv
    have hconjW : h * w * h⁻¹ = w :=
      S.conj_eq_self_of_mem_pCoreOf_centralizer_of_card_eq_two hF hc hcard hhM hw
    have hw2 : w * w = 1 := by rw [← pow_two]; exact pow_two_eq_one_of_card_eq_two hcard hw
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have heq : h * (v * w) * h⁻¹ * (v * w)⁻¹ = (h * v * h⁻¹) * v⁻¹ := by
      rw [mul_inv_rev]
      calc h * (v * w) * h⁻¹ * (w⁻¹ * v⁻¹)
          = (h * v * h⁻¹) * (h * w * h⁻¹) * (w⁻¹ * v⁻¹) := by group
        _ = (h * v * h⁻¹) * w * (w * v⁻¹) := by rw [hconjW, hwinv]
        _ = (h * v * h⁻¹) * (w * w) * v⁻¹ := by group
        _ = (h * v * h⁻¹) * v⁻¹ := by rw [hw2, mul_one]
    rw [heq]
    exact V.mul_mem hconjV (V.inv_mem hv)
  have hJV : Nat.card J = 2 * Nat.card V := S.card_pCoreOf_of_card_eq_two hF hc hcard
  exact exists_compl_or_forall_mem_mod (H := H) (J := J) (V := V)
    hVJ hJH hVn hJc hJV (S.piM1 hc) (S.piM1_surjective hF hc) (S.piM1_ker hF hc hC)
    (hexaL_t_mul_t hF) (hexaL_y_pow_four hF) (hexaL_ty_mul_ty hF)
    (hexaL_card_closure hF) (hexaL_odd hF) (hexaL_dvd hF) (hexaL_conj hF)

theorem exists_involution_of_conjSubgroup_not_mem_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    ∃ u : G,
      u ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ∧
      u ∈ M ∧ u ≠ 1 ∧ u * u = 1 ∧ u ∉ CFSG.Open.pCoreOf 2 M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  let Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W
  obtain ⟨w0, hw0ne, -⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).mp hcard
  have hw0sq : (w0 : G) * (w0 : G) = 1 := by
    rw [← pow_two]
    exact pow_two_eq_one_of_card_eq_two hcard w0.2
  have huY : g * (w0 : G) * g⁻¹ ∈ Y := by
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    simpa [mul_assoc] using w0.2
  have huM : g * (w0 : G) * g⁻¹ ∈ M := hgM huY
  have hu1 : g * (w0 : G) * g⁻¹ ≠ 1 := by
    intro h
    apply hw0ne
    apply Subtype.ext
    calc (w0 : G) = g⁻¹ * (g * (w0 : G) * g⁻¹) * g := by group
      _ = 1 := by rw [h]; simp
  have hu2 : (g * (w0 : G) * g⁻¹) * (g * (w0 : G) * g⁻¹) = 1 := by
    calc (g * (w0 : G) * g⁻¹) * (g * (w0 : G) * g⁻¹)
        = g * ((w0 : G) * (w0 : G)) * g⁻¹ := by group
      _ = 1 := by rw [hw0sq]; simp
  have huJ : g * (w0 : G) * g⁻¹ ∉ J := by
    intro hu
    have hgM' : g ∈ M :=
      S.mem_of_conj_mem hF hc hW2
        (fun a ha b hb => S.commute_of_mem_pCoreOf_centralizer_of_card_eq_two hF hc hcard ha hb)
        w0.2 (fun h => hw0ne (Subtype.ext h)) hu
    have hYW : Y = W := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro y hy
        rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hy
        have h := S.conj_mem_pCoreOf_centralizer hgM' hy
        convert h using 2 <;> group
      · rw [CFSG.CGT.Timmesfeld75.card_conjSubgroup]
    exact hgW hYW
  exact ⟨g * (w0 : G) * g⁻¹, huY, huM, hu1, hu2, huJ⟩

theorem false_of_M1_eq_M_of_dichotomy (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hdich : (∃ K : Subgroup G, blockU L ≤ K ∧ K ≤ S.M1 hc ∧
        K ⊓ CFSG.Open.pCoreOf 2 M = blockU L ∧
        K ⊔ CFSG.Open.pCoreOf 2 M = S.M1 hc) ∨
      ∀ h ∈ S.M1 hc, h * h ∈ blockU L → h ∈ CFSG.Open.pCoreOf 2 M)
    (hM1eq : S.M1 hc = M) : False := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  obtain ⟨u, -, huM, hu1, hu2, huJ⟩ :=
    S.exists_involution_of_conjSubgroup_not_mem_pCoreOf hF hc hW2 hcard hgM hgW
  have huM1 : u ∈ S.M1 hc := by rw [hM1eq]; exact huM
  have hcardW : Nat.card W = 2 := hcard
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardW
    omega
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
    fun a ha b hb => S.commute_of_mem_pCoreOf_centralizer_of_card_eq_two hF hc hcard ha hb
  rcases hdich with ⟨K, hVK, hKH, hKJ, hKJsup⟩ | hall
  · have hKM : K ≤ M := hM1eq ▸ hKH
    have hKnorm : K ≤ Subgroup.normalizer (J : Set G) :=
      fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hk)
    have hsup : K ⊔ J = M := by rw [hKJsup, hM1eq]
    have hJV : Nat.card J = 2 * Nat.card (blockU L) :=
      S.card_pCoreOf_of_card_eq_two hF hc hcard
    have hMcard : Nat.card M = 2 * Nat.card K :=
      card_sup_eq_two_mul_card_of_card_inf hKnorm hKJ hsup hJV
    have hKrel : K.relIndex M = 2 := relIndex_eq_two_of_card_eq_two_mul hKM hMcard
    obtain ⟨w, hwne, -⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).mp hcardW
    have hwJ : (w : G) ∈ J := S.pCoreOf_centralizer_le w.2
    have hw2 : (w : G) * (w : G) = 1 := by
      rw [← pow_two]
      exact pow_two_eq_one_of_card_eq_two hcardW w.2
    have hwK : (w : G) ∈ K :=
      S.mem_of_relIndex_eq_two hF hc hW2 hWab hW1 hKrel hKM hwJ
        (by rw [pow_two]; exact hw2)
    have hwKJ : (w : G) ∈ K ⊓ J := ⟨hwK, hwJ⟩
    rw [hKJ] at hwKJ
    have hwbot : (w : G) ∈ (⊥ : Subgroup G) := by
      rw [← S.blockU_inf_pCoreOf_centralizer]
      exact ⟨hwKJ, w.2⟩
    rw [Subgroup.mem_bot] at hwbot
    exact (fun h => hwne (Subtype.ext h)) hwbot
  · have huV : u * u ∈ blockU L := by rw [hu2]; exact (blockU L).one_mem
    exact huJ (hall u huM1 huV)

theorem M1_conj_iff_of_relIndex_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hrel : (S.M1 hc).relIndex M = 2) :
    ∀ m ∈ M, ∀ y : G, y ∈ S.M1 hc ↔ m * y * m⁻¹ ∈ S.M1 hc := by
  have hnormal : ((S.M1 hc).subgroupOf M).Normal :=
    Subgroup.normal_of_index_eq_two hrel
  intro m hm y
  constructor
  · intro hy
    have hyM := S.M1_le hc hy
    exact Subgroup.mem_subgroupOf.mp
      (hnormal.conj_mem ⟨y, hyM⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨m, hm⟩)
  · intro hy
    have hyM := S.M1_le hc hy
    have h1 := hnormal.conj_mem ⟨m * y * m⁻¹, hyM⟩ (Subgroup.mem_subgroupOf.mpr hy)
      ⟨m⁻¹, M.inv_mem hm⟩
    simpa [mul_assoc] using (Subgroup.mem_subgroupOf.mp h1)

theorem false_of_relIndex_M1_eq_two_of_dichotomy (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    (hdich : (∃ K : Subgroup G, blockU L ≤ K ∧ K ≤ S.M1 hc ∧
        K ⊓ CFSG.Open.pCoreOf 2 M = blockU L ∧
        K ⊔ CFSG.Open.pCoreOf 2 M = S.M1 hc) ∨
      ∀ h ∈ S.M1 hc, h * h ∈ blockU L → h ∈ CFSG.Open.pCoreOf 2 M)
    (hrel : (S.M1 hc).relIndex M = 2) : False := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  let H : Subgroup G := S.M1 hc
  have hC : C = W := S.centralizer_eq_pCoreOf_of_card_eq_two hF hc hcard
  have hcardW : Nat.card W = 2 := hcard
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardW
    omega
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
    fun a ha b hb => S.commute_of_mem_pCoreOf_centralizer_of_card_eq_two hF hc hcard ha hb
  have hW4 : ∀ w ∈ W, w ^ 4 = 1 := by
    intro w hw
    have h2 : w ^ 2 = 1 := pow_two_eq_one_of_card_eq_two hcardW hw
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, one_pow]
  have hJV : Nat.card J = 2 * Nat.card (blockU L) :=
    S.card_pCoreOf_of_card_eq_two hF hc hcard
  obtain ⟨g₁, -, hrelY, hnotle⟩ :=
    S.exists_conj hF hc hW2 hWab hW1 hW4 hrel (S.M1_le hc)
  let Y' : Subgroup G := CFSG.Quasithin.conjSubgroup J g₁
  let X : Subgroup G := Y' ⊓ M
  obtain ⟨x, hxX, hxnotM1⟩ := Set.not_subset.mp hnotle
  have hxX' : x ∈ Y' ⊓ M := hxX
  have hxY' : x ∈ Y' := (Subgroup.mem_inf.mp hxX').1
  have hxM : x ∈ M := (Subgroup.mem_inf.mp hxX').2
  have hx2 : x * x = 1 :=
    S.sq_eq_one_of_mem_conjSubgroup_pCoreOf_of_card_eq_two hF hc hcard hxY'
  have hxnothexa : S.psiM hc ⟨x, hxM⟩ ∉ hexaL := by
    intro hmem
    exact hxnotM1 ((S.mem_M1 hc).mpr ⟨hxM, hmem⟩)
  have hψx2 : S.psiM hc ⟨x, hxM⟩ * S.psiM hc ⟨x, hxM⟩ = 1 := by
    have hx2' : (⟨x, hxM⟩ : ↥M) * ⟨x, hxM⟩ = 1 := by
      apply Subtype.ext
      simpa using hx2
    calc S.psiM hc ⟨x, hxM⟩ * S.psiM hc ⟨x, hxM⟩
        = S.psiM hc (⟨x, hxM⟩ * ⟨x, hxM⟩) := (map_mul (S.psiM hc) _ _).symm
      _ = S.psiM hc 1 := by rw [hx2']
      _ = 1 := map_one _
  have hfix8 : Nat.card (fixPts {S.psiM hc ⟨x, hxM⟩}) ≤ 8 :=
    hF.fixPts_le_8 _ (S.psiM_mem_hexaM hc ⟨x, hxM⟩) hxnothexa hψx2
  have hVfix : Nat.card ↥(blockU L ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G)) ≤ 8 := by
    rw [centralizer_zpowers_eq_centralizer_singleton x,
      S.card_inf_centralizer_singleton hc ⟨x, hxM⟩]
    exact hfix8
  have hWfix : Nat.card ↥(W ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G)) ≤ 2 := by
    calc Nat.card ↥(W ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G))
        ≤ Nat.card W := Subgroup.card_le_of_le inf_le_left
      _ = 2 := hcardW
  have hJfix : Nat.card ↥(J ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G)) ≤ 16 := by
    have hA : Subgroup.zpowers x ≤ M := Subgroup.zpowers_le.mpr hxM
    have h := S.card_pCoreOf_inf_centralizer hF hc (A := Subgroup.zpowers x) hA
    rw [h]
    exact (Nat.mul_le_mul hVfix hWfix).trans (by norm_num)
  have hXJ_le : X ⊓ J ≤ J ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro y hy
    obtain ⟨hyX, hyJ⟩ := Subgroup.mem_inf.mp hy
    have hyY' : y ∈ CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g₁ :=
      (Subgroup.mem_inf.mp hyX).1
    have hxY'' : x ∈ CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g₁ := hxY'
    refine Subgroup.mem_inf.mpr ⟨hyJ, ?_⟩
    rw [centralizer_zpowers_eq_centralizer_singleton x, Subgroup.mem_centralizer_iff]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact S.commute_of_mem_conjSubgroup_pCoreOf_of_card_eq_two (g := g₁) hF hc hcard hxY'' hyY'
  have hXJcard : Nat.card ↥(X ⊓ J) ≤ 16 :=
    (Subgroup.card_le_of_le hXJ_le).trans hJfix
  have hJeq : Nat.card J = 128 := by
    rw [hJV, S.card_blockU]
  have hXcard_le : Nat.card J ≤ 2 * Nat.card X := S.card_le_two_mul_card_inf hrelY
  have hXcard : 64 ≤ Nat.card X := by omega
  have hXM : X ≤ M := inf_le_right
  have hrelX : (X ⊓ H).relIndex X ≤ 2 := by
    have h1 : (X ⊓ H).relIndex X = H.relIndex X := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    exact (Subgroup.relIndex_le_of_le_right hXM Subgroup.index_ne_zero_of_finite).trans
      (le_of_eq hrel)
  have hinfcard : 32 ≤ Nat.card ↥(X ⊓ H) := by
    have hmul := Subgroup.relIndex_mul_card (X ⊓ H) X
    rw [inf_eq_left.mpr (inf_le_left : X ⊓ H ≤ X)] at hmul
    have hle : Nat.card X ≤ 2 * Nat.card ↥(X ⊓ H) := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ hrelX
    omega
  rcases hdich with ⟨K, hVK, hKH, hKJ, hKJsup⟩ | hall
  ·
    have hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J :=
      fun h hh j hj => S.conj_mem_pCoreOf (S.M1_le hc hh) hj
    have hXne : ∀ N : Subgroup ↥hexaL, N.index ≠ 2 := index_ne_two_hexaL hF
    have hKnormal : ∀ m ∈ M, K.map (MulAut.conj m).toMonoidHom = K := by
      intro m hm
      refine conj_eq_of_inf_eq_of_sup_eq (H := H) (J := J) (V := blockU L) (K := K)
        S.blockU_le_pCoreOf (S.pCoreOf_le_M1 hF hc) hJn
        (S.piM1 hc) (S.piM1_surjective hF hc) (S.piM1_ker hF hc hC) hXne hJV
        hVK hKH hKJ hKJsup ?_ ?_ ?_
      · intro y
        exact S.M1_conj_iff_of_relIndex_eq_two hF hc hrel m hm y
      · intro y
        constructor
        · intro hy
          exact S.conj_mem_pCoreOf hm hy
        · intro hy
          have h := S.conj_mem_pCoreOf (M.inv_mem hm) hy
          simpa [mul_assoc] using h
      · intro y
        constructor
        · intro hy
          exact S.conj_mem_blockU hm hy
        · intro hy
          have h := S.conj_mem_blockU (M.inv_mem hm) hy
          simpa [mul_assoc] using h
    have hxnorm : x ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hKnormal x hxM)
    have hxnotK : x ∉ K := fun hxK => hxnotM1 (hKH hxK)
    let N : Subgroup G := K ⊔ Subgroup.zpowers x
    have hNcard : Nat.card N = 2 * Nat.card K :=
      card_sup_zpowers_of_not_mem_of_sq_eq_one hxnotK hx2 hxnorm
    have hKnorm : K ≤ Subgroup.normalizer (J : Set G) :=
      fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (S.M1_le hc (hKH hk))
    have hHcard : Nat.card H = 2 * Nat.card K :=
      card_sup_eq_two_mul_card_of_card_inf hKnorm hKJ hKJsup hJV
    have hMcard : Nat.card M = 2 * Nat.card H :=
      card_eq_two_mul_card_of_relIndex_eq_two (S.M1_le hc) hrel
    have hNleM : N ≤ M := by
      refine sup_le ?_ ?_
      · intro k hk
        exact S.M1_le hc (hKH hk)
      · exact Subgroup.zpowers_le.mpr hxM
    have hMN : Nat.card M = 2 * Nat.card N := by
      rw [hMcard, hHcard, hNcard]
    have hNrel : N.relIndex M = 2 := relIndex_eq_two_of_card_eq_two_mul hNleM hMN
    obtain ⟨w, hwne, -⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).mp hcardW
    have hwJ : (w : G) ∈ J := S.pCoreOf_centralizer_le w.2
    have hw2 : (w : G) ^ 2 = 1 := pow_two_eq_one_of_card_eq_two hcardW w.2
    have hwN : (w : G) ∈ N :=
      S.mem_of_relIndex_eq_two hF hc hW2 hWab hW1 hNrel hNleM hwJ hw2
    have hwK : (w : G) ∈ K := by
      have hzp : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) :=
        Subgroup.zpowers_le.mpr hxnorm
      have hsupN : N = K ⊔ Subgroup.zpowers x := rfl
      rw [hsupN] at hwN
      obtain ⟨k, hkK, z, hz, hkz⟩ :=
        (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := K) hzp).mp hwN
      rcases (mem_zpowers_iff_of_mul_self hx2).mp hz with hz1 | hzx
      · rw [hz1, mul_one] at hkz
        rw [hkz]
        exact hkK
      · exfalso
        have hkM1 : k ∈ H := hKH hkK
        have hwM1 : (w : G) ∈ H := by
          rw [show H = L ⊔ C from S.M1_eq hF hc, hC]
          exact Subgroup.mem_sup_right w.2
        have hkx : (w : G) = k * x := by rw [hkz, hzx]
        have hxM1 : x ∈ H := by
          have hxeq : x = k⁻¹ * (w : G) := by
            calc x = k⁻¹ * (k * x) := by group
              _ = k⁻¹ * (w : G) := by rw [hkx]
          rw [hxeq]
          exact H.mul_mem (H.inv_mem hkM1) hwM1
        exact hxnotM1 hxM1
    have hwKJ : (w : G) ∈ K ⊓ J := ⟨hwK, hwJ⟩
    rw [hKJ] at hwKJ
    have hwbot : (w : G) ∈ (⊥ : Subgroup G) := by
      rw [← S.blockU_inf_pCoreOf_centralizer]
      exact ⟨hwKJ, w.2⟩
    rw [Subgroup.mem_bot] at hwbot
    exact (fun h => hwne (Subtype.ext h)) hwbot
  ·
    have hXHJ : X ⊓ H ≤ J := by
      intro y hy
      obtain ⟨hyX, hyH⟩ := Subgroup.mem_inf.mp hy
      have hyY' : y ∈ CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g₁ :=
        (Subgroup.mem_inf.mp hyX).1
      have hy2 : y * y = 1 :=
        S.sq_eq_one_of_mem_conjSubgroup_pCoreOf_of_card_eq_two (g := g₁) hF hc hcard hyY'
      have hyV : y * y ∈ blockU L := by rw [hy2]; exact (blockU L).one_mem
      exact hall y hyH hyV
    have hcardle : Nat.card ↥(X ⊓ H) ≤ Nat.card ↥(X ⊓ J) :=
      Subgroup.card_le_of_le (le_inf inf_le_left hXHJ)
    omega

theorem false_of_card_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) : False := by
  classical
  have hC := S.centralizer_eq_pCoreOf_of_card_eq_two hF hc hcard
  have hdich := S.exists_compl_or_forall_mem_mod_M1 hF hc hcard hC
  rcases S.relIndex_M1 hF hc with hrel1 | hrel2
  · exact S.false_of_M1_eq_M_of_dichotomy hF hc hW2 hcard hgM hgW hdich
      (S.M1_eq_of_relIndex hc hrel1)
  · exact S.false_of_relIndex_M1_eq_two_of_dichotomy hF hc hW2 hcard hdich hrel2

end CFSG.CGT.Hall82.Setting
