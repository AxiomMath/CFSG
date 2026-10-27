module

public import CFSG.CGT.Hall82.Transfer
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic

public section

namespace CFSG.CGT.Hall82

variable {G : Type} [Group G]

theorem conj_pow_eq_of_conj_eq {W : Subgroup G} {a c : G}
    (hcW : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (h : ∀ w ∈ W, a * w * a⁻¹ = c * w * c⁻¹) :
    ∀ n : ℕ, ∀ w ∈ W, a ^ n * w * (a ^ n)⁻¹ = c ^ n * w * (c ^ n)⁻¹ := by
  have hcWpow : ∀ n : ℕ, ∀ w ∈ W, c ^ n * w * (c ^ n)⁻¹ ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      have h1 := ih w hw
      have h2 : c ^ (n + 1) * w * (c ^ (n + 1))⁻¹ =
          c * (c ^ n * w * (c ^ n)⁻¹) * c⁻¹ := by group
      rw [h2]
      exact hcW _ h1
  intro n
  induction n with
  | zero => intro w hw; simp
  | succ n ih =>
    intro w hw
    have hz := hcWpow n w hw
    calc a ^ (n + 1) * w * (a ^ (n + 1))⁻¹
        = a * (a ^ n * w * (a ^ n)⁻¹) * a⁻¹ := by group
      _ = a * (c ^ n * w * (c ^ n)⁻¹) * a⁻¹ := by rw [ih w hw]
      _ = c * (c ^ n * w * (c ^ n)⁻¹) * c⁻¹ := h _ hz
      _ = c ^ (n + 1) * w * (c ^ (n + 1))⁻¹ := by group

theorem mul_comm_of_mul_self_eq_one {W : Subgroup G} (h : ∀ w ∈ W, w * w = 1)
    {a b : G} (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a := by
  have ha' : a⁻¹ = a := (eq_inv_of_mul_eq_one_right (h a ha)).symm
  have hb' : b⁻¹ = b := (eq_inv_of_mul_eq_one_right (h b hb)).symm
  have hab : (a * b) * (a * b) = 1 := h (a * b) (W.mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right hab
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem mul_inv_mem_of_relIndex_eq_two {H K : Subgroup G} (h : H.relIndex K = 2)
    {x y : G} (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) :
    x * y⁻¹ ∈ H := by
  have hy'H : y⁻¹ ∉ H := fun h' => hyH (by simpa using H.inv_mem h')
  have hidx : (H.subgroupOf K).index = 2 := h
  have hiff : ((⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K ↔
      (⟨y⁻¹, K.inv_mem hy⟩ : ↥K) ∈ H.subgroupOf K) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun h' => absurd h' hxH, fun h' => absurd h' hy'H⟩
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx
    (a := (⟨x, hx⟩ : ↥K)) (b := (⟨y⁻¹, K.inv_mem hy⟩ : ↥K))).mpr hiff
  simpa [Subgroup.mem_subgroupOf] using hmem

theorem coprime_two_relIndex_of_forall_isPGroup_le [Finite G] {C W : Subgroup G}
    (hW : W ≤ C) (hW2 : IsPGroup 2 W)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ C → Q ≤ W) :
    Nat.Coprime 2 (W.relIndex C) := by
  classical
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥C)
  have hP2 : IsPGroup 2 ((P : Subgroup ↥C).map C.subtype) := P.isPGroup'.map C.subtype
  have hPle : (P : Subgroup ↥C) ≤ W.subgroupOf C := by
    intro x hx
    exact hmax _ hP2 (Subgroup.map_subtype_le _) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hWc2 : IsPGroup 2 (W.subgroupOf C) := hW2.comap_subtype (K := C)
  have hPeq : W.subgroupOf C = (P : Subgroup ↥C) := P.is_maximal' hWc2 hPle
  have hdvd : ¬ 2 ∣ (W.subgroupOf C).index := by
    rw [hPeq]
    exact P.not_dvd_index
  have hcop : Nat.Coprime 2 (W.subgroupOf C).index :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr hdvd
  simpa [Subgroup.relIndex] using hcop

end CFSG.CGT.Hall82

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem commute_of_mem_L_pCoreOf_centralizer (S : Setting G M L) {l w : G}
    (hl : l ∈ L)
    (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    l * w = w * l := by
  have hwC : w ∈ Subgroup.centralizer (L : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
  exact Subgroup.mem_centralizer_iff.mp hwC l hl

theorem pow_relIndex_pCoreOf_centralizer_mem (S : Setting G M L) {c : G}
    (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    c ^ (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))).relIndex
        (Subgroup.centralizer (L : Set G)) ∈
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  have hWsub : W.subgroupOf C = CFSG.pCore 2 ↥C := by
    simpa [W, C] using CFSG.openPCoreOf_subgroupOf 2 C
  haveI : (W.subgroupOf C).Normal := by
    rw [hWsub]
    infer_instance
  have hpow := Subgroup.pow_index_mem (W.subgroupOf C) (⟨c, hc⟩ : ↥C)
  simpa [W, C, Subgroup.relIndex, Subgroup.mem_subgroupOf] using hpow

theorem coprime_two_relIndex_pCoreOf_centralizer (S : Setting G M L)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    Nat.Coprime 2 ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))).relIndex
      (Subgroup.centralizer (L : Set G))) :=
  coprime_two_relIndex_of_forall_isPGroup_le
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hW2

theorem le_M1_iff_psiSub_le_hexaL (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A : Subgroup G}
    (hA : A ≤ M) :
    A ≤ S.M1 hc ↔ S.psiSub hc A ≤ hexaL := by
  constructor
  · intro hAM1 x hx
    rw [mem_psiSub S hc hA] at hx
    obtain ⟨a, ha, -, rfl⟩ := hx
    obtain ⟨hxM, hmem⟩ := (mem_M1 S hc).mp (hAM1 ha)
    exact hmem
  · intro hpsi a ha
    rw [mem_M1 S hc]
    exact ⟨hA ha, hpsi (by
      rw [mem_psiSub S hc hA]
      exact ⟨a, ha, hA ha, rfl⟩)⟩

theorem le_centralizer_pCoreOf_centralizer_of_not_le_M1 (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    {X : Subgroup G} (hXM : X ≤ M) (hX2 : IsPGroup 2 X)
    (hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hXM1 : ¬ X ≤ S.M1 hc)
    (hXcard : Nat.card (CFSG.Open.pCoreOf 2 M) ≤ 2 * Nat.card X) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≤
      Subgroup.centralizer (X : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let CA : Subgroup G := Subgroup.centralizer (X : Set G)
  let CV : Subgroup G := Subgroup.centralizer (blockU L : Set G)
  let psiX : Subgroup (Equiv.Perm (Fin 64)) := S.psiSub hc X
  have hXJ : X ⊓ CV ≤ CFSG.Open.pCoreOf 2 M := by
    refine S.le_pCoreOf_of_le_centralizer hF hc hW2 ?_ ?_ ?_
    · exact hX2.to_inf_left
    · exact inf_le_left.trans hXM
    · exact inf_le_right
  have hXCA : X ⊓ CV ≤ CA := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hXab y hy.1 a ha).symm
  have hXle : X ⊓ CV ≤ CFSG.Open.pCoreOf 2 M ⊓ CA := le_inf hXJ hXCA
  have hXcard_psi : Nat.card X = Nat.card ↥(X ⊓ CV) * Nat.card psiX := by
    simpa [psiX, CV] using S.card_psiSub hc hXM
  have hJCA : Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) =
      Nat.card ↥(blockU L ⊓ CA) * Nat.card ↥(W ⊓ CA) := by
    simpa [CA, W, C] using S.card_pCoreOf_inf_centralizer hF hc hXM
  have hVCA : Nat.card ↥(blockU L ⊓ CA) = Nat.card (fixPts psiX) := by
    simpa [CA, psiX] using S.card_inf_centralizer hc hXM
  have hpsiNot : ¬ psiX ≤ hexaL := by
    intro h
    exact hXM1 ((S.le_M1_iff_psiSub_le_hexaL hc hXM).mpr h)
  have hle32 : Nat.card psiX * Nat.card (fixPts psiX) ≤ 32 :=
    hF.le_32_of_not_le psiX (S.psiSub_le_hexaM hc X) (S.isPGroup_psiSub hc hX2)
      hpsiNot
  have hXle32 : Nat.card X ≤ 32 * Nat.card ↥(W ⊓ CA) := by
    calc Nat.card X = Nat.card ↥(X ⊓ CV) * Nat.card psiX := hXcard_psi
      _ ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) * Nat.card psiX :=
          Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hXle)
      _ = (Nat.card ↥(blockU L ⊓ CA) * Nat.card ↥(W ⊓ CA)) * Nat.card psiX := by
          rw [hJCA]
      _ = (Nat.card (fixPts psiX) * Nat.card ↥(W ⊓ CA)) * Nat.card psiX := by
          rw [hVCA]
      _ = (Nat.card psiX * Nat.card (fixPts psiX)) * Nat.card ↥(W ⊓ CA) := by ring
      _ ≤ 32 * Nat.card ↥(W ⊓ CA) := Nat.mul_le_mul_right _ hle32
  have hJcard : Nat.card (CFSG.Open.pCoreOf 2 M) = 64 * Nat.card W := by
    simpa [W, C] using S.card_pCoreOf hF hc
  have h64 : 64 * Nat.card W ≤ 64 * Nat.card ↥(W ⊓ CA) := by
    calc 64 * Nat.card W = Nat.card (CFSG.Open.pCoreOf 2 M) := hJcard.symm
      _ ≤ 2 * Nat.card X := hXcard
      _ ≤ 2 * (32 * Nat.card ↥(W ⊓ CA)) := Nat.mul_le_mul_left 2 hXle32
      _ = 64 * Nat.card ↥(W ⊓ CA) := by ring
  have h64eq : 64 * Nat.card ↥(W ⊓ CA) = 64 * Nat.card W :=
    le_antisymm (Nat.mul_le_mul_left 64 (Subgroup.card_le_of_le inf_le_left)) h64
  have hw_eq : Nat.card ↥(W ⊓ CA) = Nat.card W :=
    Nat.mul_left_cancel (by norm_num : 0 < 64) h64eq
  have hWCA : W ⊓ CA = W := by
    apply Subgroup.eq_of_le_of_card_ge (H := W ⊓ CA) (K := W) inf_le_left
    rw [hw_eq]
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hw' : w ∈ W ⊓ CA := by rw [hWCA]; exact hw
  exact Subgroup.mem_centralizer_iff.mp hw'.2 x hx

theorem mem_centralizer_of_mem_M1 (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1)
    {x : G} (hxM1 : x ∈ S.M1 hc) {k : ℕ} (hxk : x ^ (2 ^ k) = 1) :
    x ∈ Subgroup.centralizer
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let H : Subgroup G := Subgroup.centralizer (W : Set G)
  have hWleH : W ≤ H := fun w hw => by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact mul_comm_of_mul_self_eq_one hWel hv hw
  have hLleH : L ≤ H := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (commute_of_mem_L_pCoreOf_centralizer S hl
      (by simpa [W, C] using hw)).symm
  have hxLC : x ∈ L ⊔ C := by
    have h := hxM1
    rw [S.M1_eq hF hc] at h
    exact h
  have hCN : C ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G)
  obtain ⟨l, hl, c, hcC, hxlc⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := L) (K := C) hCN).mp hxLC
  have hlc : Commute l c := Subgroup.mem_centralizer_iff.mp hcC l hl
  have hpow : l ^ (2 ^ k) * c ^ (2 ^ k) = 1 := by
    rw [hxlc, hlc.mul_pow] at hxk
    exact hxk
  have hc_pow_eq : c ^ (2 ^ k) = (l ^ (2 ^ k))⁻¹ :=
    eq_inv_of_mul_eq_one_right hpow
  have hc_pow_H : c ^ (2 ^ k) ∈ H := by
    rw [hc_pow_eq]
    exact H.inv_mem (hLleH (L.pow_mem hl _))
  have hc_r_H : c ^ W.relIndex C ∈ H :=
    hWleH (by simpa [W, C] using S.pow_relIndex_pCoreOf_centralizer_mem hcC)
  have hcop : Nat.Coprime (2 ^ k) (W.relIndex C) :=
    (S.coprime_two_relIndex_pCoreOf_centralizer hW2).pow_left k
  have hcH : c ∈ H :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L3213.mem_of_pow_mem_of_pow_mem
      hcop hc_pow_H hc_r_H
  have hxH : x ∈ H := by
    rw [hxlc]
    exact H.mul_mem (hLleH hl) hcH
  simpa [H, W, C] using hxH

theorem commute_of_pow_two_pow_eq_one (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1)
    {x : G} (hx : x ∈ M) {k : ℕ} (hxk : x ^ (2 ^ k) = 1)
    {w : G} (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    x * w = w * x := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let H : Subgroup G := Subgroup.centralizer (W : Set G)
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
    fun a ha b hb => mul_comm_of_mul_self_eq_one (by simpa [W, C] using hWel) ha hb
  have hW1 : W ≠ ⊥ := by
    intro h
    have h1 : Nat.card W = 4 := by simpa [W, C] using hcard
    rw [h] at h1
    simp at h1
  have hW4 : ∀ v ∈ W, v ^ 4 = 1 := by
    intro v hv
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two]
    rw [hWel v (by simpa [W, C] using hv)]
    simp
  have hLleH : L ≤ H := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (commute_of_mem_L_pCoreOf_centralizer S hl
      (by simpa [W, C] using hv)).symm
  have hWleH : W ≤ H := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact mul_comm_of_mul_self_eq_one (by simpa [W, C] using hWel) hu hv
  have hcop : Nat.Coprime (2 ^ k) (W.relIndex C) :=
    (S.coprime_two_relIndex_pCoreOf_centralizer hW2).pow_left k
  rcases S.relIndex_M1 hF hc with hrel | hrel
  · have hxM1 : x ∈ S.M1 hc := by
      rw [S.M1_eq_of_relIndex hc hrel]
      exact hx
    have hxH := S.mem_centralizer_of_mem_M1 hF hc hW2 hWel hxM1 hxk
    exact (Subgroup.mem_centralizer_iff.mp (by simpa [H, W, C] using hxH) w
      (by simpa [W, C] using hw)).symm
  · obtain ⟨g, -, hrelX, hnotM1⟩ :=
      S.exists_conj hF hc hW2 hWab hW1 hW4 hrel (S.M1_le hc)
    let J : Subgroup G := CFSG.Open.pCoreOf 2 M
    let X : Subgroup G := CFSG.Quasithin.conjSubgroup J g ⊓ M
    have hXM : X ≤ M := inf_le_right
    have hXJg : X ≤ CFSG.Quasithin.conjSubgroup J g := inf_le_left
    have hX2 : IsPGroup 2 X := by
      have h1 : IsPGroup 2 (CFSG.Quasithin.conjSubgroup J g) := by
        rw [show CFSG.Quasithin.conjSubgroup J g =
          J.map (MulAut.conj g⁻¹).toMonoidHom from rfl]
        exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).map _
      exact h1.to_inf_left
    have hJab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a :=
      fun a ha b hb => S.commute_of_mem_pCoreOf hF hc hWab ha hb
    have hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
      intro a ha b hb
      have ha' : g * a * g⁻¹ ∈ J :=
        CFSG.Quasithin.mem_conjSubgroup_iff.mp (hXJg ha)
      have hb' : g * b * g⁻¹ ∈ J :=
        CFSG.Quasithin.mem_conjSubgroup_iff.mp (hXJg hb)
      have hab := hJab _ ha' _ hb'
      have hconj : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
        calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          _ = (g * b * g⁻¹) * (g * a * g⁻¹) := hab
          _ = g * (b * a) * g⁻¹ := by group
      have := congrArg (fun z => g⁻¹ * z * g) hconj
      simpa [mul_assoc] using this
    have hXcardJ : Nat.card J ≤ 2 * Nat.card X := by
      simpa [J, X] using S.card_le_two_mul_card_inf hrelX
    have hWleCX : W ≤ Subgroup.centralizer (X : Set G) :=
      S.le_centralizer_pCoreOf_centralizer_of_not_le_M1 hF hc hW2 hXM hX2 hXab hnotM1
        hXcardJ
    obtain ⟨x₀, hx0X, hx0M1⟩ := Set.not_subset.mp hnotM1
    have hx0M : x₀ ∈ M := hXM hx0X
    have hx0H : x₀ ∈ H := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ W := by simpa [W, C] using hv
      exact (Subgroup.mem_centralizer_iff.mp (hWleCX hv') x₀ hx0X).symm
    by_cases hxM1 : x ∈ S.M1 hc
    · have hxH := S.mem_centralizer_of_mem_M1 hF hc hW2 hWel hxM1 hxk
      exact (Subgroup.mem_centralizer_iff.mp (by simpa [H, W, C] using hxH) w
        (by simpa [W, C] using hw)).symm
    · have hxx0 : x * x₀⁻¹ ∈ S.M1 hc :=
        mul_inv_mem_of_relIndex_eq_two hrel hx hx0M hxM1 hx0M1
      have hxLC : x * x₀⁻¹ ∈ L ⊔ C := by
        have h := hxx0
        rw [S.M1_eq hF hc] at h
        exact h
      have hCN : C ≤ Subgroup.normalizer (L : Set G) :=
        Subgroup.centralizer_le_normalizer (L : Set G)
      obtain ⟨l, hl, c, hcC, hdecomp⟩ :=
        (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := L) (K := C)
          hCN).mp hxLC
      have hcM : c ∈ M := S.centralizer_le hcC
      have hx_eq : x = (l * c) * x₀ := by
        calc x = (x * x₀⁻¹) * x₀ := by group
          _ = (l * c) * x₀ := by rw [hdecomp]
      have hact : ∀ v ∈ W, x * v * x⁻¹ = c * v * c⁻¹ := by
        intro v hv
        have hcw : c * v * c⁻¹ ∈ W :=
          S.conj_mem_pCoreOf_centralizer hcM (by simpa [W, C] using hv)
        have hl_comm : l * (c * v * c⁻¹) = (c * v * c⁻¹) * l :=
          commute_of_mem_L_pCoreOf_centralizer S hl hcw
        calc x * v * x⁻¹ = ((l * c) * x₀) * v * x₀⁻¹ * (l * c)⁻¹ := by rw [hx_eq]; group
          _ = (l * c) * (x₀ * v * x₀⁻¹) * (l * c)⁻¹ := by group
          _ = (l * c) * v * (l * c)⁻¹ := by
              rw [show x₀ * v * x₀⁻¹ = v from by
                have hvX : v ∈ Subgroup.centralizer (X : Set G) := hWleCX (by
                  simpa [W, C] using hv)
                calc x₀ * v * x₀⁻¹ = v * x₀ * x₀⁻¹ := by
                      rw [Subgroup.mem_centralizer_iff.mp hvX x₀ hx0X]
                  _ = v := by group]
          _ = l * (c * v * c⁻¹) * l⁻¹ := by group
          _ = (c * v * c⁻¹) * l * l⁻¹ := by rw [hl_comm]
          _ = c * v * c⁻¹ := by group
      have hc_pow_conj : ∀ v ∈ W, c ^ (2 ^ k) * v * (c ^ (2 ^ k))⁻¹ = v := by
        intro v hv
        have hkey := conj_pow_eq_of_conj_eq (W := W) (a := x) (c := c)
          (fun u hu => S.conj_mem_pCoreOf_centralizer hcM (by simpa [W, C] using hu))
          hact (2 ^ k) v hv
        rw [hxk] at hkey
        simpa using hkey.symm
      have hc_pow_H : c ^ (2 ^ k) ∈ H := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have h := hc_pow_conj v hv
        have h' : c ^ (2 ^ k) * v = v * c ^ (2 ^ k) := by
          calc c ^ (2 ^ k) * v =
              (c ^ (2 ^ k) * v * (c ^ (2 ^ k))⁻¹) * c ^ (2 ^ k) := by group
            _ = v * c ^ (2 ^ k) := by rw [h]
        exact h'.symm
      have hc_r_H : c ^ W.relIndex C ∈ H :=
        hWleH (by simpa [W, C] using S.pow_relIndex_pCoreOf_centralizer_mem hcC)
      have hcH : c ∈ H :=
        CFSG.Quasithin.EmptyFaithfulMultiple.L3213.mem_of_pow_mem_of_pow_mem
          hcop hc_pow_H hc_r_H
      have hxH : x ∈ H := by
        rw [hx_eq]
        exact H.mul_mem (H.mul_mem (hLleH hl) hcH) hx0H
      exact (Subgroup.mem_centralizer_iff.mp hxH w
        (by simpa [W, C] using hw)).symm

theorem commute_of_isPGroup (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1)
    {P : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup 2 P)
    {x : G} (hx : x ∈ P)
    {w : G} (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    x * w = w * x := by
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hxpow : x ^ (2 ^ n) = 1 := by
    simpa using congrArg Subtype.val hn
  exact S.commute_of_pow_two_pow_eq_one hF hc hW2 hcard hWel (hPM hx) hxpow hw

end CFSG.CGT.Hall82.Setting
