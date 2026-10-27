module

public import CFSG.CGT.Hall82.Psi
public import CFSG.CGT.Hall82.Tight
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.CGT.Hall82

theorem le_of_forall_map_conj_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M J R : Subgroup G} (hJM : J ≤ M)
    (hNJ : Subgroup.normalizer (J : Set G) ≤ M) (hJp : IsPGroup p J)
    (hRp : IsPGroup p R) (hJR : J ≤ Subgroup.normalizer (R : Set G))
    (hA : ∀ x ∈ R ⊔ J, J.map (MulAut.conj x).toMonoidHom ≤ (R ⊔ J) ⊓ M →
      J.map (MulAut.conj x).toMonoidHom = J) :
    R ≤ M := by
  classical
  let H : Subgroup G := R ⊔ J
  let K : Subgroup G := H ⊓ M
  have hHp : IsPGroup p H := by
    have h := hJp.to_sup_of_normal_right' hRp hJR
    rw [sup_comm] at h
    exact h
  have hJK : J ≤ K := le_inf le_sup_right hJM
  by_contra hRnot
  have hKne : K ≠ H := by
    intro hKH
    apply hRnot
    have hHM : H ≤ M := by
      have hKleM : K ≤ M := inf_le_right
      rwa [hKH] at hKleM
    exact le_sup_left.trans hHM
  have hKlt : K.subgroupOf H < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    exact hKne (by
      have hmap := congrArg (Subgroup.map H.subtype) htop
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left : K ≤ H), Subgroup.map_top,
        Subgroup.range_subtype] at hmap
      exact hmap)
  letI : Group.IsNilpotent H := hHp.isNilpotent
  have hnc : NormalizerCondition H :=
    Group.normalizerCondition_of_isNilpotent (G := H)
  have hgrowth : K.subgroupOf H < Subgroup.normalizer (K.subgroupOf H : Set H) :=
    hnc _ hKlt
  obtain ⟨x, hxN, hxnot⟩ := SetLike.exists_of_lt hgrowth
  have hxnormK : ((x : H) : G) ∈ Subgroup.normalizer (K : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (K : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq (show K ≤ H from inf_le_left)]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  let A : Subgroup G := J.map (MulAut.conj ((x : H) : G)).toMonoidHom
  have hAprod : A ≤ (R ⊔ J) ⊓ M := by
    intro a ha
    rw [show A = J.map (MulAut.conj ((x : H) : G)).toMonoidHom from rfl,
      Subgroup.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact (Subgroup.mem_normalizer_iff.mp hxnormK j).mp (hJK hj)
  have hAeq : A = J := hA _ x.2 hAprod
  have hxNJ : ((x : H) : G) ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hAeq
  have hxM : ((x : H) : G) ∈ M := hNJ hxNJ
  exact hxnot (Subgroup.mem_subgroupOf.mpr ⟨x.2, hxM⟩)

theorem le_of_forall_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M J R : Subgroup G} (hJM : J ≤ M)
    (hNJ : Subgroup.normalizer (J : Set G) ≤ M) (hJp : IsPGroup p J)
    (hRp : IsPGroup p R) (hJab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (hJR : J ≤ Subgroup.normalizer (R : Set G))
    (hA : ∀ A : Subgroup G, A ≤ (R ⊔ J) ⊓ M →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card J ≤ Nat.card A → A = J) :
    R ≤ M := by
  refine le_of_forall_map_conj_eq hJM hNJ hJp hRp hJR fun x _ hle => hA _ hle ?_ ?_
  · intro a ha b hb
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hJab a0 ha0 b0 hb0]
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (K := J)
      (MulAut.conj x).injective]

end CFSG.CGT.Hall82

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem conj_mem_blockU (S : Setting G M L) {m : G} (hm : m ∈ M) {v : G}
    (hv : v ∈ blockU L) : m * v * m⁻¹ ∈ blockU L := by
  rw [← S.normalizer_blockU_eq] at hm
  exact (Subgroup.mem_normalizer_iff.mp hm v).mp hv

theorem conj_mem_pCoreOf_centralizer (S : Setting G M L) {m : G} (hm : m ∈ M) {w : G}
    (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    m * w * m⁻¹ ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
  have hmN : m ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    le_normalizer_centralizer_of_normalizer_eq S.normalizer_eq hm
  have hmN' : m ∈ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hmN
  exact (Subgroup.mem_normalizer_iff.mp hmN' w).mp hw

theorem conj_mem_pCoreOf (S : Setting G M L) {m : G} (hm : m ∈ M) {j : G}
    (hj : j ∈ CFSG.Open.pCoreOf 2 M) : m * j * m⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) j).mp hj

theorem exists_mul_of_mem_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {j : G} :
    j ∈ CFSG.Open.pCoreOf 2 M ↔
      ∃ v ∈ blockU L,
        ∃ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), j = v * w := by
  have hWN : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≤
      Subgroup.normalizer (blockU L : Set G) := by
    rw [S.normalizer_blockU_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans S.centralizer_le
  rw [S.pCoreOf_eq hF hc]
  exact TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := blockU L) hWN

theorem eq_of_mem_blockU_mul_pCoreOf_centralizer (S : Setting G M L) {v v' w w' : G}
    (hv : v ∈ blockU L) (hv' : v' ∈ blockU L)
    (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hw' : w' ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (h : v * w = v' * w') : v = v' ∧ w = w' := by
  have h1 : v'⁻¹ * v = w' * w⁻¹ := by
    calc v'⁻¹ * v = v'⁻¹ * (v * w) * w⁻¹ := by group
      _ = v'⁻¹ * (v' * w') * w⁻¹ := by rw [h]
      _ = w' * w⁻¹ := by group
  have hbot : v'⁻¹ * v = 1 := by
    have hmem : v'⁻¹ * v ∈ blockU L ⊓
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (blockU L).mul_mem ((blockU L).inv_mem hv') hv
      · rw [h1]
        exact (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))).mul_mem hw'
          ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))).inv_mem hw)
    rwa [S.blockU_inf_pCoreOf_centralizer, Subgroup.mem_bot] at hmem
  have hbot' : w' * w⁻¹ = 1 := by rw [← h1, hbot]
  constructor
  · calc v = v' * (v'⁻¹ * v) := by group
      _ = v' * 1 := by rw [hbot]
      _ = v' := by group
  · calc w = (w' * w⁻¹)⁻¹ * w' := by group
      _ = 1⁻¹ * w' := by rw [hbot']
      _ = w' := by group

theorem commute_of_mem_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {a b : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (hb : b ∈ CFSG.Open.pCoreOf 2 M) :
    a * b = b * a := by
  obtain ⟨va, hva, wa, hwa, rfl⟩ := (S.exists_mul_of_mem_pCoreOf hF hc).mp ha
  obtain ⟨vb, hvb, wb, hwb, rfl⟩ := (S.exists_mul_of_mem_pCoreOf hF hc).mp hb
  calc (va * wa) * (vb * wb) = va * (wa * vb) * wb := by group
    _ = va * (vb * wa) * wb := by rw [← S.commute_blockU_pCoreOf_centralizer hvb hwa]
    _ = (va * vb) * (wa * wb) := by group
    _ = (vb * va) * (wb * wa) := by rw [S.blockU_comm hva hvb, hWab wa hwa wb hwb]
    _ = vb * (va * wb) * wa := by group
    _ = vb * (wb * va) * wa := by rw [S.commute_blockU_pCoreOf_centralizer hva hwb]
    _ = (vb * wb) * (va * wa) := by group

theorem card_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    Nat.card (CFSG.Open.pCoreOf 2 M) =
      64 * Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) := by
  rw [S.pCoreOf_eq hF hc]
  rw [CFSG.CGT.T75P.card_sup_of_commute
    (fun v hv w hw => S.commute_blockU_pCoreOf_centralizer hv hw)
    (S.blockU_inf_pCoreOf_centralizer)]
  rw [S.card_blockU]

theorem card_le_card_inf_mul (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {X : Subgroup G}
    (hX : X ≤ CFSG.Open.pCoreOf 2 M) :
    Nat.card X ≤ Nat.card ↥(X ⊓ blockU L) *
      Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) := by
  have hMN : M ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [S.normalizer_blockU_eq]
  have hXVN : X ≤ Subgroup.normalizer (blockU L : Set G) :=
    hX.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans hMN)
  have hformula :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := X) (K := blockU L) hXVN
  rw [S.card_blockU] at hformula
  have hYJ : X ⊔ blockU L ≤ CFSG.Open.pCoreOf 2 M := by
    exact sup_le hX S.blockU_le_pCoreOf
  have hYcard : Nat.card ↥(X ⊔ blockU L) ≤
      64 * Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) := by
    have h := Subgroup.card_le_of_le (H := X ⊔ blockU L) hYJ
    rwa [S.card_pCoreOf hF hc] at h
  have hle : Nat.card ↥(X ⊔ blockU L) * Nat.card ↥(X ⊓ blockU L) ≤
      (64 * Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))) *
        Nat.card ↥(X ⊓ blockU L) :=
    Nat.mul_le_mul_right _ hYcard
  have hmul : Nat.card X * 64 ≤
      (Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) *
        Nat.card ↥(X ⊓ blockU L)) * 64 := by
    calc Nat.card X * 64 = Nat.card ↥(X ⊔ blockU L) * Nat.card ↥(X ⊓ blockU L) :=
          hformula.symm
      _ ≤ _ := hle
      _ = (Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) *
            Nat.card ↥(X ⊓ blockU L)) * 64 := by ring
  have h := Nat.le_of_mul_le_mul_right hmul (by norm_num : 0 < 64)
  rwa [mul_comm] at h

theorem mem_centralizer_mul_iff (S : Setting G M L) {A : Subgroup G} (hA : A ≤ M)
    {v w : G} (hv : v ∈ blockU L)
    (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) {a : G}
    (ha : a ∈ A) :
    a ∈ Subgroup.centralizer ({v * w} : Set G) ↔
      a ∈ Subgroup.centralizer ({v} : Set G) ∧
        a ∈ Subgroup.centralizer ({w} : Set G) := by
  have hconj_prod : a * (v * w) * a⁻¹ = (a * v * a⁻¹) * (a * w * a⁻¹) := by group
  constructor
  · intro h
    have hcomm : (v * w) * a = a * (v * w) :=
      Subgroup.mem_centralizer_iff.mp h (v * w) (by simp)
    have hfix : a * (v * w) * a⁻¹ = v * w := by
      calc a * (v * w) * a⁻¹ = (v * w) * a * a⁻¹ := by rw [hcomm]
        _ = v * w := by group
    have hv' : a * v * a⁻¹ ∈ blockU L := S.conj_mem_blockU (hA ha) hv
    have hw' : a * w * a⁻¹ ∈
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) :=
      S.conj_mem_pCoreOf_centralizer (hA ha) hw
    have hprod : (a * v * a⁻¹) * (a * w * a⁻¹) = v * w := by
      rw [← hconj_prod, hfix]
    obtain ⟨hvv, hww⟩ :=
      S.eq_of_mem_blockU_mul_pCoreOf_centralizer hv' hv hw' hw hprod
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have h2 : a * v = v * a := by
        calc a * v = (a * v * a⁻¹) * a := by group
          _ = v * a := by rw [hvv]
      exact h2.symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have h2 : a * w = w * a := by
        calc a * w = (a * w * a⁻¹) * a := by group
          _ = w * a := by rw [hww]
      exact h2.symm
  · rintro ⟨hvC, hwC⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hv_comm : v * a = a * v := Subgroup.mem_centralizer_iff.mp hvC v (by simp)
    have hw_comm : w * a = a * w := Subgroup.mem_centralizer_iff.mp hwC w (by simp)
    calc (v * w) * a = v * (w * a) := by group
      _ = v * (a * w) := by rw [hw_comm]
      _ = (v * a) * w := by group
      _ = (a * v) * w := by rw [hv_comm]
      _ = a * (v * w) := by group

theorem card_pCoreOf_inf_centralizer (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A : Subgroup G}
    (hA : A ≤ M) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ⊓
          Subgroup.centralizer (A : Set G)) := by
  classical
  let CA : Subgroup G := Subgroup.centralizer (A : Set G)
  let V : Subgroup G := blockU L
  let W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))
  let f : ↥(V ⊓ CA) × ↥(W ⊓ CA) → ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) := fun p =>
    ⟨p.1.1 * p.2.1, Subgroup.mem_inf.mpr
      ⟨(CFSG.Open.pCoreOf 2 M).mul_mem (S.blockU_le_pCoreOf p.1.2.1)
          (S.pCoreOf_centralizer_le p.2.2.1),
        Subgroup.mem_centralizer_iff.mpr (fun a haA => by
          have h1 : a * p.1.1 = p.1.1 * a :=
            Subgroup.mem_centralizer_iff.mp p.1.2.2 a haA
          have h2 : a * p.2.1 = p.2.1 * a :=
            Subgroup.mem_centralizer_iff.mp p.2.2.2 a haA
          calc a * (p.1.1 * p.2.1) = (a * p.1.1) * p.2.1 := by group
            _ = (p.1.1 * a) * p.2.1 := by rw [h1]
            _ = p.1.1 * (a * p.2.1) := by group
            _ = p.1.1 * (p.2.1 * a) := by rw [h2]
            _ = (p.1.1 * p.2.1) * a := by group)⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨v, hvV, hvCA⟩, ⟨w, hwW, hwCA⟩⟩
        ⟨⟨v', hv'V, hv'CA⟩, ⟨w', hw'W, hw'CA⟩⟩ h
      have h1 : v * w = v' * w' := congrArg Subtype.val h
      obtain ⟨hvv, hww⟩ :=
        S.eq_of_mem_blockU_mul_pCoreOf_centralizer hvV hv'V hwW hw'W h1
      simp [hvv, hww]
    · intro x
      obtain ⟨hxJ, hxCA⟩ := Subgroup.mem_inf.mp x.2
      obtain ⟨v, hvV, w, hwW, hxvw⟩ := (S.exists_mul_of_mem_pCoreOf hF hc).mp hxJ
      have hvCA : v ∈ CA := by
        rw [Subgroup.mem_centralizer_iff]
        intro a haA
        have haC : a ∈ Subgroup.centralizer ({v * w} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          rw [← hxvw]
          exact (Subgroup.mem_centralizer_iff.mp hxCA a haA).symm
        have hva := (S.mem_centralizer_mul_iff hA hvV hwW haA).mp haC
        exact (Subgroup.mem_centralizer_iff.mp hva.1 v (by simp)).symm
      have hwCA : w ∈ CA := by
        rw [Subgroup.mem_centralizer_iff]
        intro a haA
        have haC : a ∈ Subgroup.centralizer ({v * w} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          rw [← hxvw]
          exact (Subgroup.mem_centralizer_iff.mp hxCA a haA).symm
        have hwa := (S.mem_centralizer_mul_iff hA hvV hwW haA).mp haC
        exact (Subgroup.mem_centralizer_iff.mp hwa.2 w (by simp)).symm
      refine ⟨(⟨v, hvV, hvCA⟩, ⟨w, hwW, hwCA⟩), ?_⟩
      apply Subtype.ext
      exact hxvw.symm
  calc Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA)
      = Nat.card (↥(V ⊓ CA) × ↥(W ⊓ CA)) :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card ↥(V ⊓ CA) * Nat.card ↥(W ⊓ CA) := Nat.card_prod _ _
    _ = Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ⊓
          Subgroup.centralizer (A : Set G)) := rfl

theorem normalizer_pCoreOf (S : Setting G M L) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) = M :=
  CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal

theorem eq_of_le_of_card_le (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    {v : G} (hv : v ∈ blockU L) {Q : Subgroup G} (hQM : Q ≤ M)
    (hQ2 : IsPGroup 2 Q) (hQv : ∀ x ∈ Q, x * v = v * x)
    (hQL : ∀ l ∈ L, l * v = v * l → ∀ x ∈ Q, l * x * l⁻¹ ∈ Q)
    {A : Subgroup G} (hAQ : A ≤ Q) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 M) ≤ Nat.card A) :
    A = CFSG.Open.pCoreOf 2 M := by
  classical
  let CA : Subgroup G := Subgroup.centralizer (A : Set G)
  let CV : Subgroup G := Subgroup.centralizer (blockU L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))
  let psiA : Subgroup (Equiv.Perm (Fin 64)) := S.psiSub hc A
  have hAM : A ≤ M := hAQ.trans hQM
  have hA2 : IsPGroup 2 A := hQ2.to_le hAQ
  have hXJ : A ⊓ CV ≤ CFSG.Open.pCoreOf 2 M := by
    refine S.le_pCoreOf_of_le_centralizer hF hc hW2 ?_ ?_ ?_
    · exact hA2.to_inf_left
    · exact inf_le_left.trans hAM
    · exact inf_le_right
  have hXCA : A ⊓ CV ≤ CA := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hAab x hx.1 a ha).symm
  have hXle : A ⊓ CV ≤ CFSG.Open.pCoreOf 2 M ⊓ CA := le_inf hXJ hXCA
  have hXcard : Nat.card ↥(A ⊓ CV) ≤
      Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) := Subgroup.card_le_of_le hXle
  have hxle : Nat.card ↥(A ⊓ CV) ≤ Nat.card ↥(blockU L ⊓ CA) * Nat.card W := by
    have h := S.card_le_card_inf_mul hF hc hXJ
    refine h.trans ?_
    have hinf : (A ⊓ CV) ⊓ blockU L ≤ blockU L ⊓ CA := by
      intro y hy
      exact Subgroup.mem_inf.mpr ⟨hy.2, hXCA hy.1⟩
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hinf)
  by_cases hApsi : psiA = ⊥
  · have hACV : A ≤ CV := by
      intro a ha
      have haM : a ∈ M := hAM ha
      have hmem : S.psiM hc ⟨a, haM⟩ ∈ psiA := by
        rw [show psiA = S.psiSub hc A from rfl, mem_psiSub S hc hAM]
        exact ⟨a, ha, haM, rfl⟩
      rw [hApsi, Subgroup.mem_bot] at hmem
      exact (S.psiM_eq_one_iff hc ⟨a, haM⟩).mp hmem
    have hAJ : A ≤ CFSG.Open.pCoreOf 2 M :=
      S.le_pCoreOf_of_le_centralizer hF hc hW2 hA2 hAM hACV
    exact Subgroup.eq_of_le_of_card_ge hAJ hcard
  · exfalso
    have hpsi2 : IsPGroup 2 psiA := S.isPGroup_psiSub hc hA2
    have hpsiM : psiA ≤ hexaM := S.psiSub_le_hexaM hc A
    let v₀ : Fin 64 := hc.equiv.symm ⟨v, hv⟩
    have hrep : rep v₀ = v := hc.rep_symm ⟨v, hv⟩
    have hXfix : ∀ x ∈ S.psiSub hc Q, x v₀ = v₀ := by
      intro x hx
      rw [mem_psiSub S hc hQM] at hx
      obtain ⟨q, hqQ, hqM, rfl⟩ := hx
      refine (conj_rep_eq_iff S hc ⟨q, hqM⟩ v₀).mp ?_
      rw [hrep]
      calc (q : G) * v * (q : G)⁻¹ = v * q * q⁻¹ := by rw [hQv q hqQ]
        _ = v := by group
    have hXnorm : ∀ a ∈ hexaL, a v₀ = v₀ → ∀ x ∈ S.psiSub hc Q,
        a * x * a⁻¹ ∈ S.psiSub hc Q := by
      intro a ha a_fix x hx
      have ha' : a ∈ S.psiSub hc L := by rwa [S.psiSub_L hF hc]
      rw [mem_psiSub S hc S.le] at ha'
      obtain ⟨l, hlL, hlM, hlpsi⟩ := ha'
      have hlv : l * v = v * l := by
        have hconj : (l : G) * rep v₀ * (l : G)⁻¹ = rep v₀ := by
          refine (conj_rep_eq_iff S hc ⟨l, hlM⟩ v₀).mpr ?_
          rw [hlpsi]
          exact a_fix
        rw [hrep] at hconj
        calc l * v = (l * v * l⁻¹) * l := by group
          _ = v * l := by rw [hconj]
      rw [mem_psiSub S hc hQM] at hx
      obtain ⟨q, hqQ, hqM, rfl⟩ := hx
      rw [mem_psiSub S hc hQM]
      have hq := hQL l hlL hlv q hqQ
      refine ⟨l * q * l⁻¹, hq, M.mul_mem (M.mul_mem hlM hqM) (M.inv_mem hlM), ?_⟩
      have harg : (⟨l * q * l⁻¹, M.mul_mem (M.mul_mem hlM hqM) (M.inv_mem hlM)⟩ : ↥M) =
          ⟨l, hlM⟩ * ⟨q, hqM⟩ * ⟨l, hlM⟩⁻¹ := Subtype.ext rfl
      calc S.psiM hc ⟨l * q * l⁻¹, M.mul_mem (M.mul_mem hlM hqM) (M.inv_mem hlM)⟩
          = S.psiM hc (⟨l, hlM⟩ * ⟨q, hqM⟩ * ⟨l, hlM⟩⁻¹) := by rw [harg]
        _ = S.psiM hc (⟨l, hlM⟩ * ⟨q, hqM⟩) * (S.psiM hc ⟨l, hlM⟩)⁻¹ := by
            rw [map_mul, map_inv]
        _ = (S.psiM hc ⟨l, hlM⟩ * S.psiM hc ⟨q, hqM⟩) *
            (S.psiM hc ⟨l, hlM⟩)⁻¹ := by rw [map_mul]
        _ = a * S.psiM hc ⟨q, hqM⟩ * a⁻¹ := by rw [hlpsi]
    have hle32 : Nat.card psiA * Nat.card (fixPts psiA) ≤ 32 :=
      hF.le_32 v₀ (S.psiSub hc Q) (S.psiSub_le_hexaM hc Q) (S.isPGroup_psiSub hc hQ2)
        hXfix hXnorm psiA (S.psiSub_mono hc hAQ) hApsi
    have hAcard : Nat.card A = Nat.card ↥(A ⊓ CV) * Nat.card psiA := by
      simpa [psiA] using S.card_psiSub hc hAM
    have hVcard : Nat.card ↥(blockU L ⊓ CA) = Nat.card (fixPts psiA) := by
      simpa [CA, psiA] using S.card_inf_centralizer hc hAM
    have hAle : Nat.card A ≤ 32 * Nat.card W := by
      calc Nat.card A = Nat.card ↥(A ⊓ CV) * Nat.card psiA := hAcard
        _ ≤ (Nat.card ↥(blockU L ⊓ CA) * Nat.card W) * Nat.card psiA :=
            Nat.mul_le_mul_right _ hxle
        _ = (Nat.card (fixPts psiA) * Nat.card W) * Nat.card psiA := by rw [hVcard]
        _ = (Nat.card psiA * Nat.card (fixPts psiA)) * Nat.card W := by ring
        _ ≤ 32 * Nat.card W := Nat.mul_le_mul_right _ hle32
    have hJcard : Nat.card (CFSG.Open.pCoreOf 2 M) = 64 * Nat.card W := by
      simpa [W] using S.card_pCoreOf hF hc
    have hWpos : 0 < Nat.card W := Nat.card_pos
    have : 64 * Nat.card W ≤ 32 * Nat.card W := by
      calc 64 * Nat.card W = Nat.card (CFSG.Open.pCoreOf 2 M) := hJcard.symm
        _ ≤ Nat.card A := hcard
        _ ≤ 32 * Nat.card W := hAle
    omega

theorem eq_of_le_pCoreOf_centralizer (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {t : G} (ht : t ∈ CFSG.Open.pCoreOf 2 M) {A : Subgroup G}
    (hA : A ≤ CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({t} : Set G)))
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 M) ≤ Nat.card A) :
    A = CFSG.Open.pCoreOf 2 M := by
  classical
  obtain ⟨v, hv, w, hw, htvw⟩ :=
    (S.exists_mul_of_mem_pCoreOf hF hc).mp ht
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({v * w} : Set G))
  have hQM : Q ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQt : Q ≤ Subgroup.centralizer ({v * w} : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hQv : ∀ x ∈ Q, x * v = v * x := by
    intro x hxQ
    have hxC : x ∈ Subgroup.centralizer ({v * w} : Set G) := hQt hxQ
    have h := (S.mem_centralizer_mul_iff hQM hv hw hxQ).mp hxC
    exact (Subgroup.mem_centralizer_iff.mp h.1 v (by simp)).symm
  have hA' : A ≤ Q := by
    have hQeq : Q = CFSG.Open.pCoreOf 2
        (M ⊓ Subgroup.centralizer ({t} : Set G)) := by
      rw [show Q = CFSG.Open.pCoreOf 2
        (M ⊓ Subgroup.centralizer ({v * w} : Set G)) from rfl, htvw]
    rwa [hQeq]
  have hQL : ∀ l ∈ L, l * v = v * l → ∀ x ∈ Q, l * x * l⁻¹ ∈ Q := by
    intro l hlL hlv x hxQ
    have hlM : l ∈ M := S.le hlL
    have hlw : l * w = w * l := by
      have hwC : w ∈ Subgroup.centralizer (L : Set G) :=
        CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
      exact Subgroup.mem_centralizer_iff.mp hwC l hlL
    have hlt : l ∈ Subgroup.centralizer ({v * w} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      calc (v * w) * l = v * (w * l) := by group
        _ = v * (l * w) := by rw [← hlw]
        _ = (v * l) * w := by group
        _ = (l * v) * w := by rw [← hlv]
        _ = l * (v * w) := by group
    have hlN : l ∈ Subgroup.normalizer (Q : Set G) := by
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
        (Subgroup.mem_inf.mpr ⟨hlM, hlt⟩)
    exact (Subgroup.mem_normalizer_iff.mp hlN x).mp hxQ
  exact S.eq_of_le_of_card_le hF hc hW2 hv hQM hQ2 hQv hQL hA' hAab hcard

theorem pCoreOf_centralizer_singleton_le (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {t : G} (ht : t ∈ CFSG.Open.pCoreOf 2 M) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤ M := by
  classical
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  let R₀ : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({t} : Set G))
  have hJR : J ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro j hj
    have hjt : j ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (S.commute_of_mem_pCoreOf hF hc hWab hj ht).symm
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hjt
  refine le_of_forall_eq (p := 2) (M := M) (J := J) (R := R₀)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M) ?_ ?_ ?_ ?_ hJR ?_
  · rw [show J = CFSG.Open.pCoreOf 2 M from rfl, S.normalizer_pCoreOf]
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  · exact fun a ha b hb => S.commute_of_mem_pCoreOf hF hc hWab ha hb
  · intro A hA hAab hAcard
    let K : Subgroup G := (R₀ ⊔ J) ⊓ M
    let Q : Subgroup G := CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({t} : Set G))
    have hR0p : IsPGroup 2 R₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hJp : IsPGroup 2 J := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
    have hRJ2 : IsPGroup 2 ↥(R₀ ⊔ J) := by
      have h := hJp.to_sup_of_normal_right' hR0p hJR
      rw [sup_comm] at h
      exact h
    have hK2 : IsPGroup 2 K := hRJ2.to_le inf_le_left
    have hKle : K ≤ Q := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ hK2
      ·
        refine le_inf inf_le_right ?_
        have hJC : J ≤ Subgroup.centralizer ({t} : Set G) := by
          intro j hj
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          exact (S.commute_of_mem_pCoreOf hF hc hWab hj ht).symm
        exact inf_le_left.trans
          (sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) : R₀ ≤ _) hJC)
      ·
        intro m hm
        have hmM : m ∈ M := hm.1
        have hmC : m ∈ Subgroup.centralizer ({t} : Set G) := hm.2
        have hmR : m ∈ Subgroup.normalizer (R₀ : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
            (Subgroup.centralizer ({t} : Set G)) hmC
        have hmJ : m ∈ Subgroup.normalizer (J : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hmM
        have hmRJ : m ∈ Subgroup.normalizer ((R₀ ⊔ J : Subgroup G) : Set G) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          rw [Subgroup.map_sup,
            (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmR),
            (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmJ)]
        have hmM' : m ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hmM
        rw [show K = (R₀ ⊔ J) ⊓ M from rfl, Subgroup.mem_normalizer_iff_map_conj_eq]
        rw [Subgroup.map_inf _ _ _ (MulAut.conj m).injective,
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmRJ),
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp hmM')]
    exact S.eq_of_le_pCoreOf_centralizer hF hc hW2 hWab ht (hA.trans hKle) hAab hAcard

theorem le_pCoreOf_inf_of_le (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {t : G} (ht : t ∈ CFSG.Open.pCoreOf 2 M) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤
      CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({t} : Set G)) := by
  let R₀ : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({t} : Set G))
  have hRM : R₀ ≤ M := S.pCoreOf_centralizer_singleton_le hF hc hW2 hWab ht
  have hRC : R₀ ≤ Subgroup.centralizer ({t} : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hRM hRC) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  intro m hm
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
    (Subgroup.centralizer ({t} : Set G))) hm.2

theorem mem_of_conj_mem (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {w : G} (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) (hw1 : w ≠ 1)
    {g : G} (hg : g * w * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    g ∈ M := by
  classical
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  let Cw : Subgroup G := Subgroup.centralizer ({w} : Set G)
  let Ct : Subgroup G := Subgroup.centralizer ({g * w * g⁻¹} : Set G)
  have hCwM : Cw ≤ M := centralizer_le_of_mem_pCoreOf S.uniq hw hw1
  have hJab : ∀ a ∈ CFSG.Open.pCoreOf 2 M, ∀ b ∈ CFSG.Open.pCoreOf 2 M,
      a * b = b * a :=
    fun a ha b hb => S.commute_of_mem_pCoreOf hF hc hWab ha hb
  have hwJ : w ∈ J := S.pCoreOf_centralizer_le hw
  have hJleCw : J ≤ Cw := by
    intro j hj
    change j ∈ Subgroup.centralizer ({w} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (hJab j hj w hwJ).symm
  have hJnormCw : (J.subgroupOf Cw).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJleCw]
    exact hCwM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hJp : IsPGroup 2 J := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hJleP : J ≤ CFSG.Open.pCoreOf 2 Cw :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hJleCw hJnormCw hJp
  let e : G ≃* G := MulAut.conj g
  have hCmap : Cw.map e.toMonoidHom = Ct := by
    have h1 : Subgroup.centralizer (Subgroup.zpowers w : Set G) = Cw := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : Subgroup.centralizer (Subgroup.zpowers (g * w * g⁻¹) : Set G) = Ct := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    calc Cw.map e.toMonoidHom
        = (Subgroup.centralizer (Subgroup.zpowers w : Set G)).map e.toMonoidHom := by
          rw [h1]
      _ = Subgroup.centralizer ((Subgroup.zpowers w).map e.toMonoidHom : Set G) :=
          CFSG.Glauberman.map_centralizer_eq_of_equiv e (Subgroup.zpowers w)
      _ = Subgroup.centralizer (Subgroup.zpowers (e w) : Set G) := by
          rw [MonoidHom.map_zpowers]
          rfl
      _ = Subgroup.centralizer (Subgroup.zpowers (g * w * g⁻¹) : Set G) := by
          simp [e]
      _ = Ct := by rw [h2]
  have hmap_le : J.map e.toMonoidHom ≤ CFSG.Open.pCoreOf 2 Ct := by
    have h := Subgroup.map_mono (f := e.toMonoidHom) hJleP
    rwa [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e Cw, hCmap] at h
  let J' : Subgroup G := J.map e.toMonoidHom
  have hJ'le : J' ≤ CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer
      ({g * w * g⁻¹} : Set G)) :=
    hmap_le.trans (S.le_pCoreOf_inf_of_le hF hc hW2 hWab hg)
  have hJ'ab : ∀ a ∈ J', ∀ b ∈ J', a * b = b * a := by
    intro a ha b hb
    rw [show J' = J.map e.toMonoidHom from rfl, Subgroup.mem_map] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := ha
    obtain ⟨b0, hb0, rfl⟩ := hb
    rw [← map_mul, ← map_mul, hJab a0 ha0 b0 hb0]
  have hcardJ' : Nat.card J' = Nat.card J := by
    rw [show J' = J.map e.toMonoidHom from rfl]
    exact Subgroup.card_map_of_injective (f := e.toMonoidHom) (K := J) e.injective
  have hJ'eq : J' = J :=
    S.eq_of_le_pCoreOf_centralizer hF hc hW2 hWab hg hJ'le hJ'ab (by
      rw [hcardJ'])
  have hgnorm : g ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hJ'eq
  rwa [show J = CFSG.Open.pCoreOf 2 M from rfl, S.normalizer_pCoreOf] at hgnorm

theorem weaklyClosedIn_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    (hW1 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≠ ⊥) :
    CFSG.CGT.Timmesfeld75.WeaklyClosedIn (CFSG.Open.pCoreOf 2 M) M := by
  classical
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 M, ?_⟩
  intro g hgM
  let A : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M)
  have hAM : A ≤ M := hgM
  have hAdef : A = (CFSG.Open.pCoreOf 2 M).map (MulAut.conj g).toMonoidHom := rfl
  have hA2 : IsPGroup 2 A := by
    rw [hAdef]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).map (MulAut.conj g).toMonoidHom
  have hAcard : Nat.card A = Nat.card (CFSG.Open.pCoreOf 2 M) := by
    rw [hAdef]
    exact Subgroup.card_map_of_injective (K := CFSG.Open.pCoreOf 2 M)
      (MulAut.conj g).injective
  have hJab : ∀ a ∈ CFSG.Open.pCoreOf 2 M, ∀ b ∈ CFSG.Open.pCoreOf 2 M,
      a * b = b * a :=
    fun a ha b hb => S.commute_of_mem_pCoreOf hF hc hWab ha hb
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [hAdef, Subgroup.mem_map] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := ha
    obtain ⟨b0, hb0, rfl⟩ := hb
    rw [← map_mul, ← map_mul, hJab a0 ha0 b0 hb0]
  let CA : Subgroup G := Subgroup.centralizer (A : Set G)
  let CV : Subgroup G := Subgroup.centralizer (blockU L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))
  let psiA : Subgroup (Equiv.Perm (Fin 64)) := S.psiSub hc A
  have hXJ : A ⊓ CV ≤ CFSG.Open.pCoreOf 2 M := by
    refine S.le_pCoreOf_of_le_centralizer hF hc hW2 ?_ ?_ ?_
    · exact hA2.to_inf_left
    · exact inf_le_left.trans hAM
    · exact inf_le_right
  have hXCA : A ⊓ CV ≤ CA := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hAab x hx.1 a ha).symm
  have hXle : A ⊓ CV ≤ CFSG.Open.pCoreOf 2 M ⊓ CA := le_inf hXJ hXCA
  have hXcard : Nat.card ↥(A ⊓ CV) ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) :=
    Subgroup.card_le_of_le hXle
  have hpsi2 : IsPGroup 2 psiA := S.isPGroup_psiSub hc hA2
  have hpsiM : psiA ≤ hexaM := S.psiSub_le_hexaM hc A
  have hAcard_psi : Nat.card A = Nat.card ↥(A ⊓ CV) * Nat.card psiA := by
    simpa [psiA] using S.card_psiSub hc hAM
  have hJCA : Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) =
      Nat.card ↥(blockU L ⊓ CA) * Nat.card ↥(W ⊓ CA) := by
    simpa [CA, W] using S.card_pCoreOf_inf_centralizer hF hc hAM
  have hVCA : Nat.card ↥(blockU L ⊓ CA) = Nat.card (fixPts psiA) := by
    simpa [CA, psiA] using S.card_inf_centralizer hc hAM
  have h64 : Nat.card psiA * Nat.card (fixPts psiA) ≤ 64 := hF.le_64 psiA hpsiM hpsi2
  have hWCA : Nat.card ↥(W ⊓ CA) ≤ Nat.card W := Subgroup.card_le_of_le inf_le_left
  have hJcard : Nat.card (CFSG.Open.pCoreOf 2 M) = 64 * Nat.card W := by
    simpa [W] using S.card_pCoreOf hF hc
  have hAle : Nat.card A ≤ Nat.card (CFSG.Open.pCoreOf 2 M) := by
    calc Nat.card A = Nat.card ↥(A ⊓ CV) * Nat.card psiA := hAcard_psi
      _ ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) * Nat.card psiA :=
          Nat.mul_le_mul_right _ hXcard
      _ = (Nat.card ↥(blockU L ⊓ CA) * Nat.card ↥(W ⊓ CA)) * Nat.card psiA := by
          rw [hJCA]
      _ = (Nat.card (fixPts psiA) * Nat.card ↥(W ⊓ CA)) * Nat.card psiA := by rw [hVCA]
      _ = (Nat.card psiA * Nat.card (fixPts psiA)) * Nat.card ↥(W ⊓ CA) := by ring
      _ ≤ 64 * Nat.card ↥(W ⊓ CA) := Nat.mul_le_mul_right _ h64
      _ ≤ 64 * Nat.card W := Nat.mul_le_mul_left 64 hWCA
      _ = Nat.card (CFSG.Open.pCoreOf 2 M) := hJcard.symm
  have hA_eq : Nat.card A = Nat.card (CFSG.Open.pCoreOf 2 M) := hAcard
  have hAle64 : Nat.card A ≤ 64 * Nat.card ↥(W ⊓ CA) := by
    calc Nat.card A = Nat.card ↥(A ⊓ CV) * Nat.card psiA := hAcard_psi
      _ ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) * Nat.card psiA :=
          Nat.mul_le_mul_right _ hXcard
      _ = (Nat.card ↥(blockU L ⊓ CA) * Nat.card ↥(W ⊓ CA)) * Nat.card psiA := by
          rw [hJCA]
      _ = (Nat.card (fixPts psiA) * Nat.card ↥(W ⊓ CA)) * Nat.card psiA := by rw [hVCA]
      _ = (Nat.card psiA * Nat.card (fixPts psiA)) * Nat.card ↥(W ⊓ CA) := by ring
      _ ≤ 64 * Nat.card ↥(W ⊓ CA) := Nat.mul_le_mul_right _ h64
  have h64W_le : 64 * Nat.card W ≤ 64 * Nat.card ↥(W ⊓ CA) := by
    rw [← hJcard, ← hA_eq]
    exact hAle64
  have h64eq : 64 * Nat.card ↥(W ⊓ CA) = 64 * Nat.card W :=
    le_antisymm (Nat.mul_le_mul_left 64 hWCA) h64W_le
  have hw_eq : Nat.card ↥(W ⊓ CA) = Nat.card W :=
    Nat.mul_left_cancel (by norm_num : 0 < 64) h64eq
  have hWCA_eq : W ⊓ CA = W := by
    apply Subgroup.eq_of_le_of_card_ge (H := W ⊓ CA) (K := W) inf_le_left
    rw [hw_eq]
  have hWleCA : W ≤ CA := by
    intro w hw
    have : w ∈ W ⊓ CA := by rw [hWCA_eq]; exact hw
    exact this.2
  have hp_pos : 0 < Nat.card psiA := Nat.card_pos
  have hx_eq : Nat.card ↥(A ⊓ CV) = Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) := by
    have hle_rev : Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) ≤ Nat.card ↥(A ⊓ CV) := by
      have h1 : Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) * Nat.card psiA ≤
          Nat.card ↥(A ⊓ CV) * Nat.card psiA := by
        calc Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ CA) * Nat.card psiA
            = (Nat.card ↥(blockU L ⊓ CA) * Nat.card ↥(W ⊓ CA)) * Nat.card psiA := by
              rw [hJCA]
          _ = (Nat.card (fixPts psiA) * Nat.card W) * Nat.card psiA := by rw [hVCA, hw_eq]
          _ = (Nat.card psiA * Nat.card (fixPts psiA)) * Nat.card W := by ring
          _ ≤ 64 * Nat.card W := Nat.mul_le_mul_right _ h64
          _ = Nat.card (CFSG.Open.pCoreOf 2 M) := hJcard.symm
          _ = Nat.card A := hAcard.symm
          _ = Nat.card ↥(A ⊓ CV) * Nat.card psiA := hAcard_psi
      exact Nat.le_of_mul_le_mul_right h1 hp_pos
    exact le_antisymm hXcard hle_rev
  have hJCA_eq : CFSG.Open.pCoreOf 2 M ⊓ CA = A ⊓ CV := by
    have h := Subgroup.eq_of_le_of_card_ge (H := A ⊓ CV)
      (K := CFSG.Open.pCoreOf 2 M ⊓ CA) hXle (le_of_eq hx_eq.symm)
    exact h.symm
  have hWleA : W ≤ A := by
    have hWleJ : W ≤ CFSG.Open.pCoreOf 2 M := S.pCoreOf_centralizer_le
    have hWleJCA : W ≤ CFSG.Open.pCoreOf 2 M ⊓ CA := le_inf hWleJ hWleCA
    have hWleACV : W ≤ A ⊓ CV := hJCA_eq ▸ hWleJCA
    exact hWleACV.trans inf_le_left
  obtain ⟨w, hwW, hw1⟩ := (Subgroup.bot_or_exists_ne_one W).resolve_left hW1
  have hwA : w ∈ A := hWleA hwW
  have hginvw : g⁻¹ * w * g ∈ CFSG.Open.pCoreOf 2 M := by
    have : w ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M) := hwA
    rwa [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at this
  have hginvM : g⁻¹ ∈ M :=
    S.mem_of_conj_mem hF hc hW2 hWab hwW hw1 (by simpa using hginvw)
  have hgM : g ∈ M := by simpa using M.inv_mem hginvM
  have hgnorm : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := by
    rw [S.normalizer_pCoreOf]
    exact hgM
  have hAeq : A = CFSG.Open.pCoreOf 2 M := by
    change (CFSG.Open.pCoreOf 2 M).map (MulAut.conj g).toMonoidHom = CFSG.Open.pCoreOf 2 M
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgnorm
  exact hAeq

end CFSG.CGT.Hall82.Setting
