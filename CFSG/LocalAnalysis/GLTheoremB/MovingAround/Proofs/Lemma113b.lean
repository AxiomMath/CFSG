module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped Pointwise commutatorElement

namespace Lemma113b

@[expose] def IsExtremalIn (X : Type) [Group X] (P : Subgroup X) (y : X) : Prop :=
  ∀ z ∈ P, (∃ x : X, z = x⁻¹ * y * x) →
    Nat.card ↥(P ⊓ Subgroup.centralizer ({z} : Set X)) ≤
      Nat.card ↥(P ⊓ Subgroup.centralizer ({y} : Set X))

@[expose] def Input32_7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime] (P : Sylow p X) (C : Type) [CommGroup C]
    (φ : (P : Subgroup X) →* C) (b : X) (hbP : b ∈ (P : Subgroup X)), orderOf b = p →
      φ ⟨b, hbP⟩ ≠ 1 →
      (∀ (y : X) (hyP : y ∈ (P : Subgroup X)), IsExtremalIn X (P : Subgroup X) y →
        (∃ x : X, y = x⁻¹ * b * x) →
          φ ⟨b⁻¹ * y, (P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem hbP) hyP⟩ = 1) →
      MonoidHom.transfer φ b ≠ 1

section Printed

variable {G : Type} [Group G]

@[expose] def PieceD_R2 (e : G) (R : Subgroup G) : Prop :=
  ∀ g : G, g⁻¹ * e * g ∈ R →
    ∃ z ∈ R, g * z ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)

@[expose] def PieceD_R4 (E R : Subgroup G) : Prop :=
  ∃ W : Subgroup G, W ≤ R ∧ (W.subgroupOf R).Normal ∧ E ≤ W ∧ Nat.card (↥R ⧸ W.subgroupOf R) = 3 ∧
    ∀ w ∈ W, w ^ 3 = 1 → w ∈ E

@[expose] def PieceD_K3 (E Q A : Subgroup G) (e : G) : Prop :=
  ∀ x ∈ A, x ∉ E → ∀ n ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G),
    n⁻¹ * x * n ∈ Q → x⁻¹ * (n⁻¹ * x * n) ∈ E

end Printed

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_map_eq' {p : ℕ} {Y X : Subgroup G} (hX : IsSylowIn p Y X) :
    ∃ S : Sylow p ↥Y, (S : Subgroup ↥Y).map Y.subtype = X := by
  have hXY : IsPGroup p ↥(X.subgroupOf Y) :=
    hX.2.1.comap_of_injective Y.subtype Subtype.val_injective
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hXY
  refine ⟨S, ?_⟩
  have hmap : IsPGroup p ↥((S : Subgroup ↥Y).map Y.subtype) := S.isPGroup'.map Y.subtype
  have hle : X ≤ (S : Subgroup ↥Y).map Y.subtype := fun x hx =>
    ⟨⟨x, hX.1 hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  exact hX.2.2 _ (Subgroup.map_subtype_le _) hmap hle

theorem exists_sylowIn_above' {p : ℕ} {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup p ↥P) :
    ∃ Q : Subgroup G, IsSylowIn p X Q ∧ P ≤ Q := by
  obtain ⟨Q, hPQ, hQmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ X ∧ IsPGroup p ↥R}).exists_le_maximal ⟨hPX, hP⟩
  exact ⟨Q, ⟨hQmax.1.1, hQmax.1.2, fun R' hR'X hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'X, hR'p⟩ hQR') hQR'⟩, hPQ⟩

theorem centralizer_le_normalizer_zpowers' (y : G) :
    Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
  intro t ht
  have hyt : y * t = t * y := Subgroup.mem_centralizer_iff.1 ht y (Set.mem_singleton y)
  have htc : Commute t y := hyt.symm
  have hk : ∀ k : ℤ, t * y ^ k * t⁻¹ = y ^ k := by
    intro k
    rw [(htc.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    exact Subgroup.mem_zpowers_iff.2 ⟨k, (hk k).symm⟩
  · intro hm
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 hm
    have h1 : t * m * t⁻¹ = t * y ^ k * t⁻¹ := by rw [hk k, ← hk']
    have h2 : m = y ^ k := by
      calc m = t⁻¹ * (t * m * t⁻¹) * t := by group
        _ = t⁻¹ * (t * y ^ k * t⁻¹) * t := by rw [h1]
        _ = y ^ k := by
          have hcomm : Commute t⁻¹ (y ^ k) := ((htc.zpow_right k)).inv_left
          rw [hk k, hcomm.eq, mul_assoc, inv_mul_cancel, mul_one]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, h2.symm⟩

theorem isSylowIn_centralizer_of_extremal {p : ℕ} [Fact p.Prime] {R : Subgroup G}
    (hR : IsSylowIn p ⊤ R) {y : G} (hyR : y ∈ R) (hext : IsExtremalIn G R y) :
    IsSylowIn p (Subgroup.centralizer ({y} : Set G)) (R ⊓ Subgroup.centralizer ({y} : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hCdef
  have hyC : y ∈ C := Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]
  have hX0 : IsPGroup p ↥(R ⊓ C) := hR.2.1.to_le inf_le_left
  obtain ⟨T, hTsyl, hX0T⟩ := exists_sylowIn_above' (inf_le_right : R ⊓ C ≤ C) hX0
  have hyT : y ∈ T := by
    have hzy : IsPGroup p ↥(Subgroup.zpowers y) :=
      hR.2.1.to_le (Subgroup.zpowers_le.2 hyR)
    have hTN : T ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
      hTsyl.1.trans (centralizer_le_normalizer_zpowers' y)
    have hsup : IsPGroup p ↥(Subgroup.zpowers y ⊔ T) :=
      IsPGroup.to_sup_of_normal_left' hzy hTsyl.2.1 hTN
    have hle : Subgroup.zpowers y ⊔ T ≤ C :=
      sup_le (Subgroup.zpowers_le.2 hyC) hTsyl.1
    have heq := hTsyl.2.2 _ hle hsup le_sup_right
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  obtain ⟨P1, hP1T⟩ := IsPGroup.exists_le_sylow (P := T) hTsyl.2.1
  let Rs : Sylow p G := ⟨R, hR.2.1, fun hQ hRQ => hR.2.2 _ le_top hQ hRQ⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Rs P1
  have hconj : ∀ t : G, t ∈ (P1 : Subgroup G) → g⁻¹ * t * g ∈ R := by
    intro t ht
    have hRs : (Rs : Subgroup G) = R := rfl
    have hP1 : (P1 : Subgroup G) = MulAut.conj g • R := by
      rw [← hg, Sylow.smul_def]
      rfl
    rw [hP1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at ht
    simpa [MulAut.conj_apply, mul_assoc] using ht
  set z : G := g⁻¹ * y * g with hz
  have hzR : z ∈ R := hconj y (hP1T hyT)
  have hzext := hext z hzR ⟨g, rfl⟩
  have hmapLE : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ R ⊓ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · have htP1 : t ∈ (P1 : Subgroup G) := hP1T ht
      have := hconj t htP1
      simpa [MulAut.conj_apply, mul_assoc] using this
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro h' hh'
      rw [Set.mem_singleton_iff.1 hh']
      have htC : t ∈ C := hTsyl.1 ht
      have htc : y * t = t * y := (Subgroup.mem_centralizer_iff.1 htC) y (Set.mem_singleton y)
      show z * (MulAut.conj g⁻¹ t) = (MulAut.conj g⁻¹ t) * z
      rw [MulAut.conj_apply, hz]
      calc g⁻¹ * y * g * (g⁻¹ * t * g⁻¹⁻¹)
          = g⁻¹ * (y * t) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * (t * y) * g⁻¹⁻¹ := by rw [htc]
        _ = (g⁻¹ * t * g⁻¹⁻¹) * (g⁻¹ * y * g) := by group
  have hTcard : Nat.card ↥T ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({z} : Set G)) := by
    have h1 := Subgroup.card_le_of_le hmapLE
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h1
  have hXT : R ⊓ C ≤ T := hX0T
  have hcard : Nat.card ↥T ≤ Nat.card ↥(R ⊓ C) := le_trans hTcard hzext
  have hEq : R ⊓ C = T := Subgroup.eq_of_le_of_card_ge hXT hcard
  rw [hEq]
  exact hTsyl

theorem exists_conj_mem_of_isSylowIn {p : ℕ} [Fact p.Prime] {C T S : Subgroup G}
    (hT : IsSylowIn p C T) (hS : S ≤ C) (hSp : IsPGroup p ↥S) :
    ∃ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ T := by
  obtain ⟨Ts, hTs⟩ := exists_sylow_map_eq' hT
  have hSC : IsPGroup p ↥(S.subgroupOf C) :=
    hSp.comap_of_injective C.subtype Subtype.val_injective
  obtain ⟨T1, hT1⟩ := IsPGroup.exists_le_sylow hSC
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C T1 Ts
  refine ⟨c, c.2, fun s hs => ?_⟩
  have hsC : (⟨s, hS hs⟩ : ↥C) ∈ (T1 : Subgroup ↥C) := hT1 (Subgroup.mem_subgroupOf.2 hs)
  have hmem : MulAut.conj c (⟨s, hS hs⟩ : ↥C) ∈ (Ts : Subgroup ↥C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hsC
  rw [← hTs]
  exact Subgroup.mem_map_of_mem C.subtype hmem

theorem exists_adjust {p : ℕ} [Fact p.Prime] {R A : Subgroup G} (hR : IsSylowIn p ⊤ R)
    {b x y : G} (hA : IsPGroup p ↥A) (hAcomm : ∀ a ∈ A, b * a = a * b)
    (hxy : y = x⁻¹ * b * x) (hyR : y ∈ R) (hext : IsExtremalIn G R y) :
    ∃ g : G, g⁻¹ * b * g = y ∧ ∀ a ∈ A, g⁻¹ * a * g ∈ R := by
  have hT := isSylowIn_centralizer_of_extremal hR hyR hext
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hCdef
  let S : Subgroup G := A.map (MulAut.conj x⁻¹).toMonoidHom
  have hSC : S ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro h' hh'
    rw [Set.mem_singleton_iff.1 hh', hxy]
    show x⁻¹ * b * x * (x⁻¹ * a * x⁻¹⁻¹) = (x⁻¹ * a * x⁻¹⁻¹) * (x⁻¹ * b * x)
    calc x⁻¹ * b * x * (x⁻¹ * a * x⁻¹⁻¹) = x⁻¹ * (b * a) * x⁻¹⁻¹ := by group
      _ = x⁻¹ * (a * b) * x⁻¹⁻¹ := by rw [hAcomm a ha]
      _ = (x⁻¹ * a * x⁻¹⁻¹) * (x⁻¹ * b * x) := by group
  have hSp : IsPGroup p ↥S := hA.map _
  obtain ⟨c, hcC, hcS⟩ := exists_conj_mem_of_isSylowIn hT hSC hSp
  have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.1 hcC y (Set.mem_singleton y)
  refine ⟨x * c⁻¹, ?_, ?_⟩
  · calc (x * c⁻¹)⁻¹ * b * (x * c⁻¹) = c * (x⁻¹ * b * x) * c⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [hxy]
      _ = y := by rw [← hcy]; group
  · intro a ha
    have hs : (MulAut.conj x⁻¹).toMonoidHom a ∈ S := Subgroup.mem_map.2 ⟨a, ha, rfl⟩
    have h1 := (Subgroup.mem_inf.1 (hcS _ hs)).1
    have heq : (x * c⁻¹)⁻¹ * a * (x * c⁻¹) = c * (MulAut.conj x⁻¹ a) * c⁻¹ := by
      simp only [MulAut.conj_apply]
      group
    rw [heq]
    exact h1

end Sylow

end Lemma113b

open Lemma113b in
theorem lemma113_ii_pieceD_cond (hI : Input32_7) {G : Type} [Group G] [Finite G] {m : ℕ}
    {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q)
    (hC : Claim113C E A Q)
    (hR2 : ∀ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
      PieceD_R2 e R)
    (hR4 : ∀ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
      PieceD_R4 E R)
    (hK3 : PieceD_K3 E Q A e) : False := by
  obtain ⟨-, -, R, hRN, hQR, -, -, hRG⟩ := hC
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple : IsSimpleGroup G := h.standing.simple
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.standing.nonabelian
  have hAsc : IsSCp 3 M A := h.pair.1.2.1.1.1
  have hEsc : IsSCp 3 M E := h.pair.1.1.1.1
  have hAab : IsElemAbelian 3 A := hAsc.2.1
  have hEab : IsElemAbelian 3 E := hEsc.2.1
  have hAQ : A ≤ Q := le_sup_right.trans h.hQ.2
  have hAR : A ≤ R := hAQ.trans hQR
  have heA : e ∈ A := (Subgroup.mem_inf.1 h.he.1).2
  have hAcomm' : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ * a₂ = a₂ * a₁ := fun a₁ h₁ a₂ h₂ =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨a₁, h₁⟩ ⟨a₂, h₂⟩)
  obtain ⟨b, hbA, hbE⟩ : ∃ b ∈ A, b ∉ E := by
    by_contra hcon
    push_neg at hcon
    have hEA : E = A := hAsc.2.2 E hEsc.1 hEab (fun x hx => hcon x hx)
    exact h.pair.1.2.1.2 (by rw [← hEA]; exact h.pair.1.1.2)
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ one_mem E)
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hbR : b ∈ R := hAR hbA
  have hAcomm : ∀ a₁ ∈ A, b * a₁ = a₁ * b := fun a₁ h₁ => hAcomm' b hbA a₁ h₁
  let Rs : Sylow 3 G := ⟨R, hRG.2.1, fun hQ hRQ => hRG.2.2 _ le_top hQ hRQ⟩
  obtain ⟨W, _hWR, hWn, hEW, hWcard, hWΩ⟩ := hR4 R hRN hQR
  haveI : (W.subgroupOf R).Normal := hWn
  haveI : IsCyclic (↥R ⧸ W.subgroupOf R) := isCyclic_of_prime_card hWcard
  letI hcomm : CommGroup (↥R ⧸ W.subgroupOf R) := IsCyclic.commGroup
  let φ : (Rs : Subgroup G) →* (↥R ⧸ W.subgroupOf R) := QuotientGroup.mk' (W.subgroupOf R)
  have hbW : b ∉ W := fun hbW' => hbE (hWΩ b hbW' hb3)
  have hφb : φ ⟨b, hbR⟩ ≠ 1 := fun h1 =>
    hbW (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1))
  have htr : MonoidHom.transfer φ b ≠ 1 := by
    refine hI G 3 Rs (↥R ⧸ W.subgroupOf R) φ b (show b ∈ (Rs : Subgroup G) from hbR) hord
      hφb ?_
    intro y hyRs hext ⟨x, hxy⟩
    have hyR : y ∈ R := hyRs
    have hext' : IsExtremalIn G R y := hext
    have hkey : b⁻¹ * y ∈ W := by
      obtain ⟨g', hg'b, hg'A⟩ :=
        exists_adjust hRG (hRG.2.1.to_le hAR) hAcomm hxy hyR hext'
      obtain ⟨z, hzR, hhN⟩ := hR2 R hRN hQR g' (hg'A e heA)
      set hh : G := g' * z with hhdef
      have hbh : hh⁻¹ * b * hh = z⁻¹ * y * z := by
        rw [hhdef, ← hg'b]; group
      have hbhR : hh⁻¹ * b * hh ∈ R := by
        rw [hbh]; exact R.mul_mem (R.mul_mem (R.inv_mem hzR) hyR) hzR
      have hhe : hh * e * hh⁻¹ ∈ Subgroup.zpowers e :=
        (Subgroup.mem_normalizer_iff.1 hhN e).1 (Subgroup.mem_zpowers e)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hhe
      have hbe : Commute b e := hAcomm e heA
      have hbej : Commute b (e ^ j) := hbe.zpow_right j
      have hinv : hh⁻¹ * e ^ j * hh = e := by rw [hj]; group
      have he_eq : hh * e = e ^ j * hh := by rw [hj]; group
      have hcomm_e : (hh⁻¹ * b * hh) * e = e * (hh⁻¹ * b * hh) := by
        calc (hh⁻¹ * b * hh) * e = hh⁻¹ * b * (hh * e) := by group
          _ = hh⁻¹ * b * (e ^ j * hh) := by rw [he_eq]
          _ = hh⁻¹ * (b * e ^ j) * hh := by group
          _ = hh⁻¹ * (e ^ j * b) * hh := by rw [hbej.eq]
          _ = (hh⁻¹ * e ^ j * hh) * (hh⁻¹ * b * hh) := by group
          _ = e * (hh⁻¹ * b * hh) := by rw [hinv]
      have hb'C : hh⁻¹ * b * hh ∈ Subgroup.centralizer ({e} : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 ?_
        intro e' he'
        rw [Set.mem_singleton_iff.1 he']
        exact hcomm_e.symm
      have hQe : R ⊓ Subgroup.centralizer ({e} : Set G) = Q :=
        h.hQ.1.2.2 _ inf_le_right (hRG.2.1.to_le inf_le_left) (le_inf hQR h.hQ.1.1)
      have hb'Q : hh⁻¹ * b * hh ∈ Q := by
        rw [← hQe]; exact Subgroup.mem_inf.2 ⟨hbhR, hb'C⟩
      have hu : b⁻¹ * (hh⁻¹ * b * hh) ∈ E := hK3 b hbA hbE hh hhN hb'Q
      have hy : y = z * (hh⁻¹ * b * hh) * z⁻¹ := by
        rw [hhdef, ← hg'b]; group
      have hsplit : b⁻¹ * y =
          (b⁻¹ * z * b * z⁻¹) * (z * (b⁻¹ * (hh⁻¹ * b * hh)) * z⁻¹) := by
        rw [hy]; group
      have hz_norm : z * (b⁻¹ * (hh⁻¹ * b * hh)) * z⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.1 (hRN.1 hzR) _).1 hu
      have hcommW : b⁻¹ * z * b * z⁻¹ ∈ W := by
        let B1 : ↥R := ⟨b⁻¹, R.inv_mem hbR⟩
        let Z' : ↥R := ⟨z, hzR⟩
        let π : ↥R →* (↥R ⧸ W.subgroupOf R) := QuotientGroup.mk' (W.subgroupOf R)
        have hc1 : ⁅π B1, π Z'⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
        have hc2 : π ⁅B1, Z'⁆ = 1 := by rw [map_commutatorElement]; exact hc1
        have hc3 : ⁅B1, Z'⁆ ∈ W.subgroupOf R :=
          (QuotientGroup.eq_one_iff _).1 hc2
        have hc4 : ((⁅B1, Z'⁆ : ↥R) : G) = b⁻¹ * z * b * z⁻¹ := by
          simp only [commutatorElement_def, B1, Z', inv_inv, Subgroup.coe_mul,
            Subgroup.coe_inv, mul_assoc]
        rw [← hc4]
        exact Subgroup.mem_subgroupOf.1 hc3
      rw [hsplit]
      exact W.mul_mem hcommW (hEW hz_norm)
    show ((QuotientGroup.mk' (W.subgroupOf R)) (⟨b⁻¹ * y, _⟩ : (Rs : Subgroup G))) = 1
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hkey)
  have hcommutator : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    haveI := hsimple
    rcases Subgroup.Normal.eq_bot_or_eq_top ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ with h1 | h1
    · exfalso
      obtain ⟨a₁, b₁, hab⟩ := hnonab
      apply hab
      have hmem : ⁅a₁, b₁⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a₁) (Subgroup.mem_top b₁)
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h1
  have hle : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ (MonoidHom.transfer φ).ker := by
    rw [Subgroup.commutator_le]
    intro x _ y' _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  apply htr
  have hgb : b ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
    rw [hcommutator]; exact Subgroup.mem_top b
  exact MonoidHom.mem_ker.1 (hle hgb)

section PieceB

variable {G : Type} [Group G] [Finite G]

@[expose] def PieceB_WC (E Q : Subgroup G) : Prop :=
  ∀ g : G, GLBConj g E ≤ Q → GLBConj g E = E

@[expose] def PieceB_SylZ (Z Q : Subgroup G) : Prop :=
  IsSylowIn 3 (Subgroup.centralizer (Z : Set G)) Q

@[expose] def PieceB_fus (E A : Subgroup G) (e : G) : Prop :=
  Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) →
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)

@[expose] def PieceB_core (E A : Subgroup G) (e : G) : Prop :=
  Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) →
    ∃ T : Subgroup G, (∀ n ∈ Subgroup.normalizer (A : Set G), ∀ t ∈ T, n⁻¹ * t * n ∈ T) ∧
      (∀ t ∈ T, ∀ z ∈ E ⊓ A, t * z = z * t) ∧
      (∀ a ∈ A, (∀ t ∈ T, t * a = a * t) → a ∈ E ⊓ A)

theorem mem_normalizer_of_GLBConj_eq {H : Subgroup G} {x : G} (hx : GLBConj x H = H) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have hk' : k ∈ GLBConj x H := by rw [hx]; exact hk
    obtain ⟨h, hh, hkh⟩ := Subgroup.mem_map.1 hk'
    have : x * k * x⁻¹ = h := by
      rw [← hkh]
      show x * (x⁻¹ * h * x⁻¹⁻¹) * x⁻¹ = h
      group
    rw [this]
    exact hh
  · intro hk
    have h1 : (MulAut.conj x⁻¹) (x * k * x⁻¹) ∈ GLBConj x H := Subgroup.mem_map_of_mem _ hk
    rw [hx] at h1
    have h2 : (MulAut.conj x⁻¹) (x * k * x⁻¹) = k := by
      simp only [MulAut.conj_apply]
      group
    rwa [h2] at h1

theorem GLBConj_le_of_mem_normalizer {Q H : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) (hHQ : H ≤ Q) : GLBConj x H ≤ Q := by
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k ∈ Q := hHQ hk
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (Q : Set G) := inv_mem hx
  exact (Subgroup.mem_normalizer_iff.1 hxinv k).1 hk'

theorem lemma113_ii_pieceB_cond {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (_hA : Claim113A (M := M) E A e K Q)
    (hWC : PieceB_WC E Q) (hSyl : PieceB_SylZ (E ⊓ A) Q) (hfus : PieceB_fus E A e)
    (hcore : PieceB_core E A e) :
    ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
  intro hN
  have hEQ : E ≤ Q := le_sup_left.trans h.hQ.2
  have heZ : e ∈ E ⊓ A := h.he.1
  have step1 : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (E : Set G) := fun x hx =>
    mem_normalizer_of_GLBConj_eq (hWC x (GLBConj_le_of_mem_normalizer hx hEQ))
  have step2 : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := step1.trans hN
  have step3 : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro n hn
    let S : Subgroup G := Q.map (MulAut.conj n⁻¹).toMonoidHom
    have hSC : S ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro z hz
      have hz' : n * z * n⁻¹ ∈ E ⊓ A := (Subgroup.mem_normalizer_iff.1 hn z).1 hz
      have hqc := Subgroup.mem_centralizer_iff.1 (hSyl.1 hq) (n * z * n⁻¹) hz'
      show z * (n⁻¹ * q * n⁻¹⁻¹) = n⁻¹ * q * n⁻¹⁻¹ * z
      calc z * (n⁻¹ * q * n⁻¹⁻¹) = n⁻¹ * ((n * z * n⁻¹) * q) * n := by group
        _ = n⁻¹ * (q * (n * z * n⁻¹)) * n := by rw [hqc]
        _ = n⁻¹ * q * n⁻¹⁻¹ * z := by group
    have hSp : IsPGroup 3 ↥S := hSyl.2.1.map _
    obtain ⟨c, hcC, hcS⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hSyl hSC hSp
    set g : G := c * n⁻¹ with hg
    have hsub : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
      rintro _ ⟨q, hq, rfl⟩
      have h1 := hcS (MulAut.conj n⁻¹ q) (Subgroup.mem_map_of_mem _ hq)
      show g * q * g⁻¹ ∈ Q
      have h2 : g * q * g⁻¹ = c * (MulAut.conj n⁻¹ q) * c⁻¹ := by
        simp only [MulAut.conj_apply, hg]
        group
      rw [h2]
      exact h1
    have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have : (MulAut.conj g) k ∈ Q.map (MulAut.conj g).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hk
        exact hsub this
      · intro hk
        have hcard : Nat.card ↥(Q.map (MulAut.conj g).toMonoidHom) = Nat.card ↥Q :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
        have heq : Q.map (MulAut.conj g).toMonoidHom = Q :=
          Subgroup.eq_of_le_of_card_ge hsub (le_of_eq hcard.symm)
        have hk2 : MulAut.conj g k ∈ Q.map (MulAut.conj g).toMonoidHom := by
          rw [heq]; exact hk
        obtain ⟨q, hq, hqk⟩ := Subgroup.mem_map.1 hk2
        have : q = k := (MulAut.conj g).injective hqk
        exact this ▸ hq
    have hgN : g ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) :=
      step2 hgQ
    have hcN : c ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
      apply Lemma113b.centralizer_le_normalizer_zpowers' e
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact Subgroup.mem_centralizer_iff.1 hcC e heZ
    have hnEq : n = g⁻¹ * c := by
      rw [hg]; group
    rw [hnEq]
    exact (Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)).mul_mem
      ((Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)).inv_mem hgN) hcN
  obtain ⟨T, hTnorm, hTZ, hTcap⟩ := hcore step3
  have key : ∀ n ∈ Subgroup.normalizer (A : Set G), ∀ z ∈ E ⊓ A, n⁻¹ * z * n ∈ E ⊓ A := by
    intro n hn z hz
    have hzA : n⁻¹ * z * n ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) z).1 (Subgroup.mem_inf.1 hz).2
      simpa [inv_inv] using this
    refine hTcap (n⁻¹ * z * n) hzA ?_
    intro t ht
    have hnt : n * t * n⁻¹ ∈ T := by
      have := hTnorm n⁻¹ (inv_mem hn) t ht
      simpa [inv_inv] using this
    have hcomm := hTZ (n * t * n⁻¹) hnt z hz
    calc t * (n⁻¹ * z * n) = n⁻¹ * ((n * t * n⁻¹) * z) * n := by group
      _ = n⁻¹ * (z * (n * t * n⁻¹)) * n := by rw [hcomm]
      _ = (n⁻¹ * z * n) * t := by group
  have step4 : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have := key n⁻¹ (inv_mem hn) z hz
      simpa [inv_inv] using this
    · intro hz
      have h3 : n⁻¹ * (n * z * n⁻¹) * n = z := by group
      have := key n hn _ hz
      rw [h3] at this
      exact this
  exact hfus hN (step4.trans step3)

end PieceB

section PieceC

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_le {H : Subgroup G} {x : G} (h : ∀ k ∈ H, x * k * x⁻¹ ∈ H) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hcard : Nat.card ↥(H.map (MulAut.conj x).toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have heq : H.map (MulAut.conj x).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact h k hk
  · intro hk
    have hk2 : MulAut.conj x k ∈ H.map (MulAut.conj x).toMonoidHom := by
      rw [heq]; exact hk
    obtain ⟨q, hq, hqk⟩ := Subgroup.mem_map.1 hk2
    have : q = k := (MulAut.conj x).injective hqk
    exact this ▸ hq

theorem eq_of_normalizer_inf_eq {p : ℕ} [Fact p.Prime] {P R : Subgroup G}
    (hP : IsPGroup p P) (hRP : R ≤ P) (hN : P ⊓ Subgroup.normalizer (R : Set G) = R) : R = P := by
  by_contra hne
  have hHtop : R.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    have hPR : P ≤ R := (Subgroup.subgroupOf_eq_top).1 htop
    exact le_antisymm hRP hPR
  haveI hnil : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hP
  have hlt := (normalizerCondition_of_isNilpotent (G := ↥P)) (R.subgroupOf P) hHtop
  have hnot : ¬ Subgroup.normalizer ((R.subgroupOf P : Subgroup ↥P) : Set ↥P) ≤ R.subgroupOf P :=
    fun hle => lt_irrefl _ (lt_of_lt_of_le hlt hle)
  obtain ⟨y, hyN, hyH⟩ := SetLike.not_le_iff_exists.1 hnot
  have hyR : (y : G) ∈ Subgroup.normalizer (R : Set G) := by
    apply mem_normalizer_of_conj_le
    intro k hk
    have hkP : (⟨k, hRP hk⟩ : ↥P) ∈ R.subgroupOf P := Subgroup.mem_subgroupOf.2 hk
    have hyk := (Subgroup.mem_normalizer_iff.1 hyN ⟨k, hRP hk⟩).1 hkP
    exact Subgroup.mem_subgroupOf.1 hyk
  have hyPN : (y : G) ∈ P ⊓ Subgroup.normalizer (R : Set G) := ⟨y.2, hyR⟩
  rw [hN] at hyPN
  exact hyH (Subgroup.mem_subgroupOf.2 hyPN)

theorem isSylowIn_top_of_normalizer_le {p : ℕ} [Fact p.Prime] {N R : Subgroup G}
    (hR : IsSylowIn p N R) (hNR : Subgroup.normalizer (R : Set G) ≤ N) : IsSylowIn p ⊤ R := by
  obtain ⟨P', hRP'⟩ := IsPGroup.exists_le_sylow hR.2.1
  have hinf : (P' : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) = R := by
    apply le_antisymm
    · have hle : (P' : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) ≤ N :=
        inf_le_right.trans hNR
      have hpg : IsPGroup p ↥((P' : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) :=
        P'.isPGroup'.to_le inf_le_left
      have hRle : R ≤ (P' : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) :=
        le_inf hRP' Subgroup.le_normalizer
      exact (hR.2.2 _ hle hpg hRle).le
    · exact le_inf hRP' Subgroup.le_normalizer
  have hRP : R = (P' : Subgroup G) := eq_of_normalizer_inf_eq P'.isPGroup' hRP' hinf
  refine ⟨le_top, hR.2.1, fun R' _ hR'p hRle => ?_⟩
  rw [hRP] at hRle ⊢
  exact P'.is_maximal' hR'p hRle

theorem isElemAbelian_GLBConj {p : ℕ} {E' : Subgroup G} (g : G) (h : IsElemAbelian p E') :
    IsElemAbelian p (GLBConj g E') := by
  obtain ⟨hc, hx⟩ := h
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, ha'⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hb'⟩ := Subgroup.mem_map.1 y.2
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · intro x hxg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hxg
    show ((MulAut.conj g⁻¹).toMonoidHom a) ^ p = 1
    rw [← map_pow, hx a ha, map_one]

theorem GLBConj_thompsonJ_eq {p : ℕ} {R : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (R : Set G)) : GLBConj n (thompsonJ p R) = thompsonJ p R := by
  have hEk : ∀ (g : G) (E' : Subgroup G), IsEkIn p (CFSG.Open.pRank p R) R E' →
      g ∈ Subgroup.normalizer (R : Set G) → IsEkIn p (CFSG.Open.pRank p R) R (GLBConj g E') := by
    intro g E' hE' hg
    refine ⟨?_, ?_, ?_⟩
    · exact GLBConj_le_of_mem_normalizer hg hE'.1
    · exact isElemAbelian_GLBConj g hE'.2.1
    · rw [← hE'.2.2]
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hmono : ∀ g : G, g ∈ Subgroup.normalizer (R : Set G) →
      GLBConj g (thompsonJ p R) ≤ thompsonJ p R := by
    intro g hg
    unfold thompsonJ
    unfold GLBConj
    rw [Subgroup.map_iSup]
    refine iSup_le fun E' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hE' => ?_
    have hmem : IsEkIn p (CFSG.Open.pRank p R) R (GLBConj g E') := hEk g E' hE' hg
    exact le_iSup₂ (f := fun (E'' : Subgroup G) (_ : IsEkIn p (CFSG.Open.pRank p R) R E'') => E'')
      (GLBConj g E') hmem
  apply le_antisymm (hmono n hn)
  have hinv : n⁻¹ ∈ Subgroup.normalizer (R : Set G) := inv_mem hn
  have h2 := hmono n⁻¹ hinv
  have h3 : GLBConj n (GLBConj n⁻¹ (thompsonJ p R)) = thompsonJ p R := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      show (MulAut.conj n⁻¹) ((MulAut.conj n⁻¹⁻¹) z) ∈ thompsonJ p R
      have hzz : (MulAut.conj n⁻¹) ((MulAut.conj n⁻¹⁻¹) z) = z := by
        simp only [MulAut.conj_apply]
        group
      rw [hzz]
      exact hz
    · intro hx
      refine Subgroup.mem_map.2 ⟨MulAut.conj n⁻¹⁻¹ x, ?_, ?_⟩
      · exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
  calc thompsonJ p R = GLBConj n (GLBConj n⁻¹ (thompsonJ p R)) := h3.symm
    _ ≤ GLBConj n (thompsonJ p R) := by
      exact Subgroup.map_mono h2

theorem lemma113_ii_pieceC_cond {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (_hA : Claim113A (M := M) E A e K Q)
    (_hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    (hEC : IsSylowIn 3 (Subgroup.centralizer (E : Set G)) E) (hQcard : Nat.card Q = 3 ^ 5)
    (hR1 : ∃ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R ∧ Q ≤ R ∧
      Nat.card R = 3 ^ 8)
    (hR2 : ∀ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
      Nat.card R = 3 ^ 8 → E = thompsonJ 3 R) :
    Claim113C E A Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hRN, hQR, hR8⟩ := hR1
  have hEJ : E = thompsonJ 3 R := hR2 R hRN hQR hR8
  have hNR : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (E : Set G) := by
    intro n hn
    apply mem_normalizer_of_GLBConj_eq
    have hJ := GLBConj_thompsonJ_eq (p := 3) hn
    rw [← hEJ] at hJ
    exact hJ
  exact ⟨hEC, hQcard, R, hRN, hQR, hR8, hEJ, isSylowIn_top_of_normalizer_le hRN hNR⟩

end PieceC

section Leaves

open Lemma113b

@[expose] def Lemma113_ii_pieceB_Claims : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q),
    PieceB_WC E Q ∧ PieceB_SylZ (E ⊓ A) Q ∧ PieceB_fus E A e ∧ PieceB_core E A e

theorem lemma113_ii_pieceB_of (hP : Lemma113_ii_pieceB_Claims) :
    Lemma113_ii_pieceBStatement := by
  intro G _ _ m B M E A a e K Q h hA
  obtain ⟨h1, h2, h3, h4⟩ := hP h hA
  exact lemma113_ii_pieceB_cond h hA h1 h2 h3 h4

@[expose] def Lemma113_ii_pieceC_Claims : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)),
    IsSylowIn 3 (Subgroup.centralizer (E : Set G)) E ∧ Nat.card Q = 3 ^ 5 ∧
      (∃ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R ∧ Q ≤ R ∧
        Nat.card R = 3 ^ 8) ∧
      (∀ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
        Nat.card R = 3 ^ 8 → E = thompsonJ 3 R)

theorem lemma113_ii_pieceC_of (hP : Lemma113_ii_pieceC_Claims) :
    Lemma113_ii_pieceCStatement := by
  intro G _ _ m B M E A a e K Q h hA hB
  obtain ⟨h1, h2, h3, h4⟩ := hP h hA hB
  exact lemma113_ii_pieceC_cond h hA hB h1 h2 h3 h4

@[expose] def Lemma113_ii_pieceD_Claims : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hC : Claim113C E A Q),
    (∀ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
      PieceD_R2 e R) ∧
    (∀ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
      PieceD_R4 E R) ∧
    PieceD_K3 E Q A e

theorem lemma113_ii_pieceD_of (hI : Lemma113b.Input32_7) (hP : Lemma113_ii_pieceD_Claims) :
    Lemma113_ii_pieceDStatement := by
  intro G _ _ m B M E A a e K Q h hC
  obtain ⟨h1, h2, h3⟩ := hP h hC
  exact lemma113_ii_pieceD_cond hI h hC h1 h2 h3

end Leaves

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
