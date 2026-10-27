module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def LayerData166 (J : Type) [Group J] (q r : ℕ) : Prop :=
  ∃ (BJ SJ EJ : Subgroup J), IsElemAbelian q BJ ∧ Nat.card BJ = q ^ r ∧
    IsPGroup 2 SJ ∧ BJ ≤ Subgroup.normalizer (SJ : Set J) ∧
    BJ ⊓ Subgroup.centralizer (SJ : Set J) = ⊥ ∧
    EJ ≤ BJ ∧ Nat.card EJ = q ^ 2 ∧
    GLAPLayer q (Subgroup.centralizer (EJ : Set J)) ≠ ⊥

@[expose] def LayerData166At (lab : GLALabel) : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (q : ℕ), HasLabel J (fun l : GLALabel => l = lab) →
    Subgroup.center J = ⊥ → q.Prime → q ≠ 2 → q ∣ 2 ^ lab.n - 1 → LayerData166 J q lab.rank

theorem LayerData166.of_mulEquiv {J R : Type} [Group J] [Group R] [Finite J] [Finite R]
    {q r : ℕ} (e : J ≃* R) (h : LayerData166 R q r) (hq : q.Prime) :
    LayerData166 J q r := by
  obtain ⟨BJ, SJ, EJ, hBJel, hBJcard, hSJ2, hBJN, hBJcent, hEJB, hEJcard, hEJlayer⟩ := h
  have hmapc : (Subgroup.centralizer (SJ : Set R)).map e.symm.toMonoidHom =
      Subgroup.centralizer ((SJ.map e.symm.toMonoidHom : Subgroup J) : Set J) := by
    rw [CFSG.Walter.map_centralizer_mulEquiv e.symm (SJ : Set R), ← MulEquiv.coe_toMonoidHom,
      Subgroup.coe_map]
  have hmapcE : (Subgroup.centralizer (EJ : Set R)).map e.symm.toMonoidHom =
      Subgroup.centralizer ((EJ.map e.symm.toMonoidHom : Subgroup J) : Set J) := by
    rw [CFSG.Walter.map_centralizer_mulEquiv e.symm (EJ : Set R), ← MulEquiv.coe_toMonoidHom,
      Subgroup.coe_map]
  have htrans : (GLAPLayer q (Subgroup.centralizer (EJ : Set R))).map e.symm.toMonoidHom =
      GLAPLayer q (Subgroup.centralizer ((EJ.map e.symm.toMonoidHom : Subgroup J) : Set J)) := by
    rw [← glaPLayer_map hq e.symm.injective (Subgroup.centralizer (EJ : Set R)), hmapcE]
  have hEJlayer' : GLAPLayer q
      (Subgroup.centralizer ((EJ.map e.symm.toMonoidHom : Subgroup J) : Set J)) ≠ ⊥ := by
    intro hbot
    exact hEJlayer ((Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1
      (by rw [htrans, hbot]))
  refine ⟨BJ.map e.symm.toMonoidHom, SJ.map e.symm.toMonoidHom, EJ.map e.symm.toMonoidHom,
    hBJel.map e.symm.toMonoidHom, ?_, hSJ2.map e.symm.toMonoidHom, ?_, ?_,
    Subgroup.map_mono hEJB, ?_, hEJlayer'⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hBJcard]
  · exact (Subgroup.map_mono hBJN).trans (Subgroup.le_normalizer_map e.symm.toMonoidHom)
  · rw [← hmapc, ← Subgroup.map_inf _ _ _ e.symm.injective, hBJcent, Subgroup.map_bot]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hEJcard]

private theorem commute_zpowers_of_le {K : Type} [Group K] {J D : Subgroup K} {x : K}
    (hx : ∀ j ∈ J, j * x = x * j) (hD : D ≤ J) :
    ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ D, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact ((show Commute x b from (hx b (hD hb)).symm).zpow_left m).eq

private theorem inf_zpowers_eq_bot_of_le {K : Type} [Group K] {J D : Subgroup K} {x : K}
    (hD : D ≤ J) (hzx : Subgroup.zpowers x ⊓ J = ⊥) : Subgroup.zpowers x ⊓ D = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro y ⟨hyx, hyD⟩
  have h : y ∈ Subgroup.zpowers x ⊓ J := ⟨hyx, hD hyD⟩
  rw [hzx] at h
  simpa using h

private theorem card_zpowers_sup_eq_mul {K : Type} [Group K] [Finite K] {D : Subgroup K} {x : K}
    {q : ℕ} (hxq : x ^ q = 1) (hx1 : x ≠ 1) (hq : q.Prime)
    (hc : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ D, a * b = b * a)
    (hinf : Subgroup.zpowers x ⊓ D = ⊥) :
    Nat.card ↥(Subgroup.zpowers x ⊔ D) = q * Nat.card ↥D := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) D hc
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime hxq hx1] at hcard
  exact hcard

section Certs


theorem exists_concl166S_of_layerData_of_comp {K : Type} [Group K] [Finite K] {p q : ℕ}
    {x : K} {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2) (hxq : x ^ q = 1) (hx1 : x ≠ 1)
    (hZK : Subgroup.center K = ⊥) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomp : IsComponentOf J (Subgroup.centralizer ({x} : Set K)) ∧
      GLALayer (Subgroup.centralizer ({x} : Set K)) = J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J)
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hZJ : Subgroup.center ↥J = ⊥) (hmult : TrivialMultiplierT ↥J)
    (hD : LayerData166 ↥J q (evenRank K - 1)) :
    ∃ B' : Subgroup K, Concl166S K p q B' x J := by
  obtain ⟨BJ, SJ, EJ, hBJel, hBJcard, hSJ2, hBJN, hBJcent, hEJB, hEJcard, hEJlayer⟩ := hD
  haveI : Fact q.Prime := ⟨hq⟩
  have hxcomm : ∀ j ∈ J, j * x = x * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJx hj)
  have hzx : Subgroup.zpowers x ⊓ J = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro y ⟨hyx, hyJ⟩
    have hyc : (⟨y, hyJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyx
      apply Subtype.ext
      exact ((show Commute (g : K) x from hxcomm (g : K) g.2).zpow_right k).eq
    have hy1 : (⟨y, hyJ⟩ : ↥J) = 1 := by
      have hmem : (⟨y, hyJ⟩ : ↥J) ∈ (⊥ : Subgroup ↥J) := by
        rw [← hZJ]
        exact hyc
      simpa using hmem
    simpa using congrArg Subtype.val hy1
  let B' : Subgroup K := Subgroup.zpowers x ⊔ BJ.map J.subtype
  let S : Subgroup K := SJ.map J.subtype
  let E : Subgroup K := Subgroup.zpowers x ⊔ EJ.map J.subtype
  have hBJmapJ : BJ.map J.subtype ≤ J := Subgroup.map_subtype_le BJ
  have hEJmapJ : EJ.map J.subtype ≤ J := Subgroup.map_subtype_le EJ
  have hB'J : B' ⊓ J = BJ.map J.subtype := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨hyB, hyJ⟩
      have hb' : y ∈ BJ.map J.subtype ⊔ Subgroup.zpowers x := by
        rw [sup_comm]
        exact hyB
      obtain ⟨j, hj, k, rfl⟩ := exists_mul_zpow_eq_of_mem_sup_zpowers
        (fun b hb => hxcomm b (hBJmapJ hb)) hb'
      have hxk : x ^ k ∈ J := by
        have h2 : j⁻¹ * (j * x ^ k) ∈ J := J.mul_mem (J.inv_mem (hBJmapJ hj)) hyJ
        simpa using h2
      have hxk1 : x ^ k = 1 := by
        have hmem : x ^ k ∈ Subgroup.zpowers x ⊓ J :=
          ⟨Subgroup.zpow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) k, hxk⟩
        rw [hzx] at hmem
        simpa using hmem
      rw [hxk1, mul_one]
      exact hj
    · intro y hy
      exact ⟨Subgroup.mem_sup_right hy, hBJmapJ hy⟩
  have hinfB : Subgroup.zpowers x ⊓ BJ.map J.subtype = ⊥ :=
    inf_zpowers_eq_bot_of_le hBJmapJ hzx
  have hinfE : Subgroup.zpowers x ⊓ EJ.map J.subtype = ⊥ :=
    inf_zpowers_eq_bot_of_le hEJmapJ hzx
  have hxcard : Nat.card (Subgroup.zpowers x) = q := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxq hx1]
  have hcardBj : Nat.card ↥(BJ.map J.subtype) = q ^ (evenRank K - 1) := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hBJcard]
  have hcardEj : Nat.card ↥(EJ.map J.subtype) = q ^ 2 := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hEJcard]
  have hcB : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ BJ.map J.subtype, a * b = b * a :=
    commute_zpowers_of_le hxcomm hBJmapJ
  have hcE : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ EJ.map J.subtype, a * b = b * a :=
    commute_zpowers_of_le hxcomm hEJmapJ
  have hcardB : Nat.card B' = q ^ evenRank K := by
    change Nat.card ↥(Subgroup.zpowers x ⊔ BJ.map J.subtype) = q ^ evenRank K
    have hqpow : q * q ^ (evenRank K - 1) = q ^ evenRank K := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [card_zpowers_sup_eq_mul hxq hx1 hq hcB hinfB, hcardBj, hqpow]
  have hcardE : Nat.card E = q ^ 3 := by
    change Nat.card ↥(Subgroup.zpowers x ⊔ EJ.map J.subtype) = q ^ 3
    have hq3 : q * q ^ 2 = q ^ 3 := by
      rw [mul_comm, ← pow_succ]
    rw [card_zpowers_sup_eq_mul hxq hx1 hq hcE hinfE, hcardEj, hq3]
  have hxel : IsElemAbelian q (Subgroup.zpowers x) := isElemAbelian_zpowers hxq
  have hBJel' : IsElemAbelian q (BJ.map J.subtype) := hBJel.map J.subtype
  have hEJel : IsElemAbelian q (EJ.map J.subtype) :=
    hBJel'.mono (Subgroup.map_mono hEJB)
  have hB'el : IsElemAbelian q B' := hxel.sup_of_commute hBJel' hcB
  have hEel : IsElemAbelian q E := hxel.sup_of_commute hEJel hcE
  have hCJE : J ⊓ Subgroup.centralizer (E : Set K) =
      (Subgroup.centralizer (EJ : Set ↥J)).map J.subtype := by
    have hJCx : J ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set K) = J :=
      inf_eq_left.2 (by
        rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
        exact hJx)
    rw [CFSG.centralizer_sup_eq, ← inf_assoc, hJCx]
    exact (map_centralizer_subtype EJ).symm
  have he3 : GLAPLayer q (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥ := by
    have hgl := glaPLayer_map hq J.subtype_injective (Subgroup.centralizer (EJ : Set ↥J))
    intro hbot
    have h1 : (GLAPLayer q (Subgroup.centralizer (EJ : Set ↥J))).map J.subtype = ⊥ := by
      rw [← hgl, ← hCJE, hbot]
    exact hEJlayer ((Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 h1)
  have hSJ' : S ≤ J := Subgroup.map_subtype_le SJ
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set K) := by
    refine Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer (S : Set K) ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hxcomm s (hSJ' hs)
  have hBS : B' ≤ Subgroup.normalizer (S : Set K) :=
    sup_le hxN (map_le_normalizer_map hBJN)
  have hBJSbot : B' ⊓ J ⊓ Subgroup.centralizer (S : Set K) = ⊥ := by
    rw [hB'J, inf_centralizer_map, hBJcent, Subgroup.map_bot]
  have hBJS : B' ⊓ J ⊓ Subgroup.centralizer (S : Set K) ≤ Subgroup.zpowers x := by
    rw [hBJSbot]
    exact bot_le
  have hBJ : B' ≤ J ⊔ Subgroup.zpowers x := by
    refine sup_le ?_ ?_
    · exact le_sup_right
    · exact (Subgroup.map_subtype_le BJ).trans le_sup_left
  have hrankinf : evenRank K ≤ CFSG.Open.pRank q (B' ⊓ J) + 2 := by
    have hle : evenRank K - 1 ≤ CFSG.Open.pRank q (B' ⊓ J) := by
      refine CFSG.SectionRank.le_pRank hq.one_lt (k := evenRank K - 1) ?_
        (hBJel.map J.subtype) hcardBj
      rw [hB'J]
    omega
  have hsu : 3 ∣ Nat.card (Subgroup.center K) →
      (∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      J = ⊤ ∧ q = 3 ∧ ∀ k : K, k * x = x * k := by
    intro h3 _
    rw [hZK, Subgroup.card_bot] at h3
    exact absurd h3 (Nat.Prime.not_dvd_one Nat.prime_three)
  have hodd : Odd (Nat.card (Subgroup.center ↥J)) := by
    rw [hZJ, Subgroup.card_bot]
    exact odd_one
  exact ⟨B', concl166S_of_witness_of_comp hq hq2 hB'el
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    hx1 hcardB he hJx hJq hcomp labJ hJlab hshape hm2 hodd hdvd (Or.inl ⟨hZJ, hmult⟩)
    E (sup_le le_sup_left ((Subgroup.map_mono hEJB).trans le_sup_right)) hEel hcardE
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)) he3 hBJ hrankinf S
    (Subgroup.map_subtype_le SJ) (hSJ2.map J.subtype) hBS hBJS hsu⟩

theorem exists_concl166S_of_layerData {K : Type} [Group K] [Finite K] {p q : ℕ} {x : K}
    {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2) (hxq : x ^ q = 1) (hx1 : x ≠ 1)
    (hZK : Subgroup.center K = ⊥) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set K),
      ∀ h ∈ Subgroup.centralizer ({x} : Set K), g * h * g⁻¹ * h⁻¹ ∈ J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J)
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hZJ : Subgroup.center ↥J = ⊥) (hmult : TrivialMultiplierT ↥J)
    (hD : LayerData166 ↥J q (evenRank K - 1)) :
    ∃ B' : Subgroup K, Concl166S K p q B' x J :=
  exists_concl166S_of_layerData_of_comp hq hq2 hxq hx1 hZK he hJx hJq
    (isComponentOf_and_glaLayer_eq_of_commutator_mem hJx hcomm hJq) labJ hJlab hshape hm2 hdvd
    hZJ hmult hD

theorem exists_concl166S_of_layerData166At_of_comp {K : Type} [Group K] [Finite K]
    {p q : ℕ} {x : K} {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2)
    (hxq : x ^ q = 1) (hx1 : x ≠ 1)
    (hZK : Subgroup.center K = ⊥) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomp : IsComponentOf J (Subgroup.centralizer ({x} : Set K)) ∧
      GLALayer (Subgroup.centralizer ({x} : Set K)) = J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J)
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hZJ : Subgroup.center ↥J = ⊥) (hmult : TrivialMultiplierT ↥J)
    (hD : LayerData166At labJ) (hqn : q ∣ 2 ^ labJ.n - 1)
    (hrank : labJ.rank = evenRank K - 1) :
    ∃ B' : Subgroup K, Concl166S K p q B' x J := by
  have hD' : LayerData166 ↥J q (evenRank K - 1) := by
    have h := hD ↥J q hJlab hZJ hq hq2 hqn
    rwa [hrank] at h
  exact exists_concl166S_of_layerData_of_comp hq hq2 hxq hx1 hZK he hJx hJq hcomp labJ
    hJlab hshape hm2 hdvd hZJ hmult hD'

theorem exists_concl166S_of_layerData166At {K : Type} [Group K] [Finite K] {p q : ℕ} {x : K}
    {J : Subgroup K} (hq : q.Prime) (hq2 : q ≠ 2) (hxq : x ^ q = 1) (hx1 : x ≠ 1)
    (hZK : Subgroup.center K = ⊥) (he : 4 ≤ evenRank K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set K)) (hJq : CFSG.IsQuasisimple ↥J)
    (hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set K),
      ∀ h ∈ Subgroup.centralizer ({x} : Set K), g * h * g⁻¹ * h⁻¹ ∈ J)
    (labJ : GLALabel) (hJlab : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hshape : ∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center K)) labJ)
    (hm2 : evenRank K + 2 ≤ twoRank ↥J)
    (hdvd : p * q ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hZJ : Subgroup.center ↥J = ⊥) (hmult : TrivialMultiplierT ↥J)
    (hD : LayerData166At labJ) (hqn : q ∣ 2 ^ labJ.n - 1)
    (hrank : labJ.rank = evenRank K - 1) :
    ∃ B' : Subgroup K, Concl166S K p q B' x J :=
  exists_concl166S_of_layerData166At_of_comp hq hq2 hxq hx1 hZK he hJx hJq
    (isComponentOf_and_glaLayer_eq_of_commutator_mem hJx hcomm hJq) labJ hJlab hshape hm2 hdvd
    hZJ hmult hD hqn hrank

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
