module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInner
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.PCore.CommutingBalance

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

open scoped Pointwise

private theorem mul_conj_mem_centralizer {G : Type*} [Group G] {D : Subgroup G} {d y : G}
    (hd : d ∈ D) (hy : y ∈ centralizer (D : Set G)) :
    d * y * d⁻¹ ∈ centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro e he
  have h1 : y * (d⁻¹ * e) = (d⁻¹ * e) * y :=
    (hy (d⁻¹ * e) (D.mul_mem (D.inv_mem hd) he)).symm
  have h2 : y * (e * d) = (e * d) * y := (hy (e * d) (D.mul_mem he hd)).symm
  calc e * (d * y * d⁻¹) = (e * d) * y * d⁻¹ := by group
    _ = y * (e * d) * d⁻¹ := by rw [← h2]
    _ = y * e := by group
    _ = e * y := (hy e he).symm
    _ = d * (d⁻¹ * e) * y := by group
    _ = d * ((d⁻¹ * e) * y) := by rw [mul_assoc]
    _ = d * (y * (d⁻¹ * e)) := by rw [← h1]
    _ = (d * y * d⁻¹) * e := by group

private theorem conj_mem_centralizer {G : Type*} [Group G] {K : Subgroup G} {g y : G}
    (hg : g ∈ normalizer (K : Set G)) (hy : y ∈ centralizer (K : Set G)) :
    g * y * g⁻¹ ∈ centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro e he
  have hge : g⁻¹ * e * g ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) e).mp he
  have hy1 : (g⁻¹ * e * g) * y = y * (g⁻¹ * e * g) := hy _ hge
  calc e * (g * y * g⁻¹) = g * (g⁻¹ * e * g) * y * g⁻¹ := by group
    _ = g * ((g⁻¹ * e * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * e * g)) * g⁻¹ := by rw [hy1]
    _ = (g * y * g⁻¹) * e := by group

private theorem pow_three_mul_mem_centralizer {G : Type*} [Group G] {K : Subgroup G} {g m : G}
    (hg : g ∈ normalizer (K : Set G)) (hg3 : g ^ 3 ∈ centralizer (K : Set G))
    (hm : m ∈ centralizer (K : Set G)) : (g * m) ^ 3 ∈ centralizer (K : Set G) := by
  have hg2 : g ^ 2 ∈ normalizer (K : Set G) := by
    rw [pow_two]
    exact (Subgroup.normalizer (K : Set G)).mul_mem hg hg
  have h1 : g⁻¹ * m * g ∈ centralizer (K : Set G) := by
    simpa using conj_mem_centralizer (inv_mem hg) hm
  have h2 : (g ^ 2)⁻¹ * m * g ^ 2 ∈ centralizer (K : Set G) := by
    simpa using conj_mem_centralizer (inv_mem hg2) hm
  have hkey : (g * m) ^ 3
      = g ^ 3 * ((g ^ 2)⁻¹ * m * g ^ 2) * (g⁻¹ * m * g) * m := by
    simp only [pow_succ, pow_zero, one_mul, mul_one, inv_pow]
    group
  rw [hkey]
  exact mul_mem (mul_mem (mul_mem hg3 h2) h1) hm

theorem isElemAbelian_sup_zpowers_of_notMem {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {A : Subgroup X} {a : ℕ} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ a)
    {y : X} (hy : y ∉ A) (hyp : y ^ p = 1) (hcomm : ∀ b ∈ A, b * y = y * b) :
    IsElemAbelian p (A ⊔ zpowers y) ∧ Nat.card ↥(A ⊔ zpowers y) = p ^ (a + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hy1 : y ≠ 1 := fun h => hy (h ▸ A.one_mem)
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hcardE : Nat.card (zpowers y) = p := by rw [Nat.card_zpowers, hyord]
  have hEab : IsElemAbelian p (zpowers y) := isElemAbelian_zpowers hyp
  have hEA : zpowers y ≤ centralizer (A : Set X) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr hcomm)
  have hcomm' : ∀ a ∈ A, ∀ b ∈ zpowers y, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hEA hb)) a ha
  have hinf : A ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    by_contra ht1
    have hle : zpowers t ≤ zpowers y := Subgroup.zpowers_le.mpr ht.2
    have hdvdp : Nat.card (zpowers t) ∣ p := by
      rw [← hyord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).mp hdvdp with h1 | h1
    · have hbot : zpowers t = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact ht1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers t))
    · have hcardt : Nat.card (zpowers t) = p := h1
      have heq : zpowers t = zpowers y :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcardE, hcardt])
      exact hy ((Subgroup.zpowers_le.mpr ht.1) (heq.symm ▸ Subgroup.mem_zpowers y))
  refine ⟨IsElemAbelian.sup_of_commute hA hEab hcomm', ?_⟩
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A (zpowers y)
      (hEA.trans (Subgroup.centralizer_le_normalizer (A : Set X))) (disjoint_iff.mpr hinf),
    hAc, hcardE, pow_succ]

theorem exists_mul_commute_of_mem_normalizer (h714 : SevenOneFourField) {X : Type} [Group X]
    [Finite X] (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Subgroup X} (hD : CFSG.IsComponent D) (hr : CFSG.Open.pRank p D = 1) {x : X}
    (hx : x ∈ normalizer (D : Set X)) (hxp : x ^ p = 1) :
    ∃ l ∈ D, (x * l) ^ p ∈ centralizer (D : Set X) ∧
      ∃ z ∈ D, orderOf z = p ∧ x * l * z = z * (x * l) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNd : D ≤ normalizer (D : Set X) := Subgroup.le_normalizer
  have hLE : D ≤ normalizer (centralizer (D : Set X)) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd y hy
    exact mul_conj_mem_centralizer hd hy
  by_cases hxsup : x ∈ D ⊔ centralizer (D : Set X)
  · have hcoe : (↑(D ⊔ centralizer (D : Set X)) : Set X) =
        (D : Set X) * (centralizer (D : Set X) : Set X) :=
      Subgroup.coe_mul_of_left_le_normalizer_right D (centralizer (D : Set X)) hLE
    have hmem : x ∈ (D : Set X) * (centralizer (D : Set X) : Set X) := by
      rw [← hcoe]; exact hxsup
    obtain ⟨d, hdD, y, hyC, hdy⟩ := hmem
    have hxd : x * d⁻¹ = d * y * d⁻¹ := by rw [← hdy]
    have hcent : d * y * d⁻¹ ∈ centralizer (D : Set X) := mul_conj_mem_centralizer hdD hyC
    refine ⟨d⁻¹, D.inv_mem hdD, ?_, ?_⟩
    · rw [hxd]
      exact Subgroup.pow_mem (K := centralizer (D : Set X)) hcent p
    · obtain ⟨B, hBD, -, hBcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt D
      have hBcard' : Nat.card B = p := by rw [hBcard, hr, pow_one]
      obtain ⟨zB, hzBord⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) p (by rw [hBcard'])
      have hzBD : (zB : X) ∈ D := hBD zB.2
      have hzBord' : orderOf (zB : X) = p := (Subgroup.orderOf_coe zB).trans hzBord
      refine ⟨(zB : X), hzBD, hzBord', ?_⟩
      rw [hxd]
      exact (Subgroup.mem_centralizer_iff.mp hcent (zB : X) hzBD).symm
  · let N : Subgroup X := normalizer (D : Set X)
    let L : Subgroup ↥N := D.subgroupOf N
    let x' : ↥N := ⟨x, hx⟩
    have hLcomp : CFSG.IsComponent L := CFSG.LocalCores.component_overgroup hD hNd
    have hLnorm : L.Normal := Subgroup.normal_in_normalizer
    have hLrank : CFSG.Open.pRank p L = 1 := by
      change CFSG.Open.pRank p (D.subgroupOf N) = 1
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (D.subgroupOf N),
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
          (Subgroup.subgroupOfEquivOfLe hNd),
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup D]
      exact hr
    have hsup_eq : L ⊔ centralizer (L : Set ↥N) =
        (D ⊔ centralizer (D : Set X)).subgroupOf N := by
      change (D.subgroupOf N) ⊔ centralizer (D.subgroupOf N : Set ↥N) =
        (D ⊔ centralizer (D : Set X)).subgroupOf N
      rw [Subgroup.subgroupOf_sup hNd (Subgroup.centralizer_le_normalizer (D : Set X)),
        CFSG.centralizer_subgroupOf_eq D N hNd]
    have hx'sup : x' ∉ L ⊔ centralizer (L : Set ↥N) := by
      intro hmem
      rw [hsup_eq, Subgroup.mem_subgroupOf] at hmem
      exact hxsup hmem
    have hx'p : x' ^ p = 1 := by
      apply Subtype.ext
      simpa [x'] using hxp
    obtain ⟨l', hl'L, hl'pc, z', hz'L, hz'ord', hz'comm'⟩ :=
      h714 ↥N (hX.subgroup N) p hp hp2 L hLcomp hLnorm hLrank x' hx'sup
        (by rw [hx'p]; exact Subgroup.one_mem _)
    refine ⟨(l' : X), Subgroup.mem_subgroupOf.mp hl'L, ?_, (z' : X),
      Subgroup.mem_subgroupOf.mp hz'L, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hdL : (⟨d, hNd hd⟩ : ↥N) ∈ L := Subgroup.mem_subgroupOf.mpr hd
      have hcomm := Subgroup.mem_centralizer_iff.mp hl'pc (⟨d, hNd hd⟩ : ↥N) hdL
      have hcommX : d * ((x' * l') ^ p : X) = ((x' * l') ^ p : X) * d := by
        simpa only [Subgroup.coe_pow, Subgroup.coe_mul] using congrArg Subtype.val hcomm
      have hpow : ((x' * l') ^ p : X) = (x * (l' : X)) ^ p := rfl
      rw [hpow] at hcommX
      exact hcommX
    · exact (Subgroup.orderOf_coe z').trans hz'ord'
    · have h := congrArg Subtype.val hz'comm'
      simpa only [Subgroup.coe_mul] using h

theorem mem_layer_of_mem_compNormalizer (h714 : SevenOneFourField) (h72 : KFactOmegaNotCentral)
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {C : Subgroup X} {q : X}
    (hcomp : ∀ D : Subgroup X, CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
    (hinj : Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom))
    (hrank : ∀ D : Subgroup X, CFSG.IsComponent D → CFSG.Open.pRank 3 D = 1)
    (hY : centralizer (CFSG.layer X : Set X) = ⊥) {x : X} (hx : x ∈ compNormalizer X)
    (hx3 : x ^ 3 = 1) : x ∈ CFSG.layer X := by
  classical
  by_contra hxL
  let Ci : Fin 3 → Subgroup X := fun i => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom
  have hCi : ∀ i : Fin 3, CFSG.IsComponent (Ci i) :=
    fun i => (hcomp (Ci i)).mpr ⟨i, rfl⟩
  have hxCi : ∀ i : Fin 3, x ∈ normalizer (Ci i : Set X) :=
    fun i => mem_compNormalizer_iff.mp hx (Ci i) (hCi i)
  have hex : ∀ i : Fin 3, ∃ l ∈ Ci i, (x * l) ^ 3 ∈ centralizer (Ci i : Set X) ∧
      ∃ z ∈ Ci i, orderOf z = 3 ∧ x * l * z = z * (x * l) :=
    fun i => exists_mul_commute_of_mem_normalizer h714 hX Nat.prime_three (by norm_num)
      (hCi i) (hrank (Ci i) (hCi i)) (hxCi i) hx3
  choose l hl using hex
  choose z hz using fun i => (hl i).2.2
  have hcomp_ne : ∀ i j : Fin 3, i ≠ j → Ci i ≠ Ci j :=
    fun i j hij h => hij (hinj h)
  have hcent_ne : ∀ i j : Fin 3, i ≠ j → Ci i ≤ centralizer (Ci j : Set X) :=
    fun i j hij => Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute (hCi i) (hCi j)).resolve_left
        (hcomp_ne i j hij))
  have hl_cent : ∀ j i : Fin 3, j ≠ i → l j ∈ centralizer (Ci i : Set X) :=
    fun j i hji => hcent_ne j i hji (hl j).1
  have hz_cent : ∀ j i : Fin 3, j ≠ i → z j ∈ centralizer (Ci i : Set X) :=
    fun j i hji => hcent_ne j i hji (hz j).1
  have hl_comm : ∀ i j : Fin 3, i ≠ j → l i * l j = l j * l i :=
    fun i j hij => ((Subgroup.mem_centralizer_iff.mp (hl_cent i j hij)) (l j) (hl j).1).symm
  let x' : X := x * l 0 * l 1 * l 2
  have hx'3_0 : x' ^ 3 ∈ centralizer (Ci 0 : Set X) := by
    have hm : l 1 * l 2 ∈ centralizer (Ci 0 : Set X) :=
      mul_mem (hl_cent 1 0 (by decide)) (hl_cent 2 0 (by decide))
    have hg : x * l 0 ∈ normalizer (Ci 0 : Set X) :=
      mul_mem (hxCi 0) (Subgroup.le_normalizer (hl 0).1)
    have heq : x' = (x * l 0) * (l 1 * l 2) := by
      show x * l 0 * l 1 * l 2 = (x * l 0) * (l 1 * l 2)
      group
    rw [heq]
    exact pow_three_mul_mem_centralizer hg (hl 0).2.1 hm
  have hx'3_1 : x' ^ 3 ∈ centralizer (Ci 1 : Set X) := by
    have hm : l 0 * l 2 ∈ centralizer (Ci 1 : Set X) :=
      mul_mem (hl_cent 0 1 (by decide)) (hl_cent 2 1 (by decide))
    have hg : x * l 1 ∈ normalizer (Ci 1 : Set X) :=
      mul_mem (hxCi 1) (Subgroup.le_normalizer (hl 1).1)
    have heq : x' = (x * l 1) * (l 0 * l 2) := by
      show x * l 0 * l 1 * l 2 = (x * l 1) * (l 0 * l 2)
      calc x * l 0 * l 1 * l 2 = x * (l 0 * l 1) * l 2 := by group
        _ = x * (l 1 * l 0) * l 2 := by rw [hl_comm 0 1 (by decide)]
        _ = (x * l 1) * (l 0 * l 2) := by group
    rw [heq]
    exact pow_three_mul_mem_centralizer hg (hl 1).2.1 hm
  have hx'3_2 : x' ^ 3 ∈ centralizer (Ci 2 : Set X) := by
    have hm : l 0 * l 1 ∈ centralizer (Ci 2 : Set X) :=
      mul_mem (hl_cent 0 2 (by decide)) (hl_cent 1 2 (by decide))
    have hg : x * l 2 ∈ normalizer (Ci 2 : Set X) :=
      mul_mem (hxCi 2) (Subgroup.le_normalizer (hl 2).1)
    have heq : x' = (x * l 2) * (l 0 * l 1) := by
      show x * l 0 * l 1 * l 2 = (x * l 2) * (l 0 * l 1)
      calc x * l 0 * l 1 * l 2 = x * l 0 * (l 1 * l 2) := by group
        _ = x * l 0 * (l 2 * l 1) := by rw [hl_comm 1 2 (by decide)]
        _ = x * (l 0 * l 2) * l 1 := by group
        _ = x * (l 2 * l 0) * l 1 := by rw [hl_comm 0 2 (by decide)]
        _ = (x * l 2) * (l 0 * l 1) := by group
    rw [heq]
    exact pow_three_mul_mem_centralizer hg (hl 2).2.1 hm
  have hx'3_cent : ∀ i : Fin 3, x' ^ 3 ∈ centralizer (Ci i : Set X) := by
    intro i
    fin_cases i
    · exact hx'3_0
    · exact hx'3_1
    · exact hx'3_2
  have hz_comm_0 : x' * z 0 = z 0 * x' := by
    have hm : l 1 * l 2 ∈ centralizer (Ci 0 : Set X) :=
      mul_mem (hl_cent 1 0 (by decide)) (hl_cent 2 0 (by decide))
    have heq : x' = (x * l 0) * (l 1 * l 2) := by
      show x * l 0 * l 1 * l 2 = (x * l 0) * (l 1 * l 2)
      group
    have hyz : z 0 * (l 1 * l 2) = (l 1 * l 2) * z 0 :=
      Subgroup.mem_centralizer_iff.mp hm (z 0) (hz 0).1
    have hz0 : x * l 0 * z 0 = z 0 * (x * l 0) := (hz 0).2.2
    rw [heq]
    calc (x * l 0) * (l 1 * l 2) * z 0
        = (x * l 0) * ((l 1 * l 2) * z 0) := by group
      _ = (x * l 0) * (z 0 * (l 1 * l 2)) := by rw [← hyz]
      _ = (x * l 0 * z 0) * (l 1 * l 2) := by group
      _ = (z 0 * (x * l 0)) * (l 1 * l 2) := by rw [hz0]
      _ = z 0 * ((x * l 0) * (l 1 * l 2)) := by group
  have hz_comm_1 : x' * z 1 = z 1 * x' := by
    have hm : l 0 * l 2 ∈ centralizer (Ci 1 : Set X) :=
      mul_mem (hl_cent 0 1 (by decide)) (hl_cent 2 1 (by decide))
    have heq : x' = (x * l 1) * (l 0 * l 2) := by
      show x * l 0 * l 1 * l 2 = (x * l 1) * (l 0 * l 2)
      calc x * l 0 * l 1 * l 2 = x * (l 0 * l 1) * l 2 := by group
        _ = x * (l 1 * l 0) * l 2 := by rw [hl_comm 0 1 (by decide)]
        _ = (x * l 1) * (l 0 * l 2) := by group
    have hyz : z 1 * (l 0 * l 2) = (l 0 * l 2) * z 1 :=
      Subgroup.mem_centralizer_iff.mp hm (z 1) (hz 1).1
    have hz1 : x * l 1 * z 1 = z 1 * (x * l 1) := (hz 1).2.2
    rw [heq]
    calc (x * l 1) * (l 0 * l 2) * z 1
        = (x * l 1) * ((l 0 * l 2) * z 1) := by group
      _ = (x * l 1) * (z 1 * (l 0 * l 2)) := by rw [← hyz]
      _ = (x * l 1 * z 1) * (l 0 * l 2) := by group
      _ = (z 1 * (x * l 1)) * (l 0 * l 2) := by rw [hz1]
      _ = z 1 * ((x * l 1) * (l 0 * l 2)) := by group
  have hz_comm_2 : x' * z 2 = z 2 * x' := by
    have hm : l 0 * l 1 ∈ centralizer (Ci 2 : Set X) :=
      mul_mem (hl_cent 0 2 (by decide)) (hl_cent 1 2 (by decide))
    have heq : x' = (x * l 2) * (l 0 * l 1) := by
      show x * l 0 * l 1 * l 2 = (x * l 2) * (l 0 * l 1)
      calc x * l 0 * l 1 * l 2 = x * l 0 * (l 1 * l 2) := by group
        _ = x * l 0 * (l 2 * l 1) := by rw [hl_comm 1 2 (by decide)]
        _ = x * (l 0 * l 2) * l 1 := by group
        _ = x * (l 2 * l 0) * l 1 := by rw [hl_comm 0 2 (by decide)]
        _ = (x * l 2) * (l 0 * l 1) := by group
    have hyz : z 2 * (l 0 * l 1) = (l 0 * l 1) * z 2 :=
      Subgroup.mem_centralizer_iff.mp hm (z 2) (hz 2).1
    have hz2 : x * l 2 * z 2 = z 2 * (x * l 2) := (hz 2).2.2
    rw [heq]
    calc (x * l 2) * (l 0 * l 1) * z 2
        = (x * l 2) * ((l 0 * l 1) * z 2) := by group
      _ = (x * l 2) * (z 2 * (l 0 * l 1)) := by rw [← hyz]
      _ = (x * l 2 * z 2) * (l 0 * l 1) := by group
      _ = (z 2 * (x * l 2)) * (l 0 * l 1) := by rw [hz2]
      _ = z 2 * ((x * l 2) * (l 0 * l 1)) := by group
  have hz_comm : ∀ i : Fin 3, x' * z i = z i * x' := by
    intro i
    fin_cases i
    · exact hz_comm_0
    · exact hz_comm_1
    · exact hz_comm_2
  have hlayer_le : CFSG.layer X ≤ centralizer (Subgroup.zpowers (x' ^ 3) : Set X) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le ?_
    intro D hD
    obtain ⟨i, rfl⟩ := (hcomp D).mp hD
    rw [Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.mpr (hx'3_cent i)
  have hx'3_layer : x' ^ 3 ∈ centralizer (CFSG.layer X : Set X) :=
    (Subgroup.le_centralizer_iff.mp hlayer_le) (Subgroup.mem_zpowers (x' ^ 3))
  have hx'3eq1 : x' ^ 3 = 1 := by
    have h := hx'3_layer
    rw [hY] at h
    exact Subgroup.mem_bot.mp h
  have hlt : l 0 * l 1 * l 2 ∈ CFSG.layer X :=
    mul_mem (mul_mem (CFSG.LocalCores.component_le_layer (hCi 0) (hl 0).1)
      (CFSG.LocalCores.component_le_layer (hCi 1) (hl 1).1))
      (CFSG.LocalCores.component_le_layer (hCi 2) (hl 2).1)
  have hx'notin : x' ∉ CFSG.layer X := by
    intro hx'in
    apply hxL
    have hx_eq : x = x' * (l 0 * l 1 * l 2)⁻¹ := by
      rw [show x' = x * l 0 * l 1 * l 2 by rfl]
      group
    rw [hx_eq]
    exact mul_mem hx'in (inv_mem hlt)
  have hnc : ∀ i : Fin 3, ∃ c ∈ Ci i, z i * c ≠ c * z i := by
    intro i
    by_contra h
    push Not at h
    have hzc : (⟨z i, (hz i).1⟩ : ↥(Ci i)) ∈ center ↥(Ci i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (h g g.2).symm
    have h3 : orderOf (⟨z i, (hz i).1⟩ : ↥(Ci i)) = 3 :=
      (Subgroup.orderOf_coe ⟨z i, (hz i).1⟩).symm.trans (hz i).2.1
    have hdvd : 3 ∣ Nat.card (center ↥(Ci i)) := by
      have hord := Subgroup.orderOf_dvd_natCard (center ↥(Ci i)) hzc
      rwa [h3] at hord
    exact not_dvd_card_center_of_pRank_eq_one h72 hX (hCi i) Nat.prime_three (by norm_num)
      (hrank (Ci i) (hCi i)) hdvd
  let A₁ : Subgroup X := ⊥ ⊔ zpowers (z 0)
  let A₂ : Subgroup X := A₁ ⊔ zpowers (z 1)
  let A₃ : Subgroup X := A₂ ⊔ zpowers (z 2)
  have hA₁ : IsElemAbelian 3 A₁ ∧ Nat.card A₁ = 3 ^ 1 := by
    have h := isElemAbelian_sup_zpowers (p := 3) Nat.prime_three (A := (⊥ : Subgroup X))
      (C := Ci 0) (e := z 0) (a := 0) (CFSG.SectionRank.isElemAbelian_bot 3)
      (by rw [Subgroup.card_bot, pow_zero]) bot_le (hz 0).1 (hz 0).2.1 (hnc 0)
    simpa [A₁] using h
  have hA₁cent : A₁ ≤ centralizer (Ci 1 : Set X) := by
    refine sup_le bot_le ?_
    exact Subgroup.zpowers_le.mpr (hz_cent 0 1 (by decide))
  have hA₂ : IsElemAbelian 3 A₂ ∧ Nat.card A₂ = 3 ^ 2 := by
    have h := isElemAbelian_sup_zpowers (p := 3) Nat.prime_three (A := A₁) (C := Ci 1)
      (e := z 1) (a := 1) hA₁.1 hA₁.2 hA₁cent (hz 1).1 (hz 1).2.1 (hnc 1)
    simpa [A₂] using h
  have hA₂cent : A₂ ≤ centralizer (Ci 2 : Set X) := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr (hz_cent 1 2 (by decide)))
    refine sup_le bot_le ?_
    exact Subgroup.zpowers_le.mpr (hz_cent 0 2 (by decide))
  have hA₃ : IsElemAbelian 3 A₃ ∧ Nat.card A₃ = 3 ^ 3 := by
    have h := isElemAbelian_sup_zpowers (p := 3) Nat.prime_three (A := A₂) (C := Ci 2)
      (e := z 2) (a := 2) hA₂.1 hA₂.2 hA₂cent (hz 2).1 (hz 2).2.1 (hnc 2)
    simpa [A₃] using h
  have hz_mem : ∀ i : Fin 3, z i ∈ centralizer ({x'} : Set X) := fun i => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz_comm i).symm
  have hA₃cent : A₃ ≤ centralizer ({x'} : Set X) :=
    sup_le (sup_le (sup_le bot_le (Subgroup.zpowers_le.mpr (hz_mem 0)))
      (Subgroup.zpowers_le.mpr (hz_mem 1))) (Subgroup.zpowers_le.mpr (hz_mem 2))
  have hcommA₃ : ∀ b ∈ A₃, b * x' = x' * b :=
    fun b hb => (Subgroup.mem_centralizer_iff.mp (hA₃cent hb) x' (Set.mem_singleton x')).symm
  have hz_layer : ∀ i : Fin 3, z i ∈ CFSG.layer X :=
    fun i => CFSG.LocalCores.component_le_layer (hCi i) (hz i).1
  have hA₃le : A₃ ≤ CFSG.layer X :=
    sup_le (sup_le (sup_le bot_le (Subgroup.zpowers_le.mpr (hz_layer 0)))
      (Subgroup.zpowers_le.mpr (hz_layer 1))) (Subgroup.zpowers_le.mpr (hz_layer 2))
  have hx'notinA₃ : x' ∉ A₃ := fun h => hx'notin (hA₃le h)
  have hE := isElemAbelian_sup_zpowers_of_notMem (p := 3) Nat.prime_three (A := A₃) (a := 3)
    hA₃.1 hA₃.2 hx'notinA₃ hx'3eq1 hcommA₃
  have hle4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE.1 ?_
    simpa using hE.2
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
