module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BAll
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkDiag

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

open CFSG CFSG.Open CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62 (mem_normalizer_sup' mem_normalizer_of_conj_mem)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}

theorem Cfg.moved_card_and_z (h : Cfg p P x z)
    (hM : ∀ C : ComponentIndex Y, ¬ Fixed P C → IsCyclic ↥(P ⊓ C.1) ∧ center C.1 = ⊥)
    (hne : Nonempty (Moved P)) :
    ∃ E : Subgroup Y, E = ⨆ i : Moved P, omega1 p P i.1 ∧ E ≤ P ∧ E ≤ layer Y ∧
      IsElemAbelian p E ∧ z ∈ E ∧
      Nat.card (Moved P) = p ∧ p ^ p ≤ Nat.card E ∧
      (∀ e ∈ E, (∀ i : Moved P, ∀ c ∈ i.1.1, c * e = e * c) → e = 1) ∧
      (∀ g ∈ P, g ∈ normalizer (E : Set Y)) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEdef, hEP, hEl, hEe, hEn, hcard, hP5⟩ := h.moved_family hM
  have hJE := h.card_le_of_normalizes hEP hEe (hEn x h.x_mem)
  have hm1 : Nat.card (Moved P) ≤ p := by
    have : p ^ Nat.card (Moved P) ≤ p ^ p := hcard.trans hJE
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hm2 : p ≤ Nat.card (Moved P) :=
    Nat.le_of_dvd Nat.card_pos h.dvd_card_moved
  have hm : Nat.card (Moved P) = p := le_antisymm hm1 hm2
  have hpp : p ^ p ≤ Nat.card E := by
    have := hcard
    rwa [hm] at this
  have hzE : z ∈ E := by
    by_contra hzE
    have hzne : z ≠ 1 := h.z_ne_one
    have hZe : IsElemAbelian p (zpowers z) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
        (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one h.z_pow)
    have hZc : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, h.orderOf_z]
    have hEZ : E ⊓ zpowers z = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      by_contra hg1
      have hgp : g ^ p = 1 := hEe.2 g hg.1
      have hzp := zpowers_eq_of_mem_zpowers hgp h.z_pow hg1 hzne hg.2
      apply hzE
      have : z ∈ zpowers g := by rw [hzp]; exact mem_zpowers z
      exact zpowers_le.mpr hg.1 this
    have hEZc : ∀ a ∈ E, ∀ b ∈ zpowers z, a * b = b * a := fun a ha b hb =>
      h.zpowers_central hb (hEP ha)
    have hFe := isElemAbelian_sup hEe hZe hEZc
    have hFP : E ⊔ zpowers z ≤ P := sup_le hEP (zpowers_le.mpr h.z_mem)
    have hxZ : x ∈ normalizer (zpowers z : Set Y) := by
      refine mem_normalizer_of_conj_mem fun s hs => ?_
      have : x * s = s * x := h.zpowers_central hs h.x_mem
      rw [this]
      simpa using hs
    have hxF : x ∈ normalizer ((E ⊔ zpowers z : Subgroup Y) : Set Y) :=
      mem_normalizer_sup' (hEn x h.x_mem) hxZ
    have hJF := h.card_le_of_normalizes hFP hFe hxF
    have hcs := card_mul_le_card_sup hEZ
    rw [hZc] at hcs
    have h1 : p ^ p * p ≤ p ^ p := by
      calc p ^ p * p ≤ Nat.card E * p := Nat.mul_le_mul_right p hpp
        _ ≤ Nat.card ↥(E ⊔ zpowers z) := hcs
        _ ≤ p ^ p := hJF
    have h2 : p ^ p < p ^ p * p := by
      have : 0 < p ^ p := pow_pos hp.pos p
      nlinarith [hp.one_lt]
    omega
  exact ⟨E, hEdef, hEP, hEl, hEe, hzE, hm, hpp, hP5, hEn⟩


theorem commute_of_normalizes_zpowers {p : ℕ} (hp : p.Prime) {a x : Y} (ha : orderOf a = p)
    (hxp : x ^ p = 1) (hx : x ∈ normalizer ((zpowers a : Subgroup Y) : Set Y)) :
    x * a = a * x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : x * a * x⁻¹ ∈ zpowers a := (mem_normalizer_iff.mp hx a).mp (mem_zpowers a)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
  have hiter : ∀ j : ℕ, x ^ j * a * (x ^ j)⁻¹ = a ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc x ^ (j + 1) * a * (x ^ (j + 1))⁻¹ = x * (x ^ j * a * (x ^ j)⁻¹) * x⁻¹ := by group
        _ = x * a ^ (k ^ j) * x⁻¹ := by rw [ih]
        _ = (x * a * x⁻¹) ^ (k ^ j) := by rw [conj_zpow]
        _ = (a ^ k) ^ (k ^ j) := by rw [hk]
        _ = a ^ (k ^ (j + 1)) := by rw [← zpow_mul, pow_succ']
  have h2 := hiter p
  rw [hxp, one_mul, inv_one, mul_one] at h2
  have h3 : a ^ (k ^ p - 1) = 1 := by
    rw [zpow_sub_one, ← h2]
    simp
  have h4 : (p : ℤ) ∣ k ^ p - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h3
    rwa [ha] at this
  have h5 : ((k : ZMod p)) ^ p = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ p - 1) p).2 h4
    simpa [sub_eq_zero] using this
  have h6 : (k : ZMod p) = 1 := by
    rw [← ZMod.pow_card (k : ZMod p)]
    exact h5
  have h7 : (p : ℤ) ∣ k - 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) p).1 ?_
    simp [h6]
  have h8 : a ^ (k - 1) = 1 := by
    rw [← ha] at h7
    exact orderOf_dvd_iff_zpow_eq_one.1 h7
  have h9 : a ^ k = a := by
    rw [zpow_sub_one] at h8
    exact mul_inv_eq_one.1 h8
  rw [h9] at hk
  have h10 : x * a = a * x := by
    calc x * a = (x * a * x⁻¹) * x := by group
      _ = a * x := by rw [← hk]
  exact h10


theorem Cfg.struct (h : Cfg p P x z) (h64 : KFactCenterCyclicGeFive) (h610 : GL83.I_6_10_1)
    (hcycl : ∀ C : ComponentIndex Y, ¬ Fixed P C → IsCyclic ↥(P ⊓ C.1))
    (hcomp : ∃ C C' : ComponentIndex Y, C ≠ C') :
    (∀ C : ComponentIndex Y, ¬ Fixed P C) ∧ (∀ C : ComponentIndex Y, IsCyclic ↥(P ⊓ C.1)) ∧
      (∀ C : ComponentIndex Y, center C.1 = ⊥) ∧ Nat.card (ComponentIndex Y) = p ∧
      (∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C') ∧ z ∈ layer Y ∧
      (∀ g ∈ P, g ∈ centralizer (layer Y : Set Y) → g = 1) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hM : ∀ C : ComponentIndex Y, ¬ Fixed P C → IsCyclic ↥(P ⊓ C.1) ∧ center C.1 = ⊥ :=
    fun C hC => ⟨hcycl C hC, h.center_eq_bot_of_cyclic h610 (hcycl C hC)⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ComponentIndex Y, ¬ Fixed P C₀ := by
    by_contra hall
    push_neg at hall
    obtain ⟨C, C', hCC'⟩ := hcomp
    exact h.false_of_two_fixed h64 h610 hCC' (hall C) (hall C')
  obtain ⟨E, hEdef, hEP, hEl, hEe, hzE, hm, hpp, hP5, hEn⟩ :=
    h.moved_card_and_z hM ⟨⟨C₀, hC₀⟩⟩
  have hall : ∀ C : ComponentIndex Y, ¬ Fixed P C := by
    intro C hC
    have hzC := h.z_mem_comp_of_fixed hC
    have hz1 : z = 1 := hP5 z hzE fun i c hc => by
      have hne' : i.1 ≠ C := fun heq => i.2 (heq ▸ hC)
      exact comp_commute hne' c hc z hzC
    exact h.z_ne_one hz1
  have hcard : Nat.card (ComponentIndex Y) = p := by
    rw [← hm]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv hall)).symm
  have hCl : ∀ g ∈ P, g ∈ centralizer (layer Y : Set Y) → g = 1 := by
    intro g hgP hg
    by_contra hg1
    have hN : ∀ g' ∈ P, ∀ n ∈ P ⊓ centralizer (layer Y : Set Y),
        g' * n * g'⁻¹ ∈ P ⊓ centralizer (layer Y : Set Y) := by
      intro g' hg' n hn
      refine ⟨P.mul_mem (P.mul_mem hg' hn.1) (P.inv_mem hg'), ?_⟩
      show g' * n * g'⁻¹ ∈ centralizer (layer Y : Set Y)
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : g'⁻¹ * y * g' ∈ layer Y := by
        have := (CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.layer_normal Y).conj_mem y hy g'⁻¹
        simpa using this
      have hc := mem_centralizer_iff.mp hn.2 _ hy'
      calc y * (g' * n * g'⁻¹) = g' * ((g'⁻¹ * y * g') * n) * g'⁻¹ := by group
        _ = g' * (n * (g'⁻¹ * y * g')) * g'⁻¹ := by rw [hc]
        _ = g' * n * g'⁻¹ * y := by group
    have hne : P ⊓ centralizer (layer Y : Set Y) ≠ ⊥ := by
      intro hbot
      have : g ∈ P ⊓ centralizer (layer Y : Set Y) := ⟨hgP, hg⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hg1 this
    have hzc := (h.z_mem_of_normal inf_le_left hN hne).2
    have hz1 : z = 1 := hP5 z hzE fun i c hc =>
      mem_centralizer_iff.mp hzc c (component_le_layer i.1.2 hc)
    exact h.z_ne_one hz1
  have hxmoves : ∃ C₁ : ComponentIndex Y, x ∉ normalizer (C₁.1 : Set Y) := by
    by_contra hnone
    push_neg at hnone
    have hcent : ∀ i : Moved P, omega1 p P i.1 ≤ centralizer ({x} : Set Y) := by
      intro i
      obtain ⟨a₀, -, ho, he⟩ := h.omega1_eq_zpowers (hcycl i.1 i.2)
      have hnorm : x ∈ normalizer ((omega1 p P i.1 : Subgroup Y) : Set Y) := by
        rw [mem_normalizer_iff_map_conj_eq]
        have hfix : cjComp x i.1 = i.1 :=
          Subtype.ext (mem_normalizer_iff_map_conj_eq.mp (hnone i.1))
        have hmap := map_conj_omega1 p h.x_mem i.1
        rw [hfix] at hmap
        exact hmap
      rw [he] at hnorm ⊢
      have hc := commute_of_normalizes_zpowers hp ho h.x_pow hnorm
      refine zpowers_le.mpr ?_
      rw [mem_centralizer_singleton_iff]
      exact hc.symm
    have hEc : E ≤ centralizer ({x} : Set Y) := by
      rw [hEdef]
      exact iSup_le hcent
    have hcomm : ∀ e ∈ E, e * x = x * e := fun e he =>
      mem_centralizer_singleton_iff.mp (hEc he)
    have hle := h.rank_cent E hEP hEe hcomm
    have h5 := h.five_le
    have : p ^ 2 < p ^ p := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  obtain ⟨C₁, hxC₁⟩ := hxmoves
  have hinj : Function.Injective (fun k : Fin p => cjComp (x ^ (k : ℕ)) C₁) := by
    intro i j hij
    by_contra hne
    have hlt : ∀ i j : Fin p, i < j →
        cjComp (x ^ (i : ℕ)) C₁ = cjComp (x ^ (j : ℕ)) C₁ → False := by
      intro i j hij heq
      have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by omega
      have h2 : cjComp (x ^ (i : ℕ)) C₁ =
          cjComp (x ^ (i : ℕ)) (cjComp (x ^ ((j : ℕ) - (i : ℕ))) C₁) := by
        rw [← Lemma213.cjComp_mul, ← pow_add, ← hj]
        exact heq
      have h3 := Lemma213.cjComp_inj _ h2
      have h4 : x ^ ((j : ℕ) - (i : ℕ)) ∈ normalizer (C₁.1 : Set Y) :=
        mem_normalizer_iff_map_conj_eq.mpr (congrArg Subtype.val h3.symm)
      have hnd : ¬ p ∣ ((j : ℕ) - (i : ℕ)) := by
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      exact hxC₁ (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk.mem_of_pow_mem hp h.x_pow hnd h4)
    rcases lt_or_gt_of_ne hne with hlt' | hlt'
    · exact hlt i j hlt' hij
    · exact hlt j i hlt' hij.symm
  have hbij : Function.Bijective (fun k : Fin p => cjComp (x ^ (k : ℕ)) C₁) := by
    refine Function.Injective.bijective_of_nat_card_le hinj ?_
    rw [hcard, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin]
  have htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C' := by
    intro C C'
    obtain ⟨a, ha⟩ := hbij.2 C
    obtain ⟨b, hb⟩ := hbij.2 C'
    refine ⟨(b : ℕ) + (p - (a : ℕ)), ?_⟩
    have hax : cjComp (x ^ ((b : ℕ) + (p - (a : ℕ)))) C = cjComp (x ^ (b : ℕ)) C₁ := by
      rw [← ha]
      simp only
      rw [← Lemma213.cjComp_mul, ← pow_add]
      have : (b : ℕ) + (p - (a : ℕ)) + (a : ℕ) = (b : ℕ) + p := by omega
      rw [this, pow_add, h.x_pow, mul_one]
    rw [hax]
    exact hb
  exact ⟨hall, fun C => hcycl C (hall C), fun C => (hM C (hall C)).2, hcard, htrans, hEl hzE, hCl⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
