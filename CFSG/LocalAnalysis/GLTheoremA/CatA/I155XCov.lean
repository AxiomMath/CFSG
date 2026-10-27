module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XCoprime
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem core_inf_le {p : ℕ} (hp : p.Prime) {X Ks : Subgroup G} (hKX : Ks ≤ X) :
    GLAPPrimeCoreOf p X ⊓ Ks ≤ GLAPPrimeCoreOf p Ks := by
  have hO : ∀ a ∈ Ks, ∀ n ∈ GLAPPrimeCoreOf p X ⊓ Ks, a * n * a⁻¹ ∈ GLAPPrimeCoreOf p X ⊓ Ks := by
    intro a ha n hn
    refine ⟨?_, Ks.mul_mem (Ks.mul_mem ha hn.2) (Ks.inv_mem ha)⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X (hKX ha)) n).1 hn.1
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p X ⊓ Ks)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp X))
  exact le_glaPPrimeCoreOf_of_normal' inf_le_right hO hcop

theorem commutator_list_mem {Ks N : Subgroup G} (hN : ∀ g ∈ Ks, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hNKs : N ≤ Ks) (a : G) : ∀ (L : List G), (∀ l ∈ L, ⁅a, l⁆ ∈ N ∧ l ∈ Ks) →
      ⁅a, L.prod⁆ ∈ N
  | [], _ => by
    rw [List.prod_nil, commutatorElement_one_right]
    exact N.one_mem
  | l :: L, h => by
    rw [List.prod_cons, commutatorElement_mul_right]
    have ih := commutator_list_mem hN hNKs a L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact N.mul_mem (h l (List.mem_cons_self)).1 (hN l (h l List.mem_cons_self).2 _ ih)

theorem commutator_K_glbConj_le {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) {i : ℕ} (hi : ¬ p ∣ i) :
    ⁅K, GLBConj (x ^ (i : ℤ)) K⁆ ≤ GLAPPrimeCoreOf p (closureIn K (Subgroup.zpowers x)) := by
  have hi' : ¬ (p : ℤ) ∣ (0 : ℤ) - (i : ℤ) := by
    rw [zero_sub, dvd_neg, Int.natCast_dvd_natCast]
    exact hi
  have h := commutator_glbConj_le_core hp hx hxX hK hxK (i := 0) (j := (i : ℤ)) hi'
  rw [zpow_zero, gLBConj_one] at h
  exact h

theorem conj_mem_glbConj_nat {x : G} {K : Subgroup G} {c : G} (hc : c ∈ K) (i : ℕ) :
    (x ^ i)⁻¹ * c * x ^ i ∈ GLBConj (x ^ (i : ℤ)) K := by
  rw [mem_gLBConj, zpow_natCast]
  simpa [mul_assoc] using hc

theorem glbConj_nat_le_centMod {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) {i : ℕ} (hi : ¬ p ∣ i) :
    GLBConj (x ^ (i : ℤ)) K ≤ centModSubgroup p K := by
  have hi' : ¬ (p : ℤ) ∣ (i : ℤ) := by exact_mod_cast hi
  exact le_centModSubgroup_of_ne hp (glaPComponent_zpow hxX hK _) hK
    (glbConj_zpow_ne_of_not_dvd hp hx hxK hi')

theorem glbConj_le_of_le {A B : Subgroup G} (h : A ≤ B) (g : G) : GLBConj g A ≤ GLBConj g B := by
  unfold GLBConj
  exact Subgroup.map_mono h

theorem commutator_core_mem {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K J : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) (hJK : ∀ j ∈ J, j ∈ centModSubgroup p K)
    (hJKs : J ≤ closureIn K (Subgroup.zpowers x)) {j : G} (hj : j ∈ J) :
    ∀ g ∈ closureIn K (Subgroup.zpowers x),
      ⁅j, g⁆ ∈ GLAPPrimeCoreOf p (closureIn K (Subgroup.zpowers x)) := by
  set Ks := closureIn K (Subgroup.zpowers x) with hKs
  set N := GLAPPrimeCoreOf p Ks with hN
  have hNnorm : ∀ g ∈ Ks, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p Ks hg) n).1 hn
  have hKX : Ks ≤ X := closureIn_le_of_glbConj fun k =>
    (glbConj_le_of_le hK.1 _).trans (glbConj_eq_self_of_mem (X.zpow_mem hxX k)).le
  have hcomm_jx : Commute j x := Subgroup.mem_centralizer_singleton_iff.1 (hJx hj)
  have hjKs : j ∈ Ks := hJKs hj
  let S : Subgroup G :=
    { carrier := {g | g ∈ Ks ∧ ⁅j, g⁆ ∈ N}
      mul_mem' := fun {a b} ha hb => ⟨Ks.mul_mem ha.1 hb.1, by
        rw [commutatorElement_mul_right]
        exact N.mul_mem ha.2 (hNnorm a ha.1 _ hb.2)⟩
      one_mem' := ⟨Ks.one_mem, by rw [commutatorElement_one_right]; exact N.one_mem⟩
      inv_mem' := fun {a} ha => ⟨Ks.inv_mem ha.1, by
        have e : ⁅j, a⁻¹⁆ = a⁻¹ * ⁅j, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := hNnorm a⁻¹ (Ks.inv_mem ha.1) _ (N.inv_mem ha.2)
        rwa [inv_inv] at this⟩ }
  have hS : Ks ≤ S := by
    refine closureIn_le_of_glbConj (H := S) fun k => ?_
    intro g hg
    have hgKs : g ∈ Ks := glbConj_zpow_le_closureIn K x k hg
    refine ⟨hgKs, ?_⟩
    set a : G := x ^ k with ha
    set k₀ : G := a * g * a⁻¹ with hk₀
    have hk₀K : k₀ ∈ K := mem_gLBConj.1 hg
    have hak : a⁻¹ * k₀ * a = g := by rw [hk₀]; group
    have hja : j * a = a * j := (hcomm_jx.zpow_right k).eq
    have hcomm_inv : ⁅j, k₀⁆ ∈ GLAPPrimeCoreOf p K := by
      have h1 := (mem_centModSubgroup.1 (hJK j hj)).2 k₀ hk₀K
      rw [← commutatorElement_inv]
      exact (GLAPPrimeCoreOf p K).inv_mem h1
    have hconjO : a⁻¹ * ⁅j, k₀⁆ * a ∈ GLAPPrimeCoreOf p X := by
      have hO_le : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p X :=
        CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hK.2.1
      have hax : a⁻¹ ∈ X := X.inv_mem (X.zpow_mem hxX k)
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X hax) _).1
        (hO_le hcomm_inv)
      simpa [inv_inv] using this
    have hconj_eq : a⁻¹ * ⁅j, k₀⁆ * a = ⁅j, g⁆ := by
      have e1 : (MulAut.conj a⁻¹) j = j := by
        rw [MulAut.conj_apply, inv_inv, mul_assoc, hja, inv_mul_cancel_left]
      have e2 : (MulAut.conj a⁻¹) k₀ = g := by
        rw [MulAut.conj_apply, inv_inv]
        exact hak
      have hmap : (MulAut.conj a⁻¹) ⁅j, k₀⁆ = ⁅j, g⁆ := by
        rw [map_commutatorElement, e1, e2]
      rw [MulAut.conj_apply, inv_inv] at hmap
      exact hmap
    have hmemX : ⁅j, g⁆ ∈ GLAPPrimeCoreOf p X := by
      rw [← hconj_eq]
      exact hconjO
    have hmemKs : ⁅j, g⁆ ∈ Ks := by
      rw [commutatorElement_def]
      exact Ks.mul_mem (Ks.mul_mem (Ks.mul_mem hjKs hgKs) (Ks.inv_mem hjKs)) (Ks.inv_mem hgKs)
    exact core_inf_le hp hKX ⟨hmemX, hmemKs⟩
  intro g hg
  exact (hS hg).2

theorem not_centMod_all {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K J : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hJ : GLAPComponent p (closureIn K (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    ¬ (∀ j ∈ J, j ∈ centModSubgroup p K) := by
  intro hJK
  set Ks := closureIn K (Subgroup.zpowers x) with hKs
  set N := GLAPPrimeCoreOf p Ks with hN
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := hJ.1.trans inf_le_right
  have hJKs : J ≤ Ks := hJ.1.trans inf_le_left
  have hcomm : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ N := fun a ha b hb =>
    commutator_core_mem hp hx hxX hK hJx hJK hJKs ha b (hJKs hb)
  have hcop : Nat.Coprime p (Nat.card ↥N) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp Ks)
  have hJN : ⁅J, J⁆ ≤ J ⊓ N := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ⟨?_, hcomm a ha b hb⟩
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
  have hnorm : ∀ a ∈ J, ∀ n ∈ J ⊓ N, a * n * a⁻¹ ∈ J ⊓ N := fun a ha n hn =>
    ⟨J.mul_mem (J.mul_mem ha hn.1) (J.inv_mem ha),
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p Ks (hJKs ha)) n).1 hn.2⟩
  have hJO : J ⊓ N ≤ GLAPPrimeCoreOf p J :=
    le_glaPPrimeCoreOf_of_normal' inf_le_left hnorm
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hcop)
  have hJO' : ⁅J, J⁆ ≤ GLAPPrimeCoreOf p J := hJN.trans hJO
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI := isQuasisimple_nontrivial hq
  have hbot : commutator (PQuot p J) = ⊥ := by
    rw [commutator_def, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have hmem : ⁅(a' : G), (b' : G)⁆ ∈ ⁅J, J⁆ := Subgroup.commutator_mem_commutator a'.2 b'.2
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 (hJO' hmem)
    have hyc : y = ⁅a', b'⁆ := Subtype.ext (by
      have h2 : ((y : ↥J) : G) = ⁅(a' : G), (b' : G)⁆ := hyeq
      rw [h2]
      rfl)
    have hc : (⁅a', b'⁆ : ↥J) ∈ GLAPPrimeCore p ↥J := hyc ▸ hy
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) ⁅a', b'⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc
    rw [map_commutatorElement] at h1
    rw [Subgroup.mem_bot]
    exact h1
  have h := hq.1
  rw [hbot] at h
  exact ((Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup (PQuot p J))).1 inferInstance) h.symm

theorem act_one {p : ℕ} (K : Subgroup G) : act p K 1 = 1 := by
  rw [act_of_mem (Subgroup.one_mem _)]
  exact map_one (chevAut p K)

theorem cover_c {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1) {X K J : Subgroup G}
    (hxX : x ∈ X) (hK : GLAPComponent p X K) (hxK : x ∉ Subgroup.normalizer (K : Set G))
    (hJ : GLAPComponent p (closureIn K (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    K ≤ J ⊔ centModSubgroup p K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  set Ks := closureIn K (Subgroup.zpowers x) with hKs
  set N := GLAPPrimeCoreOf p Ks with hN
  set C := Ks ⊓ Subgroup.centralizer ({x} : Set G) with hC
  have hKsS : Ks ≤ K ⊔ centModSubgroup p K := closureIn_le_sup_centMod hp hx hxX hK hxK
  have hKsN : Ks ≤ Subgroup.normalizer (K : Set G) := closureIn_le_normalizer hp hx hxX hK hxK
  have hKX : Ks ≤ X := closureIn_le_of_glbConj fun k =>
    (glbConj_le_of_le hK.1 _).trans (glbConj_eq_self_of_mem (X.zpow_mem hxX k)).le
  have hKK : K ≤ Ks := le_closureIn_self K _
  have hxKs : x ∈ Subgroup.normalizer (Ks : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.L62.le_normalizer_closureIn K (Subgroup.zpowers x)
      (Subgroup.mem_zpowers x)
  have hxN : x ∈ Subgroup.normalizer (N : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p Ks hxKs
  have hNKs : N ≤ Ks := Subgroup.map_subtype_le _
  have hNconj : ∀ g ∈ Ks, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p Ks hg) n).1 hn
  have hxN' : ∀ n ∈ N, x⁻¹ * n * x ∈ N := fun n hn => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) n).1 hn
    simpa using this
  have hcopN : ¬ p ∣ Nat.card N := not_dvd_card_glaPPrimeCoreOf hp Ks
  have hN1 : ∀ n ∈ N, act p K n = 1 := fun n hn => act_core_eq_one hp hx hxX hK hxK hn
  have hCKs : C ≤ Ks := inf_le_left
  have hCN : C ≤ Subgroup.normalizer (K : Set G) := hCKs.trans hKsN
  have hJC : J ≤ C := hJ.1
  have hJKs : J ≤ Ks := hJC.trans hCKs
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := hJKs.trans hKsN
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := hJC.trans inf_le_right
  have hsurj : ∀ c ∈ K, act p K c ∈ actImage p K C := by
    intro c hc
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hc
    have hL : ∀ y ∈ List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' 1 (p - 1)),
        ∃ i : ℕ, 1 ≤ i ∧ i < p ∧ y = (x ^ i)⁻¹ * c * x ^ i := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      rw [List.mem_range'_1] at hi
      exact ⟨i, hi.1, by omega, rfl⟩
    have hLmem : ∀ y ∈ List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' 1 (p - 1)),
        y ∈ centModSubgroup p K ∧ y ∈ Ks ∧ ⁅c⁻¹, y⁆ ∈ N := by
      intro y hy
      obtain ⟨i, hi1, hip, rfl⟩ := hL y hy
      have hnd : ¬ p ∣ i := Nat.not_dvd_of_pos_of_lt (by omega) hip
      have hmemG := conj_mem_glbConj_nat (x := x) hc i
      exact ⟨glbConj_nat_le_centMod hp hx hxX hK hxK hnd hmemG,
        (glbConj_zpow_le_closureIn K x (i : ℤ)) hmemG,
        commutator_K_glbConj_le hp hx hxX hK hxK hnd (Subgroup.commutator_mem_commutator (K.inv_mem hc) hmemG)⟩
    set w : G := (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' 1 (p - 1))).prod with hw
    have hw_cm : w ∈ centModSubgroup p K := by
      rw [hw]; exact Subgroup.list_prod_mem (centModSubgroup p K) fun y hy => (hLmem y hy).1
    have hw_Ks : w ∈ Ks := by
      rw [hw]; exact Subgroup.list_prod_mem Ks fun y hy => (hLmem y hy).2.1
    have hcomm_w : ⁅c⁻¹, w⁆ ∈ N :=
      commutator_list_mem hNconj hNKs c⁻¹ _ fun y hy => ⟨(hLmem y hy).2.2, (hLmem y hy).2.1⟩
    have hp1 : p = (p - 1) + 1 := by omega
    have htel := list_telescope x c (p - 1) 1
    have hprod1 : (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' 1 p)).prod =
        ((x ^ 1)⁻¹ * c * x ^ 1) *
          (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (1 + 1) (p - 1))).prod := by
      conv_lhs => rw [hp1]
      rw [List.range'_succ, List.map_cons, List.prod_cons]
    have hprodp : (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' 1 p)).prod = w * c := by
      have h := prod_range'_succ_right (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (p - 1) 1
      have hp' : p - 1 + 1 = p := by omega
      rw [hp'] at h
      rw [h]
      congr 1
      have hcp : 1 + (p - 1) = p := by omega
      rw [hcp]
      simp [hx]
    have hz_form : x⁻¹ * (c * w) * x = w * c := by
      calc x⁻¹ * (c * w) * x = (x⁻¹ * c * x) * (x⁻¹ * w * x) := by group
        _ = ((x ^ 1)⁻¹ * c * x ^ 1) *
            (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (1 + 1) (p - 1))).prod := by
          rw [pow_one, hw, htel]
        _ = (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' 1 p)).prod := hprod1.symm
        _ = w * c := hprodp
    have hz_eq : (c * w)⁻¹ * (x⁻¹ * (c * w) * x) = w⁻¹ * ⁅c⁻¹, w⁆ * w := by
      rw [hz_form]
      simp only [commutatorElement_def]
      group
    have hz_mem : (c * w)⁻¹ * (x⁻¹ * (c * w) * x) ∈ N := by
      rw [hz_eq]
      have := hNconj w⁻¹ (Ks.inv_mem hw_Ks) _ hcomm_w
      rwa [inv_inv] at this
    obtain ⟨n, hn, hfix⟩ := exists_fixed_coset hp hx hxN hcopN hz_mem
    set z' : G := c * w * n with hz'
    have hz'Ks : z' ∈ Ks :=
      Ks.mul_mem (Ks.mul_mem (hKK hc) hw_Ks) (hNKs hn)
    have hz'x : z' * x = x * z' := by
      have h2 : x * (x⁻¹ * z' * x) = z' * x := by group
      rw [hfix] at h2
      exact h2.symm
    have hz'C : z' ∈ C := ⟨hz'Ks, Subgroup.mem_centralizer_singleton_iff.2 hz'x⟩
    have hwN : w ∈ Subgroup.normalizer (K : Set G) := (mem_centModSubgroup.1 hw_cm).1
    have hNN : N ≤ Subgroup.normalizer (K : Set G) := hNKs.trans hKsN
    have hact : act p K z' = act p K c := by
      have hcw : c * w ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hcN hwN
      have hnN : n ∈ Subgroup.normalizer (K : Set G) := hNN hn
      rw [hz', act_mul hcw hnN, act_mul hcN hwN, act_eq_one_of_centMod hp hK hw_cm, hN1 n hn,
        mul_one, mul_one]
    exact (mem_actImage_iff hCN).2 ⟨z', hz'C, hact⟩
  have hCS : C ≤ K ⊔ centModSubgroup p K := hCKs.trans hKsS
  have hCimg : actImage p K C = (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range := by
    apply le_antisymm (actImage_le_range hp hK hCS)
    intro t ht
    rw [← actImage_K_eq_range] at ht
    obtain ⟨c, hc, rfl⟩ := (mem_actImage_iff Subgroup.le_normalizer).1 ht
    exact hsurj c hc
  haveI := isSimpleGroup_range hp hK
  have hsn : IsSubnormal (actImage p K J) (actImage p K C) := isSubnormal_actImage hJ.2.1
  rw [hCimg] at hsn
  have hJ_ne : actImage p K J ≠ ⊥ := by
    intro hbot
    apply not_centMod_all hp hx hxX hK hJ
    intro j hj
    have hmem : act p K j ∈ actImage p K J := (mem_actImage_iff hJN).2 ⟨j, hj, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact centMod_iff.1 ((act_eq_one_iff hp hK (hJN hj)).1 hmem)
  have hJ_top : actImage p K J = (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range :=
    (eq_bot_or_eq_of_isSubnormal_simple _ hsn rfl).resolve_left hJ_ne
  intro c hc
  have hcR : act p K c ∈ actImage p K J := by
    rw [hJ_top]
    exact act_mem_range hc
  obtain ⟨j, hj, hjc⟩ := (mem_actImage_iff hJN).1 hcR
  have hjN : j ∈ Subgroup.normalizer (K : Set G) := hJN hj
  have hcN' : c ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hc
  have hinv : act p K j⁻¹ * act p K j = 1 := by
    rw [← act_mul (Subgroup.inv_mem _ hjN) hjN, inv_mul_cancel, act_one]
  have hjc' : act p K (j⁻¹ * c) = 1 := by
    rw [act_mul (Subgroup.inv_mem _ hjN) hcN', ← hjc]
    exact hinv
  have hm : j⁻¹ * c ∈ centModSubgroup p K :=
    centMod_iff.1 ((act_eq_one_iff hp hK (Subgroup.mul_mem _ (Subgroup.inv_mem _ hjN) hcN')).1 hjc')
  have hcj : c = j * (j⁻¹ * c) := by group
  rw [hcj]
  exact Subgroup.mul_mem_sup hj hm

theorem isPGroup_zpowers_of_pow {x : G} {p : ℕ} (hx : x ^ p = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem core_le_centMod {p : ℕ} {K : Subgroup G} : GLAPPrimeCoreOf p K ≤ centModSubgroup p K := by
  intro o ho
  have hoK : o ∈ K := Subgroup.map_subtype_le _ ho
  refine mem_centModSubgroup.2 ⟨Subgroup.le_normalizer hoK, fun l hl => ?_⟩
  rw [commutatorElement_def]
  have h1 : l * o * l⁻¹ ∈ GLAPPrimeCoreOf p K :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p K hl) o).1 ho
  exact (GLAPPrimeCoreOf p K).mul_mem h1 ((GLAPPrimeCoreOf p K).inv_mem ho)

theorem cover_b {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1) {K J : Subgroup G}
    {X : Subgroup G} (hK : GLAPComponent p X K) (hcm : CentMod p K x)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    K ≤ J ⊔ centModSubgroup p K := by
  obtain ⟨-, huniq, -, -, hsup, -⟩ :=
    glaPLayer_inf_centralizer hp hK (isPGroup_zpowers_of_pow hx) hcm
  have hJL : GLAPLayer p (K ⊓ Subgroup.centralizer ({x} : Set G)) = J := (huniq J hJ).symm
  calc K = GLAPLayer p (K ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ GLAPPrimeCoreOf p K := hsup.symm
    _ ≤ J ⊔ centModSubgroup p K :=
      sup_le ((le_of_eq hJL).trans le_sup_left) (core_le_centMod.trans le_sup_right)

theorem closureIn_eq_self_of_mem_normalizer {x : G} {K : Subgroup G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) :
    closureIn K (Subgroup.zpowers x) = K := by
  apply le_antisymm
  · refine closureIn_le_of_glbConj fun k => ?_
    have h : x ^ k ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ hxK k
    rw [mem_normalizer_iff_gLBConj_eq] at h
    exact h.le
  · exact le_closureIn_self K _

end CFSG.LocalAnalysis.GLTheoremA.I155X
