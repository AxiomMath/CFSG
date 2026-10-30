module

import CFSG.LocalAnalysis.GLTheoremA.I32One
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma34

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Step36 (p : ℕ) (B D J D' J' : Subgroup G) : Prop :=
  D' ≤ D ∧ Nat.card D' * p = Nat.card D ∧ (∀ d ∈ D', d ≠ 1 → IsEssential p B d) ∧
    GLAPComponent p (Subgroup.centralizer (D' : Set G)) J' ∧ IsChevSimple p (PSimple p J') ∧
    B ≤ Subgroup.normalizer (J' : Set G) ∧ J' = layerClosure p D' J ∧
    J ⊔ GLAPPrimeCoreOf p J' ≠ J' ∧ ∀ d ∈ D, d ∉ D' → ¬ InducesInnerMod p J' d

@[expose] def Cover36 (p : ℕ) (B D J D' J' : Subgroup G) : Prop :=
  GLAPComponent p (Subgroup.centralizer (D' : Set G)) J' ∧ IsChevSimple p (PSimple p J') ∧
    B ≤ Subgroup.normalizer (J' : Set G) ∧ J' = layerClosure p D' J ∧ J ≤ J' ∧
    GLAPComponent p (J' ⊓ Subgroup.centralizer (D : Set G)) J ∧
    J ⊔ GLAPPrimeCoreOf p J' = J' ∧ D ≤ centModSubgroup p J'

namespace S3

private theorem exists_ne_one_of_ne_bot {H : Subgroup G} (h : H ≠ ⊥) : ∃ d ∈ H, d ≠ 1 := by
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  exact ⟨d, hd, fun h' => hd1 (Subtype.ext h')⟩

private theorem mem_normalizer_inf {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  simp only [Subgroup.mem_inf]
  exact and_congr (hH h) (hK h)

private theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hH hK ⊢
  have h : GLBConj g ⁅H, K⁆ = ⁅GLBConj g H, GLBConj g K⁆ := by
    unfold GLBConj
    rw [Subgroup.map_commutator]
  rw [h, hH, hK]

private theorem not_isPGroup_two_of_perfect {H : Subgroup G} (hperf : (⁅H, H⁆ : Subgroup G) = H)
    (hne : H ≠ ⊥) : ¬ IsPGroup 2 H := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  haveI : Group.IsNilpotent H := h2.isNilpotent
  exact Group.IsPerfect.not_isSolvable H (inferInstance : Group.IsSolvable H)

private theorem eq_one_of_isPerfect_of_isSolvable' {A M : Type*} [Group A] [Group M]
    [Group.IsPerfect A] [Group.IsSolvable M] (φ : A →* M) : φ = 1 := by
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Group.IsSolvable φ.range :=
    Group.isSolvable_of_isSolvable_injective (f := φ.range.subtype) φ.range.subtype_injective
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range ‹_›
  ext h
  have : (⟨φ h, h, rfl⟩ : φ.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

private theorem exists_mul_of_cover {p : ℕ} {I K : Subgroup G} (hIK : I ≤ K)
    (hsup : I ⊔ GLAPPrimeCoreOf p K = K) :
    ∀ l ∈ K, ∃ y ∈ I, y⁻¹ * l ∈ GLAPPrimeCoreOf p K := by
  intro l hl
  have hIO : I ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    hIK.trans (le_normalizer_glaPPrimeCoreOf p K)
  have hl' : l ∈ (I ⊔ GLAPPrimeCoreOf p K : Subgroup G) := hsup.symm ▸ hl
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _ hIO] at hl'
  obtain ⟨y, hy, o, ho, hyo⟩ := Set.mem_mul.mp hl'
  refine ⟨y, hy, ?_⟩
  have : y⁻¹ * l = o := by rw [← hyo]; group
  rw [this]; exact ho

private theorem isElemAbelian_sup_zpowers_aux {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    {z : G} (hzp : z ^ p = 1) (hz : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers z) := by
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr hz)
  have hdec : ∀ x ∈ E ⊔ Subgroup.zpowers z, ∃ e ∈ E, ∃ k : ℤ, x = e * z ^ k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left E _ hnorm] at hx
    obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨e, he, k, rfl⟩
  have hcomm : ∀ e ∈ E, ∀ k : ℤ, Commute e (z ^ k) := fun e he k =>
    Commute.zpow_right (hz e he) k
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e₁, he₁, k₁, h₁⟩ := hdec x x.2
    obtain ⟨e₂, he₂, k₂, h₂⟩ := hdec y y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h₁, h₂]
    have h12 : e₁ * e₂ = e₂ * e₁ := isElemAbelian_commute hE he₁ he₂
    calc e₁ * z ^ k₁ * (e₂ * z ^ k₂) = e₁ * (z ^ k₁ * e₂) * z ^ k₂ := by group
      _ = e₁ * (e₂ * z ^ k₁) * z ^ k₂ := by rw [(hcomm e₂ he₂ k₁).eq]
      _ = (e₁ * e₂) * (z ^ k₁ * z ^ k₂) := by group
      _ = (e₂ * e₁) * (z ^ k₂ * z ^ k₁) := by rw [h12, ← zpow_add, ← zpow_add, add_comm]
      _ = e₂ * (e₁ * z ^ k₂) * z ^ k₁ := by group
      _ = e₂ * (z ^ k₂ * e₁) * z ^ k₁ := by rw [(hcomm e₁ he₁ k₂).eq]
      _ = e₂ * z ^ k₂ * (e₁ * z ^ k₁) := by group
  · obtain ⟨e, he, k, rfl⟩ := hdec x hx
    rw [(hcomm e he k).mul_pow, hE.2 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hzp, one_zpow]

theorem stage_step {p : ℕ} (hc : S3Ctx G p) (hI18 : Input18_3_4) (h1135 : I1135At G p)
    (hCl : ChevClosureAt G p) (hUn : ChevUniqueAt G p) (hInn : ChevInnerAt G p)
    {B D J Dc : Subgroup G} (hS : Star3 G p B) (hDB : D ≤ B)
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) (hDcD : Dc ≤ D)
    (hidx : Nat.card Dc * p = Nat.card D) (hDc1 : Dc ≠ ⊥)
    (hess : ∀ d ∈ Dc, d ≠ 1 → IsEssential p B d) :
    Step36 p B D J Dc (layerClosure p Dc J) ∨ Cover36 p B D J Dc (layerClosure p Dc J) := by
  have hp := hc.prime
  have hp2 := hc.odd
  have hDel : IsElemAbelian p D := isElemAbelian_mono hS.bmax.1 hDB
  have hDcB : Dc ≤ B := hDcD.trans hDB
  have hKG := S3.isKGroup_cen hc.simple hc.nonabelian hc.kProper hDc1
  obtain ⟨d, hd, hd1⟩ := exists_ne_one_of_ne_bot hDc1
  have hess' : ∃ d ∈ Dc, IsEssential p B d := ⟨d, hd, hess d hd hd1⟩
  have hnorm : ∀ J' : Subgroup G, GLAPComponent p (Subgroup.centralizer (Dc : Set G)) J' →
      B ≤ Subgroup.normalizer (J' : Set G) := fun J' hJ' =>
    (lemma34_iii hc hI18 h1135 hCl hUn hS hDcB hess' hJ').2
  obtain ⟨hJcomp, hJle, hBJc, hJcomp'⟩ :=
    S3.closure_eq hp hI18 hKG hDcD hDB hS.bmax.1 hJ hnorm
  have hChev := (lemma34_iii hc hI18 h1135 hCl hUn hS hDcB hess' hJcomp).1
  have hDJc : D ≤ Subgroup.normalizer ((layerClosure p Dc J : Subgroup G) : Set G) :=
    hDB.trans hBJc
  have hD_inner := hInn hp hp2 _ (layerClosure p Dc J) D hKG hJcomp hChev hDel hDJc ⟨J, hJcomp'⟩
  by_cases hall : ∀ d ∈ D, CentMod p (layerClosure p Dc J) d
  · right
    have hDcent : D ≤ centModSubgroup p (layerClosure p Dc J) := fun d hd =>
      centMod_iff.1 (hall d hd)
    exact ⟨hJcomp, hChev, hBJc, rfl, hJle, hJcomp',
      S3.cover_of_centMod hp hJcomp (isPGroup_of_isElemAbelian hDel) hDcent hJcomp', hDcent⟩
  · left
    push Not at hall
    obtain ⟨d₀, hd₀D, hd₀⟩ := hall
    have hout : ¬ InducesInnerMod p (layerClosure p Dc J) d₀ :=
      (hD_inner d₀ hd₀D).resolve_left hd₀
    have hDc_cent : Dc ≤ centModSubgroup p (layerClosure p Dc J) := by
      intro d hd
      rw [← centMod_iff]
      apply centMod_of_mem_centralizer
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (Subgroup.mem_centralizer_iff.1 (hJcomp.1 hj) d hd).symm
    refine ⟨hDcD, hidx, hess, hJcomp, hChev, hBJc, rfl, ?_, ?_⟩
    · intro hcov
      have h := S3.le_centModSubgroup_of_cover hJle hDJc hJ.1 hcov
      exact hd₀ (centMod_iff.2 (h hd₀D))
    · exact S3.not_inducesInnerMod_of_index_p hp hDcD hidx hDc_cent hDJc hDel.2 hd₀D hout

private theorem frattini_pow_mem {Q H : Subgroup G} (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    {u n : G} (hn : n ∈ H) (hu : u ∈ H) (h : n⁻¹ * u ∈ Q) :
    ∀ e : ℕ, (n ^ e)⁻¹ * u ^ e ∈ Q := by
  intro e
  induction e with
  | zero => simp [Q.one_mem]
  | succ e ih =>
    have h1 : n⁻¹ * ((n ^ e)⁻¹ * u ^ e) * n ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (hHQ (H.inv_mem hn)) _).1 ih
      simpa [mul_assoc] using this
    have : (n ^ (e + 1))⁻¹ * u ^ (e + 1) = (n⁻¹ * ((n ^ e)⁻¹ * u ^ e) * n) * (n⁻¹ * u) := by
      simp only [pow_succ', mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      group
    rw [this]
    exact Q.mul_mem h1 h

private theorem frattini_mem_zpowers_pow {x : G} {e : ℕ} (h : Nat.Coprime (orderOf x) e) :
    x ∈ Subgroup.zpowers (x ^ e) := by
  have hle : Subgroup.zpowers (x ^ e) ≤ Subgroup.zpowers x := by
    rw [Subgroup.zpowers_le]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) e
  have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers (x ^ e)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow h]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ Subgroup.mem_zpowers x

private theorem frattini_mem_of_odd {J₁ S : Subgroup G} (hSJ₁ : S ≤ Subgroup.normalizer (J₁ : Set G))
    (hS2 : IsPGroup 2 S) {x : G} (hx : x ∈ J₁ ⊔ S) (hodd : Odd (orderOf x)) : x ∈ J₁ := by
  have hxx := hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left J₁ _ hSJ₁] at hx
  obtain ⟨j, hj, s, hs, rfl⟩ := Set.mem_mul.mp hx
  have hH : J₁ ⊔ S ≤ Subgroup.normalizer (J₁ : Set G) := sup_le Subgroup.le_normalizer hSJ₁
  have hs' : s ∈ J₁ ⊔ S := Subgroup.mem_sup_right hs
  have h1 : s⁻¹ * (j * s) ∈ J₁ := by
    have := (Subgroup.mem_normalizer_iff.1 (hSJ₁ (S.inv_mem hs)) j).1 hj
    simpa [mul_assoc] using this
  have h2 := frattini_pow_mem hH hs' hxx h1 (orderOf (j * s))
  rw [pow_orderOf_eq_one, mul_one] at h2
  have h3 : s ^ orderOf (j * s) ∈ J₁ := by simpa using J₁.inv_mem h2
  obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (orderOf s) (orderOf (j * s)) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_left k hodd.coprime_two_right.symm)
  have hs1 : s ∈ J₁ :=
    (Subgroup.zpowers_le.2 h3) (frattini_mem_zpowers_pow hcop)
  exact J₁.mul_mem hj hs1

private theorem frattini_eq_top_of_odd {X : Type*} [Group X] [Finite X]
    (hX : commutator X = ⊤) (Q : Subgroup X) (hQ : ∀ s : X, Odd (orderOf s) → s ∈ Q) :
    Q = ⊤ := by
  have hconj : ∀ (g : X), ∀ x ∈ Subgroup.closure {s : X | Odd (orderOf s)},
      g * x * g⁻¹ ∈ Subgroup.closure {s : X | Odd (orderOf s)} := by
    intro g x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ?_
      have h : orderOf x = orderOf (g * x * g⁻¹) :=
        SemiconjBy.orderOf_eq g (x := x) (y := g * x * g⁻¹) (by simp [SemiconjBy])
      change Odd (orderOf (g * x * g⁻¹))
      rw [← h]
      exact hx
    | one => simp
    | mul x y _ _ hx hy => simpa [mul_assoc] using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa [mul_assoc] using Subgroup.inv_mem _ hx
  have hKnormal : (Subgroup.closure {s : X | Odd (orderOf s)}).Normal :=
    ⟨fun n hn g => hconj g n hn⟩
  set K : Subgroup X := Subgroup.closure {s : X | Odd (orderOf s)}
  have hKQ : K ≤ Q := (Subgroup.closure_le Q).2 fun s hs => hQ s hs
  have h2 : IsPGroup 2 (X ⧸ K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, ?_⟩
    have hxk : x ^ (2 ^ k) ∈ K := by
      refine Subgroup.subset_closure ?_
      change Odd (orderOf (x ^ (2 ^ k)))
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm]
      simpa [Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)] using hm
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hxk
  have : Group.IsNilpotent (X ⧸ K) := h2.isNilpotent
  have hsurj : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  have hperf : commutator (X ⧸ K) = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' K) (commutator X) = commutator (X ⧸ K) := by
      simp only [commutator_def]
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj]
    rw [← h1, hX, Subgroup.map_top_of_surjective _ hsurj]
  have : Subsingleton (X ⧸ K) := by
    by_contra h
    have : Nontrivial (X ⧸ K) := not_subsingleton_iff_nontrivial.1 h
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ K)).ne hperf
  have hKtop : K = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)
  exact top_le_iff.1 (hKtop ▸ hKQ)

private theorem frattini_le_primeCore {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  haveI hn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle : N.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hn, hcard ▸ hcop⟩
  intro n hn'
  exact ⟨⟨n, hNK hn'⟩, hle hn', rfl⟩

private theorem frattini_decomp_aux {Q H S₀ : Subgroup G} (hQH : Q ≤ H)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hS₀Q : S₀ ≤ Q)
    (hS₀ : Nat.card S₀ = 2 ^ (Nat.card Q).factorization 2) :
    ∀ h ∈ H, ∃ n ∈ H, n ∈ Subgroup.normalizer (S₀ : Set G) ∧ ∃ q ∈ Q, h = n * q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hQn : (Q.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hHQ
  have hS₀H : S₀ ≤ H := hS₀Q.trans hQH
  have hle : S₀.subgroupOf H ≤ Q.subgroupOf H := fun x hx => hS₀Q hx
  let P : Sylow 2 ↥(Q.subgroupOf H) :=
    Sylow.ofCard ((S₀.subgroupOf H).subgroupOf (Q.subgroupOf H)) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀H).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv]
      exact hS₀)
  have hfr := Sylow.normalizer_sup_eq_top P
  have hmap : (P : Subgroup ↥(Q.subgroupOf H)).map (Q.subgroupOf H).subtype = S₀.subgroupOf H :=
    Subgroup.map_subgroupOf_eq_of_le hle
  rw [hmap] at hfr
  intro h hh
  have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.normalizer ((S₀.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔
      Q.subgroupOf H := by
    rw [hfr]; exact Subgroup.mem_top _
  obtain ⟨n, hn, q, hq, hnq⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  refine ⟨(n : G), n.2, ?_, (q : G), hq, (congrArg Subtype.val hnq).symm⟩
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  constructor
  · intro hx
    have := (hn ⟨x, hS₀H hx⟩).1 hx
    exact this
  · intro hx
    have hxH : x ∈ H := by
      have h1 : (n : G) * x * (n : G)⁻¹ ∈ H := hS₀H hx
      have := H.mul_mem (H.mul_mem (H.inv_mem n.2) h1) n.2
      simpa [mul_assoc] using this
    exact (hn ⟨x, hxH⟩).2 hx

theorem S_props {p : ℕ} {B D D₁ N : Subgroup G} (hB : IsElemAbelian p B) (hp : p.Prime)
    (hp2 : p ≠ 2) (hDB : D ≤ B) (hD₁D : D₁ ≤ D) (hBN : B ≤ N) :
    IsPGroup 2 ↥(⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ : Subgroup G) ∧
      (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ : Subgroup G) ≤
        Subgroup.centralizer (D₁ : Set G) ∧
      B ≤ Subgroup.normalizer ((⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ :
        Subgroup G) : Set G) ∧
      (⁅D, (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ : Subgroup G)⁆ : Subgroup G) =
        ⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ := by
  have hDel : IsElemAbelian p D := isElemAbelian_mono hB hDB
  obtain ⟨hR2, hBR⟩ := S3.two_core_cen_props hBN hB (hD₁D.trans hDB)
  have hDR : D ≤ Subgroup.normalizer ((pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G) :
      Subgroup G) : Set G) := fun d hd => hBR (hDB hd)
  obtain ⟨h1, -, h3⟩ := S3.comm_two_group hp hp2 hDel hR2 hDR
  refine ⟨IsPGroup.to_le hR2 h1, h1.trans inf_le_right, fun b hb => ?_, h3⟩
  have hbD : b ∈ Subgroup.normalizer (D : Set G) := by
    apply Subgroup.centralizer_le_normalizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact isElemAbelian_commute hB (hDB hd) hb
  exact mem_normalizer_commutator hbD (hBR hb)

theorem frattini_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B J₁ S X : Subgroup G}
    (hBel : IsElemAbelian p B) (hJ₁ : GLAPComponent p X J₁)
    (hBJ₁ : B ≤ Subgroup.normalizer (J₁ : Set G)) (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hSJ₁ : S ≤ Subgroup.normalizer (J₁ : Set G)) (hSc : S ≤ centModSubgroup p J₁)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    ∃ S₀ Y₀ : Subgroup G, IsPGroup 2 S₀ ∧ S₀ ≠ ⊥ ∧ B ≤ Subgroup.normalizer (S₀ : Set G) ∧
      Y₀ ≤ J₁ ∧ Y₀ ≤ Subgroup.normalizer (S₀ : Set G) ∧ B ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      Y₀ ⊔ GLAPPrimeCoreOf p J₁ = J₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := GLAPPrimeCoreOf p J₁ with hO
  have hOJ : O ≤ J₁ := Subgroup.map_subtype_le _
  have hJ₁O : J₁ ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p J₁
  have hSO : S ≤ Subgroup.normalizer (O : Set G) := fun s hs =>
    normalizer_le_normalizer_glaPPrimeCoreOf p J₁ (hSJ₁ hs)
  have hBO : B ≤ Subgroup.normalizer (O : Set G) := fun b hb =>
    normalizer_le_normalizer_glaPPrimeCoreOf p J₁ (hBJ₁ hb)
  set Q : Subgroup G := O ⊔ S with hQ
  have hOS : O ≤ Q := le_sup_left
  have hSQ : S ≤ Q := le_sup_right
  have hOcop : Nat.Coprime p (Nat.card O) :=
    (hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp J₁)
  have hScop : Nat.Coprime p (Nat.card S) := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hQcop : Nat.Coprime p (Nat.card Q) := by
    have h := card_sup_mul_card_inf_of_le_normalizer hSO
    exact Nat.Coprime.coprime_dvd_right (Dvd.intro _ h) (Nat.Coprime.mul_right hOcop hScop)
  have hQ2 : 2 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hSne (Subgroup.card_eq_one.1 (by simpa using hn))
    exact (hn ▸ (dvd_pow_self 2 hn0)).trans (Subgroup.card_dvd_of_le hSQ)
  have hconjS : ∀ g ∈ J₁, GLBConj g S ≤ Q := by
    intro g hg y hy
    rw [mem_gLBConj] at hy
    have h1 : ⁅g⁻¹, g * y * g⁻¹⁆ ∈ O := (hSc hy).2 g⁻¹ (J₁.inv_mem hg)
    have : y = ⁅g⁻¹, g * y * g⁻¹⁆ * (g * y * g⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact Q.mul_mem (hOS h1) (hSQ hy)
  have hJ₁Q : J₁ ≤ Subgroup.normalizer (Q : Set G) := by
    intro g hg
    have key : ∀ g ∈ J₁, GLBConj g Q ≤ Q := by
      intro g hg
      have : GLBConj g Q = GLBConj g O ⊔ GLBConj g S := by
        unfold GLBConj; rw [Subgroup.map_sup]
      rw [this, gLBConj_eq_of_mem_normalizer (hJ₁O hg)]
      exact sup_le hOS (hconjS g hg)
    exact CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_normalizer_of_gLBConj_le
      (key g hg) (key g⁻¹ (J₁.inv_mem hg))
  have hSQn : S ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_normalizer_sup (hSO hs)
      (Subgroup.le_normalizer hs)
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := fun b hb =>
    CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_normalizer_sup (hBO hb) (hBS hb)
  obtain ⟨S₀, hS₀Q, hS₀2, hS₀ne, hBS₀, hS₀card⟩ :=
    exists_invariant_sylow hp Nat.prime_two (isPGroup_of_isElemAbelian hBel) hBQ hQcop hQ2
  set H : Subgroup G := J₁ ⊔ S with hH
  have hJ₁H : J₁ ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hQH : Q ≤ H := sup_le (hOJ.trans hJ₁H) hSH
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := sup_le hJ₁Q hSQn
  have hfrat := frattini_decomp_aux hQH hHQ hS₀Q hS₀card
  have hJ₁Q' : J₁ ⊓ Q ≤ O := by
    refine frattini_le_primeCore inf_le_left (fun g hg =>
      CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_normalizer_inf
        (Subgroup.le_normalizer hg) (hJ₁Q hg)) ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hQcop
  let Gen : Set G := {y : G | y ∈ J₁ ∧ y ∈ Subgroup.normalizer (S₀ : Set G) ∧ Odd (orderOf y)}
  have hY₀J₁ : Subgroup.closure Gen ≤ J₁ := (Subgroup.closure_le J₁).2 fun y hy => hy.1
  have hY₀N : Subgroup.closure Gen ≤ Subgroup.normalizer (S₀ : Set G) :=
    (Subgroup.closure_le _).2 fun y hy => hy.2.1
  have hBY₀ : B ≤ Subgroup.normalizer (Subgroup.closure Gen : Set G) := by
    have key : ∀ b ∈ B, ∀ y ∈ Subgroup.closure Gen, b * y * b⁻¹ ∈ Subgroup.closure Gen := by
      intro b hb y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (hBJ₁ hb) y).1 hy.1
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBS₀ hb) hy.2.1)
            (Subgroup.inv_mem _ (hBS₀ hb))
        · have h : orderOf y = orderOf (b * y * b⁻¹) :=
            SemiconjBy.orderOf_eq b (x := y) (y := b * y * b⁻¹) (by simp [SemiconjBy])
          rw [← h]; exact hy.2.2
      | one => simpa using (Subgroup.closure Gen).one_mem
      | mul x y _ _ hx hy =>
        simpa [mul_assoc] using (Subgroup.closure Gen).mul_mem hx hy
      | inv x _ hx => simpa [mul_assoc] using (Subgroup.closure Gen).inv_mem hx
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key b hb y, fun hy => ?_⟩
    have := key b⁻¹ (B.inv_mem hb) _ hy
    simpa [mul_assoc] using this
  have hodd_mem : ∀ u : G, u ∈ J₁ → Odd (orderOf u) → u ∈ Subgroup.closure Gen ⊔ O := by
    intro u huJ hu
    obtain ⟨n, hnH, hnS₀, q, hqQ, hunq⟩ := hfrat u (hJ₁H huJ)
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    have hbord : orderOf (n ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm]
      simp [Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)]
    have hbH : n ^ (2 ^ k) ∈ H := H.pow_mem hnH _
    have hbJ : n ^ (2 ^ k) ∈ J₁ := frattini_mem_of_odd hSJ₁ hS2 hbH (hbord ▸ hm)
    have hbN : n ^ (2 ^ k) ∈ Subgroup.normalizer (S₀ : Set G) := Subgroup.pow_mem _ hnS₀ _
    have hbY : n ^ (2 ^ k) ∈ Subgroup.closure Gen :=
      Subgroup.subset_closure ⟨hbJ, hbN, hbord ▸ hm⟩
    have hq : n⁻¹ * u ∈ Q := by
      have : n⁻¹ * u = q := by rw [hunq]; group
      rw [this]; exact hqQ
    have h1 : (n ^ (2 ^ k))⁻¹ * u ^ (2 ^ k) ∈ Q :=
      frattini_pow_mem hHQ hnH (hJ₁H huJ) hq _
    have h2 : (n ^ (2 ^ k))⁻¹ * u ^ (2 ^ k) ∈ O :=
      hJ₁Q' ⟨J₁.mul_mem (J₁.inv_mem hbJ) (J₁.pow_mem huJ _), h1⟩
    have h3 : u ^ (2 ^ k) ∈ Subgroup.closure Gen ⊔ O := by
      have : u ^ (2 ^ k) = n ^ (2 ^ k) * ((n ^ (2 ^ k))⁻¹ * u ^ (2 ^ k)) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbY) (Subgroup.mem_sup_right h2)
    exact (Subgroup.zpowers_le.2 h3)
      (frattini_mem_zpowers_pow (Nat.Coprime.pow_right k hu.coprime_two_right))
  have hcov : J₁ ≤ Subgroup.closure Gen ⊔ O := by
    have hperf : commutator ↥J₁ = ⊤ := by
      rw [← Subgroup.map_subtype_inj, Subgroup.map_subtype_commutator, Subgroup.map_top,
        Subgroup.range_subtype]
      exact glaPComponent_perfect hJ₁
    have htop := frattini_eq_top_of_odd hperf
      ((Subgroup.closure Gen ⊔ O).subgroupOf J₁) (fun u hu =>
        hodd_mem (u : G) u.2 (by rwa [Subgroup.orderOf_coe]))
    intro j hj
    have : (⟨j, hj⟩ : ↥J₁) ∈ (Subgroup.closure Gen ⊔ O).subgroupOf J₁ := htop ▸ Subgroup.mem_top _
    exact this
  exact ⟨S₀, Subgroup.closure Gen, hS₀2, hS₀ne, hBS₀, hY₀J₁, hY₀N, hBY₀,
    le_antisymm (sup_le hY₀J₁ hOJ) hcov⟩

theorem centralizer_cover {p : ℕ} (hp : p.Prime) {D Y₀ J₁ : Subgroup G} (hD : IsPGroup p D)
    (hDY₀ : D ≤ Subgroup.normalizer (Y₀ : Set G)) (hY₀ : Y₀ ≤ J₁)
    (hcov : Y₀ ⊔ GLAPPrimeCoreOf p J₁ = J₁) (hDc : D ≤ centModSubgroup p J₁)
    (hDJ₁ : D ≤ Subgroup.normalizer (J₁ : Set G)) :
    (Y₀ ⊓ Subgroup.centralizer (D : Set G)) ⊔ GLAPPrimeCoreOf p J₁ = J₁ := by
  have hDQ : D ≤ Subgroup.normalizer ((Y₀ ⊓ GLAPPrimeCoreOf p J₁ : Subgroup G) : Set G) :=
    fun d hd => mem_normalizer_inf (hDY₀ hd)
      (normalizer_le_normalizer_glaPPrimeCoreOf p J₁ (hDJ₁ hd))
  have hcop : Nat.Coprime p (Nat.card ↥(Y₀ ⊓ GLAPPrimeCoreOf p J₁)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      ((hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp J₁))
  have key := S3.eq_inf_centralizer_sup_of_pgroup hp hD
    (inf_le_left : Y₀ ⊓ GLAPPrimeCoreOf p J₁ ≤ Y₀) hDQ hcop (fun y hy d hd => by
      refine ⟨?_, (hDc hd).2 y (hY₀ hy)⟩
      have h1 : d * y⁻¹ * d⁻¹ ∈ Y₀ := (Subgroup.mem_normalizer_iff.1 (hDY₀ hd) _).1 (Y₀.inv_mem hy)
      have : ⁅y, d⁆ = y * (d * y⁻¹ * d⁻¹) := by simp only [commutatorElement_def, mul_assoc]
      rw [this]
      exact Y₀.mul_mem hy h1)
  apply le_antisymm
  · exact sup_le (inf_le_left.trans hY₀) (Subgroup.map_subtype_le _)
  · calc J₁ = Y₀ ⊔ GLAPPrimeCoreOf p J₁ := hcov.symm
      _ = ((Y₀ ⊓ Subgroup.centralizer (D : Set G)) ⊔ (Y₀ ⊓ GLAPPrimeCoreOf p J₁)) ⊔
            GLAPPrimeCoreOf p J₁ := by rw [key]
      _ ≤ (Y₀ ⊓ Subgroup.centralizer (D : Set G)) ⊔ GLAPPrimeCoreOf p J₁ :=
        sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right)) le_sup_right

theorem pcomponent_cover {p : ℕ} (hp : p.Prime) {B D X J₁ J Y₁ : Subgroup G}
    (hJ₁ : GLAPComponent p X J₁) (hJ : GLAPComponent p (J₁ ⊓ Subgroup.centralizer (D : Set G)) J)
    (hcov : J ⊔ GLAPPrimeCoreOf p J₁ = J₁) (hY₁ : Y₁ ≤ J₁ ⊓ Subgroup.centralizer (D : Set G))
    (hY₁cov : Y₁ ⊔ GLAPPrimeCoreOf p J₁ = J₁) (hBY₁ : B ≤ Subgroup.normalizer (Y₁ : Set G)) :
    ∃ J₂ : Subgroup G, GLAPComponent p Y₁ J₂ ∧ J₂ ≤ J ∧ J₂ ⊔ GLAPPrimeCoreOf p J = J ∧
      B ≤ Subgroup.normalizer (J₂ : Set G) := by
  set Y : Subgroup G := J₁ ⊓ Subgroup.centralizer (D : Set G) with hY
  have hYJ₁ : Y ≤ J₁ := inf_le_left
  have hY₁J₁ : Y₁ ≤ J₁ := hY₁.trans hYJ₁
  have hJ₁q : CFSG.Open.IsQuasisimple (PQuot p J₁) := isQuasisimple_pQuot_of_glaPComponent hp hJ₁
  have hJY : J ≤ Y := hJ.1
  have hJJ₁ : J ≤ J₁ := hJY.trans hYJ₁
  have hYcov : Y ⊔ GLAPPrimeCoreOf p J₁ = J₁ :=
    le_antisymm (sup_le hYJ₁ (Subgroup.map_subtype_le _)) (by
      calc J₁ = J ⊔ GLAPPrimeCoreOf p J₁ := hcov.symm
        _ ≤ Y ⊔ GLAPPrimeCoreOf p J₁ := sup_le_sup_right hJY _)
  obtain ⟨-, ⟨eY⟩⟩ := cover_facts hp hYJ₁ hYcov
  have hYq : CFSG.Open.IsQuasisimple (PQuot p Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eY.symm hJ₁q
  obtain ⟨-, hallY, hbarY⟩ := glaPLayer_of_isQuasisimple hYq
  have hJeq : J = GLAPLayer p Y := hallY J hJ
  have hsupY : J ⊔ GLAPPrimeCoreOf p Y = Y :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJY (hJeq ▸ hbarY)
  have hYnormJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_unique_glaPComponent hJ fun J' hJ' => (hallY J' hJ').trans hJeq.symm
  obtain ⟨hOY₁, ⟨eY₁⟩⟩ := cover_facts hp hY₁J₁ hY₁cov
  have hY₁q : CFSG.Open.IsQuasisimple (PQuot p Y₁) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eY₁.symm hJ₁q
  obtain ⟨hJ₂comp, hallY₁, hbarY₁⟩ := glaPLayer_of_isQuasisimple hY₁q
  set J₂ : Subgroup G := GLAPLayer p Y₁ with hJ₂
  have hJ₂Y₁ : J₂ ≤ Y₁ := hJ₂comp.1
  have hsupY₁ : J₂ ⊔ GLAPPrimeCoreOf p Y₁ = Y₁ :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJ₂Y₁ hbarY₁
  have hJ₂J : J₂ ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup hp hJ₂comp
      ((hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp Y))
      ((Subgroup.map_subtype_le _).trans hYnormJ) (by rw [hsupY]; exact hJ₂Y₁.trans hY₁)
  have hJ₂cov₁ : J₂ ⊔ GLAPPrimeCoreOf p J₁ = J₁ := by
    have hO : GLAPPrimeCoreOf p Y₁ ≤ GLAPPrimeCoreOf p J₁ := by
      rw [hOY₁]; exact inf_le_right
    apply le_antisymm (sup_le (hJ₂Y₁.trans hY₁J₁) (Subgroup.map_subtype_le _))
    calc J₁ = Y₁ ⊔ GLAPPrimeCoreOf p J₁ := hY₁cov.symm
      _ = (J₂ ⊔ GLAPPrimeCoreOf p Y₁) ⊔ GLAPPrimeCoreOf p J₁ := by rw [hsupY₁]
      _ ≤ J₂ ⊔ GLAPPrimeCoreOf p J₁ :=
        sup_le (sup_le le_sup_left (hO.trans le_sup_right)) le_sup_right
  have hJ₂covJ : J₂ ⊔ GLAPPrimeCoreOf p J = J := by
    obtain ⟨hOJ, -⟩ := cover_facts hp hJJ₁ hcov
    apply le_antisymm (sup_le hJ₂J (Subgroup.map_subtype_le _))
    intro l hl
    obtain ⟨y, hy, hyl⟩ := exists_mul_of_cover (hJ₂Y₁.trans hY₁J₁) hJ₂cov₁ l (hJJ₁ hl)
    have h1 : y⁻¹ * l ∈ GLAPPrimeCoreOf p J := by
      rw [hOJ]; exact ⟨J.mul_mem (J.inv_mem (hJ₂J hy)) hl, hyl⟩
    have : l = y * (y⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h1)
  refine ⟨J₂, hJ₂comp, hJ₂J, hJ₂covJ, fun b hb => ?_⟩
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := glaPComponent_gLBConj hJ₂comp b
  rw [mem_normalizer_iff_gLBConj_eq.1 (hBY₁ hb)] at h1
  exact hallY₁ _ h1

theorem exists_order_p_not_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) :
    ∀ P : Sylow p (PQuot p J), ∃ x ∈ (P : Subgroup (PQuot p J)),
      x ^ p = 1 ∧ x ∉ Subgroup.center (PQuot p J) := by
  intro P
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hdvd : p ∣ Nat.card (PQuot p J) := by
    by_contra hnd
    have hnt : Nontrivial (PQuot p J) := isQuasisimple_nontrivial hQ
    have hbot : GLAPPrimeCore p (PQuot p J) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    have htop : (⊤ : Subgroup (PQuot p J)) ≤ GLAPPrimeCore p (PQuot p J) :=
      le_sSup ⟨inferInstance, by
        rw [Subgroup.card_top]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd⟩
    rw [hbot] at htop
    obtain ⟨u, v, huv⟩ := exists_pair_ne (PQuot p J)
    exact huv ((Subgroup.mem_bot.1 (htop (Subgroup.mem_top u))).trans
      (Subgroup.mem_bot.1 (htop (Subgroup.mem_top v))).symm)
  obtain ⟨x₀, hx₀ord, hx₀c⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hQ hp hp2 hdvd
  have hx₀p : x₀ ^ p = 1 := by
    have := pow_orderOf_eq_one x₀
    rwa [hx₀ord] at this
  have hzp : IsPGroup p (Subgroup.zpowers x₀) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hx₀ord]
    exact ⟨1, by simp⟩
  obtain ⟨P', hP'⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PQuot p J) P' P
  refine ⟨g * x₀ * g⁻¹, ?_, ?_, ?_⟩
  · have h1 : g * x₀ * g⁻¹ ∈ ((g • P' : Sylow p (PQuot p J)) : Subgroup (PQuot p J)) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨x₀, hP' (Subgroup.mem_zpowers x₀), by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rwa [hg] at h1
  · rw [conj_pow, hx₀p]; simp
  · intro hz
    apply hx₀c
    have h2 := Subgroup.mem_center_iff.1 hz g
    have : x₀ = g⁻¹ * (g * x₀ * g⁻¹) * g := by group
    rw [this]
    have h3 : g⁻¹ * (g * x₀ * g⁻¹) * g = (g * x₀ * g⁻¹) := by
      have := Subgroup.mem_center_iff.1 hz g⁻¹
      calc g⁻¹ * (g * x₀ * g⁻¹) * g = (g⁻¹ * (g * x₀ * g⁻¹)) * g := rfl
        _ = ((g * x₀ * g⁻¹) * g⁻¹) * g := by rw [this]
        _ = g * x₀ * g⁻¹ := by group
    rw [h3]; exact hz

theorem centMod_of_comm_ne {p : ℕ} (hp : p.Prime) {B X J₂ : Subgroup G}
    (hJ₂ : GLAPComponent p X J₂) (hBJ₂ : B ≤ Subgroup.normalizer (J₂ : Set G))
    (hne : (⁅B, J₂⁆ : Subgroup G) ≠ J₂) : B ≤ centModSubgroup p J₂ := by
  classical
  set W : Subgroup G := ⁅J₂, B⁆ with hW
  have hWJ : W ≤ J₂ := Subgroup.le_normalizer_iff_commutator_le_left.1 hBJ₂
  have hWne : W ≠ J₂ := by rw [hW, Subgroup.commutator_comm]; exact hne
  have hJW : J₂ ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_left J₂ B
  have hWn : (W.subgroupOf J₂).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWJ).2 hJW
  have hWsn : IsSubnormal W X := IsSubnormal.step hWJ hWn hJ₂.2.1
  have hWX : W ≤ X := hWJ.trans hJ₂.1
  have hQ : CFSG.Open.IsQuasisimple (PQuot p J₂) := isQuasisimple_pQuot_of_glaPComponent hp hJ₂
  set π : ↥J₂ →* PQuot p J₂ := QuotientGroup.mk' (GLAPPrimeCore p ↥J₂) with hπ
  set M : Subgroup (PQuot p J₂) := (W.subgroupOf J₂).map π with hM
  have hMn : M.Normal := hWn.map π (QuotientGroup.mk'_surjective _)
  have hcoreX : GLAPPrimeCoreOf p J₂ ≤ GLAPPrimeCoreOf p X := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ₂.2.1]
    exact inf_le_right
  have hMtop : M ≠ ⊤ := by
    intro hMt
    refine hJ₂.2.2.2 W (lt_of_le_of_ne hWJ hWne) hWsn ?_
    show barX p X W = barX p X J₂
    refine le_antisymm (barX_mono p hWJ) (barX_le_of_forall hWX (fun k hk => ?_))
    have hk' : π ⟨k, hk⟩ ∈ M := hMt ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwk⟩ := hk'
    refine ⟨(w : G), (Subgroup.mem_subgroupOf).1 hw, hcoreX ?_⟩
    have h1 : w⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore p ↥J₂ := (QuotientGroup.eq).1 hwk
    exact ⟨_, h1, by simp⟩
  have hMcen : M ≤ Subgroup.center (PQuot p J₂) :=
    le_center_of_normal_of_isQuasisimple hQ hMn hMtop
  have hcommJ : ∀ b ∈ B, ∀ j ∈ J₂, ⁅j, b⁆ ∈ J₂ := fun b hb j hj =>
    hWJ (Subgroup.commutator_mem_commutator hj hb)
  have hcent : ∀ b (hb : b ∈ B) (j : ↥J₂), π ⟨⁅(j : G), b⁆, hcommJ b hb j j.2⟩ ∈
      Subgroup.center (PQuot p J₂) := by
    intro b hb j
    refine hMcen ⟨_, ?_, rfl⟩
    exact (Subgroup.mem_subgroupOf).2 (Subgroup.commutator_mem_commutator j.2 hb)
  haveI : Group.IsPerfect ↥J₂ := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hJ₂)
  have hkey : ∀ (c a₁ a₂ : PQuot p J₂), a₁ ∈ Subgroup.center (PQuot p J₂) →
      a₂ ∈ Subgroup.center (PQuot p J₂) → c * a₂ * c⁻¹ * a₁ = a₁ * a₂ := by
    intro c a₁ a₂ h1 h2
    have e2 := Subgroup.mem_center_iff.1 h2 c
    have e1 := Subgroup.mem_center_iff.1 h1 a₂
    calc c * a₂ * c⁻¹ * a₁ = (a₂ * c) * c⁻¹ * a₁ := by rw [e2]
      _ = a₂ * a₁ := by group
      _ = a₁ * a₂ := e1
  intro b hb
  refine ⟨hBJ₂ hb, fun l hl => ?_⟩
  let ψ : ↥J₂ →* PQuot p J₂ :=
    { toFun := fun j => π ⟨⁅(j : G), b⁆, hcommJ b hb j j.2⟩
      map_one' := by
        have : (⟨⁅(((1 : ↥J₂)) : G), b⁆, hcommJ b hb 1 (Subgroup.one_mem _)⟩ : ↥J₂) = 1 :=
          Subtype.ext (by simp)
        simp only [this, map_one]
      map_mul' := by
        intro j₁ j₂
        have e : (⟨⁅((j₁ * j₂ : ↥J₂) : G), b⁆, hcommJ b hb _ (j₁ * j₂).2⟩ : ↥J₂) =
            j₁ * ⟨⁅(j₂ : G), b⁆, hcommJ b hb j₂ j₂.2⟩ * j₁⁻¹ *
              ⟨⁅(j₁ : G), b⁆, hcommJ b hb j₁ j₁.2⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        simp only [e, map_mul, map_inv]
        exact hkey _ _ _ (hcent b hb j₁) (hcent b hb j₂) }
  have hψ : ψ = 1 := by
    have hψc : ∀ j, ψ j ∈ Subgroup.center (PQuot p J₂) := fun j => hcent b hb j
    have := eq_one_of_isPerfect_of_isSolvable' (ψ.codRestrict (Subgroup.center (PQuot p J₂)) hψc)
    ext j
    have h3 := DFunLike.congr_fun this j
    exact congrArg Subtype.val h3
  have h4 : ψ ⟨l, hl⟩ = 1 := DFunLike.congr_fun hψ ⟨l, hl⟩
  have h5 : (⟨⁅l, b⁆, hcommJ b hb l hl⟩ : ↥J₂) ∈ GLAPPrimeCore p ↥J₂ :=
    (QuotientGroup.eq_one_iff _).1 h4
  exact ⟨_, h5, rfl⟩

theorem comm_B_J2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B X J₂ M : Subgroup G}
    (hB : GLAIsBmax p B) (hJ₂ : GLAPComponent p X J₂) (hBJ₂ : B ≤ Subgroup.normalizer (J₂ : Set G))
    (hJ₂M : J₂ ≤ M) (hBM : B ≤ M) (hM : IsTwoLocal M) : (⁅B, J₂⁆ : Subgroup G) = J₂ := by
  by_contra hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hcen : B ≤ centModSubgroup p J₂ := centMod_of_comm_ne hp hJ₂ hBJ₂ hne
  set Y : Subgroup G := J₂ ⊓ Subgroup.centralizer (B : Set G) with hY
  have hYJ : Y ≤ J₂ := inf_le_left
  have hcov : Y ⊔ GLAPPrimeCoreOf p J₂ = J₂ :=
    S3.eq_inf_centralizer_sup_of_pgroup hp (GLAIsBmax.isPGroup hB) (Subgroup.map_subtype_le _)
      (fun b hb => normalizer_le_normalizer_glaPPrimeCoreOf p J₂ (hBJ₂ hb))
      ((hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp J₂))
      (fun y hy b hb => (hcen hb).2 y hy)
  let g : ↥Y →* PQuot p J₂ :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥J₂)).comp (Subgroup.inclusion hYJ)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨y, hy, o', ho', hoeq⟩ := exists_mul_of_cover hYJ hcov l hl
    refine ⟨⟨y, hy⟩, ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥J₂) (Subgroup.inclusion hYJ ⟨y, hy⟩) = _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (Subgroup.inclusion hYJ ⟨y, hy⟩)⁻¹ * ⟨l, hl⟩ = o' :=
      Subtype.ext (by simpa using hoeq.symm)
    rw [this]; exact ho'
  obtain ⟨R⟩ : Nonempty (Sylow p ↥Y) := inferInstance
  obtain ⟨xb, hxbR, hxbp, hxbc⟩ := exists_order_p_not_central hp hp2 hJ₂ (R.mapSurjective hg)
  obtain ⟨r, hrR, hrx⟩ := hxbR
  set x : G := ((r : ↥Y) : G) with hxdef
  have hxY : x ∈ Y := r.2
  have hxJ₂ : x ∈ J₂ := hYJ hxY
  have hxC : x ∈ Subgroup.centralizer (B : Set G) := (inf_le_right : Y ≤ _) hxY
  have hgr : g r = QuotientGroup.mk' (GLAPPrimeCore p ↥J₂) ⟨x, hxJ₂⟩ := rfl
  have hxp : x ^ p = 1 := by
    have h1 : g (r ^ p) = 1 := by rw [map_pow, hrx]; exact hxbp
    have h2 : (⟨x ^ p, J₂.pow_mem hxJ₂ p⟩ : ↥J₂) ∈ GLAPPrimeCore p ↥J₂ :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 : x ^ p ∈ GLAPPrimeCoreOf p J₂ := ⟨_, h2, rfl⟩
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hrR⟩
    have hk' : x ^ (p ^ k) = 1 := by
      have := congrArg (fun t : ↥(R : Subgroup ↥Y) => (((t : ↥Y)) : G)) hk
      simpa using this
    have hcop : Nat.Coprime (p ^ k) (Nat.card (GLAPPrimeCoreOf p J₂)) :=
      Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).2 (not_dvd_card_glaPPrimeCoreOf hp J₂))
    have hd1 : orderOf (x ^ p) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hk', one_pow])
    have hd2 : orderOf (x ^ p) ∣ Nat.card (GLAPPrimeCoreOf p J₂) :=
      Subgroup.orderOf_dvd_natCard _ h3
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hxB : x ∉ B := by
    intro hxB
    apply hxbc
    rw [← hrx, hgr]
    have hxcm := hcen hxB
    refine Subgroup.mem_center_iff.2 fun q => ?_
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨o', ho', hoeq⟩ := hxcm.2 l hl
    have h2 : ⁅(⟨l, hl⟩ : ↥J₂), (⟨x, hxJ₂⟩ : ↥J₂)⁆ = o' := by
      apply Subtype.ext
      exact hoeq.symm
    have h3 : ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥J₂) (⟨l, hl⟩ : ↥J₂),
        QuotientGroup.mk' (GLAPPrimeCore p ↥J₂) (⟨x, hxJ₂⟩ : ↥J₂)⁆ = 1 := by
      rw [← map_commutatorElement, h2]
      exact (QuotientGroup.eq_one_iff _).2 ho'
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have hz : ∀ e ∈ B, e * x = x * e := fun e he => Subgroup.mem_centralizer_iff.1 hxC e he
  have hEel : IsElemAbelian p (B ⊔ Subgroup.zpowers x) :=
    isElemAbelian_sup_zpowers_aux hB.1 hxp hz
  obtain ⟨S, hSne, hS2, hMS⟩ := hM
  have hES : B ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) := by
    rw [← hMS]
    refine sup_le hBM ?_
    rw [Subgroup.zpowers_le]; exact hJ₂M hxJ₂
  have hle := card_le_pow_glaTwoLocalRank hp hEel hSne hS2 hES
  rw [← hB.2.1] at hle
  have hEB : B = B ⊔ Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  exact hxB (hEB ▸ (le_sup_right : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x))

theorem i321 {R J : Subgroup G} (hR2 : IsPGroup 2 R) (hJ : (⁅J, J⁆ : Subgroup G) = J)
    (hJR : J ≤ Subgroup.normalizer (R : Set G)) :
    (⁅(⁅R, J⁆ : Subgroup G), J⁆ : Subgroup G) = ⁅R, J⁆ :=
  commutator_commutator_eq_of_perfect hR2 hJ hJR

theorem three_subgroups_ne_bot {B J₂ T : Subgroup G} (hBJ : (⁅B, J₂⁆ : Subgroup G) = J₂)
    (hJT : (⁅J₂, T⁆ : Subgroup G) = T) (hT : T ≠ ⊥) : (⁅T, B⁆ : Subgroup G) ≠ ⊥ := by
  intro hTB
  have h1 : ⁅⁅J₂, T⁆, B⁆ = ⊥ := by rw [hJT]; exact hTB
  have h2 : ⁅⁅T, B⁆, J₂⁆ = ⊥ := by rw [hTB]; exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 bot_le
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hBJ, hJT] at h3
  exact hT h3

theorem isEmpty_quaternion_of_action {R H : Subgroup G}
    (hHR : H ≤ Subgroup.normalizer (R : Set G)) (hH : (⁅H, H⁆ : Subgroup G) = H)
    (hne : (⁅R, H⁆ : Subgroup G) ≠ ⊥) : IsEmpty (R ≃* QuaternionGroup 2) := by
  refine ⟨fun e => ?_⟩
  haveI : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  haveI : Group.IsSolvable (MulAut (QuaternionGroup 2)) := by
    simpa using CFSG.ProperTwoGeneratedCore.quaternion_power_two_automorphism_solvable 1
  haveI : Group.IsSolvable (MulAut R) :=
    Group.isSolvable_of_isSolvable_injective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).injective
  have hφ := eq_one_of_isPerfect_of_isSolvable'
    ((Subgroup.normalizerMonoidHom (H := R)).comp (Subgroup.inclusion hHR))
  have hcomm : ∀ h ∈ H, ∀ w ∈ R, h * w = w * h := by
    intro h hh w hw
    have h1 : (Subgroup.normalizerMonoidHom (H := R)) ⟨h, hHR hh⟩ = 1 :=
      DFunLike.congr_fun hφ ⟨h, hh⟩
    have h2 := congrArg (fun f : MulAut R => ((f ⟨w, hw⟩ : R) : G)) h1
    have h3 : h * w * h⁻¹ = w := h2
    calc h * w = h * w * h⁻¹ * h := by group
      _ = w * h := by rw [h3]
  have hbot : (⁅R, H⁆ : Subgroup G) = ⊥ := by
    refine le_antisymm (Subgroup.commutator_le.mpr ?_) bot_le
    intro w hw h hh
    rw [Subgroup.mem_bot, commutatorElement_def, ← hcomm h hh w hw]
    group
  exact hne hbot

theorem cover_trans {p : ℕ} (hp : p.Prime) {X J₃ J J₂ : Subgroup G} (hJ₃ : GLAPComponent p X J₃)
    (hJJ₃ : J ≤ J₃) (hcov : J ⊔ GLAPPrimeCoreOf p J₃ = J₃) (hJ₂J : J₂ ≤ J)
    (hcov₂ : J₂ ⊔ GLAPPrimeCoreOf p J = J) : J₂ ⊔ GLAPPrimeCoreOf p J₃ = J₃ := by
  have hO : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p J₃ := by
    rw [(cover_facts hp hJJ₃ hcov).1]; exact inf_le_right
  apply le_antisymm
  · exact sup_le (hJ₂J.trans hJJ₃) (Subgroup.map_subtype_le _)
  · calc J₃ = J ⊔ GLAPPrimeCoreOf p J₃ := hcov.symm
      _ = (J₂ ⊔ GLAPPrimeCoreOf p J) ⊔ GLAPPrimeCoreOf p J₃ := by rw [hcov₂]
      _ ≤ J₂ ⊔ GLAPPrimeCoreOf p J₃ :=
        sup_le (sup_le le_sup_left (hO.trans le_sup_right)) le_sup_right

theorem two_group_le_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J₃ J₂ T : Subgroup G}
    (hJ₃ : GLAPComponent p X J₃) (hJ₂J₃ : J₂ ≤ J₃) (hcov : J₂ ⊔ GLAPPrimeCoreOf p J₃ = J₃)
    (hT2 : IsPGroup 2 T) (hTX : T ≤ X) (hJ₂T : J₂ ≤ Subgroup.normalizer (T : Set G))
    (hT : (⁅J₂, T⁆ : Subgroup G) = T) : T ≤ GLAPPrimeCoreOf p X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ₃L : J₃ ≤ GLAPLayer p X := le_sSup hJ₃
  have hTJ₃ : T ≤ Subgroup.normalizer (J₃ : Set G) := by
    refine S3.normalizes_of_comm (A := J₂) (fun t ht => ?_)
      (by rw [Subgroup.commutator_comm]; exact hT.ge)
    have h1 := glaPComponent_gLBConj hJ₃ t
    rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hTX ht))] at h1
    exact hJ₂J₃.trans (hJ₃L.trans
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le_normalizer hp h1))
  have hTJ₃' : T ≤ J₃ := by
    calc T = ⁅J₂, T⁆ := hT.symm
      _ ≤ ⁅J₃, T⁆ := Subgroup.commutator_mono hJ₂J₃ le_rfl
      _ ≤ J₃ := Subgroup.le_normalizer_iff_commutator_le_left.1 hTJ₃
  have hbarJ₂ : barX p J₃ J₂ = ⊤ := by
    refine top_le_iff.1 ((barX_self p J₃).symm.le.trans (barX_le_of_forall hJ₂J₃ ?_))
    intro l hl
    have hIO : J₂ ≤ Subgroup.normalizer (GLAPPrimeCoreOf p J₃ : Set G) :=
      hJ₂J₃.trans (le_normalizer_glaPPrimeCoreOf p J₃)
    have hl' : l ∈ (J₂ ⊔ GLAPPrimeCoreOf p J₃ : Subgroup G) := hcov.symm ▸ hl
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right J₂ _ hIO] at hl'
    obtain ⟨y, hy, o, ho, hyo⟩ := Set.mem_mul.mp hl'
    refine ⟨y, hy, ?_⟩
    have : y⁻¹ * l = o := by rw [← hyo]; group
    rw [this]; exact ho
  have hnorm : (barX p J₃ T).Normal := by
    have h1 := barX_le_normalizer (p := p) (C := J₃) hJ₂T
    rw [hbarJ₂] at h1
    exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h1)
  have hT2' : IsPGroup 2 (barX p J₃ T) := (hT2.comap_of_injective J₃.subtype Subtype.coe_injective).map _
  have hcop : Nat.Coprime p (Nat.card (barX p J₃ T)) := by
    obtain ⟨n, hn⟩ := hT2'.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hTb : barX p J₃ T ≤ GLAPPrimeCore p (↥J₃ ⧸ GLAPPrimeCore p ↥J₃) := le_sSup ⟨hnorm, hcop⟩
  rw [glaPPrimeCore_quotient_eq_bot hp, le_bot_iff] at hTb
  have hTO : T ≤ GLAPPrimeCoreOf p J₃ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_eq_bot_iff hTJ₃').1 hTb
  exact hTO.trans (glaPPrimeCoreOf_le_of_isSubnormal hp hJ₃.2.1)

theorem stage_two {p : ℕ} (hc : S3Ctx G p) (hI18 : Input18_3_4) (h1135 : I1135At G p)
    (hCl : ChevClosureAt G p) (hUn : ChevUniqueAt G p) {B D J D₁ N : Subgroup G}
    (hS : Star3 G p B) (hDB : D ≤ B) (hDnc : ¬ IsCyclic D)
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) (hD₁D : D₁ ≤ D)
    (hidx₁ : Nat.card D₁ * p = Nat.card D) (hD₁1 : D₁ ≠ ⊥)
    (hess₁ : ∀ d ∈ D₁, d ≠ 1 → IsEssential p B d)
    (hcover : Cover36 p B D J D₁ (layerClosure p D₁ J)) (hN : GLAIsMaxTwoLocal N) (hBN : B ≤ N)
    (hSne : (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ : Subgroup G) ≠ ⊥) :
    ∃ D₂ T J₂ : Subgroup G, D₂ ≤ D ∧ Nat.card D₂ * p = Nat.card D ∧ D₂ ≠ ⊥ ∧
      (∀ d ∈ D₂, d ≠ 1 → IsEssential p B d) ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      T ≤ Subgroup.centralizer (D₂ : Set G) ∧ J₂ ≤ J ∧ J₂ ⊔ GLAPPrimeCoreOf p J = J ∧
      J₂ ≤ Subgroup.normalizer (T : Set G) ∧ (⁅J₂, T⁆ : Subgroup G) = T := by
  have _ := hN
  have hp := hc.prime
  have hp2 := hc.odd
  have hBel := hS.bmax.1
  have hDel : IsElemAbelian p D := isElemAbelian_mono hBel hDB
  have hDne : D ≠ ⊥ := by
    rintro rfl
    exact hDnc inferInstance
  have hD₁B : D₁ ≤ B := hD₁D.trans hDB
  obtain ⟨d₁, hd₁, hd₁1⟩ := exists_ne_one_of_ne_bot hD₁1
  have hess₁' : ∃ d ∈ D₁, IsEssential p B d := ⟨d₁, hd₁, hess₁ d₁ hd₁ hd₁1⟩
  obtain ⟨hJ₁comp, -, hBJ₁, -, -, hJcomp, hJcov, hDcent⟩ := hcover
  obtain ⟨hS2, hSc, hBS, hSS⟩ := S3.S_props hBel hp hp2 hDB hD₁D hBN
  have hSD : (⁅⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆, D⁆ : Subgroup G) =
      ⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ :=
    (Subgroup.commutator_comm _ D).trans hSS
  have hSJ₁ : (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ : Subgroup G) ≤
      Subgroup.normalizer ((layerClosure p D₁ J : Subgroup G) : Set G) := by
    refine S3.normalizes_of_comm (A := D) (fun t ht => ?_) hSD.ge
    have hfix : GLBConj t (Subgroup.centralizer (D₁ : Set G)) = Subgroup.centralizer (D₁ : Set G) :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hSc ht))
    have hcomp := glaPComponent_gLBConj hJ₁comp t
    rw [hfix] at hcomp
    exact hDB.trans (lemma34_iii hc hI18 h1135 hCl hUn hS hD₁B hess₁' hcomp).2
  have hScM : (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₁ : Set G)⁆ : Subgroup G) ≤
      centModSubgroup p (layerClosure p D₁ J) :=
    S3.le_centModSubgroup_of_comm hDcent hSJ₁ hSD.ge
  obtain ⟨S₀, Y₀, hS₀2, hS₀ne, hBS₀, hY₀J₁, hY₀S₀, hBY₀, hY₀cov⟩ :=
    S3.frattini_cover hp hp2 hBel hJ₁comp hBJ₁ hS2 hSne hSJ₁ hScM hBS
  set M : Subgroup G := Subgroup.normalizer (S₀ : Set G)
  have hMloc : IsTwoLocal M := ⟨S₀, hS₀ne, hS₀2, rfl⟩
  have hBM : B ≤ M := hBS₀
  have hDM : D ≤ M := hDB.trans hBM
  have hY₁cov : (Y₀ ⊓ Subgroup.centralizer (D : Set G)) ⊔
      GLAPPrimeCoreOf p (layerClosure p D₁ J) = layerClosure p D₁ J :=
    S3.centralizer_cover hp (isPGroup_of_isElemAbelian hDel) (hDB.trans hBY₀) hY₀J₁ hY₀cov
      hDcent (hDB.trans hBJ₁)
  have hBcent : B ≤ Subgroup.centralizer (D : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hBel (hDB hd) hb
  have hBY₁ : B ≤ Subgroup.normalizer
      ((Y₀ ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_inf (hBY₀ hb) (Subgroup.le_normalizer (hBcent hb))
  obtain ⟨J₂, hJ₂comp, hJ₂J, hJ₂cov, hBJ₂⟩ :=
    S3.pcomponent_cover hp hJ₁comp hJcomp hJcov (inf_le_inf_right _ hY₀J₁) hY₁cov hBY₁
  have hJ₂Y₁ : J₂ ≤ Y₀ ⊓ Subgroup.centralizer (D : Set G) := hJ₂comp.1
  have hJ₂M : J₂ ≤ M := hJ₂Y₁.trans (inf_le_left.trans hY₀S₀)
  have hJ₂D : J₂ ≤ Subgroup.centralizer (D : Set G) := hJ₂Y₁.trans inf_le_right
  have hJ₂perf : (⁅J₂, J₂⁆ : Subgroup G) = J₂ := glaPComponent_perfect hJ₂comp
  have hBJ₂comm : (⁅B, J₂⁆ : Subgroup G) = J₂ :=
    S3.comm_B_J2 hp hp2 hS.bmax hJ₂comp hBJ₂ hJ₂M hBM hMloc
  have hJ₂ne : J₂ ≠ ⊥ := by
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ₂comp
    haveI : IsSimpleGroup (PQuot p J₂ ⧸ Subgroup.center (PQuot p J₂)) := hq.2
    haveI : Nontrivial (PQuot p J₂) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center (PQuot p J₂))).nontrivial
    haveI : Nontrivial ↥J₂ :=
      (QuotientGroup.mk_surjective (s := GLAPPrimeCore p ↥J₂)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot J₂).1 this
  have hJ₂not2 : ¬ IsPGroup 2 J₂ := not_isPGroup_two_of_perfect hJ₂perf hJ₂ne
  obtain ⟨D₂, hD₂D, hD₂idx, hD₂comm⟩ :=
    GL83.I_33_3_proved G hc.charTwo p hp hp2 M D J₂ hMloc hDne hDel hDM
      (le_inf hJ₂M hJ₂D) hJ₂not2
  have hcard : Nat.card D₂ * p = Nat.card D := by
    have h1 := Subgroup.card_mul_index (D₂.subgroupOf D)
    rw [hD₂idx] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₂D).toEquiv] at h1
  have hD₂ne : D₂ ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    have h2 : p ^ 2 ≤ Nat.card D := S3.card_ge_of_not_isCyclic hp hDel hDnc
    rw [h1, one_mul] at hcard
    have := hp.two_le
    nlinarith
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R₂ : Subgroup G := pCoreOf 2 M ⊓ Subgroup.centralizer (D₂ : Set G)
  have hR₂2 : IsPGroup 2 R₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hJ₂R₂ : J₂ ≤ Subgroup.normalizer (R₂ : Set G) := fun g hg =>
    mem_normalizer_inf (le_normalizer_pCoreOf 2 M (hJ₂M hg))
      (Subgroup.le_normalizer (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hD₂D) (hJ₂D hg)))
  have hRJ : (⁅R₂, J₂⁆ : Subgroup G) ≤ R₂ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hJ₂R₂
  have hTne : (⁅R₂, J₂⁆ : Subgroup G) ≠ ⊥ := by
    rw [Subgroup.commutator_comm R₂ J₂]
    exact hD₂comm
  have hT2 : IsPGroup 2 (⁅R₂, J₂⁆ : Subgroup G) := hR₂2.to_le hRJ
  have hTc : (⁅R₂, J₂⁆ : Subgroup G) ≤ Subgroup.centralizer (D₂ : Set G) :=
    hRJ.trans inf_le_right
  have hJ₂T : J₂ ≤ Subgroup.normalizer ((⁅R₂, J₂⁆ : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_commutator (hJ₂R₂ hg) (Subgroup.le_normalizer hg)
  have hJT : (⁅J₂, (⁅R₂, J₂⁆ : Subgroup G)⁆ : Subgroup G) = ⁅R₂, J₂⁆ :=
    (Subgroup.commutator_comm J₂ _).trans (S3.i321 hR₂2 hJ₂perf hJ₂R₂)
  have hRB : (⁅R₂, B⁆ : Subgroup G) ≠ ⊥ := by
    have h := S3.three_subgroups_ne_bot hBJ₂comm hJT hTne
    intro hbot
    exact h (le_bot_iff.1 ((Subgroup.commutator_mono hRJ le_rfl).trans hbot.le))
  have hBR₂ : B ≤ Subgroup.normalizer (R₂ : Set G) := fun b hb =>
    mem_normalizer_inf (le_normalizer_pCoreOf 2 M (hBM hb))
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.2 fun d hd =>
        isElemAbelian_commute hBel (hDB (hD₂D hd)) hb))
  have hess₂ : ∀ d ∈ D₂, d ≠ 1 → IsEssential p B d := fun d hd hd1 =>
    ⟨hDB (hD₂D hd), hd1, R₂,
      inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd)), hR₂2, hBR₂,
      hRB, fun _ => S3.isEmpty_quaternion_of_action hJ₂R₂ hJ₂perf hTne⟩
  exact ⟨D₂, ⁅R₂, J₂⁆, J₂, hD₂D, hcard, hD₂ne, hess₂, hT2, hTne, hTc, hJ₂J, hJ₂cov, hJ₂T, hJT⟩

end S3

theorem i321_holds :
    ∀ (G : Type) [Group G] [Finite G] (R J : Subgroup G), IsPGroup 2 R → (⁅J, J⁆ : Subgroup G) = J →
      J ≤ Subgroup.normalizer (R : Set G) → (⁅(⁅R, J⁆ : Subgroup G), J⁆ : Subgroup G) = ⁅R, J⁆ :=
  fun _ _ _ _ _ hR hJ hJR => S3.i321 hR hJ hJR

theorem i68_holds (p : ℕ) :
    p.Prime → p ≠ 2 → ∀ X J : Subgroup G, GLAPComponent p X J →
      ∀ P : Sylow p (PQuot p J), ∃ x ∈ (P : Subgroup (PQuot p J)), x ^ p = 1 ∧
        x ∉ Subgroup.center (PQuot p J) := fun hp hp2 _ _ hJ P =>
  S3.exists_order_p_not_central hp hp2 hJ P

theorem lemma36 {p : ℕ} (hc : S3Ctx G p) (hI18 : Input18_3_4) (h1135 : I1135At G p)
    (hCl : ChevClosureAt G p) (hUn : ChevUniqueAt G p) (hInn : ChevInnerAt G p)
    {B D J : Subgroup G} (hS : Star3 G p B) (hDB : D ≤ B) (hDnc : ¬ IsCyclic D)
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J) :
    ∃ D' J' : Subgroup G, Step36 p B D J D' J' := by
  have hp := hc.prime
  have hDel : IsElemAbelian p D := isElemAbelian_mono hS.bmax.1 hDB
  obtain ⟨N, hN, hBN⟩ := GLAIsBmax.exists_maxTwoLocal hS.bmax
  obtain ⟨D₁, hD₁D, hidx₁, hess₁, hSne⟩ := hc.lemma31 B D N hS.bmax hDB hDnc hN hBN
  have hD₁1 : D₁ ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    have h2 : p ^ 2 ≤ Nat.card D := S3.card_ge_of_not_isCyclic hp hDel hDnc
    rw [h1, one_mul] at hidx₁
    have := hp.two_le
    nlinarith
  rcases S3.stage_step hc hI18 h1135 hCl hUn hInn hS hDB hJ hD₁D hidx₁ hD₁1 hess₁ with
    hstep | hcover
  · exact ⟨D₁, _, hstep⟩
  obtain ⟨D₂, T, J₂, hD₂D, hidx₂, hD₂1, hess₂, hT2, hTne, hTc, hJ₂J, hJ₂cov, hJ₂T, hJT⟩ :=
    S3.stage_two hc hI18 h1135 hCl hUn hS hDB hDnc hJ hD₁D hidx₁ hD₁1 hess₁ hcover hN hBN hSne
  rcases S3.stage_step hc hI18 h1135 hCl hUn hInn hS hDB hJ hD₂D hidx₂ hD₂1 hess₂ with
    hstep | hcover₂
  · exact ⟨D₂, _, hstep⟩
  exfalso
  obtain ⟨hJ₃, -, -, -, hJJ₃, -, hcov, -⟩ := hcover₂
  have hcov₂ : J₂ ⊔ GLAPPrimeCoreOf p (layerClosure p D₂ J) = layerClosure p D₂ J :=
    S3.cover_trans hp hJ₃ hJJ₃ hcov hJ₂J hJ₂cov
  have hTO : T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (D₂ : Set G)) :=
    S3.two_group_le_core hp hc.odd hJ₃ (hJ₂J.trans hJJ₃) hcov₂ hT2 hTc hJ₂T hJT
  have hodd := lemma34_ii hc hS (hD₂D.trans hDB) hD₂1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2dvd : 2 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rcases k with _ | k
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hk)) hTne
    · rw [hk]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  exact (Nat.not_even_iff_odd.2 hodd)
    (even_iff_two_dvd.2 (hT2dvd.trans (Subgroup.card_dvd_of_le hTO)))

end CFSG.LocalAnalysis.GLTheoremA
