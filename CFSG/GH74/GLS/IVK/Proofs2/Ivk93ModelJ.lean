module

public import CFSG.GH74.GLS.Stage2.Final.ModelIVK410Final
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Nu

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem jm_card_sup_mul_card_inf {Q : Type*} [Group Q] (A B : Subgroup Q)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥A × ↥B →* Q, φ = A.subtype.noncommCoprod B.subtype hcm := ⟨_, rfl⟩
  have happ : ∀ p : ↥A × ↥B, φ p = (p.1 : Q) * (p.2 : Q) := fun p => by rw [hφ]; rfl
  have hrange : φ.range = A ⊔ B := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card ↥φ.ker = Nat.card ↥(A ⊓ B) := by
    have key : ∀ u : ↥φ.ker, (u.1.1 : Q) * (u.1.2 : Q) = 1 := fun u => by
      have := u.2
      rw [MonoidHom.mem_ker, happ] at this
      exact this
    refine Nat.card_congr
      { toFun := fun u => ⟨(u.1.1 : Q), u.1.1.2, by
          rw [eq_inv_of_mul_eq_one_left (key u)]; exact B.inv_mem u.1.2.2⟩
        invFun := fun x => ⟨(⟨(x : Q), x.2.1⟩, ⟨(x : Q)⁻¹, B.inv_mem x.2.2⟩), by
          rw [MonoidHom.mem_ker, happ]
          exact mul_inv_cancel _⟩
        left_inv := fun u => ?_
        right_inv := fun x => rfl }
    exact Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext (inv_eq_of_mul_eq_one_right (key u))))
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [Nat.card_prod, hker] at h1
  have h2 : Nat.card ↥φ.range = Nat.card ↥(A ⊔ B) := by rw [hrange]
  rw [h2] at h1
  rw [mul_comm]
  exact h1

section SylowPart

variable {K : Type} [Group K]

theorem jm_Ez_le_centralizer (z : K) : IVK.Ez z ≤ centralizer ({z} : Set K) :=
  Subgroup.map_subtype_le _

theorem jm_centralizer_le_normalizer_Ez (z : K) :
    centralizer ({z} : Set K) ≤ normalizer ((IVK.Ez z : Subgroup K) : Set K) := by
  have hn : ((IVK.Ez z).subgroupOf (centralizer ({z} : Set K))).Normal := by
    have h : (IVK.Ez z).subgroupOf (centralizer ({z} : Set K)) =
        layer ↥(centralizer ({z} : Set K)) := by
      unfold IVK.Ez
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        (centralizer ({z} : Set K)).subtype_injective]
    rw [h]
    have : (layer ↥(centralizer ({z} : Set K))).Characteristic :=
      CFSG.LocalCores.layer_characteristic
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (jm_Ez_le_centralizer z)).mp hn

theorem jm_le_normalizer_inf {S T : Subgroup K} (hST : S ≤ normalizer (T : Set K)) :
    S ≤ normalizer ((S ⊓ T : Subgroup K) : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hgT := Subgroup.mem_normalizer_iff.mp (hST hg) h
  constructor
  · rintro ⟨hS, hT⟩
    exact ⟨S.mul_mem (S.mul_mem hg hS) (S.inv_mem hg), hgT.mp hT⟩
  · rintro ⟨hS, hT⟩
    refine ⟨?_, hgT.mpr hT⟩
    have := S.mul_mem (S.mul_mem (S.inv_mem hg) hS) hg
    simpa [mul_assoc] using this

theorem jm_isSylowOf_of_le [Finite K] (P : Sylow 2 K) {L : Subgroup K}
    (hPL : (P : Subgroup K) ≤ L) : IsSylowOf 2 (P : Subgroup K) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : IsSylowOf 2 (P : Subgroup K) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  exact htop.of_le hPL le_top

theorem jm_card_sylow_of_decomp [Finite K] (P : Sylow 2 K) {z t w : K}
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x)
    (htP : t ∈ (P : Subgroup K)) (hwP : w ∈ (P : Subgroup K))
    (hPdec : (P : Subgroup K) = ((P : Subgroup K) ⊓ IVK.Ez z) ⊔ zpowers t ⊔ zpowers w)
    (hinf : IVK.Ez z ⊓ (zpowers t ⊔ zpowers w) = ⊥) :
    Nat.card ↥(P : Subgroup K) =
      2 ^ (Nat.card ↥(IVK.Ez z)).factorization 2 * Nat.card ↥(zpowers t ⊔ zpowers w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : (P : Subgroup K) ≤ centralizer ({z} : Set K) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzc x hx
  have hPN : (P : Subgroup K) ≤ normalizer ((IVK.Ez z : Subgroup K) : Set K) :=
    hPC.trans (jm_centralizer_le_normalizer_Ez z)
  have hsyl : IsSylowOf 2 ((P : Subgroup K) ⊓ IVK.Ez z) (IVK.Ez z) :=
    (jm_isSylowOf_of_le P hPC).inf_of_le_normalizer (jm_Ez_le_centralizer z)
      (jm_centralizer_le_normalizer_Ez z)
  have hNcard := hsyl.card_eq
  have hTP : zpowers t ⊔ zpowers w ≤ (P : Subgroup K) :=
    sup_le (Subgroup.zpowers_le.mpr htP) (Subgroup.zpowers_le.mpr hwP)
  have hTN : zpowers t ⊔ zpowers w ≤
      normalizer (((P : Subgroup K) ⊓ IVK.Ez z : Subgroup K) : Set K) :=
    hTP.trans (jm_le_normalizer_inf hPN)
  have hdisj : Disjoint ((P : Subgroup K) ⊓ IVK.Ez z) (zpowers t ⊔ zpowers w) := by
    rw [disjoint_iff]
    exact le_bot_iff.mp (hinf ▸ inf_le_inf_right (zpowers t ⊔ zpowers w) inf_le_right)
  have hcard := card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hTN hdisj
  have hPeq : (P : Subgroup K) =
      ((P : Subgroup K) ⊓ IVK.Ez z) ⊔ (zpowers t ⊔ zpowers w) := hPdec.trans (sup_assoc _ _ _)
  rw [← hNcard, ← hcard, ← hPeq]

theorem jm_two_mul_card_Ez {q : ℕ} {z t : K} {E₁ E₂ : Subgroup K}
    (hz2 : orderOf z = 2) (hEz : IVK.Ez z = E₁ ⊔ E₂)
    (hE₂ : E₂ = E₁.map (MulAut.conj t).toMonoidHom)
    (hsl : HasSL2Model ↥E₁ (fun r => r = q)) (hinf : E₁ ⊓ E₂ = zpowers z)
    (hcom : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) :
    Nat.card ↥(IVK.Ez z) * 2 = (q * (q ^ 2 - 1)) ^ 2 := by
  have h1 := jm_card_sup_mul_card_inf E₁ E₂ hcom
  have hE₂card : Nat.card ↥E₂ = Nat.card ↥E₁ := by
    rw [hE₂]
    exact Subgroup.card_map_of_injective (MulAut.conj t).injective
  rw [hinf, Nat.card_zpowers, hz2, hE₂card, card_of_hasSL2Model hsl, ← hEz] at h1
  rw [h1]
  ring

theorem jm_mem_zpowers_of_mul_self {a x : K} (ha : a * a = 1) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a := by
  have h := mem_sup_pair_of_comm (a := a) (b := 1) (by rw [mul_one, one_mul]) ha (mul_one 1)
    (x := x) (Subgroup.mem_sup_left hx)
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr (by rw [h, mul_one])

theorem jm_card_zpowers_sup_eq_four {t w : K} (ht : orderOf t = 2) (hw : orderOf w = 2)
    (hcomm : Commute t w) (htw : t * w ≠ 1) : Nat.card ↥(zpowers t ⊔ zpowers w) = 4 := by
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have hw1 : w * w = 1 := by rw [← pow_two, ← hw]; exact pow_orderOf_eq_one w
  have hcomm' : ∀ a ∈ zpowers t, ∀ b ∈ zpowers w, a * b = b * a := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact (hcomm.zpow_zpow m n).eq
  have hdisj : zpowers t ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases jm_mem_zpowers_of_mul_self ht1 hx.1 with h | h
    · rw [h]; exact one_mem _
    · rcases jm_mem_zpowers_of_mul_self hw1 hx.2 with h' | h'
      · rw [h']; exact one_mem _
      · exact absurd (by rw [← h, ← h', h]; exact ht1) htw
  have h := jm_card_sup_mul_card_inf (zpowers t) (zpowers w) hcomm'
  rw [hdisj, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, ht, hw] at h
  omega

end SylowPart

theorem jm_card_classes {K : Type} [Group K] [Finite K] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : IVK.IsSp4L4U4 K q) (P : Sylow 2 K) {z : K} (hzP : z ∈ (P : Subgroup K))
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) :
    ∃ (y : K) (b : ℕ), orderOf y = 2 ∧ ¬ IsConj z y ∧
      (∀ u : K, orderOf u = 2 → IsConj z u ∨ IsConj y u) ∧
      (b = 2 ∨ b = 4) ∧ (b = 2 ↔ IVK.IsPSp4 K q) ∧
      Nat.card ↥(P : Subgroup K) = 2 ^ nuQ q * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, w, E₁, E₂, htP, hwP, ht2, hw12, hcomm, hPdec, hinf, -, hEz, hE₂, hsl, hE₁E₂,
    hcom, -, hwiff, hcls, hnc, -, -, hwne, -⟩ :=
    CFSG.GH74.GLS.Stage2.Final.ivk_4_10 K q hq h5 hK P z hzP hz2 hzc
  have hcard := jm_card_sylow_of_decomp P hzc htP hwP hPdec hinf
  have hE2 := jm_two_mul_card_Ez hz2 hEz hE₂ hsl hE₁E₂ hcom
  have hnu : (Nat.card ↥(IVK.Ez z)).factorization 2 = nuQ q := by
    unfold nuQ
    rw [← hE2, Nat.mul_div_cancel _ (by norm_num)]
  rw [hnu] at hcard
  have hz1 : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  have ht1 : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have htzc : t * z = z * t := hzc t htP
  have hzE₁₂ : z ∈ E₁ ⊓ E₂ := by rw [hE₁E₂]; exact Subgroup.mem_zpowers z
  have hzE : z ∈ IVK.Ez z := by rw [hEz]; exact Subgroup.mem_sup_left hzE₁₂.1
  have htz_ne : t * z ≠ 1 := by
    intro h
    have htz : t = z := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_eq_of_mul_eq_one_right hz1
    have hzt : z ∈ zpowers t := by rw [← htz]; exact Subgroup.mem_zpowers t
    have hmem : z ∈ IVK.Ez z ⊓ (zpowers t ⊔ zpowers w) := ⟨hzE, Subgroup.mem_sup_left hzt⟩
    rw [hinf] at hmem
    have hz_one : z = 1 := Subgroup.mem_bot.mp hmem
    rw [hz_one, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hty2 : orderOf (t * z) = 2 := by
    refine orderOf_eq_prime ?_ htz_ne
    rw [pow_two]
    calc t * z * (t * z) = t * (z * t) * z := by simp only [mul_assoc]
      _ = t * (t * z) * z := by rw [htzc]
      _ = (t * t) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [ht1, hz1, mul_one]
  have hb : (Nat.card ↥(zpowers t ⊔ zpowers w) = 2 ∨ Nat.card ↥(zpowers t ⊔ zpowers w) = 4) ∧
      (Nat.card ↥(zpowers t ⊔ zpowers w) = 2 ↔ IVK.IsPSp4 K q) := by
    by_cases hw1 : w = 1
    · subst hw1
      have h2 : Nat.card ↥(zpowers t ⊔ zpowers (1 : K)) = 2 := by
        rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq, Nat.card_zpowers, ht2]
      exact ⟨Or.inl h2, ⟨fun _ => hwiff.mp rfl, fun _ => h2⟩⟩
    · have hw2 : orderOf w = 2 := hw12.resolve_left hw1
      obtain ⟨hconjtw, -⟩ := hwne hw1
      have htw : t * w ≠ 1 := by
        intro h
        rw [h] at hconjtw
        have hz_one : z = 1 := isConj_one_right.mp hconjtw.symm
        rw [hz_one, orderOf_one] at hz2
        exact absurd hz2 (by norm_num)
      have h4 := jm_card_zpowers_sup_eq_four ht2 hw2 hcomm htw
      exact ⟨Or.inr h4, ⟨fun h => absurd (h4.symm.trans h) (by norm_num),
        fun h => absurd (hwiff.mpr h) hw1⟩⟩
  exact ⟨t * z, Nat.card ↥(zpowers t ⊔ zpowers w), hty2, hnc, hcls, hb.1, hb.2, hcard⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
