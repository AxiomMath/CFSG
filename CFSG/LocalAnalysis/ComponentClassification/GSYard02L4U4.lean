module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02QuatTensor
import CFSG.GH74.GLS.Stage1.Main.BrPairModel
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ord
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Model
public import CFSG.GH74.GLS.Stage2.Final.ModelLUElts
import CFSG.GH74.GLS.Stage2.Final.ModelIVKFam
import CFSG.GH74.GLS.Stage2.Final.ModelPGLLin
import CFSG.GH74.GLS.Stage2.Final.ModelPGLUni

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

namespace L4U4

section Counting

variable {K : Type} [Group K] [Finite K]

private theorem card_sup_mul_card_inf_of_comm (L R : Subgroup K)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup K) * Nat.card (L ⊓ R : Subgroup K) = Nat.card L * Nat.card R := by
  let μ : L × R →* K := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : K) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup K) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : K), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : K)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

private theorem card_inf_eq_of_normal {A B N : Subgroup K} (hNB : N ≤ B)
    (hn : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N)
    (hAB : Nat.card ↥(A ⊓ B) = 2 ^ (Nat.card ↥B).factorization 2) :
    Nat.card ↥(A ⊓ N) = 2 ^ (Nat.card ↥N).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card ↥((A ⊓ B).subgroupOf B) = 2 ^ (Nat.card ↥B).factorization 2 := by
    rw [← hAB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  let S : Sylow 2 ↥B := Sylow.ofCard _ hS
  haveI : (N.subgroupOf B).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hn g g.2 x hx⟩
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal S (N := N.subgroupOf B)
  have hcard := Sylow.card_eq_multiplicity Q
  have h1 : Nat.card ↥(Q : Subgroup ↥(N.subgroupOf B)) = Nat.card ↥(A ⊓ N) := by
    rw [hQ]
    refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans ?_
    have hSc : (S : Subgroup ↥B) = (A ⊓ B).subgroupOf B := rfl
    have : (S : Subgroup ↥B) ⊓ N.subgroupOf B = (A ⊓ N).subgroupOf B := by
      rw [hSc]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, x.2⟩, h3⟩⟩
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hNB)).toEquiv
  have h2 : Nat.card ↥(N.subgroupOf B) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
  rw [← h1, hcard, h2]

private theorem card_sylow_inf_of_le (P : Sylow 2 K) {C : Subgroup K} (hPC : (P : Subgroup K) ≤ C) :
    Nat.card ↥((P : Subgroup K) ⊓ C) = 2 ^ (Nat.card ↥C).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [inf_of_le_left hPC]
  have h := Sylow.card_eq_multiplicity (P.subtype hPC)
  rw [← h]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).symm

private theorem quatIn_of_sylow_sl2 {q : ℕ} (hq : Odd q) {E₁ Q₁ : Subgroup K} {z : K}
    (hsl2 : HasSL2Model ↥E₁ (fun r => r = q)) (hQE : Q₁ ≤ E₁)
    (hQcard : Nat.card ↥Q₁ = 2 ^ (Nat.card ↥E₁).factorization 2) (hzQ : z ∈ Q₁)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : QuatIn z Q₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, iF, fF, hF, ⟨e⟩⟩ := hsl2
  have hFodd : Odd (Nat.card F) := by rw [show Nat.card F = q from hF]; exact hq
  let e' : ↥E₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hS : Nat.card ↥(Q₁.subgroupOf E₁) = 2 ^ (Nat.card ↥E₁).factorization 2 := by
    rw [← hQcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv
  let S₁ : Sylow 2 ↥E₁ := Sylow.ofCard _ hS
  have hS₁ : (S₁ : Subgroup ↥E₁) = Q₁.subgroupOf E₁ := rfl
  let P₂ : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) :=
    S₁.mapSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨n, hn3, ⟨eq⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hFodd P₂
  have hP₂ : (P₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (Q₁.subgroupOf E₁).map e'.toMonoidHom := by
    rw [← hS₁]
    exact Sylow.coe_mapSurjective _ _
  let eQ : ↥Q₁ ≃* ↥(P₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    ((Subgroup.subgroupOfEquivOfLe hQE).symm.trans
      (Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective)).trans
        (MulEquiv.subgroupCongr hP₂.symm)
  have hz2' : (⟨z, hzQ⟩ : ↥Q₁) * ⟨z, hzQ⟩ = 1 := Subtype.ext hz2
  have hz1' : (⟨z, hzQ⟩ : ↥Q₁) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hm : ∃ h, 2 ^ (n - 2) = 2 * h :=
    ⟨2 ^ (n - 3), by rw [show n - 2 = (n - 3) + 1 by omega, pow_succ, mul_comm]⟩
  exact QuatIn.of_quatData hzQ
    (QuatData.of_equiv_quaternion hm (pow_pos (by norm_num) _) (eQ.trans eq) hz2' hz1')

end Counting

section Pair

variable {K : Type} [Group K] [Finite K]

theorem conj_mem_E₁ {E₁ E₂ : Subgroup K} (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) {b : K}
    (hb : b ∈ E₁ ⊔ E₂) {n : K} (hn : n ∈ E₁) : b * n * b⁻¹ ∈ E₁ := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm hb
  have h1 : a₂ * n = n * a₂ := (hcomm n hn a₂ ha₂).symm
  have : a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₁ * n * a₁⁻¹ := by
    calc a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₁ * (a₂ * n) * a₂⁻¹ * a₁⁻¹ := by group
      _ = a₁ * (n * a₂) * a₂⁻¹ * a₁⁻¹ := by rw [h1]
      _ = a₁ * n * a₁⁻¹ := by group
  rw [this]
  exact E₁.mul_mem (E₁.mul_mem ha₁ hn) (E₁.inv_mem ha₁)

theorem conj_mem_E₂ {E₁ E₂ : Subgroup K} (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) {b : K}
    (hb : b ∈ E₁ ⊔ E₂) {n : K} (hn : n ∈ E₂) : b * n * b⁻¹ ∈ E₂ := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm hb
  have hc : a₂ * n * a₂⁻¹ ∈ E₂ := E₂.mul_mem (E₂.mul_mem ha₂ hn) (E₂.inv_mem ha₂)
  have h2 : a₁ * (a₂ * n * a₂⁻¹) = (a₂ * n * a₂⁻¹) * a₁ := hcomm a₁ ha₁ _ hc
  have : a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₂ * n * a₂⁻¹ := by
    calc a₁ * a₂ * n * (a₁ * a₂)⁻¹ = (a₁ * (a₂ * n * a₂⁻¹)) * a₁⁻¹ := by group
      _ = ((a₂ * n * a₂⁻¹) * a₁) * a₁⁻¹ := by rw [h2]
      _ = a₂ * n * a₂⁻¹ := by group
  rw [this]
  exact hc

theorem quatPair_of_dat {q : ℕ} (hq : Odd q) (P : Sylow 2 K) {z t : K} {E₁ E₂ : Subgroup K}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x)
    (hzP : z ∈ (P : Subgroup K)) (htP : t ∈ (P : Subgroup K))
    (hEC : E₁ ⊔ E₂ ≤ centralizer ({z} : Set K))
    (hEN : ∀ c ∈ centralizer ({z} : Set K), ∀ n ∈ E₁ ⊔ E₂, c * n * c⁻¹ ∈ E₁ ⊔ E₂)
    (hE₂ : E₂ = E₁.map (MulAut.conj t).toMonoidHom) (hsl2 : HasSL2Model ↥E₁ (fun r => r = q))
    (hint : E₁ ⊓ E₂ = zpowers z) (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) :
    QuatPair z (P : Subgroup K) ((P : Subgroup K) ⊓ E₁) ((P : Subgroup K) ⊓ E₂) ∧
      ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂) = (P : Subgroup K) ⊓ (E₁ ⊔ E₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : z ∈ E₁ ∧ z ∈ E₂ := by
    have : z ∈ E₁ ⊓ E₂ := by rw [hint]; exact mem_zpowers z
    exact this
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hPC : (P : Subgroup K) ≤ centralizer ({z} : Set K) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hzc x hx)
  have hcardE : Nat.card ↥((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) =
      2 ^ (Nat.card ↥(E₁ ⊔ E₂)).factorization 2 :=
    card_inf_eq_of_normal hEC hEN (card_sylow_inf_of_le P hPC)
  have hcard₁ : Nat.card ↥((P : Subgroup K) ⊓ E₁) = 2 ^ (Nat.card ↥E₁).factorization 2 :=
    card_inf_eq_of_normal le_sup_left (fun b hb n hn => conj_mem_E₁ hcomm hb hn) hcardE
  have hcard₂ : Nat.card ↥((P : Subgroup K) ⊓ E₂) = 2 ^ (Nat.card ↥E₂).factorization 2 :=
    card_inf_eq_of_normal le_sup_right (fun b hb n hn => conj_mem_E₂ hcomm hb hn) hcardE
  have hQ₁₂ : ((P : Subgroup K) ⊓ E₁) ⊓ ((P : Subgroup K) ⊓ E₂) = zpowers z := by
    apply le_antisymm
    · intro g hg
      have : g ∈ E₁ ⊓ E₂ := ⟨hg.1.2, hg.2.2⟩
      rw [hint] at this
      exact this
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨hzP, hz.1⟩, ⟨hzP, hz.2⟩⟩
  have hcardQ₁₂ : Nat.card ↥(((P : Subgroup K) ⊓ E₁) ⊓ ((P : Subgroup K) ⊓ E₂)) = 2 := by
    rw [hQ₁₂, Nat.card_zpowers, hzord]
  have hE_card : Nat.card ↥(E₁ ⊔ E₂) * 2 = Nat.card ↥E₁ * Nat.card ↥E₂ := by
    have := card_sup_mul_card_inf_of_comm E₁ E₂ hcomm
    rw [hint, Nat.card_zpowers, hzord] at this
    exact this
  have hQ_card : Nat.card ↥(((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂)) * 2 =
      Nat.card ↥((P : Subgroup K) ⊓ E₁) * Nat.card ↥((P : Subgroup K) ⊓ E₂) := by
    have := card_sup_mul_card_inf_of_comm ((P : Subgroup K) ⊓ E₁) ((P : Subgroup K) ⊓ E₂)
      (fun x hx y hy => hcomm x hx.2 y hy.2)
    rw [hcardQ₁₂] at this
    exact this
  have hfac : (Nat.card ↥(E₁ ⊔ E₂)).factorization 2 + 1 =
      (Nat.card ↥E₁).factorization 2 + (Nat.card ↥E₂).factorization 2 := by
    have h : (Nat.card ↥(E₁ ⊔ E₂) * 2).factorization 2 =
        (Nat.card ↥E₁ * Nat.card ↥E₂).factorization 2 := by rw [hE_card]
    rw [Nat.factorization_mul Nat.card_pos.ne' (by norm_num),
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h
    simpa [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] using h
  have hQcard : Nat.card ↥(((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂)) =
      Nat.card ↥((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) := by
    have h2 : Nat.card ↥(((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂)) * 2 =
        2 ^ ((Nat.card ↥(E₁ ⊔ E₂)).factorization 2) * 2 := by
      rw [hQ_card, hcard₁, hcard₂, ← pow_add, ← hfac, pow_succ]
    rw [hcardE]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hRle : ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂) ≤ (P : Subgroup K) ⊓ (E₁ ⊔ E₂) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have hR : ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂) = (P : Subgroup K) ⊓ (E₁ ⊔ E₂) :=
    Subgroup.eq_of_le_of_card_ge hRle (by rw [hQcard])
  have hq₁ : QuatIn z ((P : Subgroup K) ⊓ E₁) :=
    quatIn_of_sylow_sl2 hq hsl2 inf_le_right hcard₁ ⟨hzP, hz.1⟩ hz2 hz1
  have hfz : (MulAut.conj t) z = z := by
    rw [MulAut.conj_apply]
    have := hzc t htP
    calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [this]
      _ = z := by group
  have hQ₂ : (P : Subgroup K) ⊓ E₂ = ((P : Subgroup K) ⊓ E₁).map (MulAut.conj t).toMonoidHom := by
    ext x
    constructor
    · rintro ⟨hxP, hxE⟩
      rw [hE₂] at hxE
      obtain ⟨y, hy, hyx⟩ := hxE
      have hyx' : t * y * t⁻¹ = x := hyx
      refine ⟨y, ⟨?_, hy⟩, hyx⟩
      have : y = t⁻¹ * x * t := by rw [← hyx']; group
      rw [this]
      exact (P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem ((P : Subgroup K).inv_mem htP) hxP)
        htP
    · rintro ⟨y, ⟨hyP, hy⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem htP hyP)
          ((P : Subgroup K).inv_mem htP)
      · rw [hE₂]
        exact ⟨y, hy, rfl⟩
  have hq₂ : QuatIn z ((P : Subgroup K) ⊓ E₂) := by
    rw [hQ₂]
    exact hq₁.map_mulEquiv (MulAut.conj t) hfz
  refine ⟨?_, hR⟩
  exact
    { zc := hzc
      le₁ := inf_le_left
      le₂ := inf_le_left
      comm := fun a ha b hb => hcomm a ha.2 b hb.2
      inter := fun g hg₁ hg₂ => by
        have : g ∈ E₁ ⊓ E₂ := ⟨hg₁.2, hg₂.2⟩
        rw [hint] at this
        by_cases hg1 : g = 1
        · exact Or.inl hg1
        · exact Or.inr (FooteLit.eq_of_mem_zpowers_of_sq (by rw [sq]; exact hz2) hg1 this)
      q₁ := hq₁
      q₂ := hq₂ }

end Pair

section Involutions

variable {K : Type} [Group K]

theorem exists_inv_pair {Q : Subgroup K} {z f : K} (hQ : QuatIn z Q)
    (h2grp : ∀ g ∈ Q, ∃ k : ℕ, g ^ 2 ^ k = 1) (hzcQ : ∀ g ∈ Q, g * z = z * g)
    (hf2 : f * f = 1) (hfQ : ∀ g ∈ Q, f * g * f⁻¹ ∈ Q)
    (hnf : ∀ r ∈ Q, r * r = z → f * r * f⁻¹ ≠ r) :
    ∃ r ∈ Q, r * r = z ∧ f * r * f⁻¹ = r * z := by
  have hz2 : z * z = 1 := hQ.sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have key : ∀ k : ℕ, ∀ g ∈ Q, g ^ 2 ^ k = 1 → g ≠ 1 → g ≠ z → f * g * f⁻¹ = g⁻¹ →
      ∃ r ∈ Q, r * r = z ∧ f * r * f⁻¹ = r⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro g _ h1 hne1 _ _
      exact absurd (by simpa using h1) hne1
    | succ k ih =>
      intro g hg hgk hne1 hnez hfg
      by_cases hgz : g * g = z
      · exact ⟨g, hg, hgz, hfg⟩
      · have hg1 : g * g ≠ 1 := fun h => (hQ.unique g hg h).elim hne1 hnez
        refine ih (g * g) (Q.mul_mem hg hg) ?_ hg1 hgz ?_
        · have e : (g * g) ^ 2 ^ k = g ^ 2 ^ (k + 1) := by
            rw [← sq, ← pow_mul, pow_succ' 2 k]
          rw [e]
          exact hgk
        · calc f * (g * g) * f⁻¹ = (f * g * f⁻¹) * (f * g * f⁻¹) := by group
            _ = g⁻¹ * g⁻¹ := by rw [hfg]
            _ = (g * g)⁻¹ := by group
  by_cases H : ∀ u ∈ Q, u * (f * u * f⁻¹)⁻¹ = 1 ∨ u * (f * u * f⁻¹)⁻¹ = z
  · obtain ⟨a, ha, haz⟩ := hQ.exists_sq
    refine ⟨a, ha, haz, ?_⟩
    rcases H a ha with h | h
    · exfalso
      apply hnf a ha haz
      exact (mul_inv_eq_one.1 h).symm
    · have h' : a = z * (f * a * f⁻¹) := by
        calc a = (a * (f * a * f⁻¹)⁻¹) * (f * a * f⁻¹) := by group
          _ = z * (f * a * f⁻¹) := by rw [h]
      calc f * a * f⁻¹ = z⁻¹ * (z * (f * a * f⁻¹)) := by group
        _ = z⁻¹ * a := by rw [← h']
        _ = z * a := by rw [hzi]
        _ = a * z := (hzcQ a ha).symm
  · push_neg at H
    obtain ⟨u, hu, hne1, hnez⟩ := H
    have hfu : f * u * f⁻¹ ∈ Q := hfQ u hu
    have hg : u * (f * u * f⁻¹)⁻¹ ∈ Q := Q.mul_mem hu (Q.inv_mem hfu)
    have hff : f⁻¹ * f⁻¹ = 1 := by rw [← mul_inv_rev, hf2, inv_one]
    have hfg : f * (u * (f * u * f⁻¹)⁻¹) * f⁻¹ = (u * (f * u * f⁻¹)⁻¹)⁻¹ := by
      calc f * (u * (f * u * f⁻¹)⁻¹) * f⁻¹
          = (f * u * f⁻¹) * (f * f * u⁻¹ * (f⁻¹ * f⁻¹)) := by group
        _ = (f * u * f⁻¹) * u⁻¹ := by rw [hf2, hff]; group
        _ = (u * (f * u * f⁻¹)⁻¹)⁻¹ := by group
    obtain ⟨k, hk⟩ := h2grp _ hg
    obtain ⟨r, hr, hrr, hfr⟩ := key k _ hg hk hne1 hnez hfg
    refine ⟨r, hr, hrr, ?_⟩
    rw [hfr]
    exact inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hrr, hz2])

theorem exists_inv2_comm_of_swap {z : K} {P Q₁ Q₂ : Subgroup K} (h : QuatPair z P Q₁ Q₂) {x : K}
    (hxi : Inv2 z x) (hxQ : ∀ a ∈ Q₁, x * a * x⁻¹ ∈ Q₂) :
    ∃ y ∈ Q₁ ⊔ Q₂, Inv2 z y ∧ x * y = y * x := by
  obtain ⟨a₁, ha₁, ha₁z⟩ := h.q₁.exists_sq
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxi.sq
  obtain ⟨a₂, ha₂def⟩ : ∃ a₂, a₂ = x * a₁ * x⁻¹ := ⟨_, rfl⟩
  have ha₂ : a₂ ∈ Q₂ := by rw [ha₂def]; exact hxQ a₁ ha₁
  have hxa₁ : x * a₁ = a₂ * x := by rw [ha₂def]; group
  have hxa₂ : x * a₂ = a₁ * x := by
    calc x * a₂ = x * (x * a₁ * x⁻¹) := by rw [ha₂def]
      _ = (x * x) * a₁ * x⁻¹ := by group
      _ = a₁ * x⁻¹ := by rw [hxi.sq, one_mul]
      _ = a₁ * x := by rw [hxinv]
  have ha₂z : a₂ * a₂ = z := by
    calc a₂ * a₂ = x * (a₁ * a₁) * x⁻¹ := by rw [ha₂def]; group
      _ = x * z * x⁻¹ := by rw [ha₁z]
      _ = z := by rw [hxi.comm]; group
  refine ⟨a₁ * a₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂),
    h.inv2_mul ha₁ ha₂ ha₁z ha₂z, ?_⟩
  calc x * (a₁ * a₂) = (x * a₁) * a₂ := (mul_assoc _ _ _).symm
    _ = a₂ * x * a₂ := by rw [hxa₁]
    _ = a₂ * (x * a₂) := mul_assoc _ _ _
    _ = a₂ * (a₁ * x) := by rw [hxa₂]
    _ = (a₂ * a₁) * x := (mul_assoc _ _ _).symm
    _ = (a₁ * a₂) * x := by rw [(h.comm a₁ ha₁ a₂ ha₂).symm]

theorem exists_inv2_comm_of_inv {z : K} {P Q₁ Q₂ : Subgroup K} (h : QuatPair z P Q₁ Q₂) {f : K}
    {r₁ r₂ : K} (hr₁ : r₁ ∈ Q₁) (hr₂ : r₂ ∈ Q₂) (hr₁z : r₁ * r₁ = z) (hr₂z : r₂ * r₂ = z)
    (hf₁ : f * r₁ * f⁻¹ = r₁ * z) (hf₂ : f * r₂ * f⁻¹ = r₂ * z) :
    ∃ y ∈ Q₁ ⊔ Q₂, Inv2 z y ∧ f * y = y * f := by
  have hz2 : z * z = 1 := h.q₁.sq
  have zr₂ : z * r₂ = r₂ * z := (h.zc r₂ (h.le₂ hr₂)).symm
  have hfy : f * (r₁ * r₂) * f⁻¹ = r₁ * r₂ := by
    calc f * (r₁ * r₂) * f⁻¹ = (f * r₁ * f⁻¹) * (f * r₂ * f⁻¹) := by group
      _ = (r₁ * z) * (r₂ * z) := by rw [hf₁, hf₂]
      _ = r₁ * (z * r₂) * z := by group
      _ = r₁ * (r₂ * z) * z := by rw [zr₂]
      _ = r₁ * r₂ * (z * z) := by group
      _ = r₁ * r₂ := by rw [hz2, mul_one]
  refine ⟨r₁ * r₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left hr₁) (Subgroup.mem_sup_right hr₂),
    h.inv2_mul hr₁ hr₂ hr₁z hr₂z, ?_⟩
  calc f * (r₁ * r₂) = (f * (r₁ * r₂) * f⁻¹) * f := by group
    _ = (r₁ * r₂) * f := by rw [hfy]

end Involutions

section Joined

variable {K : Type} [Group K] [Finite K]

theorem reflTransGen_commFourAdj_of_dat410w {q : ℕ} (hq : Odd q) (P : Sylow 2 K) {z t w : K}
    {E₁ E₂ : Subgroup K} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) (hzP : z ∈ (P : Subgroup K))
    (htP : t ∈ (P : Subgroup K)) (ht2 : t * t = 1) (hwP : w ∈ (P : Subgroup K)) (hw2 : w * w = 1)
    (htw : t * w = w * t)
    (hPE : (P : Subgroup K) = ((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) ⊔ zpowers t ⊔ zpowers w)
    (hEC : E₁ ⊔ E₂ ≤ centralizer ({z} : Set K))
    (hEN : ∀ c ∈ centralizer ({z} : Set K), ∀ n ∈ E₁ ⊔ E₂, c * n * c⁻¹ ∈ E₁ ⊔ E₂)
    (hE₂ : E₂ = E₁.map (MulAut.conj t).toMonoidHom) (hsl2 : HasSL2Model ↥E₁ (fun r => r = q))
    (hint : E₁ ⊓ E₂ = zpowers z) (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a)
    (hnorm : normalizer (E₁ : Set K) ⊓ (P : Subgroup K) =
      ((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) ⊔ zpowers w)
    (hsign : ∀ k ∈ E₁ ⊔ E₂, (k * w) * (k * w) = 1 → ∀ r ∈ E₁, r * r = z →
      (k * w) * r ≠ r * (k * w))
    {F G : Subgroup K} (hF : IsKleinFour F) (hFP : F ≤ P) (hG : IsKleinFour G) (hGP : G ≤ P) :
    Relation.ReflTransGen (Sig.CommFourAdj K) F G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hpair, hR⟩ := quatPair_of_dat hq P hz2 hz1 hzc hzP htP hEC hEN hE₂ hsl2 hint hcomm
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hPC : ∀ g ∈ (P : Subgroup K), g ∈ centralizer ({z} : Set K) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hzc g hg)
  have hP2 : ∀ g ∈ (P : Subgroup K), ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := (P.isPGroup' : IsPGroup 2 (P : Subgroup K)) ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨φ, hφx, hφE₁, hφmap⟩ : ∃ φ : MulAut K, (∀ x, φ x = t * x * t⁻¹) ∧
      (∀ x ∈ E₁, φ x ∈ E₂) ∧ (∀ x ∈ E₂, ∃ a ∈ E₁, φ a = x) := by
    refine ⟨MulAut.conj t, fun x => MulAut.conj_apply t x, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hE₂]
      exact ⟨x, hx, rfl⟩
    · rw [hE₂] at hx
      obtain ⟨a, ha, hax⟩ := hx
      exact ⟨a, ha, hax⟩
  have hφφ : ∀ x, φ (φ x) = x := fun x => by
    rw [hφx, hφx]
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht2]; group
  have hφz : φ z = z := by
    rw [hφx]
    calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [hzc t htP]
      _ = z := by group
  have hφw : φ w = w := by
    rw [hφx, htw]
    group
  have hφP : ∀ x ∈ (P : Subgroup K), φ x ∈ (P : Subgroup K) := fun x hx => by
    rw [hφx]
    exact (P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem htP hx) ((P : Subgroup K).inv_mem htP)
  have hφE : ∀ x ∈ E₁ ⊔ E₂, φ x ∈ E₁ ⊔ E₂ := fun x hx => by
    rw [hφx]
    exact hEN t (hPC t htP) x hx
  have hPE_conj : ∀ g ∈ (P : Subgroup K), ∀ r ∈ (P : Subgroup K) ⊓ (E₁ ⊔ E₂),
      g * r * g⁻¹ ∈ (P : Subgroup K) ⊓ (E₁ ⊔ E₂) := fun g hg r hr =>
    ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem hg hr.1) ((P : Subgroup K).inv_mem hg),
      hEN g (hPC g hg) r hr.2⟩
  have hPnorm : ∀ g ∈ (P : Subgroup K),
      g ∈ normalizer (((P : Subgroup K) ⊓ (E₁ ⊔ E₂) : Subgroup K) : Set K) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro r
    refine ⟨hPE_conj g hg r, fun hr => ?_⟩
    have h1 := hPE_conj g⁻¹ ((P : Subgroup K).inv_mem hg) _ hr
    have e : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
    rwa [e] at h1
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup K, R = ((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) ⊔ zpowers w :=
    ⟨_, rfl⟩
  have hwR : w ∈ R := by rw [hRdef]; exact Subgroup.mem_sup_right (mem_zpowers w)
  have hRN : ∀ r ∈ R, r ∈ normalizer (E₁ : Set K) ∧ r ∈ (P : Subgroup K) := by
    intro r hr
    have : r ∈ normalizer (E₁ : Set K) ⊓ (P : Subgroup K) := by rw [hnorm, ← hRdef]; exact hr
    exact ⟨this.1, this.2⟩
  have htR : t ∈ normalizer (R : Set K) := by
    have h1 : ((P : Subgroup K) ⊓ (E₁ ⊔ E₂)).map (MulAut.conj t).toMonoidHom =
        (P : Subgroup K) ⊓ (E₁ ⊔ E₂) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hPnorm t htP)
    have h2 : (zpowers w).map (MulAut.conj t).toMonoidHom = zpowers w := by
      rw [MonoidHom.map_zpowers]
      congr 1
      show t * w * t⁻¹ = w
      rw [htw]
      group
    have key : R.map (MulAut.conj t).toMonoidHom = R := by
      rw [hRdef, Subgroup.map_sup, h1, h2]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 key
  have hPtR : (P : Subgroup K) = zpowers t ⊔ R := by
    calc (P : Subgroup K) = ((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) ⊔ zpowers t ⊔ zpowers w := hPE
      _ = ((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) ⊔ zpowers w ⊔ zpowers t := sup_right_comm _ _ _
      _ = zpowers t ⊔ (((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) ⊔ zpowers w) := sup_comm _ _
      _ = zpowers t ⊔ R := by rw [hRdef]
  have hdecomp : ∀ f ∈ (P : Subgroup K), ∃ r ∈ R, f = r ∨ f = t * r := by
    intro f hf
    rw [hPtR, ← SetLike.mem_coe,
      coe_mul_of_left_le_normalizer_right (zpowers t) R (Subgroup.zpowers_le.mpr htR)] at hf
    obtain ⟨a, ha, r, hr, rfl⟩ := hf
    by_cases ha1 : a = 1
    · exact ⟨r, hr, Or.inl (by simp [ha1])⟩
    · have hat : a = t := FooteLit.eq_of_mem_zpowers_of_sq (by rw [sq]; exact ht2) ha1 ha
      exact ⟨r, hr, Or.inr (by simp [hat])⟩
  have hRdecomp : ∀ r ∈ R, r ∈ E₁ ⊔ E₂ ∨ ∃ k ∈ E₁ ⊔ E₂, r = k * w := by
    intro r hr
    rw [hRdef, sup_comm ((P : Subgroup K) ⊓ (E₁ ⊔ E₂)) (zpowers w), ← SetLike.mem_coe,
      coe_mul_of_left_le_normalizer_right (zpowers w) ((P : Subgroup K) ⊓ (E₁ ⊔ E₂))
        (Subgroup.zpowers_le.mpr (hPnorm w hwP))] at hr
    obtain ⟨a, ha, e, he, rfl⟩ := hr
    by_cases ha1 : a = 1
    · left
      simpa [ha1] using (Subgroup.mem_inf.1 he).2
    · right
      have haw : a = w := FooteLit.eq_of_mem_zpowers_of_sq (by rw [sq]; exact hw2) ha1 ha
      refine ⟨w * e * w⁻¹, hEN w (hPC w hwP) e (Subgroup.mem_inf.1 he).2, ?_⟩
      show a * e = w * e * w⁻¹ * w
      rw [haw]
      group
  have hwN₁ : w ∈ normalizer (E₁ : Set K) := (hRN w hwR).1
  have hwE₂ : ∀ g ∈ E₂, w * g * w⁻¹ ∈ E₂ := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := hφmap g hg
    have h1 : w * a * w⁻¹ ∈ E₁ := (mem_normalizer_iff.1 hwN₁ a).1 ha
    have e : w * φ a * w⁻¹ = φ (w * a * w⁻¹) := by
      rw [map_mul, map_mul, map_inv, hφw]
    rw [e]
    exact hφE₁ _ h1
  have hzcQ₁ : ∀ g ∈ (P : Subgroup K) ⊓ E₁, g * z = z * g := fun g hg => hzc g hg.1
  have hzcQ₂ : ∀ g ∈ (P : Subgroup K) ⊓ E₂, g * z = z * g := fun g hg => hzc g hg.1
  have hinv : ∀ f ∈ (P : Subgroup K), Inv2 z f →
      ∃ y ∈ ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂), Inv2 z y ∧ f * y = y * f := by
    intro f hfP hfi
    obtain ⟨r, hrR, hfr⟩ := hdecomp f hfP
    rcases hfr with hfr | hfr
    ·
      have hfR : f ∈ R := by rw [hfr]; exact hrR
      rcases hRdecomp f hfR with hfE | ⟨k, hk, hfk⟩
      ·
        have hfPE : f ∈ (P : Subgroup K) ⊓ (E₁ ⊔ E₂) := ⟨hfP, hfE⟩
        rw [← hR] at hfPE
        exact ⟨f, hfPE, hfi, rfl⟩
      ·
        have hf2 : f * f = 1 := hfi.sq
        have hfN₁ : f ∈ normalizer (E₁ : Set K) := (hRN f hfR).1
        have hkw2 : (k * w) * (k * w) = 1 := by rw [← hfk]; exact hf2
        have hfE₁ : ∀ g ∈ E₁, f * g * f⁻¹ ∈ E₁ := fun g hg => (mem_normalizer_iff.1 hfN₁ g).1 hg
        have hfE₂ : ∀ g ∈ E₂, f * g * f⁻¹ ∈ E₂ := by
          intro g hg
          have h1 := conj_mem_E₂ hcomm hk (hwE₂ g hg)
          have e : f * g * f⁻¹ = k * (w * g * w⁻¹) * k⁻¹ := by rw [hfk]; group
          rw [e]
          exact h1
        have hfQ₁ : ∀ g ∈ (P : Subgroup K) ⊓ E₁, f * g * f⁻¹ ∈ (P : Subgroup K) ⊓ E₁ := fun g hg =>
          ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem hfP hg.1)
            ((P : Subgroup K).inv_mem hfP), hfE₁ g hg.2⟩
        have hfQ₂ : ∀ g ∈ (P : Subgroup K) ⊓ E₂, f * g * f⁻¹ ∈ (P : Subgroup K) ⊓ E₂ := fun g hg =>
          ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem hfP hg.1)
            ((P : Subgroup K).inv_mem hfP), hfE₂ g hg.2⟩
        have hnf₁ : ∀ r' ∈ (P : Subgroup K) ⊓ E₁, r' * r' = z → f * r' * f⁻¹ ≠ r' := by
          intro r' hr' hr'z hcon
          apply hsign k hk hkw2 r' hr'.2 hr'z
          rw [← hfk]
          calc f * r' = (f * r' * f⁻¹) * f := by group
            _ = r' * f := by rw [hcon]
        have hnf₂ : ∀ r' ∈ (P : Subgroup K) ⊓ E₂, r' * r' = z → f * r' * f⁻¹ ≠ r' := by
          intro r' hr' hr'z hcon
          obtain ⟨a, ha, hat⟩ := hφmap r' hr'.2
          have hφr : φ r' = a := by rw [← hat, hφφ]
          have hφf : φ f = φ k * w := by rw [hfk, map_mul, hφw]
          have hkφ : φ k ∈ E₁ ⊔ E₂ := hφE k hk
          have hφf2 : (φ k * w) * (φ k * w) = 1 := by
            rw [← hφf, ← map_mul, hf2, map_one]
          have haa : a * a = z := by
            rw [← hφr, ← map_mul, hr'z, hφz]
          have hfa : (φ k * w) * a = a * (φ k * w) := by
            rw [← hφf]
            have h1 : φ (f * r' * f⁻¹) = φ r' := by rw [hcon]
            rw [map_mul, map_mul, map_inv, hφr] at h1
            calc φ f * a = (φ f * a * (φ f)⁻¹) * φ f := by group
              _ = a * φ f := by rw [h1]
          exact hsign (φ k) hkφ hφf2 a ha haa hfa
        obtain ⟨r₁, hr₁, hr₁sq, hfr₁⟩ :=
          exists_inv_pair hpair.q₁ (fun g hg => hP2 g hg.1) hzcQ₁ hf2 hfQ₁ hnf₁
        obtain ⟨r₂, hr₂, hr₂sq, hfr₂⟩ :=
          exists_inv_pair hpair.q₂ (fun g hg => hP2 g hg.1) hzcQ₂ hf2 hfQ₂ hnf₂
        exact exists_inv2_comm_of_inv hpair hr₁ hr₂ hr₁sq hr₂sq hfr₁ hfr₂
    ·
      refine exists_inv2_comm_of_swap hpair hfi fun g hg => ?_
      have hrN := hRN r hrR
      have h1 : r * g * r⁻¹ ∈ (P : Subgroup K) ⊓ E₁ :=
        ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem hrN.2 hg.1)
          ((P : Subgroup K).inv_mem hrN.2), (mem_normalizer_iff.1 hrN.1 g).1 hg.2⟩
      have e : f * g * f⁻¹ = φ (r * g * r⁻¹) := by
        rw [hfr, hφx]
        group
      rw [e]
      exact ⟨hφP _ h1.1, hφE₁ _ h1.2⟩
  obtain ⟨a₁, ha₁, ha₁z⟩ := hpair.q₁.exists_sq
  obtain ⟨a₂, ha₂, ha₂z⟩ := hpair.q₂.exists_sq
  have hx₀ : Inv2 z (a₁ * a₂) := hpair.inv2_mul ha₁ ha₂ ha₁z ha₂z
  have hx₀m : a₁ * a₂ ∈ ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂)
  have key : ∀ F' : Subgroup K, IsKleinFour F' → F' ≤ P →
      Relation.ReflTransGen (Sig.CommFourAdj K) F' (vz z (a₁ * a₂)) := by
    intro F' hF' hFP'
    obtain ⟨f, hfF, hfi, hadj⟩ :=
      commFourAdj_vz_of_le hpair.q₁.sq hpair.q₁.ne_one hpair.zc hF' hFP'
    refine Relation.ReflTransGen.head hadj ?_
    obtain ⟨y, hy, hyi, hfy⟩ := hinv f (hFP' hfF) hfi
    exact (Relation.ReflTransGen.single
      (commFourAdj_vz hpair.q₁.sq hpair.q₁.ne_one hfi hyi hfy)).trans
        (hpair.reflTransGen_vz hy hx₀m hyi hx₀)
  exact (key F hF hFP).trans (reflTransGen_commFourAdj_symm (key G hG hGP))

end Joined

section Matrix2

variable {F : Type} [Field F]

theorem mat2_sq (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two,
      Matrix.one_apply] <;> ring

theorem mat2_pol (A B : Matrix (Fin 2) (Fin 2) F) :
    A * B + B * A = A.trace • B + B.trace • A +
      ((A * B).trace - A.trace * B.trace) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.one_apply] <;> ring

theorem sign_matrix (h2 : (2 : F) ≠ 0) {a h : Matrix (Fin 2) (Fin 2) F}
    (ha2 : a * a = -1) (hadet : a.det = 1) (hhdet : h.det = -1)
    (hh : ∃ c : F, h * h = c • (1 : Matrix (Fin 2) (Fin 2) F)) (hc : h * a = a * h) :
    (∃ l : F, h = l • (1 : Matrix (Fin 2) (Fin 2) F) ∧ l * l = -1) ∨
      (∃ b : F, h = b • a ∧ b * b = -1) := by
  obtain ⟨c, hc2⟩ := hh
  have hta : a.trace = 0 := by
    have e1 := mat2_sq a
    rw [ha2, hadet, one_smul] at e1
    have e2 : a.trace • a = 0 := by
      calc a.trace • a = (a.trace • a - 1) + 1 := (sub_add_cancel _ _).symm
        _ = -1 + 1 := by rw [← e1]
        _ = 0 := neg_add_cancel _
    rcases smul_eq_zero.1 e2 with h0 | h0
    · exact h0
    · exfalso
      rw [h0, zero_mul] at ha2
      have h1 : (1 : Matrix (Fin 2) (Fin 2) F) = 0 := neg_eq_zero.1 ha2.symm
      exact absurd (congrFun (congrFun h1 0) 0) (by simp)
  by_cases hT : h.trace = 0
  · right
    have hpol := mat2_pol h a
    simp only [hT, hta, zero_smul, zero_add, add_zero, zero_mul, sub_zero] at hpol
    rw [← hc] at hpol
    have h2' : (2 : F) • (h * a) = (h * a).trace • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [two_smul F (h * a), hpol]
    have ha1 : h * a = ((2 : F)⁻¹ * (h * a).trace) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      calc h * a = (2 : F)⁻¹ • ((2 : F) • (h * a)) := by
            rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
        _ = (2 : F)⁻¹ • ((h * a).trace • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [h2']
        _ = ((2 : F)⁻¹ * (h * a).trace) • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [smul_smul]
    set κ : F := (2 : F)⁻¹ * (h * a).trace with hκ
    have hh2 : h = (-κ) • a := by
      calc h = h * (a * (-a)) := by rw [mul_neg, ha2, neg_neg, mul_one]
        _ = (h * a) * (-a) := by rw [Matrix.mul_assoc]
        _ = (κ • (1 : Matrix (Fin 2) (Fin 2) F)) * (-a) := by rw [ha1]
        _ = (-κ) • a := by simp [smul_mul_assoc, neg_smul]
    refine ⟨-κ, hh2, ?_⟩
    have hd := hhdet
    rw [hh2, Matrix.det_smul, hadet, Fintype.card_fin] at hd
    linear_combination hd
  · left
    have e3 := mat2_sq h
    rw [hc2, hhdet] at e3
    have hTh : h.trace • h = (c - 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      calc h.trace • h = (h.trace • h - (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) +
            (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := (sub_add_cancel _ _).symm
        _ = c • (1 : Matrix (Fin 2) (Fin 2) F) + (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
          rw [← e3]
        _ = (c - 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
          rw [← add_smul]
          congr 1
          ring
    have hh1 : h = (h.trace⁻¹ * (c - 1)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      calc h = h.trace⁻¹ • (h.trace • h) := by rw [smul_smul, inv_mul_cancel₀ hT, one_smul]
        _ = h.trace⁻¹ • ((c - 1) • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [hTh]
        _ = (h.trace⁻¹ * (c - 1)) • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [smul_smul]
    refine ⟨h.trace⁻¹ * (c - 1), hh1, ?_⟩
    have hd := hhdet
    rw [hh1, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at hd
    linear_combination hd

end Matrix2

section Model

open CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {F : Type} [Field F]

private theorem coe_sc2' (c : Fˣ) :
    ((sc2 c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  simp only [Matrix.GeneralLinearGroup.coe_scalar]
  rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

private theorem sign_GL (h2 : (2 : F) ≠ 0) {U : Subgroup (GL (Fin 2) F)}
    (hnoi : ∀ l : Fˣ, sc2 l ∈ U → l * l ≠ -1) {a g : GL (Fin 2) F} (haU : a ∈ U) (hgU : g ∈ U)
    (ha2 : a * a = -1) (hadet : (a : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hgdet : (g : Matrix (Fin 2) (Fin 2) F).det = -1) (hg2 : ∃ c : Fˣ, g * g = sc2 c)
    (hc : g * a = a * g) : False := by
  obtain ⟨c, hc2⟩ := hg2
  have hmat2 : ∃ c' : F, (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      c' • (1 : Matrix (Fin 2) (Fin 2) F) := by
    refine ⟨c, ?_⟩
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hc2
    simpa only [Units.val_mul, coe_sc2'] using this
  have ha2' : (a : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) ha2
    simpa only [Units.val_mul, Units.val_neg, Units.val_one] using this
  have hc' : (g : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) =
      (a : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hc
    simpa only [Units.val_mul] using this
  rcases sign_matrix h2 ha2' hadet hgdet hmat2 hc' with ⟨l, hl, hll⟩ | ⟨b, hb, hbb⟩
  ·
    have hl0 : l ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hll
      exact one_ne_zero (neg_eq_zero.1 hll.symm)
    have hg : g = sc2 (Units.mk0 l hl0) := by
      apply Units.ext
      rw [hl, coe_sc2']
      try rfl
    exact hnoi (Units.mk0 l hl0) (hg ▸ hgU) (Units.ext (by simpa using hll))
  ·
    have hb0 : b ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hbb
      exact one_ne_zero (neg_eq_zero.1 hbb.symm)
    have hg : g * a⁻¹ = sc2 (Units.mk0 b hb0) := by
      apply Units.ext
      rw [Units.val_mul, coe_sc2', hb]
      calc b • (a : Matrix (Fin 2) (Fin 2) F) * ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = b • ((a : Matrix (Fin 2) (Fin 2) F) *
              ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by rw [smul_mul_assoc]
        _ = b • (1 : Matrix (Fin 2) (Fin 2) F) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        _ = ((Units.mk0 b hb0 : Fˣ) : F) • (1 : Matrix (Fin 2) (Fin 2) F) := rfl
    exact hnoi (Units.mk0 b hb0) (hg ▸ U.mul_mem hgU (U.inv_mem haU))
      (Units.ext (by simpa using hbb))

private theorem model_sign [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hnoi : ∀ l : Fˣ, sc2 l ∈ M.U2 → l * l ≠ -1) (hd : dRefl F ∈ M.U2) {k : PG M}
    (hk : k ∈ K1 M ⊔ K2 M)
    (hkw : (k * dP M (dRefl F) hd) * (k * dP M (dRefl F) hd) = 1) {r : PG M} (hr : r ∈ K1 M)
    (hrr : r * r = yP M) : (k * dP M (dRefl F) hd) * r ≠ r * (k * dP M (dRefl F) hd) := by
  intro hcomm
  obtain ⟨a₁, a₂, hk'⟩ := (mem_E_iff M).1 hk
  obtain ⟨a', rfl⟩ := hr
  have hab : diagGL (a₁ : GL (Fin 2) F) (a₂ : GL (Fin 2) F) ∈ M.K4 := diagGL_mem_K4_of_H2 M a₁ a₂
  have ha₁U : (a₁ : GL (Fin 2) F) ∈ M.U2 := ((M.mem_H2 _).1 a₁.2).1
  have ha'U : (a' : GL (Fin 2) F) ∈ M.U2 := ((M.mem_H2 _).1 a'.2).1
  have hg₁U : (a₁ : GL (Fin 2) F) * dRefl F ∈ M.U2 := M.U2.mul_mem ha₁U hd
  have hg₂U : (a₂ : GL (Fin 2) F) * (dRefl F)⁻¹ ∈ M.U2 :=
    M.U2.mul_mem ((M.mem_H2 _).1 a₂.2).1 (M.U2.inv_mem hd)
  have hK : diagGL ((a₁ : GL (Fin 2) F) * dRefl F) ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) ∈ M.K4 := by
    have := M.K4.mul_mem hab (diag_inv_mem_K4 M hd)
    rwa [diagGL_mul] at this
  have hX : k * dP M (dRefl F) hd = mkP M ⟨diagGL ((a₁ : GL (Fin 2) F) * dRefl F)
      ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹), hK⟩ := by
    rw [hk', iota_mul_eq_mkP_diag M a₁ a₂ hab, dP, ← map_mul]
    congr 1
    apply Subtype.ext
    show diagGL (a₁ : GL (Fin 2) F) a₂ * diagGL (dRefl F) (dRefl F)⁻¹ = _
    rw [diagGL_mul]
  rw [hX] at hkw hcomm
  have hK2 : diagGL (((a₁ : GL (Fin 2) F) * dRefl F) * ((a₁ : GL (Fin 2) F) * dRefl F))
      (((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) * ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹)) ∈ M.K4 := by
    have := M.K4.mul_mem hK hK
    rwa [diagGL_mul] at this
  have hK1 : diagGL (1 : GL (Fin 2) F) 1 ∈ M.K4 := by rw [diagGL_one]; exact M.K4.one_mem
  have hsq : mkP M ⟨diagGL (((a₁ : GL (Fin 2) F) * dRefl F) * ((a₁ : GL (Fin 2) F) * dRefl F))
      (((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) * ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹)), hK2⟩ =
      mkP M ⟨diagGL 1 1, hK1⟩ := by
    have e1 : (⟨diagGL (((a₁ : GL (Fin 2) F) * dRefl F) * ((a₁ : GL (Fin 2) F) * dRefl F))
        (((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) * ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹)), hK2⟩ :
          ↥M.K4) = ⟨diagGL ((a₁ : GL (Fin 2) F) * dRefl F)
            ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹), hK⟩ *
              ⟨diagGL ((a₁ : GL (Fin 2) F) * dRefl F) ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹), hK⟩ :=
      Subtype.ext (diagGL_mul _ _ _ _).symm
    have e2 : (⟨diagGL 1 1, hK1⟩ : ↥M.K4) = 1 := Subtype.ext diagGL_one
    rw [e1, e2, map_mul, map_one]
    exact hkw
  obtain ⟨c, hc1, -⟩ := (mkP_diag_eq_iff hK2 hK1).1 hsq
  have hg1sq : ((a₁ : GL (Fin 2) F) * dRefl F) * ((a₁ : GL (Fin 2) F) * dRefl F) = sc2 c⁻¹ := by
    have h1 : sc2 c * (((a₁ : GL (Fin 2) F) * dRefl F) * ((a₁ : GL (Fin 2) F) * dRefl F)) = 1 :=
      hc1.symm
    rw [eq_inv_of_mul_eq_one_right h1, sc2_inv]
  have hL : diagGL (((a₁ : GL (Fin 2) F) * dRefl F) * (a' : GL (Fin 2) F))
      (((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) * 1) ∈ M.K4 := by
    have := M.K4.mul_mem hK (M.blkL_mem_K4 a'.2)
    rwa [blkL_apply, diagGL_mul] at this
  have hR : diagGL ((a' : GL (Fin 2) F) * ((a₁ : GL (Fin 2) F) * dRefl F))
      (1 * ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹)) ∈ M.K4 := by
    have := M.K4.mul_mem (M.blkL_mem_K4 a'.2) hK
    rwa [blkL_apply, diagGL_mul] at this
  have hLe : mkP M ⟨diagGL ((a₁ : GL (Fin 2) F) * dRefl F)
      ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹), hK⟩ * iota1 M a' =
      mkP M ⟨diagGL (((a₁ : GL (Fin 2) F) * dRefl F) * (a' : GL (Fin 2) F))
        (((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) * 1), hL⟩ := by
    rw [iota1_apply, ← map_mul]
    congr 1
    apply Subtype.ext
    show diagGL ((a₁ : GL (Fin 2) F) * dRefl F) ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) *
      blkL F (a' : GL (Fin 2) F) = _
    rw [blkL_apply, diagGL_mul]
  have hRe : iota1 M a' * mkP M ⟨diagGL ((a₁ : GL (Fin 2) F) * dRefl F)
      ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹), hK⟩ = mkP M ⟨diagGL ((a' : GL (Fin 2) F) *
        ((a₁ : GL (Fin 2) F) * dRefl F)) (1 * ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹)), hR⟩ := by
    rw [iota1_apply, ← map_mul]
    congr 1
    apply Subtype.ext
    show blkL F (a' : GL (Fin 2) F) * diagGL ((a₁ : GL (Fin 2) F) * dRefl F)
      ((a₂ : GL (Fin 2) F) * (dRefl F)⁻¹) = _
    rw [blkL_apply, diagGL_mul]
  have hcomm' := hLe.symm.trans (hcomm.trans hRe)
  obtain ⟨c', hc1', hc2'⟩ := (mkP_diag_eq_iff hL hR).1 hcomm'
  have hsc : sc2 c' = 1 := by
    rw [one_mul, mul_one] at hc2'
    exact (mul_right_cancel (b := (a₂ : GL (Fin 2) F) * (dRefl F)⁻¹)
      (by rw [one_mul]; exact hc2'.symm))
  rw [hsc, one_mul] at hc1'
  have ha2 : (a' : GL (Fin 2) F) * (a' : GL (Fin 2) F) = -1 := by
    have h1 : iota1 M (a' * a') = iota1 M ⟨-1, M.neg_one_mem_H2⟩ := by
      rw [map_mul, iota1_negOne]
      exact hrr
    have h2' := iota1_injective M h1
    exact congrArg Subtype.val h2'
  have hadet : ((a' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := ((M.mem_H2 _).1 a'.2).2
  have hgdet : (((a₁ : GL (Fin 2) F) * dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      -1 := by
    rw [Units.val_mul, Matrix.det_mul, ((M.mem_H2 _).1 a₁.2).2, det_dRefl, one_mul]
  exact sign_GL h2 hnoi ha'U hg₁U ha2 hadet hgdet ⟨c⁻¹, hg1sq⟩ hc1'.symm

end Model

section Glue

open CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {K : Type} [Group K] [Finite K]

private theorem sylowFourJoined_of_dat410_center {q : ℕ} (hq : Odd q) (S₀ : Sylow 2 K) {z t w : K}
    {E₁ E₂ : Subgroup K} (hz : orderOf z = 2) (hc : CenterIs (S₀ : Subgroup K) z)
    (hD : Dat410 q z (S₀ : Subgroup K) t w E₁ E₂)
    (hsign : ∀ k ∈ E₁ ⊔ E₂, (k * w) * (k * w) = 1 → ∀ r ∈ E₁, r * r = z →
      (k * w) * r ≠ r * (k * w)) : SylowFourJoined K := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hzm := (hc z).2 (mem_zpowers z)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hD.t_ord, pow_two] at this
  have hw2 : w * w = 1 := by
    rcases hD.w_ord with h | h
    · rw [h, one_mul]
    · have := pow_orderOf_eq_one w
      rwa [h, pow_two] at this
  have hEz := hD.Ez_eq
  refine sylowFourJoined_of_sylow S₀ fun E F hE hES hF hFS => ?_
  exact reflTransGen_commFourAdj_of_dat410w hq S₀ hz2 hz1 hzm.2 hzm.1 hD.t_mem ht2 hD.w_mem hw2
    hD.comm (by rw [← hEz]; exact hD.prod) (by rw [← hEz]; exact Subgroup.map_subtype_le _)
    (fun c hc' n hn => by
      rw [← hEz] at hn ⊢
      exact CFSG.GH74.GLS.Stage1.Main.Ez_conj_mem hc' hn)
    hD.E₂_eq hD.sl2 hD.inter_E hD.comm_E (by rw [← hEz]; exact hD.norm_E) hsign hE hES hF hFS

end Glue

section M128A

open CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81 Equiv

private def inA0 (v : Multiplicative V4) (r : R0) : Prop :=
  ((Multiplicative.toAdd v).1 = 0 ∨ (Multiplicative.toAdd v).1 = 2) ∧
  ((Multiplicative.toAdd v).2 = 0 ∨ (Multiplicative.toAdd v).2 = 2) ∧
  ((r : Perm (Fin 4)) = 1 ∨ (r : Perm (Fin 4)) = swap 0 1 * swap 2 3)

private instance (v : Multiplicative V4) (r : R0) : Decidable (inA0 v r) := by
  unfold inA0; infer_instance

private theorem inA0_one : inA0 1 1 := by decide

private theorem inA0_mul : ∀ (v : Multiplicative V4) (r : R0) (v' : Multiplicative V4) (r' : R0),
    inA0 v r → inA0 v' r' →
      inA0 ((⟨v, r⟩ * ⟨v', r'⟩ : M128).left) ((⟨v, r⟩ * ⟨v', r'⟩ : M128).right) := by
  decide +kernel

private theorem inA0_inv : ∀ (v : Multiplicative V4) (r : R0), inA0 v r →
    inA0 (((⟨v, r⟩ : M128)⁻¹).left) (((⟨v, r⟩ : M128)⁻¹).right) := by
  decide +kernel

private theorem inA0_conj : ∀ (g : Multiplicative V4) (s : R0) (v : Multiplicative V4) (r : R0),
    inA0 v r →
      inA0 ((⟨g, s⟩ * ⟨v, r⟩ * (⟨g, s⟩ : M128)⁻¹ : M128).left)
        ((⟨g, s⟩ * ⟨v, r⟩ * (⟨g, s⟩ : M128)⁻¹ : M128).right) := by
  decide +kernel

private theorem inA0_sq : ∀ (v : Multiplicative V4) (r : R0), inA0 v r →
    (⟨v, r⟩ * ⟨v, r⟩ : M128).left = 1 ∧ (⟨v, r⟩ * ⟨v, r⟩ : M128).right = 1 := by
  decide +kernel

private theorem card_inA0 :
    Nat.card {p : Multiplicative V4 × R0 // inA0 p.1 p.2} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private def A0 : Subgroup M128 where
  carrier := {x | inA0 x.left x.right}
  one_mem' := inA0_one
  mul_mem' := fun {x y} hx hy => inA0_mul x.left x.right y.left y.right hx hy
  inv_mem' := fun {x} hx => inA0_inv x.left x.right hx

private theorem card_A0 : Nat.card ↥A0 = 8 := by
  rw [← card_inA0]
  exact Nat.card_congr (Equiv.subtypeEquiv SemidirectProduct.equivProd (fun x => Iff.rfl))

private theorem A0_conj (g x : M128) (hx : x ∈ A0) : g * x * g⁻¹ ∈ A0 :=
  inA0_conj g.left g.right x.left x.right hx

private theorem A0_sq (x : M128) (hx : x ∈ A0) : x * x = 1 := by
  obtain ⟨h1, h2⟩ := inA0_sq x.left x.right hx
  exact SemidirectProduct.ext h1 h2

private theorem sylowFourJoined_of_M128 {Q : Type} [Group Q] [Finite Q] (S : Sylow 2 Q)
    (e : M128 ≃* (S : Subgroup Q)) : SylowFourJoined Q := by
  let ι : M128 →* Q := (S : Subgroup Q).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  refine sylowFourJoined_of_normal_elemAbelian S (A := A0.map ι) ?_ ?_ ?_
  · intro s hs
    obtain ⟨m, hm⟩ := e.surjective ⟨s, hs⟩
    have hsm : ι m = s := congrArg Subtype.val hm
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨m * a * m⁻¹, A0_conj m a ha, ?_⟩
      rw [map_mul, map_mul, map_inv, hsm]
    · rintro ⟨b, hb, hbx⟩
      refine ⟨m⁻¹ * b * m, ?_, ?_⟩
      · simpa using A0_conj m⁻¹ b hb
      · rw [map_mul, map_mul, map_inv, hsm, hbx]
        group
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, A0_sq a ha, map_one]
  · rw [Subgroup.card_map_of_injective hι, card_A0]

end M128A

section Three

open CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.Blueprint

variable {F : Type} [Field F]

private theorem tP_conj_E (M : ModelData F) {e : PG M} (he : e ∈ K1 M ⊔ K2 M) :
    tP M * e * (tP M)⁻¹ ∈ K1 M ⊔ K2 M := by
  obtain ⟨a, b, rfl⟩ := (mem_E_iff M).1 he
  have e1 := tP_conj_iota1 M a
  have e2 := tP_conj_iota2 M b
  have : tP M * (iota1 M a * iota2 M b) * (tP M)⁻¹ =
      (tP M * iota1 M a * (tP M)⁻¹) * (tP M * iota2 M b * (tP M)⁻¹) := by group
  rw [this, e1, e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨a, rfl⟩) (Subgroup.mem_sup_left ⟨b, rfl⟩)

private theorem C0_conj_E (M : ModelData F) (h2 : (2 : F) ≠ 0) {c : PG M} (hc : c ∈ C0 M)
    {e : PG M} (he : e ∈ K1 M ⊔ K2 M) : c * e * c⁻¹ ∈ K1 M ⊔ K2 M := by
  obtain ⟨a, b, rfl⟩ := (mem_E_iff M).1 he
  have h1 : c * iota1 M a * c⁻¹ ∈ K1 M := C0_conj_K1 M h2 hc ⟨a, rfl⟩
  have h2' : c * iota2 M b * c⁻¹ ∈ K2 M := C0_conj_K2 M h2 hc ⟨b, rfl⟩
  have : c * (iota1 M a * iota2 M b) * c⁻¹ =
      (c * iota1 M a * c⁻¹) * (c * iota2 M b * c⁻¹) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2')

private theorem Cg_split (M : ModelData F) {g : PG M} (hg : g ∈ Cg M) :
    g ∈ C0 M ∨ ∃ c ∈ C0 M, g = tP M * c := by
  have hg' : g ∈ (Nsub M).map (mkP M) := by rw [← centralizer_yP]; exact hg
  obtain ⟨n, hn, rfl⟩ := hg'
  rcases (mem_Nsub_iff_D M).1 hn with hD | hW
  · exact Or.inl ⟨n, hD, rfl⟩
  · refine Or.inr ⟨mkP M (M.wK * n), ⟨_, hW, rfl⟩, ?_⟩
    rw [map_mul]
    show mkP M n = tP M * (tP M * mkP M n)
    rw [← mul_assoc, tP_sq, one_mul]

private theorem Cg_conj_E (M : ModelData F) (h2 : (2 : F) ≠ 0) {g : PG M} (hg : g ∈ Cg M)
    {e : PG M} (he : e ∈ K1 M ⊔ K2 M) : g * e * g⁻¹ ∈ K1 M ⊔ K2 M := by
  rcases Cg_split M hg with h | ⟨c, hc, rfl⟩
  · exact C0_conj_E M h2 h he
  · have h1 := tP_conj_E M (C0_conj_E M h2 hc he)
    have : tP M * c * e * (tP M * c)⁻¹ = tP M * (c * e * c⁻¹) * (tP M)⁻¹ := by group
    rw [this]
    exact h1

private theorem det_pm_one (hcard : Nat.card F = 3) (a : GL (Fin 2) F) :
    ((a : Matrix (Fin 2) (Fin 2) F).det = 1) ∨ ((a : Matrix (Fin 2) (Fin 2) F).det = -1) := by
  have hu : Matrix.GeneralLinearGroup.det a ^ 2 = 1 := by
    have h1 : Nat.card Fˣ = 2 := by
      rw [Nat.card_units, hcard]
    calc Matrix.GeneralLinearGroup.det a ^ 2 = Matrix.GeneralLinearGroup.det a ^ Nat.card Fˣ := by
          rw [h1]
      _ = 1 := pow_card_eq_one'
  have hu' : Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det a = 1 := by
    rw [← sq]; exact hu
  have hv := Matrix.GeneralLinearGroup.val_det_apply a
  rcases units_sq_eq_one hu' with h | h
  · left
    rw [h] at hv
    simpa using hv.symm
  · right
    rw [h] at hv
    simpa using hv.symm

private theorem C0_decomp (M : ModelData F) (h2 : (2 : F) ≠ 0) (hcard : Nat.card F = 3)
    (hd : dRefl F ∈ M.U2) {c : PG M} (hc : c ∈ C0 M) :
    c ∈ K1 M ⊔ K2 M ∨ ∃ e ∈ K1 M ⊔ K2 M, c = e * dP M (dRefl F) hd := by
  obtain ⟨n, hn, rfl⟩ := hc
  obtain ⟨a, b, hab, haU, hbU, hdet⟩ := M.exists_diagGL_of_comm h2 n.2
    (congrArg Subtype.val (mem_Dsub.1 hn))
  have hdi : (dRefl F)⁻¹ = dRefl F := inv_eq_of_mul_eq_one_right dRefl_mul_self
  have hn' : n = ⟨diagGL a b, by rw [← hab]; exact n.2⟩ := Subtype.ext hab
  rcases det_pm_one hcard a with ha1 | ha1
  ·
    left
    have hb1 : (b : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [ha1, one_mul] at hdet; exact hdet
    have hxa : a ∈ M.H2 := (M.mem_H2 a).2 ⟨haU, ha1⟩
    have hyb : b ∈ M.H2 := (M.mem_H2 b).2 ⟨hbU, hb1⟩
    have hxy := diagGL_mem_K4_of_H2 M ⟨a, hxa⟩ ⟨b, hyb⟩
    have : mkP M n = iota1 M ⟨a, hxa⟩ * iota2 M ⟨b, hyb⟩ := by
      rw [iota_mul_eq_mkP_diag M ⟨a, hxa⟩ ⟨b, hyb⟩ hxy, hn']
    rw [this]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  ·
    right
    have hb1 : (b : Matrix (Fin 2) (Fin 2) F).det = -1 := by
      rw [ha1] at hdet
      linear_combination -hdet
    have hdd : ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := det_dRefl
    have hxa : a * dRefl F ∈ M.H2 := (M.mem_H2 _).2 ⟨M.U2.mul_mem haU hd, by
      rw [Units.val_mul, Matrix.det_mul, ha1, hdd]; norm_num⟩
    have hyb : b * dRefl F ∈ M.H2 := (M.mem_H2 _).2 ⟨M.U2.mul_mem hbU hd, by
      rw [Units.val_mul, Matrix.det_mul, hb1, hdd]; norm_num⟩
    have hxy := diagGL_mem_K4_of_H2 M ⟨a * dRefl F, hxa⟩ ⟨b * dRefl F, hyb⟩
    refine ⟨iota1 M ⟨a * dRefl F, hxa⟩ * iota2 M ⟨b * dRefl F, hyb⟩,
      Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩
    rw [iota_mul_eq_mkP_diag M ⟨a * dRefl F, hxa⟩ ⟨b * dRefl F, hyb⟩ hxy, dP, ← map_mul, hn']
    congr 1
    apply Subtype.ext
    show diagGL a b = diagGL (a * dRefl F) (b * dRefl F) * diagGL (dRefl F) (dRefl F)⁻¹
    rw [diagGL_mul, hdi, mul_assoc, mul_assoc, dRefl_mul_self, mul_one, mul_one]

private theorem Cg_decomp (M : ModelData F) (h2 : (2 : F) ≠ 0) (hcard : Nat.card F = 3)
    (hd : dRefl F ∈ M.U2) {g : PG M} (hg : g ∈ Cg M) :
    ∃ k ∈ K1 M ⊔ K2 M, g = k ∨ g = k * tP M ∨ g = k * dP M (dRefl F) hd ∨
      g = k * (tP M * dP M (dRefl F) hd) := by
  have htw := tP_comm_dP M hd
  rcases Cg_split M hg with h | ⟨c, hc, rfl⟩
  · rcases C0_decomp M h2 hcard hd h with he | ⟨e, he, rfl⟩
    · exact ⟨g, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr (Or.inr (Or.inl rfl))⟩
  · rcases C0_decomp M h2 hcard hd hc with he | ⟨e, he, rfl⟩
    · refine ⟨tP M * c * (tP M)⁻¹, tP_conj_E M he, Or.inr (Or.inl ?_)⟩
      group
    · refine ⟨tP M * e * (tP M)⁻¹, tP_conj_E M he, Or.inr (Or.inr (Or.inr ?_))⟩
      group

private theorem K1_inf_K2' (M : ModelData F) : K1 M ⊓ K2 M = zpowers (yP M) := by
  apply le_antisymm
  · rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    obtain ⟨l, hl⟩ := iota1_eq_iota2_scalar a b hb.symm
    have hdet := ((M.mem_H2 _).1 a.2).2
    rw [hl, det_sc2] at hdet
    have hll : l * l = 1 := Units.ext (by simpa [sq] using hdet)
    rcases units_sq_eq_one hll with rfl | rfl
    · have ha : a = 1 := Subtype.ext (by rw [hl, sc2_one]; rfl)
      rw [ha, map_one]
      exact Subgroup.one_mem _
    · have ha : a = ⟨-1, M.neg_one_mem_H2⟩ :=
        Subtype.ext (by rw [hl]; exact CFSG.GH74.L5U5.scalar_neg_one_eq (F := F) 2)
      rw [ha, iota1_negOne]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨⟨-1, M.neg_one_mem_H2⟩, iota1_negOne M⟩, ⟨⟨-1, M.neg_one_mem_H2⟩, iota2_negOne M⟩⟩

private theorem tP_not_mem_normalizer_lin (F : Type) [Field F] [Finite F] :
    tP (ModelData.lin F) ∉
      Subgroup.normalizer (K1 (ModelData.lin F) : Set (PG (ModelData.lin F))) := by
  intro htN
  have htN' := Subgroup.mem_normalizer_iff.1 htN
  have hK21 : K2 (ModelData.lin F) ≤ K1 (ModelData.lin F) := by
    intro x hx
    rw [← tP_swap (ModelData.lin F)] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    rw [← hyx]
    exact (htN' y).1 hy
  have hmem : iota2 (ModelData.lin F) ⟨J0 F, J0_mem_H2_lin F⟩ ∈ zpowers (yP (ModelData.lin F)) := by
    rw [← K1_inf_K2']
    exact ⟨hK21 ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  rcases mem_zpowers_of_sq_one (yP_sq (ModelData.lin F)) hmem with h | h
  · have := iota2_injective (ModelData.lin F) (h.trans (map_one _).symm)
    have h00 := congrArg (fun u : ↥(ModelData.lin F).H2 =>
      ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) this
    simp [coe_J0] at h00
  · have := iota2_injective (ModelData.lin F) (h.trans (iota2_negOne (ModelData.lin F)).symm)
    have h00 := congrArg (fun u : ↥(ModelData.lin F).H2 =>
      ((u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) this
    simp [coe_J0] at h00

private theorem sylowFourJoined_lin_three [Finite F] (h2 : (2 : F) ≠ 0) (hcard : Nat.card F = 3) :
    SylowFourJoined (PG (ModelData.lin F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : dRefl F ∈ (ModelData.lin F).U2 := Subgroup.mem_top _
  have hq4 : Nat.card F % 4 = 3 := by rw [hcard]
  have hnoi : ∀ l : Fˣ, sc2 l ∈ (ModelData.lin F).U2 → l * l ≠ -1 := by
    intro l _ hll
    have : Fintype F := Fintype.ofFinite F
    have hsq : IsSquare (-1 : F) := ⟨l, by
      have := congrArg (fun u : Fˣ => (u : F)) hll
      simpa using this.symm⟩
    have := FiniteField.isSquare_neg_one_iff.1 hsq
    rw [← Nat.card_eq_fintype_card] at this
    exact this hq4
  have hCodd : Odd (Cg (ModelData.lin F)).index := by
    rw [index_C]
    exact odd_index_Nsub _ h2 (CFSG.GH74.GLS.Stage2.Final.ModelOrd.odd_index_lin F h2)
  have hww : dP (ModelData.lin F) (dRefl F) hd * dP (ModelData.lin F) (dRefl F) hd = 1 :=
    dP_mul_self hd dRefl_mul_self
  have htw := tP_comm_dP (ModelData.lin F) hd
  have hord_t : ∃ i : ℕ, tP (ModelData.lin F) ^ 2 ^ i = 1 := ⟨1, by simpa [pow_two] using tP_sq _⟩
  have hord_w : ∃ i : ℕ, dP (ModelData.lin F) (dRefl F) hd ^ 2 ^ i = 1 :=
    ⟨1, by simpa [pow_two] using hww⟩
  have hW : IsPGroup 2 ↥(zpowers (tP (ModelData.lin F)) ⊔
      zpowers (dP (ModelData.lin F) (dRefl F) hd)) :=
    CFSG.GH74.GLS.Stage2.Final.ModelSylowQ.isPGroup_sup_zpowers htw hord_t hord_w
  have hWC : zpowers (tP (ModelData.lin F)) ⊔ zpowers (dP (ModelData.lin F) (dRefl F) hd) ≤
      Cg (ModelData.lin F) :=
    sup_le (Subgroup.zpowers_le.2 (tP_mem_Cg _)) (Subgroup.zpowers_le.2 (dP_mem_Cg _ hd))
  have hW' : IsPGroup 2 ((zpowers (tP (ModelData.lin F)) ⊔
      zpowers (dP (ModelData.lin F) (dRefl F) hd)).subgroupOf (Cg (ModelData.lin F))) :=
    hW.comap_subtype
  obtain ⟨S', hS'⟩ := hW'.exists_le_sylow
  obtain ⟨P, hP⟩ := sylow_of_odd_index (Cg (ModelData.lin F)) hCodd S'
  have hPC : (P : Subgroup (PG (ModelData.lin F))) ≤ Cg (ModelData.lin F) := by
    rw [hP]; exact Subgroup.map_subtype_le _
  have hmem : ∀ x ∈ zpowers (tP (ModelData.lin F)) ⊔
      zpowers (dP (ModelData.lin F) (dRefl F) hd), x ∈ (P : Subgroup (PG (ModelData.lin F))) := by
    intro x hx
    rw [hP]
    exact ⟨⟨x, hWC hx⟩, hS' (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have htP := hmem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hwP := hmem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hcomm : ∀ x ∈ (P : Subgroup (PG (ModelData.lin F))), Commute x (yP (ModelData.lin F)) :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hPC hx)
  have hzP : yP (ModelData.lin F) ∈ (P : Subgroup (PG (ModelData.lin F))) :=
    mem_sylow_of_commute P ⟨1, by rw [pow_one, sq]; exact yP_sq _⟩ hcomm
  have hdec : ∀ s ∈ (P : Subgroup (PG (ModelData.lin F))),
      ∃ k ∈ (P : Subgroup (PG (ModelData.lin F))) ⊓
          (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F)),
        s = k ∨ s = k * tP (ModelData.lin F) ∨ s = k * dP (ModelData.lin F) (dRefl F) hd ∨
          s = k * (tP (ModelData.lin F) * dP (ModelData.lin F) (dRefl F) hd) := by
    intro s hs
    obtain ⟨k, hk, hcases⟩ := Cg_decomp (ModelData.lin F) h2 hcard hd (hPC hs)
    refine ⟨k, ⟨?_, hk⟩, hcases⟩
    have hk' : k = s ∨ k = s * (tP (ModelData.lin F))⁻¹ ∨
        k = s * (dP (ModelData.lin F) (dRefl F) hd)⁻¹ ∨
        k = s * (tP (ModelData.lin F) * dP (ModelData.lin F) (dRefl F) hd)⁻¹ := by
      rcases hcases with h | h | h | h
      · left; exact h.symm
      · right; left; rw [h]; group
      · right; right; left; rw [h]; group
      · right; right; right; rw [h]; group
    rcases hk' with h | h | h | h <;> rw [h]
    · exact hs
    · exact (P : Subgroup (PG (ModelData.lin F))).mul_mem hs
        ((P : Subgroup (PG (ModelData.lin F))).inv_mem htP)
    · exact (P : Subgroup (PG (ModelData.lin F))).mul_mem hs
        ((P : Subgroup (PG (ModelData.lin F))).inv_mem hwP)
    · exact (P : Subgroup (PG (ModelData.lin F))).mul_mem hs
        ((P : Subgroup (PG (ModelData.lin F))).inv_mem
          ((P : Subgroup (PG (ModelData.lin F))).mul_mem htP hwP))
  have hz2 := yP_sq (ModelData.lin F)
  have hz1 := yP_ne_one (ModelData.lin F) h2
  have ht2 := tP_sq (ModelData.lin F)
  have hPE : (P : Subgroup (PG (ModelData.lin F))) =
      ((P : Subgroup (PG (ModelData.lin F))) ⊓ (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))) ⊔
        zpowers (tP (ModelData.lin F)) ⊔ zpowers (dP (ModelData.lin F) (dRefl F) hd) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨k, hk, hcase⟩ := hdec s hs
      have hk' : k ∈ ((P : Subgroup (PG (ModelData.lin F))) ⊓
          (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))) ⊔ zpowers (tP (ModelData.lin F)) ⊔
            zpowers (dP (ModelData.lin F) (dRefl F) hd) :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_left hk)
      have ht' : tP (ModelData.lin F) ∈ ((P : Subgroup (PG (ModelData.lin F))) ⊓
          (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))) ⊔ zpowers (tP (ModelData.lin F)) ⊔
            zpowers (dP (ModelData.lin F) (dRefl F) hd) :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      have hw' : dP (ModelData.lin F) (dRefl F) hd ∈ ((P : Subgroup (PG (ModelData.lin F))) ⊓
          (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))) ⊔ zpowers (tP (ModelData.lin F)) ⊔
            zpowers (dP (ModelData.lin F) (dRefl F) hd) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rcases hcase with h | h | h | h <;> rw [h]
      · exact hk'
      · exact Subgroup.mul_mem _ hk' ht'
      · exact Subgroup.mul_mem _ hk' hw'
      · exact Subgroup.mul_mem _ hk' (Subgroup.mul_mem _ ht' hw')
    · exact sup_le (sup_le inf_le_left (Subgroup.zpowers_le.2 htP)) (Subgroup.zpowers_le.2 hwP)
  have hEC : K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F) ≤ Cg (ModelData.lin F) :=
    E_le_Cg _
  have hEN : ∀ c ∈ Subgroup.centralizer ({yP (ModelData.lin F)} : Set (PG (ModelData.lin F))),
      ∀ n ∈ K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F),
        c * n * c⁻¹ ∈ K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F) :=
    fun c hc n hn => Cg_conj_E (ModelData.lin F) h2 hc hn
  have hsl : HasSL2Model ↥(K1 (ModelData.lin F)) (fun r => r = 3) := by
    obtain ⟨F', iF', fF', hF', ⟨e⟩⟩ := hasSL2Model_H2_lin F
    exact ⟨F', iF', fF', by rw [hF', hcard],
      ⟨(MonoidHom.ofInjective (iota1_injective (ModelData.lin F))).symm.trans e⟩⟩
  have hwN : dP (ModelData.lin F) (dRefl F) hd ∈
      Subgroup.normalizer (K1 (ModelData.lin F) : Set (PG (ModelData.lin F))) :=
    normalizer_K1_of_C0 _ h2 (dP_mem_C0 _ hd)
  have hnorm : Subgroup.normalizer (K1 (ModelData.lin F) : Set (PG (ModelData.lin F))) ⊓
      (P : Subgroup (PG (ModelData.lin F))) =
      ((P : Subgroup (PG (ModelData.lin F))) ⊓ (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))) ⊔
        zpowers (dP (ModelData.lin F) (dRefl F) hd) := by
    apply le_antisymm
    · rintro x ⟨hxN, hxS⟩
      obtain ⟨k, hk, hcase⟩ := hdec x hxS
      have hkN : k ∈ Subgroup.normalizer (K1 (ModelData.lin F) : Set (PG (ModelData.lin F))) :=
        normalizer_K1_of_C0 _ h2 (E_le_C0 _ hk.2)
      have hk' : k ∈ ((P : Subgroup (PG (ModelData.lin F))) ⊓
          (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))) ⊔
            zpowers (dP (ModelData.lin F) (dRefl F) hd) := Subgroup.mem_sup_left hk
      have hw' : dP (ModelData.lin F) (dRefl F) hd ∈ ((P : Subgroup (PG (ModelData.lin F))) ⊓
          (K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F))) ⊔
            zpowers (dP (ModelData.lin F) (dRefl F) hd) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rcases hcase with h | h | h | h
      · rw [h]; exact hk'
      · exfalso
        apply tP_not_mem_normalizer_lin F
        have : tP (ModelData.lin F) = k⁻¹ * x := by rw [h]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hxN
      · rw [h]; exact Subgroup.mul_mem _ hk' hw'
      · exfalso
        apply tP_not_mem_normalizer_lin F
        have h1 : tP (ModelData.lin F) * dP (ModelData.lin F) (dRefl F) hd = k⁻¹ * x := by
          rw [h]; group
        have h3 : tP (ModelData.lin F) * dP (ModelData.lin F) (dRefl F) hd ∈
            Subgroup.normalizer (K1 (ModelData.lin F) : Set (PG (ModelData.lin F))) := by
          rw [h1]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hxN
        have := Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hwN)
        rwa [mul_inv_cancel_right] at this
    · refine sup_le (fun x hx => Subgroup.mem_inf.2
        ⟨normalizer_K1_of_C0 _ h2 (E_le_C0 _ hx.2), hx.1⟩)
        (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hwN, hwP⟩))
  refine sylowFourJoined_of_sylow P fun E F' hE hEP hF' hFP => ?_
  exact reflTransGen_commFourAdj_of_dat410w (q := 3) ⟨1, rfl⟩ P hz2 hz1
    (fun x hx => (hcomm x hx).eq) hzP htP ht2 hwP hww htw hPE hEC hEN (tP_swap _).symm hsl
    (K1_inf_K2' _) (fun a ha b hb => K1_K2_comm _ ha hb) hnorm
    (fun k hk hkw r hr hrr => model_sign (ModelData.lin F) h2 hnoi hd hk hkw hr hrr)
    hE hEP hF' hFP

end Three

end L4U4

section Leaves

open CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.Blueprint

theorem leafL4_ivk {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (h4 : p ^ f % 4 = 3) (hmod : LieModel X .PSL 4 p f) : SylowFourJoined X := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psl_unpack hmod
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
  have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
  have h4' : Nat.card F % 4 = 3 := by rw [hF]; exact h4
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  obtain ⟨S₀, hc, hD⟩ := lin410 h2 h5' h4' (pglStmt_lin h2 h5' h4')
  have hnoi := (clsFacts_lin h2 h5' h4').no_scalar_i
  have e' : X ≃* PG (ModelData.lin F) := e
  haveI : Finite (PG (ModelData.lin F)) := Finite.of_equiv X e'.toEquiv
  have hsyl : SylowFourJoined (PG (ModelData.lin F)) :=
    L4U4.sylowFourJoined_of_dat410_center hodd S₀ (orderOf_yP _ h2) hc hD
      (fun k hk hkw r hr hrr =>
        L4U4.model_sign (ModelData.lin F) h2 hnoi (Subgroup.mem_top _) hk hkw hr hrr)
  exact SylowFourJoined.of_mulEquiv e'.symm hsyl

theorem leafU4_ivk {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (h4 : p ^ f % 4 = 1) (hmod : LieModel X .PSU 4 p f) : SylowFourJoined X := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psu_unpack hmod
  haveI : Fact p.Prime := ⟨hp⟩
  have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  haveI : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
  have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
  obtain ⟨S₀, hc, hD⟩ := uni410 hF hp2 h5 h4 (pglStmt_uni hF hp2 h5 h4)
  have hnoi := (clsFacts_uni hF hp2 h5 h4).no_scalar_i
  have e' : X ≃* PG (ModelData.uni hF) := e
  haveI : Finite (PG (ModelData.uni hF)) := Finite.of_equiv X e'.toEquiv
  have hsyl : SylowFourJoined (PG (ModelData.uni hF)) :=
    L4U4.sylowFourJoined_of_dat410_center hodd S₀ (orderOf_yP _ h2) hc hD
      (fun k hk hkw r hr hrr =>
        L4U4.model_sign (ModelData.uni hF) h2 hnoi dRefl_mem_uni hk hkw hr hrr)
  exact SylowFourJoined.of_mulEquiv e'.symm hsyl

theorem leafL4_M128 {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h8 : p ^ f % 8 = 5) (hmod : LieModel X .PSL 4 p f) : SylowFourJoined X := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psl_unpack hmod
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
  have hq : Nat.card F % 4 = 1 := by rw [hF]; omega
  obtain ⟨Φ, hΦ⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.exists_M128_embedding_lin h2 hq
  have e' : X ≃* PG (ModelData.lin F) := e
  let Φ' : CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.M128 →* X := e'.symm.toMonoidHom.comp Φ
  have hΦ' : Function.Injective Φ' := e'.symm.injective.comp hΦ
  obtain ⟨S, ⟨eM⟩⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.exists_sylow_M128_of_embedding Φ' hΦ'
    (CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.v2_card_model_psl hp h8 hmod)
  exact L4U4.sylowFourJoined_of_M128 S eM

theorem leafU4_M128 {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h8 : p ^ f % 8 = 3) (hmod : LieModel X .PSU 4 p f) : SylowFourJoined X := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psu_unpack hmod
  haveI : Fact p.Prime := ⟨hp⟩
  have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  haveI : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
  obtain ⟨Φ, hΦ⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.exists_M128_embedding_uni hF hp2
    (by omega)
  have e' : X ≃* PG (ModelData.uni hF) := e
  let Φ' : CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.M128 →* X := e'.symm.toMonoidHom.comp Φ
  have hΦ' : Function.Injective Φ' := e'.symm.injective.comp hΦ
  obtain ⟨S, ⟨eM⟩⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.exists_sylow_M128_of_embedding Φ' hΦ'
    (CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81.v2_card_model_psu hp h8 hmod)
  exact L4U4.sylowFourJoined_of_M128 S eM

theorem leafL4_three {X : Type} [Group X] [Finite X] (hmod : LieModel X .PSL 4 3 1) :
    SylowFourJoined X := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psl_unpack hmod
  have hcard : Nat.card F = 3 := by simpa using hF
  have h2 : (2 : F) ≠ 0 :=
    CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow Nat.prime_three (by norm_num) hF
  have e' : X ≃* PG (ModelData.lin F) := e
  haveI : Finite (PG (ModelData.lin F)) := Finite.of_equiv X e'.toEquiv
  exact SylowFourJoined.of_mulEquiv e'.symm (L4U4.sylowFourJoined_lin_three h2 hcard)

end Leaves

theorem leafL4_holds : LeafL4 := by
  intro X _ _ _ _ p f hp hp2 hf h8 hmod
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hcases : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 ∨ p ^ f % 8 = 7 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hple : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  rcases hcases with h3 | h5 | h7
  · by_cases h5' : 5 ≤ p ^ f
    · exact leafL4_ivk hp hp2 h5' (by omega) hmod
    · have hp4 : p ≤ 4 := by omega
      have hp3' : p = 3 := by
        interval_cases p
        · rfl
        · exact absurd hp (by decide)
      subst hp3'
      have hf1 : f = 1 := by
        by_contra hne
        have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hf1
      exact leafL4_three hmod
  · exact leafL4_M128 hp hp2 h5 hmod
  · exact leafL4_ivk hp hp2 (by omega) (by omega) hmod

theorem leafU4_holds : LeafU4 := by
  intro X _ _ _ _ p f hp hp2 hf h8 hmod
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hcases : p ^ f % 8 = 1 ∨ p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hple : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  rcases hcases with h1 | h3 | h5
  · exact leafU4_ivk hp hp2 (by omega) (by omega) hmod
  · exact leafU4_M128 hp hp2 h3 hmod
  · exact leafU4_ivk hp hp2 (by omega) (by omega) hmod

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
