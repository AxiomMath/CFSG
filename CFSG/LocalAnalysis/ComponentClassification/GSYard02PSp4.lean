module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02QuatTensor
import CFSG.GH74.GLS.Stage1.Main.BrPairModel
import CFSG.GH74.GLS.Stage2.Final.ModelIVK410Final
import CFSG.CGT.PushingUpLit.SolK.GenFourPSp
import CFSG.CGT.PushingUpLit.SolK.GenFourA8

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

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

end Counting

section Dat410

variable {K : Type} [Group K] [Finite K]

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

theorem reflTransGen_commFourAdj_of_dat410 {q : ℕ} (hq : Odd q) (P : Sylow 2 K) {z t : K}
    {E E₁ E₂ : Subgroup K} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) (hzP : z ∈ (P : Subgroup K))
    (htP : t ∈ (P : Subgroup K)) (ht2 : t * t = 1)
    (hPE : (P : Subgroup K) = ((P : Subgroup K) ⊓ E) ⊔ zpowers t)
    (hEC : E ≤ centralizer ({z} : Set K))
    (hEN : ∀ c ∈ centralizer ({z} : Set K), ∀ n ∈ E, c * n * c⁻¹ ∈ E)
    (hE : E = E₁ ⊔ E₂) (hE₂ : E₂ = E₁.map (MulAut.conj t).toMonoidHom)
    (hsl2 : HasSL2Model ↥E₁ (fun r => r = q)) (hint : E₁ ⊓ E₂ = zpowers z)
    (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) {F G : Subgroup K} (hF : IsKleinFour F)
    (hFP : F ≤ P) (hG : IsKleinFour G) (hGP : G ≤ P) :
    Relation.ReflTransGen (CommFourAdj K) F G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : z ∈ E₁ ∧ z ∈ E₂ := by
    have : z ∈ E₁ ⊓ E₂ := by rw [hint]; exact mem_zpowers z
    exact this
  have hE₁E : E₁ ≤ E := by rw [hE]; exact le_sup_left
  have hE₂E : E₂ ≤ E := by rw [hE]; exact le_sup_right
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hPC : (P : Subgroup K) ≤ centralizer ({z} : Set K) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hzc x hx)
  have hcardE : Nat.card ↥((P : Subgroup K) ⊓ E) = 2 ^ (Nat.card ↥E).factorization 2 :=
    card_inf_eq_of_normal hEC hEN (card_sylow_inf_of_le P hPC)
  have hnorm₁ : ∀ b ∈ E, ∀ n ∈ E₁, b * n * b⁻¹ ∈ E₁ := by
    intro b hb n hn
    rw [hE] at hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm hb
    have h1 : a₂ * n = n * a₂ := (hcomm n hn a₂ ha₂).symm
    have : a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₁ * n * a₁⁻¹ := by
      calc a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₁ * (a₂ * n) * a₂⁻¹ * a₁⁻¹ := by group
        _ = a₁ * (n * a₂) * a₂⁻¹ * a₁⁻¹ := by rw [h1]
        _ = a₁ * n * a₁⁻¹ := by group
    rw [this]
    exact E₁.mul_mem (E₁.mul_mem ha₁ hn) (E₁.inv_mem ha₁)
  have hnorm₂ : ∀ b ∈ E, ∀ n ∈ E₂, b * n * b⁻¹ ∈ E₂ := by
    intro b hb n hn
    rw [hE] at hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm hb
    have hc : a₂ * n * a₂⁻¹ ∈ E₂ := E₂.mul_mem (E₂.mul_mem ha₂ hn) (E₂.inv_mem ha₂)
    have h2 : a₁ * (a₂ * n * a₂⁻¹) = (a₂ * n * a₂⁻¹) * a₁ := hcomm a₁ ha₁ _ hc
    have : a₁ * a₂ * n * (a₁ * a₂)⁻¹ = a₂ * n * a₂⁻¹ := by
      calc a₁ * a₂ * n * (a₁ * a₂)⁻¹ = (a₁ * (a₂ * n * a₂⁻¹)) * a₁⁻¹ := by group
        _ = ((a₂ * n * a₂⁻¹) * a₁) * a₁⁻¹ := by rw [h2]
        _ = a₂ * n * a₂⁻¹ := by group
    rw [this]
    exact hc
  have hcard₁ : Nat.card ↥((P : Subgroup K) ⊓ E₁) = 2 ^ (Nat.card ↥E₁).factorization 2 :=
    card_inf_eq_of_normal hE₁E hnorm₁ hcardE
  have hcard₂ : Nat.card ↥((P : Subgroup K) ⊓ E₂) = 2 ^ (Nat.card ↥E₂).factorization 2 :=
    card_inf_eq_of_normal hE₂E hnorm₂ hcardE
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
  have hE_card : Nat.card ↥E * 2 = Nat.card ↥E₁ * Nat.card ↥E₂ := by
    have := card_sup_mul_card_inf_of_comm E₁ E₂ hcomm
    rw [← hE, hint, Nat.card_zpowers, hzord] at this
    exact this
  have hQ_card : Nat.card ↥(((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂)) * 2 =
      Nat.card ↥((P : Subgroup K) ⊓ E₁) * Nat.card ↥((P : Subgroup K) ⊓ E₂) := by
    have := card_sup_mul_card_inf_of_comm ((P : Subgroup K) ⊓ E₁) ((P : Subgroup K) ⊓ E₂)
      (fun x hx y hy => hcomm x hx.2 y hy.2)
    rw [hcardQ₁₂] at this
    exact this
  have hfac : (Nat.card ↥E).factorization 2 + 1 =
      (Nat.card ↥E₁).factorization 2 + (Nat.card ↥E₂).factorization 2 := by
    have h : (Nat.card ↥E * 2).factorization 2 =
        (Nat.card ↥E₁ * Nat.card ↥E₂).factorization 2 := by rw [hE_card]
    rw [Nat.factorization_mul Nat.card_pos.ne' (by norm_num),
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h
    simpa [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] using h
  have hQcard : Nat.card ↥(((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂)) =
      Nat.card ↥((P : Subgroup K) ⊓ E) := by
    have h2 : Nat.card ↥(((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂)) * 2 =
        2 ^ ((Nat.card ↥E).factorization 2) * 2 := by
      rw [hQ_card, hcard₁, hcard₂, ← pow_add, ← hfac, pow_succ]
    rw [hcardE]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hRle : ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂) ≤ (P : Subgroup K) ⊓ E :=
    sup_le (inf_le_inf_left _ hE₁E) (inf_le_inf_left _ hE₂E)
  have hR : ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂) = (P : Subgroup K) ⊓ E :=
    Subgroup.eq_of_le_of_card_ge hRle (by rw [hQcard])
  have hPt : ∀ r ∈ (P : Subgroup K) ⊓ E, t * r * t⁻¹ ∈ (P : Subgroup K) ⊓ E := fun r hr =>
    ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem htP hr.1) ((P : Subgroup K).inv_mem htP),
      hEN t (hPC htP) r hr.2⟩
  have htN : t ∈ normalizer (((P : Subgroup K) ⊓ E : Subgroup K) : Set K) := by
    rw [mem_normalizer_iff]
    intro r
    refine ⟨hPt r, fun hr => ?_⟩
    have h1 := hPt _ hr
    have e : t * (t * r * t⁻¹) * t⁻¹ = r := by
      rw [ht_inv]
      calc t * (t * r * t) * t = (t * t) * r * (t * t) := by group
        _ = r := by rw [ht2]; group
    rwa [e] at h1
  have hP' : ∀ g ∈ (P : Subgroup K), ∃ e ∈ ((P : Subgroup K) ⊓ E₁) ⊔ ((P : Subgroup K) ⊓ E₂),
      g = e ∨ g = e * t := by
    intro g hg
    rw [hR]
    have hg' : g ∈ ((P : Subgroup K) ⊓ E) ⊔ zpowers t := by rw [← hPE]; exact hg
    rw [sup_comm, ← SetLike.mem_coe,
      coe_mul_of_left_le_normalizer_right (zpowers t) ((P : Subgroup K) ⊓ E)
        (Subgroup.zpowers_le.mpr htN)] at hg'
    obtain ⟨a, ha, r, hr, rfl⟩ := hg'
    by_cases ha1 : a = 1
    · exact ⟨r, hr, Or.inl (by show a * r = r; rw [ha1, one_mul])⟩
    · have hat : a = t := FooteLit.eq_of_mem_zpowers_of_sq (by rw [sq]; exact ht2) ha1 ha
      refine ⟨t * r * t⁻¹, hPt r hr, Or.inr ?_⟩
      show a * r = t * r * t⁻¹ * t
      rw [hat]
      group
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
  have hpair : QuatPair z (P : Subgroup K) ((P : Subgroup K) ⊓ E₁) ((P : Subgroup K) ⊓ E₂) :=
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
  have hQt : ∀ a ∈ (P : Subgroup K) ⊓ E₁, t * a * t ∈ (P : Subgroup K) ⊓ E₂ := by
    intro a ha
    refine ⟨(P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem htP ha.1) htP, ?_⟩
    rw [hE₂]
    exact ⟨a, ha.2, by simp [MulAut.conj_apply, ht_inv]⟩
  exact reflTransGen_commFourAdj_of_quatPair hpair ht2 hQt hP' hF hFP hG hGP

end Dat410

section Large

open CFSG.GH74.GLS.Stage2.Final CFSG.Blueprint

theorem sylowFourJoined_of_psp4 {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hmod : LieModel X .PSp 2 p f) : SylowFourJoined X := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hGs : IsClassicalModel X p f := ⟨hp, hp2, by omega, Or.inl hmod⟩
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psp_unpack hmod
  have hPSp : CFSG.GH74.GLS.IVK.IsPSp4 X (p ^ f) := ⟨F, iF, fF, hF, ⟨e⟩⟩
  have hSp : CFSG.GH74.GLS.IVK.IsSp4L4U4 X (p ^ f) := Or.inl hPSp
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  refine sylowFourJoined_of_sylow P fun E E' hE hEP hE' hE'P => ?_
  obtain ⟨z, hzo, hcen⟩ := modelCenter X p f hGs P
  have hzmem : z ∈ ((center ↥(P : Subgroup X)).map (P : Subgroup X).subtype) := by
    rw [hcen]
    exact mem_zpowers z
  obtain ⟨c, hc, hcz⟩ := hzmem
  have hcz' : (c : X) = z := hcz
  have hzP : z ∈ (P : Subgroup X) := hcz' ▸ c.2
  have hzc : ∀ x ∈ (P : Subgroup X), x * z = z * x := by
    intro x hx
    have := Subgroup.mem_center_iff.1 hc ⟨x, hx⟩
    rw [← hcz']
    exact congrArg Subtype.val this
  obtain ⟨t, w, E₁, E₂, htP, -, hto, -, -, hprod, -, -, hEz, hE₂, hsl2, hinter, hcommE, -,
      hw1iff, -⟩ := ivk_4_10 X (p ^ f) hodd h5 hSp P z hzP hzo hzc
  have hw1 : w = 1 := hw1iff.2 hPSp
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    omega
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hto, pow_two] at this
  have hPE : (P : Subgroup X) = ((P : Subgroup X) ⊓ CFSG.GH74.GLS.IVK.Ez z) ⊔ zpowers t := by
    rw [hw1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hprod
    exact hprod
  exact reflTransGen_commFourAdj_of_dat410 hodd P hz2 hz1 hzc hzP htP ht2 hPE
    (Subgroup.map_subtype_le _)
    (fun c hc n hn => CFSG.GH74.GLS.Stage1.Main.Ez_conj_mem hc hn) hEz hE₂ hsl2 hinter hcommE hE
    hEP hE' hE'P

end Large

section Three

open CFSG.CGT.PushingUpLit.SolK CFSG.GH74.Exceptional

private def aMem (k : Fin 64) : Bool :=
  decide (k.val ∈ [0, 1, 12, 16, 17, 21, 38, 45, 49, 51, 52, 55, 57, 58, 61, 63])

private def vInv : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

private def checkAMul : Bool :=
  (List.finRange 64).all fun k => !aMem k || (List.finRange 64).all fun k' => !aMem k' ||
    (List.finRange 64).any fun k'' => aMem k'' && spPM (spMul (vL k) (vL k')) (vL k'')

private def checkASq : Bool :=
  (List.finRange 64).all fun k => !aMem k || spPM (spMul (vL k) (vL k)) 1

private def checkAConj : Bool :=
  (List.finRange 64).all fun k => !aMem k || (List.finRange 6).all fun j =>
    (List.finRange 64).any fun k' =>
      aMem k' && spPM (spMul (spMul (vGen j) (vL k)) (vGen (vInv j))) (vL k')

private theorem checkAMul_eq : checkAMul = true := by decide +kernel

private theorem checkASq_eq : checkASq = true := by decide +kernel

private theorem checkAConj_eq : checkAConj = true := by decide +kernel

private theorem card_aMem : Nat.card {k : Fin 64 // aMem k = true} = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem aMul_check {k k' : Fin 64} (hk : aMem k = true) (hk' : aMem k' = true) :
    ∃ k'' : Fin 64, aMem k'' = true ∧ spPM (spMul (vL k) (vL k')) (vL k'') = true := by
  have h := List.all_eq_true.mp checkAMul_eq k (List.mem_finRange k)
  rw [hk] at h
  simp only [Bool.not_true, Bool.false_or] at h
  have h2 := List.all_eq_true.mp h k' (List.mem_finRange k')
  rw [hk'] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  obtain ⟨k'', -, hk''⟩ := List.any_eq_true.mp h2
  simp only [Bool.and_eq_true] at hk''
  exact ⟨k'', hk''.1, hk''.2⟩

private theorem aSq_check {k : Fin 64} (hk : aMem k = true) :
    spPM (spMul (vL k) (vL k)) 1 = true := by
  have h := List.all_eq_true.mp checkASq_eq k (List.mem_finRange k)
  rw [hk] at h
  simpa using h

private theorem aConj_check {k : Fin 64} (hk : aMem k = true) (j : Fin 6) :
    ∃ k' : Fin 64, aMem k' = true ∧
      spPM (spMul (spMul (vGen j) (vL k)) (vGen (vInv j))) (vL k') = true := by
  have h := List.all_eq_true.mp checkAConj_eq k (List.mem_finRange k)
  rw [hk] at h
  simp only [Bool.not_true, Bool.false_or] at h
  have h2 := List.all_eq_true.mp h j (List.mem_finRange j)
  obtain ⟨k', -, hk'⟩ := List.any_eq_true.mp h2
  simp only [Bool.and_eq_true] at hk'
  exact ⟨k', hk'.1, hk'.2⟩

private theorem xk_zero : xk 0 = 1 := by
  have h1 := lift_xk 0
  rw [vL_zero] at h1
  exact h1.unique lift_one

private theorem xk_mul_xk {k k' k'' : Fin 64}
    (h : spPM (spMul (vL k) (vL k')) (vL k'') = true) : xk k * xk k' = xk k'' := by
  have h1 := (lift_xk k).mul (lift_xk k')
  rw [← spMul_eq] at h1
  exact (h1.of_pm (spPM_iff.1 h)).unique (lift_xk k'')

private theorem xk_sq {k : Fin 64} (h : spPM (spMul (vL k) (vL k)) 1 = true) :
    xk k * xk k = 1 := by
  have h1 := (lift_xk k).mul (lift_xk k)
  rw [← spMul_eq] at h1
  exact (h1.of_pm (spPM_iff.1 h)).unique lift_one

private noncomputable def aSub : Subgroup PSp43 where
  carrier := {x | ∃ k, aMem k = true ∧ x = xk k}
  one_mem' := ⟨0, by decide, xk_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
    obtain ⟨k'', hk'', hpm⟩ := aMul_check hk hk'
    exact ⟨k'', hk'', xk_mul_xk hpm⟩
  inv_mem' := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, inv_eq_of_mul_eq_one_right (xk_sq (aSq_check hk))⟩

private theorem aSub_sq {a : PSp43} (ha : a ∈ aSub) : a * a = 1 := by
  obtain ⟨k, hk, rfl⟩ := ha
  exact xk_sq (aSq_check hk)

private theorem card_aSub : Nat.card aSub = 16 := by
  have e : {k : Fin 64 // aMem k = true} ≃ ↥aSub :=
    Equiv.ofBijective (fun k => ⟨xk k.1, k.1, k.2, rfl⟩)
      ⟨fun a b h => Subtype.ext (xk_injective (congrArg Subtype.val h)), fun x => by
        obtain ⟨k, hk, hx⟩ := x.2
        exact ⟨⟨k, hk⟩, Subtype.ext hx.symm⟩⟩
  rw [← Nat.card_congr e]
  exact card_aMem

private theorem aSub_conj {j : Fin 6} {x : PSp43} (hx : x ∈ aSub) :
    vGenE j * x * vGenE (vInv j) ∈ aSub := by
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨k', hk', hpm⟩ := aConj_check hk j
  refine ⟨k', hk', ?_⟩
  have h1 := ((lift_vGenE j).mul (lift_xk k)).mul (lift_vGenE (vInv j))
  rw [← spMul_eq, ← spMul_eq] at h1
  exact (h1.of_pm (spPM_iff.1 hpm)).unique (lift_xk k')

private theorem vGenE_inv' (j : Fin 6) : (vGenE j)⁻¹ = vGenE (vInv j) := by
  fin_cases j
  · exact vGenE_inv_zero
  · exact vGenE_inv_one
  · exact vGenE_inv_two
  · show (vGenE 3)⁻¹ = vGenE 0
    rw [← vGenE_inv_zero, inv_inv]
  · show (vGenE 4)⁻¹ = vGenE 1
    rw [← vGenE_inv_one, inv_inv]
  · show (vGenE 5)⁻¹ = vGenE 2
    rw [← vGenE_inv_two, inv_inv]

private theorem vInv_vInv (j : Fin 6) : vInv (vInv j) = j := by
  fin_cases j <;> rfl

private theorem vGenE_normalizer (j : Fin 6) : vGenE j ∈ normalizer (aSub : Set PSp43) := by
  rw [mem_normalizer_iff]
  intro x
  rw [vGenE_inv']
  constructor
  · intro hx
    exact aSub_conj hx
  · intro hx
    have h := aSub_conj (j := vInv j) hx
    rw [vInv_vInv, ← vGenE_inv'] at h
    have e : (vGenE j)⁻¹ * (vGenE j * x * (vGenE j)⁻¹) * vGenE j = x := by group
    rwa [e] at h

private theorem vSub_le_normalizer : vSub ≤ normalizer (aSub : Set PSp43) := by
  rw [vSub, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl)
  · exact vGenE_normalizer 0
  · exact vGenE_normalizer 1
  · exact vGenE_normalizer 2

private noncomputable def vSyl : Sylow 2 PSp43 :=
  IsPGroup.toSylow (P := vSub) (IsPGroup.of_card (n := 6) (by rw [card_vSub]; norm_num)) (by
    have h := Subgroup.card_mul_index vSub
    rw [card_vSub, card_PSp43'] at h
    have : vSub.index = 405 := by omega
    rw [this]
    norm_num)

private theorem sylowFourJoined_PSp43 [Finite PSp43] : SylowFourJoined PSp43 :=
  sylowFourJoined_of_normal_elemAbelian vSyl (A := aSub) vSub_le_normalizer
    (fun a ha => aSub_sq ha) (by rw [card_aSub]; norm_num)

theorem sylowFourJoined_of_lieModel_PSp_three {X : Type} [Group X] [Finite X]
    (h : Blueprint.LieModel X .PSp 2 3 1) : SylowFourJoined X := by
  obtain ⟨-, K, iK, fK, hK, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
    rfl
  let φ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  let e₁ : StatedProj (StatedSp 2 K) ≃* PSp43 :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  haveI : Finite PSp43 := Finite.of_equiv X (e.trans e₁).toEquiv
  exact SylowFourJoined.of_mulEquiv (e.trans e₁).symm sylowFourJoined_PSp43

end Three

theorem leafPSp4_holds : LeafPSp4 := by
  intro X _ _ _ _ p f hp hp2 hf hmod
  by_cases h5 : 5 ≤ p ^ f
  · exact sylowFourJoined_of_psp4 hp hp2 h5 hmod
  · have hple : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hp4 : p ≤ 4 := by omega
    have hp3 : p = 3 := by
      have h2 := hp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp (by decide)
    subst hp3
    have hf1 : f = 1 := by
      by_contra hne
      have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hf1
    exact sylowFourJoined_of_lieModel_PSp_three hmod

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
