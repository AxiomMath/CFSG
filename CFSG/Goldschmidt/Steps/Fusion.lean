module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_b
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreEmbedding
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.StrongClosure
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped Pointwise commutatorElement

theorem N2 :
    ∀ (G : Type) [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (Q Q₁ : Subgroup G), IsPGroup p Q →
      Q₁ ≤ Q → ∀ x : G, (∀ q ∈ Q, q⁻¹ * (x⁻¹ * q * x) ∈ Q₁) → (∀ z ∈ Q₁, x⁻¹ * z * x = z) →
      ∃ k : ℕ, x ^ (p ^ k) ∈ Subgroup.centralizer (Q : Set G) := by
  intro G _ _ p _ Q Q₁ hQ hQ₁ x hc hfix
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  refine ⟨n, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
  set c := q⁻¹ * (x⁻¹ * q * x) with hcdef
  have hcQ₁ : c ∈ Q₁ := hc q hq
  have hxc : Commute x c := by
    have h := hfix c hcQ₁
    show x * c = c * x
    calc x * c = x * (x⁻¹ * c * x) := by rw [h]
      _ = c * x := by group
  have key : ∀ k : ℕ, (x ^ k)⁻¹ * q * x ^ k = q * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : x⁻¹ * c ^ k * x = c ^ k := by
        have := (hxc.pow_right k).eq
        calc x⁻¹ * c ^ k * x = x⁻¹ * (c ^ k * x) := by group
          _ = x⁻¹ * (x * c ^ k) := by rw [this]
          _ = c ^ k := by group
      calc (x ^ (k + 1))⁻¹ * q * x ^ (k + 1) = x⁻¹ * ((x ^ k)⁻¹ * q * x ^ k) * x := by
            rw [pow_succ]; group
        _ = x⁻¹ * (q * c ^ k) * x := by rw [ih]
        _ = (x⁻¹ * q * x) * (x⁻¹ * c ^ k * x) := by group
        _ = (x⁻¹ * q * x) * c ^ k := by rw [hck]
        _ = q * c * c ^ k := by rw [hcdef]; group
        _ = q * c ^ (k + 1) := by rw [pow_succ', mul_assoc]
  have hc1 : c ^ (p ^ n) = 1 := by
    have h := pow_card_eq_one' (G := Q) (x := ⟨c, hQ₁ hcQ₁⟩)
    rw [hn] at h
    simpa using congrArg Subtype.val h
  have h1 := key (p ^ n)
  rw [hc1, mul_one] at h1
  calc q * x ^ p ^ n = x ^ p ^ n * ((x ^ p ^ n)⁻¹ * q * x ^ p ^ n) := by group
    _ = x ^ p ^ n * q := by rw [h1]

theorem N3a :
    ∀ (G : Type) [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) (A P : Subgroup G),
      A ≤ S → fusionStronglyClosed (A : Set G) (S : Subgroup G) → IsPGroup p P → A ≤ P →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro G _ _ p _ S A P hAS hcl hP hAP g hg
  obtain ⟨Q, hPQ, hQ⟩ := stronglyClosed_of_le_pGroup S hcl hP hAP
  have hle : ∀ k : G, k ∈ Subgroup.normalizer (P : Set G) → conjSub k A ≤ Q := by
    intro k hk x hx
    exact hPQ ((Subgroup.mem_normalizer_iff.1 hk x).2 (hAP (mem_conjSub.1 hx)))
  have h1 := conj_eq_of_conj_le hQ (hle g hg)
  have h2 := conj_eq_of_conj_le hQ (hle g⁻¹ (Subgroup.inv_mem _ hg))
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : g * h * g⁻¹ ∈ conjSub g⁻¹ A := by
      rw [mem_conjSub, show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group]
      exact hh
    rwa [h2] at this
  · intro hh
    have : h ∈ conjSub g A := mem_conjSub.2 hh
    rwa [h1] at this

theorem N3b :
    ∀ (G : Type) [Group G] (S B P : Subgroup G), fusionStronglyClosed (B : Set G) S → P ≤ S →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer ((P ⊓ B : Subgroup G) : Set G) := by
  intro G _ S B P hB hPS g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  constructor
  · rintro ⟨hP, hBh⟩
    have h1 : g * h * g⁻¹ ∈ P := (hg h).1 hP
    refine ⟨h1, ?_⟩
    have h2 := hB h hBh g⁻¹ (by rw [inv_inv]; exact hPS h1)
    rwa [inv_inv] at h2
  · rintro ⟨hP, hBh⟩
    have h1 : h ∈ P := (hg h).2 hP
    refine ⟨h1, ?_⟩
    have he : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    have h2 := hB _ hBh g (by rw [he]; exact hPS h1)
    rwa [he] at h2

section Helpers

variable {G : Type*} [Group G]

private theorem le_normalizer_of_stronglyClosed {S A : Subgroup G} (hAS : A ≤ S)
    (hcl : fusionStronglyClosed (A : Set G) S) : S ≤ Subgroup.normalizer (A : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro ha
    have h1 := conj_mem_of_stronglyClosed hAS hcl (S.inv_mem hs) ha
    rwa [inv_inv] at h1
  · intro ha
    have h1 := conj_mem_of_stronglyClosed hAS hcl hs ha
    rwa [show s⁻¹ * (s * h * s⁻¹) * s = h by group] at h1

private theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

private theorem normalizer_le_normalizer_centralizer (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).1
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)

private def seriesStab (Q D : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (Q : Set G) ∧ (∀ q ∈ Q, q⁻¹ * (g⁻¹ * q * g) ∈ D) ∧
    ∀ z ∈ D, g⁻¹ * z * g = z}
  mul_mem' := by
    rintro g h ⟨hgN, hgQ, hgD⟩ ⟨hhN, hhQ, hhD⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun q hq => ?_, fun z hz => ?_⟩
    · have he : q⁻¹ * ((g * h)⁻¹ * q * (g * h)) =
          (q⁻¹ * (h⁻¹ * q * h)) * (h⁻¹ * (q⁻¹ * (g⁻¹ * q * g)) * h) := by group
      rw [he, hhD _ (hgQ q hq)]
      exact D.mul_mem (hhQ q hq) (hgQ q hq)
    · rw [show (g * h)⁻¹ * z * (g * h) = h⁻¹ * (g⁻¹ * z * g) * h by group, hgD z hz, hhD z hz]
  one_mem' := ⟨Subgroup.one_mem _, fun q _ => by simp, fun z _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgN, hgQ, hgD⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun q hq => ?_, fun z hz => ?_⟩
    · have hq' : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hgN q).1 hq
      have he : q⁻¹ * (g⁻¹⁻¹ * q * g⁻¹) =
          ((g * q * g⁻¹)⁻¹ * (g⁻¹ * (g * q * g⁻¹) * g))⁻¹ := by group
      rw [he]
      exact D.inv_mem (hgQ _ hq')
    · calc g⁻¹⁻¹ * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgD z hz, inv_inv]
        _ = z := by group

private theorem mem_seriesStab {Q D : Subgroup G} {g : G} :
    g ∈ seriesStab Q D ↔ g ∈ Subgroup.normalizer (Q : Set G) ∧
      (∀ q ∈ Q, q⁻¹ * (g⁻¹ * q * g) ∈ D) ∧ ∀ z ∈ D, g⁻¹ * z * g = z := Iff.rfl

private theorem conj_mem_seriesStab {Q D : Subgroup G} {n g : G}
    (hnQ : n ∈ Subgroup.normalizer (Q : Set G)) (hnD : n ∈ Subgroup.normalizer (D : Set G))
    (hg : g ∈ seriesStab Q D) : n * g * n⁻¹ ∈ seriesStab Q D := by
  obtain ⟨hgN, hgQ, hgD⟩ := hg
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hnQ hgN) (Subgroup.inv_mem _ hnQ),
    fun q hq => ?_, fun z hz => ?_⟩
  · have hq0 : n⁻¹ * q * n ∈ Q := (Subgroup.mem_normalizer_iff''.1 hnQ q).1 hq
    have he : q⁻¹ * ((n * g * n⁻¹)⁻¹ * q * (n * g * n⁻¹)) =
        n * ((n⁻¹ * q * n)⁻¹ * (g⁻¹ * (n⁻¹ * q * n) * g)) * n⁻¹ := by group
    rw [he]
    exact (Subgroup.mem_normalizer_iff.1 hnD _).1 (hgQ _ hq0)
  · have hz0 : n⁻¹ * z * n ∈ D := (Subgroup.mem_normalizer_iff''.1 hnD z).1 hz
    calc (n * g * n⁻¹)⁻¹ * z * (n * g * n⁻¹) = n * (g⁻¹ * (n⁻¹ * z * n) * g) * n⁻¹ := by group
      _ = z := by rw [hgD _ hz0]; group

private theorem normalizer_le_normalizer_seriesStab {Q D : Subgroup G}
    (hD : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (D : Set G)) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((seriesStab Q D : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_seriesStab hn (hD hn) hg, fun hg => ?_⟩
  have hn' := Subgroup.inv_mem _ hn
  have := conj_mem_seriesStab hn' (hD hn') hg
  rwa [show n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g by group] at this

private theorem centralizer_le_seriesStab {Q D : Subgroup G} (hDQ : D ≤ Q) :
    Subgroup.centralizer (Q : Set G) ≤ seriesStab Q D := by
  intro c hc
  have hfix : ∀ q ∈ Q, c⁻¹ * q * c = q := fun q hq => by
    rw [mul_assoc, Subgroup.mem_centralizer_iff.1 hc q hq, ← mul_assoc, inv_mul_cancel,
      one_mul]
  refine ⟨Subgroup.centralizer_le_normalizer _ hc, fun q hq => ?_, fun z hz => hfix z (hDQ hz)⟩
  rw [hfix q hq, inv_mul_cancel]
  exact D.one_mem

private theorem exists_index_eq_pow [Finite G] {p : ℕ} [Fact p.Prime] {Q C K : Subgroup G}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hnorm : Q ⊔ K ≤ Subgroup.normalizer ((Q ⊔ C : Subgroup G) : Set G))
    (hpow : ∀ g ∈ K, ∃ k : ℕ, g ^ (p ^ k) ∈ C) :
    ∃ k : ℕ, ((Q ⊔ C).subgroupOf (Q ⊔ K)).index = p ^ k := by
  have : ((Q ⊔ C).subgroupOf (Q ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hp : IsPGroup p (↥(Q ⊔ K) ⧸ (Q ⊔ C).subgroupOf (Q ⊔ K)) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H r =>
      obtain ⟨q, hq, g, hg, hqg⟩ : (r : G) ∈ (Q : Set G) * (K : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q K hKQ]
        exact r.2
      obtain ⟨k, hk⟩ := hpow g hg
      refine ⟨k, ?_⟩
      have hr : r = (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(Q ⊔ K)) * ⟨g, Subgroup.mem_sup_right hg⟩ :=
        Subtype.ext hqg.symm
      have hq1 : ((⟨q, Subgroup.mem_sup_left hq⟩ : ↥(Q ⊔ K)) :
          ↥(Q ⊔ K) ⧸ (Q ⊔ C).subgroupOf (Q ⊔ K)) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hq))
      have hg1 : ((⟨g, Subgroup.mem_sup_right hg⟩ : ↥(Q ⊔ K)) :
          ↥(Q ⊔ K) ⧸ (Q ⊔ C).subgroupOf (Q ⊔ K)) ^ p ^ k = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_sup_right (by simpa using hk)
      rw [hr, QuotientGroup.mk_mul, hq1, one_mul, hg1]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  exact ⟨k, by rw [Subgroup.index_eq_card]; exact hk⟩

private theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {x : G} {k : ℕ}
    (hk : x ^ (p ^ k) = 1) : IsPGroup p (Subgroup.zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

end Helpers

theorem N4a :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A Q : Subgroup G), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
      CFSG.RankTwoShapes.IsAlperinSubgroup 2 (S : Subgroup G) Q →
      A ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro G _ _ S A Q hAS hAab hcl hQ
  obtain ⟨hQS, -, hcent, hrad⟩ := hQ
  have hQ2 : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  have hSA : (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_stronglyClosed hAS hcl
  set N := Subgroup.normalizer (Q : Set G) with hNdef
  set C := Subgroup.centralizer (Q : Set G) with hCdef
  set K := seriesStab Q (Q ⊓ A) with hKdef
  have hND : N ≤ Subgroup.normalizer ((Q ⊓ A : Subgroup G) : Set G) := N3b G S A Q hcl hQS
  have hCK : C ≤ K := centralizer_le_seriesStab inf_le_left
  have hKN : K ≤ N := fun g hg => (mem_seriesStab.1 hg).1
  have hNK : N ≤ Subgroup.normalizer (K : Set G) := normalizer_le_normalizer_seriesStab hND
  have hNC : N ≤ Subgroup.normalizer (C : Set G) := normalizer_le_normalizer_centralizer Q
  have hpow : ∀ g ∈ K, ∃ k : ℕ, g ^ (2 ^ k) ∈ C := fun g hg =>
    N2 G Q (Q ⊓ A) hQ2 inf_le_left g (mem_seriesStab.1 hg).2.1 (mem_seriesStab.1 hg).2.2
  have hQKN : Q ⊔ K ≤ N := sup_le Subgroup.le_normalizer hKN
  have hR : Q ⊔ K = Q ⊔ C := by
    refine hrad _ (sup_le_sup_left hCK Q) hQKN (fun n hn => mem_normalizer_sup hn (hNK hn)) ?_
    exact exists_index_eq_pow hKN
      (fun r hr => mem_normalizer_sup (hQKN hr) (hNC (hQKN hr))) hpow
  have hAN : A ⊓ N ≤ Q := by
    rintro x ⟨hxA, hxN⟩
    have hxK : x ∈ K := by
      refine mem_seriesStab.2 ⟨hxN, fun q hq => ⟨?_, ?_⟩, fun z hz => ?_⟩
      · exact Q.mul_mem (Q.inv_mem hq) ((Subgroup.mem_normalizer_iff''.1 hxN q).1 hq)
      · have h1 := conj_mem_of_stronglyClosed hAS hcl (hQS hq) (A.inv_mem hxA)
        rw [show q⁻¹ * (x⁻¹ * q * x) = (q⁻¹ * x⁻¹ * q) * x by group]
        exact A.mul_mem h1 hxA
      · have h' : x * z = z * x :=
          congrArg Subtype.val (hAab.is_comm.comm ⟨x, hxA⟩ ⟨z, hz.2⟩)
        rw [mul_assoc, ← h', ← mul_assoc, inv_mul_cancel, one_mul]
    have hxR : x ∈ Q ⊔ C := hR ▸ Subgroup.mem_sup_right hxK
    obtain ⟨q, hq, c, hc, rfl⟩ : x ∈ (Q : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q C
        (Subgroup.centralizer_le_normalizer _)]
      exact hxR
    have hcS : c ∈ (S : Subgroup G) := by
      rw [show c = q⁻¹ * (q * c) by group]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hQS hq)) (hAS hxA)
    exact Q.mul_mem hq (hcent ⟨hc, hcS⟩)
  have hAQ : A ≤ Q := by
    by_contra hnot
    have hlt : Q < A ⊔ Q := lt_of_le_of_ne le_sup_right fun h => hnot (h ▸ le_sup_left)
    have hP : IsPGroup 2 (A ⊔ Q : Subgroup G) := S.isPGroup'.to_le (sup_le hAS hQS)
    obtain ⟨Y, hQY, hYP, hYN, -⟩ :=
      CFSG.section10_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup hP hlt
    obtain ⟨y, hyY, hyQ⟩ := IsConcreteLE.exists_of_lt hQY
    obtain ⟨a, ha, q, hq, rfl⟩ : y ∈ (A : Set G) * (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A Q (hQS.trans hSA)]
      exact hYP hyY
    have haN : a ∈ N := by
      rw [show a = a * q * q⁻¹ by group]
      exact N.mul_mem (hYN hyY) (N.inv_mem (Subgroup.le_normalizer hq))
    exact hyQ (Q.mul_mem (hAN ⟨ha, haN⟩) hq)
  exact ⟨hAQ, N3a G S A Q hAS hcl hQ2 hAQ⟩

theorem N4b :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A P : Subgroup G) (g : G), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) → P ≤ S →
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S →
      ∃ n ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ P, n⁻¹ * x * n = g⁻¹ * x * g := by
  intro G _ _ S A P g hAS hAab hcl hPS hPg
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hPS hPg
  refine ⟨c, ?_, hcg⟩
  clear hcg
  induction hc with
  | one => exact Subgroup.one_mem _
  | step _ hQ _ hn ih => exact Subgroup.mul_mem _ ih ((N4a G S A _ hAS hAab hcl hQ).2 hn)

theorem N5a :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A H : Subgroup G), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
      Subgroup.normalizer (A : Set G) ≤ H → ∀ x g : G, x ∈ H → g⁻¹ * x * g ∈ H →
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → ∃ h ∈ H, h⁻¹ * x * h = g⁻¹ * x * g := by
  intro G _ _ S A H hAS hAab hcl hNH x g hxH hgxH hx2
  have hSH : (S : Subgroup G) ≤ H := (le_normalizer_of_stronglyClosed hAS hcl).trans hNH
  obtain ⟨k, hk⟩ := hx2
  have hzx : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hk
  have hzy : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * x * g)) := by
    have := hzx.map (MulAut.conj g⁻¹).toMonoidHom
    rwa [MonoidHom.map_zpowers,
      show (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g by simp] at this
  obtain ⟨c₁, hc₁⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_conjugate_into_sylow_within_overgroup 2
      Nat.prime_two S H hSH _ hzx (Subgroup.zpowers_le.2 hxH)
  obtain ⟨c₂, hc₂⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_conjugate_into_sylow_within_overgroup 2
      Nat.prime_two S H hSH _ hzy (Subgroup.zpowers_le.2 hgxH)
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le] at hc₁ hc₂
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc₁ hc₂
  set x' := (c₁ : G) * x * (c₁ : G)⁻¹ with hx'
  set g' := (c₁ : G) * g * (c₂ : G)⁻¹ with hg'
  have hy' : g'⁻¹ * x' * g' = (c₂ : G) * (g⁻¹ * x * g) * (c₂ : G)⁻¹ := by
    rw [hx', hg']; group
  have hPg : (Subgroup.zpowers x').map (MulAut.conj g'⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply, hy'] using hc₂
  obtain ⟨n, hn, hng⟩ := N4b G S A (Subgroup.zpowers x') g' hAS hAab hcl
    (Subgroup.zpowers_le.2 hc₁) hPg
  have h1 := hng x' (Subgroup.mem_zpowers x')
  refine ⟨(c₁ : G)⁻¹ * n * c₂, H.mul_mem (H.mul_mem (H.inv_mem c₁.2) (hNH hn)) c₂.2, ?_⟩
  calc ((c₁ : G)⁻¹ * n * c₂)⁻¹ * x * ((c₁ : G)⁻¹ * n * c₂) =
        (c₂ : G)⁻¹ * (n⁻¹ * x' * n) * c₂ := by rw [hx']; group
    _ = (c₂ : G)⁻¹ * (g'⁻¹ * x' * g') * c₂ := by rw [h1]
    _ = g⁻¹ * x * g := by rw [hy']; group

theorem N5b :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
      (S : Subgroup G) ⊓ commutator G =
        (S : Subgroup G) ⊓
          ⁅Subgroup.normalizer (A : Set G), Subgroup.normalizer (A : Set G)⁆ := by
  intro G _ _ S A hAS hAab hcl
  have hSN := le_normalizer_of_stronglyClosed hAS hcl
  apply le_antisymm
  · have hfoc := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup 2 S
    rw [show CFSG.derivedSubgroup G = commutator G from derivedSeries_one G] at hfoc
    rw [hfoc, Subgroup.closure_le]
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    have hPg : (Subgroup.zpowers x).map (MulAut.conj c⁻¹⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      simpa [MulAut.conj_apply] using hy
    obtain ⟨n, hn, hng⟩ := N4b G S A (Subgroup.zpowers x) c⁻¹ hAS hAab hcl
      (Subgroup.zpowers_le.2 hx) hPg
    have h1 : n⁻¹ * x * n = c * x * c⁻¹ := by simpa using hng x (Subgroup.mem_zpowers x)
    refine ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hx) hy, ?_⟩
    have h2 : x⁻¹ * (c * x * c⁻¹) = ⁅x⁻¹, n⁻¹⁆ := by
      rw [← h1, commutatorElement_def]; group
    rw [h2]
    exact Subgroup.commutator_mem_commutator (hSN ((S : Subgroup G).inv_mem hx))
      (Subgroup.inv_mem _ hn)
  · rw [_root_.commutator_def]
    exact inf_le_inf_left _ (Subgroup.commutator_mono le_top le_top)

theorem N5c :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A H : Subgroup G), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) → commutator G = ⊤ →
      Subgroup.normalizer (A : Set G) ≤ H → ∀ H₀ : Subgroup G, H₀ ≤ H →
      (H₀.subgroupOf H).index ≠ 2 := by
  intro G _ _ S A H hAS hAab hcl hperf hNH H₀ hH₀H hidx
  have hcomm : ⁅H, H⁆ ≤ H₀ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    set a' : H := ⟨a, ha⟩
    set b' : H := ⟨b, hb⟩
    have key : ∀ u v : H, u * v ∈ H₀.subgroupOf H ↔
        (u ∈ H₀.subgroupOf H ↔ v ∈ H₀.subgroupOf H) :=
      fun u v => Subgroup.mul_mem_iff_of_index_two hidx
    have hab : a' * b' * a'⁻¹ * b'⁻¹ ∈ H₀.subgroupOf H := by
      rw [key, key, key, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
      tauto
    have := Subgroup.mem_subgroupOf.1 hab
    simpa [commutatorElement_def, a', b'] using this
  have h5 := N5b G S A hAS hAab hcl
  rw [hperf, inf_top_eq] at h5
  have hSH₀ : (S : Subgroup G) ≤ H₀ := fun s hs =>
    hcomm (Subgroup.commutator_mono hNH hNH (h5.le hs).2)
  have hSH : (S : Subgroup G) ≤ H := hSH₀.trans hH₀H
  have hidx' : H₀.relIndex H = 2 := hidx
  have h1 := Subgroup.relIndex_mul_relIndex (S : Subgroup G) H₀ H hSH₀ hH₀H
  apply S.not_dvd_index
  refine dvd_trans ?_ (Subgroup.relIndex_dvd_index_of_le hSH)
  rw [← h1, hidx']
  exact dvd_mul_left 2 _

end CFSG.Goldschmidt
