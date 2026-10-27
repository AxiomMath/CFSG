module

public import CFSG.Goldschmidt75.B1Perfect
public import CFSG.Goldschmidt75.B1KL
public import CFSG.Goldschmidt75.B3Prelim
public import CFSG.Goldschmidt75.TheoremBc

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (centralizer (S : Set G) : Set G) := by
  intro g hg
  have key : ∀ h ∈ normalizer (S : Set G), ∀ c ∈ centralizer (S : Set G),
      h * c * h⁻¹ ∈ centralizer (S : Set G) := by
    intro h hh c hc
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : h⁻¹ * s * h ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem hh) s).mp hs
      simpa using this
    have hcs := mem_centralizer_iff.mp hc _ hs'
    calc s * (h * c * h⁻¹) = h * ((h⁻¹ * s * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * s * h)) * h⁻¹ := by rw [hcs]
      _ = h * c * h⁻¹ * s := by group
  refine mem_normalizer_iff.mpr fun c => ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_perfRes_centralizer (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (perfRes (centralizer (S : Set G)) : Set G) :=
  (normalizer_le_normalizer_centralizer S).trans (normalizer_le_normalizer_perfRes _)

theorem stronglyClosed_inf_perfRes (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    fusionStronglyClosed (((T : Subgroup G) ⊓ perfRes (centralizer (S : Set G)) :
      Subgroup G) : Set G) T := by
  set C := centralizer (S : Set G) with hC
  have hLC' : perfRes C ≤ ⁅C, C⁆ := by
    rw [← commutator_perfRes C]
    exact commutator_mono (perfRes_le C) (perfRes_le C)
  have hR1 := theoremB_c T hST hS
  intro a ha g hg
  have haL : a ∈ perfRes C := (mem_inf.mp ha).2
  have ha1 : a ∈ (⁅C, C⁆ ⊓ T : Subgroup G) := mem_inf.mpr ⟨hLC' haL, (mem_inf.mp ha).1⟩
  have hg1 : g⁻¹ * a * g ∈ (⁅C, C⁆ ⊓ T : Subgroup G) := hR1 a ha1 g hg
  obtain ⟨m, hm, hmeq⟩ := exists_normalizer_conj T hST hS (commutator_le_self C
    (mem_inf.mp ha1).1) (commutator_le_self C (mem_inf.mp hg1).1)
  have hmL := normalizer_le_normalizer_perfRes_centralizer S (inv_mem hm)
  have h1 : m⁻¹ * a * m ∈ perfRes C := by
    have := (mem_normalizer_iff.mp hmL a).mp haL
    simpa using this
  rw [hmeq] at h1
  exact mem_inf.mpr ⟨hg, h1⟩

theorem fusionIsSylowIn_inf_perfRes (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    fusionIsSylowIn 2 ((T : Subgroup G) ⊓ perfRes (centralizer (S : Set G)))
      (perfRes (centralizer (S : Set G))) := by
  have hLN : perfRes (centralizer (S : Set G)) ≤ normalizer (S : Set G) :=
    (perfRes_le _).trans (centralizer_le_normalizer _)
  have hn : ((perfRes (centralizer (S : Set G))).subgroupOf (normalizer (S : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLN).mpr
      (normalizer_le_normalizer_perfRes_centralizer S)
  exact G3a.fusionIsSylowIn_inf (fusionIsSylowIn_normalizer T hST hS) hLN hn.isSubnormal

theorem stronglyClosed_inf_inf_perfRes (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    IsMulCommutative (S ⊓ perfRes (centralizer (S : Set G)) : Subgroup G) ∧
      fusionStronglyClosed ((S ⊓ perfRes (centralizer (S : Set G)) : Subgroup G) : Set G) T := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha g hg => ?_⟩
  · exact mem_centralizer_iff.mp (perfRes_le _ (mem_inf.mp b.2).2) a (mem_inf.mp a.2).1
  · have hR := stronglyClosed_inf_perfRes T hST hS
    have haR : a ∈ (T : Subgroup G) ⊓ perfRes (centralizer (S : Set G)) :=
      mem_inf.mpr ⟨hST (mem_inf.mp ha).1, (mem_inf.mp ha).2⟩
    exact mem_inf.mpr ⟨hS a (mem_inf.mp ha).1 g hg, (mem_inf.mp (hR a haR g hg)).2⟩

theorem normal_inf_perfRes
    (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hO : goldschmidtOddCore G = ⊥) :
    (S ⊓ perfRes (centralizer (S : Set G))).Normal := by
  set L := perfRes (centralizer (S : Set G)) with hL
  set A := S ⊓ L with hA
  obtain ⟨hAab, hAcl⟩ := stronglyClosed_inf_inf_perfRes T hST hS
  have hAT : A ≤ T := inf_le_left.trans hST
  have hLA : L ≤ centralizer (A : Set G) :=
    (perfRes_le _).trans (centralizer_le inf_le_left)
  have hLM := le_centralizer_normalClosure T hAT hAab hAcl hO (commutator_perfRes _) hLA
  have hle := normalClosure_le_of_le_centralizer T hAT hAcl (inf_le_right.trans hLM)
  have heq : normalClosure (A : Set G) = A := le_antisymm hle le_normalClosure
  rw [← heq]
  exact normalClosure_normal

theorem le_of_le_centralizer_of_odd (hO : goldschmidtOddCore G = ⊥) {Q A : Subgroup G}
    (hQ : Q.Normal) (hQA : Q ≤ centralizer (A : Set G)) (hA2 : IsPGroup 2 A)
    (hodd : Odd (A.subgroupOf Q).index) : Q ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Q.Normal := hQ
  set N := A.subgroupOf Q with hN
  have hNc : ∀ n ∈ N, ∀ q : Q, q * n = n * q := by
    intro n hn q
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hQA q.2) n (mem_subgroupOf.mp hn)).symm
  have hNn : N.Normal := ⟨fun n hn q => by
    have e : q * n * q⁻¹ = n := by rw [hNc n hn q]; group
    rw [e]
    exact hn⟩
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    obtain ⟨k, hk⟩ := (hA2.comap_subtype (K := Q) : IsPGroup 2 N).exists_card_eq
    have hk' : Nat.card N = 2 ^ k := hk
    rw [hk']
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime hcop
  have hKodd : Odd (Nat.card K) := by
    rw [← hK.symm.index_eq_card]
    exact hodd
  have hKn : K.Normal := by
    refine ⟨fun k hk q => ?_⟩
    have hq : q ∈ ((N ⊔ K : Subgroup Q) : Set Q) := by rw [hK.sup_eq_top]; trivial
    rw [normal_mul] at hq
    obtain ⟨n, hn, k₀, hk₀, rfl⟩ := hq
    have e : n * k₀ * k * (n * k₀)⁻¹ = k₀ * k * k₀⁻¹ := by
      rw [mul_inv_rev, ← mul_assoc]
      calc n * k₀ * k * k₀⁻¹ * n⁻¹ = n * (k₀ * k * k₀⁻¹) * n⁻¹ := by group
        _ = (k₀ * k * k₀⁻¹) * n * n⁻¹ := by rw [hNc n hn]
        _ = k₀ * k * k₀⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem hk₀ hk) (K.inv_mem hk₀)
  have hKO : K ≤ goldschmidtOddCore Q := le_oddCore hKn hKodd
  rw [oddCore_eq_bot_of_normal (N := Q) hO, le_bot_iff] at hKO
  have hNtop : N = ⊤ := by
    have h := hK.sup_eq_top
    rwa [hKO, sup_bot_eq] at h
  intro x hx
  have : (⟨x, hx⟩ : Q) ∈ N := hNtop ▸ mem_top _
  exact mem_subgroupOf.mp this

end CFSG.Goldschmidt75
