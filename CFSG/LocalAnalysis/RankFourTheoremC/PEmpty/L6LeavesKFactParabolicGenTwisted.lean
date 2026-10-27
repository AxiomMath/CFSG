module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenDatum
public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChIJK Subgroup
open scoped Pointwise

theorem graphFixed_isSplitBNPair
    (t : TwistTag) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) [CharP K p] (σ : K ≃+* K) :
    IsSplitBNPair p ((graphFixedRootBorel t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom))
      ((graphFixedRootMonomial t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom)) ∧
      graphFixedRootMonomial t K σ.toRingHom ≤ graphFixedRootBorel t K σ.toRingHom ⊔
        Subgroup.closure (Set.range fun a => canonicalRep (coxeterSystem t.tag) K
          (t.orbitReflection a)) ∧
      ¬ p ∣ Nat.card (graphFixedRootTorus t K σ.toRingHom) ∧
      graphFixedRootBorel t K σ.toRingHom ⊓ graphFixedRootMonomial t K σ.toRingHom =
        graphFixedRootTorus t K σ.toRingHom ∧
      IsPGroup p (graphFixedPosUnipotent t K σ.toRingHom) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL t.tag K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup t K σ.toRingHom) := inferInstance
  obtain ⟨hBeq, -, huniq, -, hUB, hUn, -, -, -, -, -, -, hΓgen, -⟩ :=
    fixed_root_Bruhat_decomposition t K σ
  obtain ⟨hmonN, -, hker, hHnorm, -, -, hNeq⟩ := fixed_root_monomial_quotient t K σ.toRingHom
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  obtain ⟨hw₀rel, hn₀N, -, -, hBinter, -, -, hNB⟩ := fixed_Borel_self_normalizers t K σ w₀ hw₀
  have hBΓ : graphFixedRootBorel t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedRootBorel_le t K σ.toRingHom
  have hNΓ : graphFixedRootMonomial t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedRootMonomial_le t K σ.toRingHom
  have hHB : graphFixedRootTorus t K σ.toRingHom ≤ graphFixedRootBorel t K σ.toRingHom :=
    graphFixedRootTorus_le_graphFixedRootBorel
  have hHN : graphFixedRootTorus t K σ.toRingHom ≤ graphFixedRootMonomial t K σ.toRingHom :=
    le_inf (inf_le_left.trans (graphFixedTorus_le_graphFixedMonomial t K σ.toRingHom)) inf_le_right
  have hBN : graphFixedRootBorel t K σ.toRingHom ⊓ graphFixedRootMonomial t K σ.toRingHom =
      graphFixedRootTorus t K σ.toRingHom := by
    refine le_antisymm (fun g hg => ?_) (le_inf hHB hHN)
    obtain ⟨hgB, hgN⟩ := Subgroup.mem_inf.1 hg
    have hg1 : g ∈ borelGroup t.tag K ⊓ monomialSubgroup t.tag K :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hgB).1).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hgN).1).1⟩
    rw [(borel_weyl_intersection t.tag K).1] at hg1
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg1, (Subgroup.mem_inf.1
      (Subgroup.mem_inf.1 hgB).1).2⟩, (Subgroup.mem_inf.1 hgB).2⟩
  have hHp : ¬ p ∣ Nat.card (graphFixedRootTorus t K σ.toRingHom) := by
    intro hd
    refine not_dvd_card_torusGroup (τ := t.tag) (K := K) p
      (hd.trans (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)))
  have hcell1 : ∀ x ∈ graphFixedRootBorel t K σ.toRingHom,
      x ∈ graphFixedRootBruhatCell t K σ.toRingHom 1 := fun x hx =>
    mem_graphFixedRootBruhatCell.2 ⟨x, hx, 1, one_mem _, by simp [canonicalRep_one]⟩
  have hsB : ∀ a, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∉
      graphFixedRootBorel t K σ.toRingHom := by
    intro a hB
    have h1 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) :=
      mem_graphFixedRootBruhatCell.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
    exact Set.disjoint_left.1 (disjoint_graphFixedRootBruhatCell
      (t := t) (K := K) (σ := σ.toRingHom) (Ne.symm (t.orbitReflection_ne_one a)))
      (hcell1 _ hB) h1
  have hs2H : ∀ a, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        graphFixedRootTorus t K σ.toRingHom := by
    intro a
    have hsN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom
      (t.orbitReflection_mem a)
    have hmem : (⟨_, hsN⟩ : graphFixedRootMonomial t K σ.toRingHom) * ⟨_, hsN⟩ ∈
        (graphFixedRootWeylHom t K σ.toRingHom).ker := by
      rw [MonoidHom.mem_ker, map_mul, graphFixedRootWeylHom_canonicalRep t K σ.toRingHom
        (t.orbitReflection_mem a)]
      exact t.orbitReflection_mul_self a
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  have hS3 : ∀ s ∈ Set.range (fun a => canonicalRep (coxeterSystem t.tag) K
      (t.orbitReflection a)), ∀ w ∈ graphFixedRootMonomial t K σ.toRingHom,
      ∀ b ∈ graphFixedRootBorel t K σ.toRingHom,
      ∃ b₁ ∈ graphFixedRootBorel t K σ.toRingHom, ∃ b₂ ∈ graphFixedRootBorel t K σ.toRingHom,
        s * b * w = b₁ * w * b₂ ∨ s * b * w = b₁ * (s * w) * b₂ := by
    rintro _ ⟨a, rfl⟩ w hw b hb
    beta_reduce
    have hraW : t.orbitReflection a ∈ relWeylTwist t := t.orbitReflection_mem a
    have hsN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hraW
    obtain ⟨wb, hwb⟩ : ∃ wb, graphFixedRootWeylHom t K σ.toRingHom ⟨w, hw⟩ = wb := ⟨_, rfl⟩
    have hwbW : wb ∈ relWeylTwist t := by
      rw [← graphFixedRootWeylHom_range t K σ.toRingHom]
      exact ⟨⟨w, hw⟩, hwb⟩
    have hnN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hwbW
    have hh' : (canonicalRep (coxeterSystem t.tag) K wb)⁻¹ * w ∈
        graphFixedRootTorus t K σ.toRingHom := by
      have hmem : (⟨canonicalRep (coxeterSystem t.tag) K wb, hnN⟩ :
          graphFixedRootMonomial t K σ.toRingHom)⁻¹ * ⟨w, hw⟩ ∈
            (graphFixedRootWeylHom t K σ.toRingHom).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, graphFixedRootWeylHom_canonicalRep t K
          σ.toRingHom hwbW, hwb]
        simp
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.1 hmem
    have hrwW : t.orbitReflection a * wb ∈ relWeylTwist t := mul_mem hraW hwbW
    have hmN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hrwW
    have hh'' : (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * wb))⁻¹ *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * w) ∈
          graphFixedRootTorus t K σ.toRingHom := by
      have hmem : (⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * wb), hmN⟩ :
          graphFixedRootMonomial t K σ.toRingHom)⁻¹ *
            (⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a), hsN⟩ * ⟨w, hw⟩) ∈
              (graphFixedRootWeylHom t K σ.toRingHom).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, graphFixedRootWeylHom_canonicalRep t K
          σ.toRingHom hrwW, graphFixedRootWeylHom_canonicalRep t K σ.toRingHom hraW, hwb]
        simp
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.1 hmem
    have hmemprod : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) *
          graphFixedRootBruhatCell t K σ.toRingHom wb :=
      Set.mul_mem_mul (mem_graphFixedRootBruhatCell.2 ⟨1, one_mem _, b, hb, by simp⟩)
        (mem_graphFixedRootBruhatCell.2 ⟨1, one_mem _, _, hHB hh', by simp⟩)
    obtain ⟨hmul1, hmul2, hmul3, -⟩ := fixed_simple_Bruhat_multiplication t K σ
    have hcase1 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a * wb) →
        ∃ b₁ ∈ graphFixedRootBorel t K σ.toRingHom, ∃ b₂ ∈ graphFixedRootBorel t K σ.toRingHom,
          canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w =
            b₁ * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * w) * b₂ := by
      intro hx
      obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_graphFixedRootBruhatCell.1 hx
      generalize canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * wb) = m at hh'' he
      refine ⟨b₁, hb₁, (m⁻¹ * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * w))⁻¹
        * b₂, mul_mem (inv_mem (hHB hh'')) hb₂, ?_⟩
      rw [← he]
      group
    have hcase2 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w ∈
        graphFixedRootBruhatCell t K σ.toRingHom wb →
        ∃ b₁ ∈ graphFixedRootBorel t K σ.toRingHom, ∃ b₂ ∈ graphFixedRootBorel t K σ.toRingHom,
          canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w = b₁ * w * b₂ := by
      intro hx
      obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_graphFixedRootBruhatCell.1 hx
      generalize canonicalRep (coxeterSystem t.tag) K wb = n at hh' he
      refine ⟨b₁, hb₁, (n⁻¹ * w)⁻¹ * b₂, mul_mem (inv_mem (hHB hh')) hb₂, ?_⟩
      rw [← he]
      group
    rcases forall_height_pos_or_forall_height_neg (inv_mem hwbW) a with hp | hn
    · have hlen := (length_orbitReflection_mul_of_pos t hwbW hp).1
      rw [hmul2 wb hwbW a hlen] at hmemprod
      obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hcase1 hmemprod
      exact ⟨b₁, hb₁, b₂, hb₂, Or.inr h⟩
    · have hlen := (length_orbitReflection_mul_of_neg t hwbW hn).1
      rw [hmul3 wb hwbW a hlen] at hmemprod
      rcases hmemprod with hx | hx
      · obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hcase1 hx
        exact ⟨b₁, hb₁, b₂, hb₂, Or.inr h⟩
      · obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hcase2 hx
        exact ⟨b₁, hb₁, b₂, hb₂, Or.inl h⟩
  have hS4 : ∀ s ∈ Set.range (fun a => canonicalRep (coxeterSystem t.tag) K
      (t.orbitReflection a)), ∃ b ∈ graphFixedRootBorel t K σ.toRingHom,
        s * b * s ∉ graphFixedRootBorel t K σ.toRingHom := by
    rintro _ ⟨a, rfl⟩
    beta_reduce
    by_contra hcon
    push Not at hcon
    apply hsB a
    have hs2 := hs2H a
    have hsN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom
      (t.orbitReflection_mem a)
    have hnorm : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        Subgroup.normalizer (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) := by
      generalize canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) = n at hs2 hcon
      refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · have e : n * x * n⁻¹ = (n * x * n) * (n * n)⁻¹ := by group
        rw [e]
        exact (graphFixedRootBorel t K σ.toRingHom).mul_mem (hcon x hx)
          ((graphFixedRootBorel t K σ.toRingHom).inv_mem (hHB hs2))
      · have e : x = (n * n)⁻¹ * (n * (n * x * n⁻¹) * n) := by group
        rw [e]
        exact (graphFixedRootBorel t K σ.toRingHom).mul_mem
          ((graphFixedRootBorel t K σ.toRingHom).inv_mem (hHB hs2)) (hcon _ hx)
    have : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        graphFixedRootGroup t K σ.toRingHom ⊓
          Subgroup.normalizer (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) :=
      Subgroup.mem_inf.2 ⟨hNΓ hsN, hnorm⟩
    rw [hNB] at this
    exact this
  have hUp : IsPGroup p (graphFixedPosUnipotent t K σ.toRingHom) :=
    IsPGroup.to_le (((positive_root_triangularity.{0, 0} t.tag).2 K p).2.1) inf_le_left
  have hUH0 : graphFixedPosUnipotent t K σ.toRingHom ⊓ graphFixedRootTorus t K σ.toRingHom =
      ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxH⟩ := Subgroup.mem_inf.1 hx
    have := huniq x hxH 1 (one_mem _) 1 (one_mem _) x hxU (by simp)
    exact Subgroup.mem_bot.2 this.1
  have hUN : graphFixedPosUnipotent t K σ.toRingHom ⊓ graphFixedRootMonomial t K σ.toRingHom =
      ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
    have hxH : x ∈ graphFixedRootTorus t K σ.toRingHom := by
      rw [← hBN]
      exact Subgroup.mem_inf.2 ⟨graphFixedPosUnipotent_le_graphFixedRootBorel hxU, hxN⟩
    rw [← hUH0]
    exact Subgroup.mem_inf.2 ⟨hxU, hxH⟩
  have hUHB : graphFixedPosUnipotent t K σ.toRingHom ⊔ graphFixedRootTorus t K σ.toRingHom =
      graphFixedRootBorel t K σ.toRingHom := by
    refine le_antisymm (sup_le graphFixedPosUnipotent_le_graphFixedRootBorel hHB) fun b hb => ?_
    have hb' : b ∈ (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) := by
      rw [← hBeq]
      exact hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu)
  have hsat : (⨅ n ∈ graphFixedRootMonomial t K σ.toRingHom, CFSG.conjugate
      (graphFixedRootBorel t K σ.toRingHom) n) = graphFixedRootBorel t K σ.toRingHom ⊓
        graphFixedRootMonomial t K σ.toRingHom := by
    refine burnsideI2BN_sat_of_opposite ?_ hn₀N ?_
    · rw [hBN]
      exact hHnorm
    · intro z hz hz'
      have hzT : z ∈ graphFixedRootTorus t K σ.toRingHom := by
        rw [← hBinter]
        refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
        refine ⟨_, hz', ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      exact hHN hzT
  have hBNpair : IsSplitBNPair p ((graphFixedRootBorel t K σ.toRingHom).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom))
      ((graphFixedRootMonomial t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom)) := by
    refine burnsideI2BN_isSplit_sub (Γ := graphFixedRootGroup t K σ.toRingHom)
      (B := graphFixedRootBorel t K σ.toRingHom) (N := graphFixedRootMonomial t K σ.toRingHom)
      (U := graphFixedPosUnipotent t K σ.toRingHom)
      (S := Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) hp
      hBΓ hNΓ hΓgen.symm (by rw [hBN]; exact hHnorm) ?_ ?_ hS3 hS4
      graphFixedPosUnipotent_le_graphFixedRootBorel hUn hUp hUN ?_ hsat
      (by rw [hBN]; exact hHp)
    · rintro _ ⟨a, rfl⟩
      exact ⟨canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom (t.orbitReflection_mem a),
        hsB a, by rw [pow_two]; exact hHB (hs2H a)⟩
    · rw [hBN, sup_comm]
      exact hNeq.symm
    · rw [hBN]
      exact hUHB
  refine ⟨hBNpair, ?_, hHp, hBN, hUp⟩
  exact hNeq.le.trans (sup_le (hHB.trans le_sup_left) le_sup_right)

theorem parFam_graphFixed
    (t : TwistTag) (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ∃ Fam : ParFam ↥(graphFixedRootGroup t K σ.toRingHom) (Fin t.foldedTag.rank),
      Fam.Q = fun a => (graphFixedParabolicRadical t K σ.toRingHom {a}).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom) := by
  obtain ⟨hBN, hNle, hHp, hBNinter, hUp⟩ := graphFixed_isSplitBNPair t K Nat.prime_two σ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL t.tag K) := finite_modGL
  have hrank : 2 ≤ t.foldedTag.rank := by cases t <;> decide
  haveI : Nonempty (Fin t.foldedTag.rank) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin t.foldedTag.rank) := Fin.nontrivial_iff_two_le.mpr hrank
  have hBΓ : graphFixedRootBorel t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedRootBorel_le t K σ.toRingHom
  have hradΓ : ∀ a : Fin t.foldedTag.rank, graphFixedParabolicRadical t K σ.toRingHom {a} ≤
      graphFixedRootGroup t K σ.toRingHom := fun a =>
    graphFixedParabolicRadical_le_graphFixedRootGroup t K σ.toRingHom {a}
  have hrad_pos : ∀ a : Fin t.foldedTag.rank, graphFixedParabolicRadical t K σ.toRingHom {a} ≤
      graphFixedPosUnipotent t K σ.toRingHom := fun a =>
    graphFixedParabolicRadical_le_graphFixedPosUnipotent {a}
  have hnorm : ∀ a : Fin t.foldedTag.rank, graphFixedParabolic t K σ.toRingHom {a} ≤
      normalizer ((graphFixedParabolicRadical t K σ.toRingHom {a} : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) := fun a => by
    have h := diagram_fixed_parabolic_root_radical_normalizers t K σ {a}
    rw [← h]
    exact inf_le_right
  refine exists_parFam_of_bn_family
    (B := (graphFixedRootBorel t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom))
    (hBN.exists_sylow_normalizer Nat.prime_two)
    (fun a => ⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a),
      canonicalRep_orbitReflection_mem_graphFixedRootGroup a⟩)
    (fun a => (graphFixedParabolicRadical t K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom)) ?_ ?_ ?_ ?_ ?_ ?_
  · have hN : (graphFixedRootMonomial t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom) ≤
        (graphFixedRootBorel t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom) ⊔
          ⨆ a : Fin t.foldedTag.rank, zpowers
            (⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a),
              canonicalRep_orbitReflection_mem_graphFixedRootGroup a⟩ :
                ↥(graphFixedRootGroup t K σ.toRingHom)) := by
      intro x hx
      have hx1 : (x : ModGL t.tag K) ∈ graphFixedRootBorel t K σ.toRingHom ⊔
          Subgroup.closure (Set.range fun a => canonicalRep (coxeterSystem t.tag) K
            (t.orbitReflection a)) := hNle hx
      have hle : graphFixedRootBorel t K σ.toRingHom ⊔ Subgroup.closure
          (Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) ≤
          ((graphFixedRootBorel t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom) ⊔
            ⨆ a : Fin t.foldedTag.rank, zpowers
              (⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a),
                canonicalRep_orbitReflection_mem_graphFixedRootGroup a⟩ :
                  ↥(graphFixedRootGroup t K σ.toRingHom))).map
            (graphFixedRootGroup t K σ.toRingHom).subtype := by
        refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
        · intro b hb
          exact ⟨⟨b, hBΓ hb⟩, Subgroup.mem_sup_left hb, rfl⟩
        · rintro _ ⟨a, rfl⟩
          exact ⟨_, Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem a
            (Subgroup.mem_zpowers _)), rfl⟩
      obtain ⟨y, hy, hyx⟩ := hle hx1
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
    rw [eq_top_iff, ← hBN.gen]
    exact sup_le le_sup_left hN
  · intro a
    exact (hUp.to_le (hrad_pos a)).comap_subtype
  · intro a hbot
    obtain ⟨a', ha'⟩ := exists_ne a
    have hx : (orbitX t K σ.toRingHom a' 1 : ModGL t.tag K) ∈
        graphFixedParabolicRadical t K σ.toRingHom {a} :=
      orbitX_mem_graphFixedParabolicRadical (fun h => ha' (Set.mem_singleton_iff.mp h)) 1
    have h := Subgroup.map_subgroupOf_eq_of_le (hradΓ a)
    rw [hbot, Subgroup.map_bot] at h
    rw [← h] at hx
    exact orbitX_one_ne_one (σ := σ.toRingHom) a' (Subgroup.mem_bot.mp hx)
  · intro a
    exact Subgroup.subgroupOf_mono _
      ((hrad_pos a).trans graphFixedPosUnipotent_le_graphFixedRootBorel)
  · intro a x hx
    have hx' : (x : ModGL t.tag K) ∈ graphFixedRootBorel t K σ.toRingHom := hx
    have h1 : (x : ModGL t.tag K) ∈ normalizer
        ((graphFixedParabolicRadical t K σ.toRingHom {a} : Subgroup (ModGL t.tag K)) :
          Set (ModGL t.tag K)) :=
      hnorm a (graphFixedRootBorel_le_graphFixedParabolic t K σ.toRingHom {a} hx')
    exact mem_normalizer_subgroupOf (hradΓ a) x.2 h1
  · intro a
    have h1 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ normalizer
        ((graphFixedParabolicRadical t K σ.toRingHom {a} : Subgroup (ModGL t.tag K)) :
          Set (ModGL t.tag K)) :=
      hnorm a (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, Set.mem_singleton a, rfl⟩))
    exact mem_normalizer_subgroupOf (hradΓ a)
      (canonicalRep_orbitReflection_mem_graphFixedRootGroup a) h1


theorem hasParGen_of_twistedChevalleyModel
    {G : Type} [Group G] [Finite G] {t : TwistTag} {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel G t (2 ^ f)) : HasParGen G := by
  obtain ⟨K, hK, hKf, hcard, σ, hσ, ⟨e⟩⟩ := h
  have hord := two_le_order_twistTag t
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two (f := f * t.order)
    (Nat.mul_pos hf (by omega)) (by rw [hcard, pow_mul])
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩, RingHom.ext fun _ => rfl⟩
  have h3 := (finite_fixed_root_group_perfect t Nat.prime_two hf K hcard σ'.toRingHom hσ).2.2.1
  obtain ⟨Fam, -⟩ := parFam_graphFixed t K σ'
  obtain ⟨hBN, -, hHp, hBNinter, -⟩ := graphFixed_isSplitBNPair t K Nat.prime_two σ'
  haveI : Finite (ModGL t.tag K) := finite_modGL
  have hodd : ∀ x ∈ center ↥(graphFixedRootGroup t K σ'.toRingHom), Odd (orderOf x) := by
    intro x hx
    have hx1 : x ∈ ((graphFixedRootBorel t K σ'.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ'.toRingHom)) ⊓
        ((graphFixedRootMonomial t K σ'.toRingHom).subgroupOf
          (graphFixedRootGroup t K σ'.toRingHom)) := burnsideI2BN_center_le hBN hx
    have hxT : (x : ModGL t.tag K) ∈ graphFixedRootTorus t K σ'.toRingHom := by
      rw [← hBNinter]
      exact ⟨hx1.1, hx1.2⟩
    have hdvd : orderOf (⟨(x : ModGL t.tag K), hxT⟩ : graphFixedRootTorus t K σ'.toRingHom) ∣
        Nat.card (graphFixedRootTorus t K σ'.toRingHom) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    rw [← Subgroup.orderOf_coe]
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    exact hHp ((even_iff_two_dvd.mp hne).trans hdvd)
  let eC : ↥(graphFixedRootGroup t K σ'.toRingHom) ≃*
      ↥⁅twistedFixedGroup t K σ'.toRingHom, twistedFixedGroup t K σ'.toRingHom⁆ :=
    (MulEquiv.subgroupCongr h3).symm
  have hpg := hasParGen_of_mulEquiv eC Fam.hasParGen
  have hodd' : ∀ x ∈ center ↥⁅twistedFixedGroup t K σ'.toRingHom,
      twistedFixedGroup t K σ'.toRingHom⁆, Odd (orderOf x) := by
    intro x hx
    have hxc : eC.symm x ∈ center ↥(graphFixedRootGroup t K σ'.toRingHom) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      apply eC.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx (eC g)
    have := hodd _ hxc
    rwa [MulEquiv.orderOf_eq] at this
  have hq := hasParGen_of_surjective
    (QuotientGroup.mk' (center ↥⁅twistedFixedGroup t K σ'.toRingHom,
      twistedFixedGroup t K σ'.toRingHom⁆))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (fun x hx => hodd' x (by rwa [QuotientGroup.ker_mk'] at hx)) hpg
  exact hasParGen_of_mulEquiv e.symm hq

theorem hasParGen_of_chevalleyExceptionalModel_twisted
    {G : Type} [Group G] [Finite G] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {f : ℕ}
    (h : ChevalleyExceptionalModel G t 2 f) (ht : t = .twistedE6 ∨ t = .trialityD4) :
    HasParGen G := by
  obtain ⟨hadm, hmodel⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  rcases ht with rfl | rfl
  · exact hasParGen_of_twistedChevalleyModel hf hmodel
  · exact hasParGen_of_twistedChevalleyModel hf hmodel

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
