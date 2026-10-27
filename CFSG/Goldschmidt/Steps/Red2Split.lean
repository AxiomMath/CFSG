module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.Red2
import CFSG.Goldschmidt.Steps.Red2Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification CFSG.Goldschmidt.Red2
open CFSG.RankThreeCoreUniqueness.Helpers (pCore_isPGroup pCore_normal pCore_eq_sSup)

private theorem N22_one {G : Type} [Group G] [Finite G] {A K : Subgroup G} (hKn : K.Normal)
    (hK : IsComponentOf K ⊤)
    (hidx : Nat.card G ≤ ((Subgroup.centralizer (K : Set G)).subgroupOf (K ⊔ A)).index) :
    (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a) ∨
    (∃ K : Subgroup G, IsComponentOf K ⊤ ∧ K.Normal ∧ IsSimpleGroup K ∧ K ⊔ A = ⊤ ∧
      Subgroup.centralizer (K : Set G) = ⊥ ∧ ¬ A ≤ K) := by
  set H : Subgroup G := K ⊔ A with hHdef
  set C : Subgroup H := (Subgroup.centralizer (K : Set G)).subgroupOf H with hCdef
  have h1 : C.index ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos C.index_dvd_card
  have h2 : Nat.card H ≤ Nat.card G := H.card_le_card_group
  have hHtop : H = ⊤ := (Subgroup.card_eq_iff_eq_top H).mp (by omega)
  have hC : C = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h3 := C.card_mul_index
    have h4 : C.index = Nat.card H := by omega
    rw [h4] at h3
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h3.trans (one_mul _).symm)
  have hcent : Subgroup.centralizer (K : Set G) = ⊥ := by
    have hdisj := Subgroup.subgroupOf_eq_bot.mp hC
    rw [hHtop] at hdisj
    exact disjoint_top.mp hdisj
  have hZK : Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : (z : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
    rw [hcent, Subgroup.mem_bot] at hzc
    exact Subgroup.mem_bot.mpr (Subtype.ext hzc)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hKs : IsSimpleGroup K :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZK.symm)).isSimpleGroup
  by_cases hAK : A ≤ K
  · left
    have hKtop : K = ⊤ := by
      rw [← hHtop]
      exact le_antisymm le_sup_left (sup_le le_rfl hAK)
    let e : G ≃* K := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hKtop.symm)
    refine ⟨e.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨(a' : G), (b' : G), fun h => hab ?_⟩
    have h' : a' * b' = b' * a' := Subtype.ext h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']
  · right
    exact ⟨K, hK, hKn, hKs, hHtop, hcent, hAK⟩

private theorem N22_layer (h19 : S_N19) {G : Type} [Group G] [Finite G] {S : Sylow 2 G}
    {A : Subgroup G} (hA : CoreHyp G S A) (hIH : IH (Nat.card G))
    (hE : goldschmidtLayer G ≠ ⊥)
    (hall : ∀ K : Subgroup G, IsComponentOf K ⊤ →
      ((Subgroup.centralizer (K : Set G)).subgroupOf (K ⊔ A)).index < Nat.card G) :
    CFSG.Open.pCore 2 G ⊔ goldschmidtLayer G = ⊤ ∧
      Subgroup.centralizer (goldschmidtLayer G : Set G) = CFSG.Open.pCore 2 G := by
  have hO := hA.oddCore
  set E := goldschmidtLayer G with hEdef
  set 𝒦 : Set (Subgroup G) := {K | IsComponentOf K ⊤} with h𝒦def
  have hE𝒦 : E = sSup 𝒦 := rfl
  have hEn : E.Normal := Layer.normal G
  set CE := Subgroup.centralizer (E : Set G) with hCEdef
  have hCEn : CE.Normal := Subgroup.normal_centralizer
  have hcomm : ∀ K ∈ 𝒦, ∀ L ∈ 𝒦, K ≠ L → K ≤ Subgroup.centralizer (L : Set G) :=
    fun K hK L hL hne => component_le_centralizer hK hL hne
  have hAEC : A ≤ E ⊔ CE := by
    intro a ha
    have hg : ∀ K ∈ 𝒦, ∃ x ∈ K, a * x⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      intro K hK
      obtain ⟨t, ht, -, hconj⟩ :=
        (N21_of h19 (Nat.card G) hIH G S A hA K hK (hall K hK)).2.1 a ha
      exact ⟨t, ht.2, mul_inv_mem_centralizer_of_conj_eq hconj⟩
    obtain ⟨y, hy, hyc⟩ := exists_mem_iSup_mul_inv_mem_centralizer 𝒦 (Set.toFinite 𝒦) hcomm
      (fun K => K) (fun _ _ => le_rfl) a hg
    have hyE : y ∈ E := by
      rw [hE𝒦, sSup_eq_iSup]
      exact hy
    have hayc : a * y⁻¹ ∈ CE := mem_centralizer_sSup hyc
    have hay : a = a * y⁻¹ * y := by group
    rw [hay]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hayc) (Subgroup.mem_sup_left hyE)
  have hECE : E ⊔ CE = ⊤ := by
    rw [eq_top_iff, ← hA.gen]
    exact Subgroup.normalClosure_le_normal hAEC
  have hd := N8d G hO
  have hZE : E ⊓ CE ≤ CFSG.Open.pCore 2 G := by
    intro z hz
    obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.mp hz
    apply hd.2.1
    have hzZ : (⟨z, hzE⟩ : E) ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
    exact ⟨⟨z, hzE⟩, hzZ, rfl⟩
  have h2 : IsPGroup 2 (E ⊓ CE : Subgroup G) := (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).to_le hZE
  have hcommEC : ∀ z ∈ E, z ∈ CE → ∀ c ∈ CE, c * z = z * c :=
    fun z hz _ c hc => (Subgroup.mem_centralizer_iff.mp hc z hz).symm
  have hOq : goldschmidtOddCore (G ⧸ E) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot_of_sup E CE hO hECE hcommEC h2
  set f : CE →* G ⧸ E := (QuotientGroup.mk' E).comp CE.subtype with hfdef
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E q
    have hg : g ∈ E ⊔ CE := by
      rw [hECE]
      exact Subgroup.mem_top g
    obtain ⟨e, he, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [hfdef, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa [mul_assoc] using hEn.conj_mem e he c⁻¹
  have hfker : f.ker ≤ Subgroup.center CE := by
    intro k hk
    have hkE : (k : G) ∈ E := by
      rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      exact hk
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 k hkE).symm
  have hCElayer : Layer.subgroup CE = ⊥ := by
    rw [Layer.subgroup, sSup_eq_bot]
    intro L hL
    exfalso
    have hL' := LocalComponents.of_subnormal_subgroup CE
      (Components.chain_of_mathlib_subnormal hCEn.isSubnormal) L hL
    have hL'E : L.map CE.subtype ≤ E := Layer.component_le hL'
    have hL'C : L.map CE.subtype ≤ CE := Subgroup.map_subtype_le L
    have : Group.IsPerfect (L.map CE.subtype) := ⟨hL'.2.2.1⟩
    have : Nontrivial (L.map CE.subtype) := Quasisimple.nontrivial hL'.2.2
    apply Group.IsPerfect.not_isMulCommutative (L.map CE.subtype)
    exact ⟨⟨fun x y => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hL'C x.2) y (hL'E y.2)).symm⟩⟩
  have hlayerq : goldschmidtLayer (G ⧸ E) = ⊥ := by
    change Layer.subgroup (G ⧸ E) = ⊥
    rw [← CentralComponentQuotients.layer_map f hf hfker, hCElayer, Subgroup.map_bot]
  obtain ⟨Sb, hSb, hclb⟩ :=
    CFSG.ShultStronglyClosedTI.quotient_stronglyClosed S A E hA.le hA.closed
  have hAb : A.map (QuotientGroup.mk' E) ≤ Sb := by
    rw [hSb]
    exact Subgroup.map_mono hA.le
  have hcardq : Nat.card (G ⧸ E) < Nat.card G := by
    have h1 := E.card_mul_index
    have h3 : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot E).mpr hE
    have h4 : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [← Subgroup.index_eq_card]
    nlinarith
  obtain ⟨hq1, -, -⟩ := hIH (G ⧸ E) hcardq Sb _ hAb (isMulCommutative_map hA.comm _) hclb
    (normalClosure_map_eq_top hA.gen _ (QuotientGroup.mk'_surjective E)) hOq
  rw [hlayerq, sup_bot_eq] at hq1
  have hq2 : IsPGroup 2 (⊤ : Subgroup (G ⧸ E)) := hq1 ▸ CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2
  have hCE2 : IsPGroup 2 CE := by
    intro c
    obtain ⟨m, hm⟩ := hq2 ⟨QuotientGroup.mk' E c, Subgroup.mem_top _⟩
    have hm' : (c : G) ^ 2 ^ m ∈ E := by
      have h1 := congrArg Subtype.val hm
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨j, hj⟩ := h2 ⟨(c : G) ^ 2 ^ m, hm', CE.pow_mem c.2 _⟩
    refine ⟨m + j, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, h1]
  have hCEle : CE ≤ CFSG.Open.pCore 2 G := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
    exact le_sSup ⟨hCEn, hCE2⟩
  have hle : CFSG.Open.pCore 2 G ≤ CE := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := G) 2).isNilpotent
    have hsolv := Layer.commutes_with_solvable_subnormal (CFSG.Open.pCore 2 G)
      (Components.chain_of_mathlib_subnormal (CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2).isSubnormal)
    rw [Subgroup.commutator_comm] at hsolv
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hsolv
  have hCEeq : CE = CFSG.Open.pCore 2 G := le_antisymm hCEle hle
  refine ⟨?_, hCEeq⟩
  rw [← hCEeq, sup_comm]
  exact hECE

theorem N22_of (h19 : S_N19) : S_N22 := by
  intro G _ _ S A hA hIH hE
  by_cases hall : ∀ K : Subgroup G, IsComponentOf K ⊤ →
      ((Subgroup.centralizer (K : Set G)).subgroupOf (K ⊔ A)).index < Nat.card G
  · exact Or.inr (Or.inr ⟨hall, N22_layer h19 hA hIH hE hall⟩)
  · push Not at hall
    obtain ⟨K, hK, hidx⟩ := hall
    have hKn := (h19 G S A hA.le hA.comm hA.closed hA.gen K hK).1
    rcases N22_one hKn hK hidx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end CFSG.Goldschmidt
