module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveThree
import CFSG.RankThree.Transfer.PGroup
import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

theorem mem_of_pow_mem_of_coprime' {G : Type*} [Group G] {H : Subgroup G} {g : G} {i j : ℕ}
    (hij : Nat.Coprime i j) (hi : g ^ i ∈ H) (hj : g ^ j ∈ H) : g ∈ H := by
  have h := Nat.gcd_eq_gcd_ab i j
  rw [hij.gcd_eq_one, Nat.cast_one] at h
  have e : g = (g ^ i) ^ (Nat.gcdA i j) * (g ^ j) ^ (Nat.gcdB i j) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact mul_mem (zpow_mem hi _) (zpow_mem hj _)

variable {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem isCyclic_of_comm_mem_frattini (T : Sylow p K)
    (hirr : ∀ V : Subgroup K, V ≤ T →
      ¬ V ≤ (frattini ↥(T : Subgroup K)).map (T : Subgroup K).subtype →
      Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
        V = T)
    (htriv : ∀ g ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ (T : Subgroup K),
      g * t * g⁻¹ * t⁻¹ ∈ (frattini ↥(T : Subgroup K)).map (T : Subgroup K).subtype) :
    IsCyclic ↥(T : Subgroup K) := by
  set Φm := (frattini ↥(T : Subgroup K)).map (T : Subgroup K).subtype with hΦm
  by_cases hΦ : (T : Subgroup K) ≤ Φm
  ·
    have htop : frattini ↥(T : Subgroup K) = ⊤ := by
      rw [eq_top_iff]
      intro t _
      obtain ⟨u, hu, hut⟩ := hΦ t.2
      rwa [(T : Subgroup K).subtype_injective hut] at hu
    haveI : Subsingleton ↥(T : Subgroup K) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      have hlt : frattini ↥(T : Subgroup K) < ⊤ := by
        obtain ⟨M, hM⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup ↥(T : Subgroup K))).resolve_left
          bot_ne_top
        exact lt_of_le_of_lt (frattini_le_coatom hM.1) hM.1.lt_top
      exact hlt.ne htop
    infer_instance
  ·
    obtain ⟨s, hsT, hsΦ⟩ := Set.not_subset.mp hΦ
    set V := Subgroup.zpowers s ⊔ Φm with hV
    have hΦT : Φm ≤ T := Subgroup.map_subtype_le _
    have hVT : V ≤ T := sup_le (Subgroup.zpowers_le.mpr hsT) hΦT
    have hVΦ : ¬ V ≤ Φm := fun h => hsΦ (h (Subgroup.mem_sup_left (Subgroup.mem_zpowers s)))
    have hNV : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤
        Subgroup.normalizer (V : Set K) := by
      intro g hg
      have hgΦ : g ∈ Subgroup.normalizer (Φm : Set K) :=
        CFSG.RankThree.GF2n.mem_normalizer_inSubgroup_frattini hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgΦ ⊢
      have hle : V.map (MulAut.conj g).toMonoidHom ≤ V := by
        rw [hV, Subgroup.map_sup, show Φm.map (MulAut.conj g).toMonoidHom = Φm from hgΦ,
          MonoidHom.map_zpowers]
        refine sup_le (Subgroup.zpowers_le.mpr ?_) le_sup_right
        have hc := htriv g hg s hsT
        have : (MulAut.conj g).toMonoidHom s = (g * s * g⁻¹ * s⁻¹) * s := by
          simp [MulAut.conj_apply]
        rw [this]
        exact V.mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left (Subgroup.mem_zpowers s))
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    have hVeq := hirr V hVT hVΦ hNV
    set s' : ↥(T : Subgroup K) := ⟨s, hsT⟩
    have hmap : (Subgroup.zpowers s' ⊔ frattini ↥(T : Subgroup K)).map (T : Subgroup K).subtype =
        (⊤ : Subgroup ↥(T : Subgroup K)).map (T : Subgroup K).subtype := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      exact hVeq
    have htop := Subgroup.map_injective (T : Subgroup K).subtype_injective hmap
    have hz : Subgroup.zpowers s' = ⊤ := frattini_nongenerating htop
    exact ⟨s', fun x => Subgroup.mem_zpowers_iff.mp (hz ▸ Subgroup.mem_top x)⟩

theorem hasNormalPComplement_of_comm_mem_frattini_sylow (T : Sylow p K)
    (hirr : ∀ V : Subgroup K, V ≤ T →
      ¬ V ≤ (frattini ↥(T : Subgroup K)).map (T : Subgroup K).subtype →
      Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
        V = T)
    (htriv : ∀ g ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ (T : Subgroup K),
      g * t * g⁻¹ * t⁻¹ ∈ (frattini ↥(T : Subgroup K)).map (T : Subgroup K).subtype) :
    CFSG.HasNormalPComplement p K := by
  have hp : p.Prime := Fact.out
  have hcyc := isCyclic_of_comm_mem_frattini T hirr htriv
  have hab : ∀ a ∈ (T : Subgroup K), ∀ b ∈ (T : Subgroup K), a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
    have h : (⟨a, ha⟩ : ↥(T : Subgroup K)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hi, ← hj]
      exact zpow_mul_comm g i j
    exact congrArg Subtype.val h
  have hcent : ∀ g ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      g ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) := by
    intro g hg
    set n := orderOf g with hn
    have hn0 : n ≠ 0 := (orderOf_pos g).ne'
    have hcop : Nat.Coprime (ordProj[p] n) (ordCompl[p] n) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
    refine mem_of_pow_mem_of_coprime' hcop ?_ ?_
    ·
      have hgk : (g ^ ordProj[p] n) ^ (ordCompl[p] n) = 1 := by
        rw [← pow_mul, Nat.ordProj_mul_ordCompl_eq_self, hn, pow_orderOf_eq_one]
      have hgN := Subgroup.pow_mem _ hg (ordProj[p] n)
      exact mem_centralizer_of_comm_mem_frattini T.2 hgN hgk (Nat.coprime_ordCompl hp hn0).symm
        (htriv _ hgN)
    ·
      have hgk : (g ^ ordCompl[p] n) ^ p ^ (n.factorization p) = 1 := by
        rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, hn, pow_orderOf_eq_one]
      have hgT := CFSG.RankThree.Transfer.mem_of_pow_eq_one_of_mem_normalizer T
        (Subgroup.pow_mem _ hg _) hgk
      exact Subgroup.mem_centralizer_iff.mpr fun t ht => hab t ht _ hgT
  refine hasNormalPComplement_of_sylow_le_center_normalizer p T fun t ht => ⟨?_, ?_⟩
  · exact Subgroup.le_normalizer ht
  · show t ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hcent g hg) t ht).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
