module

public import CFSG.Monster.Existence.Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankHNFive
import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Monster.Existence CFSG.Blueprint

private theorem mrf_sup_zpowers {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) {z : G} (hz : orderOf z = p) (hzE : z ∉ E)
    (hc : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers z) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers z) = Nat.card E * p := by
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hcz : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  refine ⟨hE.sup_of_commute (isElemAbelian_zpowers hzp) fun a ha b hb => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hc a ha) n).eq
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr hc)
  have hD : Disjoint E (Subgroup.zpowers z) := by
    haveI : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcz]; exact hp⟩
    refine Subgroup.subgroupOf_eq_bot.1
      ((E.subgroupOf _).eq_bot_or_eq_top_of_prime_card.resolve_right fun h => hzE ?_)
    have hz' : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈ E.subgroupOf _ := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hz'
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hN hD, hcz]

theorem exists_elemAbelian_five_four_of_monsterExistence
    {G : Type} [Group G] (hE : MonsterExistenceStatement G) :
    ∃ E : Subgroup G, IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 4 := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, ha, -, -, -, -, -, hgraph⟩ := hE
  obtain ⟨-, c, -, -, -, -, hord, -, hocc, hshape, -⟩ := hgraph
  obtain ⟨α, β, hα, hβ, h7⟩ := hocc 7
  obtain ⟨e⟩ : Nonempty (↥(cent2 α β) ≃* NativeSporadic.Carrier .HN) := hshape α β 7 hα hβ h7
  haveI : Finite G := hfin
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hconj : ∀ u v : G, IsConj u v → orderOf u = orderOf v := by
    intro u v h
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    exact SemiconjBy.orderOf_eq g (show g * u = v * g by rw [← hg]; group)
  have hsq : ∀ x : G, IsConj a x → x * x = 1 := by
    intro x h
    have h2 : orderOf x = 2 := (hconj a x h).symm.trans ha
    rw [← sq, ← h2, pow_orderOf_eq_one]
  have hk : orderOf (α * β) = 5 := by
    rw [hconj _ _ h7, hord 7]
    rfl
  have hkα : α * β ∉ cent α := by
    intro h
    have h' : α * β * α = α * (α * β) := Subgroup.mem_centralizer_singleton_iff.1 h
    have h2 : (α * β) ^ 2 = 1 := by
      calc (α * β) ^ 2 = α * β * α * β := by rw [sq]; simp only [mul_assoc]
        _ = α * α * (β * β) := by rw [h']; simp only [mul_assoc]
        _ = 1 := by rw [hsq α hα, hsq β hβ, one_mul]
    have h5 := orderOf_dvd_of_pow_eq_one h2
    rw [hk] at h5
    norm_num at h5
  haveI : Finite (NativeSporadic.Carrier .HN) := Finite.of_equiv _ e.toEquiv
  have h3 := CFSG.AGLEmbeddingD2.three_le_pRank_HN_five
  obtain ⟨E₀, -, hE₀, hc₀⟩ := CFSG.SectionRank.exists_pRank (p := 5) (by norm_num)
    (⊤ : Subgroup (NativeSporadic.Carrier .HN))
  let f : NativeSporadic.Carrier .HN →* G := (cent2 α β).subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := (cent2 α β).subtype_injective.comp e.symm.injective
  have hmem : ∀ x ∈ E₀.map f, x ∈ cent2 α β := by
    rintro _ ⟨y, -, rfl⟩
    exact (e.symm y).2
  obtain ⟨hJ, hJc⟩ := mrf_sup_zpowers Nat.prime_five (CFSG.SectionRank.isElemAbelian_map hE₀ f) hk
    (fun h => hkα (Subgroup.mem_inf.1 (hmem _ h)).1) fun x hx =>
      (Commute.mul_right
        (show Commute x α from Subgroup.mem_centralizer_singleton_iff.1
          (Subgroup.mem_inf.1 (hmem x hx)).1)
        (show Commute x β from Subgroup.mem_centralizer_singleton_iff.1
          (Subgroup.mem_inf.1 (hmem x hx)).2)).eq
  have h4 : 5 ^ 4 ∣ Nat.card ↥(E₀.map f ⊔ Subgroup.zpowers (α * β)) := by
    rw [hJc, Subgroup.card_map_of_injective hf, hc₀, ← pow_succ]
    exact pow_dvd_pow 5 (by omega)
  obtain ⟨F, -, hF, hFc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hJ h4
  exact ⟨F, hF, hFc⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
