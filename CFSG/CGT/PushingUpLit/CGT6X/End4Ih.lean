module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltY
public import CFSG.CGT.PushingUpLit.CGT6.EmbMin

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

section Aux

theorem ih4_sup_le_normalizer {M : Type*} [Group M] {K : Subgroup M} {t : M} (ht2 : t * t = 1)
    (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K) :
    K ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set M) := by
  refine sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr ?_)
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨htK h, fun hh => ?_⟩
  have h1 := htK _ hh
  have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [hti]
    calc t * (t * h * t) * t = (t * t) * h * (t * t) := by simp only [mul_assoc]
      _ = h := by rw [ht2, one_mul, mul_one]
  rwa [e] at h1

theorem ih4_conjClosure_le {M : Type} [Group M] {Y K G' : Subgroup M} (hYK : Y ≤ K)
    (hN : G' ≤ Subgroup.normalizer (K : Set M)) : CGT6.conjClosure Y G' ≤ K := by
  rw [CGT6.conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hN hg) y).mp (hYK hy)

theorem ih4_card_sl2 {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (Fq n)) = 2 ^ n * (2 ^ (2 * n) - 1) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 n hn,
    ← pow_mul, mul_comm n 2]

theorem ih4_sl2_order_sixty {n : ℕ} (hn : 2 ≤ n) (h : 2 ^ n * (2 ^ (2 * n) - 1) = 60) :
    n = 2 := by
  by_contra hne
  have h3 : 3 ≤ n := by omega
  have h1 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
  have h2 : 64 ≤ 2 ^ (2 * n) := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 8 * 63 ≤ 2 ^ n * (2 ^ (2 * n) - 1) := Nat.mul_le_mul h1 (by omega)
  omega

theorem ih4_card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

end Aux

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem ih4_adm {G T Y K : Subgroup (MulAut V)} (cfg : Emb4Cfg G T Y) {t : MulAut V}
    (htT : t ∈ T) (ht1 : t ≠ 1) (ht2 : t * t = 1) (hYK : Y ≤ K) (hKG : K ≤ G) :
    Adm4 (K ⊔ Subgroup.zpowers t) (Subgroup.zpowers t) Y := by
  have hzT : Subgroup.zpowers t ≤ T := Subgroup.zpowers_le.mpr htT
  have hG' : K ⊔ Subgroup.zpowers t ≤ G := sup_le hKG (hzT.trans cfg.adm.hTG)
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hcent : Subgroup.zpowers t ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
    hzT.trans cfg.adm.le_centralizer
  refine
    { hTG := le_sup_right
      hT1 := fun h => ht1 (Subgroup.zpowers_eq_bot.mp h)
      hT2 := ?_
      hYC := ?_
      hsub := ?_
      hperf := cfg.adm.hperf
      hcls := cfg.adm.hcls }
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf t = 2 := orderOf_eq_prime ht2' ht1
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  · exact le_inf (hYK.trans le_sup_left) fun y hy =>
      Subgroup.centralizer_le (s := (Subgroup.zpowers t : Set (MulAut V))) (t := (T : Set _))
        hzT ((cfg.adm.hYC hy).2)
  · have h := cfg.cent t ⟨cfg.adm.hTG htT, hcent (Subgroup.mem_zpowers t)⟩ ht1 ht2'
    refine CFSG.GroupTheory.isSubnormal_subgroupOf_of_le ?_ h
    exact inf_le_inf hG' (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (Subgroup.mem_zpowers t)))

theorem ih_natural_K (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (cfg : Emb4Cfg G T Y) {K : Subgroup (MulAut V)} {t : MulAut V} (htT : t ∈ T) (ht1 : t ≠ 1)
    (ht2 : t * t = 1) (hYK : Y ≤ K) (hKG : K ≤ G) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hKA7 : Nonempty (↥K ≃* alternatingGroup (Fin 7))) (hY60 : Nat.card ↥Y = 60)
    (hKY : K ≠ Y) (hsmall : Nat.card ↥(K ⊔ Subgroup.zpowers t) < Nat.card ↥G) :
    ∃ θK : ↥K ≃* alternatingGroup (Fin 7),
      IsNatSectionWith (altAct 7) θK (commV K) ⊥ := by
  obtain ⟨e⟩ := hKA7
  have hzT : Subgroup.zpowers t ≤ T := Subgroup.zpowers_le.mpr htT
  have hG'G : K ⊔ Subgroup.zpowers t ≤ G := sup_le hKG (hzT.trans cfg.adm.hTG)
  obtain ⟨X, hX⟩ := cfg.ih V hV (K ⊔ Subgroup.zpowers t) (Or.inl hsmall)
    (isKGroup_of_le cfg.kgroup hG'G) (Subgroup.zpowers t) Y
    (ih4_adm cfg htT ht1 ht2 hYK hKG)
  have hcc : CGT6.conjClosure Y X = X := hX.conjClosure_eq hV (cfg.adm.hcls.not_isPGroup hV)
  obtain ⟨hYX, hXG', hXsub, h4⟩ := hX
  have hXK : X ≤ K :=
    calc X = CGT6.conjClosure Y X := hcc.symm
      _ ≤ CGT6.conjClosure Y (K ⊔ Subgroup.zpowers t) := CGT6.conjClosure_mono hXG'
      _ ≤ K := ih4_conjClosure_le hYK (ih4_sup_le_normalizer ht2 htK)
  have hsimple : IsSimpleGroup ↥K := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hXsubK : (X.subgroupOf K).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le le_sup_left hXsub
  have hXK' : X = K := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hXsubK with hbot | htop
    · exfalso
      have hX1 : X = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 : (⟨x, hXK hx⟩ : ↥K) ∈ X.subgroupOf K := hx
        rw [hbot, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
      have hY1 : Y = ⊥ := le_bot_iff.mp (hX1 ▸ hYX)
      rw [hY1, Subgroup.card_bot] at hY60
      omega
    · exact le_antisymm hXK (Subgroup.subgroupOf_eq_top.mp htop)
  rw [hXK'] at h4
  rcases h4 with ⟨hcl, -⟩ | ⟨n, hn, hnat, hsplit⟩
  ·
    have : Group.IsPerfect (alternatingGroup (Fin 7)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    have hperf : Group.IsPerfect ↥K :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact natSection_of_classX_alt hV (Subgroup.isPerfect_iff.mp hperf) hcl (m := 7)
      (by norm_num) (by decide) ⟨e⟩
  ·
    exfalso
    rcases hsplit with hYK' | ⟨-, ⟨eY⟩, -⟩
    · exact hKY hYK'.symm
    · have hn0 : n ≠ 0 := by omega
      have h60 : 2 ^ n * (2 ^ (2 * n) - 1) = 60 := by
        rw [← ih4_card_sl2 hn0, ← Nat.card_congr eY.toEquiv, hY60]
      obtain rfl : n = 2 := ih4_sl2_order_sixty hn h60
      have hK : Nat.card ↥K = 2520 := by rw [Nat.card_congr e.toEquiv, ih4_card_alt7]
      rcases hnat with ⟨-, θ, -⟩ | ⟨-, θ, -⟩
      · have h1 := Nat.card_congr θ.toEquiv
        rw [Nat.card_prod, ih4_card_sl2 (by norm_num), hK] at h1
        norm_num at h1
      · have h1 := Nat.card_congr θ.toEquiv
        rw [ih4_card_sl2 (by norm_num), hK] at h1
        norm_num at h1

end Main

end CFSG.CGT.PushingUpLit.CGT6X.End4
