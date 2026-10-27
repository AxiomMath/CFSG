module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
import CFSG.CGT.PushingUpLit.A78.OppSL2

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG.CGT.PushingUpLit.T2K
open scoped MatrixGroups

open CFSG.Timmesfeld in
private theorem exists_map_conj_eq_of_rankOne {X : Type*} [Group X] {A B : Subgroup X}
    (h : IsElemAbRankOne A B) {x y₁ y₂ : X}
    (h₁ : A.map (MulAut.conj y₁).toMonoidHom ≠ A.map (MulAut.conj x).toMonoidHom)
    (h₂ : A.map (MulAut.conj y₂).toMonoidHom ≠ A.map (MulAut.conj x).toMonoidHom) :
    ∃ a ∈ A.map (MulAut.conj x).toMonoidHom,
      (A.map (MulAut.conj y₁).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        A.map (MulAut.conj y₂).toMonoidHom := by
  have hne : ∀ y : X, A.map (MulAut.conj y).toMonoidHom ≠ A.map (MulAut.conj x).toMonoidHom →
      A.map (MulAut.conj (x⁻¹ * y)).toMonoidHom ≠ A := by
    intro y hy heq
    apply hy
    have := RankOne.map_conj_mul A x (x⁻¹ * y)
    rwa [mul_inv_cancel_left, heq] at this
  have k : ∀ {y a : X}, A.map (MulAut.conj (x⁻¹ * y)).toMonoidHom =
      B.map (MulAut.conj a).toMonoidHom →
      A.map (MulAut.conj y).toMonoidHom = B.map (MulAut.conj (x * a)).toMonoidHom := by
    intro y a e
    rw [RankOne.map_conj_mul B x a, ← e, ← RankOne.map_conj_mul, mul_inv_cancel_left]
  obtain ⟨a₁, ha₁, e₁⟩ := h.exists_eq_of_map_conj_ne (hne y₁ h₁)
  obtain ⟨a₂, ha₂, e₂⟩ := h.exists_eq_of_map_conj_ne (hne y₂ h₂)
  refine ⟨x * (a₂ * a₁⁻¹) * x⁻¹,
    RankOne.conj_mem_map_conj x (A.mul_mem ha₂ (A.inv_mem ha₁)), ?_⟩
  rw [k e₁, k e₂, ← RankOne.map_conj_mul,
    show x * (a₂ * a₁⁻¹) * x⁻¹ * (x * a₁) = x * a₂ by group]

open CFSG.Timmesfeld in
private theorem exists_eq_map_conj_upper {n : ℕ} (Q : Sylow 2 SL(2, GaloisField 2 n)) :
    ∃ x, (Q : Subgroup SL(2, GaloisField 2 n)) =
      (upperUnipotent (GaloisField 2 n)).map (MulAut.conj x).toMonoidHom := by
  have h := A78.isElemAbRankOne_upper_lower (GaloisField 2 n)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq SL(2, GaloisField 2 n)
    (h.isPGroup.toSylow h.not_two_dvd_index) Q
  exact ⟨x, (congrArg Sylow.toSubgroup hx).symm⟩

theorem exists_map_conj_eq_of_sylow_sl2 {n : ℕ} {Q₀ Q₁ Q₂ : Sylow 2 SL(2, GaloisField 2 n)}
    (h₁ : Q₁ ≠ Q₀) (h₂ : Q₂ ≠ Q₀) :
    ∃ a ∈ (Q₀ : Subgroup SL(2, GaloisField 2 n)),
      (Q₁ : Subgroup SL(2, GaloisField 2 n)).map (MulAut.conj a).toMonoidHom = Q₂ := by
  obtain ⟨x₀, e₀⟩ := exists_eq_map_conj_upper Q₀
  obtain ⟨x₁, e₁⟩ := exists_eq_map_conj_upper Q₁
  obtain ⟨x₂, e₂⟩ := exists_eq_map_conj_upper Q₂
  rw [e₀, e₁, e₂]
  refine exists_map_conj_eq_of_rankOne (A78.isElemAbRankOne_upper_lower _) ?_ ?_
  · rw [← e₀, ← e₁]
    exact fun h => h₁ (Sylow.ext h)
  · rw [← e₀, ← e₂]
    exact fun h => h₂ (Sylow.ext h)

theorem eq_one_of_forall_smul_sylow_sl2 {n : ℕ} (hn : 2 ≤ n) {y : SL(2, GaloisField 2 n)}
    (hy : ∀ Q : Sylow 2 SL(2, GaloisField 2 n), y • Q = Q) : y = 1 := by
  have h := A78.isElemAbRankOne_upper_lower (GaloisField 2 n)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SL(2, GaloisField 2 n) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq T2K.sl2_center_eq_bot.symm)
  have : IsSimpleGroup SL(2, GaloisField 2 n) := e.isSimpleGroup
  let ρ := MulAction.toPermHom SL(2, GaloisField 2 n) (Sylow 2 SL(2, GaloisField 2 n))
  have hyK : y ∈ ρ.ker := MonoidHom.mem_ker.2 (Equiv.Perm.ext hy)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hK | hK
  · rwa [hK, Subgroup.mem_bot] at hyK
  · exfalso
    obtain ⟨g, hg⟩ := h.exists_eq_map_conj
    have hgK : g ∈ ρ.ker := hK ▸ Subgroup.mem_top g
    have h1 : g • h.isPGroup.toSylow h.not_two_dvd_index =
        h.isPGroup.toSylow h.not_two_dvd_index :=
      DFunLike.congr_fun (MonoidHom.mem_ker.1 hgK) _
    have h2 := CFSG.Timmesfeld.RankOne.map_conj_eq_self_iff.2
      (Sylow.smul_eq_iff_mem_normalizer.1 h1)
    exact h.ne (hg.trans h2).symm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}

theorem oTwoIn_le_of_isSylowOf {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) :
    oTwoIn L ≤ S :=
  le_of_isPGroup_normal hS (oTwoIn_le L)
    (fun _ hm => normalizer_le_normalizer_oTwoIn L (Subgroup.le_normalizer hm))
    (isPGroup_oTwoIn L)

theorem isSylowOf_cj_of_mem {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) {s : G}
    (hs : s ∈ L) : CFSG.ABGLocalTools.IsSylowOf 2 (cj s S) L := by
  refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact L.mul_mem (L.mul_mem hs (hS.le hx)) (L.inv_mem hs)
  · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
    exact hS.card_eq

theorem eq_of_map_φ_eq (D : NatData L n) {S S' : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) (hS' : CFSG.ABGLocalTools.IsSylowOf 2 S' L)
    (h : (S.subgroupOf L).map D.φ = (S'.subgroupOf L).map D.φ) : S = S' := by
  have hk : ∀ {R : Subgroup G}, oTwoIn L ≤ R → D.φ.ker ≤ R.subgroupOf L :=
    fun hR l hl => Subgroup.mem_subgroupOf.2 (hR ((D.φ_ker l).1 (MonoidHom.mem_ker.1 hl)))
  have e : S.subgroupOf L = S'.subgroupOf L := by
    rw [← Subgroup.comap_map_eq_self (hk (oTwoIn_le_of_isSylowOf hS)), h,
      Subgroup.comap_map_eq_self (hk (oTwoIn_le_of_isSylowOf hS'))]
  rwa [Subgroup.subgroupOf_inj, inf_of_le_left hS.le, inf_of_le_left hS'.le] at e

theorem exists_sylow_eq_map_φ (D : NatData L n) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) :
    ∃ Q : Sylow 2 SL(2, GaloisField 2 n),
      (Q : Subgroup SL(2, GaloisField 2 n)) = (S.subgroupOf L).map D.φ := by
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq_subgroupOf
  exact ⟨P.mapSurjective D.φ_surj, by rw [Sylow.coe_mapSurjective, hP]⟩

theorem exists_cj_eq_of_isSylowOf (hL : NatBlock L n) {S₀ S₁ S₂ : Subgroup G}
    (h₀ : CFSG.ABGLocalTools.IsSylowOf 2 S₀ L) (h₁ : CFSG.ABGLocalTools.IsSylowOf 2 S₁ L)
    (h₂ : CFSG.ABGLocalTools.IsSylowOf 2 S₂ L) (h₁₀ : S₁ ≠ S₀) (h₂₀ : S₂ ≠ S₀) :
    ∃ s ∈ S₀, cj s S₁ = S₂ := by
  obtain ⟨D⟩ := hL.nonempty_natData
  obtain ⟨Q₀, e₀⟩ := exists_sylow_eq_map_φ D h₀
  obtain ⟨Q₁, e₁⟩ := exists_sylow_eq_map_φ D h₁
  obtain ⟨Q₂, e₂⟩ := exists_sylow_eq_map_φ D h₂
  have hne : ∀ {S : Subgroup G} {Q : Sylow 2 SL(2, GaloisField 2 n)},
      CFSG.ABGLocalTools.IsSylowOf 2 S L → S ≠ S₀ →
      (Q : Subgroup SL(2, GaloisField 2 n)) = (S.subgroupOf L).map D.φ → Q ≠ Q₀ :=
    fun hS hS₀ eQ hQ => hS₀ (eq_of_map_φ_eq D hS h₀ (by rw [← eQ, ← e₀, hQ]))
  obtain ⟨a, ha, hQa⟩ := exists_map_conj_eq_of_sylow_sl2 (hne h₁ h₁₀ e₁) (hne h₂ h₂₀ e₂)
  rw [e₀] at ha
  rw [e₁, e₂] at hQa
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ha
  refine ⟨(s : G), hs, eq_of_map_φ_eq D (isSylowOf_cj_of_mem h₁ s.2) h₂ ?_⟩
  rw [← hQa, ← CFSG.Timmesfeld.RankOne.map_map_conj, CFSG.Timmesfeld.map_conj_subgroupOf]

theorem mem_oTwoIn_of_forall_normalizes (hL : NatBlock L n) {l : G} (hl : l ∈ L)
    (h : ∀ S, CFSG.ABGLocalTools.IsSylowOf 2 S L → l ∈ Subgroup.normalizer (S : Set G)) :
    l ∈ oTwoIn L := by
  obtain ⟨D⟩ := hL.nonempty_natData
  refine (D.φ_ker ⟨l, hl⟩).1 (eq_one_of_forall_smul_sylow_sl2 hL.two_le fun Q => ?_)
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective D.φ_surj 2 Q
  have hP : (P : Subgroup L).map (MulAut.conj (⟨l, hl⟩ : L)).toMonoidHom = P := by
    apply Subgroup.map_injective L.subtype_injective
    rw [CFSG.Timmesfeld.RankOne.map_map_conj]
    exact CFSG.Timmesfeld.RankOne.map_conj_eq_self_iff.2 (h _ ⟨P, rfl⟩)
  refine Sylow.ext ?_
  show ((P : Subgroup L).map D.φ).map (MulAut.conj (D.φ ⟨l, hl⟩)).toMonoidHom =
    (P : Subgroup L).map D.φ
  rw [← CFSG.Timmesfeld.RankOne.map_map_conj, hP]

end CFSG.CGT.PushingUpLit.A78One
