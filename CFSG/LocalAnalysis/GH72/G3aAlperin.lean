module

public import CFSG.LocalAnalysis.GH72.DDSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.GH72

open Subgroup CFSG.CGT.Foote81L6.TStruct

variable {G : Type*} [Group G] [Finite G]

private theorem normalizes_e16_of_odd_mem_normalizer
    {S S₁ S₂ Q : Subgroup G} (hd : DDDecomp S S₁ S₂) (hQS : Q ≤ S) {E : Subgroup G}
    (hE : IsE16 E) (hEQ : E ≤ Q)
    (hodd : ∀ (D D₁ D₂ B : Subgroup G) (u : G), DDDecomp D D₁ D₂ → B ≤ D → IsE16 B →
      u ∈ Subgroup.normalizer (D : Set G) → Odd (orderOf u) →
      u ∈ Subgroup.normalizer (B : Set G))
    {t : G} (htN : t ∈ Subgroup.normalizer (Q : Set G)) (htodd : Odd (orderOf t)) :
    t ∈ Subgroup.normalizer (E : Set G) := by
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let f : N → Subgroup G := fun u => E.map (MulAut.conj ((u : G))⁻¹).toMonoidHom
  let D : Subgroup G := sSup (Set.range f)
  have hD_eq : D = ⨆ u : N, f u := sSup_range
  have hf_le_Q : ∀ u : N, f u ≤ Q := by
    intro u
    have hmapQ : Q.map (MulAut.conj ((u : G))⁻¹).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (Q : Set G)).inv_mem u.2)
    calc f u = E.map (MulAut.conj ((u : G))⁻¹).toMonoidHom := rfl
      _ ≤ Q.map (MulAut.conj ((u : G))⁻¹).toMonoidHom := Subgroup.map_mono hEQ
      _ = Q := hmapQ
  have hf_E16 : ∀ u : N, IsE16 (f u) := fun u =>
    hE.map (MulAut.conj ((u : G))⁻¹).toMonoidHom (MulAut.conj ((u : G))⁻¹).injective
  have hE_le_D : E ≤ D := by
    rw [hD_eq]
    have hf_one : f ⟨1, N.one_mem⟩ = E := by
      ext x
      simp [f]
    calc E = f ⟨1, N.one_mem⟩ := hf_one.symm
      _ ≤ ⨆ u : N, f u := le_iSup f ⟨1, N.one_mem⟩
  have hD_le_Q : D ≤ Q := by
    rw [hD_eq]
    exact iSup_le hf_le_Q
  have hD_le_S : D ≤ S := hD_le_Q.trans hQS
  have h𝒜 : ∀ K ∈ Set.range f, K ≤ S ∧ IsE16 K := by
    rintro K ⟨u, rfl⟩
    exact ⟨(hf_le_Q u).trans hQS, hf_E16 u⟩
  have hne : (Set.range f).Nonempty := ⟨f ⟨1, N.one_mem⟩, ⟨⟨1, N.one_mem⟩, rfl⟩⟩
  obtain ⟨hDsplit, hDdih₁, hDdih₂⟩ := hd.sSup_e16 (𝒜 := Set.range f) h𝒜 hne
  replace hDsplit : D = D ⊓ S₁ ⊔ D ⊓ S₂ := by simpa [D] using hDsplit
  replace hDdih₁ : IsDih (D ⊓ S₁) := by simpa [D] using hDdih₁
  replace hDdih₂ : IsDih (D ⊓ S₂) := by simpa [D] using hDdih₂
  have hcomp (n u : N) :
      (MulAut.conj (n : G)).toMonoidHom.comp (MulAut.conj ((u : G))⁻¹).toMonoidHom =
        (MulAut.conj (((u * n⁻¹ : N) : G))⁻¹).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hDinv : ∀ n : N, D.map (MulAut.conj (n : G)).toMonoidHom = D := by
    intro n
    have hsurj : Function.Surjective (fun u : N => u * n⁻¹) :=
      fun v => ⟨v * n, by group⟩
    rw [hD_eq, Subgroup.map_iSup]
    calc ⨆ u : N, (f u).map (MulAut.conj (n : G)).toMonoidHom
        = ⨆ u : N, f (u * n⁻¹) := iSup_congr fun u => by
            rw [Subgroup.map_map, hcomp]
      _ = ⨆ u : N, f u := hsurj.iSup_comp f
      _ = D := hD_eq.symm
  have htD : t ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hDinv ⟨t, htN⟩)
  by_cases hDE : IsE16 D
  · have hE_eq_D : E = D :=
      Subgroup.eq_of_le_of_card_ge hE_le_D (by rw [hE.2, hDE.2])
    rw [hE_eq_D]
    exact htD
  ·
    have hinf : (D ⊓ S₁) ⊓ (D ⊓ S₂) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨⟨-, hx₁⟩, ⟨-, hx₂⟩⟩ := hx
      exact (mem_bot.mp (hd.inf_eq ▸ (mem_inf.mpr ⟨hx₁, hx₂⟩ : x ∈ S₁ ⊓ S₂)))
    have hcomm : (D ⊓ S₂) ≤ centralizer ((D ⊓ S₁ : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hd.commute hx.2)) y hy.2
    have hcomm' : (D ⊓ S₁) ≤ centralizer ((D ⊓ S₂ : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        ((Subgroup.mem_centralizer_iff.mp (hd.commute hy.2)) x hx.2).symm
    have hsup' : (D ⊓ S₂) ⊔ (D ⊓ S₁) = D := by rw [sup_comm, ← hDsplit]
    have hinf' : (D ⊓ S₂) ⊓ (D ⊓ S₁) = ⊥ := by rw [inf_comm]; exact hinf
    by_cases h₁ : IsDihNonab (D ⊓ S₁)
    · by_cases h₂ : IsDihNonab (D ⊓ S₂)
      · have hdec : DDDecomp D (D ⊓ S₁) (D ⊓ S₂) :=
          ⟨hDsplit.symm, hinf, hcomm, hDdih₁, h₂⟩
        exact hodd D (D ⊓ S₁) (D ⊓ S₂) E t hdec hE_le_D hE htD htodd
      · have hdec : DDDecomp D (D ⊓ S₂) (D ⊓ S₁) :=
          ⟨hsup', hinf', hcomm', hDdih₂, h₁⟩
        exact hodd D (D ⊓ S₂) (D ⊓ S₁) E t hdec hE_le_D hE htD htodd
    · have hK₁ : IsKleinFour ↥(D ⊓ S₁) :=
        hDdih₁.isKleinFour_or_isDihNonab.resolve_right h₁
      by_cases h₂ : IsDihNonab (D ⊓ S₂)
      · have hdec : DDDecomp D (D ⊓ S₁) (D ⊓ S₂) :=
          ⟨hDsplit.symm, hinf, hcomm, hDdih₁, h₂⟩
        exact hodd D (D ⊓ S₁) (D ⊓ S₂) E t hdec hE_le_D hE htD htodd
      · have hK₂ : IsKleinFour ↥(D ⊓ S₂) :=
          hDdih₂.isKleinFour_or_isDihNonab.resolve_right h₂
        have hV₁ : IsFourIn S₁ (D ⊓ S₁) :=
          ⟨inf_le_right, (IsDih.isFourIn_self_of_isKleinFour hK₁).2.1,
            (IsDih.isFourIn_self_of_isKleinFour hK₁).2.2⟩
        have hV₂ : IsFourIn S₂ (D ⊓ S₂) :=
          ⟨inf_le_right, (IsDih.isFourIn_self_of_isKleinFour hK₂).2.1,
            (IsDih.isFourIn_self_of_isKleinFour hK₂).2.2⟩
        have hDE' : IsE16 D := by
          rw [hDsplit]
          exact hd.isE16_sup hV₁ hV₂
        exact absurd hDE' hDE

private theorem exists_conj_eq_of_odd_normalizer
    {S Q E : Subgroup G}
    (hcop : Nat.Coprime 2 ((S ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf
      (Subgroup.normalizer (Q : Set G))).index)
    (hoddnorm : ∀ t ∈ Subgroup.normalizer (Q : Set G), Odd (orderOf t) →
      t ∈ Subgroup.normalizer (E : Set G)) :
    ∀ n ∈ Subgroup.normalizer (Q : Set G),
      ∃ p ∈ S ⊓ Subgroup.normalizer (Q : Set G),
        E.map (MulAut.conj n⁻¹).toMonoidHom = E.map (MulAut.conj p⁻¹).toMonoidHom := by
  intro n hn
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let T : Set G := {x | x ∈ N ∧ Odd (orderOf x)}
  let H : Subgroup G := Subgroup.closure T
  have hH_eq : H = Subgroup.closure T := rfl
  have hH_le_N : H ≤ N := by
    rw [hH_eq, Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hHnorm : H ≤ Subgroup.normalizer (E : Set G) := by
    rw [hH_eq, Subgroup.closure_le]
    intro t ht
    exact hoddnorm t ht.1 ht.2
  have hN_le_normalizer_H : N ≤ Subgroup.normalizer (H : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hH_eq, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨hzN, hzodd⟩, rfl⟩
      refine ⟨N.mul_mem (N.mul_mem hx hzN) (N.inv_mem hx), ?_⟩
      have h := (MulEquiv.orderOf_eq (MulAut.conj x) z).symm
      rwa [h] at hzodd
    · rintro ⟨hyN, hyodd⟩
      refine ⟨(MulAut.conj x).symm y, ⟨?_, ?_⟩, ?_⟩
      · exact N.mul_mem (N.mul_mem (N.inv_mem hx) hyN) hx
      · have h := (MulEquiv.orderOf_eq (MulAut.conj x).symm y).symm
        rwa [h] at hyodd
      · exact MulEquiv.apply_symm_apply (MulAut.conj x) y
  haveI hHN_normal : (H.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hN_le_normalizer_H
  have hquot : IsPGroup 2 (N ⧸ H.subgroupOf N) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf N) x
    obtain ⟨k, m, hm_odd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_subgroupOf]
    change ((n ^ 2 ^ k : N) : G) ∈ Subgroup.closure T
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · simpa using N.pow_mem n.2 (2 ^ k)
    · have hdvd : orderOf ((n : N) ^ 2 ^ k) ∣ m := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, ← hord, pow_orderOf_eq_one]
      have hoddN : Odd (orderOf ((n : N) ^ 2 ^ k)) := hm_odd.of_dvd_nat hdvd
      rwa [Subgroup.orderOf_coe]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hquot
  have hHindex : H.relIndex N = 2 ^ m := by
    change (H.subgroupOf N).index = 2 ^ m
    rw [Subgroup.index_eq_card, hm]
  let P : Subgroup G := S ⊓ N
  have hP_le_N : P ≤ N := inf_le_right
  have hP_le_S : P ≤ S := inf_le_left
  have hPindex : Nat.Coprime 2 (P.relIndex N) := by
    simpa [P, N, Subgroup.relIndex] using hcop
  have hsup_eq : P ⊔ H = N := by
    have hK_le_N : P ⊔ H ≤ N := sup_le hP_le_N hH_le_N
    have hdivP : (P ⊔ H).relIndex N ∣ P.relIndex N :=
      Subgroup.relIndex_dvd_of_le_left (H := P) (K := P ⊔ H) (L := N) le_sup_left
    have hdivH : (P ⊔ H).relIndex N ∣ H.relIndex N :=
      Subgroup.relIndex_dvd_of_le_left (H := H) (K := P ⊔ H) (L := N) le_sup_right
    have hcopPH : Nat.Coprime (P.relIndex N) (2 ^ m) := by
      simpa using hPindex.symm.pow_right (n := m)
    have hone : (P ⊔ H).relIndex N = 1 := by
      refine Nat.eq_one_of_dvd_coprimes hcopPH hdivP ?_
      simpa [hHindex] using hdivH
    exact le_antisymm hK_le_N (Subgroup.relIndex_eq_one.mp hone)
  have hsupN : P.subgroupOf N ⊔ H.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hP_le_N hH_le_N, hsup_eq, Subgroup.subgroupOf_self]
  let nN : N := ⟨n, hn⟩
  have hn_mem : nN ∈ P.subgroupOf N ⊔ H.subgroupOf N := by
    rw [hsupN]
    exact Subgroup.mem_top nN
  have hn_mem' : nN ∈ H.subgroupOf N ⊔ P.subgroupOf N := by
    simpa [sup_comm] using hn_mem
  obtain ⟨h, hh, p, hp, hhp⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := H.subgroupOf N) (t := P.subgroupOf N)).mp hn_mem'
  have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hhH : (h : G) ∈ H := Subgroup.mem_subgroupOf.mp hh
  have hmap_h : E.map (MulAut.conj ((h : G))⁻¹).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (E : Set G)).inv_mem (hHnorm hhH))
  have hnp : n = (h : G) * (p : G) := by
    have := congrArg (fun z : N => (z : G)) hhp
    simpa using this.symm
  have hcomp : (MulAut.conj (n : G)⁻¹).toMonoidHom =
      (MulAut.conj ((p : G))⁻¹).toMonoidHom.comp (MulAut.conj ((h : G))⁻¹).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hnp]
    group
  refine ⟨p, ⟨hP_le_S hpP, hP_le_N hpP⟩, ?_⟩
  calc E.map (MulAut.conj (n : G)⁻¹).toMonoidHom
      = E.map ((MulAut.conj ((p : G))⁻¹).toMonoidHom.comp
          (MulAut.conj ((h : G))⁻¹).toMonoidHom) := by rw [hcomp]
    _ = (E.map (MulAut.conj ((h : G))⁻¹).toMonoidHom).map
          (MulAut.conj ((p : G))⁻¹).toMonoidHom := by rw [Subgroup.map_map]
    _ = E.map (MulAut.conj ((p : G))⁻¹).toMonoidHom := by rw [hmap_h]


theorem lemma_3_1_of_odd {G : Type*} [Group G] [Finite G] (𝔖 : Sec3Setting G)
    (hodd : ∀ (D D₁ D₂ B : Subgroup G) (u : G), DDDecomp D D₁ D₂ → B ≤ D → IsE16 B →
      u ∈ Subgroup.normalizer (D : Set G) → Odd (orderOf u) →
      u ∈ Subgroup.normalizer (B : Set G))
    (A B : Subgroup G) (hAS : A ≤ 𝔖.S) (hBS : B ≤ 𝔖.S) (hA : IsE16 A) (hB : IsE16 B)
    (g : G) (hg : A.map (MulAut.conj g).toMonoidHom = B) :
    ∃ s ∈ (𝔖.S : Subgroup G), A.map (MulAut.conj s).toMonoidHom = B := by
  have hAeq : B.map (MulAut.conj g⁻¹).toMonoidHom = A := by
    rw [← hg]
    exact map_conj_inv_map_conj A g
  obtain ⟨c, hc, hcpt⟩ :=
    CFSG.RankTwoShapes.alperin_centric_radical_fusion (S := 𝔖.S) (P := B) (g := g)
      hBS (by rw [hAeq]; exact hAS)
  have hBc : B.map (MulAut.conj c⁻¹).toMonoidHom = A := by
    have hsame : B.map (MulAut.conj c⁻¹).toMonoidHom =
        B.map (MulAut.conj g⁻¹).toMonoidHom := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by simpa [MulAut.conj_apply, mul_assoc] using (hcpt y hy).symm⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by simpa [MulAut.conj_apply, mul_assoc] using hcpt y hy⟩
    exact hsame.trans hAeq
  have hAc : A.map (MulAut.conj c).toMonoidHom = B := by
    rw [← hBc]
    rw [Subgroup.map_conj_map_conj, mul_inv_cancel, map_conj_one]
  have key : ∀ c : G, CFSG.RankTwoShapes.AlperinDecomposition 2 (𝔖.S : Subgroup G) B c →
      ∃ m ∈ Subgroup.normalizer (B : Set G), ∃ s ∈ (𝔖.S : Subgroup G), c = m * s := by
    intro c hc
    induction hc with
    | one => exact ⟨1, by simp, 1, by simp, by simp⟩
    | @step c n Q hc hQ hBQ hn ih =>
        obtain ⟨m, hm, s, hs, rfl⟩ := ih
        have hmB : B.map (MulAut.conj m⁻¹).toMonoidHom = B :=
          map_conj_eq_self_of_mem_normalizer ((Subgroup.normalizer (B : Set G)).inv_mem hm)
        have hms : B.map (MulAut.conj ((m * s)⁻¹)).toMonoidHom =
            B.map (MulAut.conj s⁻¹).toMonoidHom := by
          rw [show (m * s)⁻¹ = s⁻¹ * m⁻¹ by group]
          rw [← Subgroup.map_conj_map_conj, hmB]
        let E : Subgroup G := B.map (MulAut.conj s⁻¹).toMonoidHom
        have hE : IsE16 E := by
          exact hB.map (MulAut.conj s⁻¹).toMonoidHom (MulAut.conj s⁻¹).injective
        have hE_le_Q : E ≤ Q := by
          rw [show E = B.map (MulAut.conj ((m * s)⁻¹)).toMonoidHom from hms.symm]
          exact hBQ
        have hoddnorm : ∀ t ∈ Subgroup.normalizer (Q : Set G), Odd (orderOf t) →
            t ∈ Subgroup.normalizer (E : Set G) := fun t ht hto =>
          normalizes_e16_of_odd_mem_normalizer (S := (𝔖.S : Subgroup G)) (S₁ := 𝔖.S₁)
            (S₂ := 𝔖.S₂) (Q := Q) 𝔖.decomp hQ.1 hE hE_le_Q hodd ht hto
        obtain ⟨p, hp, hconj⟩ :=
          exists_conj_eq_of_odd_normalizer (S := (𝔖.S : Subgroup G)) (Q := Q) (E := E)
            hQ.2.1 hoddnorm n hn
        have hhN : n * p⁻¹ ∈ Subgroup.normalizer (E : Set G) := by
          apply mem_normalizer_of_map_conj_eq
          rw [← Subgroup.map_conj_map_conj, ← hconj]
          rw [Subgroup.map_conj_map_conj, mul_inv_cancel, map_conj_one]
        have hmap_h : E.map (MulAut.conj ((n * p⁻¹))⁻¹).toMonoidHom = E :=
          map_conj_eq_self_of_mem_normalizer ((Subgroup.normalizer (E : Set G)).inv_mem hhN)
        have hE_eq : E.map (MulAut.conj s).toMonoidHom = B := by
          rw [show E = B.map (MulAut.conj s⁻¹).toMonoidHom from rfl]
          rw [Subgroup.map_conj_map_conj, mul_inv_cancel, map_conj_one]
        have hshs : s * (n * p⁻¹) * s⁻¹ ∈ Subgroup.normalizer (B : Set G) := by
          apply mem_normalizer_of_map_conj_eq
          calc B.map (MulAut.conj (s * (n * p⁻¹) * s⁻¹)).toMonoidHom
              = (E.map (MulAut.conj s).toMonoidHom).map
                  (MulAut.conj (s * (n * p⁻¹) * s⁻¹)).toMonoidHom := by rw [hE_eq]
            _ = E.map (MulAut.conj ((s * (n * p⁻¹) * s⁻¹) * s)).toMonoidHom :=
                  Subgroup.map_conj_map_conj E s (s * (n * p⁻¹) * s⁻¹)
            _ = E.map (MulAut.conj (s * (n * p⁻¹))).toMonoidHom := by
                  rw [show (s * (n * p⁻¹) * s⁻¹) * s = s * (n * p⁻¹) by group]
            _ = (E.map (MulAut.conj ((n * p⁻¹))).toMonoidHom).map
                  (MulAut.conj s).toMonoidHom :=
                  (Subgroup.map_conj_map_conj E (n * p⁻¹) s).symm
            _ = (E.map (MulAut.conj ((n * p⁻¹))⁻¹).toMonoidHom).map
                  (MulAut.conj s).toMonoidHom := by
                  rw [map_conj_eq_self_of_mem_normalizer hhN,
                    map_conj_eq_self_of_mem_normalizer ((Subgroup.normalizer (E : Set G)).inv_mem hhN)]
            _ = E.map (MulAut.conj s).toMonoidHom := by rw [hmap_h]
            _ = B := hE_eq
        refine ⟨m * (s * (n * p⁻¹) * s⁻¹), ?_, s * p, ?_, ?_⟩
        · exact (Subgroup.normalizer (B : Set G)).mul_mem hm hshs
        · exact (𝔖.S : Subgroup G).mul_mem hs hp.1
        · rw [show n = (n * p⁻¹) * p by group]
          group
  obtain ⟨m, hm, s, hs, hcs⟩ := key c hc
  refine ⟨s, hs, ?_⟩
  rw [hcs] at hAc
  have h1 : (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj m).toMonoidHom = B := by
    rw [Subgroup.map_conj_map_conj]
    exact hAc
  calc A.map (MulAut.conj s).toMonoidHom
      = ((A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj m).toMonoidHom).map
          (MulAut.conj m⁻¹).toMonoidHom := by
          rw [map_conj_inv_map_conj]
    _ = B.map (MulAut.conj m⁻¹).toMonoidHom := by rw [h1]
    _ = B := map_conj_eq_self_of_mem_normalizer ((Subgroup.normalizer (B : Set G)).inv_mem hm)


end CFSG.GH72
