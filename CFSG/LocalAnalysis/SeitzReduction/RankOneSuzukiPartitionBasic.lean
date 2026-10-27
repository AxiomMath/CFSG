module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStartBasic
public import CFSG.LocalAnalysis.SteinbergBNGMSNormalRootData
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

namespace SzPartition

variable {G : Type*} [Group G]

theorem map_conj_zpowers (x g : G) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem map_conj_inv_zpowers (x g : G) :
    (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom = zpowers (g⁻¹ * x * g) := by
  rw [map_conj_zpowers, inv_inv]

theorem mem_sup_zpowers_cases {A₁ : Subgroup G} {t : G} (ht : t ∈ centralizer (A₁ : Set G))
    (ht2 : t ^ 2 = 1) {x : G} (hx : x ∈ A₁ ⊔ zpowers t) : x ∈ A₁ ∨ ∃ b ∈ A₁, x = b * t := by
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hx
  rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
  · left
    rwa [mul_one]
  · exact Or.inr ⟨y, hy, rfl⟩

theorem conj_mem_sup_zpowers {A₁ : Subgroup G} {t : G} (ht : t ∈ centralizer (A₁ : Set G))
    {x : G} (hx : x ∈ normalizer (A₁ : Set G)) (hxt : x * t = t * x) {y : G}
    (hy : y ∈ A₁ ⊔ zpowers t) : x * y * x⁻¹ ∈ A₁ ⊔ zpowers t := by
  obtain ⟨y₁, hy₁, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers ht hy
  have hxz : x * z * x⁻¹ = z := by
    rw [commute_of_mem_zpowers hz hxt, mul_inv_cancel_right]
  have e : x * (y₁ * z) * x⁻¹ = x * y₁ * x⁻¹ * z := by
    calc x * (y₁ * z) * x⁻¹ = x * y₁ * x⁻¹ * (x * z * x⁻¹) := by group
      _ = x * y₁ * x⁻¹ * z := by rw [hxz]
  rw [e]
  exact mul_mem_sup ((mem_normalizer_iff.mp hx y₁).mp hy₁) hz

theorem mem_normalizer_sup_zpowers {A₁ : Subgroup G} {t : G}
    (ht : t ∈ centralizer (A₁ : Set G)) {x : G} (hx : x ∈ normalizer (A₁ : Set G))
    (hxt : x * t = t * x) : x ∈ normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G) := by
  have hxt' : x⁻¹ * t = t * x⁻¹ := (Commute.inv_left hxt).eq
  refine mem_normalizer_iff.mpr fun y =>
    ⟨fun hy => conj_mem_sup_zpowers ht hx hxt hy, fun hy => ?_⟩
  have h1 := conj_mem_sup_zpowers ht (inv_mem hx) hxt' hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

theorem exists_mem_normalizer_not_mem_of_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    {H T : Subgroup G} (hTH : T ≤ H) (hT : ∃ P : Sylow p H, (P : Subgroup H) = T.subgroupOf H)
    (hnot : ¬ ∃ S : Sylow p G, (S : Subgroup G) = T) :
    ∃ y ∈ normalizer (T : Set G), y ∉ H := by
  obtain ⟨P, hP⟩ := hT
  have hTp : IsPGroup p T := by
    have hP' := P.isPGroup'
    rw [hP] at hP'
    exact hP'.of_equiv (subgroupOfEquivOfLe hTH)
  obtain ⟨S, hTS⟩ := hTp.exists_le_sylow
  have hne : T ≠ S := fun h => hnot ⟨S, h.symm⟩
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne ?_
    exact le_antisymm hTS (subgroupOf_eq_top.mp htop)
  obtain ⟨y, hyN, hyT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := S) _ hlt)
  rw [← subgroupOf_normalizer_eq hTS, mem_subgroupOf] at hyN
  refine ⟨y, hyN, fun hyH => hyT (mem_subgroupOf.mpr ?_)⟩
  set W := T ⊔ zpowers (y : G) with hW
  have hWH : W ≤ H := sup_le hTH (zpowers_le.mpr hyH)
  have hWp : IsPGroup p W := S.isPGroup'.to_le (sup_le hTS (zpowers_le.mpr y.2))
  have hWp' : IsPGroup p (W.subgroupOf H) := hWp.of_equiv (subgroupOfEquivOfLe hWH).symm
  have hle : (P : Subgroup H) ≤ W.subgroupOf H := by
    rw [hP]
    intro x hx
    exact mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))
  have heq := P.is_maximal' hWp' hle
  rw [hP] at heq
  have hyW : (y : G) ∈ W := mem_sup_right (mem_zpowers (y : G))
  have hyH' : (⟨y, hyH⟩ : H) ∈ W.subgroupOf H := mem_subgroupOf.mpr hyW
  rw [heq] at hyH'
  exact mem_subgroupOf.mp hyH'

end SzPartition

open SzPartition

variable {G : Type*} [Group G]

structure SzPartitionData (A₁ : Subgroup G) (t : G) : Prop where
  sq_eq_one : t ^ 2 = 1
  mem_centralizer : t ∈ centralizer (A₁ : Set G)
  conj_not_mem : ∀ g : G, g⁻¹ * t * g ∉ A₁
  fusion : ∀ g : G, g⁻¹ * t * g ∈ A₁ ⊔ zpowers t →
    ∃ n ∈ normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G), n⁻¹ * t * n = g⁻¹ * t * g
  torus : ∀ b ∈ A₁, ∀ b' ∈ A₁, b ≠ 1 → b' ≠ 1 →
    ∃ x ∈ normalizer (A₁ : Set G), x * t = t * x ∧ x * b * x⁻¹ = b'
  exists_conj : ∃ b ∈ A₁, b ≠ 1 ∧ ∃ g : G, g⁻¹ * t * g = b * t

namespace SzPartitionData

variable {A₁ : Subgroup G} {t : G}

theorem not_mem (hD : SzPartitionData A₁ t) : t ∉ A₁ := by
  simpa using hD.conj_not_mem 1

theorem mul_ne_one (hD : SzPartitionData A₁ t) {b : G} (hb : b ∈ A₁) : b * t ≠ 1 := by
  intro h
  apply hD.not_mem
  rw [eq_inv_of_mul_eq_one_right h]
  exact inv_mem hb

theorem exists_conj_eq (hD : SzPartitionData A₁ t) {b : G} (hb : b ∈ A₁) :
    ∃ g : G, g⁻¹ * t * g = b * t := by
  by_cases hb1 : b = 1
  · exact ⟨1, by rw [hb1]; group⟩
  obtain ⟨b₀, hb₀, hb₀1, g₀, hg₀⟩ := hD.exists_conj
  obtain ⟨x, -, hxt, hxb⟩ := hD.torus b₀ hb₀ b hb hb₀1 hb1
  refine ⟨g₀ * x⁻¹, ?_⟩
  calc (g₀ * x⁻¹)⁻¹ * t * (g₀ * x⁻¹) = x * (g₀⁻¹ * t * g₀) * x⁻¹ := by group
    _ = x * b₀ * x⁻¹ * (x * t * x⁻¹) := by rw [hg₀]; group
    _ = b * t := by rw [hxb, hxt, mul_inv_cancel_right]

theorem sq_mul_eq_one (hD : SzPartitionData A₁ t) {b : G} (hb : b ∈ A₁) : (b * t) ^ 2 = 1 := by
  obtain ⟨g, hg⟩ := hD.exists_conj_eq hb
  rw [← hg, sq]
  calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    _ = 1 := by rw [← sq, hD.sq_eq_one]; group

theorem zpowers_mem : zpowers t ∈ gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t) :=
  ⟨1, by rw [inv_one, map_one]; exact (Subgroup.map_id _).symm, le_sup_right⟩

theorem mem_iff (hD : SzPartitionData A₁ t) {Q : Subgroup G} :
    Q ∈ gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t) ↔ ∃ b ∈ A₁, Q = zpowers (b * t) := by
  constructor
  · rintro ⟨g, rfl, hle⟩
    rw [map_conj_inv_zpowers] at hle ⊢
    rcases mem_sup_zpowers_cases hD.mem_centralizer hD.sq_eq_one
      (zpowers_le.mp hle) with h1 | ⟨b, hb, he⟩
    · exact absurd h1 (hD.conj_not_mem g)
    · exact ⟨b, hb, by rw [he]⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨g, hg⟩ := hD.exists_conj_eq hb
    refine ⟨g, by rw [map_conj_inv_zpowers, hg], ?_⟩
    exact zpowers_le.mpr (mul_mem_sup hb (mem_zpowers t))

theorem eq_of_zpowers_eq (hD : SzPartitionData A₁ t) {b b' : G} (hb : b ∈ A₁) (hb' : b' ∈ A₁)
    (h : zpowers (b * t) = zpowers (b' * t)) : b = b' := by
  have hmem : b' * t ∈ zpowers (b * t) := h ▸ mem_zpowers _
  rcases mem_zpowers_involution_eq_one_or_eq (hD.sq_mul_eq_one hb) hmem with h1 | h1
  · exact absurd h1 (hD.mul_ne_one hb')
  · exact (mul_right_cancel h1).symm

theorem ncard_eq (hD : SzPartitionData A₁ t) :
    (gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t)).ncard = Nat.card A₁ := by
  have himage : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t) =
      (fun b => zpowers (b * t)) '' (A₁ : Set G) := by
    ext Q
    rw [hD.mem_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  have hinj : Set.InjOn (fun b => zpowers (b * t)) (A₁ : Set G) :=
    fun b hb b' hb' h => hD.eq_of_zpowers_eq hb hb' h
  rw [himage, hinj.ncard_image, ← Nat.card_coe_set_eq]
  rfl

theorem normalizer_le (hD : SzPartitionData A₁ t) :
    normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (A₁ : Set G) := by
  have key : ∀ n ∈ normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G), ∀ b ∈ A₁,
      n * b * n⁻¹ ∈ A₁ := by
    intro n hn b hb
    have hV : n * b * n⁻¹ ∈ A₁ ⊔ zpowers t := (mem_normalizer_iff.mp hn b).mp (mem_sup_left hb)
    rcases mem_sup_zpowers_cases hD.mem_centralizer hD.sq_eq_one hV with h1 | ⟨b', hb', he⟩
    · exact h1
    · exfalso
      obtain ⟨g, hg⟩ := hD.exists_conj_eq hb'
      apply hD.conj_not_mem (g * n)
      have e : (g * n)⁻¹ * t * (g * n) = b := by
        calc (g * n)⁻¹ * t * (g * n) = n⁻¹ * (g⁻¹ * t * g) * n := by group
          _ = n⁻¹ * (n * b * n⁻¹) * n := by rw [hg, he]
          _ = b := by group
      rw [e]
      exact hb
  intro n hn
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key n hn x hx, fun hx => ?_⟩
  have h1 := key n⁻¹ (inv_mem hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at h1

theorem exists_conj_t_eq (hD : SzPartitionData A₁ t) {n : G}
    (hn : n ∈ normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ c ∈ A₁, n * t * n⁻¹ = c * t := by
  have hV : n * t * n⁻¹ ∈ A₁ ⊔ zpowers t :=
    (mem_normalizer_iff.mp hn t).mp (mem_sup_right (mem_zpowers t))
  rcases mem_sup_zpowers_cases hD.mem_centralizer hD.sq_eq_one hV with h1 | h1
  · exact absurd (by rwa [inv_inv]) (hD.conj_not_mem n⁻¹)
  · exact h1

theorem map_conj_zpowers_eq_iff (hD : SzPartitionData A₁ t) (l : G) :
    (zpowers t).map (MulAut.conj l).toMonoidHom = zpowers t ↔ l * t = t * l := by
  rw [map_conj_zpowers]
  constructor
  · intro h
    have hmem : l * t * l⁻¹ ∈ zpowers t := by
      rw [← h]
      exact mem_zpowers _
    rcases mem_zpowers_involution_eq_one_or_eq hD.sq_eq_one hmem with h1 | h1
    · exfalso
      apply hD.not_mem
      rw [conj_eq_one_iff.mp h1]
      exact one_mem _
    · exact mul_inv_eq_iff_eq_mul.mp h1
  · intro h
    rw [h, mul_inv_cancel_right]

theorem map_conj_zpowers_mul {n c : G} (hnc : n * t * n⁻¹ = c * t) (b : G) :
    (zpowers (b * t)).map (MulAut.conj n).toMonoidHom = zpowers (n * b * n⁻¹ * c * t) := by
  rw [map_conj_zpowers]
  congr 1
  calc n * (b * t) * n⁻¹ = n * b * n⁻¹ * (n * t * n⁻¹) := by group
    _ = n * b * n⁻¹ * c * t := by rw [hnc]; group

theorem exists_smul_eq_zpowers (hD : SzPartitionData A₁ t)
    (Q : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t)) :
    ∃ l : normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G),
      ((l • Q : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t)) : Subgroup G) = zpowers t := by
  have hQ2 := Q.2
  obtain ⟨g, hQ, hle⟩ := hQ2
  rw [map_conj_inv_zpowers] at hQ
  have hs : g⁻¹ * t * g ∈ A₁ ⊔ zpowers t := hle (by rw [hQ]; exact mem_zpowers _)
  obtain ⟨n, hn, hnt⟩ := hD.fusion g hs
  refine ⟨⟨n, hn⟩, ?_⟩
  change (Q : Subgroup G).map (MulAut.conj n).toMonoidHom = zpowers t
  rw [hQ, ← hnt, map_conj_zpowers]
  congr 1
  group

theorem two_transitive (hD : SzPartitionData A₁ t) :
    ∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t), Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (A₁ ⊔ zpowers t) (zpowers t)).range,
        σ Q₁ = Z₁ ∧ σ Q₂ = Z₂ := by
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t),
      (R₀ : Subgroup G) = zpowers t := ⟨⟨zpowers t, zpowers_mem⟩, rfl⟩
  have htoR : ∀ Q : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t),
      ∃ l : normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G), l • Q = R₀ := fun Q => by
    obtain ⟨l, hl⟩ := hD.exists_smul_eq_zpowers Q
    exact ⟨l, Subtype.ext (hl.trans hR₀.symm)⟩
  have hne : ∀ Q : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t), Q ≠ R₀ →
      ∃ b ∈ A₁, b ≠ 1 ∧ (Q : Subgroup G) = zpowers (b * t) := by
    intro Q hQ
    obtain ⟨b, hb, hQb⟩ := hD.mem_iff.mp Q.2
    refine ⟨b, hb, fun hb1 => hQ (Subtype.ext ?_), hQb⟩
    rw [hQb, hR₀, hb1, one_mul]
  have hstab : ∀ b ∈ A₁, ∀ b' ∈ A₁, b ≠ 1 → b' ≠ 1 →
      ∃ e : normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G), e • R₀ = R₀ ∧
        ∀ Q : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t),
          (Q : Subgroup G) = zpowers (b * t) →
            ((e • Q : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t)) : Subgroup G) =
              zpowers (b' * t) := by
    intro b hb b' hb' hb1 hb'1
    obtain ⟨x, hxN, hxt, hxb⟩ := hD.torus b hb b' hb' hb1 hb'1
    have hxt' : x * t * x⁻¹ = t := by rw [hxt, mul_inv_cancel_right]
    refine ⟨⟨x, mem_normalizer_sup_zpowers hD.mem_centralizer hxN hxt⟩, Subtype.ext ?_,
      fun Q hQ => ?_⟩
    · change (R₀ : Subgroup G).map (MulAut.conj x).toMonoidHom = (R₀ : Subgroup G)
      rw [hR₀, map_conj_zpowers, hxt']
    · change (Q : Subgroup G).map (MulAut.conj x).toMonoidHom = zpowers (b' * t)
      rw [hQ, map_conj_zpowers]
      congr 1
      calc x * (b * t) * x⁻¹ = x * b * x⁻¹ * (x * t * x⁻¹) := by group
        _ = b' * t := by rw [hxb, hxt']
  intro Q₁ Q₂ Z₁ Z₂ hQ hZ
  obtain ⟨l₁, hl₁⟩ := htoR Q₁
  obtain ⟨l₂, hl₂⟩ := htoR Z₁
  have h1 : l₁ • Q₂ ≠ R₀ := fun h => hQ ((smul_left_cancel_iff l₁).mp (hl₁.trans h.symm))
  have h2 : l₂ • Z₂ ≠ R₀ := fun h => hZ ((smul_left_cancel_iff l₂).mp (hl₂.trans h.symm))
  obtain ⟨b, hb, hb1, hbQ⟩ := hne _ h1
  obtain ⟨b', hb', hb'1, hbZ⟩ := hne _ h2
  obtain ⟨e, he, heb⟩ := hstab b hb b' hb' hb1 hb'1
  refine ⟨gmsRootConjugateAction (A₁ ⊔ zpowers t) (zpowers t) (l₂⁻¹ * e * l₁), ⟨_, rfl⟩, ?_, ?_⟩
  · change (l₂⁻¹ * e * l₁) • Q₁ = Z₁
    rw [mul_smul, mul_smul, hl₁, he, inv_smul_eq_iff, hl₂]
  · change (l₂⁻¹ * e * l₁) • Q₂ = Z₂
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
    exact Subtype.ext ((heb _ hbQ).trans hbZ.symm)

theorem action_eq_one_iff (hD : SzPartitionData A₁ t)
    (l : normalizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G)) :
    gmsRootConjugateAction (A₁ ⊔ zpowers t) (zpowers t) l = 1 ↔
      (l : G) ∈ centralizer ((A₁ ⊔ zpowers t : Subgroup G) : Set G) := by
  constructor
  · intro hl
    have hfix : ∀ b ∈ A₁, (l : G) * (b * t) * (l : G)⁻¹ = b * t := by
      intro b hb
      have hQ : zpowers (b * t) ∈ gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t) :=
        hD.mem_iff.mpr ⟨b, hb, rfl⟩
      have h1 := congrArg (fun σ : Equiv.Perm (gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t)) =>
        ((σ ⟨_, hQ⟩ : gmsRootConjugates (A₁ ⊔ zpowers t) (zpowers t)) : Subgroup G)) hl
      change (zpowers (b * t)).map (MulAut.conj (l : G)).toMonoidHom = zpowers (b * t) at h1
      rw [map_conj_zpowers] at h1
      have hmem : (l : G) * (b * t) * (l : G)⁻¹ ∈ zpowers (b * t) := by
        rw [← h1]
        exact mem_zpowers _
      rcases mem_zpowers_involution_eq_one_or_eq (hD.sq_mul_eq_one hb) hmem with h2 | h2
      · exact absurd (conj_eq_one_iff.mp h2) (hD.mul_ne_one hb)
      · exact h2
    have ht : (l : G) * t * (l : G)⁻¹ = t := by simpa using hfix 1 (one_mem _)
    have hlt : (l : G) * t = t * l := mul_inv_eq_iff_eq_mul.mp ht
    have hconj : ∀ y ∈ A₁ ⊔ zpowers t, (l : G) * y * (l : G)⁻¹ = y := by
      intro y hy
      obtain ⟨y₁, hy₁, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers hD.mem_centralizer hy
      have hz' : (l : G) * z * (l : G)⁻¹ = z := by
        rw [commute_of_mem_zpowers hz hlt, mul_inv_cancel_right]
      have hy₁' : (l : G) * y₁ * (l : G)⁻¹ = y₁ := by
        calc (l : G) * y₁ * (l : G)⁻¹ =
            (l : G) * (y₁ * t) * (l : G)⁻¹ * ((l : G) * t * (l : G)⁻¹)⁻¹ := by group
          _ = y₁ := by rw [hfix y₁ hy₁, ht]; group
      calc (l : G) * (y₁ * z) * (l : G)⁻¹ =
          (l : G) * y₁ * (l : G)⁻¹ * ((l : G) * z * (l : G)⁻¹) := by group
        _ = y₁ * z := by rw [hy₁', hz']
    exact mem_centralizer_iff.mpr fun y hy => (mul_inv_eq_iff_eq_mul.mp (hconj y hy)).symm
  · intro hl
    refine Equiv.ext fun Q => Subtype.ext ?_
    change (Q : Subgroup G).map (MulAut.conj (l : G)).toMonoidHom = (Q : Subgroup G)
    have hQ2 := Q.2
    obtain ⟨-, -, hle⟩ := hQ2
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (l : G) * y * (l : G)⁻¹ ∈ (Q : Subgroup G)
      rw [← mem_centralizer_iff.mp hl y (hle hy), mul_inv_cancel_right]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      change (l : G) * x * (l : G)⁻¹ = x
      rw [← mem_centralizer_iff.mp hl x (hle hx), mul_inv_cancel_right]

end SzPartitionData

namespace SzRootCoords

variable {K : Type*} [Field K] [Fintype K] {T₁ : Subgroup G} {a : ℕ} {d : G} {u v : G → K}
  {κ : K}

theorem exists_pow_conj_eq_szA₁ (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    {b b' : G} (hb : b ∈ szA₁ T₁) (hb' : b' ∈ szA₁ T₁) (hb1 : b ≠ 1) (hb'1 : b' ≠ 1) :
    ∃ k : ℕ, (d ^ k)⁻¹ * b * d ^ k = b' := by
  have hpow : ∀ k : ℕ, ∀ x ∈ szA₁ T₁, (d ^ k)⁻¹ * x * d ^ k ∈ szA₁ T₁ ∧
      v ((d ^ k)⁻¹ * x * d ^ k) = (κ ^ (2 ^ (a + 1) + 1)) ^ k * v x := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      have e : (d ^ (k + 1))⁻¹ * x * d ^ (k + 1) = d⁻¹ * ((d ^ k)⁻¹ * x * d ^ k) * d := by
        rw [pow_succ]; group
      rw [e]
      refine ⟨hc.conj_mem_szA₁ ha hK h1, ?_⟩
      rw [hc.v_conj_szA₁ ha hK h1, h2, pow_succ]
      ring
  have hvb : v b ≠ 0 := fun h0 => hb1 (hc.eq_one_of_v_eq_zero ha hK hb h0)
  have hvb' : v b' ≠ 0 := fun h0 => hb'1 (hc.eq_one_of_v_eq_zero ha hK hb' h0)
  obtain ⟨m, hm⟩ := hμ (v b' / v b) (div_ne_zero hvb' hvb)
  obtain ⟨h1, h2⟩ := hpow m b hb
  refine ⟨m, hc.inj _ (szA₁_le T₁ h1) _ (szA₁_le T₁ hb') ?_ ?_⟩
  · rw [hc.u_eq_zero_of_mem_szA₁ ha hK h1, hc.u_eq_zero_of_mem_szA₁ ha hK hb']
  · rw [h2, hm, div_mul_cancel₀ _ hvb]

theorem torus_of_generator [Finite G] (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) {t : G}
    (hdt : d * t = t * d) :
    ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, b ≠ 1 → b' ≠ 1 →
      ∃ x ∈ normalizer (szA₁ T₁ : Set G), x * t = t * x ∧ x * b * x⁻¹ = b' := by
  have hdN : d ∈ normalizer (szA₁ T₁ : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => hc.conj_mem_szA₁ ha hK hx
  intro b hb b' hb' hb1 hb'1
  obtain ⟨k, hk⟩ := hc.exists_pow_conj_eq_szA₁ ha hK hμ hb hb' hb1 hb'1
  refine ⟨(d ^ k)⁻¹, inv_mem (pow_mem hdN k), ((Commute.pow_left hdt k).inv_left).eq, ?_⟩
  rw [inv_inv]
  exact hk

end SzRootCoords

end CFSG.SeitzReduction.RankOne
