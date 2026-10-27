module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporRank
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

section Elementary

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem card_inf_mul_card_map (E N : Subgroup G) [N.Normal] :
    Nat.card (E ⊓ N : Subgroup G) * Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E := by
  set f : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype with hf
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = E.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card f.ker = Nat.card (E ⊓ N : Subgroup G) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : f.ker => (⟨((u : E) : G), (u : E).2, ?_⟩ : (E ⊓ N : Subgroup G))) ⟨?_, ?_⟩)
    · have h2 : f (u : E) = 1 := u.2
      have h3 : QuotientGroup.mk' N ((u : E) : G) = 1 := h2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun z : (E ⊓ N : Subgroup G) => (z : G)) hab))
    · rintro ⟨g, hgE, hgN⟩
      refine ⟨⟨⟨g, hgE⟩, ?_⟩, rfl⟩
      change QuotientGroup.mk' N g = 1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← hker, ← hrange]
  exact h1

theorem exists_card_eq_pow_of_isElemAbelian [Fact p.Prime] {E : Subgroup G}
    (hE : IsElemAbelian p E) : ∃ m : ℕ, Nat.card E = p ^ m :=
  exists_card_eq_pow_of_forall_pow_eq_one hE.2

theorem crossRank_isElemAbelian_of_le {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => hE.2 y (hFE hy)⟩
  apply Subtype.ext
  exact setLike_mul_comm (hFE a.2) (hFE b.2)

theorem crossRank_isElemAbelian_subgroupOf {E : Subgroup G} (hE : IsElemAbelian p E) (L : Subgroup G) :
    IsElemAbelian p (E.subgroupOf L) := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have ha : ((a : L) : G) ∈ E := a.2
    have hb : ((b : L) : G) ∈ E := b.2
    exact setLike_mul_comm ha hb
  · apply Subtype.ext
    have := hE.2 (y : G) hy
    simpa using this

theorem exists_isElemAbelian_subgroupOf {E : Subgroup G} (hE : IsElemAbelian p E)
    (L : Subgroup G) :
    ∃ F : Subgroup L, IsElemAbelian p F ∧ Nat.card F = Nat.card (E ⊓ L : Subgroup G) ∧
      ∀ y : L, y ∈ F ↔ (y : G) ∈ E := by
  refine ⟨E.subgroupOf L, crossRank_isElemAbelian_subgroupOf hE L, ?_, fun y => Iff.rfl⟩
  refine Nat.card_congr (Equiv.ofBijective
    (fun u : E.subgroupOf L => (⟨((u : L) : G), u.2, (u : L).2⟩ : (E ⊓ L : Subgroup G)))
    ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (E ⊓ L : Subgroup G) => (z : G)) hab))
  · rintro ⟨g, hgE, hgL⟩
    exact ⟨⟨⟨g, hgL⟩, hgE⟩, rfl⟩

end Elementary

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem exists_conj_mem_of_sylow_abelian [Fact p.Prime]
    (hab : ∀ P : Sylow p G, IsMulCommutative (P : Subgroup G)) {F : Subgroup G}
    (hF : IsElemAbelian p F) (hFcard : Nat.card F = p ^ CFSG.Open.pRank p (⊤ : Subgroup G))
    {y : G} (hy : y ^ p = 1) : ∃ g : G, g * y * g⁻¹ ∈ F := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hzp : IsPGroup p (Subgroup.zpowers y) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨P₁, hP₁⟩ := hzp.exists_le_sylow
  have hyP₁ : y ∈ (P₁ : Subgroup G) := hP₁ (Subgroup.mem_zpowers y)
  have hFp : IsPGroup p F := fun z => ⟨1, Subtype.ext (by simpa using hF.2 z z.2)⟩
  obtain ⟨P₂, hP₂⟩ := hFp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₁ P₂
  refine ⟨g, ?_⟩
  have hmem : g * y * g⁻¹ ∈ (P₂ : Subgroup G) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
    have := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P₁ : Subgroup G) hyP₁
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  haveI : IsMulCommutative (P₂ : Subgroup G) := hab P₂
  let Ω : Subgroup G :=
    { carrier := {z | z ∈ (P₂ : Subgroup G) ∧ z ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        rw [Commute.mul_pow (setLike_mul_comm ha hb), ha', hb', one_mul]
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hΩmem : ∀ z, z ∈ Ω ↔ z ∈ (P₂ : Subgroup G) ∧ z ^ p = 1 := fun z => Iff.rfl
  have hΩ : IsElemAbelian p Ω := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ((hΩmem z).1 hz).2⟩
    apply Subtype.ext
    exact setLike_mul_comm (((hΩmem _).1 a.2).1) (((hΩmem _).1 b.2).1)
  have hFΩ : F ≤ Ω := fun z hz => (hΩmem z).2 ⟨hP₂ hz, hF.2 z hz⟩
  obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian hΩ
  have hjle : j ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank hp1 le_top hΩ hj
  have hΩF : Nat.card Ω ≤ Nat.card F := by
    rw [hj, hFcard]
    exact Nat.pow_le_pow_right hp.pos hjle
  have hFeq : F = Ω := Subgroup.eq_of_le_of_card_ge hFΩ hΩF
  rw [hFeq, hΩmem]
  refine ⟨hmem, ?_⟩
  rw [conj_pow, hy]
  group

theorem isMulCommutative_sylow_of_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G')
    (h : ∀ R : Sylow p G', IsMulCommutative (R : Subgroup G')) [Fact p.Prime] (P : Sylow p G) :
    IsMulCommutative (P : Subgroup G) := by
  let R : Sylow p G' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  haveI : IsMulCommutative (R : Subgroup G') := h R
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  have ha : e (a : G) ∈ (R : Subgroup G') := ⟨a, a.2, rfl⟩
  have hb : e (b : G) ∈ (R : Subgroup G') := ⟨b, b.2, rfl⟩
  apply e.injective
  have := setLike_mul_comm ha hb
  simpa using this

theorem isMulCommutative_sylow_of_mulEquiv_isCyclic {G' : Type*} [Group G'] (e : G ≃* G')
    (h : ∀ R : Sylow p G', IsCyclic (R : Subgroup G')) [Fact p.Prime] (P : Sylow p G) :
    IsMulCommutative (P : Subgroup G) :=
  isMulCommutative_sylow_of_mulEquiv e (fun R => by
    haveI := h R
    exact ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩) P

theorem three_le_pRank_centralizer_of_sylow_abelian [Fact p.Prime]
    (hab : ∀ P : Sylow p G, IsMulCommutative (P : Subgroup G))
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G)) {x : G} (hx : x ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set G)) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hzp : IsPGroup p (Subgroup.zpowers x) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hxP : x ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers x)
  haveI : IsMulCommutative (P : Subgroup G) := hab P
  have hrk := (CFSG.SectionRank.pRank_sylow P).1
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact setLike_mul_comm hz hxP
  calc 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := h3
    _ = CFSG.Open.pRank p (P : Subgroup G) := hrk.symm
    _ ≤ CFSG.Open.pRank p (centralizer ({x} : Set G)) :=
        CFSG.SectionRank.pRank_mono hp1 hPC

end Sylow

section Assembly

variable {p : ℕ} {X : Type} [Group X] [Finite X]

theorem false_of_cross_core [Fact p.Prime] (L : Subgroup X) [L.Normal]
    (hOut : CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ L)) ≤ 1)
    (hR3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) →
      ∀ y : L, orderOf y = p → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L)))
    (hSAb : CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
      ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L))
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {x : X} (hxL : x ∈ L) (hx : orderOf x = p)
    (hxc : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) : False := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  set y : L := ⟨x, hxL⟩ with hy
  have hyord : orderOf y = p := by
    rw [← hx, ← Subgroup.orderOf_coe]
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have hyp : y ^ p = 1 := hyord ▸ pow_orderOf_eq_one y
  by_cases hρ : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)
  ·
    have h1 := hR3 hρ y hyord
    have h2 : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤
        CFSG.Open.pRank p ((centralizer ({y} : Set L)).map L.subtype) :=
      CFSG.SectionRank.pRank_le_map hp1 L.subtype L.subtype_injective _
    have h4 : (centralizer ({y} : Set L)).map L.subtype ≤ centralizer ({x} : Set X) := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.1 hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hw'
    have h5 := CFSG.SectionRank.pRank_mono hp1 h4
    omega
  · replace hρ := not_le.1 hρ
    obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup X)
    set m := CFSG.Open.pRank p (⊤ : Subgroup X) with hm
    have hEL : IsElemAbelian p (E ⊓ L) := crossRank_isElemAbelian_of_le hE inf_le_left
    obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hEL
    have hEmap : IsElemAbelian p (E.map (QuotientGroup.mk' L)) :=
      CFSG.SectionRank.isElemAbelian_map hE _
    obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian hEmap
    have hmul := card_inf_mul_card_map E L
    rw [hk, hj, hEcard, ← pow_add] at hmul
    have hkj : k + j = m := (Nat.pow_right_injective hp1 hmul)
    have hjle : j ≤ 1 :=
      (CFSG.SectionRank.le_pRank hp1 le_top hEmap hj).trans hOut
    obtain ⟨F, hF, hFcard, hFmem⟩ := exists_isElemAbelian_subgroupOf hE L
    have hkρ : k ≤ CFSG.Open.pRank p (⊤ : Subgroup L) :=
      CFSG.SectionRank.le_pRank hp1 le_top hF (by rw [hFcard, hk])
    have hk2 : k = 2 ∧ CFSG.Open.pRank p (⊤ : Subgroup L) = 2 := by omega
    have hab := hSAb hk2.2
    have hFρ : Nat.card F = p ^ CFSG.Open.pRank p (⊤ : Subgroup L) := by
      rw [hFcard, hk, hk2.1, hk2.2]
    obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_abelian hab hF hFρ hyp
    have hgE : (g : X) * x * (g : X)⁻¹ ∈ E := (hFmem _).1 hg
    set E' : Subgroup X := E.map (MulAut.conj (g : X)⁻¹).toMonoidHom with hE'
    have hE'a : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hE _
    have hE'card : Nat.card E' = p ^ m := by
      rw [hE', Subgroup.card_map_of_injective (MulAut.conj (g : X)⁻¹).injective, hEcard]
    have hxE' : x ∈ E' := by
      refine ⟨(g : X) * x * (g : X)⁻¹, hgE, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    haveI : IsMulCommutative E' := hE'a.1
    have hE'C : E' ≤ centralizer ({x} : Set X) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact setLike_mul_comm hz hxE'
    have h6 := CFSG.SectionRank.le_pRank hp1 hE'C hE'a hE'card
    omega

end Assembly

end CFSG.LocalAnalysis.RankFourTheoremC
