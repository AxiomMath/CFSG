module

public import CFSG.GH74.E2.BoxT5Aux

public section

namespace CFSG.GH74.E2.Box

open Subgroup CFSG.GH74.GLS

section Hii

variable {G : Type} [Group G] [Finite G] {K A B M : Subgroup G}

theorem CommPair.hi (S : Setup K) (h : CommPair K A B) {P Q : Subgroup G} (hP : P = A ∨ P = B)
    (hQ : Q = A ∨ Q = B) {t g : G} (h2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) (htc : t ∉ Subgroup.center G)
    (c1 : ∀ a ∈ P, t * a = a * t) (c2 : ∀ a ∈ Q, (g⁻¹ * t * g) * a = a * (g⁻¹ * t * g)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have ht1 : t ≠ 1 := fun h1 => htc (h1 ▸ Subgroup.one_mem _)
  obtain ⟨m, hm⟩ := exists_involution_pow h2 ht1
  have hPconj : ConjOf K P := by
    rcases hP with rfl | rfl
    · exact h.convA
    · exact h.convB
  have hQconj : ConjOf K Q := by
    rcases hQ with rfl | rfl
    · exact h.convA
    · exact h.convB
  have hyP : t ^ m ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact (Commute.pow_left (c1 a ha) m).eq.symm
  have hconj : (g⁻¹ * t * g) ^ m = g⁻¹ * t ^ m * g := by
    simpa using (conj_pow (a := g⁻¹) (b := t) (i := m))
  have hyQ : t ^ m ∈ centralizer ((conjugate Q g⁻¹ : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, AS16.mem_conjugate_iff'] at hz
    have hz' : g⁻¹ * z * g ∈ Q := by simpa using hz
    have h3 := (Commute.pow_left (c2 _ hz') m).eq
    rw [hconj] at h3
    calc z * t ^ m = g * ((g⁻¹ * z * g) * (g⁻¹ * t ^ m * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t ^ m * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [← h3]
      _ = t ^ m * z := by group
  have hEq : P = conjugate Q g⁻¹ :=
    S.invol_unique hm hPconj (hQconj.conj g⁻¹) hyP hyQ
  have hcarry : conjugate P g = Q := by
    have := conj_inv_eq (H := Q) (K := P) (a := g⁻¹) hEq.symm
    simpa using this
  exact swapGrp_le_normalizer A B (h.carry_mem_swapGrp S hP hQ hcarry)

theorem no_index_two_of_simple {P : Type*} [Group P] [Finite P] [IsSimpleGroup P]
    (hP : 2 < Nat.card P) (F : Subgroup P) : F.index ≠ 2 := by
  intro h2
  have hn : F.Normal := Subgroup.normal_of_index_eq_two h2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F with hb | ht
  · rw [hb, Subgroup.index_bot] at h2
    omega
  · rw [ht, Subgroup.index_top] at h2
    omega

omit [Finite G] in
theorem index_fixGrp_sub {A B P : Subgroup G} (hAB : A ≠ B) (hP : P ≤ swapGrp A B) {p0 : G}
    (hp0 : p0 ∈ P) (hA : conjugate A p0 = B) (hB : conjugate B p0 = A) :
    ((fixGrp A B).subgroupOf P).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨p0, hp0⟩, ?_⟩
  rintro ⟨b, hb⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  show Xor (b * p0 ∈ fixGrp A B) (b ∈ fixGrp A B)
  rcases hP hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · have hbfix : b ∈ fixGrp A B := ⟨hb1, hb2⟩
    have hbg : b * p0 ∉ fixGrp A B := by
      rintro ⟨h1, -⟩
      rw [conj_mul, hb1, hA] at h1
      exact hAB h1.symm
    exact Or.inr ⟨hbfix, hbg⟩
  · have hbfix : b ∉ fixGrp A B := by
      rintro ⟨h1, -⟩
      rw [hb1] at h1
      exact hAB h1.symm
    have hbg : b * p0 ∈ fixGrp A B := by
      refine ⟨?_, ?_⟩
      · rw [conj_mul, hb1, hB]
      · rw [conj_mul, hb2, hA]
    exact Or.inl ⟨hbg, hbfix⟩

theorem CommPair.perfect_fixes (S : Setup K) {L L' P : Subgroup G} (hLL' : CommPair K L L')
    (hP : ConjOf K P) (hPswap : ∀ p ∈ P, p ∈ swapGrp L L') : ∀ p ∈ P, conjugate L p = L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p0, hp0, hne⟩ := hcon
  have hp0s := hPswap p0 hp0
  have hLp0 : conjugate L p0 = L' := by
    rcases hp0s with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hne
    · exact h1
  have hL'p0 : conjugate L' p0 = L := hLL'.swap S hLp0
  have hidx := index_fixGrp_sub (hLL'.ne S) (fun p hp => hPswap p hp) hp0 hLp0 hL'p0
  have := S.simple_of hP
  exact no_index_two_of_simple (S.card_gt_two hP) _ hidx

omit [Finite G] in
theorem card_conjOf {K P : Subgroup G} (h : ConjOf K P) : Nat.card ↥P = Nat.card ↥K := by
  obtain ⟨g, rfl⟩ := h
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem CommPair.false_of_diagonal
    (S : Setup K) {L P P' : Subgroup G} (hLc : ConjOf K L)
    (hPP' : CommPair K P P') (hPN : P ≤ normalizer (L : Set G)) (hPL : P ⊓ L = ⊥)
    (hPC : P ⊓ centralizer (L : Set G) = ⊥) : False := by
  have hPconj : ConjOf K P := hPP'.convA
  obtain ⟨p, hpP, hp2⟩ := AS16.exists_involution_of_isQuasisimple (S.quasi_of hPconj)
  obtain ⟨w, hwL, hw⟩ := S.inner_action hLc hPconj hPN p hpP
  have hc : ∀ x ∈ L, (w⁻¹ * p) * x = x * (w⁻¹ * p) := by
    intro x hx
    have := hw x hx
    calc (w⁻¹ * p) * x = w⁻¹ * (p * x * p⁻¹) * p := by group
      _ = w⁻¹ * (w * x * w⁻¹) * p := by rw [this]
      _ = x * (w⁻¹ * p) := by group
  have hcw : (w⁻¹ * p) * w = w * (w⁻¹ * p) := hc w hwL
  have hwp : w * p = p * w := by
    calc w * p = w * (w * (w⁻¹ * p)) := by group
      _ = w * ((w⁻¹ * p) * w) := by rw [hcw]
      _ = (w * (w⁻¹ * p)) * w := by group
      _ = p * w := by group
  have hpP' : p ∈ centralizer (P' : Set G) := by
    rw [mem_centralizer_iff]
    intro z hz
    exact (hPP'.commute p hpP z hz).symm
  have hcomp : IsCompCen p P' := S.term_of hPP'.convB p hpP' hp2
  have huniq : ∀ K' : Subgroup G, IsCompCen p K' → K' = P' :=
    (S.comp G S.hyp p hp2 P' hcomp).2
  have hwcen : w ∈ Cen p := mem_Cen'.2 hwp
  have hfixP' : conjugate P' w = P' := conjugate_eq_of_unique hcomp huniq hwcen
  have hfixP : conjugate P w = P := hPP'.symm.fix S hfixP'
  have hwN : w ∈ normalizer (P : Set G) := (AS16.conjugate_eq_self_iff P w).1 hfixP
  have hwcP : ∀ p' ∈ P, w * p' = p' * w := by
    intro p' hp'
    have h0 : w * p' * w⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hwN p').1 hp'
    have h1 : w * p' * w⁻¹ * p'⁻¹ ∈ P := P.mul_mem h0 (P.inv_mem hp')
    have h2 : w * p' * w⁻¹ * p'⁻¹ ∈ L := by
      have hmem : p' * w⁻¹ * p'⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hPN hp') _).1 (L.inv_mem hwL)
      have := L.mul_mem hwL hmem
      have e : w * (p' * w⁻¹ * p'⁻¹) = w * p' * w⁻¹ * p'⁻¹ := by group
      rwa [e] at this
    have h3 : w * p' * w⁻¹ * p'⁻¹ ∈ P ⊓ L := ⟨h1, h2⟩
    rw [hPL, Subgroup.mem_bot] at h3
    calc w * p' = (w * p' * w⁻¹ * p'⁻¹) * (p' * w) := by group
      _ = p' * w := by rw [h3, one_mul]
  have hpcentral : ∀ p' ∈ P, p' * p * p'⁻¹ = p := by
    intro p' hp'
    have hc'P : p' * p * p'⁻¹ ∈ P := P.mul_mem (P.mul_mem hp' hpP) (P.inv_mem hp')
    have hq : (p' * p * p'⁻¹)⁻¹ * p ∈ P ⊓ centralizer (L : Set G) := by
      refine ⟨P.mul_mem (P.inv_mem hc'P) hpP, ?_⟩
      refine mem_centralizer_iff.2 ?_
      intro x hx
      have hy : p'⁻¹ * x * p' ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hPN (P.inv_mem hp')) x).1 hx
        simpa using this
      have e1 : p * (p'⁻¹ * x * p') * p⁻¹ = w * (p'⁻¹ * x * p') * w⁻¹ := hw _ hy
      have hwp' : p' * w * p'⁻¹ = w := by
        calc p' * w * p'⁻¹ = (w * p') * p'⁻¹ := by rw [← hwcP p' hp']
          _ = w := by group
      have e2 : (p' * p * p'⁻¹) * x * (p' * p * p'⁻¹)⁻¹ = p * x * p⁻¹ := by
        calc (p' * p * p'⁻¹) * x * (p' * p * p'⁻¹)⁻¹
            = p' * (p * (p'⁻¹ * x * p') * p⁻¹) * p'⁻¹ := by group
          _ = p' * (w * (p'⁻¹ * x * p') * w⁻¹) * p'⁻¹ := by rw [e1]
          _ = (p' * w * p'⁻¹) * x * (p' * w * p'⁻¹)⁻¹ := by group
          _ = w * x * w⁻¹ := by rw [hwp']
          _ = p * x * p⁻¹ := (hw x hx).symm
      calc x * ((p' * p * p'⁻¹)⁻¹ * p)
          = (p' * p * p'⁻¹)⁻¹ * ((p' * p * p'⁻¹) * x * (p' * p * p'⁻¹)⁻¹) * p := by group
        _ = (p' * p * p'⁻¹)⁻¹ * (p * x * p⁻¹) * p := by rw [e2]
        _ = ((p' * p * p'⁻¹)⁻¹ * p) * x := by group
    rw [hPC, Subgroup.mem_bot] at hq
    exact inv_mul_eq_one.1 hq
  have hz : p = 1 := by
    refine S.centerFree_of hPconj p hpP fun y hy => ?_
    have := hpcentral y hy
    calc p * y = (y * p * y⁻¹) * y := by rw [this]
      _ = y * p := by group
  rw [hz, orderOf_one] at hp2
  omega

theorem CommPair.trichotomy
    (S : Setup K) {L L' P P' : Subgroup G} (hLL' : CommPair K L L')
    (hPP' : CommPair K P P') (hPN : P ≤ normalizer (L : Set G)) : P = L ∨ P = L' := by
  have hPconj : ConjOf K P := hPP'.convA
  have hLconj : ConjOf K L := hLL'.convA
  have hsimple := S.simple_of hPconj
  have hYn : ((P ⊓ L).subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨P.mul_mem (P.mul_mem g.2 hx.1) (P.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (hPN g.2) x).1 hx.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P ⊓ L).subgroupOf P) with hb | ht
  · have hPL : P ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥P) ∈ (P ⊓ L).subgroupOf P := Subgroup.mem_subgroupOf.2 hx
      rw [hb, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    have hCn : ((P ⊓ centralizer (L : Set G)).subgroupOf P).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨P.mul_mem (P.mul_mem g.2 hx.1) (P.inv_mem g.2), ?_⟩
      refine mem_centralizer_iff.2 ?_
      intro l hl
      have hgl : (g : G)⁻¹ * l * (g : G) ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hPN (P.inv_mem g.2)) l).1 hl
        simpa using this
      have h1 := mem_centralizer_iff.1 hx.2 _ hgl
      calc l * ((g : G) * x * (g : G)⁻¹) = (g : G) * (((g : G)⁻¹ * l * g) * x) * (g : G)⁻¹ := by group
        _ = (g : G) * (x * ((g : G)⁻¹ * l * g)) * (g : G)⁻¹ := by rw [h1]
        _ = ((g : G) * x * (g : G)⁻¹) * l := by group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((P ⊓ centralizer (L : Set G)).subgroupOf P) with hb2 | ht2
    · exfalso
      have hPC : P ⊓ centralizer (L : Set G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hx.1⟩ : ↥P) ∈ (P ⊓ centralizer (L : Set G)).subgroupOf P :=
          Subgroup.mem_subgroupOf.2 hx
        rw [hb2, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      exact hPP'.false_of_diagonal S hLconj hPN hPL hPC
    · right
      have hPle : P ≤ centralizer (L : Set G) := by
        intro x hx
        have : (⟨x, hx⟩ : ↥P) ∈ (P ⊓ centralizer (L : Set G)).subgroupOf P := by
          rw [ht2]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 this).2
      obtain ⟨y, hyL, hy2⟩ := AS16.exists_involution_of_isQuasisimple (S.quasi_of hLconj)
      have hyP : y ∈ centralizer (P : Set G) := by
        rw [mem_centralizer_iff]
        intro x hx
        exact (mem_centralizer_iff.1 (hPle hx) y hyL).symm
      have h1 := S.term_of hPconj y hyP hy2
      have hle : centralizer (L : Set G) ≤ centralizer ({y} : Set G) :=
        Subgroup.centralizer_le (by simpa using hyL)
      have hcomp : IsCompIn (centralizer (L : Set G)) P := isCompIn_mono h1 hPle hle
      exact hLL'.uniqB S hPconj hcomp
  · left
    have hPle : P ≤ L := by
      intro x hx
      have : (⟨x, hx⟩ : ↥P) ∈ (P ⊓ L).subgroupOf P := by rw [ht]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).2
    exact Subgroup.eq_of_le_of_card_ge hPle (by rw [card_conjOf hPconj, card_conjOf hLconj])


theorem CommPair.hii
    (S : Setup K) (h : CommPair K A B) {P : Subgroup G} (hP : P = A ∨ P = B)
    {g : G}
    (hX : P ≤ (normalizer ((A ⊔ B : Subgroup G) : Set G)).map (MulAut.conj g⁻¹).toMonoidHom) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  obtain ⟨P', hPP'⟩ : ∃ P', CommPair K P P' := by
    rcases hP with rfl | rfl
    · exact ⟨B, h⟩
    · exact ⟨A, h.symm⟩
  have hPconj : ConjOf K P := hPP'.convA
  have hLL' : CommPair K (conjugate A g) (conjugate B g) := h.conj g
  have hPN : P ≤ normalizer ((conjugate A g ⊔ conjugate B g : Subgroup G) : Set G) := by
    have e : (normalizer ((A ⊔ B : Subgroup G) : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
        normalizer (((A ⊔ B).map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.map_equiv_normalizer_eq _ _
    rw [e] at hX
    have e2 : (A ⊔ B).map (MulAut.conj g⁻¹).toMonoidHom = conjugate A g ⊔ conjugate B g :=
      Subgroup.map_sup _ _ _
    rwa [e2] at hX
  have hswap : ∀ p ∈ P, p ∈ swapGrp (conjugate A g) (conjugate B g) := fun p hp =>
    hLL'.mem_swapGrp S (hLL'.conj_normalizer S (hPN hp) (Or.inl rfl))
  have hfix := hLL'.perfect_fixes S hPconj hswap
  have hPNL : P ≤ normalizer ((conjugate A g : Subgroup G) : Set G) := fun p hp =>
    (AS16.conjugate_eq_self_iff _ _).1 (hfix p hp)
  rcases hLL'.trichotomy S hPP' hPNL with hPL | hPL'
  · exact swapGrp_le_normalizer A B (h.carry_mem_swapGrp S (Or.inl rfl) hP hPL.symm)
  · exact swapGrp_le_normalizer A B (h.carry_mem_swapGrp S (Or.inr rfl) hP hPL'.symm)

end Hii

end CFSG.GH74.E2.Box
