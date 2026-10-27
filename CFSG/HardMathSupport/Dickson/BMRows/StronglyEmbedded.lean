module

public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.BenderSuzuki

@[expose] def IsMaximalTwoSubgroup {H : Type*} [Group H] (T L : Subgroup H) : Prop :=
  T ≤ L ∧ IsPGroup 2 T ∧ ∀ P : Subgroup H, P ≤ L → IsPGroup 2 P → T ≤ P → P = T

theorem IsMaximalTwoSubgroup.of_card {G : Type*} [Group G] {S L H : Subgroup G} [Finite H] {k : ℕ}
    (hSL : S ≤ L) (hLH : L ≤ H) (hS : Nat.card S = 2 ^ k) (hk : ¬ 2 ^ (k + 1) ∣ Nat.card H) :
    IsMaximalTwoSubgroup S L := by
  refine ⟨hSL, IsPGroup.of_card hS, fun P hPL hP hSP => ?_⟩
  haveI : Finite P := Finite.of_injective _ (Subgroup.inclusion_injective (hPL.trans hLH))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hdvd : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le (hPL.trans hLH)
  have hnk : n ≤ k := by
    by_contra h
    exact hk ((pow_dvd_pow 2 (by omega : k + 1 ≤ n)).trans (hn ▸ hdvd))
  have hcard : Nat.card P ≤ Nat.card S := by
    rw [hn, hS]
    exact Nat.pow_le_pow_right (by norm_num) hnk
  exact (Subgroup.eq_of_le_of_card_ge hSP hcard).symm

theorem IsMaximalTwoSubgroup.subgroupOf {G : Type*} [Group G] {S L H : Subgroup G}
    (hLH : L ≤ H) (hS : IsMaximalTwoSubgroup S L) :
    IsMaximalTwoSubgroup (S.subgroupOf H) (L.subgroupOf H) := by
  obtain ⟨hSL, hS2, hSmax⟩ := hS
  refine ⟨fun x hx => hSL hx, hS2.of_equiv (Subgroup.subgroupOfEquivOfLe (hSL.trans hLH)).symm,
    fun P hP hP2 hSP => ?_⟩
  have hPL : P.map H.subtype ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact hP hx
  have hSP' : S ≤ P.map H.subtype := fun s hs =>
    ⟨⟨s, hLH (hSL hs)⟩, hSP hs, rfl⟩
  have h := hSmax _ hPL (hP2.map _) hSP'
  rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective P, h]
  rfl

section Criterion

variable {H : Type*} [Group H]

private theorem mem_map_conj_iff {L : Subgroup H} {g x : H} :
    x ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem exists_conj_le [Finite H] {T L R : Subgroup H} (hT : IsMaximalTwoSubgroup T L)
    (hRL : R ≤ L) (hR : IsPGroup 2 R) : ∃ m ∈ L, ∀ r ∈ R, m * r * m⁻¹ ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hT2, hTmax⟩ := hT
  have hTl : IsPGroup 2 (T.subgroupOf L) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  obtain ⟨P, hP⟩ := hTl.exists_le_sylow
  have hPT : (P : Subgroup ↥L).map L.subtype = T :=
    hTmax _ (Subgroup.map_subtype_le _) (P.isPGroup'.map _) fun t ht =>
      Subgroup.mem_map.2 ⟨⟨t, hTL ht⟩, hP ht, rfl⟩
  have hRl : IsPGroup 2 (R.subgroupOf L) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRL).symm
  obtain ⟨Q, hQ⟩ := hRl.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥L Q P
  refine ⟨m, m.2, fun r hr => ?_⟩
  have hrQ : (⟨r, hRL hr⟩ : ↥L) ∈ (Q : Subgroup ↥L) := hQ hr
  have hmem : MulAut.conj m ⟨r, hRL hr⟩ ∈ (P : Subgroup ↥L) := by
    rw [← hm, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hrQ
  rw [← hPT]
  exact Subgroup.mem_map.2 ⟨_, hmem, by simp [MulAut.conj_apply]⟩

private theorem exists_normalizing_gt [Finite H] {P Q : Subgroup H} (hP : IsPGroup 2 P)
    (hQP : Q < P) :
    ∃ Y : Subgroup H, Q < Y ∧ Y ≤ P ∧ Y ≤ Subgroup.normalizer (Q : Set H) ∧ IsPGroup 2 Y := by
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact not_le_of_gt hQP h
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥P) _ hlt
  obtain ⟨x, hxN, hxQ⟩ := SetLike.exists_of_lt hgrow
  have hxN' : (x : H) ∈ Subgroup.normalizer (Q : Set H) := by
    have := hxN
    rw [← Subgroup.subgroupOf_normalizer_eq hQP.le] at this
    exact this
  have hxQ' : (x : H) ∉ Q := hxQ
  refine ⟨Q ⊔ Subgroup.zpowers (x : H), ?_, sup_le hQP.le (Subgroup.zpowers_le.2 x.2), ?_, ?_⟩
  · refine lt_of_le_of_ne le_sup_left ?_
    intro h
    exact hxQ' (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hxN')
  · exact hP.to_le (sup_le hQP.le (Subgroup.zpowers_le.2 x.2))

private theorem exists_central_involution [Finite H] {Q R : Subgroup H} (hR : IsPGroup 2 R)
    (hQR : Q ≤ R) (hN : R ≤ Subgroup.normalizer (Q : Set H)) (hQ : Q ≠ ⊥) :
    ∃ i ∈ Q, i * i = 1 ∧ i ≠ 1 ∧ ∀ y ∈ R, y * i = i * y := by
  haveI : Group.IsNilpotent ↥R := hR.isNilpotent
  haveI hnorm : (Q.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hne : Q.subgroupOf R ≠ ⊥ := by
    intro h
    apply hQ
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hQR hx⟩ : R) ∈ Q.subgroupOf R := hx
    rw [h] at hx'
    have := Subgroup.mem_bot.1 hx'
    simpa using congrArg Subtype.val this
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have haQ : ((a : R) : H) ∈ Q := a.2.1
  have haC : ∀ y ∈ R, y * ((a : R) : H) = ((a : R) : H) * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 a.2.2 ⟨y, hy⟩)
  have ha1 : ((a : R) : H) ≠ 1 := by
    intro h
    apply ha
    ext
    simpa using h
  have hK : (Q ⊓ Subgroup.centralizer (R : Set H)) ≠ ⊥ := by
    intro h
    have : ((a : R) : H) ∈ Q ⊓ Subgroup.centralizer (R : Set H) :=
      ⟨haQ, Subgroup.mem_centralizer_iff.2 fun y hy => haC y hy⟩
    rw [h] at this
    exact ha1 (Subgroup.mem_bot.1 this)
  have hK2 : IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer (R : Set H)) :=
    hR.to_le (inf_le_left.trans hQR)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hK2
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hK (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Q ⊓ Subgroup.centralizer (R : Set H)))
    2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hx' : orderOf (x : H) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have hxI := orderOf_eq_prime_iff.1 hx'
  refine ⟨x, x.2.1, by simpa [sq] using hxI.1, hxI.2, fun y hy => ?_⟩
  exact Subgroup.mem_centralizer_iff.1 x.2.2 y hy

private theorem mem_of_le_sylow_le_conj [Finite H] {L S : Subgroup H}
    (hS : IsMaximalTwoSubgroup S L)
    (hC : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∀ c : H, c * u = u * c → c ∈ L)
    (hN : ∀ c ∈ Subgroup.normalizer (S : Set H), c ∈ L) :
    ∀ (n : ℕ) (Q : Subgroup H), Nat.card S - Nat.card Q = n → Q ≤ S → Q ≠ ⊥ →
      ∀ g : H, Q ≤ L.map (MulAut.conj g).toMonoidHom → g ∈ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hn hQS hQ1 g hg
    obtain heq | hlt := hQS.eq_or_lt
    ·
      have hgS : ∀ s ∈ S, g⁻¹ * s * g ∈ L := fun s hs => mem_map_conj_iff.1 (hg (heq ▸ hs))
      have hS'L : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ L := by
        rintro _ ⟨s, hs, rfl⟩
        simpa [MulAut.conj_apply] using hgS s hs
      obtain ⟨m, hmL, hm⟩ := exists_conj_le hS hS'L (hS.2.1.map _)
      have hle : (S.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom ≤ S := by
        rintro _ ⟨r, hr, rfl⟩
        simpa [MulAut.conj_apply] using hm r hr
      have hcard : Nat.card S ≤
          Nat.card ((S.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj m).injective,
          Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      have heq' := Subgroup.eq_of_le_of_card_ge hle hcard
      have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          (MulAut.conj (m * g⁻¹)).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      have hmap : S.map (MulAut.conj (m * g⁻¹)).toMonoidHom = S := by
        rw [← hcomp, ← Subgroup.map_map]
        exact heq'
      have hy : m * g⁻¹ ∈ L := hN _ (Subgroup.mem_normalizer_iff_map_conj_eq.2 hmap)
      have hgeq : g = (m * g⁻¹)⁻¹ * m := by group
      rw [hgeq]
      exact L.mul_mem (L.inv_mem hy) hmL
    ·
      obtain ⟨Y, hQY, hYS, hYN, hY2⟩ := exists_normalizing_gt hS.2.1 hlt
      obtain ⟨i, hiQ, hi2, hi1, hYi⟩ := exists_central_involution hY2 hQY.le hYN hQ1
      have hiL : g⁻¹ * i * g ∈ L := mem_map_conj_iff.1 (hg hiQ)
      have hi2' : (g⁻¹ * i * g) * (g⁻¹ * i * g) = 1 := by
        calc (g⁻¹ * i * g) * (g⁻¹ * i * g) = g⁻¹ * (i * i) * g := by group
          _ = 1 := by rw [hi2]; group
      have hi1' : g⁻¹ * i * g ≠ 1 := by
        intro h
        apply hi1
        have : i = g * (g⁻¹ * i * g) * g⁻¹ := by group
        rw [this, h]
        group
      have hYg : Y ≤ L.map (MulAut.conj g).toMonoidHom := by
        intro y hy
        refine mem_map_conj_iff.2 (hC _ hiL hi2' hi1' _ ?_)
        have := hYi y hy
        calc g⁻¹ * y * g * (g⁻¹ * i * g) = g⁻¹ * (y * i) * g := by group
          _ = g⁻¹ * (i * y) * g := by rw [this]
          _ = g⁻¹ * i * g * (g⁻¹ * y * g) := by group
      have hcard1 : Nat.card Q < Nat.card Y := Subgroup.card_lt_of_lt hQY
      have hcard2 : Nat.card Y ≤ Nat.card S := Subgroup.card_le_of_le hYS
      exact ih (Nat.card S - Nat.card Y) (by omega) Y rfl hYS
        ((bot_lt_iff_ne_bot).1 (lt_of_le_of_lt bot_le hQY)) g hYg

theorem isStronglyEmbeddedOrder_of_centralizers [Finite H] {L S : Subgroup H} (hL : L ≠ ⊤)
    (heven : Even (Nat.card L))
    (hC : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∀ c : H, c * u = u * c → c ∈ L)
    (hS : IsMaximalTwoSubgroup S L) (hN : ∀ c ∈ Subgroup.normalizer (S : Set H), c ∈ L) :
    IsStronglyEmbeddedOrder L := by
  refine ⟨hL, heven, fun g hg => ?_⟩
  by_contra hodd
  have hev : Even (Nat.card ↥(L ⊓ L.map (MulAut.conj g).toMonoidHom)) :=
    Nat.not_odd_iff_even.1 hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(L ⊓ L.map (MulAut.conj g).toMonoidHom)) 2 (even_iff_two_dvd.1 hev)
  have ht2 : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨htL, htg⟩ := t.2
  have hI := orderOf_eq_prime_iff.1 ht2
  obtain ⟨m, hmL, hm⟩ := exists_conj_le hS (Subgroup.zpowers_le.2 htL)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one]))
  have hmt : m * (t : H) * m⁻¹ ∈ S := hm _ (Subgroup.mem_zpowers _)
  have hQS : Subgroup.zpowers (m * (t : H) * m⁻¹) ≤ S := Subgroup.zpowers_le.2 hmt
  have hQ1 : Subgroup.zpowers (m * (t : H) * m⁻¹) ≠ ⊥ := by
    intro h
    have h0 : m * (t : H) * m⁻¹ ∈ (⊥ : Subgroup H) := h ▸ Subgroup.mem_zpowers _
    apply hI.2
    have h1 : m * (t : H) * m⁻¹ = 1 := Subgroup.mem_bot.1 h0
    calc (t : H) = m⁻¹ * (m * (t : H) * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  have hQg : Subgroup.zpowers (m * (t : H) * m⁻¹) ≤ L.map (MulAut.conj (m * g)).toMonoidHom := by
    rw [Subgroup.zpowers_le]
    refine mem_map_conj_iff.2 ?_
    have h1 : (m * g)⁻¹ * (m * (t : H) * m⁻¹) * (m * g) = g⁻¹ * t * g := by group
    rw [h1]
    exact mem_map_conj_iff.1 htg
  have hmg : m * g ∈ L := mem_of_le_sylow_le_conj hS hC hN _ _ rfl hQS hQ1 (m * g) hQg
  apply hg
  have hgeq : g = m⁻¹ * (m * g) := by group
  rw [hgeq]
  exact L.mul_mem (L.inv_mem hmL) hmg

theorem exists_conj_mem_of_isStronglyEmbeddedOrder [Finite H] {L : Subgroup H}
    (hL : IsStronglyEmbeddedOrder L) {a b : H} (ha : a ∈ L) (hb : b ∈ L) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ l ∈ L, l * a * l⁻¹ = b := by
  obtain ⟨g, hgL, hg⟩ := (isStronglyEmbedded_of_parity L hL).involutions_conjugate_in
    ha ⟨ha1, by simpa [sq] using ha2⟩ hb ⟨hb1, by simpa [sq] using hb2⟩
  exact ⟨g⁻¹, L.inv_mem hgL, by simpa [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem] using hg⟩

end Criterion

section Ambient

variable {G : Type*} [Group G]

theorem isStronglyEmbeddedOrder_subgroupOf_of_centralizers {L H S : Subgroup G} [Finite H]
    (hLH : L ≤ H) (hne : L ≠ H) (heven : Even (Nat.card L))
    (hC : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∀ g ∈ H, g * u = u * g → g ∈ L)
    (hS : IsMaximalTwoSubgroup S L)
    (hN : ∀ g ∈ H, g ∈ Subgroup.normalizer (S : Set G) → g ∈ L) :
    IsStronglyEmbeddedOrder (L.subgroupOf H) := by
  refine isStronglyEmbeddedOrder_of_centralizers (S := S.subgroupOf H) ?_ ?_ ?_
    (hS.subgroupOf hLH) ?_
  · intro h
    exact hne (le_antisymm hLH (Subgroup.subgroupOf_eq_top.1 h))
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv]
  · intro u hu hu2 hu1 c hc
    refine hC u hu (congrArg Subtype.val hu2) (fun h => hu1 (Subtype.ext h)) c c.2
      (congrArg Subtype.val hc)
  · intro c hc
    rw [← Subgroup.subgroupOf_normalizer_eq (hS.1.trans hLH)] at hc
    exact hN c c.2 hc

theorem eq_of_two_classes_of_isMaximal {L H S : Subgroup G} [Finite H] (hLH : L ≤ H)
    (heven : Even (Nat.card L))
    (hC : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∀ g ∈ H, g * u = u * g → g ∈ L)
    (hS : IsMaximalTwoSubgroup S L)
    (hN : ∀ g ∈ H, g ∈ Subgroup.normalizer (S : Set G) → g ∈ L)
    {t₁ t₂ : G} (h₁ : t₁ ∈ L) (h₂ : t₂ ∈ L) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (ht₁' : t₁ ≠ 1) (ht₂' : t₂ ≠ 1) (hnc : ∀ l ∈ L, l * t₁ * l⁻¹ ≠ t₂) : L = H := by
  by_contra hne
  have hSE := isStronglyEmbeddedOrder_subgroupOf_of_centralizers hLH hne heven hC hS hN
  obtain ⟨l, hl, hlab⟩ := exists_conj_mem_of_isStronglyEmbeddedOrder hSE
    (a := ⟨t₁, hLH h₁⟩) (b := ⟨t₂, hLH h₂⟩) h₁ h₂ (Subtype.ext ht₁) (Subtype.ext ht₂)
    (fun h => ht₁' (congrArg Subtype.val h)) (fun h => ht₂' (congrArg Subtype.val h))
  exact hnc l hl (congrArg Subtype.val hlab)

theorem eq_of_two_classes {L H : Subgroup G} [Finite H] (hLH : L ≤ H) (heven : Even (Nat.card L))
    (hC : ∀ u ∈ L, u * u = 1 → u ≠ 1 → ∀ g ∈ H, g * u = u * g → g ∈ L)
    {S : Subgroup G} {k : ℕ} (hSL : S ≤ L) (hSk : Nat.card S = 2 ^ k)
    (hk : ¬ 2 ^ (k + 1) ∣ Nat.card H)
    (hN : ∀ g ∈ H, g ∈ Subgroup.normalizer (S : Set G) → g ∈ L)
    {t₁ t₂ : G} (h₁ : t₁ ∈ L) (h₂ : t₂ ∈ L) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (ht₁' : t₁ ≠ 1) (ht₂' : t₂ ≠ 1) (hnc : ∀ l ∈ L, l * t₁ * l⁻¹ ≠ t₂) : L = H :=
  eq_of_two_classes_of_isMaximal hLH heven hC (IsMaximalTwoSubgroup.of_card hSL hLH hSk hk) hN
    h₁ h₂ ht₁ ht₂ ht₁' ht₂' hnc

end Ambient

end CFSG.HardMathSupport.Dickson.BMRows
