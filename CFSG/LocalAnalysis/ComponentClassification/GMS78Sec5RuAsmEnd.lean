module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSE
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsRu
public import CFSG.GH74.Uniqueness.Statements
import CFSG.GH74.GLS.Stage12.McLEndgame
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
import CFSG.Goldschmidt.Steps.G37Core

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.EvenSporadicStandard.RuStd

section SE

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_involutionClosure_of_simple {M : Subgroup X} (hMs : IsSimpleGroup ↥M) {v : ↥M}
    (hv : orderOf v = 2) : M ≤ CFSG.GH74.Uniqueness.involutionClosure X := by
  have htop := CFSG.GH74.GLS.Stage12.McLRec.involutionClosure_eq_top hMs hv
  intro m hm
  have hmem : (⟨m, hm⟩ : ↥M) ∈ CFSG.GH74.Uniqueness.involutionClosure ↥M := by
    rw [htop]
    exact mem_top _
  have hle : (CFSG.GH74.Uniqueness.involutionClosure ↥M).map M.subtype ≤
      CFSG.GH74.Uniqueness.involutionClosure X := by
    unfold CFSG.GH74.Uniqueness.involutionClosure
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    refine subset_closure ?_
    show orderOf (x : X) = 2
    rw [Subgroup.orderOf_coe]
    exact hx
  exact hle ⟨⟨m, hm⟩, hmem, rfl⟩

theorem false_of_isStronglyEmbedded_of_simple {M : Subgroup X}
    (hM : CFSG.IsStronglyEmbedded M) (hMs : IsSimpleGroup ↥M) (h2 : ¬ IsPGroup 2 ↥M)
    {V : Subgroup X} (hV : CFSG.Open.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := CFSG.GH74.Uniqueness.involutionClosure X with hLdef
  have hev : Even (Nat.card M) := hM.2.1
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2 (even_iff_two_dvd.mp hev)
  have hML : M ≤ L := le_involutionClosure_of_simple hMs hv
  rcases CFSG.GH74.Uniqueness.S_SE_proof X M hM with hrank | ⟨-, -, hB⟩
  ·
    have hVL : V ≤ L := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · refine subset_closure ?_
        exact orderOf_eq_prime (hV.2 x hx) hx1
    have hrank2 : 2 ≤ CFSG.Open.pRank 2 L := by
      refine le_csSup ⟨Nat.card X, ?_⟩ ⟨V, hVL, hV, by rw [hV4]; norm_num⟩
      rintro r ⟨B, -, -, hB⟩
      calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card X := Subgroup.card_le_card_group B
    exact absurd (hrank2.trans hrank) (by norm_num)
  ·
    obtain ⟨S, hS⟩ := hB
    set O := CFSG.pPrimeCore 2 ↥L with hO
    set θ : ↥M →* ↥L ⧸ O := (QuotientGroup.mk' O).comp (inclusion hML) with hθ
    have hrange : θ.range = (M.comap L.subtype).map (QuotientGroup.mk' O) := by
      rw [hθ, MonoidHom.range_comp]
      congr 1
      ext x
      constructor
      · rintro ⟨m, rfl⟩
        exact m.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [← hrange] at hS
    have hker : θ.ker = ⊥ := by
      rcases hMs.eq_bot_or_eq_top_of_normal θ.ker with h | h
      · exact h
      · exfalso
        have hle : (inclusion hML).range ≤ O := by
          rintro _ ⟨m, rfl⟩
          have hm : m ∈ θ.ker := h ▸ mem_top m
          rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at hm
          exact hm
        have hcard : Nat.card M ∣ Nat.card O := by
          rw [Nat.card_congr (MonoidHom.ofInjective (inclusion_injective hML)).toEquiv]
          exact card_dvd_of_le hle
        have hodd : Odd (Nat.card O) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
        exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat hcard)) hev
    have hinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hker
    set K := (S : Subgroup (↥L ⧸ O)).comap θ with hK
    have hKn : K.Normal := by
      refine ⟨fun k hk m => ?_⟩
      have hm : θ m ∈ normalizer ((S : Subgroup (↥L ⧸ O)) : Set (↥L ⧸ O)) := by
        rw [← hS]
        exact ⟨m, rfl⟩
      show θ (m * k * m⁻¹) ∈ (S : Subgroup (↥L ⧸ O))
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hm (θ k)).mp hk
    rcases hMs.eq_bot_or_eq_top_of_normal K with h | h
    ·
      have hS1 : (S : Subgroup (↥L ⧸ O)) = ⊥ := by
        rw [eq_bot_iff]
        intro s hs
        have hsN : s ∈ normalizer ((S : Subgroup (↥L ⧸ O)) : Set (↥L ⧸ O)) :=
          le_normalizer hs
        rw [← hS] at hsN
        obtain ⟨m, rfl⟩ := hsN
        have hmK : m ∈ K := hs
        rw [h, mem_bot] at hmK
        rw [hmK, map_one]
        exact one_mem _
      have hQodd : ¬ 2 ∣ Nat.card (↥L ⧸ O) := by
        intro h2'
        obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥L ⧸ O) 2 h2'
        have hq2 : IsPGroup 2 (zpowers q) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hq, pow_one])
        obtain ⟨S', hS'⟩ := hq2.exists_le_sylow
        have hcS : Nat.card (S : Subgroup (↥L ⧸ O)) = Nat.card (S' : Subgroup (↥L ⧸ O)) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
        rw [hS1, card_bot] at hcS
        have h2le : 2 ≤ Nat.card (S' : Subgroup (↥L ⧸ O)) := by
          calc 2 = Nat.card (zpowers q) := by rw [Nat.card_zpowers, hq]
            _ ≤ Nat.card (S' : Subgroup (↥L ⧸ O)) := card_le_of_le hS'
        omega
      have hcard : Nat.card M ∣ Nat.card (↥L ⧸ O) := by
        rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
        exact card_subgroup_dvd_card _
      exact hQodd ((even_iff_two_dvd.mp hev).trans hcard)
    ·
      apply h2
      have hle : θ.range ≤ (S : Subgroup (↥L ⧸ O)) := by
        rintro _ ⟨m, rfl⟩
        have hmK : m ∈ K := h ▸ mem_top m
        exact hmK
      have hp : IsPGroup 2 θ.range := S.isPGroup'.to_le hle
      exact hp.of_equiv (MonoidHom.ofInjective hinj).symm

end SE

section Surj

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_centralizer_subtype (H : Subgroup G) (x : ↥H) :
    Nat.card (centralizer ({x} : Set ↥H)) = Nat.card ↥(H ⊓ centralizer ({(x : G)} : Set G)) := by
  have h : (centralizer ({x} : Set ↥H)).map H.subtype =
      H ⊓ centralizer ({(x : G)} : Set G) := by
    ext y
    rw [mem_map, mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_centralizer_singleton_iff] at hw
      exact ⟨w.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hw)⟩
    · rintro ⟨hyH, hy⟩
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff] at hy ⊢
      exact Subtype.ext hy
  rw [← h, card_map_of_injective H.subtype_injective]

omit [Finite G] in
theorem card_centralizer_conj_eq (g t : G) :
    Nat.card (centralizer ({g * t * g⁻¹} : Set G)) = Nat.card (centralizer ({t} : Set G)) := by
  have h : (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * t * g⁻¹} : Set G) := by
    ext x
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hy]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
        _ = t * (g⁻¹ * x * g) := by group
  rw [← h, card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
theorem exists_elemAbelian_four {u a : G} (hu : orderOf u = 2) (ha : orderOf a = 2)
    (hua : u * a = a * u) (hne : u ≠ a) :
    ∃ V : Subgroup G, CFSG.Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hz : ∀ {w y : G}, w ^ 2 = 1 → y ∈ zpowers w → y = 1 ∨ y = w := fun hw hy =>
    CFSG.Goldschmidt.G37.eq_one_or_eq_of_mem_zpowers hw hy
  have hN : zpowers a ≤ normalizer (zpowers u : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => by
      rcases hz hu2 hy with rfl | rfl
      · rw [one_mul, mul_one]
      · exact hua))
  have hdisj : zpowers u ⊓ zpowers a = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyu, hya⟩
    rcases hz hu2 hyu with rfl | rfl
    · exact one_mem _
    · rcases hz ha2 hya with h | h
      · rw [h, orderOf_one] at hu
        exact absurd hu (by norm_num)
      · exact absurd h hne
  have hmem : ∀ y ∈ zpowers u ⊔ zpowers a, y = 1 ∨ y = u ∨ y = a ∨ y = u * a := by
    intro y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer hN hy
    rcases hz hu2 hp with rfl | rfl <;> rcases hz ha2 hq with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hu' : u * u = 1 := by rw [← sq, hu2]
  have ha' : a * a = 1 := by rw [← sq, ha2]
  refine ⟨zpowers u ⊔ zpowers a, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · rcases hmem x x.2 with h | h | h | h <;> rcases hmem y y.2 with h' | h' | h' | h' <;>
      simp only [coe_mul, h, h', one_mul, mul_one] <;>
      simp only [← mul_assoc, hua] <;> simp only [mul_assoc, hua]
  · rcases hmem y hy with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · exact hu2
    · exact ha2
    · rw [sq, show u * a * (u * a) = (u * u) * (a * a) by
        rw [mul_assoc, ← mul_assoc a u a, ← hua]; group, hu', ha', one_mul]
  · rw [AS76b.card_sup_eq_mul hN hdisj, Nat.card_zpowers, Nat.card_zpowers, hu, ha]

theorem range_eq_top_of_ruHom
    {P : Type} [Group P]
    (eP : P ≃* Blueprint.NativeSporadic.Ru) (Φ : P →* G) {z e : G} (hz : z ∈ Φ.range)
    (hz2 : orderOf z = 2) (hzC : centralizer ({z} : Set G) ≤ Φ.range)
    (hzc : 2 ^ 9 ∣ Nat.card (centralizer ({z} : Set G))) (he : e ∈ Φ.range)
    (he2 : orderOf e = 2) (hec : Nat.card (centralizer ({e} : Set G)) = 116480) :
    Φ.range = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Φ.range with hH
  have hsRu : IsSimpleGroup Blueprint.NativeSporadic.Ru := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hsPi : IsSimpleGroup P :=
    @MulEquiv.isSimpleGroup P _ Blueprint.NativeSporadic.Ru _ hsRu eP
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsPi.eq_bot_or_eq_top_of_normal Φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨y, rfl⟩ := hz
      exact hz1 (MonoidHom.mem_ker.mp (h ▸ mem_top y))
  set eH : P ≃* ↥H := MonoidHom.ofInjective hinj with heH
  have hHRu : Blueprint.NativeSporadic.IsSporadic ↥H .Ru := ⟨eH.symm.trans eP⟩
  have hF : RuFacts ↥H := ruFacts_of_isSporadic hHRu
  have hsH : IsSimpleGroup ↥H := @MulEquiv.isSimpleGroup ↥H _ P _ hsPi eH.symm
  set z' : ↥H := ⟨z, hz⟩ with hz'
  set e' : ↥H := ⟨e, he⟩ with he'
  have hz'2 : orderOf z' = 2 := (Subgroup.orderOf_coe z').symm.trans hz2
  have he'2 : orderOf e' = 2 := (Subgroup.orderOf_coe e').symm.trans he2
  have hz'c : Nat.card (centralizer ({z'} : Set ↥H)) = 245760 := by
    rcases hF.card_centralizer z' hz'2 with h | h
    · exact h
    · exfalso
      rw [card_centralizer_subtype, inf_eq_right.mpr hzC] at h
      rw [h] at hzc
      norm_num at hzc
  have he'c : Nat.card (centralizer ({e'} : Set ↥H)) = 116480 := by
    rcases hF.card_centralizer e' he'2 with h | h
    · exfalso
      have h1 : Nat.card ↥(H ⊓ centralizer ({e} : Set G)) ≤
          Nat.card (centralizer ({e} : Set G)) := card_le_of_le inf_le_right
      rw [← card_centralizer_subtype H e', h, hec] at h1
      norm_num at h1
    · exact h
  have heC : centralizer ({e} : Set G) ≤ H := by
    have h1 : H ⊓ centralizer ({e} : Set G) = centralizer ({e} : Set G) :=
      eq_of_le_of_card_ge inf_le_right (by rw [hec, ← card_centralizer_subtype H e', he'c])
    rw [← h1]
    exact inf_le_left
  have hconjC : ∀ u c : ↥H, centralizer ({(u : G)} : Set G) ≤ H →
      centralizer ({((c * u * c⁻¹ : ↥H) : G)} : Set G) ≤ H := by
    intro u c hu x hx
    have h1 : (c : G)⁻¹ * x * c ∈ centralizer ({(u : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      simp only [coe_mul, coe_inv] at hx
      calc (c : G)⁻¹ * x * c * u = (c : G)⁻¹ * (x * (c * u * (c : G)⁻¹)) * c := by group
        _ = (c : G)⁻¹ * ((c * u * (c : G)⁻¹) * x) * c := by rw [hx]
        _ = u * ((c : G)⁻¹ * x * c) := by group
    have h3 : (c : G) * ((c : G)⁻¹ * x * c) * (c : G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem c.2 (hu h1)) (H.inv_mem c.2)
    rwa [show (c : G) * ((c : G)⁻¹ * x * c) * (c : G)⁻¹ = x by group] at h3
  have hcent : ∀ u ∈ H, orderOf u = 2 → centralizer ({u} : Set G) ≤ H := by
    intro u hu hu2
    have hu'2 : orderOf (⟨u, hu⟩ : ↥H) = 2 := (Subgroup.orderOf_coe _).symm.trans hu2
    rcases hF.card_centralizer _ hu'2 with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.mp (hF.isConj_A z' _ hz'2 hu'2 hz'c h)
      have h1 := hconjC z' c hzC
      rwa [hc] at h1
    · obtain ⟨c, hc⟩ := isConj_iff.mp (hF.isConj_B e' _ he'2 hu'2 he'c h)
      have h1 := hconjC e' c heC
      rwa [hc] at h1
  have hfus : ∀ u ∈ H, orderOf u = 2 → ∀ g : G, g * u * g⁻¹ ∈ H →
      ∃ c ∈ H, c * u * c⁻¹ = g * u * g⁻¹ := by
    intro u hu hu2 g hg
    have hv2 : orderOf (g * u * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hu2
    have hu'2 : orderOf (⟨u, hu⟩ : ↥H) = 2 := (Subgroup.orderOf_coe _).symm.trans hu2
    have hv'2 : orderOf (⟨g * u * g⁻¹, hg⟩ : ↥H) = 2 := (Subgroup.orderOf_coe _).symm.trans hv2
    have hcuv : Nat.card (centralizer ({(⟨g * u * g⁻¹, hg⟩ : ↥H)} : Set ↥H)) =
        Nat.card (centralizer ({(⟨u, hu⟩ : ↥H)} : Set ↥H)) := by
      rw [card_centralizer_subtype, card_centralizer_subtype, inf_eq_right.mpr (hcent u hu hu2),
        inf_eq_right.mpr (hcent _ hg hv2)]
      exact card_centralizer_conj_eq g u
    have hconj : IsConj (⟨u, hu⟩ : ↥H) ⟨g * u * g⁻¹, hg⟩ := by
      rcases hF.card_centralizer _ hu'2 with h | h
      · exact hF.isConj_A _ _ hu'2 hv'2 h (hcuv.trans h)
      · exact hF.isConj_B _ _ hu'2 hv'2 h (hcuv.trans h)
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    exact ⟨c, c.2, congrArg Subtype.val hc⟩
  have hev : Even (Nat.card H) := even_iff_two_dvd.mpr (by rw [hF.card_eq]; norm_num)
  have hnp : ¬ IsPGroup 2 ↥H := by
    intro hp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by rw [hF.card_eq]; norm_num)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this
  obtain ⟨u, a, hu2, huc, ha2, hac, hau, -, -⟩ := hF.pair
  have hne : (u : G) ≠ (a : G) := fun h => by
    have h1 : u = a := Subtype.ext h
    rw [h1, hac] at huc
    norm_num at huc
  obtain ⟨V, hV, hV4⟩ := exists_elemAbelian_four ((Subgroup.orderOf_coe u).trans hu2)
    ((Subgroup.orderOf_coe a).trans ha2) (congrArg Subtype.val hau).symm hne
  by_contra hHG
  exact false_of_isStronglyEmbedded_of_simple
    (AS81.HeSE.isStronglyEmbedded_of_fusion H hHG hev hfus hcent) hsH hnp hV hV4

end Surj

end CFSG.ComponentClassification.GMS78.RuAsm
