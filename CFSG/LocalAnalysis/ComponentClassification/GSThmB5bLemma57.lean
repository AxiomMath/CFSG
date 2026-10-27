module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma56
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bConj

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem mem_normalizer_of_conj_mem {H : Type*} [Group H] {X : Subgroup H} {y : H}
    (h1 : ∀ x ∈ X, y * x * y⁻¹ ∈ X) (h2 : ∀ x ∈ X, y⁻¹ * x * y ∈ X) :
    y ∈ normalizer (X : Set H) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y = x by group] at this

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem conj_mem_P {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.P) : s * y * s⁻¹ ∈ h.P := by
  refine mem_inf.mpr ⟨mul_mem (mul_mem hs (h.P_le_S hy)) (inv_mem hs), ?_⟩
  have := GSThmB.conj_mem_coreActionKernel (inv_mem (h.S_le_normalizer hs)) (mem_inf.mp hy).2
  rwa [inv_inv] at this

theorem centralizer_conj_le_normalizer (hN : centralizer ({h.a} : Set H) ≤ normalizer (h.J : Set H))
    (g : H) : centralizer ({g⁻¹ * h.a * g} : Set H) ≤ normalizer (conjugate h.J g : Set H) := by
  rw [← conjugate_centralizer_singleton, ← conjugate_normalizer]
  exact map_mono hN

theorem centralizer_conj_le_Q (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) {g : H}
    (hgW : g ∈ h.W) (hgS : g⁻¹ * h.a * g ∈ h.S) (hgP : g⁻¹ * h.a * g ∉ h.P) :
    h.S ⊓ centralizer ({g⁻¹ * h.a * g} : Set H) ≤ h.Q := by
  set e := g⁻¹ * h.a * g with he
  have hB := (hB1 H h g hgW hgS hgP).1
  have hNJ := h.centralizer_conj_le_normalizer
    (h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc) g
  intro y hy
  obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
  refine mem_inf.mpr ⟨hyS, ?_⟩
  have hyN := hNJ hyC
  have key : ∀ y' : H, y' ∈ h.S → y' ∈ centralizer ({e} : Set H) →
      y' ∈ normalizer (conjugate h.J g : Set H) → ∀ x ∈ h.B, y' * x * y'⁻¹ ∈ h.B := by
    intro y' hS' hC' hN' x hx
    rw [hB] at hx ⊢
    obtain ⟨⟨hxP, hxC⟩, hxK⟩ := mem_inf.mp hx |>.imp_left mem_inf.mp
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨h.conj_mem_P hS' hxP, mul_mem (mul_mem hC' hxC)
      (inv_mem hC')⟩, ?_⟩
    have := GSThmB.conj_mem_coreActionKernel (inv_mem hN') hxK
    rwa [inv_inv] at this
  exact mem_normalizer_of_conj_mem (key y hyS hyC hyN) fun x hx => by
    have := key y⁻¹ (inv_mem hyS) (inv_mem hyC) (inv_mem hyN) x hx
    rwa [inv_inv] at this

theorem D_inf_P_eq_bot (hZ : center (OddBar h.J) = ⊥) : h.D ⊓ h.P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨hyS, hyJ⟩, ⟨-, hyC⟩⟩ := mem_inf.mp hy |>.imp mem_inf.mp mem_inf.mp
  have h1 := inf_coreActionKernel_le_of_center_eq_bot hZ (mem_inf.mpr ⟨hyJ, hyC⟩)
  have := h.S_inf_oddCore_eq_bot ▸ mem_inf.mpr ⟨hyS, h1⟩
  exact this

theorem D_ne_bot : h.D ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJeven : Even (Nat.card h.J) := by
    have h1 := even_card_of_isQuasisimple' h.isQuasisimple_J
    obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥h.J)
    rw [hk]
    exact h1.mul_right k
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := h.J) 2 (even_iff_two_dvd.mp hJeven)
  have ht2 : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have htN : (t : H) ∈ h.N0 := mem_inf.mpr ⟨h.J_le t.2, le_normalizer t.2⟩
  have h2t : IsPGroup 2 (zpowers (t : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨m, hm, hmS⟩ := exists_conjugate_le_of_sylow h.S_sylow (zpowers_le.mpr htN) h2t
  intro hD
  have hmJ : m⁻¹ * (t : H) * m ∈ h.J := by
    have := (mem_normalizer_iff.mp (inv_mem (mem_inf.mp hm).2) t).mp t.2
    rwa [inv_inv] at this
  have hmS' : m⁻¹ * (t : H) * m ∈ h.S := hmS (by
    rw [mem_conjugate_iff, show m * (m⁻¹ * (t : H) * m) * m⁻¹ = t by group]
    exact mem_zpowers _)
  have h1 : m⁻¹ * (t : H) * m = 1 := by
    have hmD : m⁻¹ * (t : H) * m ∈ h.D := mem_inf.mpr ⟨hmS', hmJ⟩
    rw [hD] at hmD
    exact mem_bot.mp hmD
  have : (t : H) = 1 := by
    calc (t : H) = m * (m⁻¹ * t * m) * m⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [this, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

theorem exists_involution_D_center :
    ∃ z : H, z ∈ h.D ∧ (∀ s ∈ h.S, s * z = z * s) ∧ orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup h.S := h.D.subgroupOf h.S with hN
  have hNn : N.Normal := by
    constructor
    intro n hn s
    rw [hN, mem_subgroupOf] at hn ⊢
    have hsN := h.S_le_normalizer s.2
    have h1 : (s : H) * n * (s : H)⁻¹ ∈ h.S :=
      mul_mem (mul_mem s.2 (h.D_le_S hn)) (inv_mem s.2)
    have h2 : (s : H) * n * (s : H)⁻¹ ∈ h.J := (mem_normalizer_iff.mp hsN _).mp (h.D_le_J hn)
    simp only [coe_mul, coe_inv]
    exact mem_inf.mpr ⟨h1, h2⟩
  have hN1 : N ≠ ⊥ := by
    intro hb
    apply h.D_ne_bot
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, h.D_le_S hy⟩ : h.S) ∈ N := hy
    rw [hb] at this
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp this))
  have hnil : Group.IsNilpotent h.S := h.isPGroup_S.isNilpotent
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
  have h2 : IsPGroup 2 ↥(N ⊓ center h.S) := h.isPGroup_S.to_subgroup _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N ⊓ center h.S)) 2 (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rcases k with _ | k
    · exfalso
      apply hX
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _)
  obtain ⟨huN, huZ⟩ := mem_inf.mp u.2
  refine ⟨((u : h.S) : H), huN, fun s hs => ?_, ?_⟩
  · exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp huZ ⟨s, hs⟩))
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]

theorem isSmallAltOrL2_J (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) : IsSmallAltOrL2 (OddBar h.J) := by
  rcases h.table hB1 hCF23 with ⟨n, hn, hJ, -⟩ | ⟨hJ | hJ, -⟩ | h3 |
      ⟨p, f, hp, hp2, hf, hJ, -⟩ | ⟨p, f, hp, hp2, hf, h5, hJ, -⟩ |
      ⟨p, f, hp, hp2, hf, h5, hJ, -⟩ | ⟨p, f, hp, hp2, hf, hJ, -⟩
  · exact Or.inl ⟨n, hn, hJ⟩
  · exact Or.inr ⟨5, 1, Nat.prime_five, by norm_num, le_rfl, by norm_num, hJ⟩
  · exact Or.inr ⟨7, 1, by norm_num, by norm_num, le_rfl, by norm_num, hJ⟩
  · exact absurd h3 (h.not_suz hB6 hCF24)
  · refine Or.inr ⟨p, 2 * f, hp, hp2, by omega, ?_, hJ⟩
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, hJ⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, hJ⟩
  · refine Or.inr ⟨p, 2 * f, hp, hp2, by omega, ?_, hJ⟩
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)

theorem fixedLayer_involutions_conj (hSmall : IsSmallAltOrL2 (OddBar h.J)) (hSI : CFSmallInv)
    {F : Subgroup H} (hFC : F ≤ coreActionKernel h.J) (hF2 : IsPGroup 2 F) {s t : H}
    (hs : s ∈ GSLit.fixedLayer h.J F) (ht : t ∈ GSLit.fixedLayer h.J F)
    (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) :
    ∃ g ∈ GSLit.fixedLayer h.J F, g⁻¹ * s * g = t := by
  set JF := GSLit.fixedLayer h.J F with hJF
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore h.isQuasisimple_J hFC hF2).1
  have hJFJ : JF ≤ h.J := fun y hy => (mem_inf.mp (GSLit.fixedLayer_le_inf _ _ hy)).1
  obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hJFJ hsup
  have hsm : IsSmallAltOrL2 (OddBar JF) := isSmallAltOrL2_of_mulEquiv e.symm hSmall
  obtain ⟨g, hg⟩ := involutions_conj_of_quotient (Y := JF) (hSI _ hsm)
    (s := ⟨s, hs⟩) (t := ⟨t, ht⟩) (by rw [Subgroup.orderOf_mk, hs2])
    (by rw [Subgroup.orderOf_mk, ht2])
  exact ⟨g, g.2, by simpa using congrArg Subtype.val hg⟩

theorem inf_conjugate_P_eq_bot (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hSI : CFSmallInv)
    {g : H} (hg : g⁻¹ * h.a * g ∈ h.J ⊔ zpowers h.a) (hga : g⁻¹ * h.a * g ∉ zpowers h.a) :
    h.P ⊓ conjugate h.P g = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hF
  have hZ := h.center_eq_bot hB1 hB6 hCF23 hCF24
  have hNJ := h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  have hPS := h.centralizer_P_eq hB1 hCF23 hCFc
  have hSmall := h.isSmallAltOrL2_J hB1 hB6 hCF23 hCF24
  set F := h.P ⊓ conjugate h.P g with hFdef
  set e := g⁻¹ * h.a * g with he
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hεc : ∀ ε ∈ zpowers h.a, ∀ y ∈ centralizer ({h.a} : Set H), y * ε = ε * y := by
    intro ε hε y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hε
    exact (Commute.zpow_right (show Commute y h.a from mem_centralizer_singleton_iff.mp hy) k).eq
  have hε2 : ∀ ε ∈ zpowers h.a, ε * ε = 1 := by
    intro ε hε
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hε
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ha2, one_zpow]
  have hSC : h.S ≤ centralizer ({h.a} : Set H) := h.S_le.trans inf_le_left
  have haN : h.a ∈ normalizer (h.J : Set H) := (mem_coreActionKernel.mp h.a_mem_coreActionKernel).1
  have hzm : e ∈ (h.J : Set H) * (zpowers h.a : Set H) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr haN)]
    exact hg
  obtain ⟨j, hj, ε, hε, hje⟩ := Set.mem_mul.mp hzm
  have hjε : j * ε = ε * j := hεc ε hε j (h.J_le hj)
  have he2 : e * e = 1 := by
    calc e * e = g⁻¹ * (h.a * h.a) * g := by rw [he]; group
      _ = 1 := by rw [ha2]; group
  have hfe : ∀ f ∈ F, f * e = e * f := by
    intro f hf
    have hgf : g * f * g⁻¹ ∈ h.P := by
      have := (mem_inf.mp hf).2
      rwa [mem_conjugate_iff] at this
    have hc := h.comm_a (h.P_le_S hgf)
    calc f * e = g⁻¹ * ((g * f * g⁻¹) * h.a) * g := by rw [he]; group
      _ = g⁻¹ * (h.a * (g * f * g⁻¹)) * g := by rw [hc]
      _ = e * f := by rw [he]; group
  have hfε : ∀ f ∈ F, f * ε = ε * f := fun f hf => hεc ε hε f (hSC (h.P_le_S (mem_inf.mp hf).1))
  have hjF : j ∈ centralizer (F : Set H) := by
    rw [mem_centralizer_iff]
    intro f hf
    have hj' : j = e * ε⁻¹ := by rw [← hje]; group
    rw [hj']
    have h1 := hfe f hf
    have h2 : f * ε⁻¹ = ε⁻¹ * f := by
      have := hfε f hf
      calc f * ε⁻¹ = ε⁻¹ * (ε * f) * ε⁻¹ := by group
        _ = ε⁻¹ * (f * ε) * ε⁻¹ := by rw [this]
        _ = ε⁻¹ * f := by group
    calc f * (e * ε⁻¹) = (f * e) * ε⁻¹ := by group
      _ = e * (f * ε⁻¹) := by rw [h1]; group
      _ = e * ε⁻¹ * f := by rw [h2]; group
  have hj2 : j * j = 1 := by
    have h1 : (j * ε) * (j * ε) = 1 := by rw [hje]; exact he2
    calc j * j = (j * ε) * (j * ε) * (ε * ε)⁻¹ := by
          rw [show (j * ε) * (j * ε) = (j * j) * (ε * ε) by
            rw [mul_assoc, ← mul_assoc ε, ← hjε]; group]
          group
      _ = 1 := by rw [h1, hε2 ε hε]; group
  have hj1 : j ≠ 1 := by
    intro h1
    apply hga
    rw [← hje, h1, one_mul]
    exact hε
  have hjo : orderOf j = 2 := orderOf_eq_prime (by rw [pow_two]; exact hj2) hj1
  have hFC : F ≤ coreActionKernel h.J := fun y hy => (mem_inf.mp (mem_inf.mp hy).1).2
  have hF2 : IsPGroup 2 F := h.isPGroup_S.to_le fun y hy => h.P_le_S (mem_inf.mp hy).1
  have hjJF : j ∈ GSLit.fixedLayer h.J F := by
    rw [GSLit.fixedLayer_eq_closure h.isQuasisimple_J hFC hF2]
    exact subset_closure ⟨mem_inf.mpr ⟨hj, hjF⟩, ⟨1, by rw [hjo, pow_one]⟩⟩
  obtain ⟨z, hzD, hzS, hzo⟩ := h.exists_involution_D_center
  have hzF : z ∈ centralizer (F : Set H) := by
    rw [mem_centralizer_iff]
    intro f hf
    exact (h.D_comm_P hzD (mem_inf.mp hf).1).symm
  have hzJF : z ∈ GSLit.fixedLayer h.J F := by
    rw [GSLit.fixedLayer_eq_closure h.isQuasisimple_J hFC hF2]
    exact subset_closure ⟨mem_inf.mpr ⟨h.D_le_J hzD, hzF⟩, ⟨1, by rw [hzo, pow_one]⟩⟩
  obtain ⟨h₀, hh₀, hh₀z⟩ := h.fixedLayer_involutions_conj hSmall hSI hFC hF2 hjJF hzJF hjo hzo
  obtain ⟨hh₀J, hh₀F⟩ := mem_inf.mp (GSLit.fixedLayer_le_inf _ _ hh₀)
  set g' := g * h₀ with hg'
  set e' := g'⁻¹ * h.a * g' with he'
  have he'eq : e' = z * ε := by
    have h1 : h₀⁻¹ * ε * h₀ = ε := by
      rw [mul_assoc, ← hεc ε hε h₀ (h.J_le hh₀J), ← mul_assoc, inv_mul_cancel, one_mul]
    calc e' = h₀⁻¹ * (j * ε) * h₀ := by rw [he', hg', hje, he]; group
      _ = (h₀⁻¹ * j * h₀) * (h₀⁻¹ * ε * h₀) := by group
      _ = z * ε := by rw [hh₀z, h1]
  have hFg' : F ≤ conjugate h.P g' := by
    intro f hf
    have hfP : g * f * g⁻¹ ∈ h.P := by
      have := (mem_inf.mp hf).2
      rwa [mem_conjugate_iff] at this
    rw [mem_conjugate_iff]
    have hc : h₀ * f * h₀⁻¹ = f := by
      rw [(mem_centralizer_iff.mp hh₀F f hf).symm, mul_inv_cancel_right]
    have h1 : g' * f * g'⁻¹ = g * (h₀ * f * h₀⁻¹) * g⁻¹ := by rw [hg']; group
    rw [h1, hc]
    exact hfP
  have hDP := h.D_inf_P_eq_bot hZ
  have he'a : e' ∉ zpowers h.a := by
    intro he'm
    have hz : z ∈ zpowers h.a := by
      have := mul_mem he'm (inv_mem hε)
      rwa [he'eq, mul_inv_cancel_right] at this
    have hzP : z ∈ h.P := (zpowers_le.mpr h.a_mem_P) hz
    have : z ∈ h.D ⊓ h.P := mem_inf.mpr ⟨hzD, hzP⟩
    rw [hDP] at this
    rw [mem_bot.mp this, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  have hSe' : h.S ≤ centralizer ({e'} : Set H) := by
    intro s hs
    rw [mem_centralizer_singleton_iff, he'eq]
    have h1 := hzS s hs
    have h2 := hεc ε hε s (hSC hs)
    calc s * (z * ε) = (s * z) * ε := by group
      _ = z * (s * ε) := by rw [h1]; group
      _ = z * ε * s := by rw [h2]; group
  obtain ⟨hSCa, hSyl⟩ := h.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
  obtain ⟨hcS, hcSyl⟩ := sylow_conjugate hSCa hSyl g'
  rw [conjugate_centralizer_singleton] at hcS hcSyl
  have hSyl' := sylow_of_card_eq hcS hcSyl hSe' h.isPGroup_S
    (card_map_of_injective (MulAut.conj g'⁻¹).injective).symm
  obtain ⟨c, hc, hcc⟩ := exists_conjugate_eq_of_sylow hcS hcSyl hSe' hSyl'
  set k := g' * c with hk
  have hNe' := h.centralizer_conj_le_normalizer hNJ g'
  have hJk : conjugate h.J k = conjugate h.J g' := by
    rw [hk, ← conjugate_conjugate, conjugate_eq_of_mem_normalizer (hNe' hc)]
  have hSk : conjugate h.S k = h.S := by rw [hk, ← conjugate_conjugate, hcc]
  have hak : k⁻¹ * h.a * k = e' := by
    have hce := mem_centralizer_singleton_iff.mp hc
    calc k⁻¹ * h.a * k = c⁻¹ * e' * c := by rw [hk, he']; group
      _ = e' := by rw [mul_assoc, ← hce, ← mul_assoc, inv_mul_cancel, one_mul]
  have hPS' : (h.S ⊓ coreActionKernel (conjugate h.J g')) ⊓ centralizer (h.S : Set H) =
      zpowers e' := by
    have : conjugate (h.P ⊓ centralizer (h.S : Set H)) k = conjugate (zpowers h.a) k := by
      rw [hPS]
    rw [conjugate_inf, conjugate_inf, conjugate_coreActionKernel, conjugate_centralizer',
      conjugate_zpowers', hJk, hSk, hak] at this
    exact this
  set X₀ := h.S ⊓ coreActionKernel h.J ⊓ coreActionKernel (conjugate h.J g') with hX₀
  have hFX : F ≤ X₀ := by
    intro f hf
    have h1 := (mem_inf.mp hf).1
    have h2 := hFg' hf
    rw [Hyp52.P, conjugate_inf, conjugate_coreActionKernel] at h2
    exact mem_inf.mpr ⟨h1, (mem_inf.mp h2).2⟩
  set N : Subgroup h.S := X₀.subgroupOf h.S with hN
  have hNn : N.Normal := by
    constructor
    intro n hn s
    rw [hN, mem_subgroupOf] at hn ⊢
    obtain ⟨⟨hnS, hnC⟩, hnC'⟩ := mem_inf.mp hn |>.imp_left mem_inf.mp
    have hsN := h.S_le_normalizer s.2
    have hsN' := hNe' (hSe' s.2)
    simp only [coe_mul, coe_inv]
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem s.2 hnS) (inv_mem s.2), ?_⟩, ?_⟩
    · have := GSThmB.conj_mem_coreActionKernel (inv_mem hsN) hnC
      rwa [inv_inv] at this
    · have := GSThmB.conj_mem_coreActionKernel (inv_mem hsN') hnC'
      rwa [inv_inv] at this
  have hN1 : N ≠ ⊥ := by
    intro hb
    apply hF
    rw [eq_bot_iff]
    intro f hf
    have hfS : f ∈ h.S := h.P_le_S (mem_inf.mp hf).1
    have : (⟨f, hfS⟩ : h.S) ∈ N := hFX hf
    rw [hb] at this
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp this))
  have hnil : Group.IsNilpotent h.S := h.isPGroup_S.isNilpotent
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  obtain ⟨huN, huZ⟩ := mem_inf.mp u.2
  have huX : ((u : h.S) : H) ∈ X₀ := huN
  obtain ⟨⟨huS, huC⟩, huC'⟩ := mem_inf.mp huX |>.imp_left mem_inf.mp
  have huc : ((u : h.S) : H) ∈ centralizer (h.S : Set H) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp huZ ⟨s, hs⟩)
  have hu1' : ((u : h.S) : H) ≠ 1 := fun h1 => hu1 (Subtype.ext (Subtype.ext h1))
  have hua : ((u : h.S) : H) = h.a := by
    have : ((u : h.S) : H) ∈ h.P ⊓ centralizer (h.S : Set H) :=
      mem_inf.mpr ⟨mem_inf.mpr ⟨huS, huC⟩, huc⟩
    rw [hPS] at this
    exact eq_of_mem_zpowers_of_orderOf_eq_two h.orderOf_a this hu1'
  have he'o : orderOf e' = 2 := by
    rw [he', show g'⁻¹ * h.a * g' = (MulAut.conj g'⁻¹) h.a by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, h.orderOf_a]
  have hue : ((u : h.S) : H) = e' := by
    have : ((u : h.S) : H) ∈ (h.S ⊓ coreActionKernel (conjugate h.J g')) ⊓
        centralizer (h.S : Set H) := mem_inf.mpr ⟨mem_inf.mpr ⟨huS, huC'⟩, huc⟩
    rw [hPS'] at this
    exact eq_of_mem_zpowers_of_orderOf_eq_two he'o this hu1'
  apply he'a
  rw [← hue, hua]
  exact mem_zpowers _

end Hyp52

end CFSG.ComponentClassification.GSThmB
