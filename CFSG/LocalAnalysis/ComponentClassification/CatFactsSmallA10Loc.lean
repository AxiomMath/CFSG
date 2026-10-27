module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA10T
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10W
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma513

public section

namespace CFSG.ComponentClassification.CatFactsSmall

namespace A10

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open Equiv

section Odd

variable {G : Type*} [Group G]

theorem exists_conj_of_inv_mul_mem {d e : G} (hd : d * d = 1) (he : e * e = 1)
    (hodd : Odd (orderOf (e * d⁻¹))) :
    ∃ j : ℕ, e = (e * d⁻¹) ^ j * d * ((e * d⁻¹) ^ j)⁻¹ := by
  set o := e * d⁻¹ with ho
  obtain ⟨m, hm⟩ := hodd
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have heod : e = o * d := by rw [ho, inv_mul_cancel_right]
  have hdo : d * o * d = o⁻¹ := by
    have h1 : o * d * (o * d) = 1 := by rw [← heod, he]
    calc d * o * d = o⁻¹ * (o * d * (o * d)) := by group
      _ = o⁻¹ := by rw [h1, mul_one]
  have hdoj : ∀ j : ℕ, d * o ^ j * d = (o ^ j)⁻¹ := by
    intro j
    have : d * o ^ j * d = (d * o * d) ^ j := by
      rw [show d * o ^ j * d = d * o ^ j * d⁻¹ by rw [hdinv], ← conj_pow, hdinv]
    rw [this, hdo, inv_pow]
  refine ⟨m + 1, ?_⟩
  have hr2 : o ^ (m + 1) * o ^ (m + 1) = o := by
    rw [← pow_add, show m + 1 + (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, ← hm,
      pow_orderOf_eq_one, one_mul]
  have h3 : d * (o ^ (m + 1))⁻¹ = o ^ (m + 1) * d := by
    have h4 := hdoj (m + 1)
    calc d * (o ^ (m + 1))⁻¹ = d * (d * o ^ (m + 1) * d) := by rw [h4]
      _ = (d * d) * o ^ (m + 1) * d := by group
      _ = o ^ (m + 1) * d := by rw [hd, one_mul]
  rw [mul_assoc, h3, ← mul_assoc, hr2, heod]

end Odd

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)
  (eK : OddBar h.K ≃* alternatingGroup (Fin 10))

theorem odd_orderOf_of_mem_oddCoreIn_K {x : H} (hx : x ∈ oddCoreIn h.K) : Odd (orderOf x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, ho, rfl⟩ := hx
  rw [subtype_apply, Subgroup.orderOf_coe, ← Subgroup.orderOf_mk o ho]
  have h1 := (pPrimeCore_coprime_card (p := 2) (G := h.K)).coprime_dvd_right
    (orderOf_dvd_natCard (⟨o, ho⟩ : pPrimeCore 2 h.K))
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h2 => by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h1
    exact h1 h2)

theorem eq_one_of_mem_TK_of_rhoW_eq_one {u : h.W} (hu : (u : H) ∈ h.T ⊓ h.K)
    (h1 : rhoW h hKa eK u = 1) : u = 1 := by
  have hB : (u : H) ∈ h.B := (rhoW_T_eq_one_iff hKa eK (t := ⟨u, hu.1⟩)).1 h1
  have hO := mem_oddCoreIn_K_of_rhoW_eq_one hKa eK (k := ⟨u, hu.2⟩) h1
  have hodd := odd_orderOf_of_mem_oddCoreIn_K hO
  obtain ⟨e, he⟩ := (isPGroup_S h).to_le (h.B_le.trans inf_le_left) ⟨u, hB⟩
  have he' : (u : H) ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  have hdvd := orderOf_dvd_of_pow_eq_one he'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' hne).2 even_two)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact Subtype.ext hi

variable (eJ : OddBar h.J ≃* alternatingGroup (Fin 6))

theorem TK_le_W : h.T ⊓ h.K ≤ h.W := fun _ hu => T_le_W hu.1

include eJ in
theorem rhoW_TK_range {τ : Perm (Fin 10)} (h4 : τ.support.card = 4)
    (hL : ∀ l, l ∈ Lsub hKa eK ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    (hLcard : Nat.card (Lsub hKa eK) = 360) :
    ((rhoW h hKa eK).comp (inclusion TK_le_W)).range = fourGroup h4 := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨u, u.2.1⟩
  · intro hv
    obtain ⟨t, ht, htv⟩ := exists_T_K_of_mem_fourGroup hKa eK h4 hL hv
    exact ⟨⟨t, ht⟩, htv⟩

theorem rhoW_TK_injective :
    Function.Injective ((rhoW h hKa eK).comp (inclusion (TK_le_W (h := h)))) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have := eq_one_of_mem_TK_of_rhoW_eq_one hKa eK (u := inclusion TK_le_W u) u.2 hu
  have h2 : ((inclusion TK_le_W u : h.W) : H) = 1 := by rw [this]; rfl
  exact Subtype.ext h2

include eJ in
theorem card_TK {τ : Perm (Fin 10)} (h4 : τ.support.card = 4)
    (hL : ∀ l, l ∈ Lsub hKa eK ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    (hLcard : Nat.card (Lsub hKa eK) = 360) : Nat.card (h.T ⊓ h.K : Subgroup H) = 4 := by
  rw [Nat.card_congr (MonoidHom.ofInjective (rhoW_TK_injective hKa eK)).toEquiv,
    rhoW_TK_range hKa eK eJ h4 hL hLcard, card_fourGroup]

theorem fourGroup_comm {τ : Perm (Fin 10)} (h4 : τ.support.card = 4) {σ σ' : Perm (Fin 10)}
    (hσ : σ ∈ fourGroup h4) (hσ' : σ' ∈ fourGroup h4) : σ * σ' = σ' * σ := by
  have h1 := ((mem_fourGroup h4 _).1 (mul_mem hσ hσ')).2.2
  have h2 := ((mem_fourGroup h4 _).1 hσ).2.2
  have h3 := ((mem_fourGroup h4 _).1 hσ').2.2
  calc σ * σ' = (σ * σ')⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = σ'⁻¹ * σ⁻¹ := mul_inv_rev σ σ'
    _ = σ' * σ := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]

include eJ in
theorem exists_lift_normalizer {τ : Perm (Fin 10)} (h4 : τ.support.card = 4)
    (hL : ∀ l, l ∈ Lsub hKa eK ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    (hLcard : Nat.card (Lsub hKa eK) = 360) {π : Perm (Fin 10)}
    (hπA : π ∈ alternatingGroup (Fin 10))
    (hπN : π ∈ normalizer (fourGroup h4 : Set (Perm (Fin 10)))) :
    ∃ n : h.K, (n : H) ∈ normalizer ((h.T ⊓ h.K : Subgroup H) : Set H) ∧
      ∀ u : h.W, (u : H) ∈ h.T ⊓ h.K →
        rhoW h hKa eK (⟨n, K_le_W h n.2⟩ * u * (⟨n, K_le_W h n.2⟩ : h.W)⁻¹) =
          π * rhoW h hKa eK u * π⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_lift_alt hKa eK hπA
  set A := h.T ⊓ h.K with hA
  set X : Subgroup H := ((fourGroup h4).comap (rhoW h hKa eK)).map h.W.subtype ⊓ h.K with hX
  have hXW : X ≤ h.W := fun x hx => K_le_W h hx.2
  have hmemX : ∀ w : h.W, (w : H) ∈ h.K → rhoW h hKa eK w ∈ fourGroup h4 → (w : H) ∈ X :=
    fun w hwK hw => ⟨⟨w, hw, rfl⟩, hwK⟩
  have hXρ : ∀ x : X, rhoW h hKa eK (inclusion hXW x) ∈ fourGroup h4 := by
    rintro ⟨x, ⟨w, hw, hwx⟩, hxK⟩
    have : inclusion hXW ⟨x, ⟨w, hw, hwx⟩, hxK⟩ = w := Subtype.ext hwx.symm
    rw [this]
    exact hw
  have hAX : A ≤ X := fun u hu =>
    hmemX ⟨u, TK_le_W hu⟩ hu.2 (rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨u, hu.1⟩)
  set ψ : X →* Perm (Fin 10) := (rhoW h hKa eK).comp (inclusion hXW) with hψ
  have hψrange : ψ.range = fourGroup h4 := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact hXρ x
    · intro hv
      obtain ⟨t, ht, htv⟩ := exists_T_K_of_mem_fourGroup hKa eK h4 hL hv
      exact ⟨⟨t, hAX ht⟩, htv⟩
  have hψker : Nat.card ψ.ker = Nat.card (pPrimeCore 2 h.K) := by
    have hle : oddCoreIn h.K ≤ X := by
      rintro _ ⟨o, ho, rfl⟩
      refine hmemX ⟨o, K_le_W h o.2⟩ o.2 ?_
      have h1 := oddTwoCore_le_ker hKa eK
        (pPrimeCore_le_oddTwoCore' (mem_pPrimeCore_W_of_mem_pPrimeCore
          (W_le_normalizer_K h hKa) ho))
      rw [MonoidHom.mem_ker] at h1
      rw [h1]
      exact one_mem _
    have hker : ψ.ker = (oddCoreIn h.K).subgroupOf X := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro hx
        exact mem_oddCoreIn_K_of_rhoW_eq_one hKa eK (k := ⟨x, x.2.2⟩) hx
      · rintro ⟨o, ho, hox⟩
        have h1 := oddTwoCore_le_ker hKa eK
          (pPrimeCore_le_oddTwoCore' (mem_pPrimeCore_W_of_mem_pPrimeCore
            (W_le_normalizer_K h hKa) ho))
        rw [MonoidHom.mem_ker] at h1
        have : inclusion hXW x = ⟨o, K_le_W h o.2⟩ := Subtype.ext (by
          rw [coe_inclusion]
          exact hox.symm)
        rw [hψ, MonoidHom.comp_apply, this]
        exact h1
    rw [hker, ← card_map_of_injective X.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hle]
    exact card_map_of_injective h.K.subtype_injective
  have hXcard : Nat.card X = Nat.card (pPrimeCore 2 h.K) * 4 := by
    rw [← ψ.ker.card_mul_index, index_ker, hψker, hψrange, card_fourGroup]
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 h.K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have hfact : (Nat.card X).factorization 2 = 2 := by
    have hpos : Nat.card (pPrimeCore 2 h.K) ≠ 0 := Nat.card_pos.ne'
    rw [hXcard, Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, zero_add,
      show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  have hcardA : Nat.card A = 4 := card_TK hKa eK eJ h4 hL hLcard
  have hkA : A.map (MulAut.conj (k : H)).toMonoidHom ≤ X := by
    rintro _ ⟨u, hu, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hkuK : (k : H) * u * (k : H)⁻¹ ∈ h.K := mul_mem (mul_mem k.2 hu.2) (inv_mem k.2)
    refine hmemX ⟨_, K_le_W h hkuK⟩ hkuK ?_
    have he : (⟨(k : H) * u * (k : H)⁻¹, K_le_W h hkuK⟩ : h.W) =
        ⟨k, K_le_W h k.2⟩ * ⟨u, TK_le_W hu⟩ * (⟨k, K_le_W h k.2⟩ : h.W)⁻¹ := Subtype.ext (by simp)
    rw [he, map_mul, map_mul, map_inv, hk]
    exact (mem_normalizer_iff.1 hπN _).1
      (rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨u, hu.1⟩)
  have hcardP : Nat.card (A.subgroupOf X) = 2 ^ (Nat.card X).factorization 2 := by
    rw [hfact, ← card_map_of_injective X.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hAX, hcardA]
    norm_num
  have hcardP' : Nat.card ((A.map (MulAut.conj (k : H)).toMonoidHom).subgroupOf X) =
      2 ^ (Nat.card X).factorization 2 := by
    rw [hfact, ← card_map_of_injective X.subtype_injective, subgroupOf_map_subtype,
      inf_of_le_left hkA, card_map_of_injective (MulAut.conj (k : H)).injective, hcardA]
    norm_num
  set PA := Sylow.ofCard (A.subgroupOf X) hcardP with hPA
  set PA' := Sylow.ofCard _ hcardP' with hPA'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X PA PA'
  have hgK : (g : H) ∈ h.K := g.2.2
  refine ⟨⟨(g : H)⁻¹ * k, mul_mem (inv_mem hgK) k.2⟩, ?_, ?_⟩
  · apply mem_normalizer_of_conj_le
    intro u hu
    have hmem : (⟨(k : H) * u * (k : H)⁻¹, hkA ⟨u, hu, rfl⟩⟩ : X) ∈ (PA' : Subgroup X) := by
      rw [hPA', Sylow.coe_ofCard, mem_subgroupOf]
      exact ⟨u, hu, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, hPA,
      Sylow.coe_ofCard, mem_subgroupOf] at hmem
    simp only [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply] at hmem
    convert hmem using 1
    simp only [coe_mul, coe_inv]
    group
  · intro u hu
    have hgV : rhoW h hKa eK (inclusion hXW g) ∈ fourGroup h4 := hXρ g
    have hπu : π * rhoW h hKa eK u * π⁻¹ ∈ fourGroup h4 := by
      have := rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨u, hu.1⟩
      exact (mem_normalizer_iff.1 hπN _).1 this
    have he : (⟨(g : H)⁻¹ * k, K_le_W h (mul_mem (inv_mem hgK) k.2)⟩ : h.W) =
        (inclusion hXW g)⁻¹ * ⟨k, K_le_W h k.2⟩ := Subtype.ext (by simp)
    rw [he, map_mul, map_mul, map_inv, map_mul, map_inv, hk]
    rw [show ((rhoW h hKa eK (inclusion hXW g))⁻¹ * π) * rhoW h hKa eK u *
        ((rhoW h hKa eK (inclusion hXW g))⁻¹ * π)⁻¹ = (rhoW h hKa eK (inclusion hXW g))⁻¹ *
          ((π * rhoW h hKa eK u * π⁻¹) * rhoW h hKa eK (inclusion hXW g)) by group,
      fourGroup_comm h4 hπu hgV, inv_mul_cancel_left]

include eJ in
theorem exists_inv_D_JB : ∃ d ∈ h.D, d ∈ GSLit.fixedLayer h.J h.B ∧ orderOf d = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDS : h.D ≤ h.S := inf_le_left
  have hBS : h.B ≤ h.S := h.B_le.trans inf_le_left
  obtain ⟨TD, hTD⟩ := exists_sylow_D h
  have h8 : 2 ^ 3 ∣ Nat.card h.J := by
    have hc := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 h.J)
    have h360 : Nat.card (h.J ⧸ pPrimeCore 2 h.J) = 360 := by
      rw [show Nat.card (h.J ⧸ pPrimeCore 2 h.J) = Nat.card (OddBar h.J) from rfl,
        Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    rw [hc, h360]
    exact Dvd.dvd.mul_right (by norm_num) _
  have h8T := TD.pow_dvd_card_of_pow_dvd_card h8
  have hDne : h.D ≠ ⊥ := by
    intro hD
    have h1 : Nat.card (TD : Subgroup h.J) = 1 := by
      rw [hTD, hD, bot_subgroupOf, card_bot]
    rw [h1] at h8T
    norm_num at h8T
  set G' := h.D ⊔ h.B with hG'
  have hG'S : G' ≤ h.S := sup_le hDS hBS
  have hG'2 : IsPGroup 2 G' := (isPGroup_S h).to_le hG'S
  have : Group.IsNilpotent G' := hG'2.isNilpotent
  have hDn : (h.D.subgroupOf G').Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have hgS : (g : H) ∈ h.S := hG'S g.2
    simp only [coe_mul, coe_inv]
    exact ⟨h.S.mul_mem (h.S.mul_mem hgS hn.1) (h.S.inv_mem hgS),
      (mem_normalizer_iff.1 (h.S_le hgS).2 _).1 hn.2⟩⟩
  have hne : h.D.subgroupOf G' ≠ ⊥ := by
    intro h1
    rw [subgroupOf_eq_bot] at h1
    exact hDne (disjoint_self.1 (h1.mono_right le_sup_left))
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨y, hyD₀, hyZ⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hyD : (y : H) ∈ h.D := hyD₀
  set E := h.D ⊓ centralizer (h.B : Set H) with hE
  have hyE : (y : H) ∈ E := by
    refine ⟨hyD, mem_centralizer_iff.2 fun b hb => ?_⟩
    have := mem_center_iff.1 hyZ ⟨b, mem_sup_right hb⟩
    exact congrArg Subtype.val this
  have hE2 : IsPGroup 2 E := (isPGroup_S h).to_le (inf_le_left.trans hDS)
  have hEnt : Nontrivial E := ⟨⟨⟨y, hyE⟩, 1, fun h1 => by
    have h2 : (y : H) = 1 := congrArg Subtype.val h1
    apply hy1
    apply Subtype.ext
    apply Subtype.ext
    exact h2⟩⟩
  obtain ⟨n, hn, hEcard⟩ := hE2.nontrivial_iff_card.1 hEnt
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := E) 2
    (by rw [hEcard]; exact dvd_pow_self 2 hn.ne')
  have hd' : orderOf (d : H) = 2 := by rw [Subgroup.orderOf_coe, hd]
  refine ⟨d, d.2.1, ?_, hd'⟩
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := (isPGroup_S h).to_le hBS
  rw [GSLit.fixedLayer_eq_closure (B5a.isQuasisimple_J h) hBJ hB2]
  exact subset_closure ⟨⟨h.D_le_J d.2.1, d.2.2⟩, 1, by rw [hd', pow_one]⟩

include hKa eK eJ in
theorem exists_conj_D (haA : h.a ∈ h.T ⊓ h.K) : ∃ g ∈ h.K, g⁻¹ * h.a * g ∈ h.D := by
  obtain ⟨τ, -, -, -, h4, hL, hLcard⟩ := exists_std_tau hKa eK eJ
  obtain ⟨d, hdD, hdJB, hd2⟩ := exists_inv_D_JB eJ (h := h)
  have hdK : d ∈ h.K := JB_le_K hKa hdJB
  have hdd : d * d = 1 := by rw [← sq, ← hd2, pow_orderOf_eq_one]
  have haa : h.a * h.a = 1 := by rw [← sq, ← h.orderOf_a, pow_orderOf_eq_one]
  set aW : h.W := ⟨h.a, TK_le_W haA⟩ with haW
  set dW : h.W := ⟨d, K_le_W h hdK⟩ with hdW
  have hαV : rhoW h hKa eK aW ∈ fourGroup h4 :=
    rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨h.a, haA.1⟩
  have hα1 : rhoW h hKa eK aW ≠ 1 := by
    intro h1
    have := eq_one_of_mem_TK_of_rhoW_eq_one hKa eK (u := aW) haA h1
    have h2 : h.a = 1 := congrArg Subtype.val this
    have h3 := h.orderOf_a
    rw [h2, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨hαA, hαfix, hα2⟩ := (mem_fourGroup h4 _).1 hαV
  have hαs : (rhoW h hKa eK aW).support.card = 4 :=
    support_card_eq_four hαA hα2 hα1 (S := τ.support) hαfix (by rw [h4]; norm_num)
  have hδL : rhoW h hKa eK dW ∈ Lsub hKa eK :=
    ⟨wbarMk h.B dW, ⟨dW, hdJB, rfl⟩, rhoBar_mk _ _ _⟩
  obtain ⟨hδA, hδfix⟩ := (hL _).1 hδL
  have hδ2 : rhoW h hKa eK dW * rhoW h hKa eK dW = 1 := by
    rw [← map_mul]
    have : dW * dW = 1 := Subtype.ext hdd
    rw [this, map_one]
  have hδ1 : rhoW h hKa eK dW ≠ 1 := by
    intro h1
    have hO := mem_oddCoreIn_K_of_rhoW_eq_one hKa eK (k := ⟨d, hdK⟩) h1
    have := odd_orderOf_of_mem_oddCoreIn_K hO
    rw [hd2] at this
    exact absurd this (by decide)
  have hδs : (rhoW h hKa eK dW).support.card = 4 := by
    refine support_card_eq_four hδA hδ2 hδ1 (S := τ.supportᶜ) (fun x hx => hδfix x ?_) ?_
    · simpa using hx
    · rw [Finset.card_compl, Fintype.card_fin, h4]
      norm_num
  obtain ⟨π, hπA, hπ⟩ := exists_alt_conj_of_support_four hα2 hα1 hδ2 hδ1 hαs hδs
  obtain ⟨k, hk⟩ := exists_lift_alt hKa eK (inv_mem hπA)
  have haK : h.a ∈ h.K := haA.2
  set e := (k : H)⁻¹ * h.a * k with he
  have heK : e ∈ h.K := mul_mem (mul_mem (inv_mem k.2) haK) k.2
  have hee : e * e = 1 := by
    rw [he, show (k : H)⁻¹ * h.a * k * ((k : H)⁻¹ * h.a * k) = (k : H)⁻¹ * (h.a * h.a) * k by
      group, haa, mul_one, inv_mul_cancel]
  have hoK : e * d⁻¹ ∈ h.K := mul_mem heK (inv_mem hdK)
  have hρo : rhoW h hKa eK ⟨(⟨e * d⁻¹, hoK⟩ : h.K), K_le_W h hoK⟩ = 1 := by
    have h1 : (⟨(⟨e * d⁻¹, hoK⟩ : h.K), K_le_W h hoK⟩ : h.W) =
        (⟨k, K_le_W h k.2⟩ : h.W)⁻¹ * aW * ⟨k, K_le_W h k.2⟩ * dW⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hk, inv_inv]
    rw [show π * rhoW h hKa eK aW * π⁻¹ = rhoW h hKa eK dW from hπ, mul_inv_cancel]
  have hodd := odd_orderOf_of_mem_oddCoreIn_K (mem_oddCoreIn_K_of_rhoW_eq_one hKa eK hρo)
  obtain ⟨j, hj⟩ := exists_conj_of_inv_mul_mem hdd hee hodd
  set o := e * d⁻¹ with ho
  refine ⟨(k : H) * o ^ j, mul_mem k.2 (pow_mem hoK j), ?_⟩
  have h1 : ((k : H) * o ^ j)⁻¹ * h.a * ((k : H) * o ^ j) = (o ^ j)⁻¹ * e * o ^ j := by
    rw [he]
    group
  have h2 : (o ^ j)⁻¹ * e * o ^ j = d := by
    calc (o ^ j)⁻¹ * e * o ^ j = (o ^ j)⁻¹ * (o ^ j * d * (o ^ j)⁻¹) * o ^ j := by
          rw [← hj]
      _ = d := by group
  rw [h1, h2]
  exact hdD

include hKa eK eJ in
theorem a10Local : Nat.card ↥(h.T ⊓ h.K) = 4 ∧ (∀ u ∈ h.T ⊓ h.K, u ^ 2 = 1) ∧
    (∃ N₀ : Subgroup H, N₀ ≤ h.K ∧ N₀ ≤ normalizer (h.T : Set H) ∧
      N₀ ≤ centralizer (h.B : Set H) ∧
      (∀ u ∈ h.T ⊓ h.K, ∀ v ∈ h.T ⊓ h.K, u ≠ 1 → v ≠ 1 → ∃ n ∈ N₀, n * u * n⁻¹ = v) ∧
      ∃ n ∈ N₀, (∃ k : ℕ, n ^ 2 ^ k = 1) ∧ ∃ u ∈ h.T ⊓ h.K, n * u * n⁻¹ ≠ u) ∧
    (h.a ∈ h.T ⊓ h.K → ∃ g ∈ h.K, g⁻¹ * h.a * g ∈ h.D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, -, -, -, h4, hL, hLcard⟩ := exists_std_tau hKa eK eJ
  set A := h.T ⊓ h.K with hA
  have hinj := rhoW_TK_injective hKa eK (h := h)
  have hrange := rhoW_TK_range hKa eK eJ h4 hL hLcard
  have hinjA : ∀ x y : h.W, (x : H) ∈ A → (y : H) ∈ A → rhoW h hKa eK x = rhoW h hKa eK y →
      x = y := by
    intro x y hx hy hxy
    have := hinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
    have h2 := congrArg (fun z : ↥(h.T ⊓ h.K) => (z : H)) this
    exact Subtype.ext h2
  have hV : ∀ x : h.W, (x : H) ∈ A → rhoW h hKa eK x ∈ fourGroup h4 := fun x hx =>
    rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨x, hx.1⟩
  have hsurjA : ∀ σ ∈ fourGroup h4, ∃ x : h.W, (x : H) ∈ A ∧ rhoW h hKa eK x = σ := by
    intro σ hσ
    rw [← hrange] at hσ
    obtain ⟨u, hu⟩ := hσ
    exact ⟨inclusion TK_le_W u, u.2, hu⟩
  have hne1 : ∀ x : h.W, (x : H) ∈ A → (x : H) ≠ 1 → rhoW h hKa eK x ≠ 1 := by
    intro x hx hx1 h1
    exact hx1 (congrArg Subtype.val (eq_one_of_mem_TK_of_rhoW_eq_one hKa eK hx h1))
  have hKB : h.K ≤ centralizer (h.B : Set H) := h.K_le_layer_W.trans h.V_le_centralizer_B
  refine ⟨card_TK hKa eK eJ h4 hL hLcard, fun u hu => ?_, ⟨h.K ⊓ normalizer (A : Set H),
    inf_le_left, fun n hn => ?_, fun n hn => hKB hn.1, fun u hu v hv hu1 hv1 => ?_, ?_⟩,
    exists_conj_D hKa eK eJ⟩
  ·
    have h1 : rhoW h hKa eK (⟨u, TK_le_W hu⟩ ^ 2) = rhoW h hKa eK 1 := by
      rw [map_pow, sq, map_one]
      exact ((mem_fourGroup h4 _).1 (hV _ hu)).2.2
    have h2 := hinjA _ _ (by simpa using pow_mem hu 2) (one_mem _) h1
    simpa using congrArg Subtype.val h2
  ·
    apply mem_normalizer_of_conj_le
    intro t ht
    obtain ⟨x, hxA, hxt⟩ := hsurjA _ (rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨t, ht⟩)
    have hbT : (x : H)⁻¹ * t ∈ h.T := mul_mem (inv_mem hxA.1) ht
    have hb : (x : H)⁻¹ * t ∈ h.B := by
      refine (rhoW_T_eq_one_iff hKa eK (t := ⟨_, hbT⟩)).1 ?_
      have he : inclusion T_le_W (⟨(x : H)⁻¹ * t, hbT⟩ : h.T) =
          x⁻¹ * inclusion T_le_W (⟨t, ht⟩ : h.T) := Subtype.ext rfl
      rw [he, map_mul, map_inv, hxt, inv_mul_cancel]
    have hnb : n * ((x : H)⁻¹ * t) * n⁻¹ = (x : H)⁻¹ * t := by
      rw [← (mem_centralizer_iff.1 (hKB hn.1) _ hb), mul_inv_cancel_right]
    have hnx : n * x * n⁻¹ ∈ A := (mem_normalizer_iff.1 hn.2 x).1 hxA
    have h1 : n * t * n⁻¹ = (n * x * n⁻¹) * (n * ((x : H)⁻¹ * t) * n⁻¹) := by group
    rw [h1, hnb]
    exact mul_mem hnx.1 hbT
  ·
    obtain ⟨π, hπA, hπN, hπ⟩ := exists_conj_fourGroup h4 (hV ⟨u, TK_le_W hu⟩ hu)
      (hV ⟨v, TK_le_W hv⟩ hv) (hne1 _ hu hu1) (hne1 _ hv hv1)
    obtain ⟨n, hnA, hnρ⟩ := exists_lift_normalizer hKa eK eJ h4 hL hLcard hπA hπN
    refine ⟨n, ⟨n.2, hnA⟩, ?_⟩
    set nW : h.W := ⟨n, K_le_W h n.2⟩ with hnW
    set uW : h.W := ⟨u, TK_le_W hu⟩ with huW
    set vW : h.W := ⟨v, TK_le_W hv⟩ with hvW
    have hnu : ((nW * uW * nW⁻¹ : h.W) : H) ∈ A := (mem_normalizer_iff.1 hnA u).1 hu
    have h1 := hnρ uW hu
    rw [hπ] at h1
    have h2 := hinjA (nW * uW * nW⁻¹) vW hnu hv h1
    have h3 : ((nW * uW * nW⁻¹ : h.W) : H) = v := congrArg Subtype.val h2
    exact h3
  ·
    obtain ⟨π, hπA, hπN, hπ2, σ, hσV, hσπ⟩ := exists_two_elt_fourGroup h4
    obtain ⟨n, hnA, hnρ⟩ := exists_lift_normalizer hKa eK eJ h4 hL hLcard hπA hπN
    set nW : h.W := ⟨n, K_le_W h n.2⟩ with hnW
    have hpow : ∀ j : ℕ, ∀ x : h.W, (x : H) ∈ A →
        ((nW ^ j * x * (nW ^ j)⁻¹ : h.W) : H) ∈ A ∧
          rhoW h hKa eK (nW ^ j * x * (nW ^ j)⁻¹) = π ^ j * rhoW h hKa eK x * (π ^ j)⁻¹ := by
      intro j
      induction j with
      | zero => intro x hx; simpa using hx
      | succ j ih =>
        intro x hx
        obtain ⟨h1, h2⟩ := ih x hx
        have he : nW ^ (j + 1) * x * (nW ^ (j + 1))⁻¹ = nW * (nW ^ j * x * (nW ^ j)⁻¹) * nW⁻¹ := by
          group
        rw [he]
        refine ⟨(mem_normalizer_iff.1 hnA _).1 h1, ?_⟩
        rw [hnρ _ h1, h2]
        group
    obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (n : H)).ne'
    obtain ⟨x, hxA, hxσ⟩ := hsurjA σ hσV
    refine ⟨(n : H) ^ m,
      pow_mem (show (n : H) ∈ h.K ⊓ normalizer (A : Set H) from ⟨n.2, hnA⟩) m, ⟨a, ?_⟩, x, hxA,
      fun h1 => hσπ ?_⟩
    · rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
    · obtain ⟨-, h2⟩ := hpow m x hxA
      have h3 : nW ^ m * x * (nW ^ m)⁻¹ = x := Subtype.ext (by simpa [hnW] using h1)
      rw [h3, hxσ] at h2
      obtain ⟨i, hi⟩ := hm
      have hπm : π ^ m = π := by
        rw [hi, pow_succ, pow_mul, sq, hπ2, one_pow, one_mul]
      rw [hπm] at h2
      exact h2.symm

end A10

open CFSG.ComponentClassification.GSThmB A10 in
theorem cfA10Local : CFA10Local := by
  intro H _ _ h hrow
  obtain ⟨⟨eJ⟩, hKa, ⟨eK⟩⟩ := hrow
  exact a10Local hKa eK eJ

end CFSG.ComponentClassification.CatFactsSmall
