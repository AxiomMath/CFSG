module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7SwapMain
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

theorem sft_not_four_dvd {B : Type} [Group B] [Finite B] (t : B) (ht : orderOf t = 2)
    (hC : ∀ b : B, b * t = t * b → b = 1 ∨ b = t) : ¬ 4 ∣ Nat.card B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hP : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht]
    norm_num
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have htS : t ∈ S := hS (mem_zpowers t)
  have hSle : ∀ s ∈ S, s = 1 ∨ s = t := by
    have hSp : IsPGroup 2 S := S.isPGroup'
    have : Nontrivial S := ⟨⟨⟨t, htS⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
    have : Nontrivial (center S) := hSp.center_nontrivial
    have hZp : IsPGroup 2 (center S) := hSp.to_subgroup _
    have h2dvd : 2 ∣ Nat.card (center S) := by
      obtain ⟨n, hn⟩ := hZp.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact not_nontrivial_iff_subsingleton.2 (Nat.card_eq_one_iff_unique.1 hn).1 inferInstance
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 h2dvd
    set z' : B := z.1.1 with hz'
    have hz'2 : orderOf z' = 2 := by
      rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
    have hz'comm : ∀ s ∈ S, z' * s = s * z' := by
      intro s hs
      have := mem_center_iff.1 z.2 ⟨s, hs⟩
      have h2 := congrArg (fun a : S => (a : B)) this
      exact h2.symm
    have hz't : z' = t := by
      rcases hC z' (hz'comm t htS) with h | h
      · rw [h, orderOf_one] at hz'2; omega
      · exact h
    intro s hs
    apply hC s
    have := hz'comm s hs
    rw [hz't] at this
    exact this.symm
  have hsub : (S : Subgroup B) ≤ zpowers t := by
    intro s hs
    rcases hSle s hs with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers t
  have hcard1 : Nat.card S ≤ 2 := by
    have := Subgroup.card_le_of_le hsub
    rwa [Nat.card_zpowers, ht] at this
  intro h4
  have h22 : 2 ^ 2 ∣ Nat.card B := by simpa using h4
  have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h22
  have h5 := Sylow.card_eq_multiplicity S
  have h6 : 2 ^ 2 ≤ 2 ^ (Nat.card B).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3
  rw [← h5] at h6
  omega

theorem sft_zpowers_cases {X : Type} [Group X] {tt : X} (htt : orderOf tt = 2) {o : X}
    (ho : o ∈ zpowers tt) : o = 1 ∨ o = tt := by
  have hsq : tt * tt = 1 := mul_self_of_orderOf_two htt
  obtain ⟨n, hn0⟩ := ho
  have hn : tt ^ n = o := hn0
  rw [← hn]
  have hmod : tt ^ n = tt ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul]
    have : tt ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hsq
    rw [this, one_zpow, mul_one]
  have : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases this with h | h
  · left; rw [hmod, h]; simp
  · right; rw [hmod, h]; simp

@[expose] def sftF1 : Subgroup (A6 × A6) := (⊤ : Subgroup A6).prod ⊥

@[expose] def sftF2 : Subgroup (A6 × A6) := (⊥ : Subgroup A6).prod ⊤

instance : sftF1.Normal := by unfold sftF1; infer_instance

instance : sftF2.Normal := by unfold sftF2; infer_instance

theorem mem_sftF1 {g : A6 × A6} : g ∈ sftF1 ↔ g.2 = 1 :=
  ⟨fun h => Subgroup.mem_bot.1 (Subgroup.mem_prod.1 h).2,
    fun h => Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, Subgroup.mem_bot.2 h⟩⟩

theorem mem_sftF2 {g : A6 × A6} : g ∈ sftF2 ↔ g.1 = 1 :=
  ⟨fun h => Subgroup.mem_bot.1 (Subgroup.mem_prod.1 h).1,
    fun h => Subgroup.mem_prod.2 ⟨Subgroup.mem_bot.2 h, Subgroup.mem_top _⟩⟩

theorem card_sftF1 : Nat.card sftF1 = 360 := by
  rw [← card_alt6]
  refine Nat.card_eq_of_bijective (fun x => (x : A6 × A6).1) ⟨?_, ?_⟩
  · rintro ⟨⟨a, b⟩, hx⟩ ⟨⟨a', b'⟩, hy⟩ h
    have hb : b = 1 := mem_sftF1.1 hx
    have hb' : b' = 1 := mem_sftF1.1 hy
    have h' : a = a' := h
    exact Subtype.ext (Prod.ext h' (hb.trans hb'.symm))
  · intro a
    exact ⟨⟨(a, 1), mem_sftF1.2 rfl⟩, rfl⟩

theorem card_sftF2 : Nat.card sftF2 = 360 := by
  rw [← card_alt6]
  refine Nat.card_eq_of_bijective (fun x => (x : A6 × A6).2) ⟨?_, ?_⟩
  · rintro ⟨⟨a, b⟩, hx⟩ ⟨⟨a', b'⟩, hy⟩ h
    have ha : a = 1 := mem_sftF2.1 hx
    have ha' : a' = 1 := mem_sftF2.1 hy
    have h' : b = b' := h
    exact Subtype.ext (Prod.ext (ha.trans ha'.symm) h')
  · intro b
    exact ⟨⟨(1, b), mem_sftF2.2 rfl⟩, rfl⟩

theorem sft_card_cases (K : Subgroup (A6 × A6)) [K.Normal] (hK : Nat.card K = 360) :
    K = sftF1 ∨ K = sftF2 := by
  have := isSimple_alt6
  rcases normal_prod_cases alt6_nonabelian K with h | h | h | h
  · exfalso
    rw [h, Subgroup.card_bot] at hK
    omega
  · exfalso
    rw [h, Subgroup.card_top, Nat.card_prod, card_alt6] at hK
    omega
  · exact Or.inl h
  · exact Or.inr h

theorem sft_aut_prod_cases (ψ : A6 × A6 ≃* A6 × A6) :
    ((∀ a : A6, (ψ (a, 1)).2 = 1) ∧ ∀ b : A6, (ψ (1, b)).1 = 1) ∨
      ((∀ a : A6, (ψ (a, 1)).1 = 1) ∧ ∀ b : A6, (ψ (1, b)).2 = 1) := by
  have := isSimple_alt6
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  obtain ⟨a0, ha0⟩ := exists_ne (1 : A6)
  have hK1 : (sftF1.map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance ψ.toMonoidHom ψ.surjective
  have hK2 : (sftF2.map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance ψ.toMonoidHom ψ.surjective
  have hk1 := sft_card_cases (sftF1.map ψ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective hinj, card_sftF1])
  have hk2 := sft_card_cases (sftF2.map ψ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective hinj, card_sftF2])
  have hne : sftF1.map ψ.toMonoidHom ≠ sftF2.map ψ.toMonoidHom := by
    intro h
    have h' : sftF1 = sftF2 := Subgroup.map_injective hinj h
    have h1 : ((a0, 1) : A6 × A6) ∈ sftF1 := mem_sftF1.2 rfl
    have h2 : ((a0, 1) : A6 × A6) ∈ sftF2 := h' ▸ h1
    exact ha0 (mem_sftF2.1 h2)
  have hm1 : ∀ a : A6, ψ (a, 1) ∈ sftF1.map ψ.toMonoidHom := fun a =>
    Subgroup.mem_map_of_mem ψ.toMonoidHom (mem_sftF1.2 rfl)
  have hm2 : ∀ b : A6, ψ (1, b) ∈ sftF2.map ψ.toMonoidHom := fun b =>
    Subgroup.mem_map_of_mem ψ.toMonoidHom (mem_sftF2.2 rfl)
  rcases hk1 with h1 | h1 <;> rcases hk2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · left
    refine ⟨fun a => ?_, fun b => ?_⟩
    · have := hm1 a
      rw [h1] at this
      exact mem_sftF1.1 this
    · have := hm2 b
      rw [h2] at this
      exact mem_sftF2.1 this
  · right
    refine ⟨fun a => ?_, fun b => ?_⟩
    · have := hm1 a
      rw [h1] at this
      exact mem_sftF2.1 this
    · have := hm2 b
      rw [h2] at this
      exact mem_sftF1.1 this
  · exact absurd (h1.trans h2.symm) hne

theorem sft_proj_cases (L : Subgroup (A6 × A6)) [IsSimpleGroup L] (hL : Nat.card L = 360) :
    (∀ g ∈ L, g.1 = 1) ∨ (∀ g ∈ L, g.2 = 1) ∨
      ((∀ a : A6, ∃ g ∈ L, g.1 = a) ∧ (∀ b : A6, ∃ g ∈ L, g.2 = b)) := by
  let l1 : ↥L →* A6 := (MonoidHom.fst A6 A6).comp L.subtype
  let l2 : ↥L →* A6 := (MonoidHom.snd A6 A6).comp L.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal l1.ker with h1 | h1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal l2.ker with h2 | h2
    · right; right
      have hi1 : Function.Injective l1 := (MonoidHom.ker_eq_bot_iff l1).1 h1
      have hi2 : Function.Injective l2 := (MonoidHom.ker_eq_bot_iff l2).1 h2
      have hb1 : Function.Bijective l1 :=
        hi1.bijective_of_nat_card_le (by rw [hL, card_alt6])
      have hb2 : Function.Bijective l2 :=
        hi2.bijective_of_nat_card_le (by rw [hL, card_alt6])
      refine ⟨fun a => ?_, fun b => ?_⟩
      · obtain ⟨x, hx⟩ := hb1.2 a
        exact ⟨(x : A6 × A6), x.2, hx⟩
      · obtain ⟨x, hx⟩ := hb2.2 b
        exact ⟨(x : A6 × A6), x.2, hx⟩
    · right; left
      intro g hg
      have : (⟨g, hg⟩ : ↥L) ∈ l2.ker := by rw [h2]; exact Subgroup.mem_top _
      exact this
  · left
    intro g hg
    have : (⟨g, hg⟩ : ↥L) ∈ l1.ker := by rw [h1]; exact Subgroup.mem_top _
    exact this

section Embedded

variable {X : Type} [Group X] [Finite X] {tt : X}

theorem sft_aux_first (htt : orderOf tt = 2)
    (e : ↥(centralizer ({tt} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    (ξ : A6 × A6 →* X) (hξ : Function.Injective ξ) (ψ : A6 × A6 ≃* A6 × A6)
    (hψ : ∀ g, tt * ξ g * tt⁻¹ = ξ (ψ g))
    (hP1 : ∀ a : A6, (ψ (a, 1)).2 = 1)
    (hLr : ∀ l ∈ centralizerDerived tt, ∃ g, ξ g = l)
    (hL : ∀ g, ξ g ∈ centralizerDerived tt → g.1 = 1) : False := by
  have := isSimple_alt6
  have htt2 : tt * tt = 1 := mul_self_of_orderOf_two htt
  obtain ⟨O, hO⟩ : ∃ O : Subgroup X, O = (ξ.comp (MonoidHom.inl A6 A6)).range := ⟨_, rfl⟩
  have hOmem : ∀ o, o ∈ O ↔ ∃ a : A6, ξ (a, 1) = o := by
    intro o
    rw [hO, MonoidHom.mem_range]
    exact Iff.rfl
  have hn : ∀ o ∈ O, tt * o * tt⁻¹ ∈ O := by
    intro o ho
    obtain ⟨a, rfl⟩ := (hOmem o).1 ho
    rw [hψ]
    have h2 : ((ψ (a, 1)).1, (1 : A6)) = ψ (a, 1) := Prod.ext rfl (hP1 a).symm
    exact (hOmem _).2 ⟨(ψ (a, 1)).1, by rw [h2]⟩
  have hcomm : ∀ o ∈ O, ∀ l ∈ centralizerDerived tt, o * l = l * o := by
    intro o ho l hl
    obtain ⟨a, rfl⟩ := (hOmem o).1 ho
    obtain ⟨g, rfl⟩ := hLr l hl
    have hg1 := hL g hl
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp [hg1]) (by simp)
  have hfix : ∀ o ∈ O, tt * o = o * tt → o = 1 ∨ o = tt := by
    intro o ho hto
    have hoc : o ∈ centralizer ({tt} : Set X) := mem_centralizer_singleton_iff.2 hto.symm
    exact sft_zpowers_cases htt
      (mem_zpowers_of_commute_derived htt e hoc (fun l hl => hcomm o ho l hl))
  by_cases htO : tt ∈ O
  · have hinj : Function.Injective (ξ.comp (MonoidHom.inl A6 A6)) := by
      intro a b h
      have := hξ h
      exact (Prod.mk.inj this).1
    have hcard : Nat.card O = 360 := by
      rw [hO, ← card_alt6]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have ht' : orderOf (⟨tt, htO⟩ : ↥O) = 2 :=
      (Subgroup.orderOf_coe (⟨tt, htO⟩ : ↥O)).symm.trans htt
    have hC : ∀ b : ↥O, b * ⟨tt, htO⟩ = ⟨tt, htO⟩ * b → b = 1 ∨ b = ⟨tt, htO⟩ := by
      intro b hb
      have hb' : tt * (b : X) = (b : X) * tt := (congrArg Subtype.val hb).symm
      rcases hfix b b.2 hb' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    apply sft_not_four_dvd (⟨tt, htO⟩ : ↥O) ht' hC
    rw [hcard]
    norm_num
  · have hfix' : ∀ o ∈ O, tt * o = o * tt → o = 1 := fun o ho h =>
      (hfix o ho h).resolve_right (fun h' => htO (h' ▸ ho))
    obtain ⟨-, hab⟩ := inv_of_centralizer_eq_bot (O := O) htt2 hn hfix'
    obtain ⟨a0, b0, hne⟩ := alt6_nonabelian
    have h1 : ξ (a0, 1) ∈ O := (hOmem _).2 ⟨a0, rfl⟩
    have h2 : ξ (b0, 1) ∈ O := (hOmem _).2 ⟨b0, rfl⟩
    have h3 := hab _ h1 _ h2
    rw [← map_mul, ← map_mul] at h3
    have h4 := hξ h3
    exact hne (congrArg Prod.fst h4)

theorem sft_aux_count
    (e : ↥(centralizer ({tt} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    (ξ : A6 × A6 →* X) (hξ : Function.Injective ξ) (ψ : A6 × A6 ≃* A6 × A6)
    (hψ : ∀ g, tt * ξ g * tt⁻¹ = ξ (ψ g))
    (hP1 : ∀ a : A6, (ψ (a, 1)).2 = 1) (hP2 : ∀ b : A6, (ψ (1, b)).1 = 1)
    (hA : ∀ a : A6, ∃ g, ξ g ∈ centralizerDerived tt ∧ g.1 = a)
    (hB : ∀ b : A6, ∃ g, ξ g ∈ centralizerDerived tt ∧ g.2 = b) : False := by
  have hLc : ∀ l ∈ centralizerDerived tt, tt * l * tt⁻¹ = l := by
    rintro _ ⟨c, -, rfl⟩
    have h := mem_centralizer_singleton_iff.1 c.2
    exact mul_inv_eq_iff_eq_mul.2 h.symm
  have hfixed : ∀ g, tt * ξ g * tt⁻¹ = ξ g → ψ g = g := fun g h =>
    hξ ((hψ g).symm.trans h)
  have hsplit : ∀ g : A6 × A6, ψ g = g → ψ (g.1, 1) = (g.1, 1) ∧ ψ (1, g.2) = (1, g.2) := by
    intro g hg
    have hmul : ψ g = ψ (g.1, 1) * ψ (1, g.2) := by
      have hg' : ((g.1, 1) * (1, g.2) : A6 × A6) = g := Prod.ext (by simp) (by simp)
      rw [← map_mul, hg']
    rw [hmul] at hg
    have e1 : (ψ (g.1, 1)).1 = g.1 := by
      have := congrArg Prod.fst hg
      simpa [Prod.fst_mul, hP2 g.2] using this
    have e2 : (ψ (1, g.2)).2 = g.2 := by
      have := congrArg Prod.snd hg
      simpa [Prod.snd_mul, hP1 g.1] using this
    exact ⟨Prod.ext e1 (hP1 g.1), Prod.ext (hP2 g.2) e2⟩
  have hψa : ∀ a : A6, ψ (a, 1) = (a, 1) := by
    intro a
    obtain ⟨g, hg, hga⟩ := hA a
    subst hga
    exact (hsplit g (hfixed g (hLc _ hg))).1
  have hψb : ∀ b : A6, ψ (1, b) = (1, b) := by
    intro b
    obtain ⟨g, hg, hgb⟩ := hB b
    subst hgb
    exact (hsplit g (hfixed g (hLc _ hg))).2
  have hψall : ∀ g : A6 × A6, ψ g = g := by
    intro g
    have hmul : g = (g.1, 1) * (1, g.2) := Prod.ext (by simp) (by simp)
    conv_lhs => rw [hmul, map_mul, hψa, hψb]
    exact hmul.symm
  have hrange : ξ.range ≤ centralizer ({tt} : Set X) := by
    rintro _ ⟨g, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := hψ g
    rw [hψall g] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  have hc1 : Nat.card ξ.range = 360 * 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hξ).toEquiv, Nat.card_prod, card_alt6]
  have hc2 : Nat.card ↥(centralizer ({tt} : Set X)) = 2 * 1440 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
  have := Subgroup.card_le_of_le hrange
  rw [hc1, hc2] at this
  omega

end Embedded

theorem swap_factors {X : Type} [Group X] [Finite X] {tt : X} (htt : orderOf tt = 2)
    (e : ↥(centralizer ({tt} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    (N : Subgroup X) [N.Normal] (hNdef : N = normalClosureOf (centralizerDerived tt))
    (φ : ↥N ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (x : ↥N) (hx : (φ x).2 = 1) (hx' : tt * (x : X) * tt⁻¹ ∈ N) :
    (φ ⟨tt * (x : X) * tt⁻¹, hx'⟩).1 = 1 := by
  have := isSimple_alt6
  let ψ : A6 × A6 ≃* A6 × A6 := (φ.symm.trans (MulAut.conjNormal tt : N ≃* N)).trans φ
  let ξ : A6 × A6 →* X := N.subtype.comp φ.symm.toMonoidHom
  have hξ : Function.Injective ξ := Subtype.val_injective.comp φ.symm.injective
  have hψ : ∀ g, (φ.symm (ψ g) : X) = tt * (φ.symm g : X) * tt⁻¹ := by
    intro g
    show ((φ.symm (φ ((MulAut.conjNormal tt : MulAut N) (φ.symm g))) : N) : X) = _
    rw [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply]
  have hψξ : ∀ g, tt * ξ g * tt⁻¹ = ξ (ψ g) := fun g => (hψ g).symm
  have key : φ ⟨tt * (x : X) * tt⁻¹, hx'⟩ = ψ (φ x) := by
    apply φ.symm.injective
    apply Subtype.ext
    rw [hψ, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  obtain ⟨a, ha⟩ : ∃ a : A6, φ x = (a, 1) := ⟨(φ x).1, Prod.ext rfl hx⟩
  rw [key, ha]
  rcases sft_aut_prod_cases ψ with ⟨hP1, hP2⟩ | ⟨hS1, hS2⟩
  swap
  · exact hS1 a
  exfalso
  have hLN : centralizerDerived tt ≤ N := by
    rw [hNdef]
    exact Subgroup.subset_normalClosure
  have hLr : ∀ l ∈ centralizerDerived tt, ∃ g, ξ g = l := by
    intro l hl
    refine ⟨φ ⟨l, hLN hl⟩, ?_⟩
    show ((φ.symm (φ ⟨l, hLN hl⟩) : N) : X) = l
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨f⟩ := lhat_equiv e
  let θ : ↥((centralizerDerived tt).comap ξ) →* ↥(centralizerDerived tt) :=
    ξ.subgroupComap (centralizerDerived tt)
  have hθ : Function.Bijective θ := by
    refine ⟨fun a b h => ?_, fun l => ?_⟩
    · apply Subtype.ext
      have h0 := Subtype.ext_iff.1 h
      have h' : ξ (a : A6 × A6) = ξ (b : A6 × A6) := h0
      exact hξ h'
    · obtain ⟨g, hg⟩ := hLr l l.2
      refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
      show ξ g ∈ centralizerDerived tt
      rw [hg]
      exact l.2
  let ι : ↥((centralizerDerived tt).comap ξ) ≃* A6 := (MulEquiv.ofBijective θ hθ).trans f
  have : IsSimpleGroup ↥((centralizerDerived tt).comap ξ) := ι.isSimpleGroup
  have hcard : Nat.card ↥((centralizerDerived tt).comap ξ) = 360 := by
    rw [Nat.card_congr ι.toEquiv, card_alt6]
  rcases sft_proj_cases _ hcard with h1 | h2 | ⟨hA, hB⟩
  · exact sft_aux_first htt e ξ hξ ψ hψξ hP1 hLr (fun g hg => h1 g hg)
  ·
    let sw : A6 × A6 ≃* A6 × A6 := MulEquiv.prodComm
    refine sft_aux_first htt e (ξ.comp sw.toMonoidHom) (hξ.comp sw.injective)
      (sw.trans (ψ.trans sw)) (fun g => hψξ (sw g)) (fun a => hP2 a) ?_ ?_
    · intro l hl
      obtain ⟨g, hg⟩ := hLr l hl
      exact ⟨sw g, hg⟩
    · intro g hg
      exact h2 (sw g) hg
  · exact sft_aux_count e ξ hξ ψ hψξ hP1 hP2 (fun a => by
      obtain ⟨g, hg, hga⟩ := hA a
      exact ⟨g, hg, hga⟩) (fun b => by
      obtain ⟨g, hg, hgb⟩ := hB b
      exact ⟨g, hg, hgb⟩)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
