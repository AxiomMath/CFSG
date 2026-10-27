module

public import CFSG.GH74.GLS.C3.Prop121.CentralQuot
public import CFSG.GH74.GLS.C3.Prop121.Alt8Coset
public import CFSG.GH74.GLS.C3.Layer3.A8Cover
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm

section Abstract

variable {M : Type} [Group M]

theorem hom_alt7_trivial {N : Subgroup M} (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    {K₀ : Subgroup M} (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 7)) (δ : ↥K₀ →* M)
    (hδ : ∀ k, δ k ∈ N) : ∀ k, δ k = 1 := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥K₀ := eK₀.isSimpleGroup
  have hn : δ.ker.Normal := MonoidHom.normal_ker δ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal δ.ker with h | h
  · exfalso
    have hinj : Function.Injective δ := (MonoidHom.ker_eq_bot_iff δ).mp h
    have hcomm : ∀ a b : ↥K₀, a * b = b * a := by
      intro a b
      apply hinj
      rw [map_mul, map_mul]
      exact hN _ (hδ a) _ (hδ b)
    let a1 : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.2 (by decide)⟩
    let a2 : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 1 3, mem_alternatingGroup.2 (by decide)⟩
    have h1 : eK₀.symm a1 * eK₀.symm a2 = eK₀.symm a2 * eK₀.symm a1 := hcomm _ _
    rw [← map_mul, ← map_mul] at h1
    have h2 := eK₀.symm.injective h1
    have h3 := congrArg Subtype.val h2
    revert h3
    decide
  · intro k
    have : k ∈ δ.ker := by rw [h]; exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.1 this

theorem card_mulAut_alt7 : Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_perm]
  simp [Nat.factorial]

variable [Finite M]

theorem not_normal_alt7 {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m)
    (hNn : (zpowers t₀).Normal) {K₀ : Subgroup M} (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 7))
    (hcent : ∀ r : M, (∀ k ∈ K₀, r * k = k * r) → r ∈ zpowers t₀)
    (hcard : Nat.card (M ⧸ zpowers t₀) = 20160)
    (eH : ↥(K₀.map (QuotientGroup.mk' (zpowers t₀))) ≃* alternatingGroup (Fin 7)) :
    ¬ (K₀.map (QuotientGroup.mk' (zpowers t₀))).Normal := by
  intro hHn
  have hcen : ∀ d ∈ zpowers t₀, ∀ m : M, m * d * m⁻¹ = d := by
    intro d hd m
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hd
    have : Commute m t₀ := hc m
    rw [(this.zpow_right i).eq]; group
  have hcomm : ∀ a ∈ zpowers t₀, ∀ b ∈ zpowers t₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self t₀ i j).eq
  let H : Subgroup (M ⧸ zpowers t₀) := K₀.map (QuotientGroup.mk' (zpowers t₀))
  let φ : (M ⧸ zpowers t₀) →* MulAut ↥H := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    have hxk : ∀ k ∈ K₀, x * k * x⁻¹ * k⁻¹ ∈ zpowers t₀ := by
      intro k hk
      rw [← QuotientGroup.eq_one_iff]
      have h1 : φ (x : M ⧸ zpowers t₀) ⟨(k : M ⧸ zpowers t₀), ⟨k, hk, rfl⟩⟩ =
          ⟨(k : M ⧸ zpowers t₀), ⟨k, hk, rfl⟩⟩ := by rw [hxb]; rfl
      have h2 := congrArg Subtype.val h1
      have h3 : (x : M ⧸ zpowers t₀) * (k : M ⧸ zpowers t₀) * (x : M ⧸ zpowers t₀)⁻¹ =
          (k : M ⧸ zpowers t₀) := h2
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact mul_inv_eq_one.2 h3
    let δ : ↥K₀ →* M := MonoidHom.mk' (fun k => x * (k : M) * x⁻¹ * (k : M)⁻¹) (by
      intro a b
      have hb := hxk b b.2
      have e : x * ((a * b : K₀) : M) * x⁻¹ * ((a * b : K₀) : M)⁻¹ =
          (x * (a : M) * x⁻¹ * (a : M)⁻¹) *
            ((a : M) * (x * (b : M) * x⁻¹ * (b : M)⁻¹) * (a : M)⁻¹) := by
        simp only [Subgroup.coe_mul]; group
      rw [e, hcen _ hb (a : M)])
    have hδ := hom_alt7_trivial hcomm eK₀ δ (fun k => hxk k k.2)
    have hx : x ∈ zpowers t₀ := by
      apply hcent
      intro k hk
      have h1 := hδ ⟨k, hk⟩
      change x * k * x⁻¹ * k⁻¹ = 1 at h1
      calc x * k = (x * k * x⁻¹ * k⁻¹) * k * x := by group
        _ = k * x := by rw [h1]; group
    exact (QuotientGroup.eq_one_iff x).2 hx
  have hle : Nat.card (M ⧸ zpowers t₀) ≤ Nat.card (MulAut ↥H) :=
    Nat.card_le_card_of_injective φ hφ
  have h5 : Nat.card (MulAut ↥H) = 5040 := by
    rw [Nat.card_congr (MulAut.congr eH).toEquiv, card_mulAut_alt7]
  omega

theorem exists_hom_alt8 {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m) (ht₃ : t₀ ^ 3 = 1) (ht₁ : t₀ ≠ 1)
    (hcard : Nat.card M = 60480) {K₀ : Subgroup M} (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 7))
    (hKN : ∀ k ∈ K₀, k ∈ zpowers t₀ → k = 1)
    (hcent : ∀ r : M, (∀ k ∈ K₀, r * k = k * r) → r ∈ zpowers t₀) :
    ∃ η : M →* alternatingGroup (Fin 8), Function.Surjective η ∧ η.ker = zpowers t₀ := by
  classical
  have hNn : (zpowers t₀).Normal := zpowers_normal_of_central hc
  have hN3 : Nat.card ↥(zpowers t₀) = 3 := card_zpowers_three ht₃ ht₁
  have hXcard : Nat.card (M ⧸ zpowers t₀) = 20160 := by
    have h1 := (zpowers t₀).card_mul_index
    rw [hN3, hcard, Subgroup.index_eq_card] at h1
    omega
  obtain ⟨eKb⟩ := map_equiv_of_inf_zpowers_eq_bot (zpowers t₀) hKN
  have eH : ↥(K₀.map (QuotientGroup.mk' (zpowers t₀))) ≃* alternatingGroup (Fin 7) :=
    eKb.symm.trans eK₀
  have hnorm := not_normal_alt7 hc hNn eK₀ hcent hXcard eH
  obtain ⟨eX⟩ := nonempty_mulEquiv_alt8_of_card_of_alt7 hXcard _ ⟨eH⟩ hnorm
  refine ⟨eX.toMonoidHom.comp (QuotientGroup.mk' (zpowers t₀)), ?_, ?_⟩
  · exact eX.surjective.comp (QuotientGroup.mk'_surjective (zpowers t₀))
  · ext m
    rw [MonoidHom.mem_ker]
    show eX (QuotientGroup.mk' (zpowers t₀) m) = 1 ↔ m ∈ zpowers t₀
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff m

theorem exists_complement_alt8 {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m) (ht₃ : t₀ ^ 3 = 1)
    (ht₁ : t₀ ≠ 1) (hcard : Nat.card M = 60480) {K₀ : Subgroup M}
    (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 7)) (hKN : ∀ k ∈ K₀, k ∈ zpowers t₀ → k = 1)
    (hcent : ∀ r : M, (∀ k ∈ K₀, r * k = k * r) → r ∈ zpowers t₀) :
    ∃ L : Subgroup M, L ⊓ zpowers t₀ = ⊥ ∧ L ⊔ zpowers t₀ = ⊤ ∧
      Nonempty (↥L ≃* alternatingGroup (Fin 8)) := by
  classical
  obtain ⟨η, hsurj, hker⟩ := exists_hom_alt8 hc ht₃ ht₁ hcard eK₀ hKN hcent
  have hkerc : η.ker ≤ Subgroup.center M := by
    rw [hker]
    intro m hm
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hm
    rw [Subgroup.mem_center_iff]
    intro m'
    exact ((show Commute m' t₀ from hc m').zpow_right i).eq
  have hk3 : IsPGroup 3 ↥η.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 1) (by rw [card_zpowers_three ht₃ ht₁]; norm_num)
  obtain ⟨L₀, hL0inf, hL0sup, hL0⟩ :=
    CFSG.GH74.GLS.Layer3.exists_complement_of_central_three_alt8 η hsurj hkerc hk3
  rw [hker] at hL0inf hL0sup
  exact ⟨L₀, hL0inf, hL0sup, hL0⟩

end Abstract

end CFSG.GH74.GLS.C3.Prop121
