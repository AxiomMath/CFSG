module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

structure Ivk93Cfg2 {J : Type} [Group J] [Finite J] (x : J) (q₁ q₂ : ℕ) (L₁ L₂ : Subgroup J) :
    Prop where
  ord : orderOf x = 2
  odd₁ : Odd q₁
  odd₂ : Odd q₂
  five₁ : 5 ≤ q₁
  five₂ : 5 ≤ q₂
  ne : L₁ ≠ L₂
  comp₁ : IsPCompIn 2 (centralizer ({x} : Set J)) L₁
  comp₂ : IsPCompIn 2 (centralizer ({x} : Set J)) L₂
  mem₁ : x ∈ L₁
  mem₂ : x ∈ L₂
  sl₁ : HasSL2Model (↥L₁ ⧸ pPrimeCore 2 ↥L₁) (fun r => r = q₁)
  sl₂ : HasSL2Model (↥L₂ ⧸ pPrimeCore 2 ↥L₂) (fun r => r = q₂)

namespace Ivk93Cfg2

variable {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup J}

theorem mul_self_eq_one (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : x * x = 1 := by
  rw [← pow_two, ← h.ord]
  exact pow_orderOf_eq_one x

theorem ne_one (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : x ≠ 1 := by
  intro h1
  have := h.ord
  rw [h1, orderOf_one] at this
  omega

theorem le₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : L₁ ≤ centralizer ({x} : Set J) := h.comp₁.1

theorem le₂ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : L₂ ≤ centralizer ({x} : Set J) := h.comp₂.1

theorem symm (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : Ivk93Cfg2 x q₂ q₁ L₂ L₁ :=
  ⟨h.ord, h.odd₂, h.odd₁, h.five₂, h.five₁, h.ne.symm, h.comp₂, h.comp₁, h.mem₂, h.mem₁, h.sl₂,
    h.sl₁⟩

theorem perfect₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : Group.IsPerfect ↥L₁ := by
  have h1 := CatalogueBAlternating.pComponent_perfect h.comp₁.2
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h.le₁).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h.le₁).surjective

theorem card₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    Nat.card ↥L₁ = q₁ * (q₁ ^ 2 - 1) * Nat.card ↥(pPrimeCore 2 ↥L₁) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L₁), card_of_hasSL2Model h.sl₁]

theorem sl2_card_ge (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : 120 ≤ q₁ * (q₁ ^ 2 - 1) := by
  have := sl2_card_mono h.five₁
  norm_num at this
  omega

theorem sl2_card_ge₂ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : 120 ≤ q₂ * (q₂ ^ 2 - 1) := h.symm.sl2_card_ge

theorem card_ge₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : 120 ≤ Nat.card ↥L₁ := by
  rw [h.card₁]
  have h1 : 1 ≤ Nat.card ↥(pPrimeCore 2 ↥L₁) := Nat.card_pos
  have h2 := h.sl2_card_ge
  nlinarith

theorem nontrivial₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : Nontrivial ↥L₁ := by
  have h1 := h.card_ge₁
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have := Nat.card_of_subsingleton (1 : ↥L₁)
  omega

theorem not_solvable₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : ¬ Group.IsSolvable ↥L₁ := by
  have := h.perfect₁
  have := h.nontrivial₁
  exact Group.IsPerfect.not_isSolvable ↥L₁

theorem false_of_solvable (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂)
    (hs : Group.IsSolvable ↥(centralizer ({x} : Set J))) : False :=
  h.not_solvable₁ (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion h.le₁) (Subgroup.inclusion_injective h.le₁))

theorem false_of_card_cent_dvd (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {N : ℕ}
    (hC : Nat.card ↥(centralizer ({x} : Set J)) ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False := by
  have h1 : Nat.card ↥L₁ ∣ Nat.card ↥(centralizer ({x} : Set J)) := Subgroup.card_dvd_of_le h.le₁
  have h2 : q₁ * (q₁ ^ 2 - 1) ∣ Nat.card ↥L₁ := ⟨_, h.card₁⟩
  exact hN q₁ h.five₁ (h2.trans (h1.trans hC))

theorem false_of_card_group (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {N : ℕ} (hJ : Nat.card J ∣ N)
    (hN : ∀ q : ℕ, 5 ≤ q → ¬ q * (q ^ 2 - 1) ∣ N) : False := by
  have h1 : Nat.card ↥L₁ ∣ Nat.card J := Subgroup.card_subgroup_dvd_card _
  have h2 : q₁ * (q₁ ^ 2 - 1) ∣ Nat.card ↥L₁ := ⟨_, h.card₁⟩
  exact hN q₁ h.five₁ (h2.trans (h1.trans hJ))

theorem exists_nonabelian_two₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    ∃ P : Subgroup J, P ≤ L₁ ∧ IsPGroup 2 ↥P ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl₁
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact h.odd₁
  obtain ⟨Q, hQ, a, ha, b, hb, hab⟩ := sl2_exists_quaternion hodd
  obtain ⟨S', hQS'⟩ := (hQ.map e.toMonoidHom).exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L₁)) 2 S'
  have hSS' : (S : Subgroup ↥L₁).map (QuotientGroup.mk' (pPrimeCore 2 ↥L₁)) = (S' : Subgroup _) := by
    rw [← hS]
    rfl
  have hna : ∃ s ∈ (S : Subgroup ↥L₁), ∃ t ∈ (S : Subgroup ↥L₁), s * t ≠ t * s := by
    by_contra hcon
    have hcom : ∀ s ∈ (S : Subgroup ↥L₁), ∀ t ∈ (S : Subgroup ↥L₁), s * t = t * s :=
      fun s hs t ht => by
        by_contra hne
        exact hcon ⟨s, hs, t, ht, hne⟩
    apply hab
    have ha' : e a ∈ (S' : Subgroup _) := hQS' ⟨a, ha, rfl⟩
    have hb' : e b ∈ (S' : Subgroup _) := hQS' ⟨b, hb, rfl⟩
    rw [← hSS'] at ha' hb'
    obtain ⟨s, hs, hsa⟩ := ha'
    obtain ⟨t, ht, htb⟩ := hb'
    apply e.injective
    rw [map_mul, map_mul, ← hsa, ← htb]
    show QuotientGroup.mk' (pPrimeCore 2 ↥L₁) s * QuotientGroup.mk' (pPrimeCore 2 ↥L₁) t =
      QuotientGroup.mk' (pPrimeCore 2 ↥L₁) t * QuotientGroup.mk' (pPrimeCore 2 ↥L₁) s
    rw [← map_mul, ← map_mul, hcom s hs t ht]
  obtain ⟨s, hs, t, ht, hst⟩ := hna
  refine ⟨(S : Subgroup ↥L₁).map L₁.subtype, ?_, S.2.map _, (s : J), ⟨s, hs, rfl⟩, (t : J),
    ⟨t, ht, rfl⟩, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · intro hc
    exact hst (Subtype.ext hc)

theorem false_of_abelian_sylow (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) (hab : CFSG.Walter.HasAbelianSylowTwo J) :
    False := by
  obtain ⟨H, -, hH2, a, ha, b, hb, hab'⟩ := h.exists_nonabelian_two₁
  obtain ⟨P, hP⟩ := hH2.exists_le_sylow
  apply hab'
  have hc := (hab P).is_comm.comm
  exact hc ⟨a, hP ha⟩ ⟨b, hP hb⟩ |> congrArg Subtype.val

theorem commute_bar (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    ∀ a ∈ (L₁.subgroupOf (centralizer ({x} : Set J))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set J)))),
      ∀ b ∈ (L₂.subgroupOf (centralizer ({x} : Set J))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set J)))), a * b = b * a := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  refine commute_map_of_ne_pComponent h.comp₁.2 h.comp₂.2 ?_ hk hl
  intro heq
  apply h.ne
  have := Subgroup.subgroupOf_inj.mp heq
  rwa [inf_eq_left.mpr h.le₁, inf_eq_left.mpr h.le₂] at this

theorem card_bar₁ (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    Nat.card ↥((L₁.subgroupOf (centralizer ({x} : Set J))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set J))))) = q₁ * (q₁ ^ 2 - 1) := by
  obtain ⟨e, -⟩ := UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal h.le₁
    h.comp₁.2.choose_spec.2.1
  rw [← Nat.card_congr e.toEquiv, card_of_hasSL2Model h.sl₁]

theorem pair_card (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    (q₁ * (q₁ ^ 2 - 1)) * (q₂ * (q₂ ^ 2 - 1)) ≤ 2 * Nat.card ↥(centralizer ({x} : Set J)) := by
  set C := centralizer ({x} : Set J) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set A₁ := (L₁.subgroupOf C).map π with hA₁
  set A₂ := (L₂.subgroupOf C).map π with hA₂
  have hc := h.commute_bar
  have h1 : Nat.card ↥A₁ = q₁ * (q₁ ^ 2 - 1) := h.card_bar₁
  have h2 : Nat.card ↥A₂ = q₂ * (q₂ ^ 2 - 1) := h.symm.card_bar₁
  have hi : Nat.card ↥(A₁ ⊓ A₂) ≤ 2 := by
    obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl₁
    obtain ⟨e', -⟩ := UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal h.le₁
      h.comp₁.2.choose_spec.2.1
    have hodd : Odd (Nat.card F) := by rw [hFq]; exact h.odd₁
    have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
    let ψ : SL(2, F) ≃* ↥A₁ := e.trans e'
    refine le_trans (Nat.card_le_card_of_injective
      (fun u : ↥(A₁ ⊓ A₂) => (⟨ψ.symm ⟨(u : _ ⧸ _), u.2.1⟩, ?_⟩ : ↥(Subgroup.center SL(2, F)))) ?_)
      (le_of_eq (CFSG.RankThree.SubgroupLists.natCard_center_sl2 h2F))
    · rw [Subgroup.mem_center_iff]
      intro g
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact hc _ (ψ g).2 _ u.2.2
    · intro u v huv
      have := congrArg (fun w : ↥(Subgroup.center SL(2, F)) => ψ (w : SL(2, F))) huv
      simp only [MulEquiv.apply_symm_apply] at this
      exact Subtype.ext (Subtype.mk.inj this)
  have := card_mul_le_of_commute A₁ A₂ hc hi
  rw [h1, h2] at this
  have h3 : Nat.card (↥C ⧸ pPrimeCore 2 ↥C) ≤ Nat.card ↥C :=
    Nat.le_of_dvd Nat.card_pos ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥C)⟩
  nlinarith [h3]

theorem false_of_pair_card (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂)
    (hN : Nat.card ↥(centralizer ({x} : Set J)) < 7200) : False := by
  have h1 := h.pair_card
  have h2 := h.sl2_card_ge
  have h3 := h.sl2_card_ge₂
  nlinarith

theorem of_equiv {J' : Type} [Group J'] [Finite J'] (Φ : J ≃* J') (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) :
    Ivk93Cfg2 (Φ x) q₁ q₂ (L₁.map Φ.toMonoidHom) (L₂.map Φ.toMonoidHom) := by
  have hc := map_centralizer_singleton_equiv' Φ x
  have hsl : ∀ {L : Subgroup J} {q : ℕ}, HasSL2Model (↥L ⧸ pPrimeCore 2 ↥L) (fun r => r = q) →
      HasSL2Model (↥(L.map Φ.toMonoidHom) ⧸ pPrimeCore 2 ↥(L.map Φ.toMonoidHom))
        (fun r => r = q) := by
    intro L q hL
    obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hL
    exact ⟨F, hF, hFin, hq, ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)).symm.trans e⟩⟩
  refine ⟨?_, h.odd₁, h.odd₂, h.five₁, h.five₂, ?_, ?_, ?_, ⟨x, h.mem₁, rfl⟩, ⟨x, h.mem₂, rfl⟩,
    hsl h.sl₁, hsl h.sl₂⟩
  · rw [MulEquiv.orderOf_eq]
    exact h.ord
  · intro heq
    exact h.ne (Subgroup.map_injective Φ.injective heq)
  · rw [← hc]
    exact ⟨Subgroup.map_mono h.le₁, (isPComponent_subgroupOf_map_iff' Φ h.le₁).1 h.comp₁.2⟩
  · rw [← hc]
    exact ⟨Subgroup.map_mono h.le₂, (isPComponent_subgroupOf_map_iff' Φ h.le₂).1 h.comp₂.2⟩

end Ivk93Cfg2

end CFSG.GH74.GLS.IVK.Proofs2
