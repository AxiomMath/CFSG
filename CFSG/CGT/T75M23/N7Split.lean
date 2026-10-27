module

public import CFSG.CGT.T75JM.N6Cert
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.CGT.T75M23

open CFSG.CGT.T75JM Equiv

@[expose] noncomputable def permEmb : Perm (Fin 6) →* Perm (Fin 7) :=
  Equiv.Perm.extendDomainHom (finSuccAboveEquiv (Fin.last 6))

theorem permEmb_injective : Function.Injective permEmb :=
  Equiv.Perm.extendDomainHom_injective _

theorem sign_permEmb (σ : Perm (Fin 6)) : Perm.sign (permEmb σ) = Perm.sign σ :=
  Equiv.Perm.sign_extendDomain σ _

@[expose] noncomputable def altEmb : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) :=
  (permEmb.comp (alternatingGroup (Fin 6)).subtype).codRestrict (alternatingGroup (Fin 7))
    fun σ => by
      rw [Equiv.Perm.mem_alternatingGroup]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [sign_permEmb]
      exact Equiv.Perm.mem_alternatingGroup.1 σ.2

theorem altEmb_injective : Function.Injective altEmb := by
  intro a b h
  apply Subtype.ext
  apply permEmb_injective
  exact congrArg Subtype.val h

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := card_a6

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem index_range_altEmb : (altEmb.range).index = 7 := by
  have h1 := (altEmb.range).index_mul_card
  have h2 : Nat.card altEmb.range = 360 := by
    rw [← card_alt6]
    exact (Nat.card_congr (MonoidHom.ofInjective altEmb_injective).toEquiv).symm
  rw [h2, card_alt7] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (h1.trans (by norm_num))

section NQ

variable {G : Type*} [Group G]

@[expose] noncomputable def normalizerTopEquiv (T : Subgroup G) [T.Normal] :
    ↥(Subgroup.normalizer (T : Set G)) ≃* G :=
  MulEquiv.ofBijective (Subgroup.normalizer (T : Set G)).subtype
    ⟨Subtype.coe_injective, fun g => ⟨⟨g, by
      rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact Subgroup.mem_top g⟩, rfl⟩⟩

@[simp] theorem normalizerTopEquiv_apply (T : Subgroup G) [T.Normal]
    (g : Subgroup.normalizer (T : Set G)) : normalizerTopEquiv T g = (g : G) :=
  rfl

@[expose] noncomputable def nqEquivOfNormal (T : Subgroup G) [T.Normal] : NQ T ≃* G ⧸ T :=
  QuotientGroup.congr (T.subgroupOf (Subgroup.normalizer (T : Set G))) T (normalizerTopEquiv T) (by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      exact ⟨⟨g, Subgroup.le_normalizer hg⟩, hg, rfl⟩)

end NQ

open CFSG.CosetTable

theorem exists_complement_of_hom {G₁ : Type*} [Group G₁]
    {T₁ : Subgroup G₁} [T₁.Normal] (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₁, a * b = b * a)
    (hsq : ∀ a ∈ T₁, a ^ 2 = 1) (h16 : Nat.card T₁ = 16)
    (hC : Subgroup.centralizer (T₁ : Set G₁) = T₁)
    (ρ : G₁ →* alternatingGroup (Fin 6)) (hρ : Function.Surjective ρ) (hker : ρ.ker = T₁) :
    ∃ K : Subgroup G₁, T₁ ⊓ K = ⊥ ∧ T₁ ⊔ K = ⊤ := by
  classical
  let φ : NQ T₁ ≃* alternatingGroup (Fin 6) :=
    (nqEquivOfNormal T₁).trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ))
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_normalizer_of_certificate hcomm hsq h16 hC φ
  obtain ⟨f1, c1⟩ := Certificates.certificate14984.2.2.2
  obtain ⟨hA0fin, hA0card⟩ := card_genSub_le rels6 (subsetOf 6 [0, 1])
  set A0 := genSub {r : FreeGroup (Fin 6) | r ∈ rels6.map FreeGroup.mk} (subsetOf 6 [0, 1])
    with hA0
  have hA0le : Nat.card A0 ≤ 360 := hA0card.trans c1
  let f : PG 6 rels6 →* G₁ := (Subgroup.normalizer (T₁ : Set G₁)).subtype.comp Ψ.toMonoidHom
  have hfsurj : Function.Surjective f := by
    intro g
    have hg : g ∈ Subgroup.normalizer (T₁ : Set G₁) := by
      rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact Subgroup.mem_top g
    obtain ⟨w, hw⟩ := Ψ.surjective ⟨g, hg⟩
    exact ⟨w, by simp [f, hw]⟩
  have hft : ∀ j : Fin 4, f (tGen j) ∈ T₁ := by
    intro j
    have : Ψ (tGen j) ∈ T₁.subgroupOf (Subgroup.normalizer (T₁ : Set G₁)) := by
      rw [← hΨ]
      exact ⟨tGen j, Subgroup.subset_closure ⟨j, rfl⟩, rfl⟩
    exact this
  set ρ' : PG 6 rels6 →* alternatingGroup (Fin 6) := ρ.comp f with hρ'
  have hρ'surj : Function.Surjective ρ' := hρ.comp hfsurj
  have hρ'one : ∀ i : Fin 6, 2 ≤ i.val → ρ' (PresentedGroup.of i) = 1 := by
    intro i hi
    have hi' : PresentedGroup.of i = tGen ⟨i.val - 2, by omega⟩ := by
      simp only [tGen]
      congr 2
      ext
      simp
      omega
    rw [hi']
    have := hft ⟨i.val - 2, by omega⟩
    rw [← hker] at this
    exact this
  have hmapA0 : A0.map ρ' = ⊤ := by
    rw [eq_top_iff]
    intro a ha
    obtain ⟨w, rfl⟩ := hρ'surj a
    clear ha
    have hw : w ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin 6 → PG 6 rels6)) := by
      rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top w
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      by_cases hi : 2 ≤ i.val
      · rw [hρ'one i hi]; exact (A0.map ρ').one_mem
      · refine ⟨PresentedGroup.of i, Subgroup.subset_closure ⟨i, ?_, rfl⟩, rfl⟩
        simp only [Set.mem_ofPred_eq, subsetOf, List.mem_filter, List.mem_finRange, true_and]
        simp only [List.contains_eq_any_beq]
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with h | h <;> simp [h]
    | one => rw [map_one]; exact (A0.map ρ').one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact (A0.map ρ').mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact (A0.map ρ').inv_mem hx
  set K : Subgroup G₁ := A0.map f with hK
  have hA0fin' : Finite A0 := hA0fin
  let g0 : A0 → K := fun a => ⟨f a, a, a.2, rfl⟩
  have hg0 : Function.Surjective g0 := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hKfin : Finite K := Finite.of_surjective g0 hg0
  have hKcard : Nat.card K ≤ 360 :=
    (Nat.card_le_card_of_surjective g0 hg0).trans hA0le
  have hρK : Function.Surjective (fun k : K => ρ (k : G₁)) := by
    intro a
    have : a ∈ A0.map ρ' := by rw [hmapA0]; exact Subgroup.mem_top a
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨⟨f w, w, hw, rfl⟩, rfl⟩
  have hKbij : Function.Bijective (fun k : K => ρ (k : G₁)) :=
    hρK.bijective_of_nat_card_le (by rw [card_alt6]; exact hKcard)
  refine ⟨K, ?_, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxT, hxK⟩
    have h1 : ρ x = 1 := by
      rw [← MonoidHom.mem_ker, hker]; exact hxT
    have : (⟨x, hxK⟩ : K) = 1 := hKbij.1 (by simp [h1])
    exact congrArg Subtype.val this
  · rw [eq_top_iff]
    intro g _
    obtain ⟨k, hk⟩ := hρK (ρ g)
    have hmem : (k : G₁)⁻¹ * g ∈ T₁ := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
      have : ρ k = ρ g := hk
      rw [this, inv_mul_cancel]
    have hg : g = (k : G₁) * ((k : G₁)⁻¹ * g) := by group
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right k.2) (Subgroup.mem_sup_left hmem)

theorem exists_complement_normalizer7 {G : Type*} [Group G]
    {T : Subgroup G} (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hsq : ∀ a ∈ T, a ^ 2 = 1)
    (h16 : Nat.card T = 16) (hC : Subgroup.centralizer (T : Set G) = T)
    (φ : NQ T ≃* alternatingGroup (Fin 7)) :
    ∃ D : Subgroup (Subgroup.normalizer (T : Set G)),
      T.subgroupOf (Subgroup.normalizer (T : Set G)) ⊓ D = ⊥ ∧
        T.subgroupOf (Subgroup.normalizer (T : Set G)) ⊔ D = ⊤ := by
  classical
  set N := Subgroup.normalizer (T : Set G) with hN
  set Tn : Subgroup ↥N := T.subgroupOf N with hTn
  let π : ↥N →* alternatingGroup (Fin 7) := φ.toMonoidHom.comp (QuotientGroup.mk' Tn)
  have hπsurj : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective Tn)
  have hπker : π.ker = Tn := by
    ext x
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk x) = 1 ↔ x ∈ Tn
    rw [map_eq_one_iff _ φ.injective, QuotientGroup.eq_one_iff]
  have hTn16 : Nat.card Tn = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv).trans h16
  have hcommTn : IsMulCommutative Tn := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hcomm _ a.2 _ b.2))⟩⟩
  have hfinN : Finite ↥N := by
    have hq : Nat.card (NQ T) = 2520 := (Nat.card_congr φ.toEquiv).trans card_alt7
    have hcardN : Nat.card ↥N = 16 * 2520 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Tn, hq, hTn16]
    exact Nat.finite_of_card_ne_zero (by rw [hcardN]; norm_num)
  set S := altEmb.range with hS
  set N1 : Subgroup ↥N := S.comap π with hN1
  have hTn_le : Tn ≤ N1 := by
    intro x hx
    rw [← hπker] at hx
    show π x ∈ S
    rw [MonoidHom.mem_ker.1 hx]
    exact S.one_mem
  have hindex : N1.index = 7 := by
    rw [hN1, Subgroup.index_comap_of_surjective S hπsurj]
    exact index_range_altEmb
  let ρ : ↥N1 →* alternatingGroup (Fin 6) :=
    (MonoidHom.ofInjective altEmb_injective).symm.toMonoidHom.comp
      ((π.comp N1.subtype).codRestrict S (fun x => x.2))
  have hρeq : ∀ x : ↥N1, altEmb (ρ x) = π (x : ↥N) := by
    intro x
    have := (MonoidHom.ofInjective altEmb_injective).apply_symm_apply
      ((π.comp N1.subtype).codRestrict S (fun x => x.2) x)
    exact congrArg Subtype.val this
  have hρsurj : Function.Surjective ρ := by
    intro a
    obtain ⟨n, hn⟩ := hπsurj (altEmb a)
    have hn1 : n ∈ N1 := by
      show π n ∈ S
      rw [hn]; exact ⟨a, rfl⟩
    refine ⟨⟨n, hn1⟩, altEmb_injective ?_⟩
    rw [hρeq]; exact hn
  have hρker : ρ.ker = Tn.subgroupOf N1 := by
    ext x
    rw [MonoidHom.mem_ker]
    show ρ x = 1 ↔ (x : ↥N) ∈ Tn
    rw [← hπker, MonoidHom.mem_ker, ← hρeq x]
    constructor
    · intro h; rw [h, map_one]
    · intro h; exact altEmb_injective (by rw [h, map_one])
  have hcentr : Subgroup.centralizer ((Tn.subgroupOf N1 : Subgroup ↥N1) : Set ↥N1) =
      Tn.subgroupOf N1 := by
    apply le_antisymm
    · intro x hx
      have hxG : ((x : ↥N) : G) ∈ Subgroup.centralizer (T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have hy : (⟨⟨t, Subgroup.le_normalizer ht⟩, hTn_le ht⟩ : ↥N1) ∈ Tn.subgroupOf N1 := ht
        have := Subgroup.mem_centralizer_iff.1 hx _ hy
        have h2 := congrArg (fun z : ↥N1 => ((z : ↥N) : G)) this
        exact h2
      rw [hC] at hxG
      exact hxG
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subtype.ext (hcomm _ hy _ hx))
  obtain ⟨K₁, hK₁⟩ := exists_complement_of_hom (T₁ := Tn.subgroupOf N1)
    (fun a ha b hb => Subtype.ext (Subtype.ext (hcomm _ ha _ hb)))
    (fun a ha => Subtype.ext (Subtype.ext (by simpa [pow_two] using hsq _ ha)))
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTn_le).toEquiv, hTn16])
    hcentr ρ hρsurj hρker
  obtain ⟨hK₁inf, hK₁sup⟩ := hK₁
  set K : Subgroup ↥N := K₁.map N1.subtype with hK
  have hNK : Tn ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxT, y, hy, rfl⟩
    have hyT : y ∈ Tn.subgroupOf N1 := hxT
    have : y ∈ Tn.subgroupOf N1 ⊓ K₁ := ⟨hyT, hy⟩
    rw [hK₁inf] at this
    have hy1 : y = 1 := Subgroup.mem_bot.1 this
    rw [hy1]; rfl
  have hsup : Tn ⊔ K = N1 := by
    apply le_antisymm
    · refine sup_le hTn_le ?_
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    · intro x hx
      have hxt : (⟨x, hx⟩ : ↥N1) ∈ Tn.subgroupOf N1 ⊔ K₁ := by
        rw [hK₁sup]; exact Subgroup.mem_top _
      obtain ⟨t, ht, k, hk, hmul⟩ := Subgroup.mem_sup_of_normal_left.1 hxt
      have hx' : x = (t : ↥N) * (k : ↥N) := by
        have := congrArg (fun z : ↥N1 => (z : ↥N)) hmul
        exact this.symm
      rw [hx']
      exact Subgroup.mul_mem_sup (show (t : ↥N) ∈ Tn from ht) ⟨k, hk, rfl⟩
  have hcop : Nat.Coprime N1.index (Nat.card Tn) := by
    rw [hindex, hTn16]; norm_num
  obtain ⟨D, -, hD1, hD2⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting Tn N1 K hcop hNK hsup
  exact ⟨D, hD1, hD2⟩

end CFSG.CGT.T75M23
