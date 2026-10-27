module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.NoFixedVectors
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G]

section TwoPart

@[expose] def productSubgroup (S H : Subgroup G) (hSH : S ≤ Subgroup.normalizer (H : Set G)) :
    Subgroup G where
  carrier := {g | ∃ s ∈ S, s⁻¹ * g ∈ H}
  one_mem' := ⟨1, S.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have h1 : t⁻¹ * (s⁻¹ * a) * t ∈ H :=
      conj_mem_of_mem_normalizer (hSH ht) ha
    have : (s * t)⁻¹ * (a * b) = (t⁻¹ * (s⁻¹ * a) * t) * (t⁻¹ * b) := by group
    rw [this]
    exact H.mul_mem h1 hb
  inv_mem' := by
    rintro a ⟨s, hs, ha⟩
    refine ⟨s⁻¹, S.inv_mem hs, ?_⟩
    have h1 : s * (s⁻¹ * a)⁻¹ * s⁻¹ ∈ H :=
      conj_mem_of_mem_normalizer' (hSH hs) (H.inv_mem ha)
    have : s⁻¹⁻¹ * a⁻¹ = s * (s⁻¹ * a)⁻¹ * s⁻¹ := by group
    rw [this]
    exact h1

theorem le_productSubgroup (S H : Subgroup G) (hSH : S ≤ Subgroup.normalizer (H : Set G)) :
    H ⊔ S ≤ productSubgroup S H hSH := by
  refine sup_le (fun h hh => ⟨1, S.one_mem, by simpa using hh⟩) (fun s hs => ⟨s, hs, ?_⟩)
  simp

theorem twoPart_conj_of_mul [Finite G] (S : Sylow 2 G) (H : Subgroup G)
    (hHodd : Odd (Nat.card H)) (hSH : (S : Subgroup G) ≤ Subgroup.normalizer (H : Set G))
    {x h π r : G} {e : ℕ} (hx : x ∈ (S : Subgroup G)) (hh : h ∈ H)
    (hπz : π ∈ Subgroup.zpowers (x * h)) (hrz : r ∈ Subgroup.zpowers (x * h))
    (hfac : π * r = x * h) (hπ : orderOf π ∣ 2 ^ e) (hr : Nat.Coprime 2 (orderOf r)) :
    ∃ c ∈ H, c * π * c⁻¹ = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sg := (S : Subgroup G) with hSg
  set L := H ⊔ Sg with hL
  have hHL : H ≤ L := le_sup_left
  have hSL : Sg ≤ L := le_sup_right
  have hLN : L ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer hSH
  have hSHbot : Sg ⊓ H = ⊥ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp S.isPGroup'
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hHodd)
  have hSHmem : ∀ y ∈ Sg, y ∈ H → y = 1 := by
    intro y hyS hyH
    have : y ∈ Sg ⊓ H := ⟨hyS, hyH⟩
    rw [hSHbot] at this
    exact this
  have hdecomp : ∀ l ∈ L, ∃ s ∈ Sg, s⁻¹ * l ∈ H := fun l hl => le_productSubgroup Sg H hSH hl
  set H' := H.subgroupOf L with hH'
  have hH'normal : H'.Normal := by
    constructor
    intro a ha l
    rw [hH', Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hLN l.property) a).mp ha
  set S' := Sg.subgroupOf L with hS'
  have hS'p : IsPGroup 2 S' :=
    S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' H').comp S'.subtype) := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective H' q
    obtain ⟨s, hs, hsl⟩ := hdecomp l l.property
    refine ⟨⟨⟨s, hSL hs⟩, by rw [hS', Subgroup.mem_subgroupOf]; exact hs⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, hH', Subgroup.mem_subgroupOf]
    exact hsl
  have hinj : Function.Injective ((QuotientGroup.mk' H').comp S'.subtype) := by
    intro a b hab
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply] at hab
    rw [QuotientGroup.eq, hH', Subgroup.mem_subgroupOf] at hab
    have haS : ((a : L) : G) ∈ Sg := Subgroup.mem_subgroupOf.mp a.property
    have hbS : ((b : L) : G) ∈ Sg := Subgroup.mem_subgroupOf.mp b.property
    have h1 := hSHmem _ (Sg.mul_mem (Sg.inv_mem haS) hbS) (by simpa using hab)
    apply Subtype.ext
    apply Subtype.ext
    rw [inv_mul_eq_one] at h1
    exact h1
  have hquot : IsPGroup 2 (L ⧸ H') := hS'p.of_surjective _ hsurj
  have hxh : x * h ∈ L := L.mul_mem (hSL hx) (hHL hh)
  have hzL : Subgroup.zpowers (x * h) ≤ L := (Subgroup.zpowers_le).mpr hxh
  have hπL : π ∈ L := hzL hπz
  have hrL : r ∈ L := hzL hrz
  have hrH : r ∈ H := by
    have hmem := mem_of_coprime_of_normal_complement H' hquot ⟨r, hrL⟩
      (by rw [Subgroup.orderOf_mk]; exact hr)
    rw [hH', Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hxπ : x⁻¹ * π ∈ H := by
    have heq : x⁻¹ * π = h * r⁻¹ := by
      calc x⁻¹ * π = x⁻¹ * (π * r) * r⁻¹ := by group
        _ = x⁻¹ * (x * h) * r⁻¹ := by rw [hfac]
        _ = h * r⁻¹ := by group
    rw [heq]
    exact H.mul_mem hh (H.inv_mem hrH)
  have hcardL : Nat.card L = Nat.card S' * Nat.card H' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H',
      ← Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩]
  have hindex : ¬ 2 ∣ S'.index := by
    have h1 := Subgroup.card_mul_index S'
    rw [hcardL] at h1
    have h2 : S'.index = Nat.card H' := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h2, hH', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hHodd)
  set π' : L := ⟨π, hπL⟩ with hπ'
  have hπp : IsPGroup 2 (Subgroup.zpowers π') := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hπ
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, hπ', Subgroup.orderOf_mk, hk]
  obtain ⟨P, hP⟩ := hπp.exists_le_sylow
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L P (hS'p.toSylow hindex)
  have hlπ : l * π' * l⁻¹ ∈ S' := by
    have hmem : π' ∈ (P : Subgroup L) := hP (Subgroup.mem_zpowers π')
    have h1 : l * π' * l⁻¹ ∈ ((l • P : Sylow 2 L) : Subgroup L) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨π', hmem, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hl, IsPGroup.toSylow_coe] at h1
    exact h1
  obtain ⟨s, hs, hsl⟩ := hdecomp (l : G) l.property
  refine ⟨s⁻¹ * l, hsl, ?_⟩
  have hlπG : (l : G) * π * (l : G)⁻¹ ∈ Sg := by
    have := Subgroup.mem_subgroupOf.mp hlπ
    simpa using this
  have hyS : (s⁻¹ * l) * π * (s⁻¹ * l)⁻¹ ∈ Sg := by
    have heq : (s⁻¹ * l) * π * (s⁻¹ * l)⁻¹ = s⁻¹ * ((l : G) * π * (l : G)⁻¹) * s := by group
    rw [heq]
    exact Sg.mul_mem (Sg.mul_mem (Sg.inv_mem hs) hlπG) hs
  have hxyH : x⁻¹ * ((s⁻¹ * l) * π * (s⁻¹ * l)⁻¹) ∈ H := by
    have hc : s⁻¹ * (l : G) ∈ H := hsl
    have hπc : π⁻¹ * (s⁻¹ * l) * π ∈ H := by
      have := conj_mem_of_mem_normalizer (hLN hπL) hc
      simpa [mul_assoc] using this
    have heq : x⁻¹ * ((s⁻¹ * l) * π * (s⁻¹ * l)⁻¹) =
        (x⁻¹ * π) * (π⁻¹ * (s⁻¹ * l) * π) * (s⁻¹ * l)⁻¹ := by group
    rw [heq]
    exact H.mul_mem (H.mul_mem hxπ hπc) (H.inv_mem hc)
  have h1 := hSHmem _ (Sg.mul_mem (Sg.inv_mem hx) hyS) hxyH
  calc (s⁻¹ * l) * π * (s⁻¹ * l)⁻¹ = x * (x⁻¹ * ((s⁻¹ * l) * π * (s⁻¹ * l)⁻¹)) := by group
    _ = x := by rw [h1, mul_one]

end TwoPart

section Node

theorem lyons_order_three_normalized_odd_subgroups_and_strong_embedding [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3) :
    (∀ H : Subgroup G, Odd (Nat.card H) →
      (S : Subgroup G) ≤ Subgroup.normalizer (H : Set G) → H = ⊥) ∧
    (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = (S : Subgroup G) ∧
      Subgroup.centralizer (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype :
        Subgroup G) : Set G) = (S : Subgroup G)) ∧
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder
      (Subgroup.normalizer (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype :
        Subgroup G) : Set G)) := by
  classical
  let := Fintype.ofFinite G
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  let := hmax
  let := hchar
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨label, hlabel, -, -, -, -, -, -, -, -, -, -, hfixed⟩ :=
    lyons_order_three_principal_character_without_sylow_fixed_vectors hnonab hT S U hSU hd basis
      ideal principal hprincipal
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hconst, -⟩ :=
    lyons_order_three_principal_induction_gram hnonab hT S U hSU hd basis ideal principal
      hprincipal
  obtain ⟨-, -, hsq, hZcard, -, -, -, -, -, -, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have hcomp := (lyons_order_three_normalizer_involution_complements hnonab hT S U hSU hd).1
  set Sg := (S : Subgroup G) with hSg
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  set ρ := (basis.representation label).representation with hρ
  have hfixV : ∀ v : (basis.representation label).vector, (∀ s ∈ Sg, ρ s v = v) → v = 0 :=
    hfixed (basis.representation label).vector ρ rfl
  have hker : MonoidHom.ker ρ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with h | h
    · exact h
    · exfalso
      have hdeg := irreducible_character_degree_ne_zero (basis.representation label)
        (basis.irreducible label)
      rw [character_one_eq_finrank] at hdeg
      have hpos : 0 < Module.finrank ℂ (basis.representation label).vector :=
        Nat.pos_of_ne_zero (by exact_mod_cast hdeg)
      have : Nontrivial (basis.representation label).vector :=
        Module.nontrivial_of_finrank_pos hpos
      obtain ⟨v, hv⟩ := exists_ne (0 : (basis.representation label).vector)
      apply hv
      apply hfixV v
      intro s _
      have hs : s ∈ MonoidHom.ker ρ := by rw [h]; exact Subgroup.mem_top s
      rw [MonoidHom.mem_ker] at hs
      rw [hs]
      rfl
  have hodd : ∀ H : Subgroup G, Odd (Nat.card H) → Sg ≤ Subgroup.normalizer (H : Set G) →
      H = ⊥ := by
    intro H hHodd hSH
    have hconst' : ∀ x ∈ Sg, x ≠ 1 → ∀ h ∈ H, ρ.character (x * h) = ρ.character x := by
      intro x hx hx1 h hh
      obtain ⟨π, r, e, hπz, hrz, hcomm, hfac, hπ, hr⟩ :=
        finite_prime_primary_factorization (x * h) 2 Nat.prime_two
      obtain ⟨c, hc, hcπ⟩ := twoPart_conj_of_mul S H hHodd hSH hx hh hπz hrz hfac hπ hr
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hπ
      have hpart : CFSG.BlocksIsPPart 2 (x * h) π :=
        ⟨r, hfac, by rw [← hcomm.eq]; exact hfac, ⟨k, hk⟩, orderOf_pos r, hr.symm⟩
      have hπ1 : π ≠ 1 := by
        intro h1
        apply hx1
        rw [← hcπ, h1]
        group
      have h1 := hconst label hlabel (x * h) π hpart hπ1
      have h2 : (basis.representation label).character x =
          (basis.representation label).character π := by
        rw [← hcπ]
        exact Representation.char_conj _ π c
      change (basis.representation label).character (x * h) =
        (basis.representation label).character x
      rw [h1, h2]
    have hle := coset_constant_character_fixed_space_kernel H Sg hSH ρ hfixV hconst'
    rw [hker] at hle
    exact le_bot_iff.mp hle
  have hcent : ∀ z ∈ Z, z ≠ 1 → Subgroup.centralizer ({z} : Set G) = Sg := by
    intro z hz hz1
    obtain ⟨hdecomp, -, -⟩ := hcomp z hz hz1
    set C := Subgroup.centralizer ({z} : Set G) with hC
    set K := (CFSG.oddCore C).map C.subtype with hK
    have hSC : Sg ≤ C := by
      intro s hs
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact (mem_map_center_iff.mp hz).2 s hs
    have hKodd : Odd (Nat.card K) := by
      rw [hK, Subgroup.card_map_of_injective C.subtype_injective]
      exact odd_card_oddCore C
    have hSK : Sg ≤ Subgroup.normalizer (K : Set G) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hsC := hSC hs
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨⟨s, hsC⟩ * k * ⟨s, hsC⟩⁻¹, (CFSG.oddCore_normal C).conj_mem k hk _, ?_⟩
        simp
      · rintro ⟨k, hk, hkeq⟩
        refine ⟨⟨s, hsC⟩⁻¹ * k * ⟨s, hsC⟩⁻¹⁻¹,
          (CFSG.oddCore_normal C).conj_mem k hk _, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hkeq ⊢
        rw [hkeq]
        group
    have hKbot := hodd K hKodd hSK
    apply le_antisymm _ hSC
    intro c hc
    obtain ⟨s, hs, k, hk, rfl⟩ := hdecomp c hc
    rw [hKbot] at hk
    rw [Subgroup.mem_bot.mp hk, mul_one]
    exact hs
  have hcentZ : Subgroup.centralizer (Z : Set G) = Sg := by
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
      by_contra hall
      push Not at hall
      have hbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hall
      have hcard : Nat.card Z = 4 := by
        rw [hZ, Subgroup.card_map_of_injective Sg.subtype_injective, hZcard]
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    apply le_antisymm
    · rw [← hcent z hz hz1]
      exact Subgroup.centralizer_le (by simpa using hz)
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact ((mem_map_center_iff.mp hw).2 s hs).symm
  refine ⟨hodd, fun z hz hz1 => ⟨hcent z hz hz1, hcentZ⟩, ?_⟩
  have hEnt : Z ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card Z = 4 := by
      rw [hZ, Subgroup.card_map_of_injective Sg.subtype_injective, hZcard]
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hnotnormal : ¬ Z.Normal := by
    intro hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with h | h
    · exact hEnt h
    · obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have haZ : a ∈ Z := by rw [h]; exact Subgroup.mem_top a
      have hbZ : b ∈ Z := by rw [h]; exact Subgroup.mem_top b
      exact ((mem_map_center_iff.mp haZ).2 b (mem_map_center_iff.mp hbZ).1).symm
  exact central_sylow_involution_set_strong_embedding S Z
    (fun w hw => (mem_map_center_iff.mp hw).1)
    (fun w hw s hs => (mem_map_center_iff.mp hw).2 s hs)
    (fun w hw => (hsq w (mem_map_center_iff.mp hw).1).mpr hw) hEnt
    (fun t ht ht2 => (hsq t ht).mp ht2) hnotnormal
    (fun w hw hw1 => by rw [hcent w hw hw1, hcentZ])

end Node

end CFSG.LyonsUnitaryFour
