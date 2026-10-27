module

public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Walter.Bender1970.S2.Cyclic

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Goldschmidt.SStarTransport

section Transport

variable {G : Type*} [Group G]

theorem open_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

theorem open_isQuasisimple_iff {Q : Type*} [Group Q] :
    CFSG.Open.IsQuasisimple Q ↔ GorensteinWalter.IsQuasisimple Q := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    have := h2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

theorem normalClosureIn_subgroupOf {H A X : Subgroup G} (hHX : H ≤ X) :
    normalClosureIn (H.subgroupOf X) (A.subgroupOf X) = (normalClosureIn H A).subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  have hle : normalClosureIn H A ≤ X := (Subgroup.map_subtype_le _).trans hHX
  rw [Subgroup.map_subgroupOf_eq_of_le hle]
  let e : ↥(H.subgroupOf X) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHX
  have hcomp : X.subtype.comp (H.subgroupOf X).subtype = H.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [normalClosureIn, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.map_normalClosure _ _ e.surjective]
  congr 2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    exact hx

theorem isSylowIn_subgroupOf {p : ℕ} {T L X : Subgroup G} (hLX : L ≤ X)
    (h : CFSG.Open.fusionIsSylowIn p T L) :
    CFSG.Open.fusionIsSylowIn p (T.subgroupOf X) (L.subgroupOf X) := by
  obtain ⟨hTL, hT, hmax⟩ := h
  refine ⟨fun x hx => hTL hx, hT.comap_subtype, fun P hPL hP hTP => ?_⟩
  have h1 := hmax (P.map X.subtype) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hPL hx) (hP.map X.subtype) (by
      intro t ht
      exact ⟨⟨t, hLX (hTL ht)⟩, hTP ht, rfl⟩)
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective P).symm

theorem mem_centralizer_subgroupOf_iff {B X : Subgroup G} (hBX : B ≤ X) (x : X) :
    x ∈ Subgroup.centralizer ((B.subgroupOf X : Subgroup X) : Set X) ↔
      (x : G) ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    exact congrArg Subtype.val (h ⟨b, hBX hb⟩ hb)
  · intro h b hb
    exact Subtype.ext (h b hb)

theorem map_centralizer_subgroupOf_le {B X : Subgroup G} (hBX : B ≤ X) :
    (Subgroup.centralizer ((B.subgroupOf X : Subgroup X) : Set X)).map X.subtype ≤
      Subgroup.centralizer (B : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_centralizer_subgroupOf_iff hBX x).mp hx

theorem mem_center_iff_mem_centralizer {L : Subgroup G} (x : L) :
    x ∈ Subgroup.center L ↔ (x : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)
  · intro h y
    exact Subtype.ext (h y y.2)

end Transport

theorem g32Q_subgroup (h32Q : S_G32Q) {G : Type} [Group G] [Finite G] {L A T : Subgroup G}
    (hLq : CFSG.Open.IsQuasisimple L) (hI : IsGoldTypeI L)
    (hZ : IsPGroup 2 (Subgroup.center L)) (hS : IsSStarIn L A)
    (hT : CFSG.Open.fusionIsSylowIn 2 T L)
    (hAT : A ≤ T) {a : G} (haA : a ∈ A) (haZ : a ∉ Subgroup.centralizer (L : Set G)) :
    (∀ M : Subgroup G, M ≤ L → L ⊓ Subgroup.centralizer ({a} : Set G) ≤ M → M ≠ L →
      M ≤ Subgroup.normalizer (T : Set G)) ∧
    L ⊓ Subgroup.normalizer (T : Set G) ⊓
        Subgroup.centralizer ((T ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) ≤
      T := by
  have hAL : A ≤ L := hS.1
  have hTL : T ≤ L := hT.1
  have hS' : IsSStarIn (⊤ : Subgroup L) (A.subgroupOf L) := by
    have h1 := isSStarIn_subgroupOf hS (le_refl L)
    rwa [Subgroup.subgroupOf_self] at h1
  obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowIn hT
  have hAT' : A.subgroupOf L ≤ (T' : Subgroup L) := by
    rw [hT']
    exact fun x hx => hAT hx
  set a' : L := ⟨a, hAL haA⟩ with ha'
  have ha'Z : a' ∉ Subgroup.center L := fun h => haZ ((mem_center_iff_mem_centralizer a').mp h)
  obtain ⟨h1, h2⟩ := h32Q L hLq hI hZ (A.subgroupOf L) hS' T' hAT' a' haA ha'Z
  have hNT : (Subgroup.normalizer ((T' : Subgroup L) : Set L)) =
      (Subgroup.normalizer (T : Set G)).subgroupOf L := by
    rw [hT', Subgroup.subgroupOf_normalizer_eq hTL]
  have hCa : ∀ x : L, x ∈ Subgroup.centralizer ({a'} : Set L) ↔
      (x : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  refine ⟨fun M hML hCM hML' => ?_, ?_⟩
  · have hM : Subgroup.centralizer ({a'} : Set L) ≤ M.subgroupOf L := by
      intro x hx
      exact hCM ⟨x.2, (hCa x).mp hx⟩
    have hMtop : M.subgroupOf L ≠ ⊤ := by
      intro h
      apply hML'
      apply le_antisymm hML
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ M.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
    have h3 := h1 (M.subgroupOf L) hM hMtop
    rw [hNT] at h3
    intro x hx
    exact h3 (show (⟨x, hML hx⟩ : L) ∈ M.subgroupOf L from hx)
  · rintro x ⟨⟨hxL, hxN⟩, hxC⟩
    have hx : (⟨x, hxL⟩ : L) ∈ (T' : Subgroup L) := by
      apply h2
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hNT]
        exact hxN
      · rw [Subgroup.mem_centralizer_iff]
        rintro y ⟨hyT, hyC⟩
        have hyT' : (y : G) ∈ T := by
          rw [hT'] at hyT
          exact hyT
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y ⟨hyT', (hCa y).mp hyC⟩)
    rw [hT'] at hx
    exact hx

theorem g33_subgroup (h33 : S_G33) {G : Type} [Group G] [Finite G] {L A T : Subgroup G}
    (hLq : CFSG.Open.IsQuasisimple L) (hI : IsGoldTypeI L) (hS : IsSStarIn L A)
    (hcl : normalClosureIn L A = L) (hT : CFSG.Open.fusionIsSylowIn 2 T L) (hAT : A ≤ T) {α : G}
    (hαL : α ∈ Subgroup.normalizer (L : Set G)) (hαA : α ∈ Subgroup.centralizer (A : Set G))
    (hαT : α ∈ Subgroup.normalizer (T : Set G)) (hαTA : ∀ t ∈ T, α⁻¹ * t * α * t⁻¹ ∈ A) :
    α ∈ T ⊔ Subgroup.centralizer (L : Set G) := by
  set N := Subgroup.normalizer (L : Set G) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hTN : T ≤ N := hT.1.trans hLN
  have hAN : A ≤ N := hAT.trans hTN
  have h1 := h33 N (L.subgroupOf N) (A.subgroupOf N) (T.subgroupOf N) Subgroup.normal_in_normalizer
    (open_isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hLq)
    (isGoldTypeI_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hI)
    (isSStarIn_subgroupOf hS hLN) (by rw [normalClosureIn_subgroupOf hLN, hcl])
    (isSylowIn_subgroupOf hLN hT) (fun x hx => hAT hx) ⟨α, hαL⟩
    ((mem_centralizer_subgroupOf_iff hAN _).mpr hαA)
    (by rw [← Subgroup.subgroupOf_normalizer_eq hTN]; exact hαT)
    (fun t ht => hαTA t ht)
  have hle : (T.subgroupOf N ⊔ Subgroup.centralizer ((L.subgroupOf N : Subgroup N) : Set N)).map
      N.subtype ≤ T ⊔ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (Subgroup.map_subgroupOf_eq_of_le hTN).le (map_centralizer_subgroupOf_le hLN)
  exact hle ⟨⟨α, hαL⟩, h1, rfl⟩

theorem g35_subgroup (h35 : S_G35) {G : Type} [Group G] [Finite G] {L A Y : Subgroup G}
    (hLq : CFSG.Open.IsQuasisimple L) (hII : IsGoldTypeII L) (hS : IsSStarIn L A) (hA : A ≠ ⊥)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) :
    (⁅Y, A⁆ = ⊥ → ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ (L ⊔ Subgroup.centralizer (L : Set G))) ∧
    ∀ a ∈ A, a ≠ 1 → L ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Y : Set G) →
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsPGroup q Y) →
      Y ≤ L ⊔ Subgroup.centralizer (L : Set G) ∧
        ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ Subgroup.centralizer (L : Set G) := by
  set N := Subgroup.normalizer (L : Set G) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hAN : A ≤ N := hS.1.trans hLN
  have hA' : A.subgroupOf N ≠ ⊥ := by
    intro h
    apply hA
    have h1 := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hAN, Subgroup.map_bot] at h1
  obtain ⟨h1, h2⟩ := h35 N (L.subgroupOf N) (A.subgroupOf N) (Y.subgroupOf N)
    Subgroup.normal_in_normalizer
    (open_isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hLq)
    (isGoldTypeII_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hII)
    (isSStarIn_subgroupOf hS hLN) hA'
  have hmapLC : (L.subgroupOf N ⊔ Subgroup.centralizer ((L.subgroupOf N : Subgroup N) : Set N)).map
      N.subtype ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (Subgroup.map_subgroupOf_eq_of_le hLN).le (map_centralizer_subgroupOf_le hLN)
  have hYmap : (Y.subgroupOf N).map N.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYL
  refine ⟨fun hYA => ?_, fun a ha ha1 hYa hYq => ?_⟩
  · have hYA' : ⁅Y.subgroupOf N, A.subgroupOf N⁆ = ⊥ := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_commutator, hYmap, Subgroup.map_subgroupOf_eq_of_le hAN, hYA,
        Subgroup.map_bot]
    obtain ⟨-, y, hy, hYy⟩ := h1 hYA'
    refine ⟨y, hy, ?_⟩
    have h3 := Subgroup.map_mono (f := N.subtype) hYy
    rw [hYmap, Subgroup.map_sup, MonoidHom.map_zpowers] at h3
    exact h3.trans (sup_le_sup le_rfl hmapLC)
  · have ha' : (⟨a, hAN ha⟩ : N) ∈ A.subgroupOf N := ha
    have ha'1 : (⟨a, hAN ha⟩ : N) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hYa' : L.subgroupOf N ⊓ Subgroup.centralizer ({⟨a, hAN ha⟩} : Set N) ≤
        Subgroup.normalizer ((Y.subgroupOf N : Subgroup N) : Set N) := by
      intro x hx
      obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
      rw [← Subgroup.subgroupOf_normalizer_eq hYL]
      apply hYa
      refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
      exact congrArg Subtype.val hxC
    have hYq' : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsPGroup q (Y.subgroupOf N) := by
      obtain ⟨q, hq, hq2, hYq⟩ := hYq
      exact ⟨q, hq, hq2, hYq.comap_subtype⟩
    obtain ⟨h3, y, hy, hYy⟩ := h2 ⟨a, hAN ha⟩ ha' ha'1 hYa' hYq'
    refine ⟨?_, y, hy, ?_⟩
    · have h4 := Subgroup.map_mono (f := N.subtype) h3
      rw [hYmap] at h4
      exact h4.trans hmapLC
    · have h4 := Subgroup.map_mono (f := N.subtype) hYy
      rw [hYmap, Subgroup.map_sup, MonoidHom.map_zpowers] at h4
      exact h4.trans (sup_le_sup le_rfl (map_centralizer_subgroupOf_le hLN))

section G34

theorem factorization_twelve_two : (12 : ℕ).factorization 2 = 2 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd]

theorem card_alternatingGroup_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup]; simp; decide

theorem eq_four_of_dvd_twelve {c : ℕ} (h1 : 4 ∣ c) (h2 : c ∣ 12) (h3 : c ≠ 12) : c = 4 := by
  obtain ⟨k, rfl⟩ := h1
  have : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) (by simpa using h2)
  have hk : k ≤ 3 := Nat.le_of_dvd (by norm_num) this
  interval_cases k <;> simp_all

theorem centralizer_le_of_normalizer_alternatingFour {L : Type*} [Group L] [Finite L]
    {A : Subgroup L} (hA : A ≠ ⊥) (hAc : IsMulCommutative A)
    (hsyl : CFSG.Open.fusionIsSylowIn 2 A ⊤)
    (e : Subgroup.normalizer (A : Set L) ≃* alternatingGroup (Fin 4)) :
    Subgroup.centralizer (A : Set L) ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (A : Set L) with hN
  set C := Subgroup.centralizer (A : Set L) with hC
  have hN12 : Nat.card N = 12 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_four]
  have hAN : A ≤ N := Subgroup.le_normalizer
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hAC : A ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hAc.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hsylN : CFSG.Open.fusionIsSylowIn 2 A N :=
    ⟨hAN, hsyl.2.1, fun P _ hP hAP => hsyl.2.2 P le_top hP hAP⟩
  obtain ⟨PS, hPS⟩ := exists_sylow_of_isSylowIn hsylN
  have hA4 : Nat.card A = 4 := by
    have h1 := Sylow.card_eq_multiplicity PS
    rw [hN12, factorization_twelve_two, hPS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv] at h1
    rw [h1]
    norm_num
  have hCdvd : Nat.card C ∣ 12 := hN12 ▸ Subgroup.card_dvd_of_le hCN
  have hAdvd : 4 ∣ Nat.card C := hA4 ▸ Subgroup.card_dvd_of_le hAC
  have hCne : Nat.card C ≠ 12 := by
    intro h12
    have hCN' : C = N := Subgroup.eq_of_le_of_card_ge hCN (by rw [h12, hN12])
    have hcent : A.subgroupOf N ≤ Subgroup.center N := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hyC : (y : L) ∈ C := by rw [hCN']; exact y.2
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hyC) x hx).symm
    have hZ : (Subgroup.center N).map (e : N →* alternatingGroup (Fin 4)) = ⊥ := by
      rw [Subgroup.map_center_eq e]
      exact alternatingGroup.center_eq_bot (by simp)
    have hbot : A.subgroupOf N = ⊥ := by
      have h1 := Subgroup.map_mono (f := (e : N →* alternatingGroup (Fin 4))) hcent
      rw [hZ, le_bot_iff] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
    apply hA
    have h2 := congrArg (Subgroup.map N.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hAN, Subgroup.map_bot] at h2
  have hC4 : Nat.card C = 4 := eq_four_of_dvd_twelve hAdvd hCdvd hCne
  have hAC' : A = C := Subgroup.eq_of_le_of_card_ge hAC (by rw [hC4, hA4])
  rw [← hAC']

theorem isCyclic_of_le_centralizer_dihedral {L : Type*} [Group L] {a : L} {n : ℕ}
    (e : Subgroup.centralizer ({a} : Set L) ≃* DihedralGroup n) {W : Subgroup L}
    (hW : W ≤ Subgroup.centralizer ({a} : Set L)) (hodd : Odd (Nat.card W)) : IsCyclic W := by
  set C := Subgroup.centralizer ({a} : Set L)
  let W' : Subgroup C := W.subgroupOf C
  have hW' : Nat.card W' = Nat.card W := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv
  have h1 : IsCyclic (W'.map e.toMonoidHom) := by
    apply CFSG.Walter.isCyclic_of_odd_card_dihedralGroup
    rw [Subgroup.card_map_of_injective e.injective, hW']
    exact hodd
  exact (MulEquiv.isCyclic ((Subgroup.subgroupOfEquivOfLe hW).symm.trans
    (W'.equivMapOfInjective _ e.injective))).mpr h1

theorem g34_subgroup (h34 : S_G34) {G : Type} [Group G] [Finite G] {L A : Subgroup G}
    (hL : IsSimpleGroup L) (hZ : Subgroup.center L = ⊥) (hII : IsGoldTypeII L)
    (hS : IsSStarIn L A) (hA : A ≠ ⊥) :
    (∀ a ∈ A, a ≠ 1 → ∀ M : Subgroup G, M ≤ L → L ⊓ Subgroup.centralizer ({a} : Set G) ≤ M →
      M ≠ L → M = L ⊓ Subgroup.centralizer ({a} : Set G) ∨
        M ≤ Subgroup.normalizer (A : Set G)) ∧
    (IsGoldL2 L → L ⊓ Subgroup.centralizer (A : Set G) ≤ A ∧
      (∀ E : Subgroup G, E ≤ L ⊓ Subgroup.normalizer (A : Set G) → Group.IsPerfect E → E = ⊥) ∧
      ∀ a ∈ A, a ≠ 1 → (∀ W : Subgroup G, W ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
        Odd (Nat.card W) → IsCyclic W) ∧
        ∀ E : Subgroup G, E ≤ L ⊓ Subgroup.centralizer ({a} : Set G) → Group.IsPerfect E →
          E = ⊥) := by
  have hAL : A ≤ L := hS.1
  set A' : Subgroup L := A.subgroupOf L with hA'
  have hS' : IsSStarIn (⊤ : Subgroup L) A' := by
    have h1 := isSStarIn_subgroupOf hS (le_refl L)
    rwa [Subgroup.subgroupOf_self] at h1
  have hA'ne : A' ≠ ⊥ := by
    intro h
    apply hA
    have h2 := congrArg (Subgroup.map L.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hAL, Subgroup.map_bot] at h2
  obtain ⟨hsyl, hL2, -, h4⟩ := h34 L hII A' hS' hA'ne
  have hCa : ∀ (x a : L), x ∈ Subgroup.centralizer ({a} : Set L) ↔
      (x : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
    intro x a
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hNA : (Subgroup.normalizer (A : Set G)).subgroupOf L = Subgroup.normalizer (A' : Set L) :=
    Subgroup.subgroupOf_normalizer_eq hAL
  refine ⟨fun a ha ha1 M hML hCM hML' => ?_, fun hL2' => ?_⟩
  · set a' : L := ⟨a, hAL ha⟩ with ha'
    have ha'A : a' ∈ A' := ha
    have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hM : Subgroup.centralizer ({a'} : Set L) ≤ M.subgroupOf L :=
      fun x hx => hCM (Subgroup.mem_inf.mpr ⟨x.2, (hCa x a').mp hx⟩)
    have hMtop : M.subgroupOf L ≠ ⊤ := by
      intro h
      apply hML'
      apply le_antisymm hML
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ M.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
    rcases h4 a' ha'A ha'1 with hco | ⟨-, -, huniq⟩
    · left
      have h1 := (hco.le_iff.mp hM).resolve_left hMtop
      apply le_antisymm _ hCM
      intro x hx
      have h2 : (⟨x, hML hx⟩ : L) ∈ M.subgroupOf L := hx
      rw [h1] at h2
      exact Subgroup.mem_inf.mpr ⟨hML hx, (hCa _ a').mp h2⟩
    · right
      obtain ⟨M'', hM'', hMM''⟩ :=
        (eq_top_or_exists_le_coatom (M.subgroupOf L)).resolve_left hMtop
      have h1 := huniq M'' hM'' (hM.trans hMM'')
      intro x hx
      have h2 : (⟨x, hML hx⟩ : L) ∈ Subgroup.normalizer (A' : Set L) :=
        h1 ▸ hMM'' (show (⟨x, hML hx⟩ : L) ∈ M.subgroupOf L from hx)
      rw [← hNA] at h2
      exact h2
  · obtain ⟨⟨eN⟩, hdih⟩ := hL2 hL2'
    refine ⟨?_, ?_, ?_⟩
    · have := hS.2.1
      have h1 := centralizer_le_of_normalizer_alternatingFour hA'ne
        (Subgroup.comap_injective_isMulCommutative A L.subtype_injective) hsyl eN
      intro x hx
      obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
      have : (⟨x, hxL⟩ : L) ∈ Subgroup.centralizer (A' : Set L) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y hy)
      exact h1 this
    · intro E hE hEp
      have hEL : E ≤ L := fun x hx => (hE hx).1
      have hsolv : Group.IsSolvable (Subgroup.normalizer (A' : Set L)) := by
        have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
        exact Group.isSolvable_of_isSolvable_injective (f := eN.toMonoidHom) eN.injective
      let ι : E →* Subgroup.normalizer (A' : Set L) :=
        (Subgroup.inclusion hEL).codRestrict _ (fun x => by
          rw [← hNA]
          exact (hE x.2).2)
      have hι : Function.Injective ι := by
        intro x y hxy
        apply Subtype.ext
        have := congrArg (fun z : Subgroup.normalizer (A' : Set L) => ((z : L) : G)) hxy
        exact this
      have hEs : Group.IsSolvable E := Group.isSolvable_of_isSolvable_injective hι
      by_contra hne
      have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hne
      exact Group.IsPerfect.not_isSolvable _ hEs
    · intro a ha ha1
      obtain ⟨p, f, hp, -, hf, h5, h8, ⟨eL⟩⟩ := hL2'
      have eLL : L ⧸ Subgroup.center L ≃* L :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      set a' : L := ⟨a, hAL ha⟩ with ha'
      have ha'A : a' ∈ A' := ha
      have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
      have hd := (@hdih p f hp hf ⟨eLL.symm.trans eL⟩ a' ha'A ha'1)
      obtain ⟨n, hn, ⟨e⟩⟩ : ∃ n : ℕ, n ≠ 0 ∧
          Nonempty (Subgroup.centralizer ({a'} : Set L) ≃* DihedralGroup n) := by
        have h48 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
        rcases h48 with h1 | h3
        · exact ⟨(p ^ f - 1) / 2, by omega, hd.1 h1⟩
        · exact ⟨(p ^ f + 1) / 2, by omega, hd.2 h3⟩
      have : NeZero n := ⟨hn⟩
      refine ⟨fun W hW hodd => ?_, fun E hE hEp => ?_⟩
      · have hWL : W ≤ L := fun x hx => (hW hx).1
        have hW' : W.subgroupOf L ≤ Subgroup.centralizer ({a'} : Set L) :=
          fun x hx => (hCa x a').mpr (hW hx).2
        have hodd' : Odd (Nat.card (W.subgroupOf L)) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv]
          exact hodd
        exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hWL)).mp
          (isCyclic_of_le_centralizer_dihedral e hW' hodd')
      · have hEL : E ≤ L := fun x hx => (hE hx).1
        have hE' : ∀ x : E, (⟨x, hEL x.2⟩ : L) ∈ Subgroup.centralizer ({a'} : Set L) :=
          fun x => (hCa _ a').mpr (hE x.2).2
        let ι : E →* DihedralGroup n :=
          e.toMonoidHom.comp ((Subgroup.inclusion hEL).codRestrict _ hE')
        have hι : Function.Injective ι := by
          intro x y hxy
          have h1 := e.injective hxy
          apply Subtype.ext
          exact congrArg (fun z : Subgroup.centralizer ({a'} : Set L) => ((z : L) : G)) h1
        have hsolv : Group.IsSolvable (DihedralGroup n) := CFSG.Walter.isSolvable_dihedralGroup' n
        have hEs : Group.IsSolvable E := Group.isSolvable_of_isSolvable_injective hι
        by_contra hne
        have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hne
        exact Group.IsPerfect.not_isSolvable _ hEs

end G34

end CFSG.Goldschmidt.G37
