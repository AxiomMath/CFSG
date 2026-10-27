module

public import CFSG.GH74.GLS.SP.Local.SPLR2Defs
public import CFSG.GH74.GLS.SP.Local.SPLR2Tools
public import CFSG.GH74.GLS.SP.Local.SPLJ
public import CFSG.GH74.GLS.SP.Local.SPLWt1
public import CFSG.Adapters.Involutions
public import CFSG.GH74.GLS.Stage4.T2SL2B

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace R2AFacts

section Basic

variable {G : Type} [Group G] (D : SPLNot3 G)

theorem mem_C₂_iff {g : G} : g ∈ D.C₂ ↔ ∀ x ∈ D.X₂, x * g = g * x := by
  unfold SPLNot3.C₂
  exact Subgroup.mem_centralizer_iff

theorem X₂_comm (h3 : SPL3X D) : ∀ x ∈ D.X₂, ∀ y ∈ D.X₂, x * y = y * x :=
  (isEAb_conjBy h3.X₁_eab D.t).1

theorem X₂_le_C₂ (h3 : SPL3X D) : D.X₂ ≤ D.C₂ := fun x hx =>
  (mem_C₂_iff D).2 fun y hy => X₂_comm D h3 y hy x hx

theorem X₂_central {g : G} (hg : g ∈ D.C₂) {x : G} (hx : x ∈ D.X₂) : g * x = x * g :=
  ((mem_C₂_iff D).1 hg x hx).symm

theorem card_X₂ (h3 : SPL3X D) : Nat.card ↥D.X₂ = D.q := by
  rw [SPLNot3.X₂, card_conjBy]
  exact h3.X₁_card

theorem odd_card_X₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) :
    Odd (Nat.card ↥D.X₂) := by
  rw [card_X₂ D h3]
  exact hs.odd_q

theorem odd_orderOf_X₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {x : G}
    (hx : x ∈ D.X₂) : Odd (orderOf x) :=
  Odd.of_dvd_nat (odd_card_X₂ D hs h3) (Subgroup.orderOf_dvd_natCard D.X₂ hx)

theorem z_mem_C₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.z ∈ D.C₂ :=
  (mem_C₂_iff D).2 fun _ hx => hs.comps.cz₂ (X₂_le_K₂ D hs h3 hx)

theorem K₁_le_C₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.K₁ ≤ D.C₂ :=
  fun k hk => (mem_C₂_iff D).2 fun _ hx => (hs.comps.comm k hk _ (X₂_le_K₂ D hs h3 hx)).symm

end Basic

section V2

variable {G : Type} [Group G] (D : SPLNot3 G)

theorem V₂_le_C₂ : D.V₂ ≤ D.C₂ := by
  intro v hv
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hv
  exact y.2

theorem card_V₂ : Nat.card ↥D.V₂ = Nat.card ↥(pPrimeCore 2 ↥D.C₂) :=
  Subgroup.card_map_of_injective D.C₂.subtype_injective

theorem V₂_odd [Finite G] : Odd (Nat.card ↥D.V₂) := by
  rw [card_V₂]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem V₂_norm {g : G} (hg : g ∈ D.C₂) {v : G} (hv : v ∈ D.V₂) : g * v * g⁻¹ ∈ D.V₂ := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hv
  exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, pPrimeCore_normal.conj_mem y hy ⟨g, hg⟩, rfl⟩

theorem odd_orderOf_V₂ [Finite G] {v : G} (hv : v ∈ D.V₂) : Odd (orderOf v) :=
  Odd.of_dvd_nat (V₂_odd D) (Subgroup.orderOf_dvd_natCard D.V₂ hv)

theorem z_not_mem_V₂ [Finite G] (hs : SPLSetup D.toSPLNot0) : D.z ∉ D.V₂ := fun hz => by
  have h := odd_orderOf_V₂ D hz
  rw [hs.syl.z_inv] at h
  exact (Nat.not_odd_iff_even.mpr even_two) h

theorem X₂_le_V₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) : D.X₂ ≤ D.V₂ := by
  have hle := X₂_le_C₂ D h3
  have hN : (D.X₂.subgroupOf D.C₂).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h : (g : G) * (n : G) = (n : G) * (g : G) := X₂_central D g.2 hn
      have e : ((g * n * g⁻¹ : ↥D.C₂) : G) = n := by
        show (g : G) * (n : G) * (g : G)⁻¹ = n
        rw [h]
        group
      rw [e]
      exact hn⟩
  have hcard : Odd (Nat.card ↥(D.X₂.subgroupOf D.C₂)) := by
    have e : Nat.card ↥(D.X₂.subgroupOf D.C₂) = Nat.card ↥D.X₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [e]
    exact odd_card_X₂ D hs h3
  have hNle : D.X₂.subgroupOf D.C₂ ≤ pPrimeCore 2 ↥D.C₂ :=
    le_sSup ⟨hN, Nat.coprime_two_left.mpr hcard⟩
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hle hx⟩, hNle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end V2

section Invol

variable {G : Type} [Group G] (D : SPLNot3 G)

theorem two_ne_zero_of_odd_card' {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro hc
  have h := (FiniteField.even_card_iff_char_two (F := F)).mp hc
  rw [← Nat.card_eq_fintype_card] at h
  have := Nat.odd_iff.mp hodd
  omega

theorem K₁_invol [Finite G] (hs : SPLSetup D.toSPLNot0) {x : G} (hx : x ∈ D.K₁) (hx2 : x * x = 1) :
    x = 1 ∨ x = D.z := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hs.comps.sl₁
  have hcard' : Nat.card F = D.q := hcard
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card' (by rw [hcard']; exact hs.odd_q)
  let e' : ↥D.K₁ ≃* Stage4.Hex.SL2 F := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have key : ∀ y : ↥D.K₁, y * y = 1 → y ≠ 1 → e' y = Stage4.Rest.T2.negOne F := by
    intro y hy hy1
    refine Stage4.Rest.T2.eq_negOne_of_involution h2 (by rw [← map_mul, hy, map_one]) ?_
    intro h
    exact hy1 (e'.injective (by rw [h, map_one]))
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have hz1 : D.z ≠ 1 := by
      intro h
      have h' := hs.syl.z_inv
      rw [h, orderOf_one] at h'
      exact absurd h' (by norm_num)
    have e1 := key ⟨x, hx⟩ (Subtype.ext hx2) (fun h => hx1 (congrArg Subtype.val h))
    have e2 := key ⟨D.z, z_mem_K₁ hs⟩ (Subtype.ext hs.z_sq) (fun h => hz1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e'.injective (e1.trans e2.symm))

theorem XK_invol [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {y : G}
    (hy : y ∈ D.X₂ ⊔ D.K₁) (hy2 : y * y = 1) : y = 1 ∨ y = D.z := by
  obtain ⟨x, hx, k, hk, rfl⟩ := mem_sup_of_commute
    (fun a ha b hb => (hs.comps.comm b hb a (X₂_le_K₂ D hs h3 ha)).symm) hy
  have hxk : Commute x k := (hs.comps.comm k hk x (X₂_le_K₂ D hs h3 hx)).symm
  obtain ⟨j, hj⟩ := odd_orderOf_X₂ D hs h3 hx
  have h1 : (x * k) ^ (2 * j + 1) = x * k := by
    have h : (x * k) ^ 2 = 1 := by rw [pow_two]; exact hy2
    rw [pow_succ, pow_mul, h, one_pow, one_mul]
  have h2 : (x * k) ^ (2 * j + 1) = k ^ (2 * j + 1) := by
    rw [hxk.mul_pow, ← hj, pow_orderOf_eq_one, one_mul]
  have hxkK : x * k ∈ D.K₁ := by
    rw [← h1, h2]
    exact D.K₁.pow_mem hk _
  exact K₁_invol D hs hxkK hy2

end Invol

section Cen

variable {G : Type} [Group G] (D : SPLNot3 G)

theorem K₁_inf_V₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) {k : G} (hk : k ∈ D.K₁)
    (hkV : k ∈ D.V₂) : k = 1 := by
  have hKC := K₁_le_C₂ D hs h3
  have hN : (D.V₂.subgroupOf D.K₁).Normal :=
    ⟨fun n hn g => by
      show ((g * n * g⁻¹ : ↥D.K₁) : G) ∈ D.V₂
      exact V₂_norm D (hKC g.2) hn⟩
  have hz := z_not_mem_V₂ D hs
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hs.comps.quasi₁
      (D.V₂.subgroupOf D.K₁) with hle | htop
  · have hkc : (⟨k, hk⟩ : ↥D.K₁) ∈ center ↥D.K₁ := hle hkV
    have hkz : k ∈ zpowers D.z := (mem_center_K₁_iff D hs ⟨k, hk⟩).mp hkc
    rcases eq_one_or_z hs hkz with h | h
    · exact h
    · exact absurd (h ▸ hkV) hz
  · exfalso
    have hzK : (⟨D.z, z_mem_K₁ hs⟩ : ↥D.K₁) ∈ D.V₂.subgroupOf D.K₁ := by
      rw [htop]
      trivial
    exact hz hzK

theorem V₂_cen_z [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) {v : G} (hv : v ∈ D.V₂)
    (hzv : D.z * v * D.z⁻¹ = v) : v ∈ D.X₂ := by
  have hvC : v ∈ D.C₂ ⊓ centralizer ({D.z} : Set G) := by
    refine ⟨V₂_le_C₂ D hv, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h : D.z * v = v * D.z := by
      calc D.z * v = (D.z * v * D.z⁻¹) * D.z := by group
        _ = v * D.z := by rw [hzv]
    exact h.symm
  rw [hCX] at hvC
  obtain ⟨x, hx, k, hk, rfl⟩ := mem_sup_of_commute
    (fun a ha b hb => (hs.comps.comm b hb a (X₂_le_K₂ D hs h3 ha)).symm) hvC
  have hxV : x ∈ D.V₂ := X₂_le_V₂ D hs h3 hx
  have hkV : k ∈ D.V₂ := by
    have e : k = x⁻¹ * (x * k) := by group
    rw [e]
    exact D.V₂.mul_mem (D.V₂.inv_mem hxV) hv
  rw [K₁_inf_V₂ D hs h3 hk hkV, mul_one]
  exact hx

end Cen

section Sylow

variable {G : Type} [Group G] (D : SPLNot3 G)

theorem orderOf_z_C₂ [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) :
    orderOf (⟨D.z, z_mem_C₂ D hs h3⟩ : ↥D.C₂) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact hs.syl.z_inv

theorem exists_sylow_cen [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) :
    ∃ S : Sylow 2 ↥D.C₂, ∃ _ : (⟨D.z, z_mem_C₂ D hs h3⟩ : ↥D.C₂) ∈ (S : Subgroup ↥D.C₂),
      ∀ s ∈ (S : Subgroup ↥D.C₂), s * ⟨D.z, z_mem_C₂ D hs h3⟩ = ⟨D.z, z_mem_C₂ D hs h3⟩ * s := by
  set z' : ↥D.C₂ := ⟨D.z, z_mem_C₂ D hs h3⟩ with hz'
  have hz'ord : orderOf z' = 2 := orderOf_z_C₂ D hs h3
  have hz'1 : z' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz'ord
    exact absurd hz'ord (by norm_num)
  have hYp : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'ord, pow_one])
  obtain ⟨S, hS⟩ := hYp.exists_le_sylow
  have hz'S : z' ∈ (S : Subgroup ↥D.C₂) := hS (Subgroup.mem_zpowers z')
  refine ⟨S, hz'S, ?_⟩
  have hSp : IsPGroup 2 ↥(S : Subgroup ↥D.C₂) := S.isPGroup'
  have : Nontrivial ↥(S : Subgroup ↥D.C₂) :=
    ⟨⟨⟨z', hz'S⟩, 1, fun h => hz'1 (congrArg Subtype.val h)⟩⟩
  have : Nontrivial ↥(center ↥(S : Subgroup ↥D.C₂)) := hSp.center_nontrivial
  have hZp : IsPGroup 2 ↥(center ↥(S : Subgroup ↥D.C₂)) := hSp.to_subgroup _
  have hdvd : 2 ∣ Nat.card ↥(center ↥(S : Subgroup ↥D.C₂)) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exfalso
      exact (not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp h).1) inferInstance
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy, pow_two] at h
    exact h
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hYY : y.1.1.1 * y.1.1.1 = 1 := by
    have h := congrArg (fun t : ↥(center ↥(S : Subgroup ↥D.C₂)) => t.1.1.1) hyy
    simpa using h
  have hYz : D.z * y.1.1.1 = y.1.1.1 * D.z := by
    have h := Subgroup.mem_center_iff.mp y.2 ⟨z', hz'S⟩
    exact congrArg (fun t : ↥(S : Subgroup ↥D.C₂) => t.1.1) h
  have hYmem : y.1.1.1 ∈ D.C₂ ⊓ centralizer ({D.z} : Set G) :=
    ⟨y.1.1.2, Subgroup.mem_centralizer_singleton_iff.mpr hYz.symm⟩
  rw [hCX] at hYmem
  have hYz' : y.1.1.1 = D.z := by
    rcases XK_invol D hs h3 hYmem hYY with h | h
    · exfalso
      apply hy1
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
    · exact h
  have hzZ : (⟨z', hz'S⟩ : ↥(S : Subgroup ↥D.C₂)) ∈ center ↥(S : Subgroup ↥D.C₂) := by
    have e : y.1 = ⟨z', hz'S⟩ := Subtype.ext (Subtype.ext hYz')
    rw [← e]
    exact y.2
  intro s hs'
  have h := Subgroup.mem_center_iff.mp hzZ ⟨s, hs'⟩
  exact congrArg (fun t : ↥(S : Subgroup ↥D.C₂) => t.1) h

theorem z_cen_mod [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) :
    ∀ g ∈ D.C₂, ⁅g, D.z⁆ ∈ D.V₂ := by
  obtain ⟨S, hz'S, hcen⟩ := exists_sylow_cen D hs h3 hCX
  set z' : ↥D.C₂ := ⟨D.z, z_mem_C₂ D hs h3⟩ with hz'
  have hz'ord : orderOf z' = 2 := orderOf_z_C₂ D hs h3
  have hz'1 : z' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz'ord
    exact absurd hz'ord (by norm_num)
  have hz'sq : z' * z' = 1 := by
    have h := pow_orderOf_eq_one z'
    rwa [hz'ord, pow_two] at h
  set z'' : ↥(S : Subgroup ↥D.C₂) := ⟨z', hz'S⟩ with hz''
  have hzZ : z'' ∈ center ↥(S : Subgroup ↥D.C₂) :=
    Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hcen s.1 s.2)
  have hz''ord : orderOf z'' = 2 := by
    rw [hz'', Subgroup.orderOf_mk]
    exact hz'ord
  have hSX : ∀ s ∈ (S : Subgroup ↥D.C₂), (s : G) ∈ D.X₂ ⊔ D.K₁ := by
    intro s hs'
    rw [← hCX]
    refine ⟨s.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (hcen s hs')
  have hwc : ∀ g : ↥D.C₂, g⁻¹ * (z'' : ↥D.C₂) * g ∈ (S : Subgroup ↥D.C₂) →
      g⁻¹ * (z'' : ↥D.C₂) * g = z'' := by
    intro g hg
    have hww : (g⁻¹ * z' * g) * (g⁻¹ * z' * g) = 1 := by
      calc (g⁻¹ * z' * g) * (g⁻¹ * z' * g) = g⁻¹ * (z' * z') * g := by group
        _ = 1 := by rw [hz'sq]; group
    have hww' : ((g⁻¹ * z' * g : ↥D.C₂) : G) * ((g⁻¹ * z' * g : ↥D.C₂) : G) = 1 :=
      congrArg Subtype.val hww
    rcases XK_invol D hs h3 (hSX _ hg) hww' with h | h
    · exfalso
      have hw1 : g⁻¹ * z' * g = 1 := Subtype.ext h
      apply hz'1
      calc z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
        _ = 1 := by rw [hw1]; group
    · exact Subtype.ext h
  obtain ⟨-, hZ⟩ := CFSG.Adapters.glauberman_zStar S z'' hzZ hz''ord hwc
  have hle : oddCore ↥D.C₂ ≤ pPrimeCore 2 ↥D.C₂ :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  intro g hg
  set g' : ↥D.C₂ := ⟨g, hg⟩ with hg'
  have hcomm : (QuotientGroup.mk g' : ↥D.C₂ ⧸ oddCore ↥D.C₂) * QuotientGroup.mk z' =
      QuotientGroup.mk z' * QuotientGroup.mk g' :=
    Subgroup.mem_center_iff.mp hZ (QuotientGroup.mk g')
  have hcO : g' * z' * g'⁻¹ * z'⁻¹ ∈ oddCore ↥D.C₂ := by
    rw [← QuotientGroup.eq_one_iff]
    have e : (QuotientGroup.mk (g' * z' * g'⁻¹ * z'⁻¹) : ↥D.C₂ ⧸ oddCore ↥D.C₂) =
        QuotientGroup.mk g' * QuotientGroup.mk z' * (QuotientGroup.mk g')⁻¹ *
          (QuotientGroup.mk z')⁻¹ := rfl
    rw [e, hcomm]
    group
  exact Subgroup.mem_map.mpr ⟨_, hle hcO, rfl⟩

end Sylow

section Mod

variable {G : Type} [Group G] (D : SPLNot3 G)

theorem z_inv_mod [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) :
    ∀ v ∈ D.V₂, D.z * v * D.z⁻¹ * v ∈ D.X₂ := by
  intro v hv
  have hzC := z_mem_C₂ D hs h3
  obtain ⟨c, hc, s, hsV, hzc, hzs, rfl⟩ := invol_decomp D.z (z_mul_z D hs) D.V₂
    (fun q hq => V₂_norm D hzC hq) (V₂_odd D) hv
  have hcX : c ∈ D.X₂ := V₂_cen_z D hs h3 hCX hc hzc
  have hcs : s * c = c * s := X₂_central D (V₂_le_C₂ D hsV) hcX
  have e : D.z * (c * s) * D.z⁻¹ * (c * s) = c * c := by
    calc D.z * (c * s) * D.z⁻¹ * (c * s)
        = (D.z * c * D.z⁻¹) * (D.z * s * D.z⁻¹) * (c * s) := by group
      _ = c * s⁻¹ * (c * s) := by rw [hzc, hzs]
      _ = c * (s⁻¹ * (c * s)) := by group
      _ = c * (s⁻¹ * (s * c)) := by rw [hcs]
      _ = c * c := by group
  rw [e]
  exact D.X₂.mul_mem hcX hcX

theorem V₂_class2 [Finite G] (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) :
    ∀ u ∈ D.V₂, ∀ v ∈ D.V₂, ⁅u, v⁆ ∈ D.X₂ := by
  have hinv := z_inv_mod D hs h3 hCX
  have aux : ∀ u ∈ D.V₂, ∀ v ∈ D.V₂, u⁻¹ * v⁻¹ * u * v ∈ D.X₂ := by
    intro u hu v hv
    have ha := hinv u hu
    have hb := hinv v hv
    have hc := hinv (u * v) (D.V₂.mul_mem hu hv)
    have hub : u⁻¹ * (D.z * v * D.z⁻¹ * v) = (D.z * v * D.z⁻¹ * v) * u⁻¹ :=
      X₂_central D (D.C₂.inv_mem (V₂_le_C₂ D hu)) hb
    have e : u⁻¹ * v⁻¹ * u * v =
        ((D.z * u * D.z⁻¹ * u) * (D.z * v * D.z⁻¹ * v))⁻¹ * (D.z * (u * v) * D.z⁻¹ * (u * v)) := by
      have h1 : D.z * (u * v) * D.z⁻¹ * (u * v) =
          (D.z * u * D.z⁻¹ * u) * (u⁻¹ * (D.z * v * D.z⁻¹ * v)) * (v⁻¹ * u * v) := by group
      rw [h1, hub]
      group
    rw [e]
    exact D.X₂.mul_mem (D.X₂.inv_mem (D.X₂.mul_mem ha hb)) hc
  intro u hu v hv
  have h := aux u⁻¹ (D.V₂.inv_mem hu) v⁻¹ (D.V₂.inv_mem hv)
  simpa [commutatorElement_def] using h

end Mod

end R2AFacts

theorem r2A_of_inputs {G : Type} [Group G] [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (_h1 : SPL2Set D.toSPLNot1) (_hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) : R2A D where
  z_mem_C₂ := R2AFacts.z_mem_C₂ D hs h3
  K₁_le_C₂ := R2AFacts.K₁_le_C₂ D hs h3
  X₂_le_V₂ := R2AFacts.X₂_le_V₂ D hs h3
  V₂_odd := R2AFacts.V₂_odd D
  V₂_norm := fun _ hg _ hv => R2AFacts.V₂_norm D hg hv
  V₂_cen_z := fun _ hv hzv => R2AFacts.V₂_cen_z D hs h3 hCX hv hzv
  z_cen_mod := R2AFacts.z_cen_mod D hs h3 hCX
  z_inv_mod := R2AFacts.z_inv_mod D hs h3 hCX
  V₂_class2 := R2AFacts.V₂_class2 D hs h3 hCX

end CFSG.GH74.GLS.SP.Local
