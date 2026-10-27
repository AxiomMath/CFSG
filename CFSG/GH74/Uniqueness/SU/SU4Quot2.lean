module

public import CFSG.GH74.Uniqueness.SU.SU4Quot
public import CFSG.GH74.Uniqueness.SU.SU4Iso
public import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

section Quot2

variable {G : Type} [Group G] [Finite G] (M : Subgroup G)

theorem exists_sylow_barImage {S : Subgroup G} (hS : IsSylowIn M S) :
    ∃ T : Sylow 2 (Mbar M), (T : Subgroup (Mbar M)) = barImage M S := by
  have hS₀ : IsSylowIn (⊤ : Subgroup ↥M) (S.subgroupOf M) := by
    refine ⟨le_top, isPGroup_subgroupOf M hS.2.1 hS.1, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hS.2.2
  have h1 := isSylowIn_map (proj M) (odd_card_ker_proj M) hS₀
  have htop : (⊤ : Subgroup ↥M).map (proj M) = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (proj_surjective M)
  rw [htop] at h1
  refine ⟨(h1.2.1).toSylow ?_, rfl⟩
  have := h1.2.2
  rw [Subgroup.relIndex_top_right, Nat.odd_iff] at this
  omega

theorem center_Mbar_eq_bot {S : Subgroup G} {z : G} (hS : IsSylowIn M S) (hzS : z ∈ S)
    (hzu : ∀ c ∈ S, (∀ s ∈ S, s * c = c * s) → c * c = 1 → c = 1 ∨ c = z)
    (hmov : ∃ u ∈ M, u⁻¹ * z * u ∈ S ∧ u⁻¹ * z * u ≠ z) :
    Subgroup.center (Mbar M) = ⊥ := by
  have hSM : S ≤ M := hS.1
  by_contra hcon
  obtain ⟨cb, hcbZ, hcb1⟩ : ∃ c ∈ Subgroup.center (Mbar M), c ≠ 1 := by
    by_contra h
    push Not at h
    exact hcon ((Subgroup.eq_bot_iff_forall _).mpr h)
  have hn : 1 < orderOf cb := Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    ⟨(orderOf_pos cb).ne', fun h => hcb1 (orderOf_eq_one_iff.mp h)⟩
  have hp : (Nat.minFac (orderOf cb)).Prime := Nat.minFac_prime (by omega)
  obtain ⟨n', hn'⟩ := Nat.minFac_dvd (orderOf cb)
  set p := Nat.minFac (orderOf cb) with hpdef
  have hn'pos : n' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hn'
    omega
  set c' := cb ^ n' with hc'def
  have hc'o : orderOf c' = p := by
    rw [hc'def, orderOf_pow_of_dvd hn'pos (Dvd.intro_left p hn'.symm)]
    conv_lhs => rw [hn']
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn'pos)
  have hc'Z : c' ∈ Subgroup.center (Mbar M) := Subgroup.pow_mem _ hcbZ _
  have hc'comm : ∀ g : Mbar M, g * c' = c' * g := fun g => Subgroup.mem_center_iff.mp hc'Z g
  have hp2 : p = 2 := by
    by_contra hp2
    have hnormal : (zpowers c').Normal := ⟨fun y hy g => by
      obtain ⟨j, rfl⟩ := hy
      have h1 : g * c' ^ j = c' ^ j * g :=
        (Commute.zpow_right (show Commute g c' from hc'comm g) j).eq
      rw [h1, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩⟩
    have hbot := (pPrimeCore_eq_bot_iff).mp (GLS.pPrimeCore_quotient_eq_bot (↥M)) (zpowers c') hnormal
      (by rw [Nat.card_zpowers, hc'o]; exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have : c' ∈ (⊥ : Subgroup (Mbar M)) := hbot ▸ Subgroup.mem_zpowers c'
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hc'o
    exact hp.one_lt.ne hc'o
  have hc'2 : c' * c' = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hc'o, hp2])
  have hc'1 : c' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc'o
    exact hp.one_lt.ne hc'o
  obtain ⟨T, hT⟩ := exists_sylow_barImage M hS
  have hTs := sylow_isSylowIn_top T
  have hzp : IsPGroup 2 ↥(zpowers c') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hc'o, hp2, pow_one])
  obtain ⟨c, -, hcT⟩ := hTs.exists_conj_le (le_top) hzp
  have hconj : conjSub c⁻¹ (zpowers c') = zpowers c' := by
    refine conjSub_eq_of_comm (fun v hv => ?_)
    obtain ⟨j, rfl⟩ := hv
    exact ((Commute.zpow_left (show Commute c' c⁻¹ from (hc'comm c⁻¹).symm) j)).eq
  rw [hconj] at hcT
  have hc'T : c' ∈ barImage M S := hT ▸ hcT (Subgroup.mem_zpowers c')
  obtain ⟨m, hmS, hmc⟩ := (mem_barImage M).mp hc'T
  have hSp := hS.2.1
  have hcentral : ∀ s ∈ S, s * (m : G) = (m : G) * s := by
    intro s hs
    have h1 : proj M (⟨s, hSM hs⟩ * m) = proj M (m * ⟨s, hSM hs⟩) := by
      rw [map_mul, map_mul, hmc]; exact hc'comm _
    have := eq_of_proj_eq_of_isPGroup M hSp hSM (a := ⟨s, hSM hs⟩ * m) (b := m * ⟨s, hSM hs⟩)
      (S.mul_mem hs hmS) (S.mul_mem hmS hs) h1
    exact congrArg Subtype.val this
  have hm2 : (m : G) * (m : G) = 1 := by
    have h1 : proj M (m * m) = proj M 1 := by rw [map_mul, map_one, hmc]; exact hc'2
    have := eq_of_proj_eq_of_isPGroup M hSp hSM (a := m * m) (b := 1) (S.mul_mem hmS hmS)
      S.one_mem h1
    exact congrArg Subtype.val this
  have hm1 : (m : G) ≠ 1 := by
    intro h
    apply hc'1
    rw [← hmc]
    have : m = 1 := Subtype.ext h
    rw [this, map_one]
  have hmz : (m : G) = z := (hzu m hmS hcentral hm2).resolve_left hm1
  obtain ⟨u, huM, huS, huz⟩ := hmov
  apply huz
  have hzbar : proj M ⟨z, hSM hzS⟩ = c' := by rw [← hmc]; congr 1; exact Subtype.ext hmz.symm
  have h1 : proj M (⟨u, huM⟩⁻¹ * ⟨z, hSM hzS⟩ * ⟨u, huM⟩) = proj M ⟨z, hSM hzS⟩ := by
    rw [map_mul, map_mul, map_inv, hzbar, hc'comm (proj M ⟨u, huM⟩)⁻¹]
    group
  have := eq_of_proj_eq_of_isPGroup M hSp hSM
    (a := ⟨u, huM⟩⁻¹ * ⟨z, hSM hzS⟩ * ⟨u, huM⟩) (b := ⟨z, hSM hzS⟩) huS hzS h1
  exact congrArg Subtype.val this

end Quot2

section Quot3

variable {G : Type} [Group G] [Finite G] (M : Subgroup G)

omit [Finite G] in
theorem barImage_conj {X : Subgroup G} (m : ↥M) :
    (barImage M X).map (MulAut.conj (proj M m)).toMonoidHom = barImage M (conjSub (m : G) X) := by
  ext y
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨a, haX, rfl⟩ := (mem_barImage M).mp he
    refine (mem_barImage M).mpr ⟨m * a * m⁻¹, ?_, ?_⟩
    · exact mem_conjSub_of_mem haX
    · show proj M m * proj M a * (proj M m)⁻¹ = proj M (m * a * m⁻¹)
      rw [map_mul, map_mul, map_inv]
  · intro hy
    obtain ⟨b, hbX, rfl⟩ := (mem_barImage M).mp hy
    have hb : (m : G)⁻¹ * (b : G) * m ∈ X := mem_conjSub.mp hbX
    refine ⟨proj M (m⁻¹ * b * m), (mem_barImage M).mpr ⟨m⁻¹ * b * m, hb, rfl⟩, ?_⟩
    show proj M m * proj M (m⁻¹ * b * m) * (proj M m)⁻¹ = proj M b
    rw [map_mul, map_mul, map_inv]
    group

theorem exists_conj_of_barImage_eq {X₁ X₂ : Subgroup G} (hX₁ : IsPGroup 2 X₁)
    (hX₂ : IsPGroup 2 X₂) (h₁M : X₁ ≤ M) (h₂M : X₂ ≤ M)
    (h : barImage M X₁ = barImage M X₂) : ∃ c : ↥M, conjSub (c : G) X₁ = X₂ := by
  obtain ⟨c, hc⟩ := exists_conj_of_map_eq (proj M) (odd_card_ker_proj M)
    (isPGroup_subgroupOf M hX₁ h₁M) (isPGroup_subgroupOf M hX₂ h₂M) h
  refine ⟨c, ?_⟩
  have hmem : ∀ (X : Subgroup G) (y : ↥M), y ∈ X.subgroupOf M ↔ (y : G) ∈ X :=
    fun X y => Subgroup.mem_subgroupOf
  ext y
  constructor
  · intro hy
    have hy' : (c : G)⁻¹ * y * c ∈ X₁ := mem_conjSub.mp hy
    have hyM : y ∈ M := by
      have : y = (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ := by group
      rw [this]
      exact M.mul_mem (M.mul_mem c.2 (h₁M hy')) (M.inv_mem c.2)
    have h1 : (⟨y, hyM⟩ : ↥M) ∈ conjSub c (X₁.subgroupOf M) := by
      rw [mem_conjSub]
      exact (hmem X₁ _).mpr (by simpa using hy')
    rw [hc] at h1
    exact (hmem X₂ _).mp h1
  · intro hy
    have hyM : y ∈ M := h₂M hy
    have h1 : (⟨y, hyM⟩ : ↥M) ∈ X₂.subgroupOf M := (hmem X₂ _).mpr hy
    rw [← hc, mem_conjSub] at h1
    have := (hmem X₁ _).mp h1
    rw [mem_conjSub]
    simpa using this

theorem pRank_centralizer_xbar {S V K : Subgroup G} {x z : G} (hxM : x ∈ M) (hx2 : x * x = 1)
    (hsyl : IsSylowIn (centralizer ({x} : Set G) ⊓ M) (centralizer ({x} : Set G) ⊓ S))
    (hV : IsFour M V) (hVgen : V = zpowers x ⊔ zpowers z)
    (hKle : K ≤ centralizer ({x} : Set G) ⊓ S)
    (hKsup : zpowers x ⊔ K = centralizer ({x} : Set G) ⊓ S) (hzK : z ∈ K)
    (hKinv : ∀ k ∈ K, k * k = 1 → k = 1 ∨ k = z) :
    Open.pRank 2 (centralizer ({xbar M x hxM} : Set (Mbar M))) = 2 := by
  have hx'2 : (⟨x, hxM⟩ : ↥M) * ⟨x, hxM⟩ = 1 := Subtype.ext hx2
  have h1 : centralizer ({xbar M x hxM} : Set (Mbar M)) =
      (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)).map (proj M) :=
    centralizer_map_eq (proj M) (proj_surjective M) (odd_card_ker_proj M) hx'2
  have h2 := pRank_map (proj M) (odd_card_ker_proj M)
    (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M))
  have h3 : (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)).map M.subtype =
      centralizer ({x} : Set G) ⊓ M := by
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, m.2⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp hm
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
    · rintro ⟨hy, hyM⟩
      refine ⟨⟨y, hyM⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy))
  have h4 := pRank_map_of_injective M.subtype M.subtype_injective
    (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M))
  rw [h3] at h4
  have h5 := hsyl.pRank_eq
  have hVel := SU1.isElemAbelian_iff.mp hV.2.1
  have hVle : V ≤ centralizer ({x} : Set G) ⊓ S := by
    rw [hVgen, ← hKsup]
    exact sup_le_sup_left (Subgroup.zpowers_le.mpr hzK) _
  have h6 : Open.pRank 2 (centralizer ({x} : Set G) ⊓ S) = 2 := by
    apply le_antisymm
    · refine SU1.pRank_le_of (fun E hE hEel k hk => ?_)
      have hEV : E ≤ V := by
        intro e he
        have heC : e ∈ zpowers x ⊔ K := hKsup ▸ hE he
        obtain ⟨a, ha, k₀, hk₀, hak⟩ := SU1.mem_sup_of_commute (A := zpowers x) (B := K)
          (fun a ha k hk => by
            obtain ⟨j, rfl⟩ := ha
            exact (Commute.zpow_left (show Commute x k from
              (Subgroup.mem_centralizer_singleton_iff.mp (hKle hk).1).symm) j).eq) heC
        have he2 : e * e = 1 := by rw [← pow_two]; exact (SU1.isElemAbelian_iff.mp hEel).2 e he
        have hka : a * k₀ = k₀ * a := by
          obtain ⟨j, rfl⟩ := ha
          exact ((Commute.zpow_left (show Commute x k₀ from
              (Subgroup.mem_centralizer_singleton_iff.mp (hKle hk₀).1).symm) j).eq)
        have ha' := eq_one_or_eq_of_mem_zpowers hx2 ha
        have haa : a * a = 1 := by rcases ha' with h | h <;> rw [h] <;> simp [hx2]
        have hk2 : k₀ * k₀ = 1 := by
          calc k₀ * k₀ = (a * a) * (k₀ * k₀) := by rw [haa, one_mul]
            _ = (a * k₀) * (a * k₀) := by
              calc (a * a) * (k₀ * k₀) = a * (a * k₀) * k₀ := by group
                _ = a * (k₀ * a) * k₀ := by rw [← hka]
                _ = (a * k₀) * (a * k₀) := by group
            _ = 1 := by rw [hak]; exact he2
        have haV : a ∈ V := by
          rw [hVgen]; exact Subgroup.mem_sup_left ha
        have hk₀V : k₀ ∈ V := by
          rcases hKinv k₀ hk₀ hk2 with h | h
          · rw [h]; exact V.one_mem
          · rw [h, hVgen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
        rw [← hak]
        exact V.mul_mem haV hk₀V
      have := Subgroup.card_le_of_le hEV
      rw [hk, hV.2.2] at this
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
    · exact SU1.le_pRank (by norm_num) hVle hV.2.1 hV.2.2
  rw [h1, h2, ← h4, ← h5, h6]

end Quot3

end CFSG.GH74.Uniqueness.SU.SU4
