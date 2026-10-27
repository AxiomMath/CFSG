module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.RowL3E8Act

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Std

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {z j : G} (h : Std Ω K J z j)
include h

variable {K' : Subgroup G} {u v s : G}

theorem index_centralizer (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) :
    (Subgroup.centralizer ({z} : Set G)).index = 7 := by
  classical
  have h8 := h.card_eGrp_K d hs
  have hcls : (ConjClasses.mk z).carrier = (eGrp Ω z K : Set G) \ {1} := by
    ext x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    constructor
    · rintro ⟨c, hc⟩
      have hx : x = c⁻¹ * z * c⁻¹⁻¹ := by rw [← hc]; group
      refine ⟨hx ▸ h.conj_mem_eGrp h8 c⁻¹, fun h1 => h.hz.ne_one ?_⟩
      have h1' : x = 1 := h1
      rw [← hc, h1']
      group
    · rintro ⟨hxE, hx1⟩
      obtain ⟨g, hg⟩ := h.exists_conj_of_mem_eGrp d hs hxE hx1
      exact ⟨g⁻¹, by rw [← hg]; group⟩
  have h1 := CFSG.GorensteinWalter.card_conjClass_eq_centralizer_index_local z
  have hsub1 : ({1} : Set G) ⊆ eGrp Ω z K := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.one_mem _
  have hEcard : (eGrp Ω z K : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h8]
  have h7 : Nat.card ↑((eGrp Ω z K : Set G) \ {1}) = 7 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff hsub1, hEcard, Set.ncard_singleton]
  rw [hcls, h7] at h1
  exact h1.symm

theorem card_map_Y (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {Θ : G →* L3Two}
    (hΘ : ∀ x : G, Θ x = 1 ↔ x ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) :
    Nat.card ((pairNormalizers K J z j).map Θ) = 24 := by
  set Y := pairNormalizers K J z j with hY
  have h8 := h.card_eGrp_K d hs
  obtain ⟨hEle, -, -⟩ := h.eGrp_facts d hs
  have hker : Θ.ker ⊓ Y = eGrp Ω z K := by
    refine le_antisymm (fun x hx => h.le_eGrp_of_centralizer d hs ⟨hx.2, (hΘ x).mp hx.1⟩)
      (le_inf (fun x hx => (hΘ x).mpr (Subgroup.mem_centralizer_iff.mpr fun e he =>
        h.eGrp_comm K e he x hx)) (hEle.trans inf_le_left))
  have h1 := Subgroup.card_mul_index (Θ.domRestrict Y).ker
  rw [Subgroup.index_ker, MonoidHom.restrict_range Y Θ, MonoidHom.ker_restrict] at h1
  have h2 : Nat.card ↥(Θ.ker.subgroupOf Y) = 8 := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, Subgroup.subgroupOf_map_subtype,
      hker, h8]
  rw [h2, d.card_Y] at h1
  omega

theorem surjective_action (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {Θ : G →* L3Two}
    (hΘ : ∀ x : G, Θ x = 1 ↔ x ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) :
    Function.Surjective Θ := by
  have hker : Θ.ker = Subgroup.centralizer (eGrp Ω z K : Set G) := by
    ext x
    exact hΘ x
  have h1 := Subgroup.card_mul_index Θ.ker
  rw [Subgroup.index_ker, hker] at h1
  obtain ⟨k, hk⟩ := (h.isPGroup_centralizer d hs).exists_card_eq
  have h7 := Subgroup.card_mul_index (Subgroup.centralizer ({z} : Set G))
  rw [h.index_centralizer d hs] at h7
  have hd7 : 7 ∣ 2 ^ k * Nat.card Θ.range := by
    rw [← hk, h1, ← h7]
    exact Dvd.intro_left _ rfl
  have hd7' : 7 ∣ Nat.card Θ.range :=
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 7 2)).dvd_of_dvd_mul_left hd7
  have hd24 : 24 ∣ Nat.card Θ.range := by
    rw [← h.card_map_Y d hs hΘ]
    exact Subgroup.card_dvd_of_le (Subgroup.map_le_range Θ _)
  have hd168 : 168 ∣ Nat.card Θ.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 24) hd7' hd24
  have hle : Nat.card Θ.range ≤ 168 := l3Two_card' ▸ Subgroup.card_le_card_group _
  have hpos : 0 < Nat.card Θ.range := Nat.card_pos
  have heq : Nat.card Θ.range = 168 := by
    obtain ⟨c, hc⟩ := hd168
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ (heq.trans l3Two_card'.symm))

theorem action_ne_one (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {Θ : G →* L3Two}
    (hΘ : ∀ x : G, Θ x = 1 ↔ x ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) {x : G}
    (hx : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) (hxx : x * x = z) : Θ x ≠ 1 := by
  obtain ⟨hEle, hsE, hsX⟩ := h.eGrp_facts d hs
  intro h1
  have h2 := Subgroup.mem_centralizer_iff.mp ((hΘ x).mp h1) s hsE
  have h3 := d.conj_of_not_mem (hEle hsE).1 (hEle hsE).2 hsX hx
  rw [hxx] at h3
  have h4 : x * s * x⁻¹ = s := by rw [← h2]; group
  rw [h4] at h3
  apply h.hz.ne_one
  calc z = z * s * s⁻¹ := by group
    _ = 1 := by rw [← h3, mul_inv_cancel]

theorem not_comm_of_three (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {Θ : G →* L3Two}
    (hΘ : ∀ x : G, Θ x = 1 ↔ x ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) {x y : G}
    (hx : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) (hxx : x * x = z) (hy : orderOf y = 3)
    (hxy : x * y = y * x) : False := by
  have h8 := h.card_eGrp_K d hs
  have hz1 : Θ z = 1 := (hΘ z).mpr (Subgroup.mem_centralizer_iff.mpr fun e he =>
    h.eGrp_comm K e he z (h.mem_eGrp_self h.hK h.hz))
  have hΘx : Θ x * Θ x = 1 := by rw [← map_mul, hxx, hz1]
  have hΘy := l3Two_centralizer_exp (Θ x) (Θ y) hΘx (h.action_ne_one d hs hΘ hx hxx)
    (by rw [← map_mul, hxy, map_mul])
  have hy3' : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy3 : Θ y ^ 3 = 1 := by rw [← map_pow, hy3', map_one]
  have hy1 : Θ y = 1 := by
    calc Θ y = Θ y ^ 4 * (Θ y ^ 3)⁻¹ := by group
      _ = 1 := by rw [hΘy, hy3]; group
  have hyA := (hΘ y).mp hy1
  obtain ⟨k, hk⟩ := (h.isPGroup_centralizer d hs) ⟨y, hyA⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := hy ▸ orderOf_dvd_of_pow_eq_one hk'
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem exists_three (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {Θ : G →* L3Two}
    (hΘ : ∀ x : G, Θ x = 1 ↔ x ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) :
    ∃ y : G, orderOf y = 3 ∧ y ∈ Subgroup.normalizer (K : Set G) ∧
      y ∈ Subgroup.normalizer (K' : Set G) ∧ (¬ ∀ k ∈ K, y * k = k * y) ∧
      ¬ ∀ k ∈ K', y * k = k * y := by
  have hsurj := h.surjective_action d hs hΘ
  have hker : Θ.ker = Subgroup.centralizer (eGrp Ω z K : Set G) := by
    ext x
    exact hΘ x
  have h1 := Subgroup.card_mul_index Θ.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, l3Two_card',
    hker] at h1
  have h7 := Subgroup.card_mul_index (Subgroup.centralizer ({z} : Set G))
  rw [h.index_centralizer d hs] at h7
  have h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := by omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyz : (y : G) * z * (y : G)⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp y.2]
    group
  have hyyy : (y : G) * (y : G) * (y : G) = 1 := by
    have h3' : (y : G) ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one _
    rwa [pow_three'] at h3'
  have htw : twinSet Ω K = {K, K'} := d.tor.htw
  have hK'K : K' ≠ K := d.tor.hne
  have hmem : ∀ L ∈ twinSet Ω K, conjSub (y : G) L ∈ twinSet Ω K := by
    intro L hL
    obtain ⟨hLΩ, w, hwK, hwL⟩ := hL
    refine ⟨h.hΩ.hyp.conjInvariant _ L hLΩ, z, h.hz, ?_⟩
    have h2 := hwL.conj (y : G)
    rwa [← h.hz.eq hwK, hyz] at h2
  have hKtw : K ∈ twinSet Ω K := by rw [htw]; exact Or.inl rfl
  have hK'tw : K' ∈ twinSet Ω K := by rw [htw]; exact Or.inr rfl
  have hfix : conjSub (y : G) K = K ∧ conjSub (y : G) K' = K' := by
    have hyK := hmem K hKtw
    have hyK' := hmem K' hK'tw
    rw [htw] at hyK hyK'
    have hcube : ∀ L, conjSub ((y : G) * (y : G) * (y : G)) L = L := by
      intro L
      rw [hyyy, conjSub_one]
    rcases hyK with hyK | hyK <;> rcases hyK' with hyK' | hyK'
    · exact absurd (conjSub_injective _ (hyK.trans hyK'.symm)) hK'K.symm
    · exact ⟨hyK, hyK'⟩
    · exfalso
      have := hcube K
      rw [conjSub_mul, conjSub_mul, hyK, hyK', hyK] at this
      exact hK'K this
    · exact absurd (conjSub_injective _ (hyK.trans hyK'.symm)) hK'K.symm
  refine ⟨y, hy3, mem_normalizer_iff_conjSub_eq.mpr hfix.1,
    mem_normalizer_iff_conjSub_eq.mpr hfix.2, fun hc => ?_, fun hc => ?_⟩
  · exact h.not_comm_of_three d hs hΘ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u)) d.u_sq hy3
      (hc u (d.tor.hUK (Subgroup.mem_zpowers u))).symm
  · obtain ⟨u', hu', hu'U, hUV⟩ := d.tor.hU'
    have hu'K : u' ∈ K' := (hu' ▸ Subgroup.mem_zpowers u' : u' ∈ K' ⊓ _).1
    have hu'X : u' ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
      rw [hUV]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u')
    have hu'u' : u' * u' = z :=
      mul_self_eq_involution_of_orderOf_four d.hzK' hu'K
        (by rw [← Nat.card_zpowers, card_of_mem_USet h.hΩ hu'U])
    exact h.not_comm_of_three d hs hΘ hu'X hu'u' hy3 (hc u' hu'K).symm

theorem card_sylow_Y (d : LJ Ω K J K' z j u v) {T : Subgroup G}
    (hT : IsSylow2In T (pairNormalizers K J z j)) : Nat.card T = 64 := by
  have h1 := Subgroup.card_mul_index (T.subgroupOf (pairNormalizers K J z j))
  rw [d.card_Y] at h1
  have h2 : Nat.card ↥(T.subgroupOf (pairNormalizers K J z j)) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
  rw [h2] at h1
  have hodd : ¬ 2 ∣ (T.subgroupOf (pairNormalizers K J z j)).index :=
    Sylow.not_dvd_index (AscQuot.sylowOfIsSylow2In' hT)
  obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
  rw [hk] at h1 ⊢
  have hk8 : k < 8 := by
    by_contra hk8
    have h3 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 0 < (T.subgroupOf (pairNormalizers K J z j)).index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have h5 : 2 ^ k ≤ 192 := by
      calc 2 ^ k ≤ 2 ^ k * (T.subgroupOf (pairNormalizers K J z j)).index :=
            Nat.le_mul_of_pos_right _ h4
        _ = 192 := h1
    omega
  interval_cases k <;> norm_num at h1 ⊢ <;> omega

theorem centralizer_le_eGrp (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {Θ : G →* L3Two}
    (hΘ : ∀ x : G, Θ x = 1 ↔ x ∈ Subgroup.centralizer (eGrp Ω z K : Set G)) :
    Subgroup.centralizer (eGrp Ω z K : Set G) ≤ eGrp Ω z K := by
  have h8 := h.card_eGrp_K d hs
  haveI hEn := h.eGrp_normal h8
  set E := eGrp Ω z K with hE
  set A := Subgroup.centralizer (E : Set G) with hA
  haveI hAn : A.Normal := inferInstance
  set Y := pairNormalizers K J z j with hY
  have hsurj := h.surjective_action d hs hΘ
  have hA2 := h.isPGroup_centralizer d hs
  have hker : Θ.ker = A := by
    ext x
    exact hΘ x
  have hG : Nat.card A * 168 = Nat.card G := by
    have h1 := Subgroup.card_mul_index Θ.ker
    rwa [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, l3Two_card',
      hker] at h1
  have hEA : E ≤ A := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun e he => h.eGrp_comm K e he x hx
  obtain ⟨hEle, -, -⟩ := h.eGrp_facts d hs
  have hEY : E ≤ Y := hEle.trans inf_le_left
  have hYA : Y ⊓ A ≤ E := h.le_eGrp_of_centralizer d hs
  have hE2 : IsPGroup 2 E := hA2.to_le hEA
  obtain ⟨T, hT, hET⟩ := IsSylow2In.exists_ge hE2 hEY
  have hT64 := h.card_sylow_Y d hT
  have hTA : T ⊓ A = E := le_antisymm ((inf_le_inf_right A hT.1).trans hYA) (le_inf hET hEA)
  have hH₀ : Nat.card ↥(T ⊔ A) * Nat.card E = Nat.card T * Nat.card A := by
    have h1 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := T) (B := A)
      (Subgroup.le_normalizer_of_normal (H := A))
    rwa [hTA] at h1
  have hidx : (T ⊔ A).index = 21 := by
    rw [h8, hT64] at hH₀
    have h1 := Subgroup.card_mul_index (T ⊔ A)
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h2 : Nat.card ↥(T ⊔ A) = 8 * Nat.card A := by omega
    rw [h2, ← hG] at h1
    have h3 : 8 * Nat.card A * (T ⊔ A).index = 8 * Nat.card A * 21 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  set π := QuotientGroup.mk' E with hπ
  set B := T.map π with hB
  set Zb := A.map π with hZb
  haveI hZbn : Zb.Normal := Subgroup.Normal.map hAn π (QuotientGroup.mk'_surjective E)
  have hZc : Zb ≤ Subgroup.center (G ⧸ E) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro gb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E gb
    have h1 : π (g * a * g⁻¹ * a⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h.comm_mem_eGrp' d hs g ha)
    simp only [map_mul, map_inv] at h1
    calc π g * π a = (π g * π a * (π g)⁻¹ * (π a)⁻¹) * (π a * π g) := by group
      _ = π a * π g := by rw [h1, one_mul]
  set H := B ⊔ Zb with hH
  have hHidx : H.index = 21 := by
    have hHmap : H = (T ⊔ A).map π := by rw [hH, hB, hZb, Subgroup.map_sup]
    have hcomap : ((T ⊔ A).map π).comap π = T ⊔ A := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr (hEA.trans le_sup_right)
    rw [hHmap, ← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective E), hcomap,
      hidx]
  have hBZ : B ⊓ Zb = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨⟨t, ht, rfl⟩, ⟨a, ha, hta⟩⟩
    rw [Subgroup.mem_bot]
    have h1 : a⁻¹ * t ∈ E := QuotientGroup.eq.mp hta
    have htA : t ∈ A := by
      have : t = a * (a⁻¹ * t) := by group
      rw [this]
      exact A.mul_mem ha (hEA h1)
    have htE : t ∈ E := hTA ▸ ⟨ht, htA⟩
    exact (QuotientGroup.eq_one_iff t).mpr htE
  have hcommB : commutator ↥H ≤ B.subgroupOf H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro h₁ _ h₂ _
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨b₁, hb₁, c₁, hc₁, he₁⟩ := Subgroup.mem_sup_of_normal_right.mp h₁.2
    obtain ⟨b₂, hb₂, c₂, hc₂, he₂⟩ := Subgroup.mem_sup_of_normal_right.mp h₂.2
    have : ((⁅h₁, h₂⁆ : ↥H) : G ⧸ E) = ⁅(h₁ : G ⧸ E), (h₂ : G ⧸ E)⁆ := by
      simp [commutatorElement_def]
    rw [this, ← he₁, ← he₂, TC.Thin.commutatorElement_mul_central (hZc hc₁) (hZc hc₂),
      commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)
  have hZ2 : IsPGroup 2 Zb := hA2.map π
  set τ : (G ⧸ E) →* Abelianization ↥H :=
    (Abelianization.of : ↥H →* Abelianization ↥H).transfer with hτ
  have hτZ : ∀ c ∈ Zb, τ c = 1 → c = 1 := by
    intro c hc hτc
    have hkey : ∀ (k : ℕ) (g₀ : G ⧸ E), g₀⁻¹ * c ^ k * g₀ ∈ H → g₀⁻¹ * c ^ k * g₀ = c ^ k := by
      intro k g₀ _
      have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ (hZc hc) k) g₀
      rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 := MonoidHom.transfer_eq_pow (Abelianization.of : ↥H →* Abelianization ↥H) c hkey
    rw [← hτ, hτc] at h1
    have hmem : c ^ H.index ∈ H := MonoidHom.transfer_eq_pow_aux c hkey
    have h2 : (⟨c ^ H.index, hmem⟩ : ↥H) ∈ commutator ↥H := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h1.symm
    have h3 : c ^ 21 ∈ B := by
      have h' : c ^ H.index ∈ B := Subgroup.mem_subgroupOf.mp (hcommB h2)
      rwa [hHidx] at h'
    have h4 : c ^ 21 ∈ B ⊓ Zb := ⟨h3, Subgroup.pow_mem _ hc 21⟩
    rw [hBZ, Subgroup.mem_bot] at h4
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ2 ⟨c, hc⟩
    rw [Subgroup.orderOf_mk] at hk
    have h5 : orderOf c ∣ 21 := orderOf_dvd_of_pow_eq_one h4
    rw [hk] at h5
    have h6 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 21)) h5
    rw [h6] at hk
    exact orderOf_eq_one_iff.mp hk
  obtain ⟨y, hy3, hyK, hyK', hycK, hycK'⟩ := h.exists_three d hs hΘ
  have hy3' : ∀ k : G, y ^ 3 * k = k * y ^ 3 := by
    intro k
    rw [← hy3, pow_orderOf_eq_one, one_mul, mul_one]
  have hKker : K ≤ (τ.comp π).ker :=
    TC.Thin.le_ker_of_three (τ.comp π) (Sec6Gen.isQuatSub_of_mem_RSet h.hΩ.hyp (h.mem_RSet h.hK))
      (h.card_eq_eight h.hK) h.hz hyK (fun k _ => hy3' k) hycK
  have hK'ker : K' ≤ (τ.comp π).ker :=
    TC.Thin.le_ker_of_three (τ.comp π)
      (Sec6Gen.isQuatSub_of_mem_RSet h.hΩ.hyp (h.mem_RSet d.tor.hK'))
      (h.card_eq_eight d.tor.hK') d.hzK' hyK' (fun k _ => hy3' k) hycK'
  have hall : ∀ M ∈ Ω, M ≤ (τ.comp π).ker := by
    intro M hM
    obtain ⟨g, hg⟩ := h.exists_conjSub hM
    have hL : conjSub g⁻¹ M ≤ (τ.comp π).ker := by
      rw [d.tor.htw] at hg
      rcases hg with hg | hg
      · rw [hg]
        exact hKker
      · rw [hg]
        exact hK'ker
    intro x hx
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ conjSub g⁻¹ M := conj_mem_conjSub hx
    have h1 := (MonoidHom.normal_ker (τ.comp π)).conj_mem _ (hL hx') g
    simpa [mul_assoc] using h1
  have htop : (⊤ : Subgroup G) ≤ (τ.comp π).ker := by
    rw [← h.hgen]
    exact iSup₂_le hall
  intro a ha
  have h1 : τ (π a) = 1 := htop (Subgroup.mem_top a)
  exact (QuotientGroup.eq_one_iff a).mp (hτZ (π a) ⟨a, ha, rfl⟩ h1)

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isL3E8_of_e8 (hΩ : TypeRHyp Ω) (hO : classicalInvolutionOddCore G = ⊥)
    {K J : Subgroup G} (hK : K ∈ Ω) {z j s : G} (hz : IsUniqueInvolution K z)
    (hzO : TightInO2 z) (hv : AViol Ω K J z j) (hall : aStar Ω K = Ω) (hgen : omegaGen Ω = ⊤)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) :
    IsL3E8 G := by
  have h : Std Ω K J z j := ⟨hΩ, hO, hK, hz, hzO, hv, hall, hgen⟩
  obtain ⟨K', u, v, d⟩ := exists_LJ hΩ hK hv.mem (WR1.inA_of_aViol hv) hz hv.hzJ
    (fun L hL => h.isPGroup hL)
  have h8 := h.card_eGrp_K d hs
  haveI hEn := h.eGrp_normal h8
  obtain ⟨Θ, hΘ⟩ := exists_action_e8 (eGrp Ω z K) (h.eGrp_comm K) (h.eGrp_sq K) h8
  have hsurj := h.surjective_action d hs hΘ
  have hAE := h.centralizer_le_eGrp d hs hΘ
  have hker : Θ.ker = eGrp Ω z K := by
    ext x
    rw [MonoidHom.mem_ker, hΘ x]
    exact ⟨fun hx => hAE hx, fun hx => Subgroup.mem_centralizer_iff.mpr fun e he =>
      h.eGrp_comm K e he x hx⟩
  refine ⟨eGrp Ω z K, hEn, ⟨⟨⟨fun a b => Subtype.ext (h.eGrp_comm K a a.2 b b.2)⟩⟩,
    fun x hx => by rw [pow_two]; exact h.eGrp_sq K x hx⟩, h8, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
