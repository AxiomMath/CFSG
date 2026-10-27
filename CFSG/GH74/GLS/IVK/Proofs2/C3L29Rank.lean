module

public import CFSG.GH74.GLS.IVK.Proofs2.PglKStab
public import CFSG.GH74.GLS.IVK.Proofs2.Perm4Facts
public import CFSG.GH74.GLS.C3.Layer1.BkIv10
public import CFSG.GH74.GLS.C3.Layer1.St1Thm4

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section S4

variable {K : Type} [Group K] [Finite K]

theorem exists_klein_data_of_equiv_perm4 (hD4 : HasD4Centralizers K) {S : Subgroup K}
    (ρ : ↥S ≃* Equiv.Perm (Fin 4)) :
    ∃ (V₀ : Subgroup K) (u₁ u₂ : K), Nat.card ↥V₀ = 4 ∧ (∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) ∧
      u₁ ∈ V₀ ∧ u₂ ∈ V₀ ∧ orderOf u₁ = 2 ∧ orderOf u₂ = 2 ∧ u₁ ≠ u₂ ∧ u₁ * u₂ = u₂ * u₁ ∧
      centralizer ({u₁} : Set K) ≤ S ∧ centralizer ({u₂} : Set K) ≤ S ∧
      S ≤ normalizer (V₀ : Set K) ∧ Nat.card ↥S = 24 := by
  set ρ' : Equiv.Perm (Fin 4) ≃* ↥S := ρ.symm with hρ'
  set kS : Subgroup ↥S := kleinFour.map ρ'.toMonoidHom with hkS
  set V₀ : Subgroup K := kS.map S.subtype with hV₀
  have hmem : ∀ k : K, k ∈ V₀ ↔ ∃ a ∈ kleinFour, ((ρ' a : ↥S) : K) = k := by
    intro k
    constructor
    · rintro ⟨s, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ρ' a, ⟨a, ha, rfl⟩, rfl⟩
  have hordA : orderOf kleinA = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact kleinA_mul_self) kleinA_ne_one
  have hordB : orderOf kleinB = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact kleinB_mul_self) kleinB_ne_one
  have hordA' : orderOf ((ρ' kleinA : ↥S) : K) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hordA
  have hordB' : orderOf ((ρ' kleinB : ↥S) : K) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hordB
  have hc : ∀ g h : Equiv.Perm (Fin 4), ((ρ' g : ↥S) : K) * ((ρ' h : ↥S) : K) =
      ((ρ' (g * h) : ↥S) : K) := fun g h => by
    rw [map_mul]
    rfl
  have hcent : ∀ (a : Equiv.Perm (Fin 4)) (u : K), u = ((ρ' a : ↥S) : K) → orderOf u = 2 →
      Nat.card ↥(Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin 4)))) = 8 →
      centralizer ({u} : Set K) ≤ S := by
    intro a u hu hu2 hcard
    set C' : Subgroup K := ((Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin 4)))).map
      ρ'.toMonoidHom).map S.subtype with hC'
    have hC'card : Nat.card ↥C' = 8 := by
      rw [hC', Subgroup.card_map_of_injective S.subtype_injective,
        Subgroup.card_map_of_injective ρ'.injective, hcard]
    have hle : C' ≤ centralizer ({u} : Set K) := by
      rintro _ ⟨s, ⟨g, hg, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff, hu]
      have hg' : g * a = a * g := mem_centralizer_singleton_iff.1 hg
      show ((ρ' g : ↥S) : K) * ((ρ' a : ↥S) : K) = ((ρ' a : ↥S) : K) * ((ρ' g : ↥S) : K)
      rw [hc, hc, hg']
    have heq : C' = centralizer ({u} : Set K) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hC'card, card_centralizer_of_d4 hD4 hu2])
    rw [← heq]
    exact Subgroup.map_subtype_le _
  refine ⟨V₀, ((ρ' kleinA : ↥S) : K), ((ρ' kleinB : ↥S) : K), ?_, ?_, ?_, ?_, hordA', hordB', ?_,
    ?_, hcent kleinA _ rfl hordA' card_centralizer_kleinA,
    hcent kleinB _ rfl hordB' card_centralizer_kleinB, ?_, ?_⟩
  · rw [hV₀, Subgroup.card_map_of_injective S.subtype_injective, hkS,
      Subgroup.card_map_of_injective ρ'.injective, card_kleinFour]
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := (hmem a).1 ha
    obtain ⟨b', hb', rfl⟩ := (hmem b).1 hb
    rw [hc, hc, kleinFour_comm a' ha' b' hb']
  · exact (hmem _).2 ⟨kleinA, kleinA_mem, rfl⟩
  · exact (hmem _).2 ⟨kleinB, kleinB_mem, rfl⟩
  · intro h
    exact kleinA_ne_kleinB (ρ'.injective (Subtype.ext h))
  · rw [hc, hc, kleinFour_comm kleinA kleinA_mem kleinB kleinB_mem]
  · intro s hs
    have hfwd : ∀ t : ↥S, ∀ k ∈ V₀, (t : K) * k * (t : K)⁻¹ ∈ V₀ := by
      intro t k hk
      obtain ⟨a, ha, rfl⟩ := (hmem k).1 hk
      refine (hmem _).2 ⟨ρ t * a * (ρ t)⁻¹, conj_mem_kleinFour _ ha, ?_⟩
      have : ρ' (ρ t * a * (ρ t)⁻¹) = t * ρ' a * t⁻¹ := by
        simp [hρ']
      rw [this]
      rfl
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hfwd ⟨s, hs⟩ k hk, fun hk => ?_⟩
    have := hfwd ⟨s, hs⟩⁻¹ _ hk
    simpa [mul_assoc] using this
  · rw [Nat.card_congr ρ.toEquiv, card_perm_four]

end S4

section Rank

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem mem_innDiagSub_of_isPGL2 (hF : L2Field F) (hfm : IsFM9 (Nat.card F)) (e : K ≃* L2 F)
    (N : L2Notation e) {y : MulAut K} (hy2 : y ^ 2 = 1) (hyInn : y ∉ innAut K)
    (hPGL : IsPGL2 ↥((MulAut.conj : K →* MulAut K).range ⊔ zpowers y)
      (fun r => r = Nat.card F)) : y ∈ innDiagSub e := by
  have hinj := conj_injective_of_L2 e
  by_contra hyD
  obtain ⟨h9, ⟨ρ⟩⟩ := exists_equiv_perm4_fixedSubgroup hF hfm e N hy2 hyD
  have hc3 : orderOf (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) = 3 :=
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    orderOf_eq_prime (by decide) (by decide)
  set c : ↥(fixedSubgroup K y) := ρ.symm (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) with hc
  have hk3 : orderOf (c : K) = 3 := by
    rw [Subgroup.orderOf_coe, hc, MulEquiv.orderOf_eq]
    exact hc3
  have hyk : y (c : K) = c := c.2
  obtain ⟨F₀, _, _, hF₀, ⟨ψ⟩⟩ := hPGL
  have hF₀9 : Nat.card F₀ = 9 := hF₀.trans h9
  let tX : ↥((MulAut.conj : K →* MulAut K).range ⊔ zpowers y) :=
    ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩
  let uX : ↥((MulAut.conj : K →* MulAut K).range ⊔ zpowers y) :=
    ⟨MulAut.conj (c : K), Subgroup.mem_sup_left ⟨c, rfl⟩⟩
  have hyne : y ≠ 1 := fun h => hyInn (by rw [h]; exact one_mem _)
  have htX : orderOf tX = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hy2 hyne
  have huX : orderOf uX = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_injective _ hinj (c : K)).trans hk3
  have hcomm : tX * uX = uX * tX := by
    apply Subtype.ext
    have h1 : y * MulAut.conj (c : K) * y⁻¹ = MulAut.conj (c : K) := by
      rw [mul_conj_mul_inv, hyk]
    calc y * MulAut.conj (c : K) = (y * MulAut.conj (c : K) * y⁻¹) * y := by group
      _ = MulAut.conj (c : K) * y := by rw [h1]
  refine pgl2_nine_no_order_six hF₀9 (t := ψ tX) (u := ψ uX) ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact htX
  · rw [MulEquiv.orderOf_eq]
    exact huX
  · rw [← map_mul, ← map_mul, hcomm]

theorem card_le_four_of_elementary_abelian (hF : L2Field F) (h9 : Nat.card F = 9) (e : K ≃* L2 F)
    (N : L2Notation e) {y : MulAut K} (hy2 : y ^ 2 = 1) (hyD : y ∈ innDiagSub e)
    (hyInn : y ∉ innAut K) {E : Subgroup (MulAut K)} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) (hyE : y ∈ E) : Nat.card ↥E ≤ 4 := by
  have hfm : IsFM9 (Nat.card F) := Or.inl h9
  have hq : Nat.card F = 7 ∨ Nat.card F = 9 := Or.inr h9
  by_cases hEX : E ≤ innDiagSub e
  ·
    have hyne : y ≠ 1 := fun h => hyInn (by rw [h]; exact one_mem _)
    have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hyne
    obtain ⟨⟨k, hk, -, ⟨ψ⟩⟩, -⟩ := ivk_1_3b F hF K e 1 (Or.inl rfl)
      (by rw [h9]; unfold Int.ModEq; norm_num) 10 (by rw [h9]; norm_num) y hyD hyInn hyo
    have hQ20 : Nat.card ↥(centralizer ({y} : Set (MulAut K)) ⊓ innDiagSub e) = 20 := by
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
      omega
    have hEQ : E ≤ centralizer ({y} : Set (MulAut K)) ⊓ innDiagSub e := fun a ha =>
      ⟨mem_centralizer_singleton_iff.2 (hcomm a ha y hyE), hEX ha⟩
    have hpg : IsPGroup 2 ↥E := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hsq g g.2⟩
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    have hdvd : 2 ^ n ∣ 20 := hn ▸ hQ20 ▸ Subgroup.card_dvd_of_le hEQ
    rw [hn]
    by_contra hlt
    have hn3 : 3 ≤ n := by
      by_contra h3
      apply hlt
      interval_cases n <;> norm_num
    have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 hn3
    have h8 : 8 ∣ 20 := by simpa using this.trans hdvd
    omega
  ·
    exfalso
    obtain ⟨f', hf'E, hf'X⟩ := IsConcreteLE.not_le_iff_exists.1 hEX
    obtain ⟨-, ⟨ρ⟩⟩ := exists_equiv_perm4_fixedSubgroup hF hfm e N (hsq f' hf'E) hf'X
    have hD4 : HasD4Centralizers K := fun u hu => (centralizer_dih_of_seven_nine hF hq e hu).1
    have hQ8 : ∀ u : K, orderOf u = 2 → Nonempty (↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓
        innDiagSub e) ≃* DihedralGroup 8) := fun u hu => (centralizer_dih_of_seven_nine hF hq e hu).2
    obtain ⟨V₀, u₁, u₂, hV₀4, hV₀comm, hu₁, hu₂, h₁, h₂, hu₁₂, hcomm12, hΓ1, hΓ2, hΓN, hΓ24⟩ :=
      exists_klein_data_of_equiv_perm4 hD4 ρ
    have hmaps : ∀ k ∈ fixedSubgroup K f', y k ∈ fixedSubgroup K f' := by
      intro k hk
      have hk' : f' k = k := hk
      have hcy : f' * y = y * f' := hcomm f' hf'E y hyE
      show f' (y k) = y k
      calc f' (y k) = (f' * y) k := rfl
        _ = (y * f') k := by rw [hcy]
        _ = y k := by
          show y (f' k) = y k
          rw [hk']
    exact hyInn (mem_innAut_of_maps_gamma e hD4 hQ8 hV₀4 hV₀comm hu₁ hu₂ h₁ h₂ hu₁₂ hcomm12 hΓ1 hΓ2
      hΓN hΓ24 hyD hmaps)

end Rank

section GLevel

theorem card_le_four_mul_inf_CxK_of_unbalancingTriple
    {G : Type} [Group G] [Finite G] {x y : G} {K : Subgroup G}
    (hunb : IsUnbalancingTriple x y K)
    (hL2 : HasL2Model (kBar K) (fun q => q = 9))
    (A : Subgroup G) (hAN : A ≤ NxK x K)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hyA : y ∈ A) :
    Nat.card ↥A ≤ 4 * Nat.card ↥(A ⊓ CxK x K) := by
  have hlu := hunb.isLocallyUnbalancing
  have hyN : y ∈ normalizer (K : Set G) := hlu.2.2.2.1
  have hLn := CFSG.GH74.GLS.C3.Layer1.Bk.hLn_normalizer K
  obtain ⟨p, f, hp, hf, hq9, hLie⟩ := hL2
  have hq9' : p ^ f = 9 := hq9
  have hfm9 : IsFM9 (p ^ f) := by
    rw [hq9']
    exact Or.inl rfl
  have hL2' : HasL2Model (kBar K) (fun r => r = p ^ f) := ⟨p, f, hp, hf, rfl, hLie⟩
  obtain ⟨hnotInn, hPGL⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.ivk10_bridge b_ivk_10_2L hlu hfm9 hL2'
  set yb : MulAut (kBar K) := CFSG.GH74.GLS.C3.Layer1.Back.actHom hLn ⟨y, hyN⟩ with hyb
  have hyb2 : yb ^ 2 = 1 := by
    rw [hyb, ← map_pow]
    have : (⟨y, hyN⟩ : ↥(normalizer (K : Set G))) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hlu.2.1]
      exact pow_orderOf_eq_one y
    rw [this, map_one]
  obtain ⟨F, _, _, e0, hF, hFq⟩ := exists_l2Field_of_hasL2Model hfm9 hL2'
  have hFq' : Nat.card F = 9 := hFq.trans hq9'
  have hfmF : IsFM9 (Nat.card F) := Or.inl hFq'
  obtain ⟨e, N, -⟩ :=
    ivk_1_2a_exists F hF (kBar K) e0 (inferInstance : Nonempty (Sylow 2 (MulAut (kBar K)))).some
  have hPGL' : IsPGL2 ↥((MulAut.conj : kBar K →* MulAut (kBar K)).range ⊔ zpowers yb)
      (fun r => r = Nat.card F) := by
    obtain ⟨F₀, i1, i2, hF₀, ⟨ψ⟩⟩ := hPGL
    exact ⟨F₀, i1, i2, hF₀.trans hFq.symm, ⟨ψ⟩⟩
  have hybD : yb ∈ innDiagSub e := mem_innDiagSub_of_isPGL2 hF hfmF e N hyb2 hnotInn hPGL'
  have hAM : A ≤ normalizer (K : Set G) := hAN.trans inf_le_right
  let αA : ↥A →* MulAut (kBar K) :=
    (CFSG.GH74.GLS.C3.Layer1.Back.actHom hLn).comp (Subgroup.inclusion hAM)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
  have hAsq : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => by
    have := hAel
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hEcomm : ∀ a ∈ αA.range, ∀ b ∈ αA.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hab : a * b = b * a := Subtype.ext (hAcomm a a.2 b b.2)
    rw [← map_mul, ← map_mul, hab]
  have hEsq : ∀ a ∈ αA.range, a ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hAsq a a.2)
    rw [this, map_one]
  have hybE : yb ∈ αA.range := ⟨⟨y, hyA⟩, rfl⟩
  have hE4 : Nat.card ↥αA.range ≤ 4 :=
    card_le_four_of_elementary_abelian hF hFq' e N hyb2 hybD hnotInn hEcomm hEsq hybE
  have hker : αA.ker = (A ⊓ CxK x K).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hax : (a : G) ∈ centralizer ({x} : Set G) := (hAN a.2).1
    have hkey := CFSG.GH74.GLS.C3.Layer1.Back.actHom_eq_one_iff_commutator_mem hLn
      ⟨(a : G), hAM a.2⟩
    constructor
    · intro h
      refine ⟨a.2, hax, hAM a.2, TwoThin.mem_normalizer_pPrimeCoreOf (hAM a.2),
        fun k hk => hkey.1 h k hk⟩
    · rintro ⟨-, -, -, -, h⟩
      exact hkey.2 h
  have hcard := Subgroup.card_ker_mul_card_range αA
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : A ⊓ CxK x K ≤ A)).toEquiv] at hcard
  calc Nat.card ↥A = Nat.card ↥(A ⊓ CxK x K) * Nat.card ↥αA.range := hcard.symm
    _ ≤ Nat.card ↥(A ⊓ CxK x K) * 4 := Nat.mul_le_mul_left _ hE4
    _ = 4 * Nat.card ↥(A ⊓ CxK x K) := mul_comm _ _


theorem b_ivk_L29_rank
    : CFSG.GH74.GLS.B_ivk_L29_rank := by
  intro G _ _ _ x y K hunb hL2 A hAN hAel hyA
  exact card_le_four_mul_inf_CxK_of_unbalancingTriple hunb hL2 A hAN hAel hyA

end GLevel

end CFSG.GH74.GLS.IVK.Proofs2
