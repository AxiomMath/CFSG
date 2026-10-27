module

public import CFSG.ClassicalInvolution.Asc77.AscC25V24
public import CFSG.ClassicalInvolution.Asc77.AscC25V21
public import CFSG.ClassicalInvolution.AschTight.S19MSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Basic

variable {G : Type} [Group G] {K : Subgroup G} {a : G}

abbrev cLoc (K : Subgroup G) (a : G) : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
  (K ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (Subgroup.centralizer ({a} : Set G))

theorem map_conjSub_cLoc (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    (conjSub c (cLoc K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub (c : G) K ⊓ Subgroup.centralizer ({a} : Set G) := by
  rw [conjSub_subgroupOf, Subgroup.subgroupOf_map_subtype]
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj (c : G)).injective]
  change conjSub (c : G) K ⊓ conjSub (c : G) (Subgroup.centralizer ({a} : Set G)) ⊓
    Subgroup.centralizer ({a} : Set G) = _
  rw [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer c.2)]
  rw [inf_assoc, inf_idem]

theorem conjSub_cLoc_eq {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub (c₁ : G) K = conjSub (c₂ : G) K) :
    conjSub c₁ (cLoc K a) = conjSub c₂ (cLoc K a) := by
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [map_conjSub_cLoc, map_conjSub_cLoc, h]

end Basic

section Sylow

theorem sylow_nonabelian_of_surj {J : Type} [Group J] [Finite J] {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (ρ : J →* SL(2, F)) (hρ : Function.Surjective ρ) (P : Sylow 2 J) :
    (∃ x ∈ (P : Subgroup J), ∃ y ∈ (P : Subgroup J), x * y ≠ y * x) ∧
      8 ≤ Nat.card (P : Subgroup J) := by
  obtain ⟨k, hk, ⟨qq⟩⟩ := specialLinearGroup_sylow_quaternion F hF (Sylow.mapSurjective hρ P)
  have hcoe : ((Sylow.mapSurjective hρ P : Sylow 2 SL(2, F)) : Subgroup SL(2, F)) =
      (P : Subgroup J).map ρ := Sylow.coe_mapSurjective hρ P
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hmem : ∀ u : ↥((Sylow.mapSurjective hρ P : Sylow 2 SL(2, F)) : Subgroup SL(2, F)),
      ∃ x ∈ (P : Subgroup J), ρ x = (u : SL(2, F)) := by
    intro u
    obtain ⟨x, hx, hxu⟩ := (SetLike.ext_iff.mp hcoe (u : SL(2, F))).mp u.2
    exact ⟨x, hx, hxu⟩
  obtain ⟨x, hx, hxa⟩ := hmem (qq.symm (QuaternionGroup.a 1))
  obtain ⟨y, hy, hyb⟩ := hmem (qq.symm (QuaternionGroup.xa 0))
  refine ⟨⟨x, hx, y, hy, fun hxy => ?_⟩, ?_⟩
  · apply quaternionGroup_a_mul_xa_ne h2
    apply qq.symm.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · have hcard : Nat.card ((P : Subgroup J).map ρ) ≤ Nat.card (P : Subgroup J) :=
      Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective ρ (P : Subgroup J))
    have h4 : Nat.card ((P : Subgroup J).map ρ) = 4 * 2 ^ k := by
      rw [← hcoe, Nat.card_congr qq.toEquiv]
      have : NeZero (2 ^ k) := ⟨by positivity⟩
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    omega

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]


theorem exists_surj_centralizer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) :
    ∃ e₀ : ℕ, 0 < e₀ ∧
      ∃ ρ : ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) →* SL(2, GaloisField p e₀),
        Function.Surjective ρ := by
  obtain ⟨e₀, -, he₀, ⟨φ'⟩⟩ := fs_fix_equiv' hp hq e hbN hb2 hσ1
  exact ⟨e₀, he₀, φ'.toMonoidHom.comp (fixHom e hbN),
    φ'.surjective.comp (fixHom_surjective e hbN hb2)⟩

theorem rset_props {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {K : Subgroup G} {a : G}
    (ρ : ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) →* SL(2, F)) (hρ : Function.Surjective ρ)
    {R : Subgroup ↥(Subgroup.centralizer ({a} : Set G))}
    (hR : R ∈ RSet (conjFamily (cLoc K a))) :
    IsPGroup 2 R ∧ (∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) ∧ 8 ≤ Nat.card R := by
  obtain ⟨J, ⟨c, rfl⟩, P, rfl⟩ := hR
  let eJ : ↥(cLoc K a) ≃* ↥(conjSub c (cLoc K a)) :=
    (cLoc K a).equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  let eL : ↥(cLoc K a) ≃* ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.subgroupOfEquivOfLe inf_le_right
  let ρJ : ↥(conjSub c (cLoc K a)) →* SL(2, F) := ρ.comp (eL.toMonoidHom.comp eJ.symm.toMonoidHom)
  have hρJ : Function.Surjective ρJ :=
    hρ.comp (eL.surjective.comp eJ.symm.surjective)
  obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := sylow_nonabelian_of_surj hF ρJ hρJ P
  refine ⟨(P.isPGroup').map _, ⟨(x : ↥(Subgroup.centralizer ({a} : Set G))),
    Subgroup.mem_map_of_mem _ hx, (y : ↥(Subgroup.centralizer ({a} : Set G))),
    Subgroup.mem_map_of_mem _ hy, fun h => hxy (Subtype.ext h)⟩, ?_⟩
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (P : Subgroup _) _
    (conjSub c (cLoc K a)).subtype_injective).toEquiv]
  exact h8

end Sylow

section DEdge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}


theorem fs3_false_of_le_normalizer (d : TwinCtx p f Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G)) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hJne : conjSub c₁ K ≠ conjSub c₂ K)
    (htwin : conjSub c₂ K ∉ twinSet Ω (conjSub c₁ K))
    {R₀ : Subgroup G} (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R₀) (hRle : R₀ ≤ conjSub c₂ K)
    (hRN : R₀ ≤ Subgroup.normalizer
      ((conjSub c₁ K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G)) : False := by
  have hI := d.hI
  have hΩ := d.hΩ
  have hJ₁ : conjSub c₁ K ∈ Ω := hΩ.conjInvariant c₁ K d.hK
  have hJ₂ : conjSub c₂ K ∈ Ω := hΩ.conjInvariant c₂ K d.hK
  have hI₁ := hI.conj c₁
  have hI₂ := hI.conj c₂
  have hzmem : c₁ * z * c₁⁻¹ ∈ conjSub c₁ K ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨conj_mem_conjSub hzKa.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₁ hzKa.2) (Subgroup.inv_mem _ hc₁)⟩
  have hRz : R₀ ≤ Subgroup.centralizer ({c₁ * z * c₁⁻¹} : Set G) := by
    intro x hx
    have h1 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈
        conjSub c₁ K ⊓ Subgroup.centralizer ({a} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hRN hx) _).mp hzmem
    have h2 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈ conjSub c₁ K := h1.1
    have h3 : x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) = 1 := by
      calc x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) =
          x * ((c₁ * z * c₁⁻¹) * (c₁ * z * c₁⁻¹)) * x⁻¹ := by group
        _ = 1 := by rw [hI₁.sq]; group
    rcases hI₁.unique _ h2 h3 with h | h
    · exfalso
      apply hI₁.ne_one
      calc c₁ * z * c₁⁻¹ = x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (c₁ * z * c₁⁻¹) = x * (c₁ * z * c₁⁻¹) * x⁻¹ * x := by group
        _ = c₁ * z * c₁⁻¹ * x := by rw [h]
  obtain ⟨V₀, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRle hRz)
  have hz₂V : c₂ * z * c₂⁻¹ ∈ V₀ := hRV (mem_of_le_member hI₂ hRle hR2 (by omega))
  have hcard : Nat.card R₀ ≤ Nat.card V₀ := Subgroup.card_le_of_le hRV
  rcases Asc77.l6_2 p f d.hp2 d.hq G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
    hI₂ V₀ hV hz₂V with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, hVc⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · have hVJ₂ : V₀ ≤ conjSub c₂ K := hV.1.trans inf_le_left
    have hVN : V₀ ≤ Subgroup.normalizer (conjSub c₁ K : Set G) :=
      le_normalizer_of_commutator_le (hVc.trans (oddCoreOf_le_self _))
    have hnbr : conjSub c₂ K ∈ omegaNbr Ω (conjSub c₁ K) :=
      ⟨hJ₂, hJne.symm, V₀, hV4, hVJ₂, hVN⟩
    have h1 := omegaNbr_conj hΩ.conjInvariant hnbr c₁⁻¹
    rw [conjSub_inv_conjSub] at h1
    have h2 := d.nbr h1
    have h3 := twinSet_conj hΩ.conjInvariant h2 c₁
    rw [conjSub_conjSub_inv] at h3
    exact htwin h3

theorem fs3_dEdgeless_or_swap (d : TwinCtx p f Ω K K' z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G)) {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (ρ : ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) →* SL(2, F))
    (hρ : Function.Surjective ρ) :
    Disconnected.DEdgeless (conjFamily (cLoc K a)) ∨
      ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K = K' := by
  by_cases hsw : ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K = K'
  · exact Or.inr hsw
  left
  push Not at hsw
  have hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G) := ⟨d.hI.mem, hzA⟩
  have key : ∀ M₁ ∈ conjFamily (cLoc K a), ∀ M₂ ∈ conjFamily (cLoc K a),
      M₂ ∉ omegaNbr (conjFamily (cLoc K a)) M₁ := by
    rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ ⟨-, hne, R₀, hR, hRle, hRN⟩
    obtain ⟨hR2, ⟨x, hx, y, hy, hxy⟩, h8⟩ := rset_props hF ρ hρ hR
    have hJne : conjSub (c₁ : G) K ≠ conjSub (c₂ : G) K :=
      fun h => hne (conjSub_cLoc_eq h).symm
    have htw : conjSub (c₂ : G) K ∉ twinSet Ω (conjSub (c₁ : G) K) := by
      rintro ⟨-, w, hw₁, hw₂⟩
      have e₁ := (d.hI.conj (c₁ : G)).eq hw₁
      have e₂ := (d.hI.conj (c₂ : G)).eq hw₂
      have hcz : (c₁ : G)⁻¹ * (c₂ : G) ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h12 : (c₁ : G) * z * (c₁ : G)⁻¹ = (c₂ : G) * z * (c₂ : G)⁻¹ := e₁.trans e₂.symm
        calc (c₁ : G)⁻¹ * (c₂ : G) * z =
              (c₁ : G)⁻¹ * ((c₂ : G) * z * (c₂ : G)⁻¹) * (c₂ : G) := by group
          _ = (c₁ : G)⁻¹ * ((c₁ : G) * z * (c₁ : G)⁻¹) * (c₂ : G) := by rw [h12]
          _ = z * ((c₁ : G)⁻¹ * (c₂ : G)) := by group
      have hcz' : (c₁ : G)⁻¹ * (c₂ : G) * z = z * ((c₁ : G)⁻¹ * (c₂ : G)) :=
        Subgroup.mem_centralizer_singleton_iff.mp hcz
      have hca : (c₁ : G)⁻¹ * (c₂ : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ c₁.2) c₂.2
      have hc2 : conjSub (c₂ : G) K = conjSub (c₁ : G) (conjSub ((c₁ : G)⁻¹ * (c₂ : G)) K) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
      rcases d.conj_K hcz' with h | h
      · apply hJne
        rw [hc2, h]
      · apply hsw ((c₁ : G)⁻¹ * (c₂ : G))
        · exact Subgroup.mem_centralizer_singleton_iff.mp hca
        · exact hcz'
        · exact h
    refine fs3_false_of_le_normalizer d hzKa c₁.2 hJne htw
      (hR2.map (Subgroup.centralizer ({a} : Set G)).subtype)
      ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
        fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₀ _
        (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
      omega
    · have h1 := Subgroup.map_mono (f := (Subgroup.centralizer ({a} : Set G)).subtype) hRle
      rw [map_conjSub_cLoc] at h1
      exact h1.trans inf_le_left
    · rw [← map_conjSub_cLoc]
      exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)
  intro M₁ hM₁ M₂ hM₂ hadj
  rcases hadj with h | h
  · exact key M₁ hM₁ M₂ hM₂ h
  · exact key M₂ hM₂ M₁ hM₁ h

end DEdge

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fs3_exists_conj_comm
    (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a)
    (hnoswap : ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K)
    {b g : G} (hbg : b = g * z * g⁻¹) (hba : b * a = a * b) :
    ∃ d : G, d * a = a * d ∧ (d⁻¹ * b * d) * z = z * (d⁻¹ * b * d) := by
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  have d' := twinCtx'_of_hyp25 h
  have hfix := fix_of_isFAut h haS hF
  have haK' : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.2
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK'
  have hσa : fieldChar hp hq e ⟨a, haK'⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hR'syl.1 h.hqR' h.hzR' hF ha2 haK'
  obtain ⟨e₀, he₀, ρ, hρ⟩ := exists_surj_centralizer hp hq e haK' ha2 hσa
  have hF₀ : ringChar (GaloisField p e₀) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e₀) p]
    exact hp
  have hzA : z ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.hyp.hzS a haS).symm
  have hDE : Disconnected.DEdgeless (conjFamily (cLoc K' a)) := by
    rcases fs3_dEdgeless_or_swap d' hzA hF₀ ρ hρ with h1 | h1
    · exact h1
    · exact absurd h1 hnoswap
  have hbA : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hba
  have hb2 : b * b = 1 := by
    rw [hbg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.hz'.sq]; group
  set s : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨b, hbA⟩ with hs
  have hs2 : s * s = 1 := Subtype.ext hb2
  have hΩ' : ∀ L ∈ conjFamily (cLoc K' a), ∀ g' : ↥(Subgroup.centralizer ({a} : Set G)),
      L.map (MulAut.conj g').toMonoidHom ∈ conjFamily (cLoc K' a) := by
    rintro _ ⟨c, rfl⟩ g'
    exact ⟨g' * c, conjSub_mul g' c _⟩
  have hne : (conjFamily (cLoc K' a)).Nonempty := ⟨_, ⟨1, conjSub_one _⟩⟩
  obtain ⟨M, ⟨c, rfl⟩, hMφ⟩ := S19M.exists_map_eq_of_dEdgeless hΩ' hne hDE (MulAut.conj s)
    (by rw [← map_mul, hs2, map_one]) (fun L hL => hΩ' L hL s)
  have hzL : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ cLoc K' a :=
    Subgroup.mem_subgroupOf.mpr ⟨d'.hI.mem, hzA⟩
  have hu : c * ⟨z, hzA⟩ * c⁻¹ ∈ conjSub c (cLoc K' a) := conj_mem_conjSub hzL
  have hsu : s * (c * ⟨z, hzA⟩ * c⁻¹) * s⁻¹ ∈ conjSub c (cLoc K' a) := by
    have h1 := conj_mem_conjSub (n := s) hu
    have h2 : conjSub s (conjSub c (cLoc K' a)) = conjSub c (cLoc K' a) := hMφ
    rwa [h2] at h1
  have hsuG : b * ((c : G) * z * (c : G)⁻¹) * b⁻¹ ∈ conjSub (c : G) K' := by
    have h1 : b * ((c : G) * z * (c : G)⁻¹) * b⁻¹ ∈
        (conjSub c (cLoc K' a)).map (Subgroup.centralizer ({a} : Set G)).subtype :=
      ⟨_, hsu, rfl⟩
    rw [map_conjSub_cLoc] at h1
    exact h1.1
  have hcI := d'.hI.conj (c : G)
  have hsq : b * ((c : G) * z * (c : G)⁻¹) * b⁻¹ * (b * ((c : G) * z * (c : G)⁻¹) * b⁻¹) = 1 := by
    calc b * ((c : G) * z * (c : G)⁻¹) * b⁻¹ * (b * ((c : G) * z * (c : G)⁻¹) * b⁻¹) =
        b * (((c : G) * z * (c : G)⁻¹) * ((c : G) * z * (c : G)⁻¹)) * b⁻¹ := by group
      _ = 1 := by rw [hcI.sq]; group
  have hbu : b * ((c : G) * z * (c : G)⁻¹) * b⁻¹ = (c : G) * z * (c : G)⁻¹ := by
    rcases hcI.unique _ hsuG hsq with h1 | h1
    · exfalso
      apply hcI.ne_one
      calc (c : G) * z * (c : G)⁻¹ =
          b⁻¹ * (b * ((c : G) * z * (c : G)⁻¹) * b⁻¹) * b := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hcomm : b * ((c : G) * z * (c : G)⁻¹) = ((c : G) * z * (c : G)⁻¹) * b := by
    calc b * ((c : G) * z * (c : G)⁻¹) =
        (b * ((c : G) * z * (c : G)⁻¹) * b⁻¹) * b := by group
      _ = ((c : G) * z * (c : G)⁻¹) * b := by rw [hbu]
  refine ⟨(c : G), Subgroup.mem_centralizer_singleton_iff.mp c.2, ?_⟩
  calc (c : G)⁻¹ * b * c * z = (c : G)⁻¹ * (b * ((c : G) * z * (c : G)⁻¹)) * c := by group
    _ = (c : G)⁻¹ * (((c : G) * z * (c : G)⁻¹) * b) * c := by rw [hcomm]
    _ = z * ((c : G)⁻¹ * b * c) := by group

theorem false_of_conj_normalizer' (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    {a b g : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF : IsFAut R' a)
    (hbg : b = g * z * g⁻¹) (hbz : b ≠ z) (hba : b * a = a * b)
    (hbN : b ∈ Subgroup.normalizer (K' : Set G)) : False := by
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  have hfix := fix_of_isFAut h haS hF
  have haK' : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.2
  have hb2 : b * b = 1 := by
    rw [hbg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.hz'.sq]; group
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK'
  have hσa : fieldChar hp hq e ⟨a, haK'⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hR'syl.1 h.hqR' h.hzR' hF ha2 haK'
  have key : ∃ y₀ ∈ K', orderOf y₀ = 4 ∧ y₀ * b = b * y₀ := by
    by_cases hχ : fieldChar hp hq e ⟨b, hbN⟩ = 1
    · exact exists_comm_order_four_of_commute hp hq e haK' hbN ha2 hb2 hba.symm hσa hχ
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hbot : IsPGroup 2 (⊥ : Subgroup G) := by
        intro x
        exact ⟨0, Subtype.ext (by simp [Subgroup.mem_bot.mp x.2])⟩
      obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge hbot
        (bot_le : ⊥ ≤ K' ⊓ Subgroup.centralizer ({b} : Set G))
      obtain ⟨⟨k, hk, ⟨eQ⟩⟩, -⟩ := fs_sylow_fixed'' hp hq e hbN hb2 hχ h.hR'syl hQ
      have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
      refine ⟨((eQ.symm (QuaternionGroup.xa 0) : Q) : G), (hQ.1 (eQ.symm _).2).1, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
        exact QuaternionGroup.orderOf_xa 0
      · exact Subgroup.mem_centralizer_singleton_iff.mp (hQ.1 (eQ.symm _).2).2
  obtain ⟨y₀, hy₀K, hy₀4, hy₀c⟩ := key
  have hbz' := eq_conj_z_of_commute_order_four h (c := 1) (g := g) (y₀ := y₀)
    (by rwa [conjSub_one]) hy₀4 (by rw [← hbg]; exact hy₀c.symm)
  exact hbz (by rw [hbg, hbz']; group)

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
